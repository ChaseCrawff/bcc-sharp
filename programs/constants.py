"""Certified jellium (one-component plasma) energies of the bcc, fcc, hcp and sc lattices (Section 9.2).

Output: results/constants.json

Quantity: e_L = E_cell / n, the Ewald energy per particle of the periodic configuration L of unit
point charges in a uniform neutralizing background (formula in bccnum/ewald_cert.py), in units
e^2/a with a the Wigner-Seitz radius ((4 pi / 3) a^3 = volume per particle).

Certification: every truncation error is bounded (packing count + summation by parts + Gaussian
tails, bccnum/intervals.py); all other arithmetic is exact rational or arb ball arithmetic.
Each energy is computed with two different Ewald parameters; the two enclosures must overlap
(alpha-independence self-check) and their intersection is reported.

hcp with optimal c/a is EXPLORATORY in its location (golden-section search, floats steer the
search) but every energy value reported for a rational (c/a)^2 is certified.
"""

import math
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, ctx  # noqa: E402

from bccnum import structures as S  # noqa: E402
from bccnum.ewald_cert import ewald_energy, default_cutoffs  # noqa: E402
from bccnum.ewald_float import ocp_energy_ws_float, cubic_cart, hcp_cart  # noqa: E402
from bccnum.intervals import arb_record  # noqa: E402
from bccnum.provenance import Run  # noqa: E402

PARAMS = {
    "alpha_ws_pair": [0.9, 1.4],      # two Ewald splitting parameters (Wigner-Seitz units)
    "X": 160,                          # cut-offs: alpha^2 R^2 >= X, K^2/(4 alpha^2) >= X
    "prec_bits": 384,
    "digits_reported": 45,
    "hcp_search": {"gamma_bracket": [1.62, 1.65], "golden_iterations": 40,
                   "search_X": 70, "search_prec_bits": 160, "gamma2_max_denominator": 10 ** 6},
}

DEFINITION = (
    "e_L = E_cell/n: Ewald energy per particle of the periodic configuration L of unit point charges "
    "with a uniform neutralizing background, G=0 Fourier mode removed (tinfoil/periodic convention), "
    "including the background term -pi Q^2/(2 V alpha^2); units e^2/a, a = Wigner-Seitz radius. "
    "Equals W/N for the periodic jellium energy W at the perfect lattice on any "
    "commensurate torus (identity of Ewald representations). Agreement with the thermodynamic-limit "
    "jellium energy of large neutral samples built from Wigner-Seitz cells is standard (argument: "
    "the cells are neutral with vanishing dipole moment, so cell-cell interactions decay like R^-5 and "
    "the limit is shape independent; total energy of a neutral system is independent of the potential "
    "offset, so the dropped G=0 mode does not matter)."
)


def certified(st, alpha_ws, X, prec):
    a, R2, k = default_cutoffs(st, alpha_ws, X)
    return ewald_energy(st, a, R2, k, prec=prec)


def summarize(r, digits):
    return {
        "alpha_nat": r["alpha"], "R2_nat": r["R2"], "kappa": r["kappa"],
        "e_ws": arb_record(r["E_per_particle_ws"], digits),
        "real_tail_bound_per_translate": float(r["tail_bound_real_per_translate"].mid()),
        "reciprocal_tail_bound": float(r["tail_bound_reciprocal_lattice_sum"].mid()),
        "n_real_points": r["n_real_points"], "n_real_shells": r["n_real_shells"],
        "n_reciprocal_points": r["n_reciprocal_points"], "n_reciprocal_shells": r["n_reciprocal_shells"],
        "phases_exact": r["phases_exact"], "seconds": round(r["seconds"], 4),
    }


def energy_pair(st, P):
    X, prec, digits = P["X"], P["prec_bits"], P["digits_reported"]
    runs = [certified(st, aw, X, prec) for aw in P["alpha_ws_pair"]]
    e1, e2 = runs[0]["E_per_particle_ws"], runs[1]["E_per_particle_ws"]
    ok = bool(e1.overlaps(e2))
    if not ok:
        raise RuntimeError(f"alpha self-check FAILED for {st.name}: {e1} vs {e2}")
    ctx.prec = prec
    e = e1.intersection(e2)
    return e, {"structure": st.describe(), "alpha_runs": [summarize(r, digits) for r in runs],
               "alpha_self_check_overlap": ok, "e_ws_certified": arb_record(e, digits),
               "e_rydberg_times_rs": arb_record(2 * e, digits)}


def golden_hcp(P):
    """Golden-section search in gamma = c/a over rational gamma^2 (certified evaluations)."""
    H = P["hcp_search"]
    cache = {}

    def f(gamma):
        g2 = Fr(gamma * gamma).limit_denominator(H["gamma2_max_denominator"])
        if g2 not in cache:
            r = certified(S.hcp(g2), 1.1, H["search_X"], H["search_prec_bits"])
            cache[g2] = r["E_per_particle_ws"]
        return float(cache[g2].mid()), g2

    lo, hi = H["gamma_bracket"]
    phi = (math.sqrt(5) - 1) / 2
    c, d = hi - phi * (hi - lo), lo + phi * (hi - lo)
    fc, fd = f(c)[0], f(d)[0]
    for _ in range(H["golden_iterations"]):
        if fc < fd:
            hi, d, fd = d, c, fc
            c = hi - phi * (hi - lo)
            fc = f(c)[0]
        else:
            lo, c, fc = c, d, fd
            d = lo + phi * (hi - lo)
            fd = f(d)[0]
    best_g2 = min(cache, key=lambda g: cache[g].mid())
    return best_g2, len(cache)


def main():
    P = PARAMS
    run = Run(__file__, P, tier="mixed")
    digits = P["digits_reported"]
    out = {"definition": DEFINITION, "energies": {}, "checks": {}, "gaps": {}}
    E = {}
    for name, fn in S.OCP_STRUCTURES.items():
        E[name], out["energies"][name] = energy_pair(fn(), P)
        print(name, E[name].str(30))

    # supercell checks (same energy per particle from conventional cells)
    for prim, conv in (("bcc", S.bcc_conventional()), ("fcc", S.fcc_conventional())):
        e_conv, rec = energy_pair(conv, P)
        out["checks"][f"{prim}_conventional_cell"] = {
            "e_ws_certified": rec["e_ws_certified"], "overlaps_primitive": bool(e_conv.overlaps(E[prim]))}

    # independent float implementation (exploratory) as a cross-check
    fl = {}
    for name in ("sc", "bcc", "fcc"):
        fl[name] = ocp_energy_ws_float(*cubic_cart(name), alpha_ws=1.2)
    fl["hcp"] = ocp_energy_ws_float(*hcp_cart(math.sqrt(8 / 3)), alpha_ws=1.2)
    out["checks"]["float_implementation"] = {
        k: {"value": v, "abs_diff_to_certified_mid": abs(v - float(E[k].mid()))} for k, v in fl.items()}

    # gaps (certified)
    ctx.prec = P["prec_bits"]
    for a, b in (("bcc", "fcc"), ("bcc", "hcp"), ("fcc", "hcp"), ("bcc", "sc")):
        g = E[a] - E[b]
        out["gaps"][f"{a}-{b}"] = {"difference_ws": arb_record(g, 30),
                                   "relative_to_|e_bcc|": arb_record(g / abs(E["bcc"]), 30),
                                   "sign_certified": ("negative" if g < 0 else "positive" if g > 0 else "undecided")}
        print(a, "-", b, g.str(20), "relative", (g / abs(E["bcc"])).str(10))

    # hcp optimal c/a (location exploratory, values certified)
    best_g2, n_eval = golden_hcp(P)
    e_opt, rec = energy_pair(S.hcp(best_g2), P)
    ctx.prec = P["prec_bits"]
    out["hcp_optimal_ca"] = {
        "tier_note": "location of the optimum exploratory (golden-section search over rational (c/a)^2); "
                     "energies certified. e_hcp(gamma*) is a certified UPPER bound for min over c/a of e_hcp.",
        "gamma2_best": str(best_g2), "c_over_a_best_float": math.sqrt(float(best_g2)),
        "c_over_a_ideal": math.sqrt(8 / 3), "n_certified_evaluations_in_search": n_eval,
        "e_ws_certified": rec["e_ws_certified"],
        "alpha_self_check_overlap": rec["alpha_self_check_overlap"],
        "e_opt_minus_e_ideal": arb_record(e_opt - E["hcp"], 30),
        "e_bcc_minus_e_opt": arb_record(E["bcc"] - e_opt, 30),
        "e_fcc_minus_e_opt": arb_record(E["fcc"] - e_opt, 30),
    }
    print("hcp opt c/a", math.sqrt(float(best_g2)), e_opt.str(25), "vs ideal", (e_opt - E["hcp"]).str(10))

    path = run.write("constants", out)
    print("wrote", path)


if __name__ == "__main__":
    main()
