"""Certificate of the lattice case (Theorem 5.1 of the paper).

Output: results/lattice.json

Claim certified (Theorem 5.1): for every lattice Lambda of covolume 4 pi/3 (WS units),
    e(Lambda) - e_bcc >= (e_fcc - e_bcc) D(Lambda),
with equality iff Lambda is a rotated bcc or fcc lattice. In covolume-one form (L = Lambda/s, s = (4 pi/3)^{1/3}, Gram matrix Y),
e(Lambda) = (H(Y) - 3)/(2 s) with H = H_{1/2} (bccnum/lattice_cert.py), so the claim is H(Y) - H_B >= 2 s g D, g = e_fcc - e_bcc,
H_B = H at bcc, H_F = H at fcc = H_B + 2 s g.

Structure (this script performs the finite checks of Section 5).
Part A, mode "boxes" (output results/lattice_boxes.json): the reduced-coordinate domain (Section 5), cut into grid^5 cells and
bisected; each terminal box is of one of the types
  (R)      a necessary reduction inequality fails at every point: no reduced representative;
  (C)      short first vector: 2 G(1/2, pi r1^2) > H_F^+ (one positive term of H);
  (E1)     inf_box P > H_F^+, P the truncated positive series (a lower bound of H), by (5.4) or (5.5)/(5.6) of Section 5.2;
  (SB/SF)  the strain-chart enclosure w of the box lies in the certified invariant region of bcc/fcc;
  (E2)     the eigenvalues of C over the box lie in [mu_lo, 1.69) and inf_box P - H_B^+ > (2 s g)^+ sup_box Q (D <= Q, Eq. (5.8)).
Part B, mode "strain" (output results/lattice_strain.json): for bcc and fcc, the ball certificate (Proposition 5.2) and the
bisection of F intersected with the invariant region (types (O), (BALL), (E1), (E2): the cases (i)-(iv) of the proof of Proposition 5.2).
Equality: (E1), (E2) are strict; (BALL) gives equality only at the centre; (R), (C), (O) contain no equality case.
Binary64 enters only as box ends, centres and beta; every comparison with a rational parameter is made in arb, and the box
half-widths are formed in arb.
"""

import argparse
import itertools
import json
import math
import os
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from flint import arb, ctx  # noqa: E402

import bccnum.lattice_cert as B  # noqa: E402

PARAMS = {
    "prec_bits": 96,
    "r1C": "4/5",                      # short-vector cut (Section 5.1)
    "r1max": "1155/1000",              # >= (8/(3 sqrt 3))^{1/3}; the box (5.3)
    "mu_lo": "9/10", "mu_hi": "169/100",
    "n_E_far": 2, "n_E_mid": 3, "n_E_near": 4, "near_dist": 0.03, "mid_dist": 0.1,
    "grid": 16,                        # the Part A root box is first cut into grid^5 equal cells
    # strain charts (Part B): invariant region ||w_E||_2 <= rho_E, ||w_T||_inf <= rho_T; ball [-beta, beta]^5
    "strain": {"bcc": {"rho_E": "2/25", "rho_T": "4/25", "beta": "1/4000", "ball_sub": 5},
               "fcc": {"rho_E": "13/200", "rho_T": "4/25", "beta": "1/4000", "ball_sub": 5}},
    "handoff_dist": 0.15,
    "strain_n": 3, "strain_n_near": 5, "strain_near": 2e-3,
    "strain_n_local": 6,               # shells summed exactly in the ball Hessians; tail by Lemma B.2
    "strain_max_depth": 120,
    "max_depth": 40, "max_boxes": 5_000_000,
}


def F2arb(s):
    f = Fr(s)
    return arb(f.numerator) / f.denominator


def setup():
    ctx.prec = PARAMS["prec_bits"]
    a1 = json.load(open(os.path.join(HERE, "results", "constants.json")))["results"]["energies"]
    eb = arb(a1["bcc"]["e_ws_certified"]["enclosure"])
    ef = arb(a1["fcc"]["e_ws_certified"]["enclosure"])
    s = (4 * arb.pi() / 3) ** (arb(1) / 3)
    K = {"H_B": 2 * s * eb + 3, "H_F": 2 * s * ef + 3, "two_s_g": 2 * s * (ef - eb), "s": s}
    K["H_B_up"] = arb(K["H_B"].upper())
    K["H_F_up"] = arb(K["H_F"].upper())
    K["tsg_up"] = arb(K["two_s_g"].upper())
    mu_lo = F2arb(PARAMS["mu_lo"])
    K["mu_lo"], K["mu_hi"] = mu_lo, F2arb(PARAMS["mu_hi"])
    K["kappa"] = arb((100 / (1 + mu_lo.sqrt()) ** 2).upper())
    K["reps"] = representatives()
    return K


# ------------------------------------------------------------------------------------------------ representatives (exact)


def exact_R(name, gamma):
    """Upper-triangular R (balls) and xi of the basis L0 gamma, L0 the covolume-one bcc or fcc basis of Muratov and Novaga (10)."""
    t = arb(2) ** (arb(1) / 3)
    if name == "bcc":
        base = [[Fr(1), Fr(0), Fr(1, 2)], [Fr(0), Fr(1), Fr(1, 2)], [Fr(0), Fr(0), Fr(1, 2)]]
        sc = t * t
    else:
        base = [[Fr(1), Fr(1), Fr(0)], [Fr(1), Fr(0), Fr(1)], [Fr(0), Fr(1), Fr(1)]]
        sc = 1 / (t * t)
    M = [[sum(base[i][k] * gamma[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    G = [[sum(M[k][i] * M[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
           + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    assert abs(det) == (Fr(1, 2) if name == "bcc" else 2), det     # covolume one after scaling: |det| * sc^{3/2} = 1
    Gb = [[arb(G[i][j].numerator) / G[i][j].denominator * sc for j in range(3)] for i in range(3)]
    r1 = Gb[0][0].sqrt()
    R01, R02 = Gb[0][1] / r1, Gb[0][2] / r1
    r2 = (Gb[1][1] - R01 ** 2).sqrt()
    R12 = (Gb[1][2] - R01 * R02) / r2
    r3 = (Gb[2][2] - R02 ** 2 - R12 ** 2).sqrt()
    R = [[r1, R01, R02], [arb(0), r2, R12], [arb(0), arb(0), r3]]
    xi = [r1, r2, R01 / r1, R02 / r1, R12 / r2]
    Rinv = [[1 / r1, -R01 / (r1 * r2), (R01 * R12 - R02 * r2) / (r1 * r2 * r3)],
            [arb(0), 1 / r2, -R12 / (r2 * r3)], [arb(0), arb(0), 1 / r3]]
    return R, Rinv, xi


# Integer bases gamma (columns in terms of the covolume-one basis L0 of Muratov and Novaga (10)) of the reduced representatives of bcc and fcc in
# the root box, found by a float search over bases built from short vectors. Each is
# re-checked here: |det| (exact), and xi recomputed in arb and compared with the expected reduced coordinates. Completeness of this
# list is not needed for soundness: a missed point would leave boxes unresolved (the run would not certify).
REP_GAMMAS = {"bcc": [[[-1, 0, 0], [-1, 0, -1], [1, -1, 1]]],
              "fcc": [[[0, -1, 0], [-1, 0, -1], [0, 0, 1]], [[0, -1, 0], [-1, 0, 0], [0, 0, -1]]]}
REP_TARGETS = {"bcc": [[1.091123636, 1.028721229, 1 / 3, 1 / 3, -.5]],
               "fcc": [[1.122462048, 0.972080649, .5, .5, -1 / 3], [1.122462048, 0.972080649, .5, .5, 1 / 3]]}


def representatives():
    out = {}
    for name in ("bcc", "fcc"):
        out[name] = []
        for gam, tg in zip(REP_GAMMAS[name], REP_TARGETS[name]):
            R, Rinv, xi = exact_R(name, [[Fr(v) for v in row] for row in gam])
            assert all(abs(float(v.mid()) - t) < 1e-8 for v, t in zip(xi, tg)), (name, [float(v.mid()) for v in xi])
            out[name].append({"gamma": gam, "R": R, "Rinv": Rinv, "xi": xi})
    return out


# ------------------------------------------------------------------------------------------------ boxes
ROOT_FIELDS = ("r1", "r2", "x", "y", "z")


def root_box():
    r1C, r1max = F2arb(PARAMS["r1C"]), F2arb(PARAMS["r1max"])
    s34 = arb(3).sqrt() / 2
    r2lo = s34 * r1C
    r2hi = (1 / (r1C * s34)).sqrt()
    lo = [float(r1C.lower()), float(r2lo.lower()), 0.0, 0.0, -0.5]
    hi = [float(r1max.upper()), float(r2hi.upper()), 0.5, 0.5, 0.5]
    # float(...) of lower()/upper() may round; widen by one ulp outward
    lo = [math.nextafter(v, -math.inf) if i < 2 else v for i, v in enumerate(lo)]
    hi = [math.nextafter(v, math.inf) if i < 2 else v for i, v in enumerate(hi)]
    return lo, hi


def balls_of(lo, hi):
    return [arb(l).union(arb(h)) for l, h in zip(lo, hi)]


def half_widths(lo, hi, c):
    """r_i >= max(h_i - c_i, c_i - l_i), formed in arb from the float ends and the float centre, so that the box
    lies in prod [c_i - r_i, c_i + r_i]."""
    out = []
    for l, h, cc in zip(lo, hi, c):
        a, b = arb(h) - arb(cc), arb(cc) - arb(l)
        out.append(arb(max(a.upper(), b.upper())))
    return out


def float_up(x):
    """The least binary64 number certainly >= the ball x."""
    f = float(x.upper())
    while not (arb(f) >= x):
        f = math.nextafter(f, math.inf)
    return f


def below_sqrt3_line(lo, hi):
    """True if sqrt(3) w2 < w1 certainly holds on the box (the box misses F there), with sqrt 3 as a ball."""
    return bool(arb(hi[1]) * arb(3).sqrt() < arb(lo[0]))


M1 = [m for m in B.half_set(1)]
M2 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1) if (a, b) > (0, 0)]


def pruned(xb):
    r1, r2, x, y, z = xb
    r3 = 1 / (r1 * r2)
    for (m1, m2, m3) in M1:
        f = (r1 * (m1 + x * m2 + y * m3)) ** 2 + (r2 * (m2 + z * m3)) ** 2 + (r3 * m3) ** 2 - r1 * r1
        if f < 0:
            return True
    for (a, b) in M2:
        f = (r2 * (a + z * b)) ** 2 + (r3 * b) ** 2 - r2 * r2
        if f < 0:
            return True
    return False


def short_vector(xb, KK):
    r1hi = arb(xb[0].upper())
    x = arb.pi() * r1hi * r1hi
    g = 2 * B.G_values(x, arb(1) / 2, 0)[0]
    return g > KK["H_F_up"]


def inside(lo, hi, blo, bhi):
    return all(blo[i] <= lo[i] and hi[i] <= bhi[i] for i in range(5))


def dist_inf(lo, hi, c):
    return max(max(c[i] - hi[i], lo[i] - c[i], 0.0) for i in range(5))


KK = None


def init_worker():
    global KK
    KK = setup()
    for name in ("bcc", "fcc"):
        for r in KK["reps"][name]:
            r["xf"] = [float(v.mid()) for v in r["xi"]]
    KK["strain"] = strain_regions(KK)


# ------------------------------------------------------------------------------------------------ strain charts (Part B)
def cubic_B0(name):
    t = arb(2) ** (arb(1) / 3)
    Z, h = arb(0), arb(1) / 2
    if name == "bcc":
        return [[t, Z, t * h], [Z, t, t * h], [Z, Z, t * h]]
    return [[1 / t, 1 / t, Z], [1 / t, Z, 1 / t], [Z, 1 / t, 1 / t]]


def strain_chart(name, KK0):
    """Chart with whitening sigma from the (diagonal) point Hessian at w = 0 (of Phi for bcc, of P for fcc)."""
    from bccnum.lattice_strain import Chart
    ch1 = Chart(cubic_B0(name), [1.0] * 5)
    w0 = [arb(0)] * 5
    J = ch1.H_partial(w0, B.half_set(5))
    h = [float(J.h[k][k].mid()) for k in range(5)]
    if name == "bcc":
        Qj, _ = ch1.Q_defect(w0, KK0["kappa"])
        h = [h[k] - float((KK0["two_s_g"] * Qj.h[k][k]).mid()) for k in range(5)]
    lamE, lamT = (h[0] + h[1]) / 2, (h[2] + h[3] + h[4]) / 3
    sig = [lamE ** -0.5] * 2 + [lamT ** -0.5] * 3
    return Chart(cubic_B0(name), sig), sig, (lamE, lamT)


def strain_w_of_xibox(xb, gamma, ch):
    """Enclosure of the chart coordinates w of the lattices with reduced coordinates in the box xb (balls), through the
    integer basis change gamma: C' = (R gamma^{-1} B0^{-1})^T (R gamma^{-1} B0^{-1}), S = 3 C'/tr C' - I, w_k = <S, E_k>/sigma_k."""
    _, R = B.gram_from_xi(xb)
    import numpy as np
    gi = np.round(np.linalg.inv(np.array(gamma, dtype=float))).astype(int).tolist()
    assert (np.array(gi) @ np.array(gamma) == np.eye(3)).all()
    Ri = [[sum((R[i][k] * gi[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)]
    A = [[sum((Ri[i][k] * ch.B0inv[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)]
    Cp = [[sum((A[k][i] * A[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)]
    tr = Cp[0][0] + Cp[1][1] + Cp[2][2]
    S = [[3 * Cp[i][j] / tr - (1 if i == j else 0) for j in range(3)] for i in range(3)]
    return [sum((S[i][j] * ch.E[k][i][j] for i in range(3) for j in range(3)), arb(0)) / ch.sigma[k] for k in range(5)]


def in_strain_region(w, reg):
    wE2 = w[0] * w[0] + w[1] * w[1]
    return bool(wE2.upper() <= reg["rho_E"].lower() ** 2 and all(abs(w[k]).upper() <= reg["rho_T"].lower() for k in (2, 3, 4)))


def beta_float(name):
    """The ball parameter as one binary64 number <= the stated rational, used by both the ball certificate and the test."""
    b = F2arb(PARAMS["strain"][name]["beta"])
    return math.nextafter(float(b.lower()), 0.0)


def strain_regions(KK0):
    out = {}
    for name in ("bcc", "fcc"):
        ch, sig, lam = strain_chart(name, KK0)
        P = PARAMS["strain"][name]
        out[name] = {"chart": ch, "sigma": sig, "lam": lam, "rho_E": F2arb(P["rho_E"]), "rho_T": F2arb(P["rho_T"]),
                     "beta": F2arb(P["beta"]), "gammas": [r["gamma"] for r in KK0["reps"][name]]}
    return out


def process(box):
    lo, hi = box
    xb = balls_of(lo, hi)
    if pruned(xb):
        return ("R", None)
    if short_vector(xb, KK):
        return ("C", None)
    rb = KK["reps"]["bcc"][0]
    db = dist_inf(lo, hi, rb["xf"])
    df = min(dist_inf(lo, hi, rf["xf"]) for rf in KK["reps"]["fcc"])
    d = min(db, df)
    n = PARAMS["n_E_near"] if d < PARAMS["near_dist"] else (PARAMS["n_E_mid"] if d < PARAMS["mid_dist"] else PARAMS["n_E_far"])
    mset = B.half_set(n)
    c = [(l + h) / 2 for l, h in zip(lo, hi)]
    rad = half_widths(lo, hi, c)
    cb = [arb(v) for v in c]
    # first order (mean value) bound: cheap, and tight away from the minima
    Jc = B.H_partial1(cb, mset)
    Jb = B.H_partial1(xb, mset)
    low = B.mean_value_lower(rad, Jc, Jb)
    if low > KK["H_F_up"]:
        return ("E1", float((low - KK["H_F_up"]).lower()))
    near = d < PARAMS["near_dist"]
    if near:
        # second order (Section 5.2) near the minima, where the first-order bound is weak
        J2c = B.H_partial(cb, mset)
        J2b = B.H_partial(xb, mset)
        low2 = B.taylor_lower_bound2(rad, J2c, B.hessian_matrix(J2b))
        if low2 > low:
            low = low2
        if low > KK["H_F_up"]:
            return ("E1", float((low - KK["H_F_up"]).lower()))
    # hand-off to a strain chart: the w-enclosure of the cell lies in the certified invariant region
    if d < PARAMS["handoff_dist"]:
        for name in ("bcc", "fcc"):
            reg = KK["strain"][name]
            for rep, gam in zip(KK["reps"][name], reg["gammas"]):
                if max(abs(rep["xf"][i] - (lo[i] + hi[i]) / 2) for i in range(5)) > PARAMS["handoff_dist"]:
                    continue
                w = strain_w_of_xibox(xb, gam, reg["chart"])
                if all(x.is_finite() for x in w) and in_strain_region(w, reg):
                    return ("SB" if name == "bcc" else "SF", None)
    C = B.C_matrix(xb, rb["Rinv"])
    elo, ehi = B.gershgorin(C)
    if elo >= KK["mu_lo"] and ehi < KK["mu_hi"]:
        Qc = B.Q_defect_jet1(cb, rb["Rinv"], KK["kappa"])
        Qb = B.Q_defect_jet1(xb, rb["Rinv"], KK["kappa"])
        qsup = B.mean_value_upper(rad, Qc, Qb)
        qv = arb(Qb.v.upper())
        if qv < qsup:
            qsup = qv
        margin = low - KK["H_B_up"] - KK["tsg_up"] * qsup
        if margin > 0:
            return ("E2", float(margin.lower()))
    return ("S", None)


SREG = None
SNAME = None


def init_strain_worker(name):
    global SREG, SNAME
    init_worker()
    SNAME = name
    SREG = KK["strain"][name]


def strain_process(box):
    """Process a w-box of the strain region SREG (fundamental domain F of the cubic group intersected with the invariant
    region; Section 5.3 and Proposition 5.2, in the w-chart)."""
    lo, hi = box
    reg = SREG
    ch = reg["chart"]
    # outside F: w1 < 0, or w2 < w1/sqrt3, or w3 < 0, or w4 < 0 throughout
    if hi[0] < 0 or hi[2] < 0 or hi[3] < 0 or below_sqrt3_line(lo, hi):
        return ("O", None)
    wb = balls_of(lo, hi)
    # outside the invariant region throughout
    if (wb[0] * wb[0] + wb[1] * wb[1]).lower() > reg["rho_E"].upper() ** 2 or \
            any(min(abs(lo[k]), abs(hi[k])) > float_up(reg["rho_T"]) and lo[k] * hi[k] > 0 for k in (2, 3, 4)):
        return ("O", None)
    beta = beta_float(SNAME)
    bb2 = arb(beta) * arb(beta)
    if (wb[0] * wb[0] + wb[1] * wb[1]).upper() <= bb2.lower() and all(-beta <= lo[k] and hi[k] <= beta for k in (2, 3, 4)):
        return ("BALL", None)                    # box inside the invariant ball {||w_E||_2 <= beta, ||w_T||_inf <= beta}
    d = max(max(abs(lo[k]), abs(hi[k])) for k in range(5))
    n = PARAMS["strain_n_near"] if d < PARAMS["strain_near"] else PARAMS["strain_n"]
    mset = B.half_set(n)
    c = [(l + h) / 2 for l, h in zip(lo, hi)]
    cb = [arb(v) for v in c]
    rad = half_widths(lo, hi, c)
    bc = ch.base(cb)
    bb = ch.base(wb)
    if not (bb[2].v > 0):                         # d(w) > 0 on the box: the chart is valid there
        return ("S", None)
    Pc = ch.H_partial(cb, mset, bc)
    Pb = ch.H_partial(wb, mset, bb)
    tries = []
    if SNAME == "bcc":
        Cb = ch.C_jets(wb, bb)
        elo, ehi = B.gershgorin([[x.v for x in row] for row in Cb])
        if elo >= KK["mu_lo"] and ehi < KK["mu_hi"]:
            Qc, _ = ch.Q_defect(cb, KK["kappa"], bc)
            Qb, _ = ch.Q_defect(wb, KK["kappa"], bb)
            tries.append(("E2", Pc - Qc * KK["tsg_up"] - KK["H_B_up"], Pb - Qb * KK["tsg_up"]))
    tries.append(("E1", Pc - KK["H_F_up"], Pb))
    for typ, fc, fb in tries:
        Hb = B.hessian_matrix(fb)
        best = B.mean_value_lower(rad, fc, fb)
        lam = B.lam_min_lower(Hb)
        if lam is not None and lam > 0:
            q = B.box_quadratic_lower(rad, fc, lam)
            best = q if q > best else best
        t = B.taylor_lower_bound2(rad, fc, Hb)
        best = t if t > best else best
        if best > 0:
            return (typ, float(best.lower()))
    return ("S", None)


def strain_ball_certificate(name):
    """PD Hessian of Phi (bcc) / P (fcc) on every sub-box (of [0,beta]^4 x [-beta,beta]) that meets F and the invariant
    ball Ball = {||w_E||_2 <= beta, ||w_T||_inf <= beta}. By the symmetry of Section 5.3 this gives PD on all of Ball, which is convex."""
    KK0 = setup()
    reg = strain_regions(KK0)[name]
    ch = reg["chart"]
    beta = beta_float(name)
    nsub = PARAMS["strain"][name]["ball_sub"]
    nl = PARAMS["strain_n_local"]
    mset = B.half_set(nl)
    e01 = [beta * i / nsub for i in range(nsub + 1)]
    e11 = [-beta + 2 * beta * i / nsub for i in range(nsub + 1)]
    # the sub-boxes must cover [0,beta]^4 x [-beta,beta]: exact outer ends, increasing interior faces (check 1, X1)
    assert e01[0] == 0.0 and e01[-1] == beta and e11[0] == -beta and e11[-1] == beta
    assert all(x < y for x, y in zip(e01, e01[1:])) and all(x < y for x, y in zip(e11, e11[1:]))
    worst, n_checked, allok = None, 0, True
    for cell in itertools.product(range(nsub), repeat=5):
        lo = [e01[c] for c in cell[:4]] + [e11[cell[4]]]
        hi = [e01[c + 1] for c in cell[:4]] + [e11[cell[4] + 1]]
        if below_sqrt3_line(lo, hi):
            continue                                   # does not meet F (w1, w3, w4 >= 0 by construction)
        if arb(lo[0]) * arb(lo[0]) + arb(lo[1]) * arb(lo[1]) > arb(beta) * arb(beta):
            continue                                   # does not meet Ball (certainly; tangent cells are kept)
        wb = balls_of(lo, hi)
        J = ch.H_partial(wb, mset)
        tau = ch.hessian_tail(wb, nl)
        if tau is None:
            allok = False
            break
        Hm = [[J.h[i][j] + arb(0, tau.upper()) for j in range(5)] for i in range(5)]
        if name == "bcc":
            Qj, Cj = ch.Q_defect(wb, KK0["kappa"])
            Hm = [[Hm[i][j] - KK0["two_s_g"] * Qj.h[i][j] for j in range(5)] for i in range(5)]
        lam = B.lam_min_lower(Hm)
        n_checked += 1
        if lam is None or not (lam > 0):
            allok = False
            break
        worst = lam if worst is None or lam < worst else worst
    rec = {"name": name, "beta": PARAMS["strain"][name]["beta"], "sub": nsub, "subboxes_checked": n_checked,
           "all_pd": allok, "min_lambda_lower": None if worst is None else worst.str(10)}
    if name == "bcc":
        Cj = ch.C_jets([arb(-beta).union(arb(beta))] * 5)          # a superset of Ball
        elo, ehi = B.gershgorin([[x.v for x in row] for row in Cj])
        rec["C_eig_range"] = [elo.str(8), ehi.str(8)]
        rec["C_range_ok"] = bool(elo >= KK0["mu_lo"] and ehi < KK0["mu_hi"])
    return rec


def strain_certificate(name, procs=4, log=print):
    KK0 = setup()
    reg = strain_regions(KK0)[name]
    rE, rT = float_up(reg["rho_E"]), float_up(reg["rho_T"])      # outward
    work = [([0.0, 0.0, 0.0, 0.0, -rT], [rE, rE, rT, rT, rT])]
    counts, margins = {}, {}
    depth, nboxes = 0, 0
    t0 = time.perf_counter()
    with Pool(procs, initializer=init_strain_worker, initargs=(name,)) as pool:
        while work and depth <= PARAMS["strain_max_depth"] and nboxes < PARAMS["max_boxes"]:
            res = pool.map(strain_process, work, chunksize=max(1, len(work) // 64))
            nxt = []
            for box, (typ, mg) in zip(work, res):
                nboxes += 1
                if typ == "S":
                    nxt.extend(split(box))
                else:
                    counts[typ] = counts.get(typ, 0) + 1
                    if mg is not None:
                        margins[typ] = mg if typ not in margins else min(margins[typ], mg)
            log("strain", name, "depth", depth, "processed", len(work), "split", len(nxt) // 2, counts,
                round(time.perf_counter() - t0), "s")
            work = nxt
            depth += 1
    return {"name": name, "rho_E": PARAMS["strain"][name]["rho_E"], "rho_T": PARAMS["strain"][name]["rho_T"],
            "sigma_floats": reg["sigma"], "sigma_hex": [float(x).hex() for x in reg["sigma"]],
            "root": [[0.0, 0.0, 0.0, 0.0, -rT], [rE, rE, rT, rT, rT]],
            "terminal_counts": counts, "smallest_margins": margins, "unresolved": len(work), "boxes_processed": nboxes,
            "depth_reached": depth}


def split(box):
    """Bisect at the midpoint of the widest coordinate (the two halves share the float face m; their union is the box)."""
    lo, hi = box
    w = [h - l for l, h in zip(lo, hi)]
    k = max(range(5), key=lambda i: w[i])
    m = (lo[k] + hi[k]) / 2
    a_hi = list(hi); a_hi[k] = m
    b_lo = list(lo); b_lo[k] = m
    return [(list(lo), a_hi), (b_lo, list(hi))]


def main(argv=None):
    from bccnum.provenance import Run, sha256_file
    parser = argparse.ArgumentParser(description="Verify the selected part of the lattice certificate.")
    parser.add_argument("mode", nargs="?", choices=("all", "boxes", "strain"), default="all")
    mode = parser.parse_args(argv).mode
    # the constants this run reads (setup(), in this process and in every worker), recorded with the parameters and
    # hashed again when the result is written
    constants = os.path.join(HERE, "results", "constants.json")
    PARAMS["inputs"] = {"results/constants.json": sha256_file(constants)}
    run = Run(__file__, PARAMS, tier="cert",
              inputs={"results/constants.json": (constants, PARAMS["inputs"]["results/constants.json"])})
    t0 = time.perf_counter()
    out = {}
    certified = True
    if mode in ("all", "strain"):
        with Pool(2) as pool:
            out["strain_balls"] = pool.map(strain_ball_certificate, ["bcc", "fcc"])
        for r in out["strain_balls"]:
            print("strain ball", r, flush=True)
        out["strain_regions"] = [strain_certificate(n, procs=int(os.environ.get("BS_PROCS", "4")),
                                                    log=lambda *a: print(*a, flush=True)) for n in ("bcc", "fcc")]
        certified = (all(r["unresolved"] == 0 for r in out["strain_regions"])
                     and all(r["all_pd"] for r in out["strain_balls"])
                     and out["strain_balls"][0].get("C_range_ok", False))
    if mode in ("all", "boxes"):
        counts = {}
        margins = {}
        root_prec = ctx.prec
        lo0, hi0 = root_box()                    # rigorous at any precision: ball ends, then one ulp outward
        k = PARAMS["grid"]
        w = [(h - l) / k for l, h in zip(lo0, hi0)]

        def cells():
            for idx in itertools.product(range(k), repeat=5):
                lo = [lo0[i] + idx[i] * w[i] for i in range(5)]
                hi = [hi0[i] if idx[i] == k - 1 else lo0[i] + (idx[i] + 1) * w[i] for i in range(5)]
                yield (lo, hi)
        nboxes = 0
        depth = 0
        with Pool(int(os.environ.get("BS_PROCS", "4")), initializer=init_worker) as pool:
            # level 0: the grid cells, streamed (cells share faces; their union is the root box, since the last cell in each
            # coordinate ends exactly at the root's upper end)
            work = []
            cl = list(cells())
            for box, (typ, mg) in zip(cl, pool.imap(process, cl, chunksize=256)):
                nboxes += 1
                if typ == "S":
                    work.extend(split(box))
                else:
                    counts[typ] = counts.get(typ, 0) + 1
                    if mg is not None:
                        margins[typ] = mg if typ not in margins else min(margins[typ], mg)
                if nboxes % 100000 == 0:
                    print("grid", nboxes, counts, len(work), round(time.perf_counter() - t0), "s", flush=True)
            print("grid done", nboxes, counts, "to split", len(work) // 2, round(time.perf_counter() - t0), "s", flush=True)
            depth = 1
            while work and depth <= PARAMS["max_depth"] and nboxes < PARAMS["max_boxes"]:
                res = pool.map(process, work, chunksize=max(1, len(work) // 64))
                nxt = []
                for box, (typ, mg) in zip(work, res):
                    nboxes += 1
                    if typ == "S":
                        nxt.extend(split(box))
                    else:
                        counts[typ] = counts.get(typ, 0) + 1
                        if mg is not None:
                            margins[typ] = mg if typ not in margins else min(margins[typ], mg)
                print("depth", depth, "processed", len(work), "split", len(nxt) // 2, "counts", counts,
                      round(time.perf_counter() - t0), "s", flush=True)
                work = nxt
                depth += 1
        KK0 = setup()
        r1C, r1max = F2arb(PARAMS["r1C"]), F2arb(PARAMS["r1max"])
        s34 = arb(3).sqrt() / 2
        root_ok = bool(arb(lo0[0]) <= r1C and arb(hi0[0]) >= r1max and arb(lo0[1]) <= s34 * r1C
                       and arb(hi0[1]) >= (1 / (r1C * s34)).sqrt() and lo0[2:] == [0.0, 0.0, -0.5] and hi0[2:] == [0.5, 0.5, 0.5])
        sr = strain_regions(KK0)
        key = "strain_regions" if mode == "boxes" else "strain_region_parameters"   # in mode "all" the key
        # "strain_regions" holds the strain certificates of the strain part
        out[key] = {n: {"rho_E": PARAMS["strain"][n]["rho_E"], "rho_T": PARAMS["strain"][n]["rho_T"],
                                     "sigma_hex": [float(x).hex() for x in r["sigma"]], "gammas": r["gammas"]}
                                 for n, r in sr.items()}
        out["boxes"] = {"terminal_counts": counts, "smallest_margins": margins, "unresolved": len(work),
                        "boxes_processed": nboxes, "depth_reached": depth,
                        "root_used": [lo0, hi0], "root_built_at_prec_bits": root_prec, "root_contains_proof_root_box": root_ok}
        certified = certified and root_ok and not work
    if mode == "all":
        out["certified"] = certified
    path = run.write("lattice" + ("" if mode == "all" else "_" + mode), out)
    print("wrote", path, round(time.perf_counter() - t0), "s")
    if not certified:
        print(f"Lattice {mode} verification failed", file=sys.stderr)
    return 0 if certified else 1


if __name__ == "__main__":
    sys.exit(main())
