"""Generate the eight-dimensional local charts of Section 6 (Theorem 6.2) using radial Taylor bounds.

All mathematical decisions use rational arithmetic or arb, never floats.
Each ellipsoid is certified as a whole, with all Ewald derivative tails.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import os
import sys

from flint import arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bccnum.chart_atlas import GramChart, atlas_check, central_cubic, derivative_tail
from bccnum.two_site import symmetry_classes
from bccnum.intervals import arb_record
from bccnum.provenance import Run


def inputs():
    path = os.path.join(HERE, "results", "constants.json")
    with open(path, "rb") as handle:
        raw = handle.read()                     # hashed and parsed from the same bytes
    data = json.loads(raw)["results"]["energies"]
    def energy(name):
        d = data[name]["e_ws_certified"]
        return arb(d["lower"]).union(arb(d["upper"]))
    return energy("bcc"), energy("fcc"), {"path": "results/constants.json", "sha256": hashlib.sha256(raw).hexdigest()}


def serialize(value):
    if isinstance(value, arb):
        return arb_record(value)
    if isinstance(value, dict):
        return {str(k): serialize(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serialize(x) for x in value]
    return value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prec", type=int, default=160)
    parser.add_argument("--n0", type=int, default=8)
    parser.add_argument("--grid-denominator", type=int, default=10000)
    parser.add_argument("--max-radius", default="3/100")
    parser.add_argument("--output", default="local_charts")
    args = parser.parse_args(); ctx.prec = args.prec
    if args.n0 < 1 or args.grid_denominator < 1:
        raise ValueError("positive truncation and grid denominator required")
    max_radius = F(args.max_radius)
    if not 0 < max_radius <= F(1, 20):
        raise ValueError("max radius must be in (0,1/20]")
    eb, ef, source = inputs(); gap = ef - eb
    assert gap > 0
    scale_choices = {("bcc", (0, 0, 1)): [F(1, 3), F(1, 2), F(2, 3), F(1)],
                     ("bcc", (1, 1, 1)): [F(1, 8), F(1, 4), F(1, 2), F(1)],
                     ("fcc", (0, 0, 1)): [F(1, 4), F(1, 3), F(1, 2), F(1)],
                     ("fcc", (0, 1, 1)): [F(1, 6), F(1, 4), F(1, 2), F(1)]}
    params = {"precision_bits": args.prec, "n0": args.n0, "grid_denominator": args.grid_denominator,
              "max_radius": str(max_radius), "inputs": source, "random_seed": None,
              "chart": "C=det(I+S)^(-1/3)(I+S); A=sqrt(C); X=a_c A (B'Z^3 union (B'Z^3+B'f0+u))",
              "domain": "||S||_F^2 + |u/optical_scale|^2 <= radius^2",
              "eigenvalue_method": "28 exact rational bisections with enclosing arb LDL pivots; no float proposals",
              "radius_search": "integer bisection over rational grid, records every attempted check; only successful domains asserted",
              "interpreter": os.path.basename(sys.executable)}
    run = Run(__file__, params, "cert", seeds=None,
              inputs={source["path"]: (os.path.join(HERE, "results", "constants.json"), source["sha256"])})
    records, symmetry = [], {}
    for name in ("bcc", "fcc"):
        rows, classes = symmetry_classes(name); symmetry[name] = classes
        for cls in classes:
            representative = cls["representative"]
            row = next(x for x in rows if x["character"] == representative)
            chart = GramChart(row)
            J, tails, _ = chart.energy_jet([arb(0)] * 8, args.n0)
            assert J.v.overlaps(eb if name == "bcc" else ef)
            assert all(x.contains(0) for x in J.g)
            ellipsoids = []
            for scale in scale_choices[(name, representative)]:
                cubic, cubic_norm = central_cubic(chart, args.n0, scale)
                t3 = derivative_tail(chart, F(0), args.n0, scale, 3)
                lo, hi = 1, int(max_radius * args.grid_denominator)
                attempts = []; best = None
                while lo <= hi:
                    mid = (lo + hi) // 2; radius = F(mid, args.grid_denominator)
                    checked = atlas_check(chart, J.h, cubic_norm, t3, radius, scale, gap, args.n0)
                    attempts.append({"radius": str(radius), **checked})
                    if checked["certified"]:
                        best = {"radius": str(radius), "optical_scale": str(scale),
                                "optical_radius": str(radius * scale), **checked}
                        lo = mid + 1
                    else:
                        hi = mid - 1
                assert best is not None, (name, representative, scale)
                best["attempts"] = attempts
                best["finite_cubic_monomials"] = [{"powers": list(p), "coefficient": c} for p, c in sorted(cubic.items())]
                ellipsoids.append(best)
                print("atlas", name, representative, "scale", scale, "radius", best["radius"],
                      "optical", best["optical_radius"], "margin", best["objective_per_norm_squared_lower"], flush=True)
            # Ellipsoid axes are r on five strain coordinates and r*h on three
            # optical coordinates, so componentwise comparison proves inclusion.
            active = []
            for i, e in enumerate(ellipsoids):
                r, u = F(e["radius"]), F(e["optical_radius"])
                dominated = any(j != i and F(other["radius"]) >= r and F(other["optical_radius"]) >= u and
                                (F(other["radius"]) > r or F(other["optical_radius"]) > u)
                                for j, other in enumerate(ellipsoids))
                e["contained_in_another_ellipsoid"] = dominated
                if not dominated:
                    active.append(i)
            common_ball = max(min(F(e["radius"]), F(e["optical_radius"])) for e in ellipsoids)
            records.append({"name": name, "representative": representative, "members": cls["members"],
                            "reference_period": row["period"], "period_scale": "2^(1/3)" if name == "fcc" else "1",
                            "fractional_offset": row["offset"], "center_energy": J.v,
                            "center_hessian_lower_triangle": [[J.h[i][j] for j in range(i + 1)] for i in range(8)],
                            "center_value_gradient_hessian_tails": tails,
                            "ellipsoids": ellipsoids, "nondominated_ellipsoid_indices": active,
                            "common_euclidean_eight_ball_radius": str(common_ball)})
    result = {"status": "certified in ball arithmetic (Section 9.1 of the paper)",
              "global_theorem_proved": False, "e_bcc": eb, "e_fcc": ef, "gap": gap,
              "exact_symmetry_classes": symmetry, "eight_dimensional_atlas": records,
              "conclusion": "e(X)-e_bcc >= (e_fcc-e_bcc) D(X) on every listed complete ellipsoid; all fourteen representations covered by exact orthogonal symmetry",
              "membership": "C=B'^(-T) R^T R B'^(-1); S=3C/tr(C)-I; u=B'(f-f0-n); require ||S||F^2+|u/optical_scale|^2 <= radius^2 after the exact period basis witness",
              "limitation": "A union of local neighborhoods only. No global compact-set coverage asserted."}
    print(run.write(args.output, serialize(result)), flush=True)


if __name__ == "__main__":
    main()
