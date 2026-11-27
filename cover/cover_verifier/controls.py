"""Negative controls for the verifier: inputs that must be rejected, each for a stated real reason.

    python -B -m cover_verifier.controls CERTIFICATE_DIRECTORY [--bits B] [--report FILE]

Four kinds of controls:

  * every rule, with many choices of its parameters, applied through the dispatcher of the verifier to two
    boxes on which the conclusions (N), (E) and (D) are false: a box around a body-centred cubic point
    (e = e_B < e_F and Def = 0 there) and a box around a face-centred cubic point (e = e_F and Def = 0 there);
    the anchor rules may accept these boxes, but only with condition (A), which is true;
  * parameters outside the ranges that the lemmas require (alpha <= 0, a support built on a box that leaves
    {r1, r2 > 0}, t outside [0, 1], rho outside [0, 1], invalid registrations, anchors and witnesses);
  * a leaf of the certificate with one parameter changed, or with its box moved outside the hypotheses of
    its rule;
  * a certificate from which a box has been removed, or in which a containment or a cover is false
    (completeness pass).

A control that cannot be run because the certificate has no leaf of the rule counts as a failure unless
--allow-missing is given.

Each changed leaf is reported together with the outcome of the unchanged leaf, and the completeness
controls with the outcome of the unchanged files (the baselines, which must be accepted).
Exit status 0 means that every control was rejected and every baseline accepted.
"""

from argparse import ArgumentParser
import copy
from fractions import Fraction
import gzip
import json
from pathlib import Path
import sys
import tempfile

from . import boxes, rules
from .balls import e_f_upper, set_precision, upper
from .energy import ExponentialSupport
from .verify import build_support, check_leaf, completeness_pass, open_text, stage_files, subdivision

EPS = Fraction(1, 1024)
# The body-centred cubic lattice in the chart: R = identity, f = (1/2, 1/2, 1/2); a box around it inside K.
BCC_BOX = ((1 - EPS, 1 - EPS, Fraction(0), Fraction(0), -EPS, Fraction(1, 2) - EPS, Fraction(1, 2) - EPS, Fraction(1, 2) - EPS),
           (1 + EPS, 1 + EPS, EPS, EPS, EPS, Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)))


def records(path):
    with open_text(path) as stream:
        stream.readline()
        for line in stream:
            yield json.loads(line)


def find_leaf(files, rule, skip=0):
    """The first leaf with the given rule: (file, record, index, box, leaf, supports)."""
    for path in files:
        supports = {}
        for record in records(path):
            kind = record.get("t")
            if kind == "support":
                supports[record["id"]] = record
            elif kind == "forget":
                supports.clear()
            elif kind == "region" and record["leaf"][0] == rule:
                if skip:
                    skip -= 1
                    continue
                return path, record, -1, boxes.parse_box(record["box"]), record["leaf"], dict(supports)
            elif kind in ("piece", "cut"):
                names = [leaf[0] for leaf in (record["leaves"] if kind == "piece" else [p[1] for p in record["parts"]])]
                if rule in names:
                    if skip:
                        skip -= 1
                        continue
                    _, parts = subdivision(record)
                    index = names.index(rule)
                    return path, record, index, parts[index][0], parts[index][1], dict(supports)
    return None


HALF = Fraction(1, 2)
# A face-centred cubic point of the chart: r1 = r2 = 2^(-1/6) = 0.890898..., x = y = z = 0, f = (1/2, 1/2, 1/2)
# (a square lattice of side 2^(-1/6) stacked at the height 2^(1/3), with the second coset at the body centre).
FCC_BOX = ((Fraction(8908, 10000), Fraction(8908, 10000), Fraction(0), Fraction(0), -EPS, HALF - EPS, HALF - EPS, HALF - EPS),
           (Fraction(8910, 10000), Fraction(8910, 10000), EPS, EPS, EPS, HALF, HALF, HALF))
CUBIC = [[[1, 0, 0], [0, 1, 0], [0, 0, 1]], ["1/2", "1/2", "1/2"], [0, 0, 0]]     # the registration B' = I of Z^3 u (Z^3 + f0)
CENTRE = ["1/2", "1/2", "1/2"]


def battery_supports():
    """Descriptions of supports of the three kinds: (tangent, exponential, vertexmax)."""
    tangent = [["tangent", a, c, l, mix] for a, c, l in (("1", 2, "5"), ("23/20", 3, "8"), ("6/5", 2, "5"))
               for mix in ([], [[0, 4096]], [[255, 2048], [37, 1024]])]
    exponential = [["exponential", a, c, l] for a, c, l in (("1", 2, "6"), ("6/5", 2, "5"), ("6/5", 3, "7"),
                                                              ("23/20", 3, "8"), ("1", 1, "50"))]
    vertexmax = [["vertexmax", a, c, l, r, f] for a, c, l in (("1", 2, "5"), ("6/5", 3, "8"), ("6/5", 2, "50"))
                 for r in (False, True) for f in ("tangent", "exponential")]
    return tangent, exponential, vertexmax


def named_supports(box):
    """The same supports as records built on the box enlarged twice about its centre, with a leaf for each."""
    dom = enlarged(box, 2)
    records, leaves = {}, []
    for group in battery_supports():
        for spec in group:
            record = {"t": "support", "id": f"s{len(records)}", "dom": [[str(v) for v in dom[0]], [str(v) for v in dom[1]]],
                      "kind": spec[0], "alpha": spec[1], "cube": spec[2], "limit": spec[3]}
            if spec[0] == "tangent":
                record["mix"] = spec[4]
            elif spec[0] == "vertexmax":
                record["reserve"], record["form"] = spec[4], spec[5]
            records[record["id"]] = record
            tangent_form = spec[0] == "tangent" or (spec[0] == "vertexmax" and spec[5] == "tangent")
            leaves.append(["E2" if tangent_form else "E3", record["id"]])
            leaves.append(["D1", record["id"], CUBIC])
    return records, leaves


def battery_leaves():
    """Leaves of every rule with conclusion (N), (E) or (D), for many parameters inside their ranges."""
    tangent, exponential, vertexmax = battery_supports()
    for alpha in ("1", "6/5", "23/20"):
        for cube in (1, 2, 3):
            yield ["E1", alpha, cube]
    for support in tangent:
        yield ["E2", support]
    for support in exponential:
        yield ["E3", support]
    for support in vertexmax:
        yield ["E2" if support[5] == "tangent" else "E3", support]
    for support in exponential + vertexmax:
        for variant in (1, 2):
            for rho in ("0", "1/2", "1"):
                yield ["E4", support, variant, rho]
    yield ["PL"]
    for eta in (str(EPS), "1/8", "49/100"):
        yield ["PF", 0, eta]
    for support in tangent[:3] + exponential[:2] + vertexmax[:2]:
        yield ["D1", support, CUBIC]
    for support in tangent[:4]:
        for k in (0, 1, 2048, 4095, 4096):
            yield ["D3", support, CUBIC, [0, 0, 0, 1], k]
    for support in exponential[:2]:
        yield ["AS", CENTRE, [0, 0, 0], support]
    yield ["AC", CENTRE, [0, 0, 0]]
    yield ["AC", CENTRE, [0, 0, 0], CUBIC]
    for kind, m in (("full", [0, 1, 0]), ("full", [0, 0, 1]), ("full", [1, 1, 1]), ("projected", [0, 0, 1])):
        yield ["N", kind, m]
    yield ["SL", [[0, 0, "1", "full", [0, 1, 0]]], ["E3", exponential[1]]]


def invalid_leaves():
    """Leaves with a parameter outside the range that its lemma requires: (description, leaf, support records)."""
    crossing = {"t": "support", "id": "s", "kind": "vertexmax", "alpha": "1", "cube": 3, "limit": "1000", "reserve": True,
                "form": "exponential",
                "dom": [["-8"] + [str(v) for v in BCC_BOX[0][1:5]] + ["0", "0", "0"],
                        ["10"] + [str(v) for v in BCC_BOX[1][1:5]] + ["1", "1", "1"]]}
    reversed_dom = dict(crossing, dom=[crossing["dom"][1], crossing["dom"][0]])
    exponential = ["exponential", "6/5", 2, "5"]
    for alpha in ("0", "-1", "-10"):
        yield f"alpha = {alpha} in energy rule (i)", ["E1", alpha, 2], {}
        yield f"alpha = {alpha} in a tangent support", ["E2", ["tangent", alpha, 2, "50", []]], {}
        yield f"alpha = {alpha} in an exponential support", ["E3", ["exponential", alpha, 2, "50"]], {}
        yield f"alpha = {alpha} in a support with phase reserve", ["E3", ["vertexmax", alpha, 2, "50", True, "exponential"]], {}
        yield f"alpha = {alpha} in deficit rule (i)", ["D1", ["exponential", alpha, 2, "50"], CUBIC], {}
        yield f"alpha = {alpha} in anchor rule (ii)", ["AS", CENTRE, [0, 0, 0], ["exponential", alpha, 2, "50"]], {}
    yield "a support with phase reserve built on a box that crosses r1 = 0", ["E3", "s"], {"s": crossing}
    yield "a support built on a box with reversed intervals", ["E3", "s"], {"s": reversed_dom}
    yield "a support that is not defined", ["E3", "missing"], {}
    for k in (-1, 4097, 1.5, "1"):
        yield f"t = {k!r}/4096 in the joint vertex rule", ["D3", ["tangent", "1", 2, "5", []], CUBIC, [0, 0, 0, 1], k], {}
    for quaternion in ([0, 0, 0, 0], [0, 0, 1.0, 1], [0, 0, 1]):
        yield f"quaternion {quaternion}", ["D3", ["tangent", "1", 2, "5", []], CUBIC, quaternion, 2048], {}
    for rho in ("-1/2", "2"):
        yield f"rho = {rho} in the reduced variant", ["E4", exponential, 2, rho], {}
    yield "variant 3 of the reduced variant", ["E4", exponential, 3, "1/2"], {}
    for eta in ("-1/8", "1/2", "3/4"):
        yield f"eta = {eta} in planar rule (ii)", ["PF", 0, eta], {}
    yield "a non-integer translation in planar rule (ii)", ["PF", 0.5, "1/8"], {}
    double = [[[2, 0, 0], [0, 1, 0], [0, 0, 1]], ["1/2", "1/2", "1/2"], [0, 0, 0]]
    outside = [[["1/2", 0, 0], [0, 2, 0], [0, 0, 1]], ["1/2", "1/2", "1/2"], [0, 0, 0]]
    integral = [CUBIC[0], ["0", "1", "0"], [0, 0, 0]]
    thirds = [CUBIC[0], ["1/3", "1/2", "1/2"], [0, 0, 0]]
    wrong_class = [CUBIC[0], ["1/2", "0", "0"], [0, 0, 0]]
    fractional = [CUBIC[0], CUBIC[1], [0.5, 0, 0]]
    for name, registration in (("of determinant 2", double), ("with a column outside the lattice", outside),
                               ("with f0 in Z^3", integral), ("with f0 outside (1/2)Z^3", thirds),
                               ("with f0 not the half class of B'", wrong_class), ("with a non-integer n", fractional)):
        yield f"a registration {name}", ["D1", exponential, registration], {}
    for name, f0, n in (("in Z^3", ["0", "1", "0"], [0, 0, 0]), ("outside (1/2)Z^3", ["1/3", "1/2", "1/2"], [0, 0, 0]),
                        ("with a non-integer n", CENTRE, [0.5, 0, 0])):
        for rule in ("AG", "AP", "AC"):
            yield f"an anchor {name} ({rule})", [rule, f0, n], {}
    yield "the witness m = 0 of (N)", ["N", "full", [0, 0, 0]], {}
    yield "a witness of (N) of unknown kind", ["N", "partial", [0, 1, 0]], {}
    yield "a non-integer witness of (N)", ["N", "full", [0, 0.5, 0]], {}
    yield "a slab along an offset coordinate", ["SL", [[5, 0, str(HALF - EPS / 2), "full", [0, 1, 0]]], ["E3", exponential]], {}
    yield "a slab with side 2", ["SL", [[0, 2, "1", "full", [0, 1, 0]]], ["E3", exponential]], {}
    yield "a rule that does not exist", ["XX"], {}
    yield "a held leaf given to the inequality pass", ["H", "x"], {}


def battery_controls(report):
    """The first two kinds of controls; they need no certificate."""
    for name, box in (("BCC", BCC_BOX), ("FCC", FCC_BOX)):
        tally, accepted = {}, []
        records, named = named_supports(box)
        for leaf in list(battery_leaves()) + named:
            outcome, detail = run_leaf(box, leaf, records)
            if outcome == "accepted":
                accepted.append([leaf, detail])
            kind = "accepted" if outcome == "accepted" else ("inequality" if detail.startswith("Unproved") else "hypothesis")
            entry = tally.setdefault(leaf[0], {"inequality": 0, "hypothesis": 0, "accepted": 0})
            entry[kind] += 1
        report.append({"control": f"every rule with conclusion (N), (E) or (D) on a box around the {name} point "
                                  f"({sum(sum(e.values()) for e in tally.values())} leaves)",
                       "reason_it_must_fail": "the box contains a reduced point with e <= e_F and Def = 0",
                       "outcome": "accepted" if accepted else "rejected",
                       "detail": {"rejections by rule (inequality not established / hypothesis violated)": tally,
                                  "accepted": accepted}})
        for rule in ("AG", "AP"):
            def supports(spec, where):
                return build_support(spec, where)
            try:
                _, condition, margin = check_leaf(box, [rule, CENTRE, [0, 0, 0]], supports)
                outcome, detail = ("rejected" if condition == "A" else "accepted"), f"accepted with ({condition}), margin {float(margin):.3e}"
            except Exception as error:
                outcome, detail = "rejected", f"{type(error).__name__}: {error}"
            report.append({"control": f"anchor rule {rule} on the box around the {name} point: any condition other than (A)",
                           "reason_it_must_fail": "(D) and (E) are false on the box; (A) about the anchor is true",
                           "outcome": outcome, "detail": detail})
    wide = (BCC_BOX[0], BCC_BOX[1][:2] + (Fraction(3, 4),) + BCC_BOX[1][3:])
    outcome, detail = run_leaf(wide, ["E4", ["exponential", "6/5", 2, "5"], 1, "1"], {})
    report.append({"control": "reduced variant with c_1 on a box with x up to 3/4",
                   "reason_it_must_fail": "c_1 >= c_2 needs x^2 <= 1/4 (proof of Lemma 7.5(iv))", "outcome": outcome, "detail": detail})
    for description, leaf, records in invalid_leaves():
        outcome, detail = run_leaf(BCC_BOX, leaf, records)
        if outcome == "rejected" and detail.startswith("Unproved"):
            outcome = "accepted"                    # it must be the parameter that is refused, not the inequality
            detail = "the parameter was not refused: " + detail
        report.append({"control": description, "reason_it_must_fail": "the parameter is outside the range that the rule requires",
                       "outcome": outcome, "detail": detail})


def run_leaf(box, leaf, support_records):
    """Outcome of one leaf: ("accepted", margin) or ("rejected", reason)."""
    def supports(spec, where):
        return build_support(spec, where) if isinstance(spec, list) else build_support(support_records[spec])
    try:
        _, _, margin = check_leaf(box, leaf, supports)
        return "accepted", float(margin)
    except Exception as error:                     # as in the verifier: every failure is a rejection
        return "rejected", f"{type(error).__name__}: {error}"


def shifted(box, axis, amount):
    lo, hi = box
    return (lo[:axis] + (lo[axis] + amount,) + lo[axis + 1:], hi[:axis] + (hi[axis] + amount,) + hi[axis + 1:])


def other_half_class(f0):
    """f0 with 1/2 added to the first coordinate for which the result is not in Z^3."""
    f0 = [Fraction(v) for v in f0]
    for axis in range(3):
        moved = f0[:axis] + [f0[axis] + Fraction(1, 2)] + f0[axis + 1:]
        if any(v.denominator != 1 for v in moved):
            return [str(v) for v in moved]
    raise ValueError("no neighbouring half class")


def inline_exponential(record):
    """The inline description of a support record (to rebuild the support on another box)."""
    kind = record.get("kind", "tangent")
    spec = [kind, record["alpha"], record["cube"], record["limit"]]
    if kind == "tangent":
        spec.append(record["mix"])
    elif kind == "vertexmax":
        spec += [bool(record.get("reserve")), record.get("form", "tangent")]
    return spec


def negated(spec):
    """The inline description of a support with alpha replaced by -alpha."""
    spec = inline_exponential(spec) if isinstance(spec, dict) else list(spec)
    return [spec[0], str(-Fraction(spec[1]))] + spec[2:]


def enlarged(box, factor):
    mid = boxes.centre(box)
    lo = tuple(m - factor * (m - a) for m, a in zip(mid, box[0]))
    hi = tuple(m + factor * (b - m) for m, b in zip(mid, box[1]))
    return lo, hi


def arithmetic_controls(files, report):
    def note(name, why, outcome, detail):
        report.append({"control": name, "reason_it_must_fail": why, "outcome": outcome, "detail": detail})

    # 1. the conclusion (E) is false on a box that contains the body-centred cubic lattice
    support = ExponentialSupport(BCC_BOX, Fraction(6, 5), 2, Fraction(5))
    value = support.energy_lower(BCC_BOX)
    note("energy rule on a box containing BCC", "e = e_B < e_F at a point of the box, so no lower bound can exceed e_F",
         "rejected" if upper(value - e_f_upper()) < 0 else "accepted", f"E_- - e_F^+ = {float(value - e_f_upper()):.3e}")
    for kind, m in (("full", (0, 1, 0)), ("full", (0, 0, 1)), ("projected", (0, 0, 1)), ("full", (1, 0, 0))):
        try:
            rules.rule_n(BCC_BOX, kind, m)
            outcome, detail = "accepted", ""
        except rules.Rejected as error:
            outcome, detail = "rejected", str(error)
        note(f"(N) with {kind} {m} on a box containing BCC", "the shape (1,1,0,0,0) of the box is reduced", outcome, detail)

    # 2. leaves of the certificate with one parameter changed or with the box moved
    supports_of = [{}]
    found_leaves = {}

    def mutate(rule, name, why, change, skip=0, keep=None):
        if rule not in found_leaves:
            found_leaves[rule] = find_leaf(files, rule)
        found = found_leaves[rule]
        if found is None:
            report.append({"control": f"{name} ({rule})", "reason_it_must_fail": why, "outcome": "not run",
                           "detail": "the certificate has no leaf of this rule"})
            return
        path, record, index, box, leaf, supports = found
        if keep is not None:
            keep[0] = supports
        original = run_leaf(box, leaf, supports)
        new_box, new_leaf = change(box, copy.deepcopy(leaf))
        outcome, detail = run_leaf(new_box, new_leaf, supports)
        result = outcome if original[0] == "accepted" else "original rejected"
        note(f"{name} ({rule} leaf of {path.name}, {record['id']}, leaf {index})", why, result,
             {"unchanged_leaf": original, "changed_outcome": outcome, "changed_leaf": detail})

    mutate("D3", "trial rotation replaced by the identity",
           "with a wrong rotation the trial cost 100|A - U|^2 is large and the joint inequality is false at a vertex",
           lambda box, leaf: (box, leaf[:3] + [[0, 0, 0, 1]] + leaf[4:]))
    mutate("D3", "registration translated by e_1",
           "the displacement h = R(f - f0 - n) then has length about 1 and the cost exceeds every bound",
           lambda box, leaf: (box, leaf[:2] + [[leaf[2][0], leaf[2][1], [leaf[2][2][0] + 1] + leaf[2][2][1:]]] + leaf[3:]))
    mutate("D1", "registration translated by e_1", "the defect bound is then not below one",
           lambda box, leaf: (box, leaf[:2] + [[leaf[2][0], leaf[2][1], [leaf[2][2][0] + 1] + leaf[2][2][1:]]]))
    mutate("E3", "alpha replaced by -alpha",
           "the series (7.2) holds for alpha > 0 only; with a negative alpha the direct terms change sign and the constant grows",
           lambda box, leaf: (box, [leaf[0], negated(supports_of[0][leaf[1]] if isinstance(leaf[1], str) else leaf[1])]),
           keep=supports_of)
    mutate("E1", "alpha replaced by -alpha", "the series (7.2) holds for alpha > 0 only",
           lambda box, leaf: (box, [leaf[0], str(-Fraction(leaf[1])), leaf[2]]))
    mutate("E2", "box enlarged eight times about its centre",
           "the support is valid only inside the box on which it was built",
           lambda box, leaf: (enlarged(box, 8), leaf))
    mutate("E3", "box enlarged sixteen times about its centre",
           "the support is valid only inside the box on which it was built (term set and phase chords are those of that box)",
           lambda box, leaf: (enlarged(box, 16), leaf))
    mutate("E3", "the support rebuilt on the box enlarged four times",
           "base points at the centre of a box four times as wide: the lower bound at the far vertices is below e_F",
           lambda box, leaf: (enlarged(box, 4), [leaf[0], inline_exponential(supports_of[0][leaf[1]])
                                                 if isinstance(leaf[1], str) else leaf[1]]), keep=supports_of)
    mutate("E1", "box enlarged twice about its centre",
           "the partial sum with interval bounds over the larger box is below e_F",
           lambda box, leaf: (enlarged(box, 2), leaf))
    mutate("E4", "rho replaced by 2", "Lemma 7.5(iv) needs 0 <= rho <= 1 (the coefficient of r1^2 must stay nonnegative)",
           lambda box, leaf: (box, leaf[:3] + ["2"]))
    mutate("E4", "the reduced term dropped (rule (iii) with the same support)",
           "without the term lambda c of Lemma 7.5(iv) the support is not above e_F on this box",
           lambda box, leaf: (box, ["E3", leaf[1]]))
    mutate("SL", "the witness of the first slab replaced by m = (1, 1, 1)",
           "the inequality (4.2) for m = (1,1,1) is not violated on the slab, so the slab does not satisfy (N)",
           lambda box, leaf: (box, [leaf[0], [leaf[1][0][:3] + ["full", [1, 1, 1]]] + leaf[1][1:], leaf[2]]))
    mutate("SL", "the first slab moved outside the box", "a slab must be cut off by a plane through the interior of the box",
           lambda box, leaf: (box, [leaf[0], [leaf[1][0][:2] + [str(box[1][leaf[1][0][0]] + 1)] + leaf[1][0][3:]] + leaf[1][1:],
                                    leaf[2]]))
    mutate("N", "integer vector replaced by (1, 1, 1)", "the inequality (4.2) for m = (1,1,1) is not violated on the box",
           lambda box, leaf: (box, ["N", "full", [1, 1, 1]]))
    mutate("PF", "box moved by 1/4 in f_3", "the box leaves the band |f_3 - 1/2| <= eta of the fibre bound",
           lambda box, leaf: (shifted(box, 7, Fraction(1, 4)), leaf))
    mutate("PL", "box enlarged sixteen times about its centre",
           "the enlarged box contains planes f_3 in Z, where the two cosets share their layers: no band eta <= f_3 <= 1 - eta",
           lambda box, leaf: (enlarged(box, 16), leaf))
    mutate("AP", "anchor translated by e_3", "|delta_3| >= 1/2: outside the hypotheses of the planar gain",
           lambda box, leaf: (box, [leaf[0], leaf[1], leaf[2][:2] + [leaf[2][2] + 1]]))
    mutate("AG", "anchor replaced by a neighbouring point of (1/2)Z^3",
           "about a point of (1/2)Z^3 at distance 1/2 from the right one the quadratic form is not positive on the box",
           lambda box, leaf: (box, [leaf[0], other_half_class(leaf[1]), leaf[2]]))
    mutate("AG", "anchor replaced by a point of Z^3", "an anchor must lie in (1/2)Z^3 outside Z^3 (the energy is infinite on Z^3)",
           lambda box, leaf: (box, [leaf[0], ["0", "0", "0"], leaf[2]]))
    mutate("AS", "box moved by 1/2 in f_1",
           "at this distance from the anchor the loss of the quadratic form exceeds the deficit of the anchor",
           lambda box, leaf: (shifted(box, 5, Fraction(1, 2)), leaf))
    mutate("AC", "anchor translated by e_3", "|delta_3| >= 1/2: outside the hypotheses of the planar gain",
           lambda box, leaf: (box, [leaf[0], leaf[1], leaf[2][:2] + [leaf[2][2] + 1]] + leaf[3:]))
    mutate("AG", "box moved by 1/2 in f_1",
           "at this distance from the anchor the quadratic form of Lemma C.3 is not positive (its fourth-order losses grow with the box)",
           lambda box, leaf: (shifted(box, 5, Fraction(1, 2)), leaf))


def reflection_controls(attempt, baseline, workdir):
    """A chain of three small files around the reflection step, and four mutations of it.

    File 1 bisects K at f1 = 0 and holds both halves; file 2 is the reflection step, after which the held
    set is {K n {f1 >= 0}}; file 3 replaces that box by a tree all of whose leaves name a rule.  (The
    completeness pass does not evaluate rules, so the leaves of file 3 are only placeholders.)
    """
    lo, hi = boxes.K_BOX
    k_box = [[str(v) for v in lo], [str(v) for v in hi]]
    upper_half = [[str(v) for v in lo[:5] + (Fraction(0),) + lo[6:]], k_box[1]]
    header = {"format": "cover-certificate-1"}
    first = [header, {"t": "piece", "id": "K", "box": k_box, "tree": "5..", "leaves": [["H"], ["H"]]}, {"t": "end", "held": 2}]
    mirror = [dict(header, step="mirror")]
    third = [header, {"t": "piece", "id": "half", "box": upper_half, "from": [upper_half], "tree": "0..",
                      "leaves": [["PL"], ["PL"]]}, {"t": "end", "held": 0}]

    def write(label, *contents):
        target = workdir / label
        target.mkdir()
        paths = []
        for number, content in enumerate(contents, 1):
            path = target / f"stage{number:02d}.jsonl"
            path.write_text("".join(json.dumps(record) + "\n" for record in content), encoding="utf-8", newline="\n")
            paths.append(path)
        return paths

    def full(paths):                                   # these chains start from K: no partial run
        def run():
            completeness_pass(paths, lambda text: None)
        return run

    baseline("K bisected at f1 = 0, reflection step, the upper half replaced", full(write("r0", first, mirror, third)))
    attempt("a second reflection step", "after a reflection step only the weaker covering property holds, "
            "from which a second step does not follow", full(write("r1", first, mirror, mirror, third)))
    whole = [header, {"t": "piece", "id": "K", "box": k_box, "tree": ".", "leaves": [["H"]]}, {"t": "end", "held": 1}]
    attempt("reflection step with a held box that crosses f1 = 0", "the step pairs boxes of {f1 >= 0} with boxes of {f1 <= 0}",
            full(write("r2", whole, mirror, third)))
    lower_half = [k_box[0], [str(v) for v in hi[:5] + (Fraction(0),) + hi[6:]]]
    wrong = [header, dict(third[1], box=lower_half), {"t": "end", "held": 0}]
    attempt("after the reflection step a piece whose box does not contain the held box it replaces",
            "a held box may be replaced only by a tree on a box that contains it", full(write("r3", first, mirror, wrong)))
    attempt("the reflection step left out", "the two halves of K are then held and are not received by the last file",
            full(write("r4", first, third)))


def completeness_controls(files, report, baselines, workdir):
    """Mutated copies of the two smallest consecutive stage files; the completeness pass must fail."""
    def attempt(name, why, paths):
        try:
            if callable(paths):
                paths()
            else:
                completeness_pass(paths, lambda text: None, partial=True, require_empty=True)
            outcome, detail = "accepted", ""
        except Exception as error:
            outcome, detail = "rejected", str(error)
        report.append({"control": name, "reason_it_must_fail": why, "outcome": outcome, "detail": detail})

    def baseline(name, paths, require_empty=True):
        try:
            if callable(paths):
                paths()
            else:
                completeness_pass(paths, lambda text: None, partial=True, require_empty=require_empty)
            outcome, detail = "accepted", ""
        except Exception as error:
            outcome, detail = "rejected", str(error)
        baselines.append({"baseline": name, "outcome": outcome, "detail": detail})

    last_two = files[-2:]
    lines = [list(open_text(p)) for p in last_two]
    baseline("the last two stage files, unchanged", last_two)
    reflection_controls(attempt, baseline, Path(workdir))

    def write(index, new_lines, label):
        target = Path(workdir) / label
        target.mkdir()
        out = []
        for k, path in enumerate(last_two):
            copy_path = target / path.name
            with (gzip.open(copy_path, "wt", encoding="utf-8", newline="\n") if path.name.endswith(".gz")
                  else open(copy_path, "wt", encoding="utf-8", newline="\n")) as stream:
                stream.writelines(new_lines if k == index else lines[k])
            out.append(copy_path)
        return out

    # a piece removed from the last file
    position = next(i for i, line in enumerate(lines[1]) if '"t":"piece"' in line)
    attempt("one piece removed from the last file", "a held box of the preceding file is then discharged by nothing",
            write(1, lines[1][:position] + lines[1][position + 1:], "removed"))
    # a discharged leaf of the last file turned into a held leaf
    record = json.loads(lines[1][position])
    record["leaves"][0] = ["H"]
    end = [json.dumps({"t": "end", "held": 1}) + "\n"]
    attempt("a discharged leaf of the last file declared held", "the last file then holds a box",
            write(1, lines[1][:position] + [json.dumps(record) + "\n"] + lines[1][position + 1:-1] + end, "held"))
    # a piece of the last file shrunk
    record = json.loads(lines[1][position])
    lo, hi = record["box"]
    hi = list(hi)
    hi[0] = str((Fraction(lo[0]) + Fraction(hi[0])) / 2)
    record["box"] = [lo, hi]
    attempt("a piece of the last file replaced by its lower half in r1", "the box is not one of the held boxes",
            write(1, lines[1][:position] + [json.dumps(record) + "\n"] + lines[1][position + 1:], "shrunk"))
    # a bisection tree with a missing half
    position0 = next(i for i, line in enumerate(lines[0]) if '"t":"piece"' in line and len(json.loads(line)["tree"]) > 1)
    record = json.loads(lines[0][position0])
    record["tree"] = record["tree"][:-1]
    record["leaves"] = record["leaves"][:-1]
    attempt("the last leaf of a bisection tree removed", "a bisection must keep both closed halves",
            write(0, lines[0][:position0] + [json.dumps(record) + "\n"] + lines[0][position0 + 1:], "tree"))
    # containment in a region and exact covers
    for path in files:
        seen_regions = {}
        for record in records(path):
            if record.get("t") == "region":
                seen_regions[record["id"]] = record
            elif record.get("t") == "cut":
                target = Path(workdir) / "cut"
                target.mkdir(exist_ok=True)

                def run(name, why, changed, regions):
                    copy_path = target / (name.replace(" ", "_") + ".jsonl")
                    with open(copy_path, "wt", encoding="utf-8", newline="\n") as stream:
                        stream.write(json.dumps({"format": "cover-certificate-1"}) + "\n")
                        for region in regions:
                            stream.write(json.dumps(region) + "\n")
                        stream.write(json.dumps(changed) + "\n")
                        stream.write(json.dumps({"t": "end", "held": sum(p[1][0] == "H" for p in changed["parts"])}) + "\n")
                    attempt(name, why, [copy_path])

                used = [seen_regions[p[1][1]] for p in record["parts"] if p[1][0] == "IN"]
                held = [k for k, part in enumerate(record["parts"]) if part[1][0] == "H"]
                if not held:
                    continue
                smaller = dict(record, parts=record["parts"][:held[0]] + record["parts"][held[0] + 1:])
                run("one held part removed from an exact cut", "the remaining parts do not cover the box", smaller, used)
                if used:
                    moved = copy.deepcopy(used)
                    moved[0]["box"][0][5] = str(Fraction(moved[0]["box"][0][5]) + 3)
                    moved[0]["box"][1][5] = str(Fraction(moved[0]["box"][1][5]) + 3)
                    run("a region moved by 3 in f_1", "the clip is not contained in the image of the region", record, moved)
                return


def main(argv=None):
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--bits", type=int, default=128)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--allow-missing", action="store_true",
                        help="do not count as failures the controls for rules of which the certificate has no leaf")
    args = parser.parse_args(argv)
    set_precision(args.bits)
    files = stage_files(args.certificate)
    report, baselines = [], []
    battery_controls(report)
    arithmetic_controls(files, report)
    with tempfile.TemporaryDirectory() as workdir:
        completeness_controls(files, report, baselines, workdir)
    failures = skipped = 0
    for entry in baselines:
        ok = entry["outcome"] == "accepted"
        failures += not ok
        print(("ok   " if ok else "BAD  ") + "baseline: " + entry["baseline"] + ": " + entry["outcome"] + " " + entry["detail"], flush=True)
    bad_baselines = failures
    for entry in report:
        if entry["outcome"] == "not run":
            skipped += 1
            failures += not args.allow_missing
            print("SKIP " + entry["control"] + ": " + entry["detail"], flush=True)
            continue
        ok = entry["outcome"] == "rejected"
        failures += not ok
        print(("ok   " if ok else "BAD  ") + entry["control"] + ": " + entry["outcome"], flush=True)
        print("       reason: " + entry["reason_it_must_fail"], flush=True)
        print("       detail: " + json.dumps(entry["detail"]), flush=True)
    done = len(report) - skipped
    passed = sum(entry["outcome"] == "rejected" for entry in report)
    print(f"{done} controls run, {passed} rejected as required; {skipped} not run; "
          f"{len(baselines)} baselines, {len(baselines) - bad_baselines} accepted", flush=True)
    if args.report:
        args.report.write_text(json.dumps({"bits": args.bits, "baselines": baselines, "controls": report}, indent=1) + "\n",
                               encoding="utf-8", newline="\n")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
