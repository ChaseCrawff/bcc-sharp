"""Refine a certificate where the verifier rejects a leaf.

    python -B -m cover_verifier.refine CERTIFICATE_DIRECTORY RECEIPT OUTPUT_DIRECTORY [--depth D] [--workers N]

For every leaf of a piece that RECEIPT lists as rejected this program looks for a replacement that the
verifier accepts: first another rule on the same box (for an anchor leaf the other anchor rules about the
same anchor; for an energy or planar leaf a witness of (N) with a small integer vector, energy rule (iii)
with one of four standard supports built on the box, its reduced variant (iv), and the anchor rules about
the nearest point of (1/2)Z^3), then a bisection of the box, up to depth D, with the same search on both closed halves.  The certificate is written to
OUTPUT_DIRECTORY with these leaves replaced by what was found.

The program proves nothing.  Its output is a certificate like any other and has to be verified; the only
facts it relies on are that a box whose two closed halves are discharged is covered by discharged boxes,
and that the verifier decides.
"""

from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from fractions import Fraction
import gzip
from itertools import product
import json
from pathlib import Path
import re
import sys

from . import boxes, rules
from .balls import set_precision
from .verify import build_support, check_leaf, open_text, referenced_supports, stage_files

WEIGHTS = (3, 3, Fraction(3, 2), 1, 1, 1, 1, 1)      # preference for bisecting the coordinates r1, r2, x
STANDARD = (["exponential", "6/5", 2, "5"], ["exponential", "6/5", 3, "7"],
            ["exponential", "23/20", 3, "8"], ["exponential", "1", 2, "6"])
# candidates for a witness of (N): the vectors of {-1,0,1}^3 up to sign, and four pairs (m2, m3) for (4.3)
WITNESSES = tuple([("projected", (0, a, b)) for a, b in ((0, 1), (1, 0), (1, 1), (1, -1))]
                  + [("full", m) for m in product((0, 1), (-1, 0, 1), (-1, 0, 1)) if m > (0, 0, 0)])
ERRORS = (Exception,)                                # the verifier treats every failure as a rejection
PIECE = re.compile(r'\{"t":"piece","id":"([^"]*)"')


def piece_identifier(line):
    """The identifier if the line is a piece record, else None (without parsing the usual lines)."""
    if line.startswith('{"t":"'):
        match = PIECE.match(line)
        return match.group(1) if match else None
    record = json.loads(line)
    return record.get("id") if record.get("t") == "piece" else None


def restricted(leaf, box):
    """A leaf with slabs (Lemma 7.2(iii)) written for a larger box, adapted to the sub-box ``box``: a slab
    whose plane does not cut the remaining box is dropped if the remaining box lies outside it, and ends
    the list with its witness of (N) if the remaining box lies inside it."""
    if leaf[0] != "SL":
        return leaf
    lo, hi = box
    slabs = []
    for slab in leaf[1]:
        axis, side, value, kind, m = slab
        value = Fraction(value)
        inside = hi[axis] <= value if side == 0 else lo[axis] >= value
        outside = lo[axis] >= value if side == 0 else hi[axis] <= value
        if inside:
            return ["SL", slabs, ["N", kind, m]] if slabs else ["N", kind, m]
        if outside:
            continue
        slabs.append(slab)
        if side == 0:
            lo = lo[:axis] + (value,) + lo[axis + 1:]
        else:
            hi = hi[:axis] + (value,) + hi[axis + 1:]
    return ["SL", slabs, leaf[2]] if slabs else leaf[2]


def anchor_leaves(f0, n, skip=None):
    """The anchor rules about the anchor (f0, n); the planar gain needs f0_3 in 1/2 + Z."""
    planar = Fraction(f0[2]).denominator == 2
    for name in ("AG", "AP", "AC", "AS"):
        if name != skip and (planar or name in ("AG", "AS")):
            yield [name, f0, n] + ([STANDARD[0]] if name == "AS" else [])


def alternatives(leaf, box):
    """The leaves to try on ``box`` in place of a rejected leaf, the leaf itself first."""
    yield leaf
    rule = leaf[0]
    if rule == "SL":
        lo, hi = box
        for axis, side, value, _, _ in leaf[1]:                    # the box that remains after the slabs
            value = Fraction(value)
            lo, hi = (lo[:axis] + (value,) + lo[axis + 1:], hi) if side == 0 else (lo, hi[:axis] + (value,) + hi[axis + 1:])
        for inner in alternatives(leaf[2], (lo, hi)):
            if inner is not leaf[2]:
                yield ["SL", leaf[1], inner]
    elif rule in ("AG", "AS", "AP", "AC"):
        yield from anchor_leaves(leaf[1], leaf[2], skip=rule)
    elif rule in ("PL", "PF", "E1", "E2", "E3", "E4"):
        for kind, m in WITNESSES:                                   # the box may contain no reduced point
            yield ["N", kind, list(m)]
        for spec in STANDARD:                                       # the standard supports, built on the box itself
            if rule != "E3" or spec != leaf[1]:
                yield ["E3", spec]
        for spec in STANDARD[:2]:                                   # the reduced variant of Lemma 7.5(iv)
            for variant in (2, 1):
                for rho in ("1", "1/2"):
                    yield ["E4", spec, variant, rho]
        # the anchor rules about the point of (1/2)Z^3 nearest to the centre of the offset box
        f0 = [Fraction(round(a + b), 2) for a, b in zip(box[0][5:], box[1][5:])]
        if any(v.denominator == 2 for v in f0):
            yield from anchor_leaves([str(v) for v in f0], [0, 0, 0])


def search(box, leaf, supports, depth, axes):
    """(tree, leaves): a bisection tree of ``box`` and one accepted leaf for each of its parts, or None."""
    leaf = restricted(leaf, box)
    for candidate in alternatives(leaf, box):
        try:
            check_leaf(box, candidate, supports)
            return ".", [candidate]
        except ERRORS:
            continue
    if depth == 0:
        return None
    lo, hi = box
    order = sorted((i for i in range(8) if hi[i] > lo[i]), key=lambda i: -WEIGHTS[i] * (hi[i] - lo[i]))
    for axis in order[:axes]:
        tree, leaves = str(axis), []
        for half in boxes.bisect(box, axis):
            found = search(half, leaf, supports, depth - 1, axes)
            if found is None:
                break
            tree += found[0]
            leaves += found[1]
        else:
            return tree, leaves
    return None


def refine_piece(job):
    """Worker: one piece with the indices of its rejected leaves -> (new JSON line, changes, failed indices)."""
    bits, piece, indices, support_records, depth, axes = job
    set_precision(bits)
    built = {}

    def supports(spec, box):
        if isinstance(spec, list):
            return build_support(spec, box)
        if spec not in built:
            built[spec] = build_support(support_records[spec])
        return built[spec]

    box = boxes.parse_box(piece["box"])
    leaf_boxes = boxes.tree_leaves(box, piece["tree"])
    positions = [i for i, symbol in enumerate(piece["tree"]) if symbol == "."]
    tree, leaves, recorded = list(piece["tree"]), [], []
    old_recorded = piece.get("recorded") or [None] * len(piece["leaves"])
    changes, failed = Counter(), []
    for index, (leaf, note) in enumerate(zip(piece["leaves"], old_recorded)):
        found = search(leaf_boxes[index], leaf, supports, depth, axes) if index in indices else None
        if found is None:
            if index in indices:
                failed.append(index)
            found = (".", [leaf])
        elif index in indices:
            names = sorted({new[0] if new[0] != "SL" else "SL+" + new[2][0] for new in found[1]})
            changes[f"{leaf[0]} -> {'/'.join(names)} in {len(found[1])} part(s)"] += 1
        tree[positions[index]] = found[0]
        leaves.extend(found[1])
        recorded.extend([note] * len(found[1]))
    piece = dict(piece, tree="".join(tree), leaves=leaves)
    if "recorded" in piece:
        piece["recorded"] = recorded
    return piece["id"], json.dumps(piece, separators=(",", ":")) + "\n", changes, failed


def main(argv=None):
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--axes", type=int, default=2, help="number of coordinates tried for each bisection")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args(argv)
    receipt = json.loads(args.receipt.read_text(encoding="utf-8"))
    files = stage_files(args.certificate)
    inputs = [*files, args.receipt]
    for path in files:
        target = args.output / path.name
        if target.exists() and any(target.samefile(source) for source in inputs):
            parser.error(f"output {target} aliases an input file")
    args.output.mkdir(parents=True, exist_ok=True)
    unresolved = 0
    for path in files:
        wanted = {}
        for piece, index, _, _ in receipt["rejected"].get(path.name, []):
            wanted.setdefault(piece, set()).add(index)
        target = args.output / path.name
        if not wanted:
            target.write_bytes(path.read_bytes())
            continue
        # first pass: search replacements for the pieces with rejected leaves
        new_lines, changes, support_records = {}, Counter(), {}

        def collect(result):
            nonlocal unresolved
            identifier, line, part, failed = result
            new_lines[identifier] = line
            changes.update(part)
            unresolved += len(failed)
            for index in failed:
                print(f"{path.name}: piece {identifier} leaf {index}: no replacement found", flush=True)

        with open_text(path) as source, ProcessPoolExecutor(args.workers) as pool:
            pending = set()
            for line in source:
                if not line.startswith(('{"t":"support"', '{"t":"forget"')) and piece_identifier(line) not in wanted:
                    continue
                record = json.loads(line)
                kind = record.get("t")
                if kind == "support":
                    support_records[record["id"]] = record
                elif kind == "forget":
                    support_records.clear()
                elif kind == "piece" and record["id"] in wanted:
                    needed = {sid: support_records[sid] for sid in referenced_supports(record)}
                    pending.add(pool.submit(refine_piece, (receipt["bits"], record, wanted[record["id"]], needed,
                                                           args.depth, args.axes)))
                    if len(pending) >= 4 * args.workers:
                        done, pending = wait(pending, return_when=FIRST_COMPLETED)
                        for future in done:
                            collect(future.result())
            for future in pending:
                collect(future.result())
        missing = set(wanted) - set(new_lines)
        for identifier in sorted(missing):
            unresolved += len(wanted[identifier])
            print(f"{path.name}: {identifier}: not a piece; its rejected leaf is left as it is", flush=True)
        # second pass: copy the file with the refined pieces replaced
        opener = gzip.open if target.name.endswith(".gz") else open
        with open_text(path) as source, opener(target, "wt", encoding="utf-8", newline="\n") as sink:
            for line in source:
                sink.write(new_lines.get(piece_identifier(line), line))
        print(f"{path.name}: {len(new_lines)} pieces refined: {dict(sorted(changes.items()))}", flush=True)
    print("unresolved leaves:", unresolved)
    return 1 if unresolved else 0


if __name__ == "__main__":
    sys.exit(main())
