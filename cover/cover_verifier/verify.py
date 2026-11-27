"""Verify a flat certificate of the cover (Theorem 7.3 of the paper).

    python -B -m cover_verifier.verify CERTIFICATE_DIRECTORY [--workers N] [--bits B] [--receipt FILE]

Two passes over the files ``stageNN.jsonl[.gz]`` in the order of their names:

(a) completeness, in exact rational arithmetic, in the main process: every bisection tree is complete,
    every cut is a cover, the pieces of each stage are the held leaves of the preceding stage, the first
    stage starts from the box K of (4.5), and the last stage holds nothing;
(b) inequalities, in ball arithmetic, in worker processes: every leaf that is not held proves its box
    discharged by the rule it names.

The format of the files is described in FORMAT.md.  The receipt holds the SHA-256 of the modules of the verifier
and of the files, taken at the start and again at the end of the run; a run during which they change fails.
Exit status 0 means that both passes succeeded.
"""

from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from fractions import Fraction
import gzip
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import sys
import time

from . import boxes, defect, rules
from .balls import set_precision
from .energy import ExponentialSupport, TangentSupport, VertexMaxSupport

FORMAT = "cover-certificate-1"


def open_text(path):
    return gzip.open(path, "rt", encoding="utf-8") if str(path).endswith(".gz") else open(path, "rt", encoding="utf-8")


def stage_files(directory):
    files = sorted(p for p in Path(directory).iterdir() if p.name.startswith("stage") and ".jsonl" in p.name)
    if not files:
        raise SystemExit("no stage files found")
    return files


# ---------------------------------------------------------------------------------------------
# (b) inequalities
# ---------------------------------------------------------------------------------------------
SUPPORT_RULES = ("E2", "E3", "E4", "D1", "D3")


def subdivision(record):
    """The boxes into which a ``piece`` or ``cut`` record divides its box, each with its leaf.

    A piece is divided by its bisection tree.  A cut lists boxes with arbitrary rational endpoints; that
    they cover the box of the record is checked in the completeness pass.
    """
    box = boxes.parse_box(record["box"])
    boxes.check_shape_part(box)
    if record["t"] == "cut":
        parts = [(boxes.parse_box(part), leaf) for part, leaf in record["parts"]]
        for part, _ in parts:
            if not boxes.contains(box, part):
                raise ValueError(f"cut {record['id']}: a part leaves the box")
        return box, parts
    leaf_boxes = boxes.tree_leaves(box, record["tree"])
    if len(leaf_boxes) != len(record["leaves"]):
        raise ValueError(f"piece {record['id']}: the number of leaves differs from the tree")
    return box, list(zip(leaf_boxes, record["leaves"]))


def build_support(record, box=None):
    """The support object of a ``support`` record, or of an inline description
    [kind, alpha, cube, limit, ...] whose box ``dom`` is the box of the leaf that carries it.

    kind "tangent":      Lemma 7.5(ii); needs the vertex mixture ``mix``;
    kind "exponential":  Lemma 7.5(iii), base points at the centre of ``dom``;
    kind "vertexmax":    base points at the vertex maxima, with ``reserve`` (Lemma 7.5(iii')) and
                         ``form`` "tangent" (Lemma 7.5(ii)(a)) or "exponential" (Lemma 7.5(iii)).
    """
    if isinstance(record, list):
        kind, alpha, cube, limit, *rest = record
        record = {"kind": kind, "alpha": alpha, "cube": cube, "limit": limit}
        if kind == "tangent":
            record["mix"] = rest[0]
        elif kind == "vertexmax":
            record["reserve"], record["form"] = rest
        dom = box
    else:
        dom = boxes.parse_box(record["dom"])
    kind = record.get("kind", "tangent")
    alpha, limit = Fraction(record["alpha"]), Fraction(record["limit"])
    if kind == "exponential":
        return ExponentialSupport(dom, alpha, record["cube"], limit)
    if kind == "vertexmax":
        return VertexMaxSupport(dom, alpha, record["cube"], limit, bool(record.get("reserve")),
                                record.get("form", "tangent"))
    if kind == "tangent":
        return TangentSupport(dom, alpha, record["cube"], limit, record["mix"])
    raise rules.Rejected(f"unknown kind of support {kind!r}")


def exponential_form(support):
    return isinstance(support, ExponentialSupport) or (isinstance(support, VertexMaxSupport) and support.exponential)


def check_leaf(box, leaf, supports):
    """Dispatch one leaf.  ``supports(spec, box)`` returns the support named or described by ``spec``.
    Returns (rule, condition, margin)."""
    rule = leaf[0]
    if rule == "N":
        return rule, *rules.rule_n(box, leaf[1], tuple(leaf[2]))
    if rule == "SL":
        result = rules.rule_slabs(box, leaf[1], lambda rest: check_leaf(rest, leaf[2], supports))
        return "SL+" + result[0], result[1], result[2]
    if rule == "E1":
        return rule, *rules.rule_e1(box, leaf[1], leaf[2])
    if rule == "PL":
        return rule, *rules.rule_pl(box)
    if rule in ("E2", "E3", "E4"):
        support = supports(leaf[1], box)
        if rule == "E2" and exponential_form(support):
            raise rules.Rejected("E2 needs a support of Lemma 7.5(ii)")
        if rule == "E3" and not exponential_form(support):
            raise rules.Rejected("E3 needs a support of Lemma 7.5(iii)")
        reduced = (leaf[2], leaf[3]) if rule == "E4" else None
        return rule, *rules.rule_e(box, support, reduced)
    if rule == "D1":
        return rule, *rules.rule_d1(box, supports(leaf[1], box), defect.Registration(*leaf[2]))
    if rule == "D3":
        return rule, *rules.rule_d3(box, supports(leaf[1], box), defect.Registration(*leaf[2]), tuple(leaf[3]), leaf[4])
    if rule == "PF":
        return rule, *rules.rule_pf(box, leaf[1], leaf[2])
    if rule == "AP":
        return rule, *rules.rule_ap(box, leaf[1], leaf[2])
    if rule == "AG":
        return rule, *rules.rule_ag(box, leaf[1], leaf[2])
    if rule == "AS":
        # the support bounds the energy of the anchor: an inline description is built on S x {f0 + n}
        point = tuple(Fraction(v) + k for v, k in zip(leaf[1], leaf[2]))
        anchor_box = (box[0][:5] + point, box[1][:5] + point)
        return rule, *rules.rule_as(box, leaf[1], leaf[2], supports(leaf[3], anchor_box))
    if rule == "AC":
        registration = defect.Registration(*leaf[3]) if len(leaf) > 3 else None
        return rule, *rules.rule_ac(box, leaf[1], leaf[2], registration)
    raise rules.Rejected(f"unknown rule {rule!r}")


def check_batch(job):
    """Worker: verify the leaves of a batch of pieces and regions.  Returns statistics and rejections."""
    bits, items, support_records = job
    set_precision(bits)
    built = {}

    def supports(spec, box):
        if isinstance(spec, list):                      # inline description: built on the box of the leaf
            return build_support(spec, box)
        if spec not in built:
            built[spec] = build_support(support_records[spec])
        return built[spec]

    counts, smallest, rejected = Counter(), {}, []
    start = time.process_time()

    def check(identifier, index, box, leaf):
        try:
            rule, condition, margin = check_leaf(box, leaf, supports)
            if condition not in ("N", "E", "D", "A") or not (margin.is_finite() and margin > 0):
                raise rules.Rejected("the rule returned no positive margin")
        except Exception as error:                 # any failure, of whatever kind, is a rejection of the leaf
            name = leaf[0] if isinstance(leaf, list) and leaf and isinstance(leaf[0], str) else "?"
            rejected.append([identifier, index, name, f"{type(error).__name__}: {error}"])
            return
        key = f"{rule}:{condition}"
        counts[key] += 1
        value = float(margin)
        if key not in smallest or value < smallest[key][0]:
            smallest[key] = (value, identifier, index)

    for record in items:
        try:
            region = record["t"] == "region"
            identifier = record["id"]
            if region:
                box = boxes.parse_box(record["box"])
                boxes.check_shape_part(box)
                parts = [(box, record["leaf"])]
            else:
                parts = subdivision(record)[1]
        except Exception as error:                 # a malformed record is rejected as a whole
            rejected.append([str(record)[:80], -1, "record", f"{type(error).__name__}: {error}"])
            continue
        for index, (leaf_box, leaf) in enumerate(parts):
            if isinstance(leaf, list) and leaf[:1] in (["H"], ["IN"]):
                continue                           # held and contained leaves belong to the completeness pass
            check(identifier, -1 if region else index, leaf_box, leaf)
    return counts, smallest, rejected, time.process_time() - start


def record_leaves(record):
    if record["t"] == "region":
        return [record["leaf"]]
    return [leaf for _, leaf in record["parts"]] if record["t"] == "cut" else record["leaves"]


def referenced_supports(record):
    """The identifiers of the support records that the leaves of a record refer to."""
    found = set()

    def visit(leaf):
        if leaf[0] == "SL":
            visit(leaf[2])
        elif leaf[0] in SUPPORT_RULES and isinstance(leaf[1], str):
            found.add(leaf[1])
        elif leaf[0] == "AS" and isinstance(leaf[3], str):
            found.add(leaf[3])

    for leaf in record_leaves(record):
        visit(leaf)
    return found


def batches(path, bits, size):
    """Yield worker jobs: batches of pieces and regions with the support records they refer to."""
    supports, items, needed, missing = {}, [], {}, set()
    with open_text(path) as stream:
        stream.readline()                              # the header
        for line in stream:
            record = json.loads(line)
            kind = record.get("t") if isinstance(record, dict) else "malformed"
            # every record sees exactly the supports that precede it: the batch ends before a support that it
            # uses (or has looked for in vain) is defined again, and at every "forget"
            if items and (kind == "forget" or (kind == "support" and (record.get("id") in needed or record.get("id") in missing))):
                yield bits, items, needed
                items, needed, missing = [], {}, set()
            if kind == "support":
                supports[record.get("id")] = record
            elif kind == "forget":
                supports.clear()
            elif kind in ("piece", "cut", "region", "malformed"):
                try:
                    leaves = record_leaves(record)
                    if kind != "region" and all(isinstance(leaf, list) and leaf[:1] in (["H"], ["IN"]) for leaf in leaves):
                        continue                       # no inequality to check in this record
                    referenced = referenced_supports(record)
                except Exception:                      # the worker rejects the record
                    referenced = set()
                items.append(record)
                for sid in referenced:
                    if sid in supports:
                        needed[sid] = supports[sid]
                    else:
                        missing.add(sid)               # the worker rejects the leaf
                if len(items) >= size:
                    yield bits, items, needed
                    items, needed, missing = [], {}, set()
    if items:
        yield bits, items, needed


def inequality_pass(files, bits, workers, batch_size, log):
    totals, smallest, rejected, cpu = {}, {}, {}, 0.0
    for path in files:
        counts, least, bad = Counter(), {}, []
        started = time.time()

        def collect(result):
            nonlocal cpu
            part_counts, part_least, part_bad, seconds = result
            counts.update(part_counts)
            bad.extend(part_bad)
            cpu += seconds
            for key, value in part_least.items():
                if key not in least or value[0] < least[key][0]:
                    least[key] = value

        with ProcessPoolExecutor(workers) as pool:
            pending = set()
            for job in batches(path, bits, batch_size):
                pending.add(pool.submit(check_batch, job))
                if len(pending) >= 3 * workers:                 # bounded queue: at most 3 batches per worker
                    done, pending = wait(pending, return_when=FIRST_COMPLETED)
                    for future in done:
                        collect(future.result())
            for future in pending:
                collect(future.result())
        totals[path.name], smallest[path.name], rejected[path.name] = dict(counts), least, bad
        log(f"{path.name}: inequalities {dict(sorted(counts.items()))}; rejected {len(bad)}; "
            f"{time.time() - started:.0f} s elapsed")
        for key, (value, piece, index) in sorted(least.items()):
            log(f"    smallest margin {key}: {value:.6e} (piece {piece}, leaf {index})")
    return totals, smallest, rejected, cpu


# ---------------------------------------------------------------------------------------------
# (a) completeness
# ---------------------------------------------------------------------------------------------
def completeness_pass(files, log, partial=False, require_empty=None):
    """Exact check that the stages chain from the box K to the empty set of held pieces.

    ``held`` is the set of boxes still to be discharged.  It starts as {K}.  Every piece of a stage must
    be an element of ``held`` (it is removed), no element may be left when the stage has been read, and
    the held leaves of the trees of the stage form the new set.  With ``partial`` the pieces of the first
    file are taken as given and, unless ``require_empty`` is set, boxes may remain held at the end.
    Returns per-stage counts.
    """
    held = None if partial else {boxes.encode(boxes.K_BOX)}
    mirrored = False
    summary = {}
    for path in files:
        pieces = leaves = contained = 0
        new_held = set()
        declared = None
        regions = {}
        with open_text(path) as stream:
            header = json.loads(stream.readline())
            if header.get("format") != FORMAT:
                raise ValueError(f"{path.name}: unknown format")
            if header.get("step") == "mirror":
                # the reflection step: the held set is replaced by the boxes P n iota(P')
                if held is None or mirrored:
                    raise ValueError("the reflection step needs the held set and can be used only once")
                if stream.read().strip():
                    raise ValueError(f"{path.name}: a reflection step has no records")
                mirrored = True
                before = len(held)
                held = boxes.mirror_step(held)
                summary[path.name] = {"reflection": True, "held_before": before, "held": len(held)}
                log(f"{path.name}: completeness {summary[path.name]}")
                continue
            for line in stream:
                record = json.loads(line)
                kind = record.get("t")
                if kind in ("piece", "cut"):
                    box, parts = subdivision(record)
                    if held is not None:
                        # the record replaces the held boxes listed under "from" (default: its own box),
                        # each of which must lie in the box of the record
                        sources = [boxes.parse_box(b) for b in record["from"]] if "from" in record else [box]
                        for source in sources:
                            code = boxes.encode(source)
                            if code not in held or not boxes.contains(box, source):
                                raise ValueError(f"{path.name}: {kind} {record['id']} does not replace held boxes")
                            held.remove(code)
                    if kind == "cut" and not boxes.covered(box, [part for part, _ in parts]):
                        raise ValueError(f"{path.name}: cut {record['id']}: the parts do not cover the box")
                    pieces += 1
                    leaves += len(parts)
                    for leaf_box, leaf in parts:
                        if leaf[0] == "H":
                            new_held.add(boxes.encode(leaf_box))
                        elif leaf[0] == "IN":
                            # Lemma 7.2(ii): a box contained in a discharged box, in its image under iota or
                            # in an integer translate of these, is discharged.
                            image = regions[leaf[1]]
                            if len(leaf) > 2:
                                if leaf[2] not in (0, 1):
                                    raise ValueError("the reflection flag must be 0 or 1")
                                if leaf[2]:
                                    image = boxes.reflect(image)
                                image = boxes.translate(image, tuple(leaf[3]))
                            if not boxes.contains(image, leaf_box):
                                raise ValueError(f"{path.name}: {kind} {record['id']}: leaf outside region {leaf[1]}")
                            contained += 1
                elif kind == "region":
                    box = boxes.parse_box(record["box"])
                    boxes.check_shape_part(box)
                    if record["leaf"][0] in ("H", "IN"):
                        raise ValueError("a region needs a rule")
                    regions[record["id"]] = box
                elif kind == "forget":
                    regions.clear()
                elif kind == "end":
                    declared = record["held"]
        if held:
            raise ValueError(f"{path.name}: {len(held)} held boxes are not received by this stage")
        if declared != len(new_held):
            raise ValueError(f"{path.name}: the declared number of held leaves is wrong")
        summary[path.name] = {"pieces": pieces, "leaves": leaves, "contained": contained, "held": len(new_held)}
        log(f"{path.name}: completeness {summary[path.name]}")
        held = new_held
    if held and (require_empty if require_empty is not None else not partial):
        raise ValueError(f"the last stage holds {len(held)} pieces")
    return summary


# ---------------------------------------------------------------------------------------------
def environment():
    import flint
    return {"python": sys.version, "python-flint": flint.__version__, "flint": getattr(flint, "__FLINT_VERSION__", None),
            "platform": platform.platform(), "processors": os.cpu_count()}


def source_digests():
    here = Path(__file__).resolve().parent
    return {p.name: sha256(p.read_bytes()).hexdigest() for p in sorted(here.glob("*.py"))}


def input_digests(files):
    return {p.name: sha256(p.read_bytes()).hexdigest() for p in files}


def overall(counts, smallest):
    """Per rule and condition over all files: the number of boxes and the smallest margin with its place."""
    total = {}
    for name, tally in counts.items():
        for key, number in tally.items():
            entry = total.setdefault(key, {"boxes": 0, "smallest_margin": None})
            entry["boxes"] += number
            value, piece, index = smallest[name][key]
            if entry["smallest_margin"] is None or value < entry["smallest_margin"]:
                entry.update(smallest_margin=value, file=name, piece=piece, leaf=index)
    return dict(sorted(total.items()))


def main(argv=None):
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--bits", type=int, default=128)
    parser.add_argument("--batch", type=int, default=64)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--partial", action="store_true",
                        help="check a subset of consecutive stages: the first file need not start from K")
    parser.add_argument("--skip-completeness", action="store_true")
    parser.add_argument("--skip-inequalities", action="store_true")
    args = parser.parse_args(argv)
    lines = []

    def log(text):
        print(text, flush=True)
        lines.append(text)

    started = time.time()
    files = stage_files(args.certificate)
    digests = input_digests(files)
    log(f"certificate {args.certificate} ({len(files)} stage files), {args.bits} bits, {args.workers} workers")
    report = {"format": FORMAT, "program": "cover_verifier.verify", "bits": args.bits, "inputs": digests,
              "verifier": source_digests(), "environment": environment(),
              "partial": args.partial, "workers": args.workers, "batch": args.batch,
              "arguments": [str(a) for a in (sys.argv[1:] if argv is None else argv)],
              "started": time.strftime("%Y-%m-%dT%H:%M:%S%z", time.localtime(started))}
    ok = True
    if not args.skip_completeness:
        try:
            cpu_before = time.process_time()
            report["completeness"] = completeness_pass(files, log, args.partial)
            report["completeness_cpu_seconds"] = time.process_time() - cpu_before
            log("completeness: PASS" + (" (partial chain: the pieces of the first file are taken as given)"
                                        if args.partial else " (from the box K to no held piece)"))
        except Exception as error:                 # a malformed certificate fails; it does not end the run
            log(f"completeness: FAIL: {type(error).__name__}: {error}")
            report["completeness_error"] = f"{type(error).__name__}: {error}"
            ok = False
    if not args.skip_inequalities:
        set_precision(args.bits)
        counts, smallest, rejected, cpu = inequality_pass(files, args.bits, args.workers, args.batch, log)
        report.update({"counts": counts, "smallest_margins": smallest, "rejected": rejected, "cpu_seconds": cpu,
                       "rules": overall(counts, smallest)})
        bad = sum(len(v) for v in rejected.values())
        for key, entry in report["rules"].items():
            log(f"    {key}: {entry['boxes']} boxes, smallest margin {entry['smallest_margin']:.6e} "
                f"({entry['file']}, piece {entry['piece']}, leaf {entry['leaf']})")
        log(f"inequalities: {'PASS' if not bad else f'FAIL ({bad} leaves rejected)'}; CPU {cpu:.0f} s")
        ok = ok and not bad
    # the verifier and the certificate are hashed again at the end; a change during the run fails it
    report["verifier_at_end"] = source_digests()
    report["inputs_at_end"] = input_digests(files)
    unchanged = report["verifier_at_end"] == report["verifier"] and report["inputs_at_end"] == report["inputs"]
    log("verifier and certificate unchanged during the run" if unchanged
        else "FAIL: the verifier or the certificate changed during the run")
    ok = ok and unchanged
    report["elapsed_seconds"] = time.time() - started
    # only a run of both passes on a chain that starts from K establishes the theorem
    limits = [text for flag, text in ((args.partial, "the chain does not start from K"),
                                      (args.skip_completeness, "completeness not checked"),
                                      (args.skip_inequalities, "inequalities not checked")) if flag]
    report["scope"] = "complete" if not limits else "incomplete: " + "; ".join(limits)
    report["result"] = "FAIL" if not ok else ("PASS" if not limits else "PASS OF AN INCOMPLETE RUN")
    log(f"RESULT: {report['result']}" + (f" ({'; '.join(limits)})" if limits else ""))
    if args.receipt:
        args.receipt.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    if args.log:
        args.log.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
