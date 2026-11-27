"""Check a receipt of the verifier against the recorded receipt.

usage: python -B check_receipt.py <receipt.json> [<recorded receipt.json>]

The receipt must have complete scope, result PASS and no rejected leaf; its verifier hashes must equal the SHA-256 of
the modules of cover_verifier/ beside this checker, and the hashes it took at the end of the run those it took at the
start; and its certificate hashes, coverage, counts by stage and condition and boxes per rule must equal those of the
recorded receipt run/receipt.json. The recorded receipt itself must have
been made by those modules on the files of certificate/ (its verifier and certificate hashes equal theirs), and the
recorded negative controls run/controls.json must have run on the same modules and files (hashed before and after,
unchanged, by record_controls.py beside this checker), with every control rejected, the unchanged leaf accepted in every
control that changes a leaf, and every baseline accepted. With a second argument, that receipt is the reference
instead, its verifier hashes are the expected ones, and the recorded files are not consulted. The smallest margins and
their locations are printed for inspection, not compared. Exit status is 0 when all criteria hold, 1 for a failed
check and 2 for incorrect usage.
"""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RECORDED = HERE / "run" / "receipt.json"


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unchanged(receipt):
    """The hashes taken at the end of the run equal those taken at its start."""
    return (receipt.get("verifier_at_end") == receipt.get("verifier") is not None
            and receipt.get("inputs_at_end") == receipt.get("inputs") is not None)


def recorded_run_checks(recorded, verifier):
    """The recorded receipt against the files beside this checker, and the recorded controls against both."""
    certificate = {p.name: sha256(p) for p in sorted((HERE / "certificate").glob("stage*.jsonl*"))}
    checks = [("recorded run/receipt.json: its verifier hashes equal the SHA-256 of the modules of cover_verifier/ "
               "beside this checker", recorded.get("verifier") == verifier),
              ("recorded run/receipt.json: its certificate hashes equal the SHA-256 of the files of certificate/",
               recorded.get("inputs") == certificate),
              ("recorded run/receipt.json: the verifier and the certificate unchanged during the run",
               unchanged(recorded))]
    path = RECORDED.parent / "controls.json"
    report = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
    prov = report.get("provenance", {})
    controls, baselines = report.get("controls", []), report.get("baselines", [])
    changed = [c for c in controls if isinstance(c.get("detail"), dict) and "unchanged_leaf" in c["detail"]]
    checks += [
        ("recorded run/controls.json: run by record_controls.py beside this checker on these modules and on the "
         "certificate of the recorded receipt, hashed before and after, unchanged",
         prov.get("unchanged") is True and prov.get("before") == prov.get("after")
         and (prov.get("before") or {}).get("program_sha256") == sha256(HERE / "record_controls.py")
         and (prov.get("before") or {}).get("verifier") == verifier
         and (prov.get("before") or {}).get("inputs") == recorded.get("inputs")),
        ("recorded run/controls.json: every control rejected, the unchanged leaf accepted in every control that "
         "changes a leaf, every baseline accepted",
         bool(controls) and all(c.get("outcome") == "rejected" for c in controls)
         and bool(changed) and all(c["detail"]["unchanged_leaf"][0] == "accepted" for c in changed)
         and bool(baselines) and all(b.get("outcome") == "accepted" for b in baselines)),
    ]
    return checks


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def boxes_per_rule(receipt):
    rules = receipt.get("rules")
    return {key: entry.get("boxes") for key, entry in rules.items()} if isinstance(rules, dict) else None


def margin(entry):
    value = entry.get("smallest_margin")
    return f"{value:.6e}" if isinstance(value, (int, float)) else "-"


def place(entry):
    return f"{entry.get('file')}, piece {entry.get('piece')}, leaf {entry.get('leaf')}" if entry else "-"


def main(argv):
    if len(argv) not in (1, 2):
        print(__doc__)
        return 2
    run = load(argv[0])
    recorded = load(argv[1] if len(argv) == 2 else RECORDED)
    checks = []
    if len(argv) == 2:
        verifier = recorded["verifier"]
    else:
        verifier = {p.name: sha256(p) for p in (HERE / "cover_verifier").glob("*.py")}
        checks += recorded_run_checks(recorded, verifier)
    rejected = run.get("rejected")
    checks += [
        ("scope is complete", run.get("scope") == "complete"),
        ("result is PASS", run.get("result") == "PASS"),
        ("no rejected leaf", isinstance(rejected, dict) and not any(rejected.values())),
        ("verifier: SHA-256 of the source files match the expected verifier", run.get("verifier") == verifier),
        ("verifier and certificate: the hashes taken at the end of the run equal those taken at its start",
         unchanged(run)),
        ("inputs: SHA-256 of the certificate files equal to the recorded ones", run.get("inputs") == recorded["inputs"]),
        ("completeness: counts of the first pass equal to the recorded ones",
         run.get("completeness") == recorded["completeness"]),
        ("counts: boxes per rule and condition in each file equal to the recorded ones",
         run.get("counts") == recorded["counts"]),
        ("rules: boxes per rule equal to the recorded ones", boxes_per_rule(run) == boxes_per_rule(recorded)),
    ]
    for text, ok in checks:
        print(f"{'ok  ' if ok else 'FAIL'}  {text}")
    print("diagnostics, not compared: smallest margin per rule (this run / recorded) and where it occurs")
    mine, theirs = run.get("rules") or {}, recorded.get("rules") or {}
    for key in sorted(set(mine) | set(theirs)):
        a, b = mine.get(key, {}), theirs.get(key, {})
        where = place(a) if place(a) == place(b) else f"{place(a)} / recorded: {place(b)}"
        print(f"  {key:9} {margin(a)} / {margin(b)}  ({where})")
    accepted = all(ok for _, ok in checks)
    print("ACCEPTED" if accepted else "NOT ACCEPTED")
    return 0 if accepted else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
