"""Run the negative controls and record what they ran on.

usage: python -B record_controls.py <certificate directory> --report <file> [--bits B] [--allow-missing]

Runs the negative controls of cover_verifier/controls.py with the same arguments and adds to their report a block
"provenance": the SHA-256 of this program, of the modules of cover_verifier/ and of the files of the certificate, taken
before the controls start and again after they end; the start time and the elapsed time; the arguments; and the
environment (interpreter, python-flint, FLINT, platform). Exit status is that of the controls, or 1 if a module or a
file of the certificate changed during the run.
"""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import sys
import time

from cover_verifier import controls, verify


def digests(certificate):
    return {"program_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
            "verifier": verify.source_digests(),
            "inputs": {p.name: sha256(p.read_bytes()).hexdigest() for p in verify.stage_files(certificate)}}


def main(argv=None):
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--bits", type=int, default=128)
    parser.add_argument("--allow-missing", action="store_true")
    args = parser.parse_args(argv)
    forwarded = [str(args.certificate), "--bits", str(args.bits), "--report", str(args.report)]
    if args.allow_missing:
        forwarded.append("--allow-missing")
    before = digests(args.certificate)
    started = time.time()
    status = controls.main(forwarded)
    elapsed = time.time() - started
    after = digests(args.certificate)
    unchanged = before == after
    provenance = {"program": "record_controls.py", "arguments": [str(a) for a in (sys.argv[1:] if argv is None else argv)],
                  "started": time.strftime("%Y-%m-%dT%H:%M:%S%z", time.localtime(started)),
                  "elapsed_seconds": elapsed, "environment": verify.environment(),
                  "before": before, "after": after, "unchanged": unchanged}
    report = json.loads(args.report.read_text(encoding="utf-8"))
    args.report.write_text(json.dumps({"provenance": provenance, **report}, indent=1) + "\n", encoding="utf-8",
                           newline="\n")
    print(f"provenance: program, {len(before['verifier'])} verifier modules and {len(before['inputs'])} certificate "
          f"files {'unchanged' if unchanged else 'CHANGED'} during the run", flush=True)
    return status if unchanged else 1


if __name__ == "__main__":
    sys.exit(main())
