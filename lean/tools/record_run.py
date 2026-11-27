"""Run a command and record what it read: a snapshot before and after it (Windows or POSIX).

Usage: python record_run.py --scope scope.json --formal <Lake package dir> --out <record.json> --log <output file>
       [--file <path> ...] -- <command> [<argument> ...]

Takes a snapshot (snapshot.py: the tools, the interpreter, the toolchain, the package configuration, the sources and
all compiled files of the scope, the compiled files of the dependencies and the given files), writes the record with
that snapshot at once, runs the command in the package directory with its standard output and standard error written
to the log file, takes the snapshot again, and completes the record: the command, the executable it resolves to
(path and SHA-256), the LEAN_* and ELAN_* environment variables, the start and end time, the wall time, the exit
status, the SHA-256 and size of the log, both snapshots, and whether they agree in everything but the time. Relative
paths of --file are relative to the package directory. Refuses to overwrite an existing record or log. Exit status:
that of the command, or 1 if the two snapshots differ.
"""
import argparse
import datetime
import json
import os
import shutil
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import snapshot as snap  # noqa: E402


def write(path, record):
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(record, fh, indent=1)
        fh.write("\n")


def main():
    argv = sys.argv[1:]
    if "--" not in argv:
        sys.exit(__doc__)
    split = argv.index("--")
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", required=True)
    ap.add_argument("--formal", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--file", action="append", default=[])
    args = ap.parse_args(argv[:split])
    command = argv[split + 1:]
    if not command:
        sys.exit("no command")
    formal = os.path.abspath(args.formal)
    scope = os.path.abspath(args.scope)
    out, log = os.path.abspath(args.out), os.path.abspath(args.log)
    for path in (out, log):
        if os.path.exists(path):
            sys.exit(f"{path} exists; give a new path")
        os.makedirs(os.path.dirname(path), exist_ok=True)
    os.chdir(formal)
    executable = shutil.which(command[0])
    if executable is None:
        sys.exit(f"{command[0]} not found")
    executable = os.path.abspath(executable)
    record = {"command": command, "executable": {"path": executable, "sha256": snap.sha256_file(executable)},
              "environment": {k: v for k, v in sorted(os.environ.items()) if k.upper().startswith(("LEAN", "ELAN"))}}
    record["before"] = snap.snapshot(scope, formal, args.file)
    record["start"] = datetime.datetime.now().astimezone().isoformat(timespec="seconds")
    write(out, record)
    t0 = time.time()
    with open(log, "xb") as fh:
        status = subprocess.run([executable] + command[1:], cwd=formal, stdin=subprocess.DEVNULL, stdout=fh,
                                stderr=subprocess.STDOUT).returncode
    record["wall_s"] = round(time.time() - t0, 1)
    record["end"] = datetime.datetime.now().astimezone().isoformat(timespec="seconds")
    record["exit"] = status
    record["log"] = {"file": os.path.basename(log), "sha256": snap.sha256_file(log), "bytes": os.path.getsize(log)}
    record["after"] = snap.snapshot(scope, formal, args.file)
    record["unchanged"] = snap.same(record["before"], record["after"])
    write(out, record)
    print(f"{record['end']} exit {status}, wall {record['wall_s']} s, snapshots "
          f"{'equal' if record['unchanged'] else 'DIFFER'}; record {out}")
    sys.exit(status if record["unchanged"] else 1)


if __name__ == "__main__":
    main()
