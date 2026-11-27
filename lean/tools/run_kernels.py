"""Export declarations with `leanexport` and run the bundled kernels on the export (Windows).

Usage:
  python run_kernels.py export --scope <scope.json> --formal <Lake package dir> --modules <file> --names <file>
                        --out <export.ndjson> --log <dir>
  python run_kernels.py check --export <export.ndjson> --log <dir> --kernels lean,paranoid,nanoda,lean4lean,con-leche,con-ron
                        [--threads 4] [--commit-limit-gib 40] [--timeout-s 86400]

`export` runs  leanexport <modules> -- <names>  with the LEAN_PATH that `lake env` reports, and writes the NDJSON
export.  Its record holds a snapshot (snapshot.py) taken before the export starts and one taken after it ends: the
tools, the toolchain, the sources and compiled files of the scope, the compiled files of the dependencies, the two
list files, and after the export the SHA-256, size and first line of the export; the two must agree in everything
but the time and the export.

`check` runs, one after another and each in its own Windows job object:

  lean        leanchecker --from-export <export>            Lean's kernel on the export, empty environment
  paranoid    leanchecker-paranoid --from-export <export>   the toolchain's second build of that checker
  nanoda      nanoda_bin <config.json>                      nanoda (Rust), permitted axioms: the three
  lean4lean   lean4lean --import <export>                   Lean4Lean
  con-leche   con-leche --verified --jobs=<n> <export>
  con-ron     con-ron --verified --jobs=<n> <export>

Each start waits for the memory gate of gated_runner.py.  Immediately before a checker starts and again after it ends,
the record takes a snapshot of the tools, of the files in the toolchain's bin/ directory and of the export (SHA-256,
size, first line); a checker whose two snapshots differ counts as failed.  For nanoda the snapshots include its
configuration file, which the record also holds.  Results (exit code, wall and CPU time, peak commit and working set,
last lines of output, the two snapshots) go to <log>/kernels.jsonl; full output to <log>/<kernel>.log.  Both modes
refuse a --log directory that already holds a kernels.jsonl or run_kernels.log.  ../check_records.py checks these
records against the export records.
"""
import argparse
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gated_runner as gr  # noqa: E402
import snapshot as snap  # noqa: E402

TC = gr.default_toolchain_bin()


def wait_gate(expect_gib, log):
    last = 0.0
    while True:
        pf = gr.perf()
        ok = (pf["committed"] + expect_gib * gr.GIB < 125 * gr.GIB
              and pf["committed"] + expect_gib * gr.GIB < pf["limit"] - 8 * gr.GIB
              and pf["avail"] > 12000 * gr.MIB)
        gate = dict(committed_gib=round(pf["committed"] / gr.GIB, 2), limit_gib=round(pf["limit"] / gr.GIB, 2),
                    avail_mb=round(pf["avail"] / gr.MIB))
        if ok:
            return gate
        if time.time() - last > 60:
            last = time.time()
            log(f"gate closed: {gate}")
        time.sleep(5)


def run_job(name, cmd, cwd, env, log_path, limit_gib, timeout_s, expect_gib, log, files):
    gate = wait_gate(expect_gib, log)
    before = snap.snapshot(None, None, files, lib=False)
    export_key = files[0].replace("\\", "/")
    log(f"start {name}: {cmd}; gate {gate}; export sha256 {before['files'][export_key]['sha256']}")
    j = gr.Job(name, cmd, cwd, env, log_path, int(limit_gib * gr.GIB), int(expect_gib * gr.GIB))
    status = None
    while j.p.poll() is None:
        if time.time() - j.t0 > timeout_s:
            gr.kernel32.TerminateJobObject(j.h, 1)
            j.p.wait()
            status = "timeout"
            break
        if time.time() - j.last_sample >= 2.0:
            j.sample()
        time.sleep(0.5)
    rec = j.finish(status)
    after = snap.snapshot(None, None, files, lib=False)
    rec["gate_at_start"] = gate
    rec["peak_ws_any_bytes"] = rec.pop("peak_ws_proc_bytes")
    with open(log_path, "rb") as fh:
        data = fh.read()
    rec["tail"] = data[-1500:].decode("utf-8", errors="replace")
    rec["export_sha256"] = before["files"][export_key]["sha256"]
    rec["unchanged"] = snap.same(before, after)
    rec["before"], rec["after"] = before, after
    log(f"done {name}: exit {rec['exit']}, wall {rec['wall_s']} s, cpu {rec['cpu_s']} s, peak commit "
        f"{rec['peak_commit_proc_bytes'] / gr.GIB:.2f} GiB, peak ws {rec['peak_ws_any_bytes'] / gr.GIB:.2f} GiB; "
        f"snapshot {'unchanged' if rec['unchanged'] else 'CHANGED'}")
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["export", "check"])
    ap.add_argument("--scope")
    ap.add_argument("--formal")
    ap.add_argument("--modules")
    ap.add_argument("--names")
    ap.add_argument("--out")
    ap.add_argument("--export")
    ap.add_argument("--log")
    ap.add_argument("--kernels", default="lean,paranoid,nanoda,lean4lean,con-leche,con-ron")
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--commit-limit-gib", type=float, default=40.0)
    ap.add_argument("--expect-gib", type=float, default=16.0)
    ap.add_argument("--timeout-s", type=float, default=86400.0)
    ap.add_argument("--tag", default="")
    args = ap.parse_args()
    need = ("scope", "formal", "modules", "names", "out", "log") if args.mode == "export" else ("export", "log")
    missing = [f"--{n}" for n in need if getattr(args, n) is None]
    if missing:
        ap.error(f"{args.mode} needs {' '.join(missing)}")
    os.makedirs(args.log, exist_ok=True)
    for name in ("kernels.jsonl", "run_kernels.log"):
        if os.path.exists(os.path.join(args.log, name)):
            sys.exit(f"{os.path.join(args.log, name)} exists; give a new --log directory")
    runlog = open(os.path.join(args.log, "run_kernels.log"), "a", encoding="utf-8", newline="\n")

    def log(msg):
        line = f"{gr.now()} {msg}"
        runlog.write(line + "\n")
        runlog.flush()
        print(line, flush=True)

    env = dict(os.environ)
    env["PATH"] = TC + os.pathsep + env.get("PATH", "")
    env["LEAN_ABORT_ON_PANIC"] = "1"
    results = os.path.join(args.log, "kernels.jsonl")
    tag = args.tag

    if args.mode == "export":
        formal, scope = os.path.abspath(args.formal), os.path.abspath(args.scope)
        out = os.path.abspath(args.out)
        if os.path.exists(out):
            sys.exit(f"{out} exists; give a new path")
        lists = [os.path.abspath(args.modules), os.path.abspath(args.names)]
        before = snap.snapshot(scope, formal, lists)   # taken before the lists are read; compared after the export
        r = subprocess.run([os.path.join(TC, "lake.exe"), "env", "printenv", "LEAN_PATH"], cwd=formal,
                           capture_output=True, text=True, env=env)
        lean_path = r.stdout.strip()
        if r.returncode != 0 or not lean_path:
            sys.exit(f"lake env printenv LEAN_PATH failed: {r.stderr}")
        env["LEAN_PATH"] = lean_path
        modules = [l.strip() for l in open(lists[0], encoding="utf-8") if l.strip()]
        names = [l.strip() for l in open(lists[1], encoding="utf-8") if l.strip()]
        cmd = [os.path.join(TC, "leanexport.exe")] + modules + ["--"] + names
        log(f"export: {len(modules)} modules imported, {len(names)} declarations requested, "
            f"command line {sum(len(c) + 1 for c in cmd)} characters")
        gate = wait_gate(args.expect_gib, log)
        j = gr.Job("leanexport", cmd, formal, env, out, int(args.commit_limit_gib * gr.GIB),
                   int(args.expect_gib * gr.GIB))
        while j.p.poll() is None:
            if time.time() - j.last_sample >= 2.0:
                j.sample()
            time.sleep(0.5)
        rec = j.finish()
        after = snap.snapshot(scope, formal, lists + [out])
        rec["gate_at_start"] = gate
        rec["cmd"] = rec["cmd"][:1] + [f"<{len(modules)} modules>", "--", f"<{len(names)} names>"]
        rec["lean_path"] = lean_path
        rec["export_file"] = out
        rec["export_bytes"] = os.path.getsize(out)
        rec["export_sha256"] = after["files"][out.replace("\\", "/")]["sha256"]
        with open(out, "rb") as fh:
            rec["export_lines"] = sum(chunk.count(b"\n") for chunk in iter(lambda: fh.read(1 << 24), b""))
        with open(out, "rb") as fh:
            rec["export_header"] = fh.readline().decode("utf-8", errors="replace").strip()
        rec["kernel"] = "leanexport" + tag
        same = dict(after, files={k: v for k, v in after["files"].items() if k != out.replace("\\", "/")})
        rec["unchanged"] = snap.same(before, same)
        rec["before"], rec["after"] = before, after
        log(f"export done: exit {rec['exit']}, {rec['export_bytes']} bytes, {rec['export_lines']} lines, "
            f"wall {rec['wall_s']} s, sha256 {rec['export_sha256']}; snapshot "
            f"{'unchanged' if rec['unchanged'] else 'CHANGED'}")
        with open(results, "a", encoding="utf-8", newline="\n") as fh:
            fh.write(json.dumps(rec) + "\n")
        sys.exit(0 if rec["exit"] == 0 and rec["unchanged"] else 1)

    exp = os.path.abspath(args.export)
    cwd = os.path.dirname(exp)
    table = {
        "lean": [os.path.join(TC, "leanchecker.exe"), "--from-export", exp],
        "paranoid": [os.path.join(TC, "leanchecker-paranoid.exe"), "--from-export", exp],
        "lean4lean": [os.path.join(TC, "lean4lean.exe"), "--import", exp],
        "con-leche": [os.path.join(TC, "con-leche.exe"), "--verified", f"--jobs={args.threads}", exp],
        "con-ron": [os.path.join(TC, "con-ron.exe"), "--verified", f"--jobs={args.threads}", exp],
    }
    failed = []
    for k in args.kernels.split(","):
        config = None
        files = [exp]
        if k == "nanoda":
            # beside the export, in the directory where nanoda runs
            cfg = os.path.join(cwd, f"nanoda{tag}.config.json")
            config = dict(use_stdin=False, export_file_path=exp,
                          permitted_axioms=["propext", "Classical.choice", "Quot.sound"],
                          unpermitted_axiom_hard_error=True, num_threads=args.threads,
                          nat_extension=True, string_extension=True, print_success_message=True)
            with open(cfg, "w", encoding="utf-8", newline="\n") as fh:
                json.dump(config, fh)
            cmd = [os.path.join(TC, "nanoda_bin.exe"), cfg]
            files.append(cfg)
        else:
            cmd = table[k]
        rec = run_job(k, cmd, cwd, env, os.path.join(args.log, f"{k}{tag}.log"), args.commit_limit_gib,
                      args.timeout_s, args.expect_gib, log, files)
        if config is not None:
            rec["nanoda_config"] = config
        rec["kernel"] = k + tag
        rec["export"] = os.path.basename(exp)
        with open(results, "a", encoding="utf-8", newline="\n") as fh:
            fh.write(json.dumps(rec) + "\n")
        if rec["exit"] != 0 or not rec["unchanged"]:
            failed.append(k)
    log(f"check done; failed: {failed}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
