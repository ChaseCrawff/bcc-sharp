"""Check the records of the build and of the checks against each other and against the files of this directory.

usage: python check_records.py [--write-checks] [--partial]   (in this directory; any system with Python 3.9 or later)

Reads records/ and verifies:
  * build: every module of scope.json built once with exit status 0; the states before and after the build have the
    SHA-256 of every source equal to scope.json and bracket the build; the digest of the .olean hashes taken right
    after each module was built (the build digest), which olean-sha256.txt lists; every log of the recorded size,
    building its own module only, with no error; summary.json, summary.md and log-check.json regenerated from the
    results and the logs;
  * every step that ran on the build (the two no-build checks, the two audit files, the replay, the two exports):
    the expected command, run by lake of the toolchain or by Python; exit status 0; its two snapshots, taken before
    and after the step, equal in everything but the time; in each, the sources digest that scope.json gives, the
    .olean digest equal to the build digest, the package configuration and the tools equal to those of this
    directory, and exactly the expected files, equal to those of this directory where it holds them; its log of the
    recorded size and SHA-256; started after the build ended;
  * the same compiled files (every part, .olean.private and .ir included), dependencies, toolchain and interpreter in
    every snapshot;
  * replay: every module replayed once, inside the recorded step, with exit status 0, the .olean hash taken after it
    equal to the build's, and a log of the recorded size consisting of the single line "replaying <module>";
    summary.json, summary.md and log-check.json regenerated from the results and the logs;
  * exports: made from the lists of audit/, with LEAN_PATH inside the hashed directories and the toolchain's commit
    in the header; statistics and dependency analysis read the bytes of the export record, after it was written, and
    find the requested theorems as theorems; the free theorems are those of audit/free-names.txt;
  * checks: each checker ran on the bytes its export record names, hashed immediately before it started and again
    after it ended; exit status 0; a log of the recorded size with a line that states acceptance, with the number of
    declarations of the export where the checker prints one; started after the export was written;
  * THEOREMS.md and audit/theorem-table.json are what tools/make_theorem_table.py writes from the audit log.

The table of checks is compared with records/kernels/checks.json (written by --write-checks). With --partial, records
not yet present are skipped. Exit status 0 when every check holds, 1 otherwise.
"""
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
R = os.path.join(HERE, "records")
PARTIAL = "--partial" in sys.argv[1:]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
RESULT = {"lean": r"Lean default kernel accepts the solution", "paranoid": r"Lean default kernel accepts the solution",
          "nanoda": r"Checked \d+ declarations with no typechecker errors.*", "lean4lean": r"checked (\d+) declarations",
          "con-leche": r"con-leche: accepted (\d+) declarations.*", "con-ron": r"con-ron: accepted (\d+) declarations.*"}
EXE = {"lean": "leanchecker.exe", "paranoid": "leanchecker-paranoid.exe", "nanoda": "nanoda_bin.exe",
       "lean4lean": "lean4lean.exe", "con-leche": "con-leche.exe", "con-ron": "con-ron.exe"}
PACKAGE_FILES = ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "scope.json")
results = []


def check(text, ok):
    results.append((text, bool(ok)))
    print(f"{'ok  ' if ok else 'FAIL'}  {text}")
    return bool(ok)


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def load(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def jsonl(path):
    with open(path, encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def t(text):
    return datetime.datetime.fromisoformat(text)


def present(path):
    if os.path.exists(path):
        return True
    if not PARTIAL:
        check(f"{os.path.relpath(path, HERE)} is present", False)
    return False


def same(a, b):
    return {k: v for k, v in a.items() if k != "time"} == {k: v for k, v in b.items() if k != "time"}


def digest(lines):
    return hashlib.sha256("".join(line + "\n" for line in lines).encode("utf-8")).hexdigest()


def norm(key):
    return key.replace("\\", "/")


def absolute(key):
    return bool(re.match(r"^[A-Za-z]:|^/", norm(key))) or "users/" in norm(key).lower()


def local(key):
    """The file of this directory that a record's key names, or None: <package>/x or a relative x."""
    key = norm(key)
    if key.startswith("<package>/"):
        key = key[len("<package>/"):]
    if absolute(key) or key.startswith("<"):
        return None
    path = os.path.join(HERE, key)
    return path if os.path.isfile(path) else None


scope = load(os.path.join(HERE, "scope.json"))
order = scope["order"]
tools = {n: sha(os.path.join(HERE, "tools", n)) for n in sorted(os.listdir(os.path.join(HERE, "tools"))) if n.endswith(".py")}
package_files = {n: sha(os.path.join(HERE, n)) for n in PACKAGE_FILES}
sources_digest = digest(f"{scope['modules'][m]['sha256']}  {scope['modules'][m]['path']}" for m in order)
snapshots = []

# build
build = {}
for r in jsonl(os.path.join(R, "build", "results.jsonl")):
    build.setdefault(r["module"], []).append(r)
check("build: every module of scope.json built once, with exit status 0",
      sorted(build) == sorted(order) and all(len(v) == 1 and v[0]["exit"] == 0 for v in build.values()))
olean = {m: build[m][0].get("olean_sha256") for m in order if m in build}
build_digest = digest(f"{olean.get(m)}  {m.replace('.', '/')}.olean" for m in order)
build_end = max(t(v[0]["end"]) for v in build.values())
build_start = min(t(v[0]["start"]) for v in build.values())
states = [load(os.path.join(R, "build", f"state-{w}.json")) for w in ("before", "after")]
check("build: before and after the build, the SHA-256 of every source equals scope.json",
      all(s["sources"] == len(order) == s["sources_equal_to_scope"] for s in states)
      and all(s["sources_sha256"][m] == scope["modules"][m]["sha256"] for s in states for m in order))
check("build: the state before is taken before the first module starts, the state after once the last has ended",
      t(states[0]["time"]) <= build_start and t(states[1]["time"]) >= build_end)
githash = re.search(r"commit ([0-9a-f]{40})", states[0]["lean_version"])
githash = githash.group(1) if githash else None
print(f"      build digest of the .olean hashes: {build_digest}; build ended {build_end.isoformat()}; Lean {githash}")


def unpack_logs(sub, dest):
    """The logs of records/<sub>/logs.tar.gz by module; those named after a module of scope.json also into dest/logs/."""
    with tarfile.open(os.path.join(R, sub, "logs.tar.gz"), "r:gz") as tar:
        logs = {os.path.basename(m.name)[:-4]: tar.extractfile(m).read() for m in tar.getmembers() if m.isfile()}
    os.makedirs(os.path.join(dest, "logs"))
    for m, data in logs.items():
        if m in scope["modules"]:
            with open(os.path.join(dest, "logs", m + ".log"), "wb") as fh:
                fh.write(data)
    return logs


def regenerated(sub, replay=False):
    """summary.json, summary.md and log-check.json of records/<sub> are what the tools write from its results and logs."""
    with tempfile.TemporaryDirectory() as tmp:
        unpack_logs(sub, tmp)
        runs = [subprocess.run([sys.executable, "-B", os.path.join("tools", "summarize_results.py"), "scope.json",
                                f"records/{sub}/results.jsonl", os.path.join(tmp, "summary.json"),
                                os.path.join(tmp, "summary.md")], cwd=HERE, capture_output=True),
                subprocess.run([sys.executable, "-B", os.path.join("tools", "verify_build_logs.py"), "scope.json", tmp,
                                os.path.join(tmp, "log-check.json")] + (["--replay"] if replay else []),
                               cwd=HERE, capture_output=True)]
        return all(r.returncode == 0 for r in runs) and all(
            sha(os.path.join(tmp, f)) == sha(os.path.join(R, sub, f)) for f in ("summary.json", "summary.md", "log-check.json"))


with tempfile.TemporaryDirectory() as tmp:
    build_logs = unpack_logs("build", tmp)
check("build: every log in logs.tar.gz has the size recorded for its module",
      sorted(build_logs) == sorted(order) and all(len(build_logs[m]) == build[m][0]["log_bytes"] for m in order if m in build))
check("build: summary.json, summary.md and log-check.json are what tools/summarize_results.py and "
      "tools/verify_build_logs.py write from results.jsonl and the logs; every log builds its own module only, with no error",
      regenerated("build") and load(os.path.join(R, "build", "log-check.json"))["problems"] == {})
olean_list = {}
with open(os.path.join(R, "build", "olean-sha256.txt"), encoding="utf-8") as fh:
    for line in fh:
        h, _, p = line.rstrip("\n").partition("  ")
        olean_list[p] = h
check("build: olean-sha256.txt lists the .olean hash of every module, taken right after it was built",
      olean_list == {f"{m.replace('.', '/')}.olean": olean.get(m) for m in order})


def snapshot_ok(name, s, expected_files):
    sc = s.get("scope", {})
    keys = {norm(k) for k in s.get("files", {})}
    ok = (sc.get("sources_equal_to_scope") == len(order) == sc.get("modules") and not sc.get("missing")
          and sc.get("sources_digest") == sources_digest and sc.get("olean_digest") == build_digest
          and s.get("tools") == tools and s.get("package_files") == package_files and keys == set(expected_files)
          and not any(absolute(k) for k in keys))
    for key, info in s.get("files", {}).items():
        path = local(key)
        if path is not None and sha(path) != info["sha256"]:
            ok = False
            print(f"      {name}: {key} differs from the file of this directory")
    return ok


def run_record(name, path, command, files=()):
    if not present(path):
        return None
    r = load(path)
    if "after" not in r:                              # written at the start of the step, completed at its end
        if not PARTIAL:
            check(f"{name}: the record is complete", False)
        return None
    snapshots.extend((r["before"], r["after"]))
    exe = norm(r["executable"]["path"])
    log = os.path.join(os.path.dirname(path), r["log"]["file"])
    check(f"{name}: command {' '.join(command)}; exit 0; snapshots before and after equal; sources, compiled files, "
          f"configuration, tools and named files as above; log as recorded; started after the build",
          r["command"] == command
          and (exe.startswith("<toolchain>/bin/") or command[0] == "python") and exe.lower().endswith(f"/{command[0]}.exe")
          and r["exit"] == 0 and same(r["before"], r["after"]) and r["unchanged"]
          and snapshot_ok(name, r["before"], files) and snapshot_ok(name, r["after"], files)
          and os.path.isfile(log) and r["log"]["sha256"] == sha(log) and r["log"]["bytes"] == os.path.getsize(log)
          and t(r["start"]) > build_end and t(r["before"]["time"]) > build_end)
    return r


run_record("no-build BccSharp", os.path.join(R, "no-build", "BccSharp.json"), ["lake", "build", "--no-build", "BccSharp"])
run_record("no-build Mathlib", os.path.join(R, "no-build", "Mathlib.json"), ["lake", "build", "--no-build", "Mathlib"])
for name in ("ScopeAxioms", "CorollaryFcc"):
    run_record(f"audit {name}", os.path.join(R, "audit", f"{name}.json"), ["lake", "env", "lean", f"audit/{name}.lean"],
               [f"audit/{name}.lean"])
replay_run = run_record("replay", os.path.join(R, "replay", "record.json"),
                        ["python", "-B", "tools/gated_runner.py", "--scope", "scope.json", "--formal", ".",
                         "--outdir", "records/replay", "--jobs", "3", "--ignore-deps", "--hash-olean",
                         "--command", '["lake","env","leanchecker","--verbose","{module}"]'])

# replay
if replay_run is not None and present(os.path.join(R, "replay", "results.jsonl")):
    replay = {}
    for r in jsonl(os.path.join(R, "replay", "results.jsonl")):
        replay.setdefault(r["module"], []).append(r)
    check("replay: every module replayed once with exit status 0 by lake env leanchecker, inside the recorded step",
          sorted(replay) == sorted(order) and all(len(v) == 1 and v[0]["exit"] == 0 for v in replay.values())
          and all(norm(v[0]["cmd"][0]).endswith("/bin/lake.exe") and v[0]["cmd"][1:] == ["env", "leanchecker", "--verbose", m]
                  for m, v in replay.items())
          and all(t(replay_run["start"]) <= t(v[0]["start"]) and t(v[0]["end"]) <= t(replay_run["end"])
                  for v in replay.values()))
    check("replay: the .olean hash taken after each module equals the build's",
          all(replay[m][0].get("olean_sha256") == olean[m] for m in order if m in replay))
    with tarfile.open(os.path.join(R, "replay", "logs.tar.gz"), "r:gz") as tar:
        logs = {os.path.basename(m.name)[:-4]: tar.extractfile(m).read() for m in tar.getmembers() if m.isfile()}
    check("replay: every log has the recorded size and is the single line 'replaying <module>' for its own module",
          sorted(logs) == sorted(order) and all(
              logs[m].decode("utf-8", errors="replace").splitlines() == [f"replaying {m}"]
              and len(logs[m]) == replay[m][0]["log_bytes"] for m in order if m in replay))
    check("replay: summary.json, summary.md and log-check.json are what tools/summarize_results.py and "
          "tools/verify_build_logs.py write from results.jsonl and the logs",
          regenerated("replay", replay=True)
          and load(os.path.join(R, "replay", "log-check.json"))["logs_not_exactly_replaying_own_module"] == [])

# exports, statistics, dependency analysis
exports = {}
LISTS = {"table.ndjson": "table-names.txt", "free.ndjson": "free-names.txt"}
for sub, name in (("table-export", "table.ndjson"), ("free-export", "free.ndjson")):
    path = os.path.join(R, "kernels", sub, "kernels.jsonl")
    if not present(path):
        continue
    recs = jsonl(path)
    e = recs[-1]
    exports[name] = e
    snapshots.extend((e["before"], e["after"]))
    lists = {"<package>/audit/table-modules.txt", f"<package>/audit/{LISTS[name]}"}
    export_key = f"<package>/.lake/exports/{name}"
    lean_path = [norm(p) for p in e["lean_path"].split(";" if ";" in e["lean_path"] else ":") if p]
    allowed = re.compile(r"^(<package>/\.lake/packages/[^/]+/\.lake/build/lib/lean|<package>/\.lake/build/lib/lean|"
                         r"<toolchain>/lib/lean)/?$")
    header = json.loads(e["export_header"])
    check(f"export {name}: one record; leanexport of the toolchain; exit 0; snapshots before and after equal but for the "
          f"export; made from audit/table-modules.txt and audit/{LISTS[name]}; LEAN_PATH inside the hashed "
          f"directories; the toolchain's commit in the header; started after the build",
          len(recs) == 1 and norm(e["cmd"][0]) == "<toolchain>/bin/leanexport.exe" and e["exit"] == 0
          and e["unchanged"] and same(e["before"], dict(e["after"], files={k: v for k, v in e["after"]["files"].items()
                                                                         if norm(k) != export_key}))
          and snapshot_ok(name, e["before"], lists) and snapshot_ok(name, e["after"], lists | {export_key})
          and e["after"]["files"].get(export_key, {}).get("sha256") == e["export_sha256"]
          and norm(e["export_file"]) == export_key and lean_path and all(allowed.match(p) for p in lean_path)
          and header["meta"]["lean"]["githash"] == githash and t(e["start"]) > build_end)
for stats, name in (("table-stats.json", "table.ndjson"), ("free-stats.json", "free.ndjson"),
                    ("table-taint.json", "table.ndjson")):
    path = os.path.join(R, "kernels", stats)
    if name not in exports or not present(path):
        continue
    s = load(path)
    e = exports[name]
    check(f"{stats}: read the bytes of the export record of {name}, after that export was written",
          s.get("sha256") == e["export_sha256"] and s.get("bytes") == e["export_bytes"]
          and s.get("program_sha256") == tools.get(s.get("program")) and t(s["start"]) > t(e["end"]))
    if "stats" in stats:
        names = [l.strip() for l in open(os.path.join(HERE, "audit", LISTS[name]), encoding="utf-8") if l.strip()]
        check(f"{stats}: the {len(names)} theorems of audit/{LISTS[name]} are theorems of the export; its axioms are the three",
              s.get("find", {}) and local(s["find"]["file"]) and sha(local(s["find"]["file"])) == s["find"]["sha256"]
              and norm(s["find"]["file"]) == f"audit/{LISTS[name]}" and s["requested"] == len(names)
              and s["requested_not_theorems"] == {} and s["axioms"] == sorted(AXIOMS)
              and s["header"]["meta"]["lean"]["githash"] == githash)
if "table.ndjson" in exports and os.path.exists(os.path.join(R, "kernels", "table-taint.json")):
    taint = load(os.path.join(R, "kernels", "table-taint.json"))
    free_names = [l.strip() for l in open(os.path.join(HERE, "audit", "free-names.txt"), encoding="utf-8") if l.strip()]
    table_names = [l.strip() for l in open(os.path.join(HERE, "audit", "table-names.txt"), encoding="utf-8") if l.strip()]
    check("table-taint.json: from audit/table-names.txt and audit/markers.json, every marker found, every theorem in the "
          "export, no forward reference to a marked declaration, and the free theorems are those of audit/free-names.txt",
          {norm(k) for k in taint["inputs"]} == {"audit/table-names.txt", "audit/markers.json"}
          and all(local(k) and sha(local(k)) == v for k, v in taint["inputs"].items())
          and all(taint["markers_found"].values()) and taint["not_in_export"] == [] and taint["requested"] == len(table_names)
          and taint["forward_references_to_classed_declarations"] == [] and taint["constants_never_declared"] == []
          and taint["unknown_expression_keys"] == {} and sorted(taint["free_of_all_classes"]) == sorted(free_names))

# checks
rows = []
totals = {}
for name in exports:
    p = os.path.join(R, "kernels", ("table" if name == "table.ndjson" else "free") + "-stats.json")
    if os.path.exists(p):
        totals[name] = load(p)["declarations_total"]
for sub in sorted(os.listdir(os.path.join(R, "kernels"))) if os.path.isdir(os.path.join(R, "kernels")) else []:
    path = os.path.join(R, "kernels", sub, "kernels.jsonl")
    if sub.endswith("-export") or not os.path.isfile(path):
        continue
    for r in jsonl(path):
        e = exports.get(r["export"], {})
        export_key = f"<package>/.lake/exports/{r['export']}"
        expected = {export_key} | ({"<package>/.lake/exports/nanoda.config.json"} if r["kernel"] == "nanoda" else set())
        before, after = r["before"]["files"].get(export_key, {}), r["after"]["files"].get(export_key, {})
        log_path = os.path.join(R, "kernels", sub, r["log"])
        data = open(log_path, "rb").read() if os.path.isfile(log_path) else b""
        text = data.decode("utf-8", errors="replace")
        found = [l.strip() for l in text.splitlines() if re.fullmatch(RESULT[r["kernel"]], l.strip())]
        m = re.fullmatch(RESULT[r["kernel"]], found[-1]) if found else None
        count_ok = True
        if m and m.groups() and r["export"] in totals:
            count_ok = int(m.group(1)) == totals[r["export"]] - (3 if r["kernel"] == "lean4lean" else 0)
        cfg_ok = True
        if r["kernel"] == "nanoda":
            c = r.get("nanoda_config", {})
            cfg_ok = (c.get("permitted_axioms") == AXIOMS and c.get("unpermitted_axiom_hard_error") is True
                      and os.path.basename(norm(c.get("export_file_path", ""))) == r["export"])
        row = dict(export=r["export"], checker=r["kernel"], record=f"{sub}/kernels.jsonl", start=r["start"],
                   end=r["end"], exit=r["exit"], wall_s=r["wall_s"], cpu_s=r["cpu_s"],
                   peak_commit_gib=round(r["peak_commit_proc_bytes"] / 2 ** 30, 2),
                   export_sha256_before=before.get("sha256"), export_sha256_after=after.get("sha256"),
                   result_line=found[-1] if m else None)
        snapshots.extend((r["before"], r["after"]))
        check(f"check {r['kernel']} of {r['export']}: its checker on the bytes of the export record, hashed before and "
              f"after; exit 0; log as recorded, stating acceptance; started after the export was written",
              e and row["exit"] == 0 and same(r["before"], r["after"]) and r["unchanged"] and m is not None and count_ok
              and cfg_ok and os.path.basename(norm(r["cmd"][0])) == EXE[r["kernel"]] and norm(r["cmd"][0]).startswith("<toolchain>/bin/")
              and any(norm(a) == export_key or norm(a).endswith("/nanoda.config.json") for a in r["cmd"][1:])
              and {norm(k) for k in r["before"]["files"]} == expected and {norm(k) for k in r["after"]["files"]} == expected
              and row["export_sha256_before"] == row["export_sha256_after"] == e.get("export_sha256")
              and before.get("bytes") == e.get("export_bytes") and r["before"]["tools"] == tools
              and len(data) == r["log_bytes"] and data[-1500:].decode("utf-8", errors="replace") == r["tail"]
              and t(row["start"]) > t(e["end"]))
        rows.append(row)
expected_checks = {("free.ndjson", k) for k in ("lean", "paranoid", "nanoda", "lean4lean", "con-leche", "con-ron")} | {
    ("table.ndjson", k) for k in ("lean", "lean4lean")}
if not PARTIAL:
    check("checks: each of the eight checks recorded once",
          sorted((r["export"], r["checker"]) for r in rows) == sorted(expected_checks))
for part in ("bin", "lib"):
    check(f"every snapshot names the same toolchain {part}/ (where taken)",
          len({json.dumps(s["toolchain"].get(part), sort_keys=True) for s in snapshots if part in s["toolchain"]}) <= 1)
for part in ("build_lib", "packages", "python"):
    check(f"every snapshot that takes it names the same {part}",
          len({json.dumps(s[part], sort_keys=True) for s in snapshots if part in s}) <= 1)
table = dict(exports={n: dict(sha256=e["export_sha256"], bytes=e["export_bytes"], lines=e["export_lines"],
                              record=("table" if n == "table.ndjson" else "free") + "-export/kernels.jsonl")
                      for n, e in exports.items()},
             checks=rows)
checks_path = os.path.join(R, "kernels", "checks.json")
if "--write-checks" in sys.argv[1:]:
    with open(checks_path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(table, fh, indent=1, ensure_ascii=False)
        fh.write("\n")
if not PARTIAL or os.path.exists(checks_path):
    check("records/kernels/checks.json is the table of these checks", os.path.isfile(checks_path) and load(checks_path) == table)

# the table of theorems
audit_log = os.path.join(R, "audit", "ScopeAxioms.log")
if present(audit_log):
    with tempfile.TemporaryDirectory() as tmp:
        run = subprocess.run([sys.executable, "-B", os.path.join(HERE, "tools", "make_theorem_table.py"),
                              os.path.join(HERE, "scope.json"), HERE, os.path.join(HERE, "audit", "theorems.json"),
                              audit_log, os.path.join(tmp, "THEOREMS.md"), os.path.join(tmp, "theorem-table.json")],
                             capture_output=True)
        check("THEOREMS.md and audit/theorem-table.json are generated from records/audit/ScopeAxioms.log",
              run.returncode == 0 and sha(os.path.join(tmp, "THEOREMS.md")) == sha(os.path.join(HERE, "THEOREMS.md"))
              and sha(os.path.join(tmp, "theorem-table.json")) == sha(os.path.join(HERE, "audit", "theorem-table.json")))

failed = [text for text, ok in results if not ok]
print("ALL RECORDS CONSISTENT" if not failed else f"{len(failed)} CHECKS FAILED")
sys.exit(0 if not failed else 1)
