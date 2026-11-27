"""Totals of a gated_runner results file.

Usage: python summarize_results.py <scope.json> <results.jsonl> <out json> [<out md>]

Writes the totals (modules, attempts, failures, elapsed time, sums of wall and CPU time,
peaks) and, in the Markdown file, the per-library totals and the twenty longest modules.
CPU time is that of the Windows job object of each command (the command and all its child
processes); `lean` CPU and working sets are sampled every two seconds.
"""
import datetime
import json
import sys

scope = json.load(open(sys.argv[1], encoding="utf-8"))
recs = [json.loads(l) for l in open(sys.argv[2], encoding="utf-8")]
out = sys.argv[3]
out_md = sys.argv[4] if len(sys.argv) > 4 else None
G = 2 ** 30

ok = [r for r in recs if r["exit"] == 0]
bad = [r for r in recs if r["exit"] != 0]
mods_ok = {r["module"] for r in ok}
dup = len(ok) - len(mods_ok)
t0 = min(datetime.datetime.fromisoformat(r["start"]) for r in recs)
t1 = max(datetime.datetime.fromisoformat(r["end"]) for r in recs)
by_lib = {}
for r in ok:
    lib = scope["modules"][r["module"]]["lib"]
    c = by_lib.setdefault(lib, dict(modules=0, wall_s=0.0, cpu_s=0.0, lines=0))
    c["modules"] += 1
    c["wall_s"] += r["wall_s"]
    c["cpu_s"] += r["cpu_s"]
    c["lines"] += scope["modules"][r["module"]]["lines"]
res = dict(
    results_file=sys.argv[2].replace("\\", "/"),
    scope_modules=len(scope["order"]),
    attempts=len(recs),
    modules_ok=len(mods_ok),
    modules_ok_twice=dup,
    failed_attempts=[(r["module"], r["exit"]) for r in bad],
    missing=[m for m in scope["order"] if m not in mods_ok],
    first_start=t0.isoformat(),
    last_end=t1.isoformat(),
    elapsed_s=round((t1 - t0).total_seconds()),
    sum_wall_s=round(sum(r["wall_s"] for r in recs), 1),
    sum_cpu_s=round(sum(r["cpu_s"] for r in recs), 1),
    sum_cpu_hours=round(sum(r["cpu_s"] for r in recs) / 3600, 2),
    sum_lean_cpu_sampled_s=round(sum(r.get("lean_cpu_sampled_s", 0) for r in recs), 1),
    max_lean_peak_ws_gib=round(max(r["lean_peak_ws_bytes"] for r in recs) / G, 2),
    max_peak_commit_proc_gib=round(max(r["peak_commit_proc_bytes"] for r in recs) / G, 2),
    max_peak_commit_job_gib=round(max(r["peak_commit_job_bytes"] for r in recs) / G, 2),
    module_of_max_ws=max(recs, key=lambda r: r["lean_peak_ws_bytes"])["module"],
    module_of_max_commit=max(recs, key=lambda r: r["peak_commit_proc_bytes"])["module"],
    max_committed_at_start_gib=max(r["gate_at_start"]["committed_gib"] for r in recs),
    min_avail_at_start_mb=min(r["gate_at_start"]["avail_mb"] for r in recs),
    max_running_at_start=max(len(r["gate_at_start"]["running"]) for r in recs) + 1,
    by_library={k: {kk: (round(vv, 1) if isinstance(vv, float) else vv) for kk, vv in v.items()} for k, v in by_lib.items()},
)
with open(out, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(res, fh, indent=1)
    fh.write("\n")
print(json.dumps({k: v for k, v in res.items() if k != "missing"}, indent=1))
print("missing:", len(res["missing"]), res["missing"][:10])
if out_md:
    L = ["| Library | Modules | Lines | Sum of wall time (s) | CPU time (s) |", "|---|---:|---:|---:|---:|"]
    for k in sorted(by_lib):
        v = by_lib[k]
        L.append(f"| `{k}` | {v['modules']} | {v['lines']:,} | {v['wall_s']:,.0f} | {v['cpu_s']:,.0f} |")
    L.append(f"| all | {len(mods_ok)} | {sum(v['lines'] for v in by_lib.values()):,} | "
             f"{sum(v['wall_s'] for v in by_lib.values()):,.0f} | {sum(v['cpu_s'] for v in by_lib.values()):,.0f} |")
    L.append("")
    L.append("| Module | Wall (s) | CPU (s) | Peak working set (GiB) | Peak commit (GiB) |")
    L.append("|---|---:|---:|---:|---:|")
    for r in sorted(ok, key=lambda r: -r["cpu_s"])[:20]:
        L.append(f"| `{r['module']}` | {r['wall_s']:,.0f} | {r['cpu_s']:,.0f} | {r['lean_peak_ws_bytes'] / G:.2f} | "
                 f"{r['peak_commit_proc_bytes'] / G:.2f} |")
    with open(out_md, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(L) + "\n")
