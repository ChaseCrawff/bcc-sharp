"""Check the per-module logs of a build run or of a replay run.

Usage: python verify_build_logs.py <scope.json> <outdir of gated_runner> <out json> [--replay]

For every module of the scope: its log must contain exactly one line "Built <X>", with X the
module itself (so the Lake call compiled this module and no other), the line "Build completed
successfully", and no line starting with "error".  Also counts warnings by the module they
are reported for, and collects the build time that Lake prints.  With --replay (logs of
`leanchecker --verbose M`): every log must consist of the single line "replaying M" for its
own module.
"""
import json
import os
import re
import sys

scope = json.load(open(sys.argv[1], encoding="utf-8"))
outdir = sys.argv[2]
out = sys.argv[3]
if "--replay" in sys.argv[4:]:
    wrong = []
    for m in scope["order"]:
        p = os.path.join(outdir, "logs", m + ".log")
        if not os.path.exists(p) or open(p, "rb").read().decode("utf-8", errors="replace").splitlines() != [
                f"replaying {m}"]:
            wrong.append(m)
    with open(out, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(dict(modules=len(scope["order"]), logs_not_exactly_replaying_own_module=wrong), fh, indent=1)
        fh.write("\n")
    print(f"{len(scope['order'])} modules, {len(wrong)} logs not exactly 'replaying <module>': {wrong[:5]}")
    sys.exit(1 if wrong else 0)
bad = {}
lake_time = {}
own_warnings = {}
total_bytes = 0
for m in scope["order"]:
    p = os.path.join(outdir, "logs", m + ".log")
    if not os.path.exists(p):
        bad[m] = "no log"
        continue
    data = open(p, "rb").read()
    total_bytes += len(data)
    text = data.decode("utf-8", errors="replace")
    built = re.findall(r"Built (\S+)(?: \(([0-9.]+)(ms|s|m)\))?", text)
    names = [b[0] for b in built]
    problems = []
    if names != [m]:
        problems.append(f"Built lines: {names[:5]}")
    if "Build completed successfully" not in text:
        problems.append("no success line")
    if re.search(r"(?m)^error", text):
        problems.append("error line")
    if problems:
        bad[m] = "; ".join(problems)
    if built and built[0][1]:
        v = float(built[0][1])
        unit = built[0][2]
        lake_time[m] = v / 1000 if unit == "ms" else (v * 60 if unit == "m" else v)
    path = scope["modules"][m]["path"]
    own_warnings[m] = len(re.findall(r"(?m)^warning: " + re.escape(path) + ":", text))
res = dict(modules=len(scope["order"]), problems=bad, logs_total_bytes=total_bytes,
           sum_lake_module_time_s=round(sum(lake_time.values()), 1), lake_time_reported=len(lake_time),
           modules_with_own_warnings=sum(1 for v in own_warnings.values() if v),
           own_warnings_total=sum(own_warnings.values()), lake_time_s=lake_time)
with open(out, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(res, fh, indent=1)
    fh.write("\n")
print(f"{res['modules']} modules, {len(bad)} with problems {list(bad.items())[:5]}; logs {total_bytes / 1e6:.1f} MB; "
      f"sum of Lake's module times {res['sum_lake_module_time_s']} s over {len(lake_time)} modules; "
      f"warnings in the modules' own files: {res['own_warnings_total']} in {res['modules_with_own_warnings']} modules")
