"""Record the state of the Lake package before or after a recorded run.

Usage: python record_state.py <scope.json> <Lake package dir> <out.json>

Writes: the time, the SHA-256 of every source of the scope and whether it equals the one in scope.json,
the versions of lean and lake (from the toolchain found on PATH or in LEAN_TOOLCHAIN_BIN), the platform,
and the compiled files present under .lake/build for modules of the scope.
"""
import datetime
import hashlib
import json
import os
import platform
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gated_runner as gr  # noqa: E402

scope_p, pkg, out = sys.argv[1:4]
scope = json.load(open(scope_p, encoding="utf-8"))


def run(cmd, cwd=None):
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as e:
        return f"error: {e}"


tc = gr.default_toolchain_bin()
sources = {}
for m in scope["order"]:
    p = os.path.join(pkg, scope["modules"][m]["path"])
    h = hashlib.sha256(open(p, "rb").read()).hexdigest()
    sources[m] = {"sha256": h, "equals_scope": h == scope["modules"][m]["sha256"]}
built = sum(1 for m in scope["order"]
            if os.path.exists(os.path.join(pkg, ".lake", "build", "lib", "lean", m.replace(".", "/") + ".olean")))
state = {
    "time": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
    "sources": len(sources),
    "sources_equal_to_scope": sum(1 for v in sources.values() if v["equals_scope"]),
    "sources_sha256": {m: v["sha256"] for m, v in sources.items()},
    "lean_version": run([os.path.join(tc, "lean"), "--version"]),
    "lake_version": run([os.path.join(tc, "lake"), "--version"]),
    "platform": platform.platform(),
    "processors": os.cpu_count(),
    "compiled_modules_present": built,
}
json.dump(state, open(out, "w", encoding="utf-8", newline="\n"), indent=1)
print(f"sources equal to scope.json {state['sources_equal_to_scope']} of {state['sources']}; "
      f"compiled modules present {built}")
