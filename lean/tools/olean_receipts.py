"""SHA-256 receipts of the compiled files of the scope.

Usage: python olean_receipts.py <scope.json> <formal dir> <out receipts.json> [<out sha256 list>]

For every module of the scope: size and SHA-256 of its .olean and .ilean under
<formal>/.lake/build/lib/lean.  Also a digest of the whole list, and a count
of the files under .lake/build that belong to modules outside the scope
(expected: none in a clean tree).
"""
import hashlib
import json
import os
import sys

scope = json.load(open(sys.argv[1], encoding="utf-8"))
formal = os.path.abspath(sys.argv[2])
out = sys.argv[3]
out_list = sys.argv[4] if len(sys.argv) > 4 else None
lib = os.path.join(formal, ".lake", "build", "lib", "lean")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for c in iter(lambda: fh.read(1 << 22), b""):
            h.update(c)
    return h.hexdigest()


rows = {}
missing = []
for m in scope["order"]:
    base = os.path.join(lib, *m.split("."))
    row = {}
    for ext in ("olean", "ilean"):
        p = base + "." + ext
        if os.path.exists(p):
            row[ext + "_bytes"] = os.path.getsize(p)
            row[ext + "_sha256"] = sha(p)
        else:
            missing.append(m + "." + ext)
    rows[m] = row

# every .olean under the build tree, to detect modules outside the scope
present = []
for root, _dirs, files in os.walk(lib):
    for f in files:
        if f.endswith(".olean"):
            rel = os.path.relpath(os.path.join(root, f), lib).replace("\\", "/")
            present.append(rel[:-6].replace("/", "."))
outside = sorted(set(present) - set(scope["order"]))

lines = [f"{rows[m].get('olean_sha256', 'MISSING')}  {m.replace('.', '/')}.olean" for m in scope["order"]]
digest = hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()
total = sum(r.get("olean_bytes", 0) for r in rows.values())
result = dict(formal=formal.replace("\\", "/"), modules=len(rows), missing=missing, olean_outside_scope=outside,
              olean_total_bytes=total, list_sha256=digest, receipts=rows)
with open(out, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(result, fh, indent=1)
    fh.write("\n")
if out_list:
    with open(out_list, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(lines) + "\n")
print(f"{len(rows)} modules, {len(missing)} missing files {missing[:5]}, {len(outside)} .olean outside the scope "
      f"{outside[:5]}, total .olean {total / 1e6:.1f} MB, list digest {digest}")
