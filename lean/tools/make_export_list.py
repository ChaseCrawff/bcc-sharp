"""Write the module list and the declaration list for `leanexport`.

Usage: python make_export_list.py <scope.json> <Lake package dir> <theorems.json> <out modules.txt> <out names.txt>
       [--items A,B,C,D,E,F] [--exclude <name> ...]

The declarations are the theorems of the scope table (audit/theorems.json).
The modules are those that define them (found by scanning the sources of the
scope for the declaration), so that `leanexport` imports no more than needed.
"""
import json
import os
import re
import sys

scope = json.load(open(sys.argv[1], encoding="utf-8"))
formal = sys.argv[2]
table = json.load(open(sys.argv[3], encoding="utf-8"))
out_mods, out_names = sys.argv[4], sys.argv[5]
rest = sys.argv[6:]
items = None
exclude = set()
i = 0
while i < len(rest):
    if rest[i] == "--items":
        items = set(rest[i + 1].split(","))
        i += 2
    elif rest[i] == "--exclude":
        exclude.add(rest[i + 1])
        i += 2
    else:
        sys.exit(f"unknown argument {rest[i]}")

names = [t["name"] for t in table if (items is None or t["item"] in items) and t["name"] not in exclude]
decl = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive)\s+([^\s:({\[]+)")
where = {}
for m in scope["order"]:
    stack = []
    for line in open(os.path.join(formal, scope["modules"][m]["path"]), encoding="utf-8"):
        mm = re.match(r"^namespace\s+(\S+)", line)
        if mm:
            stack.append(mm.group(1))
            continue
        mm = re.match(r"^end\s+(\S+)", line)
        if mm and stack and stack[-1] == mm.group(1):
            stack.pop()
            continue
        mm = decl.match(line)
        if mm:
            where.setdefault(".".join(stack + [mm.group(1)]), m)
missing = [n for n in names if n not in where]
if missing:
    sys.exit(f"declarations not located in the sources: {missing}")
mods = [m for m in scope["order"] if m in {where[n] for n in names}]
with open(out_mods, "w", encoding="utf-8", newline="\n") as fh:
    fh.write("\n".join(mods) + "\n")
with open(out_names, "w", encoding="utf-8", newline="\n") as fh:
    fh.write("\n".join(names) + "\n")
print(f"{len(names)} declarations in {len(mods)} modules")
