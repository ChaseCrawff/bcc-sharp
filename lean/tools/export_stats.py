"""Statistics of a `leanexport` NDJSON file, by a direct reading of the file (no Lean code).

Usage: python export_stats.py <export.ndjson> <out json> [--find <file with one name per line>]

Reports the header, the number of lines, the number of declarations by kind,
the names of all axioms declared in the export, and whether each requested
name occurs as a theorem.  Every declaration that the exported theorems
depend on is in the export, so the list of axioms is the complete list of
axioms on which they can depend.  Also the SHA-256 and size of the bytes read
(and of the --find file, hashed from the bytes that are parsed), the start and
end time, and the SHA-256 of this program.
"""
import datetime
import hashlib
import json
import sys

path, out = sys.argv[1], sys.argv[2]
start = datetime.datetime.now().astimezone().isoformat(timespec="seconds")
program_sha256 = hashlib.sha256(open(__file__, "rb").read()).hexdigest()
want = []
find = None
if len(sys.argv) > 4 and sys.argv[3] == "--find":
    data = open(sys.argv[4], "rb").read()
    find = {"file": sys.argv[4].replace("\\", "/"), "sha256": hashlib.sha256(data).hexdigest()}
    want = [l.strip() for l in data.decode("utf-8").splitlines() if l.strip()]

DECL = (b'{"axiom"', b'{"def"', b'{"thm"', b'{"opaque"', b'{"quot"', b'{"inductive"')
names = {0: ""}
kinds = {}
declared = {}
axioms = []
header = None
lines = 0
h = hashlib.sha256()
size = 0
with open(path, "rb") as fh:
    for raw in fh:
        lines += 1
        h.update(raw)
        size += len(raw)
        if lines == 1:
            header = json.loads(raw)
            continue
        if raw.startswith(b'{"in"'):
            o = json.loads(raw)
            if "str" in o:
                pre = names[o["str"]["pre"]]
                names[o["in"]] = (pre + "." if pre else "") + o["str"]["str"]
            else:
                pre = names[o["num"]["pre"]]
                names[o["in"]] = (pre + "." if pre else "") + str(o["num"]["i"])
            continue
        if not raw.startswith(DECL):
            continue
        o = json.loads(raw)
        k = next(iter(o))
        kinds[k] = kinds.get(k, 0) + 1
        if k in ("axiom", "def", "thm", "opaque", "quot"):
            n = names.get(o[k]["name"], str(o[k]["name"]))
            declared[n] = k
            if k == "axiom":
                axioms.append(n)

found = {w: declared.get(w) for w in want}
res = dict(program="export_stats.py", program_sha256=program_sha256, start=start,
           end=datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
           file=path.replace("\\", "/"), bytes=size, sha256=h.hexdigest(), header=header, lines=lines,
           declarations=kinds, declarations_total=sum(kinds.values()), axioms=sorted(axioms),
           names_in_table=len(names), find=find, requested=len(want),
           requested_not_theorems={w: k for w, k in found.items() if k != "thm"})
with open(out, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(res, fh, indent=1, ensure_ascii=False)
    fh.write("\n")
print(json.dumps(res, ensure_ascii=False))
