"""Which exported theorems depend on which marker declarations?  Direct reading of a `leanexport` file.

Usage: python export_taint.py <export.ndjson> <names file> <markers json> <out json>

<markers json> maps a class name to a list of declaration names, for example
  {"constants": ["...Constants.bcc_primitive_enclosed", ...], "lattice": ["...forest_checked", ...]}

The export lists expressions and declarations in dependency order: an expression line comes
after the lines of its subexpressions, and a declaration after the declarations it uses
(apart from references inside one inductive or mutual block).  One pass therefore suffices:
every expression gets the union of the classes of the constants occurring in it, and every
declaration the union over its type and value, plus its own class if it is a marker.  The
script fails if a constant is used before its declaration outside its own block, so the
ordering assumption is checked, not assumed.

Output: for each requested name the classes it depends on, and the counts; the SHA-256 and size of the export bytes
read and of the names and markers files, the start and end time, and the SHA-256 of this program.
"""
import datetime
import hashlib
import json
import sys

path, names_file, markers_file, out = sys.argv[1:5]
start = datetime.datetime.now().astimezone().isoformat(timespec="seconds")
program_sha256 = hashlib.sha256(open(__file__, "rb").read()).hexdigest()
raw_inputs = {f: open(f, "rb").read() for f in (names_file, markers_file)}   # hashed and parsed from the same bytes
inputs = {f.replace("\\", "/"): hashlib.sha256(data).hexdigest() for f, data in raw_inputs.items()}
export_hash = hashlib.sha256()
export_bytes = 0
want = [l.strip() for l in raw_inputs[names_file].decode("utf-8").splitlines() if l.strip()]
markers = json.loads(raw_inputs[markers_file])
classes = sorted(markers)
bit = {c: 1 << i for i, c in enumerate(classes)}
marker_bit = {}
for c in classes:
    for n in markers[c]:
        marker_bit[n] = marker_bit.get(n, 0) | bit[c]

names = {0: ""}
expr = bytearray(1 << 20)       # class bits of each expression id
const_of = {}                   # expression id -> name id, for constants not yet declared
decl = {}                       # name id -> class bits
pending = {}                    # name id -> list of expression ids waiting for its declaration
EXPR_KEYS = ("app", "lam", "forallE", "letE", "proj", "mdata", "const", "bvar", "sort", "natVal", "strVal",
             "fvar", "mvar", "lit")
decl_count = 0
forward_refs = 0
tainted_forward = []
unknown_keys = {}


def grow(n):
    global expr
    if n >= len(expr):
        expr.extend(bytes(max(len(expr), n + 1 - len(expr))))


def bits_of(obj):
    """Union of the class bits of all expression ids referenced in a declaration object."""
    b = 0
    stack = [obj]
    while stack:
        o = stack.pop()
        if isinstance(o, dict):
            for k, v in o.items():
                if k in ("type", "value", "rhs") and isinstance(v, int):
                    b |= expr[v]
                elif isinstance(v, (dict, list)):
                    stack.append(v)
        elif isinstance(o, list):
            stack.extend(x for x in o if isinstance(x, (dict, list)))
    return b


def declared_names(obj):
    """Name ids declared by a declaration object (the key "name" of nested records)."""
    res = []
    stack = [obj]
    while stack:
        o = stack.pop()
        if isinstance(o, dict):
            if isinstance(o.get("name"), int) and ("type" in o):
                res.append(o["name"])
            stack.extend(v for v in o.values() if isinstance(v, (dict, list)))
        elif isinstance(o, list):
            stack.extend(x for x in o if isinstance(x, (dict, list)))
    return res


lines = 0
with open(path, "rb") as fh:
    for raw in fh:
        lines += 1
        export_hash.update(raw)
        export_bytes += len(raw)
        if lines == 1:
            continue
        o = json.loads(raw)
        if "in" in o:
            if "str" in o:
                pre = names[o["str"]["pre"]]
                names[o["in"]] = (pre + "." if pre else "") + o["str"]["str"]
            else:
                pre = names[o["num"]["pre"]]
                names[o["in"]] = (pre + "." if pre else "") + str(o["num"]["i"])
            continue
        if "il" in o:
            continue
        if "ie" in o:
            e = o["ie"]
            grow(e)
            b = 0
            if "app" in o:
                b = expr[o["app"]["fn"]] | expr[o["app"]["arg"]]
            elif "const" in o:
                n = o["const"]["name"]
                if n in decl:
                    b = decl[n]
                else:
                    pending.setdefault(n, []).append(e)
            elif "lam" in o:
                b = expr[o["lam"]["type"]] | expr[o["lam"]["body"]]
            elif "forallE" in o:
                b = expr[o["forallE"]["type"]] | expr[o["forallE"]["body"]]
            elif "letE" in o:
                b = expr[o["letE"]["type"]] | expr[o["letE"]["value"]] | expr[o["letE"]["body"]]
            elif "proj" in o:
                b = expr[o["proj"]["struct"]]
                n = o["proj"]["typeName"]
                if n in decl:
                    b |= decl[n]
            elif "mdata" in o:
                b = expr[o["mdata"]["expr"]]
            else:
                k = next(k for k in o if k != "ie")
                if k not in ("bvar", "sort", "natVal", "strVal"):
                    unknown_keys[k] = unknown_keys.get(k, 0) + 1
            expr[e] = b
            continue
        # a declaration
        decl_count += 1
        b = bits_of(o)
        ns = declared_names(o)
        for n in ns:
            b |= marker_bit.get(names.get(n, ""), 0)
        for n in ns:
            decl[n] = b
            if n in pending:
                # References emitted before the declaration.  Harmless when the declaration has no
                # class bit (nothing to propagate); counted separately when it has one, because
                # expressions built on such a reference in the meantime did not receive the bit.
                forward_refs += len(pending[n])
                if b:
                    tainted_forward.append(names.get(n, str(n)))
                for e in pending.pop(n):
                    expr[e] |= b

unresolved = sorted(names.get(n, str(n)) for n in pending)
by_name = {names[n]: b for n, b in decl.items()}
res = {}
for w in want:
    if w not in by_name:
        res[w] = None
    else:
        res[w] = [c for c in classes if by_name[w] & bit[c]]
marker_found = {n: (n in by_name) for n in marker_bit}
summary = dict(program="export_taint.py", program_sha256=program_sha256, start=start,
               end=datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
               file=path.replace("\\", "/"), bytes=export_bytes, sha256=export_hash.hexdigest(), inputs=inputs,
               lines=lines, declarations=decl_count, classes=classes,
               markers_found=marker_found, forward_references=forward_refs,
               forward_references_to_classed_declarations=sorted(set(tainted_forward)),
               unknown_expression_keys=unknown_keys,
               constants_never_declared=unresolved[:50],
               requested=len(want), not_in_export=[w for w in want if res[w] is None],
               free_of_all_classes=[w for w in want if res[w] == []],
               by_class={c: [w for w in want if res[w] and c in res[w]] for c in classes},
               result=res)
with open(out, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(summary, fh, indent=1, ensure_ascii=False)
    fh.write("\n")
print(f"lines {lines}, declarations {decl_count}, forward references {forward_refs} "
      f"(to classed declarations: {sorted(set(tainted_forward))}), never declared {len(unresolved)}, "
      f"unknown expression keys {unknown_keys}")
print("markers found:", marker_found)
print(f"requested {len(want)}: not in export {len(summary['not_in_export'])}, free {len(summary['free_of_all_classes'])}, "
      + ", ".join(f"{c} {len(summary['by_class'][c])}" for c in classes))
