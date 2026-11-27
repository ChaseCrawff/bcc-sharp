"""Compare the .olean hashes of two records.

Usage: python compare_receipts.py <A> <B> [<out json>]

Each of A and B is either a receipts file of olean_receipts.py (JSON with "receipts") or a
results file of gated_runner.py run with --hash-olean (JSON lines).  Reports the modules
present in both, the number with equal .olean hash and equal .ilean hash, and the modules
that differ.
"""
import json
import sys


def load(path):
    text = open(path, encoding="utf-8").read()
    if path.endswith(".jsonl"):
        res = {}
        for line in text.splitlines():
            r = json.loads(line)
            if r.get("exit") == 0 and r.get("olean_sha256"):
                res[r["module"]] = dict(olean_sha256=r["olean_sha256"], ilean_sha256=r.get("ilean_sha256"),
                                        olean_bytes=r.get("olean_bytes"))
        return res
    return json.loads(text)["receipts"]


a, b = load(sys.argv[1]), load(sys.argv[2])
common = sorted(set(a) & set(b))
same_o = [m for m in common if a[m].get("olean_sha256") == b[m].get("olean_sha256")]
same_i = [m for m in common if a[m].get("ilean_sha256") == b[m].get("ilean_sha256")]
diff_o = [m for m in common if m not in set(same_o)]
res = dict(a=sys.argv[1].replace("\\", "/"), b=sys.argv[2].replace("\\", "/"), modules_a=len(a), modules_b=len(b),
           common=len(common), olean_equal=len(same_o), ilean_equal=len(same_i), olean_differ=diff_o,
           only_a=sorted(set(a) - set(b)), only_b=sorted(set(b) - set(a)))
if len(sys.argv) > 3:
    with open(sys.argv[3], "w", encoding="utf-8", newline="\n") as fh:
        json.dump(res, fh, indent=1)
        fh.write("\n")
print(f"A {len(a)} modules, B {len(b)} modules, common {len(common)}; .olean equal {len(same_o)}, "
      f".ilean equal {len(same_i)}; .olean differ: {diff_o[:10]}{' ...' if len(diff_o) > 10 else ''}")
