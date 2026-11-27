"""SHA-256 snapshot of what a Lean step reads: the tools, the interpreter, the toolchain, the package configuration,
the sources and compiled files of the scope, the compiled files of the dependencies, and given files.

Usage: python snapshot.py <scope.json> <Lake package dir> <out.json> [--file <path> ...]
(as a module: snapshot(scope_path, formal, files) returns the record)

The record holds the time; the SHA-256 of every program in this directory and of the Python interpreter that runs
it; of every file in the bin/ directory of the toolchain, and a digest of all files of its lib/ directory; of
lakefile.toml, lake-manifest.json, lean-toolchain and scope.json; for the scope, the number of sources whose SHA-256
equals the one in scope.json and the digests of the lists "<SHA-256>  <path>" of its sources, .olean files and .ilean
files in the order of scope.json (the .olean digest is the list_sha256 of olean_receipts.py); a digest of every file
under .lake/build/lib/lean (all parts of the compiled modules: .olean, .olean.server, .olean.private, .ir, .ir.sig,
.ilean, and Lake's .hash and .trace files) and one of every file under .lake/packages/*/.lake/build/lib together with
the configuration files at the top of each dependency, each with the number of files by suffix; and for each given
file its SHA-256, size and first line. A digest is the SHA-256 of the list of "<SHA-256>  <relative path>" lines, one
per file, each ending in a newline, sorted by path.
"""
import datetime
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PACKAGE_FILES = ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "scope.json")
CONFIG_FILES = ("lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def now():
    return datetime.datetime.now().astimezone().isoformat(timespec="seconds")


def digest(lines):
    return hashlib.sha256("".join(line + "\n" for line in lines).encode("utf-8")).hexdigest()


def suffix(name):
    i = name.find(".")
    return name[i:] if i >= 0 else ""


def digest_of(paths, root):
    """Digest of the given files, by path relative to root, with the number of files by suffix."""
    lines, counts = [], {}
    for path in paths:
        rel = os.path.relpath(path, root).replace("\\", "/")
        lines.append(f"{sha256_file(path)}  {rel}")
        s = suffix(os.path.basename(path))
        counts[s] = counts.get(s, 0) + 1
    lines.sort(key=lambda line: line.split("  ", 1)[1])
    return {"files": len(lines), "by_suffix": dict(sorted(counts.items())), "digest": digest(lines)}


def walk(root):
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames.sort()
        out.extend(os.path.join(dirpath, name) for name in filenames)
    return out


def toolchain_dir():
    sys.path.insert(0, HERE)
    import gated_runner
    return os.path.dirname(os.path.abspath(gated_runner.default_toolchain_bin()))


def file_info(path):
    with open(path, "rb") as fh:
        first = fh.readline()
    return {"sha256": sha256_file(path), "bytes": os.path.getsize(path),
            "first_line": first[:300].decode("utf-8", errors="replace").rstrip("\r\n")}


def snapshot(scope_path, formal, files=(), packages=True, lib=True):
    """With scope_path None, only the time, the tools, the interpreter, the toolchain and the given files; with lib
    False, the toolchain without its lib/ directory."""
    tc = toolchain_dir()
    record = {
        "time": now(),
        "python": {"version": sys.version, "sha256": sha256_file(sys.executable)},
        "tools": {name: sha256_file(os.path.join(HERE, name)) for name in sorted(os.listdir(HERE)) if name.endswith(".py")},
        "toolchain": {"bin": {name: sha256_file(os.path.join(tc, "bin", name))
                              for name in sorted(os.listdir(os.path.join(tc, "bin")))
                              if os.path.isfile(os.path.join(tc, "bin", name))}},
    }
    if lib:
        record["toolchain"]["lib"] = digest_of(walk(os.path.join(tc, "lib")), os.path.join(tc, "lib"))
    if scope_path is not None:
        scope = json.load(open(scope_path, encoding="utf-8"))
        order = scope["order"]
        lib_dir = os.path.join(formal, ".lake", "build", "lib", "lean")
        sources, oleans, ileans, missing = [], [], [], []
        equal = 0
        for m in order:
            rel = scope["modules"][m]["path"]
            h = sha256_file(os.path.join(formal, rel))
            equal += h == scope["modules"][m]["sha256"]
            sources.append(f"{h}  {rel}")
            base = os.path.join(lib_dir, *m.split("."))
            for ext, rows in (("olean", oleans), ("ilean", ileans)):
                path = base + "." + ext
                if os.path.exists(path):
                    rows.append(f"{sha256_file(path)}  {m.replace('.', '/')}.{ext}")
                else:
                    missing.append(f"{m}.{ext}")
        record["package_files"] = {name: sha256_file(os.path.join(formal, name)) for name in PACKAGE_FILES}
        record["scope"] = {"modules": len(order), "sources_equal_to_scope": equal, "sources_digest": digest(sources),
                           "olean_digest": digest(oleans), "ilean_digest": digest(ileans), "missing": missing}
        record["build_lib"] = digest_of(walk(lib_dir), lib_dir)
        if packages:
            root = os.path.join(formal, ".lake", "packages")
            paths = []
            for pkg in sorted(os.listdir(root)):
                paths.extend(os.path.join(root, pkg, name) for name in CONFIG_FILES
                             if os.path.isfile(os.path.join(root, pkg, name)))
                compiled = os.path.join(root, pkg, ".lake", "build", "lib")
                if os.path.isdir(compiled):
                    paths.extend(walk(compiled))
            record["packages"] = digest_of(paths, root)
    record["files"] = {path.replace("\\", "/"): file_info(path) for path in files}
    return record


def same(a, b):
    """The two snapshots agree in everything but the time."""
    return {k: v for k, v in a.items() if k != "time"} == {k: v for k, v in b.items() if k != "time"}


if __name__ == "__main__":
    args = sys.argv[1:]
    extra = [args[i + 1] for i, a in enumerate(args) if a == "--file"]
    scope_path, formal, out = [a for i, a in enumerate(args) if a != "--file" and (i == 0 or args[i - 1] != "--file")]
    rec = snapshot(scope_path, os.path.abspath(formal), extra)
    with open(out, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(rec, fh, indent=1)
        fh.write("\n")
    print(f"{rec['time']}: {rec['scope']['sources_equal_to_scope']} of {rec['scope']['modules']} sources equal to "
          f"scope.json, {len(rec['scope']['missing'])} compiled files missing, olean digest "
          f"{rec['scope']['olean_digest'][:16]}, build lib {rec['build_lib']['files']} files, packages "
          f"{rec.get('packages', {}).get('files')} files")
