"""Pack a directory of logs into one tar.gz with fixed metadata (same inputs, same bytes).

Usage: python pack_logs.py <directory> <out.tar.gz>
"""
import gzip
import hashlib
import io
import os
import sys
import tarfile

src, out = os.path.abspath(sys.argv[1]), sys.argv[2]
base = os.path.basename(src)
buf = io.BytesIO()
n = size = 0
with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as tar:
    for root, _dirs, files in sorted(os.walk(src)):
        for f in sorted(files):
            p = os.path.join(root, f)
            rel = os.path.relpath(p, src).replace("\\", "/")
            data = open(p, "rb").read()
            ti = tarfile.TarInfo(base + "/" + rel)
            ti.size = len(data)
            ti.mtime = 1795392000
            ti.mode = 0o644
            ti.uid = ti.gid = 0
            ti.uname = ti.gname = ""
            tar.addfile(ti, io.BytesIO(data))
            n += 1
            size += len(data)
with open(out, "wb") as fh:
    with gzip.GzipFile(filename="", mode="wb", fileobj=fh, mtime=0, compresslevel=9) as gz:
        gz.write(buf.getvalue())
print(f"{n} files, {size} bytes -> {out}: {os.path.getsize(out)} bytes, sha256 "
      f"{hashlib.sha256(open(out, 'rb').read()).hexdigest()}")
