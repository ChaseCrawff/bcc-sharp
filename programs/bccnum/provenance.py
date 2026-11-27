"""Provenance block written with every result file.

Records the program and the SHA-256 of its source, of every module of this package and of every input file, taken
when the run starts, and whether all of them are unchanged when the result is written; the parameters, the
interpreter, the versions of python-flint, FLINT, numpy and SciPy, the start time and the wall time. A run during
which a source or an input changed still writes its result (with "unchanged_at_end": false) and then fails.
"""
import datetime
import hashlib
import json
import os
import platform
import sys
import time

PROGRAMS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PACKAGE_DIR = os.path.join(PROGRAMS_DIR, "bccnum")
RESULTS_DIR = os.path.join(PROGRAMS_DIR, "results")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def package_versions():
    out = {}
    for name in ("flint", "numpy", "scipy"):
        try:
            mod = __import__(name)
            out[name] = getattr(mod, "__version__", None)
            if name == "flint":
                out["FLINT"] = getattr(mod, "__FLINT_VERSION__", None)
        except ImportError:
            out[name] = None
    return out


def source_hashes():
    return {"bccnum/" + fn: sha256_file(os.path.join(PACKAGE_DIR, fn))
            for fn in sorted(os.listdir(PACKAGE_DIR)) if fn.endswith(".py")}


class Run:
    """Usage: run = Run(__file__, params, tier, seeds, inputs); ...; run.write(name, results).

    inputs maps the name of each input file to (path, SHA-256 of the bytes the program read, or None to hash the file
    now)."""

    def __init__(self, script_file, params, tier, seeds=None, inputs=None):
        assert tier in ("cert", "expl", "mixed")
        self.script_file = os.path.abspath(script_file)
        self.params = params
        self.tier = tier
        self.seeds = seeds
        self.inputs = {name: (path, digest or sha256_file(path)) for name, (path, digest) in (inputs or {}).items()}
        self.at_start = self.digests(start=True)
        self.t0 = time.perf_counter()
        self.started = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")

    def digests(self, start=False):
        return {"program_sha256": sha256_file(self.script_file), "source_sha256": source_hashes(),
                "inputs_sha256": {name: (digest if start else sha256_file(path))
                                  for name, (path, digest) in self.inputs.items()}}

    def provenance(self):
        at_end = self.digests()
        return {
            "program": os.path.basename(self.script_file),
            "program_sha256": self.at_start["program_sha256"],
            "source_sha256": self.at_start["source_sha256"],
            "inputs_sha256": self.at_start["inputs_sha256"],
            "unchanged_at_end": at_end == self.at_start,
            "parameters": self.params,
            "seeds": self.seeds,
            "python": sys.version,
            "platform": platform.platform(),
            "packages": package_versions(),
            "started_utc": self.started,
            "wall_time_s": round(time.perf_counter() - self.t0, 3),
            "tier": self.tier,
        }

    def write(self, name, results):
        directory = os.environ.get("BCC_RESULTS_DIR") or RESULTS_DIR
        os.makedirs(directory, exist_ok=True)
        path = os.path.join(directory, name + ".json")
        provenance = self.provenance()
        payload = {"provenance": provenance, "results": results}
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(payload, f, indent=1, sort_keys=False, default=str)
            f.write("\n")
        if not provenance["unchanged_at_end"]:
            raise RuntimeError(f"{name}: a source or input file changed during the run")
        return os.path.relpath(path, PROGRAMS_DIR).replace("\\", "/")
