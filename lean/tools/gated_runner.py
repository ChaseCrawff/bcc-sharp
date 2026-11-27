"""Gated per-module runner for the clean build and for the checker runs (Windows).

Usage:
  python gated_runner.py --scope scope.json --formal <Lake package dir> --outdir <dir>
         [--jobs 3] [--command '["lake","build","+{module}"]'] [--ignore-deps]
         [--only <file with module names>] [--resume] [--hash-olean]
         [--max-commit-gib 125] [--min-avail-mb 12000] [--headroom-gib 16]
         [--proc-commit-limit-gib 28] [--timeout-s 14400]

One process per module.  A module is started only when

  * every import of it inside the scope has finished with exit code 0 in this
    run or an earlier run recorded in the same results file (so one Lake call
    compiles exactly one module); with --ignore-deps this condition is dropped;
  * fewer than --jobs processes of this runner are running;
  * the memory gate holds:  system commit charge plus a reservation for this
    runner's own processes that have not yet reached their expected commit is
    below --max-commit-gib and below (commit limit - --headroom-gib), and the
    available physical memory exceeds --min-avail-mb.

Each process tree runs in its own Windows job object.  The job gives the CPU
time (user + kernel) of the command and all its child processes, including
those that have exited, and the peak commit.  Working sets are sampled every
two seconds from the processes of the job.  A per-process commit limit
(--proc-commit-limit-gib) makes an allocation beyond it fail inside that
process instead of exhausting the machine.  The runner stops only processes
of its own jobs.

Outputs in --outdir:  logs/<Module>.log (stdout and stderr of the command),
results.jsonl (one record per attempt), runner.log.
A file named STOP in --outdir makes the runner start nothing new.
"""
import argparse
import ctypes
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from ctypes import wintypes

GIB = 1 << 30
MIB = 1 << 20

kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
psapi = ctypes.WinDLL("psapi", use_last_error=True)
ntdll = ctypes.WinDLL("ntdll")

HANDLE = wintypes.HANDLE
DWORD = wintypes.DWORD
SIZE_T = ctypes.c_size_t


class IO_COUNTERS(ctypes.Structure):
    _fields_ = [(n, ctypes.c_ulonglong) for n in (
        "ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
        "ReadTransferCount", "WriteTransferCount", "OtherTransferCount")]


class JOBOBJECT_BASIC_LIMIT_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("PerProcessUserTimeLimit", ctypes.c_longlong),
        ("PerJobUserTimeLimit", ctypes.c_longlong),
        ("LimitFlags", DWORD),
        ("MinimumWorkingSetSize", SIZE_T),
        ("MaximumWorkingSetSize", SIZE_T),
        ("ActiveProcessLimit", DWORD),
        ("Affinity", SIZE_T),
        ("PriorityClass", DWORD),
        ("SchedulingClass", DWORD),
    ]


class JOBOBJECT_EXTENDED_LIMIT_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("BasicLimitInformation", JOBOBJECT_BASIC_LIMIT_INFORMATION),
        ("IoInfo", IO_COUNTERS),
        ("ProcessMemoryLimit", SIZE_T),
        ("JobMemoryLimit", SIZE_T),
        ("PeakProcessMemoryUsed", SIZE_T),
        ("PeakJobMemoryUsed", SIZE_T),
    ]


class JOBOBJECT_BASIC_ACCOUNTING_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("TotalUserTime", ctypes.c_longlong),
        ("TotalKernelTime", ctypes.c_longlong),
        ("ThisPeriodTotalUserTime", ctypes.c_longlong),
        ("ThisPeriodTotalKernelTime", ctypes.c_longlong),
        ("TotalPageFaultCount", DWORD),
        ("TotalProcesses", DWORD),
        ("ActiveProcesses", DWORD),
        ("TotalTerminatedProcesses", DWORD),
    ]


class JOBOBJECT_BASIC_PROCESS_ID_LIST(ctypes.Structure):
    _fields_ = [
        ("NumberOfAssignedProcesses", DWORD),
        ("NumberOfProcessIdsInList", DWORD),
        ("ProcessIdList", SIZE_T * 256),
    ]


class PROCESS_MEMORY_COUNTERS_EX(ctypes.Structure):
    _fields_ = [
        ("cb", DWORD),
        ("PageFaultCount", DWORD),
        ("PeakWorkingSetSize", SIZE_T),
        ("WorkingSetSize", SIZE_T),
        ("QuotaPeakPagedPoolUsage", SIZE_T),
        ("QuotaPagedPoolUsage", SIZE_T),
        ("QuotaPeakNonPagedPoolUsage", SIZE_T),
        ("QuotaNonPagedPoolUsage", SIZE_T),
        ("PagefileUsage", SIZE_T),
        ("PeakPagefileUsage", SIZE_T),
        ("PrivateUsage", SIZE_T),
    ]


class PERFORMANCE_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("cb", DWORD),
        ("CommitTotal", SIZE_T),
        ("CommitLimit", SIZE_T),
        ("CommitPeak", SIZE_T),
        ("PhysicalTotal", SIZE_T),
        ("PhysicalAvailable", SIZE_T),
        ("SystemCache", SIZE_T),
        ("KernelTotal", SIZE_T),
        ("KernelPaged", SIZE_T),
        ("KernelNonpaged", SIZE_T),
        ("PageSize", SIZE_T),
        ("HandleCount", DWORD),
        ("ProcessCount", DWORD),
        ("ThreadCount", DWORD),
    ]


kernel32.CreateJobObjectW.restype = HANDLE
kernel32.CreateJobObjectW.argtypes = [wintypes.LPVOID, wintypes.LPCWSTR]
kernel32.AssignProcessToJobObject.argtypes = [HANDLE, HANDLE]
kernel32.AssignProcessToJobObject.restype = wintypes.BOOL
kernel32.SetInformationJobObject.argtypes = [HANDLE, ctypes.c_int, wintypes.LPVOID, DWORD]
kernel32.SetInformationJobObject.restype = wintypes.BOOL
kernel32.QueryInformationJobObject.argtypes = [HANDLE, ctypes.c_int, wintypes.LPVOID, DWORD, ctypes.POINTER(DWORD)]
kernel32.QueryInformationJobObject.restype = wintypes.BOOL
kernel32.TerminateJobObject.argtypes = [HANDLE, wintypes.UINT]
kernel32.TerminateJobObject.restype = wintypes.BOOL
kernel32.OpenProcess.restype = HANDLE
kernel32.OpenProcess.argtypes = [DWORD, wintypes.BOOL, DWORD]
kernel32.CloseHandle.argtypes = [HANDLE]
kernel32.GetProcessTimes.argtypes = [HANDLE] + [ctypes.POINTER(wintypes.FILETIME)] * 4
kernel32.GetProcessTimes.restype = wintypes.BOOL
kernel32.QueryFullProcessImageNameW.argtypes = [HANDLE, DWORD, wintypes.LPWSTR, ctypes.POINTER(DWORD)]
kernel32.QueryFullProcessImageNameW.restype = wintypes.BOOL
psapi.GetProcessMemoryInfo.argtypes = [HANDLE, wintypes.LPVOID, DWORD]
psapi.GetProcessMemoryInfo.restype = wintypes.BOOL
psapi.GetPerformanceInfo.argtypes = [wintypes.LPVOID, DWORD]
psapi.GetPerformanceInfo.restype = wintypes.BOOL
ntdll.NtResumeProcess.argtypes = [HANDLE]

JobObjectBasicAccountingInformation = 1
JobObjectBasicProcessIdList = 3
JobObjectExtendedLimitInformation = 9
JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x100
JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x2000
CREATE_SUSPENDED = 0x4
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000


def now():
    return datetime.datetime.now().astimezone().isoformat(timespec="seconds")


def perf():
    pi = PERFORMANCE_INFORMATION()
    pi.cb = ctypes.sizeof(pi)
    if not psapi.GetPerformanceInfo(ctypes.byref(pi), pi.cb):
        raise ctypes.WinError(ctypes.get_last_error())
    return dict(
        committed=pi.CommitTotal * pi.PageSize,
        limit=pi.CommitLimit * pi.PageSize,
        avail=pi.PhysicalAvailable * pi.PageSize,
    )


def ft(x):
    return ((x.dwHighDateTime << 32) | x.dwLowDateTime) / 1e7


class Job:
    def __init__(self, module, cmd, cwd, env, log_path, proc_limit, expect):
        self.module = module
        self.cmd = cmd
        self.expect = expect
        self.log_path = log_path
        self.logf = open(log_path, "wb")
        self.h = kernel32.CreateJobObjectW(None, None)
        if not self.h:
            raise ctypes.WinError(ctypes.get_last_error())
        info = JOBOBJECT_EXTENDED_LIMIT_INFORMATION()
        info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_PROCESS_MEMORY | JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
        info.ProcessMemoryLimit = proc_limit
        if not kernel32.SetInformationJobObject(self.h, JobObjectExtendedLimitInformation, ctypes.byref(info), ctypes.sizeof(info)):
            raise ctypes.WinError(ctypes.get_last_error())
        self.start_iso = now()
        self.t0 = time.time()
        self.p = subprocess.Popen(cmd, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=self.logf,
                                  stderr=subprocess.STDOUT, creationflags=CREATE_SUSPENDED)
        if not kernel32.AssignProcessToJobObject(self.h, int(self.p._handle)):
            err = ctypes.WinError(ctypes.get_last_error())
            self.p.kill()
            raise err
        ntdll.NtResumeProcess(int(self.p._handle))
        self.cur_commit = 0
        self.peak_job_commit_sampled = 0
        self.peak_job_ws_sampled = 0
        self.procs = {}  # pid -> dict(image, peak_ws, peak_commit, cpu)
        self.last_sample = 0.0

    def sample(self):
        lst = JOBOBJECT_BASIC_PROCESS_ID_LIST()
        if not kernel32.QueryInformationJobObject(self.h, JobObjectBasicProcessIdList, ctypes.byref(lst), ctypes.sizeof(lst), None):
            return
        cur_commit = 0
        cur_ws = 0
        for i in range(lst.NumberOfProcessIdsInList):
            pid = int(lst.ProcessIdList[i])
            hp = kernel32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, pid)
            if not hp:
                continue
            try:
                pmc = PROCESS_MEMORY_COUNTERS_EX()
                pmc.cb = ctypes.sizeof(pmc)
                if not psapi.GetProcessMemoryInfo(hp, ctypes.byref(pmc), pmc.cb):
                    continue
                d = self.procs.setdefault(pid, dict(image="", peak_ws=0, peak_commit=0, cpu=0.0))
                if not d["image"]:
                    buf = ctypes.create_unicode_buffer(1024)
                    n = DWORD(1024)
                    if kernel32.QueryFullProcessImageNameW(hp, 0, buf, ctypes.byref(n)):
                        d["image"] = os.path.basename(buf.value).lower()
                d["peak_ws"] = max(d["peak_ws"], pmc.PeakWorkingSetSize)
                d["peak_commit"] = max(d["peak_commit"], pmc.PeakPagefileUsage)
                c, e, kt, ut = (wintypes.FILETIME() for _ in range(4))
                if kernel32.GetProcessTimes(hp, ctypes.byref(c), ctypes.byref(e), ctypes.byref(kt), ctypes.byref(ut)):
                    d["cpu"] = ft(kt) + ft(ut)
                cur_commit += pmc.PagefileUsage
                cur_ws += pmc.WorkingSetSize
            finally:
                kernel32.CloseHandle(hp)
        self.cur_commit = cur_commit
        self.peak_job_commit_sampled = max(self.peak_job_commit_sampled, cur_commit)
        self.peak_job_ws_sampled = max(self.peak_job_ws_sampled, cur_ws)
        self.last_sample = time.time()

    def reservation(self):
        return max(0, self.expect - self.cur_commit)

    def finish(self, status=None):
        acct = JOBOBJECT_BASIC_ACCOUNTING_INFORMATION()
        kernel32.QueryInformationJobObject(self.h, JobObjectBasicAccountingInformation, ctypes.byref(acct), ctypes.sizeof(acct), None)
        ext = JOBOBJECT_EXTENDED_LIMIT_INFORMATION()
        kernel32.QueryInformationJobObject(self.h, JobObjectExtendedLimitInformation, ctypes.byref(ext), ctypes.sizeof(ext), None)
        self.logf.close()
        kernel32.CloseHandle(self.h)
        lean = [d for d in self.procs.values() if d["image"].startswith("lean")]
        rec = dict(
            module=self.module,
            cmd=self.cmd,
            start=self.start_iso,
            end=now(),
            wall_s=round(time.time() - self.t0, 1),
            exit=self.p.returncode if status is None else status,
            cpu_user_s=round(acct.TotalUserTime / 1e7, 1),
            cpu_kernel_s=round(acct.TotalKernelTime / 1e7, 1),
            cpu_s=round((acct.TotalUserTime + acct.TotalKernelTime) / 1e7, 1),
            processes=int(acct.TotalProcesses),
            peak_commit_proc_bytes=int(ext.PeakProcessMemoryUsed),
            peak_commit_job_bytes=int(ext.PeakJobMemoryUsed),
            peak_ws_proc_bytes=max([d["peak_ws"] for d in self.procs.values()], default=0),
            peak_ws_job_sampled_bytes=int(self.peak_job_ws_sampled),
            lean_cpu_sampled_s=round(sum(d["cpu"] for d in lean), 1),
            lean_peak_ws_bytes=max([d["peak_ws"] for d in lean], default=0),
            lean_peak_commit_bytes=max([d["peak_commit"] for d in lean], default=0),
            log=os.path.basename(self.log_path),
            log_bytes=os.path.getsize(self.log_path),
        )
        return rec


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def default_toolchain_bin():
    import shutil
    if os.environ.get("LEAN_TOOLCHAIN_BIN"):
        return os.environ["LEAN_TOOLCHAIN_BIN"]
    lake = shutil.which("lake")
    if lake:
        return os.path.dirname(os.path.realpath(lake))
    return os.path.join(os.path.expanduser("~"), ".elan", "toolchains", "leanprover--lean4---v4.35.0", "bin")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", required=True)
    ap.add_argument("--formal", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--toolchain-bin", default=default_toolchain_bin(),
                    help="directory with lake.exe, lean.exe and leanchecker.exe of Lean 4.35.0 "
                         "(default: $LEAN_TOOLCHAIN_BIN, else the directory of `lake` on PATH, else the elan path)")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--command", default='["lake","build","+{module}"]')
    ap.add_argument("--ignore-deps", action="store_true")
    ap.add_argument("--only")
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--hash-olean", action="store_true")
    ap.add_argument("--serial-first", type=int, default=1, help="number of first modules run alone")
    ap.add_argument("--max-commit-gib", type=float, default=125.0)
    ap.add_argument("--min-avail-mb", type=float, default=12000.0)
    ap.add_argument("--headroom-gib", type=float, default=16.0)
    ap.add_argument("--expect-gib", type=float, default=10.0)
    ap.add_argument("--expect-heavy-gib", type=float, default=16.0)
    ap.add_argument("--proc-commit-limit-gib", type=float, default=28.0)
    ap.add_argument("--timeout-s", type=float, default=14400.0)
    ap.add_argument("--spacing-s", type=float, default=3.0)
    ap.add_argument("--env", action="append", default=[], metavar="KEY=VALUE",
                    help="extra environment variable for the commands (repeatable)")
    ap.add_argument("--env-file", help="file with KEY=VALUE lines, added to the environment of the commands")
    args = ap.parse_args()

    scope = json.load(open(args.scope, encoding="utf-8"))
    mods = scope["modules"]
    order = scope["order"]
    if args.only:
        only = [l.strip() for l in open(args.only, encoding="utf-8") if l.strip()]
        unknown = [m for m in only if m not in mods]
        if unknown:
            sys.exit(f"not in scope: {unknown}")
        order = [m for m in order if m in set(only)]
    os.makedirs(os.path.join(args.outdir, "logs"), exist_ok=True)
    results_path = os.path.join(args.outdir, "results.jsonl")
    runner_log = open(os.path.join(args.outdir, "runner.log"), "a", encoding="utf-8", newline="\n")

    def log(msg):
        line = f"{now()} {msg}"
        runner_log.write(line + "\n")
        runner_log.flush()
        print(line, flush=True)

    done_ok = set()
    if args.resume and os.path.exists(results_path):
        for line in open(results_path, encoding="utf-8"):
            r = json.loads(line)
            if r["exit"] == 0:
                done_ok.add(r["module"])
    cmd_template = json.loads(args.command)
    exe = os.path.join(args.toolchain_bin, cmd_template[0] + ".exe")
    env = dict(os.environ)
    env["PATH"] = args.toolchain_bin + os.pathsep + env.get("PATH", "")
    extra = list(args.env)
    if args.env_file:
        extra += [l.rstrip("\r\n") for l in open(args.env_file, encoding="utf-8") if "=" in l]
    for kv in extra:
        k, v = kv.split("=", 1)
        env[k] = v

    # modules that earlier builds measured above 5.5 GB of working set
    heavy = re.compile(
        r"LocalBalls(Bcc|Fcc)(Analytic|Modes|Metric|Slab)|Lattice\.ForestG0|Lattice\.Atlas\.(Bcc|Fcc|Table)|"
        r"Round7Leaves|FLeafSample|Round6ScreenedLeaf|OverlayPilotLeaves|ReferenceCert|PrefixSidecarItems|"
        r"Stage6DLeaves|Stage5bOpticalLeaves|Stage3Leaves|PlanarFibreTri|TangentTable|LeafFix.*(Leaves|Corner|Round)|"
        r"AdaptiveThin")

    deps = {m: ([] if args.ignore_deps else [d for d in mods[m]["deps"]]) for m in order}
    if not args.ignore_deps:
        # imports outside --only must already be built in an earlier run
        for m in order:
            for d in deps[m]:
                if d not in order and d not in done_ok:
                    sys.exit(f"{m} needs {d}, which is neither selected nor recorded as built")
    # priority: number of modules that depend on it, transitively
    users = {m: set() for m in order}
    for m in reversed(order):
        for d in mods[m]["deps"]:
            if d in users:
                users[d].add(m)
                users[d] |= users[m]
    pending = [m for m in order if m not in done_ok]
    finished_ok = set(done_ok)
    failed = {}
    running = []
    last_start = 0.0
    last_gate_note = 0.0
    started = 0
    log(f"runner start: {len(pending)} modules to run, {len(done_ok)} recorded as done, jobs={args.jobs}, "
        f"command={cmd_template}, gate: commit<{args.max_commit_gib} GiB and <limit-{args.headroom_gib} GiB, "
        f"avail>{args.min_avail_mb} MB, per-process commit limit {args.proc_commit_limit_gib} GiB, pid {os.getpid()}")
    t_run = time.time()
    with open(results_path, "a", encoding="utf-8", newline="\n") as results:
        while pending or running:
            # reap
            for j in list(running):
                rc = j.p.poll()
                status = None
                if rc is None and time.time() - j.t0 > args.timeout_s:
                    kernel32.TerminateJobObject(j.h, 1)
                    j.p.wait()
                    status = "timeout"
                    rc = j.p.returncode
                if rc is None:
                    if time.time() - j.last_sample >= 2.0:
                        j.sample()
                    continue
                j.sample()
                gate = j.gate
                rec = j.finish(status)
                rec["lib"] = mods[j.module]["lib"]
                rec["gate_at_start"] = gate
                if args.hash_olean and rec["exit"] == 0:
                    rel = j.module.replace(".", "/")
                    base = os.path.join(args.formal, ".lake", "build", "lib", "lean", rel)
                    for ext in ("olean", "ilean"):
                        pth = base + "." + ext
                        if os.path.exists(pth):
                            rec[ext + "_bytes"] = os.path.getsize(pth)
                            rec[ext + "_sha256"] = sha256_file(pth)
                        else:
                            rec[ext + "_bytes"] = None
                results.write(json.dumps(rec) + "\n")
                results.flush()
                running.remove(j)
                if rec["exit"] == 0:
                    finished_ok.add(j.module)
                else:
                    failed[j.module] = rec["exit"]
                log(f"done {j.module}: exit {rec['exit']}, wall {rec['wall_s']} s, cpu {rec['cpu_s']} s, "
                    f"lean peak ws {rec['lean_peak_ws_bytes'] / GIB:.2f} GiB, peak commit/process "
                    f"{rec['peak_commit_proc_bytes'] / GIB:.2f} GiB; {len(finished_ok)} ok, {len(failed)} failed, "
                    f"{len(pending)} pending, {len(running)} running")
            # start
            stop = os.path.exists(os.path.join(args.outdir, "STOP"))
            cap = 1 if started < args.serial_first else args.jobs
            if pending and not stop and len(running) < cap and time.time() - last_start >= args.spacing_s:
                ready = [m for m in pending if all(d in finished_ok for d in deps[m])]
                if ready:
                    ready.sort(key=lambda m: (-len(users[m]), m))
                    m = ready[0]
                    pf = perf()
                    resv = sum(j.reservation() for j in running)
                    eff = pf["committed"] + resv
                    ok = (eff < args.max_commit_gib * GIB and eff < pf["limit"] - args.headroom_gib * GIB
                          and pf["avail"] > args.min_avail_mb * MIB)
                    gate = dict(committed_gib=round(pf["committed"] / GIB, 2), limit_gib=round(pf["limit"] / GIB, 2),
                                avail_mb=round(pf["avail"] / MIB), reservation_gib=round(resv / GIB, 2),
                                running=[j.module for j in running])
                    if ok:
                        cmd = [exe] + [a.replace("{module}", m) for a in cmd_template[1:]]
                        expect = (args.expect_heavy_gib if heavy.search(m) else args.expect_gib) * GIB
                        j = Job(m, cmd, args.formal, env, os.path.join(args.outdir, "logs", m + ".log"),
                                int(args.proc_commit_limit_gib * GIB), expect)
                        j.gate = gate
                        running.append(j)
                        pending.remove(m)
                        started += 1
                        last_start = time.time()
                        log(f"start {m} (pid {j.p.pid}); gate {gate}")
                    elif time.time() - last_gate_note > 60:
                        last_gate_note = time.time()
                        log(f"gate closed for {m}: {gate}")
                elif not running:
                    # nothing can start: the rest depends on failed modules
                    log(f"stopping: {len(pending)} modules depend on failed modules {sorted(failed)}")
                    break
            if stop and not running:
                log("STOP file present; nothing running; leaving")
                break
            time.sleep(0.5)
    log(f"runner end: {len(finished_ok) - len(done_ok)} built in this run, {len(failed)} failed {sorted(failed)}, "
        f"{len(pending)} not started, elapsed {time.time() - t_run:.0f} s")
    sys.exit(0 if not failed and not pending else 1)


if __name__ == "__main__":
    main()
