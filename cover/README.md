# The cover (Theorem 7.3)

This directory holds the certificate of the cover of Theorem 7.3 of the paper, the program that verifies it, and the
record of its verification.

| Path | Content |
|---|---|
| `certificate/` | the flat certificate: thirteen files `stage01a.jsonl.gz` ... `stage10.jsonl.gz`, 186,697,255 bytes in all, in the format of [`cover_verifier/FORMAT.md`](cover_verifier/FORMAT.md); SHA-256 in [`../SHA256SUMS`](../SHA256SUMS) and in `run/receipt.json` |
| `cover_verifier/` | the verifier: fourteen Python modules that use only the standard library and python-flint; what it checks, what it takes as given and which statement of the paper each module implements are described in [`cover_verifier/README.md`](cover_verifier/README.md) |
| `check_receipt.py` | checks the receipt of a run against the recorded receipt by the criteria below, and the recorded receipt and controls against the files of this directory (standard library only) |
| `record_controls.py` | runs the negative controls of `cover_verifier/controls.py` and records in their report what they ran on |
| `run/receipt.json` | receipt of the recorded run: result, scope, the SHA-256 of every source file of the verifier and of every input file, taken at the start of the run and again at its end, interpreter and library versions, the number of boxes per rule and condition, the smallest margin per rule with the box where it occurs, times |
| `run/run.log`, `run/stdout.txt` | log and console output of the recorded run |
| `run/controls.json`, `run/controls.txt` | report and console output of the recorded negative controls; the report holds the SHA-256 of `record_controls.py`, of every module of the verifier and of every file of the certificate, taken before the controls start and again after they end, the times and the environment |

## Requirements

Python 3.14 (the recorded run uses CPython 3.14.2 on Windows 11, x86-64) and python-flint 0.9.0, which contains
FLINT 3.6.0 (`pip install python-flint==0.9.0`).

## Commands

All commands run from this directory and write into a directory `my-run/`, so the recorded files in `run/` stay
unchanged:

```
mkdir my-run
```

### Quick checks (minutes)

```
python -B record_controls.py certificate --report my-run/controls.json
```

runs the negative controls: rules applied where their conclusion is false, changed parameters, boxes outside the
hypotheses of their rule, removed boxes, false covers and containments, a misused reflection step. Every control must
be rejected, and in each of the 22 controls that change a leaf of the certificate the unchanged leaf must be accepted
(the report records both outcomes). The command prints `101 controls run, 101 rejected as required; 0 not run;
2 baselines, 2 accepted` and a line saying that the verifier and the certificate were unchanged during the run, and
exits with status 0 (160 s in the recorded run). `python -B -m cover_verifier.controls` with the same
arguments runs the same controls without the record of what they ran on.

```
python -B -m cover_verifier.verify certificate --skip-inequalities --receipt my-run/first-pass.json --log my-run/first-pass.log
```

runs only the first pass, the check in exact rational arithmetic that the certificate covers the reduced domain
(570 s of processor time in the recorded run). Its receipt has scope `incomplete: inequalities not checked` and result
`PASS OF AN INCOMPLETE RUN`; it does not establish Theorem 7.3.

### Full replay

```
python -B -m cover_verifier.verify certificate --workers 6 --bits 128 --receipt my-run/receipt.json --log my-run/run.log
python -B check_receipt.py my-run/receipt.json
```

The first command runs the two passes of Section 9.3 of the paper: the first pass as above, then the hypothesis of the
rule of every part and box that carries one, in ball arithmetic at 128 bits. It prints `RESULT: PASS` when every check
passes. `--workers` is the number of processes of the second pass (default 4); 6 is the setting of the recorded run,
not a requirement, and with fewer processes the run takes longer (the recorded run: 3.3 hours elapsed and
18.6 processor-hours on 6 processes). The second command checks the receipt by the criteria below.

### Acceptance criteria

A run establishes Theorem 7.3 when its receipt satisfies all of the following, which `check_receipt.py` checks:

1. `scope` is `complete` and `result` is `PASS`. The exit status alone is not enough: a run of the first pass alone
   also exits with status 0.
2. `rejected` lists no leaf in any file.
3. `verifier` equals the SHA-256 of the fourteen modules in `cover_verifier/`, and `inputs` (the SHA-256 of the
   thirteen files of the certificate) equals that of `run/receipt.json`.
4. The coverage and the counts equal those of `run/receipt.json`: `completeness` (pieces, leaves, held and contained
   boxes of the first pass, per file), `counts` (boxes per rule and condition, per file) and the number `boxes` of
   every entry of `rules`.

The margins (`smallest_margins`, and `smallest_margin` in `rules`) and the boxes where they occur (`file`, `piece`,
`leaf`) are diagnostics, not criteria; `check_receipt.py` prints them beside the recorded ones. When two boxes have
the same smallest margin, the box that is reported can depend on the order in which the worker processes finish. The
fields `environment`, `workers`, `arguments` and the times describe the run and are not compared.

`check_receipt.py` also checks the recorded files themselves: the `verifier` and `inputs` of `run/receipt.json`
equal the SHA-256 of the modules of `cover_verifier/` and of the files of `certificate/`; and `run/controls.json` was
written by `record_controls.py` (its SHA-256 as recorded) with these modules and the certificate of the recorded
receipt, hashed before and after the controls and unchanged, with every control rejected, the unchanged leaf accepted
in every control that changes a leaf, and every baseline accepted. With the recorded files of this repository,
`python -B check_receipt.py run/receipt.json` prints `ACCEPTED`.

## The recorded run

With the verifier and the certificate of this repository (the receipt records the SHA-256 of every file), on a
workstation with an AMD Ryzen 9 9950X3D (16 cores, 32 logical processors) and 62 GiB of memory, which runs other jobs
at the same time, with 6 worker processes (the setting of this run, not a requirement):

- Result `PASS`, scope `complete`, no part or box rejected.
- 17,092,214 parts and boxes with a rule: 15,926,598 with condition (E), 567,015 with (D), 97,831 with (A),
  500,770 with (N); the counts per stage and rule are those of Table 7.1 of the paper.
- Smallest margins: about `8.6e-13` for (E), `8.4e-12` for (D), `1.4e-6` for (N), and `1.2e-5` for the least pivot of
  condition (A) (per rule in the receipt and at the end of `run/stdout.txt`).
- Time: 11,863 s elapsed, 67,066 s of processor time (18.6 processor-hours).
- Negative controls (`run/controls.json`, with the same verifier and certificate, hashed before and after): 101
  controls run, 101 rejected as required, with the unchanged leaf accepted in each of the 22 controls that change a
  leaf; 2 baselines (unchanged parts of the certificate), 2 accepted.

## The certificate

The first line of each file is a header with the format and the stage; the other lines, the boxes of the stage with
their subdivisions, rules and parameters, are described in `cover_verifier/FORMAT.md`. The verifier implements the
statements of the paper and imports no code other than the Python standard library and python-flint.
