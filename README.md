# BCC optimality and sharp stability for two-point periodic Coulomb configurations

**Result.** At fixed density, the body-centred cubic (BCC) lattice is the unique minimizer of the Coulomb energy per
particle (point charges in a uniform neutralizing background, the energy defined by Ewald summation) among periodic
configurations admitting a period cell with at most two points. More precisely, every such configuration `X`
satisfies the sharp stability inequality `e(X) - e_BCC >= (e_FCC - e_BCC) D(X)`, where `D(X)` in `[0, 1]` is an
explicit local defect, with equality only for the BCC and the face-centred cubic (FCC) lattices (Theorems 1.1 and 1.2
of the paper).

**Verification.** The full two-point result is computer-assisted: an exact rational check that the certificate covers
the reduced domain, and a replay of every inequality of the certificate in Arb interval (ball) arithmetic. The
Bravais-lattice case (one point per cell, Theorem 5.1) is also proved in Lean 4, independently of these programs, with
its own certificate evaluated by Lean's kernel.

- The paper: [`paper/bcc-two-point-coulomb.pdf`](paper/bcc-two-point-coulomb.pdf)
- How to replay the full cover, and when a replay is accepted: [`cover/README.md`](cover/README.md#full-replay)
- The recorded receipt of the replay: [`cover/run/receipt.json`](cover/run/receipt.json)

**License:** MIT for the code, data and records ([`LICENSE`](LICENSE)); the paper in `paper/` is licensed under
CC BY 4.0 ([`paper/LICENSE`](paper/LICENSE)).

## Contents and the statements they support

| Directory | Content | Paper |
|---|---|---|
| [`paper/`](paper/) | LaTeX sources and the PDF (`bcc-two-point-coulomb.pdf`); `main.tex` is the root file | |
| [`cover/`](cover/) | the certificate of the cover (13 files, 187 MB), the standalone verifier, the record of its run and of the negative controls | Theorem 7.3, Table 7.1, Sections 9.3 and 9.4 |
| [`programs/`](programs/) | the programs for the constants, the lattice case and the local charts, with the results of their runs | Proposition 2.7 and Section 9.2; Theorem 5.1, Proposition 5.2, Table 5.1; Theorem 6.2, Tables 6.1 and 6.2; Section 9.3 |
| [`lean/`](lean/) | the Lean 4 sources of the part of the formal development that Section 9.5 describes, with the records of a clean build, an axiom audit, a replay of every module and checks by other kernels | Section 9.5 |
| `SHA256SUMS` | SHA-256 of every other file of the repository | |

Each directory has its own README with details. The proof of the main theorems combines the lattice case (Theorem 5.1,
certified by `programs/lattice.py` and proved in `lean/`), the constants (Proposition 2.7, computed by
`programs/constants.py` and enclosed in `lean/`), the cover (Theorem 7.3, the certificate in `cover/` with its
verifier) and the analytic statements of the paper. The local charts of Section 6 (`programs/local_charts.py`) are a
result of their own, which the main proof does not use. The Lean development also reduces the two-site theorem to the
statement that its checking functions accept the cover, without evaluating them on the whole certificate (Section 9.5).

## Software

| Part | Software |
|---|---|
| `cover/`, `programs/` | Python 3.14 (CPython 3.14.2 in the recorded runs), python-flint 0.9.0 with FLINT 3.6.0, and for `programs/` also numpy (2.5.4 in the recorded runs) and, for `constants.py` only, SciPy (1.18.1 in the recorded runs) |
| `lean/` | Lean 4.35.0 and Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679` (pinned in `lean/lake-manifest.json`); Python 3.9 or later for the tools; the checkers `leanchecker`, `leanchecker-paranoid`, `nanoda`, `lean4lean`, `con-leche`, `con-ron` and `leanexport`, all distributed with the Lean 4.35.0 toolchain |
| `paper/` | a LaTeX distribution (pdfLaTeX with BibTeX, or Tectonic) with `amsart`, `pgfplots` and standard packages |

The recorded runs were performed on Windows 11. The cover verifier uses portable Python code; we have not yet run the
full replay on Linux. For Lean, follow the POSIX build and replay commands in [`lean/README.md`](lean/README.md). The
Windows job runner and its helper scripts are not required for those steps.

The machine of the recorded runs has an AMD Ryzen 9 9950X3D (16 cores, 32 logical processors) and 62 GiB of memory
and runs other jobs at the same time; the numbers of processes below are the recorded settings, not requirements.

## Reproducing

The times below are those of the recorded runs. The commands for the cover and for Lean write into directories of your
choice; the programs write into `programs/results/`, so run them in a fresh clone to keep the recorded results, and
compare as each directory's README describes.

**The cover** (in `cover/`, after `mkdir my-run`; see its README). A quick check, the negative controls (3 minutes):

```
python -B record_controls.py certificate --report my-run/controls.json
```

rejects all 101 controls, and in each of the 22 controls that change a leaf of the certificate it accepts the unchanged
leaf; the report records the SHA-256 of the verifier and of the certificate before and after the controls. The full
replay and the check of its receipt:

```
python -B -m cover_verifier.verify certificate --workers 6 --bits 128 --receipt my-run/receipt.json --log my-run/run.log
python -B check_receipt.py my-run/receipt.json
```

The replay ends with `RESULT: PASS` (3.3 hours with 6 worker processes, 18.6 processor-hours; 6 is the recorded
setting, not a requirement). `check_receipt.py` accepts the receipt when it has scope `complete`, result `PASS`, no
rejected leaf, the recorded SHA-256 of the verifier and of the certificate at the start and at the end of the run, and
the recorded coverage and rule counts (17,092,214 parts and boxes with a rule, the counts of Table 7.1), and when the
recorded receipt and controls were made with the verifier and the certificate of this repository; it prints the
margins and the boxes where they occur as diagnostics.

**Constants, local charts, lattice case** (in `programs/`; see its README):

```
python -B constants.py           # under a second: results/constants.json (optional, see below)
python -B local_charts.py        # about 3 minutes: results/local_charts.json
python -B lattice.py boxes       # about 24 minutes on 4 processes: results/lattice_boxes.json
python -B lattice.py strain      # about 2.4 hours on 4 processes: results/lattice_strain.json
```

The last three read `results/constants.json`; the shipped file is the one the recorded results read. Running
`constants.py` regenerates it with the same results and a new provenance block, hence a new SHA-256. Expected: the
enclosures of `e_BCC` and `e_FCC` printed in Section 9.2; no unresolved box in either part of the lattice case, with
the counts of Table 5.1; the inequality of Theorem 6.2 on every listed ellipsoid of the local charts.

**Lean** (in `lean/`; see its README): `lake exe cache get`, `lake build --no-build Mathlib`, then one `lake build +M`
per module in the order of `modules.txt` (12.6 processor-hours, 3.8 hours at three modules in parallel; up to 10 GB of
memory per module), then `lake build --no-build BccSharp` and the axiom audit `lake env lean audit/ScopeAxioms.lean`
(3 minutes). The replay with `leanchecker` takes 12.0 processor-hours. The checks of the exported table are separate
from the build and take longer: 7.7 hours for `leanchecker --from-export` and 9.1 hours for Lean4Lean, one process
each. Expected: every module builds; only the axioms `propext`, `Classical.choice` and `Quot.sound` occur; every
checker accepts. `python check_records.py` in `lean/` checks the recorded build and checks against each other and
against the files of the repository.

**Tests** (in the root directory): `python -B -m unittest discover -s tests` runs regression tests of the verifier's
input checks, the controls and their record, the receipt check, the refiner, the failure of a run whose code or input
changes while it runs, and the failure handling of the programs.

**Paper**: `pdflatex main`, `bibtex main`, `pdflatex main`, `pdflatex main` in `paper/`, or `tectonic -X compile
main.tex`; the build writes `main.pdf`. A build with Tectonic 0.17.0 gives 49 pages whose text equals that of
`paper/bcc-two-point-coulomb.pdf` word for word.

## Results of the recorded runs

- Cover: `PASS`, scope `complete`, no rejection; negative controls 101 of 101 rejected, with the unchanged leaf accepted
  in each of the 22 that change a leaf, and 2 of 2 baselines accepted (`cover/run/`).
- Constants: `e_BCC ∈ [-0.89592925568176528916624546293829460538061046722070, -0.89592925568176528916624546293829460538061046722066]`,
  `e_FCC ∈ [-0.89587361519510845989748779611028534450181510608894, -0.89587361519510845989748779611028534450181510608890]`
  (`programs/results/constants.json`).
- Lattice case: no unresolved box in the box part (1,463,656 boxes examined) or in the two strain charts, with the
  counts of Table 5.1 (`programs/results/lattice_boxes.json`, `lattice_strain.json`).
- Local charts: the inequality holds on every listed ellipsoid, among them the eight of Table 6.2
  (`programs/results/local_charts.json`).
- Lean: 405 of 405 modules built; no axiom other than the three above in any of the 47,462 constants of the 405
  modules; every module replayed by `leanchecker`; the 130 table theorems with all 86,924 declarations they depend on
  accepted from the export by Lean's kernel and by Lean4Lean, and the 54 that depend on no certificate also by nanoda,
  con-leche, con-ron and `leanchecker-paranoid`, each check on the export bytes that its export record names, hashed
  before and after the checker (`lean/records/`).

## Checksums

`SHA256SUMS` lists the SHA-256 of every file of the repository except itself. To check it, in the root directory:
`sha256sum -c SHA256SUMS` (on Windows, for example, in Git Bash).
