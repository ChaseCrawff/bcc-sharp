# Lean development

Lean 4 sources of the part of the formal development that Section 9.5 of the paper lists as proved, with the files
needed to build them at pinned versions of Lean and Mathlib, the tools used for the recorded build and checks, and
their records. One library, `BccSharp`, of 405 modules (about 180,000 lines; 122 of the modules, about 93,000 lines,
are generated certificate data with one `decide +kernel` statement per item).

## What the sources prove

[`THEOREMS.md`](THEOREMS.md) lists 130 top-level theorems by name (relative to the namespace `BccSharp.Coulomb`),
module and line, with their axioms, grouped as the items of Section 9.5:

- **A. Definitions and invariances** (33). The periodic Coulomb kernel as an Ewald sum, its Fourier coefficients and
  its regular limit at the origin; the energy per particle for every splitting parameter; its equality with the series
  with nonnegative terms, for one and for two points per cell; independence of the period lattice, invariance under
  isometries, behaviour under dilation; the defect, its invariances and its equality at all points of a two-site
  configuration.
- **B. Constants** (5). Enclosures of the energies of the BCC and FCC lattices of width 4·10⁻⁵⁰, and of their
  difference (namespace `Constants`).
- **C. The lattice case** (13). For every lattice of density 3/(4π) the sharp inequality, with equality only for BCC
  and FCC (`BravaisCover.StrainAtlas.latticeCase_proved`, Theorem 5.1); the values of the energy and the defect on
  BCC and FCC.
- **D. Analytic part of the two-site theorem** (17). The compact reduction, the existence of a registration with its
  inequality, upper bounds for the defect from a registration, bounds for its growth away from an anchor, and
  Montgomery's inequality for the planar theta function.
- **E. Checking functions** (49). Functions that take a box with certificate data and return a Boolean, each with a
  proof that acceptance implies the inequality on the box.
- **F. Reduction** (13). `FinalAssembly.statementFull_of_runs_merged` and its variants: the full statement of the
  two-site theorem (`Full.StatementFull`) follows from three equations which say that the checking functions accept a
  cover of the reduced domain.

The reduction theorems have hypotheses, and these sources do not discharge them: the evaluation of the checking
functions on the certificate of the cover is not part of the formal development (Section 9.5 says so). The two-site
theorem itself is therefore **not** proved by these sources; the lattice case is. `Full.StatementFull` has no clause
for Corollary 1.3; [`audit/CorollaryFcc.lean`](audit/CorollaryFcc.lean), a supplementary file outside the library,
derives it from the clauses of `StatementFull` (`records/audit/CorollaryFcc.log`). `Statement` is in
`BccSharp.TwoSite.Interface`, `StatementFull` in `BccSharp.TwoSite.StatementFull`, and a statement of the defect that
uses only Mathlib in `BccSharp.TwoSite.Spec` (namespace `TwoSiteSpec`).

## Layout

| Path | Content |
|---|---|
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lake package `bcc_sharp` with the library `BccSharp`; Lean 4.35.0; Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679` with its eight dependencies as pinned in the manifest |
| `BccSharp/Analysis/` | 39 modules of general analysis: Gaussian and lattice sums, the Ewald splitting, special functions, interval and fixed-point arithmetic, Fourier uniqueness on a torus |
| `BccSharp/TwoSite/` | definitions and invariances, the statement, the constants (`ReferenceCert`), the series, the analytic part, Montgomery's inequality |
| `BccSharp/Lattice/` | the lattice case: strain charts, local balls, the tangent forest and tables, `Atlas/` (the two strain atlases and `LatticeCase`) |
| `BccSharp/Cover/` | the checking functions of the rules of the cover with their soundness proofs, generated certificate data, and sample evaluations |
| `BccSharp/FinalAssembly.lean` | item F |
| `modules.txt` | the 405 modules in an order in which each comes after its imports |
| `levels.txt` | the same modules in 58 lines; the modules of a line import only modules of earlier lines |
| `scope.json` | the import graph, with size and SHA-256 of every source |
| `audit/` | the axiom audit (`ScopeAxioms.lean`), the table of theorems (`theorems.json`, `theorem-table.json`), the lists for the exports, the markers of the two certificates (`markers.json`), and `CorollaryFcc.lean` |
| `tools/` | the programs used for the recorded build and checks (usage in the header of each) |
| `records/` | the records of the build and the checks (below) |
| `check_records.py` | checks the records against each other and against the files of this directory (below) |

Names of the cover part refer to the stages and rules of Section 7 of the paper: `Stage2` to `Stage6` (with `Stage5a`
and `Stage5b` for the two parts of stage 5) are the checks of the items of those stages of Table 7.1; `Direct`
(direct and moment bounds of stage 2), `Overlay` (the planar rules as used in stages 2 and 3), `Adaptive` (the
log-convex supports of the energy rules), `Corner` (the common-corner energy of stage 7), `HalfShift` (the energy gain
of Appendix C.1-C.3), `JointDeficit` (deficit rule (ii)), `PlanarFibre` (the fibre bound and the planar gain,
Lemmas C.8-C.10), `Continuation` (stage 9) and `PlanarAnchor` (Lemmas C.11 and C.12) label the rules. `Series` is the
positive series of Proposition 2.3.

Other words in names describe how the data of the cover are organized, which the checking functions follow: a *round*
(`Round5`, `Round6`, `Round7`) is one pass of refinement of a set of boxes within a stage; a *pilot* (`Pilot`,
`CatPilot011`, ...) is a small sample of boxes on which a checking function is evaluated in the kernel; a *sidecar* is
a supplementary list of certificates (direct and moment bounds) for some boxes of stage 2; the *corpus* and its
*prefix* are the boxes of the first stages together with their data, in the order of the stages; *early* and *late*
refer to the first and the later stages; a *replay* is the evaluation of checking functions on the boxes of the cover
with their data, and the *historical* cover is the cover as its stages describe it. String literals such as
`"stage4/optical"` or `"overlay/hard-roots.json"` are labels of the source of a box's data; they name no file of this
repository. Modules with "pilot", "sample" or "controls" in their names evaluate a checking function on a few boxes
(controls: on boxes where it must reject).

## Requirements

Lean 4.35.0 (`elan` installs it from `lean-toolchain`), Git, and for the tools Python 3.9 or later. Memory: the
largest module needs 9.8 GiB of working set (14.7 GiB of committed memory on Windows); allow 16 GB per parallel job.
Disk: about 12 GB (7 GB for Mathlib with its compiled files, 4 GB of build output), and 1.5 GB more for the two
exports of the kernel checks.

Times of the recorded runs, step by step (every check needs a finished build):

| Step | Processor time | Elapsed |
|---|---|---|
| build of the 405 modules | 12.6 hours | 3.8 hours, three modules in parallel |
| axiom audit | | 3 minutes |
| replay with `leanchecker` | 12.0 hours | 4.1 hours, three modules in parallel |
| the two exports | | under a minute each |
| six checkers on the export without certificates | | under three minutes each |
| `leanchecker --from-export` on the export of the table | 7.7 hours | 7.7 hours, one process |
| Lean4Lean on the export of the table | 9.1 hours | 9.1 hours, one process |
| a snapshot of what a step reads, before and after it | | two to three minutes each |

The 3.8 hours of the build do not include the checks. The two checks of the whole table from its export take about
eight and nine hours more, with a peak of 7.1 GiB of committed memory each. The checks were recorded while other jobs
ran on the same machine.

## Build

Lake starts all modules of a target at once and has no limit on parallel jobs; several modules need 6 to 10 GB each.
Build one module per Lake call, in dependency order; the package has no default target for this reason. In this
directory:

1. Mathlib: `lake exe cache get`, then `lake build --no-build Mathlib`, which must report that all targets are up to
   date.
2. The 405 modules, sequentially in any POSIX shell:

   ```
   (while read -r m; do lake build "+$m" || exit 1; done < modules.txt)
   ```

   or three at a time, level by level (with an `xargs` that has `-P`, as GNU and BSD `xargs` do):

   ```
   (while read -r level; do printf '%s\n' $level | xargs -P 3 -I{} lake build +{} || exit 1; done < levels.txt)
   ```

   Each loop runs in a subshell, which stops at the first level or module that fails and then exits with status 1
   (`xargs` first finishes the other modules of the level); the status is 0 only when every module is built.

   On Windows only (the runner uses Windows job objects), with a memory gate and a record of time and memory per
   module, as for the recorded build:

   ```
   python tools/gated_runner.py --scope scope.json --formal . --outdir my-build --jobs 3 --hash-olean
   ```

   (`records/build` holds the record of the recorded build; give another `--outdir` so as not to append to it.)
   The runner starts a module when its imports are built, fewer than three of its processes run, the system commit
   charge is below 125 GiB and more than 12 GB of memory are available (`--max-commit-gib`, `--min-avail-mb`,
   `--headroom-gib`); it finds `lake` on `PATH`, or takes `--toolchain-bin`.
   `python tools/record_state.py scope.json . <out.json>` (also Windows only, since it imports the runner) records the
   SHA-256 of every source before and after a build.
3. `lake build --no-build BccSharp` must report that all targets are up to date.

## Checks

- **Axioms.** `lake env lean audit/ScopeAxioms.lean` (generated by `tools/make_audit.py`) imports all 405 modules,
  lists the axioms declared in them, reports which axioms every constant of these modules depends on, prints the
  statements of 30 headline theorems and runs `#print axioms` on the 130 theorems of the table; `tools/make_theorem_table.py`
  writes `THEOREMS.md` from its output. In Lean 4.35 the axioms of an imported declaration are read from data stored in
  the compiled file of its module; the export check below does not use them.
- **Replay.** For each module `M`: `lake env leanchecker --verbose M`, which reads the compiled file of `M`, loads its
  imports and sends every declaration that `M` adds to the kernel again (a separate program, the same kernel). In a
  POSIX shell:

  ```
  (while read -r m; do lake env leanchecker --verbose "$m" || exit 1; done < modules.txt)
  ```

  On Windows, with the runner:
  `python tools/gated_runner.py --scope scope.json --formal . --outdir my-replay --jobs 3 --ignore-deps --hash-olean --command "[\"lake\",\"env\",\"leanchecker\",\"--verbose\",\"{module}\"]"`.
- **Export and other kernels.** The exports themselves, NDJSON files of 875 MB (the table) and 608 MB (the theorems
  without certificates), are not in this repository. `records/kernels/` holds their sizes, SHA-256 and statistics and
  the records of the checks, and the exports are regenerated from a build as follows. `tools/make_export_list.py`
  writes the lists `audit/table-modules.txt` and `audit/table-names.txt`; `tools/run_kernels.py export` runs
  `leanexport` on them (the theorems and every declaration they depend on, Mathlib included, as one NDJSON file);
  `tools/export_stats.py` lists what an export declares and, with `--find`, whether the listed names are theorems of
  it; `tools/export_taint.py` finds the theorems that depend on neither certificate (`audit/markers.json`);
  `audit/free-names.txt` lists these 54 theorems, and the second export takes them with the modules of
  `audit/table-modules.txt`; `tools/run_kernels.py check` runs the checkers bundled with Lean 4.35.0 on an export:
  Lean's kernel (`leanchecker --from-export`, and `leanchecker-paranoid`), nanoda, con-leche and con-ron (a Rust
  re-implementation of con-leche's checker), and Lean4Lean (a re-implementation of Lean's kernel in Lean).
  `tools/run_kernels.py` runs only on Windows (each checker in a Windows job object, behind the memory gate of
  `tools/gated_runner.py`). Its header lists the command line of every checker and its code the configuration file it
  writes for nanoda; on other systems these commands can be run directly, with the toolchain's `bin` directory on
  `PATH`. For an export, `leanexport <modules> -- <names>` runs with `LEAN_PATH` set to the output of
  `lake env printenv LEAN_PATH`, and its output (standard output and standard error) is the export file. The record of
  an export holds a snapshot taken before it and one taken after it (below); the record of a check holds the SHA-256,
  size and first line of the export, taken immediately before the checker starts and again after it ends, with the
  SHA-256 of the tools and of the toolchain's programs.
- **Snapshots and records of a step.** `tools/snapshot.py` takes the SHA-256 of what a step reads: the tools, the
  Python interpreter, the toolchain (its programs, and a digest of its library), `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` and `scope.json`, the 405 sources, every file under `.lake/build/lib/lean`
  (all parts of a compiled module: `.olean`, `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`, `.ilean`, and Lake's
  `.hash` and `.trace` files), every compiled file of Mathlib and its dependencies under `.lake/packages`, and the
  files the step names. `python tools/record_run.py --scope scope.json --formal . --out <record.json> --log <log>
  [--file <path>] -- <command>` runs a command between two snapshots and records both, with the command, the
  executable, the times, the exit status and the SHA-256 of the output.
- **Checking the records.** `python check_records.py` (in this directory, on any system with Python 3.9 or later)
  checks the records of `records/` against each other and against the files of this directory: the build (its logs,
  its list of `.olean` hashes, and its summaries regenerated from its results and logs), the snapshots of every later
  step (equal before and after, and equal across steps), the commands, the replay of every module (its logs and
  summaries likewise), the exports and the lists they were made from, the statistics and the dependency analysis of
  the exports, and every check against the export record it names, with all the times in order; it prints
  `ALL RECORDS CONSISTENT` when every check holds.
- **Compiled files.** `python tools/olean_receipts.py scope.json . <out.json> <out.txt>` writes the SHA-256 of the 405
  `.olean` files; `records/build/olean-sha256.txt` has the values of the recorded build (Windows 11, x86-64). The
  compiled files of some modules contain the absolute path of their source file, so they differ between build
  directories.

## Recorded build and checks

On Windows 11 with an AMD Ryzen 9 9950X3D (16 cores, 32 logical processors) and 62 GiB of memory, which runs other
jobs at the same time. Absolute paths of the build directory, of the toolchain and of the directory of the Python
interpreter in the records are replaced by `<package>`, `<toolchain>` and `<python>`; no file whose SHA-256 a record
holds contains such a path. `python check_records.py` checks the records as described under Checks and prints
`ALL RECORDS CONSISTENT`.

- **State** (`records/build/state-before.json`, `state-after.json`): the SHA-256 of all 405 sources equal those of
  `scope.json`, which are the sources of this repository; no compiled module before the build.
- **Build** (`records/build/`): 405 of 405 modules built, each by its own Lake call, from 10:14 to 14:05 (13,840 s
  elapsed), 12.6 processor-hours; largest working set 9.76 GiB (`BccSharp.Cover.PrefixSidecarItems`); every log contains
  exactly its own module's build and no error, and 538 warnings in 76 modules (linter and similar, none about `sorry`)
  (`log-check.json`; the logs in `logs.tar.gz`). The record of each module holds the SHA-256 of its `.olean` and
  `.ilean`, taken right after it was built (the `.olean` hashes also in `olean-sha256.txt`).
- **Snapshots.** Every later step that reads the build was recorded with a snapshot taken before it and one taken after
  it, and the two agree. All these snapshots agree with each other: the 405 sources of `scope.json`; the package
  configuration; the 2,337 files under `.lake/build/lib/lean` (for the 405 modules: `.olean`, `.ilean` and Lake's
  `.trace`, `.hash` files; for the 39 modules of `BccSharp/Analysis/` also `.olean.server`, `.olean.private`, `.ir` and
  `.ir.sig`), whose `.olean` files have the SHA-256 taken right after each module was built; the 117,664 compiled and
  configuration files of Mathlib and its dependencies; the toolchain (27 programs and libraries in `bin/`, 15,316 files
  in `lib/`); the Python interpreter; and the tools of `tools/`.
- **Up to date** (`records/no-build/`): `lake build --no-build BccSharp` reports all 9,452 jobs up to date, and
  `lake build --no-build Mathlib` all 9,046 jobs of Mathlib and its dependencies.
- **Axioms** (`records/audit/ScopeAxioms.log`, `ScopeAxioms.json`): no axiom is declared in the 405 modules; all 47,462
  constants (28,390 theorems, 16,205 internal names) use only `propext`, `Classical.choice` and `Quot.sound` (all
  three: 35,402; none: 7,797; `propext`: 3,668; `Quot.sound` and `propext`: 592; `Quot.sound`: 3); all 130 table
  theorems use all three. `audit/CorollaryFcc.lean` checks with the same axioms (`CorollaryFcc.log`,
  `CorollaryFcc.json`).
- **Replay** (`records/replay/`): `lake env leanchecker --verbose M` for each of the 405 modules, three at a time,
  14,817 s elapsed, 12.0 processor-hours: 405 of 405 with exit status 0, every log the single line `replaying M` for
  its own module (`log-check.json`; the logs in `logs.tar.gz`), and the `.olean` of every module with the SHA-256 of
  the build when its replay ended.
- **Exports** (`records/kernels/`; the exports themselves are not in the repository): the 130 table theorems with all
  their dependencies, 86,924 declarations, among them exactly the three axioms, each of the 130 a theorem of the export
  (`table-stats.json`; the export: 874,780,365 bytes, SHA-256
  `12d95762c8c355948f429a6bcf879ccef51f90f6461d7d576b23fe5c8983ee39`, its record in `table-export/`); 54 of the 130
  depend on neither certificate (`table-taint.json`; 73 depend on the constants certificate, 17 on the lattice
  certificate), exported separately with 67,038 declarations, each of the 54 a theorem of that export
  (`free-stats.json`; the export: 608,174,018 bytes, SHA-256
  `dcba89afbcd0d9897e28f439761d511b5e9a2e2a60e56068e78a5d9cdc83f202`, record in `free-export/`). `checks.json` lists
  every check below with the SHA-256 of the export taken before and after the checker, its exit status and its result
  line.
- **Six checkers on the certificate-free export** (`records/kernels/free/`): accepted by `leanchecker --from-export`,
  `leanchecker-paranoid`, nanoda ("Checked 69348 declarations with no typechecker errors", with one message of its
  pretty printer about axioms), Lean4Lean ("checked 67035 declarations": all, counting the four `Quot` declarations as
  one), con-leche and con-ron (67,038 declarations each), each in under three minutes.
- **The whole table** (`records/kernels/table-lean/`, `table-lean4lean/`): accepted by `leanchecker --from-export`
  ("Lean default kernel accepts the solution"; 27,710 s, peak commit 7.1 GiB) and by Lean4Lean ("checked 86921
  declarations": all, counting the four `Quot` declarations as one; 32,701 s, peak commit 7.1 GiB). Every one of the
  130 table theorems is thus checked by Lean's kernel in the build, in the replay and from the export, and by
  Lean4Lean; the 54 that depend on no certificate also by nanoda, con-leche, con-ron and `leanchecker-paranoid`.
