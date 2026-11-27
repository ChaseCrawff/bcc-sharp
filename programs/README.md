# Programs for the constants, the lattice case and the local charts

These programs compute, in ball arithmetic, the constants of Proposition 2.7 and Section 9.2 of the paper, the
certificate of the lattice case (Theorem 5.1, Proposition 5.2, Table 5.1) and the local charts of Section 6
(Theorem 6.2, Tables 6.1 and 6.2). Section 9.3 of the paper describes the last two; Section 9.1 the arithmetic.

| Path | Content |
|---|---|
| `constants.py` | energies per particle of the BCC, FCC, HCP (ideal axis ratio) and simple cubic lattices from the Ewald formula (2.4) of the paper for two splitting parameters, with every truncation error bounded; for HCP also a search for the axis ratio of least energy, which finds a candidate ratio and certifies the energy there, but does not certify that this ratio is optimal; output `results/constants.json` |
| `lattice.py` | the certificate of the lattice case, in two parts: `boxes` (the reduced-coordinate domain of Section 5, cut into a grid of boxes that are bisected until every box is settled) and `strain` (the strain charts at BCC and FCC, Section 5.3 and Proposition 5.2); reads `results/constants.json`; outputs `results/lattice_boxes.json`, `results/lattice_strain.json` |
| `local_charts.py` | the eight-dimensional local charts at the fourteen two-site descriptions of BCC and FCC (Theorem 6.2); reads `results/constants.json`; output `results/local_charts.json` |
| `bccnum/` | the modules these programs use: exact rational and integer helpers (`exact.py`), ball enclosures and tail bounds (`intervals.py`), the Ewald sums (`ewald_cert.py`, and `ewald_float.py` in floating point, used only to steer the search for the HCP axis ratio and as a cross-check), the lattices (`structures.py`), the lattice case (`lattice_cert.py`, `lattice_strain.py`), the two-site energy and its local charts (`two_site.py`, `chart_atlas.py`), and the provenance block of the result files (`provenance.py`) |
| `results/` | the result files of the recorded runs and their console output (`*.out`) |

Every result file starts with a provenance block: the program and the SHA-256 of its source and of every module of
`bccnum/`, and for the two programs that read `results/constants.json` the SHA-256 of the bytes they read
(`inputs_sha256`, also among the parameters), all taken when the run starts; `unchanged_at_end`, true when the
program, the modules and the input have the same SHA-256 when the result is written (a run in which one of them
changed writes its result and then fails); the parameters; the interpreter; the versions of python-flint, FLINT, numpy
and SciPy; the start time and the wall time.
The field `tier` is `cert` when every accepted inequality is certified in ball arithmetic, and `mixed` for
`constants.py`, where floating-point arithmetic steers the search for the HCP axis ratio (every reported energy is
certified; the location of the optimum is not).

## Requirements

Python 3.14 with python-flint 0.9.0 (FLINT 3.6.0) and numpy, and for `constants.py` also SciPy, whose `erfc` the
floating-point helper `bccnum/ewald_float.py` uses (the recorded runs use CPython 3.14.2, numpy 2.5.4 and SciPy 1.18.1
on Windows 11, x86-64).

## Commands

The programs write into `results/`, or into the directory named by the environment variable `BCC_RESULTS_DIR` if it
is set; set it (or work in a fresh clone of this repository) to keep the recorded files. Run the programs from this
directory.

`local_charts.py` and `lattice.py` read the constants from `results/constants.json` and record the SHA-256 of that
file in their provenance block. With the shipped file, which is the one the recorded results read (SHA-256
`410932caeee78af4d05a8fa264b11e326bed7177c375460f6cb0da2ed7ce200b`), run

```
python -B local_charts.py
python -B lattice.py boxes
python -B lattice.py strain
```

To regenerate the constants as well, run `python -B constants.py` first. The new `results/constants.json` has the same
`results` part (timings aside) but a new provenance block (start time, wall time), so its SHA-256 differs from the one
above, and the other two programs then record the new value.

`lattice.py` uses a pool of worker processes whose size is taken from the environment variable `BS_PROCS` (default
4). Without an argument it runs both parts, writes `results/lattice.json` and adds the field `certified`, which is true
when no box of either part is left unresolved, the ball certificates at BCC and FCC hold and the starting box of the
box part contains the box (5.3) of the paper. In every mode the program exits with status 1 when its part is not
certified. To compare with the record, compare the `results` part of each file with the recorded one (`git diff`
shows the differences; only the timing fields `seconds` and the provenance block should differ).

## The recorded runs

With the programs of this repository (the provenance blocks record the SHA-256 of every source file), on a
workstation with an AMD Ryzen 9 9950X3D, which runs other jobs at the same time:

- `constants.py` (384 bits; splitting parameters 0.9 and 1.4 in units of the inverse Wigner-Seitz radius): under a
  second of computation. The intersections of the two enclosures are
  `e_BCC in [-0.89592925568176528916624546293829460538061046722070, -0.89592925568176528916624546293829460538061046722066]`
  and
  `e_FCC in [-0.89587361519510845989748779611028534450181510608894, -0.89587361519510845989748779611028534450181510608890]`,
  the numbers of Section 9.2. The HCP search, steered in floating point over rational values of `(c/a)^2`, ends at
  `(c/a)^2 = 1482679/554207` (`c/a = 1.63564...`), where the energy is certified to lie in
  `[-0.89583845120301684084713130771872217506931381780706, -0.89583845120301684084713130771872217506931381780702]`:
  a certified upper bound for the least HCP energy over all axis ratios, not a certificate that this ratio is optimal.
- `local_charts.py` (160 bits): 178 s. For each of the four classes of Table 6.1 the program certifies four
  ellipsoids; the eight listed in `nondominated_ellipsoid_indices` are those of Table 6.2. The result states
  `e(X) - e_bcc >= (e_fcc - e_bcc) D(X)` on every listed ellipsoid, with the fourteen descriptions covered by exact
  orthogonal symmetry.
- `lattice.py boxes` (96 bits, four worker processes): 1,412 s; no box unresolved; the starting box contains the
  box (5.3) of the paper (`root_contains_proof_root_box`); 1,463,656 boxes examined (depth
  12); terminal boxes by type R 727,455, E1 490,653, SB 22,564, SF 15,444, which are the types (R), (E), (B), (F) of
  the row "global cover" of Table 5.1; smallest margin of type E1 `3.85e-9`.
- `lattice.py strain` (96 bits, four worker processes): 8,755 s; no box unresolved in either strain chart (BCC:
  O 12,553, BALL 2, E1 95,223, E2 1,299; FCC: O 3,775, BALL 2, E1 43,229, which are the types (i), (ii), (iii), (iv) of
  the rows "chart of B0" and "chart of F0" of Table 5.1); the ball certificates at BCC and FCC hold (`all_pd`).
