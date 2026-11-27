# Format of the flat certificate (version `cover-certificate-1`)

Section, lemma and equation numbers refer to the paper.

The certificate is a directory of files `stageNN*.jsonl` or `stageNN*.jsonl.gz`, read in the lexicographic order of
their names. Each file is JSON Lines in UTF-8: one JSON value per line. The verifier treats every value in these files
as untrusted.

## Conventions

- **Rational numbers** are strings `"p/q"` or `"p"` (as accepted by Python's `fractions.Fraction`). Integers that are
  parameters (`n`, `m`, quaternions, flags, `cube`) are JSON integers.
- **Coordinates** are in the order `(r1, r2, x, y, z, f1, f2, f3)` of (4.1) and (4.5) of the paper; they are numbered
  `0..7`. The first five are the *shape*, the last three the *offset*.
- A **box** is `[[lo_0, ..., lo_7], [hi_0, ..., hi_7]]` with `lo_i <= hi_i`; it stands for the closed product of the
  intervals. The verifier requires `lo_0 > 0` and `lo_1 > 0` of every box, including the box `dom` of a support (the
  matrix `R` of (4.1) is then defined on the box, and the squared lengths are separately convex on it, Lemma 7.4).
  Boxes with a rule may extend beyond the shape part of `K`; the boxes that the cover has to exhaust are sub-boxes of
  `K` by construction.
- **Vertices.** A box has 256 vertices. Vertex number `v` in `0..255` takes the upper endpoint of coordinate `i` if and
  only if bit `7 - i` of `v` is set.
- A **registration** `REG` is `[B, f0, n]`: `B` a 3x3 matrix given by its three rows (rationals), the basis matrix `B'`
  of Section 7.5; `f0` three rationals in `(1/2)Z`; `n` three integers.
- An **anchor** is given by `f0` (three rationals in `(1/2)Z`, not all integers) and `n` (three integers); the rule is
  applied to `delta = f - f0 - n` (Section 7.7).

## Records

Line 1 of every file is a header

    {"format": "cover-certificate-1", "stage": "..."}

`stage` is informational. A header with the additional field `"step": "mirror"` makes the file a *reflection step*: it has no other
record (see "Completeness" below). The other lines are objects with a field `"t"`.

### `{"t": "support", "id": ID, "dom": BOX, "kind": KIND, "alpha": Q, "cube": c, "limit": Q, ...}`

A lower bound for the energy of the kind described in Lemma 7.5, built on the box `dom` and usable on every box
contained in `dom`. Common fields:

- `alpha`: the parameter of the screened series (7.2), a rational number `> 0`.
- `cube`, `limit`: the set `J` of terms consists of the terms of (7.2) with `max |m_i| <= cube` (an integer) whose
  squared length at the centre of `dom` is positive and at most `limit`.

`kind` (default `"tangent"`) selects the bound and the remaining fields:

| `kind` | Bound | Further fields |
|---|---|---|
| `"tangent"` | Lemma 7.5(ii), forms (a), (b), (c) | `mix`: `[[v, k], ...]`, a probability distribution `p` on the vertices of `dom`: start from the uniform distribution and, for each step (`0 <= v <= 255`, `1 <= k <= 4096`), replace `p` by `(1 - k/4096) p + (k/4096) delta_v`. The base points `(Q_j, T_j)` are the averages of `(q_j, t_j)` over the vertices with respect to `p`. |
| `"exponential"` | Lemma 7.5(iii) | none: the base points `Q_j` are the squared lengths at the centre of `dom`; reciprocal terms use the chord (7.4) of the phase over `dom` and are omitted where no chord exists. |
| `"vertexmax"` | Lemma 7.5(ii)(a) or (iii) with constant phase bounds | `form`: `"tangent"` or `"exponential"`; `reserve`: `true` adds the phase reserve of Lemma 7.5(iii'). The base points are upper bounds for the maxima of the squared lengths over the vertices of `dom`, which are their suprema over `dom`; the phase factors are bounded below by their minima over `dom`; the capacity of a reciprocal pair in the phase reserve is `2 F_d` at its base point. |

A support record must precede the records that refer to it; an identifier refers to the last support record with
that identifier that precedes the record and is not separated from it by a `forget` record. Wherever a leaf takes a
support `S`, `S` is either the `id` of a support record or an **inline description** `[KIND, alpha, cube, limit, ...]` (followed by `mix` for
`"tangent"` and by `reserve, form` for `"vertexmax"`), which stands for the support built on the box of the leaf
itself (for the leaf `AS`: on the box of the anchor, see below).

### `{"t": "forget"}`

Discards all support records and all regions read so far in the file.

### `{"t": "piece", "id": ID, "box": BOX, "tree": TREE, "leaves": [LEAF, ...]}`

A box received by the stage and its subdivision by bisections.

- `tree` is a string, the pre-order encoding of a binary tree: a digit `0`..`7` means "bisect this coordinate at its
  exact midpoint" and is followed by the encoding of the lower half and then of the upper half; `.` is a leaf.
- `leaves` lists the leaves in the order of the `.` symbols.
- Optional `"from": [BOX, ...]`: the held boxes that this record replaces (default: the box of the record itself).
  Each of them must lie in the box of the record.
- Optional fields `class` and `recorded` are ignored (`recorded` holds margins stored with the data of a leaf).

### `{"t": "cut", "id": ID, "box": BOX, "parts": [[BOX, LEAF], ...]}`

A box received by the stage and a subdivision into boxes with arbitrary rational endpoints. Every part must lie in
the box of the record, and the parts must cover it; the verifier decides this exactly. `from` as for a piece.

### `{"t": "region", "id": ID, "box": BOX, "leaf": LEAF}`

A box that is discharged by the rule `LEAF` (not `H` or `IN`) without being a part of the subdivision. Pieces and
cuts that follow in the same file may refer to it by leaves `IN`. Regions need not lie in `K`.

### `{"t": "end", "held": N}`

Last line: the number of held leaves of the file.

## Leaves

`S` is a support (identifier or inline description), `Q` a rational, `REG` a registration.

| Leaf | Statement of the paper | Meaning of the parameters |
|---|---|---|
| `["H"]` | none | the box is held: the next file has to replace it |
| `["IN", ID]` or `["IN", ID, s, n]` | Lemma 7.2(ii) | the box is contained in the box of region `ID`; in the second form, in its image under `iota` if `s = 1` (not if `s = 0`), translated by the integer vector `n` |
| `["N", KIND, m]` | (N) of Definition 7.1 | `m` three integers; `KIND = "full"`: (4.2) is violated strictly on the box for `m`; `"projected"`: (4.3) is violated strictly for `(m2, m3)` |
| `["SL", [[i, side, a, KIND, m], ...], LEAF]` | Lemma 7.2(iii) | slabs cut off one after the other along shape coordinates `i` in `0..4`: `side = 0` removes `{kappa_i <= a}`, `side = 1` removes `{kappa_i >= a}`; each slab satisfies (N) with the witness `(KIND, m)`; `LEAF` is applied to the remaining box |
| `["E1", alpha, cube]` | energy rule (i), Lemma 7.5(i) | partial sum over `max |m_i| <= cube` with interval bounds |
| `["E2", S]` | energy rule (ii), Lemma 7.5(ii) | `S` of kind `tangent`, or `vertexmax` with form `tangent` |
| `["E3", S]` | energy rule (iii), Lemma 7.5(iii) | `S` of kind `exponential`, or `vertexmax` with form `exponential` |
| `["E4", S, variant, rho]` | reduced variant, Lemma 7.5(iv) | `S` of kind `exponential` or `vertexmax`; `variant` 1 or 2 selects `c_1` or `c_2`; `lambda = rho * lambda_{e_1}`, `0 <= rho <= 1` |
| `["PL"]` | planar rule (i), Lemma 7.7(i) | none (the translation in `f3` is determined by the box) |
| `["PF", s, eta]` | planar rule (ii), Lemma 7.7(ii) with Lemma C.8 | after the translation `f3 -> f3 - s` (integer `s`), `|f3 - 1/2| <= eta` on the box |
| `["D1", S, REG]` | deficit rule (i), Lemma 7.9(i) | energy bound from `S`; defect bound from `REG` by Lemma 7.8(ii) |
| `["D3", S, REG, [x, y, z, w], k]` | deficit rule (ii), Lemma 7.9(ii) (joint vertex rule) | `S` of kind `tangent`; the rotation `U` is the one of the integer quaternion `(x, y, z, w)`; `t = k/4096` |
| `["AG", f0, n]` | anchor rules, Lemma 7.12, with the energy gain of Lemma C.3 | anchor `f0`, `n` |
| `["AS", f0, n, S]` | anchor rule (ii), Lemma 7.12(ii), with the energy gain of Lemma C.3 | `s_-` is obtained from the lower bound of `S` for the energy of the anchor on `S_box x {f0 + n}` (`S_box` the shape box of the leaf) and from Lemma 7.8(v); an inline `S` is built on that box |
| `["AP", f0, n]` | anchor rules, Lemma 7.12, with the planar gain of Lemma C.10 | `f0_3` in `1/2 + Z` |
| `["AC", f0, n]` or `["AC", f0, n, REG]` | centred tests, Lemma C.12 | as `AP`; `REG` is used for the bound `D^+` of test (ii) |

### Ranges of the parameters

A leaf whose parameters are outside these ranges is rejected: `alpha > 0`; `cube` in `1..4` for `E1`; in `E4`,
`variant` in `{1, 2}`, `0 <= rho <= 1`, and for `variant = 1` the box must satisfy `|x| <= 1/2`; in `PF`, `s` an integer
and `0 <= eta < 1/2`; in `D3`, the quaternion four integers, not all zero, and `k` an integer with `0 <= k <= 4096`; a
registration needs `det B = 1`, the columns of `B` in `Z^3 u (Z^3 + (1/2,1/2,1/2))`, `f0` in `(1/2)Z^3` outside
`Z^3` with `B f0` in the same lattice, and `n` three integers; an anchor needs `f0` in `(1/2)Z^3` outside `Z^3` and `n`
three integers, and `AP`, `AC` need `|f3 - f0_3 - n_3| < 1/2` on the box; a witness of (N) is a nonzero integer
vector (for `"projected"`, `(m2, m3)` nonzero); a slab is cut along a shape coordinate by a plane through the
interior of the remaining box; the steps `[v, k]` of a mixture are integers with `0 <= v <= 255`, `1 <= k <= 4096`.

## What the verifier requires of the files

**Completeness** (exact rational arithmetic). The verifier keeps a set of *held* boxes, initially `{K}` with the box
`K` of (4.5).

1. Every `tree` parses exactly and has as many leaves as `leaves`; then the leaf boxes cover the box of the piece.
   The parts of a cut lie in its box and cover it.
2. Every piece or cut of a file removes from the held set the boxes listed under `from` (default: its own box); each
   of them must be in the set and must lie in the box of the record. When the file has been read, the set must be
   empty. The boxes of the leaves `["H"]` of the file form the new set, and their number must equal `held` of the
   `end` record.
3. The box of a leaf `["IN", ...]` lies in the stated image of the box of the region it names.
4. A reflection step requires every held box to lie in `{f1 >= 0}` or in `{f1 <= 0}` and replaces the held set by
   the set of all boxes `P n iota(P')` of positive volume, `P` a held box in `{f1 >= 0}` and `P'` one in
   `{f1 <= 0}` (Section 7.8 of the paper, "Reflection"). At most one reflection step is allowed.
5. After the last file the held set is empty.

**Inequalities** (ball arithmetic). Every leaf other than `["H"]` and `["IN", ...]`, and the leaf of every region, is
accepted by its rule on its box at the working precision of the run.

Together these give Theorem 7.3: every point of `K` lies in a discharged box or in the mirror image of one.
