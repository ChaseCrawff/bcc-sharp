# Verifier for the cover of Theorem 7.3

This directory contains a standalone program that checks the cover of Theorem 7.3 of the paper "Optimality and sharp
stability of the body-centred cubic lattice for the Coulomb energy among periodic configurations with two points per
cell": a finite family of boxes in the eight-dimensional chart `(r1, r2, x, y, z, f1, f2, f3)`, each *discharged* by
one of the sufficient conditions of Section 7 and Appendix C, such that every point of the box `K` of (4.5) lies in a
discharged box or in the mirror image of one.

The program implements the statements of the paper. It
uses only the Python standard library and python-flint (the ball arithmetic of Arb), and it imports no other code.

## What is checked

The input is a *flat certificate*: a directory of files `stageNN*.jsonl[.gz]` in the format of [FORMAT.md](FORMAT.md).
Each file lists the boxes received by a stage and, for each of them, a subdivision whose parts are either *held*
(passed to the next file) or carry a rule and its exact parameters.

1. **Completeness, in exact rational arithmetic** (`boxes.py`, `verify.py`). Every bisection keeps both closed halves;
   every other subdivision is tested to be a cover; the boxes replaced by a file are exactly the boxes held by the
   preceding one; the first file starts from `K`; the last file holds nothing. The reflection step of Section 7.8 is
   carried out by the verifier itself, and so is every containment of a box in a translate or mirror image of a
   discharged box (Lemma 7.2(ii)). No volume and no floating-point number is used.
2. **Inequalities, in ball arithmetic** (`rules.py` and the modules it uses). For every part that carries a rule, the
   hypothesis of the rule is recomputed on the box from its parameters, and the part is accepted only if the
   inequality holds for the whole ball. A non-finite ball is a rejection.

All data in the certificate are untrusted: base points, weights, registrations, rotations, anchors, witnesses and
trees are proposals whose only effect is whether an inequality can be accepted. Parameters outside the ranges that
the lemmas require (FORMAT.md) are rejected.

Boxes that carry a rule are not required to lie in the shape part of `K` (some are centred on its faces `x = 0`,
`y = 0`). This does not affect Theorem 7.3: bisection, containment, reflection and integer translation do not change
the shape coordinates, so every point of `K` is covered within the shape part of `K`; and the only rule whose proof
uses the shape part of `K`, the reduced variant with `c_1` (it needs `x^2 <= 1/4`), tests this on its box.

## What is taken as given

- **The lattice case, Theorem 5.1** of the paper (`e - e_B >= g D` for all lattices, with equality only for the
  body-centred and face-centred cubic lattices). It enters through condition (A) of Definition 7.1, through the lower
  bound `s_- >= 0` of Lemma 7.12(ii) and through Lemma 7.12(iii). It has an independent formal proof (Section 9.5).
- **The enclosures of the constants** `e_B`, `e_F` of Section 9.2 (Proposition 2.7); they are the four rational
  numbers at the top of `balls.py`.
- **Montgomery's theorem** on the planar theta function, in planar rule (i) (Lemma 7.7(i)).
- The analytic statements of the paper: the lemmas of Sections 3, 4, 7 and Appendices B, C say that each rule implies
  the condition it claims. The verifier checks hypotheses, not proofs.

The trusted base of a run is therefore: the source in this directory; CPython's integers and `fractions`; and the
operations of Arb used here (`+ - * /`, integer powers, `sqrt`, `root`, `exp`, `log`, `sin`, `cos`, `cos_pi`, `sinh`,
`cosh`, `erfc`, `floor`, the constant pi, products of matrices of balls, unions, minima and maxima of balls, bounds
for absolute values, midpoints and radii, endpoint extraction and comparisons).

Every box of the certificate is discharged by one of the conditions (N), (E), (D) or (A) of Definition 7.1, through
the rules listed below; the verifier accepts no other kind of leaf.

## Rules

| Leaf | Function in `rules.py` | Statement implemented | Condition obtained |
|---|---|---|---|
| `N` | `rule_n` | Definition 7.1(N) through a strict violation of (4.2) or (4.3) | (N) |
| `SL` | `rule_slabs` | Lemma 7.2(iii) | that of the inner rule |
| `E1` | `rule_e1` | Lemma 7.5(i) | (E) |
| `E2`, `E3`, `E4` | `rule_e` | Lemma 7.5(ii), (iii), (iii'), (iv) | (E) |
| `PL` | `rule_pl` | Lemma 7.7(i) with the tails of Section C.4 | (E) |
| `PF` | `rule_pf` | Lemma 7.7(ii) with Lemma C.8 and Remark C.9 | (E) |
| `D1` | `rule_d1` | Lemma 7.9(i) with Lemma 7.8(ii) | (D) |
| `D3` | `rule_d3` | Lemma 7.9(ii) (joint vertex rule) with the majorant that follows it | (D) |
| `AG` | `rule_ag` | Lemma 7.12 with Lemmas C.3, C.5, C.6 | (A), (D) or (E) |
| `AS` | `rule_as` | Lemma 7.12(ii) with Lemmas 7.5, 7.8(v), C.3, C.5, C.6 | (D) |
| `AP` | `rule_ap` | Lemma 7.12 with Lemmas C.10, C.5, C.6 | (A), (D) or (E) |
| `AC` | `rule_ac` | Lemma C.12 with Lemmas C.10, C.11 | (E) or (D) |

## Modules and the statements they implement

| Module | Content | Paper |
|---|---|---|
| `balls.py` | constants, kernels `F_r`, `F_d`, the functions `G(a, t)` | (2.5), (7.2), (C.1), Sections 9.1, 9.2 |
| `boxes.py` | boxes, bisection trees, exact covering test, reflection, translation, the reflection step | Sections 7.1, 7.8, Lemma 7.2 |
| `shape.py` | `R(xi)`, `M`, `M^-1`, squared lengths | (4.1), (7.2) |
| `energy.py` | supports and the vertex principle | Lemmas 7.4, 7.5, (7.3)-(7.6) |
| `defect.py` | registrations; bounds for the defect; the convex majorant; the complete list; the growth coefficient | Lemma 7.8, text after Lemma 7.9, Lemma C.5 |
| `jets.py` | first and second derivatives in ball arithmetic; the bounds (5.4)-(5.6); `LDL^T` | Section 5.2, Lemma C.6(i) |
| `planar.py` | layer bound; fibre bound; planar gain; energy of an anchor | Lemma 7.7, Lemmas C.7, C.8, Remark C.9, Lemmas C.10, C.11 |
| `gain.py` | uniform energy-gain form | Lemmas C.1, C.2, C.3, Remark C.4 |
| `anchor.py` | positivity tests; anchor rules; centred tests | Lemmas 7.12, C.6, C.12 |
| `rules.py` | one function per kind of leaf | see the table above |
| `verify.py` | the two passes, the log and the receipt | Theorem 7.3 |
| `refine.py` | auxiliary: replaces leaves that a run rejects by other rules or by bisections (its output is a certificate, to be verified) | |
| `controls.py` | negative controls | |

## Choices made by the verifier

Where the paper leaves a parameter free and the certificate does not store it, the verifier computes it by a fixed
recipe; these recipes affect only the strength of a bound.

- *Supports.* The set of terms and the base points are determined by the box of the support and by its description
  (FORMAT.md). For a tangent support the choice between the forms (b) and (c) of Lemma 7.5(ii) for a reciprocal term
  is described in the docstring of `energy.TangentSupport`; the weights of the phase reserve are allocated greedily
  (`energy.VertexMaxSupport`).
- *Enclosures over a shape box.* Functions of the shape are enclosed by their interval value intersected with the mean
  value form (5.4); lower bounds use the largest of the interval value, (5.5) and (5.6).
- *Anchor rules.* The tests of Lemma C.6 are tried in the order (i), (ii), then the floor `J` with `s_- = 0`, then the
  comparison with `g^+ (1 - D_0^-)`; the first success decides. The list of registrations of Lemma 7.8(iv) is
  computed by the verifier for the shape box of the leaf.
- *Planar rules.* In the fibre bound all three bounds of Lemma C.8 and Remark C.9 are evaluated and the best is used.
  In the layer bound the in-plane term is bounded by Montgomery's theorem.

## Running

```
python -B -m cover_verifier.verify CERTIFICATE_DIRECTORY --workers 8 --bits 128 --receipt receipt.json --log run.log
```

run from the parent directory of this one. The exit status is 0 when no check that was run failed. A run that skips a pass or checks only part of the chain
ends with `PASS OF AN INCOMPLETE RUN` and records its scope in the receipt; only scope `complete` with result `PASS`
establishes the theorem. The receipt
records the SHA-256 of every source file of the verifier and of every input file, taken at the start of the run
(`verifier`, `inputs`) and again at its end (`verifier_at_end`, `inputs_at_end`; a run during which they differ
fails), the interpreter and library versions, the number of boxes per rule and condition, the smallest margin per rule
with the box where it occurs, and the CPU time. `--partial` checks a directory that contains only some consecutive stages: the
boxes of its first file are then taken as given, and boxes may remain held at the end.

A margin reported for a rule is the lower endpoint of the quantity whose positivity was proved: an energy per
particle for conditions (E) and (D), `1 - sup` of the left side of (4.2) or (4.3) divided by its right side for (N),
and the least pivot of an `LDL^T` factorization for condition (A).

```
python -B -m cover_verifier.controls CERTIFICATE_DIRECTORY --report controls.json
```

runs the negative controls: rules applied where their conclusion is false, leaves of the certificate with a changed
parameter or with the box moved outside the hypotheses of the rule, and certificates with a removed box, a false
cover, a false containment or a misused reflection step. Every control must be rejected; in a control that changes a
leaf, the unchanged leaf must also be accepted, and the two completeness baselines must both pass.

```
python -B -m cover_verifier.refine CERTIFICATE_DIRECTORY RECEIPT OUTPUT_DIRECTORY
```

replaces rejected leaves by other rules or by bisections. Use an output directory whose stage files are distinct
from every input stage and the receipt. Replay the resulting certificate to verify it.
