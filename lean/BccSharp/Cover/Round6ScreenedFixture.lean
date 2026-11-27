import BccSharp.Cover.Round6ScreenedLeaf
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false

/-! A Continuation round-six J leaf at the recorded Ewald screening 23/20, end to end.

`BccSharp.Cover.Round6ScreenedLeaf` proves the strict J comparison at every valid
point of the leaf box `leaf6` (tree slot 9, leaf path
`f`, support path the whole root) through `jleaf_sound_screened`, with all
178 support terms and all 256 corner margins kernel-checked at `s = 23/20`.
Here:

* `round6_leaf_all`: `0 < deficit` at every point of the leaf box, with no
  premise. `round6_leaf_valid` shows that every point of the box is valid
  (`valid_of_box`: positive radial coordinates, first offset coordinate in
  `(0, 1)`).
* `round6_nonvacuous`: the box contains a `good` point (valid, reduced and
  separated), the rational point `goodPoint`, by `good_of_check`. Unlike the
  round-seven fixture, this leaf therefore certifies points through the cover
  framework (`round6_leaf_good`).
* At `s = 1` the published envelope does not close this leaf: the untrusted
  numerical sweep and the `#eval` dump of the s = 1 evaluator give a
  negative minimum corner margin. That is a statement about
  the re-proposed s = 1 support, not a kernel-checked theorem.
* Negative controls, each failing for a real reason:
  - `item_mutation_rejected`: a changed literal term is rejected, because the
    checker recomputes the term from its witness;
  - `leaf_mutation_rejected`: lowering the support constant by `2·10⁻⁸`
    (`4.9·10⁻⁹` per particle, more than the leaf's minimum margin
    `3.08·10⁻⁹`) makes the 256-corner check fail;
  - `screening_mutation_rejected`: checking the same support with the s = 1
    constant `4` in place of `2s + 2/s²` fails;
  - `screening_in_terms_rejected`: a cross item computed at `23/20` is
    rejected at `s = 1`, so the screening enters the term computation. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.JLeaf.Round6
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Screened

/-- Every point of the leaf box is a valid chart point. -/
theorem round6_leaf_valid (p : Chart) (hp : leaf6.Mem p) : (chartPoint p).Valid :=
  valid_of_box leaf6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) p hp

/-- **The round-six leaf at every point of its box**, with no premise:
`e − e_BCC − g D > 0` for the Series energy and the actual capped defect. -/
theorem round6_leaf_all (p : Chart) (hp : leaf6.Mem p) : 0 < deficit (chartPoint p) :=
  leaf6_strict p hp (round6_leaf_valid p hp)

/-- The same leaf as a route result of the cover framework, on `good` points. -/
theorem round6_leaf_good (p : Chart) (hp : leaf6.Mem p) (gp : good p) :
    Route.result .strictJoint p :=
  jleaf_sound_screened_good screen support6 leaf6 lins6 K6 w6 reg6 valid6 struct6 agg6.1 agg6.2
    leafOk6 p hp gp

/-- A rational point of the leaf box near its most reduced corner. -/
def goodPoint : Fin 8 → ℚ :=
  ![181 / 209, 422 / 517, 77 / 230, 1 / 1280, -1 / 3414, 1280 / 2561, 853 / 1707, 1707 / 3415]

theorem goodPoint_mem : ∀ i, leaf6.lo i ≤ goodPoint i ∧ goodPoint i ≤ leaf6.hi i := by
  decide +kernel

/-- `goodPoint` is valid, reduced and separated: `x ≥ √(1 − r₂²/r₁²)` holds there
with room `3.1·10⁻⁴` in `r₁² x² + r₂² − r₁²`, and the third offset coordinate is
at distance `1707/3415` from the integers. -/
theorem goodPoint_good : good (fun i => (goodPoint i : ℝ)) :=
  good_of_check goodPoint 0 0 (1707 / 3415) (by decide +kernel)

/-- **Non-vacuity**: the leaf box contains a good point. -/
theorem round6_nonvacuous : ∃ p : Chart, leaf6.Mem p ∧ good p := by
  refine ⟨fun i => (goodPoint i : ℝ), ?_, goodPoint_good⟩
  intro i
  obtain ⟨h1, h2⟩ := goodPoint_mem i
  exact ⟨(Rat.cast_le (K := ℝ)).mpr h1, (Rat.cast_le (K := ℝ)).mpr h2⟩

/-- Negative control: changing one literal coefficient makes the item fail. -/
theorem item_mutation_rejected :
    itemOkS screen support6 ⟨it6_0.wit, { it6_0.lin with const := it6_0.lin.const + 1 }⟩ =
      false := by
  decide +kernel

/-- Negative control at leaf level: lowering the support constant by `2·10⁻⁸`
makes some corner margin negative, so the 256-corner check fails. -/
theorem leaf_mutation_rejected :
    leafCheckS screen leaf6 support6 (K6 - 2 / 100000000) w6 reg6 = false := by
  decide +kernel

/-- Negative control on the screening: the screened support checked with the
s = 1 constant `4` instead of `2s + 2/s²` fails. -/
theorem screening_mutation_rejected : leafCheckS 1 leaf6 support6 K6 w6 reg6 = false := by
  decide +kernel

/-- Negative control on the screening inside the terms: the first cross item,
whose literal was computed at `23/20`, is rejected at `s = 1`, because the
checker recomputes the term with the prefactors `s` and `s³`. -/
theorem screening_in_terms_rejected : itemOkS 1 support6 it6_15 = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.JLeaf.Round6
