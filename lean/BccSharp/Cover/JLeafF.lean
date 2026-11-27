import BccSharp.Cover.JLeafCheck

set_option autoImplicit false

/-! F leaves of the JointDeficit/Continuation adaptive trees: the shared energy minorant of
`BccSharp.Cover.JLeafTerms` exceeds the upper Constants FCC energy at all 256 corners of
the leaf, so the energy is strictly above `e_FCC` throughout the closed box. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.DirectRoute (cornerRat scaleInput scaleWitness)
open BccSharp.Coulomb.BravaisCover (cubeRootCheck)

def fCornerLower (b : Cell) (K : ℚ) (wt : Fin 19 → ℚ) (bits : Axis → Bool) : ℚ :=
  divScale (aggValueQ K wt (cornerRat b bits) - 4) - Constants.fccBracket.hi

def FLeafGood (b S : Cell) (K : ℚ) (wt : Fin 19 → ℚ) : Prop :=
  boxIn b S = true ∧ 0 < b.lo 0 ∧ 0 < b.lo 1 ∧ (∀ i, b.lo i ≤ b.hi i) ∧
    cubeRootCheck scaleWitness scaleInput = true ∧ 0 < scaleWitness.lower ∧
    cornerCheck (fCornerLower b K wt) = true

instance (b S : Cell) (K : ℚ) (wt : Fin 19 → ℚ) : Decidable (FLeafGood b S K wt) := by
  unfold FLeafGood; infer_instance

def fleafCheck (b S : Cell) (K : ℚ) (wt : Fin 19 → ℚ) : Bool := decide (FLeafGood b S K wt)

/-- Soundness of one F leaf: energy strictly above FCC at every valid point of
the box. -/
theorem fleaf_sound (S b : Cell) (lins : List LinTerm) (K : ℚ) (wt : Fin 19 → ℚ)
    (valid : ∀ t ∈ lins, t.Valid S) (hs : structureOk lins = true)
    (hK : aggConst lins = K) (hw : ∀ j, aggWeight lins j = wt j)
    (hl : fleafCheck b S K wt = true) (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) := by
  have g : FLeafGood b S K wt := of_decide_eq_true hl
  obtain ⟨inside, lo0, lo1, ordered, cube, lower, corners⟩ := g
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast lo0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast lo1
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  let F : Chart → ℝ := fun x => (linSum lins x - 4) / (2 * ac) - (Constants.fccBracket.hi : ℝ)
  have chord : ChordLower b F := by
    have base := linSum_chord lins b b0 b1 (fun t ht => (valid t ht).1)
    intro x hx i t t0 t1 e
    have h := base x hx i t t0 t1 e
    show (1 - t) * ((linSum lins (atLower b x i) - 4) / (2 * ac) - (Constants.fccBracket.hi : ℝ)) +
      t * ((linSum lins (atUpper b x i) - 4) / (2 * ac) - (Constants.fccBracket.hi : ℝ)) ≤
        (linSum lins x - 4) / (2 * ac) - (Constants.fccBracket.hi : ℝ)
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have ipos : (0 : ℝ) ≤ (2 * ac)⁻¹ := inv_nonneg.mpr acpos.le
    nlinarith [mul_le_mul_of_nonneg_right h ipos]
  have enclose : ∀ bits, (fCornerLower b K wt bits : ℝ) ≤ F (corner b bits) := by
    intro bits
    have c0 : cornerRat b bits 0 ≠ 0 := (cornerRat_pos b bits 0 lo0 (ordered 0)).ne'
    have c1 : cornerRat b bits 1 ≠ 0 := (cornerRat_pos b bits 1 lo1 (ordered 1)).ne'
    have cr0 : (corner b bits) 0 ≠ 0 := by rw [corner_coord]; exact_mod_cast c0
    have cr1 : (corner b bits) 1 ≠ 0 := by rw [corner_coord]; exact_mod_cast c1
    have lin := linSum_feat lins (corner b bits) cr0 cr1
    have agg : linSum lins (corner b bits) = (aggValueQ K wt (cornerRat b bits) : ℝ) := by
      rw [lin, ← hK]
      unfold aggValueQ
      push_cast
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hw j, featGen_cast, cornerRat_cast]
    have div := divScale_le (aggValueQ K wt (cornerRat b bits) - 4) cube lower
    show (fCornerLower b K wt bits : ℝ) ≤
      (linSum lins (corner b bits) - 4) / (2 * ac) - (Constants.fccBracket.hi : ℝ)
    rw [agg]
    unfold fCornerLower
    push_cast at div ⊢
    linarith
  have pos := cornerCheck_sound b F chord (fCornerLower b K wt) enclose corners p hp
  have lowerE : (linSum lins p - 4) / (2 * ac) ≤ energy (chartPoint p) := by
    have h := support_sound S lins valid hs p (boxIn_sound inside hp) hv
    show (linSum lins p - 4) / (2 * ac) ≤ (h₂ (chartPoint p) - 4) / (2 * ac)
    exact div_le_div_of_nonneg_right (by linarith) acpos.le
  have fccUp : energy fcc ≤ (Constants.fccBracket.hi : ℝ) := (Constants.reference_bounds .fcc).2
  have : 0 < F p := pos
  simp only [F] at this
  linarith

/-- The same leaf as a route result for the cover framework, on `good` points. -/
theorem fleaf_sound_good (S b : Cell) (lins : List LinTerm) (K : ℚ) (wt : Fin 19 → ℚ)
    (valid : ∀ t ∈ lins, t.Valid S) (hs : structureOk lins = true)
    (hK : aggConst lins = K) (hw : ∀ j, aggWeight lins j = wt j)
    (hl : fleafCheck b S K wt = true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  fleaf_sound S b lins K wt valid hs hK hw hl p hp gp.1

end BccSharp.Coulomb.CompactCover.JLeaf
