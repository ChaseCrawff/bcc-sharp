import BccSharp.Cover.JLeafScreenedTerms

set_option autoImplicit false

/-! J-leaf checker at a rational Ewald screening `s > 0`, and its soundness.

The screened energy minorant is `T = (linSum − (2s + 2/s²)) / (2 a_c)`
(`support_soundS`). At the 256 corners of a leaf it differs from the s = 1
minorant `(linSum − 4) / (2 a_c)` only through the constant, so the screened
check is the s = 1 `leafCheck` of `BccSharp.Cover.JLeafCheck` applied to the support
constant `K + 4 − (2s + 2/s²)` (`aggValue_shift`), together with `0 < s`.
`jleaf_sound_screened` repeats the proof of `jleaf_sound` with the screened
energy bound; the registered-cost and common-corner steps are unchanged.
The screening `s` is a rational parameter of the leaf data. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf.Screened
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.DirectRoute (cornerRat scaleInput scaleWitness)

/-- `2s + 2/s²`, the constant of the screened series (`4` at `s = 1`). -/
def selfConst (s : ℚ) : ℚ := 2 * s + 2 / (s * s)

theorem selfConst_cast (s : ℚ) : ((selfConst s : ℚ) : ℝ) = 2 * (s : ℝ) + 2 / (s : ℝ) ^ 2 := by
  simp only [selfConst]
  push_cast
  ring

theorem selfConst_one : selfConst 1 = 4 := by norm_num [selfConst]

/-- Shifting the support constant by `4 − c` turns the s = 1 corner value
`aggValueQ K' wt x − 4` into `aggValueQ K wt x − c`. -/
theorem aggValue_shift (K c : ℚ) (wt : Fin 19 → ℚ) (x : Fin 8 → ℚ) :
    aggValueQ (K + 4 - c) wt x - 4 = aggValueQ K wt x - c := by
  unfold aggValueQ
  ring

/-- The screened leaf check: `0 < s`, and the s = 1 leaf check with the
support constant shifted by `4 − (2s + 2/s²)`. -/
def leafCheckS (s : ℚ) (b S : Cell) (K : ℚ) (wt : Fin 19 → ℚ) (r : RegData) : Bool :=
  decide (0 < s) && leafCheck b S (K + 4 - selfConst s) wt r

/-- **Soundness of one J leaf at screening `s`.** Strict deficit at every valid
point of the closed leaf box, from a support whose terms are valid at screening
`s` on a box containing the leaf. -/
theorem jleaf_sound_screened (s : ℚ) (S b : Cell) (lins : List LinTerm) (K : ℚ)
    (wt : Fin 19 → ℚ) (r : RegData) (valid : ∀ t ∈ lins, TermValid s S t)
    (hs : structureOk lins = true) (hK : aggConst lins = K) (hw : ∀ j, aggWeight lins j = wt j)
    (hl : leafCheckS s b S K wt r = true) (p : Chart) (hp : b.Mem p)
    (hv : (chartPoint p).Valid) : 0 < deficit (chartPoint p) := by
  obtain ⟨sok, hl1⟩ := Bool.and_eq_true_iff.mp hl
  have spos : 0 < s := of_decide_eq_true sok
  have g : LeafGood b S (K + 4 - selfConst s) wt r := of_decide_eq_true hl1
  obtain ⟨inside, lo0, lo1, ordered, cube, lower, reg, unit, cond, small, corners⟩ := g
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast lo0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast lo1
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  let T : Chart → ℝ := fun x => (linSum lins x - ((selfConst s : ℚ) : ℝ)) / (2 * ac)
  let C : Chart → ℝ := regCost r.N r.U r.w
  -- Separate concavity of the energy minorant.
  have energyChord : ChordLower b T := by
    have base := linSum_chord lins b b0 b1 (fun t ht => (valid t ht).1)
    intro x hx i t t0 t1 e
    have h := base x hx i t t0 t1 e
    show (1 - t) * ((linSum lins (atLower b x i) - ((selfConst s : ℚ) : ℝ)) / (2 * ac)) +
      t * ((linSum lins (atUpper b x i) - ((selfConst s : ℚ) : ℝ)) / (2 * ac)) ≤
        (linSum lins x - ((selfConst s : ℚ) : ℝ)) / (2 * ac)
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have ipos : (0 : ℝ) ≤ (2 * ac)⁻¹ := inv_nonneg.mpr acpos.le
    nlinarith [mul_le_mul_of_nonneg_right h ipos]
  -- Separate convexity of the registered cost.
  have costChord : ChordUpper b C := regCost_chord r.N r.U r.w b b0 b1 unit cond
  -- Energy lower bound from the screened support.
  have energyLower : ∀ x, b.Mem x → (chartPoint x).Valid → T x ≤ energy (chartPoint x) := by
    intro x hx gx
    have h := support_soundS s spos S lins valid hs x (boxIn_sound inside hx) gx
    show (linSum lins x - ((selfConst s : ℚ) : ℝ)) / (2 * ac) ≤ energy (chartPoint x)
    rw [selfConst_cast]
    exact h
  -- The cost is at most 1/2 on the box, so it bounds the defect.
  have costSmall : ∀ x, b.Mem x → C x ≤ 1 / 2 := by
    intro x hx
    obtain ⟨bits, hb⟩ := corner_le b (fun y => -C y) costChord x hx
    have cv : C (corner b bits) = (regCostQ r.N r.U r.w (cornerRat b bits) : ℝ) := by
      rw [← cornerRat_cast b bits]
      exact (regCostQ_cast r.N r.U r.w (cornerRat b bits)
        (cornerRat_pos b bits 0 lo0 (ordered 0)).ne'
        (cornerRat_pos b bits 1 lo1 (ordered 1)).ne').symm
    have hs := (Rat.cast_le (K := ℝ)).mpr (small bits)
    push_cast at hs
    have : C (corner b bits) ≤ 1 / 2 := by rw [cv]; exact hs
    have hb' : -C (corner b bits) ≤ -C x := hb
    linarith
  have defectUpper : ∀ x, b.Mem x → (chartPoint x).Valid → defect (chartPoint x) ≤ C x := by
    intro x hx gx
    exact defect_le_regCost r.B r.N r.U r.f0 r.wrap reg x gx (costSmall x hx)
  -- Corner values.
  have cornerVals : ∀ bits, (cornerLower b (K + 4 - selfConst s) wt r bits : ℝ) ≤
      jointFunction T C 4096 (corner b bits) := by
    intro bits
    have c0 : cornerRat b bits 0 ≠ 0 := (cornerRat_pos b bits 0 lo0 (ordered 0)).ne'
    have c1 : cornerRat b bits 1 ≠ 0 := (cornerRat_pos b bits 1 lo1 (ordered 1)).ne'
    have cr0 : (corner b bits) 0 ≠ 0 := by
      rw [corner_coord]; exact_mod_cast c0
    have cr1 : (corner b bits) 1 ≠ 0 := by
      rw [corner_coord]; exact_mod_cast c1
    have lin := linSum_feat lins (corner b bits) cr0 cr1
    have agg : linSum lins (corner b bits) = (aggValueQ K wt (cornerRat b bits) : ℝ) := by
      rw [lin, ← hK]
      unfold aggValueQ
      push_cast
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hw j, featGen_cast, cornerRat_cast]
    have cost : C (corner b bits) = (regCostQ r.N r.U r.w (cornerRat b bits) : ℝ) := by
      rw [← cornerRat_cast b bits]
      exact (regCostQ_cast r.N r.U r.w (cornerRat b bits) c0 c1).symm
    have div := divScale_le (aggValueQ (K + 4 - selfConst s) wt (cornerRat b bits) - 4) cube lower
    rw [aggValue_shift] at div
    unfold jointFunction mixedDefect
    show (cornerLower b (K + 4 - selfConst s) wt r bits : ℝ) ≤
      (linSum lins (corner b bits) - ((selfConst s : ℚ) : ℝ)) / (2 * ac) -
      (Constants.bccBracket.hi : ℝ) - (Constants.gapBracket.hi : ℝ) *
        (1 - ((4096 : ℕ) : ℝ) / 4096 + ((4096 : ℕ) : ℝ) / 4096 * C (corner b bits))
    rw [agg, cost]
    unfold cornerLower
    rw [aggValue_shift]
    push_cast at div ⊢
    norm_num
    linarith
  exact jointCorner_sound_valid b T C 4096 (cornerLower b (K + 4 - selfConst s) wt r)
    (by norm_num) energyChord costChord energyLower defectUpper cornerVals corners p hp hv

/-- The same leaf as a route result for the cover framework, on `good` points. -/
theorem jleaf_sound_screened_good (s : ℚ) (S b : Cell) (lins : List LinTerm) (K : ℚ)
    (wt : Fin 19 → ℚ) (r : RegData) (valid : ∀ t ∈ lins, TermValid s S t)
    (hs : structureOk lins = true) (hK : aggConst lins = K) (hw : ∀ j, aggWeight lins j = wt j)
    (hl : leafCheckS s b S K wt r = true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    Route.result .strictJoint p :=
  jleaf_sound_screened s S b lins K wt r valid hs hK hw hl p hp gp.1

end BccSharp.Coulomb.CompactCover.JLeaf.Screened
