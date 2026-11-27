import BccSharp.TwoSite.ReciprocalRepetition

set_option autoImplicit false

/-! Inverse-length scaling for the screened Ewald energy, including
the neutralizing constant and the regular self term. Change the Ewald split
from α to α/t when the lengths are multiplied by t. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

theorem sq_mulVec_gram (B : Mat) (v : Vec) : sq (B.mulVec v) = quad (gram B) v := by
  change sq (B.mulVec v) = dot v ((B.transpose*B).mulVec v)
  rw [← Matrix.mulVec_mulVec, dot_mulVec_eq B.transpose v (B.mulVec v), Matrix.transpose_transpose]
  simp only [sq, dot, pow_two]

theorem dualWave_sq_gram (B : Mat) (n : IntVec) :
    sq (dualWave B n) = (2*Real.pi)^2 * quad (gram B)⁻¹ (castVec n) := by
  rw [dualWave, sq_smul, sq_mulVec_gram]
  unfold gram
  rw [Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]

theorem volume_scale (t : ℝ) (ht : 0 < t) (B : Mat) : volumeOf (t • B) = t^3 * volumeOf B := by
  simp only [volumeOf, Matrix.det_smul, Fintype.card_fin, abs_mul, abs_of_pos (pow_pos ht 3)]

theorem linearImage_scale (t : ℝ) (B : Mat) (n : IntVec) :
    linearImage (t • B) n = t • linearImage B n := by
  simp [linearImage, Matrix.smul_mulVec]

theorem dualWave_scale (t : ℝ) (ht : 0 < t) (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    dualWave (t • B) n = t⁻¹ • dualWave B n := by
  have inv : (t • B)⁻¹ = t⁻¹ • B⁻¹ := by
    have h := Matrix.inv_smul' B (Units.mk0 t ht.ne') (isUnit_iff_ne_zero.mpr hB)
    simpa only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] using h
  simp only [dualWave, inv, Matrix.transpose_smul, Matrix.smul_mulVec, smul_smul]
  rw [mul_comm]

theorem dot_right_smul (t : ℝ) (k x : Vec) : dot k (t • x) = t * dot k x := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem screened_scale (α t : ℝ) (ht : 0 < t) (x : Vec) : screened (α/t) (t • x) = screened α x/t := by
  unfold screened
  rw [norm_smul_nonnegative t x ht.le]
  have he : α/t * (t * Real.sqrt (sq x)) = α * Real.sqrt (sq x) := by field_simp [ht.ne']
  rw [he, div_div, mul_comm t]

theorem reciprocalGreenTerm_scale (α t : ℝ) (ht : 0 < t) (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    reciprocalGreenTerm (α/t) (t • B) n = t^2 * reciprocalGreenTerm α B n := by
  unfold reciprocalGreenTerm
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn, dualWave_scale t ht B hB n, sq_smul]
    let q := sq (dualWave B n)
    change Real.exp (-((t⁻¹)^2*q / (4*(α/t)^2))) / ((t⁻¹)^2*q) =
      t^2*(Real.exp (-(q/(4*α^2)))/q)
    have hex : (t⁻¹)^2*q/(4*(α/t)^2) = q/(4*α^2) := by
      by_cases ha : α = 0
      · simp [ha]
      · field_simp [ht.ne', ha] <;> ring
    rw [hex]
    by_cases hq : q = 0
    · simp [hq]
    · field_simp [ht.ne', hq] <;> ring

theorem background_scale (α t : ℝ) (ht : 0 < t) (B : Mat) (hB : B.det ≠ 0) :
    greenBackground (α/t) (t • B) = greenBackground α B/t := by
  unfold greenBackground
  rw [volume_scale t ht B]
  by_cases ha : α = 0
  · simp [ha]
  · have hv : volumeOf B ≠ 0 := (abs_pos.mpr hB).ne'
    field_simp [ht.ne', ha, hv] <;> ring

theorem periodicGreen_scale (α t : ℝ) (ht : 0 < t) (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    periodicGreen (α/t) (t • B) (t • x) = periodicGreen α B x/t := by
  unfold periodicGreen
  have hR : (∑' n, screened (α/t) (t • x + linearImage (t • B) n)) =
      (∑' n, screened α (x + linearImage B n))/t := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    rw [linearImage_scale, ← smul_add, screened_scale α t ht]
  have hD : (∑' n, reciprocalGreenTerm (α/t) (t • B) n*
      Real.cos (dot (dualWave (t • B) n) (t • x))) =
      t^2*(∑' n, reciprocalGreenTerm α B n*Real.cos (dot (dualWave B n) x)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [reciprocalGreenTerm_scale α t ht B hB, dualWave_scale t ht B hB, dot_right_smul, dot_left_smul]
    have ep : t * (t⁻¹ * dot (dualWave B n) x) = dot (dualWave B n) x := by field_simp [ht.ne']
    rw [ep, mul_assoc]
  rw [hR, hD, volume_scale t ht B, background_scale α t ht B hB]
  field_simp [ht.ne', ((abs_pos.mpr hB).ne' : volumeOf B ≠ 0)] <;> ring

theorem regularSelf_scale (α t : ℝ) (ht : 0 < t) (B : Mat) (hB : B.det ≠ 0) :
    ewaldRegularSelf (α/t) (t • B) = ewaldRegularSelf α B/t := by
  unfold ewaldRegularSelf
  have hR : (∑' n : IntVec, if n=0 then 0 else screened (α/t) (linearImage (t • B) n)) =
      (∑' n : IntVec, if n=0 then 0 else screened α (linearImage B n))/t := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    by_cases hn : n=0
    · simp [hn]
    · rw [if_neg hn, if_neg hn, linearImage_scale, screened_scale α t ht]
  have hD : (∑' n, reciprocalGreenTerm (α/t) (t • B) n) =
      t^2 * (∑' n, reciprocalGreenTerm α B n) := by
    rw [← tsum_mul_left]
    exact tsum_congr (reciprocalGreenTerm_scale α t ht B hB)
  rw [hR, hD, volume_scale t ht B, background_scale α t ht B hB]
  field_simp [ht.ne', ((abs_pos.mpr hB).ne' : volumeOf B ≠ 0),
    (Real.sqrt_pos.mpr Real.pi_pos).ne'] <;> ring

theorem greenPerParticle_scale {ι : Type} [Fintype ι] (α t : ℝ) (ht : 0 < t)
    (B : Mat) (hB : B.det ≠ 0) (s : ι → Vec) :
    greenPerParticle (α/t) (t • B) (fun i => t • s i) = greenPerParticle α B s/t := by
  have hs : (∑ i, ∑ j, if i=j then 0 else periodicGreen (α/t) (t • B) (t • s i - t • s j)) =
      (∑ i, ∑ j, if i=j then 0 else periodicGreen α B (s i - s j))/t := by
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i=j
    · simp [h]
    · rw [if_neg h, if_neg h, ← smul_sub, periodicGreen_scale α t ht B hB]
  unfold greenPerParticle greenCellEnergy
  dsimp only
  rw [hs, regularSelf_scale α t ht B hB]
  by_cases hn : (Fintype.card ι : ℝ) = 0
  · simp [hn]
  · field_simp [ht.ne', hn] <;> ring

end BccSharp.Coulomb
