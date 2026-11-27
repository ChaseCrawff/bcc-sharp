import BccSharp.Lattice.GeometricLeaves
import BccSharp.TwoSite.ReferencePoints

set_option autoImplicit false

/-! Conversion of the Lattice positive series to the physical one-site
energy. Finite positive truncations can be compared for the strict E1
route in the same normalization as the reference gap and primitive anchor. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover

def bravaisScale : ℝ := ac / Constants.fccLength

theorem bravaisScale_positive : 0 < bravaisScale := by
  have h : 0 < Constants.fccLength := by unfold Constants.fccLength; positivity
  exact div_pos ac_positive h

theorem bravaisScale_cube : bravaisScale^3 = 4*Real.pi/3 := by
  have ht : Constants.fccLength^3 = 2 := by
    rw [Constants.fccLength, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [bravaisScale,div_pow,ac_cube,ht]
  ring

def normalizedChart (p : Point) : Mat := chartBasis (coordLift p)
def primitiveChart (p : Point) : Mat := Constants.fccLength⁻¹ • normalizedChart p

theorem normalizedChart_det (p : Point) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    (normalizedChart p).det = 1 := by
  rw [normalizedChart,chartBasis, Matrix.det_fin_three]
  norm_num [coordLift]
  field_simp [h0,h1]

def shortKernel (R : Mat) (n : IntVec) : ℝ :=
  if n=0 then 0 else screened (Real.sqrt Real.pi) (linearImage R n)

def dualKernel (R : Mat) (n : IntVec) : ℝ :=
  (4*Real.pi)*reciprocalGreenTerm (Real.sqrt Real.pi) R n

def positiveSeries (R : Mat) : ℝ :=
  (∑' n : IntVec, shortKernel R n) + (∑' n : IntVec, dualKernel R n)

theorem shortKernel_nonnegative (R : Mat) (n : IntVec) : 0 ≤ shortKernel R n := by
  unfold shortKernel
  split_ifs
  · exact le_rfl
  · unfold screened
    change 0 ≤ BccSharp.Gaussian.erfcIntegral _ / _
    exact div_nonneg (BccSharp.Ewald.erfc_nonneg _) (Real.sqrt_nonneg _)

theorem dualKernel_nonnegative (R : Mat) (n : IntVec) : 0 ≤ dualKernel R n := by
  unfold dualKernel reciprocalGreenTerm
  split_ifs
  · positivity
  · exact mul_nonneg (by positivity) (div_nonneg (Real.exp_pos _).le (sq_nonnegative _))

theorem shortKernel_summable (R : Mat) (hR : R.det ≠ 0) : Summable (shortKernel R) := by
  have h := screened_lattice_summable (Real.sqrt Real.pi) (Real.sqrt_pos.mpr Real.pi_pos) R hR 0
  simp only [zero_add] at h
  apply h.summable_of_eq_zero_or_self
  intro n
  by_cases hn : n=0 <;> simp [shortKernel,hn]

theorem dualKernel_summable (R : Mat) (hR : R.det ≠ 0) : Summable (dualKernel R) :=
  (reciprocal_lattice_summable (Real.sqrt Real.pi) (Real.sqrt_pos.mpr Real.pi_pos) R hR).mul_left _

theorem screened_sqrtpi_to_kernel (v : Vec) (hv : v ≠ 0) :
    screened (Real.sqrt Real.pi) v = gKernel (1/2) (Real.pi*sq v) := by
  rw [← screened_series_term v hv,seriesScreen,screened_scale _ ac ac_positive]
  field_simp [ac_positive.ne']

theorem shortKernel_eq (R : Mat) (hR : R.det ≠ 0) (n : IntVec) (hn : n ≠ 0) :
    shortKernel R n = gKernel (1/2) (Real.pi*sq (linearImage R n)) := by
  have hz : linearImage R n ≠ 0 := by
    intro h
    apply hn
    apply (periodIndices R hR).injective
    apply Subtype.ext
    change linearImage R n = linearImage R 0
    rw [h, linearImage, castVec_zero, Matrix.mulVec_zero]
  simpa [shortKernel,hn] using screened_sqrtpi_to_kernel _ hz

theorem dualKernel_eq (R : Mat) (hR : R.det ≠ 0) (n : IntVec) (hn : n ≠ 0) :
    dualKernel R n = gKernel 1 (Real.pi*sq (cycleFrequency R n)) := by
  have hu : cycleFrequency R n ≠ 0 := fun eq =>
    hn (cycleFrequency_injective R hR (eq.trans (cycleFrequency_zero R).symm))
  have hq : 0 < sq (cycleFrequency R n) :=
    lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hu))
  rw [dualKernel, reciprocal_cycle _ R hR n hn, Real.sq_sqrt Real.pi_pos.le,
    gKernel_one (mul_pos Real.pi_pos hq)]
  have he : Real.pi^2*sq (cycleFrequency R n)/Real.pi = Real.pi*sq (cycleFrequency R n) := by
    field_simp [Real.pi_pos.ne']
  rw [he]
  ring

theorem positiveSeries_finite_lower (R : Mat) (hR : R.det ≠ 0) (f : Finset IntVec) :
    (∑ n ∈ f, (shortKernel R n+dualKernel R n)) ≤ positiveSeries R := by
  rw [Finset.sum_add_distrib]
  exact add_le_add
    ((shortKernel_summable R hR).sum_le_tsum f (fun n _ => shortKernel_nonnegative R n))
    ((dualKernel_summable R hR).sum_le_tsum f (fun n _ => dualKernel_nonnegative R n))

theorem unitVolumeRegularSelf_eq (R : Mat) (hv : volumeOf R=1) :
    ewaldRegularSelf (Real.sqrt Real.pi) R = positiveSeries R-3 := by
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold ewaldRegularSelf positiveSeries shortKernel dualKernel greenBackground
  rw [tsum_mul_left,hv,div_one,one_mul,Real.sq_sqrt Real.pi_pos.le,div_self Real.pi_pos.ne']
  field_simp [hs] <;> ring

theorem normalizedRegularSelf_eq (R : Mat) (hR : R.det=1) :
    ewaldRegularSelf (Real.sqrt Real.pi) R = positiveSeries R-3 :=
  unitVolumeRegularSelf_eq R (by simp [volumeOf,hR])

theorem oneSiteEnergy_from_unitVolume (R : Mat) (hR : volumeOf R=1) :
    oneSiteEnergy (Constants.fccLength⁻¹ • R) = (positiveSeries R-3)/(2*bravaisScale) := by
  have hd : R.det≠0 := by intro h; simp [volumeOf,h] at hR
  have hs : ac • (Constants.fccLength⁻¹ • R) = bravaisScale • R := by
    unfold bravaisScale
    rw [smul_smul,div_eq_mul_inv]
  have hPhys : (bravaisScale • R).det ≠ 0 := by
    rw [Matrix.det_smul,Fintype.card_fin]
    exact mul_ne_zero (pow_pos bravaisScale_positive _).ne' hd
  have hK : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  have hi := ewaldRegularSelf_screening_independent seriesScreen
    (Real.sqrt Real.pi/bravaisScale) (bravaisScale • R) hPhys hK
    (div_pos (Real.sqrt_pos.mpr Real.pi_pos) bravaisScale_positive)
  rw [oneSite_energy_is_self,hs,hi,regularSelf_scale _ _ bravaisScale_positive R hd,unitVolumeRegularSelf_eq R hR]
  ring

theorem oneSiteEnergy_from_normalized (R : Mat) (hR : R.det=1) :
    oneSiteEnergy (Constants.fccLength⁻¹ • R) = (positiveSeries R-3)/(2*bravaisScale) :=
  oneSiteEnergy_from_unitVolume R (by simp [volumeOf,hR])

theorem chartEnergy_eq (p : Point) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    oneSiteEnergy (primitiveChart p) = (positiveSeries (normalizedChart p)-3)/(2*bravaisScale) :=
  oneSiteEnergy_from_normalized _ (normalizedChart_det p h0 h1)

def HfccUpper : ℚ := 3+2*1611991954016469/10^15 * Constants.fccBracket.hi

theorem fcc_H_upper : 3+2*bravaisScale*energy fcc ≤ (HfccUpper : ℝ) := by
  have hq : (1611991954016469/10^15 : ℝ) ≤ bravaisScale := by
    have hcube : (1611991954016469/10^15 : ℝ)^3 ≤ bravaisScale^3 := by
      rw [bravaisScale_cube]
      linarith [Real.pi_gt_d20]
    exact le_of_pow_le_pow_left₀ (by norm_num) bravaisScale_positive.le hcube
  have hb := (Constants.reference_bounds .fcc).2
  have hneg : (Constants.fccBracket.hi : ℝ) ≤ 0 := by norm_num [Constants.fccBracket]
  have he : 2*bravaisScale*energy fcc ≤ 2*bravaisScale*(Constants.fccBracket.hi : ℝ) :=
    mul_le_mul_of_nonneg_left hb (mul_nonneg zero_le_two bravaisScale_positive.le)
  have h' := mul_le_mul_of_nonpos_right (show (2 : ℝ)*(1611991954016469/10^15) ≤ 2*bravaisScale by linarith) hneg
  unfold HfccUpper
  push_cast
  linarith

theorem unitVolume_above_fcc_of_series (R : Mat) (hR : volumeOf R=1)
    (h : (HfccUpper : ℝ) < positiveSeries R) : Sharp (Constants.fccLength⁻¹ • R) := by
  apply sharp_of_above_fcc _ Constants.reference_gap_checked.2
  rw [oneSiteEnergy_from_unitVolume R hR]
  apply (lt_div_iff₀ (mul_pos two_pos bravaisScale_positive : (0 : ℝ) < 2*bravaisScale)).mpr
  linarith [fcc_H_upper]

theorem normalized_above_fcc_of_series (R : Mat) (hR : R.det=1)
    (h : (HfccUpper : ℝ) < positiveSeries R) : Sharp (Constants.fccLength⁻¹ • R) :=
  unitVolume_above_fcc_of_series R (by simp [volumeOf,hR]) h

theorem chart_above_fcc_of_series (p : Point) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0)
    (h : (HfccUpper : ℝ) < positiveSeries (normalizedChart p)) : Sharp (primitiveChart p) :=
  normalized_above_fcc_of_series _ (normalizedChart_det p h0 h1) h

end BccSharp.Coulomb.BravaisCover
