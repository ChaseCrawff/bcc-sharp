import BccSharp.TwoSite.ReferenceCert
import BccSharp.TwoSite.PhysicalScale

set_option autoImplicit false

/-! Normalization of the Constants packet against the actual screened
regular self term on the primitive lattice. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

namespace Constants

def tripleEquiv : Triple ≃ IntVec where
  toFun := asVector
  invFun n := (n 0,n 1,n 2)
  left_inv z := by rcases z with ⟨a,b,c⟩; rfl
  right_inv n := by funext i; fin_cases i <;> rfl

theorem asVector_zero : asVector (0 : Triple) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem asVector_eq_zero_iff (z : Triple) : asVector z = 0 ↔ z = 0 := by
  constructor
  · intro h
    exact tripleEquiv.injective (h.trans asVector_zero.symm)
  · rintro rfl
    exact asVector_zero

theorem natural_volume_eq (ref : Reference) : volumeOf ref.naturalBasis = (ref.naturalVolume : ℝ) := by
  rw [volumeOf, naturalBasis_det]
  exact abs_of_nonneg (by cases ref <;> norm_num [Reference.naturalVolume])

theorem primitive_real_index (ref : Reference) (z : Triple) :
    ref.realTerm z = (1/2 : ℝ) *
      (if asVector z = 0 then 0 else screened (ref.alpha : ℝ) (linearImage ref.naturalBasis (asVector z))) := by
  have hzero : asVector z = 0 ↔ z = 0 := asVector_eq_zero_iff z
  unfold Reference.realTerm
  simp only [hzero]
  by_cases hz : z = 0
  · simp [hz]
  · simp only [if_neg hz]
    rw [screened, linearImage, sq_mulVec_gram, direct_quad_eq]
    unfold Reference.directValue Reference.realRadius
    rw [div_mul_eq_mul_div]
    ring

theorem primitive_dual_index (ref : Reference) (z : Triple) :
    ref.dualTerm z = (2 * Real.pi / volumeOf ref.naturalBasis) *
      reciprocalGreenTerm (ref.alpha : ℝ) ref.naturalBasis (asVector z) := by
  have hzero : asVector z = 0 ↔ z = 0 := asVector_eq_zero_iff z
  unfold Reference.dualTerm reciprocalGreenTerm
  simp only [hzero]
  by_cases hz : z = 0
  · simp [hz]
  · simp only [if_neg hz]
    rw [dualWave_sq_gram, gram_inverse_eq, reciprocal_quad_eq, natural_volume_eq]
    unfold Reference.reciprocalValue Reference.dualRadius
    have hExponent : (2*Real.pi)^2 * (ref.dualForm (asVector z) : ℝ) / (4*(ref.alpha : ℝ)^2) =
        Real.pi^2 * (ref.dualForm (asVector z) : ℝ) / (ref.alpha : ℝ)^2 := by ring
    rw [hExponent]
    have hv : (ref.naturalVolume : ℝ) ≠ 0 := by cases ref <;> norm_num [Reference.naturalVolume]
    by_cases hq : (ref.dualForm (asVector z) : ℝ) = 0
    · simp [hq]
    · field_simp [Real.pi_pos.ne', hv, hq] <;> ring

theorem primitiveWS_eq_regularSelf (ref : Reference) : ref.primitiveWS =
    ref.wsFactor * (ewaldRegularSelf (ref.alpha : ℝ) ref.naturalBasis / 2) := by
  have realSum : (∑' z, ref.realTerm z) = (1/2 : ℝ) *
      (∑' n : IntVec, if n = 0 then 0 else screened (ref.alpha : ℝ) (linearImage ref.naturalBasis n)) := by
    calc
      _ = ∑' z : Triple, (1/2 : ℝ) * (if asVector z = 0 then 0 else
          screened (ref.alpha : ℝ) (linearImage ref.naturalBasis (asVector z))) := tsum_congr (primitive_real_index ref)
      _ = _ := by
        rw [tsum_mul_left]
        congr 1
        exact tripleEquiv.tsum_eq (fun n : IntVec =>
          if n = 0 then 0 else screened (ref.alpha : ℝ) (linearImage ref.naturalBasis n))
  have dualSum : (∑' z, ref.dualTerm z) = (2*Real.pi/volumeOf ref.naturalBasis) *
      (∑' n : IntVec, reciprocalGreenTerm (ref.alpha : ℝ) ref.naturalBasis n) := by
    calc
      _ = ∑' z : Triple, (2*Real.pi/volumeOf ref.naturalBasis) *
          reciprocalGreenTerm (ref.alpha : ℝ) ref.naturalBasis (asVector z) := tsum_congr (primitive_dual_index ref)
      _ = _ := by
        rw [tsum_mul_left]
        congr 1
        exact tripleEquiv.tsum_eq (fun n : IntVec => reciprocalGreenTerm (ref.alpha : ℝ) ref.naturalBasis n)
  unfold Reference.primitiveWS Reference.fullNatural ewaldRegularSelf greenBackground
  rw [realSum, dualSum, natural_volume_eq]
  ring

theorem primitive_bcc_physical : bccBracket.contains
    (Reference.wsFactor .bcc * (ewaldRegularSelf (Reference.alpha .bcc : ℝ) (Reference.naturalBasis .bcc) / 2)) := by
  rw [← primitiveWS_eq_regularSelf .bcc]
  exact bcc_primitive_enclosed

theorem primitive_fcc_physical : fccBracket.contains
    (Reference.wsFactor .fcc * (ewaldRegularSelf (Reference.alpha .fcc : ℝ) (Reference.naturalBasis .fcc) / 2)) := by
  rw [← primitiveWS_eq_regularSelf .fcc]
  exact fcc_primitive_enclosed

theorem wsFactor_positive (ref : Reference) : 0 < ref.wsFactor := by
  have hV : (0 : ℝ) < (ref.naturalVolume : ℝ) := by cases ref <;> norm_num [Reference.naturalVolume]
  unfold Reference.wsFactor
  positivity

theorem primitiveWS_eq_scaled_cell (ref : Reference) : ref.primitiveWS =
    greenPerParticle ((ref.alpha : ℝ) / (ref.wsFactor)⁻¹)
      ((ref.wsFactor)⁻¹ • ref.naturalBasis) (fun _ : Fin 1 => (0 : Vec)) := by
  have hS := wsFactor_positive ref
  have hV : ref.naturalBasis.det ≠ 0 := by rw [naturalBasis_det]; cases ref <;> norm_num [Reference.naturalVolume]
  have h := greenPerParticle_scale (ref.alpha : ℝ) (ref.wsFactor)⁻¹ (inv_pos.mpr hS)
    ref.naturalBasis hV (fun _ : Fin 1 => (0 : Vec))
  rw [primitiveWS_eq_regularSelf ref]
  rw [show (fun _ : Fin 1 => (0 : Vec)) = fun _ : Fin 1 => (ref.wsFactor)⁻¹ • (0 : Vec) by simp]
  rw [h]
  simp [greenPerParticle, greenCellEnergy, Fin.sum_univ_one, div_inv_eq_mul]
  ring

end Constants
end BccSharp.Coulomb
