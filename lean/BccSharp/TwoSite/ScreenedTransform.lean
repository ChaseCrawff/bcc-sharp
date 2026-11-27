import BccSharp.TwoSite.PhysicalScale
import BccSharp.Analysis.CoulombTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false

/-! Whole-space screened Fourier transform for arbitrary positive
screening. The fixed-screening Fourier integral is reused with dilation
and the determinant factor for three-dimensional Lebesgue measure. -/

noncomputable section
open MeasureTheory

namespace BccSharp.Coulomb
open BccSharp

def screenedPhaseAt (α : ℝ) (u x : Vec) : ℂ :=
  (screened α x : ℂ) * CoulombLaplace.wave u x

private theorem square_agrees (x : Vec) : sq x = Ewald.sq x := by
  simp [sq, Ewald.sq, Fin.sum_univ_three]

private def realDilation (t : ℝ) (ht : t ≠ 0) : Vec ≃ᵐ Vec where
  toFun x := t • x
  invFun x := t⁻¹ • x
  left_inv x := by
    show t⁻¹ • t • x = x
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  right_inv x := by
    show t • t⁻¹ • x = x
    rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  measurable_toFun := (continuous_const_smul t).measurable
  measurable_invFun := (continuous_const_smul t⁻¹).measurable

private theorem dilation_measure (t : ℝ) (ht : 0 < t) :
    Measure.map (realDilation t ht.ne') (volume : Measure Vec) =
      ENNReal.ofReal ((t^3)⁻¹) • volume := by
  change Measure.map (fun x : Vec => t • x) (volume : Measure Vec) = _
  rw [Measure.map_addHaar_smul volume ht.ne']
  rw [Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos ht 3))]

private theorem screenedPhase_dilation (α : ℝ) (ha : 0 < α) (u x : Vec) :
    screenedPhaseAt α u x = (α/2 : ℝ) •
      CoulombLaplace.screenedPhase ((α/2 : ℝ)⁻¹ • u) ((α/2 : ℝ) • x) := by
  let t := α/2
  have ht : 0 < t := by dsimp [t]; positivity
  have hs := screened_scale α t ht x
  have htwo : α/t = 2 := by dsimp [t]; field_simp [ha.ne']
  rw [htwo] at hs
  have h := (eq_div_iff ht.ne').mp hs
  have he : screened α x = t*screened 2 (t • x) := by rw [mul_comm t, h]
  have hpot (v : Vec) : RealSpaceHessian.potential v = screened 2 v := by
    unfold RealSpaceHessian.potential RadialPotential.screened RealSpaceHessian.radius screened
    rw [square_agrees] <;> rfl
  have hdot : Ewald.dot (t⁻¹ • u) (t • x) = Ewald.dot u x := by
    change dot (t⁻¹ • u) (t • x) = dot u x
    rw [dot_right_smul, dot_left_smul, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  change screenedPhaseAt α u x = t • CoulombLaplace.screenedPhase (t⁻¹ • u) (t • x)
  unfold screenedPhaseAt CoulombLaplace.screenedPhase CoulombLaplace.wave
  rw [hpot, hdot, he, Complex.real_smul]
  push_cast
  ring

theorem screenedPhaseAt_integrable (α : ℝ) (ha : 0 < α) (u : Vec) :
    Integrable (screenedPhaseAt α u) := by
  let t := α/2
  have ht : 0 < t := by dsimp [t]; positivity
  let f := CoulombLaplace.screenedPhase (t⁻¹ • u)
  have hmap : Integrable f (Measure.map (realDilation t ht.ne') volume) := by
    rw [dilation_measure t ht]
    exact (CoulombLaplace.screenedPhase_integrable _).smul_measure ENNReal.ofReal_ne_top
  have h := (integrable_map_equiv (realDilation t ht.ne') f).mp hmap
  rw [show screenedPhaseAt α u = fun x => t • f (realDilation t ht.ne' x) from
    funext (screenedPhase_dilation α ha u)]
  exact h.smul t

theorem screenedPhaseAt_integral_dilation (α : ℝ) (ha : 0 < α) (u : Vec) :
    (∫ x : Vec, screenedPhaseAt α u x) =
      (((α/2 : ℝ)^2)⁻¹ : ℝ) • ∫ x : Vec, CoulombLaplace.screenedPhase ((α/2 : ℝ)⁻¹ • u) x := by
  let t := α/2
  have ht : 0 < t := by dsimp [t]; positivity
  let f := CoulombLaplace.screenedPhase (t⁻¹ • u)
  calc
    _ = t • ∫ x : Vec, f (realDilation t ht.ne' x) := by
      rw [← integral_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall (screenedPhase_dilation α ha u))
    _ = _ := by
      rw [← integral_map_equiv, dilation_measure t ht, integral_smul_measure,
        ENNReal.toReal_ofReal (by positivity), smul_smul]
      change (t*(t^3)⁻¹) • (∫ x : Vec, f x) = ((t^2)⁻¹) • (∫ x : Vec, f x)
      rw [show t*(t^3)⁻¹ = (t^2)⁻¹ by field_simp [ht.ne'] <;> ring]

theorem screenedPhaseAt_fourier (α : ℝ) (ha : 0 < α) (u : Vec) (hu : u ≠ 0) :
    (∫ x : Vec, screenedPhaseAt α u x) =
      ((1/(Real.pi*sq u)*(1-Real.exp (-(Real.pi^2*sq u/α^2))) : ℝ) : ℂ) := by
  let t := α/2
  have ht : 0 < t := by dsimp [t]; positivity
  have hb : t⁻¹ • u ≠ 0 := smul_ne_zero (inv_ne_zero ht.ne') hu
  have hs : sq u ≠ 0 := fun h => hu ((sq_eq_zero_iff _).mp h)
  have h := CoulombLaplace.screened_fourier hb
  rw [← square_agrees] at h
  rw [screenedPhaseAt_integral_dilation α ha u]
  change ((t^2)⁻¹ : ℝ) • (∫ x : Vec, CoulombLaplace.screenedPhase (t⁻¹ • u) x) = _
  rw [h]
  change ((t^2)⁻¹ : ℝ) •
    ((1/(Real.pi*sq (t⁻¹ • u))*(1-Real.exp (-Ewald.beta*sq (t⁻¹ • u))) : ℝ) : ℂ) = _
  rw [sq_smul, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  have he : -Ewald.beta*((t⁻¹)^2*sq u) = -(Real.pi^2*sq u/α^2) := by
    unfold Ewald.beta t
    field_simp [ha.ne'] <;> ring
  rw [he]
  field_simp [ht.ne', Real.pi_pos.ne', hs] <;> ring

theorem screenedPhaseAt_mass (α : ℝ) (ha : 0 < α) :
    (∫ x : Vec, screenedPhaseAt α 0 x) = ((Real.pi/α^2 : ℝ) : ℂ) := by
  rw [screenedPhaseAt_integral_dilation α ha 0, smul_zero, CoulombLaplace.screened_fourier_zero,
    Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  field_simp [ha.ne'] <;> ring

end BccSharp.Coulomb
