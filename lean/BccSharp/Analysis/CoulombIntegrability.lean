module

public import BccSharp.Analysis.CoulombLaplace
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute integrability for the Gaussian representation of screened
Coulomb, including its Fourier phase. This justifies the needed Fubini swap. -/
@[expose] public section
namespace BccSharp.CoulombLaplace
open Real Ewald Set MeasureTheory Filter
open scoped BigOperators

theorem gaussian_product (a : ℝ) (x : Vec) :
    exp (-a*Ewald.sq x) = ∏ i : Fin 3, exp (-a*(x i)^2) := by
  rw [← Real.exp_sum]
  simp only [Fin.sum_univ_three,Ewald.sq]
  congr 1
  ring

theorem real_gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (fun x : Vec => exp (-a*Ewald.sq x)) := by
  simp_rw [gaussian_product]
  exact Integrable.fintype_prod (fun _ : Fin 3 => integrable_exp_neg_mul_sq ha)

theorem gaussian_mass (a : ℝ) :
    (∫ x : Vec, exp (-a*Ewald.sq x)) = (sqrt (π/a))^3 := by
  simp_rw [gaussian_product]
  calc
    _ = (∫ x : ℝ, exp (-a*x^2))^3 :=
      integral_fintype_prod_volume_eq_pow (ι:=Fin 3) (fun x : ℝ => exp (-a*x^2))
    _ = _ := congrArg (fun y : ℝ => y^3) (integral_gaussian a)

theorem gaussian_mass_square {s : ℝ} (hs : 0 < s) :
    (∫ x : Vec, exp (-s^2*Ewald.sq x)) = (sqrt π)^3/s^3 := by
  rw [gaussian_mass,Real.sqrt_div pi_pos.le,Real.sqrt_sq_eq_abs,abs_of_pos hs,div_pow]

theorem gaussianPhase_norm (a : ℝ) (u x : Vec) :
    ‖gaussianPhase a u x‖=exp (-a*Ewald.sq x) := by
  simp [gaussianPhase,Complex.norm_exp]

theorem mass_integrable : IntegrableOn (fun s : ℝ => (sqrt π)^3/s^3) (Ioi (2 : ℝ)) := by
  have h := (integrableOn_Ioi_rpow_of_lt (a:=(-3 : ℝ)) (by norm_num) (c:=2) (by norm_num)).const_mul ((sqrt π)^3)
  have he (s : ℝ) : s^(-3 : ℝ)=(s^3)⁻¹ := by
    convert Real.rpow_neg_natCast s 3 using 1; norm_num
  simpa only [IntegrableOn,he,div_eq_mul_inv] using h

/-- The four-dimensional space/scale integrand is absolutely integrable,
so its Fourier transform may be evaluated by integrating Gaussians first. -/
theorem phase_joint_integrable (u : Vec) :
    Integrable (fun sx : ℝ×Vec => gaussianPhase (sx.1^2) u sx.2)
      ((volume.restrict (Ioi (2 : ℝ))).prod volume) := by
  have hm : Continuous (fun sx : ℝ×Vec => gaussianPhase (sx.1^2) u sx.2) := by
    unfold gaussianPhase Ewald.sq dot
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 2 < s at hs
    exact gaussian_integrable (by nlinarith : 0 < s^2) u
  · apply mass_integrable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 2 < s at hs
    simp_rw [gaussianPhase_norm]
    exact (gaussian_mass_square (by linarith : 0 < s)).symm

/-- Fubini applies to the actual screened-potential Fourier integrand. -/
theorem gaussian_fubini (u : Vec) :
    (∫ x : Vec, ∫ s in Ioi (2 : ℝ), gaussianPhase (s^2) u x) =
      ∫ s in Ioi (2 : ℝ), ∫ x : Vec, gaussianPhase (s^2) u x :=
  (integral_integral_swap (phase_joint_integrable u)).symm

end BccSharp.CoulombLaplace
