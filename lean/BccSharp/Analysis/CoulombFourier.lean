module

public import BccSharp.Analysis.CoulombIntegrability

/-! Fourier transform of the screened Coulomb potential from its absolutely
integrable Gaussian representation. -/
@[expose] public section
namespace BccSharp.CoulombLaplace
open Real Ewald Set MeasureTheory Filter
open scoped BigOperators Topology

theorem gaussian_zero_phase (a : ℝ) (x : Vec) :
    gaussianPhase a 0 x=(exp (-a*Ewald.sq x) : ℂ) := by
  simp [gaussianPhase,dot,Complex.ofReal_exp]

theorem gaussian_fourier_scalar {s : ℝ} (hs : 0 < s) (u : Vec) :
    (∫ x : Vec, gaussianPhase (s^2) u x) =
      (((sqrt π)^3/s^3*exp (-π^2*Ewald.sq u/s^2) : ℝ) : ℂ) := by
  have hz := gaussian_fourier (sq_pos_of_pos hs) (0 : Vec)
  simp_rw [gaussian_zero_phase] at hz
  rw [integral_complex_ofReal,gaussian_mass_square hs] at hz
  simp only [Ewald.sq,Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),add_zero,mul_zero,zero_div,
    Complex.ofReal_zero,neg_zero,Complex.exp_zero,mul_one] at hz
  rw [gaussian_fourier (sq_pos_of_pos hs) u,← hz]
  push_cast
  congr 1
  congr 1
  ring

theorem scale_derivative {A s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun t : ℝ => exp (-A/t^2)) (2*A/s^3*exp (-A/s^2)) s := by
  convert (((hasDerivAt_id s).pow 2).inv (pow_ne_zero 2 hs)).const_mul (-A) |>.exp using 1
  · funext t
    simp [div_eq_mul_inv]
  · simp only [Pi.inv_apply,Pi.pow_apply,id_eq]
    field_simp
    ring

theorem scale_tendsto (A : ℝ) : Tendsto (fun s : ℝ => exp (-A/s^2)) atTop (𝓝 1) := by
  have hi : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hp : Tendsto (fun s : ℝ => -A*(s⁻¹)^2) atTop (𝓝 0) := by
    simpa using (hi.pow 2).const_mul (-A)
  have h := (Real.continuous_exp.tendsto 0).comp hp
  simpa only [exp_zero,Function.comp_def,inv_pow,div_eq_mul_inv] using h

theorem scale_integral {A : ℝ} (hA : 0 < A) :
    (∫ s in Ioi (2 : ℝ), 2*A/s^3*exp (-A/s^2)) = 1-exp (-A/4) := by
  have hd (s : ℝ) (hs : s ∈ Ici (2 : ℝ)) :
      HasDerivAt (fun t : ℝ => exp (-A/t^2)) (2*A/s^3*exp (-A/s^2)) s := by
    apply scale_derivative
    have h : 2 ≤ s := hs
    linarith
  have hn (s : ℝ) (hs : s ∈ Ioi (2 : ℝ)) : 0 ≤ 2*A/s^3*exp (-A/s^2) := by
    have h : 2 < s := hs
    positivity
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd hn (scale_tendsto A)
  convert h using 1; norm_num

end BccSharp.CoulombLaplace
