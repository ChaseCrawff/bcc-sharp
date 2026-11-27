module

public import BccSharp.Analysis.CoulombFourier

/-! Fourier transform of the actual erfc-screened Coulomb potential, including
its zero mode. All integral exchanges use the proved absolute integrability. -/
@[expose] public section
namespace BccSharp.CoulombLaplace
open Real Ewald Set MeasureTheory Filter
open scoped BigOperators Topology

noncomputable def wave (u x : Vec) : ℂ :=
  Complex.exp (-((2*π*dot u x : ℝ) : ℂ)*Complex.I)

noncomputable def screenedPhase (u x : Vec) : ℂ :=
  (RealSpaceHessian.potential x : ℂ)*wave u x

theorem gaussianPhase_factor (a : ℝ) (u x : Vec) :
    gaussianPhase a u x = (exp (-a*Ewald.sq x) : ℂ)*wave u x := by
  simp only [gaussianPhase,wave,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  ring

theorem square_pos {x : Vec} (hx : x ≠ 0) : 0 < Ewald.sq x := by
  by_contra hn
  have h : x 0^2+x 1^2+x 2^2 ≤ 0 := le_of_not_gt hn
  have h0 : x 0=0 := by nlinarith [sq_nonneg (x 1),sq_nonneg (x 2)]
  have h1 : x 1=0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 2)]
  have h2 : x 2=0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  apply hx
  funext i
  fin_cases i <;> assumption

theorem screenedPhase_integral {x : Vec} (hx : x ≠ 0) (u : Vec) :
    screenedPhase u x = ((2/sqrt π : ℝ) : ℂ)*
      ∫ s in Ioi (2 : ℝ), gaussianPhase (s^2) u x := by
  simp_rw [gaussianPhase_factor]
  rw [integral_mul_const,integral_complex_ofReal]
  rw [screenedPhase,potential_integral (square_pos hx)]
  push_cast
  ring

theorem screenedPhase_integrable (u : Vec) : Integrable (screenedPhase u) := by
  apply ((phase_joint_integrable u).integral_prod_right.const_mul
    ((2/sqrt π : ℝ) : ℂ)).congr
  filter_upwards [volume.ae_ne (0 : Vec)] with x hx
  exact (screenedPhase_integral hx u).symm

theorem screened_transform_gaussian (u : Vec) :
    (∫ x : Vec, screenedPhase u x) = ((2/sqrt π : ℝ) : ℂ)*
      ∫ s in Ioi (2 : ℝ), ∫ x : Vec, gaussianPhase (s^2) u x := by
  calc
    _ = ∫ x : Vec, ((2/sqrt π : ℝ) : ℂ)*∫ s in Ioi (2 : ℝ), gaussianPhase (s^2) u x := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (0 : Vec)] with x hx
      exact screenedPhase_integral hx u
    _ = _ := by rw [integral_const_mul,gaussian_fubini]

theorem screened_transform_scalar (u : Vec) :
    (∫ x : Vec, screenedPhase u x) =
      (((2/sqrt π)*∫ s in Ioi (2 : ℝ), (sqrt π)^3/s^3*exp (-π^2*Ewald.sq u/s^2) : ℝ) : ℂ) := by
  rw [screened_transform_gaussian]
  have he : (∫ s in Ioi (2 : ℝ), ∫ x : Vec, gaussianPhase (s^2) u x) =
      ∫ s in Ioi (2 : ℝ), (((sqrt π)^3/s^3*exp (-π^2*Ewald.sq u/s^2) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 2 < s at hs
    exact gaussian_fourier_scalar (by linarith) u
  rw [he,integral_complex_ofReal,Complex.ofReal_mul]

theorem gaussian_scale_integral {A : ℝ} (hA : 0 < A) :
    (∫ s in Ioi (2 : ℝ), (sqrt π)^3/s^3*exp (-A/s^2)) =
      (sqrt π)^3/(2*A)*(1-exp (-A/4)) := by
  have he (s : ℝ) : (sqrt π)^3/s^3*exp (-A/s^2) =
      ((sqrt π)^3/(2*A))*(2*A/s^3*exp (-A/s^2)) := by
    field_simp
  simp_rw [he]
  rw [integral_const_mul,scale_integral hA]

/-- Nonzero Fourier modes of erfc(2|x|)/|x| in the 2π convention. -/
theorem screened_fourier {u : Vec} (hu : u ≠ 0) :
    (∫ x : Vec, screenedPhase u x) =
      ((1/(π*Ewald.sq u)*(1-exp (-Ewald.beta*Ewald.sq u)) : ℝ) : ℂ) := by
  have hs := square_pos hu
  have hr : sqrt π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  rw [screened_transform_scalar]
  rw [show -π^2*Ewald.sq u = -(π^2*Ewald.sq u) by ring]
  rw [gaussian_scale_integral (mul_pos (sq_pos_of_pos pi_pos) hs)]
  congr 1
  have he : -(π^2*Ewald.sq u)/4 = -Ewald.beta*Ewald.sq u := by
    unfold Ewald.beta
    ring
  rw [he]
  field_simp
  rw [Real.sq_sqrt pi_pos.le]

theorem inverse_cube_integral : (∫ s in Ioi (2 : ℝ), (s^3)⁻¹) = 1/8 := by
  have h := integral_Ioi_rpow_of_lt (a:=(-3 : ℝ)) (by norm_num) (c:=2) (by norm_num)
  have he (s : ℝ) : s^(-3 : ℝ)=(s^3)⁻¹ := by
    convert Real.rpow_neg_natCast s 3 using 1; norm_num
  simp only [he] at h
  norm_num [Real.rpow_neg_natCast] at h
  exact h

/-- The total mass of the screened Coulomb potential is π/4. -/
theorem screened_fourier_zero : (∫ x : Vec, screenedPhase 0 x) = ((π/4 : ℝ) : ℂ) := by
  rw [screened_transform_scalar]
  simp only [Ewald.sq,Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),add_zero,mul_zero,div_eq_mul_inv,zero_mul,exp_zero,mul_one]
  rw [integral_const_mul,inverse_cube_integral]
  congr 1
  have hr : sqrt π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  field_simp
  nlinarith [Real.sq_sqrt pi_pos.le]

end BccSharp.CoulombLaplace
