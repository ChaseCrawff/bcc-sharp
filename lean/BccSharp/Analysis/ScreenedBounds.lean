module

public import BccSharp.Analysis.RealSpaceHessian
public import BccSharp.Analysis.GaussianSummability

/-! Uniform bounds for the screened potential and its derivatives away from
its singularity, suitable for differentiation of periodic lattice sums. -/
@[expose] public section
namespace BccSharp.Ewald
open Real LatticeTails

theorem radialHessian_quarter_bound {r t d : ℝ} (hr : 1 / 4 ≤ r) (ht : |t| ≤ 1)
    (hd : |d| ≤ 1) : |radialHessian r t d| ≤ 800 * exp (-(4 * r ^ 2)) := by
  have hr0 : 0 < r := by linarith
  have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hi2 : r⁻¹ ≤ 4 := by
    simpa using (one_div_le hr0 (by norm_num : (0 : ℝ) < 4)).mpr hr
  have hp : 0 < sqrt Real.pi := sqrt_pos.mpr pi_pos
  have hp1 : 1 ≤ sqrt Real.pi := by
    nlinarith [sq_sqrt pi_pos.le, Real.pi_gt_three]
  have hpi : 0 ≤ (sqrt Real.pi)⁻¹ := inv_nonneg.mpr hp.le
  have hpi1 : (sqrt Real.pi)⁻¹ ≤ 1 := by
    simpa using (one_div_le hp (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hp1)
  have he := (exp_pos (-(4 * r ^ 2))).le
  have hc : Gaussian.erfcIntegral (2 * r) ≤
      exp (-(4 * r ^ 2)) * r⁻¹ * (sqrt Real.pi)⁻¹ / 2 := by
    have h := Gaussian.erfc_upper (by positivity : 0 < 2 * r)
    have heq : -(2 * r) ^ 2 = -(4 * r ^ 2) := by ring
    rw [heq] at h
    convert h using 1; ring
  have hab : |3 * t - d| ≤ 4 := by
    calc
      _ ≤ |3 * t| + |d| := abs_sub _ _
      _ ≤ 3 * 1 + 1 := by rw [abs_mul]; norm_num; linarith
      _ = _ := by norm_num
  have hab' : |(12 * r⁻¹ ^ 2 + 32) * t - 4 * d * r⁻¹ ^ 2| ≤
      (12 * r⁻¹ ^ 2 + 32) * 1 + 4 * 1 * r⁻¹ ^ 2 := by
    calc
      _ ≤ |(12 * r⁻¹ ^ 2 + 32) * t| + |4 * d * r⁻¹ ^ 2| := abs_sub _ _
      _ = (12 * r⁻¹ ^ 2 + 32) * |t| + 4 * |d| * r⁻¹ ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 12 * r⁻¹ ^ 2 + 32),
          abs_of_nonneg (by positivity : 0 ≤ r⁻¹ ^ 2)]
        norm_num
      _ ≤ _ := by gcongr
  calc
    _ ≤ |Gaussian.erfcIntegral (2 * r) * r⁻¹ ^ 3 * (3 * t - d)| +
        |exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ *
          ((12 * r⁻¹ ^ 2 + 32) * t - 4 * d * r⁻¹ ^ 2)| := abs_add_le _ _
    _ = Gaussian.erfcIntegral (2 * r) * r⁻¹ ^ 3 * |3 * t - d| +
        exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ *
          |(12 * r⁻¹ ^ 2 + 32) * t - 4 * d * r⁻¹ ^ 2| := by
      simp only [abs_mul, abs_of_nonneg (erfc_nonneg _), abs_of_nonneg hi,
        abs_of_nonneg hpi, abs_of_nonneg he, abs_pow]
    _ ≤ (exp (-(4 * r ^ 2)) * r⁻¹ * (sqrt Real.pi)⁻¹ / 2) * r⁻¹ ^ 3 * 4 +
        exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ *
          ((12 * r⁻¹ ^ 2 + 32) * 1 + 4 * 1 * r⁻¹ ^ 2) := by
      gcongr
    _ = exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ * (2 * r⁻¹ ^ 4 + 16 * r⁻¹ ^ 2 + 32) := by ring
    _ ≤ exp (-(4 * r ^ 2)) * 1 * (2 * 4 ^ 4 + 16 * 4 ^ 2 + 32) := by gcongr
    _ = _ := by ring

end BccSharp.Ewald

namespace BccSharp.RealSpaceHessian
open Real Ewald RadialPotential

theorem component_radius (w : Vec) (i : Fin 3) : |w i| ≤ radius w := by
  have h := component_sq_le w i
  have hs := radius_square (sq_nonnegative w)
  have hr : 0 ≤ radius w := Real.sqrt_nonneg _
  nlinarith [sq_abs (w i)]

theorem erfc_quarter_bound {r : ℝ} (hr : 1/4 ≤ r) :
    Gaussian.erfcIntegral (2*r) ≤ 2*exp (-4*r^2) := by
  have hr0 : 0 < r := by linarith
  have hp : 1 ≤ sqrt π := by nlinarith [sq_sqrt pi_pos.le,pi_gt_three,sqrt_nonneg π]
  have h := Gaussian.erfc_upper (by positivity : 0 < 2*r)
  rw [show -(2*r)^2 = -4*r^2 by ring] at h
  apply h.trans
  apply (div_le_iff₀ (by positivity : 0 < 2*r*sqrt π)).2
  have he := exp_pos (-4*r^2)
  have hb : 1/2 ≤ 2*r*sqrt π := by
    calc
      (1/2 : ℝ) ≤ 2*r := by linarith
      _ ≤ 2*r*sqrt π := le_mul_of_one_le_right (by positivity) hp
  nlinarith [mul_le_mul_of_nonneg_left hb he.le]

theorem potential_bound {w : Vec} (hw : 1/4 ≤ radius w) :
    |potential w| ≤ 8*exp (-4*Ewald.sq w) := by
  have hr : 0 < radius w := by linarith
  have he := erfc_quarter_bound hw
  have hs := radius_square (sq_nonnegative w)
  rw [potential,screened,abs_div,abs_of_nonneg (erfc_nonneg _),abs_of_pos hr]
  apply (div_le_iff₀ hr).2
  rw [hs] at he
  have hp := exp_pos (-4*Ewald.sq w)
  nlinarith

theorem first_bound {r : ℝ} (hr : 1/4 ≤ r) :
    |first r| ≤ 48*exp (-4*r^2) := by
  have hr0 : 0 < r := by linarith
  have hi : 0 ≤ r⁻¹ := by positivity
  have hi4 : r⁻¹ ≤ 4 := by
    simpa using (one_div_le hr0 (by norm_num : (0 : ℝ) < 4)).mpr hr
  have hp : 1 ≤ sqrt π := by nlinarith [sq_sqrt pi_pos.le,pi_gt_three,sqrt_nonneg π]
  have hpi : 0 ≤ (sqrt π)⁻¹ := by positivity
  have hpi1 : (sqrt π)⁻¹ ≤ 1 := by simpa using inv_le_one_of_one_le₀ hp
  have he := (exp_pos (-4*r^2)).le
  calc
    |first r| = 4*exp (-4*r^2)*(sqrt π)⁻¹*r⁻¹ + Gaussian.erfcIntegral (2*r)*r⁻¹^2 := by
      unfold first
      rw [abs_of_nonpos (by
        have h1 : 0 ≤ 4*exp (-4*r^2)*(sqrt π)⁻¹*r⁻¹ := by positivity
        have h2 : 0 ≤ Gaussian.erfcIntegral (2*r)*r⁻¹^2 :=
          mul_nonneg (erfc_nonneg _) (sq_nonneg _)
        nlinarith)]
      ring
    _ ≤ 4*exp (-4*r^2)*1*4 + (2*exp (-4*r^2))*4^2 := by
      gcongr
      exact erfc_quarter_bound hr
    _ = _ := by ring

theorem gradient_bound {w : Vec} (hw : 1/4 ≤ radius w) (i : Fin 3) :
    |gradient w i| ≤ 48*exp (-4*Ewald.sq w) := by
  have hr : 0 < radius w := by linarith
  rw [gradient,abs_mul,abs_div,abs_of_pos hr]
  calc
    _ ≤ |first (radius w)| / radius w * radius w := by
      gcongr
      exact component_radius w i
    _ = |first (radius w)| := div_mul_cancel₀ _ hr.ne'
    _ ≤ _ := by simpa only [radius_square (sq_nonnegative w)] using first_bound hw

theorem hessian_bound {w : Vec} (hw : 1/4 ≤ radius w) (i j : Fin 3) :
    |hessian w i j| ≤ 800*exp (-4*Ewald.sq w) := by
  have hs : 0 < Ewald.sq w := by
    have hsq := radius_square (sq_nonnegative w)
    nlinarith
  rw [hessian_formula hs]
  have h := radialHessian_quarter_bound hw (abs_ratio w i j)
    (show |(if i=j then 1 else 0 : ℝ)| ≤ 1 by split_ifs <;> norm_num)
  simpa only [radius_square (sq_nonnegative w),neg_mul] using h

end BccSharp.RealSpaceHessian
