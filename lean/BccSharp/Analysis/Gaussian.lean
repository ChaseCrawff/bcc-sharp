module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp

/-! Gaussian tail estimates. These are bounds on ordinary
real integrals; they do not assume the correctness of numerical quadrature. -/

@[expose] public section

namespace BccSharp.Gaussian

open MeasureTheory Set Real

theorem tail {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    (∫ x : ℝ in Ioi R, exp (-a * x ^ 2)) ≤ exp (-a * R ^ 2) / (2 * a * R) := by
  have hc : -2 * a * R < 0 := by nlinarith [mul_pos ha hR]
  have hf : IntegrableOn (fun x : ℝ => exp (-a * x ^ 2)) (Ioi R) :=
    (integrable_exp_neg_mul_sq ha).integrableOn
  have hg := (integrableOn_exp_mul_Ioi hc R).const_mul (exp (a * R ^ 2))
  calc
    _ ≤ ∫ x : ℝ in Ioi R, exp (a * R ^ 2) * exp ((-2 * a * R) * x) := by
      apply setIntegral_mono_on hf hg measurableSet_Ioi
      intro x _
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg ha.le (sq_nonneg (x - R))]
    _ = exp (-a * R ^ 2) / (2 * a * R) := by
      rw [integral_const_mul, integral_exp_mul_Ioi hc]
      have he : exp (a * R ^ 2) * exp ((-2 * a * R) * R) = exp (-a * R ^ 2) := by
        rw [← exp_add]
        congr 1
        ring
      field_simp
      convert he using 1 <;> congr 1 <;> ring_nf

/-- The nonpositive-power branch of the Gaussian tail estimate, for any real exponent. -/
theorem weighted_tail_nonpos {a R k : ℝ} (ha : 0 < a) (hR : 0 < R) (hk : k ≤ 0) :
    (∫ x : ℝ in Ioi R, x ^ k * exp (-a * x ^ 2)) ≤
      R ^ k * exp (-a * R ^ 2) / (2 * a * R) := by
  have hg : IntegrableOn (fun x : ℝ => R ^ k * exp (-a * x ^ 2)) (Ioi R) :=
    (integrable_exp_neg_mul_sq ha).integrableOn.const_mul (R ^ k)
  have hpoint : ∀ x ∈ Ioi R, x ^ k * exp (-a * x ^ 2) ≤ R ^ k * exp (-a * x ^ 2) := by
    intro x hx
    exact mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos hR hx.le hk) (exp_pos _).le
  have hf : IntegrableOn (fun x : ℝ => x ^ k * exp (-a * x ^ 2)) (Ioi R) := by
    apply hg.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rpow_nonneg (hR.le.trans hx.le) k) (exp_pos _).le)]
    exact hpoint x hx
  calc
    _ ≤ ∫ x : ℝ in Ioi R, R ^ k * exp (-a * x ^ 2) :=
      setIntegral_mono_on hf hg measurableSet_Ioi hpoint
    _ = R ^ k * (∫ x : ℝ in Ioi R, exp (-a * x ^ 2)) := integral_const_mul _ _
    _ ≤ R ^ k * (exp (-a * R ^ 2) / (2 * a * R)) :=
      mul_le_mul_of_nonneg_left (tail ha hR) (rpow_nonneg hR.le k)
    _ = _ := by ring

/-- The positive-power branch of the Gaussian tail estimate. The denominator is proved
positive from the stated guard `k < 2 a R²`. -/
theorem weighted_tail_nonneg {a R k : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hk : 0 ≤ k) (hguard : k < 2 * a * R ^ 2) :
    (∫ x : ℝ in Ioi R, x ^ k * exp (-a * x ^ 2)) ≤
      R ^ k * exp (-a * R ^ 2) / (2 * a * R - k / R) := by
  let c := 2 * a * R - k / R
  have hc : 0 < c := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hR).mpr
    nlinarith
  have hf : IntegrableOn (fun x : ℝ => x ^ k * exp (-a * x ^ 2)) (Ioi R) :=
    (integrable_rpow_mul_exp_neg_mul_sq ha (by linarith : -1 < k)).integrableOn
  have hg := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) R).const_mul
    (R ^ k * exp (-a * R ^ 2 + c * R))
  calc
    _ ≤ ∫ x : ℝ in Ioi R, (R ^ k * exp (-a * R ^ 2 + c * R)) * exp (-c * x) := by
      apply setIntegral_mono_on hf hg measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hR.trans hx
      have hlog : log x - log R ≤ x / R - 1 := by
        rw [← log_div hx0.ne' hR.ne']
        exact log_le_sub_one_of_pos (div_pos hx0 hR)
      have hlog' : k * (log x - log R) ≤ k / R * (x - R) := by
        calc
          _ ≤ k * (x / R - 1) := mul_le_mul_of_nonneg_left hlog hk
          _ = _ := by field_simp
      simp only [rpow_def_of_pos hx0, rpow_def_of_pos hR, ← exp_add]
      apply exp_le_exp.mpr
      dsimp [c]
      have hd : k / R * R = k := div_mul_cancel₀ k hR.ne'
      nlinarith [mul_nonneg ha.le (sq_nonneg (x - R))]
    _ = R ^ k * exp (-a * R ^ 2) / c := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hc), neg_div_neg_eq,
        ← mul_div_assoc]
      congr 1
      rw [mul_assoc, ← exp_add]
      congr 2
      ring

/-- Integral definition of the complementary error function. Its connection to
the numerical erfc evaluator is still an enclosure obligation. -/
noncomputable def erfcIntegral (x : ℝ) : ℝ := 2 / sqrt Real.pi * ∫ y : ℝ in Ioi x, exp (-y ^ 2)

theorem erfc_upper {x : ℝ} (hx : 0 < x) :
    erfcIntegral x ≤ exp (-x ^ 2) / (x * sqrt Real.pi) := by
  have hs : 0 < sqrt Real.pi := sqrt_pos.mpr pi_pos
  have h := mul_le_mul_of_nonneg_left (tail (by norm_num : (0 : ℝ) < 1) hx)
    (show 0 ≤ 2 / sqrt Real.pi from by positivity)
  simp only [neg_mul, one_mul] at h
  unfold erfcIntegral
  calc
    _ ≤ 2 / sqrt Real.pi * (exp (-x ^ 2) / (2 * 1 * x)) := h
    _ = _ := by ring

end BccSharp.Gaussian
