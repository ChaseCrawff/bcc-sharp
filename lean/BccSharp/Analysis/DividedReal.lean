module

public import BccSharp.Analysis.DividedExp
public import Mathlib.Analysis.Complex.RealDeriv

/-! Actual real first and second derivatives for normalized analytic
primitives. Complex slope and prefactor include exponential, trigonometric,
and removable-quotient primitives in a single proved rule. -/

@[expose] public section
namespace BccSharp.DividedExp

noncomputable def realLine (d : ℕ) (a b : ℂ) (x : ℝ) : ℝ := (b * value d (a * x)).re
noncomputable def realLineFirst (d : ℕ) (a b : ℂ) (x : ℝ) : ℝ :=
  (b * a * (value d (a * x) - (d : ℂ) * value (d + 1) (a * x))).re
noncomputable def realLineSecond (d : ℕ) (a b : ℂ) (x : ℝ) : ℝ :=
  (b * a ^ 2 * (value d (a * x) - 2 * (d : ℂ) * value (d + 1) (a * x) +
    (d : ℂ) * (d + 1) * value (d + 2) (a * x))).re

theorem realLine_hasDerivAt (d : ℕ) (a b : ℂ) (x : ℝ) :
    HasDerivAt (realLine d a b) (realLineFirst d a b x) x := by
  have h := (((hasDerivAt_value d (a * x)).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_mul a)).const_mul b).real_of_complex
  convert h using 1
  · rfl
  · unfold realLineFirst
    congr 1
    ring

theorem realLineFirst_hasDerivAt (d : ℕ) (a b : ℂ) (x : ℝ) :
    HasDerivAt (realLineFirst d a b) (realLineSecond d a b x) x := by
  have h := (((hasDerivAt_firstDerivative d (a * x)).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_mul a)).const_mul (b * a)).real_of_complex
  convert h using 1
  · rfl
  · unfold realLineSecond
    congr 1
    ring

theorem value_zero_order (z : ℂ) : value 0 z = Complex.exp z := by
  by_cases hz : z = 0 <;> simp [value, taylor, hz]

theorem realLine_exprel (x : ℝ) : realLine 1 1 1 x = exprel x := by simp [realLine, exprel]

theorem realLine_sinc (x : ℝ) : realLine 1 Complex.I 1 x = sinc x := by
  simp [realLine, sinc, mul_comm Complex.I]

theorem realLine_cosc (x : ℝ) : realLine 2 Complex.I 1 x = cosc x := by
  simp [realLine, cosc, mul_comm Complex.I]

theorem realLine_exp (x : ℝ) : realLine 0 1 1 x = Real.exp x := by
  simp [realLine, value_zero_order, Complex.exp_ofReal_re]

theorem realLine_cos (x : ℝ) : realLine 0 Complex.I 1 x = Real.cos x := by
  simp [realLine, value_zero_order, mul_comm Complex.I]

theorem realLine_sin (x : ℝ) : realLine 0 Complex.I (-Complex.I) x = Real.sin x := by
  simp [realLine, value_zero_order, Complex.mul_re, mul_comm Complex.I]

end BccSharp.DividedExp
