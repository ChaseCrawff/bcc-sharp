module

public import BccSharp.Analysis.Erfc
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Taylor enclosures for removable exponential quotients. The order-d quotient
is defined at zero by its limit. Bounds are uniform through zero and therefore
can be used for the regular Ewald matrix at Gamma. -/

@[expose] public section
namespace BccSharp.DividedExp

open Complex

noncomputable def taylor (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, z ^ k / (k.factorial : ℂ)

noncomputable def shifted (d n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, z ^ k / ((d + k).factorial : ℂ)

noncomputable def value (d : ℕ) (z : ℂ) : ℂ :=
  if z = 0 then 1 / (d.factorial : ℂ) else (exp z - taylor d z) / z ^ d

theorem taylor_split (d n : ℕ) (z : ℂ) :
    taylor (d + n) z = taylor d z + z ^ d * shifted d n z := by
  unfold taylor shifted
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_add]
  ring

theorem shifted_zero (d n : ℕ) (hn : 0 < n) :
    shifted d n 0 = 1 / (d.factorial : ℂ) := by
  unfold shifted
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · simp [hn]

/-- Finite remainder with a guard that can be checked in rational arithmetic.
There is no division by the magnitude of the argument in the final bound. -/
theorem remainder (d n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : ‖z‖ / (d + n + 1 : ℕ) ≤ 1 / 2) :
    ‖value d z - shifted d n z‖ ≤ 2 * ‖z‖ ^ n / ((d + n).factorial : ℝ) := by
  by_cases hzero : z = 0
  · simp [hzero, value, shifted_zero d n hn, zero_pow (Nat.ne_of_gt hn)]
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have heq : value d z - shifted d n z = (exp z - taylor (d + n) z) / z ^ d := by
    rw [value, ite_eq_right hzero, taylor_split]
    field_simp
    ring
  rw [heq, norm_div, norm_pow]
  have h := Complex.exp_bound' (x := z) (n := d + n) (by simpa using hz)
  calc
    _ ≤ (‖z‖ ^ (d + n) / ((d + n).factorial : ℝ) * 2) / ‖z‖ ^ d :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by rw [pow_add]; field_simp

/-- The ordinary first divided exponential, including its value at zero. -/
theorem first_identity (z : ℂ) : z * value 1 z = exp z - 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [value, hz, taylor]
    field_simp

/-- The second divided exponential removes both constant and linear terms. -/
theorem second_identity (z : ℂ) : z ^ 2 * value 2 z = exp z - 1 - z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [value, hz, taylor, Finset.sum_range_succ]
    field_simp
    ring


/-- Real and imaginary components inherit the complex remainder unchanged. -/
theorem re_remainder (d n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : ‖z‖ / (d + n + 1 : ℕ) ≤ 1 / 2) :
    |(value d z).re - (shifted d n z).re| ≤
      2 * ‖z‖ ^ n / ((d + n).factorial : ℝ) := by
  exact (Complex.abs_re_le_norm (value d z - shifted d n z)).trans (remainder d n hn z hz)

theorem im_remainder (d n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : ‖z‖ / (d + n + 1 : ℕ) ≤ 1 / 2) :
    |(value d z).im - (shifted d n z).im| ≤
      2 * ‖z‖ ^ n / ((d + n).factorial : ℝ) := by
  exact (Complex.abs_im_le_norm (value d z - shifted d n z)).trans (remainder d n hn z hz)

noncomputable def exprel (x : ℝ) : ℝ := (value 1 (x : ℂ)).re
noncomputable def sinc (x : ℝ) : ℝ := (value 1 ((x : ℂ) * I)).re
noncomputable def cosc (x : ℝ) : ℝ := (value 2 ((x : ℂ) * I)).re
noncomputable def sinhc (x : ℝ) : ℝ := (exprel x + exprel (-x)) / 2
noncomputable def coshc (x : ℝ) : ℝ := ((value 2 (x : ℂ)).re + (value 2 (-x : ℂ)).re) / 2

@[simp] theorem exprel_zero : exprel 0 = 1 := by simp [exprel, value]
@[simp] theorem sinc_zero : sinc 0 = 1 := by simp [sinc, value]
@[simp] theorem cosc_zero : cosc 0 = 1 / 2 := by norm_num [cosc, value]
@[simp] theorem sinhc_zero : sinhc 0 = 1 := by simp [sinhc]
@[simp] theorem coshc_zero : coshc 0 = 1 / 2 := by norm_num [coshc, value]

theorem exprel_identity (x : ℝ) : x * exprel x = Real.exp x - 1 := by
  have h := congrArg Complex.re (first_identity (x : ℂ))
  simpa [exprel, Complex.exp_re] using h

theorem sinc_identity (x : ℝ) : x * sinc x = Real.sin x := by
  have h := congrArg Complex.im (first_identity ((x : ℂ) * I))
  simpa [sinc, Complex.mul_im, Complex.exp_ofReal_mul_I_im] using h

theorem cosc_identity (x : ℝ) : x ^ 2 * cosc x = 1 - Real.cos x := by
  have h := congrArg Complex.re (second_identity ((x : ℂ) * I))
  simp [cosc, pow_two, Complex.mul_re] at h ⊢
  linarith

theorem sinhc_identity (x : ℝ) : x * sinhc x = Real.sinh x := by
  have h1 := exprel_identity x
  have h2 := exprel_identity (-x)
  rw [sinhc, Real.sinh_eq]
  nlinarith

theorem coshc_identity (x : ℝ) : x ^ 2 * coshc x = Real.cosh x - 1 := by
  have h1 := congrArg Complex.re (second_identity (x : ℂ))
  have h2 := congrArg Complex.re (second_identity (-x : ℂ))
  simp [pow_two, Complex.mul_re, Complex.exp_re] at h1 h2
  rw [coshc, Real.cosh_eq]
  nlinarith


open scoped Topology
open Asymptotics Filter

/-- Consecutive divided exponentials satisfy an exact recurrence at every
complex argument, including zero. -/
theorem recurrence (d : ℕ) (z : ℂ) :
    z * value (d + 1) z = value d z - 1 / (d.factorial : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, value]
  · rw [value, value, ite_eq_right hz, ite_eq_right hz]
    simp only [taylor, Finset.sum_range_succ, pow_succ]
    field_simp
    ring

theorem hasDerivAt_zero (d : ℕ) :
    HasDerivAt (value d) (1 / ((d + 1).factorial : ℂ)) 0 := by
  have ho : (fun z : ℂ => value d z - 1 / (d.factorial : ℂ) -
      z * (1 / ((d + 1).factorial : ℂ))) =O[𝓝 0] fun z => z ^ 2 := by
    apply isBigO_iff.mpr
    refine ⟨2 / ((d + 2).factorial : ℝ), ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hg : ‖z‖ / (d + 2 + 1 : ℕ) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      push_cast
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have h := remainder d 2 (by decide) z hg
    have he : value d z - shifted d 2 z = value d z - 1 / (d.factorial : ℂ) -
        z * (1 / ((d + 1).factorial : ℂ)) := by
      simp [shifted, Finset.sum_range_succ]
      ring
    rw [he] at h
    simpa only [norm_pow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  rw [hasDerivAt_iff_isLittleO]
  simpa only [value, ite_true, sub_zero, smul_eq_mul] using
    ho.trans_isLittleO (isLittleO_pow_id (𝕜 := ℂ) (by decide : 1 < 2))

/-- A derivative formula without a singular denominator. It will also supply
second-derivative interval bounds by applying the same rule twice. -/
theorem hasDerivAt_value (d : ℕ) (z : ℂ) :
    HasDerivAt (value d) (value d z - (d : ℂ) * value (d + 1) z) z := by
  induction d with
  | zero =>
      have he : value 0 = Complex.exp := by
        funext w
        by_cases hw : w = 0 <;> simp [value, taylor, hw]
      simpa [he] using Complex.hasDerivAt_exp z
  | succ d ih =>
      by_cases hz : z = 0
      · subst z
        convert hasDerivAt_zero (d + 1) using 1
        simp only [value, ite_true]
        have hfac : ((d + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d + 1)
        have hd2 : ((d : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast (show d + 1 + 1 ≠ 0 by omega)
        rw [Nat.factorial_succ (d + 1)]
        push_cast
        field_simp
        ring
      · have hd := (ih.sub_const (1 / (d.factorial : ℂ))).div (hasDerivAt_id z) hz
        have heq : value (d + 1) =ᶠ[𝓝 z] fun w => (value d w - 1 / (d.factorial : ℂ)) / w := by
          filter_upwards [eventually_ne_nhds hz] with w hw
          exact (eq_div_iff hw).mpr (by simpa [mul_comm] using recurrence d w)
        have h := hd.congr_of_eventuallyEq heq
        convert h using 1
        have h0 := recurrence d z
        have h1 := recurrence (d + 1) z
        have hf : ((d + 1 : ℕ) : ℂ) / ((d + 1).factorial : ℂ) = 1 / (d.factorial : ℂ) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp
        simp only [id_eq, mul_one, Nat.cast_add, Nat.cast_one]
        apply (eq_div_iff (pow_ne_zero 2 hz)).mpr
        push_cast at hf
        linear_combination (z - 1) * h0 - (d + 1 : ℂ) * z * h1 + z * hf


theorem hasDerivAt_firstDerivative (d : ℕ) (z : ℂ) :
    HasDerivAt (fun w => value d w - (d : ℂ) * value (d + 1) w)
      (value d z - 2 * (d : ℂ) * value (d + 1) z +
        (d : ℂ) * (d + 1) * value (d + 2) z) z := by
  convert (hasDerivAt_value d z).sub ((hasDerivAt_value (d + 1) z).const_mul (d : ℂ)) using 1
  push_cast
  ring


@[fun_prop] theorem continuous_value (d : ℕ) : Continuous (value d) :=
  continuous_iff_continuousAt.mpr fun z => (hasDerivAt_value d z).continuousAt

@[fun_prop] theorem continuous_exprel : Continuous exprel :=
  Complex.continuous_re.comp ((continuous_value 1).comp Complex.continuous_ofReal)

@[fun_prop] theorem continuous_sinc : Continuous sinc :=
  Complex.continuous_re.comp ((continuous_value 1).comp (Complex.continuous_ofReal.mul continuous_const))

@[fun_prop] theorem continuous_cosc : Continuous cosc :=
  Complex.continuous_re.comp ((continuous_value 2).comp (Complex.continuous_ofReal.mul continuous_const))

@[fun_prop] theorem continuous_sinhc : Continuous sinhc := by
  unfold sinhc
  fun_prop

@[fun_prop] theorem continuous_coshc : Continuous coshc := by
  unfold coshc
  fun_prop

end BccSharp.DividedExp
