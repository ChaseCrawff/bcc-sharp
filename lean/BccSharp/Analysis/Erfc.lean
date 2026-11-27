module

public import BccSharp.Analysis.SpecialFunctions
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Finite, two-sided enclosures for the integral complementary error function.
All polynomial coefficients and remainder witnesses are rational; the bounds
come from the ordinary exponential series and interval integrals. -/

@[expose] public section
namespace BccSharp.Erfc

open Real MeasureTheory Set

/-- The general exponential remainder, with a guard on the order rather than
an artificial restriction of the argument to [-1,1]. -/
theorem exp_remainder (x : ℝ) (n : ℕ) (hx : |x| / (n + 1 : ℕ) ≤ 1 / 2) :
    |exp x - ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)| ≤
      |x| ^ n / (n.factorial : ℝ) * 2 := by
  have h := Complex.exp_bound' (x := (x : ℂ)) (n := n) (by simpa using hx)
  simpa only [← Complex.ofReal_exp, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

noncomputable def polynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k) / (k.factorial : ℝ)

noncomputable def primitive (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) /
    ((k.factorial : ℝ) * (2 * k + 1 : ℕ))

theorem gaussian_remainder (x : ℝ) (n : ℕ) (hx : x ^ 2 / (n + 1 : ℕ) ≤ 1 / 2) :
    |exp (-x ^ 2) - polynomial n x| ≤ x ^ (2 * n) / (n.factorial : ℝ) * 2 := by
  have h := exp_remainder (-x ^ 2) n (by simpa using hx)
  have he : (∑ k ∈ Finset.range n, (-x ^ 2) ^ k / (k.factorial : ℝ)) = polynomial n x := by
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_pow, ← pow_mul]
  rw [abs_neg, abs_of_nonneg (sq_nonneg x), ← pow_mul, he] at h
  exact h

theorem integral_polynomial (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, polynomial n t) = primitive n x := by
  unfold polynomial primitive
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    simp
    field_simp
  · intro k _
    exact (by fun_prop : Continuous (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k) /
      (k.factorial : ℝ))).intervalIntegrable _ _

theorem integral_remainder {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hguard : x ^ 2 / (n + 1 : ℕ) ≤ 1 / 2) :
    |(∫ t in (0 : ℝ)..x, exp (-t ^ 2)) - primitive n x| ≤
      2 * x ^ (2 * n + 1) / (n.factorial : ℝ) := by
  have hc : IntervalIntegrable (fun t : ℝ => exp (-t ^ 2)) volume 0 x :=
    (by fun_prop : Continuous (fun t : ℝ => exp (-t ^ 2))).intervalIntegrable _ _
  have hp : IntervalIntegrable (polynomial n) volume 0 x := by
    apply Continuous.intervalIntegrable
    unfold polynomial
    fun_prop
  rw [← integral_polynomial, ← intervalIntegral.integral_sub hc hp, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := x) (C := x ^ (2 * n) / (n.factorial : ℝ) * 2)
    (f := fun t : ℝ => exp (-t ^ 2) - polynomial n t) ?_
  · simpa [abs_of_nonneg hx, pow_succ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · intro t ht
    rw [uIoc_of_le hx] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have ht2 : t ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
    have hg : t ^ 2 / (n + 1 : ℕ) ≤ 1 / 2 :=
      (div_le_div_of_nonneg_right ht2 (by positivity)).trans hguard
    apply (gaussian_remainder t n hg).trans
    gcongr
    exact ht.2

theorem split_integral {x : ℝ} (hx : 0 ≤ x) :
    Gaussian.erfcIntegral x = 1 - 2 / sqrt Real.pi * (∫ t in (0 : ℝ)..x, exp (-t ^ 2)) := by
  have hi : IntegrableOn (fun t : ℝ => exp (-t ^ 2)) (Ioi 0) := by
    simpa using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn (s := Ioi 0)
  have h := intervalIntegral.integral_Ioi_sub_Ioi hi hx
  have hg : (∫ t : ℝ in Ioi 0, exp (-t ^ 2)) = sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi 1
  rw [hg] at h
  unfold Gaussian.erfcIntegral
  have hs : sqrt Real.pi ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
  rw [← h]
  field_simp
  ring

/-- Uniform finite series error for erfc, valid at zero as well. -/
theorem approximation {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hguard : x ^ 2 / (n + 1 : ℕ) ≤ 1 / 2) :
    |Gaussian.erfcIntegral x - (1 - 2 / sqrt Real.pi * primitive n x)| ≤
      4 * x ^ (2 * n + 1) / (sqrt Real.pi * (n.factorial : ℝ)) := by
  rw [split_integral hx]
  have h := mul_le_mul_of_nonneg_left (integral_remainder hx n hguard)
    (by positivity : 0 ≤ 2 / sqrt Real.pi)
  calc
    _ = |-(2 / sqrt Real.pi * ((∫ t in (0 : ℝ)..x, exp (-t ^ 2)) - primitive n x))| := by
      congr 1
      ring
    _ = (2 / sqrt Real.pi) * |(∫ t in (0 : ℝ)..x, exp (-t ^ 2)) - primitive n x| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (show 0 ≤ 2 / sqrt Real.pi by positivity)]
    _ ≤ (2 / sqrt Real.pi) * (2 * x ^ (2 * n + 1) / (n.factorial : ℝ)) := h
    _ = _ := by ring


/-- Rational part of the Gaussian primitive at sqrt(q). -/
def series (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (-q) ^ k / ((k.factorial : ℚ) * (2 * k + 1 : ℕ))

theorem primitive_sqrt {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
    primitive n (sqrt (q : ℝ)) = sqrt (q : ℝ) * (series q n : ℝ) := by
  have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq
  unfold primitive series
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ, pow_mul, sq_sqrt hq', neg_pow]
  ring

theorem sqrt_remainder {q : ℚ} (hq : 0 ≤ q) (n : ℕ)
    (hguard : q / (n + 1 : ℕ) ≤ 1 / 2) :
    |Gaussian.erfcIntegral (sqrt (q : ℝ)) -
      (1 - 2 * sqrt (q : ℝ) / sqrt Real.pi * (series q n : ℝ))| ≤
      4 * sqrt (q : ℝ) * (q : ℝ) ^ n / (sqrt Real.pi * (n.factorial : ℝ)) := by
  have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq
  have hg : (q : ℝ) / (n + 1 : ℕ) ≤ 1 / 2 := by
    have hh : ((q / (n + 1 : ℕ) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hguard
    simpa using hh
  have h := approximation (sqrt_nonneg (q : ℝ)) n (by rwa [sq_sqrt hq'])
  rw [primitive_sqrt hq, pow_succ, pow_mul, sq_sqrt hq'] at h
  convert h using 1 <;> ring_nf

open Intervals

/-- An outward rounding rule, reused by generated finite witnesses. -/
theorem widen {b c : Ball} {x : ℝ} (hx : b.Contains x)
    (h : |b.mid - c.mid| + b.rad ≤ c.rad) : c.Contains x := by
  have h' : |(b.mid : ℝ) - c.mid| + b.rad ≤ c.rad := by
    have hh : (((|b.mid - c.mid| + b.rad) : ℚ) : ℝ) ≤ (c.rad : ℝ) := Rat.cast_le.mpr h
    simpa using hh
  unfold Ball.Contains at *
  calc
    |x - c.mid| = |(x - b.mid) + (b.mid - c.mid)| := by congr 1; ring
    _ ≤ |x - b.mid| + |(b.mid : ℝ) - c.mid| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Enlarge a ball by an exact error allowance for the represented quantity. -/
theorem perturb {b : Ball} {x y : ℝ} {e : ℚ} (hx : b.Contains x)
    (he : |y - x| ≤ (e : ℝ)) : (⟨b.mid, b.rad + e⟩ : Ball).Contains y := by
  unfold Ball.Contains at *
  push_cast
  calc
    |y - b.mid| = |(y - x) + (x - b.mid)| := by congr 1; ring
    _ ≤ |y - x| + |x - b.mid| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Sound finite erfc witness at sqrt(q). The two input balls enclose sqrt(q)
and 1/sqrt(pi), respectively; every other input is rational. -/
theorem enclosure {q e : ℚ} {n : ℕ} {s p : Ball}
    (hq : 0 ≤ q) (hguard : q / (n + 1 : ℕ) ≤ 1 / 2)
    (hs : s.Contains (sqrt (q : ℝ))) (hp : p.Contains (sqrt Real.pi)⁻¹)
    (he : 4 * (s.mid + s.rad) * (p.mid + p.rad) * q ^ n / (n.factorial : ℚ) ≤ e) :
    (let b := (Ball.exact 1).sub (((Ball.exact 2).mul s).mul p |>.mul (Ball.exact (series q n)))
     (⟨b.mid, b.rad + e⟩ : Ball)).Contains (Gaussian.erfcIntegral (sqrt (q : ℝ))) := by
  let b := (Ball.exact 1).sub (((Ball.exact 2).mul s).mul p |>.mul (Ball.exact (series q n)))
  have hb : b.Contains (1 - 2 * sqrt (q : ℝ) * (sqrt Real.pi)⁻¹ * (series q n : ℝ)) := by
    simpa only [b, Rat.cast_one, Rat.cast_ofNat] using Ball.contains_sub (Ball.contains_exact 1)
      (Ball.contains_mul (Ball.contains_mul (Ball.contains_mul (Ball.contains_exact 2) hs) hp)
        (Ball.contains_exact (series q n)))
  apply perturb hb
  have hs' := ((SpecialFunctions.contains_iff_endpoints _ _).mp hs).2
  have hp' := ((SpecialFunctions.contains_iff_endpoints _ _).mp hp).2
  have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq
  have hpi := inv_nonneg.mpr (sqrt_nonneg Real.pi)
  have herr := sqrt_remainder hq n hguard
  rw [div_eq_mul_inv (2 * sqrt (q : ℝ))] at herr
  apply herr.trans
  have he' : 4 * ((s.mid : ℝ) + s.rad) * ((p.mid : ℝ) + p.rad) * (q : ℝ) ^ n /
      (n.factorial : ℝ) ≤ (e : ℝ) := by
    have hh : (((4 * (s.mid + s.rad) * (p.mid + p.rad) * q ^ n / (n.factorial : ℚ)) : ℚ) : ℝ) ≤ (e : ℝ) := Rat.cast_le.mpr he
    simpa using hh
  apply le_trans _ he'
  rw [div_eq_mul_inv, mul_inv]
  calc
    _ = 4 * sqrt (q : ℝ) * (sqrt Real.pi)⁻¹ * (q : ℝ) ^ n / (n.factorial : ℝ) := by ring
    _ ≤ _ := by
      have hs0 : 0 ≤ (s.mid : ℝ) + s.rad := (sqrt_nonneg (q : ℝ)).trans hs'
      gcongr


/-- Fixed rational witnesses for sqrt(3) and 1/sqrt(pi). -/
def sqrtThree : Ball :=
  ⟨(173205080756887729352 / 10 ^ 20 + 173205080756887729353 / 10 ^ 20) / 2,
    (173205080756887729353 / 10 ^ 20 - 173205080756887729352 / 10 ^ 20) / 2⟩

def invSqrtPi : Ball :=
  ⟨(10 ^ 20 / 177245385090551602731 + 10 ^ 20 / 177245385090551602729) / 2,
    (10 ^ 20 / 177245385090551602729 - 10 ^ 20 / 177245385090551602731) / 2⟩

theorem sqrtThree_contains : sqrtThree.Contains (sqrt (3 : ℝ)) := by
  apply Ball.sqrt_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem invSqrtPi_contains : invSqrtPi.Contains (sqrt Real.pi)⁻¹ := by
  have hl : (177245385090551602729 / 10 ^ 20 : ℝ) ≤ sqrt Real.pi := by
    nlinarith [sqrt_nonneg Real.pi, sq_sqrt pi_pos.le, pi_gt_d20]
  have hu : sqrt Real.pi ≤ (177245385090551602731 / 10 ^ 20 : ℝ) := by
    nlinarith [sqrt_nonneg Real.pi, sq_sqrt pi_pos.le, pi_lt_d20]
  apply SpecialFunctions.contains_of_endpoints
  · have h := one_div_le_one_div_of_le (sqrt_pos.mpr pi_pos) hu
    norm_num at h ⊢
    exact h
  · have h := one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 177245385090551602729 / 10 ^ 20) hl
    norm_num at h ⊢
    exact h

/-- A two-sided enclosure of the nearest-neighbour value. Its proof checks the
finite Taylor polynomial and its integral remainder using rational arithmetic. -/
theorem sqrt_three_tight :
    (⟨1430587843542964 / 10 ^ 17, 1 / 10 ^ 17⟩ : Ball).Contains
      (Gaussian.erfcIntegral (sqrt 3)) := by
  have h := enclosure (q := 3) (n := 40) (e := 1 / 10 ^ 26)
    (by norm_num) (by norm_num) sqrtThree_contains invSqrtPi_contains
    (by norm_num [sqrtThree, invSqrtPi, Nat.factorial])
  apply widen (by simpa only [Rat.cast_ofNat] using h)
  norm_num [Ball.sub, Ball.add, Ball.neg, Ball.mul, Ball.exact,
    sqrtThree, invSqrtPi, series, Finset.sum_range_succ, Nat.factorial]

end BccSharp.Erfc
