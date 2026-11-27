module

public import BccSharp.Analysis.Intervals
public import BccSharp.Analysis.Ewald

/-! Rational witnesses for finite special-function evaluation. Taylor bounds
and monotonicity are proved in ℝ; no external special-function implementation
or compiler-based decision oracle is trusted. -/

@[expose] public section
namespace BccSharp.SpecialFunctions

open Intervals Real

/-- Endpoint witnesses can be rounded outward without changing their meaning. -/
theorem contains_of_endpoints {x : ℝ} {l u : ℚ} (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (⟨(l + u) / 2, (u - l) / 2⟩ : Ball).Contains x := by
  simp only [Ball.Contains, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem contains_iff_endpoints (b : Ball) (x : ℝ) :
    b.Contains x ↔ (b.mid - b.rad : ℝ) ≤ x ∧ x ≤ (b.mid + b.rad : ℝ) := by
  unfold Ball.Contains
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- A direct use of mathlib's proved rational pi bounds. -/
theorem pi_enclosure :
    (⟨3141592653589793238465 / 10 ^ 21, 5 / 10 ^ 21⟩ : Ball).Contains Real.pi := by
  rw [contains_iff_endpoints]
  norm_num
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

def taylor (q : ℚ) (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, q ^ k / (k.factorial : ℚ)

def taylorError (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * n)

/-- Rational Taylor enclosure on [-1,1], with an explicit proved remainder. -/
theorem exp_taylor (q : ℚ) (n : ℕ) (hq : |q| ≤ 1) (hn : 0 < n) :
    (⟨taylor q n, taylorError q n⟩ : Ball).Contains (exp (q : ℝ)) := by
  have h := Real.exp_bound (by exact_mod_cast hq : |(q : ℝ)| ≤ 1) hn
  unfold Ball.Contains taylor taylorError
  push_cast
  convert h using 1; simp [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, mul_div_assoc]

/-- Range reduction for the exponential, using a positive integer k and
nonnegative rational endpoints for exp(q/k). -/
theorem exp_range_reduction {q l u : ℚ} {k n : ℕ} (hk : 0 < k)
    (hq : |q / k| ≤ 1) (hn : 0 < n)
    (hl0 : 0 ≤ l)
    (hl : l ≤ taylor (q / k) n - taylorError (q / k) n)
    (hu : taylor (q / k) n + taylorError (q / k) n ≤ u) :
    (l ^ k : ℚ) ≤ exp (q : ℝ) ∧ exp (q : ℝ) ≤ (u ^ k : ℚ) := by
  have h := (contains_iff_endpoints _ _).mp (exp_taylor (q / k) n hq hn)
  have hlr : (l : ℝ) ≤ exp ((q / k : ℚ) : ℝ) := by
    have hl' : (l : ℝ) ≤ (taylor (q / k) n : ℝ) - (taylorError (q / k) n : ℝ) := by
      exact_mod_cast hl
    exact hl'.trans h.1
  have hur : exp ((q / k : ℚ) : ℝ) ≤ (u : ℝ) := by
    exact h.2.trans (by exact_mod_cast hu)
  have he : exp ((q / k : ℚ) : ℝ) ^ k = exp (q : ℝ) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    field_simp
  constructor
  · rw [Rat.cast_pow, ← he]
    exact pow_le_pow_left₀ (by exact_mod_cast hl0) hlr k
  · rw [Rat.cast_pow, ← he]
    exact pow_le_pow_left₀ (exp_pos _).le hur k

/-- Monotonicity transfers two rational argument witnesses to a real input
interval. All finite-evaluation obligations here are exact rational inequalities. -/
theorem exp_enclosure {x : ℝ} {a b l u : ℚ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ))
    (hl : (l : ℝ) ≤ exp (a : ℝ)) (hu : exp (b : ℝ) ≤ (u : ℝ)) :
    (⟨(l + u) / 2, (u - l) / 2⟩ : Ball).Contains (exp x) :=
  contains_of_endpoints (hl.trans (exp_le_exp.mpr ha)) ((exp_le_exp.mpr hb).trans hu)

/-- A coarse erfc enclosure sufficient for some positivity certificates.
The exponential witness has its mathematical meaning in the hypothesis, and
can be discharged by exp_taylor / exp_range_reduction. -/
theorem erfc_enclosure {x : ℝ} {l p e : ℚ} (hl : 0 < l) (hp : 0 < p)
    (hx : (l : ℝ) ≤ x) (hpi : (p : ℝ) ≤ sqrt Real.pi)
    (he : exp (-(l : ℝ) ^ 2) ≤ (e : ℝ)) :
    (⟨e / (2 * l * p), e / (2 * l * p)⟩ : Ball).Contains (Gaussian.erfcIntegral x) := by
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hx0 : 0 < x := hlr.trans_le hx
  have he' : exp (-x ^ 2) ≤ (e : ℝ) := by
    apply le_trans (exp_le_exp.mpr ?_) he
    nlinarith
  have hden : (l : ℝ) * p ≤ x * sqrt Real.pi := mul_le_mul hx hpi hpr.le hx0.le
  have hu : Gaussian.erfcIntegral x ≤ (e / (l * p) : ℚ) := by
    apply (Gaussian.erfc_upper hx0).trans
    push_cast
    exact div_le_div₀ ((exp_pos _).le.trans he') he' (mul_pos hlr hpr) hden
  have hn := Ewald.erfc_nonneg x
  unfold Ball.Contains
  push_cast
  apply abs_le.mpr
  have heq : (e : ℝ) / ((l : ℝ) * p) = 2 * ((e : ℝ) / (2 * l * p)) := by ring
  push_cast at hu
  constructor <;> linarith

/-- A concrete exponential evaluation with no enclosure assumptions. -/
theorem exp_neg_three_enclosure :
    (⟨(4978 + 4980) / 200000, (4980 - 4978) / 200000⟩ : Ball).Contains (exp (-3)) := by
  have h := exp_range_reduction (q := -3) (k := 4) (n := 12)
    (l := 4723665 / 10000000) (u := 4723666 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [taylor, taylorError, Finset.sum_range_succ])
    (by norm_num [taylor, taylorError, Finset.sum_range_succ])
  rw [contains_iff_endpoints]
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The nearest-neighbour erfc value, bounded using its integral definition
and exact Taylor arithmetic. This does not rely on the Arb evaluator. -/
theorem erfc_sqrt_three :
    0 ≤ Gaussian.erfcIntegral (sqrt 3) ∧ Gaussian.erfcIntegral (sqrt 3) ≤ 17 / 1000 := by
  have hl : (1732 / 1000 : ℝ) ≤ sqrt 3 := by
    nlinarith [sqrt_nonneg (3 : ℝ), sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hp : (1772 / 1000 : ℝ) ≤ sqrt Real.pi := by
    nlinarith [sqrt_nonneg Real.pi, sq_sqrt pi_pos.le, Real.pi_gt_d4]
  have h := exp_range_reduction (q := -(1732 / 1000) ^ 2) (k := 4) (n := 12)
    (l := 0) (u := 4723874 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [taylor, taylorError, Finset.sum_range_succ])
    (by norm_num [taylor, taylorError, Finset.sum_range_succ])
  have he : exp (-(1732 / 1000 : ℝ) ^ 2) ≤ (4980 / 100000 : ℚ) := by
    norm_num at h ⊢
    linarith [h.2]
  have hc := erfc_enclosure (l := 1732 / 1000) (p := 1772 / 1000) (e := 4980 / 100000)
    (by norm_num) (by norm_num) (by norm_num at hl ⊢; exact hl)
    (by norm_num at hp ⊢; exact hp) (by norm_num at he ⊢; exact he)
  have hh := (contains_iff_endpoints _ _).mp hc
  norm_num at hh
  exact ⟨Ewald.erfc_nonneg _, by linarith [hh.2]⟩

end BccSharp.SpecialFunctions
