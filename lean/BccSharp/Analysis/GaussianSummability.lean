module

public import BccSharp.Analysis.WeightedTails

/-! Absolute convergence for Gaussians at every positive scale. The bound is
uniform over all integer triples and therefore also applies to sublattices. -/
@[expose] public section
namespace BccSharp.LatticeTails
open Real

/-- Completing the square supplies a geometric majorant at any positive scale. -/
theorem scaled_gaussian_le_weight {a : ℝ} (ha : 0 < a) (z : Triple) :
    exp (-a * normSq z) ≤ exp (3/(4*a)) * weight z := by
  have hs (n : ℕ) : (n : ℝ) - a*(n : ℝ)^2 ≤ 1/(4*a) := by
    have h := sq_nonneg (2*a*(n : ℝ)-1)
    apply (le_div_iff₀ (by positivity : 0 < 4*a)).2
    nlinarith
  have h := hs z.1.natAbs
  have h' := hs z.2.1.natAbs
  have h'' := hs z.2.2.natAbs
  have hb : -a*normSq z ≤ 3/(4*a) - (length z : ℝ) := by
    rw [normSq_eq_square]
    simp only [square,length,Nat.cast_add,Nat.cast_pow]
    have hh : 3/(4*a) = 1/(4*a) + 1/(4*a) + 1/(4*a) := by ring
    rw [hh]
    linarith
  calc
    _ ≤ exp (3/(4*a) - (length z : ℝ)) := exp_le_exp.mpr hb
    _ = exp (3/(4*a)) * exp (-1) ^ length z := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (exp_pos _).le Real.exp_neg_one_lt_half.le _) (exp_pos _).le

theorem scaled_gaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun z : Triple => exp (-a * normSq z)) := by
  apply (weight_summable.mul_left (exp (3/(4*a)))).of_nonneg_of_le
    (fun _ => (exp_pos _).le)
  exact scaled_gaussian_le_weight ha

theorem summable_of_scaled_gaussian_bound {f : Triple → ℝ} {C a : ℝ}
    (_hC : 0 ≤ C) (ha : 0 < a) (hf : ∀ z, |f z| ≤ C * exp (-a*normSq z)) : Summable f := by
  apply ((scaled_gaussian_summable ha).mul_left C).of_norm_bounded
  exact hf

/-- A quadratic factor can be absorbed by halving the Gaussian exponent. -/
theorem quadratic_gaussian_bound {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (1+s)*exp (-a*s) ≤ (1+2/a)*exp (-(a/2)*s) := by
  have ht : 0 ≤ a/2*s := by positivity
  have he : a/2*s ≤ exp (a/2*s) := by linarith [Real.add_one_le_exp (a/2*s)]
  have h1 : 1 ≤ exp (a/2*s) := Real.one_le_exp ht
  have h2 : s ≤ (2/a)*exp (a/2*s) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).2
    nlinarith
  have hb : 1+s ≤ (1+2/a)*exp (a/2*s) := by nlinarith
  calc
    _ ≤ ((1+2/a)*exp (a/2*s))*exp (-a*s) := mul_le_mul_of_nonneg_right hb (exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end BccSharp.LatticeTails
