module

public import BccSharp.Analysis.DividedReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Exact rational trigonometric enclosures with proved Taylor remainders,
Lipschitz propagation of input uncertainty and integer-period reduction. -/

@[expose] public section
namespace BccSharp.TrigBounds

open Real Intervals

def iPower : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => (-(iPower n).2, (iPower n).1)

theorem iPower_correct (n : ℕ) :
    ((iPower n).1 : ℂ) + ((iPower n).2 : ℂ) * Complex.I = Complex.I ^ n := by
  induction n with
  | zero => norm_num [iPower]
  | succ n ih =>
    rw [pow_succ, ← ih]
    simp only [iPower, Rat.cast_neg]
    linear_combination -((iPower n).2 : ℂ) * Complex.I_sq

def cosPolynomial (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, q ^ k / (k.factorial : ℚ) * (iPower k).1

def sinPolynomial (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, q ^ k / (k.factorial : ℚ) * (iPower k).2

def error (q : ℚ) (n : ℕ) : ℚ := 2 * |q| ^ n / (n.factorial : ℚ)

theorem polynomial_complex (q : ℚ) (n : ℕ) :
    (cosPolynomial q n : ℂ) + (sinPolynomial q n : ℂ) * Complex.I =
      DividedExp.shifted 0 n ((q : ℂ) * Complex.I) := by
  unfold cosPolynomial sinPolynomial DividedExp.shifted
  push_cast
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_assoc _ ((iPower k).2 : ℂ) Complex.I, ← mul_add, iPower_correct, mul_pow]
  ring

theorem cos_point (q : ℚ) (n : ℕ) (hn : 0 < n) (hq : |q| / (n + 1 : ℕ) ≤ 1 / 2) :
    (⟨cosPolynomial q n, error q n⟩ : Ball).Contains (cos (q : ℝ)) := by
  have hgr : (((|q| / (n + 1 : ℕ)) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
  push_cast at hgr
  have hg : ‖(q : ℂ) * Complex.I‖ / (0 + n + 1 : ℕ) ≤ 1 / 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hgr
  have hcast : ((q : ℝ) : ℂ) = (q : ℂ) := by norm_cast
  have h := DividedExp.re_remainder 0 n hn ((q : ℂ) * Complex.I) hg
  rw [DividedExp.value_zero_order, ← polynomial_complex] at h
  have he := Complex.exp_ofReal_mul_I_re (q : ℝ)
  rw [hcast] at he
  rw [he] at h
  simpa [Ball.Contains, error, Complex.norm_real, Real.norm_eq_abs] using h

theorem sin_point (q : ℚ) (n : ℕ) (hn : 0 < n) (hq : |q| / (n + 1 : ℕ) ≤ 1 / 2) :
    (⟨sinPolynomial q n, error q n⟩ : Ball).Contains (sin (q : ℝ)) := by
  have hgr : (((|q| / (n + 1 : ℕ)) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
  push_cast at hgr
  have hg : ‖(q : ℂ) * Complex.I‖ / (0 + n + 1 : ℕ) ≤ 1 / 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hgr
  have hcast : ((q : ℝ) : ℂ) = (q : ℂ) := by norm_cast
  have h := DividedExp.im_remainder 0 n hn ((q : ℂ) * Complex.I) hg
  rw [DividedExp.value_zero_order, ← polynomial_complex] at h
  have he := Complex.exp_ofReal_mul_I_im (q : ℝ)
  rw [hcast] at he
  rw [he] at h
  simpa [Ball.Contains, error, Complex.norm_real, Real.norm_eq_abs] using h

def cosBall (b : Ball) (n : ℕ) : Ball := ⟨cosPolynomial b.mid n, error b.mid n + b.rad⟩
def sinBall (b : Ball) (n : ℕ) : Ball := ⟨sinPolynomial b.mid n, error b.mid n + b.rad⟩

theorem cos_contains {b : Ball} {x : ℝ} (hx : b.Contains x) {n : ℕ}
    (hn : 0 < n) (hg : |b.mid| / (n + 1 : ℕ) ≤ 1 / 2) : (cosBall b n).Contains (cos x) :=
  Erfc.perturb (cos_point b.mid n hn hg) ((abs_cos_sub_cos_le x b.mid).trans hx)

theorem sin_contains {b : Ball} {x : ℝ} (hx : b.Contains x) {n : ℕ}
    (hn : 0 < n) (hg : |b.mid| / (n + 1 : ℕ) ≤ 1 / 2) : (sinBall b n).Contains (sin x) :=
  Erfc.perturb (sin_point b.mid n hn hg) ((abs_sin_sub_sin_le x b.mid).trans hx)

def piBall : Ball := ⟨3141592653589793238465 / 10 ^ 21, 5 / 10 ^ 21⟩
def reduce (b : Ball) (k : ℤ) : Ball := b.sub ((Ball.exact k).mul ((Ball.exact 2).mul piBall))

theorem reduce_contains {b : Ball} {x : ℝ} (hx : b.Contains x) (k : ℤ) :
    (reduce b k).Contains (x - k * (2 * π)) := by
  exact Ball.contains_sub hx (Ball.contains_mul (Ball.contains_exact k)
    (Ball.contains_mul (Ball.contains_exact 2) SpecialFunctions.pi_enclosure))

theorem reduced_cos {b : Ball} {x : ℝ} (hx : b.Contains x) (k : ℤ) {n : ℕ}
    (hn : 0 < n) (hg : |(reduce b k).mid| / (n + 1 : ℕ) ≤ 1 / 2) :
    (cosBall (reduce b k) n).Contains (cos x) := by
  have h := cos_contains (reduce_contains hx k) hn hg
  simpa only [cos_sub_int_mul_two_pi] using h

theorem reduced_sin {b : Ball} {x : ℝ} (hx : b.Contains x) (k : ℤ) {n : ℕ}
    (hn : 0 < n) (hg : |(reduce b k).mid| / (n + 1 : ℕ) ≤ 1 / 2) :
    (sinBall (reduce b k) n).Contains (sin x) := by
  have h := sin_contains (reduce_contains hx k) hn hg
  simpa only [sin_sub_int_mul_two_pi] using h

end BccSharp.TrigBounds
