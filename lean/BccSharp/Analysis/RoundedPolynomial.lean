module

public import BccSharp.Analysis.IntervalChecks
public import BccSharp.Analysis.TrigBounds

/-! Deterministic outward rounding and Horner bounds. All rounding is proved
correct for the actual polynomial; large exact Taylor fractions are avoided. -/

@[expose] public section
namespace BccSharp.RoundedPolynomial

open Intervals Real
open scoped BigOperators

def powTwo (e : ℤ) : ℚ := if 0 ≤ e then 2 ^ e.toNat else 1 / 2 ^ (-e).toNat

theorem powTwo_pos (e : ℤ) : 0 < powTwo e := by
  unfold powTwo
  split_ifs <;> positivity

def roundBall (b : Ball) : Ball :=
  let size := |b.mid| + b.rad
  if size = 0 then b else
    let exponent : ℤ := (size.num.natAbs.log2 : ℤ) - (size.den.log2 : ℤ) - 72
    let unit := powTwo exponent
    let mid : ℚ := (⌊b.mid / unit + 1 / 2⌋ : ℤ) * unit
    ⟨mid, (⌈(|mid - b.mid| + b.rad) / unit⌉ : ℤ) * unit⟩

theorem round_covers (b : Ball) : b.Covers (roundBall b) := by
  unfold roundBall
  dsimp only
  split_ifs with hz
  · simp [Ball.Covers]
  · unfold Ball.Covers
    dsimp only
    rw [abs_sub_comm b.mid]
    exact (div_le_iff₀ (powTwo_pos _)).mp (Int.le_ceil _)

theorem round_contains {b : Ball} {x : ℝ} (h : b.Contains x) : (roundBall b).Contains x :=
  Ball.covers_sound (round_covers b) h

noncomputable def polynomial (coeff : ℕ → ℚ) (d : ℕ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, x => (coeff d : ℝ) + x * polynomial coeff (d + 1) n x

theorem polynomial_sum (coeff : ℕ → ℚ) (d n : ℕ) (x : ℝ) :
    polynomial coeff d n x = ∑ k ∈ Finset.range n, (coeff (d + k) : ℝ) * x ^ k := by
  induction n generalizing d with
  | zero => simp [polynomial]
  | succ n ih =>
    rw [polynomial, ih, Finset.sum_range_succ']
    simp only [pow_zero, Nat.add_zero, mul_one]
    rw [add_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show d + 1 + k = d + (k + 1) by omega, pow_succ]
    ring

def evaluate (coeff : ℕ → ℚ) (d : ℕ) : ℕ → Ball → Ball
  | 0, _ => Ball.exact 0
  | n + 1, b => roundBall ((Ball.exact (coeff d)).add (b.mul (evaluate coeff (d + 1) n b)))

theorem evaluate_contains (coeff : ℕ → ℚ) (d n : ℕ) {b : Ball} {x : ℝ} (h : b.Contains x) :
    (evaluate coeff d n b).Contains (polynomial coeff d n x) := by
  induction n generalizing d with
  | zero => simpa [evaluate, polynomial] using Ball.contains_exact 0
  | succ n ih =>
    exact round_contains (Ball.contains_add (Ball.contains_exact (coeff d)) (Ball.contains_mul h (ih (d+1))))

def inflate (b : Ball) (e : ℚ) : Ball := ⟨b.mid, b.rad + e⟩

theorem inflate_contains {b : Ball} {e : ℚ} {x y : ℝ} (h : b.Contains y) (he : |x-y| ≤ (e : ℝ)) :
    (inflate b e).Contains x := by
  have ht := abs_sub_le x y (b.mid : ℝ)
  unfold Ball.Contains inflate at *
  push_cast
  linarith

def expCoefficients (n : ℕ) : ℚ := 1 / (n.factorial : ℚ)
def expBound (q : ℚ) (n : ℕ) : Ball :=
  inflate (evaluate expCoefficients 0 n (Ball.exact q)) (2 / (n.factorial : ℚ))

theorem expBound_contains {q : ℚ} {n : ℕ} (hq : |q| ≤ 1) (hn : 0 < n) :
    (expBound q n).Contains (exp (q : ℝ)) := by
  have hp := evaluate_contains expCoefficients 0 n (Ball.contains_exact q)
  have he : polynomial expCoefficients 0 n (q : ℝ) = (SpecialFunctions.taylor q n : ℝ) := by
    simp only [polynomial_sum, expCoefficients, SpecialFunctions.taylor, Nat.zero_add]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hp
  apply inflate_contains hp
  have ht := SpecialFunctions.exp_taylor q n hq hn
  have hpow : |q| ^ n ≤ (1 : ℚ) := by simpa using pow_le_pow_left₀ (abs_nonneg q) hq n
  have herror : SpecialFunctions.taylorError q n ≤ 2 / (n.factorial : ℚ) := by
    unfold SpecialFunctions.taylorError
    have hf : 0 < (n.factorial : ℚ) := by positivity
    have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
    have hn1 : 1 ≤ (n : ℚ) := by exact_mod_cast hn
    have hv : |q| ^ n * (n + 1 : ℕ) ≤ 2 * (n : ℚ) := by
      have hh := mul_le_mul_of_nonneg_right hpow (show (0 : ℚ) ≤ (n + 1 : ℕ) by positivity)
      push_cast at hh ⊢
      linarith
    apply (div_le_div_iff₀ (mul_pos hf hnq) hf).2
    convert mul_le_mul_of_nonneg_right hv hf.le using 1; ring
  exact ht.trans (Rat.cast_le.mpr herror)

def trigCoefficients (imaginary : Bool) (n : ℕ) : ℚ :=
  (if imaginary then (TrigBounds.iPower n).2 else (TrigBounds.iPower n).1) / (n.factorial : ℚ)

def trigMagnitude (q : ℚ) : ℚ := (⌈|q|⌉ : ℤ)
def trigError (q : ℚ) (n : ℕ) : ℚ := 2 * trigMagnitude q ^ n / (n.factorial : ℚ)
def trigBound (imaginary : Bool) (q : ℚ) (n : ℕ) : Ball :=
  inflate (evaluate (trigCoefficients imaginary) 0 n (Ball.exact q)) (trigError q n)

theorem trigError_le (q : ℚ) (n : ℕ) : TrigBounds.error q n ≤ trigError q n := by
  have hm : |q| ≤ trigMagnitude q := Int.le_ceil _
  unfold TrigBounds.error trigError
  gcongr

theorem cosBound_contains {q : ℚ} {n : ℕ} (hn : 0 < n) (hq : |q| / (n + 1 : ℕ) ≤ 1 / 2) :
    (trigBound false q n).Contains (cos (q : ℝ)) := by
  have hp := evaluate_contains (trigCoefficients false) 0 n (Ball.contains_exact q)
  have he : polynomial (trigCoefficients false) 0 n (q : ℝ) = (TrigBounds.cosPolynomial q n : ℝ) := by
    simp only [polynomial_sum, trigCoefficients, Bool.false_eq_true, ite_false,
      TrigBounds.cosPolynomial, Nat.zero_add]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hp
  exact inflate_contains hp ((TrigBounds.cos_point q n hn hq).trans (Rat.cast_le.mpr (trigError_le q n)))

theorem sinBound_contains {q : ℚ} {n : ℕ} (hn : 0 < n) (hq : |q| / (n + 1 : ℕ) ≤ 1 / 2) :
    (trigBound true q n).Contains (sin (q : ℝ)) := by
  have hp := evaluate_contains (trigCoefficients true) 0 n (Ball.contains_exact q)
  have he : polynomial (trigCoefficients true) 0 n (q : ℝ) = (TrigBounds.sinPolynomial q n : ℝ) := by
    simp only [polynomial_sum, trigCoefficients, ite_true, TrigBounds.sinPolynomial, Nat.zero_add]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hp
  exact inflate_contains hp ((TrigBounds.sin_point q n hn hq).trans (Rat.cast_le.mpr (trigError_le q n)))

def cosBall (b : Ball) (n : ℕ) : Ball := inflate (trigBound false b.mid n) b.rad
def sinBall (b : Ball) (n : ℕ) : Ball := inflate (trigBound true b.mid n) b.rad

theorem cos_contains {b : Ball} {x : ℝ} (hx : b.Contains x) {n : ℕ}
    (hn : 0 < n) (hg : |b.mid| / (n + 1 : ℕ) ≤ 1 / 2) : (cosBall b n).Contains (cos x) :=
  inflate_contains (cosBound_contains hn hg) ((abs_cos_sub_cos_le x b.mid).trans hx)

theorem sin_contains {b : Ball} {x : ℝ} (hx : b.Contains x) {n : ℕ}
    (hn : 0 < n) (hg : |b.mid| / (n + 1 : ℕ) ≤ 1 / 2) : (sinBall b n).Contains (sin x) :=
  inflate_contains (sinBound_contains hn hg) ((abs_sin_sub_sin_le x b.mid).trans hx)

end BccSharp.RoundedPolynomial
