import BccSharp.TwoSite.ReferenceKernels

set_option autoImplicit false

/-! High-precision Constants π enclosure. Machin's identity is a theorem of
mathlib. The finite alternating series error is derived from a rational
geometric identity integrated on a compact real interval. -/

noncomputable section
open scoped BigOperators
open Real MeasureTheory Set

namespace BccSharp.Coulomb.Constants
namespace HighPrecision

def atanPolynomial (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ)^k * t^(2*k)

def atanPrimitive (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1 : ℚ)^k * x^(2*k+1) / (2*k+1 : ℕ)

theorem geometric_identity (n : ℕ) (t : ℝ) :
    atanPolynomial n t + (-1 : ℝ)^n * t^(2*n) / (1+t^2) = 1 / (1+t^2) := by
  induction n with
  | zero => simp [atanPolynomial]
  | succ n ih =>
      have hp : atanPolynomial (n+1) t = atanPolynomial n t + (-1 : ℝ)^n * t^(2*n) := by
        unfold atanPolynomial
        rw [Finset.sum_range_succ]
      have h : (-1 : ℝ)^n * t^(2*n) + (-1 : ℝ)^(n+1) * t^(2*(n+1)) / (1+t^2) =
          (-1 : ℝ)^n * t^(2*n) / (1+t^2) := by
        rw [pow_succ (-1 : ℝ) n, show 2*(n+1) = 2*n+2 by omega, pow_add]
        field_simp [show 1+t^2 ≠ 0 by positivity] <;> ring
      rw [hp, add_assoc, h, ih]

theorem integrate_polynomial (n : ℕ) (q : ℚ) :
    (∫ t in (0 : ℝ)..(q : ℝ), atanPolynomial n t) = (atanPrimitive n q : ℝ) := by
  unfold atanPolynomial atanPrimitive
  push_cast
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  · intro k _
    exact (by fun_prop : Continuous (fun t : ℝ => (-1 : ℝ)^k * t^(2*k))).intervalIntegrable _ _

theorem arctan_from_integral (x : ℝ) :
    (∫ t in (0 : ℝ)..x, 1/(1+t^2)) = Real.arctan x := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) :=
    continuous_const.div (by fun_prop) (fun _ => by positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x) (fun t _ => Real.hasDerivAt_arctan t) (hc.intervalIntegrable 0 x)
  simpa [one_div, Real.arctan_zero] using h

theorem atan_error (n : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    |Real.arctan (q : ℝ) - (atanPrimitive n q : ℝ)| ≤ ((q^(2*n+1) : ℚ) : ℝ) := by
  have hx : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) :=
    continuous_const.div (by fun_prop) (fun _ => by positivity)
  have hp : Continuous (atanPolynomial n) := by unfold atanPolynomial; fun_prop
  rw [← arctan_from_integral, ← integrate_polynomial,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable 0 (q : ℝ)) (hp.intervalIntegrable 0 (q : ℝ)),
    ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (q : ℝ))
    (C := (q : ℝ)^(2*n)) (f := fun t => 1/(1+t^2) - atanPolynomial n t) ?_
  · simpa [abs_of_nonneg hx, pow_succ, mul_comm] using h
  · intro t ht
    rw [uIoc_of_le hx] at ht
    have ht' := ht.1.le
    have he : 1/(1+t^2) - atanPolynomial n t = (-1 : ℝ)^n * t^(2*n) / (1+t^2) := by
      linarith [geometric_identity n t]
    rw [he, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (pow_nonneg ht' _), abs_of_nonneg (by positivity : 0 ≤ 1+t^2)]
    exact (div_le_self (pow_nonneg ht' _) (by nlinarith [sq_nonneg t])).trans
      (pow_le_pow_left₀ ht' ht.2 _)

def piMid (n m : ℕ) : ℚ := 16 * atanPrimitive n (1/5) - 4 * atanPrimitive m (1/239)
def piRadius (n m : ℕ) : ℚ := 16 * (1/5 : ℚ)^(2*n+1) + 4 * (1/239 : ℚ)^(2*m+1)
def piBall (n m : ℕ) : BccSharp.Intervals.Ball := ⟨piMid n m, piRadius n m⟩

theorem piBall_sound (n m : ℕ) : (piBall n m).Contains Real.pi := by
  have hMachin : Real.pi = 16 * Real.arctan (1/5) - 4 * Real.arctan (1/239) := by
    have h : 4 * Real.arctan (1/5) - Real.arctan (1/239) = Real.pi / 4 := by
      simpa [one_div] using Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    linarith
  have a := abs_le.mp (atan_error n (q := 1/5) (by norm_num))
  have b := abs_le.mp (atan_error m (q := 1/239) (by norm_num))
  unfold piBall BccSharp.Intervals.Ball.Contains piMid piRadius
  rw [abs_le, hMachin]
  push_cast at a b ⊢
  exact ⟨by linarith [a.1, b.2], by linarith [a.2, b.1]⟩

/-- The choice of orders can be increased without changing the checker. -/
def referencePi : BccSharp.Intervals.Ball := piBall 54 20

theorem referencePi_sound : referencePi.Contains Real.pi := piBall_sound 54 20

open BccSharp
open BccSharp.Intervals (Ball)

/-- Square-root and inversion witness for a high precision normalizer. -/
structure RootProposal where
  lower : ℚ
  upper : ℚ

def RootProposal.ball (w : RootProposal) : Ball :=
  ⟨(w.lower + w.upper)/2, (w.upper - w.lower)/2⟩

def RootProposal.check (w : RootProposal) (input : Ball) : Bool :=
  decide (0 ≤ w.lower ∧ 0 ≤ w.upper ∧ w.lower^2 ≤ input.mid - input.rad ∧
    input.mid + input.rad ≤ w.upper^2 ∧ w.ball.invertible)

theorem RootProposal.sound (w : RootProposal) (input : Ball) (x : ℝ)
    (hx : 0 ≤ x) (hball : input.Contains x) (ok : w.check input = true) :
    w.ball.Contains (Real.sqrt x) := by
  have h : 0 ≤ w.lower ∧ 0 ≤ w.upper ∧ w.lower^2 ≤ input.mid - input.rad ∧
      input.mid + input.rad ≤ w.upper^2 ∧ w.ball.invertible := of_decide_eq_true ok
  have ⟨hl, hu⟩ := (SpecialFunctions.contains_iff_endpoints input x).mp hball
  have l : (w.lower : ℝ)^2 ≤ ((input.mid - input.rad : ℚ) : ℝ) := by exact_mod_cast h.2.2.1
  have u : ((input.mid + input.rad : ℚ) : ℝ) ≤ (w.upper : ℝ)^2 := by exact_mod_cast h.2.2.2.1
  have hlo : (w.lower : ℝ)^2 ≤ x := le_trans (by simpa only [Rat.cast_sub] using l) hl
  have hup : x ≤ (w.upper : ℝ)^2 := hu.trans (by simpa only [Rat.cast_add] using u)
  exact Ball.sqrt_enclosure h.1 hx hlo hup h.2.1

theorem RootProposal.inverse_sound (w : RootProposal) (input : Ball) (x : ℝ)
    (hx : 0 ≤ x) (hball : input.Contains x) (ok : w.check input = true) :
    w.ball.inv.Contains (Real.sqrt x)⁻¹ := by
  have h : 0 ≤ w.lower ∧ 0 ≤ w.upper ∧ w.lower^2 ≤ input.mid - input.rad ∧
      input.mid + input.rad ≤ w.upper^2 ∧ w.ball.invertible := of_decide_eq_true ok
  exact Ball.contains_inv h.2.2.2.2 (w.sound input x hx hball ok)

structure ErfcSeriesProposal where
  root : RootProposal
  order : ℕ
  error : ℚ

def ErfcSeriesProposal.check (w : ErfcSeriesProposal) (q : ℚ) (p : Ball) : Bool :=
  w.root.check (Ball.exact q) && decide (0 ≤ q ∧ q / (w.order + 1 : ℕ) ≤ 1/2 ∧
    4 * (w.root.ball.mid + w.root.ball.rad) * (p.mid+p.rad) * q^w.order / (w.order.factorial : ℚ) ≤ w.error)

def ErfcSeriesProposal.result (w : ErfcSeriesProposal) (q : ℚ) (p : Ball) : Ball :=
  let b := (Ball.exact 1).sub ((((Ball.exact 2).mul w.root.ball).mul p).mul
    (Ball.exact (Erfc.series q w.order)))
  ⟨b.mid,b.rad+w.error⟩

theorem ErfcSeriesProposal.sound (w : ErfcSeriesProposal) (q : ℚ) (p : Ball)
    (hp : p.Contains (Real.sqrt Real.pi)⁻¹) (ok : w.check q p = true) :
    (w.result q p).Contains (Gaussian.erfcIntegral (Real.sqrt (q : ℝ))) := by
  have both := Bool.and_eq_true_iff.mp ok
  have h : 0 ≤ q ∧ q / (w.order + 1 : ℕ) ≤ 1/2 ∧
      4 * (w.root.ball.mid + w.root.ball.rad) * (p.mid+p.rad) * q^w.order / (w.order.factorial : ℚ)
        ≤ w.error := of_decide_eq_true both.2
  have r : 0 ≤ w.root.lower ∧ 0 ≤ w.root.upper ∧ w.root.lower^2 ≤ (Ball.exact q).mid - (Ball.exact q).rad ∧
      (Ball.exact q).mid + (Ball.exact q).rad ≤ w.root.upper^2 ∧ w.root.ball.invertible :=
    of_decide_eq_true both.1
  have lo : (w.root.lower : ℝ)^2 ≤ (q : ℝ) := by
    have hr : w.root.lower^2 ≤ q := by simpa [Ball.exact] using r.2.2.1
    exact_mod_cast hr
  have hi : (q : ℝ) ≤ (w.root.upper : ℝ)^2 := by
    have hr : q ≤ w.root.upper^2 := by simpa [Ball.exact] using r.2.2.2.1
    exact_mod_cast hr
  have hs : w.root.ball.Contains (Real.sqrt (q : ℝ)) :=
    Ball.sqrt_enclosure r.1 (Rat.cast_nonneg.mpr h.1) lo hi r.2.1
  exact Erfc.enclosure h.1 h.2.1 hs hp h.2.2

/-- Spend one tenth of the exponent on summability and keep nine tenths as
the spatial cutoff loss. This is used only for omitted positive terms. -/
theorem exponential_cutoff {x cutoff : ℝ} (h : cutoff ≤ x) :
    Real.exp (-x) ≤ Real.exp (-(9/10 : ℝ)*cutoff) * Real.exp (-x/10) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end HighPrecision
end BccSharp.Coulomb.Constants
