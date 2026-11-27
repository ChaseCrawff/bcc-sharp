module

public import BccSharp.Analysis.ExpBounds
public import BccSharp.Analysis.Erfc

/-! Checked reusable shell constants: a square root, its Gaussian, and erfc.
The series method handles small shells; the integral upper bound handles the
exponentially small far shells without cancellation in a long polynomial. -/

@[expose] public section
namespace BccSharp.ErfcBounds

open Real Intervals

inductive Method where
  | series (order : ℕ) (error : ℚ)
  | upper
  deriving DecidableEq, Repr

structure Witness where
  rootLo : ℚ
  rootHi : ℚ
  gaussian : ExpBounds.Witness
  method : Method
  result : Ball
  deriving DecidableEq, Repr

namespace Witness

def root (w : Witness) : Ball := ⟨(w.rootLo + w.rootHi) / 2, (w.rootHi - w.rootLo) / 2⟩

def baseCheck (w : Witness) (q : ℚ) : Bool := decide (0 < q ∧ 0 ≤ w.rootLo ∧ 0 ≤ w.rootHi ∧
  w.rootLo ^ 2 ≤ q ∧ q ≤ w.rootHi ^ 2 ∧ w.root.invertible ∧ w.gaussian.check (Ball.exact (-q)) = true)

def upperBall (w : Witness) : Ball := (w.gaussian.result.mul w.root.inv).mul Erfc.invSqrtPi

def raw (w : Witness) (q : ℚ) : Ball := match w.method with
  | .series n e =>
    let b := (Ball.exact 1).sub ((((Ball.exact 2).mul w.root).mul Erfc.invSqrtPi).mul (Ball.exact (Erfc.series q n)))
    ⟨b.mid, b.rad + e⟩
  | .upper => let u := w.upperBall.mid + w.upperBall.rad; ⟨u / 2, u / 2⟩

def methodCheck (w : Witness) (q : ℚ) : Bool := match w.method with
  | .series n e => decide (q / (n + 1 : ℕ) ≤ 1 / 2 ∧
      4 * (w.root.mid + w.root.rad) * (Erfc.invSqrtPi.mid + Erfc.invSqrtPi.rad) * q ^ n / (n.factorial : ℚ) ≤ e)
  | .upper => true

def check (w : Witness) (q : ℚ) : Bool := w.baseCheck q && w.methodCheck q && decide ((w.raw q).Covers w.result)

theorem root_sound {w : Witness} {q : ℚ} (hc : w.baseCheck q = true) : w.root.Contains (sqrt (q : ℝ)) := by
  have h : 0 < q ∧ 0 ≤ w.rootLo ∧ 0 ≤ w.rootHi ∧ w.rootLo ^ 2 ≤ q ∧ q ≤ w.rootHi ^ 2 ∧
      w.root.invertible ∧ w.gaussian.check (Ball.exact (-q)) = true := of_decide_eq_true hc
  exact Ball.sqrt_enclosure h.2.1 (by exact_mod_cast h.1.le) (by exact_mod_cast h.2.2.2.1)
    (by exact_mod_cast h.2.2.2.2.1) h.2.2.1

theorem gaussian_sound {w : Witness} {q : ℚ} (hc : w.baseCheck q = true) :
    w.gaussian.result.Contains (exp (-(q : ℝ))) := by
  have h : 0 < q ∧ 0 ≤ w.rootLo ∧ 0 ≤ w.rootHi ∧ w.rootLo ^ 2 ≤ q ∧ q ≤ w.rootHi ^ 2 ∧
      w.root.invertible ∧ w.gaussian.check (Ball.exact (-q)) = true := of_decide_eq_true hc
  simpa only [Rat.cast_neg] using ExpBounds.Witness.sound h.2.2.2.2.2.2 (Ball.contains_exact (-q))

theorem sound {w : Witness} {q : ℚ} (hc : w.check q = true) :
    w.result.Contains (Gaussian.erfcIntegral (sqrt (q : ℝ))) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hb := Bool.and_eq_true_iff.mp hh.1
  have h : 0 < q ∧ 0 ≤ w.rootLo ∧ 0 ≤ w.rootHi ∧ w.rootLo ^ 2 ≤ q ∧ q ≤ w.rootHi ^ 2 ∧
      w.root.invertible ∧ w.gaussian.check (Ball.exact (-q)) = true := of_decide_eq_true hb.1
  have hr := root_sound hb.1
  have he := gaussian_sound hb.1
  have hq : (0 : ℝ) < q := by exact_mod_cast h.1
  apply Ball.covers_sound (of_decide_eq_true hh.2)
  cases hm : w.method with
  | series n e =>
    have hc' : q / (n + 1 : ℕ) ≤ 1 / 2 ∧
        4 * (w.root.mid + w.root.rad) * (Erfc.invSqrtPi.mid + Erfc.invSqrtPi.rad) * q ^ n / (n.factorial : ℚ) ≤ e := by
      simpa only [methodCheck, hm, decide_eq_true_eq] using hb.2
    simpa only [raw, hm] using Erfc.enclosure h.1.le hc'.1 hr Erfc.invSqrtPi_contains hc'.2
  | upper =>
    have hi := Ball.contains_inv h.2.2.2.2.2.1 hr
    have hp := Ball.contains_mul (Ball.contains_mul he hi) Erfc.invSqrtPi_contains
    have hu := (SpecialFunctions.contains_iff_endpoints _ _).mp hp
    have hg := Gaussian.erfc_upper (sqrt_pos.mpr hq)
    rw [sq_sqrt hq.le] at hg
    have hupper : Gaussian.erfcIntegral (sqrt (q : ℝ)) ≤
        (w.upperBall.mid : ℝ) + w.upperBall.rad := by
      apply le_trans _ hu.2
      convert hg using 1
      ring
    have hzero := Ewald.erfc_nonneg (sqrt (q : ℝ))
    simp only [raw, hm, Ball.Contains]
    push_cast
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end Witness
end BccSharp.ErfcBounds
