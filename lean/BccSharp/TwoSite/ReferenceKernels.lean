import BccSharp.TwoSite.Reference
import BccSharp.Analysis.ErfcBounds

set_option autoImplicit false

/-! Reuse of the repository's real special-function checkers for Constants
shells. A single pi enclosure parameter is shared by reciprocal kernels.
The existing pi and erfc constants determine the attainable precision. -/

noncomputable section
open Classical

namespace BccSharp.Coulomb.Constants
open BccSharp
open BccSharp.Intervals (Ball)

theorem erfc_agrees (x : ℝ) : erfcIntegral x = Gaussian.erfcIntegral x := by
  rfl

def DirectShell.argument (ref : Reference) (q : ℚ) : ℚ := ref.alpha ^ 2 * q

def DirectShell.bound (ref : Reference) (w : ErfcBounds.Witness) : Ball :=
  (Ball.exact (ref.alpha / 2)).mul (w.result.mul w.root.inv)

def DirectShell.check (ref : Reference) (q : ℚ) (w : ErfcBounds.Witness) : Bool :=
  w.check (DirectShell.argument ref q)

theorem DirectShell.sound (ref : Reference) (q : ℚ) (w : ErfcBounds.Witness)
    (h : DirectShell.check ref q w = true) : (DirectShell.bound ref w).Contains (ref.directValue q) := by
  have hbase := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  rcases (of_decide_eq_true hbase : 0 < DirectShell.argument ref q ∧ 0 ≤ w.rootLo ∧
    0 ≤ w.rootHi ∧ w.rootLo ^ 2 ≤ DirectShell.argument ref q ∧
    DirectShell.argument ref q ≤ w.rootHi ^ 2 ∧ w.root.invertible ∧
    w.gaussian.check (Ball.exact (-DirectShell.argument ref q)) = true) with
    ⟨_, _, _, _, _, hi, _⟩
  have hInv := Ball.contains_inv hi (ErfcBounds.Witness.root_sound hbase)
  have hErfc := ErfcBounds.Witness.sound h
  have hα : 0 < (ref.alpha : ℝ) := by cases ref <;> norm_num [Reference.alpha]
  have hs : Real.sqrt ((DirectShell.argument ref q : ℚ) : ℝ) =
      (ref.alpha : ℝ) * Real.sqrt (q : ℝ) := by
    unfold DirectShell.argument
    push_cast
    rw [Real.sqrt_mul (sq_nonneg (ref.alpha : ℝ)), Real.sqrt_sq hα.le]
  have raw := Ball.contains_mul (Ball.contains_exact (ref.alpha / 2)) (Ball.contains_mul hErfc hInv)
  rw [hs, ← erfc_agrees] at raw
  change (DirectShell.bound ref w).Contains _ at raw
  convert raw using 1
  unfold Reference.directValue
  push_cast
  by_cases hz : Real.sqrt (q : ℝ) = 0
  · simp [hz]
  · field_simp [hα.ne', hz] <;> ring

def ReciprocalShell.argument (ref : Reference) (q : ℚ) (pi : Ball) : Ball :=
  (pi.mul pi).mul (Ball.exact (-q / ref.alpha ^ 2))

def ReciprocalShell.denominator (ref : Reference) (q : ℚ) (pi : Ball) : Ball :=
  pi.mul (Ball.exact (2 * ref.naturalVolume * q))

def ReciprocalShell.check (ref : Reference) (q : ℚ) (pi : Ball) (w : ExpBounds.Witness) : Bool :=
  w.check (ReciprocalShell.argument ref q pi) &&
    decide (ReciprocalShell.denominator ref q pi).invertible

def ReciprocalShell.bound (ref : Reference) (q : ℚ) (pi : Ball) (w : ExpBounds.Witness) : Ball :=
  w.result.mul (ReciprocalShell.denominator ref q pi).inv

theorem ReciprocalShell.sound (ref : Reference) (q : ℚ) (pi : Ball) (w : ExpBounds.Witness)
    (hπ : pi.Contains Real.pi) (hc : ReciprocalShell.check ref q pi w = true) :
    (ReciprocalShell.bound ref q pi w).Contains (ref.reciprocalValue q) := by
  have h := Bool.and_eq_true_iff.mp hc
  have ha : (ReciprocalShell.argument ref q pi).Contains
      (-(Real.pi ^ 2 * (q : ℝ) / (ref.alpha : ℝ)^2)) := by
    have hArg := Ball.contains_mul (Ball.contains_mul hπ hπ) (Ball.contains_exact (-q / ref.alpha ^ 2))
    have e : -(Real.pi ^ 2 * (q : ℝ) / (ref.alpha : ℝ)^2) =
        Real.pi * Real.pi * ((-q / ref.alpha ^ 2 : ℚ) : ℝ) := by
      push_cast
      ring
    rw [e]
    exact hArg
  have hd : (ReciprocalShell.denominator ref q pi).Contains
      (2 * Real.pi * (ref.naturalVolume : ℝ) * (q : ℝ)) := by
    have hDen := Ball.contains_mul hπ (Ball.contains_exact (2 * ref.naturalVolume * q))
    have e : 2 * Real.pi * (ref.naturalVolume : ℝ) * (q : ℝ) =
        Real.pi * ((2 * ref.naturalVolume * q : ℚ) : ℝ) := by
      push_cast
      ring
    rw [e]
    exact hDen
  have he := ExpBounds.Witness.sound h.1 ha
  have hi := Ball.contains_inv (of_decide_eq_true h.2) hd
  unfold Reference.reciprocalValue ReciprocalShell.bound
  rw [div_eq_mul_inv]
  exact Ball.contains_mul he hi

end BccSharp.Coulomb.Constants
