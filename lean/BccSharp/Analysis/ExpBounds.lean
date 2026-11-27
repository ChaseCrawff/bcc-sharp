module

public import BccSharp.Analysis.IntervalChecks
public import BccSharp.Analysis.SpecialFunctions
public import BccSharp.Analysis.RoundedPolynomial

/-! A finite witness format for exponential range reduction. Each squaring
is rounded to a proposed rational ball and checked exactly, so denominator
growth in the external generator is not part of the trusted argument. -/

@[expose] public section
namespace BccSharp.ExpBounds

open Intervals Real

def squareChain (b : Ball) : List Ball → Bool
  | [] => true
  | c :: cs => decide ((b.mul b).Covers c) && squareChain c cs

def terminal (b : Ball) : List Ball → Ball
  | [] => b
  | c :: cs => terminal c cs

theorem squareChain_sound {cs : List Ball} {b : Ball} {x : ℝ}
    (hb : b.Contains x) (hc : squareChain b cs = true) :
    (terminal b cs).Contains (x ^ (2 ^ cs.length)) := by
  induction cs generalizing b x with
  | nil => simpa [terminal] using hb
  | cons c cs ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have hd : (b.mul b).Covers c := of_decide_eq_true hh.1
    have h := ih (Ball.covers_sound hd (Ball.contains_mul hb hb)) hh.2
    simpa [terminal, pow_mul, pow_succ, mul_assoc, mul_pow] using h

structure PointWitness where
  order : ℕ
  seed : Ball
  squares : List Ball
  deriving DecidableEq, Repr

namespace PointWitness

def argument (w : PointWitness) (q : ℚ) : ℚ := q / (2 ^ w.squares.length : ℕ)
def bound (w : PointWitness) : Ball := terminal w.seed w.squares

def check (w : PointWitness) (q : ℚ) : Bool :=
  decide (0 < w.order ∧ |w.argument q| ≤ 1) &&
    (decide ((RoundedPolynomial.expBound (w.argument q) w.order).Covers w.seed) ||
      decide ((⟨SpecialFunctions.taylor (w.argument q) w.order,
        SpecialFunctions.taylorError (w.argument q) w.order⟩ : Ball).Covers w.seed)) &&
    squareChain w.seed w.squares

theorem sound {w : PointWitness} {q : ℚ} (hw : w.check q = true) :
    w.bound.Contains (exp (q : ℝ)) := by
  have hh := Bool.and_eq_true_iff.mp hw
  have ha := Bool.and_eq_true_iff.mp hh.1
  have hd : 0 < w.order ∧ |w.argument q| ≤ 1 := of_decide_eq_true ha.1
  have ho : (RoundedPolynomial.expBound (w.argument q) w.order).Covers w.seed ∨
      (⟨SpecialFunctions.taylor (w.argument q) w.order,
        SpecialFunctions.taylorError (w.argument q) w.order⟩ : Ball).Covers w.seed := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using ha.2
  have hs : w.seed.Contains (exp ((w.argument q : ℚ) : ℝ)) := by
    rcases ho with hf | hl
    · exact Ball.covers_sound hf (RoundedPolynomial.expBound_contains hd.2 hd.1)
    · exact Ball.covers_sound hl (SpecialFunctions.exp_taylor _ _ hd.2 hd.1)
  have he := squareChain_sound hs hh.2
  have hp : exp ((w.argument q : ℚ) : ℝ) ^ (2 ^ w.squares.length) = exp (q : ℝ) := by
    rw [← exp_nat_mul]
    congr 1
    unfold argument
    push_cast
    field_simp
  rw [hp] at he
  exact he

end PointWitness

structure Witness where
  lower : PointWitness
  upper : PointWitness
  result : Ball
  deriving DecidableEq, Repr

namespace Witness

def check (w : Witness) (b : Ball) : Bool :=
  w.lower.check (b.mid - b.rad) && w.upper.check (b.mid + b.rad) &&
    decide (w.result.mid - w.result.rad ≤ w.lower.bound.mid - w.lower.bound.rad ∧
      w.upper.bound.mid + w.upper.bound.rad ≤ w.result.mid + w.result.rad)

theorem sound {w : Witness} {b : Ball} {x : ℝ}
    (hw : w.check b = true) (hb : b.Contains x) : w.result.Contains (exp x) := by
  have hh := Bool.and_eq_true_iff.mp hw
  have he := Bool.and_eq_true_iff.mp hh.1
  have hd : w.result.mid - w.result.rad ≤ w.lower.bound.mid - w.lower.bound.rad ∧
      w.upper.bound.mid + w.upper.bound.rad ≤ w.result.mid + w.result.rad := of_decide_eq_true hh.2
  have hlo := (SpecialFunctions.contains_iff_endpoints _ _).mp (PointWitness.sound he.1)
  have hup := (SpecialFunctions.contains_iff_endpoints _ _).mp (PointWitness.sound he.2)
  have hx := (SpecialFunctions.contains_iff_endpoints _ _).mp hb
  rw [SpecialFunctions.contains_iff_endpoints]
  have h1 : (w.result.mid : ℝ) - w.result.rad ≤ (w.lower.bound.mid : ℝ) - w.lower.bound.rad := by exact_mod_cast hd.1
  have h2 : (w.upper.bound.mid : ℝ) + w.upper.bound.rad ≤ (w.result.mid : ℝ) + w.result.rad := by exact_mod_cast hd.2
  constructor
  · apply h1.trans (hlo.1.trans (exp_le_exp.mpr ?_))
    simpa using hx.1
  · apply (exp_le_exp.mpr hx.2).trans
    simpa using hup.2.trans h2

end Witness
end BccSharp.ExpBounds
