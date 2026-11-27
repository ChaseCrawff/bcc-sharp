import BccSharp.Cover.CoverExactRealGeometry
import BccSharp.Cover.CoverDirectSeries

set_option autoImplicit false

/-! Direct `energy_exact_real_n1` evaluator on the original addressed
sidecar box. The published exact distances are checked independently.
The old reciprocal control and the Constants comparison use the shared proof. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.DirectRoute
open BccSharp.Coverage BravaisCover
open BccSharp.Intervals (Ball)

structure RealOperand where
  mode : IntVec
  cross : Bool
  multiplicity : Nat
  upper : ℚ
  kernelLower : ℚ
  slopeLower : ℚ

structure ExactRealProposal where
  ownerBox : Cell
  terms : List RealOperand

def readDistance (w : ExactRealProposal) (s : Bool) (n : IntVec) : Option RealOperand :=
  w.terms.find? (fun r => r.cross==s && decide (r.mode=n))

def RealOperand.key (r : RealOperand) : Bool × IntVec := (r.cross,r.mode)

def operandRoster (w : ExactRealProposal) : Bool :=
  let entered := w.terms.map RealOperand.key
  let wanted := (directIndices 1).map (fun n => (true,n)) ++ (pairedIndices 1).map (fun n => (false,n))
  decide (entered.Nodup ∧ entered.length=wanted.length) &&
    wanted.all (fun key => decide (key∈entered)) &&
    w.terms.all (fun r => decide (r.multiplicity = if r.cross then 1 else 2))

def evalExactDistance (b : Cell) (w : ExactRealProposal) (s : Bool) (n : IntVec) : Option ℚ := do
  let r ← readDistance w s n
  if exactUpperCheck b s n r.upper then directLower (Ball.exact r.upper) else none

theorem evalExactDistance_sound (b : Cell) (w : ExactRealProposal) (s : Bool) (n : IntVec)
    (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b=true) (pos : 0<quad (gram (chartBasis p)) (chartVector p s n))
    (v : ℚ) (ok : evalExactDistance b w s n=some v) :
    (v : ℝ)≤gKernel (1/2) (Real.pi*quad (gram (chartBasis p)) (chartVector p s n)) := by
  cases proposal : readDistance w s n with
  | none => simp [evalExactDistance,proposal] at ok
  | some row =>
    by_cases tested : exactUpperCheck b s n row.upper=true
    · have upper := exactUpperCheck_sound b s n row.upper tested hd p hp
      have endpointPos := pos.trans_le upper
      have pointEval : directLower (Ball.exact row.upper)=some v := by
        simpa [evalExactDistance,proposal,tested] using ok
      have value := halfLower_sound (Ball.contains_exact row.upper) endpointPos _ _ pointEval
      exact value.trans (halfKernel_decreasing (mul_pos Real.pi_pos pos)
        (mul_le_mul_of_nonneg_left upper Real.pi_pos.le))
    · simp [evalExactDistance,proposal,tested] at ok

def exactRealValue (b : Cell) (w : ExactRealProposal) : Option ℚ :=
  finiteValueWith b 1 (evalExactDistance b w true) (evalExactDistance b w false)

def exactRealCheck (b : Cell) (w : ExactRealProposal) : Bool :=
  ((sameCell w.ownerBox b && operandRoster w) &&
    (diagonalsCheck b && cubeRootCheck scaleWitness scaleInput)) &&
  (decide ((directIndices 1).Nodup ∧ (pairedIndices 1).Nodup) &&
    match exactRealValue b w with
    | some v => decide (fccHUpper<v)
    | none => false)

theorem exactRealCheck_sound (b : Cell) (w : ExactRealProposal) (p : Chart) (hp : b.Mem p)
    (valid : (chartPoint p).Valid) (ok : exactRealCheck b w=true) : energy fcc<energy (chartPoint p) := by
  obtain ⟨data,work⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨_,constants⟩ := Bool.and_eq_true_iff.mp data
  obtain ⟨hd,scale⟩ := Bool.and_eq_true_iff.mp constants
  obtain ⟨nd,compared⟩ := Bool.and_eq_true_iff.mp work
  cases ev : exactRealValue b w with
  | none => simp [ev] at compared
  | some result =>
    have strict : fccHUpper< result := of_decide_eq_true (by simpa [ev] using compared)
    have bound := finiteValueWith_sound b 1 (evalExactDistance b w true) (evalExactDistance b w false)
      p hp hd valid (of_decide_eq_true nd)
      (fun n _ v e => evalExactDistance_sound b w true n p hp hd (cross_distance_positive valid n) v e)
      (fun n hn v e => by
        unfold seriesDirectTerm
        rw [ite_eq_right (lex_ne hn)]
        exact evalExactDistance_sound b w false n p hp hd (period_distance_positive valid n hn) v e)
      result ev
    exact aboveFCC_of_lower _ scale result strict bound

theorem exactRealCheck_physical (b : Cell) (w : ExactRealProposal) (p : Chart) (hp : b.Mem p)
    (valid : (chartPoint p).Valid) (ok : exactRealCheck b w=true) :
    greenPerParticle seriesScreen (physicalBasis fcc) (physicalTwoPositions fcc)<
      greenPerParticle seriesScreen (physicalBasis (chartPoint p)) (physicalTwoPositions (chartPoint p)) := by
  rw [green_two_eq_energy fcc (Constants.refTwo_valid .fcc),green_two_eq_energy _ valid]
  exact exactRealCheck_sound b w p hp valid ok

end BccSharp.Coulomb.CompactCover.DirectRoute
