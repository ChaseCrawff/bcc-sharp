import BccSharp.TwoSite.Bravais
import BccSharp.Analysis.Coverage

set_option autoImplicit false

/-! Lattice routing for the separate five-dimensional Bravais quotient
and strain covers. A numerical terminal name carries no mathematical weight
until its typed, box-specific evaluator supplies `Sound`. -/

noncomputable section
open Classical

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage

abbrev Point := Fin 5 → ℝ
abbrev Rectangle := Box 5

inductive Route where
  | reducedFailure | shortVector | aboveFCC | strictDefect
  | bccStrain | fccStrain | outsideStrain | ball | curvature | checkedFragment
  deriving DecidableEq, Repr

def split (b : Rectangle) (axis : Fin 5) (cut : ℚ) (upper : Bool) : Rectangle where
  lo i := if i = axis ∧ upper = true then cut else b.lo i
  hi i := if i = axis ∧ upper = false then cut else b.hi i

theorem split_covers (b : Rectangle) (i : Fin 5) (r : ℚ) (p : Point) (h : b.Mem p) :
    (split b i r false).Mem p ∨ (split b i r true).Mem p := by
  rcases le_total (p i) (r : ℝ) with lo | hi
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simpa [split] using And.intro (h i).1 lo
    · simpa [split, hj] using h j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simpa [split] using And.intro hi (h i).2
    · simpa [split, hj] using h j

inductive Trace where
  | branch (axis : Fin 5) (face : ℚ) (lower upper : Trace)
  | terminal (route : Route) (witness : Nat)

/-- Original binary64 Lattice faces are proposed exact rationals. Check the
face in the parent. A binary64 midpoint need not equal a rational midpoint. -/
def Trace.check (checkLeaf : Route → Nat → Rectangle → Bool) (parent : Rectangle) : Trace → Bool
  | .terminal route witness => checkLeaf route witness parent
  | .branch axis face lower upper =>
      decide (parent.lo axis ≤ face ∧ face ≤ parent.hi axis) &&
        (lower.check checkLeaf (split parent axis face false) &&
         upper.check checkLeaf (split parent axis face true))

def Sound (test : Route → Nat → Rectangle → Bool) (eligible closed : Point → Prop) : Prop :=
  ∀ route witness box, test route witness box = true →
    ∀ p, box.Mem p → eligible p → closed p

theorem Trace.sound (test : Route → Nat → Rectangle → Bool) (eligible closed : Point → Prop)
    (correct : Sound test eligible closed) (trace : Trace) (root : Rectangle)
    (checked : trace.check test root = true) (p : Point) (within : root.Mem p) (live : eligible p) : closed p := by
  induction trace generalizing root with
  | terminal route witness => exact correct route witness root checked p within live
  | branch axis face lower upper lowerIH upperIH =>
      have h := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).2
      rcases split_covers root axis face p within with left | right
      · exact lowerIH (split root axis face false) h.1 left
      · exact upperIH (split root axis face true) h.2 right

def Sharp (B : Mat) : Prop :=
  0 ≤ oneSiteDeficit B ∧ (oneSiteDeficit B = 0 →
    rigidCopy (lattice B) bcc.points ∨ rigidCopy (lattice B) fcc.points)

/-- Strictly above FCC suffices for the sharp one-site conclusion under
the same actual capped defect as the two-site theorem. -/
theorem sharp_of_above_fcc (B : Mat) (hGap : 0 < gap) (h : energy fcc < oneSiteEnergy B) : Sharp B := by
  have cap := (cappedDefect_range (liftedNeighbors (lattice B) 0)).2
  have penalty := mul_le_mul_of_nonneg_left cap hGap.le
  change gap * oneSiteDefect B ≤ gap * 1 at penalty
  have positive : 0 < oneSiteDeficit B := by
    unfold oneSiteDeficit gap
    unfold gap at penalty
    linarith
  exact ⟨positive.le, fun hz => (positive.ne' hz).elim⟩

/-- Explicit Bravais global root assembly. For the original Lattice route the
root roster is the exact grid checked against its outer endpoints. Strain
delegates must discharge `checkLeaf` through both certified strain atlases. -/
theorem lattice_assemble (presents : Mat → Point → Prop) (valid : Point → Prop)
    (box : Rectangle) (test : Route → Nat → Rectangle → Bool) (trace : Trace)
    (covered : trace.check test box = true)
    (reduce : ∀ B : Mat, B.det = 1/2 →
      Sharp B ∨ ∃ p, box.Mem p ∧ valid p ∧ presents B p)
    (correct : Sound test valid (fun p => ∀ B, presents B p → Sharp B)) : LatticeCase := by
  intro B det
  rcases reduce B det with strict | ⟨p, inside, hp, represents⟩
  · exact strict
  · exact trace.sound test valid _ correct box covered p inside hp B represents

end BccSharp.Coulomb.BravaisCover
