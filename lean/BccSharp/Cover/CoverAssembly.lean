import BccSharp.Cover.CoverReflection
import BccSharp.Cover.CoverCorner

set_option autoImplicit false

/-! Stage6 comparison binding and composition with the checked late
corpus. The only remaining earlier cover premise ends at Stage5b, after
the real local/optical certificates and clips. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Coverage
open LatePackets

structure Stage6Proposal where
  compare : Comparison
  targetSeed : String
  targetFragment : ℕ
  sourceSeed : String
  sourceFragment : ℕ
  profile : Fin 3
  target : Cell
  source : Cell

def Stage6Proposal.route (w : Stage6Proposal) : Route :=
  match w.compare with | .fcc => .strictFCC | .deficit => .strictDeficit

structure Stage6Request where
  input : Atom
  proposal : Stage6Proposal

def Stage6Request.located (q : Stage6Request) (seed : String) (fragment : ℕ) (box : Cell) : Bool :=
  if fragment=0 then
    match decodeSeed seed with
    | some path => sameCell box (restrict q.input.ownerHull path)
    | none => false
  else
    decide (seed=q.input.address.seed ∧ fragment=q.input.address.replacement) && sameCell box q.input.box

def Stage6Request.geometry (q : Stage6Request) : Bool :=
  let a := q.input
  let w := q.proposal
  let addr := (decide (a.address.path=[]) && q.located w.targetSeed w.targetFragment w.target) &&
    q.located w.sourceSeed w.sourceFragment w.source
  addr && ((boxInside a.box w.target && boxInside w.target w.source) && boxInside w.source a.ownerHull)

abbrev Stage6Checker := Stage6Request → Bool

def Stage6CheckerSound (check : Stage6Checker) : Prop :=
  ∀ q, q.geometry=true → check q=true →
    ∀ p, q.proposal.target.Mem p → good p → q.proposal.route.result p

inductive Stage6Trace where
  | keep (label : InputClass)
  | close (proposal : Stage6Proposal)

def runStage6 (check : Stage6Checker) (a : Atom) (trace : Stage6Trace) : Option (List Atom) :=
  match trace with
  | .keep label => some [{a with label := label}]
  | .close w =>
      let q : Stage6Request := ⟨a,w⟩
      if q.geometry && check q then some [] else none

theorem runStage6_sound {check : Stage6Checker} (sound : Stage6CheckerSound check)
    (a : Atom) (trace : Stage6Trace) (out : List Atom) (ok : runStage6 check a trace=some out)
    (p : Chart) (gp : good p) (hp : a.box.Mem p) : LeafProof (chartPoint p) ∨ Slots out p := by
  cases trace with
  | keep label =>
      have e : [{a with label := label}]=out := Option.some.inj ok
      rw [← e]
      exact Or.inr ⟨a.asCell,by simp [Atom.asCell],hp⟩
  | close w =>
      let q : Stage6Request := ⟨a,w⟩
      by_cases h : (q.geometry && check q)=true
      · obtain ⟨geometry,analytic⟩ := Bool.and_eq_true_iff.mp h
        have part := (Bool.and_eq_true_iff.mp ((Bool.and_eq_true_iff.mp geometry).2)).1
        have bound := boxInside_sound ((Bool.and_eq_true_iff.mp part).1) hp
        exact Or.inl (w.route.toLeaf p gp (sound q geometry analytic p bound gp))
      · simp [runStage6,q,h] at ok

theorem checkedStage6 {check : Stage6Checker} (sound : Stage6CheckerSound check)
    (input output : List Atom) (rows : List (Row Stage6Trace))
    (ok : runRows (runStage6 check) input rows=some output) :
    Handoff {p | Slots input p} {p | Slots output p} :=
  fun p hp gp => runRows_sound (runStage6_sound sound) input rows output ok p gp hp

theorem checkedHistoricalCover {early : Stage6Checker} {late : Checker}
    (sEarly : Stage6CheckerSound early) (sLate : CheckerSound late)
    (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (upstream : Handoff positiveHalf {p | Slots stage5b p})
    (rStage6 : runRows (runStage6 early) stage5b rows=some stage6)
    (closed : corp.run late stage6=some []) : Handoff chartRoot ∅ :=
  from_positive_half (Handoff.trans upstream (Handoff.trans
    (checkedStage6 sEarly stage5b stage6 rows rStage6) (corp.cover sLate stage6 closed)))

end BccSharp.Coulomb.CompactCover

namespace BccSharp.Coulomb
open CompactCover
open CompactCover.LatePackets

theorem assemble_from_checked_cover (analytic : GlobalAnalyticInputs)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early) (sLate : CheckerSound late)
    (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (upstream : Handoff positiveHalf {p | Slots stage5b p})
    (rStage6 : runRows (runStage6 early) stage5b rows=some stage6) (closed : corp.run late stage6=some []) : Statement := by
  have cover := checkedHistoricalCover sEarly sLate stage5b stage6 rows corp upstream rStage6 closed
  have gp := Constants.reference_gap_checked.2
  apply assemble
  refine ⟨gp,fun q _ => defect_range q,analytic.compact,?_,analytic.bccValues,analytic.fccValues,
    Constants.refTwo_valid .fcc,analytic.fccSaturated,analytic.register⟩
  intro q p rep
  have cert := Handoff.final cover p ((inRoot_iff p).mp rep.root) ⟨rep.valid,rep.reduced,rep.separation⟩
  have e : deficit (chartPoint p)=deficit q := by simp only [deficit,rep.sameEnergy,rep.sameDefect]
  by_cases h : deficit q≤0
  · obtain ⟨z,hcase⟩ := leaf_of_nonpositive (chartPoint p) gp (defect_range (chartPoint p)).2
      (by simpa only [e] using h) cert
    rw [e] at z
    exact .classifiedNonnegative z.ge (fun _ => reduced_equality_transport q p rep hcase)
  · exact .strictDeficit (lt_of_not_ge h)

end BccSharp.Coulomb
