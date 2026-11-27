import BccSharp.TwoSite.Bravais
import BccSharp.Analysis.Coverage

set_option autoImplicit false

/-! Routing and geometric kernel for the complete compact proof.
The executable tree and stage checkers do exact rational work. Their
soundness consumes a theorem for each witness family on the derived cell. -/

noncomputable section
open Classical

namespace BccSharp.Coulomb
namespace CompactCover

open BccSharp.Coverage

abbrev Cell := Box 8
abbrev Axis := Fin 8

def root : Cell :=
  ⟨![5/8, 1/2, 0, 0, -1/2, -1/2, -1/2, -1/2],
   ![37/32, 11/8, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2]⟩

theorem inRoot_iff (p : Chart) : inRoot p ↔ root.Mem p := by
  norm_num [inRoot, root, Box.Mem, Fin.forall_fin_succ, Set.mem_Icc] <;> tauto

def good (p : Chart) : Prop :=
  (chartPoint p).Valid ∧ reductionInequalities p ∧ separated (chartPoint p)

def replaceEnd (b : Cell) (i : Axis) (cut : ℚ) (upper : Bool) : Cell where
  lo j := if j = i ∧ upper = true then cut else b.lo j
  hi j := if j = i ∧ upper = false then cut else b.hi j

def midpoint (b : Cell) (i : Axis) : ℚ := (b.lo i + b.hi i) / 2

theorem two_closed_children (b : Cell) (i : Axis) (r : ℚ) (p : Chart) (hp : b.Mem p) :
    (replaceEnd b i r false).Mem p ∨ (replaceEnd b i r true).Mem p := by
  rcases le_total (p i) (r : ℝ) with h | h
  · left
    intro j
    by_cases he : j = i
    · subst j
      simpa [replaceEnd] using And.intro (hp i).1 h
    · simpa [replaceEnd, he] using hp j
  · right
    intro j
    by_cases he : j = i
    · subst j
      simpa [replaceEnd] using And.intro h (hp i).2
    · simpa [replaceEnd, he] using hp j

def intersection (a b : Cell) : Cell where
  lo i := max (a.lo i) (b.lo i)
  hi i := min (a.hi i) (b.hi i)

theorem mem_intersection (a b : Cell) (p : Chart) :
    (intersection a b).Mem p ↔ a.Mem p ∧ b.Mem p := by
  constructor
  · intro h
    have h' i := h i
    simp [intersection, max_le_iff, le_min_iff] at h'
    exact ⟨fun i => ⟨(h' i).1.1, (h' i).2.1⟩, fun i => ⟨(h' i).1.2, (h' i).2.2⟩⟩
  · rintro ⟨ha, hb⟩ i
    simpa [intersection, max_le_iff, le_min_iff] using
      And.intro (And.intro (ha i).1 (hb i).1) (And.intro (ha i).2 (hb i).2)

/-- An exact clip and closed coordinate slabs cover the parent. The trace
can subdivide these slabs again to make their interiors disjoint. -/
theorem clip_and_closed_slabs (parent clip : Cell) (p : Chart) (hp : parent.Mem p) :
    (intersection parent clip).Mem p ∨ ∃ i : Axis,
      (replaceEnd parent i (clip.lo i) false).Mem p ∨
      (replaceEnd parent i (clip.hi i) true).Mem p := by
  by_cases hc : clip.Mem p
  · exact Or.inl ((mem_intersection parent clip p).mpr ⟨hp, hc⟩)
  · right
    have failure : ∃ i : Axis, ¬ ((clip.lo i : ℝ) ≤ p i ∧ p i ≤ (clip.hi i : ℝ)) :=
      not_forall.mp hc
    obtain ⟨i, fail⟩ := failure
    refine ⟨i, ?_⟩
    by_cases low : p i < (clip.lo i : ℝ)
    · left
      intro j
      by_cases he : j = i
      · subst j
        simpa [replaceEnd] using And.intro (hp i).1 low.le
      · simpa [replaceEnd, he] using hp j
    · have high : (clip.hi i : ℝ) ≤ p i :=
        (lt_of_not_ge (fun h => fail ⟨le_of_not_gt low, h⟩)).le
      right
      intro j
      by_cases he : j = i
      · subst j
        simpa [replaceEnd] using And.intro high (hp i).2
      · simpa [replaceEnd, he] using hp j

def sameCell (a b : Cell) : Bool := decide (∀ i, a.lo i = b.lo i ∧ a.hi i = b.hi i)

theorem sameCell_sound {a b : Cell} (h : sameCell a b = true) : a = b := by
  have h' : ∀ i, a.lo i = b.lo i ∧ a.hi i = b.hi i := of_decide_eq_true h
  cases a
  cases b
  congr
  · funext i
    exact (h' i).1
  · funext i
    exact (h' i).2

structure Key where
  original : Nat
  seed : String
  replacement : Nat
  path : List Nat
  deriving DecidableEq, Repr

structure AddressedCell where
  key : Key
  cell : Cell

def sameAddressedCell (a b : AddressedCell) : Bool := decide (a.key = b.key) && sameCell a.cell b.cell

theorem sameAddressedCell_sound {a b : AddressedCell} (h : sameAddressedCell a b = true) : a = b := by
  have h' := Bool.and_eq_true_iff.mp h
  have hk : a.key = b.key := of_decide_eq_true h'.1
  have hc := sameCell_sound h'.2
  cases a
  cases b
  congr

/-- Preserve geometric rejections and the two equality-capable routes. -/
inductive Route where
  | invalidReduction | strictFCC | strictDeficit | strictJoint
  | localAtlas | relativeOptical | absoluteDefect | anchorSlack
  deriving DecidableEq, Repr

def LocalEvidence (q : TwoSite) : Prop :=
  ∃ cost coefficient : ℝ, 0 < coefficient ∧ 0 ≤ cost ∧ coefficient * cost ≤ deficit q ∧
    (cost = 0 → IsBCC q ∨ IsFCC q)

def OpticalEvidence (q : TwoSite) : Prop :=
  ∃ (f₀ : Vec) (n : IntVec) (coefficient : ℝ),
    HalfClass f₀ ∧ 0 < coefficient ∧ 0 ≤ deficit (anchorOf q f₀) ∧
    deficit (anchorOf q f₀) + coefficient * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤ deficit q ∧
    (deficit (anchorOf q f₀) = 0 →
      sq (q.basis.mulVec (q.offset - f₀ - castVec n)) = 0 → IsBCC q ∨ IsFCC q)

def Route.result (route : Route) (p : Chart) : Prop :=
  match route with
  | .invalidReduction => ¬ reductionInequalities p
  | .strictFCC => energy fcc < energy (chartPoint p)
  | .strictDeficit | .strictJoint | .absoluteDefect | .anchorSlack => 0 < deficit (chartPoint p)
  | .localAtlas => LocalEvidence (chartPoint p)
  | .relativeOptical => OpticalEvidence (chartPoint p)

theorem Route.toLeaf (route : Route) (p : Chart) (h : good p) (w : route.result p) :
    LeafProof (chartPoint p) := by
  cases route with
  | invalidReduction => exact (w h.2.1).elim
  | strictFCC => exact .strictFCC w
  | strictDeficit | strictJoint | absoluteDefect | anchorSlack => exact .strictDeficit w
  | localAtlas =>
      obtain ⟨cost, coefficient, positive, nonnegative, bound, center⟩ := w
      exact .localBasin cost coefficient positive nonnegative bound center
  | relativeOptical =>
      obtain ⟨f₀, n, coefficient, half, positive, anchor, bound, eqCase⟩ := w
      exact .optical f₀ n coefficient half positive anchor bound eqCase

structure WitnessRef where
  route : Route
  source : String
  record : Nat
  deriving DecidableEq, Repr

inductive Cut where
  | dyadic (axis : Axis)
  | rational (axis : Axis) (value : ℚ)

def Cut.position (cut : Cut) (b : Cell) : Axis × ℚ :=
  match cut with
  | .dyadic i => (i, midpoint b i)
  | .rational i r => (i, r)

def Cut.fits (cut : Cut) (b : Cell) : Bool :=
  let (i, r) := cut.position b
  decide (b.lo i ≤ r ∧ r ≤ b.hi i)

def Cut.child (cut : Cut) (b : Cell) (upper : Bool) : Cell :=
  let (i, r) := cut.position b
  replaceEnd b i r upper

inductive Tree where
  | close (witness : WitnessRef)
  | hold (key : Key)
  | split (cut : Cut) (lower upper : Tree)

def Tree.holds (b : Cell) : Tree → List AddressedCell
  | .close _ => []
  | .hold key => [⟨key, b⟩]
  | .split cut lower upper => lower.holds (cut.child b false) ++ upper.holds (cut.child b true)

def Tree.check (checkWitness : WitnessRef → Cell → Bool) (b : Cell) : Tree → Bool
  | .close w => checkWitness w b
  | .hold _ => true
  | .split cut lower upper => cut.fits b &&
      (lower.check checkWitness (cut.child b false) && upper.check checkWitness (cut.child b true))

def Held (cells : List AddressedCell) (p : Chart) : Prop :=
  ∃ row ∈ cells, row.cell.Mem p

theorem held_append {a b : List AddressedCell} {p : Chart} :
    Held (a ++ b) p ↔ Held a p ∨ Held b p := by
  constructor
  · rintro ⟨row, hr, hm⟩
    rcases List.mem_append.mp hr with ha | hb
    · exact Or.inl ⟨row, ha, hm⟩
    · exact Or.inr ⟨row, hb, hm⟩
  · rintro (⟨row, ha, hm⟩ | ⟨row, hb, hm⟩)
    · exact ⟨row, List.mem_append.mpr (Or.inl ha), hm⟩
    · exact ⟨row, List.mem_append.mpr (Or.inr hb), hm⟩

def SoundCheck (check : WitnessRef → Cell → Bool) : Prop :=
  ∀ w b, check w b = true → ∀ p, b.Mem p → good p → w.route.result p

theorem Tree.sound {check : WitnessRef → Cell → Bool} (checkSound : SoundCheck check)
    (tree : Tree) (b : Cell) (hCheck : tree.check check b = true) (p : Chart)
    (hs : good p) (hMem : b.Mem p) : LeafProof (chartPoint p) ∨ Held (tree.holds b) p := by
  induction tree generalizing b with
  | close w => exact Or.inl (w.route.toLeaf p hs (checkSound w b hCheck p hMem hs))
  | hold key => exact Or.inr ⟨⟨key, b⟩, by simp [Tree.holds], hMem⟩
  | split cut lower upper lowerIH upperIH =>
      have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hCheck).2
      rcases two_closed_children b (cut.position b).1 (cut.position b).2 p hMem with hl | hu
      · rcases lowerIH (cut.child b false) both.1 hl with h | h
        · exact Or.inl h
        · exact Or.inr (held_append.mpr (Or.inl h))
      · rcases upperIH (cut.child b true) both.2 hu with h | h
        · exact Or.inl h
        · exact Or.inr (held_append.mpr (Or.inr h))

structure RootTrace where
  input : AddressedCell
  tree : Tree

/-- Stream one stage in exact input order. The resulting list is determined
by the verified trees and must feed the next stage. -/
def runStage (check : WitnessRef → Cell → Bool) :
    List AddressedCell → List RootTrace → Option (List AddressedCell)
  | [], [] => some []
  | row :: rows, job :: jobs =>
      if sameAddressedCell row job.input && job.tree.check check row.cell then
        (runStage check rows jobs).map (fun remaining => job.tree.holds row.cell ++ remaining)
      else none
  | _, _ => none

theorem stage_sound {check : WitnessRef → Cell → Bool} (checkSound : SoundCheck check)
    (incoming : List AddressedCell) (jobs : List RootTrace) (outgoing : List AddressedCell)
    (hRun : runStage check incoming jobs = some outgoing) (p : Chart) (hs : good p)
    (hMem : Held incoming p) : LeafProof (chartPoint p) ∨ Held outgoing p := by
  induction incoming generalizing jobs outgoing with
  | nil => simp [Held] at hMem
  | cons row rows ih =>
      cases jobs with
      | nil => simp [runStage] at hRun
      | cons job jobs =>
          simp only [runStage] at hRun
          split at hRun
          next hCheck =>
            cases hre : runStage check rows jobs with
            | none => simp [hre] at hRun
            | some more =>
                simp [hre] at hRun
                subst outgoing
                have hHeads := Bool.and_eq_true_iff.mp hCheck
                have hPartition : Held [row] p ∨ Held rows p := held_append.mp hMem
                rcases hPartition with hh | ht
                · obtain ⟨candidate, member, inside⟩ := hh
                  have he : candidate = row := by simpa using member
                  subst candidate
                  rcases job.tree.sound checkSound row.cell hHeads.2 p hs inside with w | held
                  · exact Or.inl w
                  · exact Or.inr (held_append.mpr (Or.inl held))
                · rcases ih jobs more hre ht with w | held
                  · exact Or.inl w
                  · exact Or.inr (held_append.mpr (Or.inr held))
          next _ => simp at hRun

def runChain (check : WitnessRef → Cell → Bool) (start : List AddressedCell) :
    List (List RootTrace) → Option (List AddressedCell)
  | [] => some start
  | jobs :: later => (runStage check start jobs).bind (fun next => runChain check next later)

theorem chain_sound {check : WitnessRef → Cell → Bool} (checkSound : SoundCheck check)
    (stages : List (List RootTrace)) (incoming outgoing : List AddressedCell)
    (h : runChain check incoming stages = some outgoing) (p : Chart) (hp : good p)
    (start : Held incoming p) : LeafProof (chartPoint p) ∨ Held outgoing p := by
  induction stages generalizing incoming with
  | nil =>
      have he : incoming = outgoing := Option.some.inj h
      exact Or.inr (he ▸ start)
  | cons jobs later ih =>
      cases hStep : runStage check incoming jobs with
      | none => simp [runChain, hStep] at h
      | some next =>
          rcases stage_sound checkSound incoming jobs next hStep p hp start with w | hold
          · exact Or.inl w
          · exact ih next (by simpa [runChain, hStep] using h) hold

theorem chain_zero_holds {check : WitnessRef → Cell → Bool} (checkSound : SoundCheck check)
    (stages : List (List RootTrace)) (incoming : List AddressedCell)
    (h : runChain check incoming stages = some []) (p : Chart) (hp : good p)
    (start : Held incoming p) : LeafProof (chartPoint p) := by
  rcases chain_sound checkSound stages incoming [] h p hp start with w | impossible
  · exact w
  · simp [Held] at impossible

/-- Composition also admits the exact restriction and reflection steps that
are expressed as set inclusions. -/
abbrev Handoff (incoming outgoing : Set Chart) : Prop :=
  ∀ p ∈ incoming, good p → LeafProof (chartPoint p) ∨ p ∈ outgoing

theorem Handoff.trans {a b c : Set Chart} (hab : Handoff a b) (hbc : Handoff b c) :
    Handoff a c := by
  intro p hp goodP
  rcases hab p hp goodP with direct | remaining
  · exact Or.inl direct
  · exact hbc p remaining goodP

theorem Handoff.final {a : Set Chart} (h : Handoff a ∅) (p : Chart) (hp : p ∈ a)
    (goodP : good p) : LeafProof (chartPoint p) := by
  rcases h p hp goodP with direct | remaining
  · exact direct
  · simp at remaining

/-- Independent exclusion passes on the same closed entry leave the
intersection of their held regions. Shared boundaries are preserved. -/
theorem Handoff.meet {entry left right : Set Chart} (first : Handoff entry left)
    (second : Handoff entry right) : Handoff entry (left ∩ right) := by
  intro p hp goodP
  rcases first p hp goodP with done | hl
  · exact Or.inl done
  · rcases second p hp goodP with done | hr
    · exact Or.inl done
    · exact Or.inr ⟨hl, hr⟩

def pairwiseClips (keyFor : Key → Key → Key) (left right : List AddressedCell) : List AddressedCell :=
  left.flatMap (fun a => right.map (fun b => ⟨keyFor a.key b.key, intersection a.cell b.cell⟩))

theorem pairwiseClips_exact (keyFor : Key → Key → Key) (left right : List AddressedCell) (p : Chart) :
    Held (pairwiseClips keyFor left right) p ↔ Held left p ∧ Held right p := by
  constructor
  · rintro ⟨row, hRow, hp⟩
    unfold pairwiseClips at hRow
    obtain ⟨a, ha, him⟩ := List.mem_flatMap.mp hRow
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp him
    obtain ⟨insideA, insideB⟩ := (mem_intersection a.cell b.cell p).mp hp
    exact ⟨⟨a, ha, insideA⟩, ⟨b, hb, insideB⟩⟩
  · rintro ⟨⟨a, ha, insideA⟩, ⟨b, hb, insideB⟩⟩
    refine ⟨⟨keyFor a.key b.key, intersection a.cell b.cell⟩, ?_,
      (mem_intersection a.cell b.cell p).mpr ⟨insideA, insideB⟩⟩
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

theorem reflected_closed_regions {dense target accepted remaining : Set Chart}
    (denseInTarget : target ⊆ closure dense) (acceptedClosed : IsClosed accepted)
    (remainingClosed : IsClosed remaining) (covered : dense ⊆ accepted ∪ remaining) :
    target ⊆ accepted ∪ remaining :=
  Coverage.closed_cover denseInTarget (acceptedClosed.union remainingClosed) covered

end CompactCover
end BccSharp.Coulomb
