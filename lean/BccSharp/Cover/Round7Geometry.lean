import Init.Data.Rat.Basic
import Lean.Elab.Tactic.Decide
import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Simpa
import Lean.Elab.Tactic.Rewrite

set_option autoImplicit false

/-! Continuation round-seven fixture. This file checks tree structure and binds
literal receipt rows to local paths. The parent endpoints and analytic validity
of the five recorded margins are explicit inputs to subsequent work. -/

namespace Round7Geometry

abbrev Axis := Fin 8

structure Box where
  lo : Axis → Rat
  hi : Axis → Rat

def Box.mem {α : Type} [LE α] (b : Box) (lift : Rat → α) (p : Axis → α) : Prop :=
  ∀ i, lift (b.lo i) ≤ p i ∧ p i ≤ lift (b.hi i)

def Box.half (b : Box) (axis : Axis) (upper : Bool) : Box where
  lo i := if i = axis ∧ upper = true then (b.lo i + b.hi i) / 2 else b.lo i
  hi i := if i = axis ∧ upper = false then (b.lo i + b.hi i) / 2 else b.hi i

theorem mem_some_half {α : Type} [LE α] (total : ∀ x y : α, x ≤ y ∨ y ≤ x)
    (lift : Rat → α) (p : Axis → α) (b : Box) (axis : Axis) (hp : b.mem lift p) :
    (b.half axis false).mem lift p ∨ (b.half axis true).mem lift p := by
  rcases total (p axis) (lift ((b.lo axis + b.hi axis) / 2)) with h | h
  · apply Or.inl
    intro i
    rcases Decidable.em (i = axis) with same | same
    · subst i
      simpa [Box.half] using And.intro (hp axis).1 h
    · simpa [Box.half, same] using hp i
  · apply Or.inr
    intro i
    rcases Decidable.em (i = axis) with same | same
    · subst i
      simpa [Box.half] using And.intro h (hp axis).2
    · simpa [Box.half, same] using hp i

theorem mem_both_on_split {α : Type} [LE α] (refl : ∀ x : α, x ≤ x)
    (lift : Rat → α) (p : Axis → α) (b : Box) (axis : Axis) (hp : b.mem lift p)
    (onSplit : p axis = lift ((b.lo axis + b.hi axis) / 2)) :
    (b.half axis false).mem lift p ∧ (b.half axis true).mem lift p := by
  have toMid : p axis ≤ lift ((b.lo axis + b.hi axis) / 2) := by
    rw [← onSplit]
    exact refl _
  have fromMid : lift ((b.lo axis + b.hi axis) / 2) ≤ p axis := by
    rw [← onSplit]
    exact refl _
  constructor
  · intro i
    rcases Decidable.em (i = axis) with same | same
    · subst i
      simpa [Box.half] using And.intro (hp axis).1 toMid
    · simpa [Box.half, same] using hp i
  · intro i
    rcases Decidable.em (i = axis) with same | same
    · subst i
      simpa [Box.half] using And.intro fromMid (hp axis).2
    · simpa [Box.half, same] using hp i

inductive Tree where
  | terminal
  | split (axis : Axis) (left right : Tree)

def digit (axis : Axis) (upper : Bool) : Nat := 2 * axis.val + (if upper then 1 else 0)

def Tree.paths : Tree → List (List Nat)
  | .terminal => [[]]
  | .split axis left right =>
      (left.paths.map (fun path => digit axis false :: path)) ++
      (right.paths.map (fun path => digit axis true :: path))

/-- Bind a terminal predicate to both the exact split path and the derived box. -/
def Tree.Valid (leaf : List Nat → Box → Prop) (b : Box) : Tree → Prop
  | .terminal => leaf [] b
  | .split axis left right =>
      left.Valid (fun path => leaf (digit axis false :: path)) (b.half axis false) ∧
      right.Valid (fun path => leaf (digit axis true :: path)) (b.half axis true)

theorem Tree.sound {α : Type} [LE α] (total : ∀ x y : α, x ≤ y ∨ y ≤ x)
    (lift : Rat → α) (p : Axis → α) (result : Prop) (tree : Tree) (b : Box)
    (leaf : List Nat → Box → Prop) (checked : tree.Valid leaf b)
    (soundLeaf : ∀ path cell, leaf path cell → cell.mem lift p → result)
    (hp : b.mem lift p) : result := by
  induction tree generalizing b leaf with
  | terminal => exact soundLeaf [] b checked hp
  | split axis left right leftIH rightIH =>
      have both : left.Valid (fun path => leaf (digit axis false :: path)) (b.half axis false) ∧
          right.Valid (fun path => leaf (digit axis true :: path)) (b.half axis true) := checked
      rcases mem_some_half total lift p b axis hp with lower | upper
      · exact leftIH _ _ both.1 (fun path => soundLeaf (digit axis false :: path)) lower
      · exact rightIH _ _ both.2 (fun path => soundLeaf (digit axis true :: path)) upper

structure ParentAddress where
  batch : String
  batchPayloadSha256 : String
  rootSlot : Nat
  heldPath : List Nat
  deriving DecidableEq

structure RotationProposal where
  selector : Nat
  halfClass : List Int
  quaternionNumerator : List Int
  quaternionScale : Nat
  deriving DecidableEq

/-- All five rows are J. `supportPath` may differ from the leaf path. -/
structure JointRow where
  path : List Nat
  supportPath : List Nat
  rotation : RotationProposal
  marginNumerator : Nat
  marginDenominator : Nat
  deriving DecidableEq

def previousBatchHash : String :=
  "2c6e192c69f4308b29564115c28353ec39e4c5dcb66c7fa96a93f03f0d94844c"

def parent0 : ParentAddress :=
  ⟨"666291-0000020", previousBatchHash, 11, [3, 13, 9, 0, 13, 11, 3, 4, 6]⟩

def parent1 : ParentAddress :=
  ⟨"666291-0000020", previousBatchHash, 11, [3, 13, 9, 0, 13, 11, 3, 4, 7]⟩

def finalBatchHash : String :=
  "c2c9d6404e4f0788d7892b6e1f46e5dbf3179c60b10d02712ba0ba3955583b50"

def checkSource (batch digest : String) (parents : List ParentAddress) : Bool :=
  decide (batch = "666291-0000000" ∧ digest = finalBatchHash ∧ parents = [parent0, parent1])

def tree0 : Tree := .split 0 .terminal (.split 6 .terminal .terminal)
def tree1 : Tree := .split 0 .terminal .terminal

def rotation0 : RotationProposal := ⟨0, [1, 1, 1], [-5701126, 2952578, -7127435, 13764233], 4096⟩
def rotation1 : RotationProposal := ⟨0, [1, 1, 1], [-5701259, 2952835, -7127328, 13764177], 4096⟩

def marginDenominator : Nat := 182687704666362864775460604089535377456991567872

def rows0 : List JointRow :=
  [ ⟨[0], [0], rotation0, 9184082202354214961966061469149348193, marginDenominator⟩,
    ⟨[1, 12], [1, 12], rotation0, 128176877421327491505275969358895169889, marginDenominator⟩,
    ⟨[1, 13], [1], rotation0, 99667074214364308576623271142730679775, marginDenominator⟩ ]

def rows1 : List JointRow :=
  [ ⟨[0], [0], rotation1, 97496591693990964059518152926112300313, marginDenominator⟩,
    ⟨[1], [1], rotation1, 59379201183614030534832522901626210885, marginDenominator⟩ ]

def checkRows (tree : Tree) (rows : List JointRow) : Bool :=
  decide (rows.map JointRow.path = tree.paths) &&
    rows.all (fun row => row.supportPath.isPrefixOf row.path &&
      decide (0 < row.marginNumerator ∧ 0 < row.marginDenominator))

theorem fixture_paths : checkRows tree0 rows0 = true ∧ checkRows tree1 rows1 = true := by
  decide

theorem missing_child_rejected : checkRows tree0 (rows0.take 2) = false := by
  decide

theorem misaddressed_row_rejected : checkRows tree0 (rows0.reverse) = false := by
  decide

theorem parent_addresses_distinct : parent0 ≠ parent1 := by
  decide

theorem source_order_checked :
    checkSource "666291-0000000" finalBatchHash [parent0, parent1] = true ∧
    checkSource "666291-0000000" finalBatchHash [parent1, parent0] = false := by
  decide

/-- Arithmetic implementation supplies this predicate at each derived box.
An imported margin sign cannot establish the predicate on its own. -/
def BoundLeaf (rows : List JointRow) (certifies : JointRow → Box → Prop)
    (path : List Nat) (cell : Box) : Prop :=
  ∃ row ∈ rows, row.path = path ∧ certifies row cell

theorem round7_covers {α : Type} [LE α] (total : ∀ x y : α, x ≤ y ∨ y ≤ x)
    (lift : Rat → α) (p : Axis → α) (result : Prop) (b₀ b₁ : Box)
    (certifies : ParentAddress → JointRow → Box → Prop)
    (closed0 : tree0.Valid (BoundLeaf rows0 (certifies parent0)) b₀)
    (closed1 : tree1.Valid (BoundLeaf rows1 (certifies parent1)) b₁)
    (sound : ∀ parent row cell, certifies parent row cell → cell.mem lift p → result)
    (h : b₀.mem lift p ∨ b₁.mem lift p) : result := by
  cases h with
  | inl hp =>
      refine tree0.sound total lift p result b₀ _ closed0 ?_ hp
      intro path cell hleaf hmem
      obtain ⟨row, _, _, hcert⟩ := hleaf
      exact sound parent0 row cell hcert hmem
  | inr hp =>
      refine tree1.sound total lift p result b₁ _ closed1 ?_ hp
      intro path cell hleaf hmem
      obtain ⟨row, _, _, hcert⟩ := hleaf
      exact sound parent1 row cell hcert hmem

#print axioms fixture_paths
#print axioms missing_child_rejected
#print axioms misaddressed_row_rejected
#print axioms parent_addresses_distinct
#print axioms source_order_checked
#print axioms mem_both_on_split
#print axioms round7_covers

end Round7Geometry
