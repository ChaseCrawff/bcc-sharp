import BccSharp.Lattice.TangentTables

set_option autoImplicit false

/-! Compact plans for the Lattice global forest of the tangent route.

A `Plan` lists only the split axes and, at each leaf, its kind and payload: a
reduction witness, the lattice indices and table positions of a tangent E1 leaf,
or a strain hand-off. `Plan.build` expands a plan into the `AddressedTree
TPayload` of `BccSharp.Lattice.TangentCover`: every cut is at the midpoint of the
current box, and every node reports the address and box that
`AddressedTree.check` derives, so the check compares them with themselves. The
leaf checks are those of `tangentGlobalCheck`, unchanged; plans are untrusted
data. `grid` is a `4^5` grid of `globalRoot`, and `rootCheck` is the forest
check of one grid cell. `checkAt_cut` splits the check of a cut into the checks
of its two halves, so that large roots can be checked one subtree at a time. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.TangentCover.Forest
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentE1
open BccSharp.Coulomb.BravaisCover.TangentCover

/-- The lattice index with code `49 (n₀+3) + 7 (n₁+3) + (n₂+3)`. -/
def decodeIdx (k : ℕ) : IntVec :=
  ![((k / 49 : ℕ) : ℤ) - 3, (((k / 7) % 7 : ℕ) : ℤ) - 3, ((k % 7 : ℕ) : ℤ) - 3]

/-- An E1 term: an index code and a table position. -/
def decodeTerm (x : ℕ × ℕ) : IntVec × ℕ := (decodeIdx x.1, x.2)

/-- A compact forest plan. -/
inductive Plan where
  | cut (axis : Fin 5) (lower upper : Plan)
  | redFull (code : ℕ)
  | redProjected (a d : ℤ)
  | e1 (dir dual : List (ℕ × ℕ))
  | sb
  | sf

/-- The midpoint of a box along an axis. -/
def mid (b : Rectangle) (axis : Fin 5) : ℚ := (b.lo axis + b.hi axis) / 2

/-- The lower or upper half of a box, cut at the midpoint. -/
def childBox (b : Rectangle) (axis : Fin 5) (upper : Bool) : Rectangle := split b axis (mid b axis) upper

/-- The addressed tree of a plan, rooted at the address `a` and the box `b`. -/
def Plan.build : Plan → Address → Rectangle → AddressedTree TPayload
  | .cut axis l u, a, b =>
    .cut a b axis (mid b axis) (l.build (a.child false) (childBox b axis false))
      (u.build (a.child true) (childBox b axis true))
  | .redFull m, a, b => .leaf a b .reducedFailure (.old (.reduction (.full (decodeIdx m))))
  | .redProjected x y, a, b => .leaf a b .reducedFailure (.old (.reduction (.projected x y)))
  | .e1 d u, a, b => .leaf a b .aboveFCC (.tangent (d.map decodeTerm) (u.map decodeTerm))
  | .sb, a, b => .leaf a b .bccStrain (.old .strainHandoff)
  | .sf, a, b => .leaf a b .fccStrain (.old .strainHandoff)

/-- The forest check of a plan at an address and a box, with the proved tables. -/
def Plan.checkAt (P : Plan) (a : Address) (b : Rectangle) : Bool :=
  (P.build a b).check (tangentGlobalCheck Tables.tables) a b

theorem exactBox_self (b : Rectangle) : exactBox b b = true :=
  decide_eq_true fun _ => ⟨rfl, rfl⟩

/-- A cut is checked by its face and its two halves. -/
theorem checkAt_cut (axis : Fin 5) (l u : Plan) (a : Address) (b : Rectangle)
    (face : decide (b.lo axis < mid b axis ∧ mid b axis < b.hi axis) = true)
    (lower : l.checkAt (a.child false) (childBox b axis false) = true)
    (upper : u.checkAt (a.child true) (childBox b axis true) = true) :
    (Plan.cut axis l u).checkAt a b = true := by
  unfold Plan.checkAt at lower upper ⊢
  simp only [Plan.build, AddressedTree.check, exactBox_self, decide_true, Bool.and_true, Bool.true_and]
  exact Bool.and_eq_true_iff.mpr ⟨face, Bool.and_eq_true_iff.mpr ⟨lower, upper⟩⟩

/-! ## The root grid -/

/-- A `4^5` grid of `globalRoot`: outer edges those of `globalRoot`; inner edges of the first
two coordinates on the grid `2^-12`, of the other three exact quarters. -/
def grid : Grid 4 :=
  ⟨![![7205759403792791 / 2 ^ 53, 3640 / 4096, 4004 / 4096, 4367 / 4096, 1300414392403231 / 2 ^ 50],
     ![6240370697243165 / 2 ^ 53, 3359 / 4096, 3879 / 4096, 4400 / 4096, 5410650294669431 / 2 ^ 52],
     ![0, 1 / 8, 1 / 4, 3 / 8, 1 / 2],
     ![0, 1 / 8, 1 / 4, 3 / 8, 1 / 2],
     ![-1 / 2, -1 / 4, 0, 1 / 4, 1 / 2]]⟩

theorem grid_check : grid.check globalRoot = true := by decide +kernel

/-- The address of a grid cell, keyed by its owner and suffix. -/
def rootAddress (owner : Fin 2 → Fin 4) (suffix : Fin 3 → Fin 4) : Address :=
  gridAddress .global (Fin.append owner suffix)

/-- The box of a grid cell, keyed by its owner and suffix. -/
def rootBox (owner : Fin 2 → Fin 4) (suffix : Fin 3 → Fin 4) : Rectangle :=
  grid.box (Fin.append owner suffix)

/-- The forest check of one grid cell. -/
def rootCheck (P : Plan) (owner : Fin 2 → Fin 4) (suffix : Fin 3 → Fin 4) : Bool :=
  P.checkAt (rootAddress owner suffix) (rootBox owner suffix)

theorem fin4_forall {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end BccSharp.Coulomb.BravaisCover.TangentCover.Forest
