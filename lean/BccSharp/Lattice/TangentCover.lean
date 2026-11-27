import BccSharp.Lattice.TangentE1
import BccSharp.Lattice.LocalBalls

set_option autoImplicit false

/-! The Lattice global forest with tangent E1 leaves.

Tangents are certified once, in two tables (`TTree`) of anchored tangent lines,
one per kernel. An E1 leaf lists its lattice indices with table positions; the
leaf check looks the tangents up, sums them into an aggregate and runs the
32-corner check of `BccSharp.Lattice.TangentE1`. Every other leaf keeps its existing
payload and checker (`globalWithHandoffsCheck`). `latticeCase_from_tangent_forest`
then gives `LatticeCase` from a grid of any size, the two tables, the forest checks
and the two strain-atlas checks; the local balls are proved (`localBalls`). -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.TangentCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentE1
open BccSharp.Coulomb.CompactCover

/-! ## Tangent tables -/

/-- A binary tree of anchored tangents; leaves at depth `h` are indexed from the left. -/
inductive TTree where
  | tip
  | leaf (anchor : ℚ) (t : Stage2.Tangent)
  | node (l r : TTree)

def TTree.get : TTree → ℕ → ℕ → Option Stage2.Tangent
  | .leaf _ t, 0, _ => some t
  | .node l r, h + 1, k => if k < 2 ^ h then l.get h k else r.get h (k - 2 ^ h)
  | _, _, _ => none

def TTree.Valid (kind : KernelKind) : TTree → Prop
  | .tip => True
  | .leaf _ t => ValidTangent kind t
  | .node l r => l.Valid kind ∧ r.Valid kind

theorem TTree.get_valid (kind : KernelKind) :
    ∀ (t : TTree), t.Valid kind → ∀ (h k : ℕ) (r : Stage2.Tangent), t.get h k = some r → ValidTangent kind r
  | .tip, _, h, k, r, hg => by cases h <;> simp [TTree.get] at hg
  | .leaf _ t, hv, h, k, r, hg => by
    cases h with
    | zero =>
      simp only [TTree.get, Option.some.injEq] at hg
      exact hg ▸ hv
    | succ h => simp [TTree.get] at hg
  | .node l r', hv, h, k, r, hg => by
    cases h with
    | zero => simp [TTree.get] at hg
    | succ h =>
      simp only [TTree.get] at hg
      split_ifs at hg
      · exact TTree.get_valid kind l hv.1 h k r hg
      · exact TTree.get_valid kind r' hv.2 h _ r hg

def tangentEq (a b : Stage2.Tangent) : Bool := decide (a.intercept = b.intercept ∧ a.penalty = b.penalty)

/-- Every leaf's tangent is the fast tangent at its anchor. -/
def TTree.check (kind : KernelKind) : TTree → Bool
  | .tip => true
  | .leaf x t => match fastTangent kind x with
    | some u => tangentEq u t
    | none => false
  | .node l r => l.check kind && r.check kind

theorem TTree.check_valid (kind : KernelKind) : ∀ (t : TTree), t.check kind = true → t.Valid kind
  | .tip, _ => trivial
  | .leaf x t, h => by
    simp only [TTree.check] at h
    split at h
    next u hu =>
      have e : u.intercept = t.intercept ∧ u.penalty = t.penalty := of_decide_eq_true h
      have hv := fastTangent_sound kind x u hu
      cases u
      cases t
      simp only at e
      obtain ⟨rfl, rfl⟩ := e
      exact hv
    next => contradiction
  | .node l r, h => by
    simp only [TTree.check, Bool.and_eq_true] at h
    exact ⟨TTree.check_valid kind l h.1, TTree.check_valid kind r h.2⟩

/-- A certified pair of tables of height `height`. -/
structure Tables where
  height : ℕ
  half : TTree
  one : TTree

def Tables.Valid (T : Tables) : Prop := T.half.Valid .half ∧ T.one.Valid .one

/-! ## Tangent E1 leaves -/

def tableTerms (t : TTree) (h : ℕ) : List (IntVec × ℕ) → Option (List Term)
  | [] => some []
  | x :: rest =>
    match t.get h x.2, tableTerms t h rest with
    | some u, some us => some ((x.1, u) :: us)
    | _, _ => none

theorem tableTerms_sound (kind : KernelKind) (t : TTree) (hv : t.Valid kind) (h : ℕ)
    (l : List (IntVec × ℕ)) (ts : List Term) (e : tableTerms t h l = some ts) :
    ts.map Prod.fst = l.map Prod.fst ∧ ∀ x ∈ ts, ValidTangent kind x.2 := by
  induction l generalizing ts with
  | nil =>
    simp only [tableTerms, Option.some.injEq] at e
    subst e
    simp
  | cons x rest ih =>
    simp only [tableTerms] at e
    split at e
    next u us hu hus =>
      simp only [Option.some.injEq] at e
      subst e
      obtain ⟨e', v⟩ := ih us hus
      refine ⟨by simp [e'], ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact TTree.get_valid kind t hv h x.2 u hu
      · exact v y hy
    next => contradiction

/-- An E1 leaf: direct and dual lattice indices, each with a table position. -/
def tangentLeafCheck (T : Tables) (dir dual : List (IntVec × ℕ)) (b : Rectangle) : Bool :=
  ((sortedStrict (dir.map Prod.fst) && sortedStrict (dual.map Prod.fst)) &&
    ((dir.all fun x => nonzeroB x.1) && (dual.all fun x => nonzeroB x.1))) &&
  match tableTerms T.half T.height dir, tableTerms T.one T.height dual with
  | some d, some u => leafCheck (TermSet.mk d u).aggregate b
  | _, _ => false

theorem tangentLeafCheck_sound (T : Tables) (hT : T.Valid) (dir dual : List (IntVec × ℕ))
    (b : Rectangle) (ok : tangentLeafCheck T dir dual b = true) (p : Point) (hp : b.Mem p) :
    Sharp (primitiveChart p) := by
  unfold tangentLeafCheck at ok
  obtain ⟨hstruct, hleaf⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hsort, hnz⟩ := Bool.and_eq_true_iff.mp hstruct
  obtain ⟨sd, su⟩ := Bool.and_eq_true_iff.mp hsort
  obtain ⟨zd, zu⟩ := Bool.and_eq_true_iff.mp hnz
  split at hleaf
  next d u hd hu =>
    obtain ⟨ed, vd⟩ := tableTerms_sound .half T.half hT.1 T.height dir d hd
    obtain ⟨eu, vu⟩ := tableTerms_sound .one T.one hT.2 T.height dual u hu
    have valid : (TermSet.mk d u).Valid := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · show (d.map Prod.fst).Nodup
        rw [ed]; exact sortedStrict_nodup _ sd
      · show (u.map Prod.fst).Nodup
        rw [eu]; exact sortedStrict_nodup _ su
      · intro x hx
        refine ⟨?_, vd x hx⟩
        have hmem : x.1 ∈ dir.map Prod.fst := ed ▸ List.mem_map_of_mem hx
        obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
        rw [← hyx]
        exact nonzeroB_sound _ (List.all_eq_true.mp zd y hy)
      · intro x hx
        refine ⟨?_, vu x hx⟩
        have hmem : x.1 ∈ dual.map Prod.fst := eu ▸ List.mem_map_of_mem hx
        obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
        rw [← hyx]
        exact nonzeroB_sound _ (List.all_eq_true.mp zu y hy)
    exact leafCheck_sound _ ⟨_, valid, rfl⟩ b hleaf p hp
  next => contradiction

/-! ## The global forest -/

/-- An existing global payload, or a tangent E1 leaf. -/
inductive TPayload where
  | old (w : Payload)
  | tangent (dir dual : List (IntVec × ℕ))

def tangentGlobalCheck (T : Tables) (a : Address) (r : Route) (w : TPayload) (b : Rectangle) : Bool :=
  match w with
  | .old w => globalWithHandoffsCheck a r w b
  | .tangent dir dual => decide (a.family = .global ∧ r = .aboveFCC) && tangentLeafCheck T dir dual b

theorem tangentGlobalCheck_sound (T : Tables) (hT : T.Valid) (atlas : Reference → AtlasRows)
    (checked : ∀ ref, (atlas ref).check ref = true) (ballProof : ∀ ref, NonzeroLocalStrain ref) :
    AddressedSound (tangentGlobalCheck T) reduced (fun p => Sharp (primitiveChart p)) := by
  intro a r w b ok p hp live
  cases w with
  | old w => exact globalWithHandoffsCheck_sound atlas checked ballProof a r w b ok p hp live
  | tangent dir dual =>
    exact tangentLeafCheck_sound T hT dir dual b (Bool.and_eq_true_iff.mp ok).2 p hp

/-- `LatticeCase` from a checked global grid forest of any size with tangent E1 leaves,
two certified tangent tables and the two checked strain atlases. -/
theorem latticeCase_from_tangent_forest {count : ℕ} (positive : 0 < count) (g : Grid count)
    (gOK : g.check globalRoot = true) (T : Tables) (hT : T.Valid)
    (forest : (Fin 2 → Fin count) → (Fin 3 → Fin count) → AddressedTree TPayload)
    (checked : ∀ owner suffix, (forest owner suffix).check (tangentGlobalCheck T)
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix)) = true)
    (atlas : Reference → AtlasRows) (atlasOK : ∀ ref, (atlas ref).check ref = true) : LatticeCase := by
  intro B hB
  rcases KZ.physical_escape_or_root B hB with strict | ⟨r, root⟩
  · exact strict
  · apply r.transport
    exact addressed_grid_sound g positive globalRoot gOK .global (tangentGlobalCheck T)
      (tangentGlobalCheck_sound T hT atlas atlasOK localBalls) forest checked r.point
      (globalRoot_contains r.point root) r.reducedPoint

end BccSharp.Coulomb.BravaisCover.TangentCover
