import BccSharp.TwoSite.BravaisCover

set_option autoImplicit false

/-! Closed-grid and addressed-forest checker for Lattice. Every subtree
is tied to the exact box derived from its root and shared cuts. The owner
split enumerates keys mathematically; reported box and owner counts are
diagnostics. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage

inductive Reference where
  | bcc | fcc
  deriving DecidableEq, Repr

inductive Family where
  | global
  | strain (ref : Reference)
  | localBall (ref : Reference)
  deriving DecidableEq, Repr

structure Address where
  family : Family
  root : List ℕ
  path : List Bool
  deriving DecidableEq, Repr

def Address.child (a : Address) (upper : Bool) : Address :=
  { a with path := a.path ++ [upper] }

def exactBox (a b : Rectangle) : Bool :=
  decide (∀ i, a.lo i=b.lo i ∧ a.hi i=b.hi i)

theorem exactBox_sound {a b : Rectangle} (h : exactBox a b = true) : a=b := by
  have he : ∀ i, a.lo i=b.lo i ∧ a.hi i=b.hi i := of_decide_eq_true h
  cases a
  cases b
  congr
  · exact funext fun i => (he i).1
  · exact funext fun i => (he i).2

/-- The source address and endpoints are repeated in a decoded row. A row
from another owner or chart cannot discharge the current parent. -/
inductive AddressedTree (Witness : Type) where
  | cut (a : Address) (reportedBox : Rectangle) (axis : Fin 5) (face : ℚ)
      (lower upper : AddressedTree Witness)
  | leaf (a : Address) (reportedBox : Rectangle) (route : Route) (witness : Witness)

def AddressedTree.check {W : Type} (test : Address → Route → W → Rectangle → Bool) :
    AddressedTree W → Address → Rectangle → Bool
  | .cut reported got axis face lower upper, key, fromParent =>
      (decide (reported=key) && exactBox got fromParent) &&
        (decide (fromParent.lo axis < face ∧ face < fromParent.hi axis) &&
          (lower.check test (key.child false) (split fromParent axis face false) &&
           upper.check test (key.child true) (split fromParent axis face true)))
  | .leaf reported got route w, key, fromParent =>
      (decide (reported=key) && exactBox got fromParent) && test key route w fromParent

def AddressedSound {W : Type} (test : Address → Route → W → Rectangle → Bool)
    (eligible closed : Point → Prop) : Prop :=
  ∀ a route w b, test a route w b = true → ∀ p, b.Mem p → eligible p → closed p

theorem AddressedTree.sound {W : Type} {test : Address → Route → W → Rectangle → Bool}
    {eligible closed : Point → Prop} (hTest : AddressedSound test eligible closed)
    (t : AddressedTree W) (a : Address) (b : Rectangle) (ok : t.check test a b = true)
    (p : Point) (hp : b.Mem p) (he : eligible p) : closed p := by
  induction t generalizing a b with
  | leaf reported got route w =>
      exact hTest a route w b (Bool.and_eq_true_iff.mp ok).2 p hp he
  | cut reported got axis face left right ihLeft ihRight =>
      have hBoth := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).2).2
      rcases split_covers b axis face p hp with hL | hR
      · exact ihLeft _ _ hBoth.1 hL
      · exact ihRight _ _ hBoth.2 hR

structure Grid (count : ℕ) where
  edge : Fin 5 → Fin (count+1) → ℚ

def Grid.box {count : ℕ} (g : Grid count) (key : Fin 5 → Fin count) : Rectangle :=
  ⟨fun i => g.edge i (key i).castSucc, fun i => g.edge i (key i).succ⟩

def Grid.outer {count : ℕ} (g : Grid count) : Rectangle :=
  ⟨fun i => g.edge i 0, fun i => g.edge i (Fin.last count)⟩

def Grid.check {count : ℕ} (g : Grid count) (root : Rectangle) : Bool :=
  exactBox g.outer root &&
    decide (∀ i : Fin 5, ∀ j : Fin count, g.edge i j.castSucc < g.edge i j.succ)

private theorem adjacent_cover (edge : ℕ → ℝ) (x : ℝ) (start : edge 0 ≤ x)
    (count : ℕ) (positive : 0 < count) (stop : x ≤ edge count) :
    ∃ k < count, edge k ≤ x ∧ x ≤ edge (k+1) := by
  induction count with
  | zero => omega
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨0, by omega, start, stop⟩
    · by_cases hx : x ≤ edge n
      · obtain ⟨k,hk,hlo,hhi⟩ := ih (by omega) hx
        exact ⟨k, by omega, hlo, hhi⟩
      · exact ⟨n, by omega, (lt_of_not_ge hx).le, stop⟩

theorem Grid.covers {count : ℕ} (g : Grid count) (positive : 0 < count)
    (root : Rectangle) (ok : g.check root = true) (p : Point) (hp : root.Mem p) :
    ∃ key, (g.box key).Mem p := by
  classical
  have hOuter := exactBox_sound (Bool.and_eq_true_iff.mp ok).1
  rw [← hOuter] at hp
  have hChoose (i : Fin 5) : ∃ j : Fin count,
      (g.edge i j.castSucc : ℝ) ≤ p i ∧ p i ≤ g.edge i j.succ := by
    let xs (k : ℕ) : ℝ := if h : k < count+1 then (g.edge i ⟨k,h⟩ : ℝ) else 0
    have hlo : xs 0 ≤ p i := by simpa [xs,Grid.outer] using (hp i).1
    have hhi : p i ≤ xs count := by simpa [xs,Grid.outer,Fin.last] using (hp i).2
    obtain ⟨k,hk,ha,hb⟩ := adjacent_cover xs (p i) hlo count positive hhi
    refine ⟨⟨k,hk⟩, ?_, ?_⟩
    · have hk' : k ≤ count := hk.le
      simpa [xs,hk',Fin.castSucc] using ha
    · simpa [xs,hk,Fin.succ] using hb
  choose key h using hChoose
  exact ⟨key,h⟩

def gridAddress {count : ℕ} (kind : Family) (key : Fin 5 → Fin count) : Address :=
  ⟨kind, List.ofFn (fun i : Fin 5 => (key i).val), []⟩

/-- Finitary key decomposition used for deterministic owners. Omitting
any two-digit owner or any suffix prevents constructing the premise. -/
theorem owner_suffix_covers {count : ℕ} (key : Fin 5 → Fin count) :
    ∃ owner : Fin 2 → Fin count, ∃ suffix : Fin 3 → Fin count,
      Fin.append owner suffix = key := by
  exact ⟨fun i => key (Fin.castAdd 3 i), fun j => key (Fin.natAdd 2 j), by
    funext i
    fin_cases i <;> rfl⟩

theorem addressed_grid_sound {count : ℕ} {W : Type} {eligible closed : Point → Prop}
    (g : Grid count) (positive : 0 < count) (root : Rectangle) (gridOK : g.check root = true)
    (kind : Family) (test : Address → Route → W → Rectangle → Bool)
    (testSound : AddressedSound test eligible closed)
    (forest : (Fin 2 → Fin count) → (Fin 3 → Fin count) → AddressedTree W)
    (checked : ∀ owner suffix, (forest owner suffix).check test
      (gridAddress kind (Fin.append owner suffix)) (g.box (Fin.append owner suffix)) = true)
    (p : Point) (hp : root.Mem p) (he : eligible p) : closed p := by
  obtain ⟨key,hKey⟩ := g.covers positive root gridOK p hp
  obtain ⟨owner,suffix,rfl⟩ := owner_suffix_covers key
  exact (forest owner suffix).sound testSound _ _ (checked owner suffix) p hKey he

structure RootRow (W : Type) where
  key : Address
  tree : AddressedTree W

def checkRootRows {W : Type} (test : Address → Route → W → Rectangle → Bool)
    (rows : List (RootRow W)) (a : Address) (b : Rectangle) : Bool :=
  match rows.find? (fun row => decide (row.key=a)) with
  | none => false
  | some row => row.tree.check test a b

theorem checkRootRows_sound {W : Type} {test : Address → Route → W → Rectangle → Bool}
    {eligible closed : Point → Prop} (hTest : AddressedSound test eligible closed)
    (rows : List (RootRow W)) (a : Address) (b : Rectangle)
    (checked : checkRootRows test rows a b = true) (p : Point) (hp : b.Mem p) (he : eligible p) :
    closed p := by
  unfold checkRootRows at checked
  split at checked
  · contradiction
  next row _ => exact row.tree.sound hTest a b checked p hp he

theorem addressed_rows_cover {count : ℕ} {W : Type} {eligible closed : Point → Prop}
    (g : Grid count) (pos : 0 < count) (root : Rectangle) (ok : g.check root = true)
    (kind : Family) (test : Address → Route → W → Rectangle → Bool)
    (testSound : AddressedSound test eligible closed)
    (rows : (Fin 2 → Fin count) → List (RootRow W))
    (checked : ∀ (owner : Fin 2 → Fin count) (suffix : Fin 3 → Fin count),
      checkRootRows test (rows owner)
      (gridAddress kind (Fin.append owner suffix)) (g.box (Fin.append owner suffix)) = true)
    (p : Point) (hp : root.Mem p) (he : eligible p) : closed p := by
  obtain ⟨key,hKey⟩ := g.covers pos root ok p hp
  obtain ⟨owner,suffix,rfl⟩ := owner_suffix_covers key
  exact checkRootRows_sound testSound _ _ _ (checked owner suffix) p hKey he

/-- Exact subtree stitching for the large single-root strain trees. A
fragment can close a spine terminal only at its full address and box. -/
def fragmentCheck {W : Type} (test : Address → Route → W → Rectangle → Bool)
    (fragments : List (RootRow W)) (a : Address) (route : Route) (claim : Address)
    (b : Rectangle) : Bool :=
  decide (route = .checkedFragment ∧ a=claim) && checkRootRows test fragments a b

theorem fragmentCheck_sound {W : Type} {test : Address → Route → W → Rectangle → Bool}
    {eligible closed : Point → Prop} (hTest : AddressedSound test eligible closed)
    (fragments : List (RootRow W)) :
    AddressedSound (fragmentCheck test fragments) eligible closed := by
  intro a route claim b ok p hp he
  exact checkRootRows_sound hTest fragments a b (Bool.and_eq_true_iff.mp ok).2 p hp he

theorem spine_sound {W : Type} {test : Address → Route → W → Rectangle → Bool}
    {eligible closed : Point → Prop} (hTest : AddressedSound test eligible closed)
    (fragments : List (RootRow W)) (spine : AddressedTree Address) (a : Address) (b : Rectangle)
    (checked : spine.check (fragmentCheck test fragments) a b = true)
    (p : Point) (hp : b.Mem p) (he : eligible p) : closed p :=
  spine.sound (fragmentCheck_sound hTest fragments) a b checked p hp he

end BccSharp.Coulomb.BravaisCover
