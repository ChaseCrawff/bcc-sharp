module

public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Exact box subdivision and the closed-cover boundary argument. These rules
do not infer strict positivity at boundary points from a limit of positive
matrices: positivity must hold on each retained *closed* box. -/

@[expose] public section

namespace BccSharp.Coverage

structure Box (n : ℕ) where
  lo : Fin n → ℚ
  hi : Fin n → ℚ

namespace Box

def Mem {n : ℕ} (b : Box n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (b.lo i : ℝ) ≤ x i ∧ x i ≤ (b.hi i : ℝ)

def child {n : ℕ} (b : Box n) (s : Fin n → Bool) : Box n where
  lo i := if s i then (b.lo i + b.hi i) / 2 else b.lo i
  hi i := if s i then b.hi i else (b.lo i + b.hi i) / 2

theorem mem_child_subset {n : ℕ} (b : Box n) (s : Fin n → Bool) (x : Fin n → ℝ)
    (hb : ∀ i, b.lo i ≤ b.hi i) (h : (b.child s).Mem x) : b.Mem x := by
  intro i
  have hi := h i
  have hi' : (b.lo i : ℝ) ≤ b.hi i := by exact_mod_cast hb i
  simp only [child] at hi
  split_ifs at hi <;> push_cast at hi <;> constructor <;> linarith

theorem mem_some_child {n : ℕ} (b : Box n) (x : Fin n → ℝ) (h : b.Mem x) :
    ∃ s : Fin n → Bool, (b.child s).Mem x := by
  classical
  refine ⟨fun i => decide (((b.lo i : ℝ) + b.hi i) / 2 ≤ x i), fun i => ?_⟩
  have hi := h i
  simp only [child]
  split_ifs with hm <;> push_cast <;> simp_all only [decide_eq_true_eq, not_le]
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, hm.le⟩

theorem isClosed {n : ℕ} (b : Box n) : IsClosed {x | b.Mem x} := by
  have heq : {x | b.Mem x} = ⋂ i, {x : Fin n → ℝ | (b.lo i : ℝ) ≤ x i ∧ x i ≤ (b.hi i : ℝ)} := by
    ext x
    simp [Mem]
  rw [heq]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)

end Box

/-- Boundary coverage transfers through a closed union of successful boxes.
The premise is about a closed covering set, not the open cone of PD matrices. -/
theorem closed_cover {X : Type*} [TopologicalSpace X] {U W C : Set X}
    (hW : W ⊆ closure U) (hC : IsClosed C) (hU : U ⊆ C) : W ⊆ C :=
  hW.trans (closure_minimal hU hC)

/-- Once coverage is known, every point receives a certificate for a closed
region containing it. This rule also allows the punctured Taylor ball. -/
theorem assemble {X ι : Type*} {W : Set X} (region : ι → Set X) (P : X → Prop)
    (cover : ∀ x ∈ W, ∃ i, x ∈ region i) (cert : ∀ i x, x ∈ region i → P x) :
    ∀ x ∈ W, P x := by
  intro x hx
  obtain ⟨i, hi⟩ := cover x hx
  exact cert i x hi

end BccSharp.Coverage
