import BccSharp.TwoSite.GlobalCompact

set_option autoImplicit false

/-! Attainment of the actual capped defect. The neighbor set of a valid
two-site configuration inside the strict outer cutoff is finite, the proper
rotations form a compact set and every trial is continuous in the rotation.
Hence a capped defect below one is the value of an actual trial. -/

noncomputable section
open scoped BigOperators Topology

namespace BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.BravaisCover

theorem sq_add_le (a b : Vec) : sq (a + b) ≤ 2 * sq a + 2 * sq b := by
  unfold sq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (a i - b i)]

theorem sq_sub_le (a b : Vec) : sq (a - b) ≤ 2 * sq a + 2 * sq b := by
  have h := sq_add_le a (-b)
  have hn : sq (-b) = sq b := by simp [sq, Pi.neg_apply]
  rw [← sub_eq_add_neg, hn] at h
  exact h

/-- The nonzero lifts of a valid two-site configuration inside the outer
cutoff form a finite set. -/
theorem twoSite_neighbors_finite (q : TwoSite) (hq : q.Valid) : (neighbors q).Finite := by
  have hB : q.basis.det ≠ 0 := by rw [hq.1]; exact one_ne_zero
  let t := q.basis.mulVec q.offset
  have h1 := finite_lattice_sublevel q.basis hB ((13/10 : ℝ)^2) (by positivity)
  have h2 := finite_lattice_sublevel q.basis hB (2*(13/10 : ℝ)^2 + 2*sq t)
    (by have := sq_nonnegative t; positivity)
  apply (h1.union (h2.image (fun y => y + t))).subset
  rintro v ⟨hv, _, hlen⟩
  rw [zero_add] at hv
  rcases hv with hv | ⟨y, hy, rfl⟩
  · exact Or.inl ⟨hv, hlen.le⟩
  · refine Or.inr ⟨y, ⟨hy, ?_⟩, rfl⟩
    have h := sq_sub_le (y + t) t
    rw [add_sub_cancel_right] at h
    linarith

def properSet : Set Mat := {U | proper U}

theorem proper_entry_bound (U : Mat) (hU : proper U) (i j : Fin 3) :
    U i j ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := congrFun (congrFun hU.1 j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have hle : (U i j)^2 ≤ 1 := by
    rw [← h]
    have hs := Finset.single_le_sum (f := fun k => U k j * U k j)
      (fun k _ => mul_self_nonneg (U k j)) (Finset.mem_univ i)
    simpa [pow_two] using hs
  have ha := (sq_le_one_iff_abs_le_one (U i j)).mp hle
  exact ⟨(abs_le.mp ha).1, (abs_le.mp ha).2⟩

theorem properSet_closed : IsClosed properSet := by
  have h1 : IsClosed {U : Mat | U.transpose * U = 1} :=
    isClosed_eq ((continuous_id.matrix_transpose).matrix_mul continuous_id) continuous_const
  have h2 : IsClosed {U : Mat | U.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  exact h1.inter h2

theorem properSet_compact : IsCompact properSet := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin 3 =>
      Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)) : Set Mat) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  refine hbox.of_isClosed_subset properSet_closed ?_
  intro U hU i _ j _
  exact proper_entry_bound U hU i j

theorem defectTrial_continuous {Y : Set Vec} (σ : Fin 14 ↪ ↥Y) :
    Continuous (fun U : Mat => defectTrial U σ) := by
  unfold defectTrial
  apply Continuous.add _ continuous_const
  apply Continuous.mul continuous_const
  apply continuous_finsetSum _ (fun j _ => ?_)
  unfold sq
  apply continuous_finsetSum _ (fun i _ => ?_)
  apply Continuous.pow
  apply Continuous.sub continuous_const
  exact (continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)

theorem defectCandidates_compact {Y : Set Vec} (hY : Y.Finite) :
    IsCompact (defectCandidates Y) := by
  have : Finite ↥Y := hY.to_subtype
  have h : {c | ∃ U : Mat, proper U ∧ ∃ σ : Fin 14 ↪ ↥Y, c = defectTrial U σ} =
      ⋃ σ : Fin 14 ↪ ↥Y, (fun U => defectTrial U σ) '' properSet := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨U, hU, σ, rfl⟩
      exact ⟨σ, U, hU, rfl⟩
    · rintro ⟨σ, U, hU, rfl⟩
      exact ⟨U, hU, σ, rfl⟩
  unfold defectCandidates
  rw [h]
  exact (isCompact_iUnion (fun σ => properSet_compact.image (defectTrial_continuous σ))).insert 1

/-- A capped defect below one is attained by an actual trial. -/
theorem cappedDefect_attained {Y : Set Vec} (hY : Y.Finite) (h : cappedDefect Y < 1) :
    ∃ U : Mat, proper U ∧ ∃ σ : Fin 14 ↪ ↥Y, defectTrial U σ = cappedDefect Y := by
  have hmem : sInf (defectCandidates Y) ∈ defectCandidates Y :=
    (defectCandidates_compact hY).sInf_mem ⟨1, Set.mem_insert _ _⟩
  rcases Set.mem_insert_iff.mp hmem with h1 | ⟨U, hU, σ, hσ⟩
  · exact absurd h1 (ne_of_lt h)
  · exact ⟨U, hU, σ, hσ.symm⟩

end BccSharp.Coulomb.GlobalInputs
