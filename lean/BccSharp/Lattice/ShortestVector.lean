import BccSharp.Lattice.FccDefect

set_option autoImplicit false

/-! First KZ step in an arbitrary full-rank basis. The minimizer is
chosen from a proved finite ambient sublevel and is primitive. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover

theorem linearImage_ne_zero (B : Mat) (hB : B.det≠0) (n : IntVec) (hn : n≠0) :
    linearImage B n≠0 := by
  intro h
  apply hn
  apply (periodIndices B hB).injective
  apply Subtype.ext
  change linearImage B n=linearImage B 0
  have h0 : linearImage B 0 = 0 := by
    show B.mulVec (castVec 0) = 0
    rw [castVec_zero, Matrix.mulVec_zero]
  rw [h0]
  exact h

theorem shortest_lattice_index (B : Mat) (hB : B.det≠0) :
    ∃ n : IntVec, n≠0 ∧ ∀ m : IntVec, m≠0 → sq (linearImage B n)≤ sq (linearImage B m) := by
  classical
  let e : IntVec := ![1,0,0]
  let x := linearImage B e
  let M := sq x
  let S : Set Vec := {y | y∈lattice B ∧ sq y≤M}
  have hf : S.Finite := finite_lattice_sublevel B hB M (sq_nonnegative x)
  let s := hf.toFinset.erase 0
  have hmem (y : Vec) : y∈s ↔ y≠0 ∧ y∈lattice B ∧ sq y≤M := by
    simp [s,S,Finset.mem_erase]
  have hxe : x≠0 := linearImage_ne_zero B hB e (by decide)
  have hx : x∈s := (hmem x).2 ⟨hxe,⟨e,rfl⟩,le_rfl⟩
  obtain ⟨y,hy,least⟩ := Finset.exists_min_image s sq ⟨x,hx⟩
  obtain ⟨hne,⟨n,rfl⟩,bound⟩ := (hmem y).1 hy
  refine ⟨n,?_,?_⟩
  · rintro rfl
    apply hne
    show B.mulVec (castVec 0) = 0
    rw [castVec_zero, Matrix.mulVec_zero]
  · intro m hm
    let z := linearImage B m
    by_cases hz : sq z≤M
    · exact least z ((hmem z).2 ⟨linearImage_ne_zero B hB m hm,⟨m,rfl⟩,hz⟩)
    · exact bound.trans (le_of_not_ge hz)

theorem shortest_index_primitive (B : Mat) (hB : B.det≠0) (n : IntVec) (hn : n≠0)
    (least : ∀ m : IntVec, m≠0 → sq (linearImage B n)≤ sq (linearImage B m))
    (k : ℤ) (hk : 1 < |k|) (m : IntVec) : n≠fun i => k*m i := by
  intro same
  have hm : m≠0 := by
    rintro rfl
    apply hn
    rw [same]
    funext i
    simp
  have wide : (1 : ℝ) < |(k : ℝ)| := by exact_mod_cast hk
  have wide' : (1 : ℝ) < (k : ℝ)^2 := by
    have e := mul_pos (sub_pos.mpr wide) (show 0 < |(k : ℝ)|+1 by positivity)
    nlinarith [sq_abs (k : ℝ)]
  have positive : 0<sq (linearImage B m) :=
    lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp (linearImage_ne_zero B hB m hm)))
  have he : linearImage B n=(k : ℝ) • linearImage B m := by
    unfold linearImage
    rw [show castVec n=(k : ℝ) • castVec m by
      rw [same]
      funext i
      simp [castVec,Pi.smul_apply,smul_eq_mul]]
    rw [Matrix.mulVec_smul]
  have hl := least m hm
  rw [he,sq_smul] at hl
  have strict : sq (linearImage B m)<(k : ℝ)^2*sq (linearImage B m) := by
    simpa using mul_lt_mul_of_pos_right wide' positive
  exact (not_lt_of_ge hl) strict

end BccSharp.Coulomb.BravaisCover
