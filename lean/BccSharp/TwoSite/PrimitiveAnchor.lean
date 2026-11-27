import BccSharp.TwoSite.ReferencePoints

set_option autoImplicit false

/-! Exact one-site presentation of every valid half-period anchor.
The pivot is a coordinate where the half-period class is odd. The basis,
its determinant, and both cosets are proved by integer parity. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb

private def halfVector (r : IntVec) : Vec := fun i => (r i : ℝ)/2
private def halfColumn (r : IntVec) (j : Fin 3) : Mat :=
  fun i k => if k=j then halfVector r i else if i=k then 1 else 0

private theorem halfColumn_det (r : IntVec) (j : Fin 3) (hr : r j = 1) :
    (halfColumn r j).det = 1/2 := by
  rw [Matrix.det_fin_three]
  rcases (by decide : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2) j with rfl | rfl | rfl <;>
    norm_num [halfColumn, halfVector, hr]

private theorem halfColumn_apply (r : IntVec) (j i : Fin 3) (n : IntVec) :
    (halfColumn r j).mulVec (castVec n) i =
      (if i=j then 0 else (n i : ℝ)) + (n j : ℝ) * ((r i : ℝ)/2) := by
  fin_cases j <;> fin_cases i <;>
    norm_num [halfColumn,halfVector,Matrix.mulVec,dotProduct,Fin.sum_univ_three,castVec] <;> ring

private def reducedInteger (j : Fin 3) (n : IntVec) (i : Fin 3) : ℤ :=
  if i=j then 0 else n i

private theorem halfColumn_parity (r : IntVec) (j : Fin 3) (n : IntVec) :
    (halfColumn r j).mulVec (castVec n) =
      castVec (fun i => reducedInteger j n i+(n j/2)*r i) + ((n j%2 : ℤ) : ℝ) • halfVector r := by
  have h : n j = 2*(n j/2)+n j%2 := by omega
  funext i
  rw [halfColumn_apply]
  have he : (n j : ℝ) = 2*((n j/2 : ℤ) : ℝ)+((n j%2 : ℤ) : ℝ) := by exact_mod_cast h
  by_cases hi : i=j <;>
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, halfVector, castVec, reducedInteger, hi] <;>
    push_cast <;> rw [he] <;> ring

private def insertHalfInteger (r : IntVec) (j : Fin 3) (n : IntVec) (b : ℤ) : IntVec :=
  fun i => if i=j then 2*n j + b else n i - n j*r i

private theorem halfColumn_insert (r : IntVec) (j : Fin 3) (hr : r j=1) (n : IntVec) (b : ℤ) :
    (halfColumn r j).mulVec (castVec (insertHalfInteger r j n b)) = castVec n+(b : ℝ) • halfVector r := by
  funext i
  rw [halfColumn_apply]
  by_cases hi : i=j
  · subst i
    simp [insertHalfInteger, castVec, halfVector, hr, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
      push_cast <;> ring
  · simp [insertHalfInteger, castVec, halfVector, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
      push_cast <;> ring

private theorem halfColumn_points (B : Mat) (r : IntVec) (j : Fin 3) (hr : r j=1) :
    lattice (B*halfColumn r j) =
      lattice B ∪ translate (B.mulVec (halfVector r)) (lattice B) := by
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    let m := fun i => reducedInteger j n i+(n j/2)*r i
    have h : n j%2 = 0 ∨ n j%2 = 1 := by omega
    show (B*halfColumn r j).mulVec (castVec n) ∈ _
    rw [← Matrix.mulVec_mulVec, halfColumn_parity]
    change B.mulVec (castVec m+((n j%2 : ℤ) : ℝ) • halfVector r) ∈ _
    rcases h with he | ho
    · simp only [he, Int.cast_zero, zero_smul, add_zero]
      exact Or.inl ⟨m,rfl⟩
    · simp only [ho, Int.cast_one, one_smul, Matrix.mulVec_add]
      exact Or.inr ⟨B.mulVec (castVec m),⟨m,rfl⟩,rfl⟩
  · rintro (⟨n,rfl⟩ | ⟨_,⟨n,rfl⟩,rfl⟩)
    · refine ⟨insertHalfInteger r j n 0, ?_⟩
      show (B*halfColumn r j).mulVec (castVec (insertHalfInteger r j n 0)) = B.mulVec (castVec n)
      rw [← Matrix.mulVec_mulVec, halfColumn_insert r j hr]
      simp
    · refine ⟨insertHalfInteger r j n 1, ?_⟩
      show (B*halfColumn r j).mulVec (castVec (insertHalfInteger r j n 1)) =
        B.mulVec (castVec n) + B.mulVec (halfVector r)
      rw [← Matrix.mulVec_mulVec, halfColumn_insert r j hr]
      simp [Matrix.mulVec_add]

private theorem anchor_offset_parity (q : TwoSite) (half : HalfClass q.offset) :
    ∃ (r k : IntVec) (j : Fin 3), r j=1 ∧ q.offset=halfVector r+castVec k := by
  obtain ⟨n,hn⟩ := half.1
  let r : IntVec := fun i => n i%2
  let k : IntVec := fun i => n i/2
  have hf : q.offset=halfVector r+castVec k := by
    funext i
    have he : (2 : ℝ)*q.offset i = (n i : ℝ) := congrFun hn i
    have hd : n i=2*(n i/2)+n i%2 := by omega
    have hreal : (n i : ℝ)=2*((n i/2 : ℤ) : ℝ)+((n i%2 : ℤ) : ℝ) := by exact_mod_cast hd
    change q.offset i = ((n i%2 : ℤ) : ℝ)/2 + ((n i/2 : ℤ) : ℝ)
    linarith
  have hj : ∃ j : Fin 3, r j=1 := by
    by_contra! h
    have hz (i : Fin 3) : r i=0 := by
      have hi := h i
      change n i%2 ≠ 1 at hi
      change n i%2=0
      omega
    have he : halfVector r = 0 := by funext i; simp [halfVector,hz]
    exact half.2 k (by simpa only [he,zero_add] using hf)
  obtain ⟨j,hj⟩ := hj
  exact ⟨r,k,j,hj,hf⟩

theorem primitive_anchor_exists (q : TwoSite) (hq : q.Valid) (half : HalfClass q.offset) :
    Nonempty (PrimitiveAnchorModel q) := by
  obtain ⟨r,k,j,hj,hf⟩ := anchor_offset_parity q half
  let P := q.basis*halfColumn r j
  have hP : P.det = 1/2 := by
    unfold P
    rw [Matrix.det_mul, hq.1, halfColumn_det r j hj, one_mul]
  have hpoints : lattice P = q.points := by
    unfold P
    rw [halfColumn_points _ _ _ hj, TwoSite.points, hf, Matrix.mulVec_add]
    exact congrArg (fun S => lattice q.basis ∪ S)
      (translate_period_add (periodGroup q.basis) _ _ ⟨k,rfl⟩).symm
  have hs : (ac • P).det ≠ 0 := by
    rw [Matrix.det_smul, Fintype.card_fin, hP]
    exact (mul_pos (pow_pos ac_positive _) (by norm_num)).ne'
  have hphys : lattice (ac • P) = periodicPoints (physicalBasis q) (physicalTwoPositions q) := by
    rw [Constants.scaled_lattice, hpoints, Constants.physical_points_eq_twoSite]
  refine ⟨⟨P,hP,hpoints,?_⟩⟩
  have hp : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  have he := Constants.pointsRepetition_energy (ac • P) hs q hq hphys seriesScreen hp
  unfold oneSiteEnergy
  rw [← he, green_two_eq_energy q hq]

theorem bravais_comparison_from_lattice (h : LatticeCase) : BravaisComparison :=
  bravais_of_one_site h primitive_anchor_exists

end BccSharp.Coulomb
