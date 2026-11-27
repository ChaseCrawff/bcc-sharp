import BccSharp.Lattice.KzBasis

set_option autoImplicit false

/-! Assembly of an oriented Lattice chart from the arbitrary normalized
period basis. The integer inverse comes from the floor generation theorem. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.KZ

private theorem castMatrix_injective : Function.Injective toRealMatrix := by
  intro A B h
  ext i j
  have e := congrFun (congrFun h i) j
  change (A i j : ℝ)=(B i j : ℝ) at e
  exact_mod_cast e

private theorem castMatrix_one : toRealMatrix (1 : Matrix (Fin 3) (Fin 3) ℤ)=1 := by
  ext i j
  by_cases h : i=j <;> simp [toRealMatrix,Matrix.one_apply,h]

private theorem castMatrix_mul (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    toRealMatrix (A*B)=toRealMatrix A*toRealMatrix B := Matrix.map_mul

private theorem castMatrix_neg (A : Matrix (Fin 3) (Fin 3) ℤ) :
    toRealMatrix (-A)= -toRealMatrix A := by
  ext i j
  simp [toRealMatrix,Matrix.map_apply,Matrix.neg_apply]

private theorem rebaseColumns (B : Mat) (indices : Fin 3 → IntVec) :
    (B*toRealMatrix (fun i j => indices j i)) =
      fun i j => linearImage B (indices j) i := by
  ext i j
  rfl

private theorem cancel_left {B A C : Mat} (hB : B.det≠0) (h : B*A=B*C) : A=C := by
  have e := congrArg (fun R : Mat => B⁻¹*R) h
  simpa only [← mul_assoc,Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB),one_mul] using e

namespace Picked

variable {L : Mat} (p : Picked L)

theorem integer_basis (hL : L.det≠0) :
    ∃ H G : Matrix (Fin 3) (Fin 3) ℤ,
      L*toRealMatrix H=p.basis ∧ H*G=1 ∧ G*H=1 := by
  classical
  have cols (j : Fin 3) : ∃ n : IntVec, linearImage L n=fun i => p.basis i j := by
    have h : (fun i => p.basis i j)∈lattice L := by
      fin_cases j
      · simpa [basis,columns] using p.aL
      · simpa [basis,columns] using p.bL
      · simpa [basis,columns] using p.cL
    exact h
  choose ns hns using cols
  let H : Matrix (Fin 3) (Fin 3) ℤ := fun i j => ns j i
  have hH : L*toRealMatrix H=p.basis := by
    show L*toRealMatrix (fun i j => ns j i)=p.basis
    rw [rebaseColumns]
    ext i j
    exact congrFun (hns j) i
  have orig (j : Fin 3) : ∃ n : IntVec, linearImage p.basis n=fun i => L i j :=
    p.generates _ (column_lattice L j)
  choose ms hms using orig
  let G : Matrix (Fin 3) (Fin 3) ℤ := fun i j => ms j i
  have hG : p.basis*toRealMatrix G=L := by
    show p.basis*toRealMatrix (fun i j => ms j i)=L
    rw [rebaseColumns]
    ext i j
    exact congrFun (hms j) i
  refine ⟨H,G,hH,?_,?_⟩
  · apply castMatrix_injective
    rw [castMatrix_mul,castMatrix_one]
    apply cancel_left hL
    rw [← mul_assoc,hH,hG,mul_one]
  · apply castMatrix_injective
    rw [castMatrix_mul,castMatrix_one]
    apply cancel_left p.basis_nonsingular
    rw [← mul_assoc,hG,hH,mul_one]

def point : Point := ![p.r1,p.r2,p.x,p.y,p.z]

private theorem third_eq_inv (unit : p.r1*p.r2*p.r3=1) : (p.r1*p.r2)⁻¹=p.r3 := by
  calc
    _ = (p.r1*p.r2)⁻¹*1 := by rw [mul_one]
    _ = _ := by
      rw [← unit,← mul_assoc,inv_mul_cancel₀ (mul_pos p.r1_pos p.r2_pos).ne',one_mul]

theorem chart_eq (unit : p.r1*p.r2*p.r3=1) : normalizedChart p.point=p.triangular := by
  unfold normalizedChart chartBasis
  simp [point,coordLift,triangular,p.third_eq_inv unit]

private theorem colExpansion (j k : ℤ) :
    drop p.a (linearImage p.basis (![0,j,k] : IntVec)) =
      ((j : ℝ)+p.z*(k : ℝ)) • p.v+(k : ℝ) • p.w := by
  unfold linearImage basis
  rw [columns_mulVec]
  simp only [castVec,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Int.cast_zero,zero_smul,zero_add,drop_add,drop_smul]
  change (j : ℝ) • p.v+(k : ℝ) • drop p.a p.c=_
  rw [p.c_drop,smul_add,smul_smul,add_smul,mul_comm p.z]
  abel

private theorem projection_norm (j k : ℤ) :
    sq (drop p.a (linearImage p.basis (![0,j,k] : IntVec))) =
      (p.r2*((j : ℝ)+p.z*(k : ℝ)))^2+(p.r3*(k : ℝ))^2 := by
  have orth (a b : ℝ) : dot (a • p.v) (b • p.w)=0 := by
    rw [dot_smul,dot_symm (a • p.v) p.w,dot_smul,dot_symm p.w p.v,p.vw]
    simp
  rw [p.colExpansion,sq_add,orth,mul_zero,add_zero,sq_smul,sq_smul]
  have hv : p.r2^2=sq p.v := Real.sq_sqrt p.bPos.le
  have hw : p.r3^2=sq p.w := Real.sq_sqrt p.cPos.le
  rw [← hv,← hw]
  ring

theorem point_reduced (unit : p.r1*p.r2*p.r3=1) (G H : Matrix (Fin 3) (Fin 3) ℤ)
    (hb : L*toRealMatrix H=p.basis) (hi : H*G=1) : reduced p.point := by
  have mem (n : IntVec) : linearImage p.basis n∈lattice L := by
    rw [← rebase_sameLattice L H G hi, hb]
    exact ⟨n,rfl⟩
  have hChart := p.chart_eq unit
  have r1sq : p.r1^2=sq p.a := Real.sq_sqrt p.aPos.le
  have r2sq : p.r2^2=sq p.v := Real.sq_sqrt p.bPos.le
  constructor
  · intro n hn
    change p.r1^2≤ sq (linearImage (normalizedChart p.point) n)
    rw [hChart,r1sq]
    have hl := p.aMin _ (mem n) (sq_pos (linearImage_ne_zero _ p.basis_nonsingular n hn))
    rw [p.factor,linearImage,← Matrix.mulVec_mulVec,sq_orthogonal p.rotation_ortho] at hl
    exact hl
  · intro j k nonzero
    let n : IntVec := ![0,j,k]
    have pp : 0<sq (drop p.a (linearImage p.basis n)) := by
      show 0<sq (drop p.a (linearImage p.basis (![0,j,k] : IntVec)))
      rw [p.projection_norm]
      rcases nonzero with hj | hk
      · by_cases hk : k=0
        · rw [hk]
          have hJ : (j : ℝ)≠0 := by exact_mod_cast hj
          have hP := sq_pos_of_ne_zero (mul_ne_zero p.r2_pos.ne' hJ)
          simpa using hP
        · have hK : (k : ℝ)≠0 := by exact_mod_cast hk
          exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (mul_ne_zero p.r3_pos.ne' hK))
      · have hK : (k : ℝ)≠0 := by exact_mod_cast hk
        exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (mul_ne_zero p.r3_pos.ne' hK))
    have hl := p.bMin _ (mem n) pp
    change sq p.v≤ sq (drop p.a (linearImage p.basis (![0,j,k] : IntVec))) at hl
    rw [p.projection_norm,← r2sq] at hl
    have h3 : p.r3=(p.r1*p.r2)⁻¹ := (p.third_eq_inv unit).symm
    change p.r2^2≤(p.r2*((j : ℝ)+p.z*(k : ℝ)))^2+((k : ℝ)/(p.r1*p.r2))^2
    rw [h3,← div_eq_inv_mul] at hl
    exact hl

end Picked

structure OrientedChart (L : Mat) where
  point : Point
  rotation : Mat
  basisChange : Matrix (Fin 3) (Fin 3) ℤ
  inverseChange : Matrix (Fin 3) (Fin 3) ℤ
  leftInverse : basisChange*inverseChange=1
  rightInverse : inverseChange*basisChange=1
  properRotation : proper rotation
  basisEquation : L*toRealMatrix basisChange=rotation*normalizedChart point
  reducedPoint : reduced point
  r1Positive : 0<point 0
  r2Positive : 0<point 1
  xBound : point 2∈Set.Icc (0 : ℝ) (1/2)
  yBound : point 3∈Set.Icc (0 : ℝ) (1/2)
  zBound : point 4∈Set.Icc (-1/2 : ℝ) (1/2)

theorem oriented_chart (L : Mat) (hL : L.det=1) : Nonempty (OrientedChart L) := by
  have hn : L.det≠0 := by rw [hL]; exact one_ne_zero
  obtain ⟨p⟩ := picked_nonempty L hn
  obtain ⟨H,G,basis,hi,gi⟩ := p.integer_basis hn
  have d : H.det*G.det=1 := by rw [← Matrix.det_mul,hi,Matrix.det_one]
  have hH : |(toRealMatrix H).det|=1 := by
    have e : (toRealMatrix H).det=((H.det : ℤ) : ℝ) := by
      unfold toRealMatrix
      rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
      simp
    rw [e]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one d with e | e <;> norm_num [e]
  have tpos : 0<p.r1*p.r2*p.r3 := mul_pos (mul_pos p.r1_pos p.r2_pos) p.r3_pos
  have unit : p.r1*p.r2*p.r3=1 := by
    have e := congrArg (fun B : Mat => |B.det|) (basis.trans p.factor)
    simp only [Matrix.det_mul,abs_mul,hL,abs_one,hH,p.rotation_det_abs,one_mul,
      p.triangular_det,abs_of_pos tpos] at e
    exact e.symm
  have hEq := basis.trans (p.factor.trans (congrArg (fun T => p.rotation*T) (p.chart_eq unit).symm))
  have red := p.point_reduced unit G H basis hi
  by_cases pos : p.rotation.det=1
  · exact ⟨⟨p.point,p.rotation,H,G,hi,gi,⟨p.rotation_ortho,pos⟩,hEq,red,
      p.r1_pos,p.r2_pos,p.xBound,p.yBound,p.zBound⟩⟩
  · have uNeg : p.rotation.det=-1 := by
      have e := p.rotation_det_abs
      by_cases h : 0≤p.rotation.det
      · rw [abs_of_nonneg h] at e
        exact (pos e).elim
      · rw [abs_of_neg (lt_of_not_ge h)] at e
        linarith
    have hOrient : proper (-p.rotation) := by
      refine ⟨by simp [Matrix.transpose_neg,p.rotation_ortho],?_⟩
      rw [← neg_one_smul ℝ p.rotation,Matrix.det_smul,Fintype.card_fin,uNeg]
      norm_num
    refine ⟨⟨p.point,-p.rotation,-H,-G,by simpa using hi,by simpa using gi,hOrient,?_,red,
      p.r1_pos,p.r2_pos,p.xBound,p.yBound,p.zBound⟩⟩
    rw [castMatrix_neg,mul_neg,neg_mul,hEq]

end BccSharp.Coulomb.BravaisCover.KZ
