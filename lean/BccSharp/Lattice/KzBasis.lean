import BccSharp.Lattice.KzChoices

set_option autoImplicit false

/-! Generation and triangular factorization for the three KZ
minima. Successive floor remainders certify that the columns generate the
full original lattice; no primitive extension theorem is assumed. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.KZ

structure Picked (L : Mat) where
  a : Vec
  b : Vec
  c : Vec
  aL : a∈lattice L
  bL : b∈lattice L
  cL : c∈lattice L
  aPos : 0<sq a
  bPos : 0<sq (drop a b)
  cPos : 0<sq (doubleDrop a (drop a b) c)
  xBound : coeff a b∈Set.Icc (0 : ℝ) (1/2)
  yBound : coeff a c∈Set.Icc (0 : ℝ) (1/2)
  zBound : coeff (drop a b) c∈Set.Icc (-1/2 : ℝ) (1/2)
  aMin : ∀ t∈lattice L, 0<sq t → sq a≤ sq t
  bMin : ∀ t∈lattice L, 0<sq (drop a t) → sq (drop a b)≤ sq (drop a t)
  cMin : ∀ t∈lattice L, 0<sq (doubleDrop a (drop a b) t) →
    sq (doubleDrop a (drop a b) c)≤ sq (doubleDrop a (drop a b) t)

theorem picked_nonempty (L : Mat) (hL : L.det≠0) : Nonempty (Picked L) := by
  obtain ⟨n,hn,minA⟩ := shortest_lattice_index L hL
  let a := linearImage L n
  have aL : a∈lattice L := ⟨n,rfl⟩
  have ha : a≠0 := linearImage_ne_zero L hL n hn
  obtain ⟨b,bL,hb,hx,minB⟩ := chooseSecond L hL a ha aL
  let v := drop a b
  have hv : v≠0 := fun h => hb.ne' ((sq_eq_zero_iff v).2 h)
  obtain ⟨c,cL,hc,hy,hz,minC⟩ := chooseThird L hL a b v ha hv rfl aL bL
  refine ⟨⟨a,b,c,aL,bL,cL,sq_pos ha,hb,hc,hx,hy,hz,?_,minB,minC⟩⟩
  intro t ht hp
  obtain ⟨m,rfl⟩ := ht
  change sq (linearImage L n)≤ sq (linearImage L m)
  apply minA m
  intro e
  subst m
  change 0<sq (linearImage L 0) at hp
  have h0 : sq (linearImage L 0)=0 := by
    rw [sq_eq_zero_iff]
    show L.mulVec (castVec 0)=0
    rw [castVec_zero,Matrix.mulVec_zero]
  rw [h0] at hp
  exact lt_irrefl _ hp

def columns (u v w : Vec) : Mat := fun i j => ![u i,v i,w i] j

theorem columns_mulVec (u v w x : Vec) :
    (columns u v w).mulVec x = x 0 • u+x 1 • v+x 2 • w := by
  funext i
  simp [columns,Matrix.mulVec,dotProduct,Fin.sum_univ_three,Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;> ring

def axis (a : Vec) : Vec := (Real.sqrt (sq a))⁻¹ • a

theorem radius_axis (a : Vec) (h : 0<sq a) : Real.sqrt (sq a) • axis a=a := by
  simp [axis,smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr h).ne']

theorem dot_axis (a b : Vec) :
    dot (axis a) (axis b)=(Real.sqrt (sq a))⁻¹*(Real.sqrt (sq b))⁻¹*dot a b := by
  simp only [axis]
  rw [dot_smul,dot_symm ((Real.sqrt (sq a))⁻¹ • a),
    dot_smul,dot_symm b a]
  ring

theorem dot_axis_self (a : Vec) (h : 0<sq a) : dot (axis a) (axis a)=1 := by
  rw [dot_axis,dot_self]
  have hr := (Real.sqrt_pos.mpr h).ne'
  field_simp [hr] <;> nlinarith [Real.sq_sqrt h.le]

namespace Picked

variable {L : Mat} (p : Picked L)

def v : Vec := drop p.a p.b
def w : Vec := doubleDrop p.a p.v p.c
def r1 : ℝ := Real.sqrt (sq p.a)
def r2 : ℝ := Real.sqrt (sq p.v)
def r3 : ℝ := Real.sqrt (sq p.w)
def x : ℝ := coeff p.a p.b
def y : ℝ := coeff p.a p.c
def z : ℝ := coeff p.v p.c

theorem a_ne : p.a≠0 := fun e => p.aPos.ne' ((sq_eq_zero_iff _).2 e)
theorem v_ne : p.v≠0 := fun e => p.bPos.ne' ((sq_eq_zero_iff _).2 e)
theorem w_ne : p.w≠0 := fun e => p.cPos.ne' ((sq_eq_zero_iff _).2 e)

theorem r1_pos : 0<p.r1 := Real.sqrt_pos.mpr p.aPos
theorem r2_pos : 0<p.r2 := Real.sqrt_pos.mpr p.bPos
theorem r3_pos : 0<p.r3 := Real.sqrt_pos.mpr p.cPos

theorem av : dot p.a p.v=0 := dot_drop p.a p.b p.a_ne
theorem aw : dot p.a p.w=0 := dot_doubleDrop_left p.a p.v p.c p.a_ne p.av
theorem vw : dot p.v p.w=0 := dot_drop p.v (drop p.a p.c) p.v_ne

theorem b_decomp : p.b=p.x • p.a+p.v := by unfold x v drop; abel

theorem c_drop : drop p.a p.c=p.z • p.v+p.w := by
  have h := coeff_drop_invariant p.a p.v p.c ((dot_symm _ _).trans p.av)
  unfold z w doubleDrop
  rw [show drop p.v (drop p.a p.c) = drop p.a p.c-coeff p.v (drop p.a p.c) • p.v from rfl,h]
  abel

theorem c_decomp : p.c=p.y • p.a+p.z • p.v+p.w := by
  have h : p.c=p.y • p.a+drop p.a p.c := by unfold y drop; abel
  rw [p.c_drop,← add_assoc] at h
  exact h

def basis : Mat := columns p.a p.b p.c
def rotation : Mat := columns (axis p.a) (axis p.v) (axis p.w)
def triangular : Mat := !![p.r1,p.r1*p.x,p.r1*p.y;0,p.r2,p.r2*p.z;0,0,p.r3]

theorem rotation_ortho : p.rotation.transpose*p.rotation=1 := by
  have av : dot (axis p.a) (axis p.v)=0 := by rw [dot_axis,p.av,mul_zero]
  have aw : dot (axis p.a) (axis p.w)=0 := by rw [dot_axis,p.aw,mul_zero]
  have vw : dot (axis p.v) (axis p.w)=0 := by rw [dot_axis,p.vw,mul_zero]
  have a := dot_axis_self p.a p.aPos
  have b := dot_axis_self p.v p.bPos
  have c := dot_axis_self p.w p.cPos
  ext i j
  have entry : (p.rotation.transpose*p.rotation) i j =
      dot (![axis p.a,axis p.v,axis p.w] i) (![axis p.a,axis p.v,axis p.w] j) := by
    unfold rotation
    rw [Matrix.mul_apply]
    unfold dot
    apply Finset.sum_congr rfl
    intro k _
    fin_cases i <;> fin_cases j <;> rfl
  rw [entry]
  have va := (dot_symm (axis p.v) (axis p.a)).trans av
  have wa := (dot_symm (axis p.w) (axis p.a)).trans aw
  have wv := (dot_symm (axis p.w) (axis p.v)).trans vw
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply,a,b,c,av,aw,vw,va,wa,wv]

theorem rotation_det_abs : |p.rotation.det|=1 := by
  have h := congrArg Matrix.det p.rotation_ortho
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one,← pow_two,← sq_abs] at h
  have eq : |p.rotation.det|^2=(1 : ℝ)^2 := by simpa using h
  exact le_antisymm ((sq_le_sq₀ (abs_nonneg _) zero_le_one).mp eq.le)
    ((sq_le_sq₀ zero_le_one (abs_nonneg _)).mp eq.ge)

theorem triangular_det : p.triangular.det=p.r1*p.r2*p.r3 := by
  norm_num [triangular,Matrix.det_fin_three]

theorem factor : p.basis=p.rotation*p.triangular := by
  have a : p.r1 • axis p.a=p.a := radius_axis _ p.aPos
  have v : p.r2 • axis p.v=p.v := radius_axis _ p.bPos
  have w : p.r3 • axis p.w=p.w := radius_axis _ p.cPos
  have xa : (p.r1*p.x) • axis p.a=p.x • p.a := by rw [mul_comm,← smul_smul,a]
  have ya : (p.r1*p.y) • axis p.a=p.y • p.a := by rw [mul_comm,← smul_smul,a]
  have zv : (p.r2*p.z) • axis p.v=p.z • p.v := by rw [mul_comm,← smul_smul,v]
  ext i j
  change p.basis i j=(p.rotation.mulVec (fun k => p.triangular k j)) i
  rw [rotation,columns_mulVec]
  fin_cases j
  · simpa [basis,columns,triangular] using (congrFun a i).symm
  · simpa [basis,columns,triangular,xa,v] using congrFun p.b_decomp i
  · simpa [basis,columns,triangular,ya,zv,w] using congrFun p.c_decomp i

theorem basis_nonsingular : p.basis.det≠0 := by
  rw [p.factor,Matrix.det_mul,p.triangular_det]
  have hu : p.rotation.det≠0 := by
    intro hz
    have h := p.rotation_det_abs
    simp [hz] at h
  exact mul_ne_zero hu (mul_ne_zero (mul_ne_zero p.r1_pos.ne' p.r2_pos.ne') p.r3_pos.ne')

private theorem remainder_zero {v y : Vec} (F : Vec → Vec) (s : ℝ)
    (hs : 0≤ s ∧ s<1) (hv : 0<sq v) (he : F y=s • v)
    (h : 0<sq (F y) → sq v≤ sq (F y)) : s=0 := by
  by_contra hn
  have hp : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hn)
  have hi : s^2<1 := by
    have H := mul_pos (sub_pos.mpr hs.2) (show 0<1+s by linarith)
    nlinarith
  have eh : sq (F y)=s^2*sq v := by rw [he,sq_smul]
  have h1 := h (by rw [eh]; exact mul_pos (pow_pos hp _) hv)
  have h2 := mul_lt_mul_of_pos_right hi hv
  rw [eh] at h1
  linarith

/-- Integer generation from three successive shortest positive remainders. -/
theorem generates (t : Vec) (ht : t∈lattice L) : ∃ n : IntVec, linearImage p.basis n=t := by
  let d := p.basis⁻¹.mulVec t
  have hd : d 0 • p.a+d 1 • p.b+d 2 • p.c=t := by
    rw [← columns_mulVec]
    change p.basis.mulVec (p.basis⁻¹.mulVec t)=t
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr p.basis_nonsingular),Matrix.one_mulVec]
  let n : IntVec := fun i => ⌊d i⌋
  let s (i : Fin 3) : ℝ := d i-(n i : ℝ)
  have frac (i : Fin 3) : 0≤ s i ∧ s i<1 := floor_remainder (d i)
  let t3 := t-(n 2 : ℝ) • p.c
  have t3mem : t3∈lattice L := lattice_sub_multiple L ht p.cL (n 2)
  have e3 : t3=d 0 • p.a+d 1 • p.b+s 2 • p.c := by
    unfold t3 s
    rw [← hd,sub_smul]
    abel
  have f3 : doubleDrop p.a p.v t3=s 2 • p.w := by
    rw [e3]
    simp [doubleDrop_add,doubleDrop_smul,doubleDrop_first p.a p.v p.a_ne,
      doubleDrop_second p.a p.b p.v rfl p.v_ne,w]
  have z3 : s 2=0 :=
    remainder_zero _ _ (frac 2) p.cPos f3 (p.cMin t3 t3mem)
  let t2 := t3-(n 1 : ℝ) • p.b
  have t2mem : t2∈lattice L := lattice_sub_multiple L t3mem p.bL (n 1)
  have e2 : t2=d 0 • p.a+s 1 • p.b := by
    unfold t2
    rw [e3,z3,zero_smul,add_zero]
    unfold s
    rw [sub_smul]
    abel
  have f2 : drop p.a t2=s 1 • p.v := by
    rw [e2]
    simp [drop_add,drop_smul,drop_self _ p.a_ne,v]
  have z2 : s 1=0 := remainder_zero _ _ (frac 1) p.bPos f2 (p.bMin t2 t2mem)
  let t1 := t2-(n 0 : ℝ) • p.a
  have t1mem : t1∈lattice L := lattice_sub_multiple L t2mem p.aL (n 0)
  have e1 : t1=s 0 • p.a := by
    unfold t1
    rw [e2,z2,zero_smul,add_zero]
    unfold s
    rw [sub_smul]
  have z1 : s 0=0 := remainder_zero id _ (frac 0) p.aPos e1 (p.aMin t1 t1mem)
  have d0 : d 0=(n 0 : ℝ) := sub_eq_zero.mp z1
  have d1 : d 1=(n 1 : ℝ) := sub_eq_zero.mp z2
  have d2 : d 2=(n 2 : ℝ) := sub_eq_zero.mp z3
  exact ⟨n,by
    unfold linearImage basis
    rw [columns_mulVec]
    simpa only [castVec,d0,d1,d2] using hd⟩

end Picked
end BccSharp.Coulomb.BravaisCover.KZ
