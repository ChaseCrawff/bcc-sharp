import BccSharp.Lattice.ShortestVector

set_option autoImplicit false

/-! KZ choices in the ambient lattice. Centered representatives of
bounded projected vectors lie in a finite squared-length sublevel. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.KZ

theorem dot_symm (u v : Vec) : dot u v=dot v u := by
  simp [dot,mul_comm]

theorem dot_self (u : Vec) : dot u u=sq u := by simp [dot,sq,pow_two]

theorem dot_add (u x y : Vec) : dot u (x+y)=dot u x+dot u y := by
  simp [dot,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem dot_sub (u x y : Vec) : dot u (x-y)=dot u x-dot u y := by
  simp [dot,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem dot_smul (u x : Vec) (a : ℝ) : dot u (a • x)=a*dot u x := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.smul_apply,smul_eq_mul] <;> ring

theorem sq_pos {x : Vec} (hx : x≠0) : 0<sq x :=
  lt_of_le_of_ne (sq_nonnegative x) (Ne.symm (mt (sq_eq_zero_iff x).mp hx))

theorem sq_add (u v : Vec) : sq (u+v)=sq u+sq v+2*dot u v := by
  simp [sq,dot,Fin.sum_univ_three,Pi.add_apply]
  ring

def coeff (u x : Vec) : ℝ := dot u x/sq u
def drop (u x : Vec) : Vec := x-(coeff u x) • u

theorem coeff_add (u x y : Vec) : coeff u (x+y)=coeff u x+coeff u y := by
  simp [coeff,dot_add,add_div]

theorem coeff_sub (u x y : Vec) : coeff u (x-y)=coeff u x-coeff u y := by
  simp [coeff,dot_sub,sub_div]

theorem coeff_smul (u x : Vec) (a : ℝ) : coeff u (a • x)=a*coeff u x := by
  simp [coeff,dot_smul,mul_div_assoc]

theorem coeff_zero (u : Vec) : coeff u 0=0 := by simp [coeff,dot]

theorem coeff_self (u : Vec) (hu : u≠0) : coeff u u=1 := by
  rw [coeff,dot_self,div_self (sq_pos hu).ne']

theorem drop_add (u x y : Vec) : drop u (x+y)=drop u x+drop u y := by
  simp only [drop,coeff_add,add_smul]
  abel

theorem drop_sub (u x y : Vec) : drop u (x-y)=drop u x-drop u y := by
  simp only [drop,coeff_sub,sub_smul]
  abel

theorem drop_smul (u x : Vec) (a : ℝ) : drop u (a • x)=a • drop u x := by
  simp only [drop,coeff_smul,smul_smul,smul_sub]

theorem drop_zero (u : Vec) : drop u 0=0 := by simp [drop,coeff_zero]

theorem drop_self (u : Vec) (hu : u≠0) : drop u u=0 := by simp [drop,coeff_self u hu]

theorem drop_eq (u x : Vec) (h : dot u x=0) : drop u x=x := by simp [drop,coeff,h]

theorem dot_drop (u x : Vec) (hu : u≠0) : dot u (drop u x)=0 := by
  rw [drop,dot_sub,dot_smul,dot_self,coeff,div_mul_cancel₀ _ (sq_pos hu).ne',sub_self]

theorem sq_decomp (u x : Vec) (hu : u≠0) :
    sq x=sq (drop u x)+(coeff u x)^2*sq u := by
  have hx : drop u x+coeff u x • u=x := by unfold drop; abel
  have hd : dot (drop u x) (coeff u x • u)=0 := by
    rw [dot_smul,dot_symm (drop u x),dot_drop _ _ hu,mul_zero]
  calc
    sq x = sq (drop u x+coeff u x • u) := congrArg sq hx.symm
    _ = _ := by rw [sq_add,sq_smul,hd,mul_zero,add_zero]

theorem coeff_drop_invariant (u v x : Vec) (ortho : dot v u=0) :
    coeff v (drop u x)=coeff v x := by
  rw [drop,coeff_sub,coeff_smul]
  have ho : coeff v u=0 := by simp [coeff,ortho]
  rw [ho,mul_zero,sub_zero]

def doubleDrop (u v x : Vec) : Vec := drop v (drop u x)

theorem doubleDrop_sub (u v x y : Vec) :
    doubleDrop u v (x-y)=doubleDrop u v x-doubleDrop u v y := by
  simp [doubleDrop,drop_sub]

theorem doubleDrop_smul (u v x : Vec) (a : ℝ) :
    doubleDrop u v (a • x)=a • doubleDrop u v x := by simp [doubleDrop,drop_smul]

theorem doubleDrop_add (u v x y : Vec) :
    doubleDrop u v (x+y)=doubleDrop u v x+doubleDrop u v y := by simp [doubleDrop,drop_add]

theorem doubleDrop_first (u v : Vec) (hu : u≠0) : doubleDrop u v u=0 := by
  rw [doubleDrop,drop_self _ hu,drop_zero]

theorem doubleDrop_second (u b : Vec) (v : Vec) (hv : v=drop u b) (hn : v≠0) :
    doubleDrop u v b=0 := by
  unfold doubleDrop
  rw [← hv,drop_self _ hn]

theorem dot_doubleDrop_left (u v x : Vec) (hu : u≠0) (hv : dot u v=0) :
    dot u (doubleDrop u v x)=0 := by
  change dot u (drop u x-coeff v (drop u x) • v)=0
  rw [dot_sub,dot_smul,dot_drop _ _ hu,hv,mul_zero,sub_zero]

theorem lattice_sub_multiple (B : Mat) {x y : Vec} (hx : x∈lattice B) (hy : y∈lattice B) (k : ℤ) :
    x-(k : ℝ) • y∈lattice B := by
  obtain ⟨m,rfl⟩ := hx
  obtain ⟨n,rfl⟩ := hy
  refine ⟨fun i => m i-k*n i,?_⟩
  have e : castVec (fun i => m i-k*n i)=castVec m-(k : ℝ) • castVec n := by
    funext i
    simp [castVec,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  show B.mulVec (castVec (fun i => m i-k*n i)) = B.mulVec (castVec m)-(k : ℝ) • B.mulVec (castVec n)
  rw [e,Matrix.mulVec_sub,Matrix.mulVec_smul]

theorem lattice_neg (B : Mat) {x : Vec} (h : x∈lattice B) : -x∈lattice B :=
  (periodGroup B).neg_mem h

theorem floor_remainder (a : ℝ) : 0≤a-(⌊a⌋ : ℝ) ∧ a-(⌊a⌋ : ℝ)<1 := by
  exact ⟨sub_nonneg.mpr (Int.floor_le _),by linarith [Int.lt_floor_add_one a]⟩

def centerInteger (a : ℝ) : ℤ := ⌊a+1/2⌋

theorem center_remainder (a : ℝ) : |a-(centerInteger a : ℝ)|≤1/2 := by
  apply abs_le.mpr
  unfold centerInteger
  have h := floor_remainder (a+1/2)
  constructor <;> linarith [h.1,h.2]

def centerAlong (u x : Vec) : Vec := x-(centerInteger (coeff u x) : ℝ) • u

theorem centerAlong_lattice (B : Mat) {u x : Vec} (hu : u∈lattice B) (hx : x∈lattice B) :
    centerAlong u x∈lattice B := lattice_sub_multiple B hx hu _

theorem centerAlong_coeff (u x : Vec) (hu : u≠0) :
    |coeff u (centerAlong u x)|≤1/2 := by
  unfold centerAlong
  rw [coeff_sub,coeff_smul,coeff_self _ hu,mul_one]
  exact center_remainder _

theorem centerAlong_drop (u x : Vec) (hu : u≠0) : drop u (centerAlong u x)=drop u x := by
  simp [centerAlong,drop_sub,drop_smul,drop_self _ hu]

theorem square_half_bound {x : ℝ} (hx : |x|≤1/2) : x^2≤1/4 := by
  have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [sq_abs] at h
  linarith

theorem nonzero_dot_column (B : Mat) (hB : B.det≠0) (v : Vec) (hv : v≠0) :
    ∃ i : Fin 3, dot v (fun j => B j i)≠0 := by
  by_contra! hz
  have hm : B.transpose.mulVec v=0 := by
    funext i
    simpa [dot,Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm] using hz i
  have hT : IsUnit B.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hB)
  exact hv (Matrix.mulVec_injective_of_isUnit hT (hm.trans (Matrix.mulVec_zero _).symm))

theorem column_lattice (B : Mat) (i : Fin 3) : (fun j => B j i)∈lattice B := by
  refine ⟨Pi.single i 1,?_⟩
  have e : castVec (Pi.single i (1 : ℤ))=Pi.single i (1 : ℝ) := by
    funext j
    by_cases h : j=i <;> simp [castVec,Pi.single_apply,h]
  show B.mulVec (castVec (Pi.single i 1)) = B.col i
  rw [e,Matrix.mulVec_single_one]

theorem perpendicular_seed (u : Vec) : ∃ v : Vec, v≠0 ∧ dot v u=0 := by
  by_cases h : u 0=0 ∧ u 1=0
  · refine ⟨![1,0,0],?_,?_⟩
    · intro e
      have he := congrFun e 0
      norm_num at he
    · simp [dot,Fin.sum_univ_three,h.1]
  · let v : Vec := ![u 1,-u 0,0]
    refine ⟨v,?_,?_⟩
    · intro e
      apply h
      have a := congrFun e 0
      have b := congrFun e 1
      norm_num [v] at a b
      exact ⟨by linarith,by linarith⟩
    · simp [v,dot,Fin.sum_univ_three] <;> ring

def cross (u v : Vec) : Vec :=
  ![u 1*v 2-u 2*v 1,u 2*v 0-u 0*v 2,u 0*v 1-u 1*v 0]

theorem cross_perpendicular (u v : Vec) :
    dot (cross u v) u=0 ∧ dot (cross u v) v=0 := by
  constructor <;> simp [cross,dot,Fin.sum_univ_three] <;> ring

theorem cross_square (u v : Vec) : sq (cross u v)=sq u*sq v-(dot u v)^2 := by
  simp [cross,sq,dot,Fin.sum_univ_three] <;> ring

theorem cross_nonzero (u v : Vec) (hu : u≠0) (hv : v≠0) (ortho : dot u v=0) :
    cross u v≠0 := by
  intro e
  have h := cross_square u v
  have h0 : sq (0 : Vec)=0 := (sq_eq_zero_iff _).2 rfl
  rw [e,h0,ortho,zero_pow (by decide : (2 : ℕ)≠0),sub_zero] at h
  exact (mul_pos (sq_pos hu) (sq_pos hv)).ne' h.symm

/-- Take a positive minimum without a projected-lattice topological
instance. The normalizer supplies a bounded ambient representative of
every projected value under the finite seed threshold. -/
theorem positive_lattice_minimum (B : Mat) (hB : B.det≠0) (f : Vec → ℝ) (C : ℝ) (hC : 0≤C)
    (norm : ∀ x∈lattice B, ∃ y∈lattice B, f y=f x ∧ sq y≤C+f x)
    (seed : ∃ x∈lattice B, 0<f x) :
    ∃ x∈lattice B, 0<f x ∧ ∀ y∈lattice B, 0<f y → f x≤f y := by
  classical
  obtain ⟨w,hw,hpos⟩ := seed
  let S : Set Vec := {x | x∈lattice B ∧ sq x≤C+f w}
  have hF : S.Finite := finite_lattice_sublevel B hB _ (add_nonneg hC hpos.le)
  let s := hF.toFinset.filter (fun x => 0<f x ∧ f x≤f w)
  have mem (x : Vec) : x∈s ↔ x∈S ∧ 0<f x ∧ f x≤f w := by simp [s]
  obtain ⟨w',hw',hww,hN⟩ := norm w hw
  have hne : s.Nonempty := ⟨w',(mem _).2 ⟨⟨hw',hN⟩,by rwa [hww],hww.le⟩⟩
  obtain ⟨x,hx,hle⟩ := Finset.exists_min_image s f hne
  have H := (mem x).1 hx
  refine ⟨x,H.1.1,H.2.1,?_⟩
  intro y hy hp
  by_cases hi : f y≤f w
  · obtain ⟨z,hz,hzy,hNZ⟩ := norm y hy
    have hz' : z∈s := (mem _).2 ⟨⟨hz,by linarith⟩,by rwa [hzy],by rwa [hzy]⟩
    simpa [hzy] using hle z hz'
  · exact H.2.2.trans (le_of_not_ge hi)

end BccSharp.Coulomb.BravaisCover.KZ
