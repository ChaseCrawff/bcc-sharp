import BccSharp.Lattice.KzProjection

set_option autoImplicit false

/-! Second and third KZ choices. The two ambient normalizers retain
the exact projected vector and give a uniform length bound on its representative. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.KZ

private theorem coeff_neg (u x : Vec) : coeff u (-x)= -coeff u x := by
  simpa using coeff_smul u x (-1)

private theorem drop_neg (u x : Vec) : drop u (-x)= -drop u x := by
  simpa using drop_smul u x (-1)

private theorem sq_neg (x : Vec) : sq (-x)=sq x := by simp [sq,Pi.neg_apply]

private def chooseSign (u x : Vec) : Vec := if 0≤ coeff u x then x else -x

private theorem chooseSign_lattice (B : Mat) (u : Vec) {x : Vec} (h : x∈lattice B) :
    chooseSign u x∈lattice B := by
  unfold chooseSign
  split_ifs
  · exact h
  · exact lattice_neg B h

private theorem chooseSign_coeff (u x : Vec) : coeff u (chooseSign u x)=|coeff u x| := by
  unfold chooseSign
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h),coeff_neg]

private theorem chooseSign_abs (u v x : Vec) :
    |coeff v (chooseSign u x)|=|coeff v x| := by
  unfold chooseSign
  split_ifs <;> simp [coeff_neg]

private theorem chooseSign_drop_sq (u x : Vec) :
    sq (drop u (chooseSign u x))=sq (drop u x) := by
  unfold chooseSign
  split_ifs <;> simp [drop_neg,sq_neg]

private theorem chooseSign_doubleDrop_sq (u v x : Vec) :
    sq (doubleDrop u v (chooseSign u x))=sq (doubleDrop u v x) := by
  unfold chooseSign doubleDrop
  split_ifs <;> simp [drop_neg,sq_neg]

private theorem dot_drop_eq (v u x : Vec) (h : dot v u=0) : dot v (drop u x)=dot v x := by
  rw [drop,dot_sub,dot_smul,h,mul_zero,sub_zero]

private theorem firstProjection_seed (B : Mat) (hB : B.det≠0) (u : Vec) :
    ∃ x∈lattice B, 0<sq (drop u x) := by
  obtain ⟨v,hv,hortho⟩ := perpendicular_seed u
  obtain ⟨i,hi⟩ := nonzero_dot_column B hB v hv
  let x : Vec := fun j => B j i
  refine ⟨x,column_lattice B i,sq_pos ?_⟩
  intro hz
  apply hi
  rw [← dot_drop_eq v u x hortho,hz]
  simp [dot]

theorem chooseSecond (B : Mat) (hB : B.det≠0) (u : Vec)
    (hu : u≠0) (huL : u∈lattice B) :
    ∃ b∈lattice B, 0<sq (drop u b) ∧ coeff u b∈Set.Icc (0 : ℝ) (1/2) ∧
      ∀ x∈lattice B, 0<sq (drop u x) → sq (drop u b)≤ sq (drop u x) := by
  have norm (x : Vec) (hx : x∈lattice B) :
      ∃ y∈lattice B, sq (drop u y)=sq (drop u x) ∧ sq y≤ sq u/4+sq (drop u x) := by
    let y := centerAlong u x
    have same : drop u y=drop u x := centerAlong_drop u x hu
    have bound := mul_le_mul_of_nonneg_right
      (square_half_bound (centerAlong_coeff u x hu)) (sq_nonnegative u)
    refine ⟨y,centerAlong_lattice B huL hx,congrArg sq same,?_⟩
    rw [sq_decomp u y hu,same]
    linarith
  obtain ⟨x,hx,hxpos,least⟩ := positive_lattice_minimum B hB (fun x => sq (drop u x))
    (sq u/4) (div_nonneg (sq_nonnegative u) (by norm_num)) norm (firstProjection_seed B hB u)
  let y := centerAlong u x
  let b := chooseSign u y
  have same : sq (drop u b)=sq (drop u x) :=
    (chooseSign_drop_sq u y).trans (congrArg sq (centerAlong_drop u x hu))
  have centered : coeff u b∈Set.Icc (0 : ℝ) (1/2) := by
    change 0≤ coeff u (chooseSign u y) ∧ coeff u (chooseSign u y)≤1/2
    rw [chooseSign_coeff]
    exact ⟨abs_nonneg _,centerAlong_coeff u x hu⟩
  exact ⟨b,chooseSign_lattice B u (centerAlong_lattice B huL hx),same.symm ▸ hxpos,centered,
    fun z hz hp => same.trans_le (least z hz hp)⟩

private def centerPlane (u b v x : Vec) : Vec :=
  centerAlong u (x-(centerInteger (coeff v x) : ℝ) • b)

private theorem centerPlane_lattice (B : Mat) (u b v x : Vec)
    (hu : u∈lattice B) (hb : b∈lattice B) (hx : x∈lattice B) :
    centerPlane u b v x∈lattice B :=
  centerAlong_lattice B hu (lattice_sub_multiple B hx hb _)

private theorem centerPlane_proj (u b v x : Vec) (hu : u≠0) (hv : v≠0)
    (hb : v=drop u b) : doubleDrop u v (centerPlane u b v x)=doubleDrop u v x := by
  unfold centerPlane centerAlong
  simp [doubleDrop_sub,doubleDrop_smul,doubleDrop_first u v hu,
    doubleDrop_second u b v hb hv]

private theorem centerPlane_coeff (u b v x : Vec) (hu : u≠0) (hv : v≠0)
    (hb : v=drop u b) (hvu : dot v u=0) :
    |coeff u (centerPlane u b v x)|≤1/2 ∧ |coeff v (centerPlane u b v x)|≤1/2 := by
  refine ⟨centerAlong_coeff u _ hu,?_⟩
  have hvu' : coeff v u=0 := by simp [coeff,hvu]
  have hb' : coeff v b=1 := by
    rw [← coeff_drop_invariant u v b hvu,← hb,coeff_self _ hv]
  unfold centerPlane centerAlong
  rw [coeff_sub,coeff_smul,hvu',mul_zero,sub_zero,coeff_sub,coeff_smul,hb',mul_one]
  exact center_remainder _

private theorem secondProjection_seed (B : Mat) (hB : B.det≠0) (u v : Vec)
    (hu : u≠0) (hv : v≠0) (hUV : dot u v=0) :
    ∃ x∈lattice B, 0<sq (doubleDrop u v x) := by
  let w := cross u v
  obtain ⟨i,hi⟩ := nonzero_dot_column B hB w (cross_nonzero u v hu hv hUV)
  let x : Vec := fun j => B j i
  refine ⟨x,column_lattice B i,sq_pos ?_⟩
  intro hz
  apply hi
  have e : dot w (doubleDrop u v x)=dot w x := by
    unfold doubleDrop
    rw [dot_drop_eq w v _ (cross_perpendicular u v).2,dot_drop_eq w u _ (cross_perpendicular u v).1]
  rw [← e,hz]
  simp [dot]

theorem chooseThird (B : Mat) (hB : B.det≠0) (u b v : Vec)
    (hu : u≠0) (hv : v≠0) (hb : v=drop u b)
    (huL : u∈lattice B) (hbL : b∈lattice B) :
    ∃ c∈lattice B, 0<sq (doubleDrop u v c) ∧ coeff u c∈Set.Icc (0 : ℝ) (1/2) ∧
      coeff v c∈Set.Icc (-1/2 : ℝ) (1/2) ∧
      ∀ x∈lattice B, 0<sq (doubleDrop u v x) → sq (doubleDrop u v c)≤ sq (doubleDrop u v x) := by
  have huv : dot u v=0 := by rw [hb,dot_drop _ _ hu]
  have hvu : dot v u=0 := (dot_symm v u).trans huv
  have norm (x : Vec) (hx : x∈lattice B) : ∃ y∈lattice B,
      sq (doubleDrop u v y)=sq (doubleDrop u v x) ∧
      sq y≤(sq u+sq v)/4+sq (doubleDrop u v x) := by
    let y := centerPlane u b v x
    have same : doubleDrop u v y=doubleDrop u v x := centerPlane_proj u b v x hu hv hb
    have h := centerPlane_coeff u b v x hu hv hb hvu
    have left := mul_le_mul_of_nonneg_right (square_half_bound h.1) (sq_nonnegative u)
    have right := mul_le_mul_of_nonneg_right (square_half_bound h.2) (sq_nonnegative v)
    refine ⟨y,centerPlane_lattice B u b v x huL hbL hx,congrArg sq same,?_⟩
    rw [sq_decomp u y hu,sq_decomp v (drop u y) hv,coeff_drop_invariant u v y hvu]
    change sq (doubleDrop u v y)+(coeff v y)^2*sq v+(coeff u y)^2*sq u≤_
    rw [same]
    linarith
  obtain ⟨x,hx,hp,least⟩ :=
    positive_lattice_minimum B hB (fun x => sq (doubleDrop u v x)) ((sq u+sq v)/4)
      (div_nonneg (add_nonneg (sq_nonnegative u) (sq_nonnegative v)) (by norm_num)) norm
      (secondProjection_seed B hB u v hu hv huv)
  let y := centerPlane u b v x
  let c := chooseSign u y
  have same : sq (doubleDrop u v c)=sq (doubleDrop u v x) :=
    (chooseSign_doubleDrop_sq u v y).trans (congrArg sq (centerPlane_proj u b v x hu hv hb))
  have bounds := centerPlane_coeff u b v x hu hv hb hvu
  have h₁ : coeff u c∈Set.Icc (0 : ℝ) (1/2) := by
    change 0≤ coeff u (chooseSign u y) ∧ coeff u (chooseSign u y)≤1/2
    rw [chooseSign_coeff]
    exact ⟨abs_nonneg _,bounds.1⟩
  have h₂ : coeff v c∈Set.Icc (-1/2 : ℝ) (1/2) := by
    have habs : |coeff v c| ≤ 1/2 := by
      change |coeff v (chooseSign u y)| ≤ 1/2
      rw [chooseSign_abs]
      exact bounds.2
    have hb2 := abs_le.mp habs
    exact ⟨by linarith [hb2.1], hb2.2⟩
  exact ⟨c,chooseSign_lattice B u (centerPlane_lattice B u b v x huL hbL hx),same.symm ▸ hp,
    h₁,h₂,fun z hz hpos => same.trans_le (least z hz hpos)⟩

end BccSharp.Coulomb.BravaisCover.KZ
