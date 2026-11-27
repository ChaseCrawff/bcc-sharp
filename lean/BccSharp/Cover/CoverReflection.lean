import BccSharp.Cover.CoverClips

set_option autoImplicit false

/-! Two-coset swap on the actual compact chart. Inversion permutes
the fourteen star labels, so the rotated trial can use the same proper
rotation after reflecting the neighbors. The representative itself also
arises by translation, which preserves the rigid-copy conclusions. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Coverage

def offsetSwap (q : TwoSite) : TwoSite := ⟨q.basis,-q.offset⟩

private theorem sq_neg_vec (v : Vec) : sq (-v)=sq v := by simp [sq]

private theorem quad_neg_vec (A : Mat) (v : Vec) : quad A (-v)=quad A v := by
  simp [quad,Matrix.mulVec_neg]

private def negIndex : IntVec ≃ IntVec where
  toFun n := -n
  invFun n := -n
  left_inv n := neg_neg n
  right_inv n := neg_neg n

theorem energy_offsetSwap (q : TwoSite) : energy (offsetSwap q)=energy q := by
  let A := q.basis.transpose*q.basis
  let F (n : IntVec) := gKernel (1/2) (Real.pi*quad A (castVec n+q.offset))
  have e : (∑' n : IntVec, gKernel (1/2) (Real.pi*quad A (castVec n+ -q.offset)))=∑' n, F n := by
    rw [← negIndex.tsum_eq F]
    apply tsum_congr
    intro n
    change _ = F (-n)
    unfold F
    rw [castVec_neg,show -castVec n+q.offset= -(castVec n+ -q.offset) by abel,quad_neg_vec]
  have c (n : IntVec) : Real.cos (2*Real.pi*dot (castVec n) (-q.offset))=
      Real.cos (2*Real.pi*dot (castVec n) q.offset) := by
    have h : dot (castVec n) (-q.offset)= -dot (castVec n) q.offset := by
      simp [dot,Finset.sum_neg_distrib]
    rw [h,mul_neg,Real.cos_neg]
  unfold energy h₂
  simp only [offsetSwap]
  rw [show q.basis.transpose*q.basis=A by rfl,e]
  simp only [c,F]

private theorem lattice_neg_closed (A : Mat) {v : Vec} (h : v∈lattice A) : -v∈lattice A := by
  obtain ⟨i,rfl⟩ := h
  exact ⟨-i,by
    show A.mulVec (castVec (-i))= -A.mulVec (castVec i)
    rw [castVec_neg,Matrix.mulVec_neg]⟩

private theorem swap_points_neg (q : TwoSite) : (offsetSwap q).points = (fun x : Vec => -x) '' q.points := by
  ext v
  constructor
  · rintro (h | ⟨y,hy,e⟩)
    · exact ⟨-v,Or.inl (lattice_neg_closed _ h),neg_neg v⟩
    · refine ⟨-y+q.basis.mulVec q.offset,Or.inr ⟨-y,lattice_neg_closed _ hy,rfl⟩,?_⟩
      rw [e]
      simp only [offsetSwap,Matrix.mulVec_neg,neg_add_rev,neg_neg]
      abel
  · rintro ⟨v,(h | ⟨y,hy,e⟩),rfl⟩
    · exact Or.inl (lattice_neg_closed _ h)
    · refine Or.inr ⟨-y,lattice_neg_closed _ hy,?_⟩
      rw [e]
      simp only [offsetSwap,Matrix.mulVec_neg,neg_add_rev]
      abel

private theorem swap_points_translate (q : TwoSite) :
    (offsetSwap q).points=translate (-(q.basis.mulVec q.offset)) q.points := by
  ext v
  constructor
  · rintro (h | ⟨y,hy,e⟩)
    · exact ⟨v+q.basis.mulVec q.offset,Or.inr ⟨v,h,rfl⟩,by abel⟩
    · exact ⟨y,Or.inl hy,by simpa [offsetSwap,Matrix.mulVec_neg] using e⟩
  · rintro ⟨x,(h | ⟨y,hy,e⟩),ev⟩
    · exact Or.inr ⟨x,h,by simpa [offsetSwap,Matrix.mulVec_neg] using ev⟩
    · exact Or.inl (by rwa [ev,e,add_neg_cancel_right])

private def opposite (i : Fin 14) : Fin 14 := ![7,6,5,4,3,2,1,0,9,8,11,10,13,12] i

private def oppositeEquiv : Fin 14 ≃ Fin 14 where
  toFun := opposite
  invFun := opposite
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem star_opposite (i : Fin 14) : star (oppositeEquiv i)=-star i := by
  funext j
  fin_cases i <;> fin_cases j <;> norm_num [oppositeEquiv,opposite,star]

private theorem neg_neighbor (q : TwoSite) {v : Vec} (h : v∈neighbors q) : -v∈neighbors (offsetSwap q) := by
  have h' : v∈q.points ∧ v≠0 ∧ sq v<(13/10 : ℝ)^2 := by
    have h0 : 0 + v ∈ q.points ∧ v ≠ 0 ∧ sq v < (13/10 : ℝ)^2 := h
    rwa [zero_add] at h0
  change 0 + -v ∈ (offsetSwap q).points ∧ -v ≠ 0 ∧ sq (-v) < (13/10 : ℝ)^2
  simp only [zero_add,swap_points_neg,sq_neg_vec,neg_ne_zero]
  exact ⟨⟨v,h'.1,rfl⟩,h'.2⟩

@[simp] theorem offsetSwap_involutive (q : TwoSite) : offsetSwap (offsetSwap q)=q := by
  cases q; simp [offsetSwap]

private def neighborSwap (q : TwoSite) : ↥(neighbors q) ≃ ↥(neighbors (offsetSwap q)) where
  toFun v := ⟨-v.val,neg_neighbor q v.property⟩
  invFun v := ⟨-v.val,by simpa only [offsetSwap_involutive] using neg_neighbor (offsetSwap q) v.property⟩
  left_inv v := Subtype.ext (neg_neg v.val)
  right_inv v := Subtype.ext (neg_neg v.val)

private theorem candidates_swap (q : TwoSite) : defectCandidates (neighbors q) ⊆
    defectCandidates (neighbors (offsetSwap q)) := by
  classical
  intro cost h
  rcases Set.mem_insert_iff.mp h with rfl | ⟨U,hU,sigma,rfl⟩
  · exact Set.mem_insert _ _
  let e := neighborSwap q
  let tau := (oppositeEquiv.toEmbedding.trans sigma).trans e.toEmbedding
  apply Set.mem_insert_of_mem
  refine ⟨U,hU,tau,?_⟩
  have matching (i : Fin 14) : sq ((tau i : Vec)-U.mulVec (star i))=
      sq ((sigma (oppositeEquiv i) : Vec)-U.mulVec (star (oppositeEquiv i))) := by
    change sq (-((sigma (oppositeEquiv i) : Vec))-U.mulVec (star i))=_
    rw [star_opposite,Matrix.mulVec_neg,show -((sigma (oppositeEquiv i) : Vec))-U.mulVec (star i)=
      -((sigma (oppositeEquiv i) : Vec)- -(U.mulVec (star i))) by abel,sq_neg_vec]
  have sums : (∑ i, sq ((tau i : Vec)-U.mulVec (star i)))=(∑ i, sq ((sigma i : Vec)-U.mulVec (star i))) := by
    simp only [matching]
    exact oppositeEquiv.sum_comp (fun i => sq ((sigma i : Vec)-U.mulVec (star i)))
  have covered (v : ↥(neighbors q)) : e v∈Set.range tau ↔ v∈Set.range sigma := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨oppositeEquiv i,e.injective hi⟩
    · rintro ⟨i,rfl⟩
      exact ⟨oppositeEquiv.symm i,by simp [tau]⟩
  let excluded (v : ↥(neighbors (offsetSwap q))) := if v∈Set.range tau then 0 else annularWeight v.val
  have unmatched : (∑' v, excluded v)=∑' v : ↥(neighbors q),
      if v∈Set.range sigma then 0 else annularWeight v.val := by
    rw [← e.tsum_eq excluded]
    apply tsum_congr
    intro v
    simp only [excluded,covered]
    have eq : annularWeight (e v).val=annularWeight v.val := by
      change annularWeight (-v.val)=_
      simp [annularWeight,sq_neg_vec]
    rw [eq]
  unfold defectTrial
  change _ = _ + (∑' v, excluded v)
  rw [sums,unmatched]

theorem defect_offsetSwap (q : TwoSite) : defect (offsetSwap q)=defect q := by
  have inclusion := candidates_swap (offsetSwap q)
  rw [offsetSwap_involutive] at inclusion
  unfold defect cappedDefect
  rw [Set.Subset.antisymm inclusion (candidates_swap q)]

theorem deficit_offsetSwap (q : TwoSite) : deficit (offsetSwap q)=deficit q := by
  simp [deficit,energy_offsetSwap,defect_offsetSwap]

private theorem rigidCopy_of_swap (q : TwoSite) (S : Set Vec) (h : rigidCopy (offsetSwap q).points S) : rigidCopy q.points S := by
  obtain ⟨v,U,hU,hEq⟩ := h
  have sw := swap_points_translate (offsetSwap q)
  rw [offsetSwap_involutive,hEq] at sw
  let t : Vec := -((offsetSwap q).basis.mulVec (offsetSwap q).offset)
  refine ⟨v+t,U,hU,?_⟩
  change q.points=translate (v+t) (U.mulVec '' S)
  rw [sw]
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,ey⟩,ex⟩
    exact ⟨z,hz,by rw [ex,ey]; simp only [t]; abel⟩
  · rintro ⟨z,hz,e⟩
    exact ⟨z+v,⟨z,hz,rfl⟩,by rw [e]; simp only [t]; abel⟩

theorem leaf_of_swap (q : TwoSite) (w : LeafProof (offsetSwap q)) : LeafProof q := by
  have gapPositive := Constants.reference_gap_checked.2
  by_cases h : deficit q≤0
  · have hn : deficit (offsetSwap q)≤0 := by rwa [deficit_offsetSwap]
    obtain ⟨z,k⟩ := leaf_of_nonpositive _ gapPositive (defect_range _).2 hn w
    rw [deficit_offsetSwap] at z
    exact .classifiedNonnegative z.ge (fun _ => k.elim (fun a => Or.inl (rigidCopy_of_swap q _ a))
      (fun a => Or.inr (rigidCopy_of_swap q _ a)))
  · exact .strictDeficit (lt_of_not_ge h)

def reflectChart (p : Chart) : Chart := fun i => if i.val<5 then p i else -p i

def reflectCell (b : Cell) : Cell :=
  ⟨fun i => if i.val<5 then b.lo i else -b.hi i,fun i => if i.val<5 then b.hi i else -b.lo i⟩

theorem reflectChart_mem (b : Cell) (p : Chart) : (reflectCell b).Mem (reflectChart p) ↔ b.Mem p := by
  simp only [Box.Mem,reflectCell,reflectChart]
  apply forall_congr'
  intro i
  by_cases h : i.val<5
  · simp [h]
  · simp [h,and_comm]

theorem chartPoint_reflect (p : Chart) : chartPoint (reflectChart p)=offsetSwap (chartPoint p) := by
  -- The basis reads only coordinates 0 to 4, which the reflection keeps.
  have hb : chartBasis (reflectChart p)=chartBasis p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chartBasis,reflectChart]
  -- Coordinates 5 to 7 are the fractional offset, which the reflection negates.
  have ho : (![reflectChart p 5,reflectChart p 6,reflectChart p 7] : Vec)= -![p 5,p 6,p 7] := by
    funext i
    fin_cases i <;> simp [reflectChart]
  show (⟨chartBasis (reflectChart p),![reflectChart p 5,reflectChart p 6,reflectChart p 7]⟩ : TwoSite)=
    ⟨chartBasis p,-![p 5,p 6,p 7]⟩
  rw [hb,ho]

theorem good_reflect (p : Chart) (h : good p) : good (reflectChart p) := by
  obtain ⟨⟨det,distinct⟩,reduced,short,cross⟩ := h
  refine ⟨?_,?_,?_⟩
  · rw [chartPoint_reflect]
    exact ⟨det,fun n eq => distinct (-n) (by
      rw [castVec_neg]
      apply neg_injective
      simpa [offsetSwap] using eq)⟩
  · have b := congrArg TwoSite.basis (chartPoint_reflect p)
    change chartBasis (reflectChart p)=chartBasis p at b
    simpa only [reductionInequalities,b,show reflectChart p 0=p 0 by rfl,
      show reflectChart p 1=p 1 by rfl,show reflectChart p 4=p 4 by rfl] using reduced
  · rw [chartPoint_reflect]
    refine ⟨short,?_⟩
    intro n
    have e := cross (-n)
    rw [castVec_neg,show -castVec n+(chartPoint p).offset= -(castVec n+ -(chartPoint p).offset) by abel,
      Matrix.mulVec_neg,sq_neg_vec] at e
    exact e

def positiveHalf : Set Chart := {p | root.Mem p ∧ 0≤p 5}

@[simp] theorem reflectChart_twice (p : Chart) : reflectChart (reflectChart p)=p := by
  funext i
  by_cases h : i.val<5 <;> simp [reflectChart,h]

theorem reflectRoot : reflectCell root=root := by
  show (⟨fun i => if i.val<5 then root.lo i else -root.hi i,
    fun i => if i.val<5 then root.hi i else -root.lo i⟩ : Cell)=⟨root.lo,root.hi⟩
  congr 1 <;> funext i <;> fin_cases i <;> norm_num [root]

def reflectedRoster (rows : List AddressedCell) : List AddressedCell :=
  rows.map (fun a => ⟨a.key,reflectCell a.cell⟩)

theorem reflectedRoster_sound (rows : List AddressedCell) (p : Chart) :
    Held rows (reflectChart p) ↔ Held (reflectedRoster rows) p := by
  constructor
  · rintro ⟨a,ha,he⟩
    have h := (reflectChart_mem a.cell (reflectChart p)).mpr he
    exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simpa using h⟩
  · rintro ⟨r,hr,hp⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
    have h : (reflectCell a.cell).Mem (reflectChart (reflectChart p)) := by simpa using hp
    exact ⟨a,ha,(reflectChart_mem _ _).mp h⟩

/-- The stage-3 mirror join takes an actual positive pass and its inherited
full-chart cover. The intersection includes face-only clips. -/
theorem mirror_handoff (before after : List AddressedCell) (key : Key → Key → Key)
    (old : Handoff chartRoot (cellUnion before))
    (positive : Handoff {p | positiveHalf p ∧ Held before p} (cellUnion after)) :
    Handoff positiveHalf (cellUnion (pairwiseClips key after (reflectedRoster before))) := by
  intro p hp gp
  have pr : positiveHalf p := hp
  rcases old p pr.1 gp with done | left
  · exact Or.inl done
  rcases positive p ⟨pr,left⟩ gp with done | right
  · exact Or.inl done
  have hr : root.Mem (reflectChart p) := by
    rw [← reflectRoot]
    exact (reflectChart_mem root p).mpr pr.1
  rcases old (reflectChart p) hr (good_reflect p gp) with oppositeProof | oppositeHold
  · rw [chartPoint_reflect] at oppositeProof
    exact Or.inl (leaf_of_swap _ oppositeProof)
  · exact Or.inr ((pairwiseClips_exact _ _ _ _).mpr ⟨right,(reflectedRoster_sound _ _).mp oppositeHold⟩)

/-- A cover of the half chart supplies the whole chart, including the seam
and both outer offset faces. Later passes can retain only the positive half. -/
theorem from_positive_half (covered : Handoff positiveHalf ∅) : Handoff chartRoot ∅ := by
  intro p hp gp
  by_cases side : 0≤p 5
  · exact covered p ⟨hp,side⟩ gp
  · have inRoot : root.Mem (reflectChart p) := by
      rw [← reflectRoot]
      exact (reflectChart_mem root p).mpr hp
    have pos : 0≤ reflectChart p 5 := by
      change 0≤ -p 5
      linarith [lt_of_not_ge side]
    have leaf := Handoff.final covered (reflectChart p) ⟨inRoot,pos⟩ (good_reflect p gp)
    rw [chartPoint_reflect] at leaf
    exact Or.inl (leaf_of_swap (chartPoint p) leaf)

end BccSharp.Coulomb.CompactCover
