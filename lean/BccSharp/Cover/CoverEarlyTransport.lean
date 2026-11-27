import BccSharp.Cover.CoverReflection

set_option autoImplicit false

/-! Transport of an entire addressed comparison through an integer
offset shift, or through the stage-3 two-coset swap followed by a shift. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Coverage

def shiftChart (p : Chart) (n : IntVec) : Chart :=
  ![p 0,p 1,p 2,p 3,p 4,p 5+(n 0 : ℝ),p 6+(n 1 : ℝ),p 7+(n 2 : ℝ)]

def shiftAmount (n : IntVec) : Axis → ℚ := ![0,0,0,0,0,(n 0 : ℚ),(n 1 : ℚ),(n 2 : ℚ)]

def shiftCell (b : Cell) (n : IntVec) : Cell :=
  ⟨fun i => b.lo i+shiftAmount n i,fun i => b.hi i+shiftAmount n i⟩

theorem shifted_iff (b : Cell) (n : IntVec) (p : Chart) : (shiftCell b n).Mem p ↔ b.Mem (shiftChart p (-n)) := by
  unfold Box.Mem
  apply forall_congr'
  intro i
  fin_cases i <;> simp [shiftCell,shiftAmount,shiftChart,castVec,sub_eq_add_neg] <;>
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem chartPoint_shift (p : Chart) (n : IntVec) : chartPoint (shiftChart p n)=wrap (chartPoint p) n := by
  have hB : chartBasis (shiftChart p n)=chartBasis p := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hO : (![shiftChart p n 5,shiftChart p n 6,shiftChart p n 7] : Vec)=
      ![p 5,p 6,p 7]+castVec n := by
    ext i
    fin_cases i <;> simp [shiftChart,castVec]
  simp only [chartPoint,wrap,hB,hO]

private theorem shape_shift (p : Chart) (n : IntVec) : chartBasis (shiftChart p n)=chartBasis p := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem good_shift (p : Chart) (n : IntVec) (h : good p) : good (shiftChart p n) := by
  obtain ⟨⟨det,distinct⟩,reduction,short,cross⟩ := h
  refine ⟨?_,?_,?_⟩
  · rw [chartPoint_shift]
    refine ⟨det,fun m h => distinct (m-n) ?_⟩
    have e : (chartPoint p).offset+castVec n=castVec m := h
    rw [sub_eq_add_neg,castVec_add,castVec_neg]
    exact eq_sub_of_add_eq e
  · simpa only [reductionInequalities,shape_shift,show shiftChart p n 0=p 0 by rfl,
      show shiftChart p n 1=p 1 by rfl,show shiftChart p n 4=p 4 by rfl] using reduction
  · rw [chartPoint_shift]
    refine ⟨short,fun m => ?_⟩
    have e := cross (m+n)
    rw [castVec_add] at e
    simpa only [wrap,add_assoc,add_comm (castVec n) (chartPoint p).offset] using e

theorem points_wrap (q : TwoSite) (n : IntVec) : (wrap q n).points=q.points := by
  ext x
  constructor
  · rintro (hx | ⟨y,⟨z,hy⟩,hx⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨q.basis.mulVec (castVec (z+n)),⟨z+n,rfl⟩,?_⟩
      rw [hx,←hy,castVec_add,Matrix.mulVec_add]
      simp only [wrap,Matrix.mulVec_add]
      abel
  · rintro (hx | ⟨y,⟨z,hy⟩,hx⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨q.basis.mulVec (castVec (z-n)),⟨z-n,rfl⟩,?_⟩
      rw [hx,←hy,sub_eq_add_neg,castVec_add,castVec_neg,Matrix.mulVec_add,Matrix.mulVec_neg]
      simp only [wrap,Matrix.mulVec_add]
      abel

theorem leaf_wrap (q : TwoSite) (n : IntVec) (w : LeafProof (wrap q n)) : LeafProof q := by
  have pEq := points_wrap q n
  have hD : defect (wrap q n)=defect q := by simp only [defect,neighbors,pEq]
  have e : deficit (wrap q n)=deficit q := by simp only [deficit,energy_wrap,hD]
  by_cases nonpos : deficit q≤0
  · have h : deficit (wrap q n)≤0 := by simpa only [e]
    obtain ⟨z,k⟩ := leaf_of_nonpositive _ Constants.reference_gap_checked.2 (defect_range _).2 h w
    rw [e] at z
    exact .classifiedNonnegative z.ge (fun _ => by simpa only [IsBCC,IsFCC,pEq] using k)
  · exact .strictDeficit (lt_of_not_ge nonpos)

structure ChartMotion where
  reflected : Bool
  translate : IntVec

def ChartMotion.image (m : ChartMotion) (b : Cell) : Cell :=
  shiftCell (if m.reflected then reflectCell b else b) m.translate

def ChartMotion.preimage (m : ChartMotion) (p : Chart) : Chart :=
  let q := shiftChart p (-m.translate)
  if m.reflected then reflectChart q else q

theorem ChartMotion.pull_mem (m : ChartMotion) (b : Cell) (p : Chart)
    (h : (m.image b).Mem p) : b.Mem (m.preimage p) := by
  have e := (shifted_iff _ _ _).mp h
  cases hflip : m.reflected
  · simpa [ChartMotion.preimage,hflip] using e
  · have hf := (reflectChart_mem b (reflectChart (shiftChart p (-m.translate)))).mp
      (by simpa only [reflectChart_twice,hflip,ite_true] using e)
    simpa [ChartMotion.preimage,hflip] using hf

theorem ChartMotion.pull_good (m : ChartMotion) (p : Chart) (gp : good p) : good (m.preimage p) := by
  unfold ChartMotion.preimage
  split
  · exact good_reflect _ (good_shift _ _ gp)
  · exact good_shift _ _ gp

theorem ChartMotion.push_leaf (m : ChartMotion) (p : Chart)
    (h : LeafProof (chartPoint (m.preimage p))) : LeafProof (chartPoint p) := by
  apply leaf_wrap (chartPoint p) (-m.translate)
  rw [← chartPoint_shift]
  unfold ChartMotion.preimage at h
  split at h
  · rw [chartPoint_reflect] at h
    exact leaf_of_swap _ h
  · exact h

end BccSharp.Coulomb.CompactCover
