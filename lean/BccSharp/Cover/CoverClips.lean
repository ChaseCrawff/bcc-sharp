import BccSharp.Cover.CoverLatePackets

set_option autoImplicit false

/-! Exact closed-box partition operations shared by stage-3, Stage4, Stage5a,
and Stage5b. Clip cuts always retain the common face. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Coverage

def insideCheck (inner outer : Cell) : Bool :=
  decide (∀ i, outer.lo i ≤ inner.lo i ∧ inner.hi i ≤ outer.hi i)

theorem insideCheck_sound {inner outer : Cell} (ok : insideCheck inner outer=true)
    {p : Chart} (hp : inner.Mem p) : outer.Mem p := by
  have e : ∀ i, outer.lo i ≤ inner.lo i ∧ inner.hi i ≤ outer.hi i := of_decide_eq_true ok
  intro i
  exact ⟨(by exact_mod_cast (e i).1 : (outer.lo i : ℝ)≤ inner.lo i).trans (hp i).1,
    (hp i).2.trans (by exact_mod_cast (e i).2)⟩

def positiveCell (b : Cell) : Bool := decide (∀ i, b.lo i<b.hi i)

structure SlabCut where
  axis : Axis
  cut : ℚ
  keepUpper : Bool

def SlabCut.keep (s : SlabCut) (b : Cell) : Cell := replaceEnd b s.axis s.cut s.keepUpper
def SlabCut.slab (s : SlabCut) (b : Cell) : Cell := replaceEnd b s.axis s.cut (!s.keepUpper)

def SlabCut.check (s : SlabCut) (b : Cell) : Bool :=
  decide (b.lo s.axis < s.cut ∧ s.cut < b.hi s.axis)

def carve : Cell → List SlabCut → Option (List Cell × Cell)
  | b, [] => some ([],b)
  | b,s::ss =>
      if s.check b then do
        let (tail,clip) ← carve (s.keep b) ss
        pure (s.slab b::tail,clip)
      else none

theorem carve_cover (b : Cell) (steps : List SlabCut) (slabs : List Cell) (clip : Cell)
    (ok : carve b steps=some (slabs,clip)) (p : Chart) (hp : b.Mem p) :
    (∃ s ∈ slabs, s.Mem p) ∨ clip.Mem p := by
  induction steps generalizing b slabs clip with
  | nil =>
      have e : ([],b)=(slabs,clip) := Option.some.inj ok
      have ec : b = clip := (Prod.mk.inj e).2
      rw [← ec]
      exact Or.inr hp
  | cons s ss ih =>
      by_cases fits : s.check b=true
      · cases er : carve (s.keep b) ss with
        | none => simp [carve,fits,er] at ok
        | some result =>
          rcases result with ⟨more,target⟩
          have e : (s.slab b::more,target)=(slabs,clip) := by simpa [carve,fits,er] using ok
          obtain ⟨es, ec⟩ := Prod.mk.inj e
          rw [← es, ← ec]
          have sides : (s.slab b).Mem p ∨ (s.keep b).Mem p := by
            cases ee : s.keepUpper
            · simpa [SlabCut.keep,SlabCut.slab,ee,or_comm] using two_closed_children b s.axis s.cut p hp
            · simpa [SlabCut.keep,SlabCut.slab,ee] using two_closed_children b s.axis s.cut p hp
          rcases sides with out | into
          · exact Or.inl ⟨s.slab b,List.mem_cons_self,out⟩
          · rcases ih (s.keep b) more target er into with ⟨k,hk,km⟩ | inside
            · exact Or.inl ⟨k,List.mem_cons_of_mem _ hk,km⟩
            · exact Or.inr inside
      · simp [carve,fits] at ok

def clipSteps (b clip : Cell) : List SlabCut :=
  (List.finRange 8).flatMap fun i =>
    (if b.lo i < clip.lo i then [⟨i,clip.lo i,true⟩] else []) ++
    (if clip.hi i < b.hi i then [⟨i,clip.hi i,false⟩] else [])

/-- Produce slabs for the exact intersection, retaining the original on
degenerate or disjoint intersections. Arithmetical evidence belongs to
the source rectangle and is restricted by the checked containment. -/
def checkedSubtract (parent source : Cell) : Option (List Cell × Option Cell) :=
  let intended := intersection parent source
  if positiveCell intended then do
    let (slabs,reached) ← carve parent (clipSteps parent intended)
    if sameCell reached intended && insideCheck reached source then pure (slabs,some reached) else none
  else some ([parent],none)

theorem checkedSubtract_sound (parent source : Cell) (rest : List Cell) (credit : Option Cell)
    (ok : checkedSubtract parent source=some (rest,credit)) (p : Chart) (hp : parent.Mem p) :
    (∃ s ∈ rest, s.Mem p) ∨ (∃ c, credit=some c ∧ c.Mem p ∧ source.Mem p) := by
  simp only [checkedSubtract] at ok
  by_cases live : positiveCell (intersection parent source)=true
  · rw [ite_eq_left live] at ok
    cases he : carve parent (clipSteps parent (intersection parent source)) with
    | none =>
      rw [he] at ok
      simp at ok
    | some result =>
      rcases result with ⟨slabs,reached⟩
      rw [he] at ok
      change (if (sameCell reached (intersection parent source) && insideCheck reached source) = true
        then some (slabs,some reached) else none) = some (rest,credit) at ok
      by_cases bounded : (sameCell reached (intersection parent source) && insideCheck reached source)=true
      · rw [ite_eq_left bounded] at ok
        obtain ⟨er, ec⟩ := Prod.mk.inj (Option.some.inj ok)
        rw [← er, ← ec]
        exact (carve_cover parent _ slabs reached he p hp).imp_right fun h =>
          ⟨reached,rfl,h,insideCheck_sound (Bool.and_eq_true_iff.mp bounded).2 h⟩
      · rw [ite_eq_right bounded] at ok
        simp at ok
  · rw [ite_eq_right live] at ok
    obtain ⟨er, ec⟩ := Prod.mk.inj (Option.some.inj ok)
    rw [← er, ← ec]
    exact Or.inl ⟨parent,by simp,hp⟩

theorem coalesce_closed_siblings (parent : Cell) (s : Cut) (fits : s.fits parent=true) (p : Chart) :
    parent.Mem p ↔ (s.child parent false).Mem p ∨ (s.child parent true).Mem p := by
  have range : parent.lo (s.position parent).1 ≤ (s.position parent).2 ∧
      (s.position parent).2 ≤ parent.hi (s.position parent).1 := of_decide_eq_true fits
  refine ⟨fun h => two_closed_children parent _ _ _ h,?_⟩
  rintro (lo | hi) i
  · by_cases e : i=(s.position parent).1
    · subst i
      have h := lo (s.position parent).1
      simp [Cut.child,replaceEnd] at h
      exact ⟨h.1,h.2.trans (by exact_mod_cast range.2)⟩
    · simpa [Cut.child,replaceEnd,e] using lo i
  · by_cases e : i=(s.position parent).1
    · subst i
      have h := hi (s.position parent).1
      simp [Cut.child,replaceEnd] at h
      exact ⟨(by exact_mod_cast range.1 : (parent.lo (s.position parent).1 : ℝ) ≤ (s.position parent).2).trans h.1,h.2⟩
    · simpa [Cut.child,replaceEnd,e] using hi i

end BccSharp.Coulomb.CompactCover
