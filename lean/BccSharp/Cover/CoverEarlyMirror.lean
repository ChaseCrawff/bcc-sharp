import BccSharp.Cover.CoverEarlyReplay

set_option autoImplicit false

/-! The stage-3 roster keeps only positive-width mirror clips.
Recover boundary points inside the closed, finite union of paid and
held boxes before invoking any physical leaf theorem. -/

noncomputable section
open scoped Topology

namespace BccSharp.Coulomb.CompactCover.EarlyReplay
open BccSharp.Coverage
open Filter Set

def CellStrict (b : Cell) (p : Chart) : Prop :=
  ∀ i, (b.lo i : ℝ) < p i ∧ p i < (b.hi i : ℝ)

theorem CellStrict.mem {b : Cell} {p : Chart} (hp : CellStrict b p) : b.Mem p :=
  fun i => ⟨(hp i).1.le,(hp i).2.le⟩

theorem held_closed (xs : List AddressedCell) : IsClosed {p | Held xs p} := by
  induction xs with
  | nil => simpa [Held] using (isClosed_empty : IsClosed (∅ : Set Chart))
  | cons a xs ih =>
    have hBox : IsClosed {p : Chart | a.cell.Mem p} := by
      have e : {p : Chart | a.cell.Mem p} =
          ⋂ (i : Axis), (fun p : Chart => p i) ⁻¹' Icc (a.cell.lo i : ℝ) (a.cell.hi i : ℝ) := by
        ext p; simp [Box.Mem]
      rw [e]
      exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)
    have unionEq : {p | Held (a::xs) p} = {p : Chart | a.cell.Mem p} ∪ {p | Held xs p} := by
      ext p
      change Held ([a]++xs) p ↔ a.cell.Mem p ∨ Held xs p
      simp [held_append,Held]
    rw [unionEq]
    exact hBox.union ih

theorem covers_closed (s : Snapshot) : IsClosed {p | s.Covers p} :=
  (held_closed s.paid).union (held_closed s.held)

theorem closed_mem_from_strict (b : Cell) (width : positiveCell b=true)
    {C : Set Chart} (closed : IsClosed C) (strict : ∀ p, CellStrict b p → p∈C)
    (p : Chart) (hp : b.Mem p) : p∈C := by
  let mid : Chart := fun i => ((b.lo i : ℝ)+(b.hi i : ℝ))/2
  let f : ℝ → Chart := fun t i => (1-t)*p i+t*mid i
  have cf : Continuous f := by
    apply continuous_pi
    intro i
    dsimp [f]
    fun_prop
  have zero : f 0=p := by ext i; simp [f]
  have tend : Tendsto f (𝓝[Set.Ioi (0:ℝ)] 0) (𝓝 p) :=
    zero ▸ cf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have lower : ∀ᶠ t in 𝓝[Set.Ioi (0:ℝ)] 0, 0<t := self_mem_nhdsWithin
  have upper : ∀ᶠ t in 𝓝[Set.Ioi (0:ℝ)] 0, t<1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have widths : ∀ i, b.lo i<b.hi i := of_decide_eq_true width
  apply closed.mem_of_tendsto tend
  filter_upwards [lower,upper] with t lt ht
  apply strict
  intro i
  have wi : (b.lo i : ℝ)<b.hi i := by exact_mod_cast widths i
  have a : (b.lo i : ℝ)< mid i := by dsimp [mid]; linarith only [wi]
  have d : mid i<(b.hi i : ℝ) := by dsimp [mid]; linarith only [wi]
  have pL := mul_nonneg (sub_pos.mpr ht).le (sub_nonneg.mpr (hp i).1)
  have pU := mul_nonneg (sub_pos.mpr ht).le (sub_nonneg.mpr (hp i).2)
  have mL := mul_pos lt (sub_pos.mpr a)
  have mU := mul_pos lt (sub_pos.mpr d)
  dsimp [f]
  exact ⟨by nlinarith only [pL,mL],by nlinarith only [pU,mU]⟩

private theorem intersection_has_width {a b : Cell} {p : Chart}
    (ha : CellStrict a p) (hb : b.Mem p) (wb : positiveCell b=true) :
    positiveCell (intersection a b)=true := by
  have w : ∀ i, b.lo i<b.hi i := of_decide_eq_true wb
  apply decide_eq_true
  intro i
  have h : (max (a.lo i : ℝ) (b.lo i : ℝ))< min (a.hi i : ℝ) (b.hi i : ℝ) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    exact ⟨⟨(ha i).1.trans (ha i).2,(ha i).1.trans_le (hb i).2⟩,
      ⟨(hb i).1.trans_lt (ha i).2,by exact_mod_cast w i⟩⟩
  exact_mod_cast h

def MirrorClips (key : Key → Key → Key) (pos opposite : List AddressedCell) : List AddressedCell :=
  pos.flatMap fun a => opposite.filterMap fun b =>
    let clipped := intersection a.cell b.cell
    if positiveCell clipped then some ⟨key a.key b.key,clipped⟩ else none

theorem mirrorClips_mem (key : Key → Key → Key) {pos opposite : List AddressedCell}
    {a b : AddressedCell} (ha : a∈pos) (hb : b∈opposite) {p : Chart}
    (hA : CellStrict a.cell p) (hB : b.cell.Mem p) (hw : positiveCell b.cell=true) :
    Held (MirrorClips key pos opposite) p := by
  have w := intersection_has_width hA hB hw
  refine ⟨⟨key a.key b.key,intersection a.cell b.cell⟩,?_,(mem_intersection _ _ _).mpr ⟨hA.mem,hB⟩⟩
  apply List.mem_flatMap.mpr
  exact ⟨a,ha,List.mem_filterMap.mpr ⟨b,hb,by simp [w]⟩⟩

def nonpositive (rows : List AddressedCell) : List AddressedCell :=
  rows.filter (fun a => decide (a.cell.hi 5≤0))

def halvesCheck (before : Snapshot) : Bool :=
  before.held.all (fun a => decide (0≤a.cell.lo 5 ∨ a.cell.hi 5≤0))

def mirror (key : Key → Key → Key) (before afterPositive : Snapshot) : Option Snapshot :=
  let opposite := reflectedRoster (nonpositive before.held)
  if (halvesCheck before && afterPositive.held.all (fun a => positiveCell a.cell && decide (0≤a.cell.lo 5))) &&
      opposite.all (fun a => positiveCell a.cell) then
    some ⟨afterPositive.paid++reflectedRoster before.paid,MirrorClips key afterPositive.held opposite⟩
  else none

/-- The old full-chart snapshot and checked positive pass imply the
complete mirror handoff, including offset zero and face-only contacts. -/
theorem mirror_sound (key : Key → Key → Key) (old pos out : Snapshot)
    (ho : old.Sound) (hp : pos.Sound)
    (coverOld : ∀ p, root.Mem p → old.Covers p)
    (coverPos : ∀ p, p∈positiveHalf → pos.Covers p)
    (within : pos.held.all (fun a => insideCheck a.cell root)=true)
    (eq : mirror key old pos=some out) : out.Sound ∧ (∀ p, p∈positiveHalf → out.Covers p) := by
  let opposite := reflectedRoster (nonpositive old.held)
  by_cases admissible : ((halvesCheck old && pos.held.all (fun a => positiveCell a.cell &&
      decide (0≤a.cell.lo 5))) && opposite.all (fun a => positiveCell a.cell))=true
  · have eo : (⟨pos.paid++reflectedRoster old.paid,MirrorClips key pos.held opposite⟩ : Snapshot)=out := by
      simpa [mirror,opposite,admissible] using eq
    subst out
    obtain ⟨hpPos,negative⟩ := Bool.and_eq_true_iff.mp admissible
    obtain ⟨sep,positive⟩ := Bool.and_eq_true_iff.mp hpPos
    constructor
    · intro p paid goodP
      rcases held_append.mp paid with pa | reflected
      · exact hp p pa goodP
      · have original := ho _ ((reflectedRoster_sound old.paid p).mpr reflected) (good_reflect _ goodP)
        rw [chartPoint_reflect] at original
        exact leaf_of_swap _ original
    · intro p hpHalf
      rcases coverPos p hpHalf with already | ⟨a,ha,hpA⟩
      · exact Or.inl (held_append.mpr (Or.inl already))
      obtain ⟨wa,side⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp positive a ha)
      have cs : IsClosed {p | (⟨pos.paid++reflectedRoster old.paid,
          MirrorClips key pos.held opposite⟩ : Snapshot).Covers p} := covers_closed _
      apply closed_mem_from_strict a.cell wa cs _ p hpA
      intro q hq
      have lo : (0:ℝ)≤a.cell.lo 5 := by exact_mod_cast (of_decide_eq_true side : 0≤a.cell.lo 5)
      have neg : reflectChart q 5<0 := by change -q 5<0; linarith only [lo,(hq 5).1]
      have hRoot : root.Mem (reflectChart q) := by
        rw [←reflectRoot]
        exact (reflectChart_mem _ _).mpr (insideCheck_sound (List.all_eq_true.mp within a ha) hq.mem)
      rcases coverOld _ hRoot with paid | ⟨b,hb,hbq⟩
      · exact Or.inl (held_append.mpr (Or.inr ((reflectedRoster_sound _ _).mp paid)))
      · have sides : 0≤b.cell.lo 5 ∨ b.cell.hi 5≤0 := of_decide_eq_true (List.all_eq_true.mp sep b hb)
        have n : b.cell.hi 5≤0 := sides.resolve_left fun left => by
          have l : (0:ℝ)≤b.cell.lo 5 := by exact_mod_cast left
          linarith only [l,(hbq 5).1,neg]
        have member : (⟨b.key,reflectCell b.cell⟩ : AddressedCell) ∈ opposite := by
          apply List.mem_map.mpr
          exact ⟨b,List.mem_filter.mpr ⟨hb,decide_eq_true n⟩,rfl⟩
        have qb : (reflectCell b.cell).Mem q := by
          simpa using (reflectChart_mem b.cell (reflectChart q)).mpr hbq
        exact Or.inr (mirrorClips_mem key ha member hq qb (List.all_eq_true.mp negative _ member))
  · simp [mirror,opposite,admissible] at eq

end BccSharp.Coulomb.CompactCover.EarlyReplay
