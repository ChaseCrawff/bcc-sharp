import BccSharp.Cover.CoverClips

set_option autoImplicit false

/-! Common-corner finishing rules for Corner, JointDeficit and Continuation.
The expression-level lower support and registered upper cost are explicit
analytic interfaces. This module checks the finite common-corner minimum
and justifies the cap blend and signed comparison with Constants's endpoints. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Coverage

def corner (b : Cell) (bits : Axis → Bool) : Chart := fun i =>
  if bits i then b.hi i else b.lo i

def atLower (b : Cell) (p : Chart) (i : Axis) := Function.update p i (b.lo i : ℝ)
def atUpper (b : Cell) (p : Chart) (i : Axis) := Function.update p i (b.hi i : ℝ)

private theorem endpoint_mem (b : Cell) (p : Chart) (hp : b.Mem p) (i : Axis) :
    b.Mem (atLower b p i) ∧ b.Mem (atUpper b p i) := by
  have order : (b.lo i : ℝ) ≤ b.hi i := (hp i).1.trans (hp i).2
  constructor
  · intro j
    by_cases eq : j=i
    · rw [eq]
      have e : atLower b p i i = b.lo i := Function.update_self _ _ _
      rw [e]
      exact ⟨le_rfl, order⟩
    · have e : atLower b p i j = p j := Function.update_of_ne eq _ _
      rw [e]
      exact hp j
  · intro j
    by_cases eq : j=i
    · rw [eq]
      have e : atUpper b p i i = b.hi i := Function.update_self _ _ _
      rw [e]
      exact ⟨order, le_rfl⟩
    · have e : atUpper b p i j = p j := Function.update_of_ne eq _ _
      rw [e]
      exact hp j

/-- The two-point chord for the interval determined by the actual leaf.
The same interpolation parameter is required for the two constituents
of a signed comparison. -/
def ChordLower (b : Cell) (f : Chart → ℝ) : Prop :=
  ∀ p, b.Mem p → ∀ i : Axis, ∀ t : ℝ, 0≤t → t≤1 →
    p i=(1-t)*(b.lo i : ℝ)+t*(b.hi i : ℝ) →
    (1-t)*f (atLower b p i)+t*f (atUpper b p i)≤f p

def ChordUpper (b : Cell) (f : Chart → ℝ) : Prop := ChordLower b (fun p => -f p)

private theorem chord_min (b : Cell) (f : Chart → ℝ) (h : ChordLower b f)
    (p : Chart) (hp : b.Mem p) (i : Axis) : min (f (atLower b p i)) (f (atUpper b p i))≤f p := by
  by_cases e : (b.lo i : ℝ)=b.hi i
  · have pi : p i=b.lo i := le_antisymm ((hp i).2.trans_eq e.symm) (hp i).1
    have low : atLower b p i=p := by
      funext j
      by_cases eq : j=i <;> simp_all [atLower]
    rw [low]
    exact min_le_left _ _
  · have positive : 0<((b.hi i : ℝ)-b.lo i) := sub_pos.mpr (lt_of_le_of_ne ((hp i).1.trans (hp i).2) e)
    let t := (p i-b.lo i)/((b.hi i : ℝ)-b.lo i)
    have lo : 0≤t := div_nonneg (sub_nonneg.mpr (hp i).1) positive.le
    have hi : t≤1 := (div_le_one positive).mpr (sub_le_sub_right (hp i).2 _)
    have eq : p i=(1-t)*(b.lo i : ℝ)+t*(b.hi i : ℝ) := by
      dsimp [t]; field_simp [positive.ne'] <;> ring
    have k := add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left (f (atLower b p i)) (f (atUpper b p i))) (sub_nonneg.mpr hi))
      (mul_le_mul_of_nonneg_left (min_le_right (f (atLower b p i)) (f (atUpper b p i))) lo)
    rw [← add_mul,sub_add_cancel,one_mul] at k
    exact k.trans (h p hp i t lo hi eq)

theorem corner_le (b : Cell) (f : Chart → ℝ) (h : ChordLower b f) (p : Chart) (hp : b.Mem p) :
    ∃ bits, f (corner b bits)≤f p := by
  classical
  have extend (s : Finset Axis) : ∃ q, b.Mem q ∧ f q≤f p ∧ ∀ i∈s, q i=b.lo i ∨ q i=b.hi i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨p,hp,le_rfl,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨q,hq,hf,known⟩ := ih
      obtain ⟨lo,up⟩ := endpoint_mem b q hq i
      have e := chord_min b f h q hq i
      rcases le_total (f (atLower b q i)) (f (atUpper b q i)) with a | d
      · refine ⟨atLower b q i,lo,(min_eq_left a ▸ e).trans hf,?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inl (by simp [atLower])
        · have neq : j≠i := fun r => hi (r ▸ hj)
          have same : atLower b q i j = q j := Function.update_of_ne neq _ _
          rw [same]
          exact known j hj
      · refine ⟨atUpper b q i,up,(min_eq_right d ▸ e).trans hf,?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inr (by simp [atUpper])
        · have neq : j≠i := fun r => hi (r ▸ hj)
          have same : atUpper b q i j = q j := Function.update_of_ne neq _ _
          rw [same]
          exact known j hj
  obtain ⟨q,_,e,k⟩ := extend Finset.univ
  let bits (i : Axis) := decide (q i=(b.hi i : ℝ))
  have eq : corner b bits=q := by
    funext i
    by_cases eq : q i=(b.hi i : ℝ)
    · simp [corner,bits,eq]
    · have lo := (k i (Finset.mem_univ i)).resolve_right eq
      have low : bits i = false := by simp [bits,eq]
      have c : corner b bits i = (b.lo i : ℝ) := by simp [corner,low]
      rw [c]
      exact lo.symm
  exact ⟨bits,eq.symm ▸ e⟩

abbrev CornerLower := (Axis → Bool) → ℚ

def cornerCheck (lower : CornerLower) : Bool := decide (∀ s : Axis → Bool, 0<lower s)

theorem cornerCheck_sound (b : Cell) (f : Chart → ℝ) (chord : ChordLower b f)
    (lower : CornerLower) (enclose : ∀ s, (lower s : ℝ)≤f (corner b s))
    (ok : cornerCheck lower=true) (p : Chart) (hp : b.Mem p) : 0<f p := by
  obtain ⟨bits,hbits⟩ := corner_le b f chord p hp
  have pos : 0<lower bits := (of_decide_eq_true ok : ∀ s, _) bits
  exact (show (0 : ℝ)<lower bits by exact_mod_cast pos).trans_le ((enclose bits).trans hbits)

def mixedDefect (weight : ℕ) (C : ℝ) : ℝ :=
  let t : ℝ := (weight : ℝ)/4096
  1-t+t*C

def jointFunction (T C : Chart → ℝ) (weight : ℕ) (p : Chart) : ℝ :=
  T p-(Constants.bccBracket.hi : ℝ)-(Constants.gapBracket.hi : ℝ)*mixedDefect weight (C p)

theorem jointChord (b : Cell) (T C : Chart → ℝ) (weight : ℕ)
    (energyChord : ChordLower b T) (costChord : ChordUpper b C) : ChordLower b (jointFunction T C weight) := by
  intro p hp i t t₀ t₁ coord
  have energy := energyChord p hp i t t₀ t₁ coord
  have cost := costChord p hp i t t₀ t₁ coord
  have gu : (0 : ℝ)≤ Constants.gapBracket.hi := Constants.reference_gap_checked.2.le.trans Constants.reference_gap_checked.1.2
  have a : (0 : ℝ)≤(Constants.gapBracket.hi : ℝ)*((weight : ℝ)/4096) := by positivity
  have e := mul_le_mul_of_nonneg_left cost a
  unfold jointFunction mixedDefect
  linarith only [energy,e]

theorem jointCorner_sound (b : Cell) (T C : Chart → ℝ) (weight : ℕ) (lower : CornerLower)
    (mix : weight≤4096) (energyChord : ChordLower b T) (costChord : ChordUpper b C)
    (energyLower : ∀ p, b.Mem p → good p → T p≤energy (chartPoint p))
    (defectUpper : ∀ p, b.Mem p → good p → defect (chartPoint p)≤C p)
    (corners : ∀ bits, (lower bits : ℝ)≤jointFunction T C weight (corner b bits))
    (ok : cornerCheck lower=true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    Route.result .strictJoint p := by
  have h := cornerCheck_sound b _ (jointChord b T C weight energyChord costChord) lower corners ok p hp
  have hT := energyLower p hp gp
  have hC := defectUpper p hp gp
  have hB : energy bcc ≤ (Constants.bccBracket.hi : ℝ) := (Constants.reference_bounds .bcc).2
  have hg := Constants.reference_gap_checked.1.2
  have nng := Constants.reference_gap_checked.2.le.trans hg
  let t : ℝ := (weight : ℝ)/4096
  have t₀ : 0≤t := by dsimp [t]; positivity
  have t₁ : t≤1 := (div_le_one (by norm_num : (0 : ℝ)<4096)).mpr (by exact_mod_cast mix)
  have hd := defect_range (chartPoint p)
  have cap : defect (chartPoint p)≤ mixedDefect weight (C p) := by
    have cap1 := mul_le_mul_of_nonneg_left hd.2 (sub_nonneg.mpr t₁)
    have cap2 := mul_le_mul_of_nonneg_left hC t₀
    show defect (chartPoint p) ≤ 1-t+t*C p
    linarith only [cap1,cap2]
  have credit := mul_le_mul hg cap hd.1 nng
  change 0<deficit (chartPoint p)
  unfold deficit jointFunction at *
  linarith only [h,hT,hB,credit]

end BccSharp.Coulomb.CompactCover
