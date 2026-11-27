import BccSharp.Cover.Stage2Bulk

set_option autoImplicit false

/-! Stage2 reciprocal phase budget. A proposed allocation pays
against the residual of the same tangents and the same phase floors.
The signed-zero and capacity tests are exact. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Stage2
open BccSharp.Coverage DirectRoute BravaisCover
open BccSharp.Intervals (Ball)

def waveUpper (b : Cell) (n : IntVec) : ℚ :=
  (Finset.univ : Finset (Fin 5 → Bool)).sup' Finset.univ_nonempty fun s => dualCorner (shapePart b s) n

theorem waveUpper_sound (b : Cell) (p : Chart) (n : IntVec) (hp : b.Mem p) (hd : diagonalsCheck b=true) :
    quad (gram (chartBasis p))⁻¹ (castVec n)≤(waveUpper b n : ℝ) := by
  obtain ⟨h0,h1⟩ := radialLoPos b hd
  have p0 := h0.trans_le (hp 0).1
  have p1 := h1.trans_le (hp 1).1
  rw [←dualRadial_eq n p p0.ne' p1.ne']
  obtain ⟨bits,upper⟩ := corner_le (squareDiag b) (fun q => -dualRadial n q) (dualRadial_chord n b hd) _
    (squarePoint_mem hp hd)
  have eq : (⟨.reciprocal,n⟩ : Mode).atCorner b bits=dualCorner (shapePart b (selectShape bits)) n := by
    norm_num [Mode.atCorner,dualCorner,shapePart,selectShape,squaredCorner,cornerRat]
  have cmp : dualCorner (shapePart b (selectShape bits)) n≤waveUpper b n :=
    Finset.le_sup' (fun s => dualCorner (shapePart b s) n) (Finset.mem_univ (selectShape bits))
  have value := Mode.atCorner_eq b bits ⟨.reciprocal,n⟩
  rw [eq] at value
  -- The reciprocal radial of the mode is `dualRadial` by definition.
  have radial : Mode.radial ⟨.reciprocal,n⟩ (corner (squareDiag b) bits)=
      dualRadial n (corner (squareDiag b) bits) := rfl
  rw [radial] at value
  calc dualRadial n (squarePoint p) ≤ dualRadial n (corner (squareDiag b) bits) := neg_le_neg_iff.mp upper
    _ = (dualCorner (shapePart b (selectShape bits)) n : ℝ) := value.symm
    _ ≤ (waveUpper b n : ℝ) := Rat.cast_le.mpr cmp

def capacity (b : Cell) (m : Mode) : Option ℚ := do
  if m.family=.reciprocal then
    let x ← reciprocalLower (Ball.exact (waveUpper b m.index))
    pure (max 0 (lower96 (2*x)))
  else some 0

theorem capacity_sound (b : Cell) (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hv : (chartPoint p).Valid) (m : Mode) (valid : m.valid) (dual : m.family=.reciprocal)
    (cap : ℚ) (ok : capacity b m=some cap) : (cap : ℝ)≤2* seriesReciprocalTerm (chartPoint p) m.index := by
  let n := m.index
  let q := chartPoint p
  have npos : lexPositive n := valid.2.resolve_left (by simp [dual])
  have strict := reciprocalPositive hv (lex_ne npos)
  let u := waveUpper b n
  have up := waveUpper_sound b p n hp hd
  have pos := strict.trans_le up
  cases eval : reciprocalLower (Ball.exact u) with
  | none => simp [capacity,dual,u,n,eval] at ok
  | some x =>
    have e : cap=max 0 (lower96 (2*x)) := by simpa [capacity,dual,u,n,eval,eq_comm] using ok
    have atUpper := oneLower_sound (Ball.contains_exact u) pos _ _ eval
    have k := atUpper.trans (oneKernel_decreasing (mul_pos Real.pi_pos strict)
      (mul_le_mul_of_nonneg_left up Real.pi_pos.le))
    rw [e,seriesReciprocalTerm,if_neg (lex_ne npos)]
    push_cast
    apply max_le
    · rw [gKernel_one (mul_pos Real.pi_pos strict)]
      exact mul_nonneg (by norm_num) (div_nonneg (Real.exp_pos _).le (mul_nonneg Real.pi_pos.le strict.le))
    · exact (Rat.cast_le.mpr (lower96_le _)).trans (by push_cast; exact mul_le_mul_of_nonneg_left k (by norm_num))

structure Allocation where
  a : IntVec
  b : IntVec
  c : IntVec
  minusB : Bool
  minusC : Bool
  amount : ℚ

def wave (i : IntVec) : Mode := ⟨.reciprocal,i⟩
def signed (minus : Bool) (n : IntVec) : IntVec := if minus then -n else n
def Allocation.members (r : Allocation) : Finset Mode := {wave r.a,wave r.b,wave r.c}

def Allocation.valid (r : Allocation) (s : Finset Mode) : Prop :=
  0≤ r.amount ∧ r.members⊆s ∧ r.a≠r.b ∧ r.a≠r.c ∧ r.b≠r.c ∧
    r.a+signed r.minusB r.b+signed r.minusC r.c=0

instance (r : Allocation) (s : Finset Mode) : Decidable (r.valid s) := by unfold Allocation.valid; infer_instance

private theorem cos_triangle (x y z : ℝ) (sum : x+y+z=0) :
    3/2≤(1+Real.cos x)+(1+Real.cos y)+(1+Real.cos z) := by
  have cosz : Real.cos z=Real.cos (x+y) := by rw [show z= -(x+y) by linarith only [sum],Real.cos_neg]
  rw [cosz,Real.cos_add]
  nlinarith only [Real.sin_sq_add_cos_sq x,Real.sin_sq_add_cos_sq y,
    sq_nonneg (1+Real.cos x+Real.cos y),sq_nonneg (Real.sin x-Real.sin y)]

theorem Allocation.phaseFloor (r : Allocation) (s : Finset Mode) (h : r.valid s) (q : TwoSite) :
    (3/2:ℝ)≤∑ m∈r.members,phaseFactor q m.index := by
  obtain ⟨_,_,ab,ac,bc,zero⟩ := h
  let angle (n : IntVec) := 2*Real.pi*dot (castVec n) q.offset
  have add (a b : IntVec) : angle (a+b)=angle a+angle b := by
    simp [angle,castVec_add,dot,add_mul,Finset.sum_add_distrib,mul_add]
  have neg (a : IntVec) : angle (-a) = -angle a := by
    simp [angle,castVec_neg,dot,Finset.sum_neg_distrib,mul_neg,neg_mul]
  have signPhase (s : Bool) (n : IntVec) : Real.cos (angle (signed s n))=Real.cos (angle n) := by
    cases s <;> simp [signed,neg,Real.cos_neg]
  have eq := congrArg angle zero
  simp only [add] at eq
  have angleZero : angle 0=0 := by simp [angle,castVec,dot]
  rw [angleZero] at eq
  have lo := cos_triangle _ _ _ eq
  simp only [signPhase] at lo
  have wab : wave r.a≠wave r.b := fun h => ab (congrArg Mode.index h)
  have wac : wave r.a≠wave r.c := fun h => ac (congrArg Mode.index h)
  have wbc : wave r.b≠wave r.c := fun h => bc (congrArg Mode.index h)
  have wa : wave r.a∉({wave r.b,wave r.c} : Finset Mode) := by simp [wab,wac]
  rw [Allocation.members,Finset.sum_insert wa,Finset.sum_insert (by simpa using wbc),Finset.sum_singleton]
  unfold wave phaseFactor angle at *
  linarith only [lo]

def spent (budget : Array Allocation) (m : Mode) : ℚ :=
  ∑ i : Fin budget.size, if m∈budget[i].members then budget[i].amount else 0

def budgetGain (xs : List Line) (budget : Array Allocation) : ℚ :=
  ∑ i : Fin budget.size,budget[i].amount*(3/2-∑ m∈budget[i].members,floorAt xs m)

def capCheck (b : Cell) (budget : Array Allocation) (m : Mode) : Bool :=
  if spent budget m=0 then true else
    match capacity b m with
    | none => false
    | some c => decide (spent budget m≤ c)

def budgetCheck (b : Cell) (xs : List Line) (budget : Array Allocation) : Bool :=
  decide (∀ i : Fin budget.size,budget[i].valid (retained xs)) &&
    decide (∀ m∈retained xs,capCheck b budget m=true)

theorem budget_sound (b : Cell) (xs : List Line) (budget : Array Allocation) (checked : budgetCheck b xs budget=true)
    (inputs : List AnchorRow) (evaluation : prepare b inputs=some xs) (p : Chart) (hp : b.Mem p)
    (hd : diagonalsCheck b=true) (hv : (chartPoint p).Valid) :
    (budgetGain xs budget : ℝ)≤∑ m∈retained xs,residualAt xs (chartPoint p) m := by
  let q := chartPoint p
  let s := retained xs
  let gap (m : Mode) := phaseFactor q m.index-(floorAt xs m : ℝ)
  have valid : ∀ i : Fin budget.size,budget[i].valid s := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1
  have caps : ∀ m∈s,capCheck b budget m=true := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2
  have incidence (i : Fin budget.size) :
      (budget[i].amount : ℝ)*(3/2-∑ m∈budget[i].members,(floorAt xs m : ℝ)) ≤
        ∑ m∈s,if m∈budget[i].members then (budget[i].amount : ℝ)*gap m else 0 := by
    let a := budget[i]
    have lower := a.phaseFloor s (valid i) q
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_right lower (∑ m∈a.members,(floorAt xs m : ℝ)))
      (by exact_mod_cast (valid i).1 : (0:ℝ)≤a.amount)
    have incl : s.filter (fun m => m∈a.members)=a.members := by
      ext m
      exact ⟨fun e => (Finset.mem_filter.mp e).2,fun e => Finset.mem_filter.mpr ⟨(valid i).2.1 e,e⟩⟩
    rw [←Finset.sum_sub_distrib,Finset.mul_sum] at h
    rw [←Finset.sum_filter,incl]
    exact h
  have distribute : (∑ i : Fin budget.size,∑ m∈s,if m∈budget[i].members then
      (budget[i].amount : ℝ)*gap m else 0) = ∑ m∈s,(spent budget m : ℝ)*gap m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    unfold spent
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have perMode (m : Mode) (hm : m∈s) : (spent budget m : ℝ)*gap m≤ residualAt xs q m := by
    have info := preparedMode b inputs xs evaluation p hp hd hv m hm
    by_cases used : spent budget m=0
    · simpa [used] using info.2.2.1
    · have dual : m.family=.reciprocal := by
        by_contra no
        apply used
        unfold spent
        apply Finset.sum_eq_zero
        intro i _
        have nope : m∉budget[i].members := by
          intro h
          have e : m=wave budget[i].a ∨ m=wave budget[i].b ∨ m=wave budget[i].c := by
            simpa [Allocation.members] using h
          rcases e with rfl | rfl | rfl <;> exact no rfl
        exact ite_eq_right nope
      cases cap : capacity b m with
      | none =>
        have h := caps m hm
        simp [capCheck,used,cap] at h
      | some c =>
        obtain ⟨line,found⟩ := existsLine xs m (List.mem_toFinset.mp hm)
        have modeEq := (findLine_sound xs m line found).2
        have formula : residualAt xs q m=2*gap m* seriesReciprocalTerm q m.index := by
          simp [residualAt,floorAt,found,Line.residual,modeEq,dual,gap]
        have pos := reciprocalPositive hv (lex_ne (info.1.2.resolve_left (by simp [dual])))
        have gpos : 0< seriesReciprocalTerm q m.index := by
          have hn := lex_ne (info.1.2.resolve_left (by simp [dual]))
          rw [seriesReciprocalTerm,if_neg hn,gKernel_one (mul_pos Real.pi_pos pos)]
          exact div_pos (Real.exp_pos _) (mul_pos Real.pi_pos pos)
        have nn : 0≤gap m := by
          by_contra! e
          have hneg := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num : (0:ℝ)<2) e) gpos
          exact (not_lt_of_ge (formula ▸ info.2.2.1)) hneg
        have paid : spent budget m≤ c := of_decide_eq_true (by simpa [capCheck,used,cap] using caps m hm)
        have upper := (Rat.cast_le.mpr paid).trans (capacity_sound b p hp hd hv m info.1 dual c cap)
        rw [formula]
        have credit := mul_le_mul_of_nonneg_right upper nn
        linarith only [credit]
  unfold budgetGain
  push_cast
  exact (Finset.sum_le_sum (fun i _ => incidence i)).trans (distribute ▸ Finset.sum_le_sum (fun m hm => perMode m hm))

/- The fold runs over the distinct retained modes, `(xs.map Line.mode).dedup`,
whose `toFinset` is `retained xs`. `Finset.toList` has no executable code, and
the minimum (and any `none`) does not depend on the order of the modes. -/
private def shrinkBudget (b : Cell) (xs : List Line) (budget : Array Allocation) : Option (Array Allocation) := do
  let scale ← (xs.map Line.mode).dedup.foldlM (fun current m =>
    let charge := spent budget m
    if 0<charge then do
      let c ← capacity b m
      pure (min current (max 0 (c/charge)))
    else some current) (1:ℚ)
  pure (budget.map fun r => {r with amount := scale*r.amount})

/-- A new scalar enclosure can reduce a capacity. Preserve the old
allocation as a proposal and, if needed, shrink it before checking all
actual incidences again. -/
def checkedBudget (b : Cell) (xs : List Line) (budget : Array Allocation) : Option ℚ := do
  if budgetCheck b xs budget then pure (budgetGain xs budget)
  else
    let candidate ← shrinkBudget b xs budget
    if budgetCheck b xs candidate then pure (budgetGain xs candidate) else none

theorem checkedBudget_sound (b : Cell) (xs : List Line) (budget : Array Allocation) (value : ℚ)
    (ok : checkedBudget b xs budget=some value) (inputs : List AnchorRow) (evaluation : prepare b inputs=some xs)
    (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b=true) (hv : (chartPoint p).Valid) :
    (value : ℝ)≤∑ m∈retained xs,residualAt xs (chartPoint p) m := by
  by_cases initial : budgetCheck b xs budget=true
  · have e : budgetGain xs budget=value := by simpa [checkedBudget,initial] using ok
    rw [←e]
    exact budget_sound b xs budget initial inputs evaluation p hp hd hv
  · cases repair : shrinkBudget b xs budget with
    | none => simp [checkedBudget,initial,repair] at ok
    | some candidate =>
      by_cases accepted : budgetCheck b xs candidate=true
      · have e : budgetGain xs candidate=value := by simpa [checkedBudget,initial,repair,accepted] using ok
        rw [←e]
        exact budget_sound b xs candidate accepted inputs evaluation p hp hd hv
      · simp [checkedBudget,initial,repair,accepted] at ok

def phaseValue (b : Cell) (r : Proposal) (budget : Array Allocation) : Option ℚ := do
  let xs ← prepare b r.selected
  let gain ← checkedBudget b xs budget
  pure (baseline b xs+gain)

def phaseCheck (b : Cell) (r : Proposal) (budget : Array Allocation) : Bool :=
  (sameCell b r.ownerBox && decide ((r.selected.map AnchorRow.mode).Nodup)) &&
  ((diagonalsCheck b && cubeRootCheck scaleWitness scaleInput) &&
    match phaseValue b r budget with | some x => decide (fccHUpper<x) | none => false)

theorem phaseCheck_sound (b : Cell) (r : Proposal) (budget : Array Allocation) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) (ok : phaseCheck b r budget=true) : energy fcc<energy (chartPoint p) := by
  obtain ⟨data,comparison⟩ := Bool.and_eq_true_iff.mp ((Bool.and_eq_true_iff.mp ok).2)
  obtain ⟨hd,scale⟩ := Bool.and_eq_true_iff.mp data
  cases eval : prepare b r.selected with
  | none => simp [phaseValue,eval] at comparison
  | some xs =>
    cases cap : checkedBudget b xs budget with
    | none => simp [phaseValue,eval,cap] at comparison
    | some bound =>
      have strict : fccHUpper<baseline b xs+bound := by
        exact of_decide_eq_true (by simpa [phaseValue,eval,cap] using comparison)
      have base := preparedLower b r.selected xs eval p hp hd hv
      have gain := checkedBudget_sound b xs budget bound cap r.selected eval p hp hd hv
      apply aboveFCC_of_lower _ scale _ strict
      push_cast
      linarith only [base,gain]

end BccSharp.Coulomb.CompactCover.Stage2
