import BccSharp.Cover.Stage2Geometry

set_option autoImplicit false

/-! Stage2 tangent checker on a whole, addressed Direct box. Modes are
selected from the recorded radius-two candidate families. Only the
independently checked kernel tangents, phase floors, and joint corner
upper give credit. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Stage2
open BccSharp BccSharp.Coverage DirectRoute BravaisCover

structure AnchorRow where
  mode : Mode
  ticks : ℕ

def Mode.valid (m : Mode) : Prop :=
  (∀ i, (-2 : ℤ)≤ m.index i ∧ m.index i≤2) ∧ (m.family=.cross ∨ lexPositive m.index)

instance (m : Mode) : Decidable m.valid := by unfold Mode.valid; infer_instance

def Mode.kind (m : Mode) : KernelKind := if m.family=.reciprocal then .one else .half

def phaseFactor (q : TwoSite) (n : IntVec) : ℝ := 1+Real.cos (2*Real.pi*dot (castVec n) q.offset)

def Mode.term (m : Mode) (q : TwoSite) : ℝ :=
  match m.family with
  | .cross => seriesCrossTerm q m.index
  | .period => 2* seriesDirectTerm q m.index
  | .reciprocal => 2*pairedTerm q m.index

structure Line where
  mode : Mode
  intercept : ℚ
  penalty : ℚ
  floor : ℚ

def floorFor (b : Cell) (m : Mode) : Option ℚ :=
  if m.family=.reciprocal then do
    let k ← phaseLower (phaseTurns b m.index)
    pure (max 0 (lower96 k))
  else some 1

theorem floorFor_sound (b : Cell) (m : Mode) (y : ℚ) (ok : floorFor b m=some y)
    (p : Chart) (hp : b.Mem p) : 0≤y ∧
      (m.family=.reciprocal → (y : ℝ)≤phaseFactor (chartPoint p) m.index) ∧
      (m.family≠.reciprocal → y=1) := by
  by_cases dual : m.family=.reciprocal
  · cases current : phaseLower (phaseTurns b m.index) with
    | none => simp [floorFor,dual,current] at ok
    | some v =>
      have eq : y=max 0 (lower96 v) := by simpa [floorFor,dual,current,eq_comm] using ok
      have phase := phaseLower_sound (phaseTurns_sound hp m.index) v current
      have nn : 0≤phaseFactor (chartPoint p) m.index := by
        unfold phaseFactor
        linarith [Real.neg_one_le_cos (2*Real.pi*dot (castVec m.index) (chartPoint p).offset)]
      refine ⟨by rw [eq]; exact le_max_left _ _,fun _ => ?_,fun h => (h dual).elim⟩
      rw [eq]
      push_cast
      exact max_le nn ((Rat.cast_le.mpr (lower96_le v)).trans phase)
  · have eq : y=1 := by simpa [floorFor,dual,eq_comm] using ok
    exact ⟨by rw [eq]; exact zero_le_one,fun h => (dual h).elim,fun _ => eq⟩

def evalLine (b : Cell) (r : AnchorRow) : Option Line := do
  if !decide r.mode.valid then none else
    let bound ← tangent r.mode.kind r.ticks
    let floor ← floorFor b r.mode
    let multiplier := if r.mode.family=.cross then (1:ℚ) else 2*floor
    pure ⟨r.mode,multiplier*bound.intercept,multiplier*bound.penalty,floor⟩

/-- The extra reciprocal residual is kept explicit for the phase-budget
stage. The plain tangent route may discard it because it is nonnegative. -/
def Line.residual (r : Line) (q : TwoSite) : ℝ :=
  if r.mode.family=.reciprocal then
    2*(phaseFactor q r.mode.index-(r.floor : ℝ))* seriesReciprocalTerm q r.mode.index
  else 0

private theorem bulk_kernel_half (x : ℝ) : kernelValue .half x=gKernel (1/2) x := by
  norm_num [kernelValue,KernelKind.power]

private theorem bulk_kernel_one (x : ℝ) : kernelValue .one x=gKernel 1 x := by
  norm_num [kernelValue,KernelKind.power]

theorem evalLine_sound (b : Cell) (src : AnchorRow) (r : Line) (ok : evalLine b src=some r)
    (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b=true) (hv : (chartPoint p).Valid) :
    r.mode=src.mode ∧ r.mode.valid ∧ 0≤ r.penalty ∧ 0≤ r.residual (chartPoint p) ∧
    (r.intercept : ℝ)-(r.penalty : ℝ)*r.mode.radial (squarePoint p)≤
      r.mode.term (chartPoint p)-r.residual (chartPoint p) := by
  by_cases permitted : src.mode.valid
  · cases kt : tangent src.mode.kind src.ticks with
    | none => simp [evalLine,permitted,kt] at ok
    | some t =>
      cases ft : floorFor b src.mode with
      | none => simp [evalLine,permitted,kt,ft] at ok
      | some f =>
        let mult := if src.mode.family=.cross then (1:ℚ) else 2*f
        have eq : r=⟨src.mode,mult*t.intercept,mult*t.penalty,f⟩ := by
          simpa [evalLine,permitted,kt,ft,mult,eq_comm] using ok
        subst r
        obtain ⟨tp,ts⟩ := tangent_sound _ _ _ kt
        obtain ⟨fn,fb,fu⟩ := floorFor_sound b src.mode f ft p hp
        have mp : 0≤ mult := by dsimp [mult]; split <;> positivity
        refine ⟨rfl,permitted,mul_nonneg mp tp,?_⟩
        -- The goal with the line's projections reduced, so that the helper equalities rewrite.
        show 0 ≤ Line.residual ⟨src.mode,mult*t.intercept,mult*t.penalty,f⟩ (chartPoint p) ∧
          ((mult*t.intercept : ℚ) : ℝ)-((mult*t.penalty : ℚ) : ℝ)*src.mode.radial (squarePoint p)≤
            src.mode.term (chartPoint p)-Line.residual ⟨src.mode,mult*t.intercept,mult*t.penalty,f⟩ (chartPoint p)
        cases family : src.mode.family with
        | cross =>
          have distance := cross_distance_positive hv src.mode.index
          have bound := ts _ distance
          have kind : src.mode.kind=.half := by simp [Mode.kind,family]
          rw [kind,bulk_kernel_half] at bound
          have multOne : mult=1 := by simp [mult,family]
          have radial : src.mode.radial (squarePoint p)=
              quad (gram (chartBasis p)) (chartVector p true src.mode.index) := by
            simp only [Mode.radial,family]
            exact squaredRadial_eq p true _
          have term : src.mode.term (chartPoint p)=
              gKernel (1/2) (Real.pi*quad (gram (chartBasis p)) (chartVector p true src.mode.index)) := by
            simp only [Mode.term,family]
            rfl
          have residual : Line.residual ⟨src.mode,mult*t.intercept,mult*t.penalty,f⟩ (chartPoint p)=0 := by
            simp [Line.residual,family]
          refine ⟨le_of_eq residual.symm,?_⟩
          rw [residual,radial,term,multOne]
          push_cast
          linear_combination bound
        | period =>
          have lex : lexPositive src.mode.index := permitted.2.resolve_left (by simp [family])
          have distance := period_distance_positive hv src.mode.index lex
          have bound := ts _ distance
          have kind : src.mode.kind=.half := by simp [Mode.kind,family]
          rw [kind,bulk_kernel_half] at bound
          have one : f=1 := fu (by simp [family])
          have multTwo : mult=2 := by simp [mult,family,one]
          have radial : src.mode.radial (squarePoint p)=
              quad (gram (chartBasis p)) (chartVector p false src.mode.index) := by
            simp only [Mode.radial,family]
            exact squaredRadial_eq p false _
          have term : src.mode.term (chartPoint p)=
              2*gKernel (1/2) (Real.pi*quad (gram (chartBasis p)) (chartVector p false src.mode.index)) := by
            simp only [Mode.term,family]
            rw [seriesDirectTerm,ite_eq_right (lex_ne lex)]
            rfl
          have residual : Line.residual ⟨src.mode,mult*t.intercept,mult*t.penalty,f⟩ (chartPoint p)=0 := by
            simp [Line.residual,family]
          refine ⟨le_of_eq residual.symm,?_⟩
          rw [residual,radial,term,multTwo]
          push_cast
          linear_combination 2*bound
        | reciprocal =>
          have lex : lexPositive src.mode.index := permitted.2.resolve_left (by simp [family])
          have pos := reciprocalPositive hv (lex_ne lex)
          have bound := ts _ pos
          have kind : src.mode.kind=.one := by simp [Mode.kind,family]
          rw [kind,bulk_kernel_one] at bound
          have base : seriesReciprocalTerm (chartPoint p) src.mode.index=
              gKernel 1 (Real.pi*quad (gram (chartPoint p).basis)⁻¹ (castVec src.mode.index)) := by
            rw [seriesReciprocalTerm,ite_eq_right (lex_ne lex)]
          have nonnegative : 0 ≤ seriesReciprocalTerm (chartPoint p) src.mode.index := by
            rw [base,←bulk_kernel_one]
            exact value_nonnegative _ (mul_pos Real.pi_pos pos)
          have gap := sub_nonneg.mpr (fb family)
          have multFloor : mult=2*f := by simp [mult,family]
          have residual : Line.residual ⟨src.mode,mult*t.intercept,mult*t.penalty,f⟩ (chartPoint p)=
              2*(phaseFactor (chartPoint p) src.mode.index-(f : ℝ))*
                seriesReciprocalTerm (chartPoint p) src.mode.index := by
            simp [Line.residual,family]
          have term : src.mode.term (chartPoint p)=
              2*(phaseFactor (chartPoint p) src.mode.index* seriesReciprocalTerm (chartPoint p) src.mode.index) := by
            simp only [Mode.term,family]
            rw [pairedTerm_eq]
            rfl
          obtain ⟨h0,h1⟩ := radialLoPos b hd
          have d0 := h0.trans_le (hp 0).1
          have d1 := h1.trans_le (hp 1).1
          have radial : src.mode.radial (squarePoint p)=
              quad (gram (chartPoint p).basis)⁻¹ (castVec src.mode.index) := by
            simp only [Mode.radial,family]
            exact dualRadial_eq _ p d0.ne' d1.ne'
          have twice := mul_le_mul_of_nonneg_left bound (by positivity : (0:ℝ)≤2*(f : ℝ))
          refine ⟨?_,?_⟩
          · rw [residual]
            exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) gap) nonnegative
          · rw [residual,radial,term,multFloor,base]
            push_cast
            linear_combination twice
  · simp [evalLine,permitted] at ok

def prepare (b : Cell) : List AnchorRow → Option (List Line)
  | [] => some []
  | r::rs => do
    let line ← evalLine b r
    let rest ← prepare b rs
    pure (line::rest)

theorem prepare_sound (b : Cell) (src : List AnchorRow) (out : List Line) (h : prepare b src=some out)
    (r : Line) (hr : r∈out) : ∃ raw∈src,evalLine b raw=some r := by
  induction src generalizing out with
  | nil =>
    have e : ([] : List Line)=out := Option.some.inj h
    cases e
    simp at hr
  | cons a as ih =>
    cases hA : evalLine b a with
    | none => simp [prepare,hA] at h
    | some z =>
      cases hRest : prepare b as with
      | none => simp [prepare,hA,hRest] at h
      | some zs =>
        have e : z::zs=out := by simpa [prepare,hA,hRest] using h
        cases e
        rcases List.mem_cons.mp hr with rfl | later
        · exact ⟨a,by simp,hA⟩
        · obtain ⟨raw,hm,check⟩ := ih _ hRest later
          exact ⟨raw,List.mem_cons_of_mem _ hm,check⟩

def findLine : List Line → Mode → Option Line
  | [],_ => none
  | r::rs,m => if r.mode=m then some r else findLine rs m

theorem findLine_sound (xs : List Line) (m : Mode) (r : Line) (h : findLine xs m=some r) :
    r∈xs ∧ r.mode=m := by
  induction xs with
  | nil => simp [findLine] at h
  | cons a as ih =>
    by_cases matchMode : a.mode=m
    · have e : a=r := by simpa [findLine,matchMode] using h
      subst r
      exact ⟨by simp,matchMode⟩
    · have tail := ih (by simpa [findLine,matchMode] using h)
      exact ⟨List.mem_cons_of_mem _ tail.1,tail.2⟩

theorem existsLine (xs : List Line) (m : Mode) (hm : m∈xs.map Line.mode) : ∃ r,findLine xs m=some r := by
  induction xs with
  | nil => simp at hm
  | cons a as ih =>
    by_cases found : a.mode=m
    · exact ⟨a,by simp [findLine,found]⟩
    · have there : m∈as.map Line.mode := by
        rw [List.map_cons,List.mem_cons] at hm
        exact hm.resolve_left (fun h => found h.symm)
      obtain ⟨r,h⟩ := ih there
      exact ⟨r,by simpa [findLine,found] using h⟩

def collect (s : Finset Mode) (f : Family) : Finset IntVec :=
  (s.filter (fun m => m.family=f)).image Mode.index

private theorem family_sum (s : Finset Mode) (tag : Family) (f : IntVec → ℝ) :
    (∑ n ∈ collect s tag,f n)=∑ m ∈ s,if m.family=tag then f m.index else 0 := by
  unfold collect
  rw [Finset.sum_image,Finset.sum_filter]
  intro a ha b hb eq
  have aj := (Finset.mem_filter.mp ha).2
  have bj := (Finset.mem_filter.mp hb).2
  cases a; cases b; simp_all

theorem physical_sum_le (s : Finset Mode) (q : TwoSite) (hv : q.Valid)
    (ok : ∀ m∈s,m.valid) : (∑ m ∈ s,m.term q)≤h₂ q := by
  have positive (f : Family) (hf : f≠.cross) : ∀ n∈collect s f,lexPositive n := by
    intro n h
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hs,tag⟩ := Finset.mem_filter.mp hm
    exact (ok m hs).2.resolve_left (fun a => hf (tag.symm.trans a))
  have full := finite_lower q hv (bothSigns (collect s .period)) (collect s .cross) (bothSigns (collect s .reciprocal))
  rw [←sum_pairs _ (positive .period (by decide)) _ (even_direct q),
    ←sum_pairs _ (positive .reciprocal (by decide)) _ (even_pair q)] at full
  rw [family_sum,family_sum,family_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib] at full
  exact le_trans (le_of_eq (by
    apply Finset.sum_congr rfl
    intro m _
    cases tag : m.family <;> simp [Mode.term,tag])) full

def weight (xs : List Line) (m : Mode) : ℚ := (findLine xs m).elim 0 Line.penalty
def intercept (xs : List Line) (m : Mode) : ℚ := (findLine xs m).elim 0 Line.intercept
def residualAt (xs : List Line) (q : TwoSite) (m : Mode) : ℝ :=
  (findLine xs m).elim 0 (fun r => r.residual q)
def floorAt (xs : List Line) (m : Mode) : ℚ := (findLine xs m).elim 0 Line.floor
def retained (xs : List Line) : Finset Mode := (xs.map Line.mode).toFinset

def exactUpper (b : Cell) (g : Moments) : ℚ :=
  (Finset.univ : Finset (Fin 5 → Bool)).sup' Finset.univ_nonempty fun shape =>
    let p := shapePart b shape
    let row := primalMetric p
    let dualContribution := sixDot (dualMetric p) g.reciprocal
    (Finset.univ : Finset (Fin 3 → Bool)).sup' Finset.univ_nonempty fun f =>
      sixDot row (g.shift (offsetPart b f))+dualContribution

theorem exactUpper_sound (b : Cell) (g : Moments) (shape : Fin 5 → Bool) (f : Fin 3 → Bool) :
    packedCorner b g shape f≤exactUpper b g := by
  -- The inner maximum over the three offset bits, for a fixed shape corner.
  let inner (s : Fin 5 → Bool) : ℚ :=
    (Finset.univ : Finset (Fin 3 → Bool)).sup' Finset.univ_nonempty fun x =>
      sixDot (primalMetric (shapePart b s)) (g.shift (offsetPart b x))+
        sixDot (dualMetric (shapePart b s)) g.reciprocal
  have row : packedCorner b g shape f ≤ inner shape :=
    Finset.le_sup' (fun x => sixDot (primalMetric (shapePart b shape)) (g.shift (offsetPart b x))+
      sixDot (dualMetric (shapePart b shape)) g.reciprocal) (Finset.mem_univ f)
  have column : inner shape ≤ exactUpper b g := Finset.le_sup' inner (Finset.mem_univ shape)
  exact row.trans column

structure Proposal where
  ownerBox : Cell
  selected : List AnchorRow

def baseline (b : Cell) (xs : List Line) : ℚ :=
  let s := retained xs
  (∑ m ∈ s,intercept xs m)-exactUpper b (moments s (weight xs))

theorem preparedMode (b : Cell) (inputs : List AnchorRow) (xs : List Line)
    (evals : prepare b inputs=some xs) (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hv : (chartPoint p).Valid) (m : Mode) (hm : m∈retained xs) :
    m.valid ∧ 0≤weight xs m ∧ 0≤ residualAt xs (chartPoint p) m ∧
      (intercept xs m : ℝ) - (weight xs m : ℝ)*m.radial (squarePoint p)≤
        m.term (chartPoint p)-residualAt xs (chartPoint p) m := by
  obtain ⟨line,read⟩ := existsLine xs m (List.mem_toFinset.mp hm)
  obtain ⟨member,identity⟩ := findLine_sound xs m line read
  obtain ⟨raw,_,value⟩ := prepare_sound b inputs xs evals line member
  obtain ⟨_,validated,nn,residual,bound⟩ := evalLine_sound b raw line value p hp hd hv
  exact ⟨identity ▸ validated,by simpa [weight,read] using nn,
    by simpa [residualAt,read] using residual,by simpa [intercept,weight,residualAt,read,identity] using bound⟩

theorem preparedLower (b : Cell) (inputs : List AnchorRow) (xs : List Line)
    (evals : prepare b inputs=some xs) (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hv : (chartPoint p).Valid) :
    (baseline b xs : ℝ)+(∑ m ∈ retained xs,residualAt xs (chartPoint p) m)≤h₂ (chartPoint p) := by
  let s := retained xs
  let upper := exactUpper b (moments s (weight xs))
  have info := preparedMode b inputs xs evals p hp hd hv
  have cost := corner_upper b hd s (weight xs) (fun m hm => (info m hm).2.1) upper
    (fun bits => by rw [←packedCorner_eq]; exact exactUpper_sound b _ _ _) p hp
  have summed := Finset.sum_le_sum (fun m hm => (info m hm).2.2.2)
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib] at summed
  have full := physical_sum_le s (chartPoint p) hv (fun m hm => (info m hm).1)
  unfold baseline
  push_cast
  linarith only [cost,summed,full]

def bulkValue (b : Cell) (r : Proposal) : Option ℚ := do
  let xs ← prepare b r.selected
  pure (baseline b xs)

def bulkCheck (b : Cell) (r : Proposal) : Bool :=
  (sameCell b r.ownerBox && decide ((r.selected.map AnchorRow.mode).Nodup)) &&
  ((diagonalsCheck b && cubeRootCheck scaleWitness scaleInput) &&
    match bulkValue b r with
    | none => false
    | some u => decide (fccHUpper<u))

theorem bulkCheck_sound (b : Cell) (r : Proposal) (p : Chart) (hp : b.Mem p)
    (hv : (chartPoint p).Valid) (ok : bulkCheck b r=true) : energy fcc<energy (chartPoint p) := by
  have options := (Bool.and_eq_true_iff.mp ok).2
  obtain ⟨constants,compare⟩ := Bool.and_eq_true_iff.mp options
  obtain ⟨hd,scale⟩ := Bool.and_eq_true_iff.mp constants
  cases evals : prepare b r.selected with
  | none => simp [bulkValue,evals] at compare
  | some xs =>
    have strict : fccHUpper<baseline b xs := of_decide_eq_true (by simpa [bulkValue,evals] using compare)
    have bound := preparedLower b r.selected xs evals p hp hd hv
    have nn := Finset.sum_nonneg (fun m hm => (preparedMode b r.selected xs evals p hp hd hv m hm).2.2.1)
    exact aboveFCC_of_lower _ scale _ strict ((le_add_of_nonneg_right nn).trans bound)

theorem bulkCheck_physical (b : Cell) (r : Proposal) (p : Chart) (hp : b.Mem p)
    (hv : (chartPoint p).Valid) (ok : bulkCheck b r=true) :
    greenPerParticle seriesScreen (physicalBasis fcc) (physicalTwoPositions fcc)<
      greenPerParticle seriesScreen (physicalBasis (chartPoint p)) (physicalTwoPositions (chartPoint p)) := by
  rw [green_two_eq_energy fcc (Constants.refTwo_valid .fcc),green_two_eq_energy _ hv]
  exact bulkCheck_sound b r p hp hv ok

end BccSharp.Coulomb.CompactCover.Stage2
