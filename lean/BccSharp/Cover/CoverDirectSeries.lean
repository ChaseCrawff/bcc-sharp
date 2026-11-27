import BccSharp.Cover.CoverDirectOperands
import BccSharp.Lattice.StrainMetric

set_option autoImplicit false

/-! direct leaf proof against the actual Series/physical energy.
The finite sum is over the two fixed cubes with a deterministic cutoff fallback.
Every omitted mode has a nonnegative contribution in the *combined* series. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.CompactCover.DirectRoute
open BccSharp BccSharp.Coverage BravaisCover
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

def pairedTerm (q : TwoSite) (n : IntVec) : ℝ := seriesReciprocalTerm q n+ seriesCosineTerm q n

theorem pairedTerm_eq (q : TwoSite) (n : IntVec) :
    pairedTerm q n=(1+Real.cos (2*Real.pi*dot (castVec n) q.offset))* seriesReciprocalTerm q n := by
  unfold pairedTerm seriesCosineTerm
  ring

private theorem realNonnegative (x : ℝ) : 0≤gKernel (1/2) x := by
  rw [gKernel_half]
  exact mul_nonneg (by norm_num) (MeasureTheory.integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem realPositive {B : Mat} (hB : B.det≠0) {v : Vec} (hv : v≠0) : 0<quad (gram B) v := by
  rw [←sq_mulVec_gram]
  apply lt_of_le_of_ne (sq_nonnegative _)
  intro e
  have h := (sq_eq_zero_iff _).mp e.symm
  have unit : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB)
  exact hv (Matrix.mulVec_injective_of_isUnit unit (h.trans (Matrix.mulVec_zero B).symm))

theorem reciprocalPositive {q : TwoSite} (hq : q.Valid) {n : IntVec} (hn : n≠0) :
    0<quad (gram q.basis)⁻¹ (castVec n) := by
  rw [dual_quad]
  have hz : cycleFrequency q.basis n≠0 := by
    intro e
    exact hn (cycleFrequency_injective _ (series_basis_nonsingular q hq) (e.trans (cycleFrequency_zero _).symm))
  exact lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hz))

private theorem reciprocalNonnegative (q : TwoSite) (hq : q.Valid) (n : IntVec) : 0≤ seriesReciprocalTerm q n := by
  by_cases hn : n=0
  · simp [seriesReciprocalTerm,hn]
  have positive := mul_pos Real.pi_pos (reciprocalPositive hq hn)
  rw [seriesReciprocalTerm,if_neg hn,gKernel_one positive]
  exact div_nonneg (Real.exp_pos _).le positive.le

private theorem pairedNonnegative (q : TwoSite) (hq : q.Valid) (n : IntVec) : 0≤pairedTerm q n := by
  rw [pairedTerm_eq]
  exact mul_nonneg (by linarith [Real.neg_one_le_cos (2*Real.pi*dot (castVec n) q.offset)])
    (reciprocalNonnegative q hq n)

theorem real_summable (q : TwoSite) (hq : q.Valid) :
    Summable (seriesDirectTerm q) ∧ Summable (seriesCrossTerm q) := by
  have hs : 0< seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  have hd := series_physical_basis_nonsingular q hq
  have direct := screened_lattice_summable seriesScreen hs (physicalBasis q) hd 0
  have dropZero : Summable (fun n : IntVec => if n=0 then 0 else screened seriesScreen (linearImage (physicalBasis q) n)) := by
    apply direct.summable_of_eq_zero_or_self
    intro n
    by_cases hn : n=0 <;> simp [hn]
  have cross := screened_lattice_summable seriesScreen hs (physicalBasis q) hd (physicalTwoPositions q 1)
  have directEq : seriesDirectTerm q = fun n => ac*(if n=0 then 0 else screened seriesScreen (linearImage (physicalBasis q) n)) :=
    funext (series_direct_mode q hq)
  have crossEq : seriesCrossTerm q = fun n => ac*screened seriesScreen (physicalTwoPositions q 1+linearImage (physicalBasis q) n) :=
    funext (series_cross_mode q hq)
  rw [directEq,crossEq]
  exact ⟨dropZero.mul_left ac,cross.mul_left ac⟩

theorem finite_lower (q : TwoSite) (hq : q.Valid) (period cross reciprocal : Finset IntVec) :
    (∑ n ∈ period,seriesDirectTerm q n)+(∑ n ∈ cross,seriesCrossTerm q n)+
      (∑ n ∈ reciprocal,pairedTerm q n) ≤ h₂ q := by
  have real := real_summable q hq
  have m := series_modes q hq
  rw [series_reciprocal_split q m.reciprocalSummable m.cosineSummable,
    ← m.reciprocalSummable.tsum_add m.cosineSummable]
  exact add_le_add (add_le_add
    (real.1.sum_le_tsum _ (fun n _ => by
      unfold seriesDirectTerm
      split_ifs <;> first | exact le_rfl | exact realNonnegative _))
    (real.2.sum_le_tsum _ (fun n _ => realNonnegative _)))
    ((m.reciprocalSummable.add m.cosineSummable).sum_le_tsum _ (fun n _ => pairedNonnegative q hq n))

def lexPositive (n : IntVec) : Prop := 0<n 0 ∨ (n 0=0 ∧ (0<n 1 ∨ (n 1=0 ∧ 0<n 2)))
instance (n : IntVec) : Decidable (lexPositive n) := by unfold lexPositive; infer_instance

theorem lex_ne {n : IntVec} (h : lexPositive n) : n≠0 := by
  intro eq
  subst n
  simp [lexPositive] at h

private theorem lex_not_neg {n : IntVec} (h : lexPositive n) : ¬lexPositive (-n) := by
  unfold lexPositive at *
  simp only [Pi.neg_apply,neg_pos,neg_eq_zero] at *
  intro backwards
  rcases h with a | ⟨a,b | ⟨b,c⟩⟩ <;>
    rcases backwards with x | ⟨x,y | ⟨y,z⟩⟩ <;> omega

private theorem even_quad (B : Mat) (v : Vec) : quad B (-v)=quad B v := by
  simp [quad,Matrix.mulVec_neg]

theorem even_direct (q : TwoSite) (n : IntVec) : seriesDirectTerm q (-n)= seriesDirectTerm q n := by
  simp [seriesDirectTerm,castVec_neg,even_quad]

theorem even_pair (q : TwoSite) (n : IntVec) : pairedTerm q (-n)=pairedTerm q n := by
  have phase : dot (-castVec n) q.offset = -dot (castVec n) q.offset := by
    simp [dot,Finset.sum_neg_distrib]
  simp [pairedTerm_eq,seriesReciprocalTerm,phase,castVec_neg,even_quad,mul_neg,Real.cos_neg]

def bothSigns (s : Finset IntVec) := s∪s.image (fun n => -n)

theorem sum_pairs (s : Finset IntVec) (hs : ∀ n ∈ s, lexPositive n)
    (f : IntVec → ℝ) (hf : ∀ n, f (-n)=f n) :
    (∑ n ∈ s,2*f n)=∑ n ∈ bothSigns s,f n := by
  have hdis : Disjoint s (s.image fun n => -n) := by
    apply Finset.disjoint_left.mpr
    intro n hin hneg
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hneg
    exact lex_not_neg (hs m hm) (hs _ hin)
  rw [bothSigns,Finset.sum_union hdis,Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
  simp_rw [hf,two_mul,Finset.sum_add_distrib]

def halfProposal (t : ℚ) : ErfcSeriesProposal :=
  let root := Constants.rootPair 2 t t (max 2 (t+1))
  let n := if t≤6 then 96 else 4*(⌈t⌉ : ℤ).toNat+128
  ⟨root,n,4*root.ball.hi* Constants.piInverseRoot.hi*t^n/(n.factorial : ℚ)⟩

private def expSquaring : Nat → Ball → List Ball
  | 0,_ => []
  | k+1,b =>
    let c := RoundedPolynomial.roundBall (b.mul b)
    c :: expSquaring k c

def expEndpoint (x : ℚ) : ExpBounds.Witness :=
  let s := RoundedPolynomial.expBound (x/1024) 64
  let p : ExpBounds.PointWitness := ⟨64,s,expSquaring 10 s⟩
  ⟨p,p,p.bound⟩

def directLower (z : Ball) : Option ℚ :=
  halfLower z (.check (halfProposal (Constants.piInput.mul z).hi))

def reciprocalLower (z : Ball) : Option ℚ :=
  oneLower z (.check (expEndpoint (-(Constants.piInput.mul z).hi)))

theorem cross_distance_positive {p : Chart} (hq : (chartPoint p).Valid) (n : IntVec) :
    0<quad (gram (chartBasis p)) (chartVector p true n) := by
  have nz : castVec n+(chartPoint p).offset≠0 := by
    intro hz
    apply hq.2 (-n)
    rw [castVec_neg]
    have h : (chartPoint p).offset = (castVec n+(chartPoint p).offset)-castVec n := by abel
    rw [h,hz,zero_sub]
  exact realPositive (series_basis_nonsingular (chartPoint p) hq) nz

theorem period_distance_positive {p : Chart} (hq : (chartPoint p).Valid) (n : IntVec) (hn : lexPositive n) :
    0<quad (gram (chartBasis p)) (chartVector p false n) := by
  have nz : castVec n≠0 := by
    intro h
    apply lex_ne hn
    funext i
    have c := congrFun h i
    change ((n i : ℤ) : ℝ)=0 at c
    exact_mod_cast c
  exact realPositive (series_basis_nonsingular (chartPoint p) hq) nz

private theorem cross_lower_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hq : (chartPoint p).Valid) (n : IntVec) (v : ℚ) (e : directLower (realDistance b true n)=some v) :
    (v : ℝ)≤ seriesCrossTerm (chartPoint p) n :=
  halfLower_sound (realDistance_sound hp hd true n) (cross_distance_positive hq n) _ _ e

private theorem period_lower_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hq : (chartPoint p).Valid) (n : IntVec) (hn : lexPositive n) (v : ℚ)
    (e : directLower (realDistance b false n)=some v) : (v : ℝ)≤ seriesDirectTerm (chartPoint p) n := by
  rw [seriesDirectTerm,if_neg (lex_ne hn)]
  exact halfLower_sound (realDistance_sound hp hd false n) (period_distance_positive hq n hn) _ _ e

private theorem oneLower_nonnegative {z : Ball} {w : OneLower} {l : ℚ} (ok : oneLower z w=some l) :
    0≤l := by
  cases w with
  | «omit» =>
    have hl : l=0 := (Option.some.inj ok).symm
    exact le_of_eq hl.symm
  | check w =>
    simp only [oneLower] at ok
    split_ifs at ok
    rw [← Option.some.inj ok]
    exact le_max_left _ _

def phaseModeLower (b : Cell) (n : IntVec) : Option ℚ := do
  let a ← phaseLower (phaseTurns b n)
  let c ← reciprocalLower (reciprocalDistance b n)
  pure (a*c)

private theorem phaseModeLower_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hq : (chartPoint p).Valid) (n : IntVec) (hn : lexPositive n) (v : ℚ)
    (e : phaseModeLower b n=some v) : (v : ℝ)≤pairedTerm (chartPoint p) n := by
  cases phase : phaseLower (phaseTurns b n) with
  | none => simp [phaseModeLower,phase] at e
  | some a =>
    cases recip : reciprocalLower (reciprocalDistance b n) with
    | none => simp [phaseModeLower,phase,recip] at e
    | some c =>
      have eq : v=a*c := by simpa [phaseModeLower,phase,recip,eq_comm] using e
      have hA := phaseLower_sound (phaseTurns_sound hp n) a phase
      have hC := oneLower_sound (reciprocalDistance_sound hp hd n) (reciprocalPositive hq (lex_ne hn)) _ _ recip
      rw [eq,Rat.cast_mul,pairedTerm_eq]
      apply mul_le_mul hA _ _ ((by exact_mod_cast phaseLower_nonnegative phase : (0:ℝ)≤a).trans hA)
      · rw [seriesReciprocalTerm,ite_eq_right (lex_ne hn)]
        exact hC
      · exact_mod_cast oneLower_nonnegative recip

def roundLower (x : ℚ) : ℚ := (⌊x* Constants.grid⌋ : ℤ)/ Constants.grid

theorem roundLower_le (x : ℚ) : roundLower x≤x := by
  unfold roundLower
  exact (div_le_iff₀ (by norm_num [Constants.grid])).2 (Int.floor_le _)

def sumLower (eval : IntVec → Option ℚ) : List IntVec → Option ℚ
  | [] => some 0
  | n::ns => do
    let a ← eval n
    let rest ← sumLower eval ns
    pure (roundLower a+rest)

theorem sumLower_sound (eval : IntVec → Option ℚ) (value : IntVec → ℝ)
    (indices : List IntVec) (nd : indices.Nodup)
    (pointwise : ∀ n ∈ indices, ∀ x, eval n=some x → (x : ℝ)≤value n)
    (x : ℚ) (ok : sumLower eval indices=some x) :
    (x : ℝ)≤∑ n ∈ indices.toFinset,value n := by
  induction indices generalizing x with
  | nil => have e : x=0 := (Option.some.inj ok).symm; simp [e]
  | cons a ns ih =>
    obtain ⟨fresh,restND⟩ := List.nodup_cons.mp nd
    cases ea : eval a with
    | none => simp [sumLower,ea] at ok
    | some u =>
      cases en : sumLower eval ns with
      | none => simp [sumLower,ea,en] at ok
      | some v =>
        have eq : x=roundLower u+v := by simpa [sumLower,ea,en,eq_comm] using ok
        rw [eq,Rat.cast_add,List.toFinset_cons,Finset.sum_insert (by simpa using fresh)]
        have roundLe : (roundLower u : ℝ)≤(u : ℝ) := by exact_mod_cast roundLower_le u
        exact add_le_add (roundLe.trans (pointwise a (by simp) u ea))
          (ih restND (fun n hn => pointwise n (List.mem_cons_of_mem _ hn)) v en)

def directIndices (radius : Nat) : List IntVec := 0 :: cubeIndices radius
def pairedIndices (radius : Nat) := (cubeIndices radius).filter (fun n => decide (lexPositive n))

def crossEval (b : Cell) (n : IntVec) : Option ℚ := directLower (realDistance b true n)
def periodEval (b : Cell) (n : IntVec) : Option ℚ := directLower (realDistance b false n)

def finiteValueWith (b : Cell) (radius : Nat) (cross period : IntVec → Option ℚ) : Option ℚ := do
  let c ← sumLower cross (directIndices radius)
  let s ← sumLower period (pairedIndices radius)
  let r ← sumLower (phaseModeLower b) (pairedIndices radius)
  pure (s*2+c+r*2)

theorem finiteValueWith_extra_sound (b : Cell) (radius : Nat) (cross period : IntVec → Option ℚ)
    (p : Chart) (hp : b.Mem p) (h : diagonalsCheck b=true)
    (hq : (chartPoint p).Valid) (nd : (directIndices radius).Nodup ∧ (pairedIndices radius).Nodup)
    (eCross ePeriod : IntVec → ℝ)
    (hc : ∀ n ∈ directIndices radius, ∀ v, cross n=some v → (v : ℝ)≤ seriesCrossTerm (chartPoint p) n+eCross n)
    (hs : ∀ n, lexPositive n → ∀ v, period n=some v → (v : ℝ)≤ seriesDirectTerm (chartPoint p) n+ePeriod n)
    (v : ℚ) (ok : finiteValueWith b radius cross period=some v) :
    (v : ℝ)≤h₂ (chartPoint p)+((∑ n ∈ (directIndices radius).toFinset,eCross n)+
      2*(∑ n ∈ (pairedIndices radius).toFinset,ePeriod n)) := by
  cases c : sumLower cross (directIndices radius) with
  | none => simp [finiteValueWith,c] at ok
  | some cv =>
    cases s : sumLower period (pairedIndices radius) with
    | none => simp [finiteValueWith,c,s] at ok
    | some sv =>
      cases r : sumLower (phaseModeLower b) (pairedIndices radius) with
      | none => simp [finiteValueWith,c,s,r] at ok
      | some rv =>
        let q := chartPoint p
        let half := (pairedIndices radius).toFinset
        have pos (n : IntVec) (hn : n∈pairedIndices radius) : lexPositive n :=
          of_decide_eq_true (List.mem_filter.mp hn).2
        have pos' (n : IntVec) (hn : n∈half) : lexPositive n := pos n (List.mem_toFinset.mp hn)
        have hC := sumLower_sound cross (fun n => seriesCrossTerm q n+eCross n) _ nd.1 hc cv c
        have hS := sumLower_sound period (fun n => seriesDirectTerm q n+ePeriod n) _ nd.2
          (fun n hn => hs n (pos n hn)) sv s
        have hR := sumLower_sound (phaseModeLower b) (pairedTerm q) _ nd.2
          (fun n hn => phaseModeLower_sound hp h hq n (pos n hn)) rv r
        rw [Finset.sum_add_distrib] at hS hC
        have pS : 2*(sv : ℝ)≤(∑ n ∈ bothSigns half,seriesDirectTerm q n)+2*(∑ n ∈ half,ePeriod n) := by
          rw [←sum_pairs half pos' _ (even_direct q),←Finset.mul_sum]
          linarith only [hS]
        have rS : 2*(rv : ℝ)≤∑ n ∈ bothSigns half,pairedTerm q n := by
          rw [←sum_pairs half pos' _ (even_pair q),←Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hR (by norm_num)
        have eq : v=sv*2+cv+rv*2 := by simpa [finiteValueWith,c,s,r,eq_comm] using ok
        have hFull := finite_lower q hq (bothSigns half) (directIndices radius).toFinset (bothSigns half)
        rw [eq]
        push_cast
        linarith only [hFull,pS,rS,hC]

theorem finiteValueWith_sound (b : Cell) (radius : Nat) (cross period : IntVec → Option ℚ)
    (p : Chart) (hp : b.Mem p) (h : diagonalsCheck b=true)
    (hq : (chartPoint p).Valid) (nd : (directIndices radius).Nodup ∧ (pairedIndices radius).Nodup)
    (hc : ∀ n ∈ directIndices radius, ∀ v, cross n=some v → (v : ℝ)≤ seriesCrossTerm (chartPoint p) n)
    (hs : ∀ n, lexPositive n → ∀ v, period n=some v → (v : ℝ)≤ seriesDirectTerm (chartPoint p) n)
    (v : ℚ) (ok : finiteValueWith b radius cross period=some v) : (v : ℝ)≤h₂ (chartPoint p) := by
  simpa using finiteValueWith_extra_sound b radius cross period p hp h hq nd (fun _ => 0) (fun _ => 0)
    (fun n hn a e => by simpa using hc n hn a e) (fun n hn a e => by simpa using hs n hn a e) v ok

def finiteValue (b : Cell) (radius : Nat) : Option ℚ :=
  finiteValueWith b radius (crossEval b) (periodEval b)

theorem finiteValue_sound (b : Cell) (radius : Nat) (p : Chart) (hp : b.Mem p) (h : diagonalsCheck b=true)
    (hq : (chartPoint p).Valid) (nd : (directIndices radius).Nodup ∧ (pairedIndices radius).Nodup)
    (v : ℚ) (ok : finiteValue b radius=some v) : (v : ℝ)≤h₂ (chartPoint p) :=
  finiteValueWith_sound b radius _ _ p hp h hq nd (fun n _ => cross_lower_sound hp h hq n)
    (fun n hn => period_lower_sound hp h hq n hn) v ok

def scaleInput : Ball := (Ball.exact (8/3)).mul Constants.piInput
def scaleWitness : RootProposal := Constants.rootPair 3 scaleInput.lo scaleInput.hi 3
def fccHUpper : ℚ := 4+2*scaleWitness.lower* Constants.fccBracket.hi

theorem fccHUpper_sound (validRoot : cubeRootCheck scaleWitness scaleInput=true) :
    4+2*ac*energy fcc≤(fccHUpper : ℝ) := by
  have enclosed : scaleInput.Contains (8*Real.pi/3) := by
    have hm := Ball.contains_mul (Ball.contains_exact (8/3 : ℚ)) Constants.piInput_sound
    have e : ((8/3 : ℚ) : ℝ)*Real.pi=8*Real.pi/3 := by push_cast; ring
    rw [e] at hm
    exact hm
  have h := cubeRoot_sound scaleWitness scaleInput (8*Real.pi/3) (by positivity) enclosed validRoot
  have acLo : (scaleWitness.lower : ℝ)≤ac := by
    have hlo := (endpoints h).1
    dsimp only [RootProposal.ball,Ball.lo] at hlo
    push_cast at hlo
    unfold ac
    linarith only [hlo]
  have fccHi : energy fcc≤(Constants.fccBracket.hi : ℝ) := (Constants.reference_bounds .fcc).2
  have negative : (Constants.fccBracket.hi : ℝ)≤0 := by norm_num [Constants.fccBracket]
  have e := mul_le_mul_of_nonneg_left fccHi (mul_nonneg (by norm_num) ac_positive.le : (0:ℝ)≤2*ac)
  have d := mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_left acLo (by norm_num : (0:ℝ)≤2)) negative
  unfold fccHUpper
  push_cast
  linarith only [e,d]

theorem aboveFCC_of_lower (q : TwoSite) (hs : cubeRootCheck scaleWitness scaleInput=true)
    (v : ℚ) (strict : fccHUpper<v) (bound : (v : ℝ)≤h₂ q) : energy fcc<energy q := by
  have strictR : (fccHUpper : ℝ)<v := by exact_mod_cast strict
  change energy fcc<(h₂ q-4)/(2*ac)
  apply (lt_div_iff₀ (mul_pos two_pos ac_positive : (0:ℝ)<2*ac)).2
  linarith only [fccHUpper_sound hs,strictR,bound]

def radiusCheck (b : Cell) (radius : Nat) : Bool :=
  decide ((directIndices radius).Nodup ∧ (pairedIndices radius).Nodup) &&
    match finiteValue b radius with
    | some v => decide (fccHUpper<v)
    | none => false

def check (b : Cell) : Bool :=
  (diagonalsCheck b && cubeRootCheck scaleWitness scaleInput) && (radiusCheck b 1 || radiusCheck b 2)

theorem radiusCheck_sound (b : Cell) (radius : Nat) (p : Chart) (hp : b.Mem p) (hq : (chartPoint p).Valid)
    (hd : diagonalsCheck b=true) (hs : cubeRootCheck scaleWitness scaleInput=true)
    (ok : radiusCheck b radius=true) : energy fcc<energy (chartPoint p) := by
  obtain ⟨nd,compared⟩ := Bool.and_eq_true_iff.mp ok
  cases ev : finiteValue b radius with
  | none => simp [ev] at compared
  | some v =>
    have bound := finiteValue_sound b radius p hp hd hq (of_decide_eq_true nd) v ev
    have strict : fccHUpper<v := of_decide_eq_true (by simpa [ev] using compared)
    exact aboveFCC_of_lower _ hs v strict bound

theorem check_sound (b : Cell) (ok : check b=true) (p : Chart) (hp : b.Mem p) (hq : (chartPoint p).Valid) :
    energy fcc<energy (chartPoint p) := by
  obtain ⟨constants,cutoff⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨geom,scale⟩ := Bool.and_eq_true_iff.mp constants
  rcases Bool.or_eq_true_iff.mp cutoff with one | two
  · exact radiusCheck_sound b 1 p hp hq geom scale one
  · exact radiusCheck_sound b 2 p hp hq geom scale two

theorem check_physical (b : Cell) (ok : check b=true) (p : Chart) (hp : b.Mem p) (hq : (chartPoint p).Valid) :
    greenPerParticle seriesScreen (physicalBasis fcc) (physicalTwoPositions fcc) <
      greenPerParticle seriesScreen (physicalBasis (chartPoint p)) (physicalTwoPositions (chartPoint p)) := by
  rw [green_two_eq_energy fcc (Constants.refTwo_valid .fcc),green_two_eq_energy _ hq]
  exact check_sound b ok p hp hq

end BccSharp.Coulomb.CompactCover.DirectRoute
