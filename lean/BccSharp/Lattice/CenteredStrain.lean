import BccSharp.Lattice.StrainFirstJet

set_option autoImplicit false

/-! Centered E1/E2 check for the BCC strain rows. Both evaluations
use one support chosen from the parent box, and E2 subtracts the defect
penalty before taking absolute bounds of the signed derivatives. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

inductive StrainObjective where
  | aboveFCC
  | strictDefect

def StrainObjective.threshold : StrainObjective → ℚ
  | .aboveFCC => HfccUpper
  | .strictDefect => HbccUpper

def StrainObjective.penalty : StrainObjective → ℚ
  | .aboveFCC => 0
  | .strictDefect => gapFactorUpper*kappaUpper

structure StrainSupport where
  direct : List IntVec
  reciprocal : List IntVec

def bccArgument (kind : KernelKind) (p : Point) (n : IntVec) : ℝ :=
  let C := reconstructedMetric .bcc p
  Real.pi * match kind with
    | .half => quad C (linearImage (cubicBasis .bcc) n)
    | .one => quad C⁻¹ (cycleFrequency (cubicBasis .bcc) n)

def bccArgumentJet (kind : KernelKind) (J : StrainFirstJets) (root : RootProposal) (n : IntVec) : FirstJet :=
  let q := match kind with
    | .half => strainQuadJet J.metric (directVectorBall root n)
    | .one => strainQuadJet J.reciprocal (reciprocalVectorBall root n)
  ((FirstJet.constant Constants.piInput).mul q).round

theorem bccArgumentJet_sound (kind : KernelKind) (b : Rectangle)
    (w : StrainMetricWitness) (root : RootProposal)
    (hw : strainMetricCheck .bcc b w=true) (hr : cubeRootCheck root (Ball.exact 2)=true)
    (n : IntVec) : (bccArgumentJet kind (strainFirstJets .bcc b w) root n).Agrees b
      (fun p => bccArgument kind p n) := by
  have h := strainFirstJets_sound .bcc b w hw
  have hπ := FirstJet.constant_sound b Constants.piInput Real.pi Constants.piInput_sound
  cases kind with
  | half =>
    exact FirstJet.round_sound (FirstJet.mul_sound hπ
      (strainQuadJet_sound h.1 _ _ (directVectorBall_sound root hr n)))
  | one =>
    exact FirstJet.round_sound (FirstJet.mul_sound hπ
      (strainQuadJet_sound h.2 _ _ (reciprocalVectorBall_sound root hr n)))

private def kernelLimit : KernelKind → ℚ
  | .half => 64
  | .one => 128

private def argumentUsable (kind : KernelKind) (q : FirstJet) : Bool :=
  q.value.positive && decide (q.value.hi ≤ kernelLimit kind)

def centeredSupport (b : Rectangle) (radius : ℕ) : StrainSupport :=
  let w := automaticStrainMetric b
  let J := strainFirstJets .bcc b w
  let root := Constants.rootPair 3 2 2 2
  let indices := cubeIndices radius
  let retain (kind : KernelKind) := indices.filter (fun n =>
    decide (n≠0) && argumentUsable kind (bccArgumentJet kind J root n))
  ⟨retain .half,retain .one⟩

private theorem centeredSupport_nonzero (b : Rectangle) (radius : ℕ) :
    (∀ n ∈ (centeredSupport b radius).direct, n≠0) ∧
    (∀ n ∈ (centeredSupport b radius).reciprocal, n≠0) := by
  constructor
  · intro n h
    exact of_decide_eq_true
      (Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2).1
  · intro n h
    exact of_decide_eq_true
      (Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2).1

private def automaticKernelWitness (kind : KernelKind) (t : Ball) : KernelWitness :=
  let e := Constants.expProposal t.neg
  match kind with
  | .half => .half (automaticErfc t.lo) (automaticErfc t.hi) e
  | .one => .one e

private theorem automaticKernelWitness_kind (kind : KernelKind) (t : Ball) :
    (automaticKernelWitness kind t).kind=kind := by cases kind <;> rfl

private def checkedKernelJet (kind : KernelKind) (q : FirstJet) : Option FirstJet :=
  if argumentUsable kind q then
    let w := automaticKernelWitness kind q.value
    if w.check q.value then some (q.kernel w).round else none
  else none

private theorem checkedKernelJet_sound (kind : KernelKind) (b : Rectangle) (q out : FirstJet)
    (f : Point → ℝ) (hq : q.Agrees b f) (ok : checkedKernelJet kind q=some out) :
    out.Agrees b (fun p => kernelValue kind (f p)) := by
  unfold checkedKernelJet at ok
  by_cases range : argumentUsable kind q = true
  · rw [if_pos range] at ok
    dsimp only at ok
    by_cases checked : (automaticKernelWitness kind q.value).check q.value = true
    · rw [if_pos checked] at ok
      have h := FirstJet.round_sound (FirstJet.kernel_sound hq _ checked)
      rw [automaticKernelWitness_kind] at h
      rw [← Option.some.inj ok]
      exact h
    · rw [if_neg checked] at ok
      cases ok
  · rw [if_neg range] at ok
    cases ok

private def sumCheckedJets (eval : IntVec → Option FirstJet) : List IntVec → Option FirstJet
  | [] => some (FirstJet.constant (Ball.exact 0))
  | n::rest => do
    let a ← eval n
    let R ← sumCheckedJets eval rest
    pure (a.add R)

private theorem sumCheckedJets_sound (b : Rectangle) (f : IntVec → Point → ℝ)
    (eval : IntVec → Option FirstJet) (hs : ∀ n j, eval n=some j → j.Agrees b (f n))
    (indices : List IntVec) (hn : indices.Nodup) (j : FirstJet)
    (ok : sumCheckedJets eval indices=some j) :
    j.Agrees b (fun p => ∑ n ∈ indices.toFinset, f n p) := by
  classical
  induction indices generalizing j with
  | nil =>
    have e : FirstJet.constant (Ball.exact 0)=j := Option.some.inj ok
    rw [← e]
    simpa using FirstJet.constant_sound b (Ball.exact 0) 0 (FirstJet.contains_exact_of_eq Rat.cast_zero)
  | cons n rest ih =>
    have hnd := List.nodup_cons.mp hn
    cases h₁ : eval n with
    | none => simp [sumCheckedJets,h₁] at ok
    | some a =>
      cases h₂ : sumCheckedJets eval rest with
      | none => simp [sumCheckedJets,h₁,h₂] at ok
      | some d =>
        have e : a.add d=j := by simpa [sumCheckedJets,h₁,h₂] using ok
        have hm : n∉rest.toFinset := by simpa using hnd.1
        rw [← e]
        simpa [List.toFinset_cons,Finset.sum_insert hm] using
          FirstJet.add_sound (hs n a h₁) (ih hnd.2 d h₂)

def bccFiniteSeries (S : StrainSupport) (p : Point) : ℝ :=
  (∑ n ∈ S.direct.toFinset, kernelValue .half (bccArgument .half p n)) +
    (∑ n ∈ S.reciprocal.toFinset, kernelValue .one (bccArgument .one p n))

def bccSignedObjective (mode : StrainObjective) (S : StrainSupport) (p : Point) : ℝ :=
  bccFiniteSeries S p-(mode.penalty : ℝ)*frobSq (reconstructedMetric .bcc p-1)-
    (mode.threshold : ℝ)

private def signedJet (mode : StrainObjective) (b : Rectangle) (w : StrainMetricWitness)
    (root : RootProposal) (S : StrainSupport) : Option FirstJet := do
  if ((strainMetricCheck .bcc b w && cubeRootCheck root (Ball.exact 2)) &&
       decide (S.direct.Nodup ∧ S.reciprocal.Nodup)) then
    let J := strainFirstJets .bcc b w
    let d ← sumCheckedJets (fun n => checkedKernelJet .half (bccArgumentJet .half J root n)) S.direct
    let r ← sumCheckedJets (fun n => checkedKernelJet .one (bccArgumentJet .one J root n)) S.reciprocal
    let Q := (FirstJet.constant (Ball.exact mode.penalty)).mul (strainFrobJet J.metric)
    pure (((d.add r).sub Q).sub (FirstJet.constant (Ball.exact mode.threshold)))
  else none

private theorem signedJet_sound (mode : StrainObjective) (b : Rectangle) (w : StrainMetricWitness)
    (root : RootProposal) (S : StrainSupport) (j : FirstJet)
    (ok : signedJet mode b w root S=some j) : j.Agrees b (bccSignedObjective mode S) := by
  let J := strainFirstJets .bcc b w
  let eval (kind : KernelKind) (n : IntVec) := checkedKernelJet kind (bccArgumentJet kind J root n)
  unfold signedJet at ok
  split_ifs at ok with passes
  have h := Bool.and_eq_true_iff.mp passes
  have hw := Bool.and_eq_true_iff.mp h.1
  have hn : S.direct.Nodup ∧ S.reciprocal.Nodup := of_decide_eq_true h.2
  have term (kind : KernelKind) (n : IntVec) (x : FirstJet) (e : eval kind n=some x) :
      x.Agrees b (fun p => kernelValue kind (bccArgument kind p n)) :=
    checkedKernelJet_sound kind b _ x _ (bccArgumentJet_sound kind b w root hw.1 hw.2 n) e
  cases hd : sumCheckedJets (eval .half) S.direct with
  | none => simp [J,eval,hd] at ok
  | some d =>
    cases hr : sumCheckedJets (eval .one) S.reciprocal with
    | none => simp [J,eval,hd,hr] at ok
    | some r =>
      let Q := (FirstJet.constant (Ball.exact mode.penalty)).mul (strainFrobJet J.metric)
      have e : ((d.add r).sub Q).sub (FirstJet.constant (Ball.exact mode.threshold))=j := by
        simpa [J,eval,Q,hd,hr] using ok
      have hD := sumCheckedJets_sound b _ _ (term .half) S.direct hn.1 d hd
      have hR := sumCheckedJets_sound b _ _ (term .one) S.reciprocal hn.2 r hr
      have hQ := FirstJet.mul_sound (FirstJet.constant_sound b _ _ (Ball.contains_exact mode.penalty))
        (strainFrobJet_sound (strainFirstJets_sound .bcc b w hw.1).1)
      have hT := FirstJet.constant_sound b _ _ (Ball.contains_exact mode.threshold)
      rw [← e]
      exact FirstJet.sub_sound (FirstJet.sub_sound (FirstJet.add_sound hD hR) hQ) hT

private def centerRectangle (b : Rectangle) : Rectangle :=
  ⟨fun i => (coordinateBall b i).mid,fun i => (coordinateBall b i).mid⟩

private theorem centerRectangle_mem (b : Rectangle) : (centerRectangle b).Mem (boxCenter b) := by
  intro i
  exact ⟨le_rfl,le_rfl⟩

private def centeredLower (mode : StrainObjective) (b : Rectangle) (S : StrainSupport) :
    Option ℚ := do
  let c := centerRectangle b
  let root := Constants.rootPair 3 2 2 2
  let whole ← signedJet mode b (automaticStrainMetric b) root S
  let atCenter ← signedJet mode c (automaticStrainMetric c) root S
  pure (meanValueLower b atCenter.value whole.gradient)

private theorem centeredLower_sound (mode : StrainObjective) (b : Rectangle) (S : StrainSupport)
    (m : ℚ) (ok : centeredLower mode b S=some m) (p : Point) (hp : b.Mem p) :
    (m : ℝ) ≤ bccSignedObjective mode S p := by
  let c := centerRectangle b
  let root := Constants.rootPair 3 2 2 2
  cases hw : signedJet mode b (automaticStrainMetric b) root S with
  | none => simp [centeredLower,root,hw] at ok
  | some whole =>
    cases hc : signedJet mode c (automaticStrainMetric c) root S with
    | none => simp [centeredLower,c,root,hw,hc] at ok
    | some atCenter =>
      have e : meanValueLower b atCenter.value whole.gradient=m := by
        simpa [centeredLower,c,root,hw,hc] using ok
      rw [← e]
      exact FirstJet.centeredLower_sound (signedJet_sound mode b _ root S whole hw) atCenter.value
        ((signedJet_sound mode c _ root S atCenter hc).1 _ (centerRectangle_mem b)) p hp

private theorem bccFiniteSeries_lower (p : Point) (S : StrainSupport)
    (hd : ∀ n ∈ S.direct, n≠0) (hr : ∀ n ∈ S.reciprocal, n≠0)
    (A : Mat) (hA : A.det=1) (hC : gram A=reconstructedMetric .bcc p) :
    bccFiniteSeries S p ≤ positiveSeries (A*cubicBasis .bcc) := by
  classical
  let R := A*cubicBasis .bcc
  have hR : R.det≠0 := by unfold R; rw [Matrix.det_mul,hA,bccCubic_det,one_mul]; exact one_ne_zero
  have e₁ : (∑ n ∈ S.direct.toFinset, kernelValue .half (bccArgument .half p n)) =
      ∑ n ∈ S.direct.toFinset, shortKernel R n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [shortKernel_eq _ hR _ (hd n (by simpa using hn))]
    simp only [kernelValue,KernelKind.power,bccArgument,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,R]
    rw [(bcc_strain_norms A _ hC n).1]
  have e₂ : (∑ n ∈ S.reciprocal.toFinset, kernelValue .one (bccArgument .one p n)) =
      ∑ n ∈ S.reciprocal.toFinset, dualKernel R n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [dualKernel_eq _ hR _ (hr n (by simpa using hn))]
    simp only [kernelValue,KernelKind.power,bccArgument,Rat.cast_one,R]
    rw [(bcc_strain_norms A _ hC n).2]
  unfold bccFiniteSeries positiveSeries
  rw [e₁,e₂]
  exact add_le_add
    ((shortKernel_summable R hR).sum_le_tsum _ (fun n _ => shortKernel_nonnegative R n))
    ((dualKernel_summable R hR).sum_le_tsum _ (fun n _ => dualKernel_nonnegative R n))

private def modeGuard (mode : StrainObjective) (b : Rectangle) : Bool :=
  match mode with
  | .aboveFCC => true
  | .strictDefect =>
    let B := metricBall .bcc b (automaticStrainMetric b)
    spectralCheck B (automaticUpperPad B)

def centeredBccStrainCheck (mode : StrainObjective) (b : Rectangle) (radius : ℕ) : Bool :=
  (decide (0< radius ∧ radius≤6) && modeGuard mode b) &&
    match centeredLower mode b (centeredSupport b radius) with
    | none => false
    | some v => decide (0<v)

theorem centeredBccStrainCheck_sound (mode : StrainObjective) (b : Rectangle) (radius : ℕ)
    (ok : centeredBccStrainCheck mode b radius=true) (p : Point) (hp : b.Mem p) :
    BccStrainSharp p := by
  let S := centeredSupport b radius
  let w := automaticStrainMetric b
  let root := Constants.rootPair 3 2 2 2
  have h := Bool.and_eq_true_iff.mp ok
  have hg := (Bool.and_eq_true_iff.mp h.1).2
  obtain ⟨v,ev,hv⟩ : ∃ v, centeredLower mode b S=some v ∧ 0<v := by
    cases e : centeredLower mode b S with
    | none => simp [S,e] at h
    | some v =>
      refine ⟨v,by first | exact e | rfl,?_⟩
      exact of_decide_eq_true (by simpa [S,e] using h.2)
  have ht := centeredLower_sound mode b S v ev p hp
  have positive := (by exact_mod_cast hv : (0 : ℝ)<v).trans_le ht
  have hS := centeredSupport_nonzero b radius
  intro A det gramEq
  let R := A*cubicBasis .bcc
  have rh : R.det=1 := by unfold R; rw [Matrix.det_mul,det,bccCubic_det,one_mul]
  have series := bccFiniteSeries_lower p S hS.1 hS.2 A det gramEq
  cases mode with
  | aboveFCC =>
    apply normalized_above_fcc_of_series R rh
    unfold bccSignedObjective StrainObjective.penalty StrainObjective.threshold at positive
    push_cast at positive
    linarith
  | strictDefect =>
    have wm : strainMetricCheck .bcc b w=true := by
      have present : ∃ j, signedJet .strictDefect b w root S=some j := by
        cases e : signedJet .strictDefect b w root S with
        | none => simp [centeredLower,w,root,e] at ev
        | some j => exact ⟨j,rfl⟩
      obtain ⟨j,hj⟩ := present
      unfold signedJet at hj
      split_ifs at hj with checks
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checks).1).1
    let B := metricBall .bcc b w
    have sp : spectralCheck B (automaticUpperPad B)=true := hg
    have hm : B.Contains (gram A) := by
      rw [gramEq]
      exact (strainMetric_evaluate .bcc b w wm p hp).1
    have defBound := defectPointwiseUpper_sound _ A (by rw [det]; norm_num)
      (bcc_strain_points A) B hm _ sp
    rw [gramEq] at defBound
    apply strict_e2_from_same_point R rh _ defBound
    unfold bccSignedObjective StrainObjective.penalty StrainObjective.threshold at positive
    push_cast at positive
    linarith

end BccSharp.Coulomb.BravaisCover
