import BccSharp.Lattice.BccFrame

set_option autoImplicit false

/-! Endpoint E2 proof for the addressed BCC strain rows. The strict
comparison uses the actual chart, the full positive series, and the capped
defect. Failure to obtain a positive endpoint margin rejects the row. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

def quadBall (M : MetricBalls) (u : Fin 3 → Ball) : Ball :=
  Constants.sumBalls Finset.univ fun i =>
    Constants.sumBalls Finset.univ fun j => ((M i j).mul (u i)).mul (u j)

theorem quadBall_sound (M : MetricBalls) (u : Fin 3 → Ball) (C : Mat) (x : Vec)
    (hC : M.Contains C) (hx : ∀ i, (u i).Contains (x i)) :
    (quadBall M u).Contains (quad C x) := by
  rw [← hessianQuadratic_eq_quad]
  exact Constants.sumBalls_sound _ _ _ (fun i _ => Constants.sumBalls_sound _ _ _ (fun j _ =>
    Ball.contains_mul (Ball.contains_mul (hC i j) (hx i)) (hx j)))

def bccFrameDirectQ (n : IntVec) : Fin 3 → ℚ :=
  ![(n 0 : ℚ)+(n 2 : ℚ)/2,(n 1 : ℚ)+(n 2 : ℚ)/2,(n 2 : ℚ)/2]

def bccFrameDualQ (n : IntVec) : Fin 3 → ℚ :=
  ![(n 0 : ℚ),(n 1 : ℚ),2*(n 2 : ℚ)-(n 0 : ℚ)-(n 1 : ℚ)]

def directVectorBall (root : RootProposal) (n : IntVec) (i : Fin 3) : Ball :=
  root.ball.mul (Ball.exact (bccFrameDirectQ n i))

def reciprocalVectorBall (root : RootProposal) (n : IntVec) (i : Fin 3) : Ball :=
  root.ball.inv.mul (Ball.exact (bccFrameDualQ n i))

theorem directVectorBall_sound (root : RootProposal) (ok : cubeRootCheck root (Ball.exact 2) = true)
    (n : IntVec) (i : Fin 3) :
    (directVectorBall root n i).Contains (linearImage (cubicBasis .bcc) n i) := by
  have hr : root.ball.Contains Constants.fccLength :=
    cubeRoot_sound root (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) ok
  rw [bccCubic_short]
  have e : (bccFrameDirectQ n i : ℝ) = bccFrameDirect n i := by
    fin_cases i <;> norm_num [bccFrameDirectQ,bccFrameDirect] <;> push_cast <;> ring
  simpa [directVectorBall,e,Pi.smul_apply,smul_eq_mul] using
    (Ball.contains_mul hr (Ball.contains_exact (bccFrameDirectQ n i)))

theorem reciprocalVectorBall_sound (root : RootProposal) (ok : cubeRootCheck root (Ball.exact 2) = true)
    (n : IntVec) (i : Fin 3) :
    (reciprocalVectorBall root n i).Contains (cycleFrequency (cubicBasis .bcc) n i) := by
  have hr : root.ball.Contains Constants.fccLength :=
    cubeRoot_sound root (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) ok
  have hi := Ball.contains_inv (cubeRoot_invertible root (Ball.exact 2) ok) hr
  rw [bccCubic_dual]
  have e : (bccFrameDualQ n i : ℝ) = bccFrameDual n i := by
    fin_cases i <;> norm_num [bccFrameDualQ,bccFrameDual] <;> push_cast <;> ring
  simpa [reciprocalVectorBall,e,Pi.smul_apply,smul_eq_mul] using
    (Ball.contains_mul hi (Ball.contains_exact (bccFrameDualQ n i)))

def strainDirectBall (b : Rectangle) (w : StrainMetricWitness) (root : RootProposal)
    (n : IntVec) : Ball :=
  quadBall (metricBall .bcc b w) (directVectorBall root n)

def strainDualBall (b : Rectangle) (w : StrainMetricWitness) (root : RootProposal)
    (n : IntVec) : Ball :=
  quadBall (inverseMetricBall .bcc b w) (reciprocalVectorBall root n)

def evaluateKernelPair (qDirect qDual : Ball) (t : SeriesTerm) : Option ℚ := do
  if t.index = 0 then none else
    let a ← halfLower qDirect t.direct
    let d ← oneLower qDual t.dual
    pure (a+d)

theorem evaluateKernelPair_sound (R : Mat) (hR : R.det ≠ 0) (qDirect qDual : Ball)
    (t : SeriesTerm) (v : ℚ)
    (hd : qDirect.Contains (sq (linearImage R t.index)))
    (hr : qDual.Contains (sq (cycleFrequency R t.index)))
    (ok : evaluateKernelPair qDirect qDual t = some v) :
    (v : ℝ) ≤ shortKernel R t.index+dualKernel R t.index := by
  unfold evaluateKernelPair at ok
  split_ifs at ok with hn
  cases e : halfLower qDirect t.direct with
  | none => simp [e] at ok
  | some a =>
    cases f : oneLower qDual t.dual with
    | none => simp [e,f] at ok
    | some d =>
      have hv : v=a+d := by simpa [e,f,eq_comm] using ok
      have hi : linearImage R t.index ≠ 0 := by
        intro hz
        apply hn
        apply (periodIndices R hR).injective
        apply Subtype.ext
        change linearImage R t.index=linearImage R 0
        rw [linearImage, linearImage, castVec_zero, Matrix.mulVec_zero]
        exact hz
      have hf : cycleFrequency R t.index ≠ 0 := fun z =>
        hn (cycleFrequency_injective R hR (z.trans (cycleFrequency_zero R).symm))
      have positive (x : Vec) (hx : x ≠ 0) : 0<sq x :=
        lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hx))
      rw [hv,Rat.cast_add,shortKernel_eq _ hR _ hn,dualKernel_eq _ hR _ hn]
      exact add_le_add (halfLower_sound hd (positive _ hi) _ _ e)
        (oneLower_sound hr (positive _ hf) _ _ f)

def evaluateStrainTerm (b : Rectangle) (w : StrainMetricWitness) (root : RootProposal)
    (t : SeriesTerm) : Option ℚ :=
  evaluateKernelPair (strainDirectBall b w root t.index) (strainDualBall b w root t.index) t

theorem evaluateStrainTerm_sound (b : Rectangle) (w : StrainMetricWitness) (root : RootProposal)
    (rootOK : cubeRootCheck root (Ball.exact 2) = true) (A C : Mat) (hC : gram A = C)
    (hM : (metricBall .bcc b w).Contains C) (hI : (inverseMetricBall .bcc b w).Contains C⁻¹)
    (hR : (A*cubicBasis .bcc).det ≠ 0) (t : SeriesTerm) (v : ℚ)
    (ok : evaluateStrainTerm b w root t = some v) :
    (v : ℝ) ≤ shortKernel (A*cubicBasis .bcc) t.index+dualKernel (A*cubicBasis .bcc) t.index := by
  refine evaluateKernelPair_sound _ hR _ _ t v ?_ ?_ ok
  · rw [(bcc_strain_norms A C hC t.index).1]
    exact quadBall_sound _ _ _ _ hM (directVectorBall_sound root rootOK t.index)
  · rw [(bcc_strain_norms A C hC t.index).2]
    exact quadBall_sound _ _ _ _ hI (reciprocalVectorBall_sound root rootOK t.index)

structure StrainE2Witness where
  metric : StrainMetricWitness
  bccRoot : RootProposal
  upperPad : ℚ
  terms : List SeriesTerm

private theorem strainFiniteLower (b : Rectangle) (w : StrainE2Witness) (A C : Mat)
    (hA : A.det=1) (hC : gram A=C) (rootOK : cubeRootCheck w.bccRoot (Ball.exact 2)=true)
    (hM : (metricBall .bcc b w.metric).Contains C) (hI : (inverseMetricBall .bcc b w.metric).Contains C⁻¹)
    (nd : (w.terms.map SeriesTerm.index).Nodup) (v : ℚ)
    (ev : evaluateTermList (evaluateStrainTerm b w.metric w.bccRoot) w.terms=some v) :
    (v : ℝ) ≤ positiveSeries (A*cubicBasis .bcc) := by
  let R := A*cubicBasis .bcc
  have hR : R.det≠0 := by unfold R; rw [Matrix.det_mul,hA,bccCubic_det,one_mul]; exact one_ne_zero
  have hb := evaluateTermList_sound (evaluateStrainTerm b w.metric w.bccRoot)
    (fun n => shortKernel R n+dualKernel R n)
    (evaluateStrainTerm_sound b w.metric w.bccRoot rootOK A C hC hM hI hR) w.terms nd v ev
  exact hb.trans (positiveSeries_finite_lower R hR _)

def strainE2Check (b : Rectangle) (w : StrainE2Witness) : Bool :=
  let B := metricBall .bcc b w.metric
  ((strainMetricCheck .bcc b w.metric && cubeRootCheck w.bccRoot (Ball.exact 2)) &&
    (spectralCheck B w.upperPad && decide ((w.terms.map SeriesTerm.index).Nodup))) &&
    match evaluateTermList (evaluateStrainTerm b w.metric w.bccRoot) w.terms with
    | some v => decide (HbccUpper+gapFactorUpper*defectUpper B<v)
    | none => false

def BccStrainSharp (p : Point) : Prop :=
  ∀ A : Mat, A.det=1 → gram A=reconstructedMetric .bcc p →
    Sharp (Constants.fccLength⁻¹ • (A*cubicBasis .bcc))

/-- E2's spectral guard also proves the existence of an oriented frame. -/
def StrainE2Result (p : Point) : Prop :=
  (∃ A : Mat, A.det=1 ∧ gram A=reconstructedMetric .bcc p) ∧ BccStrainSharp p

theorem strainE2Check_sound (b : Rectangle) (w : StrainE2Witness)
    (ok : strainE2Check b w = true) (p : Point) (hp : b.Mem p) : StrainE2Result p := by
  classical
  let B := metricBall .bcc b w.metric
  let C := reconstructedMetric .bcc p
  have h := Bool.and_eq_true_iff.mp ok
  have h0 := Bool.and_eq_true_iff.mp h.1
  have hs := Bool.and_eq_true_iff.mp h0.1
  have hg := Bool.and_eq_true_iff.mp h0.2
  obtain ⟨hM,hI,hD⟩ := strainMetric_evaluate .bcc b w.metric hs.1 p hp
  have nd : (w.terms.map SeriesTerm.index).Nodup := of_decide_eq_true hg.2
  obtain ⟨v,ev,hv⟩ : ∃ v, evaluateTermList (evaluateStrainTerm b w.metric w.bccRoot) w.terms=some v ∧
      HbccUpper+gapFactorUpper*defectUpper B<v := by
    cases e : evaluateTermList (evaluateStrainTerm b w.metric w.bccRoot) w.terms with
    | none => simp [e] at h
    | some v =>
      refine ⟨v,by first | exact e | rfl,?_⟩
      exact of_decide_eq_true (by simpa [e,B] using h.2)
  refine ⟨bcc_strain_basis p hD (spectralCheck_sound B C hM w.upperPad hg.1).1,?_⟩
  intro A hA ag
  let R := A*cubicBasis .bcc
  have hR : R.det=1 := by unfold R; rw [Matrix.det_mul,hA,bccCubic_det,one_mul]
  have hb := strainFiniteLower b w A C hA ag hs.2 hM hI nd v ev
  have hDef := defectUpper_sound _ A (by rw [hA]; norm_num) (bcc_strain_points A) B
    (by rw [ag]; exact hM) w.upperPad hg.1
  exact strict_e2_from_series R hR v (defectUpper B) hb hDef hv

def automaticStrainMetricFor (ref : Reference) (b : Rectangle) : StrainMetricWitness :=
  let s₂ := Constants.rootPair 2 2 2 2
  let s₆ := Constants.rootPair 2 6 6 3
  let d := detBall (shiftedTensorBall ref b ⟨s₂,s₆,⟨0,0⟩⟩)
  ⟨s₂,s₆,Constants.rootPair 3 d.lo d.hi (1+max |d.lo| |d.hi|)⟩

def automaticStrainMetric (b : Rectangle) : StrainMetricWitness := automaticStrainMetricFor .bcc b

def automaticUpperPad (B : MetricBalls) : ℚ :=
  let M := upperDifference B
  let slack (i : Fin 3) := (M i i).lo-∑ j : Fin 3, offDiagUpper M i j
  min (slack 0) (min (slack 1) (slack 2))/2

def automaticStrainE2 (b : Rectangle) (radius : ℕ) : StrainE2Witness :=
  let w := automaticStrainMetric b
  let root := Constants.rootPair 3 2 2 2
  ⟨w,root,automaticUpperPad (metricBall .bcc b w),
    (cubeIndices radius).map (fun n => automaticKernelTerm n
      (strainDirectBall b w root n) (strainDualBall b w root n))⟩

def strainE2RadiusCheck (b : Rectangle) (radius : ℕ) : Bool :=
  decide (0< radius ∧ radius≤6) && strainE2Check b (automaticStrainE2 b radius)

theorem strainE2RadiusCheck_sound (b : Rectangle) (radius : ℕ)
    (ok : strainE2RadiusCheck b radius = true) (p : Point) (hp : b.Mem p) : StrainE2Result p :=
  strainE2Check_sound b _ (Bool.and_eq_true_iff.mp ok).2 p hp

def bccStrainE1Check (b : Rectangle) (w : StrainE2Witness) : Bool :=
  ((strainMetricCheck .bcc b w.metric && cubeRootCheck w.bccRoot (Ball.exact 2)) &&
    decide ((w.terms.map SeriesTerm.index).Nodup)) &&
    match evaluateTermList (evaluateStrainTerm b w.metric w.bccRoot) w.terms with
    | some v => decide (HfccUpper<v)
    | none => false

theorem bccStrainE1Check_sound (b : Rectangle) (w : StrainE2Witness)
    (ok : bccStrainE1Check b w = true) (p : Point) (hp : b.Mem p) : BccStrainSharp p := by
  classical
  have h := Bool.and_eq_true_iff.mp ok
  have h0 := Bool.and_eq_true_iff.mp h.1
  have hs := Bool.and_eq_true_iff.mp h0.1
  obtain ⟨hM,hI,_⟩ := strainMetric_evaluate .bcc b w.metric hs.1 p hp
  have nd : (w.terms.map SeriesTerm.index).Nodup := of_decide_eq_true h0.2
  obtain ⟨v,ev,hv⟩ : ∃ v, evaluateTermList (evaluateStrainTerm b w.metric w.bccRoot) w.terms=some v ∧
      HfccUpper<v := by
    cases e : evaluateTermList (evaluateStrainTerm b w.metric w.bccRoot) w.terms with
    | none => simp [e] at h
    | some v =>
      refine ⟨v,by first | exact e | rfl,?_⟩
      exact of_decide_eq_true (by simpa [e] using h.2)
  intro A hA ag
  have hR : (A*cubicBasis .bcc).det=1 := by rw [Matrix.det_mul,hA,bccCubic_det,one_mul]
  exact normalized_above_fcc_of_series _ hR
    ((by exact_mod_cast hv : (HfccUpper : ℝ)<v).trans_le
      (strainFiniteLower b w A (reconstructedMetric .bcc p) hA ag hs.2 hM hI nd v ev))

def bccStrainE1RadiusCheck (b : Rectangle) (radius : ℕ) : Bool :=
  decide (0< radius ∧ radius≤6) && bccStrainE1Check b (automaticStrainE2 b radius)

theorem bccStrainE1RadiusCheck_sound (b : Rectangle) (radius : ℕ)
    (ok : bccStrainE1RadiusCheck b radius = true) (p : Point) (hp : b.Mem p) : BccStrainSharp p :=
  bccStrainE1Check_sound b _ (Bool.and_eq_true_iff.mp ok).2 p hp

end BccSharp.Coulomb.BravaisCover
