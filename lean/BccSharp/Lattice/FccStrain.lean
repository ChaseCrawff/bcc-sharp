import BccSharp.Lattice.StrainOrigin

set_option autoImplicit false

/-! FCC strain E1 endpoint arithmetic for the conventional
frame. Coulomb normalization uses the absolute covolume of that frame. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

private def fccDirectQ (n : IntVec) : Fin 3 → ℚ :=
  ![(n 0 : ℚ)+(n 1 : ℚ),(n 0 : ℚ)+(n 2 : ℚ),(n 1 : ℚ)+(n 2 : ℚ)]

private def fccDualQ (n : IntVec) : Fin 3 → ℚ :=
  ![((n 0 : ℚ)+(n 1 : ℚ)-(n 2 : ℚ))/2,((n 0 : ℚ)-(n 1 : ℚ)+(n 2 : ℚ))/2,
    (-(n 0 : ℚ)+(n 1 : ℚ)+(n 2 : ℚ))/2]

private def fccDirectVectorBall (root : RootProposal) (n : IntVec) (i : Fin 3) : Ball :=
  root.ball.inv.mul (Ball.exact (fccDirectQ n i))

private def fccDualVectorBall (root : RootProposal) (n : IntVec) (i : Fin 3) : Ball :=
  root.ball.mul (Ball.exact (fccDualQ n i))

private theorem fccDirectVectorBall_sound (r : RootProposal) (ok : cubeRootCheck r (Ball.exact 2)=true)
    (n : IntVec) (i : Fin 3) :
    (fccDirectVectorBall r n i).Contains (linearImage (cubicBasis .fcc) n i) := by
  have h : r.ball.Contains Constants.fccLength :=
    cubeRoot_sound r (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) ok
  have hi := Ball.contains_inv (cubeRoot_invertible r _ ok) h
  have hi' := Ball.contains_mul hi (Ball.contains_exact (fccDirectQ n i))
  convert hi' using 1
  · rfl
  fin_cases i <;> norm_num [linearImage,cubicBasis,fccDirectQ,Matrix.mulVec,dotProduct,castVec,
    Fin.sum_univ_three,Matrix.smul_apply,smul_eq_mul] <;> push_cast <;> ring

/-- Entrywise form of `cubicInverse_eq` for FCC. Its statement hides the
rational matrix inside a lambda that `simp` cannot rewrite through. -/
private theorem fccInverse_apply (k i : Fin 3) :
    (cubicBasis .fcc)⁻¹ k i = Constants.fccLength * (cubicInverseQ .fcc k i : ℝ) := by
  rw [cubicInverse_eq]
  rfl

private theorem fccDualVectorBall_sound (r : RootProposal) (ok : cubeRootCheck r (Ball.exact 2)=true)
    (n : IntVec) (i : Fin 3) :
    (fccDualVectorBall r n i).Contains (cycleFrequency (cubicBasis .fcc) n i) := by
  have h : r.ball.Contains Constants.fccLength :=
    cubeRoot_sound r (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) ok
  have h' := Ball.contains_mul h (Ball.contains_exact (fccDualQ n i))
  convert h' using 1
  · rfl
  rw [cycleFrequency]
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three,Matrix.transpose_apply,fccInverse_apply]
  fin_cases i <;> norm_num [cubicInverseQ,fccDualQ,castVec] <;> ring

private def fccDirectQBall (b : Rectangle) (w : StrainMetricWitness) (r : RootProposal) (n : IntVec) :
    Ball := quadBall (metricBall .fcc b w) (fccDirectVectorBall r n)

private def fccDualQBall (b : Rectangle) (w : StrainMetricWitness) (r : RootProposal) (n : IntVec) :
    Ball := quadBall (inverseMetricBall .fcc b w) (fccDualVectorBall r n)

private def fccEval (b : Rectangle) (w : StrainMetricWitness) (r : RootProposal) (t : SeriesTerm) :
    Option ℚ := evaluateKernelPair (fccDirectQBall b w r t.index) (fccDualQBall b w r t.index) t

private theorem fccEval_sound (b : Rectangle) (w : StrainMetricWitness) (r : RootProposal)
    (hr : cubeRootCheck r (Ball.exact 2)=true) (A C : Mat) (hC : gram A=C)
    (hM : (metricBall .fcc b w).Contains C) (hI : (inverseMetricBall .fcc b w).Contains C⁻¹)
    (hR : (A*cubicBasis .fcc).det≠0) (t : SeriesTerm) (v : ℚ) (ev : fccEval b w r t=some v) :
    (v : ℝ)≤ shortKernel (A*cubicBasis .fcc) t.index+dualKernel (A*cubicBasis .fcc) t.index := by
  refine evaluateKernelPair_sound _ hR _ _ t v ?_ ?_ ev
  · rw [(strain_norms .fcc A C hC t.index).1]
    exact quadBall_sound _ _ _ _ hM (fccDirectVectorBall_sound r hr t.index)
  · rw [(strain_norms .fcc A C hC t.index).2]
    exact quadBall_sound _ _ _ _ hI (fccDualVectorBall_sound r hr t.index)

def FccStrainSharp (p : Point) : Prop :=
  ∀ A : Mat, A.det=1 → gram A=reconstructedMetric .fcc p → Sharp (strainBasis .fcc A)

private def automaticFccTerms (b : Rectangle) (w : StrainMetricWitness) (r : RootProposal) (radius : ℕ) :
    List SeriesTerm :=
  (cubeIndices radius).map (fun n => automaticKernelTerm n (fccDirectQBall b w r n) (fccDualQBall b w r n))

def fccStrainRadiusCheck (b : Rectangle) (radius : ℕ) : Bool :=
  let w := automaticStrainMetricFor .fcc b
  let r := Constants.rootPair 3 2 2 2
  let terms := automaticFccTerms b w r radius
  ((decide (0< radius ∧ radius≤6) && strainMetricCheck .fcc b w) &&
    (cubeRootCheck r (Ball.exact 2) && decide ((terms.map SeriesTerm.index).Nodup))) &&
  match evaluateTermList (fccEval b w r) terms with
  | none => false
  | some v => decide (HfccUpper<v)

theorem fccStrainRadiusCheck_sound (b : Rectangle) (radius : ℕ) (ok : fccStrainRadiusCheck b radius=true)
    (p : Point) (hp : b.Mem p) : FccStrainSharp p := by
  let w := automaticStrainMetricFor .fcc b
  let r := Constants.rootPair 3 2 2 2
  let terms := automaticFccTerms b w r radius
  have h := Bool.and_eq_true_iff.mp ok
  have h₀ := Bool.and_eq_true_iff.mp h.1
  have hW := (Bool.and_eq_true_iff.mp h₀.1).2
  have hR := Bool.and_eq_true_iff.mp h₀.2
  have nd : (terms.map SeriesTerm.index).Nodup := of_decide_eq_true hR.2
  obtain ⟨hM,hI,_⟩ := strainMetric_evaluate .fcc b w hW p hp
  obtain ⟨v,ev,strict⟩ : ∃ v, evaluateTermList (fccEval b w r) terms=some v ∧ HfccUpper<v := by
    cases e : evaluateTermList (fccEval b w r) terms with
    | none => simp [w,r,terms,e] at h
    | some v =>
      refine ⟨v,by first | exact e | rfl,?_⟩
      exact of_decide_eq_true (by simpa [w,r,terms,e] using h.2)
  intro A hA hC
  let R := A*cubicBasis .fcc
  have hVol : volumeOf R=1 := by
    unfold volumeOf R
    rw [Matrix.det_mul,hA,one_mul]
    exact cubicBasis_unitVolume .fcc
  have hn : R.det≠0 := by intro e; simp [volumeOf,e] at hVol
  have hsum := evaluateTermList_sound (fccEval b w r) (fun n => shortKernel R n+dualKernel R n)
    (fccEval_sound b w r hR.1 A _ hC hM hI hn) terms nd v ev
  apply unitVolume_above_fcc_of_series R hVol
  exact (by exact_mod_cast strict : (HfccUpper : ℝ)<v).trans_le
    (hsum.trans (positiveSeries_finite_lower R hn _))

end BccSharp.Coulomb.BravaisCover
