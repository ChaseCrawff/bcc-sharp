import BccSharp.Lattice.Routing

set_option autoImplicit false

/-! Exact local-ball objective, spectral guard and radial strictness.
The infinite sum is centered at the actual physical reference value.
The remaining analytic input is differentiation of this sum and its
checked signed, tail-inclusive Hessian. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open Constants.HighPrecision

def strainFullSeries (ref : Reference) (w : Point) : ℝ :=
  let C := reconstructedMetric ref w
  (∑' n : IntVec, if n=0 then 0 else
    gKernel (1/2) (Real.pi*quad C (linearImage (cubicBasis ref) n))) +
  (∑' n : IntVec, if n=0 then 0 else
    gKernel 1 (Real.pi*quad C⁻¹ (cycleFrequency (cubicBasis ref) n)))

private theorem deformed_unitVolume (ref : Reference) (A : Mat) (hA : |A.det|=1) :
    volumeOf (A*cubicBasis ref)=1 := by
  unfold volumeOf
  rw [Matrix.det_mul,abs_mul,hA,one_mul]
  exact cubicBasis_unitVolume ref

theorem strainFullSeries_eq_of_absDet (ref : Reference) (w : Point) (A : Mat) (hA : |A.det|=1)
    (hGram : gram A=reconstructedMetric ref w) :
    strainFullSeries ref w=positiveSeries (A*cubicBasis ref) := by
  let R := A*cubicBasis ref
  have hV := deformed_unitVolume ref A hA
  have hn : R.det≠0 := by
    intro e
    change |R.det|=1 at hV
    simp [e] at hV
  unfold strainFullSeries positiveSeries
  dsimp only
  congr 1
  · apply tsum_congr
    intro n
    by_cases e : n=0
    · simp [e,shortKernel]
    · rw [if_neg e,shortKernel_eq _ hn n e,(strain_norms ref A _ hGram n).1]
  · apply tsum_congr
    intro n
    by_cases e : n=0
    · simp [e,dualKernel,reciprocalGreenTerm]
    · rw [if_neg e,dualKernel_eq _ hn n e,(strain_norms ref A _ hGram n).2]

theorem strainFullSeries_eq (ref : Reference) (w : Point) (A : Mat) (hA : A.det=1)
    (hGram : gram A=reconstructedMetric ref w) :
    strainFullSeries ref w=positiveSeries (A*cubicBasis ref) :=
  strainFullSeries_eq_of_absDet ref w A (by simp [hA]) hGram

theorem strainFullSeries_energy_of_absDet (ref : Reference) (w : Point) (A : Mat) (hA : |A.det|=1)
    (hGram : gram A=reconstructedMetric ref w) :
    strainFullSeries ref w-3=(2*bravaisScale)*oneSiteEnergy (strainBasis ref A) := by
  rw [strainFullSeries_eq_of_absDet ref w A hA hGram]
  have h := oneSiteEnergy_from_unitVolume (A*cubicBasis ref) (deformed_unitVolume ref A hA)
  change oneSiteEnergy (strainBasis ref A)=(positiveSeries (A*cubicBasis ref)-3)/(2*bravaisScale) at h
  have e := (eq_div_iff (mul_pos two_pos bravaisScale_positive : (0 : ℝ)<2*bravaisScale).ne').mp h
  rw [← e]
  ring

private theorem strainFullSeries_energy (ref : Reference) (w : Point) (A : Mat) (hA : A.det=1)
    (hGram : gram A=reconstructedMetric ref w) :
    strainFullSeries ref w-3=(2*bravaisScale)*oneSiteEnergy (strainBasis ref A) :=
  strainFullSeries_energy_of_absDet ref w A (by simp [hA]) hGram

def localPenalty : Reference → ℚ
  | .bcc => gapFactorUpper*kappaUpper
  | .fcc => 0

def localSignedObjective (ref : Reference) (w : Point) : ℝ :=
  strainFullSeries ref w - strainFullSeries ref 0 -
    (localPenalty ref : ℝ)*frobSq (reconstructedMetric ref w-1)

theorem localSignedObjective_zero (ref : Reference) : localSignedObjective ref 0=0 := by
  simp [localSignedObjective,reconstructedMetric_zero,frobSq]

def localBccSpectralCheck : Bool :=
  let w := automaticStrainMetric ballRoot
  let B := metricBall .bcc ballRoot w
  strainMetricCheck .bcc ballRoot w && spectralCheck B (automaticUpperPad B)

theorem localSignedObjective_lower (ref : Reference) (w : Point) (hFold : folded w)
    (hBall : inProductBall beta beta w) (A : Mat) (hA : A.det=1)
    (hGram : gram A=reconstructedMetric ref w)
    (spectral : ref=.bcc → localBccSpectralCheck=true) :
    localSignedObjective ref w≤(2*bravaisScale)*oneSiteDeficit (strainBasis ref A) := by
  have E := strainFullSeries_energy ref w A hA hGram
  have C := strainFullSeries_energy ref 0 1 (by simp)
    (by simp [gram,reconstructedMetric_zero])
  rw [strain_reference_energy] at C
  have gapPos := Constants.reference_gap_checked.2
  have Dnon : 0≤oneSiteDefect (strainBasis ref A) := (cappedDefect_range _).1
  have g : 0≤(2*bravaisScale)*gap :=
    mul_nonneg (mul_pos two_pos bravaisScale_positive).le gapPos.le
  cases ref with
  | bcc =>
    simp only [idealEnergy] at C
    let wm := automaticStrainMetric ballRoot
    let B := metricBall .bcc ballRoot wm
    have spec := Bool.and_eq_true_iff.mp (spectral rfl)
    have hM := (strainMetric_evaluate .bcc ballRoot wm spec.1 w (ballRoot_contains w hFold hBall)).1
    have hG : B.Contains (gram A) := by rw [hGram]; exact hM
    have D := defectPointwiseUpper_sound _ A (by rw [hA]; norm_num)
      (bcc_strain_points A) B hG (automaticUpperPad B) spec.2
    rw [hGram] at D
    change oneSiteDefect (strainBasis .bcc A)≤_ at D
    have gp : 0≤(gapFactorUpper : ℝ) := g.trans gapFactorUpper_sound
    have h := mul_le_mul gapFactorUpper_sound D Dnon gp
    unfold localSignedObjective localPenalty oneSiteDeficit
    push_cast
    linarith
  | fcc =>
    simp only [idealEnergy] at C
    have D : oneSiteDefect (strainBasis .fcc A)≤1 := (cappedDefect_range _).2
    have h := mul_le_mul_of_nonneg_left D g
    unfold localSignedObjective localPenalty oneSiteDeficit gap at *
    push_cast
    linarith

/-- The exact ray stays in the same closed folded ball. Its first
derivative is zero at the anchor and its second derivative is the actual
Hessian applied to the fixed displacement twice. -/
theorem local_strict_of_signed_ray (ref : Reference) (w : Point) (hFold : folded w)
    (hBall : inProductBall beta beta w) (nonzero : w≠0) (A : Mat) (hA : A.det=1)
    (hGram : gram A=reconstructedMetric ref w) (spectral : ref=.bcc → localBccSpectralCheck=true)
    (M : Point → RealHessian) (d : ℝ → ℝ) (d0 : d 0=0)
    (continuous : ContinuousOn (fun t : ℝ => localSignedObjective ref (t • w)) (Set.Icc 0 1))
    (continuousD : ContinuousOn d (Set.Icc 0 1))
    (first : ∀ t∈Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ => localSignedObjective ref (s • w)) (d t) t)
    (second : ∀ t∈Set.Ioo (0 : ℝ) 1, HasDerivAt d (hessianQuadratic (M (t • w)) w) t)
    (curvature : ∀ z, folded z → inProductBall beta beta z →
      ∀ v : Point, v≠0 → 0<hessianQuadratic (M z) v) :
    0<oneSiteDeficit (strainBasis ref A) := by
  have ray := centered_ray_strict (fun t : ℝ => localSignedObjective ref (t • w)) d d0
    continuous continuousD first (fun t ht => by
      have live := folded_productBall_ray w hFold beta beta hBall t (Set.Ioo_subset_Icc_self ht)
      exact ⟨_,curvature (t • w) live.1 live.2 w nonzero,second t ht⟩)
  have strict : 0<localSignedObjective ref w := by
    simpa [localSignedObjective_zero] using ray
  have h := strict.trans_le (localSignedObjective_lower ref w hFold hBall A hA hGram spectral)
  by_contra! bad
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
    (mul_pos two_pos bravaisScale_positive : (0 : ℝ)<2*bravaisScale).le bad)) h

end BccSharp.Coulomb.BravaisCover
