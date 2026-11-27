import BccSharp.Lattice.StrictLeaves

set_option autoImplicit false

/-! Escape estimate for the lattice. The only scalar numerical test is the outward
comparison of the exact half-kernel at 16π/25 against the Constants FCC bound. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open BccSharp.Intervals (Ball)

def escapeArgument : Ball := Ball.exact (16/25)
def escapeWitness : HalfLower :=
  .check (automaticErfc (Constants.piInput.mul escapeArgument).hi)

def escapeCheck : Bool :=
  match halfLower escapeArgument escapeWitness with
  | some t => decide (HfccUpper < 2*t)
  | none => false

theorem escape_checked : escapeCheck = true := by
  decide +kernel

theorem escape_scalar : (HfccUpper : ℝ) < 2*gKernel (1/2) (Real.pi*(16/25)) := by
  obtain ⟨t,ht,hc⟩ : ∃ t, halfLower escapeArgument escapeWitness = some t ∧ HfccUpper < 2*t := by
    cases e : halfLower escapeArgument escapeWitness with
    | none =>
      have h := escape_checked
      simp [escapeCheck,e] at h
    | some t =>
      refine ⟨t,by first | exact e | rfl,?_⟩
      exact of_decide_eq_true (by simpa [escapeCheck,e] using escape_checked)
  have h := halfLower_sound (q := escapeArgument) (x := (16/25 : ℝ))
    (by simpa [escapeArgument] using (Ball.contains_exact (16/25 : ℚ))) (by norm_num)
    escapeWitness t ht
  exact (by exact_mod_cast hc : (HfccUpper : ℝ)<2*(t : ℝ)).trans_le
    (mul_le_mul_of_nonneg_left h (by norm_num))

private theorem shortKernel_neg (R : Mat) (n : IntVec) : shortKernel R (-n)=shortKernel R n := by
  have h : linearImage R (-n) = -linearImage R n := by
    simp [linearImage,castVec_neg,Matrix.mulVec_neg]
  have hn : sq (linearImage R (-n))=sq (linearImage R n) := by
    rw [h]
    simp [sq,Pi.neg_apply]
  simp [shortKernel,screened,neg_eq_zero,hn]

theorem twoShort_above_fcc (R : Mat) (hR : R.det=1) (n : IntVec) (hn : n≠0)
    (short : (HfccUpper : ℝ) < 2*gKernel (1/2) (Real.pi*sq (linearImage R n))) :
    Sharp (Constants.fccLength⁻¹ • R) := by
  have hR' : R.det≠0 := by rw [hR]; exact one_ne_zero
  have hnn : n≠-n := by
    intro e
    apply hn
    funext i
    have h := congrFun e i
    change n i = -(n i) at h
    change n i = 0
    omega
  rw [← shortKernel_eq R hR' n hn] at short
  have hSum := positiveSeries_finite_lower R hR' {n,-n}
  rw [Finset.sum_pair hnn,shortKernel_neg] at hSum
  have ht : (HfccUpper : ℝ)<positiveSeries R := by
    linarith [dualKernel_nonnegative R n,dualKernel_nonnegative R (-n)]
  exact normalized_above_fcc_of_series R hR ht

theorem veryShortVector_above_fcc (R : Mat) (hR : R.det=1) (n : IntVec) (hn : n≠0)
    (short : sq (linearImage R n) ≤ (16/25 : ℝ)) :
    Sharp (Constants.fccLength⁻¹ • R) := by
  have hR' : R.det≠0 := by rw [hR]; exact one_ne_zero
  have hInj : Function.Injective R.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det R).mpr (isUnit_iff_ne_zero.mpr hR'))
  have hnx : linearImage R n ≠ 0 := by
    intro h
    have h' := hInj (h.trans (Matrix.mulVec_zero R).symm)
    apply hn
    funext i
    have e := congrFun h' i
    change (n i : ℝ) = 0 at e
    exact_mod_cast e
  have hp : 0 < sq (linearImage R n) := lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hnx))
  have hk := halfKernel_decreasing (mul_pos Real.pi_pos hp) (mul_le_mul_of_nonneg_left short Real.pi_pos.le)
  exact twoShort_above_fcc R hR n hn (escape_scalar.trans_le (mul_le_mul_of_nonneg_left hk (by norm_num)))

private theorem firstIndex_length (p : Point) :
    sq (linearImage (normalizedChart p) (![1,0,0] : IntVec)) = (p 0)^2 := by
  norm_num [sq,linearImage,normalizedChart,chartBasis,coordLift,castVec,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem chart_short_escape (p : Point) (h₀ : 0 < p 0) (h₁ : 0 < p 1)
    (short : p 0 ≤ (4/5 : ℝ)) : Sharp (primitiveChart p) := by
  let n : IntVec := ![1,0,0]
  have h : sq (linearImage (normalizedChart p) n) ≤ (16/25 : ℝ) := by
    show sq (linearImage (normalizedChart p) (![1,0,0] : IntVec)) ≤ (16/25 : ℝ)
    rw [firstIndex_length]
    nlinarith [pow_le_pow_left₀ h₀.le short 2]
  exact veryShortVector_above_fcc _ (normalizedChart_det p h₀.ne' h₁.ne') n (by decide) h

/-- Basis-independent escape on the density slice, before a KZ chart has
been chosen. The caller supplies the short vector in the given basis. -/
theorem oneSite_short_escape (B : Mat) (hB : B.det = 1/2) (n : IntVec) (hn : n ≠ 0)
    (short : Constants.fccLength^2*sq (linearImage B n) ≤ (16/25 : ℝ)) : Sharp B := by
  have ht : 0< Constants.fccLength := by unfold Constants.fccLength; positivity
  have cube : Constants.fccLength^3=2 := by
    rw [Constants.fccLength,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  let R := Constants.fccLength • B
  have hR : R.det=1 := by
    show (Constants.fccLength • B).det = 1
    rw [Matrix.det_smul,Fintype.card_fin,cube,hB]; norm_num
  have hz : sq (linearImage R n) ≤ (16/25 : ℝ) := by
    show sq (linearImage (Constants.fccLength • B) n) ≤ (16/25 : ℝ)
    rw [linearImage_scale,sq_smul]
    exact short
  have h := veryShortVector_above_fcc R hR n hn hz
  simpa [R,smul_smul,inv_mul_cancel₀ ht.ne'] using h

theorem chart_escape_or_root (p : Point) (hr : reduced p) (h₀ : 0<p 0) (h₁ : 0<p 1)
    (hx : p 2 ∈ Set.Icc (0 : ℝ) (1/2)) (hy : p 3 ∈ Set.Icc (0 : ℝ) (1/2))
    (hz : p 4 ∈ Set.Icc (-1/2 : ℝ) (1/2)) : Sharp (primitiveChart p) ∨ proofRoot p := by
  rcases le_total (p 0) (4/5 : ℝ) with h | h
  · exact Or.inl (chart_short_escape p h₀ h₁ h)
  · exact Or.inr (proofRoot_of_reduced_far p hr h h₁ hx hy hz)

def shortBoxArgument (b : Rectangle) : Ball := sqBall (coordinateBall b 0)

def shortBoxLower (b : Rectangle) : Option ℚ :=
  let q := shortBoxArgument b
  halfLower q (.check (automaticErfc (Constants.piInput.mul q).hi))

def shortBoxCheck (b : Rectangle) : Bool :=
  decide (0<b.lo 0 ∧ 0<b.lo 1) &&
    match shortBoxLower b with
    | none => false
    | some t => decide (HfccUpper<2*t)

theorem shortBoxCheck_sound (b : Rectangle) (ok : shortBoxCheck b = true) (p : Point)
    (hp : b.Mem p) : Sharp (primitiveChart p) := by
  have h := Bool.and_eq_true_iff.mp ok
  have signs : 0<b.lo 0 ∧ 0<b.lo 1 := of_decide_eq_true h.1
  have h₀ := (by exact_mod_cast signs.1 : (0 : ℝ)<b.lo 0).trans_le (hp 0).1
  have h₁ := (by exact_mod_cast signs.2 : (0 : ℝ)<b.lo 1).trans_le (hp 1).1
  obtain ⟨v,ev,strict⟩ : ∃ t, shortBoxLower b=some t ∧ HfccUpper<2*t := by
    cases e : shortBoxLower b with
    | none => simp [e] at h
    | some t =>
      refine ⟨t,by first | exact e | rfl,?_⟩
      exact of_decide_eq_true (by simpa [e] using h.2)
  have q : (shortBoxArgument b).Contains ((p 0)^2) := sqBall_sound (coordinateBall_sound hp 0)
  have hv := halfLower_sound q (pow_pos h₀ 2)
    (.check (automaticErfc (Constants.piInput.mul (shortBoxArgument b)).hi)) v ev
  apply twoShort_above_fcc (normalizedChart p) (normalizedChart_det p h₀.ne' h₁.ne')
    (![1,0,0] : IntVec) (by decide)
  rw [firstIndex_length]
  exact (by exact_mod_cast strict : (HfccUpper : ℝ)<2*(v : ℝ)).trans_le
    (mul_le_mul_of_nonneg_left hv (by norm_num))

end BccSharp.Coulomb.BravaisCover
