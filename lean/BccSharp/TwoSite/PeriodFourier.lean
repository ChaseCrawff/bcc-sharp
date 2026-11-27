import BccSharp.TwoSite.EwaldCellRepetition
import BccSharp.Analysis.CoulombPeriodization
import BccSharp.Analysis.FourierUniqueness

set_option autoImplicit false

/-! Lattice Fourier lemmas in a general nonsingular basis. The
normalized frequency is expressed in cycles, so the reciprocal wave
used in the Ewald sum is (2π) times that frequency. -/

noncomputable section
open MeasureTheory Module
open scoped BigOperators Pointwise

namespace BccSharp.Coulomb
open BccSharp

def periodCell (B : Mat) (hB : B.det ≠ 0) : Set Vec :=
  ZSpan.fundamentalDomain (matrixBasis B hB)

theorem periodCell_fundamental (B : Mat) (hB : B.det ≠ 0) :
    IsAddFundamentalDomain (periodModule B) (periodCell B hB) volume := by
  rw [periodModule_eq_span B hB]
  exact ZSpan.isAddFundamentalDomain (matrixBasis B hB) volume

theorem periodCell_measurable (B : Mat) (hB : B.det ≠ 0) : MeasurableSet (periodCell B hB) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem periodCell_finite (B : Mat) (hB : B.det ≠ 0) :
    volume (periodCell B hB) < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top

theorem periodCell_volume (B : Mat) (hB : B.det ≠ 0) :
    volume.real (periodCell B hB) = volumeOf B := by
  unfold periodCell
  rw [ZSpan.volume_real_fundamentalDomain]
  have hmat : Matrix.of (matrixBasis B hB) = B.transpose := by
    ext i j
    exact matrixBasis_column B hB i j
  rw [hmat, Matrix.det_transpose]
  rfl

def cycleFrequency (B : Mat) (n : IntVec) : Vec := (B⁻¹).transpose.mulVec (castVec n)

def cellWave (B : Mat) (n : IntVec) (x : Vec) : ℂ :=
  CoulombLaplace.wave (cycleFrequency B n) x

theorem cycleFrequency_transpose (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    B.transpose.mulVec (cycleFrequency B n) = castVec n := by
  rw [cycleFrequency, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB), Matrix.transpose_one, Matrix.one_mulVec]

theorem cycleFrequency_injective (B : Mat) (hB : B.det ≠ 0) :
    Function.Injective (cycleFrequency B) := by
  intro n m h
  have he := congrArg B.transpose.mulVec h
  rw [cycleFrequency_transpose B hB, cycleFrequency_transpose B hB] at he
  funext i
  have hi := congrFun he i
  change (n i : ℝ) = (m i : ℝ) at hi
  exact_mod_cast hi

theorem cycleFrequency_zero (B : Mat) : cycleFrequency B 0 = 0 := by
  rw [cycleFrequency, castVec_zero, Matrix.mulVec_zero]

theorem cycleFrequency_dot (B : Mat) (hB : B.det ≠ 0) (n : IntVec) (x : Vec) :
    dot (cycleFrequency B n) (B.mulVec x) = dot (castVec n) x := by
  rw [dot_mulVec_eq, cycleFrequency_transpose B hB]

theorem cellWave_zero (B : Mat) (x : Vec) : cellWave B 0 x = 1 := by
  rw [cellWave, cycleFrequency_zero, CoulombPeriodization.wave_zero]

theorem cellWave_add (B : Mat) (n : IntVec) (x y : Vec) :
    cellWave B n (x+y) = cellWave B n x * cellWave B n y :=
  CoulombPeriodization.wave_add _ _ _

theorem cellWave_norm (B : Mat) (n : IntVec) (x : Vec) : ‖cellWave B n x‖ = 1 :=
  CoulombPeriodization.wave_norm _ _

theorem cellWave_period (B : Mat) (hB : B.det ≠ 0) (n : IntVec)
    (z : periodModule B) : cellWave B n z.val = 1 := by
  obtain ⟨m,hm⟩ := z.property
  change B.mulVec (castVec m) = z.val at hm
  unfold cellWave CoulombLaplace.wave
  change Complex.exp (-((2*Real.pi*dot (cycleFrequency B n) z.val : ℝ) : ℂ)*Complex.I) = 1
  rw [← hm, cycleFrequency_dot B hB, dot_integer]
  let k : ℤ := ∑ i, n i*m i
  rw [show -((2*Real.pi*(k : ℝ) : ℝ) : ℂ)*Complex.I =
    ((-k : ℤ) : ℂ)*(2*Real.pi*Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem cellWave_sub_frequency (B : Mat) (n m : IntVec) (x : Vec) :
    cellWave B (-m) x * cellWave B n x = cellWave B (n-m) x := by
  have hc : cycleFrequency B (n-m) = cycleFrequency B n + cycleFrequency B (-m) := by
    rw [sub_eq_add_neg, cycleFrequency, castVec_add, Matrix.mulVec_add] <;> rfl
  simp only [cellWave, CoulombLaplace.wave, hc, ← Complex.exp_add]
  congr 1
  simp only [Ewald.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_neg]
  ring

theorem cellWave_continuous (B : Mat) (n : IntVec) : Continuous (cellWave B n) := by
  unfold cellWave CoulombLaplace.wave Ewald.dot
  fun_prop

def cellPeriodize (B : Mat) (f : Vec → ℂ) (x : Vec) : ℂ :=
  ∑' z : periodModule B, f (z.val+x)

instance (B : Mat) : MeasurableVAdd (periodModule B) Vec :=
  (inferInstance : MeasurableVAdd (periodModule B).toAddSubgroup Vec)

instance (B : Mat) : VAddInvariantMeasure (periodModule B) Vec volume :=
  (inferInstance : VAddInvariantMeasure (periodModule B).toAddSubgroup Vec volume)

private theorem period_translate_integrable (B : Mat) (hB : B.det ≠ 0)
    {f : Vec → ℂ} (hf : Integrable f) (z : periodModule B) :
    IntegrableOn (fun x => f (z.val+x)) (periodCell B hB) :=
  ((measurePreserving_add_left volume z.val).integrable_comp_of_integrable hf).integrableOn

private theorem period_sum_lintegral (B : Mat) (hB : B.det ≠ 0) {f : Vec → ℂ} (hf : Integrable f) :
    (∑' z : periodModule B, ∫⁻ x in periodCell B hB, ‖f (z.val+x)‖ₑ) < ⊤ := by
  letI : Countable (periodModule B) := Countable.of_equiv _ (periodIndices B hB)
  have h := (periodCell_fundamental B hB).lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
  change (∫⁻ x, ‖f x‖ₑ) = (∑' z : periodModule B, ∫⁻ x in periodCell B hB, ‖f (z.val+x)‖ₑ) at h
  rw [← h]
  exact hf.hasFiniteIntegral

theorem cellPeriodize_integrable (B : Mat) (hB : B.det ≠ 0) {f : Vec → ℂ} (hf : Integrable f) :
    IntegrableOn (cellPeriodize B f) (periodCell B hB) := by
  letI : Countable (periodModule B) := Countable.of_equiv _ (periodIndices B hB)
  have hm (z : periodModule B) := (period_translate_integrable B hB hf z).aestronglyMeasurable
  refine ⟨AEStronglyMeasurable.tsum hm, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun z => (hm z).enorm)]
  exact period_sum_lintegral B hB hf

theorem cellPeriodize_integral (B : Mat) (hB : B.det ≠ 0) {f : Vec → ℂ} (hf : Integrable f) :
    (∫ x in periodCell B hB, cellPeriodize B f x) = ∫ x : Vec, f x := by
  letI : Countable (periodModule B) := Countable.of_equiv _ (periodIndices B hB)
  unfold cellPeriodize
  rw [integral_tsum (fun z => (period_translate_integrable B hB hf z).aestronglyMeasurable)
    (period_sum_lintegral B hB hf).ne]
  exact ((periodCell_fundamental B hB).integral_eq_tsum'' f hf).symm

theorem cellPeriodize_mul_wave (B : Mat) (hB : B.det ≠ 0) (f : Vec → ℂ) (n : IntVec) (x : Vec) :
    cellPeriodize B f x * cellWave B n x = cellPeriodize B (fun y => f y * cellWave B n y) x := by
  simp only [cellPeriodize, cellWave_add, cellWave_period B hB, one_mul, tsum_mul_right]

theorem cellPeriodize_periodic (B : Mat) (f : Vec → ℂ) (z : periodModule B) (x : Vec) :
    cellPeriodize B f (x+z.val) = cellPeriodize B f x := by
  classical
  calc
    _ = ∑' w : periodModule B, f ((Equiv.addRight z w).val+x) := by
      apply tsum_congr
      intro w
      change f (w.val+(x+z.val)) = f ((w+z).val+x)
      congr 1
      change w.val+(x+z.val) = (w.val+z.val)+x
      abel
    _ = ∑' w : periodModule B, f (w.val+x) :=
      (Equiv.addRight z).tsum_eq (fun w : periodModule B => f (w.val+x))
    _ = _ := rfl

def cellFourier (B : Mat) (hB : B.det ≠ 0) (f : Vec → ℂ) (n : IntVec) : ℂ :=
  ∫ x in periodCell B hB, f x * cellWave B n x

theorem cellFourier_periodize (B : Mat) (hB : B.det ≠ 0) (f : Vec → ℂ) (n : IntVec)
    (hf : Integrable (fun y => f y * cellWave B n y)) :
    cellFourier B hB (cellPeriodize B f) n = ∫ x : Vec, f x * cellWave B n x := by
  unfold cellFourier
  simp_rw [cellPeriodize_mul_wave B hB]
  exact cellPeriodize_integral B hB hf

/-- Local copy of `dot_right_smul` from `BccSharp.TwoSite.PhysicalScale`, which this
file does not import. -/
private theorem cell_dot_right_smul (t : ℝ) (k x : Vec) : dot k (t • x) = t * dot k x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cellWave_integral (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    (∫ x in periodCell B hB, cellWave B n x) = if n=0 then (volumeOf B : ℂ) else 0 := by
  classical
  letI : Countable (periodModule B) := Countable.of_equiv _ (periodIndices B hB)
  by_cases hn : n=0
  · subst n
    simp only [if_pos rfl, cellWave_zero, integral_const]
    have he : (volume.restrict (periodCell B hB)).real Set.univ = volume.real (periodCell B hB) := by
      simp [measureReal_def]
    rw [he, periodCell_volume B hB]
    simp [Complex.real_smul]
  rw [if_neg hn]
  let u := cycleFrequency B n
  have hu : u ≠ 0 := fun h => hn (cycleFrequency_injective B hB (h.trans (cycleFrequency_zero B).symm))
  let y : Vec := (1/(2*sq u)) • u
  have hsq : sq u ≠ 0 := fun h => hu ((sq_eq_zero_iff u).mp h)
  have hy : Ewald.dot u y = 1/2 := by
    change dot u ((1/(2*sq u)) • u) = _
    rw [cell_dot_right_smul]
    have hs : dot u u = sq u := by simp [dot, sq, pow_two]
    rw [hs]
    field_simp [hsq]
  have hyw : cellWave B n y = -1 := by
    unfold cellWave CoulombLaplace.wave
    change Complex.exp (-((2*Real.pi*Ewald.dot u y : ℝ) : ℂ)*Complex.I) = _
    rw [hy, show -((2*Real.pi*(1/2 : ℝ) : ℝ) : ℂ)*Complex.I = -(Real.pi*Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have ht := (periodCell_fundamental B hB).vadd_of_comm y
  have hi := (periodCell_fundamental B hB).setIntegral_eq ht (f := cellWave B n) (fun z x => by
    change cellWave B n (z.val+x) = cellWave B n x
    rw [cellWave_add, cellWave_period B hB, one_mul])
  have himage : y +ᵥ periodCell B hB = (fun x : Vec => y+x) '' periodCell B hB := rfl
  rw [himage, (measurePreserving_add_left volume y).setIntegral_image_emb
    (measurableEmbedding_addLeft y) (cellWave B n) (periodCell B hB)] at hi
  simp_rw [cellWave_add, hyw] at hi
  rw [integral_const_mul] at hi
  linear_combination (1/2 : ℂ)*hi

theorem cellWave_integrable (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    IntegrableOn (cellWave B n) (periodCell B hB) := by
  letI : IsFiniteMeasure (volume.restrict (periodCell B hB)) :=
    isFiniteMeasure_restrict.mpr (periodCell_finite B hB).ne
  exact (integrable_const (1 : ℝ)).mono' (cellWave_continuous B n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (cellWave_norm B n x).le)

theorem cell_integrable_mul_wave (B : Mat) (hB : B.det ≠ 0) (n : IntVec) {f : Vec → ℂ}
    (hf : IntegrableOn f (periodCell B hB)) :
    IntegrableOn (fun x => f x*cellWave B n x) (periodCell B hB) := by
  apply hf.norm.mono'
  · exact hf.aestronglyMeasurable.mul (cellWave_continuous B n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by rw [norm_mul, cellWave_norm, mul_one])

theorem cellFourier_add (B : Mat) (hB : B.det ≠ 0) (n : IntVec) {f g : Vec → ℂ}
    (hf : IntegrableOn f (periodCell B hB)) (hg : IntegrableOn g (periodCell B hB)) :
    cellFourier B hB (fun x => f x+g x) n = cellFourier B hB f n + cellFourier B hB g n := by
  unfold cellFourier
  simp_rw [add_mul]
  exact integral_add (cell_integrable_mul_wave B hB n hf) (cell_integrable_mul_wave B hB n hg)

theorem cellFourier_sub (B : Mat) (hB : B.det ≠ 0) (n : IntVec) {f g : Vec → ℂ}
    (hf : IntegrableOn f (periodCell B hB)) (hg : IntegrableOn g (periodCell B hB)) :
    cellFourier B hB (fun x => f x-g x) n = cellFourier B hB f n - cellFourier B hB g n := by
  unfold cellFourier
  simp_rw [sub_mul]
  exact integral_sub (cell_integrable_mul_wave B hB n hf) (cell_integrable_mul_wave B hB n hg)

theorem cellFourier_const_mul (B : Mat) (hB : B.det ≠ 0) (n : IntVec) (c : ℂ) (f : Vec → ℂ) :
    cellFourier B hB (fun x => c*f x) n = c*cellFourier B hB f n := by
  unfold cellFourier
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

def cellSeries (B : Mat) (a : IntVec → ℝ) (x : Vec) : ℂ :=
  ∑' n : IntVec, (a n : ℂ) * cellWave B (-n) x

theorem cellSeries_summable (B : Mat) {a : IntVec → ℝ} (ha : Summable a) (x : Vec) :
    Summable (fun n : IntVec => (a n : ℂ) * cellWave B (-n) x) := by
  apply ha.norm.of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, cellWave_norm, mul_one]

theorem cellSeries_continuous (B : Mat) {a : IntVec → ℝ} (ha : Summable a) :
    Continuous (cellSeries B a) := by
  apply continuous_tsum (u := fun n => ‖a n‖)
    (fun n => continuous_const.mul (cellWave_continuous B (-n))) ha.norm
  intro n x
  show ‖(a n : ℂ) * cellWave B (-n) x‖ ≤ ‖a n‖
  rw [norm_mul, Complex.norm_real, cellWave_norm, mul_one]

theorem cellSeries_integrable (B : Mat) (hB : B.det ≠ 0) {a : IntVec → ℝ} (ha : Summable a) :
    IntegrableOn (cellSeries B a) (periodCell B hB) := by
  letI : IsFiniteMeasure (volume.restrict (periodCell B hB)) :=
    isFiniteMeasure_restrict.mpr (periodCell_finite B hB).ne
  apply (integrable_const (∑' n, ‖a n‖)).mono' (cellSeries_continuous B ha).aestronglyMeasurable
  filter_upwards with x
  apply tsum_of_norm_bounded ha.norm.hasSum
  intro n
  rw [norm_mul, Complex.norm_real, cellWave_norm, mul_one]

theorem cellSeries_periodic (B : Mat) (hB : B.det ≠ 0) (a : IntVec → ℝ)
    (z : periodModule B) (x : Vec) :
    cellSeries B a (x+z.val) = cellSeries B a x := by
  simp_rw [cellSeries, cellWave_add, cellWave_period B hB, mul_one]

theorem cellSeries_fourier (B : Mat) (hB : B.det ≠ 0) {a : IntVec → ℝ} (ha : Summable a) (n : IntVec) :
    cellFourier B hB (cellSeries B a) n = (volumeOf B : ℂ) * a n := by
  classical
  have hi (m : IntVec) : IntegrableOn (fun x => (a m : ℂ) * cellWave B (n-m) x) (periodCell B hB) :=
    (cellWave_integrable B hB (n-m)).const_mul _
  have hn : Summable (fun m : IntVec => ∫ x in periodCell B hB, ‖(a m : ℂ)*cellWave B (n-m) x‖) := by
    simp_rw [norm_mul, Complex.norm_real, cellWave_norm, mul_one, integral_const, smul_eq_mul]
    exact ha.norm.mul_left _
  unfold cellFourier cellSeries
  simp_rw [← tsum_mul_right, mul_assoc, cellWave_sub_frequency]
  rw [← integral_tsum_of_summable_integral_norm hi hn]
  have he (m : IntVec) :
      (∫ x in periodCell B hB, (a m : ℂ)*cellWave B (n-m) x) =
        if m=n then (volumeOf B : ℂ)*a n else 0 := by
    rw [integral_const_mul, cellWave_integral B hB]
    by_cases h : m=n
    · subst m
      simp [mul_comm]
    · have h' : n-m ≠ 0 := fun eq => h (sub_eq_zero.mp eq).symm
      simp [h, h']
  simp_rw [he]
  simp

theorem cellConstant_fourier (B : Mat) (hB : B.det ≠ 0) (c : ℂ) (n : IntVec) :
    cellFourier B hB (fun _ => c) n = if n=0 then c * (volumeOf B : ℂ) else 0 := by
  classical
  unfold cellFourier
  rw [integral_const_mul, cellWave_integral B hB]
  split_ifs <;> simp

private abbrev CubeCoordinates := {x : Vec // ∀ i, x i ∈ Set.Ico (0 : ℝ) (0+1)}

private def cellCoordinates (B : Mat) (hB : B.det ≠ 0) : periodCell B hB ≃ᵐ CubeCoordinates where
  toFun x := ⟨(matrixBasis B hB).equivFunL x.val, by
    simpa only [Basis.equivFunL_apply, zero_add, periodCell, ZSpan.mem_fundamentalDomain] using x.property⟩
  invFun y := ⟨(matrixBasis B hB).equivFunL.symm y.val, by
    change ∀ i, (matrixBasis B hB).repr ((matrixBasis B hB).equivFunL.symm y.val) i ∈ Set.Ico (0 : ℝ) 1
    simpa only [← Basis.equivFunL_apply, ContinuousLinearEquiv.apply_symm_apply, zero_add] using y.property⟩
  left_inv x := Subtype.ext ((matrixBasis B hB).equivFunL.symm_apply_apply x.val)
  right_inv y := Subtype.ext ((matrixBasis B hB).equivFunL.apply_symm_apply y.val)
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact (matrixBasis B hB).equivFunL.continuous.measurable.comp measurable_subtype_coe
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact (matrixBasis B hB).equivFunL.symm.continuous.measurable.comp measurable_subtype_coe

private def cubeTorus : UnitAddTorus (Fin 3) ≃ᵐ CubeCoordinates :=
  (MeasurableEquiv.piCongrRight fun _ : Fin 3 => AddCircle.measurableEquivIco 1 0).trans
    MeasurableEquiv.subtypePiEquivPi.symm

private def cellTorus (B : Mat) (hB : B.det ≠ 0) : periodCell B hB ≃ᵐ UnitAddTorus (Fin 3) :=
  (cellCoordinates B hB).trans cubeTorus.symm

private theorem cellTorus_coord (B : Mat) (hB : B.det ≠ 0) (x : periodCell B hB) (i : Fin 3) :
    cellTorus B hB x i = ((matrixBasis B hB).repr x.val i : UnitAddCircle) := by
  change ((matrixBasis B hB).equivFunL x.val i : UnitAddCircle) = _
  rw [Basis.equivFunL_apply]

private theorem cell_coords_reconstruct (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    B.mulVec (fun i => (matrixBasis B hB).repr x i) = x := by
  calc
    _ = ∑ i, ((matrixBasis B hB).repr x i) • matrixBasis B hB i := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, matrixBasis_column]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = _ := (matrixBasis B hB).sum_repr x

private theorem cellTorus_wave (B : Mat) (hB : B.det ≠ 0) (n : IntVec) (x : periodCell B hB) :
    UnitAddTorus.mFourier n (cellTorus B hB x) = cellWave B (-n) x.val := by
  have hdot : dot (cycleFrequency B (-n)) x.val =
      -(∑ i : Fin 3, (n i : ℝ)*((matrixBasis B hB).repr x.val i)) := by
    have he := cycleFrequency_dot B hB (-n) (fun i => (matrixBasis B hB).repr x.val i)
    rw [cell_coords_reconstruct B hB] at he
    rw [he]
    simp [dot, castVec_neg, Pi.neg_apply, castVec, Fin.sum_univ_three] <;> ring
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, cellTorus_coord, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum, cellWave, CoulombLaplace.wave]
  change _ = Complex.exp (-((2*Real.pi*dot (cycleFrequency B (-n)) x.val : ℝ) : ℂ)*Complex.I)
  rw [hdot]
  congr 1
  simp only [Fin.sum_univ_three, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_neg,
    Complex.ofReal_intCast, Complex.ofReal_ofNat]
  ring

private def cellSubMeasure (B : Mat) (hB : B.det ≠ 0) : Measure (periodCell B hB) :=
  volume.comap Subtype.val

private instance (B : Mat) (hB : B.det ≠ 0) : IsFiniteMeasure (cellSubMeasure B hB) := by
  constructor
  rw [cellSubMeasure, Measure.comap_apply _ Subtype.val_injective
    (fun _ => (periodCell_measurable B hB).subtype_image) _ MeasurableSet.univ,
    Set.image_univ, Subtype.range_val]
  exact periodCell_finite B hB

private def cellTorusMeasure (B : Mat) (hB : B.det ≠ 0) : Measure (UnitAddTorus (Fin 3)) :=
  (cellSubMeasure B hB).map (cellTorus B hB)

private instance (B : Mat) (hB : B.det ≠ 0) : IsFiniteMeasure (cellTorusMeasure B hB) :=
  inferInstanceAs (IsFiniteMeasure ((cellSubMeasure B hB).map (cellTorus B hB)))

private def liftToCellTorus (B : Mat) (hB : B.det ≠ 0) (f : Vec → ℂ) (x : UnitAddTorus (Fin 3)) : ℂ :=
  f ((cellTorus B hB).symm x).val

private theorem liftToCellTorus_integrable (B : Mat) (hB : B.det ≠ 0) {f : Vec → ℂ}
    (hf : IntegrableOn f (periodCell B hB)) :
    Integrable (liftToCellTorus B hB f) (cellTorusMeasure B hB) := by
  rw [cellTorusMeasure, integrable_map_equiv]
  simpa only [liftToCellTorus, MeasurableEquiv.symm_apply_apply, Function.comp_def, cellSubMeasure] using
    (integrableOn_iff_comap_subtypeVal (periodCell_measurable B hB)).mp hf

private theorem liftToCellTorus_fourier (B : Mat) (hB : B.det ≠ 0) (f : Vec → ℂ) (n : IntVec) :
    (∫ x, UnitAddTorus.mFourier n x*liftToCellTorus B hB f x ∂cellTorusMeasure B hB) =
      cellFourier B hB f (-n) := by
  rw [cellTorusMeasure, integral_map_equiv]
  simp only [liftToCellTorus, MeasurableEquiv.symm_apply_apply, cellTorus_wave]
  simp_rw [mul_comm (cellWave _ _ _)]
  exact integral_subtype_comap (periodCell_measurable B hB) (fun x : Vec => f x * cellWave B (-n) x)

theorem cellFourier_unique_periodic (B : Mat) (hB : B.det ≠ 0)
    {f g : Vec → ℂ} (hf : IntegrableOn f (periodCell B hB)) (hg : IntegrableOn g (periodCell B hB))
    (pf : ∀ z : periodModule B, ∀ x, f (x+z.val)=f x)
    (pg : ∀ z : periodModule B, ∀ x, g (x+z.val)=g x)
    (hc : ∀ n, cellFourier B hB f n = cellFourier B hB g n) : f =ᵐ[volume] g := by
  have he := FourierUniqueness.ae_eq (liftToCellTorus_integrable B hB hf)
    (liftToCellTorus_integrable B hB hg) (fun n => by
      rw [liftToCellTorus_fourier, liftToCellTorus_fourier]
      exact hc (-n))
  have hd := ae_of_ae_map (cellTorus B hB).measurable.aemeasurable he
  have hr : f =ᵐ[volume.restrict (periodCell B hB)] g := by
    apply (ae_restrict_iff_subtype (periodCell_measurable B hB)).mpr
    simpa only [liftToCellTorus, MeasurableEquiv.symm_apply_apply, cellSubMeasure] using hd
  have hh : ∀ᵐ x : Vec, x ∈ periodCell B hB → f x=g x :=
    (ae_restrict_iff' (periodCell_measurable B hB)).mp hr
  have ht (z : periodModule B) : ∀ᵐ x : Vec, z.val+x ∈ periodCell B hB → f x=g x := by
    have hx := (measurePreserving_add_left volume z.val).quasiMeasurePreserving.ae hh
    filter_upwards [hx] with x hx
    intro hmem
    simpa only [add_comm z.val x, pf, pg] using hx hmem
  letI : Countable (periodModule B) := Countable.of_equiv _ (periodIndices B hB)
  have hall : ∀ᵐ x : Vec, ∀ z : periodModule B, z.val+x ∈ periodCell B hB → f x=g x := ae_all_iff.mpr ht
  filter_upwards [hall, (periodCell_fundamental B hB).ae_covers] with x hx hcover
  obtain ⟨z,hz⟩ := hcover
  exact hx z hz

end BccSharp.Coulomb
