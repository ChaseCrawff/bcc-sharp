import BccSharp.Cover.OverlayScalarHeat
import BccSharp.Cover.CoverDirectSeries

set_option autoImplicit false

/-! Normalization bridge from the actual Series definition to the
regularized heat integral. The high and low scales are evaluated
separately and each contributes exactly -2 from its background term. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp DirectRoute

theorem integrateSeries {ι : Type*} [Countable ι] {S : Set ℝ} (f : ι→ℝ→ℝ)
    (hi : ∀ i, IntegrableOn (f i) S) (hs : Summable (fun i => ∫ s in S, ‖f i s‖)) :
    IntegrableOn (fun s => ∑' i, f i s) S ∧
      (∫ s in S, ∑' i, f i s)=∑' i, ∫ s in S, f i s := by
  refine ⟨?_,(integral_tsum_of_summable_integral_norm hi hs).symm⟩
  let μ := volume.restrict S
  have meas (i : ι) : AEStronglyMeasurable (f i) μ := (hi i).aestronglyMeasurable
  have mass (i : ι) : (∫⁻ s, ‖f i s‖ₑ ∂μ)=ENNReal.ofReal (∫ s, ‖f i s‖ ∂μ) := by
    have e := ofReal_integral_eq_lintegral_ofReal (hi i).norm (Filter.Eventually.of_forall (fun s => norm_nonneg (f i s)))
    first | exact e.symm
          | simpa only [ofReal_norm_eq_enorm] using e.symm
          | simpa only [enorm_eq_nnnorm,ofReal_norm] using e.symm
  refine ⟨AEStronglyMeasurable.tsum meas,?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun s => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun i => (meas i).enorm)]
  simp_rw [mass]
  have nn (i : ι) : 0≤∫ s, ‖f i s‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have e : (∑' i, ENNReal.ofReal (∫ s, ‖f i s‖ ∂μ))=
      ENNReal.ofReal (∑' i, ∫ s, ‖f i s‖ ∂μ) := by
    first | exact (ENNReal.ofReal_tsum_of_nonneg nn hs).symm
          | exact (ENNReal.ofReal_tsum_of_nonneg hs nn).symm
  rw [e]
  exact ENNReal.ofReal_lt_top

private theorem direct_vector_ne (q : TwoSite) (hq : q.Valid) {n : IntVec} (hn : n≠0) :
    linearImage q.basis n≠0 := by
  intro e
  have unit : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (series_basis_nonsingular q hq))
  have he := Matrix.mulVec_injective_of_isUnit unit (e.trans (Matrix.mulVec_zero q.basis).symm)
  exact hn (funext fun i => by
    have h0 : ((n i : ℤ) : ℝ)=0 := congrFun he i
    exact_mod_cast h0)

private theorem cross_vector_ne (q : TwoSite) (hq : q.Valid) (n : IntVec) :
    q.basis.mulVec (castVec n+q.offset)≠0 := by
  intro e
  have unit : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (series_basis_nonsingular q hq))
  have he := Matrix.mulVec_injective_of_isUnit unit (e.trans (Matrix.mulVec_zero q.basis).symm)
  apply hq.2 (-n)
  have id : q.offset = castVec n+q.offset-castVec n := by abel
  rw [id,he,zero_sub,castVec_neg]

private theorem directHeat_integrable (x : Vec) (hx : x≠0) : Integrable (fun s : ℝ => 2*heat s x) := by
  have h : 0<Real.pi*sq x := mul_pos Real.pi_pos (lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff x).mp hx)))
  convert (integrable_exp_neg_mul_sq h).const_mul (2:ℝ) using 1
  funext s
  unfold heat
  congr 2
  ring

private theorem directHeat_kernel (x : Vec) :
    (∫ s in Ioi (1:ℝ), 2*heat s x)=gKernel (1/2) (Real.pi*sq x) := by
  rw [gKernel_half,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  unfold heat
  congr 2
  ring

def directHeatMode (q : TwoSite) (n : IntVec) (s : ℝ) : ℝ := if n=0 then 0 else 2*heat s (linearImage q.basis n)
def crossHeatMode (q : TwoSite) (n : IntVec) (s : ℝ) : ℝ := 2*heat s (q.basis.mulVec (castVec n+q.offset))

private theorem largeHeat_point (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0<s) :
    seriesHeatIntegrand q s=(∑' n, directHeatMode q n s)+(∑' n, crossHeatMode q n s)-4*(s^3)⁻¹ := by
  have hB := series_basis_nonsingular q hq
  have dir := heat_lattice_summable s hs q.basis hB 0
  simp only [zero_add] at dir
  have h0 : heat s (linearImage q.basis 0)=1 := by simp [linearImage,castVec_zero,heat,sq]
  have eq := (sum_at_zero _ dir).2
  rw [h0] at eq
  have ed : heatTheta q.basis 0 s=1+∑' n, if n=0 then 0 else heat s (linearImage q.basis n) := by
    simpa [heatTheta,heatThetaAt] using eq
  have ec : heatTheta q.basis q.offset s=(∑' n, heat s (q.basis.mulVec (castVec n+q.offset))) := by
    unfold heatTheta heatThetaAt
    apply tsum_congr
    intro n
    rw [linearImage,← Matrix.mulVec_add,add_comm q.offset]
  unfold seriesHeatIntegrand crossHeatMode directHeatMode
  rw [ed,ec,tsum_mul_left]
  have e (n : IntVec) : (if n=0 then 0 else 2*heat s (linearImage q.basis n))=
      2*(if n=0 then 0 else heat s (linearImage q.basis n)) := by split_ifs <;> simp
  simp_rw [e,tsum_mul_left]
  ring

theorem heat_integral_large (q : TwoSite) (hq : q.Valid) :
    IntegrableOn (seriesHeatIntegrand q) (Ioi 1) ∧
    (∫ s in Ioi (1:ℝ), seriesHeatIntegrand q s)=
      (∑' n, seriesDirectTerm q n)+(∑' n, seriesCrossTerm q n)-2 := by
  have direct n : IntegrableOn (directHeatMode q n) (Ioi 1) := by
    by_cases h : n=0
    · have e : directHeatMode q n=fun _ => 0 := by funext s; simp [directHeatMode,h]
      rw [e]
      exact integrableOn_zero
    · have e : directHeatMode q n=fun s => 2*heat s (linearImage q.basis n) := by
        funext s; simp [directHeatMode,h]
      rw [e]
      exact (directHeat_integrable _ (direct_vector_ne q hq h)).integrableOn
  have cross n : IntegrableOn (crossHeatMode q n) (Ioi 1) := (directHeat_integrable _ (cross_vector_ne q hq n)).integrableOn
  have eqDir n : (∫ s in Ioi (1:ℝ), directHeatMode q n s)= seriesDirectTerm q n := by
    by_cases h : n=0
    · simp [directHeatMode,seriesDirectTerm,h]
    · simp only [directHeatMode,seriesDirectTerm,h,↓reduceIte]
      rw [directHeat_kernel,linearImage,sq_mulVec_gram]
  have eqCross n : (∫ s in Ioi (1:ℝ), crossHeatMode q n s)= seriesCrossTerm q n := by
    simp only [crossHeatMode]
    rw [directHeat_kernel,sq_mulVec_gram,seriesCrossTerm]
  have nd n s : 0≤directHeatMode q n s := by
    unfold directHeatMode
    split_ifs
    · exact le_rfl
    · exact mul_nonneg zero_le_two (heat_nonneg _ _)
  have nc n s : 0≤ crossHeatMode q n s := mul_nonneg zero_le_two (heat_nonneg _ _)
  have sums := real_summable q hq
  have D := integrateSeries (directHeatMode q) direct (by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (nd _ _),eqDir]; exact sums.1)
  have C := integrateSeries (crossHeatMode q) cross (by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (nc _ _),eqCross]; exact sums.2)
  have rp (s : ℝ) : s^(-3 : ℝ)=(s^3)⁻¹ := by
    convert Real.rpow_neg_natCast s 3 using 1 <;> norm_num
  have bg : IntegrableOn (fun s : ℝ => 4*(s^3)⁻¹) (Ioi 1) := by
    have h := (integrableOn_Ioi_rpow_of_lt (a := (-3:ℝ)) (by norm_num) (c := 1) zero_lt_one).const_mul (4:ℝ)
    simp only [rp] at h
    exact h
  have bgValue : (∫ s in Ioi (1:ℝ), 4*(s^3)⁻¹)=2 := by
    rw [integral_const_mul,← show (∫ s in Ioi (1:ℝ), s^(-3 : ℝ))=(∫ s in Ioi (1:ℝ), (s^3)⁻¹) by simp only [rp]]
    rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num
  have eq : (seriesHeatIntegrand q) =ᵐ[volume.restrict (Ioi (1:ℝ))]
      fun s => (∑' n, directHeatMode q n s)+(∑' n, crossHeatMode q n s)-4*(s^3)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact largeHeat_point q hq s (zero_lt_one.trans hs)
  have DC : IntegrableOn (fun s => (∑' n, directHeatMode q n s)+(∑' n, crossHeatMode q n s)) (Ioi 1) :=
    D.1.fun_add C.1
  refine ⟨(DC.fun_sub bg).congr eq.symm,?_⟩
  rw [integral_congr_ae eq,integral_sub DC bg,integral_add D.1 C.1,D.2,C.2,bgValue]
  simp only [eqDir,eqCross]

def reciprocalWeight (q : TwoSite) (n : IntVec) : ℝ := 1+Real.cos (2*Real.pi*dot (castVec n) q.offset)
def reciprocalHeatMode (q : TwoSite) (n : IntVec) (s : ℝ) : ℝ :=
  if n=0 then 0 else reciprocalWeight q n*inversionHeat (Real.pi*sq (cycleFrequency q.basis n)) s

theorem reciprocalWeight_nonneg (q : TwoSite) (n : IntVec) : 0≤ reciprocalWeight q n := by
  unfold reciprocalWeight
  linarith [Real.neg_one_le_cos (2*Real.pi*dot (castVec n) q.offset)]

private theorem smallHeat_point (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0<s) :
    seriesHeatIntegrand q s=(∑' n, reciprocalHeatMode q n s)-2 := by
  have hB := series_basis_nonsingular q hq
  have d := heat_cycle_summable s⁻¹ (inv_pos.mpr hs) q.basis hB
  let g (n : IntVec) := heat s⁻¹ (cycleFrequency q.basis n)
  let c (n : IntVec) := Real.cos (2*Real.pi*dot (castVec n) q.offset)
  have dc : Summable (fun n => g n*c n) := d.of_norm_bounded (fun n => by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (heat_nonneg _ _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_le.mpr
      ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) (heat_nonneg _ _))
  have z (n : IntVec) : g n+g n*c n=reciprocalWeight q n*g n := by unfold reciprocalWeight c; ring
  have H : heatDual q.basis 0 s⁻¹+heatDual q.basis q.offset s⁻¹=
      2+∑' n, if n=0 then 0 else reciprocalWeight q n*g n := by
    calc
      _ = (∑' n, g n)+(∑' n, g n*c n) := by simp [heatDual,g,c,dot]
      _ = ∑' n, (g n+g n*c n) := (d.tsum_add dc).symm
      _ = g 0+g 0*c 0+(∑' n, if n=0 then 0 else g n+g n*c n) := (sum_at_zero _ (d.add dc)).2
      _ = _ := by
        have g0 : g 0=1 := by simp [g,heat,cycleFrequency_zero,sq]
        have c0 : c 0=1 := by simp [c,dot,castVec_zero]
        rw [g0,c0]
        simp only [z]
        ring
  unfold seriesHeatIntegrand
  rw [heat_poisson q.basis hB 0 s hs,heat_poisson q.basis hB q.offset s hs,volumeOf,hq.1,abs_one,one_mul,
    ← mul_add,H]
  have each (n : IntVec) : reciprocalHeatMode q n s=(2*(s^3)⁻¹)*
      (if n=0 then 0 else reciprocalWeight q n*g n) := by
    by_cases hn : n=0
    · simp [reciprocalHeatMode,hn]
    · simp only [reciprocalHeatMode,hn,↓reduceIte,inversionHeat,g,heat]
      rw [show -(Real.pi*sq (cycleFrequency q.basis n))/s^2=
        -Real.pi*(s⁻¹)^2*sq (cycleFrequency q.basis n) by ring]
      ring
  simp_rw [each,tsum_mul_left]
  ring

theorem heat_integral_small (q : TwoSite) (hq : q.Valid) :
    IntegrableOn (seriesHeatIntegrand q) (Ioc 0 1) ∧
    (∫ s in Ioc (0:ℝ) 1, seriesHeatIntegrand q s)=(∑' n, pairedTerm q n)-2 := by
  let S := Ioc (0:ℝ) 1
  have A (n : IntVec) (hn : n≠0) : 0<Real.pi*sq (cycleFrequency q.basis n) := by
    rw [← dual_quad]
    exact mul_pos Real.pi_pos (reciprocalPositive hq hn)
  have h (n : IntVec) : IntegrableOn (reciprocalHeatMode q n) S := by
    by_cases hn : n=0
    · have e : reciprocalHeatMode q n=fun _ => 0 := by funext s; simp [reciprocalHeatMode,hn]
      rw [e]
      exact integrableOn_zero
    · have e : reciprocalHeatMode q n=fun s =>
          reciprocalWeight q n*inversionHeat (Real.pi*sq (cycleFrequency q.basis n)) s := by
        funext s; simp [reciprocalHeatMode,hn]
      rw [e]
      exact ((inversionHeat_integrable (A n hn)).mono_set (fun s hs => hs.1)).const_mul _
  have e (n : IntVec) : (∫ s in S, reciprocalHeatMode q n s)=pairedTerm q n := by
    by_cases hn : n=0
    · simp [reciprocalHeatMode,hn,pairedTerm_eq,seriesReciprocalTerm]
    · simp only [reciprocalHeatMode,hn,↓reduceIte]
      rw [integral_const_mul,inversionHeat_small (A n hn),pairedTerm_eq,seriesReciprocalTerm,
        if_neg hn,dual_quad,gKernel_one (A n hn)] <;> rfl
  have nn (n : IntVec) {s : ℝ} (hs : 0<s) : 0≤ reciprocalHeatMode q n s := by
    unfold reciprocalHeatMode
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (reciprocalWeight_nonneg q n) (by unfold inversionHeat; positivity)
  have ms := series_modes q hq
  have sum := integrateSeries (reciprocalHeatMode q) h (by
    have equal (n : IntVec) : (∫ s in S, ‖reciprocalHeatMode q n s‖)=pairedTerm q n := by
      rw [← e]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      rw [Real.norm_eq_abs,abs_of_nonneg (nn n hs.1)]
    simpa only [equal,pairedTerm] using ms.reciprocalSummable.add ms.cosineSummable)
  letI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr (by simp [S])
  have const : IntegrableOn (fun _ : ℝ => (2:ℝ)) S := integrable_const _
  have eq : seriesHeatIntegrand q =ᵐ[volume.restrict S] fun s => (∑' n, reciprocalHeatMode q n s)-2 := by
    filter_upwards [ae_restrict_mem (show MeasurableSet S from measurableSet_Ioc)] with s hs
    exact smallHeat_point q hq s hs.1
  refine ⟨(sum.1.sub const).congr eq.symm,?_⟩
  change (∫ s in S, seriesHeatIntegrand q s)=_
  rw [integral_congr_ae eq,integral_sub sum.1 const,sum.2]
  simp [e,S,Real.volume_Ioc]

theorem energy_eq_heat_integral (q : TwoSite) (hq : q.Valid) :
    IntegrableOn (seriesHeatIntegrand q) (Ioi 0) ∧
    2*ac*energy q=∫ s in Ioi (0:ℝ), seriesHeatIntegrand q s := by
  obtain ⟨hl,L⟩ := heat_integral_large q hq
  obtain ⟨hs,S⟩ := heat_integral_small q hq
  have union : Ioc (0:ℝ) 1 ∪ Ioi 1=Ioi 0 := by
    ext s
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      exact (le_or_gt s 1).elim (fun h' => Or.inl ⟨h,h'⟩) Or.inr
  have dis : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr (fun _ h h' => (not_lt_of_ge h.2) h')
  rw [← union]
  refine ⟨hs.union hl,?_⟩
  rw [setIntegral_union dis measurableSet_Ioi hs hl,S,L,energy]
  have m := series_modes q hq
  rw [series_reciprocal_split q m.reciprocalSummable m.cosineSummable,← m.reciprocalSummable.tsum_add m.cosineSummable]
  unfold pairedTerm
  field_simp [ac_positive.ne'] <;> ring

end BccSharp.Coulomb.CompactCover.OverlayPlanar
