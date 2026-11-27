import BccSharp.TwoSite.GeneralSummability
import BccSharp.TwoSite.PhysicalScale
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

/-! Conversion of the Series two-site expression into the explicit
screened Ewald series at the Series split. -/

noncomputable section
open scoped BigOperators
open Classical MeasureTheory

namespace BccSharp.Coulomb

theorem gKernel_half (t : ℝ) :
    gKernel (1/2) t = 2 * ∫ s in Set.Ioi (1 : ℝ), Real.exp (-t*s^2) := by
  let g (u : ℝ) := Real.exp (-t*u)*u ^ ((1/2 : ℝ)-1)
  have h := integral_comp_rpow_Ioi_of_pos' (g := g)
    (by norm_num : (0 : ℝ) < 2) (c := 1) zero_le_one
  rw [Real.one_rpow] at h
  change (∫ s in Set.Ioi (1 : ℝ), g s) = _
  rw [← h, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have sp : 0 < s := zero_lt_one.trans (Set.mem_Ioi.mp hs)
  have hp : (s^2) ^ ((1/2 : ℝ)-1) = s⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul sp.le]
    rw [show ((2 : ℕ) : ℝ) * ((1/2 : ℝ)-1) = -1 by norm_num, Real.rpow_neg_one]
  change (2 * s ^ ((2 : ℝ)-1)) * g (s ^ (2 : ℝ)) = 2 * Real.exp (-t*s^2)
  rw [Real.rpow_two]
  rw [show (2 : ℝ)-1 = 1 by norm_num, Real.rpow_one]
  unfold g
  rw [hp]
  field_simp [sp.ne'] <;> ring

theorem screened_series_term (v : Vec) (hv : v ≠ 0) :
    ac * screened seriesScreen (ac • v) = gKernel (1/2) (Real.pi*sq v) := by
  have hs : 0 < sq v := lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff v).mp hv))
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  calc
    _ = screened (Real.sqrt Real.pi) v := by
      rw [seriesScreen, screened_scale _ ac ac_positive]
      field_simp [ac_positive.ne']
    _ = _ := by
      rw [screened_gaussian_integral _ v hs, gKernel_half]
      let g (s : ℝ) := Real.exp (-s^2*sq v)
      have h := integral_comp_mul_right_Ioi' g 1 hp
      simp only [one_mul, smul_eq_mul] at h
      change (2/Real.sqrt Real.pi)*(∫ s in Set.Ioi (Real.sqrt Real.pi), g s) = _
      rw [← h]
      have he : (∫ s in Set.Ioi (1 : ℝ), g (s*Real.sqrt Real.pi)) =
          ∫ s in Set.Ioi (1 : ℝ), Real.exp (-(Real.pi*sq v)*s^2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s _
        show Real.exp (-(s * Real.sqrt Real.pi)^2 * sq v) = Real.exp (-(Real.pi*sq v)*s^2)
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
        congr 1
        ring
      rw [he]
      field_simp [hp.ne'] <;> ring

theorem series_basis_nonsingular (q : TwoSite) (hq : q.Valid) : q.basis.det ≠ 0 := by
  rw [hq.1]
  exact one_ne_zero

theorem series_physical_basis_nonsingular (q : TwoSite) (hq : q.Valid) : (physicalBasis q).det ≠ 0 := by
  have hv := physicalBasis_volume q hq
  unfold volumeOf at hv
  intro hz
  rw [hz, abs_zero] at hv
  exact (pow_pos ac_positive 3).ne' hv.symm

theorem series_direct_mode (q : TwoSite) (hq : q.Valid) (n : IntVec) :
    seriesDirectTerm q n = ac * (if n=0 then 0 else screened seriesScreen (linearImage (physicalBasis q) n)) := by
  by_cases hn : n=0
  · simp [seriesDirectTerm, hn]
  have hv : q.basis.mulVec (castVec n) ≠ 0 := by
    intro h
    have hB : IsUnit q.basis :=
      (Matrix.isUnit_iff_isUnit_det q.basis).mpr (isUnit_iff_ne_zero.mpr (series_basis_nonsingular q hq))
    have he := Matrix.mulVec_injective_of_isUnit hB (h.trans (Matrix.mulVec_zero q.basis).symm)
    apply hn
    funext i
    have e := congrFun he i
    change ((n i : ℤ) : ℝ) = 0 at e
    exact_mod_cast e
  rw [seriesDirectTerm, if_neg hn, if_neg hn, physicalBasis, linearImage_scale, linearImage,
    screened_series_term _ hv, sq_mulVec_gram]

theorem series_cross_mode (q : TwoSite) (hq : q.Valid) (n : IntVec) :
    seriesCrossTerm q n =
      ac * screened seriesScreen (physicalTwoPositions q 1 + linearImage (physicalBasis q) n) := by
  have hv : q.basis.mulVec (castVec n + q.offset) ≠ 0 := by
    intro h
    have hB : IsUnit q.basis :=
      (Matrix.isUnit_iff_isUnit_det q.basis).mpr (isUnit_iff_ne_zero.mpr (series_basis_nonsingular q hq))
    have he := Matrix.mulVec_injective_of_isUnit hB (h.trans (Matrix.mulVec_zero q.basis).symm)
    apply hq.2 (-n)
    rw [castVec_neg]
    calc
      q.offset = castVec n + q.offset - castVec n := by abel
      _ = -castVec n := by rw [he, zero_sub]
  have hpos : physicalTwoPositions q 1 + linearImage (physicalBasis q) n =
      ac • q.basis.mulVec (castVec n + q.offset) := by
    rw [physicalBasis, linearImage_scale, linearImage, physicalTwoPositions, normalizedTwoPositions,
      if_neg (show (1 : Fin 2) ≠ 0 by decide), ← smul_add, Matrix.mulVec_add, add_comm]
  rw [hpos, screened_series_term _ hv, sq_mulVec_gram]
  rfl

theorem series_reciprocal_mode (q : TwoSite) (hq : q.Valid) (n : IntVec) :
    seriesReciprocalTerm q n =
      ac*(4*Real.pi/volumeOf (physicalBasis q))*reciprocalGreenTerm seriesScreen (physicalBasis q) n := by
  by_cases hn : n=0
  · simp [seriesReciprocalTerm, reciprocalGreenTerm, hn]
  let Q := quad (gram q.basis)⁻¹ (castVec n)
  have hq0 : Q ≠ 0 := by
    intro h
    have hs := dualWave_sq_gram q.basis n
    change sq (dualWave q.basis n) = (2*Real.pi)^2*Q at hs
    rw [h, mul_zero, sq_eq_zero_iff] at hs
    exact hn (dualWave_injective _ (series_basis_nonsingular q hq) (hs.trans (dualWave_zero _).symm))
  have hqpos : 0 < Q := by
    have hs := dualWave_sq_gram q.basis n
    have hp : 0 < (2*Real.pi)^2 := by positivity
    have hN := sq_nonnegative (dualWave q.basis n)
    change sq (dualWave q.basis n) = (2*Real.pi)^2*Q at hs
    rw [hs] at hN
    exact lt_of_le_of_ne (nonneg_of_mul_nonneg_right hN hp) (Ne.symm hq0)
  rw [seriesReciprocalTerm, reciprocalGreenTerm, if_neg hn, if_neg hn, physicalBasis_volume q hq,
    gKernel_one (mul_pos Real.pi_pos hqpos), physicalBasis, dualWave_scale ac ac_positive _ (series_basis_nonsingular q hq),
    sq_smul, dualWave_sq_gram, seriesScreen, div_pow, Real.sq_sqrt Real.pi_pos.le]
  have hex : (ac⁻¹)^2 * ((2*Real.pi)^2*Q) / (4*(Real.pi/ac^2)) = Real.pi*Q := by
    field_simp [ac_positive.ne', Real.pi_pos.ne'] <;> ring
  change Real.exp (-(Real.pi*Q))/(Real.pi*Q) =
    ac*(4*Real.pi/ac^3)*(Real.exp (-((ac⁻¹)^2*((2*Real.pi)^2*Q)/(4*(Real.pi/ac^2))))/
      ((ac⁻¹)^2*((2*Real.pi)^2*Q)))
  rw [hex]
  field_simp [ac_positive.ne', Real.pi_pos.ne', hq0] <;> ring

theorem series_phase (q : TwoSite) (hq : q.Valid) (n : IntVec) :
    dot (dualWave (physicalBasis q) n) (physicalTwoPositions q 1) =
      2*Real.pi*dot (castVec n) q.offset := by
  simp only [physicalBasis, physicalTwoPositions, normalizedTwoPositions,
    show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [dualWave_scale ac ac_positive _ (series_basis_nonsingular q hq),
    dot_right_smul, dot_left_smul, dot_mulVec_eq, transpose_mul_dual _ (series_basis_nonsingular q hq),
    dot_left_smul]
  field_simp [ac_positive.ne'] <;> ring

theorem series_cosine_mode (q : TwoSite) (hq : q.Valid) (n : IntVec) :
    seriesCosineTerm q n = ac*(4*Real.pi/volumeOf (physicalBasis q))*
      (reciprocalGreenTerm seriesScreen (physicalBasis q) n*
        Real.cos (dot (dualWave (physicalBasis q) n) (physicalTwoPositions q 1))) := by
  rw [seriesCosineTerm, series_reciprocal_mode q hq, series_phase q hq]
  ring

theorem periodicGreen_even (α : ℝ) (B : Mat) (v : Vec) :
    periodicGreen α B (-v) = periodicGreen α B v := by
  have screen_neg (x : Vec) : screened α (-x) = screened α x := by
    have he : sq (-x) = sq x := by simp [sq, Pi.neg_apply]
    simp [screened, he]
  have dneg (k : Vec) : dot k (-v) = -dot k v := by
    simpa only [zero_sub, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using dot_sub_right k 0 v
  have hreal : (∑' n, screened α (-v+linearImage B n)) =
      ∑' n, screened α (v+linearImage B n) := by
    calc
      _ = ∑' n, screened α (v+linearImage B (-n)) := by
        congr 1
        funext n
        have hl : linearImage B (-n) = -linearImage B n := by
          simp [linearImage, castVec_neg, Matrix.mulVec_neg]
        rw [hl, ← screen_neg (v + -linearImage B n)]
        congr 1
        abel
      _ = _ := (Equiv.neg IntVec).tsum_eq (fun n => screened α (v + linearImage B n))
  unfold periodicGreen
  simp_rw [hreal, dneg, Real.cos_neg]

theorem periodicGreen_add_period (α : ℝ) (B : Mat) (hB : B.det ≠ 0) (v y : Vec)
    (hy : y ∈ lattice B) : periodicGreen α B (v+y) = periodicGreen α B v := by
  obtain ⟨n, hn⟩ := hy
  change linearImage B n = y at hn
  have hreal : (∑' m, screened α ((v+y)+linearImage B m)) =
      ∑' m, screened α (v+linearImage B m) := by
    calc
      _ = ∑' m, screened α (v+linearImage B (addPeriodIndex n m)) := by
        apply tsum_congr
        intro m
        change screened α ((v+y)+linearImage B m) = screened α (v+linearImage B (m+n))
        rw [← hn]
        simp only [linearImage, castVec_add, Matrix.mulVec_add]
        congr 1
        abel
      _ = _ := (addPeriodIndex n).tsum_eq (fun m => screened α (v + linearImage B m))
  have hcos (m : IntVec) : Real.cos (dot (dualWave B m) (v+y)) = Real.cos (dot (dualWave B m) v) := by
    have hw := (dual_iff_annihilates B hB (dualWave B m)).mpr ⟨m,rfl⟩ y ⟨n,hn⟩
    obtain ⟨z,hz⟩ := (physicalWave_eq_one (dualWave B m) y).mp hw
    rw [dot_add_right, hz]
    exact Real.cos_add_int_mul_two_pi _ _
  unfold periodicGreen
  simp_rw [hreal, hcos]

private theorem seriesScreen_pos : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive

theorem series_modes (q : TwoSite) (hq : q.Valid) : SeriesModeIdentification q := by
  have hr := reciprocal_lattice_summable seriesScreen seriesScreen_pos (physicalBasis q)
    (series_physical_basis_nonsingular q hq)
  have hc := reciprocalPair_summable seriesScreen (physicalBasis q) (physicalTwoPositions q 1) hr
  refine ⟨?_, ?_, ?_, periodicGreen_even _ _ _, ?_⟩
  · exact (hr.mul_left (ac*(4*Real.pi/volumeOf (physicalBasis q)))).congr
      (fun n => (series_reciprocal_mode q hq n).symm)
  · exact (hc.mul_left (ac*(4*Real.pi/volumeOf (physicalBasis q)))).congr
      (fun n => (series_cosine_mode q hq n).symm)
  · unfold periodicGreen
    simp_rw [series_cross_mode q hq, series_cosine_mode q hq, tsum_mul_left, series_background_exact q hq]
    field_simp [ac_positive.ne'] <;> ring
  · unfold ewaldRegularSelf
    simp_rw [series_direct_mode q hq, series_reciprocal_mode q hq, tsum_mul_left,
      series_background_exact q hq, series_self_exact]
    field_simp [ac_positive.ne'] <;> ring

theorem green_two_eq_energy (q : TwoSite) (hq : q.Valid) :
    greenPerParticle seriesScreen (physicalBasis q) (physicalTwoPositions q) = energy q :=
  green_two_eq_h₂ q (series_modes q hq) ac_positive.ne'

end BccSharp.Coulomb
