import BccSharp.Cover.CoverDirectSeries
import BccSharp.TwoSite.ScreeningIndependence

set_option autoImplicit false

/-! Series positive Ewald series at an arbitrary screening `s > 0`.
The Ewald split of the physical lattice is `s * seriesScreen`; `s = 1` is the
Series split behind `h₂`. For every valid two-site point,

`h₂ q - 4 = s * S_cross + s * S_period + (1/s²) * S_wave - 2s - 2/s²`,

with the direct rate `π s²`, the reciprocal rate `π/s²`, and all three series
summable. Every term of the three series is nonnegative, so a finite partial
sum minus `2s + 2/s²` is a lower bound for `h₂ q - 4`. The proof computes the
physical Green function and regular self term at the split `s * seriesScreen`
mode by mode, and connects the splits with
`periodicGreen_screening_independent` and
`ewaldRegularSelf_screening_independent`. -/

noncomputable section
open scoped BigOperators
open Classical MeasureTheory

namespace BccSharp.Coulomb.ScreenedSeries

/-- Cross mode at screening `s`, without its prefactor `s`. -/
def crossTerm (s : ℝ) (q : TwoSite) (n : IntVec) : ℝ :=
  gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n + q.offset))

/-- Period mode at screening `s`, without its prefactor `s`; zero at `n = 0`. -/
def periodTerm (s : ℝ) (q : TwoSite) (n : IntVec) : ℝ :=
  if n = 0 then 0 else gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n))

/-- Reciprocal kernel at screening `s`, without phase or prefactor `1/s²`. -/
def recipTerm (s : ℝ) (q : TwoSite) (n : IntVec) : ℝ :=
  if n = 0 then 0 else gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2)

/-- Wave mode at screening `s`, with its phase and without its prefactor `1/s²`. -/
def waveTerm (s : ℝ) (q : TwoSite) (n : IntVec) : ℝ :=
  if n = 0 then 0 else
    (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
      gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2)

/-- The screened positive series with its two constants. -/
def screenedValue (s : ℝ) (q : TwoSite) : ℝ :=
  s * (∑' n, crossTerm s q n) + s * (∑' n, periodTerm s q n) +
    (1 / s^2) * (∑' n, waveTerm s q n) - 2 * s - 2 / s^2

/-! ### Agreement with the Series objects at `s = 1` -/

/-- At `s = 1` the screened value is `h₂ q - 4`, by definition. -/
theorem screenedValue_one (q : TwoSite) : screenedValue 1 q = h₂ q - 4 := by
  simp only [screenedValue, crossTerm, periodTerm, waveTerm, h₂, gram, one_pow, mul_one, div_one,
    one_mul]
  ring

theorem crossTerm_one (q : TwoSite) : crossTerm 1 q = seriesCrossTerm q := by
  funext n
  simp [crossTerm, seriesCrossTerm]

theorem periodTerm_one (q : TwoSite) : periodTerm 1 q = seriesDirectTerm q := by
  funext n
  simp [periodTerm, seriesDirectTerm]

theorem waveTerm_one (q : TwoSite) : waveTerm 1 q = CompactCover.DirectRoute.pairedTerm q := by
  funext n
  rw [CompactCover.DirectRoute.pairedTerm_eq]
  by_cases hn : n = 0
  · simp [waveTerm, seriesReciprocalTerm, hn]
  · simp [waveTerm, seriesReciprocalTerm, hn]

/-! ### Elementary facts -/

theorem gKernel_nonneg (a t : ℝ) : 0 ≤ gKernel a t := by
  unfold gKernel
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg (zero_lt_one.trans (Set.mem_Ioi.mp hu)).le _)

theorem crossTerm_nonneg (s : ℝ) (q : TwoSite) (n : IntVec) : 0 ≤ crossTerm s q n := by
  unfold crossTerm
  exact gKernel_nonneg _ _

theorem periodTerm_nonneg (s : ℝ) (q : TwoSite) (n : IntVec) : 0 ≤ periodTerm s q n := by
  unfold periodTerm
  split_ifs
  · exact le_rfl
  · exact gKernel_nonneg _ _

theorem waveTerm_nonneg (s : ℝ) (q : TwoSite) (n : IntVec) : 0 ≤ waveTerm s q n := by
  unfold waveTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by linarith [Real.neg_one_le_cos (2 * Real.pi * dot (castVec n) q.offset)])
      (gKernel_nonneg _ _)

theorem waveTerm_eq (s : ℝ) (q : TwoSite) (n : IntVec) :
    waveTerm s q n = (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) * recipTerm s q n := by
  by_cases hn : n = 0
  · simp [waveTerm, recipTerm, hn]
  · simp [waveTerm, recipTerm, hn]

private theorem quad_neg (M : Mat) (v : Vec) : quad M (-v) = quad M v := by
  simp [quad, Matrix.mulVec_neg]

theorem periodTerm_neg (s : ℝ) (q : TwoSite) (n : IntVec) :
    periodTerm s q (-n) = periodTerm s q n := by
  simp [periodTerm, castVec_neg, quad_neg]

theorem waveTerm_neg (s : ℝ) (q : TwoSite) (n : IntVec) :
    waveTerm s q (-n) = waveTerm s q n := by
  have phase : dot (-castVec n) q.offset = -dot (castVec n) q.offset := by
    simp [dot, Finset.sum_neg_distrib]
  simp [waveTerm, castVec_neg, quad_neg, phase, mul_neg, Real.cos_neg]

private theorem castVec_ne_zero {n : IntVec} (hn : n ≠ 0) : castVec n ≠ 0 := by
  intro h
  apply hn
  funext i
  have e := congrFun h i
  change ((n i : ℤ) : ℝ) = 0 at e
  exact_mod_cast e

private theorem screen_pos : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive

private theorem screen_sq (s : ℝ) : (s * seriesScreen)^2 = s^2 * Real.pi / ac^2 := by
  rw [seriesScreen, mul_pow, div_pow, Real.sq_sqrt Real.pi_pos.le]
  ring

/-- The second site is not a period of the physical lattice. -/
theorem offset_not_period (q : TwoSite) (hq : q.Valid) :
    physicalTwoPositions q 1 ∉ lattice (physicalBasis q) := by
  rintro ⟨n, hn⟩
  change linearImage (physicalBasis q) n = physicalTwoPositions q 1 at hn
  rw [physicalBasis, linearImage_scale, physicalTwoPositions, normalizedTwoPositions,
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] at hn
  have h₁ : linearImage q.basis n = q.basis.mulVec q.offset := (smul_right_inj ac_positive.ne').mp hn
  rw [linearImage] at h₁
  have hB : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (series_basis_nonsingular q hq))
  exact hq.2 n (Matrix.mulVec_injective_of_isUnit hB h₁).symm

/-! ### The physical modes at the split `s * seriesScreen` -/

/-- One real-space mode at the split `s * seriesScreen`. -/
theorem screened_term {s : ℝ} (hs : 0 < s) (v : Vec) (hv : 0 < sq v) :
    ac * screened (s * seriesScreen) (ac • v) = s * gKernel (1/2) (Real.pi * s^2 * sq v) := by
  have hr : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hp : 0 < s * Real.sqrt Real.pi := mul_pos hs hr
  calc
    _ = screened (s * Real.sqrt Real.pi) v := by
      rw [(show s * seriesScreen = s * Real.sqrt Real.pi / ac by rw [seriesScreen]; ring),
        screened_scale _ ac ac_positive]
      field_simp [ac_positive.ne']
    _ = _ := by
      rw [screened_gaussian_integral _ v hv, gKernel_half]
      let g (u : ℝ) := Real.exp (-u^2 * sq v)
      have h := integral_comp_mul_right_Ioi' g 1 hp
      simp only [one_mul, smul_eq_mul] at h
      change (2 / Real.sqrt Real.pi) * (∫ u in Set.Ioi (s * Real.sqrt Real.pi), g u) = _
      rw [← h]
      have he : (∫ u in Set.Ioi (1 : ℝ), g (u * (s * Real.sqrt Real.pi))) =
          ∫ u in Set.Ioi (1 : ℝ), Real.exp (-(Real.pi * s^2 * sq v) * u^2) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro u _
        show Real.exp (-(u * (s * Real.sqrt Real.pi))^2 * sq v) =
          Real.exp (-(Real.pi * s^2 * sq v) * u^2)
        rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
        congr 1
        ring
      rw [he]
      field_simp [hr.ne']

theorem period_mode (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) (n : IntVec) :
    ac * (if n = 0 then 0 else screened (s * seriesScreen) (linearImage (physicalBasis q) n)) =
      s * periodTerm s q n := by
  by_cases hn : n = 0
  · simp [periodTerm, hn]
  have hpos : 0 < sq (q.basis.mulVec (castVec n)) := by
    rw [sq_mulVec_gram]
    exact CompactCover.DirectRoute.realPositive (series_basis_nonsingular q hq) (castVec_ne_zero hn)
  rw [ite_eq_right hn, periodTerm, ite_eq_right hn, physicalBasis, linearImage_scale, linearImage,
    screened_term hs _ hpos, sq_mulVec_gram]

theorem cross_mode (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) (n : IntVec) :
    ac * screened (s * seriesScreen) (physicalTwoPositions q 1 + linearImage (physicalBasis q) n) =
      s * crossTerm s q n := by
  have hv : castVec n + q.offset ≠ 0 := by
    intro h
    apply hq.2 (-n)
    rw [castVec_neg]
    calc
      q.offset = castVec n + q.offset - castVec n := by abel
      _ = -castVec n := by rw [h, zero_sub]
  have hpos : 0 < sq (q.basis.mulVec (castVec n + q.offset)) := by
    rw [sq_mulVec_gram]
    exact CompactCover.DirectRoute.realPositive (series_basis_nonsingular q hq) hv
  have hx : physicalTwoPositions q 1 + linearImage (physicalBasis q) n =
      ac • q.basis.mulVec (castVec n + q.offset) := by
    rw [physicalBasis, linearImage_scale, linearImage, physicalTwoPositions, normalizedTwoPositions,
      ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), ← smul_add, Matrix.mulVec_add, add_comm]
  rw [hx, screened_term hs _ hpos, sq_mulVec_gram]
  rfl

theorem reciprocal_mode (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) (n : IntVec) :
    ac * (4 * Real.pi / volumeOf (physicalBasis q)) *
        reciprocalGreenTerm (s * seriesScreen) (physicalBasis q) n =
      (1 / s^2) * recipTerm s q n := by
  by_cases hn : n = 0
  · simp [recipTerm, reciprocalGreenTerm, hn]
  have hQ : 0 < quad (gram q.basis)⁻¹ (castVec n) := CompactCover.DirectRoute.reciprocalPositive hq hn
  have ht : 0 < Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2 :=
    div_pos (mul_pos Real.pi_pos hQ) (pow_pos hs 2)
  rw [recipTerm, reciprocalGreenTerm, ite_eq_right hn, ite_eq_right hn, physicalBasis_volume q hq,
    gKernel_one ht, physicalBasis, dualWave_scale ac ac_positive _ (series_basis_nonsingular q hq),
    sq_smul, dualWave_sq_gram, screen_sq]
  generalize quad (gram q.basis)⁻¹ (castVec n) = Q at hQ ⊢
  have hex : (ac⁻¹)^2 * ((2 * Real.pi)^2 * Q) / (4 * (s^2 * Real.pi / ac^2)) =
      Real.pi * Q / s^2 := by
    field_simp [ac_positive.ne', Real.pi_pos.ne', hs.ne']
    ring
  rw [hex]
  field_simp [ac_positive.ne', Real.pi_pos.ne', hQ.ne', hs.ne']
  ring

theorem background (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    ac * greenBackground (s * seriesScreen) (physicalBasis q) = 1 / s^2 := by
  rw [greenBackground, physicalBasis_volume q hq, screen_sq]
  field_simp [ac_positive.ne', Real.pi_pos.ne', hs.ne']

/-! ### Summability -/

theorem crossTerm_summable (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    Summable (crossTerm s q) := by
  have h := screened_lattice_summable (s * seriesScreen) (mul_pos hs screen_pos) (physicalBasis q)
    (series_physical_basis_nonsingular q hq) (physicalTwoPositions q 1)
  refine ((h.mul_left ac).mul_left s⁻¹).congr (fun n => ?_)
  rw [cross_mode q hq s hs n, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem periodTerm_summable (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    Summable (periodTerm s q) := by
  have direct := screened_lattice_summable (s * seriesScreen) (mul_pos hs screen_pos) (physicalBasis q)
    (series_physical_basis_nonsingular q hq) 0
  have dropZero : Summable (fun n : IntVec =>
      if n = 0 then 0 else screened (s * seriesScreen) (linearImage (physicalBasis q) n)) := by
    apply direct.summable_of_eq_zero_or_self
    intro n
    by_cases hn : n = 0 <;> simp [hn]
  refine ((dropZero.mul_left ac).mul_left s⁻¹).congr (fun n => ?_)
  rw [period_mode q hq s hs n, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem recipTerm_summable (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    Summable (recipTerm s q) := by
  have h := reciprocal_lattice_summable (s * seriesScreen) (mul_pos hs screen_pos) (physicalBasis q)
    (series_physical_basis_nonsingular q hq)
  refine ((h.mul_left (ac * (4 * Real.pi / volumeOf (physicalBasis q)))).mul_left (s^2)).congr
    (fun n => ?_)
  rw [reciprocal_mode q hq s hs n, ← mul_assoc, mul_one_div_cancel (pow_ne_zero 2 hs.ne'), one_mul]

theorem cosTerm_summable (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    Summable (fun n => Real.cos (2 * Real.pi * dot (castVec n) q.offset) * recipTerm s q n) := by
  refine (recipTerm_summable q hq s hs).norm.of_norm_bounded (fun n => ?_)
  rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

theorem waveTerm_summable (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    Summable (waveTerm s q) :=
  ((recipTerm_summable q hq s hs).add (cosTerm_summable q hq s hs)).congr
    (fun n => by rw [waveTerm_eq]; ring)

/-! ### The physical Green function and regular self term at screening `s` -/

theorem green_offset (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    ac * periodicGreen (s * seriesScreen) (physicalBasis q) (physicalTwoPositions q 1) =
      s * (∑' n, crossTerm s q n) +
        (1 / s^2) * (∑' n, Real.cos (2 * Real.pi * dot (castVec n) q.offset) * recipTerm s q n) -
        1 / s^2 := by
  have hR : ac * (∑' n, screened (s * seriesScreen)
      (physicalTwoPositions q 1 + linearImage (physicalBasis q) n)) =
      s * ∑' n, crossTerm s q n := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    exact cross_mode q hq s hs n
  have hD : ac * ((4 * Real.pi / volumeOf (physicalBasis q)) *
      ∑' n, reciprocalGreenTerm (s * seriesScreen) (physicalBasis q) n *
        Real.cos (dot (dualWave (physicalBasis q) n) (physicalTwoPositions q 1))) =
      (1 / s^2) * ∑' n, Real.cos (2 * Real.pi * dot (castVec n) q.offset) * recipTerm s q n := by
    rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [← mul_assoc, reciprocal_mode q hq s hs n, series_phase q hq n]
    ring
  have hB := background q hq s hs
  unfold periodicGreen
  linear_combination hR + hD - hB

theorem regular_self (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    ac * ewaldRegularSelf (s * seriesScreen) (physicalBasis q) =
      s * (∑' n, periodTerm s q n) + (1 / s^2) * (∑' n, recipTerm s q n) - 2 * s - 1 / s^2 := by
  have hR : ac * (∑' n : IntVec, if n = 0 then 0 else
      screened (s * seriesScreen) (linearImage (physicalBasis q) n)) =
      s * ∑' n, periodTerm s q n := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    exact period_mode q hq s hs n
  have hD : ac * ((4 * Real.pi / volumeOf (physicalBasis q)) *
      ∑' n, reciprocalGreenTerm (s * seriesScreen) (physicalBasis q) n) =
      (1 / s^2) * ∑' n, recipTerm s q n := by
    rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    exact reciprocal_mode q hq s hs n
  have hS : ac * (2 * (s * seriesScreen) / Real.sqrt Real.pi) = 2 * s := by
    rw [seriesScreen]
    field_simp [ac_positive.ne', (Real.sqrt_pos.2 Real.pi_pos).ne']
  have hB := background q hq s hs
  unfold ewaldRegularSelf
  linear_combination hR + hD - hS - hB

/-- The two-site physical Ewald pair plus regular self term at the split
`s * seriesScreen`, in the screened series. -/
theorem green_sum (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    ac * (periodicGreen (s * seriesScreen) (physicalBasis q) (physicalTwoPositions q 1) +
      ewaldRegularSelf (s * seriesScreen) (physicalBasis q)) = screenedValue s q := by
  have hG := green_offset q hq s hs
  have hS := regular_self q hq s hs
  have hw : (∑' n, waveTerm s q n) = (∑' n, recipTerm s q n) +
      ∑' n, Real.cos (2 * Real.pi * dot (castVec n) q.offset) * recipTerm s q n := by
    rw [← (recipTerm_summable q hq s hs).tsum_add (cosTerm_summable q hq s hs)]
    refine tsum_congr (fun n => ?_)
    rw [waveTerm_eq]
    ring
  unfold screenedValue
  rw [hw]
  linear_combination hG + hS

/-! ### The screened series identity -/

theorem h₂_sub_four_eq (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    h₂ q - 4 = screenedValue s q := by
  have hk : 0 < seriesScreen := screen_pos
  have hL := series_physical_basis_nonsingular q hq
  have hG := periodicGreen_screening_independent (1 * seriesScreen) (s * seriesScreen) _ hL
    (mul_pos one_pos hk) (mul_pos hs hk) (offset_not_period q hq)
  have hR := ewaldRegularSelf_screening_independent (1 * seriesScreen) (s * seriesScreen) _ hL
    (mul_pos one_pos hk) (mul_pos hs hk)
  rw [← screenedValue_one q, ← green_sum q hq 1 one_pos, ← green_sum q hq s hs, hG, hR]

/-- **Series positive Ewald series at screening `s`.** For every valid two-site
point and every `s > 0`, with `B = q.basis` and `f = q.offset`. -/
theorem h₂_screened (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    h₂ q - 4 =
      s * (∑' n : IntVec,
        gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n + q.offset))) +
      s * (∑' n : IntVec, if n = 0 then 0 else
        gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n))) +
      (1 / s^2) * (∑' n : IntVec, if n = 0 then 0 else
        (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
          gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2)) -
      2 * s - 2 / s^2 :=
  h₂_sub_four_eq q hq s hs

/-- The three series of `h₂_screened` are summable. -/
theorem screened_summable (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    Summable (fun n : IntVec =>
        gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n + q.offset))) ∧
      Summable (fun n : IntVec => if n = 0 then 0 else
        gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n))) ∧
      Summable (fun n : IntVec => if n = 0 then 0 else
        (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
          gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2)) :=
  ⟨crossTerm_summable q hq s hs, periodTerm_summable q hq s hs, waveTerm_summable q hq s hs⟩

theorem energy_screened (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s) :
    energy q = screenedValue s q / (2 * ac) := by
  rw [energy, h₂_sub_four_eq q hq s hs]

/-! ### Finite lower bounds -/

theorem finite_lower (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s)
    (cross period wave : Finset IntVec) :
    s * (∑ n ∈ cross, crossTerm s q n) + s * (∑ n ∈ period, periodTerm s q n) +
      (1 / s^2) * (∑ n ∈ wave, waveTerm s q n) - 2 * s - 2 / s^2 ≤ h₂ q - 4 := by
  rw [h₂_sub_four_eq q hq s hs]
  unfold screenedValue
  have hc := (crossTerm_summable q hq s hs).sum_le_tsum cross (fun n _ => crossTerm_nonneg s q n)
  have hp := (periodTerm_summable q hq s hs).sum_le_tsum period (fun n _ => periodTerm_nonneg s q n)
  have hw := (waveTerm_summable q hq s hs).sum_le_tsum wave (fun n _ => waveTerm_nonneg s q n)
  have hs2 : 0 ≤ 1 / s^2 := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hc hs.le
  have h₂' := mul_le_mul_of_nonneg_left hp hs.le
  have h₃ := mul_le_mul_of_nonneg_left hw hs2
  linarith

/-- **Finite lower bound at screening `s`.** Any finite partial sums of the
three series of `h₂_screened`, minus `2s + 2/s²`, are at most `h₂ q - 4`. -/
theorem finite_lower_screened (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s)
    (cross period wave : Finset IntVec) :
    s * (∑ n ∈ cross,
        gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n + q.offset))) +
      s * (∑ n ∈ period, if n = 0 then 0 else
        gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n))) +
      (1 / s^2) * (∑ n ∈ wave, if n = 0 then 0 else
        (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
          gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2)) -
      2 * s - 2 / s^2 ≤ h₂ q - 4 :=
  finite_lower q hq s hs cross period wave

/-- The corner envelope form: cross modes over any finite set
with prefactor `s`, period and wave modes over lex-positive halves with
prefactors `2s` and `2/s²`. -/
theorem finite_lower_lex (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s)
    (cross half waves : Finset IntVec)
    (hhalf : ∀ n ∈ half, CompactCover.DirectRoute.lexPositive n)
    (hwaves : ∀ n ∈ waves, CompactCover.DirectRoute.lexPositive n) :
    s * (∑ n ∈ cross, crossTerm s q n) + 2 * s * (∑ n ∈ half, periodTerm s q n) +
      (2 / s^2) * (∑ n ∈ waves, waveTerm s q n) - 2 * s - 2 / s^2 ≤ h₂ q - 4 := by
  have h := finite_lower q hq s hs cross (CompactCover.DirectRoute.bothSigns half)
    (CompactCover.DirectRoute.bothSigns waves)
  have hp : (∑ n ∈ CompactCover.DirectRoute.bothSigns half, periodTerm s q n) =
      2 * ∑ n ∈ half, periodTerm s q n := by
    rw [← CompactCover.DirectRoute.sum_pairs half hhalf _ (periodTerm_neg s q), Finset.mul_sum]
  have hw : (∑ n ∈ CompactCover.DirectRoute.bothSigns waves, waveTerm s q n) =
      2 * ∑ n ∈ waves, waveTerm s q n := by
    rw [← CompactCover.DirectRoute.sum_pairs waves hwaves _ (waveTerm_neg s q), Finset.mul_sum]
  rw [hp, hw] at h
  calc
    _ = s * (∑ n ∈ cross, crossTerm s q n) + s * (2 * ∑ n ∈ half, periodTerm s q n) +
        (1 / s^2) * (2 * ∑ n ∈ waves, waveTerm s q n) - 2 * s - 2 / s^2 := by ring
    _ ≤ h₂ q - 4 := h

theorem energy_finite_lower (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s)
    (cross period wave : Finset IntVec) :
    (s * (∑ n ∈ cross, crossTerm s q n) + s * (∑ n ∈ period, periodTerm s q n) +
      (1 / s^2) * (∑ n ∈ wave, waveTerm s q n) - 2 * s - 2 / s^2) / (2 * ac) ≤ energy q := by
  unfold energy
  exact div_le_div_of_nonneg_right (finite_lower q hq s hs cross period wave)
    (mul_pos two_pos ac_positive).le

/-- **Energy-level corner envelope.**
Cross modes over any finite set with prefactor `s`; period and wave modes over
lex-positive finite sets with prefactors `2s` and `2/s²`; constant
`-2s - 2/s²`; division by `2 ac`. The terms are written out; lex-positive
indices are nonzero, so no `n = 0` guard is needed. -/
theorem energy_finite_lower_lex (q : TwoSite) (hq : q.Valid) (s : ℝ) (hs : 0 < s)
    (cross half waves : Finset IntVec)
    (hhalf : ∀ n ∈ half, CompactCover.DirectRoute.lexPositive n)
    (hwaves : ∀ n ∈ waves, CompactCover.DirectRoute.lexPositive n) :
    (s * (∑ n ∈ cross,
        gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n + q.offset))) +
      2 * s * (∑ n ∈ half, gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n))) +
      (2 / s^2) * (∑ n ∈ waves, (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
        gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2)) -
      2 * s - 2 / s^2) / (2 * ac) ≤ energy q := by
  have hp : (∑ n ∈ half, gKernel (1/2) (Real.pi * s^2 * quad (gram q.basis) (castVec n))) =
      ∑ n ∈ half, periodTerm s q n := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [periodTerm, ite_eq_right (CompactCover.DirectRoute.lex_ne (hhalf n hn))]
  have hw : (∑ n ∈ waves, (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
        gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / s^2)) =
      ∑ n ∈ waves, waveTerm s q n := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [waveTerm, ite_eq_right (CompactCover.DirectRoute.lex_ne (hwaves n hn))]
  rw [hp, hw, energy]
  exact div_le_div_of_nonneg_right (finite_lower_lex q hq s hs cross half waves hhalf hwaves)
    (mul_pos two_pos ac_positive).le

end BccSharp.Coulomb.ScreenedSeries
