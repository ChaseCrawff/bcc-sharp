import BccSharp.TwoSite.ScreeningIndependence

set_option autoImplicit false

/-! Regular part of the general periodic Green function. The
nonzero-image sum converges uniformly near the origin, and the removed
singularity is computed by the compact Gaussian screening difference. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace BccSharp.Coulomb
open BccSharp

private theorem gaussianLine_integrable : Integrable (fun s : ℝ => Real.exp (-s^2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) zero_lt_one

theorem erfcIntegral_continuous : Continuous erfcIntegral := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := (gaussianLine_integrable.integrableOn (s := Set.Ioi (t-1))).continuousOn_Ici_primitive_Ioi
  have ht : t ∈ Set.Ioi (t-1) := by change t-1 < t; linarith
  have hn : Set.Ici (t-1) ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds ht) Set.Ioi_subset_Ici_self
  have hp := h.continuousAt hn
  change ContinuousAt (fun x : ℝ => (2/Real.sqrt Real.pi) *
    ∫ s in Set.Ioi x, Real.exp (-s^2)) t
  exact continuousAt_const.mul hp

theorem screened_continuousAt (α : ℝ) {x : Vec} (hx : sq x ≠ 0) : ContinuousAt (screened α) x := by
  have hs : Continuous (fun y : Vec => Real.sqrt (sq y)) := by unfold sq; fun_prop
  have hu : ContinuousAt (fun y : Vec => erfcIntegral (α * Real.sqrt (sq y))) x :=
    (erfcIntegral_continuous.comp (continuous_const.mul hs)).continuousAt
  exact hu.div hs.continuousAt (Real.sqrt_pos.mpr
    (lt_of_le_of_ne (sq_nonnegative _) (Ne.symm hx))).ne'

private theorem cast_integer_sq_ge_one {n : IntVec} (hn : n ≠ 0) : 1 ≤ sq (castVec n) := by
  have existen : ∃ i : Fin 3, n i ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  obtain ⟨i,hi⟩ := existen
  have hf : (1 : ℝ) ≤ (n i : ℝ)^2 := by
    have e : n i ≤ -1 ∨ 1 ≤ n i := by omega
    rcases e with h | h
    · have hh : (n i : ℝ) ≤ -1 := by exact_mod_cast h
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (show (1 : ℝ) ≤ -(n i : ℝ) by linarith) 2
    · have hh : (1 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast h
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hh 2
  refine hf.trans ?_
  exact Finset.single_le_sum (fun j _ => sq_nonneg (castVec n j)) (Finset.mem_univ i)

private theorem screened_gaussian_bound (α : ℝ) (ha : 0 < α) (x : Vec) (hx : 0 < sq x) :
    ‖screened α x‖ ≤ Real.exp (-(α^2*sq x))/(α*Real.sqrt Real.pi*sq x) := by
  let r := Real.sqrt (sq x)
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r^2 = sq x := Real.sq_sqrt hx.le
  rw [Real.norm_eq_abs]
  change |Gaussian.erfcIntegral (α*r)/r| ≤ _
  rw [abs_of_nonneg (div_nonneg (Ewald.erfc_nonneg _) hr.le)]
  calc
    _ ≤ (Real.exp (-(α*r)^2)/(α*r*Real.sqrt Real.pi))/r :=
      div_le_div_of_nonneg_right (Gaussian.erfc_upper (mul_pos ha hr)) hr.le
    _ = _ := by
      rw [mul_pow, hr2, div_div, show (α*r*Real.sqrt Real.pi)*r = α*Real.sqrt Real.pi*r^2 by ring, hr2]

def regularRealSeries (α : ℝ) (B : Mat) (x : Vec) : ℝ :=
  ∑' n : IntVec, if n=0 then 0 else screened α (x+linearImage B n)

theorem regularRealSeries_continuousAt_zero (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) :
    ContinuousAt (regularRealSeries α B) 0 := by
  classical
  obtain ⟨c,hc,coerce⟩ := matrix_coercivity B hB
  let U : Set Vec := {x | sq x < c/4}
  have hU : IsOpen U := by
    have hsq : Continuous sq := by unfold sq; fun_prop
    exact isOpen_lt hsq continuous_const
  have h0 : (0 : Vec) ∈ U := by simpa [U,sq] using (show 0 < c/4 by positivity)
  have hco (n : IntVec) : c*sq (castVec n) ≤ sq (linearImage B n) := coerce _
  have hx (x : Vec) (hm : x ∈ U) (n : IntVec) (hn : n ≠ 0) :
      c/4 < sq (x+linearImage B n) := by
    have hh := shifted_sq x (linearImage B n)
    have hn' := mul_le_mul_of_nonneg_left (cast_integer_sq_ge_one hn) hc.le
    change sq x < c/4 at hm
    linarith [hco n]
  let C := (α*Real.sqrt Real.pi*(c/4))⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum := (integerGaussian_summable (show 0 < α^2*c/2 by positivity)).mul_left
    (C*Real.exp (α^2*(c/4)))
  refine ContinuousOn.continuousAt ?_ (hU.mem_nhds h0)
  unfold regularRealSeries
  refine continuousOn_tsum (fun n => ?_) hsum (fun n x hm => ?_)
  · by_cases hn : n=0
    · simp only [ite_eq_left hn]
      exact continuousOn_const
    · simp only [ite_eq_right hn]
      intro x hm
      have hpos : sq (x+linearImage B n) ≠ 0 :=
        ne_of_gt ((show (0 : ℝ) < c/4 by positivity).trans (hx x hm n hn))
      have hadd : ContinuousAt (fun y : Vec => y+linearImage B n) x := by fun_prop
      exact ((screened_continuousAt α hpos).comp_of_eq hadd rfl).continuousWithinAt
  · show ‖(if n=0 then 0 else screened α (x+linearImage B n))‖ ≤
      C*Real.exp (α^2*(c/4))*Real.exp (-(α^2*c/2)*sq (castVec n))
    by_cases hn : n=0
    · rw [ite_eq_left hn, norm_zero]
      positivity
    rw [ite_eq_right hn]
    have hr := (show (0 : ℝ) < c/4 by positivity).trans (hx x hm n hn)
    have h2 := shifted_sq x (linearImage B n)
    have h3 : c*sq (castVec n)/2-c/4 ≤ sq (x+linearImage B n) := by
      change sq x < c/4 at hm
      linarith [hco n]
    have ht : -(α^2*sq (x+linearImage B n)) ≤ α^2*(c/4)-(α^2*c/2)*sq (castVec n) := by
      have hh := mul_le_mul_of_nonneg_left h3 (sq_nonneg α)
      linarith
    have hden : α*Real.sqrt Real.pi*(c/4) ≤ α*Real.sqrt Real.pi*sq (x+linearImage B n) :=
      mul_le_mul_of_nonneg_left (hx x hm n hn).le (by positivity)
    calc
      _ ≤ Real.exp (-(α^2*sq (x+linearImage B n)))/(α*Real.sqrt Real.pi*sq (x+linearImage B n)) :=
        screened_gaussian_bound α ha _ hr
      _ ≤ Real.exp (-(α^2*sq (x+linearImage B n)))/(α*Real.sqrt Real.pi*(c/4)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
      _ = C*Real.exp (-(α^2*sq (x+linearImage B n))) := by unfold C; ring
      _ ≤ C*Real.exp (α^2*(c/4)-(α^2*c/2)*sq (castVec n)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht) hC
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring

theorem reciprocalPair_continuous (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) :
    Continuous (reciprocalPair α B) := by
  rw [show reciprocalPair α B = fun x => (cellSeries B (reciprocalGreenTerm α B) x).re from
    funext (fun x => (cellReciprocal_real α ha B hB x).symm)]
  exact Complex.continuous_re.comp (cellSeries_continuous B (reciprocal_lattice_summable α ha B hB))

private theorem erfcIntegral_zero : erfcIntegral 0 = 1 := by
  have h : (∫ s in Set.Ioi (0 : ℝ), Real.exp (-s^2)) = Real.sqrt Real.pi/2 := by
    simpa using integral_gaussian_Ioi 1
  rw [erfcIntegral, h]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']

private theorem realSeries_split (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    (∑' n : IntVec, screened α (x+linearImage B n)) = regularRealSeries α B x + screened α x := by
  classical
  let f (n : IntVec) := screened α (x+linearImage B n)
  have hf : Summable f := screened_lattice_summable α ha B hB x
  let r (n : IntVec) := if n=0 then 0 else f n
  have hr : Summable r := hf.summable_of_eq_zero_or_self (by intro n; by_cases hn : n=0 <;> simp [r,hn])
  let s (n : IntVec) := if n=0 then screened α x else 0
  have hs : HasSum s (screened α x) := by
    simpa [s] using (hasSum_single (f := s) (0 : IntVec) (by intro n hn; simp [s,hn]))
  have he (n : IntVec) : f n = r n+s n := by
    by_cases hn : n=0
    · subst hn
      simp [r, s, f, linearImage, castVec_zero]
    · simp [r, s, f, hn]
  unfold regularRealSeries
  change (∑' n, f n) = (∑' n, r n)+_
  simp_rw [he]
  rw [hr.tsum_add hs.summable, hs.tsum_eq]

theorem periodicGreen_regular_limit (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) :
    Filter.Tendsto (fun x => periodicGreen α B x - 1/Real.sqrt (sq x))
      (𝓝[Set.univ \ lattice B] (0 : Vec)) (𝓝 (ewaldRegularSelf α B)) := by
  let R (x : Vec) := regularRealSeries α B x - screenedDifference 0 α x +
    (4*Real.pi/volumeOf B)*reciprocalPair α B x - greenBackground α B
  have hc : ContinuousAt R 0 :=
    (((regularRealSeries_continuousAt_zero α ha B hB).sub
      (screenedDifference_continuous 0 α).continuousAt).add
      (continuousAt_const.mul (reciprocalPair_continuous α ha B hB).continuousAt)).sub continuousAt_const
  have hR : R 0 = ewaldRegularSelf α B := by
    unfold R regularRealSeries ewaldRegularSelf reciprocalPair dot
    simp [screenedDifference_zero]
    ring
  rw [← hR]
  apply Filter.Tendsto.congr' _ (hc.continuousWithinAt : ContinuousWithinAt R (Set.univ \ lattice B) 0)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by
    intro he
    exact hx.2 (he ▸ (periodGroup B).zero_mem)
  have hn := screenedDifference_eq_sub 0 α ha.le x hx0
  have hCoul : screened 0 x = 1/Real.sqrt (sq x) := by simp [screened, erfcIntegral_zero]
  rw [hCoul] at hn
  unfold R periodicGreen reciprocalPair
  rw [realSeries_split α ha B hB x]
  linarith

theorem periodicGreen_common_regular_limit (α β : ℝ) (ha : 0 < α) (hb : 0 < β)
    (B : Mat) (hB : B.det ≠ 0) :
    Filter.Tendsto (fun x => periodicGreen α B x - 1/Real.sqrt (sq x))
      (𝓝[Set.univ \ lattice B] (0 : Vec)) (𝓝 (ewaldRegularSelf β B)) := by
  rw [← ewaldRegularSelf_screening_independent α β B hB ha hb]
  exact periodicGreen_regular_limit α ha B hB

end BccSharp.Coulomb
