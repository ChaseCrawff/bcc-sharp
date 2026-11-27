import BccSharp.TwoSite.Montgomery
import BccSharp.Cover.OverlayArea
import BccSharp.Cover.OverlayPhysicalIdentity
import BccSharp.TwoSite.SeriesModes
import BccSharp.Cover.OverlayEnergyHeat

/-!
# Overlay: the triangular planar lower bound from Montgomery's theorem

For a chart `p` with `0 < p 0` and `0 < p 1`, the planar theta function
`planeTheta p s 0 0` is Montgomery's `θ(α; x, y)` at `α = p 0 * p 1 * s²`,
`x = p 2`, `y = p 1 / p 0` (`planeTheta_eq_theta2`). Montgomery's Theorem 1 compares it
pointwise with the unit-area triangular chart `hexChart`, and a change of variables
gives `triangleRegularized * √(cReal p) ≤ planarRegularized p`, the bound that
`triangularRelaxation` uses. The identification `planarRegularized hexChart =
triangleRegularized` splits the integral at `s = 1` and uses `plane_poisson` on `(0, 1]`.

The `_of` theorems take Montgomery's Theorem 1 as a hypothesis, so they show the one
property of the theta function the comparison uses. `planarRegularized_ge_triangle` and
`energy_fcc_lt_of_numeratorCheck` discharge it with `Montgomery.theorem1`.

Source: H. L. Montgomery, *Minimal theta functions*,
Glasgow Math. J. 30 (1988) 75–85, Theorem 1.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar

open BccSharp

/-! ### The unit-area triangular chart -/

/-- The unit-area triangular chart. `cReal hexChart = 1`, its planar norm is
`triangleQ · false` and its dual norm `κSq` is `triangleQ · true`. Coordinates 3–6 are
not used; `hexChart 7 = 1/2` lies in the seam range of `chart_energy_planar`. -/
noncomputable def hexChart : Chart :=
  ![Real.sqrt (2 / Real.sqrt 3), Real.sqrt (Real.sqrt 3 / 2), 1 / 2, 0, 0, 0, 0, 1 / 2]

private theorem sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem hexChart_zero : hexChart 0 = Real.sqrt (2 / Real.sqrt 3) := rfl
theorem hexChart_one : hexChart 1 = Real.sqrt (Real.sqrt 3 / 2) := rfl
theorem hexChart_two : hexChart 2 = 1 / 2 := rfl
theorem hexChart_seven : hexChart 7 = 1 / 2 := rfl

theorem hexChart_pos_zero : 0 < hexChart 0 := by
  rw [hexChart_zero]; exact Real.sqrt_pos.mpr (div_pos two_pos sqrt3_pos)

theorem hexChart_pos_one : 0 < hexChart 1 := by
  rw [hexChart_one]; exact Real.sqrt_pos.mpr (div_pos sqrt3_pos two_pos)

private theorem hexChart_sq_zero : hexChart 0 ^ 2 = 2 / Real.sqrt 3 := by
  rw [hexChart_zero]; exact Real.sq_sqrt (div_pos two_pos sqrt3_pos).le

private theorem hexChart_sq_one : hexChart 1 ^ 2 = Real.sqrt 3 / 2 := by
  rw [hexChart_one]; exact Real.sq_sqrt (div_pos sqrt3_pos two_pos).le

theorem hexChart_mul : hexChart 0 * hexChart 1 = 1 := by
  rw [hexChart_zero, hexChart_one, ← Real.sqrt_mul (div_pos two_pos sqrt3_pos).le,
    show 2 / Real.sqrt 3 * (Real.sqrt 3 / 2) = 1 by field_simp, Real.sqrt_one]

theorem cReal_hexChart : cReal hexChart = 1 := by
  rw [cReal, hexChart_mul, inv_one]

theorem hexChart_ratio : hexChart 1 / hexChart 0 = Real.sqrt 3 / 2 := by
  have h0 := hexChart_pos_zero
  have h1 := hexChart_pos_one
  have hsq : (hexChart 1 / hexChart 0) ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
    rw [div_pow, hexChart_sq_zero, hexChart_sq_one, div_pow, sqrt3_sq]
    field_simp
    nlinarith [sqrt3_sq]
  exact (pow_left_inj₀ (div_pos h1 h0).le (div_pos sqrt3_pos two_pos).le two_ne_zero).mp hsq

theorem planarNorm_hexChart (i j : ℤ) :
    planarNorm hexChart (i : ℝ) (j : ℝ) = triangleQ (i, j) false := by
  unfold planarNorm triangleQ triangleForm
  rw [mul_pow, mul_pow, hexChart_sq_zero, hexChart_sq_one, hexChart_two]
  simp only [Bool.false_eq_true, ↓reduceIte]
  push_cast
  field_simp
  nlinarith [sqrt3_sq]

theorem κSq_hexChart (m : Wave) : κSq hexChart m = triangleQ m true := by
  unfold κSq triangleQ triangleForm
  rw [mul_pow, mul_pow, inv_pow, inv_pow, hexChart_sq_zero, hexChart_sq_one, hexChart_two]
  simp only [↓reduceIte]
  push_cast
  field_simp
  nlinarith [sqrt3_sq]

/-! ### Montgomery's comparison, pointwise and integrated -/

/-- The chart's planar theta function is Montgomery's `θ(α; x, y)`. -/
theorem planeTheta_eq_theta2 (p : Chart) (hr : 0 < p 0) (ht : 0 < p 1) (s : ℝ) :
    planeTheta p s 0 0 = Montgomery.theta2 (p 0 * p 1 * s ^ 2) (p 2) (p 1 / p 0) := by
  have h0 := hr.ne'
  have h1 := ht.ne'
  unfold planeTheta Montgomery.theta2
  refine tsum_congr fun m => ?_
  unfold planeHeat planarNorm
  congr 1
  field_simp
  ring

theorem planeTheta_hexChart (u : ℝ) :
    planeTheta hexChart u 0 0 = Montgomery.thetaHex (u ^ 2) := by
  rw [planeTheta_eq_theta2 hexChart hexChart_pos_zero hexChart_pos_one, hexChart_mul, one_mul,
    hexChart_two, hexChart_ratio]
  rfl

theorem planeTheta_hex_le (hM : Montgomery.Theorem1) (p : Chart) (hr : 0 < p 0) (ht : 0 < p 1)
    (s : ℝ) (hs : 0 < s) :
    planeTheta hexChart (Real.sqrt (p 0 * p 1) * s) 0 0 ≤ planeTheta p s 0 0 := by
  have ha : 0 < p 0 * p 1 := mul_pos hr ht
  rw [planeTheta_hexChart, planeTheta_eq_theta2 p hr ht, mul_pow, Real.sq_sqrt ha.le]
  exact hM _ (by positivity) _ _ (div_pos ht hr)

theorem planarRegularHeat_hex_le (hM : Montgomery.Theorem1) (p : Chart) (hr : 0 < p 0)
    (ht : 0 < p 1) (s : ℝ) (hs : 0 < s) :
    planarRegularHeat hexChart (Real.sqrt (p 0 * p 1) * s) ≤ planarRegularHeat p s := by
  have ha : 0 < p 0 * p 1 := mul_pos hr ht
  have h := planeTheta_hex_le hM p hr ht s hs
  unfold planarRegularHeat
  rw [cReal_hexChart, cReal, mul_pow, Real.sq_sqrt ha.le, one_mul, mul_inv]
  linarith

theorem planarRegularHeat_update (p : Chart) (v : ℝ) :
    planarRegularHeat (Function.update p 7 v) = planarRegularHeat p := by
  funext s
  simp [planarRegularHeat, planeTheta, planeHeat, planarNorm, cReal]

theorem planarRegularHeat_integrable (p : Chart) (hr : 0 < p 0) (ht : 0 < p 1) :
    IntegrableOn (planarRegularHeat p) (Ioi 0) := by
  have h := (chart_energy_planar (Function.update p 7 (1 / 2))
    (by simpa [Function.update_apply] using hr) (by simpa [Function.update_apply] using ht)
    (by norm_num [Function.update_apply]) (by norm_num [Function.update_apply])).1
  rwa [planarRegularHeat_update] at h

/-- Montgomery's theorem, integrated: the scaled triangular integral is a lower bound. -/
theorem planarRegularized_ge_scaled (hM : Montgomery.Theorem1) (p : Chart) (hr : 0 < p 0)
    (ht : 0 < p 1) :
    Real.sqrt (cReal p) * planarRegularized hexChart ≤ planarRegularized p := by
  set b := Real.sqrt (p 0 * p 1) with hb
  have hbpos : 0 < b := Real.sqrt_pos.mpr (mul_pos hr ht)
  have hint := planarRegularHeat_integrable hexChart hexChart_pos_zero hexChart_pos_one
  have hint' : IntegrableOn (fun s => planarRegularHeat hexChart (b * s)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff _ _ hbpos, mul_zero]
    exact hint
  have hcv : ∫ s in Ioi (0:ℝ), planarRegularHeat hexChart (b * s) =
      b⁻¹ * planarRegularized hexChart := by
    rw [integral_comp_mul_left_Ioi _ _ hbpos, mul_zero, smul_eq_mul]
    rfl
  have hsqrt : Real.sqrt (cReal p) = b⁻¹ := by rw [cReal, Real.sqrt_inv]
  rw [hsqrt, ← hcv]
  exact setIntegral_mono_on hint' (planarRegularHeat_integrable p hr ht) measurableSet_Ioi
    (fun s hs => planarRegularHeat_hex_le hM p hr ht s hs)

/-! ### The triangular integral equals `triangleRegularized`

`kernel_half_eq`, `triangleQ_dominates'`, `normSq_ge_one` and the bound in
`triangleKernel_summable` repeat private lemmas of `BccSharp.Cover.OverlayArea` (`kernel_half`,
`triangleQ_dominates` and the body of `triangleTermAll_summable`), which are not visible
outside that module. -/

private theorem kernel_half_eq (x : ℝ) :
    BravaisCover.kernelValue .half x = gKernel (1/2) x := by
  norm_num [BravaisCover.kernelValue, BravaisCover.KernelKind.power]

/-- `0 ≤ gKernel (1/2) t ≤ e^{-t}/t` for `t > 0`. -/
theorem gKernel_half_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ gKernel (1/2) t ∧ gKernel (1/2) t ≤ Real.exp (-t) / t := by
  have h := BravaisCover.kernelValue_positive_bound .half ht
  rw [kernel_half_eq] at h
  exact h

private theorem triangleQ_dominates' (m : Wave) (d : Bool) :
    LatticeTails.normSq (m.1, m.2, 0) ≤ Real.pi * triangleQ m d := by
  have f : (m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2 ≤ 2 * (triangleForm m d : ℝ) := by
    cases d <;> simp [triangleForm] <;> nlinarith only [
      sq_nonneg ((m.1 : ℝ) + (m.2 : ℝ)), sq_nonneg ((m.1 : ℝ) - (m.2 : ℝ))]
  have nn : 0 ≤ (triangleForm m d : ℝ) := by
    nlinarith only [f, sq_nonneg (m.1 : ℝ), sq_nonneg (m.2 : ℝ)]
  have hs₁ : Real.sqrt 3 ≤ 2 :=
    (sq_le_sq₀ sqrt3_pos.le (by norm_num)).mp (by rw [sqrt3_sq]; norm_num)
  have co : 2 ≤ 2 * Real.pi / Real.sqrt 3 :=
    (le_div_iff₀ sqrt3_pos).mpr (by linarith [Real.pi_gt_three])
  calc
    _ = (m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2 := by norm_num [LatticeTails.normSq]
    _ ≤ 2 * (triangleForm m d : ℝ) := f
    _ ≤ (2 * Real.pi / Real.sqrt 3) * (triangleForm m d : ℝ) := mul_le_mul_of_nonneg_right co nn
    _ = _ := by unfold triangleQ; ring

private theorem normSq_ge_one (m : Wave) (hz : m ≠ 0) :
    (1:ℝ) ≤ LatticeTails.normSq (m.1, m.2, 0) := by
  have len : 1 ≤ LatticeTails.length (m.1, m.2, 0) := by
    by_contra! hbad
    simp only [LatticeTails.length, Int.natAbs_zero, add_zero] at hbad
    have e : m.1.natAbs + m.2.natAbs = 0 := by omega
    obtain ⟨e₁, e₂⟩ := Nat.add_eq_zero_iff.mp e
    exact hz (Prod.ext (Int.natAbs_eq_zero.mp e₁) (Int.natAbs_eq_zero.mp e₂))
  rw [LatticeTails.normSq_eq_square]
  exact_mod_cast len.trans (LatticeTails.length_le_square (m.1, m.2, 0))

/-- Each triangular `gKernel` family is summable. -/
theorem triangleKernel_summable (d : Bool) :
    Summable (fun m : Wave => if m = 0 then 0 else gKernel (1/2) (Real.pi * triangleQ m d)) := by
  have g := LatticeTails.hasSum_integer_geometric.summable
  have h := g.mul_of_nonneg g (fun _ => by positivity) (fun _ => by positivity)
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) h
  · split_ifs with hz
    · exact le_rfl
    · exact (gKernel_half_bounds (mul_pos Real.pi_pos (triangleQ_pos m d hz))).1
  · split_ifs with hz
    · positivity
    · have t := (normSq_ge_one m hz).trans (triangleQ_dominates' m d)
      have b := (gKernel_half_bounds (zero_lt_one.trans_le t)).2
      calc gKernel (1/2) (Real.pi * triangleQ m d)
          ≤ Real.exp (-(Real.pi * triangleQ m d)) / (Real.pi * triangleQ m d) := b
        _ ≤ Real.exp (-(Real.pi * triangleQ m d)) := div_le_self (Real.exp_pos _).le t
        _ ≤ Real.exp (-LatticeTails.normSq (m.1, m.2, 0)) :=
            Real.exp_le_exp.mpr (neg_le_neg (triangleQ_dominates' m d))
        _ ≤ LatticeTails.weight (m.1, m.2, 0) := LatticeTails.gaussian_le_weight _
        _ = (1/2:ℝ) ^ m.1.natAbs * (1/2:ℝ) ^ m.2.natAbs := by
            simp [LatticeTails.weight, LatticeTails.length, pow_add]

private theorem triangleQ_zero (d : Bool) : triangleQ (0 : Wave) d = 0 := by
  cases d <;> simp [triangleQ, triangleForm]

private theorem hex_heat (s : ℝ) (m : Wave) :
    planeHeat hexChart s 0 0 m = Real.exp (-(Real.pi * triangleQ m false) * s ^ 2) := by
  obtain ⟨i, j⟩ := m
  simp only [planeHeat, add_zero]
  rw [planarNorm_hexChart]
  ring_nf

private theorem hex_dual (u : ℝ) (m : Wave) :
    planeDualTerm hexChart u 0 0 m = Real.exp (-(Real.pi * triangleQ m true) * u ^ 2) := by
  simp only [planeDualTerm, mul_zero, add_zero, Real.cos_zero, mul_one]
  rw [κSq_hexChart]
  ring_nf

/-- For `s > 0`: `planarRegularHeat hexChart s = Σ_{m ≠ 0} 2 e^{-πQ_m s²} - 2/s²`. -/
private theorem hex_large (s : ℝ) (hs : 0 < s) :
    planarRegularHeat hexChart s =
      (∑' m : Wave, if m = 0 then 0 else 2 * Real.exp (-(Real.pi * triangleQ m false) * s ^ 2))
        - 2 * (s ^ 2)⁻¹ := by
  have hsum := planeHeat_summable hexChart hexChart_pos_zero.ne' hexChart_pos_one.ne' s hs 0 0
  obtain ⟨-, e⟩ := sum_at_zero _ hsum
  have hz : planeHeat hexChart s 0 0 0 = 1 := by
    rw [hex_heat, triangleQ_zero]; simp
  have hr : (∑' m : Wave, if m = 0 then 0 else
        2 * Real.exp (-(Real.pi * triangleQ m false) * s ^ 2)) =
      2 * ∑' m : Wave, if m = 0 then 0 else planeHeat hexChart s 0 0 m := by
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    split_ifs <;> simp [hex_heat]
  unfold planarRegularHeat planeTheta
  rw [e, hz, cReal_hexChart, hr]
  ring

/-- For `s > 0`: `planarRegularHeat hexChart s = Σ_{m ≠ 0} 2 s⁻² e^{-πQ*_m s⁻²} - 2`. -/
private theorem hex_small (s : ℝ) (hs : 0 < s) :
    planarRegularHeat hexChart s =
      (∑' m : Wave, if m = 0 then 0 else
          2 * (s ^ 2)⁻¹ * Real.exp (-(Real.pi * triangleQ m true) * (s⁻¹) ^ 2)) - 2 := by
  have hsum := planeDual_summable hexChart hexChart_pos_zero.ne' hexChart_pos_one.ne' s⁻¹
    (inv_pos.mpr hs) 0 0
  obtain ⟨-, e⟩ := sum_at_zero _ hsum
  have hz : planeDualTerm hexChart s⁻¹ 0 0 0 = 1 := by
    rw [hex_dual, triangleQ_zero]; simp
  have hr : (∑' m : Wave, if m = 0 then 0 else
        2 * (s ^ 2)⁻¹ * Real.exp (-(Real.pi * triangleQ m true) * (s⁻¹) ^ 2)) =
      2 * (s ^ 2)⁻¹ * ∑' m : Wave, if m = 0 then 0 else planeDualTerm hexChart s⁻¹ 0 0 m := by
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    split_ifs <;> simp [hex_dual]
  unfold planarRegularHeat
  rw [plane_poisson hexChart hexChart_pos_zero hexChart_pos_one s hs 0 0, cReal_hexChart]
  unfold planeDual
  rw [e, hz, hr]
  ring

/-- `∫_{s>1} 2 e^{-t s²} ds = gKernel (1/2) t`. -/
private theorem large_kernel {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => 2 * Real.exp (-t * s ^ 2)) (Ioi 1) ∧
    ∫ s in Ioi (1:ℝ), 2 * Real.exp (-t * s ^ 2) = gKernel (1/2) t := by
  refine ⟨((integrable_exp_neg_mul_sq ht).const_mul 2).integrableOn, ?_⟩
  rw [integral_const_mul, gKernel_half]

/-- `∫_{0<s≤1} 2 s⁻² e^{-t s⁻²} ds = gKernel (1/2) t`, by the substitution `s ↦ s⁻¹`. -/
private theorem small_kernel_eq {t : ℝ} (_ht : 0 < t) :
    ∫ s in Ioc (0:ℝ) 1, 2 * (s ^ 2)⁻¹ * Real.exp (-t * (s⁻¹) ^ 2) = gKernel (1/2) t := by
  set g : ℝ → ℝ := (Ioi (1:ℝ)).indicator (fun y => 2 * Real.exp (-t * y ^ 2)) with hg
  have key := integral_comp_rpow_Ioi g (p := (-1:ℝ)) (by norm_num)
  have hR : ∫ y in Ioi (0:ℝ), g y = gKernel (1/2) t := by
    rw [hg, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one), integral_const_mul, gKernel_half]
  have hL : ∫ x in Ioi (0:ℝ), (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) • g (x ^ (-1:ℝ)) =
      ∫ x in Ioo (0:ℝ) 1, 2 * (x ^ 2)⁻¹ * Real.exp (-t * (x⁻¹) ^ 2) := by
    rw [← Set.Ioi_inter_Iio, ← setIntegral_indicator measurableSet_Iio]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := hx
    simp only [hg, Set.indicator, Set.mem_Ioi, Set.mem_Iio, smul_eq_mul]
    rw [Real.rpow_neg_one, show (-1:ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx0.le,
      Real.rpow_two]
    by_cases h1 : x < 1
    · simp only [(one_lt_inv₀ hx0).mpr h1, h1, ↓reduceIte]
      norm_num
      ring
    · have h2 : ¬ 1 < x⁻¹ := by rwa [one_lt_inv₀ hx0]
      simp only [h2, h1, ↓reduceIte, mul_zero]
  rw [← setIntegral_congr_set Ioo_ae_eq_Ioc, ← hL, key, hR]

private theorem small_kernel_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => 2 * (s ^ 2)⁻¹ * Real.exp (-t * (s⁻¹) ^ 2)) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2 / t) (by simp [Real.volume_Ioc])
    (by fun_prop) (ae_of_all _ fun s => ?_)
  have hu : 0 ≤ (s ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg s)
  have hexp : t * (s ^ 2)⁻¹ * Real.exp (-t * (s ^ 2)⁻¹) ≤ 1 := by
    have := Real.add_one_le_exp (t * (s ^ 2)⁻¹)
    have hpos := Real.exp_pos (t * (s ^ 2)⁻¹)
    rw [show -t * (s ^ 2)⁻¹ = -(t * (s ^ 2)⁻¹) by ring, Real.exp_neg]
    rw [mul_inv_le_iff₀ hpos]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow]
  rw [le_div_iff₀ ht]
  nlinarith [hexp, Real.exp_pos (-t * (s ^ 2)⁻¹)]

private theorem inv_sq_integral :
    IntegrableOn (fun s : ℝ => 2 * (s ^ 2)⁻¹) (Ioi 1) ∧
    ∫ s in Ioi (1:ℝ), 2 * (s ^ 2)⁻¹ = 2 := by
  have e : EqOn (fun s : ℝ => 2 * (s ^ 2)⁻¹) (fun s => 2 * s ^ (-2:ℝ)) (Ioi 1) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := zero_le_one.trans (le_of_lt hs)
    simp only
    rw [Real.rpow_neg hs0, Real.rpow_two]
  have hi : IntegrableOn (fun s : ℝ => 2 * s ^ (-2:ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) zero_lt_one).const_mul 2
  refine ⟨hi.congr_fun e.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) zero_lt_one]
  norm_num

private theorem large_part :
    IntegrableOn (planarRegularHeat hexChart) (Ioi 1) ∧
    ∫ s in Ioi (1:ℝ), planarRegularHeat hexChart s =
      (∑' m : Wave, if m = 0 then 0 else gKernel (1/2) (Real.pi * triangleQ m false)) - 2 := by
  let f : Wave → ℝ → ℝ := fun m s =>
    if m = 0 then 0 else 2 * Real.exp (-(Real.pi * triangleQ m false) * s ^ 2)
  have hi : ∀ m, IntegrableOn (f m) (Ioi 1) := by
    intro m
    by_cases hz : m = 0
    · simp [f, hz]
    · simpa [f, hz] using (large_kernel (mul_pos Real.pi_pos (triangleQ_pos m false hz))).1
  have hint : ∀ m, ∫ s in Ioi (1:ℝ), f m s =
      if m = 0 then 0 else gKernel (1/2) (Real.pi * triangleQ m false) := by
    intro m
    by_cases hz : m = 0
    · simp [f, hz]
    · simpa [f, hz] using (large_kernel (mul_pos Real.pi_pos (triangleQ_pos m false hz))).2
  have hnorm : ∀ m, ∫ s in Ioi (1:ℝ), ‖f m s‖ = ∫ s in Ioi (1:ℝ), f m s := by
    intro m
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    simp only [f]
    split_ifs
    · simp
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hs : Summable (fun m => ∫ s in Ioi (1:ℝ), ‖f m s‖) := by
    simp_rw [hnorm, hint]
    exact triangleKernel_summable false
  obtain ⟨hI, hE⟩ := integrateSeries f hi hs
  obtain ⟨hpI, hpE⟩ := inv_sq_integral
  have heq : EqOn (planarRegularHeat hexChart) (fun s => (∑' m, f m s) - 2 * (s ^ 2)⁻¹) (Ioi 1) :=
    fun s hs => hex_large s (zero_lt_one.trans hs)
  refine ⟨(hI.sub hpI).congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hI hpI, hE, hpE,
    tsum_congr hint]

private theorem small_part :
    IntegrableOn (planarRegularHeat hexChart) (Ioc 0 1) ∧
    ∫ s in Ioc (0:ℝ) 1, planarRegularHeat hexChart s =
      (∑' m : Wave, if m = 0 then 0 else gKernel (1/2) (Real.pi * triangleQ m true)) - 2 := by
  let f : Wave → ℝ → ℝ := fun m s =>
    if m = 0 then 0 else 2 * (s ^ 2)⁻¹ * Real.exp (-(Real.pi * triangleQ m true) * (s⁻¹) ^ 2)
  have hi : ∀ m, IntegrableOn (f m) (Ioc 0 1) := by
    intro m
    by_cases hz : m = 0
    · simp [f, hz]
    · simpa [f, hz] using small_kernel_integrable (mul_pos Real.pi_pos (triangleQ_pos m true hz))
  have hint : ∀ m, ∫ s in Ioc (0:ℝ) 1, f m s =
      if m = 0 then 0 else gKernel (1/2) (Real.pi * triangleQ m true) := by
    intro m
    by_cases hz : m = 0
    · simp [f, hz]
    · simpa [f, hz] using small_kernel_eq (mul_pos Real.pi_pos (triangleQ_pos m true hz))
  have hnorm : ∀ m, ∫ s in Ioc (0:ℝ) 1, ‖f m s‖ = ∫ s in Ioc (0:ℝ) 1, f m s := by
    intro m
    refine setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
    simp only [f]
    split_ifs
    · simp
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : Summable (fun m => ∫ s in Ioc (0:ℝ) 1, ‖f m s‖) := by
    simp_rw [hnorm, hint]
    exact triangleKernel_summable true
  obtain ⟨hI, hE⟩ := integrateSeries f hi hs
  have hc : IntegrableOn (fun _ : ℝ => (2:ℝ)) (Ioc 0 1) := by
    refine integrableOn_const ?_
    simp [Real.volume_Ioc]
  have heq : EqOn (planarRegularHeat hexChart) (fun s => (∑' m, f m s) - 2) (Ioc 0 1) :=
    fun s hs => hex_small s hs.1
  refine ⟨(hI.sub hc).congr_fun heq.symm measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_sub hI hc, hE, tsum_congr hint,
    setIntegral_const]
  simp

/-- The unit-area triangular regularized integral is `triangleRegularized`. -/
theorem planarRegularized_hexChart : planarRegularized hexChart = triangleRegularized := by
  obtain ⟨hIs, hEs⟩ := small_part
  obtain ⟨hIl, hEl⟩ := large_part
  have hsplit : ∀ m : Wave, triangleTermAll m =
      (if m = 0 then 0 else gKernel (1/2) (Real.pi * triangleQ m false)) +
        (if m = 0 then 0 else gKernel (1/2) (Real.pi * triangleQ m true)) := by
    intro m
    unfold triangleTermAll triangleValue
    by_cases hz : m = 0
    · simp [hz, Prod.mk_zero_zero]
    · have hz' : m ≠ (0, 0) := hz
      simp [hz, hz']
  unfold planarRegularized triangleRegularized
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIs hIl, hEs, hEl,
    tsum_congr hsplit, (triangleKernel_summable false).tsum_add (triangleKernel_summable true)]
  ring

/-! ### The Overlay comparison and the strict FCC leaf, given Montgomery's theorem -/

/-- Given Montgomery's Theorem 1: `triangleRegularized * √(cReal p) ≤ planarRegularized p`. -/
theorem planarRegularized_ge_triangle_of (hM : Montgomery.Theorem1) (p : Chart)
    (hr : 0 < p 0) (ht : 0 < p 1) :
    triangleRegularized * Real.sqrt (cReal p) ≤ planarRegularized p := by
  rw [← planarRegularized_hexChart, mul_comm]
  exact planarRegularized_ge_scaled hM p hr ht

open BccSharp.Coverage BravaisCover DirectRoute in
/-- Given Montgomery's Theorem 1, a successful Overlay numerator check is a strict FCC leaf. -/
theorem energy_fcc_lt_of_numeratorCheck_of (hM : Montgomery.Theorem1) {raw : Cell} {p : Chart}
    (hp : raw.Mem p) (cube : ℕ) (ok : numeratorCheck raw cube = true)
    (hs : cubeRootCheck scaleWitness scaleInput = true)
    (strict : fccHUpper - 4 < numeratorLower raw cube) :
    energy fcc < energy (chartPoint p) := by
  have h1 := triangularRelaxation_aboveFCC hp cube ok hs strict
  have layer : layerCheck raw cube = true := (Bool.and_eq_true_iff.mp ok).2
  have h2 := addressed_energy_planar hp cube layer
  let q := seamPoint raw p
  let B := seamCell raw
  have hm : B.Mem q := seamPoint_mem hp
  have c := (Bool.and_eq_true_iff.mp layer).1
  simp only [retainedCheck, Bool.and_eq_true] at c
  have h := diagonalsCheck_sound c.1.1
  have r : 0 < q 0 := (show (0:ℝ) < (coord B 0).lo by exact_mod_cast h.1).trans_le
    (endpoints (coord_sound hm 0)).1
  have t : 0 < q 1 := (show (0:ℝ) < (coord B 1).lo by exact_mod_cast h.2.1).trans_le
    (endpoints (coord_sound hm 1)).1
  have h3 := planarRegularized_ge_triangle_of hM q r t
  have hac := ac_positive
  unfold triangularRelaxation at h1
  have h4 : 2 * ac * energy fcc < 2 * ac * energy (chartPoint p) := by linarith
  exact lt_of_mul_lt_mul_left h4 (by positivity)

/-! ### Unconditional forms -/

/-- The Overlay comparison: `triangleRegularized * √(cReal p) ≤ planarRegularized p`. -/
theorem planarRegularized_ge_triangle (p : Chart) (hr : 0 < p 0) (ht : 0 < p 1) :
    triangleRegularized * Real.sqrt (cReal p) ≤ planarRegularized p :=
  planarRegularized_ge_triangle_of Montgomery.theorem1 p hr ht

open BccSharp.Coverage BravaisCover DirectRoute in
/-- A successful Overlay numerator check whose lower endpoint clears `fccHUpper - 4` is a strict
FCC leaf: `energy fcc < energy (chartPoint p)` at every point of the cell. -/
theorem energy_fcc_lt_of_numeratorCheck {raw : Cell} {p : Chart}
    (hp : raw.Mem p) (cube : ℕ) (ok : numeratorCheck raw cube = true)
    (hs : cubeRootCheck scaleWitness scaleInput = true)
    (strict : fccHUpper - 4 < numeratorLower raw cube) :
    energy fcc < energy (chartPoint p) :=
  energy_fcc_lt_of_numeratorCheck_of Montgomery.theorem1 hp cube ok hs strict

end BccSharp.Coulomb.CompactCover.OverlayPlanar
