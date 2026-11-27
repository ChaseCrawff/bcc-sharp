import BccSharp.Lattice.KernelJet
import BccSharp.TwoSite.SeriesModes
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

/-! Log-convex supports of the two Series kernels, and Jensen's inequality for the
exponential. These are the analytic facts behind the Adaptive log-convex support routes
(`T`, `J`, `U`, `Z`, `R`, `K`, `I`).

* `logTangent`: for either kernel `g = kernelValue k` and any anchor `T > 0`,
  `g T · exp(-(t - T) · W / g T) ≤ g t` for every `t > 0`, where
  `W = (e^{-T} + a g T) / T = -g'(T)` (`a = 1/2` or `1`). This is the tangent line of
  `log g` at `T`. For the half kernel it follows from the integral
  `g t = 2 ∫_{s>1} e^{-t s²}` and `1 + z ≤ e^z` (the proof of Jensen's inequality for
  the probability measure `e^{-T s²} ds / ∫ e^{-T s²}`), with the moment identity
  `∫_{s>1} s² e^{-T s²} = (e^{-T} + ∫_{s>1} e^{-T s²}) / (2T)` (integration by parts).
  For the reciprocal kernel `g t = e^{-t}/t` it is `log x ≤ x - 1`.
* `jensen_exp`: `C · exp((Σ cᵢ xᵢ)/C) ≤ Σ cᵢ exp xᵢ` for weights `cᵢ ≥ 0` with sum
  `C > 0`.
* `kexp_lower`: a lower bound of `K exp(S/K)` from `K ∈ [Klo, Khi]`, `0 < Klo`, and
  `Slo ≤ S`. -/

noncomputable section
open MeasureTheory Set Real Filter Topology

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BravaisCover

/-! ### The half kernel -/

theorem half_integrableOn {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => exp (-T * s ^ 2)) (Ioi 1) :=
  (integrable_exp_neg_mul_sq hT).integrableOn

theorem half_moment_integrableOn {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => s ^ 2 * exp (-T * s ^ 2)) (Ioi 1) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq hT (s := 2) (by norm_num)).integrableOn
    (s := Ioi (1:ℝ))
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- `x e^{-T x²} → 0` at infinity. -/
theorem tendsto_mul_exp_neg_sq {T : ℝ} (hT : 0 < T) :
    Tendsto (fun x : ℝ => x * exp (-T * x ^ 2)) atTop (𝓝 0) := by
  have base : Tendsto (fun x : ℝ => (T * x) ^ 1 * exp (-(T * x))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop hT)
  have scaled : Tendsto (fun x : ℝ => T⁻¹ * ((T * x) ^ 1 * exp (-(T * x)))) atTop (𝓝 0) := by
    simpa using base.const_mul T⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds scaled ?_ ?_
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hx0 : (0:ℝ) ≤ x := zero_le_one.trans hx
    have hsq : x ≤ x ^ 2 := by nlinarith
    have he : exp (-T * x ^ 2) ≤ exp (-(T * x)) :=
      exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hsq hT.le])
    calc x * exp (-T * x ^ 2) ≤ x * exp (-(T * x)) := mul_le_mul_of_nonneg_left he hx0
      _ = T⁻¹ * ((T * x) ^ 1 * exp (-(T * x))) := by field_simp

/-- The second moment of the half kernel's Gaussian. -/
theorem half_moment_eq {T : ℝ} (hT : 0 < T) :
    (∫ s in Ioi (1:ℝ), s ^ 2 * exp (-T * s ^ 2)) =
      (exp (-T) + ∫ s in Ioi (1:ℝ), exp (-T * s ^ 2)) / (2 * T) := by
  let u : ℝ → ℝ := fun x => x
  let u' : ℝ → ℝ := fun _ => 1
  let v : ℝ → ℝ := fun x => -exp (-T * x ^ 2) / (2 * T)
  let v' : ℝ → ℝ := fun x => x * exp (-T * x ^ 2)
  have hu : ∀ x ∈ Ioi (1:ℝ), HasDerivAt u (u' x) x := fun x _ => hasDerivAt_id x
  have hv : ∀ x ∈ Ioi (1:ℝ), HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -T * y ^ 2) (-T * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-T))
    have h2 := (h1.exp.neg).div_const (2 * T)
    convert h2 using 1
    simp only [v']
    field_simp
  have huv' : IntegrableOn (u * v') (Ioi (1:ℝ)) := by
    refine IntegrableOn.congr_fun (half_moment_integrableOn hT) (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, u, v']
    ring
  have hu'v : IntegrableOn (u' * v) (Ioi (1:ℝ)) := by
    have h : IntegrableOn (fun x : ℝ => -(exp (-T * x ^ 2) / (2 * T))) (Ioi (1:ℝ)) :=
      ((half_integrableOn hT).div_const (2 * T)).neg
    refine IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, u', v]
    ring
  have h_zero : Tendsto (u * v) (𝓝[>] (1:ℝ)) (𝓝 (1 * (-exp (-T * 1 ^ 2) / (2 * T)))) := by
    have c : Continuous (u * v) := by
      simp only [u, v]
      fun_prop
    exact (c.tendsto 1).mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have h := (tendsto_mul_exp_neg_sq hT).const_mul (-(1 / (2 * T)))
    simp only [mul_zero] at h
    refine h.congr (fun x => ?_)
    simp only [Pi.mul_apply, u, v]
    ring
  have ibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  have lhs : (∫ x in Ioi (1:ℝ), u x * v' x) = ∫ s in Ioi (1:ℝ), s ^ 2 * exp (-T * s ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [u, v']
    ring
  have rhs : (∫ x in Ioi (1:ℝ), u' x * v x) = -((∫ s in Ioi (1:ℝ), exp (-T * s ^ 2)) / (2 * T)) := by
    rw [← integral_div, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [u', v]
    ring
  rw [lhs, rhs] at ibp
  rw [ibp]
  simp only [one_pow, mul_one, one_mul]
  field_simp
  ring

/-- **Log-convex tangent of the half kernel.** -/
theorem half_logTangent {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    gKernel (1/2) T * exp (-(t - T) * ((exp (-T) + gKernel (1/2) T / 2) / (T * gKernel (1/2) T))) ≤
      gKernel (1/2) t := by
  set I := ∫ s in Ioi (1:ℝ), exp (-T * s ^ 2) with hI
  set J := ∫ s in Ioi (1:ℝ), s ^ 2 * exp (-T * s ^ 2) with hJ
  have gT : gKernel (1/2) T = 2 * I := by rw [gKernel_half]
  have gt : gKernel (1/2) t = 2 * ∫ s in Ioi (1:ℝ), exp (-t * s ^ 2) := gKernel_half t
  have I0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi (fun _ _ => (exp_pos _).le)
  have gt0 : 0 ≤ gKernel (1/2) t := by
    rw [gt]
    exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi (fun _ _ => (exp_pos _).le))
  rcases I0.eq_or_lt with Iz | Ipos
  · rw [gT, ← Iz]
    simpa using gt0
  -- The rate `v = J / I`.
  have Jeq : J = (exp (-T) + I) / (2 * T) := half_moment_eq hT
  set v := J / I with hv
  have rate : (exp (-T) + gKernel (1/2) T / 2) / (T * gKernel (1/2) T) = v := by
    rw [hv, Jeq, gT]
    field_simp
  rw [rate]
  set c := exp (-(t - T) * v) with hc
  set d := t - T with hd
  have c0 : 0 ≤ c := (exp_pos _).le
  -- Pointwise lower bound from `1 + z ≤ e^z`.
  have point : ∀ s ∈ Ioi (1:ℝ),
      c * (exp (-T * s ^ 2) - d * (s ^ 2 * exp (-T * s ^ 2) - v * exp (-T * s ^ 2))) ≤
        exp (-t * s ^ 2) := by
    intro s _
    have split : exp (-t * s ^ 2) = exp (-T * s ^ 2) * (c * exp (-d * (s ^ 2 - v))) := by
      rw [hc, ← exp_add, ← exp_add]
      congr 1
      rw [hd]
      ring
    have one := add_one_le_exp (-d * (s ^ 2 - v))
    have e0 : 0 ≤ exp (-T * s ^ 2) := (exp_pos _).le
    rw [split]
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left one c0) e0
    calc c * (exp (-T * s ^ 2) - d * (s ^ 2 * exp (-T * s ^ 2) - v * exp (-T * s ^ 2)))
        = exp (-T * s ^ 2) * (c * (-d * (s ^ 2 - v) + 1)) := by ring
      _ ≤ _ := h
  have intLow : IntegrableOn
      (fun s : ℝ => c * (exp (-T * s ^ 2) - d * (s ^ 2 * exp (-T * s ^ 2) - v * exp (-T * s ^ 2))))
      (Ioi 1) := by
    have a := half_integrableOn hT
    have b := half_moment_integrableOn hT
    exact (a.sub ((b.sub (a.const_mul v)).const_mul d)).const_mul c
  have intHigh : IntegrableOn (fun s : ℝ => exp (-t * s ^ 2)) (Ioi 1) := half_integrableOn ht
  have mono := setIntegral_mono_on intLow intHigh measurableSet_Ioi point
  have value : (∫ s in Ioi (1:ℝ),
      c * (exp (-T * s ^ 2) - d * (s ^ 2 * exp (-T * s ^ 2) - v * exp (-T * s ^ 2)))) = c * I := by
    have a := half_integrableOn hT
    have b := half_moment_integrableOn hT
    have shape : (∫ s in Ioi (1:ℝ),
        c * (exp (-T * s ^ 2) - d * (s ^ 2 * exp (-T * s ^ 2) - v * exp (-T * s ^ 2)))) =
        ∫ s in Ioi (1:ℝ), ((c * (1 + d * v)) * exp (-T * s ^ 2) - (c * d) * (s ^ 2 * exp (-T * s ^ 2))) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
      ring
    rw [shape, integral_sub (a.const_mul _) (b.const_mul _), integral_const_mul, integral_const_mul,
      ← hI, ← hJ]
    have vI : v * I = J := by rw [hv]; field_simp
    calc c * (1 + d * v) * I - c * d * J = c * I + c * d * (v * I - J) := by ring
      _ = c * I := by rw [vI]; ring
  rw [value] at mono
  rw [gT, gt]
  nlinarith [mono]

/-! ### The reciprocal kernel -/

theorem one_logTangent {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    gKernel 1 T * exp (-(t - T) * ((exp (-T) + gKernel 1 T) / (T * gKernel 1 T))) ≤ gKernel 1 t := by
  rw [gKernel_one hT, gKernel_one ht]
  have eT := exp_pos (-T)
  have rate : (exp (-T) + exp (-T) / T) / (T * (exp (-T) / T)) = 1 + 1 / T := by
    field_simp
  rw [rate]
  -- With `x = t / T`: `x ≤ e^{x-1}`, so `e^{-(x-1)} ≤ T / t`.
  have key : t / T ≤ exp (t / T - 1) := by
    have h := add_one_le_exp (t / T - 1)
    linarith
  have hx : 0 < t / T := div_pos ht hT
  have inv : exp (-(t / T - 1)) ≤ T / t := by
    rw [exp_neg, inv_le_comm₀ (exp_pos _) (div_pos hT ht), inv_div]
    exact key
  have arg : -T + -(t - T) * (1 + 1 / T) = -t + -(t / T - 1) := by
    field_simp
    ring
  have expand : exp (-T) / T * exp (-(t - T) * (1 + 1 / T)) = exp (-t) / T * exp (-(t / T - 1)) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← exp_add, ← exp_add, arg]
  rw [expand]
  calc exp (-t) / T * exp (-(t / T - 1)) ≤ exp (-t) / T * (T / t) :=
        mul_le_mul_of_nonneg_left inv (by positivity)
    _ = exp (-t) / t := by field_simp

/-! ### Both kernels -/

/-- **Log-convex tangent.** `W = (e^{-T} + a g T)/T` is `-g'(T)` (`kernelSlope`). -/
theorem logTangent (k : KernelKind) {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    kernelValue k T *
        exp (-(t - T) * ((exp (-T) + (k.power : ℝ) * kernelValue k T) / (T * kernelValue k T))) ≤
      kernelValue k t := by
  cases k with
  | half =>
    have e : ((KernelKind.half.power : ℚ) : ℝ) = 1 / 2 := by norm_num [KernelKind.power]
    simp only [kernelValue, e]
    rw [show (1:ℝ) / 2 * gKernel (1 / 2) T = gKernel (1 / 2) T / 2 by ring]
    exact half_logTangent hT ht
  | one =>
    have e : ((KernelKind.one.power : ℚ) : ℝ) = 1 := by norm_num [KernelKind.power]
    simp only [kernelValue, e, one_mul]
    exact one_logTangent hT ht

/-! ### Jensen's inequality for the exponential -/

theorem jensen_exp {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (c0 : ∀ i ∈ s, 0 ≤ c i)
    (C0 : 0 < ∑ i ∈ s, c i) :
    (∑ i ∈ s, c i) * exp ((∑ i ∈ s, c i * x i) / ∑ i ∈ s, c i) ≤ ∑ i ∈ s, c i * exp (x i) := by
  set C := ∑ i ∈ s, c i with hC
  set X := ∑ i ∈ s, c i * x i with hX
  set m := X / C with hm
  have term : ∀ i ∈ s, c i * (exp m * (x i - m + 1)) ≤ c i * exp (x i) := by
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (c0 i hi)
    have h := add_one_le_exp (x i - m)
    have e := exp_pos m
    calc exp m * (x i - m + 1) ≤ exp m * exp (x i - m) := mul_le_mul_of_nonneg_left h e.le
      _ = exp (x i) := by rw [← exp_add]; ring_nf
  have total := Finset.sum_le_sum term
  have pointwise : ∀ i ∈ s, c i * (exp m * (x i - m + 1)) =
      exp m * (c i * x i) + (exp m * (1 - m)) * c i := by
    intro i _
    ring
  have expand : (∑ i ∈ s, c i * (exp m * (x i - m + 1))) = exp m * X + (exp m * (1 - m)) * C := by
    rw [Finset.sum_congr rfl pointwise, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have mC : m * C = X := by
    rw [hm]
    field_simp
  rw [expand] at total
  calc C * exp m = exp m * X + (exp m * (1 - m)) * C := by
        have : exp m * X = exp m * (m * C) := by rw [mC]
        rw [this]
        ring
    _ ≤ _ := total

/-- `K e^{S/K}` from an enclosure `K ∈ [Klo, Khi]`, `0 < Klo`, and `Slo ≤ S`: for
`Slo ≥ 0` it is at least `Klo e^{Slo/Khi}`, otherwise at least `Klo e^{Slo/Klo}`. -/
theorem kexp_lower {K S Klo Khi Slo : ℝ} (hlo : Klo ≤ K) (hhi : K ≤ Khi) (pos : 0 < Klo)
    (hS : Slo ≤ S) :
    Klo * exp (Slo / (if 0 ≤ Slo then Khi else Klo)) ≤ K * exp (S / K) := by
  have K0 : 0 < K := pos.trans_le hlo
  have step : exp (Slo / (if 0 ≤ Slo then Khi else Klo)) ≤ exp (S / K) := by
    apply exp_le_exp.mpr
    split_ifs with h
    · calc Slo / Khi ≤ Slo / K := div_le_div_of_nonneg_left h K0 hhi
        _ ≤ S / K := div_le_div_of_nonneg_right hS K0.le
    · have h' : Slo < 0 := lt_of_not_ge h
      calc Slo / Klo ≤ Slo / K := by
            rw [div_le_div_iff₀ pos K0]
            nlinarith
        _ ≤ S / K := div_le_div_of_nonneg_right hS K0.le
  exact mul_le_mul hlo step (exp_pos _).le K0.le

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
