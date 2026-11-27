import BccSharp.Lattice.LocalObjective
import BccSharp.Lattice.HessianTail
import BccSharp.TwoSite.GeneralSummability
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false

/-! Differentiation of the exact local Ewald series along a ray.
The exchange uses uniform bounds on an open real interval containing
the closed segment used by strictness. The finite near modes and the
infinite Gaussian part use different bounds. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp

def rayKernel (k : KernelKind) (a : IntVec → ℝ → ℝ) (n : IntVec) (t : ℝ) : ℝ :=
  if n = 0 then 0 else kernelValue k (a n t)

def rayKernelFirst (k : KernelKind) (a da : IntVec → ℝ → ℝ) (n : IntVec) (t : ℝ) : ℝ :=
  if n = 0 then 0 else kernelSlope k (a n t) * da n t

def rayKernelSecond (k : KernelKind) (a da dda : IntVec → ℝ → ℝ)
    (n : IntVec) (t : ℝ) : ℝ :=
  if n = 0 then 0 else kernelCurvature k (a n t) * (da n t)^2 +
    kernelSlope k (a n t) * dda n t

theorem rayKernel_derivatives (k : KernelKind) (a da dda : IntVec → ℝ → ℝ)
    (n : IntVec) (t : ℝ) (h : n ≠ 0 → 0 < a n t ∧
      HasDerivAt (a n) (da n t) t ∧ HasDerivAt (da n) (dda n t) t) :
    HasDerivAt (rayKernel k a n) (rayKernelFirst k a da n t) t ∧
    HasDerivAt (rayKernelFirst k a da n) (rayKernelSecond k a da dda n t) t := by
  by_cases hn : n = 0
  · have e₁ : rayKernel k a n = fun _ => 0 := by funext s; simp [rayKernel, hn]
    have e₂ : rayKernelFirst k a da n = fun _ => 0 := by funext s; simp [rayKernelFirst, hn]
    have e₃ : rayKernelSecond k a da dda n t = 0 := by simp [rayKernelSecond, hn]
    rw [e₁, e₂, e₃]
    exact ⟨hasDerivAt_const t (0 : ℝ), hasDerivAt_const t (0 : ℝ)⟩
  obtain ⟨ha, hd, hdd⟩ := h hn
  have e := (kernelValue_hasDerivAt k ha).comp t hd
  have f := ((kernelSlope_hasDerivAt k ha).comp t hd).mul hdd
  constructor
  · convert e using 1
    · funext s; simp [rayKernel, hn]
    · simp [rayKernelFirst, hn]
  · convert f using 1
    · ext s; simp [rayKernelFirst, hn]
    · simp only [rayKernelSecond, if_neg hn, Function.comp_apply]; ring

theorem rayKernel_gaussian_bounds (k : KernelKind) {a da dda z α K₁ K₂ : ℝ}
    (ha : 1 ≤ a) (hz : 0 ≤ z) (hα : 0 < α) (hza : α*z ≤ a)
    (hd : |da| ≤ K₁*z) (hdd : |dda| ≤ K₂*z) (h₁ : 0 ≤ K₁) (h₂ : 0 ≤ K₂) :
    |kernelValue k a| ≤ Real.exp (-(α/2)*z) ∧
    |kernelSlope k a * da| ≤ (4*K₁/α)*Real.exp (-(α/2)*z) ∧
    |kernelCurvature k a * da^2 + kernelSlope k a * dda| ≤
      (80*K₁^2/α^2+4*K₂/α)*Real.exp (-(α/2)*z) := by
  have hp : 0 < a := zero_lt_one.trans_le ha
  have ev : Real.exp (-a)/a ≤ Real.exp (-α*z) :=
    (div_le_self (Real.exp_pos _).le ha).trans (Real.exp_le_exp.mpr (by linarith))
  have es : Real.exp (-α*z) = Real.exp (-(α/2)*z)*Real.exp (-(α/2)*z) := by
    rw [← Real.exp_add]; congr 1; ring
  have ep : z*Real.exp (-(α/2)*z) ≤ 2/α := by
    have h := Real.add_one_le_exp (α/2*z)
    have g : α/2*z ≤ Real.exp (α/2*z) := by linarith
    have he := mul_le_mul_of_nonneg_right g (Real.exp_pos (-(α/2)*z)).le
    rw [← Real.exp_add, show α/2*z+ -(α/2)*z=0 by ring, Real.exp_zero] at he
    apply (le_div_iff₀ hα).mpr
    linarith only [show α*(z*Real.exp (-(α/2)*z)) ≤ 2 by nlinarith only [he]]
  have epp : z^2*Real.exp (-(α/2)*z) ≤ 16/α^2 := by
    have h₄ : z*Real.exp (-(α/4)*z) ≤ 4/α := by
      have h := Real.add_one_le_exp (α/4*z)
      have g : α/4*z ≤ Real.exp (α/4*z) := by linarith
      have he := mul_le_mul_of_nonneg_right g (Real.exp_pos (-(α/4)*z)).le
      rw [← Real.exp_add, show α/4*z+ -(α/4)*z=0 by ring, Real.exp_zero] at he
      apply (le_div_iff₀ hα).mpr
      nlinarith only [he]
    have hh := pow_le_pow_left₀ (mul_nonneg hz (Real.exp_pos _).le) h₄ 2
    have id : ((2 : ℕ) : ℝ)* (-(α/4)*z) = -(α/2)*z := by norm_num <;> ring
    rw [mul_pow, div_pow, ← Real.exp_nat_mul (-(α/4)*z) 2, id] at hh
    exact hh.trans_eq (by norm_num)
  have ed : z*Real.exp (-α*z) ≤ (2/α)*Real.exp (-(α/2)*z) := by
    rw [es, ← mul_assoc]; exact mul_le_mul_of_nonneg_right ep (Real.exp_pos _).le
  have edd : z^2*Real.exp (-α*z) ≤ (16/α^2)*Real.exp (-(α/2)*z) := by
    rw [es, ← mul_assoc]; exact mul_le_mul_of_nonneg_right epp (Real.exp_pos _).le
  have ⟨ks, kc⟩ := kernelDerivative_bounds k ha
  have hs : |kernelSlope k a| ≤ 2*Real.exp (-α*z) := by
    rw [mul_div_assoc] at ks
    linarith only [ks, mul_le_mul_of_nonneg_left ev (show (0 : ℝ) ≤ 2 by norm_num)]
  have hc : |kernelCurvature k a| ≤ 5*Real.exp (-α*z) := by
    rw [mul_div_assoc] at kc
    linarith only [kc, mul_le_mul_of_nonneg_left ev (show (0 : ℝ) ≤ 5 by norm_num)]
  have linear (x K : ℝ) (hx : |x| ≤ K*z) (hK : 0 ≤ K) :
      |kernelSlope k a * x| ≤ (4*K/α)*Real.exp (-(α/2)*z) := by
    rw [abs_mul]
    calc
      _ ≤ (2*Real.exp (-α*z))*(K*z) :=
        mul_le_mul hs hx (abs_nonneg _) (by positivity)
      _ = (2*K)*(z*Real.exp (-α*z)) := by ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left ed (by positivity : 0 ≤ 2*K) using 1
        ring
  have quadratic : |kernelCurvature k a * da^2| ≤
      (80*K₁^2/α^2)*Real.exp (-(α/2)*z) := by
    rw [abs_mul, abs_pow]
    calc
      _ ≤ (5*Real.exp (-α*z))*(K₁*z)^2 :=
        mul_le_mul hc (pow_le_pow_left₀ (abs_nonneg _) hd 2) (sq_nonneg _) (by positivity)
      _ = (5*K₁^2)*(z^2*Real.exp (-α*z)) := by ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left edd (by positivity : 0 ≤ 5*K₁^2) using 1
        ring
  refine ⟨?_, linear da K₁ hd h₁, ?_⟩
  · obtain ⟨h0, h⟩ := kernelValue_positive_bound k hp
    rw [abs_of_nonneg h0]
    exact (h.trans ev).trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα.le hz]))
  · calc
      _ ≤ |kernelCurvature k a * da^2|+|kernelSlope k a * dda| := abs_add_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add quadratic (linear dda K₂ hdd h₂)

theorem localRayInterval_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Finite near modes need their own bounds. Remote modes use a single
positive lower exponent and two quadratic growth bounds, yielding a
summable normal majorant on the entire open ray interval. -/
theorem rayKernel_tsum_derivatives (k : KernelKind) (a da dda : IntVec → ℝ → ℝ)
    (near : Finset IntVec) (bound : IntVec → ℝ) (e α K₁ K₂ : ℝ)
    (he : 0 < e) (hα : 0 < α) (h₁ : 0 ≤ K₁) (h₂ : 0 ≤ K₂)
    (jet : ∀ n s, n ≠ 0 → s ∈ Set.Ioo (-e) e → 0 < a n s ∧
      HasDerivAt (a n) (da n s) s ∧ HasDerivAt (da n) (dda n s) s)
    (remote : ∀ n ∉ near, n ≠ 0 → ∀ s ∈ Set.Ioo (-e) e,
      1 ≤ a n s ∧ α*sq (castVec n) ≤ a n s ∧
      |da n s| ≤ K₁*sq (castVec n) ∧ |dda n s| ≤ K₂*sq (castVec n))
    (localBound : ∀ n ∈ near, 0 ≤ bound n ∧ ∀ s ∈ Set.Ioo (-e) e,
      |rayKernel k a n s| ≤ bound n ∧ |rayKernelFirst k a da n s| ≤ bound n ∧
      |rayKernelSecond k a da dda n s| ≤ bound n) :
    ∀ t ∈ Set.Ioo (-e) e,
      Summable (fun n => rayKernelFirst k a da n t) ∧
      HasDerivAt (fun s => ∑' n, rayKernel k a n s) (∑' n, rayKernelFirst k a da n t) t ∧
      HasDerivAt (fun s => ∑' n, rayKernelFirst k a da n s)
        (∑' n, rayKernelSecond k a da dda n t) t := by
  classical
  let C := 1 + 4*K₁/α + (80*K₁^2/α^2+4*K₂/α)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let U (n : IntVec) := if n ∈ near then bound n else C*Real.exp (-(α/2)*sq (castVec n))
  have hU : Summable U := by
    apply summable_of_finset_compl near
    have hs := ((integerGaussian_summable (show 0 < α/2 by positivity)).mul_left C).subtype
      (fun n => n ∉ near)
    refine hs.congr (fun i => ?_)
    have hi : (i : IntVec) ∉ near := i.2
    simp only [U, Function.comp_apply, if_neg hi]
  have major (n : IntVec) (t : ℝ) (ht : t ∈ Set.Ioo (-e) e) :
      ‖rayKernel k a n t‖ ≤ U n ∧ ‖rayKernelFirst k a da n t‖ ≤ U n ∧
      ‖rayKernelSecond k a da dda n t‖ ≤ U n := by
    simp only [Real.norm_eq_abs]
    by_cases hm : n ∈ near
    · simpa [U, hm] using (localBound n hm).2 t ht
    by_cases hn : n = 0
    · subst hn
      have hz : 0 ≤ U 0 := by
        simp only [U, if_neg hm]
        exact mul_nonneg hC (Real.exp_pos _).le
      simp [rayKernel, rayKernelFirst, rayKernelSecond, hz]
    obtain ⟨ha, hza, hd, hdd⟩ := remote n hm hn t ht
    obtain ⟨e, d, dd⟩ := rayKernel_gaussian_bounds k ha (sq_nonnegative _) hα hza hd hdd h₁ h₂
    have e₀ : (1 : ℝ) ≤ C := by dsimp [C]; linarith [show 0 ≤ 4*K₁/α by positivity,
      show 0 ≤ 80*K₁^2/α^2+4*K₂/α by positivity]
    have e₁ : 4*K₁/α ≤ C := by dsimp [C]; linarith [show 0 ≤ 80*K₁^2/α^2+4*K₂/α by positivity]
    have e₂ : 80*K₁^2/α^2+4*K₂/α ≤ C := by dsimp [C]; linarith [show 0 ≤ 4*K₁/α by positivity]
    simpa [U, hm, hn, rayKernel, rayKernelFirst, rayKernelSecond] using
      And.intro (e.trans (by simpa using mul_le_mul_of_nonneg_right e₀ (Real.exp_pos _).le))
        (And.intro (d.trans (mul_le_mul_of_nonneg_right e₁ (Real.exp_pos _).le))
          (dd.trans (mul_le_mul_of_nonneg_right e₂ (Real.exp_pos _).le)))
  have h0 : (0 : ℝ) ∈ Set.Ioo (-e) e := ⟨neg_lt_zero.mpr he,he⟩
  have point n s hs := rayKernel_derivatives k a da dda n s (fun hn => jet n s hn hs)
  intro t ht
  exact ⟨hU.of_norm_bounded (fun n => (major n t ht).2.1),
    hasDerivAt_tsum_of_isPreconnected hU isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun n s hs => (point n s hs).1) (fun n s hs => (major n s hs).2.1)
      h0 (hU.of_norm_bounded (fun n => (major n 0 h0).1)) ht,
    hasDerivAt_tsum_of_isPreconnected hU isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun n s hs => (point n s hs).2) (fun n s hs => (major n s hs).2.2)
      h0 (hU.of_norm_bounded (fun n => (major n 0 h0).2.1)) ht⟩

end BccSharp.Coulomb.BravaisCover
