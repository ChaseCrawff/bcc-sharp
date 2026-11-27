import BccSharp.TwoSite.MontgomeryDefs

/-!
# Montgomery's minimal theta functions: shared identities

This module proves the interfaces `Theta1Deriv`, `Unfold13` and `Duality` of
`BccSharp.TwoSite.MontgomeryDefs`, and the continuity of `Qser`, for the paper

H. L. Montgomery, *Minimal theta functions*, Glasgow Math. J. 30 (1988) 75–85.

* `theta1_hasDerivAt`: `∂_β θ(t; β) = -sin(2πβ) Q(t; β)` (the definition of `Q`).
* `sqrt_mul_theta1`: Poisson summation, the paper's (8).
* `unfold13`: the paper's (13).
* `duality`: the paper's (2), `θ(1/α) = α θ(α)`.
-/

set_option autoImplicit false

namespace BccSharp.Coulomb.Montgomery

open Real

/-! ### Chebyshev bound -/

theorem abs_sin_nat_mul_le (n : ℕ) (θ : ℝ) : |Real.sin (n * θ)| ≤ n * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : |Real.sin (k * θ) * Real.cos θ| ≤ |Real.sin (k * θ)| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one θ)
    have h2 : |Real.cos (k * θ) * Real.sin θ| ≤ |Real.sin θ| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
    calc |Real.sin (((k + 1 : ℕ) : ℝ) * θ)|
        = |Real.sin (k * θ) * Real.cos θ + Real.cos (k * θ) * Real.sin θ| := by
          push_cast; rw [add_mul, one_mul, Real.sin_add]
      _ ≤ |Real.sin (k * θ) * Real.cos θ| + |Real.cos (k * θ) * Real.sin θ| := abs_add_le _ _
      _ ≤ k * |Real.sin θ| + |Real.sin θ| := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * |Real.sin θ| := by push_cast; ring

theorem abs_U_eval_cos_le (n : ℕ) (θ : ℝ) :
    |(Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos θ)| ≤ n + 1 := by
  by_cases hs : Real.sin θ = 0
  · have hc : Real.cos θ = 1 ∨ Real.cos θ = -1 := by
      have h := Real.sin_sq_add_cos_sq θ
      rw [hs] at h
      have h2 : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · left; linarith
      · right; linarith
    rcases hc with h | h
    · rw [h, Polynomial.Chebyshev.U_eval_one]
      push_cast
      rw [abs_of_nonneg (by positivity)]
    · rw [h, Polynomial.Chebyshev.U_eval_neg_one]
      rcases Int.units_eq_one_or ((n : ℤ).negOnePow) with hu | hu <;>
        · rw [hu]; push_cast; rw [abs_mul]; norm_num; rw [abs_of_nonneg (by positivity)]
  · have key := Polynomial.Chebyshev.U_real_cos θ (n : ℤ)
    have hb := abs_sin_nat_mul_le (n + 1) θ
    have hpos : 0 < |Real.sin θ| := abs_pos.mpr hs
    push_cast at key hb
    rw [← key, abs_mul] at hb
    exact le_of_mul_le_mul_right hb hpos

/-! ### Summability and continuity of `Q` -/

theorem summable_sq_exp_succ {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 ht 2
  have hi : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := by
    intro a b hab; simpa using hab
  refine (h.comp_injective hi).congr fun k => ?_
  simp only [Function.comp_apply, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [abs_of_nonneg (by positivity)]
  push_cast
  ring_nf

theorem summable_Qser_term {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) *
      (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos (2 * π * β))) := by
  refine Summable.of_norm_bounded (summable_sq_exp_succ ht) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (k : ℝ) + 1),
    abs_of_pos (Real.exp_pos _)]
  have hU := abs_U_eval_cos_le k (2 * π * β)
  calc ((k : ℝ) + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) *
        |(Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos (2 * π * β))|
      ≤ ((k : ℝ) + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) * ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hU (by positivity)
    _ = ((k : ℝ) + 1) ^ 2 * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) := by ring

theorem Qser_continuous {t : ℝ} (ht : 0 < t) : Continuous (Qser t) := by
  unfold Qser
  refine continuous_const.mul (continuous_tsum (fun k => ?_) (summable_sq_exp_succ ht)
    (fun k β => ?_))
  · exact continuous_const.mul ((Polynomial.Chebyshev.U ℝ (k : ℤ)).continuous.comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (k : ℝ) + 1),
      abs_of_pos (Real.exp_pos _)]
    have hU := abs_U_eval_cos_le k (2 * π * β)
    calc ((k : ℝ) + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) *
          |(Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos (2 * π * β))|
        ≤ ((k : ℝ) + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
      _ = ((k : ℝ) + 1) ^ 2 * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) := by ring

/-! ### The `β`-derivative of `theta1` -/

private theorem summable_abs_mul_exp {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℤ => 2 * π * |(k : ℝ)| * Real.exp (-π * (k : ℝ) ^ 2 * t)) := by
  have h := (summable_pow_mul_jacobiTheta₂_term_bound 0 ht 1).mul_left (2 * π)
  refine h.congr fun k => ?_
  simp only [pow_one, mul_zero, zero_mul, sub_zero, Int.cast_abs]
  ring_nf

private theorem theta1_term_hasDerivAt (t : ℝ) (k : ℤ) (β : ℝ) :
    HasDerivAt (fun b : ℝ => Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * b))
      (-(2 * π * k) * Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.sin (2 * π * k * β)) β := by
  have h := ((hasDerivAt_id β).const_mul (2 * π * k)).cos.const_mul
    (Real.exp (-π * (k : ℝ) ^ 2 * t))
  convert h using 1
  · ext b; simp
  · simp; ring

/-- `∂_β θ(t; β)` as a series. -/
theorem theta1_hasDerivAt_series {t : ℝ} (ht : 0 < t) (β : ℝ) :
    HasDerivAt (theta1 t)
      (∑' k : ℤ, -(2 * π * k) * Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.sin (2 * π * k * β)) β := by
  have hu := summable_abs_mul_exp ht
  have h0 : Summable (fun k : ℤ => Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * 0)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      summable_exp_neg_mul_int_sq (c := π * t) (mul_pos Real.pi_pos ht)
  exact hasDerivAt_tsum hu (fun k b => theta1_term_hasDerivAt t k b)
    (fun k b => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos Real.pi_pos, abs_two]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _))
    h0 β

/-- The derivative series equals `-sin(2πβ) Q(t; β)`. -/
theorem theta1Deriv_series_eq {t : ℝ} (ht : 0 < t) (β : ℝ) :
    (∑' k : ℤ, -(2 * π * k) * Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.sin (2 * π * k * β)) =
      -(Real.sin (2 * π * β) * Qser t β) := by
  set g : ℤ → ℝ := fun k => -(2 * π * k) * Real.exp (-π * (k : ℝ) ^ 2 * t) *
    Real.sin (2 * π * k * β) with hg
  have hgs : Summable g := by
    refine Summable.of_norm_bounded (summable_abs_mul_exp ht) fun k => ?_
    rw [hg, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos Real.pi_pos, abs_two]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hneg : ∀ n : ℕ, g (-((n : ℤ) + 1)) = g ((n : ℤ) + 1) := by
    intro n
    simp only [hg]
    push_cast
    rw [show 2 * π * (-((n : ℝ) + 1)) * β = -(2 * π * ((n : ℝ) + 1) * β) by ring, Real.sin_neg]
    ring_nf
  have hsucc : ∀ n : ℕ, g ((n : ℤ) + 1) =
      -(Real.sin (2 * π * β) * (2 * π * (((n : ℝ) + 1) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) *
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (2 * π * β))))) := by
    intro n
    have key := Polynomial.Chebyshev.U_real_cos (2 * π * β) (n : ℤ)
    simp only [hg]
    push_cast
    push_cast at key
    rw [show 2 * π * ((n : ℝ) + 1) * β = ((n : ℝ) + 1) * (2 * π * β) by ring, ← key]
    ring
  have hnat : Summable (fun n : ℕ => g n) := hgs.comp_injective Nat.cast_injective
  have hnat' : Summable (fun n : ℕ => g (-(n + 1))) := by
    refine hgs.comp_injective (i := fun n : ℕ => (-((n : ℤ) + 1))) ?_
    intro a b hab; simpa using hab
  rw [tsum_of_nat_of_neg_add_one hnat hnat', hnat.tsum_eq_zero_add]
  have hz : g ((0 : ℕ) : ℤ) = 0 := by simp [hg]
  rw [hz, zero_add]
  have e1 : (∑' n : ℕ, g ((n + 1 : ℕ) : ℤ)) = ∑' n : ℕ, g ((n : ℤ) + 1) := by
    congr 1
  have e2 : (∑' n : ℕ, g (-((n : ℤ) + 1))) = ∑' n : ℕ, g ((n : ℤ) + 1) := by
    congr 1; funext n; exact hneg n
  rw [e1, e2]
  simp_rw [hsucc, tsum_neg, tsum_mul_left]
  unfold Qser
  ring

theorem theta1_hasDerivAt : Theta1Deriv := by
  intro t ht β
  have h := theta1_hasDerivAt_series ht β
  rwa [theta1Deriv_series_eq ht β] at h

/-! ### Poisson summation (Montgomery (8)) -/

theorem theta1_summable {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Summable (fun k : ℤ => Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * β)) := by
  have h := summable_exp_neg_mul_int_sq (c := π * t) (mul_pos Real.pi_pos ht)
  refine Summable.of_norm_bounded h fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-π * (k : ℝ) ^ 2 * t) * |Real.cos (2 * π * k * β)|
      ≤ Real.exp (-π * (k : ℝ) ^ 2 * t) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ = Real.exp (-(π * t) * (k : ℝ) ^ 2) := by ring_nf

theorem theta1_neg (t β : ℝ) : theta1 t (-β) = theta1 t β := by
  unfold theta1
  refine tsum_congr fun k => ?_
  rw [show 2 * π * (k : ℝ) * -β = -(2 * π * k * β) by ring, Real.cos_neg]

/-- Montgomery (8): `√τ · θ(τ; β) = Σ_m e^{-π(m+β)²/τ}`. -/
theorem sqrt_mul_theta1 {τ : ℝ} (hτ : 0 < τ) (β : ℝ) :
    Real.sqrt τ * theta1 τ β = ∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / τ) := by
  have ha : 0 < ((τ : ℂ)).re := by simpa using hτ
  have key := Complex.tsum_exp_neg_quadratic ha (Complex.I * (-β : ℝ))
  have hterm : ∀ n : ℤ, Complex.exp (-π * (τ : ℂ) * n ^ 2 + 2 * π * (Complex.I * (-β : ℝ)) * n) =
      Complex.exp (((-π * (n : ℝ) ^ 2 * τ : ℝ) : ℂ) + ((-(2 * π * n * β) : ℝ) : ℂ) * Complex.I) := by
    intro n; congr 1; push_cast; ring
  have hsL : Summable (fun n : ℤ =>
      Complex.exp (-π * (τ : ℂ) * n ^ 2 + 2 * π * (Complex.I * (-β : ℝ)) * n)) := by
    refine Summable.of_norm_bounded
      (summable_exp_neg_mul_int_sq (c := π * τ) (mul_pos Real.pi_pos hτ)) fun n => ?_
    rw [hterm, Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, add_zero]
    exact le_of_eq (by ring_nf)
  have hL : (∑' n : ℤ, Complex.exp (-π * (τ : ℂ) * n ^ 2 + 2 * π * (Complex.I * (-β : ℝ)) * n)).re =
      theta1 τ β := by
    rw [Complex.re_tsum hsL, ← theta1_neg]
    unfold theta1
    refine tsum_congr fun n => ?_
    rw [hterm, Complex.exp_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one,
      Complex.add_im, Complex.mul_im, zero_add]
    congr 1
    ring_nf
  have hR : ∀ n : ℤ, Complex.exp (-π / (τ : ℂ) * (n + Complex.I * (Complex.I * (-β : ℝ))) ^ 2) =
      ((Real.exp (-π * ((n : ℝ) + β) ^ 2 / τ) : ℝ) : ℂ) := by
    intro n
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hsqrt : (τ : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt τ : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hτ.le]
    push_cast
    rfl
  simp_rw [hR] at key
  rw [← Complex.ofReal_tsum, hsqrt] at key
  have hre := congrArg Complex.re key
  rw [hL] at hre
  have hpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  rw [show (1 : ℂ) / ((Real.sqrt τ : ℝ) : ℂ) *
      ((∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / τ) : ℝ) : ℂ) =
      (((Real.sqrt τ)⁻¹ * ∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / τ) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re] at hre
  rw [hre]
  field_simp

/-! ### Summability of the two-dimensional series, (13) and (2) -/

/-- The summand of `theta2` is dominated by a product of one-dimensional Gaussians. -/
theorem theta2_summable {α x y : ℝ} (hα : 0 < α) (hy : 0 < y) :
    Summable (fun p : ℤ × ℤ =>
      Real.exp (-π * α * (((p.1 : ℝ) + p.2 * x) ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y)) := by
  set δ : ℝ := min 1 (y ^ 2 / (2 * (x ^ 2 + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * x ^ 2 ≤ y ^ 2 / 2 := by
    have h := min_le_right 1 (y ^ 2 / (2 * (x ^ 2 + 1)))
    have hx : 0 ≤ x ^ 2 := sq_nonneg x
    calc δ * x ^ 2 ≤ y ^ 2 / (2 * (x ^ 2 + 1)) * x ^ 2 := mul_le_mul_of_nonneg_right h hx
      _ ≤ y ^ 2 / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg y, sq_nonneg x]
  set c₁ : ℝ := π * α * δ / (2 * y) with hc₁
  set c₂ : ℝ := π * α * y / 2 with hc₂
  have hc₁pos : 0 < c₁ := by positivity
  have hc₂pos : 0 < c₂ := by positivity
  have hprod := (summable_exp_neg_mul_int_sq hc₁pos).mul_of_nonneg
    (summable_exp_neg_mul_int_sq hc₂pos) (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun p => ?_) hprod
  rw [← Real.exp_add, Real.exp_le_exp]
  set m : ℝ := (p.1 : ℝ)
  set n : ℝ := (p.2 : ℝ)
  have hq : δ * m ^ 2 / 2 + y ^ 2 * n ^ 2 / 2 ≤ (m + n * x) ^ 2 + (n * y) ^ 2 := by
    have h1 : m ^ 2 / 2 - n ^ 2 * x ^ 2 ≤ (m + n * x) ^ 2 := by nlinarith [sq_nonneg (m + 2 * n * x)]
    have h2 : δ * (m + n * x) ^ 2 ≤ (m + n * x) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hδ1
    nlinarith [mul_le_mul_of_nonneg_left h1 hδpos.le, sq_nonneg n, hδ2,
      mul_le_mul_of_nonneg_left hδ2 (sq_nonneg n)]
  have hcoef : 0 < π * α / y := by positivity
  calc -c₁ * m ^ 2 + -c₂ * n ^ 2 = -(π * α / y) * (δ * m ^ 2 / 2 + y ^ 2 * n ^ 2 / 2) := by
        rw [hc₁, hc₂]; field_simp; ring
    _ ≥ -(π * α / y) * ((m + n * x) ^ 2 + (n * y) ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hq hcoef.le]
    _ = -π * α * ((m + n * x) ^ 2 + (n * y) ^ 2) / y := by ring

/-- Montgomery (13). -/
theorem unfold13 : Unfold13 := by
  intro α hα x y hy
  have hτ : 0 < y / α := div_pos hy hα
  set F : ℤ × ℤ → ℝ := fun p =>
    Real.exp (-π * α * (((p.1 : ℝ) + p.2 * x) ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y) with hF
  have hs : Summable F := theta2_summable hα hy
  have hs' : Summable (fun q : ℤ × ℤ => F (q.2, q.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hs
  have hswap : theta2 α x y = ∑' q : ℤ × ℤ, F (q.2, q.1) := by
    unfold theta2
    exact ((Equiv.prodComm ℤ ℤ).tsum_eq F).symm
  rw [hswap, hs'.tsum_prod, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hinner : ∀ m : ℤ, F (m, n) = Real.exp (-π * α * y * (n : ℝ) ^ 2) *
      Real.exp (-π * ((m : ℝ) + n * x) ^ 2 / (y / α)) := by
    intro m
    simp only [hF]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [hinner]
  rw [tsum_mul_left, ← sqrt_mul_theta1 hτ]
  ring

/-- Montgomery (2): `θ(1/α) = α θ(α)`. -/
theorem duality : Duality := by
  intro α hα x y hy
  have hα' : 0 < α⁻¹ := inv_pos.mpr hα
  set H : ℤ → ℤ → ℝ := fun n k => Real.exp (-π * α * y * (n : ℝ) ^ 2) *
    (Real.exp (-π * (k : ℝ) ^ 2 * (y / α)) * Real.cos (2 * π * k * (n * x))) with hH
  have hHs : Summable (Function.uncurry H) := by
    have hprod := (summable_exp_neg_mul_int_sq (c := π * α * y) (by positivity)).mul_of_nonneg
      (summable_exp_neg_mul_int_sq (c := π * (y / α)) (by positivity))
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    refine Summable.of_norm_bounded hprod fun p => ?_
    simp only [Function.uncurry, hH]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-π * α * y * (p.1 : ℝ) ^ 2) *
          (Real.exp (-π * (p.2 : ℝ) ^ 2 * (y / α)) * |Real.cos (2 * π * p.2 * (p.1 * x))|)
        ≤ Real.exp (-π * α * y * (p.1 : ℝ) ^ 2) * (Real.exp (-π * (p.2 : ℝ) ^ 2 * (y / α)) * 1) := by
          gcongr; exact Real.abs_cos_le_one _
      _ = Real.exp (-(π * α * y) * (p.1 : ℝ) ^ 2) * Real.exp (-(π * (y / α)) * (p.2 : ℝ) ^ 2) := by
          ring_nf
  have hA : theta2 α x y = Real.sqrt (y / α) * ∑' n : ℤ, ∑' k : ℤ, H n k := by
    rw [unfold13 α hα x y hy]
    congr 1
    refine tsum_congr fun n => ?_
    simp only [hH, theta1]
    rw [tsum_mul_left]
  have hB : theta2 α⁻¹ x y = Real.sqrt (y * α) * ∑' n : ℤ, ∑' k : ℤ, H k n := by
    rw [unfold13 α⁻¹ hα' x y hy, show y / α⁻¹ = y * α by field_simp]
    congr 1
    refine tsum_congr fun n => ?_
    simp only [hH, theta1]
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show 2 * π * (n : ℝ) * (k * x) = 2 * π * k * (n * x) by ring]
    have e1 : Real.exp (-π * α⁻¹ * y * (n : ℝ) ^ 2) = Real.exp (-π * (n : ℝ) ^ 2 * (y / α)) := by
      congr 1; field_simp
    have e2 : Real.exp (-π * (k : ℝ) ^ 2 * (y * α)) = Real.exp (-π * α * y * (k : ℝ) ^ 2) := by
      congr 1; ring
    rw [e1, e2]
    ring
  rw [hB, hHs.tsum_comm, hA]
  have hsq : Real.sqrt (y * α) = α * Real.sqrt (y / α) := by
    rw [show y * α = α ^ 2 * (y / α) by field_simp, Real.sqrt_mul (sq_nonneg α),
      Real.sqrt_sq hα.le]
  rw [hsq]
  ring

end BccSharp.Coulomb.Montgomery
