import BccSharp.TwoSite.MontgomeryBasic

/-!
# Montgomery's Lemma 2 for `0 < t < 1` at the endpoints `β = 0, 1/2`

H. L. Montgomery, *Minimal theta functions*, Glasgow Math. J. 30 (1988) 75–85, Lemma 2
(stated on p. 78; the case `t < 1` is argued on p. 79).

Write `P(t; β) = Σ_m e^{-π(m+β)²/t}`, so that `√t θ(t; β) = P(t; β)` (`sqrt_mul_theta1`).
Differentiating this identity in `t` gives (`smallT_key`)

  `-2 ∂_t θ(t; β) = (t√t)⁻¹ Σ_m (1 - 2π(m+β)²/t) e^{-π(m+β)²/t}`.

At the endpoints `Q(t; 0) = -2 ∂_t θ(t; 0)` and `Q(t; 1/2) = 2 ∂_t θ(t; 1/2)`
(`smallT_Qser_zero`, `smallT_Qser_half`). For `0 < t < 1` the dual series at `β = 0`
has the term `1` at `m = 0` and nonpositive terms elsewhere. At `β = 1/2` all of its
terms are nonpositive, and the terms `m = 0, -1` add up to `-(π/t - 2) e^{-π/(4t)}`,
which is at most `-e^{-π/(4t)}`.
-/

set_option autoImplicit false

namespace BccSharp.Coulomb.Montgomery

open Real Filter Topology

/-! ### The two series -/

/-- The series of `∂_t θ(t; β)`. -/
noncomputable def smallT_dtheta (t β : ℝ) : ℝ :=
  ∑' k : ℤ, -π * (k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * β)

/-- The dual series `Σ_m (1 - 2π(m+β)²/t) e^{-π(m+β)²/t}`. -/
noncomputable def smallT_dual (t β : ℝ) : ℝ :=
  ∑' m : ℤ, (1 - 2 * π * ((m : ℝ) + β) ^ 2 / t) * Real.exp (-π * ((m : ℝ) + β) ^ 2 / t)

/-! ### Shifted Gaussian summability -/

theorem smallT_summable_shift {c : ℝ} (hc : 0 < c) (β : ℝ) :
    Summable (fun m : ℤ => Real.exp (-c * ((m : ℝ) + β) ^ 2)) := by
  have h := (summable_exp_neg_mul_int_sq (c := c / 2) (by positivity)).mul_left
    (Real.exp (c * β ^ 2))
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_) h
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (m : ℝ) ^ 2 / 2 - β ^ 2 ≤ ((m : ℝ) + β) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) + 2 * β)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]

theorem smallT_sq_mul_exp_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    x ^ 2 * Real.exp (-c * x ^ 2) ≤ 2 / c * Real.exp (-(c / 2) * x ^ 2) := by
  have h1 := Real.add_one_le_exp (c / 2 * x ^ 2)
  have h2 : x ^ 2 ≤ 2 / c * Real.exp (c / 2 * x ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [sq_nonneg x]
  calc x ^ 2 * Real.exp (-c * x ^ 2)
      ≤ 2 / c * Real.exp (c / 2 * x ^ 2) * Real.exp (-c * x ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 2 / c * Real.exp (-(c / 2) * x ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem smallT_summable_sq_shift {c : ℝ} (hc : 0 < c) (β : ℝ) :
    Summable (fun m : ℤ => ((m : ℝ) + β) ^ 2 * Real.exp (-c * ((m : ℝ) + β) ^ 2)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity) (fun _ => smallT_sq_mul_exp_le hc _)
    ((smallT_summable_shift (c := c / 2) (by positivity) β).mul_left (2 / c))

/-! ### The `t`-derivative of `θ(t; β)` -/

theorem smallT_summable_dtheta_majorant {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℤ => π * ((k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * t))) := by
  refine ((smallT_summable_sq_shift (c := π * t) (by positivity) 0).mul_left π).congr
    fun k => ?_
  rw [add_zero, show -(π * t) * (k : ℝ) ^ 2 = -π * (k : ℝ) ^ 2 * t by ring]

theorem smallT_dtheta_summable {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Summable (fun k : ℤ =>
      -π * (k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * β)) := by
  refine Summable.of_norm_bounded (smallT_summable_dtheta_majorant ht) fun k => ?_
  have e : -π * (k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * β) =
      -(π * ((k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * t))) * Real.cos (2 * π * k * β) := by
    ring
  rw [Real.norm_eq_abs, e, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

theorem smallT_theta_term_hasDerivAt (β : ℝ) (k : ℤ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-π * (k : ℝ) ^ 2 * u) * Real.cos (2 * π * k * β))
      (-π * (k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * s) * Real.cos (2 * π * k * β)) s := by
  have h := (((hasDerivAt_id' s).const_mul (-π * (k : ℝ) ^ 2)).exp).mul_const
    (Real.cos (2 * π * k * β))
  convert h using 1
  ring

/-- `∂_t θ(t; β)` as a series. -/
theorem smallT_theta_hasDerivAt_t {t : ℝ} (ht : 0 < t) (β : ℝ) :
    HasDerivAt (fun u => theta1 u β) (smallT_dtheta t β) t := by
  have hu := smallT_summable_dtheta_majorant (half_pos ht)
  unfold theta1 smallT_dtheta
  refine hasDerivAt_tsum_of_isPreconnected (t := Set.Ioi (t / 2)) (y₀ := t)
    (g := fun (k : ℤ) (u : ℝ) => Real.exp (-π * (k : ℝ) ^ 2 * u) * Real.cos (2 * π * k * β))
    (g' := fun (k : ℤ) (u : ℝ) => -π * (k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * u) *
      Real.cos (2 * π * k * β))
    hu isOpen_Ioi isPreconnected_Ioi (fun k s _ => smallT_theta_term_hasDerivAt β k s)
    (fun k s hs => ?_) (Set.mem_Ioi.mpr (by linarith)) (theta1_summable ht β)
    (Set.mem_Ioi.mpr (by linarith))
  have hs' : t / 2 < s := hs
  show ‖-π * (k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * s) * Real.cos (2 * π * k * β)‖ ≤
    π * ((k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * (t / 2)))
  have hexp : Real.exp (-π * (k : ℝ) ^ 2 * s) ≤ Real.exp (-π * (k : ℝ) ^ 2 * (t / 2)) := by
    rw [Real.exp_le_exp]
    have : 0 ≤ π * (k : ℝ) ^ 2 := by positivity
    nlinarith
  have e : -π * (k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * s) * Real.cos (2 * π * k * β) =
      -(π * ((k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * s))) * Real.cos (2 * π * k * β) := by
    ring
  rw [Real.norm_eq_abs, e, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  calc π * ((k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * s)) * |Real.cos (2 * π * k * β)|
      ≤ π * ((k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * s)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ ≤ π * ((k : ℝ) ^ 2 * Real.exp (-π * (k : ℝ) ^ 2 * (t / 2))) := by
        rw [mul_one]
        gcongr

/-! ### The `t`-derivative of the dual series -/

theorem smallT_dual_term_hasDerivAt (x : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.exp (-π * x ^ 2 / u))
      (Real.exp (-π * x ^ 2 / s) * (π * x ^ 2 / s ^ 2)) s := by
  have h := ((hasDerivAt_inv hs).const_mul (-π * x ^ 2)).exp
  convert h using 1
  simp only [div_eq_mul_inv]
  ring_nf

theorem smallT_dual_bound {t s : ℝ} (ht : 0 < t) (hs1 : t / 2 < s) (hs2 : s < 2 * t) (x : ℝ) :
    ‖Real.exp (-π * x ^ 2 / s) * (π * x ^ 2 / s ^ 2)‖ ≤
      4 * π / t ^ 2 * (x ^ 2 * Real.exp (-(π / (2 * t)) * x ^ 2)) := by
  have hs0 : 0 < s := lt_trans (half_pos ht) hs1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : Real.exp (-π * x ^ 2 / s) ≤ Real.exp (-(π / (2 * t)) * x ^ 2) := by
    rw [Real.exp_le_exp]
    have h : π * x ^ 2 / (2 * t) ≤ π * x ^ 2 / s :=
      div_le_div_of_nonneg_left (by positivity) hs0 hs2.le
    have e1 : -π * x ^ 2 / s = -(π * x ^ 2 / s) := by ring
    have e2 : -(π / (2 * t)) * x ^ 2 = -(π * x ^ 2 / (2 * t)) := by ring
    rw [e1, e2]
    linarith
  have h2 : π * x ^ 2 / s ^ 2 ≤ 4 * π / t ^ 2 * x ^ 2 := by
    have hsq : (t / 2) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs1.le 2
    calc π * x ^ 2 / s ^ 2 ≤ π * x ^ 2 / (t / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = 4 * π / t ^ 2 * x ^ 2 := by field_simp; ring
  calc Real.exp (-π * x ^ 2 / s) * (π * x ^ 2 / s ^ 2)
      ≤ Real.exp (-(π / (2 * t)) * x ^ 2) * (4 * π / t ^ 2 * x ^ 2) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = 4 * π / t ^ 2 * (x ^ 2 * Real.exp (-(π / (2 * t)) * x ^ 2)) := by ring

theorem smallT_summable_dual_exp {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Summable (fun m : ℤ => Real.exp (-π * ((m : ℝ) + β) ^ 2 / t)) := by
  refine (smallT_summable_shift (c := π / t) (by positivity) β).congr fun m => ?_
  congr 1
  ring

theorem smallT_dual_hasDerivAt {t : ℝ} (ht : 0 < t) (β : ℝ) :
    HasDerivAt (fun u => ∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / u))
      (∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / t) * (π * ((m : ℝ) + β) ^ 2 / t ^ 2)) t := by
  have hu : Summable (fun m : ℤ => 4 * π / t ^ 2 *
      (((m : ℝ) + β) ^ 2 * Real.exp (-(π / (2 * t)) * ((m : ℝ) + β) ^ 2))) :=
    (smallT_summable_sq_shift (by positivity) β).mul_left _
  exact hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (t / 2) (2 * t)) (y₀ := t)
    (g := fun (m : ℤ) (u : ℝ) => Real.exp (-π * ((m : ℝ) + β) ^ 2 / u))
    (g' := fun (m : ℤ) (u : ℝ) =>
      Real.exp (-π * ((m : ℝ) + β) ^ 2 / u) * (π * ((m : ℝ) + β) ^ 2 / u ^ 2))
    hu isOpen_Ioo isPreconnected_Ioo
    (fun m s hs => smallT_dual_term_hasDerivAt _ (lt_trans (half_pos ht) hs.1).ne')
    (fun m s hs => smallT_dual_bound ht hs.1 hs.2 _) ⟨by linarith, by linarith⟩
    (smallT_summable_dual_exp ht β) ⟨by linarith, by linarith⟩

/-! ### The differentiated Poisson identity -/

private theorem smallT_alg {r t θ D G G' : ℝ} (hr : 0 < r) (htr : r * r = t)
    (h1 : 1 / (2 * r) * θ + r * D = G') (h2 : r * θ = G) :
    -2 * D = (t * r)⁻¹ * (G - 2 * t * G') := by
  have hr' : r ≠ 0 := hr.ne'
  subst htr h1 h2
  field_simp
  ring

/-- `-2 ∂_t θ(t; β) = (t√t)⁻¹ Σ_m (1 - 2π(m+β)²/t) e^{-π(m+β)²/t}`. -/
theorem smallT_key {t : ℝ} (ht : 0 < t) (β : ℝ) :
    -2 * smallT_dtheta t β = (t * Real.sqrt t)⁻¹ * smallT_dual t β := by
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hprod := (Real.hasDerivAt_sqrt ht.ne').mul (smallT_theta_hasDerivAt_t ht β)
  have heq : (fun u => Real.sqrt u * theta1 u β) =ᶠ[𝓝 t]
      (fun u => ∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / u)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun u hu => sqrt_mul_theta1 hu β
  have huniq := hprod.unique ((smallT_dual_hasDerivAt ht β).congr_of_eventuallyEq heq)
  have hs1 := smallT_summable_dual_exp ht β
  have hs2 : Summable (fun m : ℤ =>
      Real.exp (-π * ((m : ℝ) + β) ^ 2 / t) * (π * ((m : ℝ) + β) ^ 2 / t ^ 2)) := by
    refine ((smallT_summable_sq_shift (c := π / t) (by positivity) β).mul_left
      (π / t ^ 2)).congr fun m => ?_
    rw [show -(π / t) * ((m : ℝ) + β) ^ 2 = -π * ((m : ℝ) + β) ^ 2 / t by ring]
    ring
  have hE : smallT_dual t β = (∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / t)) -
      2 * t * ∑' m : ℤ, Real.exp (-π * ((m : ℝ) + β) ^ 2 / t) *
        (π * ((m : ℝ) + β) ^ 2 / t ^ 2) := by
    rw [← tsum_mul_left, ← hs1.tsum_sub (hs2.mul_left (2 * t))]
    unfold smallT_dual
    refine tsum_congr fun m => ?_
    field_simp
  rw [hE]
  exact smallT_alg hr (Real.mul_self_sqrt ht.le) huniq (sqrt_mul_theta1 ht β)

/-! ### The endpoint values of `Q` -/

theorem smallT_tsum_int_even {f : ℤ → ℝ} (hf : Summable f) (he : ∀ k, f (-k) = f k)
    (h0 : f 0 = 0) : ∑' k : ℤ, f k = 2 * ∑' n : ℕ, f ((n : ℤ) + 1) := by
  have h1 : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    hf.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) fun a b h => by simpa using h
  have h2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) fun a b h => by simpa using h
  rw [tsum_of_add_one_of_neg_add_one h1 h2, h0, add_zero]
  simp_rw [he]
  ring

theorem smallT_dtheta_eq {t : ℝ} (ht : 0 < t) (β : ℝ) :
    smallT_dtheta t β = -(2 * π) * ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 *
      Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) * Real.cos (2 * π * ((n : ℝ) + 1) * β) := by
  unfold smallT_dtheta
  rw [smallT_tsum_int_even (smallT_dtheta_summable ht β)
    (fun k => by simp only [Int.cast_neg, neg_sq, mul_neg, neg_mul, Real.cos_neg]) (by simp),
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  push_cast
  ring

theorem smallT_Qser_zero {t : ℝ} (ht : 0 < t) : Qser t 0 = -2 * smallT_dtheta t 0 := by
  rw [smallT_dtheta_eq ht 0]
  unfold Qser
  have e : ∀ n : ℕ, ((n : ℝ) + 1) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) *
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (2 * π * 0)) =
      ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) *
        Real.cos (2 * π * ((n : ℝ) + 1) * 0) := by
    intro n
    simp only [mul_zero, Real.cos_zero, Polynomial.Chebyshev.U_eval_one, Int.cast_natCast]
    ring
  simp_rw [e]
  ring

theorem smallT_Qser_half {t : ℝ} (ht : 0 < t) :
    Qser t (1 / 2) = 2 * smallT_dtheta t (1 / 2) := by
  rw [smallT_dtheta_eq ht (1 / 2)]
  unfold Qser
  have e : ∀ n : ℕ, ((n : ℝ) + 1) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) *
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (2 * π * (1 / 2))) =
      -(((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) *
        Real.cos (2 * π * ((n : ℝ) + 1) * (1 / 2))) := by
    intro n
    have h1 : Real.cos (2 * π * (1 / 2)) = -1 := by
      rw [show 2 * π * (1 / 2 : ℝ) = π by ring, Real.cos_pi]
    have h2 : Real.cos (2 * π * ((n : ℝ) + 1) * (1 / 2)) = (-1) ^ (n + 1) := by
      rw [← Real.cos_nat_mul_pi]
      congr 1
      push_cast
      ring
    rw [h1, h2, Polynomial.Chebyshev.U_eval_neg_one, Int.cast_negOnePow_natCast]
    push_cast
    ring
  simp_rw [e, tsum_neg]
  ring

/-! ### The bounds for `0 < t < 1` -/

theorem smallT_dual_summable {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Summable (fun m : ℤ => (1 - 2 * π * ((m : ℝ) + β) ^ 2 / t) *
      Real.exp (-π * ((m : ℝ) + β) ^ 2 / t)) := by
  have h1 := smallT_summable_shift (c := π / t) (by positivity) β
  have h2 := (smallT_summable_sq_shift (c := π / t) (by positivity) β).mul_left (2 * π / t)
  refine (h1.sub h2).congr fun m => ?_
  rw [show -(π / t) * ((m : ℝ) + β) ^ 2 = -π * ((m : ℝ) + β) ^ 2 / t by ring]
  ring

theorem smallT_dual_zero_le {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : smallT_dual t 0 ≤ 1 := by
  unfold smallT_dual
  calc (∑' m : ℤ, (1 - 2 * π * ((m : ℝ) + 0) ^ 2 / t) * Real.exp (-π * ((m : ℝ) + 0) ^ 2 / t))
      ≤ ∑' m : ℤ, (if m = 0 then (1 : ℝ) else 0) := by
        refine (smallT_dual_summable ht 0).tsum_le_tsum (fun m => ?_)
          (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
        split_ifs with hm
        · subst hm
          simp
        · have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
            have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
            nlinarith [abs_mul_abs_self (m : ℝ)]
          have hneg : 1 - 2 * π * ((m : ℝ) + 0) ^ 2 / t ≤ 0 := by
            rw [add_zero, sub_nonpos, le_div_iff₀ ht]
            nlinarith [Real.pi_gt_three]
          exact mul_nonpos_of_nonpos_of_nonneg hneg (Real.exp_pos _).le
    _ = 1 := by simp

theorem smallT_dual_half_le {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    smallT_dual t (1 / 2) ≤ -Real.exp (-π / (4 * t)) := by
  unfold smallT_dual
  set f : ℤ → ℝ := fun m => (1 - 2 * π * ((m : ℝ) + 1 / 2) ^ 2 / t) *
    Real.exp (-π * ((m : ℝ) + 1 / 2) ^ 2 / t) with hf
  have hfs : Summable f := smallT_dual_summable ht (1 / 2)
  have hnonneg : ∀ m : ℤ, 0 ≤ -f m := by
    intro m
    have hmm : (0 : ℤ) ≤ m * (m + 1) := by
      rcases le_or_gt 0 m with h | h
      · exact mul_nonneg h (by omega)
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    have hq : (1 / 4 : ℝ) ≤ ((m : ℝ) + 1 / 2) ^ 2 := by
      have : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast hmm
      nlinarith
    have hc : 1 - 2 * π * ((m : ℝ) + 1 / 2) ^ 2 / t ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ ht]
      nlinarith [Real.pi_gt_three]
    simp only [hf]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hc (Real.exp_pos _).le)
  have hpt : 3 / 2 ≤ π / (2 * t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hE := Real.exp_pos (-π / (4 * t))
  have e0 : f 0 = (1 - π / (2 * t)) * Real.exp (-π / (4 * t)) := by
    simp only [hf, Int.cast_zero, zero_add]
    rw [show -π * (1 / 2 : ℝ) ^ 2 / t = -π / (4 * t) by ring]
    congr 1
    ring
  have e1 : f (-1) = (1 - π / (2 * t)) * Real.exp (-π / (4 * t)) := by
    simp only [hf]
    push_cast
    rw [show -π * ((-1 : ℝ) + 1 / 2) ^ 2 / t = -π / (4 * t) by ring]
    congr 1
    ring
  have hsum := hfs.neg.sum_le_tsum {0, -1} (fun m _ => hnonneg m)
  rw [Finset.sum_pair (by norm_num), tsum_neg, e0, e1] at hsum
  nlinarith

/-- Montgomery, Lemma 2 for `0 < t < 1`, at `β = 0` and `β = 1/2`. -/
theorem smallT_bounds : ∀ t : ℝ, 0 < t → t < 1 →
    Qser t 0 ≤ (t * Real.sqrt t)⁻¹ ∧
      (t * Real.sqrt t)⁻¹ * Real.exp (-π / (4 * t)) ≤ Qser t (1 / 2) := by
  intro t ht ht1
  have hpos : 0 < (t * Real.sqrt t)⁻¹ := inv_pos.mpr (mul_pos ht (Real.sqrt_pos.mpr ht))
  refine ⟨?_, ?_⟩
  · rw [smallT_Qser_zero ht, smallT_key ht 0]
    calc (t * Real.sqrt t)⁻¹ * smallT_dual t 0 ≤ (t * Real.sqrt t)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (smallT_dual_zero_le ht ht1) hpos.le
      _ = (t * Real.sqrt t)⁻¹ := mul_one _
  · rw [smallT_Qser_half ht]
    have k1 := smallT_key ht (1 / 2)
    have h := mul_le_mul_of_nonneg_left (smallT_dual_half_le ht ht1) hpos.le
    rw [mul_neg] at h
    linarith

end BccSharp.Coulomb.Montgomery
