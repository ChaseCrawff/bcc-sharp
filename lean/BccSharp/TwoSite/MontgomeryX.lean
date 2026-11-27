import BccSharp.TwoSite.MontgomeryBasic

/-!
# Montgomery's minimal theta functions: Lemmas 2 and 4

H. L. Montgomery, *Minimal theta functions*, Glasgow Math. J. 30 (1988) 75–85.

`xMonotone_of` proves the interface `XMonotone` (the paper's Lemma 4, non-strict) from
`Lemma1` and the small-`t` endpoint bounds `SmallT` (part of the paper's Lemma 2).
Montgomery's constants `1 ± 1/3000` are loosened: for `t ≥ 1` we use
`Q(t; 0) ≤ (16π/3) e^{-πt}` and `Q(t; 1/2) ≥ (8π/3) e^{-πt}`. Because `α ≥ 1` and `y ≥ 1/2`
give `αy ≥ 1/2`, the paper's constant `0.868649…` is replaced by the bound `G(αy, 2) ≤ 1`
(`Gsum_two_le`).
-/

set_option autoImplicit false

namespace BccSharp.Coulomb.Montgomery

open Real

/-! ### Numerical lemmas -/

theorem exp_pi_ge_twenty : (20 : ℝ) ≤ Real.exp π := by
  have h1 := Real.exp_one_gt_d9
  have h3 : Real.exp 3 ≤ Real.exp π := Real.exp_le_exp.mpr Real.pi_gt_three.le
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h4 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
  nlinarith [h4]

theorem sq_add_two_le (j : ℕ) : ((j : ℝ) + 2) ^ 2 ≤ 4 * 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ k ih =>
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h : ((k : ℝ) + 1 + 2) ^ 2 ≤ 4 * ((k : ℝ) + 2) ^ 2 := by nlinarith
    calc ((k : ℝ) + 1 + 2) ^ 2 ≤ 4 * ((k : ℝ) + 2) ^ 2 := h
      _ ≤ 4 * (4 * 4 ^ k) := by linarith
      _ = 4 * 4 ^ (k + 1) := by ring

/-- `G(c, s) = Σ_j (j+2)² e^{-πc((j+2)² - s)}`. -/
noncomputable def Gsum (c s : ℝ) : ℝ :=
  ∑' j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - s))

private theorem geom_tsum_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2000) :
    ∑' j : ℕ, r ^ (j + 1) ≤ 1 / 3 := by
  have hr1 : r < 1 := by linarith
  have hs := summable_geometric_of_lt_one h0 hr1
  rw [show (fun j : ℕ => r ^ (j + 1)) = fun j => r * r ^ j by funext j; ring, tsum_mul_left,
    tsum_geometric_of_lt_one h0 hr1]
  rw [mul_inv_le_iff₀ (by linarith)]
  nlinarith

/-- For `c ≥ 1`: `G(c, 1) ≤ 1/3`. -/
theorem Gsum_one_le {c : ℝ} (hc : 1 ≤ c) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 2 * Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 1))) ∧
    Gsum c 1 ≤ 1 / 3 := by
  set r : ℝ := 4 * Real.exp (-(3 * π)) with hr
  have hepi := exp_pi_ge_twenty
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 2000 := by
    have h3 : Real.exp (3 * π) = Real.exp π ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    have : (8000 : ℝ) ≤ Real.exp (3 * π) := by
      rw [h3]; nlinarith [pow_le_pow_left₀ (by norm_num) hepi 3]
    rw [hr, Real.exp_neg]
    rw [show (4 : ℝ) * (Real.exp (3 * π))⁻¹ = 4 / Real.exp (3 * π) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hterm : ∀ j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 1)) ≤
      r ^ (j + 1) := by
    intro j
    have hq : 3 * ((j : ℝ) + 1) ≤ c * (((j : ℝ) + 2) ^ 2 - 1) := by
      have : 3 * ((j : ℝ) + 1) ≤ ((j : ℝ) + 2) ^ 2 - 1 := by nlinarith
      nlinarith [sq_nonneg ((j : ℝ) + 2)]
    have he : Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 1)) ≤ Real.exp (-(3 * π)) ^ (j + 1) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      push_cast
      nlinarith [Real.pi_pos]
    calc ((j : ℝ) + 2) ^ 2 * Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 1))
        ≤ (4 * 4 ^ j) * Real.exp (-(3 * π)) ^ (j + 1) :=
          mul_le_mul (sq_add_two_le j) he (Real.exp_pos _).le (by positivity)
      _ = r ^ (j + 1) := by rw [hr, mul_pow, pow_succ 4 j]; ring
  have hs : Summable (fun j : ℕ => r ^ (j + 1)) :=
    (summable_geometric_of_lt_one hr0 (by linarith)).mul_left r |>.congr fun j => by ring
  have hf : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 2 *
      Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 1))) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hs
  exact ⟨hf, (Summable.tsum_le_tsum hterm hf hs).trans (geom_tsum_le hr0 hr1)⟩

/-- For `c ≥ 1/2`: `G(c, 2) ≤ 1`. -/
theorem Gsum_two_le {c : ℝ} (hc : 1 / 2 ≤ c) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 2 * Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 2))) ∧
    Gsum c 2 ≤ 1 := by
  have hepi := exp_pi_ge_twenty
  set a : ℝ := 4 * Real.exp (-π) with ha
  set r : ℝ := 4 * Real.exp (-(2 * π)) with hr
  have ha0 : 0 ≤ a := by positivity
  have hr0 : 0 ≤ r := by positivity
  have ha1 : a ≤ 1 / 5 := by
    rw [ha, Real.exp_neg, show (4 : ℝ) * (Real.exp π)⁻¹ = 4 / Real.exp π by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hr1 : r ≤ 1 / 100 := by
    have h2 : Real.exp (2 * π) = Real.exp π ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have : (400 : ℝ) ≤ Real.exp (2 * π) := by rw [h2]; nlinarith
    rw [hr, Real.exp_neg, show (4 : ℝ) * (Real.exp (2 * π))⁻¹ = 4 / Real.exp (2 * π) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hterm : ∀ j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 2)) ≤
      a * r ^ j := by
    intro j
    have hq : 2 * (j : ℝ) + 1 ≤ c * (((j : ℝ) + 2) ^ 2 - 2) := by
      have : 2 * (2 * (j : ℝ) + 1) ≤ ((j : ℝ) + 2) ^ 2 - 2 := by nlinarith [sq_nonneg (j : ℝ)]
      nlinarith [sq_nonneg ((j : ℝ) + 2)]
    have he : Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 2)) ≤
        Real.exp (-π) * Real.exp (-(2 * π)) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [Real.pi_pos]
    calc ((j : ℝ) + 2) ^ 2 * Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 2))
        ≤ (4 * 4 ^ j) * (Real.exp (-π) * Real.exp (-(2 * π)) ^ j) :=
          mul_le_mul (sq_add_two_le j) he (Real.exp_pos _).le (by positivity)
      _ = a * r ^ j := by rw [ha, hr, mul_pow]; ring
  have hs : Summable (fun j : ℕ => a * r ^ j) :=
    (summable_geometric_of_lt_one hr0 (by linarith)).mul_left a
  have hf : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 2 *
      Real.exp (-π * c * (((j : ℝ) + 2) ^ 2 - 2))) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hs
  refine ⟨hf, (Summable.tsum_le_tsum hterm hf hs).trans ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
  rw [mul_inv_le_iff₀ (by linarith)]
  nlinarith

/-! ### `Q` between its endpoint values (Lemma 1 and the shape of `Q`) -/

theorem Qser_cos_congr (t : ℝ) {β β' : ℝ}
    (h : Real.cos (2 * π * β) = Real.cos (2 * π * β')) : Qser t β = Qser t β' := by
  unfold Qser; rw [h]

theorem Qser_neg (t β : ℝ) : Qser t (-β) = Qser t β := by
  apply Qser_cos_congr
  rw [show 2 * π * -β = -(2 * π * β) by ring, Real.cos_neg]

theorem exists_Icc_Qser (t β : ℝ) : ∃ β' ∈ Set.Icc (0:ℝ) (1 / 2), Qser t β = Qser t β' := by
  refine ⟨Real.arccos (Real.cos (2 * π * β)) / (2 * π), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (Real.arccos_nonneg _) (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    linarith [Real.arccos_le_pi (Real.cos (2 * π * β))]
  · apply Qser_cos_congr
    rw [show 2 * π * (Real.arccos (Real.cos (2 * π * β)) / (2 * π)) =
      Real.arccos (Real.cos (2 * π * β)) by field_simp,
      Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)]

theorem Qser_between (h1 : Lemma1) {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Qser t (1 / 2) ≤ Qser t β ∧ Qser t β ≤ Qser t 0 := by
  obtain ⟨β', hβ', e⟩ := exists_Icc_Qser t β
  rw [e]
  have hA := h1 t ht
  exact ⟨hA hβ' ⟨by norm_num, le_rfl⟩ hβ'.2, hA ⟨le_rfl, by norm_num⟩ hβ' hβ'.1⟩

private theorem summable_sq_exp_two {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * t)) := by
  have h := (summable_sq_exp_succ ht).comp_injective (add_left_injective 1)
  refine h.congr fun j => ?_
  simp only [Function.comp_apply]
  push_cast
  ring_nf

theorem Qser_zero_eq {t : ℝ} (ht : 0 < t) :
    Qser t 0 = 4 * π * (Real.exp (-π * t) +
      ∑' j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * t)) := by
  unfold Qser
  have hs := summable_Qser_term ht 0
  rw [hs.tsum_eq_zero_add]
  congr 2
  · simp
  · refine tsum_congr fun j => ?_
    rw [mul_zero, Real.cos_zero, Polynomial.Chebyshev.U_eval_one]
    push_cast
    ring_nf

theorem Qser_half_ge {t : ℝ} (ht : 0 < t) :
    4 * π * (Real.exp (-π * t) -
      ∑' j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * t)) ≤ Qser t (1 / 2) := by
  unfold Qser
  have hs := summable_Qser_term ht (1 / 2)
  rw [hs.tsum_eq_zero_add]
  have h0 : ((((0 : ℕ) : ℝ) + 1) * Real.exp (-π * (((0 : ℕ) : ℝ) + 1) ^ 2 * t) *
      (Polynomial.Chebyshev.U ℝ ((0 : ℕ) : ℤ)).eval (Real.cos (2 * π * (1 / 2)))) =
      Real.exp (-π * t) := by simp
  rw [h0]
  have htail : -(∑' j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * t)) ≤
      ∑' j : ℕ, (((j + 1 : ℕ) : ℝ) + 1) * Real.exp (-π * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 * t) *
        (Polynomial.Chebyshev.U ℝ ((j + 1 : ℕ) : ℤ)).eval (Real.cos (2 * π * (1 / 2))) := by
    rw [← tsum_neg]
    refine Summable.tsum_le_tsum (fun j => ?_) (summable_sq_exp_two ht).neg
      (hs.comp_injective (add_left_injective 1))
    have hU := abs_U_eval_cos_le (j + 1) (2 * π * (1 / 2))
    have hU' := neg_abs_le ((Polynomial.Chebyshev.U ℝ ((j + 1 : ℕ) : ℤ)).eval
      (Real.cos (2 * π * (1 / 2))))
    push_cast at hU hU' ⊢
    have hp : 0 ≤ ((j : ℝ) + 1 + 1) * Real.exp (-π * ((j : ℝ) + 1 + 1) ^ 2 * t) := by positivity
    have e : ((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * t) =
        ((j : ℝ) + 1 + 1) * Real.exp (-π * ((j : ℝ) + 1 + 1) ^ 2 * t) * ((j : ℝ) + 1 + 1) := by
      ring_nf
    rw [e, neg_mul_eq_mul_neg]
    exact mul_le_mul_of_nonneg_left (by linarith) hp
  nlinarith [Real.pi_pos]

/-- Lemma 2 for `t ≥ 1` (loosened constants). -/
theorem Qser_bounds_large (h1 : Lemma1) {t : ℝ} (ht : 1 ≤ t) (β : ℝ) :
    8 * π / 3 * Real.exp (-π * t) ≤ Qser t β ∧ Qser t β ≤ 16 * π / 3 * Real.exp (-π * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  obtain ⟨hGs, hG⟩ := Gsum_one_le ht
  have hsum : ∑' j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * t) =
      Real.exp (-π * t) * Gsum t 1 := by
    unfold Gsum
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hE := Real.exp_pos (-π * t)
  obtain ⟨hlo, hhi⟩ := Qser_between h1 ht0 β
  constructor
  · refine le_trans ?_ ((Qser_half_ge ht0).trans hlo)
    rw [hsum]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hG hE.le]
  · refine hhi.trans (le_of_eq_of_le (Qser_zero_eq ht0) ?_)
    rw [hsum]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hG hE.le]

/-! ### Lemma 4 -/

/-- An even series over `ℤ` with zero central term is twice its positive half. -/
theorem tsum_int_even {g : ℤ → ℝ} (hg : Summable g) (h0 : g 0 = 0)
    (heven : ∀ n : ℕ, g (-((n : ℤ) + 1)) = g ((n : ℤ) + 1)) :
    ∑' n : ℤ, g n = 2 * ∑' j : ℕ, g ((j : ℤ) + 1) := by
  have hnat : Summable (fun n : ℕ => g n) := hg.comp_injective Nat.cast_injective
  have hnat' : Summable (fun n : ℕ => g (-(n + 1))) := by
    refine hg.comp_injective (i := fun n : ℕ => (-((n : ℤ) + 1))) ?_
    intro a b hab; simpa using hab
  rw [tsum_of_nat_of_neg_add_one hnat hnat', hnat.tsum_eq_zero_add]
  have e1 : (∑' n : ℕ, g ((n + 1 : ℕ) : ℤ)) = ∑' n : ℕ, g ((n : ℤ) + 1) := by
    congr 1
  have e2 : (∑' n : ℕ, g (-((n : ℤ) + 1))) = ∑' n : ℕ, g ((n : ℤ) + 1) :=
    tsum_congr heven
  rw [e1, e2, Nat.cast_zero, h0]
  ring

/-- Bounds `A ≤ Q(t; ·) ≤ B` with `B · G(c, 1) ≤ A`, for `α ≥ 1`, `y ≥ 1/2`, `t = y/α`, `c = αy`. -/
private theorem lemma4_bounds (h1 : Lemma1) (hS : SmallT) {α y : ℝ} (hα : 1 ≤ α)
    (hy : 1 / 2 ≤ y) :
    ∃ A B : ℝ, 0 < A ∧ B * Gsum (α * y) 1 ≤ A ∧
      ∀ β, A ≤ Qser (y / α) β ∧ Qser (y / α) β ≤ B := by
  have hα0 : 0 < α := by linarith
  have hy0 : 0 < y := by linarith
  have ht : 0 < y / α := div_pos hy0 hα0
  rcases le_or_gt 1 (y / α) with h | h
  · refine ⟨8 * π / 3 * Real.exp (-π * (y / α)), 16 * π / 3 * Real.exp (-π * (y / α)),
      by positivity, ?_, fun β => Qser_bounds_large h1 h β⟩
    have hαy : α ≤ y := by rwa [le_div_iff₀ hα0, one_mul] at h
    have hc : 1 ≤ α * y := by nlinarith
    have hG := (Gsum_one_le hc).2
    have hE := Real.exp_pos (-π * (y / α))
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hG (by positivity :
      (0:ℝ) ≤ 16 * π / 3 * Real.exp (-π * (y / α)))]
  · set t := y / α with htd
    refine ⟨(t * Real.sqrt t)⁻¹ * Real.exp (-π / (4 * t)), (t * Real.sqrt t)⁻¹, by positivity,
      ?_, fun β => ?_⟩
    · have hc : 1 / 2 ≤ α * y := by nlinarith
      obtain ⟨-, hG2⟩ := Gsum_two_le hc
      have hsplit : Gsum (α * y) 1 = Real.exp (-π * (α * y)) * Gsum (α * y) 2 := by
        unfold Gsum
        rw [← tsum_mul_left]
        refine tsum_congr fun j => ?_
        have e : Real.exp (-π * (α * y) * (((j : ℝ) + 2) ^ 2 - 1)) =
            Real.exp (-π * (α * y)) * Real.exp (-π * (α * y) * (((j : ℝ) + 2) ^ 2 - 2)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e]
        ring
      have hcmp : Real.exp (-π * (α * y)) ≤ Real.exp (-π / (4 * t)) := by
        rw [Real.exp_le_exp, htd]
        have hq : α / (4 * y) ≤ α * y := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        have e : -π / (4 * (y / α)) = -π * (α / (4 * y)) := by field_simp
        rw [e]
        nlinarith [Real.pi_pos]
      rw [hsplit]
      have hB : 0 ≤ (t * Real.sqrt t)⁻¹ := by positivity
      calc (t * Real.sqrt t)⁻¹ * (Real.exp (-π * (α * y)) * Gsum (α * y) 2)
          ≤ (t * Real.sqrt t)⁻¹ * (Real.exp (-π * (α * y)) * 1) := by
            gcongr
        _ ≤ (t * Real.sqrt t)⁻¹ * Real.exp (-π / (4 * t)) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hcmp hB
    · obtain ⟨hlo, hhi⟩ := Qser_between h1 ht β
      obtain ⟨h0, hhalf⟩ := hS t ht h
      exact ⟨hhalf.trans hlo, hhi.trans h0⟩

/-- Montgomery, Lemma 4 (non-strict), from Lemma 1 and the small-`t` bounds. -/
theorem xMonotone_of (h1 : Lemma1) (hS : SmallT) : XMonotone := by
  suffices H : ∀ α : ℝ, 1 ≤ α → ∀ y : ℝ, 1 / 2 ≤ y →
      AntitoneOn (fun x => theta2 α x y) (Set.Icc 0 (1 / 2)) by
    intro α hα y hy
    rcases le_or_gt 1 α with h | h
    · exact H α h y hy
    · have hinv : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr h.le
      have hy0 : 0 < y := by linarith
      have e : ∀ x, theta2 α x y = α⁻¹ * theta2 α⁻¹ x y := by
        intro x
        have := duality α⁻¹ (inv_pos.mpr hα) x y hy0
        rwa [inv_inv] at this
      intro a ha b hb hab
      simp only [e]
      exact mul_le_mul_of_nonneg_left (H α⁻¹ hinv y hy ha hb hab) (inv_nonneg.mpr hα.le)
  intro α hα y hy
  have hα0 : 0 < α := by linarith
  have hy0 : 0 < y := by linarith
  have ht : 0 < y / α := div_pos hy0 hα0
  have hc0 : 0 < α * y := mul_pos hα0 hy0
  obtain ⟨A, B, hA0, hAB, hQ⟩ := lemma4_bounds h1 hS hα hy
  set t := y / α with htd
  set Φ : ℝ → ℝ := fun x => ∑' n : ℤ, Real.exp (-π * α * y * (n : ℝ) ^ 2) * theta1 t (n * x)
    with hΦ
  have hrep : ∀ x, theta2 α x y = Real.sqrt (y / α) * Φ x := fun x => unfold13 α hα0 x y hy0
  have hB0 : 0 ≤ B := le_trans hA0.le ((hQ 0).1.trans (hQ 0).2)
  have hDb : ∀ β, |-(Real.sin (2 * π * β) * Qser t β)| ≤ B := by
    intro β
    have hQ0 : 0 ≤ Qser t β := le_trans hA0.le (hQ β).1
    rw [abs_neg, abs_mul, abs_of_nonneg hQ0]
    calc |Real.sin (2 * π * β)| * Qser t β ≤ 1 * Qser t β :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) hQ0
      _ ≤ B := by linarith [(hQ β).2]
  have hu : Summable (fun n : ℤ => Real.exp (-π * α * y * (n : ℝ) ^ 2) * (B * |(n : ℝ)|)) := by
    have h := (summable_pow_mul_jacobiTheta₂_term_bound 0 hc0 1).mul_left B
    refine h.congr fun n => ?_
    simp only [pow_one, mul_zero, zero_mul, sub_zero, Int.cast_abs]
    ring_nf
  have hderiv : ∀ x, HasDerivAt Φ (∑' n : ℤ, Real.exp (-π * α * y * (n : ℝ) ^ 2) *
      (-(Real.sin (2 * π * (n * x)) * Qser t (n * x)) * n)) x := by
    intro x
    rw [hΦ]
    refine hasDerivAt_tsum
      (g := fun (n : ℤ) (z : ℝ) => Real.exp (-π * α * y * (n : ℝ) ^ 2) * theta1 t (n * z))
      (g' := fun (n : ℤ) (z : ℝ) => Real.exp (-π * α * y * (n : ℝ) ^ 2) *
        (-(Real.sin (2 * π * (n * z)) * Qser t (n * z)) * n))
      (y₀ := 0) hu (fun n x => ?_) (fun n x => ?_) ?_ x
    · have hin : HasDerivAt (fun z : ℝ => (n : ℝ) * z) (n : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (n : ℝ)
      exact ((theta1_hasDerivAt t ht ((n : ℝ) * x)).comp x hin).const_mul _
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      gcongr
      · exact hDb _
    · have h := (summable_exp_neg_mul_int_sq (c := π * α * y) (by positivity)).mul_right
        (theta1 t 0)
      refine h.congr fun n => ?_
      simp only [mul_zero]
      ring_nf
  have hsign : ∀ x ∈ Set.Ioo (0:ℝ) (1 / 2), (∑' n : ℤ, Real.exp (-π * α * y * (n : ℝ) ^ 2) *
      (-(Real.sin (2 * π * (n * x)) * Qser t (n * x)) * n)) ≤ 0 := by
    intro x hx
    have hs : 0 < Real.sin (2 * π * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, hx.1]) (by nlinarith [Real.pi_pos, hx.2])
    set b : ℤ → ℝ := fun n => (n : ℝ) * Real.exp (-π * α * y * (n : ℝ) ^ 2) *
      Real.sin (2 * π * (n * x)) * Qser t (n * x) with hbd
    have hbbound : ∀ n : ℤ, ‖b n‖ ≤ Real.exp (-π * α * y * (n : ℝ) ^ 2) * (B * |(n : ℝ)|) := by
      intro n
      have h := hDb ((n : ℝ) * x)
      rw [abs_neg] at h
      rw [Real.norm_eq_abs, hbd]
      calc |(n : ℝ) * Real.exp (-π * α * y * (n : ℝ) ^ 2) * Real.sin (2 * π * (n * x)) *
            Qser t (n * x)|
          = Real.exp (-π * α * y * (n : ℝ) ^ 2) *
            (|Real.sin (2 * π * (n * x)) * Qser t (n * x)| * |(n : ℝ)|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]; ring
        _ ≤ Real.exp (-π * α * y * (n : ℝ) ^ 2) * (B * |(n : ℝ)|) := by gcongr
    have hbs : Summable b := Summable.of_norm_bounded hu hbbound
    have hrw : (fun n : ℤ => Real.exp (-π * α * y * (n : ℝ) ^ 2) *
        (-(Real.sin (2 * π * (n * x)) * Qser t (n * x)) * n)) = fun n => -b n := by
      funext n; simp only [hbd]; ring
    rw [hrw, tsum_neg, neg_nonpos]
    have hb0 : b 0 = 0 := by simp [hbd]
    have hbeven : ∀ n : ℕ, b (-((n : ℤ) + 1)) = b ((n : ℤ) + 1) := by
      intro n
      simp only [hbd]
      push_cast
      rw [show (2 * π * (-((n : ℝ) + 1) * x)) = -(2 * π * (((n : ℝ) + 1) * x)) by ring,
        Real.sin_neg, show (-((n : ℝ) + 1) * x) = -(((n : ℝ) + 1) * x) by ring, Qser_neg]
      ring_nf
    rw [tsum_int_even hbs hb0 hbeven]
    -- the positive half
    have hbn : Summable (fun j : ℕ => b ((j : ℤ) + 1)) := by
      refine hbs.comp_injective (i := fun j : ℕ => (j : ℤ) + 1) ?_
      intro a c h; simpa using h
    rw [hbn.tsum_eq_zero_add]
    set E : ℝ := Real.exp (-π * (α * y)) with hE
    have hsum2 := summable_sq_exp_two hc0
    have hterm : ∀ j : ℕ, -(Real.sin (2 * π * x) * B *
        (((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * (α * y)))) ≤
        b (((j + 1 : ℕ) : ℤ) + 1) := by
      intro j
      have hsj := abs_sin_nat_mul_le (j + 2) (2 * π * x)
      have hQj := hQ ((((j + 1 : ℕ) : ℤ) + 1 : ℤ) * x)
      have hQnn : 0 ≤ Qser t ((((j + 1 : ℕ) : ℤ) + 1 : ℤ) * x) := le_trans hA0.le hQj.1
      simp only [hbd]
      push_cast at hsj hQj hQnn ⊢
      have e1 : 2 * π * (((j : ℝ) + 1 + 1) * x) = ((j : ℝ) + 2) * (2 * π * x) := by ring
      rw [e1]
      have hsin : -(((j : ℝ) + 2) * Real.sin (2 * π * x)) ≤ Real.sin (((j : ℝ) + 2) * (2 * π * x)) := by
        have := neg_abs_le (Real.sin (((j : ℝ) + 2) * (2 * π * x)))
        rw [abs_of_pos hs] at hsj
        linarith
      have hexp : Real.exp (-π * α * y * ((j : ℝ) + 1 + 1) ^ 2) =
          Real.exp (-π * ((j : ℝ) + 2) ^ 2 * (α * y)) := by congr 1; ring
      rw [hexp]
      set Qj := Qser t (((j : ℝ) + 1 + 1) * x)
      have hE2 := Real.exp_pos (-π * ((j : ℝ) + 2) ^ 2 * (α * y))
      have hpos : 0 ≤ ((j : ℝ) + 1 + 1) * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * (α * y)) := by
        positivity
      set P := ((j : ℝ) + 1 + 1) * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * (α * y)) with hP
      set S := Real.sin (((j : ℝ) + 2) * (2 * π * x)) with hS'
      have hPQ : 0 ≤ P * Qj := mul_nonneg hpos hQnn
      have step1 : P * (-(((j : ℝ) + 2) * Real.sin (2 * π * x))) * Qj ≤ P * S * Qj := by
        have := mul_le_mul_of_nonneg_left hsin hPQ
        nlinarith
      have step2 : P * (-(((j : ℝ) + 2) * Real.sin (2 * π * x))) * B ≤
          P * (-(((j : ℝ) + 2) * Real.sin (2 * π * x))) * Qj := by
        have hk : 0 ≤ P * (((j : ℝ) + 2) * Real.sin (2 * π * x)) := by positivity
        have := mul_le_mul_of_nonneg_left hQj.2 hk
        nlinarith
      calc -(Real.sin (2 * π * x) * B * (((j : ℝ) + 2) ^ 2 *
            Real.exp (-π * ((j : ℝ) + 2) ^ 2 * (α * y))))
          = P * (-(((j : ℝ) + 2) * Real.sin (2 * π * x))) * B := by rw [hP]; ring
        _ ≤ P * (-(((j : ℝ) + 2) * Real.sin (2 * π * x))) * Qj := step2
        _ ≤ P * S * Qj := step1
    have htail := Summable.tsum_le_tsum hterm ((hsum2.mul_left (Real.sin (2 * π * x) * B)).neg)
      (hbn.comp_injective (add_left_injective 1))
    rw [tsum_neg, tsum_mul_left] at htail
    have hfirst : E * Real.sin (2 * π * x) * A ≤ b (((0 : ℕ) : ℤ) + 1) := by
      have e : b (((0 : ℕ) : ℤ) + 1) = E * Real.sin (2 * π * x) * Qser t x := by
        simp only [hbd, hE]
        push_cast
        simp only [one_pow, mul_one, one_mul]
        rw [show -π * α * y = -π * (α * y) by ring]
      rw [e]
      exact mul_le_mul_of_nonneg_left (hQ x).1 (mul_pos (Real.exp_pos _) hs).le
    have hG : ∑' j : ℕ, ((j : ℝ) + 2) ^ 2 * Real.exp (-π * ((j : ℝ) + 2) ^ 2 * (α * y)) =
        E * Gsum (α * y) 1 := by
      unfold Gsum
      rw [hE, ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      have e : Real.exp (-π * ((j : ℝ) + 2) ^ 2 * (α * y)) =
          Real.exp (-π * (α * y)) * Real.exp (-π * (α * y) * (((j : ℝ) + 2) ^ 2 - 1)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e]
      ring
    rw [hG] at htail
    have hEp : 0 < E := Real.exp_pos _
    have hkey : E * Real.sin (2 * π * x) * A - Real.sin (2 * π * x) * B * (E * Gsum (α * y) 1) ≥ 0 := by
      have := mul_le_mul_of_nonneg_left hAB (mul_pos hEp hs).le
      nlinarith
    nlinarith
  -- monotonicity of Φ, then of θ
  have hantiΦ : AntitoneOn Φ (Set.Icc 0 (1 / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2))
    · exact fun x _ => (hderiv x).continuousAt.continuousWithinAt
    · exact fun x _ => (hderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      exact hsign x hx
  intro a ha b hb hab
  show theta2 α b y ≤ theta2 α a y
  rw [hrep a, hrep b]
  exact mul_le_mul_of_nonneg_left (hantiΦ ha hb hab) (Real.sqrt_nonneg _)

/-! ### Reduction to the fundamental domain and Theorem 1 -/

open scoped MatrixGroups

theorem theta2_eq_normSq (α : ℝ) (z : ℂ) :
    theta2 α z.re z.im =
      ∑' p : ℤ × ℤ, Real.exp (-π * α * Complex.normSq ((p.1 : ℂ) + p.2 * z) / z.im) := by
  unfold theta2
  refine tsum_congr fun p => ?_
  congr 1
  rw [Complex.normSq_apply]
  simp
  ring

theorem theta2_neg_x (α x y : ℝ) : theta2 α (-x) y = theta2 α x y := by
  unfold theta2
  conv_rhs => rw [← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map_fst, id_eq,
    Prod.map_snd, Int.cast_neg]
  ring_nf

/-- `θ(α; ·)` is invariant under the modular group. -/
theorem theta2_smul (α : ℝ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    theta2 α (g • z).re (g • z).im = theta2 α z.re z.im := by
  have h1 := theta2_eq_normSq α ((g • z : UpperHalfPlane) : ℂ)
  have h2 := theta2_eq_normSq α (z : ℂ)
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1 h2
  rw [h1, h2]
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rwa [Matrix.det_fin_two] at h
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 * g 1 1 + p.2 * g 0 1, p.1 * g 1 0 + p.2 * g 0 0)
      invFun := fun q => (q.1 * g 0 0 - q.2 * g 0 1, -(q.1 * g 1 0) + q.2 * g 1 1)
      left_inv := fun p => Prod.ext (by simp only; linear_combination p.1 * hdet)
        (by simp only; linear_combination p.2 * hdet)
      right_inv := fun q => Prod.ext (by simp only; linear_combination q.1 * hdet)
        (by simp only; linear_combination q.2 * hdet) }
  conv_rhs => rw [← e.tsum_eq]
  refine tsum_congr fun p => ?_
  congr 1
  have hden : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) z
    rwa [← ModularGroup.denom_apply]
  have hw : ((g • z : UpperHalfPlane) : ℂ) =
      ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have him : (g • z).im = z.im / Complex.normSq ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  have hnum : (p.1 : ℂ) + p.2 * ((g • z : UpperHalfPlane) : ℂ) =
      (((e p).1 : ℂ) + (e p).2 * z) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) := by
    rw [hw, eq_div_iff hden, add_mul, mul_assoc, div_mul_cancel₀ _ hden]
    simp only [e, Equiv.coe_fn_mk]
    push_cast
    ring
  have hns : Complex.normSq ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.mpr hden).ne'
  rw [hnum, Complex.normSq_div, him, ← mul_div_assoc, div_div_div_cancel_right₀ hns]

/-- Montgomery, Theorem 1 (the inequality), from Lemma 4 and Lemma 7 on `x = 1/2`. -/
theorem theorem1_of (hX : XMonotone) (hY : YMonotoneHalf) : Theorem1 := by
  intro α hα x y hy
  let z : UpperHalfPlane := ⟨⟨x, y⟩, hy⟩
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hz : theta2 α x y = theta2 α (g • z).re (g • z).im := (theta2_smul α g z).symm
  rw [hz]
  set w := g • z with hwdef
  obtain ⟨hn, hre⟩ := hg
  have hwim : 0 < w.im := w.im_pos
  have hnorm : 1 ≤ w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply] at hn
    simpa [sq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hn
  have hre2 : w.re ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hre
    nlinarith
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs3 := Real.sqrt_nonneg 3
  have hsq3 : Real.sqrt 3 / 2 ≤ w.im := by
    by_contra hlt
    have hlt' := not_le.mp hlt
    nlinarith
  have hyhalf : 1 / 2 ≤ w.im := by
    have : 1 ≤ Real.sqrt 3 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hrefl : theta2 α w.re w.im = theta2 α |w.re| w.im := by
    rcases abs_cases w.re with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, theta2_neg_x]
  rw [hrefl]
  have hu0 : 0 ≤ |w.re| := abs_nonneg _
  calc thetaHex α = theta2 α (1 / 2) (Real.sqrt 3 / 2) := rfl
    _ ≤ theta2 α (1 / 2) w.im := hY α hα (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hsq3) hsq3
    _ ≤ theta2 α |w.re| w.im :=
        hX α hα w.im hyhalf ⟨hu0, hre⟩ ⟨by norm_num, le_rfl⟩ hre

end BccSharp.Coulomb.Montgomery
