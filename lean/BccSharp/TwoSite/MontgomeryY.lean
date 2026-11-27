import BccSharp.TwoSite.MontgomeryDefs

/-!
# Montgomery, Lemmas 5–7 on the line `x = 1/2`

H. L. Montgomery, *Minimal theta functions*, Glasgow Math. J. 30 (1988) 75–85.

Main result: `yMonotoneHalf_of_duality : Duality → YMonotoneHalf`, i.e.
`θ(α; 1/2, ·)` increases on `[√3/2, ∞)` for every `α > 0`.

Write `h(y) = θ(α; 1/2, y) = Σ e`, with summand `e = exp(-πα (u² + n²y²)/y)`, `u = m + n/2`
(`ee`), and `G = y² h' = Σ πα (u² - n²y²) e` (`gt`).

* Termwise differentiation (`hasDerivAt_tsum_of_isPreconnected`) on `(3/5, ∞)`, with the
  majorant `(1 + m² + n²)² e^{-κ(m²+n²)}` (`summable_majorant`), gives `h' = G / y²` and
  `G' = Σ (π²α²(u² - n²y²)²/y² - 2παn²y) e = y² (h'' + (2/y) h')`.
* Lemma 5 (`key_ineq`), for `α ≥ 1`, `y ≥ √3/2`: `G' ≥ 0`. The positive part is bounded below
  by its four terms `(±1, 0)`, `(0, ±1)` (`four_terms`); the negative part `2παy Σ n² e` is
  bounded above row by row (`sum_n2_bound`): the rows `n = ±1` by `2e^{-c/4}/(1 - e^{-2c})`,
  every other row by `2/(1 - e^{-c/4})` (`c = πα/y`), and the weights `n² e^{-παn²y}`,
  `|n| ≥ 2`, by a geometric tail. The resulting scalar inequality (`scalar_key`) is proved
  with `e^t ≥ 1 + t`, `1/(1 - e^{-x}) ≤ 1 + 1/x`, `e^7 ≥ 1000`, `π > 3.14` and a quintic
  polynomial inequality on `y ≥ 0.866` (`poly_core`).
* Corner (`corner`): `G(√3/2) = 0`, by the order-3 symmetry `(m, n) ↦ (-n, m + n)` of
  `m² + mn + n²` (`rot`).
* Lemma 6: `G` is monotone on `[√3/2, ∞)`, hence `G ≥ 0` there, hence `h' ≥ 0` and `h` is
  monotone (`monotone_of_one_le`).
* `α < 1` follows from `α⁻¹ > 1` and `θ(α) = α⁻¹ θ(α⁻¹)` (the hypothesis `Duality`).
-/

set_option autoImplicit false

namespace BccSharp.Coulomb.Montgomery

open Real

namespace YHalf

/-! ### Geometric comparison sums -/

private lemma geom_bound_nat {f : ℕ → ℝ} {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf0 : ∀ j, 0 ≤ f j) (hf : ∀ j, f j ≤ C * r ^ j) :
    Summable f ∧ ∑' j, f j ≤ C / (1 - r) := by
  have hg : Summable (fun j : ℕ => C * r ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hf hg
  refine ⟨hs, ?_⟩
  calc ∑' j, f j ≤ ∑' j, C * r ^ j := hs.tsum_le_tsum hf hg
    _ = C / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

private lemma geom_bound_int {f : ℤ → ℝ} {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf0 : ∀ n, 0 ≤ f n) (hfp : ∀ j : ℕ, f j ≤ C * r ^ j)
    (hfn : ∀ j : ℕ, f (-((j : ℤ) + 1)) ≤ C * r ^ j) :
    Summable f ∧ ∑' n, f n ≤ 2 * C / (1 - r) := by
  obtain ⟨h1, h1'⟩ := geom_bound_nat (f := fun j : ℕ => f j) hr0 hr1 (fun j => hf0 _) hfp
  obtain ⟨h2, h2'⟩ := geom_bound_nat (f := fun j : ℕ => f (-((j : ℤ) + 1))) hr0 hr1
    (fun j => hf0 _) hfn
  refine ⟨Summable.of_nat_of_neg_add_one h1 h2, ?_⟩
  rw [tsum_of_nat_of_neg_add_one h1 h2]
  calc _ ≤ C / (1 - r) + C / (1 - r) := add_le_add h1' h2'
    _ = 2 * C / (1 - r) := by ring

/-! ### A summable Gaussian majorant on `ℤ²` -/

/-- `T(p) = m² + n²`. -/
private noncomputable def tt (p : ℤ × ℤ) : ℝ := (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2

private lemma tt_nonneg (p : ℤ × ℤ) : 0 ≤ tt p := by unfold tt; positivity

private lemma summable_majorant {κ : ℝ} (hκ : 0 < κ) :
    Summable (fun p : ℤ × ℤ => (1 + tt p) ^ 2 * Real.exp (-κ * tt p)) := by
  have h1 := summable_exp_neg_mul_int_sq (c := κ / 2) (by positivity)
  have h2 : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(κ / 2) * (p.1 : ℝ) ^ 2) * Real.exp (-(κ / 2) * (p.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (h2.mul_left (32 / κ ^ 2 * Real.exp (κ / 4)))
  have hT0 := tt_nonneg p
  have hs := Real.quadratic_le_exp_of_nonneg (x := κ * (1 + tt p) / 4) (by positivity)
  have key : (1 + tt p) ^ 2 ≤ 32 / κ ^ 2 * Real.exp (κ * (1 + tt p) / 4) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (κ * (1 + tt p) / 4)]
  have hsplit : Real.exp (κ * (1 + tt p) / 4) * Real.exp (-κ * tt p)
      = Real.exp (κ / 4) * Real.exp (-(3 * κ / 4) * tt p) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hmono : Real.exp (-(3 * κ / 4) * tt p)
      ≤ Real.exp (-(κ / 2) * (p.1 : ℝ) ^ 2) * Real.exp (-(κ / 2) * (p.2 : ℝ) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold tt
    nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2 : ℝ)]
  calc (1 + tt p) ^ 2 * Real.exp (-κ * tt p)
      ≤ 32 / κ ^ 2 * Real.exp (κ * (1 + tt p) / 4) * Real.exp (-κ * tt p) := by
        gcongr
    _ = 32 / κ ^ 2 * Real.exp (κ / 4) * Real.exp (-(3 * κ / 4) * tt p) := by
        rw [mul_assoc, hsplit]; ring
    _ ≤ 32 / κ ^ 2 * Real.exp (κ / 4) *
        (Real.exp (-(κ / 2) * (p.1 : ℝ) ^ 2) * Real.exp (-(κ / 2) * (p.2 : ℝ) ^ 2)) := by
        gcongr

/-! ### The summand of `θ(α; 1/2, y)` and its `y`-derivatives -/

/-- `u = m + n/2`. -/
private noncomputable def uu (p : ℤ × ℤ) : ℝ := (p.1 : ℝ) + p.2 * (1 / 2)

/-- The summand of `theta2 α (1/2) y`. -/
private noncomputable def ee (α y : ℝ) (p : ℤ × ℤ) : ℝ :=
  Real.exp (-π * α * (uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y)

private lemma theta2_half_eq (α y : ℝ) : theta2 α (1 / 2) y = ∑' p, ee α y p := rfl

private lemma ee_pos (α y : ℝ) (p : ℤ × ℤ) : 0 < ee α y p := Real.exp_pos _

/-- `πα(u² - n²y²)`: the summand of `y² ∂_y θ`, divided by the summand of `θ`. -/
private noncomputable def ww (α y : ℝ) (p : ℤ × ℤ) : ℝ := π * α * (uu p ^ 2 - ((p.2 : ℝ) * y) ^ 2)

/-- `∂_y` of the summand. -/
private noncomputable def d1 (α y : ℝ) (p : ℤ × ℤ) : ℝ := ee α y p * (ww α y p / y ^ 2)

/-- `y² ∂_y` of the summand. -/
private noncomputable def gt (α y : ℝ) (p : ℤ × ℤ) : ℝ := ee α y p * ww α y p

/-- `∂_y (y² ∂_y)` of the summand. -/
private noncomputable def d2 (α y : ℝ) (p : ℤ × ℤ) : ℝ :=
  ee α y p * (ww α y p ^ 2 / y ^ 2 - 2 * π * α * (p.2 : ℝ) ^ 2 * y)

private lemma hasDerivAt_phase (α : ℝ) (p : ℤ × ℤ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => -π * α * (uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y) (ww α y p / y ^ 2) y := by
  have h0 : HasDerivAt (fun y : ℝ => (p.2 : ℝ) * y) (p.2 : ℝ) y := by
    simpa using (hasDerivAt_id' (x := y)).const_mul (p.2 : ℝ)
  have h1 : HasDerivAt (fun y => -π * α * (uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2))
      (-π * α * (2 * ((p.2 : ℝ) * y) * (p.2 : ℝ))) y := by
    have h2 := ((h0.fun_pow 2).const_add (uu p ^ 2)).const_mul (-π * α)
    convert h2 using 1
    push_cast
    ring
  have h3 := h1.fun_div (hasDerivAt_id' (x := y)) hy
  convert h3 using 1
  unfold ww
  ring

private lemma hasDerivAt_ee (α : ℝ) (p : ℤ × ℤ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => ee α y p) (d1 α y p) y :=
  (hasDerivAt_phase α p hy).exp

private lemma hasDerivAt_ww (α : ℝ) (p : ℤ × ℤ) (y : ℝ) :
    HasDerivAt (fun y => ww α y p) (-(2 * π * α * (p.2 : ℝ) ^ 2 * y)) y := by
  have h0 : HasDerivAt (fun y : ℝ => (p.2 : ℝ) * y) (p.2 : ℝ) y := by
    simpa using (hasDerivAt_id' (x := y)).const_mul (p.2 : ℝ)
  have h2 := ((h0.fun_pow 2).const_sub (uu p ^ 2)).const_mul (π * α)
  unfold ww
  convert h2 using 1
  push_cast
  ring

private lemma hasDerivAt_gt (α : ℝ) (p : ℤ × ℤ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => gt α y p) (d2 α y p) y := by
  have h := (hasDerivAt_ee α p hy).fun_mul (hasDerivAt_ww α p y)
  unfold gt
  convert h using 1
  unfold d2 d1
  ring

/-! ### Majorants on `3/5 < y < Y` -/

private lemma quad_lower (p : ℤ × ℤ) {y : ℝ} (hy : 1 / 3 ≤ y ^ 2) :
    tt p / 4 ≤ uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2 := by
  unfold tt uu
  nlinarith [sq_nonneg ((p.1 : ℝ) + 2 / 3 * p.2),
    mul_nonneg (sq_nonneg (p.2 : ℝ)) (sub_nonneg.mpr hy)]

private lemma quad_upper (p : ℤ × ℤ) {y Y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y) :
    uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2 ≤ (2 + Y ^ 2) * tt p := by
  have hy2 : y ^ 2 ≤ Y ^ 2 := by nlinarith
  unfold tt uu
  nlinarith [sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ) / 2),
    mul_nonneg (sq_nonneg (p.2 : ℝ)) (sub_nonneg.mpr hy2),
    mul_nonneg (sq_nonneg Y) (sq_nonneg (p.1 : ℝ)), sq_nonneg (p.2 : ℝ)]

private lemma abs_ww_le {α y Y : ℝ} (hα : 0 < α) (hy0 : 0 ≤ y) (hyY : y ≤ Y) (p : ℤ × ℤ) :
    |ww α y p| ≤ π * α * ((2 + Y ^ 2) * tt p) := by
  have hpa : 0 < π * α := mul_pos pi_pos hα
  have h1 := quad_upper p hy0 hyY
  unfold ww
  rw [abs_mul, abs_of_pos hpa]
  apply mul_le_mul_of_nonneg_left _ hpa.le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (uu p), sq_nonneg ((p.2 : ℝ) * y)]

private lemma ee_le {α y Y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) (hyY : y < Y) (p : ℤ × ℤ) :
    ee α y p ≤ Real.exp (-(π * α / (4 * Y)) * tt p) := by
  have hy0 : 0 < y := by linarith
  have hY0 : 0 < Y := by linarith
  have hpa : 0 < π * α := mul_pos pi_pos hα
  have hq := quad_lower p (y := y) (by nlinarith)
  have hT := tt_nonneg p
  unfold ee
  apply Real.exp_le_exp.mpr
  have h1 : tt p / 4 / Y ≤ tt p / 4 / y := div_le_div_of_nonneg_left (by positivity) hy0 hyY.le
  have h2 : tt p / 4 / y ≤ (uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y :=
    div_le_div_of_nonneg_right hq hy0.le
  have e1 : -π * α * (uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y
      = -(π * α) * ((uu p ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y) := by ring
  have e2 : -(π * α / (4 * Y)) * tt p = -(π * α) * (tt p / 4 / Y) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left (h1.trans h2) hpa.le
  linarith

private lemma abs_d1_le {α y Y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) (hyY : y < Y) (p : ℤ × ℤ) :
    |d1 α y p| ≤ 3 * (π * α) * (2 + Y ^ 2) *
      ((1 + tt p) ^ 2 * Real.exp (-(π * α / (4 * Y)) * tt p)) := by
  have hy0 : 0 < y := by linarith
  have hT := tt_nonneg p
  have he := ee_le hα hy hyY p
  have hw := abs_ww_le hα hy0.le hyY.le p
  have hpa : 0 < π * α := mul_pos pi_pos hα
  have hy2 : 1 / y ^ 2 ≤ 3 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hTT : tt p ≤ (1 + tt p) ^ 2 := by nlinarith
  have hE := Real.exp_pos (-(π * α / (4 * Y)) * tt p)
  unfold d1
  rw [abs_mul, abs_of_pos (ee_pos α y p), abs_div, abs_of_pos (by positivity : (0 : ℝ) < y ^ 2)]
  calc ee α y p * (|ww α y p| / y ^ 2)
      ≤ Real.exp (-(π * α / (4 * Y)) * tt p) * (π * α * ((2 + Y ^ 2) * tt p) * 3) := by
        apply mul_le_mul he _ (by positivity) hE.le
        rw [div_eq_mul_one_div]
        exact mul_le_mul hw hy2 (by positivity) (by positivity)
    _ = 3 * (π * α) * (2 + Y ^ 2) * (tt p * Real.exp (-(π * α / (4 * Y)) * tt p)) := by ring
    _ ≤ 3 * (π * α) * (2 + Y ^ 2) * ((1 + tt p) ^ 2 * Real.exp (-(π * α / (4 * Y)) * tt p)) := by
        gcongr

private lemma abs_d2_le {α y Y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) (hyY : y < Y) (p : ℤ × ℤ) :
    |d2 α y p| ≤ (3 * (π * α) ^ 2 * (2 + Y ^ 2) ^ 2 + 2 * (π * α) * Y) *
      ((1 + tt p) ^ 2 * Real.exp (-(π * α / (4 * Y)) * tt p)) := by
  have hy0 : 0 < y := by linarith
  have hY0 : 0 < Y := by linarith
  have hT := tt_nonneg p
  have he := ee_le hα hy hyY p
  have hw := abs_ww_le hα hy0.le hyY.le p
  have hpa : 0 < π * α := mul_pos pi_pos hα
  have hn : (p.2 : ℝ) ^ 2 ≤ tt p := by unfold tt; nlinarith [sq_nonneg (p.1 : ℝ)]
  have hw2 : ww α y p ^ 2 ≤ (π * α * ((2 + Y ^ 2) * tt p)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  have hinner : |ww α y p ^ 2 / y ^ 2 - 2 * π * α * (p.2 : ℝ) ^ 2 * y|
      ≤ 3 * (π * α) ^ 2 * (2 + Y ^ 2) ^ 2 * tt p ^ 2 + 2 * (π * α) * Y * tt p := by
    have h1 : 0 ≤ ww α y p ^ 2 / y ^ 2 := by positivity
    have h2 : 0 ≤ 2 * π * α * (p.2 : ℝ) ^ 2 * y := by positivity
    have h3 : ww α y p ^ 2 / y ^ 2 ≤ 3 * (π * α) ^ 2 * (2 + Y ^ 2) ^ 2 * tt p ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hq : 0 ≤ (π * α * ((2 + Y ^ 2) * tt p)) ^ 2 := by positivity
      have hy3 : 1 ≤ 3 * y ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy3 hq]
    have h4 : 2 * π * α * (p.2 : ℝ) ^ 2 * y ≤ 2 * (π * α) * Y * tt p := by
      have := mul_le_mul hn hyY.le hy0.le hT
      nlinarith
    rw [abs_le]; constructor <;> linarith
  have hTT : tt p ≤ (1 + tt p) ^ 2 := by nlinarith
  have hTT2 : tt p ^ 2 ≤ (1 + tt p) ^ 2 := by nlinarith
  have hE := Real.exp_pos (-(π * α / (4 * Y)) * tt p)
  have hA : 0 ≤ 3 * (π * α) ^ 2 * (2 + Y ^ 2) ^ 2 := by positivity
  have hB : 0 ≤ 2 * (π * α) * Y := by positivity
  unfold d2
  rw [abs_mul, abs_of_pos (ee_pos α y p)]
  calc ee α y p * |ww α y p ^ 2 / y ^ 2 - 2 * π * α * (p.2 : ℝ) ^ 2 * y|
      ≤ Real.exp (-(π * α / (4 * Y)) * tt p) *
        (3 * (π * α) ^ 2 * (2 + Y ^ 2) ^ 2 * tt p ^ 2 + 2 * (π * α) * Y * tt p) :=
        mul_le_mul he hinner (abs_nonneg _) hE.le
    _ ≤ Real.exp (-(π * α / (4 * Y)) * tt p) *
        ((3 * (π * α) ^ 2 * (2 + Y ^ 2) ^ 2 + 2 * (π * α) * Y) * (1 + tt p) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        nlinarith [mul_le_mul_of_nonneg_left hTT2 hA, mul_le_mul_of_nonneg_left hTT hB]
    _ = _ := by ring

private lemma summable_of_bound {f : ℤ × ℤ → ℝ} {K κ : ℝ} (hκ : 0 < κ)
    (hf : ∀ p, |f p| ≤ K * ((1 + tt p) ^ 2 * Real.exp (-κ * tt p))) : Summable f :=
  Summable.of_norm_bounded ((summable_majorant hκ).mul_left K)
    (fun p => by rw [Real.norm_eq_abs]; exact hf p)

/-- Every family `ee · (polynomial of degree ≤ 4 in m, n)` that we use is dominated by
`(1 + T)² e^{-κT}` near a fixed `y > 3/5`. -/
private lemma summable_wt {α y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) :
    Summable (fun p => (1 + tt p) ^ 2 * ee α y p) := by
  have hκ : 0 < π * α / (4 * (y + 1)) := by have := mul_pos pi_pos hα; positivity
  refine summable_of_bound (K := 1) hκ (fun p => ?_)
  have he := ee_le hα hy (lt_add_one y) p
  have hT := tt_nonneg p
  rw [abs_of_nonneg (by have := ee_pos α y p; positivity), one_mul]
  gcongr

private lemma summable_ee {α y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) : Summable (fun p => ee α y p) := by
  refine Summable.of_nonneg_of_le (fun p => (ee_pos α y p).le) (fun p => ?_) (summable_wt hα hy)
  have hT := tt_nonneg p
  have h1 : 1 ≤ (1 + tt p) ^ 2 := by nlinarith
  exact le_mul_of_one_le_left (ee_pos α y p).le h1

private lemma summable_gt {α y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) : Summable (fun p => gt α y p) := by
  have hpa : 0 < π * α := mul_pos pi_pos hα
  refine Summable.of_norm_bounded ((summable_wt hα hy).mul_left (π * α * (2 + y ^ 2)))
    (fun p => ?_)
  have hw := abs_ww_le (y := y) (Y := y) hα (by linarith) le_rfl p
  have hT := tt_nonneg p
  have he := ee_pos α y p
  have hTT : tt p ≤ (1 + tt p) ^ 2 := by nlinarith
  rw [Real.norm_eq_abs]
  unfold gt
  rw [abs_mul, abs_of_pos he]
  calc ee α y p * |ww α y p| ≤ ee α y p * (π * α * ((2 + y ^ 2) * tt p)) :=
        mul_le_mul_of_nonneg_left hw he.le
    _ = π * α * (2 + y ^ 2) * (tt p * ee α y p) := by ring
    _ ≤ π * α * (2 + y ^ 2) * ((1 + tt p) ^ 2 * ee α y p) := by gcongr

/-- `θ(α; 1/2, ·)` is differentiable on `(3/5, ∞)` with the termwise derivative. -/
private lemma hasDerivAt_theta {α : ℝ} (hα : 0 < α) {y : ℝ} (hy : 3 / 5 < y) :
    HasDerivAt (fun y => theta2 α (1 / 2) y) (∑' p, d1 α y p) y := by
  have hκ : 0 < π * α / (4 * (y + 1)) := by have := mul_pos pi_pos hα; positivity
  have hmem : y ∈ Set.Ioo (3 / 5 : ℝ) (y + 1) := ⟨hy, lt_add_one y⟩
  exact hasDerivAt_tsum_of_isPreconnected (g := fun p y => ee α y p) (g' := fun p y => d1 α y p)
    ((summable_majorant hκ).mul_left (3 * (π * α) * (2 + (y + 1) ^ 2)))
    isOpen_Ioo isPreconnected_Ioo
    (fun p z hz => hasDerivAt_ee α p (by linarith [hz.1]))
    (fun p z hz => by rw [Real.norm_eq_abs]; exact abs_d1_le hα hz.1 hz.2 p)
    hmem (summable_ee hα hy) hmem

/-- `G = y² ∂_y θ` is differentiable on `(3/5, ∞)` with the termwise derivative. -/
private lemma hasDerivAt_G {α : ℝ} (hα : 0 < α) {y : ℝ} (hy : 3 / 5 < y) :
    HasDerivAt (fun y => ∑' p, gt α y p) (∑' p, d2 α y p) y := by
  have hκ : 0 < π * α / (4 * (y + 1)) := by have := mul_pos pi_pos hα; positivity
  have hmem : y ∈ Set.Ioo (3 / 5 : ℝ) (y + 1) := ⟨hy, lt_add_one y⟩
  exact hasDerivAt_tsum_of_isPreconnected (g := fun p y => gt α y p) (g' := fun p y => d2 α y p)
    ((summable_majorant hκ).mul_left (3 * (π * α) ^ 2 * (2 + (y + 1) ^ 2) ^ 2 +
      2 * (π * α) * (y + 1)))
    isOpen_Ioo isPreconnected_Ioo
    (fun p z hz => hasDerivAt_gt α p (by linarith [hz.1]))
    (fun p z hz => by rw [Real.norm_eq_abs]; exact abs_d2_le hα hz.1 hz.2 p)
    hmem (summable_gt hα hy) hmem

private lemma tsum_d1_eq (α y : ℝ) : ∑' p, d1 α y p = (∑' p, gt α y p) / y ^ 2 := by
  rw [← tsum_div_const]
  congr 1
  ext p
  unfold d1 gt
  ring

/-! ### The corner `y = √3/2`: `G(√3/2) = 0` (Montgomery's Lemma 7 setup) -/

/-- The order-3 symmetry `(m, n) ↦ (-n, m + n)` of the form `m² + mn + n²`. -/
private def rot : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (-p.2, p.1 + p.2)
  invFun p := (p.1 + p.2, -p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private lemma rot_apply (p : ℤ × ℤ) : rot p = (-p.2, p.1 + p.2) := rfl

private lemma sqrt3_half_sq : (√3 / 2 : ℝ) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

private lemma sqrt3_half_gt : (433 / 500 : ℝ) < √3 / 2 := by
  have h : (1.732 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

private lemma gt_corner (α : ℝ) (p : ℤ × ℤ) :
    gt α (√3 / 2) p = π * α *
      Real.exp (-π * α * ((p.1 : ℝ) ^ 2 + p.1 * p.2 + (p.2 : ℝ) ^ 2) / (√3 / 2)) *
      ((p.1 : ℝ) ^ 2 + p.1 * p.2 - (p.2 : ℝ) ^ 2 / 2) := by
  unfold gt ee ww uu
  simp only [mul_pow, sqrt3_half_sq]
  have e1 : -π * α * (((p.1 : ℝ) + p.2 * (1 / 2)) ^ 2 + (p.2 : ℝ) ^ 2 * (3 / 4)) / (√3 / 2)
      = -π * α * ((p.1 : ℝ) ^ 2 + p.1 * p.2 + (p.2 : ℝ) ^ 2) / (√3 / 2) := by ring
  rw [e1]
  ring

private lemma corner {α : ℝ} (hα : 0 < α) : ∑' p, gt α (√3 / 2) p = 0 := by
  have hy₀ : (3 / 5 : ℝ) < √3 / 2 := by linarith [sqrt3_half_gt]
  have hs := summable_gt hα hy₀
  set f : ℤ × ℤ → ℝ := fun p => gt α (√3 / 2) p with hf
  have hsum : ∀ p, f p + f (rot p) + f (rot (rot p)) = 0 := by
    intro p
    simp only [hf, gt_corner, rot_apply]
    push_cast
    have ex1 : (-(p.2 : ℝ)) ^ 2 + -(p.2 : ℝ) * ((p.1 : ℝ) + p.2) + ((p.1 : ℝ) + p.2) ^ 2
        = (p.1 : ℝ) ^ 2 + p.1 * p.2 + (p.2 : ℝ) ^ 2 := by ring
    have ex2 : (-((p.1 : ℝ) + p.2)) ^ 2 + -((p.1 : ℝ) + p.2) * (-(p.2 : ℝ) + ((p.1 : ℝ) + p.2))
        + (-(p.2 : ℝ) + ((p.1 : ℝ) + p.2)) ^ 2 = (p.1 : ℝ) ^ 2 + p.1 * p.2 + (p.2 : ℝ) ^ 2 := by
      ring
    rw [ex1, ex2]
    ring
  have hs1 : Summable (fun p => f (rot p)) := rot.summable_iff.mpr hs
  have hs2 : Summable (fun p => f (rot (rot p))) :=
    (rot.summable_iff (f := fun p => f (rot p))).mpr hs1
  have h1 : ∑' p, f (rot p) = ∑' p, f p := rot.tsum_eq f
  have h2 : ∑' p, f (rot (rot p)) = ∑' p, f p := by
    rw [rot.tsum_eq (fun p => f (rot p)), h1]
  have h0 : ∑' p, (f p + f (rot p) + f (rot (rot p))) = 0 := by simp [hsum]
  rw [(hs.add hs1).tsum_add hs2, hs.tsum_add hs1, h1, h2] at h0
  show ∑' p, f p = 0
  linarith

/-! ### Row sums `Σ_m e^{-c (m + n/2)²}` -/

private lemma nat_le_sq (j : ℕ) : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ j := by exact_mod_cast h
    nlinarith

private lemma exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)

/-- `Σ_k e^{-k n²} ≤ 2 / (1 - e^{-k})`. -/
private lemma gauss_bound {k : ℝ} (hk : 0 < k) :
    Summable (fun n : ℤ => Real.exp (-k * (n : ℝ) ^ 2)) ∧
      ∑' n : ℤ, Real.exp (-k * (n : ℝ) ^ 2) ≤ 2 * 1 / (1 - Real.exp (-k)) := by
  refine geom_bound_int (Real.exp_pos _).le (exp_neg_lt_one hk) (fun n => (Real.exp_pos _).le)
    (fun j => ?_) (fun j => ?_)
  · rw [one_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have := nat_le_sq j
    push_cast
    nlinarith
  · rw [one_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    push_cast
    nlinarith [mul_nonneg hk.le (sq_nonneg (j : ℝ)), mul_nonneg hk.le hj]

/-- Row sums `Σ_m e^{-c (m + n/2)²}`. -/
private noncomputable def rowsum (c : ℝ) (n : ℤ) : ℝ :=
  ∑' m : ℤ, Real.exp (-c * ((m : ℝ) + n * (1 / 2)) ^ 2)

private lemma rowsum_nonneg (c : ℝ) (n : ℤ) : 0 ≤ rowsum c n :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

/-- Every row sum is at most `Σ_k e^{-c k²/4} ≤ 2 / (1 - e^{-c/4})`. -/
private lemma rowsum_le {c : ℝ} (hc : 0 < c) (n : ℤ) :
    Summable (fun m : ℤ => Real.exp (-c * ((m : ℝ) + n * (1 / 2)) ^ 2)) ∧
      rowsum c n ≤ 2 / (1 - Real.exp (-(c / 4))) := by
  obtain ⟨hg, hgle⟩ := gauss_bound (k := c / 4) (by positivity)
  have he : Function.Injective (fun m : ℤ => 2 * m + n) := by
    intro a b h
    simp only at h
    omega
  have hfg : ∀ m : ℤ, Real.exp (-(c / 4) * (((2 * m + n : ℤ)) : ℝ) ^ 2)
      = Real.exp (-c * ((m : ℝ) + n * (1 / 2)) ^ 2) := by
    intro m; congr 1; push_cast; ring
  have hf : Summable (fun m : ℤ => Real.exp (-c * ((m : ℝ) + n * (1 / 2)) ^ 2)) :=
    (hg.comp_injective he).congr hfg
  refine ⟨hf, ?_⟩
  calc rowsum c n ≤ ∑' k : ℤ, Real.exp (-(c / 4) * (k : ℝ) ^ 2) :=
        Summable.tsum_le_tsum_of_inj (fun m : ℤ => 2 * m + n) he
          (fun _ _ => (Real.exp_pos _).le) (fun m => (hfg m).ge) hf hg
    _ ≤ 2 * 1 / (1 - Real.exp (-(c / 4))) := hgle
    _ = 2 / (1 - Real.exp (-(c / 4))) := by ring

/-- The odd row: `Σ_m e^{-c (m + 1/2)²} ≤ 2 e^{-c/4} / (1 - e^{-2c})`. -/
private lemma rowsum_one_le {c : ℝ} (hc : 0 < c) :
    rowsum c 1 ≤ 2 * Real.exp (-(c / 4)) / (1 - Real.exp (-(2 * c))) := by
  have h := geom_bound_int
    (f := fun m : ℤ => Real.exp (-c * ((m : ℝ) + ((1 : ℤ) : ℝ) * (1 / 2)) ^ 2))
    (C := Real.exp (-(c / 4))) (r := Real.exp (-(2 * c))) (Real.exp_pos _).le
    (exp_neg_lt_one (by positivity)) (fun _ => (Real.exp_pos _).le) (fun j => ?_) (fun j => ?_)
  · exact h.2
  · rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := nat_le_sq j
    push_cast
    nlinarith
  · rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := nat_le_sq j
    push_cast
    nlinarith

private lemma rowsum_neg (c : ℝ) (n : ℤ) : rowsum c (-n) = rowsum c n := by
  unfold rowsum
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  ext m
  simp only [Equiv.neg_apply]
  congr 1
  push_cast
  ring

/-! ### The weighted sum `Σ n² e` -/

private lemma ee_split {α y : ℝ} (hy : 0 < y) (p : ℤ × ℤ) :
    ee α y p = Real.exp (-(π * α) * (p.2 : ℝ) ^ 2 * y) *
      Real.exp (-(π * α / y) * ((p.1 : ℝ) + p.2 * (1 / 2)) ^ 2) := by
  unfold ee uu
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

private lemma tsum_n2_ee {α y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) :
    ∑' p : ℤ × ℤ, (p.2 : ℝ) ^ 2 * ee α y p
        = ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-(π * α) * (n : ℝ) ^ 2 * y) * rowsum (π * α / y) n ∧
      Summable (fun n : ℤ =>
        (n : ℝ) ^ 2 * Real.exp (-(π * α) * (n : ℝ) ^ 2 * y) * rowsum (π * α / y) n) := by
  have hy0 : 0 < y := by linarith
  set F : ℤ × ℤ → ℝ := fun p => (p.2 : ℝ) ^ 2 * ee α y p with hFdef
  have hF : Summable F := by
    refine Summable.of_nonneg_of_le (fun p => by have := ee_pos α y p; positivity) (fun p => ?_)
      (summable_wt hα hy)
    have hT := tt_nonneg p
    have hn : (p.2 : ℝ) ^ 2 ≤ (1 + tt p) ^ 2 := by
      unfold tt at hT ⊢; nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2 : ℝ)]
    exact mul_le_mul_of_nonneg_right hn (ee_pos α y p).le
  have hF' : Summable (fun q : ℤ × ℤ => F (q.2, q.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hF
  have hswap : ∑' p, F p = ∑' q : ℤ × ℤ, F (q.2, q.1) := ((Equiv.prodComm ℤ ℤ).tsum_eq F).symm
  have hrow : ∀ n : ℤ, ∑' m : ℤ, F (m, n)
      = (n : ℝ) ^ 2 * Real.exp (-(π * α) * (n : ℝ) ^ 2 * y) * rowsum (π * α / y) n := by
    intro n
    unfold rowsum
    rw [← tsum_mul_left]
    congr 1
    ext m
    simp only [hFdef]
    rw [ee_split hy0]
    ring
  refine ⟨?_, hF'.prod.congr hrow⟩
  rw [hswap, hF'.tsum_prod]
  exact tsum_congr hrow

private lemma tsum_int_even {W : ℤ → ℝ} (hW : Summable W) (hev : ∀ n, W (-n) = W n) (h0 : W 0 = 0) :
    ∑' n, W n = 2 * W 1 + 2 * ∑' j : ℕ, W ((j : ℤ) + 2) := by
  have hpos : Summable (fun j : ℕ => W j) := hW.comp_injective Nat.cast_injective
  have hneg : Summable (fun j : ℕ => W (-((j : ℤ) + 1))) :=
    hW.comp_injective (fun a b h => by
      simp only [neg_inj, add_left_inj, Nat.cast_inj] at h; exact h)
  have hpos1 : Summable (fun j : ℕ => W ((j : ℤ) + 1)) :=
    hW.comp_injective (fun a b h => by simp only [add_left_inj, Nat.cast_inj] at h; exact h)
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  have e1 : ∑' j : ℕ, W (-((j : ℤ) + 1)) = ∑' j : ℕ, W ((j : ℤ) + 1) :=
    tsum_congr (fun j => hev _)
  have e2 : ∑' j : ℕ, W (j : ℤ) = W 0 + ∑' j : ℕ, W ((j : ℤ) + 1) := by
    rw [hpos.tsum_eq_zero_add]
    push_cast
    ring
  have e3 : ∑' j : ℕ, W ((j : ℤ) + 1) = W 1 + ∑' j : ℕ, W ((j : ℤ) + 2) := by
    rw [hpos1.tsum_eq_zero_add]
    congr 1
  rw [e1, e2, e3, h0]
  ring

private lemma sq_exp_tail {a y : ℝ} (hay : 0 ≤ a * y) (j : ℕ) :
    ((j : ℝ) + 2) ^ 2 * Real.exp (-a * ((j : ℝ) + 2) ^ 2 * y)
      ≤ 4 * Real.exp (-4 * a * y) * Real.exp (1 - 4 * a * y) ^ j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : 1 + (j : ℝ) / 2 ≤ Real.exp ((j : ℝ) / 2) := by
    linarith [Real.add_one_le_exp ((j : ℝ) / 2)]
  have h2 : ((j : ℝ) + 2) ^ 2 ≤ 4 * Real.exp (j : ℝ) := by
    have h3 : (1 + (j : ℝ) / 2) ^ 2 ≤ Real.exp ((j : ℝ) / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [← Real.exp_nat_mul] at h3
    have h4 : ((2 : ℕ) : ℝ) * ((j : ℝ) / 2) = j := by push_cast; ring
    rw [h4] at h3
    nlinarith
  have h5 : Real.exp (-a * ((j : ℝ) + 2) ^ 2 * y) ≤ Real.exp (-4 * a * y + j * (-4 * a * y)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ a * y * (j : ℝ) ^ 2 := by positivity
    nlinarith
  rw [← Real.exp_nat_mul]
  have e : Real.exp (j : ℝ) * Real.exp (-4 * a * y + j * (-4 * a * y))
      = Real.exp (-4 * a * y) * Real.exp (j * (1 - 4 * a * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc ((j : ℝ) + 2) ^ 2 * Real.exp (-a * ((j : ℝ) + 2) ^ 2 * y)
      ≤ 4 * Real.exp (j : ℝ) * Real.exp (-4 * a * y + j * (-4 * a * y)) :=
        mul_le_mul h2 h5 (Real.exp_pos _).le (by positivity)
    _ = 4 * (Real.exp (j : ℝ) * Real.exp (-4 * a * y + j * (-4 * a * y))) := by ring
    _ = 4 * Real.exp (-4 * a * y) * Real.exp (j * (1 - 4 * a * y)) := by rw [e]; ring

/-- `Σ_{m,n} n² e ≤ 2 e^{-ay} · 2e^{-c/4}/(1-e^{-2c})
  + 2 · (2/(1-e^{-c/4})) · 4e^{-4ay}/(1-e^{1-4ay})`, with `a = πα`, `c = a/y`. -/
private lemma sum_n2_bound {α y : ℝ} (hα : 1 ≤ α) (hy : √3 / 2 ≤ y) :
    ∑' p : ℤ × ℤ, (p.2 : ℝ) ^ 2 * ee α y p ≤
      2 * (Real.exp (-(π * α) * y) *
        (2 * Real.exp (-(π * α / y / 4)) / (1 - Real.exp (-(2 * (π * α / y)))))) +
      2 * (2 / (1 - Real.exp (-(π * α / y / 4))) * (4 * Real.exp (-4 * (π * α) * y)) /
        (1 - Real.exp (1 - 4 * (π * α) * y))) := by
  have hα0 : 0 < α := by linarith
  have hy0 : (433 / 500 : ℝ) < y := lt_of_lt_of_le sqrt3_half_gt hy
  have hy35 : 3 / 5 < y := by linarith
  have hypos : 0 < y := by linarith
  have hpa : 0 < π * α := mul_pos pi_pos hα0
  have hpi : (157 / 50 : ℝ) < π := by linarith [Real.pi_gt_d2]
  have hpa' : (157 / 50 : ℝ) < π * α := by nlinarith
  set c := π * α / y with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨heq, hWs⟩ := tsum_n2_ee hα0 hy35
  rw [heq]
  set W : ℤ → ℝ := fun n => (n : ℝ) ^ 2 * Real.exp (-(π * α) * (n : ℝ) ^ 2 * y) * rowsum c n
    with hW
  have hev : ∀ n, W (-n) = W n := by
    intro n
    simp only [hW]
    rw [rowsum_neg]
    push_cast
    ring_nf
  have h0 : W 0 = 0 := by simp [hW]
  rw [tsum_int_even hWs hev h0]
  have hW1 : W 1 ≤ Real.exp (-(π * α) * y) *
      (2 * Real.exp (-(c / 4)) / (1 - Real.exp (-(2 * c)))) := by
    have := rowsum_one_le hcpos
    simp only [hW, Int.cast_one, one_pow, one_mul, mul_one]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have hay : 0 ≤ π * α * y := by positivity
  have hr1 : Real.exp (1 - 4 * (π * α) * y) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have htail : ∑' j : ℕ, W ((j : ℤ) + 2) ≤
      2 / (1 - Real.exp (-(c / 4))) * (4 * Real.exp (-4 * (π * α) * y)) /
        (1 - Real.exp (1 - 4 * (π * α) * y)) := by
    refine (geom_bound_nat (Real.exp_pos _).le hr1 (fun j => ?_) (fun j => ?_)).2
    · simp only [hW]
      have := rowsum_nonneg c ((j : ℤ) + 2)
      positivity
    · have hrow := (rowsum_le hcpos ((j : ℤ) + 2)).2
      have hq := sq_exp_tail (a := π * α) hay j
      have hq2 : 0 < 1 - Real.exp (-(c / 4)) := by
        have := exp_neg_lt_one (x := c / 4) (by positivity); linarith
      simp only [hW]
      push_cast
      calc ((j : ℝ) + 2) ^ 2 * Real.exp (-(π * α) * ((j : ℝ) + 2) ^ 2 * y) *
            rowsum c ((j : ℤ) + 2)
          ≤ (4 * Real.exp (-4 * (π * α) * y) * Real.exp (1 - 4 * (π * α) * y) ^ j) *
            (2 / (1 - Real.exp (-(c / 4)))) := by
            apply mul_le_mul _ hrow (rowsum_nonneg _ _) (by positivity)
            convert hq using 2
        _ = 2 / (1 - Real.exp (-(c / 4))) * (4 * Real.exp (-4 * (π * α) * y)) *
            Real.exp (1 - 4 * (π * α) * y) ^ j := by ring
  have hc4 : π * α / y / 4 = c / 4 := rfl
  rw [hc4]
  linarith

/-! ### Lemma 5 at `x = 1/2`: the scalar inequality -/

private lemma inv_one_sub_exp_le {x : ℝ} (hx : 0 < x) : 1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
  have hE : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h1 := Real.add_one_le_exp x
  have hEpos := Real.exp_pos (-x)
  have hq : 0 < 1 - Real.exp (-x) := by have := exp_neg_lt_one hx; linarith
  have hEle : Real.exp (-x) * (1 + x) ≤ 1 := by nlinarith
  rw [div_le_iff₀ hq]
  have e : (1 + 1 / x) * (1 - Real.exp (-x)) = ((1 + x) * (1 - Real.exp (-x))) / x := by
    field_simp
    ring
  rw [e, le_div_iff₀ hx]
  nlinarith

private lemma exp_seven_ge : (1000 : ℝ) ≤ Real.exp 7 := by
  have h := Real.exp_one_gt_d9
  have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h7]
  calc (1000 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
    _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h.le 7

private lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h := Real.exp_one_gt_d9
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

/-- The polynomial core of Lemma 5, after `e^t ≥ 1 + t` and the crude geometric bounds. -/
private lemma poly_core {a y : ℝ} (ha : 157 / 50 < a) (hy : 433 / 500 < y) (hy2 : 3 / 4 ≤ y ^ 2) :
    y ^ 3 * (4 * (1 + y / (2 * a)) + 4 / 125 * (1 + 4 * y / a))
      ≤ a * (1 + a * (y ^ 2 - 3 / 4) / y) + a * (1 / 4 - y ^ 2) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hapos : 0 < a := by linarith
  have hs : 0 ≤ y - 433 / 500 := by linarith
  have hP : 504 / 125 * y ^ 4 + 266 / 125 / (157 / 50) * y ^ 5
      ≤ 157 / 50 * y + (157 / 50) ^ 2 * (y ^ 2 - 3 / 4) + 157 / 50 * y * (1 / 4 - y ^ 2) ^ 2 := by
    nlinarith [pow_nonneg hs 2, pow_nonneg hs 3, pow_nonneg hs 4, pow_nonneg hs 5]
  have hw : 0 ≤ y ^ 2 - 3 / 4 := by linarith
  have h1 : 157 / 50 * y + (157 / 50) ^ 2 * (y ^ 2 - 3 / 4) + 157 / 50 * y * (1 / 4 - y ^ 2) ^ 2
      ≤ a * y + a ^ 2 * (y ^ 2 - 3 / 4) + a * y * (1 / 4 - y ^ 2) ^ 2 := by
    have ha2 : (157 / 50 : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith
    have hq : 0 ≤ y * (1 / 4 - y ^ 2) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right ha.le hypos.le, mul_le_mul_of_nonneg_right ha2 hw,
      mul_le_mul_of_nonneg_right ha.le hq]
  have h2 : 266 / 125 * y ^ 5 / a ≤ 266 / 125 / (157 / 50) * y ^ 5 := by
    rw [div_le_iff₀ hapos]
    have h5 : 0 < y ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right ha.le h5.le]
  have hfinal : 504 / 125 * y ^ 4 + 266 / 125 * y ^ 5 / a
      ≤ a * y + a ^ 2 * (y ^ 2 - 3 / 4) + a * y * (1 / 4 - y ^ 2) ^ 2 := by linarith
  have eL : y * (y ^ 3 * (4 * (1 + y / (2 * a)) + 4 / 125 * (1 + 4 * y / a)))
      = 504 / 125 * y ^ 4 + 266 / 125 * y ^ 5 / a := by
    field_simp
    ring
  have eR : y * (a * (1 + a * (y ^ 2 - 3 / 4) / y) + a * (1 / 4 - y ^ 2) ^ 2)
      = a * y + a ^ 2 * (y ^ 2 - 3 / 4) + a * y * (1 / 4 - y ^ 2) ^ 2 := by
    field_simp
  have h := hfinal
  rw [← eL, ← eR] at h
  exact le_of_mul_le_mul_left h hypos

/-- Lemma 5 at `x = 1/2`, `a = πα ≥ π`, `y ≥ √3/2`, in the form produced by the series bounds:
`2ay · (bound on Σ n² e) ≤ (the four terms (±1,0), (0,±1) of Σ a²(u²-n²y²)²/y² e)`. -/
private lemma scalar_key {a y : ℝ} (ha : π ≤ a) (hy : √3 / 2 ≤ y) :
    2 * a * y * (2 * (Real.exp (-a * y) *
        (2 * Real.exp (-(a / y / 4)) / (1 - Real.exp (-(2 * (a / y)))))) +
      2 * (2 / (1 - Real.exp (-(a / y / 4))) * (4 * Real.exp (-4 * a * y)) /
        (1 - Real.exp (1 - 4 * a * y))))
    ≤ 2 * (a ^ 2 / y ^ 2 * Real.exp (-a / y)) +
      2 * (a ^ 2 * (1 / 4 - y ^ 2) ^ 2 / y ^ 2 * Real.exp (-a * (1 / 4 + y ^ 2) / y)) := by
  have hpi : (157 / 50 : ℝ) < π := by linarith [Real.pi_gt_d2]
  have ha0 : 157 / 50 < a := by linarith
  have hapos : 0 < a := by linarith
  have hy0 : 433 / 500 < y := lt_of_lt_of_le sqrt3_half_gt hy
  have hypos : 0 < y := by linarith
  have hy2 : 3 / 4 ≤ y ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hy 2
    rwa [sqrt3_half_sq] at this
  have hyne : y ≠ 0 := hypos.ne'
  have hane : a ≠ 0 := hapos.ne'
  have hq1pos : 0 < 1 - Real.exp (-(2 * (a / y))) := by
    have := exp_neg_lt_one (x := 2 * (a / y)) (by positivity); linarith
  have hq2pos : 0 < 1 - Real.exp (-(a / y / 4)) := by
    have := exp_neg_lt_one (x := a / y / 4) (by positivity); linarith
  have hexp3 : Real.exp (1 - 4 * a * y) ≤ 1 / 2 := by
    calc Real.exp (1 - 4 * a * y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ 1 / 2 := exp_neg_one_le_half
  have hq3pos : 0 < 1 - Real.exp (1 - 4 * a * y) := by linarith
  have b1 : 1 / (1 - Real.exp (-(2 * (a / y)))) ≤ 1 + y / (2 * a) := by
    have := inv_one_sub_exp_le (x := 2 * (a / y)) (by positivity)
    convert this using 2
    field_simp
  have b2 : 1 / (1 - Real.exp (-(a / y / 4))) ≤ 1 + 4 * y / a := by
    have := inv_one_sub_exp_le (x := a / y / 4) (by positivity)
    convert this using 2
    field_simp
  have b3 : 1 / (1 - Real.exp (1 - 4 * a * y)) ≤ 2 := by
    rw [div_le_iff₀ hq3pos]; linarith
  set q1 := 1 - Real.exp (-(2 * (a / y))) with hq1
  set q2 := 1 - Real.exp (-(a / y / 4)) with hq2
  set q3 := 1 - Real.exp (1 - 4 * a * y) with hq3
  set Z := Real.exp (-3 * a * y + a / y / 4) with hZ
  have bZ : Z ≤ 1 / 1000 := by
    have h7 : -3 * a * y + a / y / 4 ≤ -7 := by
      have h12 : 0 < 12 * y ^ 2 - 1 := by linarith
      have h28 : 28 * y ≤ a * (12 * y ^ 2 - 1) := by nlinarith
      have e : -3 * a * y + a / y / 4 = -(a * (12 * y ^ 2 - 1)) / (4 * y) := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      linarith
    calc Z ≤ Real.exp (-7) := Real.exp_le_exp.mpr h7
      _ = 1 / Real.exp 7 := by rw [Real.exp_neg, inv_eq_one_div]
      _ ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) exp_seven_ge
  set t := a * (y ^ 2 - 3 / 4) / y with ht
  have bt : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  set E₁ := Real.exp (-a * (1 / 4 + y ^ 2) / y) with hE₁
  have i1 : Real.exp (-a * y) * Real.exp (-(a / y / 4)) = E₁ := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have i2 : Real.exp (-a / y) = E₁ * Real.exp t := by
    rw [← Real.exp_add, ht]; congr 1; field_simp; ring
  have i3 : Real.exp (-4 * a * y) = E₁ * Z := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hE₁pos : 0 < E₁ := Real.exp_pos _
  have core : y ^ 3 * (4 / q1 + 16 * Z / (q2 * q3))
      ≤ a * Real.exp t + a * (1 / 4 - y ^ 2) ^ 2 := by
    have hpoly := poly_core ha0 hy0 hy2
    have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
    have c1 : 4 / q1 ≤ 4 * (1 + y / (2 * a)) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left b1 (by norm_num)
    have c2 : 16 * Z / (q2 * q3) ≤ 4 / 125 * (1 + 4 * y / a) := by
      have e : 16 * Z / (q2 * q3) = 16 * Z * (1 / q2) * (1 / q3) := by field_simp
      rw [e]
      calc 16 * Z * (1 / q2) * (1 / q3) ≤ 16 * (1 / 1000) * (1 + 4 * y / a) * 2 := by
            gcongr
        _ = 4 / 125 * (1 + 4 * y / a) := by ring
    calc y ^ 3 * (4 / q1 + 16 * Z / (q2 * q3))
        ≤ y ^ 3 * (4 * (1 + y / (2 * a)) + 4 / 125 * (1 + 4 * y / a)) := by gcongr
      _ ≤ a * (1 + t) + a * (1 / 4 - y ^ 2) ^ 2 := hpoly
      _ ≤ a * Real.exp t + a * (1 / 4 - y ^ 2) ^ 2 := by gcongr
  rw [i2, i3]
  have eL : 2 * a * y * (2 * (Real.exp (-a * y) * (2 * Real.exp (-(a / y / 4)) / q1)) +
      2 * (2 / q2 * (4 * (E₁ * Z)) / q3))
      = 2 * a * E₁ / y ^ 2 * (y ^ 3 * (4 / q1 + 16 * Z / (q2 * q3))) := by
    rw [← i1]
    field_simp
    ring
  have eR : 2 * (a ^ 2 / y ^ 2 * (E₁ * Real.exp t)) + 2 * (a ^ 2 * (1 / 4 - y ^ 2) ^ 2 / y ^ 2 * E₁)
      = 2 * a * E₁ / y ^ 2 * (a * Real.exp t + a * (1 / 4 - y ^ 2) ^ 2) := by
    field_simp
  rw [eL, eR]
  exact mul_le_mul_of_nonneg_left core (by positivity)

/-! ### Lemma 5 at `x = 1/2`: `G' = Σ₁ - Σ₂ ≥ 0` -/

private lemma summable_A {α y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) :
    Summable (fun p => ee α y p * (ww α y p ^ 2 / y ^ 2)) := by
  have hy0 : 0 < y := by linarith
  refine Summable.of_nonneg_of_le (fun p => by have := ee_pos α y p; positivity) (fun p => ?_)
    ((summable_wt hα hy).mul_left (3 * (π * α * (2 + y ^ 2)) ^ 2))
  have hw := abs_ww_le (y := y) (Y := y) hα hy0.le le_rfl p
  have hT := tt_nonneg p
  have he := ee_pos α y p
  have hw2 : ww α y p ^ 2 ≤ (π * α * (2 + y ^ 2)) ^ 2 * (1 + tt p) ^ 2 := by
    have h1 : ww α y p ^ 2 ≤ (π * α * ((2 + y ^ 2) * tt p)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hw 2
    have h2 : tt p ^ 2 ≤ (1 + tt p) ^ 2 := by nlinarith
    calc ww α y p ^ 2 ≤ (π * α * ((2 + y ^ 2) * tt p)) ^ 2 := h1
      _ = (π * α * (2 + y ^ 2)) ^ 2 * tt p ^ 2 := by ring
      _ ≤ (π * α * (2 + y ^ 2)) ^ 2 * (1 + tt p) ^ 2 := by gcongr
  have hy2 : 1 / y ^ 2 ≤ 3 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  calc ee α y p * (ww α y p ^ 2 / y ^ 2) = ee α y p * ww α y p ^ 2 * (1 / y ^ 2) := by ring
    _ ≤ ee α y p * ((π * α * (2 + y ^ 2)) ^ 2 * (1 + tt p) ^ 2) * 3 := by gcongr
    _ = 3 * (π * α * (2 + y ^ 2)) ^ 2 * ((1 + tt p) ^ 2 * ee α y p) := by ring

private lemma summable_B {α y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) :
    Summable (fun p => ee α y p * (2 * π * α * (p.2 : ℝ) ^ 2 * y)) := by
  have hy0 : 0 < y := by linarith
  refine Summable.of_nonneg_of_le (fun p => by have := ee_pos α y p; positivity) (fun p => ?_)
    ((summable_wt hα hy).mul_left (2 * π * α * y))
  have hT := tt_nonneg p
  have he := ee_pos α y p
  have hn : (p.2 : ℝ) ^ 2 ≤ (1 + tt p) ^ 2 := by
    unfold tt at hT ⊢; nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2 : ℝ)]
  calc ee α y p * (2 * π * α * (p.2 : ℝ) ^ 2 * y)
      = 2 * π * α * y * ((p.2 : ℝ) ^ 2 * ee α y p) := by ring
    _ ≤ 2 * π * α * y * ((1 + tt p) ^ 2 * ee α y p) := by gcongr

/-- `Σ₁ ≥` the four terms `(±1, 0)`, `(0, ±1)`. -/
private lemma four_terms {α y : ℝ} (hα : 0 < α) (hy : 3 / 5 < y) :
    2 * ((π * α) ^ 2 / y ^ 2 * Real.exp (-(π * α) / y)) +
      2 * ((π * α) ^ 2 * (1 / 4 - y ^ 2) ^ 2 / y ^ 2 *
        Real.exp (-(π * α) * (1 / 4 + y ^ 2) / y))
    ≤ ∑' p, ee α y p * (ww α y p ^ 2 / y ^ 2) := by
  have hA := summable_A hα hy
  have hnn : ∀ p, 0 ≤ ee α y p * (ww α y p ^ 2 / y ^ 2) := fun p => by
    have := ee_pos α y p; positivity
  have hle := hA.sum_le_tsum ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ))
    (fun p _ => hnn p)
  refine le_trans (le_of_eq ?_) hle
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e10 : ee α y (1, 0) = Real.exp (-(π * α) / y) := by
    unfold ee uu; congr 1; push_cast; ring
  have em10 : ee α y (-1, 0) = Real.exp (-(π * α) / y) := by
    unfold ee uu; congr 1; push_cast; ring
  have e01 : ee α y (0, 1) = Real.exp (-(π * α) * (1 / 4 + y ^ 2) / y) := by
    unfold ee uu; congr 1; push_cast; ring
  have e0m1 : ee α y (0, -1) = Real.exp (-(π * α) * (1 / 4 + y ^ 2) / y) := by
    unfold ee uu; congr 1; push_cast; ring
  have w10 : ww α y (1, 0) = π * α := by unfold ww uu; push_cast; ring
  have wm10 : ww α y (-1, 0) = π * α := by unfold ww uu; push_cast; ring
  have w01 : ww α y (0, 1) = π * α * (1 / 4 - y ^ 2) := by unfold ww uu; push_cast; ring
  have w0m1 : ww α y (0, -1) = π * α * (1 / 4 - y ^ 2) := by unfold ww uu; push_cast; ring
  rw [e10, em10, e01, e0m1, w10, wm10, w01, w0m1]
  ring

/-- Montgomery, Lemma 5 at `x = 1/2`: `(y² h')' = y² (h'' + (2/y) h') ≥ 0` for `α ≥ 1`,
`y ≥ √3/2`. -/
private lemma key_ineq {α y : ℝ} (hα : 1 ≤ α) (hy : √3 / 2 ≤ y) : 0 ≤ ∑' p, d2 α y p := by
  have hα0 : 0 < α := by linarith
  have hy0 : (433 / 500 : ℝ) < y := lt_of_lt_of_le sqrt3_half_gt hy
  have hy35 : 3 / 5 < y := by linarith
  have hypos : 0 < y := by linarith
  have hA := summable_A hα0 hy35
  have hB := summable_B hα0 hy35
  have hsplit : ∑' p, d2 α y p = ∑' p, ee α y p * (ww α y p ^ 2 / y ^ 2)
      - ∑' p, ee α y p * (2 * π * α * (p.2 : ℝ) ^ 2 * y) := by
    rw [← hA.tsum_sub hB]
    congr 1
    ext p
    unfold d2
    ring
  have hBeq : ∑' p, ee α y p * (2 * π * α * (p.2 : ℝ) ^ 2 * y)
      = 2 * (π * α) * y * ∑' p : ℤ × ℤ, (p.2 : ℝ) ^ 2 * ee α y p := by
    rw [← tsum_mul_left]
    congr 1
    ext p
    ring
  have hlow := four_terms hα0 hy35
  have hN := sum_n2_bound hα hy
  have hsc := scalar_key (a := π * α) (y := y) (by nlinarith [pi_pos]) hy
  have hN' := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 2 * (π * α) * y)
  rw [hsplit, hBeq]
  linarith

/-! ### Lemmas 6 and 7: monotonicity on `[√3/2, ∞)` -/

private lemma monotone_of_one_le {α : ℝ} (hα : 1 ≤ α) :
    MonotoneOn (fun y => theta2 α (1 / 2) y) (Set.Ici (√3 / 2)) := by
  have hα0 : 0 < α := by linarith
  have hy0 : (3 / 5 : ℝ) < √3 / 2 := by linarith [sqrt3_half_gt]
  have hGd : ∀ y ∈ Set.Ici (√3 / 2),
      HasDerivAt (fun y => ∑' p, gt α y p) (∑' p, d2 α y p) y :=
    fun y hy => hasDerivAt_G hα0 (lt_of_lt_of_le hy0 hy)
  have hGmono : MonotoneOn (fun y => ∑' p, gt α y p) (Set.Ici (√3 / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => ∑' p, d2 α y p)
      (convex_Ici _) (fun y hy => (hGd y hy).continuousAt.continuousWithinAt) ?_ ?_
    · intro y hy
      rw [interior_Ici] at hy
      exact (hGd y (Set.mem_Ici.mpr hy.le)).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact key_ineq hα hy.le
  have hGnn : ∀ y ∈ Set.Ici (√3 / 2), 0 ≤ ∑' p, gt α y p := by
    intro y hy
    have h : ∑' p, gt α (√3 / 2) p ≤ ∑' p, gt α y p := hGmono Set.self_mem_Ici hy hy
    rwa [corner hα0] at h
  have hθd : ∀ y ∈ Set.Ici (√3 / 2),
      HasDerivAt (fun y => theta2 α (1 / 2) y) (∑' p, d1 α y p) y :=
    fun y hy => hasDerivAt_theta hα0 (lt_of_lt_of_le hy0 hy)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => ∑' p, d1 α y p)
    (convex_Ici _) (fun y hy => (hθd y hy).continuousAt.continuousWithinAt) ?_ ?_
  · intro y hy
    rw [interior_Ici] at hy
    exact (hθd y (Set.mem_Ici.mpr hy.le)).hasDerivWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    show 0 ≤ ∑' p, d1 α y p
    rw [tsum_d1_eq]
    exact div_nonneg (hGnn y (Set.mem_Ici.mpr hy.le)) (sq_nonneg y)

end YHalf

/-- Montgomery, Lemma 7 on the line `x = 1/2`, from the duality `θ(1/α) = α θ(α)`:
`θ(α; 1/2, ·)` increases on `[√3/2, ∞)` for every `α > 0`. -/
theorem yMonotoneHalf_of_duality (hD : Duality) : YMonotoneHalf := by
  intro α hα
  rcases le_or_gt 1 α with h1 | h1
  · exact YHalf.monotone_of_one_le h1
  · have hinv : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr h1.le
    have hmono := YHalf.monotone_of_one_le hinv
    have hy0 : (0 : ℝ) < √3 / 2 := by positivity
    have e : ∀ y : ℝ, 0 < y → theta2 α (1 / 2) y = α⁻¹ * theta2 α⁻¹ (1 / 2) y := by
      intro y hy
      rw [hD α hα (1 / 2) y hy]
      field_simp
    intro y₁ hy₁ y₂ hy₂ hle
    show theta2 α (1 / 2) y₁ ≤ theta2 α (1 / 2) y₂
    rw [e y₁ (lt_of_lt_of_le hy0 hy₁), e y₂ (lt_of_lt_of_le hy0 hy₂)]
    exact mul_le_mul_of_nonneg_left (hmono hy₁ hy₂ hle) (inv_nonneg.mpr hα.le)

end BccSharp.Coulomb.Montgomery
