import BccSharp.TwoSite.MontgomeryDefs

/-!
# Jacobi triple product and Montgomery's Lemma 1

H. L. Montgomery, *Minimal theta functions*, Glasgow Math. J. 30 (1988) 75–85, Lemma 1: for
`t > 0`, `Q(t; β) = -∂_β θ(t; β) / sin 2πβ` decreases on `[0, 1/2]`.

## Main results

* `jacobi_triple_product`: for `Im τ > 0`, `q = e^{πiτ}` and `w = e^{2πiz}`, the product
  `∏_{n ≥ 0} (1 - q^{2n+2}) (1 + q^{2n+1} w) (1 + q^{2n+1} w⁻¹)` has the value
  `jacobiTheta₂ z τ = ∑_{n ∈ ℤ} q^{n²} w^n` in the sense of Mathlib's `HasProd`
  (an unconditional product, which allows the value `0`).
* `theta1_triple_product`, `theta1_eq_tprod`: the real form
  `θ(t; β) = ∏_{r ≥ 1} (1 - e^{-2πrt}) (1 + 2 e^{-(2r-1)πt} cos 2πβ + e^{-2(2r-1)πt})`.
* `lemma1_of`: `Theta1Deriv` and continuity of `Qser t` imply `Lemma1`.

## Proof outline

*Triple product.* The `q`-binomial theorem
`∏_{i < n} (1 + q^{2i+1} y) = ∑_{j ≤ n} q^{j²} [n choose j]_{q²} y^j` (`qBinomial_odd`, by
induction on `n`, with Gaussian binomials defined by the `q`-Pascal rule), taken at `n = 2N`
and `y = q^{-2N} w`, gives the finite identity
`∏_{r < N} (1 + q^{2r+1} w) (1 + q^{2r+1} w⁻¹) = ∑_{|k| ≤ N} [2N choose N+k]_{q²} q^{k²} w^k`
(`finite_jacobi_triple_product`). After multiplication by `(q²; q²)_N`, the closed form
`[2N choose N+k]_p = (p; p)_{2N} / ((p; p)_{N+k} (p; p)_{N-k})` shows that every coefficient
tends to `1` and is bounded by `C² / c²`, where `c ≤ ‖(p; p)_m‖ ≤ C` for all `m`. Tannery's
theorem (`tendsto_tsum_of_dominated_convergence`) then identifies the limit of the partial
products with `∑_k q^{k²} w^k`.

*Lemma 1.* Put `Φ(c) = θ(t; arccos(c) / 2π)` (`thetaCos`). On `[-1, 1]` the real triple
product writes `Φ(c)` as a product of factors `a_n (1 + 2 b_n c + b_n²)` with `a_n > 0` and
`0 < b_n < 1`, each positive, increasing and affine in `c`. Finite products of such factors
are convex (`ConvexOn.mul`), hence so is their pointwise limit `Φ`. By `Theta1Deriv` and the
chain rule through `arccos`, `Φ'(cos 2πβ) = Q(t; β) / 2π` for `β ∈ (0, 1/2)`. The derivative
of a convex differentiable function is monotone, and `cos 2πβ` decreases on `(0, 1/2)`, so
`Q(t; ·)` decreases there; continuity of `Q(t; ·)` extends this to `[0, 1/2]`. Montgomery
instead writes `Q` as an explicit series of positive decreasing terms; both arguments rest on
the positivity and monotonicity of the factors `1 + 2 b_n c + b_n²`.
-/

set_option autoImplicit false

namespace BccSharp.Coulomb.Montgomery

open Real Complex Filter Topology Finset

/-! ### Gaussian binomial coefficients -/

/-- Gaussian binomial coefficients `[n choose k]_p`, defined by the `p`-Pascal rule
`[n+1 choose k+1]_p = [n choose k]_p + p^(k+1) [n choose k+1]_p`. -/
noncomputable def gaussBinom (p : ℂ) : ℕ → ℕ → ℂ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom p n k + p ^ (k + 1) * gaussBinom p n (k + 1)

@[simp] theorem gaussBinom_zero_right (p : ℂ) (n : ℕ) : gaussBinom p n 0 = 1 := by
  cases n <;> rfl

theorem gaussBinom_succ_succ (p : ℂ) (n k : ℕ) :
    gaussBinom p (n + 1) (k + 1) = gaussBinom p n k + p ^ (k + 1) * gaussBinom p n (k + 1) :=
  rfl

theorem gaussBinom_eq_zero_of_lt (p : ℂ) : ∀ {n k : ℕ}, n < k → gaussBinom p n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [gaussBinom_succ_succ, gaussBinom_eq_zero_of_lt p (n := n) (k := k) (by omega),
      gaussBinom_eq_zero_of_lt p (n := n) (k := k + 1) (by omega), mul_zero, add_zero]

theorem gaussBinom_self (p : ℂ) : ∀ n : ℕ, gaussBinom p n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [gaussBinom_succ_succ, gaussBinom_self p n,
      gaussBinom_eq_zero_of_lt p (Nat.lt_succ_self n), mul_zero, add_zero]

/-- The `p`-Pochhammer symbol `(p; p)_n = ∏_{i < n} (1 - p^(i+1))`. -/
noncomputable def qPoch (p : ℂ) (n : ℕ) : ℂ := ∏ i ∈ range n, (1 - p ^ (i + 1))

theorem qPoch_zero (p : ℂ) : qPoch p 0 = 1 := by simp [qPoch]

theorem qPoch_succ (p : ℂ) (n : ℕ) : qPoch p (n + 1) = qPoch p n * (1 - p ^ (n + 1)) := by
  simp [qPoch, prod_range_succ]

/-- Closed form of the Gaussian binomial coefficient, without division:
`[n+k choose k]_p (p; p)_k (p; p)_n = (p; p)_{n+k}`. -/
theorem gaussBinom_mul_qPoch (p : ℂ) (k : ℕ) : ∀ n : ℕ,
    gaussBinom p (n + k) k * qPoch p k * qPoch p n = qPoch p (n + k) := by
  induction k with
  | zero => intro n; simp [qPoch_zero]
  | succ k ihk =>
    intro n
    induction n with
    | zero => simp [gaussBinom_self, qPoch_zero]
    | succ n ihn =>
      have h1 := ihk (n + 1)
      have h2 := ihn
      rw [show n + (k + 1) = n + 1 + k by ring] at h2
      rw [show n + 1 + (k + 1) = n + 1 + k + 1 by ring, gaussBinom_succ_succ]
      rw [qPoch_succ p (n + 1 + k), qPoch_succ p k, qPoch_succ p n]
      rw [qPoch_succ p n] at h1
      rw [qPoch_succ p k] at h2
      linear_combination (1 - p ^ (k + 1)) * h1 + p ^ (k + 1) * (1 - p ^ (n + 1)) * h2

/-- The `q`-binomial theorem in the form used for the triple product:
`∏_{i < n} (1 + q^(2i+1) y) = ∑_{j ≤ n} q^(j²) [n choose j]_{q²} y^j`. -/
theorem qBinomial_odd (q : ℂ) (n : ℕ) : ∀ y : ℂ,
    ∏ i ∈ range n, (1 + q ^ (2 * i + 1) * y) =
      ∑ j ∈ range (n + 1), q ^ (j * j) * gaussBinom (q ^ 2) n j * y ^ j := by
  induction n with
  | zero => intro y; simp
  | succ n ih =>
    intro y
    rw [prod_range_succ']
    have hshift : ∏ i ∈ range n, (1 + q ^ (2 * (i + 1) + 1) * y) =
        ∏ i ∈ range n, (1 + q ^ (2 * i + 1) * (q ^ 2 * y)) :=
      prod_congr rfl fun i _ => by ring
    rw [hshift, ih]
    have h5 : ∑ j ∈ range (n + 1), q ^ (j * j) * gaussBinom (q ^ 2) n j * (q ^ 2 * y) ^ j =
        ∑ j ∈ range (n + 1), q ^ ((j + 1) * (j + 1)) *
          ((q ^ 2) ^ (j + 1) * gaussBinom (q ^ 2) n (j + 1)) * y ^ (j + 1) + 1 := by
      rw [sum_range_succ' _ n, sum_range_succ _ n,
        gaussBinom_eq_zero_of_lt _ (Nat.lt_succ_self n)]
      simp only [gaussBinom_zero_right, mul_zero, zero_mul, add_zero, pow_zero, mul_one]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    have h6 : ∑ j ∈ range (n + 1), q ^ (j * j) * gaussBinom (q ^ 2) n j * (q ^ 2 * y) ^ j *
        (q ^ (2 * 0 + 1) * y) =
        ∑ j ∈ range (n + 1), q ^ ((j + 1) * (j + 1)) * gaussBinom (q ^ 2) n j * y ^ (j + 1) :=
      sum_congr rfl fun j _ => by ring
    rw [sum_range_succ' _ (n + 1)]
    simp only [gaussBinom_succ_succ, gaussBinom_zero_right]
    rw [mul_add, mul_one, sum_mul, h5, h6]
    simp only [mul_add, add_mul, sum_add_distrib]
    ring

private theorem sum_odd_range (N : ℕ) : ∑ m ∈ range N, (2 * m + 1) = N * N := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

/-- The finite Jacobi triple product:
`∏_{r < N} (1 + q^(2r+1) w) (1 + q^(2r+1) w⁻¹) = ∑_{j ≤ 2N} [2N choose j]_{q²} q^((j-N)²) w^(j-N)`.
-/
theorem finite_jacobi_triple_product {q w : ℂ} (hq : q ≠ 0) (hw : w ≠ 0) (N : ℕ) :
    ∏ r ∈ range N, ((1 + q ^ (2 * r + 1) * w) * (1 + q ^ (2 * r + 1) * w⁻¹)) =
      ∑ j ∈ range (2 * N + 1),
        gaussBinom (q ^ 2) (2 * N) j * (q ^ (((j : ℤ) - N) ^ 2) * w ^ ((j : ℤ) - N)) := by
  set P := ∏ r ∈ range N, ((1 + q ^ (2 * r + 1) * w) * (1 + q ^ (2 * r + 1) * w⁻¹)) with hP
  have key := qBinomial_odd q (2 * N) (w / q ^ (2 * N))
  have hL : ∏ i ∈ range (2 * N), (1 + q ^ (2 * i + 1) * (w / q ^ (2 * N))) =
      w ^ N / q ^ (N * N) * P := by
    have hsplit : ∏ i ∈ range (2 * N), (1 + q ^ (2 * i + 1) * (w / q ^ (2 * N))) =
        (∏ m ∈ range N, (1 + q ^ (2 * (N - 1 - m) + 1) * (w / q ^ (2 * N)))) *
          ∏ m ∈ range N, (1 + q ^ (2 * (N + m) + 1) * (w / q ^ (2 * N))) := by
      rw [prod_range_reflect (fun i => 1 + q ^ (2 * i + 1) * (w / q ^ (2 * N))) N,
        ← prod_range_add, two_mul]
    rw [hsplit]
    have h1 : ∀ m ∈ range N, 1 + q ^ (2 * (N - 1 - m) + 1) * (w / q ^ (2 * N)) =
        w / q ^ (2 * m + 1) * (1 + q ^ (2 * m + 1) * w⁻¹) := by
      intro m hm
      have hm' : m < N := mem_range.mp hm
      have e : 2 * N = (2 * (N - 1 - m) + 1) + (2 * m + 1) := by omega
      rw [e, pow_add q (2 * (N - 1 - m) + 1) (2 * m + 1)]
      field_simp
      ring
    have h2 : ∀ m ∈ range N, 1 + q ^ (2 * (N + m) + 1) * (w / q ^ (2 * N)) =
        1 + q ^ (2 * m + 1) * w := by
      intro m _
      rw [show 2 * (N + m) + 1 = 2 * N + (2 * m + 1) by ring, pow_add q (2 * N) (2 * m + 1)]
      field_simp
    rw [prod_congr rfl h1, prod_congr rfl h2, prod_mul_distrib]
    have h3 : ∏ m ∈ range N, (w / q ^ (2 * m + 1)) = w ^ N / q ^ (N * N) := by
      rw [prod_div_distrib, prod_const, card_range, prod_pow_eq_pow_sum, sum_odd_range]
    rw [h3, hP, prod_mul_distrib]
    ring
  have hterm : ∀ j : ℕ, q ^ (((j : ℤ) - N) ^ 2) * w ^ ((j : ℤ) - N) =
      q ^ (j * j) * (w / q ^ (2 * N)) ^ j * (q ^ (N * N) / w ^ N) := by
    intro j
    have e1 : ((j : ℤ) - N) ^ 2 = ((j * j + N * N : ℕ) : ℤ) - ((2 * N * j : ℕ) : ℤ) := by
      push_cast; ring
    rw [e1, zpow_sub₀ hq, zpow_sub₀ hw, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
      div_pow, ← pow_mul, pow_add]
    field_simp
  calc P = (q ^ (N * N) / w ^ N) * (w ^ N / q ^ (N * N) * P) := by field_simp
    _ = (q ^ (N * N) / w ^ N) * ∑ j ∈ range (2 * N + 1),
          q ^ (j * j) * gaussBinom (q ^ 2) (2 * N) j * (w / q ^ (2 * N)) ^ j := by
        rw [← hL, key]
    _ = ∑ j ∈ range (2 * N + 1),
          gaussBinom (q ^ 2) (2 * N) j * (q ^ (((j : ℤ) - N) ^ 2) * w ^ ((j : ℤ) - N)) := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [hterm j]
        ring

/-! ### The infinite `p`-Pochhammer product -/

private theorem summable_norm_pow_succ {p : ℂ} (hp : ‖p‖ < 1) :
    Summable (fun i : ℕ => ‖p ^ (i + 1)‖) := by
  simp_rw [norm_pow, pow_succ]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hp).mul_right _

/-- `(p; p)_n → (p; p)_∞` for `‖p‖ < 1`. -/
theorem tendsto_qPoch {p : ℂ} (hp : ‖p‖ < 1) :
    Tendsto (qPoch p) atTop (𝓝 (∏' i : ℕ, (1 - p ^ (i + 1)))) :=
  (multipliable_one_sub_of_summable (summable_norm_pow_succ hp)).hasProd.tendsto_prod_nat

/-- A uniform positive lower bound for `‖(p; p)_m‖`: the real partial products
`∏_{i < m} (1 - ‖p‖^(i+1))` decrease to a nonzero limit. -/
theorem exists_pos_le_norm_qPoch {p : ℂ} (hp : ‖p‖ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ m, c ≤ ‖qPoch p m‖ := by
  have hr0 : 0 ≤ ‖p‖ := norm_nonneg _
  have hfac : ∀ i : ℕ, 0 < 1 - ‖p‖ ^ (i + 1) := fun i =>
    sub_pos.mpr (pow_lt_one₀ hr0 hp (Nat.succ_ne_zero i))
  have hsum : Summable (fun i : ℕ => ‖‖p‖ ^ (i + 1)‖) := by
    simp_rw [norm_pow, norm_norm, pow_succ]
    exact (summable_geometric_of_lt_one hr0 hp).mul_right _
  have hlim : Tendsto (fun m => ∏ i ∈ range m, (1 - ‖p‖ ^ (i + 1))) atTop
      (𝓝 (∏' i : ℕ, (1 - ‖p‖ ^ (i + 1)))) :=
    (multipliable_one_sub_of_summable hsum).hasProd.tendsto_prod_nat
  have hanti : Antitone (fun m => ∏ i ∈ range m, (1 - ‖p‖ ^ (i + 1))) := by
    refine antitone_nat_of_succ_le fun m => ?_
    rw [prod_range_succ]
    exact mul_le_of_le_one_right (prod_nonneg fun i _ => (hfac i).le)
      (by linarith [pow_nonneg hr0 (m + 1)])
  have hne : ∏' i : ℕ, (1 - ‖p‖ ^ (i + 1)) ≠ 0 := by
    have h := tprod_one_add_ne_zero_of_summable (f := fun i : ℕ => -(‖p‖ ^ (i + 1)))
      (fun i => (by linarith [hfac i] : (0 : ℝ) < 1 + -(‖p‖ ^ (i + 1))).ne')
      (by simpa using hsum)
    simpa [sub_eq_add_neg] using h
  have hnn : 0 ≤ ∏' i : ℕ, (1 - ‖p‖ ^ (i + 1)) :=
    ge_of_tendsto' hlim fun m => prod_nonneg fun i _ => (hfac i).le
  refine ⟨_, lt_of_le_of_ne hnn (Ne.symm hne), fun m => (hanti.le_of_tendsto hlim m).trans ?_⟩
  rw [qPoch, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => (hfac i).le) fun i _ => ?_
  have h := norm_sub_norm_le (1 : ℂ) (p ^ (i + 1))
  rwa [norm_one, norm_pow] at h

/-- A uniform upper bound for `‖(p; p)_m‖` (a convergent sequence is bounded). -/
theorem exists_norm_qPoch_le {p : ℂ} (hp : ‖p‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖qPoch p m‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (tendsto_qPoch hp))
  exact ⟨C, (norm_nonneg _).trans (hC _ ⟨0, rfl⟩), fun m => hC _ ⟨m, rfl⟩⟩

/-- Closed form of the central Gaussian binomial coefficient `[2N choose N+k]_p`. -/
theorem gaussBinom_center {p : ℂ} (hne : ∀ m, qPoch p m ≠ 0) {N : ℕ} {k : ℤ}
    (hk : -(N : ℤ) ≤ k ∧ k ≤ N) :
    gaussBinom p (2 * N) (k + N).toNat =
      qPoch p (2 * N) / (qPoch p (k + N).toNat * qPoch p ((N : ℤ) - k).toNat) := by
  have hcl := gaussBinom_mul_qPoch p (k + N).toNat ((N : ℤ) - k).toNat
  have e : ((N : ℤ) - k).toNat + (k + N).toNat = 2 * N := by omega
  rw [e] at hcl
  rw [eq_div_iff (mul_ne_zero (hne _) (hne _)), ← hcl]
  ring

/-! ### The Jacobi triple product -/

/-- `jacobiTheta₂_term n z τ = q^(n²) w^n` with `q = e^{πiτ}` and `w = e^{2πiz}`. -/
theorem jacobiTheta₂_term_eq_pow (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n z τ = cexp (π * I * τ) ^ (n ^ 2) * cexp (2 * π * I * z) ^ n := by
  rw [jacobiTheta₂_term, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_cexp_pi_I_mul_lt_one {τ : ℂ} (hτ : 0 < τ.im) :
    ‖cexp (π * I * τ)‖ < 1 := by
  have h : ((π : ℂ) * I * τ).re = -(π * τ.im) := by simp [Complex.mul_re]
  rw [Complex.norm_exp, Real.exp_lt_one_iff, h, neg_lt_zero]
  exact mul_pos Real.pi_pos hτ

/-- **Jacobi triple product.** For `Im τ > 0`, `q = e^{πiτ}` and `w = e^{2πiz}`,
`θ(z, τ) = ∏_{n ≥ 0} (1 - q^{2n+2}) (1 + q^{2n+1} w) (1 + q^{2n+1} w⁻¹)`, where
`θ(z, τ) = jacobiTheta₂ z τ = ∑_{n ∈ ℤ} q^{n²} w^n`. The product converges unconditionally. -/
theorem jacobi_triple_product {z τ q w : ℂ} (hτ : 0 < τ.im) (hq : q = cexp (π * I * τ))
    (hw : w = cexp (2 * π * I * z)) :
    HasProd (fun n : ℕ => (1 - q ^ (2 * (n + 1))) * (1 + q ^ (2 * n + 1) * w) *
      (1 + q ^ (2 * n + 1) * w⁻¹)) (jacobiTheta₂ z τ) := by
  have hq0 : q ≠ 0 := hq ▸ Complex.exp_ne_zero _
  have hw0 : w ≠ 0 := hw ▸ Complex.exp_ne_zero _
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_I_mul_lt_one hτ
  have hq2 : ‖q‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hqn two_ne_zero
  have hpn : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact hq2
  have hT : ∀ k : ℤ, jacobiTheta₂_term k z τ = q ^ (k ^ 2) * w ^ k := fun k => by
    rw [hq, hw]; exact jacobiTheta₂_term_eq_pow k z τ
  -- multipliability of the product
  have hg : Summable (fun n : ℕ => (‖q‖ ^ 2) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hq2
  have hs1 : Summable (fun n : ℕ => ‖q ^ (2 * (n + 1))‖) := by
    refine (hg.mul_left (‖q‖ ^ 2)).congr fun n => ?_
    rw [norm_pow]; ring
  have hs2 : Summable (fun n : ℕ => ‖q ^ (2 * n + 1) * w‖) := by
    refine (hg.mul_left (‖q‖ * ‖w‖)).congr fun n => ?_
    rw [norm_mul, norm_pow]; ring
  have hs3 : Summable (fun n : ℕ => ‖q ^ (2 * n + 1) * w⁻¹‖) := by
    refine (hg.mul_left (‖q‖ * ‖w⁻¹‖)).congr fun n => ?_
    rw [norm_mul, norm_pow]; ring
  have hmult : Multipliable (fun n : ℕ => (1 - q ^ (2 * (n + 1))) *
      (1 + q ^ (2 * n + 1) * w) * (1 + q ^ (2 * n + 1) * w⁻¹)) :=
    ((multipliable_one_sub_of_summable hs1).mul (multipliable_one_add_of_summable hs2)).mul
      (multipliable_one_add_of_summable hs3)
  -- bounds on the Pochhammer symbols
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_qPoch hpn
  obtain ⟨C, hC0, hC⟩ := exists_norm_qPoch_le hpn
  have hne : ∀ m, qPoch (q ^ 2) m ≠ 0 := fun m => norm_pos_iff.mp (hc0.trans_le (hc m))
  have hL := tendsto_qPoch hpn
  set L := ∏' i : ℕ, (1 - (q ^ 2) ^ (i + 1)) with hLdef
  have hL0 : L ≠ 0 := norm_pos_iff.mp (hc0.trans_le (ge_of_tendsto' hL.norm hc))
  -- the partial products as sums over `ℤ`
  let F : ℕ → ℤ → ℂ := fun N k => if -(N : ℤ) ≤ k ∧ k ≤ N then
    qPoch (q ^ 2) N * gaussBinom (q ^ 2) (2 * N) (k + N).toNat * jacobiTheta₂_term k z τ else 0
  have hF : ∀ N : ℕ, ∏ n ∈ range N, ((1 - q ^ (2 * (n + 1))) * (1 + q ^ (2 * n + 1) * w) *
      (1 + q ^ (2 * n + 1) * w⁻¹)) = ∑' k, F N k := by
    intro N
    have h1 : ∏ n ∈ range N, ((1 - q ^ (2 * (n + 1))) * (1 + q ^ (2 * n + 1) * w) *
        (1 + q ^ (2 * n + 1) * w⁻¹)) = qPoch (q ^ 2) N *
        ∏ r ∈ range N, ((1 + q ^ (2 * r + 1) * w) * (1 + q ^ (2 * r + 1) * w⁻¹)) := by
      rw [qPoch, ← prod_mul_distrib]
      refine prod_congr rfl fun n _ => ?_
      rw [← pow_mul]; ring
    have hzero : ∀ k ∉ Icc (-(N : ℤ)) N, F N k = 0 := by
      intro k hk
      rw [mem_Icc] at hk
      simp only [F]
      rw [ite_eq_right hk]
    rw [h1, finite_jacobi_triple_product hq0 hw0, mul_sum, tsum_eq_sum hzero]
    refine sum_nbij' (fun j => (j : ℤ) - N) (fun k => (k + N).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [mem_range] at hj
      rw [mem_Icc]
      omega
    · intro k hk
      rw [mem_Icc] at hk
      rw [mem_range]
      omega
    · intro j _
      simp
    · intro k hk
      rw [mem_Icc] at hk
      omega
    · intro j hj
      rw [mem_range] at hj
      have hcond : -(N : ℤ) ≤ (j : ℤ) - N ∧ (j : ℤ) - N ≤ N := by omega
      simp only [F, ite_eq_left hcond, hT]
      rw [show ((j : ℤ) - N + N).toNat = j by omega]
      ring
  -- pointwise limits of the coefficients
  have hpt : ∀ k : ℤ, Tendsto (fun N => F N k) atTop (𝓝 (jacobiTheta₂_term k z τ)) := by
    intro k
    have hev : ∀ᶠ N : ℕ in atTop, qPoch (q ^ 2) N * (qPoch (q ^ 2) (2 * N) /
        (qPoch (q ^ 2) (k + N).toNat * qPoch (q ^ 2) ((N : ℤ) - k).toNat)) *
          jacobiTheta₂_term k z τ = F N k := by
      filter_upwards [eventually_ge_atTop k.natAbs] with N hN
      have hcond : -(N : ℤ) ≤ k ∧ k ≤ N := by omega
      simp only [F, ite_eq_left hcond, gaussBinom_center hne hcond]
    have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun N hN => by omega⟩
    have hkN : Tendsto (fun N : ℕ => (k + N).toNat) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b + k.natAbs, fun N hN => by omega⟩
    have hNk : Tendsto (fun N : ℕ => ((N : ℤ) - k).toNat) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b + k.natAbs, fun N hN => by omega⟩
    have hlim := (hL.mul ((hL.comp h2N).div ((hL.comp hkN).mul (hL.comp hNk))
      (mul_ne_zero hL0 hL0))).mul (tendsto_const_nhds (x := jacobiTheta₂_term k z τ))
    rw [show L * (L / (L * L)) * jacobiTheta₂_term k z τ = jacobiTheta₂_term k z τ by
      field_simp] at hlim
    exact hlim.congr' hev
  -- domination
  have hbd : ∀ N : ℕ, ∀ k : ℤ,
      ‖F N k‖ ≤ C * (C / (c * c)) * ‖jacobiTheta₂_term k z τ‖ := by
    intro N k
    by_cases hcond : -(N : ℤ) ≤ k ∧ k ≤ N
    · simp only [F, ite_eq_left hcond, gaussBinom_center hne hcond, norm_mul, norm_div]
      gcongr
      · exact hC N
      · exact hC _
      · exact hc _
      · exact hc _
    · simp only [F, ite_eq_right hcond, norm_zero]
      have := norm_nonneg (jacobiTheta₂_term k z τ)
      positivity
  have hsum : Summable (fun k : ℤ => C * (C / (c * c)) * ‖jacobiTheta₂_term k z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).mpr hτ).norm.mul_left _
  have hT' := tendsto_tsum_of_dominated_convergence hsum hpt (Eventually.of_forall hbd)
  have hlimP : Tendsto (fun N => ∏ n ∈ range N, ((1 - q ^ (2 * (n + 1))) *
      (1 + q ^ (2 * n + 1) * w) * (1 + q ^ (2 * n + 1) * w⁻¹))) atTop
      (𝓝 (jacobiTheta₂ z τ)) := by
    simp_rw [hF]
    exact hT'
  rw [← tendsto_nhds_unique hmult.hasProd.tendsto_prod_nat hlimP]
  exact hmult.hasProd

/-! ### The real form -/

/-- `theta1 t β` is Mathlib's `jacobiTheta₂` at real `z = β` and `τ = i t`. -/
theorem jacobiTheta₂_I_mul_eq_theta1 {t : ℝ} (ht : 0 < t) (β : ℝ) :
    jacobiTheta₂ (β : ℂ) (I * t) = (theta1 t β : ℂ) := by
  have hτ : 0 < (I * (t : ℂ)).im := by simpa using ht
  have hreal : (starRingEnd ℂ) (jacobiTheta₂ (β : ℂ) (I * t)) =
      jacobiTheta₂ (β : ℂ) (I * t) := by
    rw [jacobiTheta₂_conj]
    congr 1
    · exact Complex.conj_ofReal β
    · simp [Complex.conj_ofReal]
  rw [← Complex.conj_eq_iff_re.mp hreal]
  congr 1
  rw [jacobiTheta₂, Complex.re_tsum ((summable_jacobiTheta₂_term_iff _ _).mpr hτ)]
  unfold theta1
  congr 1
  ext k
  have e : 2 * (π : ℂ) * I * (k : ℂ) * (β : ℂ) + (π : ℂ) * I * (k : ℂ) ^ 2 * (I * (t : ℂ)) =
      ((-π * (k : ℝ) ^ 2 * t : ℝ) : ℂ) + ((2 * π * k * β : ℝ) : ℂ) * I := by
    push_cast
    linear_combination ((π : ℂ) * (k : ℂ) ^ 2 * (t : ℂ)) * I_sq
  rw [jacobiTheta₂_term, e, Complex.exp_re]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add]

private theorem hasProd_of_ofReal {f : ℕ → ℝ} {a : ℝ}
    (h : HasProd (fun n => (f n : ℂ)) (a : ℂ)) : HasProd f a := by
  have h2 := (Complex.continuous_re.tendsto (a : ℂ)).comp h
  simp only [Function.comp_def, ← Complex.ofReal_prod, Complex.ofReal_re] at h2
  exact h2

/-- **Jacobi triple product, real form.** For `t > 0` and real `β`,
`θ(t; β) = ∏_{r ≥ 1} (1 - e^{-2πrt}) (1 + 2 e^{-(2r-1)πt} cos 2πβ + e^{-2(2r-1)πt})`,
indexed by `n = r - 1 ≥ 0`. The product converges unconditionally. -/
theorem theta1_triple_product {t : ℝ} (ht : 0 < t) (β : ℝ) :
    HasProd (fun n : ℕ => (1 - Real.exp (-2 * π * ((n : ℝ) + 1) * t)) *
      (1 + 2 * Real.exp (-(2 * (n : ℝ) + 1) * π * t) * Real.cos (2 * π * β) +
        Real.exp (-2 * (2 * (n : ℝ) + 1) * π * t))) (theta1 t β) := by
  have hτ : 0 < (I * (t : ℂ)).im := by simpa using ht
  have h := jacobi_triple_product (z := (β : ℂ)) (τ := I * t) hτ rfl rfl
  rw [jacobiTheta₂_I_mul_eq_theta1 ht] at h
  apply hasProd_of_ofReal
  have hq : cexp (π * I * (I * t)) = ((Real.exp (-π * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination ((π : ℂ) * (t : ℂ)) * I_sq
  have hw0 : cexp (2 * π * I * β) ≠ 0 := Complex.exp_ne_zero _
  have hw2 : cexp (2 * π * I * β) + (cexp (2 * π * I * β))⁻¹ =
      2 * ((Real.cos (2 * π * β) : ℝ) : ℂ) := by
    rw [← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
    push_cast
    ring_nf
  have hinv : cexp (2 * π * I * β) * (cexp (2 * π * I * β))⁻¹ = 1 := mul_inv_cancel₀ hw0
  convert h using 2 with n
  rw [hq]
  have e1 : Real.exp (-2 * π * ((n : ℝ) + 1) * t) = Real.exp (-π * t) ^ (2 * (n + 1)) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e2 : Real.exp (-(2 * (n : ℝ) + 1) * π * t) = Real.exp (-π * t) ^ (2 * n + 1) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e3 : Real.exp (-2 * (2 * (n : ℝ) + 1) * π * t) =
      (Real.exp (-π * t) ^ (2 * n + 1)) ^ 2 := by
    rw [← pow_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [e1, e2, e3]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  linear_combination
    (-(1 - ((Real.exp (-π * t) : ℝ) : ℂ) ^ (2 * (n + 1))) *
      ((Real.exp (-π * t) : ℝ) : ℂ) ^ (2 * n + 1)) * hw2 +
    (-(1 - ((Real.exp (-π * t) : ℝ) : ℂ) ^ (2 * (n + 1))) *
      (((Real.exp (-π * t) : ℝ) : ℂ) ^ (2 * n + 1)) ^ 2) * hinv

/-- The real triple product as an equation for `tprod`. -/
theorem theta1_eq_tprod {t : ℝ} (ht : 0 < t) (β : ℝ) :
    theta1 t β = ∏' n : ℕ, (1 - Real.exp (-2 * π * ((n : ℝ) + 1) * t)) *
      (1 + 2 * Real.exp (-(2 * (n : ℝ) + 1) * π * t) * Real.cos (2 * π * β) +
        Real.exp (-2 * (2 * (n : ℝ) + 1) * π * t)) :=
  (theta1_triple_product ht β).tprod_eq.symm

/-! ### Montgomery's Lemma 1 -/

/-- The `n`-th factor of the real triple product as a function of `c = cos 2πβ`:
`(1 - e^{-2π(n+1)t}) (1 + 2 e^{-(2n+1)πt} c + e^{-2(2n+1)πt})`. -/
noncomputable def jtpFactor (t : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  (1 - Real.exp (-2 * π * ((n : ℝ) + 1) * t)) *
    (1 + 2 * Real.exp (-(2 * (n : ℝ) + 1) * π * t) * c +
      Real.exp (-2 * (2 * (n : ℝ) + 1) * π * t))

private theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) (n : ℕ) :
    0 < 1 - Real.exp (-2 * π * ((n : ℝ) + 1) * t) := by
  rw [sub_pos, Real.exp_lt_one_iff]
  have : 0 < π * ((n : ℝ) + 1) * t := by positivity
  linarith

/-- The factors are positive for `c ≥ -1`, since `1 + 2bc + b² ≥ (1 - b)² > 0`. -/
theorem jtpFactor_pos {t : ℝ} (ht : 0 < t) (n : ℕ) {c : ℝ} (hc : -1 ≤ c) :
    0 < jtpFactor t n c := by
  unfold jtpFactor
  have hB1 : Real.exp (-(2 * (n : ℝ) + 1) * π * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < (2 * (n : ℝ) + 1) * π * t := by positivity
    linarith
  have hB0 : 0 < Real.exp (-(2 * (n : ℝ) + 1) * π * t) := Real.exp_pos _
  have hB2 : Real.exp (-2 * (2 * (n : ℝ) + 1) * π * t) =
      Real.exp (-(2 * (n : ℝ) + 1) * π * t) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [hB2]
  refine mul_pos (one_sub_exp_pos ht n) ?_
  nlinarith [mul_nonneg hB0.le (by linarith : (0 : ℝ) ≤ c + 1),
    sq_pos_of_pos (by linarith : (0 : ℝ) < 1 - Real.exp (-(2 * (n : ℝ) + 1) * π * t))]

theorem jtpFactor_monotone {t : ℝ} (ht : 0 < t) (n : ℕ) : Monotone (jtpFactor t n) := by
  intro x y hxy
  unfold jtpFactor
  refine mul_le_mul_of_nonneg_left ?_ (one_sub_exp_pos ht n).le
  have := Real.exp_pos (-(2 * (n : ℝ) + 1) * π * t)
  nlinarith

theorem jtpFactor_convexOn (t : ℝ) (n : ℕ) {s : Set ℝ} (hs : Convex ℝ s) :
    ConvexOn ℝ s (jtpFactor t n) := by
  refine ⟨hs, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
  simp only [jtpFactor, smul_eq_mul]
  linear_combination (-((1 - Real.exp (-2 * π * ((n : ℝ) + 1) * t)) *
    (1 + Real.exp (-2 * (2 * (n : ℝ) + 1) * π * t)))) * hab

/-- The partial products are convex, monotone and nonnegative on `[-1, 1]`. -/
theorem partialProd_jtpFactor {t : ℝ} (ht : 0 < t) (N : ℕ) :
    ConvexOn ℝ (Set.Icc (-1) 1) (fun c => ∏ n ∈ range N, jtpFactor t n c) ∧
      MonotoneOn (fun c => ∏ n ∈ range N, jtpFactor t n c) (Set.Icc (-1) 1) ∧
      ∀ c ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ ∏ n ∈ range N, jtpFactor t n c := by
  induction N with
  | zero =>
    simp only [prod_range_zero]
    exact ⟨convexOn_const 1 (convex_Icc _ _), monotoneOn_const, fun _ _ => zero_le_one⟩
  | succ N ih =>
    obtain ⟨hconv, hmono, hnn⟩ := ih
    simp only [prod_range_succ]
    have hf0 : ∀ c ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ jtpFactor t N c := fun c hc =>
      (jtpFactor_pos ht N hc.1).le
    refine ⟨?_, ?_, ?_⟩
    · exact hconv.mul (jtpFactor_convexOn t N (convex_Icc _ _)) (fun c hc => hnn c hc)
        (fun c hc => hf0 c hc) (hmono.monovaryOn ((jtpFactor_monotone ht N).monotoneOn _))
    · intro x hx y hy hxy
      exact mul_le_mul (hmono hx hy hxy) (jtpFactor_monotone ht N hxy) (hf0 x hx) (hnn y hy)
    · intro c hc
      exact mul_nonneg (hnn c hc) (hf0 c hc)

/-- `Φ(c) = θ(t; arccos(c) / 2π)`, so that `θ(t; β) = Φ(cos 2πβ)` for `β ∈ [0, 1/2]`. -/
noncomputable def thetaCos (t c : ℝ) : ℝ := theta1 t (Real.arccos c / (2 * π))

/-- On `[-1, 1]`, `Φ(c)` is the product of the factors `jtpFactor t n c`. -/
theorem thetaCos_hasProd {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    HasProd (fun n => jtpFactor t n c) (thetaCos t c) := by
  have h := theta1_triple_product ht (Real.arccos c / (2 * π))
  have e : 2 * π * (Real.arccos c / (2 * π)) = Real.arccos c := by
    field_simp
  rw [e, Real.cos_arccos hc.1 hc.2] at h
  exact h

/-- `Φ` is convex on `[-1, 1]`, as a pointwise limit of convex partial products. -/
theorem thetaCos_convexOn {t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Set.Icc (-1) 1) (thetaCos t) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ Set.Icc (-1 : ℝ) 1 := convex_Icc _ _ hx hy ha hb hab
  have h1 := (thetaCos_hasProd ht hxy).tendsto_prod_nat
  have h2 := ((thetaCos_hasProd ht hx).tendsto_prod_nat.const_mul a).add
    ((thetaCos_hasProd ht hy).tendsto_prod_nat.const_mul b)
  simp only [smul_eq_mul] at h1 h2 ⊢
  exact le_of_tendsto_of_tendsto' h1 h2 fun N => by
    simpa only [smul_eq_mul] using (partialProd_jtpFactor ht N).1.2 hx hy ha hb hab

/-- On `(-1, 1)`, `Φ'(c) = Q(t; arccos(c) / 2π) / 2π`. -/
theorem thetaCos_hasDerivAt (hD : Theta1Deriv) {t : ℝ} (ht : 0 < t) {c : ℝ}
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (thetaCos t) (Qser t (Real.arccos c / (2 * π)) / (2 * π)) c := by
  have hs : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hc.1, hc.2])
  have h1 : HasDerivAt (fun x => Real.arccos x / (2 * π))
      (-(1 / Real.sqrt (1 - c ^ 2)) / (2 * π)) c :=
    (Real.hasDerivAt_arccos (ne_of_gt hc.1) (ne_of_lt hc.2)).div_const _
  have h3 := (hD t ht (Real.arccos c / (2 * π))).comp c h1
  have e : 2 * π * (Real.arccos c / (2 * π)) = Real.arccos c := by
    field_simp
  rw [e, Real.sin_arccos] at h3
  have hfun : thetaCos t = theta1 t ∘ fun x => Real.arccos x / (2 * π) := rfl
  rw [hfun]
  convert h3 using 1
  field_simp

private theorem cos_two_pi_mul_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    Real.cos (2 * π * x) ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h0 : 0 < 2 * π * x := by have := hx.1; positivity
  have h1 : 2 * π * x < π := by nlinarith [hx.2, Real.pi_pos]
  constructor
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl h1
    rwa [Real.cos_pi] at this
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl h1.le h0
    rwa [Real.cos_zero] at this

private theorem arccos_cos_two_pi_mul {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Real.arccos (Real.cos (2 * π * x)) / (2 * π) = x := by
  rw [Real.arccos_cos (by nlinarith [hx.1, Real.pi_pos]) (by nlinarith [hx.2, Real.pi_pos])]
  field_simp

/-- Antitone on an open interval and continuous implies antitone on its closure. -/
private theorem antitoneOn_Icc_of_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (h : AntitoneOn f (Set.Ioo a b)) : AntitoneOn f (Set.Icc a b) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  have hm : (x + y) / 2 ∈ Set.Ioo a b := ⟨by linarith [hx.1], by linarith [hy.2]⟩
  have h1 : f y ≤ f ((x + y) / 2) := by
    have hlim : Tendsto f (𝓝[<] y) (𝓝 (f y)) :=
      hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show (x + y) / 2 < y by linarith)] with z hz
    exact h hm ⟨by linarith [hz.1, hm.1], by linarith [hz.2, hy.2]⟩ hz.1.le
  have h2 : f ((x + y) / 2) ≤ f x := by
    have hlim : Tendsto f (𝓝[>] x) (𝓝 (f x)) :=
      hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show x < (x + y) / 2 by linarith)] with z hz
    exact h ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hm.2]⟩ hm hz.2.le
  exact h1.trans h2

/-- **Montgomery, Lemma 1** (monotone part, non-strict): given `Theta1Deriv` and continuity of
`Q(t; ·)`, `Q(t; ·)` decreases on `[0, 1/2]` for every `t > 0`. -/
theorem lemma1_of (hD : Theta1Deriv) (hC : ∀ t : ℝ, 0 < t → Continuous (Qser t)) :
    Lemma1 := by
  intro t ht
  have hconv : ConvexOn ℝ (Set.Ioo (-1) 1) (thetaCos t) :=
    (thetaCos_convexOn ht).subset Set.Ioo_subset_Icc_self (convex_Ioo _ _)
  have hmono : MonotoneOn (deriv (thetaCos t)) (Set.Ioo (-1) 1) :=
    hconv.monotoneOn_deriv fun c hc => (thetaCos_hasDerivAt hD ht hc).differentiableAt
  have hopen : AntitoneOn (Qser t) (Set.Ioo 0 (1 / 2)) := by
    intro x hx y hy hxy
    have hcx := cos_two_pi_mul_mem_Ioo hx
    have hcy := cos_two_pi_mul_mem_Ioo hy
    have hle : Real.cos (2 * π * y) ≤ Real.cos (2 * π * x) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hx.1, Real.pi_pos])
        (by nlinarith [hy.2, Real.pi_pos]) (by nlinarith [Real.pi_pos])
    have hdx := (thetaCos_hasDerivAt hD ht hcx).deriv
    have hdy := (thetaCos_hasDerivAt hD ht hcy).deriv
    rw [arccos_cos_two_pi_mul (Set.Ioo_subset_Icc_self hx)] at hdx
    rw [arccos_cos_two_pi_mul (Set.Ioo_subset_Icc_self hy)] at hdy
    have := hmono hcy hcx hle
    rw [hdx, hdy] at this
    exact (div_le_div_iff_of_pos_right (by positivity)).mp this
  exact antitoneOn_Icc_of_Ioo (hC t ht) hopen

end BccSharp.Coulomb.Montgomery
