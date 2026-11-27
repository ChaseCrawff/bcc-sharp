import BccSharp.TwoSite.Coverage

set_option autoImplicit false

/-! A finite sufficient condition for a chart point to be `good` (valid, reduced
and separated), and its rational form `goodCheck`, checked by `decide`.

A cover leaf certifies something through the cover framework only if its box
meets the `good` points; a box from a dyadic tree can miss the reduced domain
entirely (the Continuation round-seven roots do). `good_of_bounds` reduces the infinite
families of `reductionInequalities` and `separated` to a few inequalities,
using the triangular chart basis

`|B v|² = (r₁ (v₀ + x v₁ + y v₂))² + (r₂ (v₁ + z v₂))² + (v₂ / (r₁ r₂))²`

(`sq_chartBasis`):

* a period with `n₂ ≠ 0` has squared length at least `1/(r₁r₂)²`, so `c1`,
  `c4`;
* a period with `n₂ = 0` and `|n₁| ≥ 2` has squared length at least `4 r₂²`,
  so `c2`;
* a period with `n₂ = 0` and `n₁ = ±1` has squared length at least
  `r₁² x² + r₂²` when `0 ≤ x ≤ 1/2`, so `c3`;
* the second site has squared distance at least `d²/(r₁ r₂)²` from every
  lattice point when the third offset coordinate is at distance at least `d`
  from the integers (`c5`).
-/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover

theorem sq_chartBasis (p : Chart) (v : Vec) :
    sq ((chartBasis p).mulVec v) = (p 0 * (v 0 + p 2 * v 1 + p 3 * v 2)) ^ 2 +
      (p 1 * (v 1 + p 4 * v 2)) ^ 2 + (v 2 * (p 0 * p 1)⁻¹) ^ 2 := by
  simp [sq, chartBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- An integer shift of a point at distance at least `d` from the integers
stays at distance at least `d` from zero. -/
theorem shift_sq_ge (m k : ℤ) (x d : ℝ) (hd : 0 ≤ d) (lo : (k : ℝ) + d ≤ x)
    (hi : x ≤ (k : ℝ) + 1 - d) : d ^ 2 ≤ ((m : ℝ) + x) ^ 2 := by
  rcases le_or_gt (-k) m with h | h
  · have hm : -(k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have e : d ≤ (m : ℝ) + x := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr e) (by linarith : (0 : ℝ) ≤ (m : ℝ) + x + d)]
  · have h' : m ≤ -k - 1 := by omega
    have hm : (m : ℝ) ≤ -(k : ℝ) - 1 := by exact_mod_cast h'
    have e : (m : ℝ) + x ≤ -d := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -((m : ℝ) + x) - d)
      (by linarith : (0 : ℝ) ≤ -((m : ℝ) + x) + d)]

theorem one_le_sq_int {n : ℤ} (h : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ≤ n ^ 2 := by
    rcases lt_or_gt_of_ne h with h | h
    · nlinarith
    · nlinarith
  exact_mod_cast h1

theorem four_le_sq_int {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ -1) : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h4 : (4 : ℤ) ≤ n ^ 2 := by
    rcases lt_or_gt_of_ne h0 with h | h
    · have : n ≤ -2 := by omega
      nlinarith
    · have : 2 ≤ n := by omega
      nlinarith
  exact_mod_cast h4

/-- The first family of `reductionInequalities`: `B e₁` is a shortest period. -/
theorem reduced_first (p : Chart) (h2lo : 0 ≤ p 2) (h2hi : p 2 ≤ 1 / 2)
    (c1 : (p 0) ^ 2 ≤ ((p 0 * p 1)⁻¹) ^ 2) (c2 : (p 0) ^ 2 ≤ 4 * (p 1) ^ 2)
    (c3 : (p 0) ^ 2 ≤ (p 0) ^ 2 * (p 2) ^ 2 + (p 1) ^ 2) (n : IntVec) (hn : n ≠ 0) :
    (p 0) ^ 2 ≤ sq ((chartBasis p).mulVec (castVec n)) := by
  rw [sq_chartBasis]
  simp only [castVec]
  have u0 := sq_nonneg (p 0 * ((n 0 : ℝ) + p 2 * (n 1 : ℝ) + p 3 * (n 2 : ℝ)))
  have u1 := sq_nonneg (p 1 * ((n 1 : ℝ) + p 4 * (n 2 : ℝ)))
  have u2 := sq_nonneg ((n 2 : ℝ) * (p 0 * p 1)⁻¹)
  by_cases hc : n 2 = 0
  · have c0 : ((n 2 : ℤ) : ℝ) = 0 := by exact_mod_cast hc
    rw [c0]
    by_cases hb : n 1 = 0
    · have b0 : ((n 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hb
      have ha : n 0 ≠ 0 := by
        intro ha
        apply hn
        funext i
        fin_cases i
        · exact ha
        · exact hb
        · exact hc
      have a1 := one_le_sq_int ha
      rw [b0]
      have e : (p 0 * ((n 0 : ℝ) + p 2 * 0 + p 3 * 0)) ^ 2 = (p 0) ^ 2 * (n 0 : ℝ) ^ 2 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left a1 (sq_nonneg (p 0)), sq_nonneg (p 1 * (0 + p 4 * 0)),
        sq_nonneg ((0 : ℝ) * (p 0 * p 1)⁻¹)]
    · by_cases hb1 : n 1 = 1
      · have b1 : ((n 1 : ℤ) : ℝ) = 1 := by exact_mod_cast hb1
        rw [b1]
        have s := shift_sq_ge (n 0) 0 (p 2) (p 2) h2lo (by simp) (by push_cast; linarith)
        have e1 : (p 0 * ((n 0 : ℝ) + p 2 * 1 + p 3 * 0)) ^ 2 = (p 0) ^ 2 * ((n 0 : ℝ) + p 2) ^ 2 := by
          ring
        have e2 : (p 1 * (1 + p 4 * 0)) ^ 2 = (p 1) ^ 2 := by ring
        rw [e1, e2]
        nlinarith [mul_le_mul_of_nonneg_left s (sq_nonneg (p 0)), sq_nonneg ((0 : ℝ) * (p 0 * p 1)⁻¹)]
      · by_cases hbm : n 1 = -1
        · have b1 : ((n 1 : ℤ) : ℝ) = -1 := by exact_mod_cast hbm
          rw [b1]
          have s := shift_sq_ge (-n 0) 0 (p 2) (p 2) h2lo (by simp) (by push_cast; linarith)
          have e1 : (p 0 * ((n 0 : ℝ) + p 2 * -1 + p 3 * 0)) ^ 2 =
              (p 0) ^ 2 * (((-n 0 : ℤ) : ℝ) + p 2) ^ 2 := by
            push_cast; ring
          have e2 : (p 1 * (-1 + p 4 * 0)) ^ 2 = (p 1) ^ 2 := by ring
          rw [e1, e2]
          nlinarith [mul_le_mul_of_nonneg_left s (sq_nonneg (p 0)),
            sq_nonneg ((0 : ℝ) * (p 0 * p 1)⁻¹)]
        · have b4 := four_le_sq_int hb hb1 hbm
          have e2 : (p 1 * ((n 1 : ℝ) + p 4 * 0)) ^ 2 = (p 1) ^ 2 * (n 1 : ℝ) ^ 2 := by ring
          rw [e2]
          nlinarith [mul_le_mul_of_nonneg_left b4 (sq_nonneg (p 1)),
            sq_nonneg (p 0 * ((n 0 : ℝ) + p 2 * (n 1 : ℝ) + p 3 * 0)),
            sq_nonneg ((0 : ℝ) * (p 0 * p 1)⁻¹)]
  · have c1' := one_le_sq_int hc
    have e : ((n 2 : ℝ) * (p 0 * p 1)⁻¹) ^ 2 = (n 2 : ℝ) ^ 2 * ((p 0 * p 1)⁻¹) ^ 2 := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right c1' (sq_nonneg ((p 0 * p 1)⁻¹))]

/-- **Good points from finitely many inequalities.** -/
theorem good_of_bounds (p : Chart) (h0 : 5 / 8 < p 0) (h1 : 0 < p 1) (h2lo : 0 ≤ p 2)
    (h2hi : p 2 ≤ 1 / 2) (c1 : (p 0) ^ 2 ≤ ((p 0 * p 1)⁻¹) ^ 2) (c2 : (p 0) ^ 2 ≤ 4 * (p 1) ^ 2)
    (c3 : (p 0) ^ 2 ≤ (p 0) ^ 2 * (p 2) ^ 2 + (p 1) ^ 2) (c4 : (p 1) ^ 2 ≤ ((p 0 * p 1)⁻¹) ^ 2)
    (k5 : ℤ) (lo5 : (k5 : ℝ) < p 5) (hi5 : p 5 < (k5 : ℝ) + 1)
    (k7 : ℤ) (d : ℝ) (hd : 0 ≤ d) (lo7 : (k7 : ℝ) + d ≤ p 7) (hi7 : p 7 ≤ (k7 : ℝ) + 1 - d)
    (c5 : 1 / 4 < d ^ 2 * ((p 0 * p 1)⁻¹) ^ 2) : good p := by
  have p0 : 0 < p 0 := by linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- determinant one
    have e : (chartPoint p).basis.det = p 0 * p 1 * (p 0 * p 1)⁻¹ := by
      simp [chartPoint, chartBasis, Matrix.det_fin_three]
    rw [e]
    exact mul_inv_cancel₀ (mul_ne_zero p0.ne' h1.ne')
  · -- non-integral offset
    intro n hn
    have e5 : p 5 = ((n 0 : ℤ) : ℝ) := congrFun hn 0
    have a : k5 < n 0 := by
      have h : (k5 : ℝ) < ((n 0 : ℤ) : ℝ) := by rw [← e5]; exact lo5
      exact_mod_cast h
    have c : n 0 < k5 + 1 := by
      have h : ((n 0 : ℤ) : ℝ) < (k5 : ℝ) + 1 := by rw [← e5]; exact hi5
      exact_mod_cast h
    omega
  · -- `B e₁` is a shortest period
    exact reduced_first p h2lo h2hi c1 c2 c3
  · -- the second reduction inequality
    intro j k hjk
    have u := sq_nonneg (p 1 * ((j : ℝ) + p 4 * (k : ℝ)))
    by_cases hk : k = 0
    · have hj : j ≠ 0 := by
        rcases hjk with h | h
        · exact h
        · exact absurd hk h
      have k0 : ((k : ℤ) : ℝ) = 0 := by exact_mod_cast hk
      rw [k0]
      have j1 := one_le_sq_int hj
      have e : (p 1 * ((j : ℝ) + p 4 * 0)) ^ 2 = (p 1) ^ 2 * (j : ℝ) ^ 2 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left j1 (sq_nonneg (p 1)), sq_nonneg ((0 : ℝ) / (p 0 * p 1))]
    · have k1 := one_le_sq_int hk
      have e : ((k : ℝ) / (p 0 * p 1)) ^ 2 = (k : ℝ) ^ 2 * ((p 0 * p 1)⁻¹) ^ 2 := by
        rw [div_eq_mul_inv]; ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right k1 (sq_nonneg ((p 0 * p 1)⁻¹))]
  · -- separation of the periods
    intro n hn
    have r := reduced_first p h2lo h2hi c1 c2 c3 n hn
    have : (5 / 8 : ℝ) ^ 2 < (p 0) ^ 2 := by nlinarith
    exact lt_of_lt_of_le this r
  · -- separation of the second site
    intro n
    show (1 / 2 : ℝ) ^ 2 < sq ((chartBasis p).mulVec (castVec n + ![p 5, p 6, p 7]))
    rw [sq_chartBasis]
    have v2 : (castVec n + ![p 5, p 6, p 7]) 2 = (n 2 : ℝ) + p 7 := by
      simp [castVec]
    rw [v2]
    have s := shift_sq_ge (n 2) k7 (p 7) d hd lo7 hi7
    have e : (((n 2 : ℝ) + p 7) * (p 0 * p 1)⁻¹) ^ 2 =
        ((n 2 : ℝ) + p 7) ^ 2 * ((p 0 * p 1)⁻¹) ^ 2 := by ring
    rw [e]
    have m := mul_le_mul_of_nonneg_right s (sq_nonneg ((p 0 * p 1)⁻¹))
    nlinarith [sq_nonneg (p 0 * ((castVec n + ![p 5, p 6, p 7]) 0 +
        p 2 * (castVec n + ![p 5, p 6, p 7]) 1 + p 3 * ((n 2 : ℝ) + p 7))),
      sq_nonneg (p 1 * ((castVec n + ![p 5, p 6, p 7]) 1 + p 4 * ((n 2 : ℝ) + p 7)))]

/-- The conditions of `good_of_bounds` at a rational point, with integers `k5`,
`k7` and a rational distance `d`. -/
def GoodBounds (q : Fin 8 → ℚ) (k5 k7 : ℤ) (d : ℚ) : Prop :=
  5 / 8 < q 0 ∧ 0 < q 1 ∧ 0 ≤ q 2 ∧ q 2 ≤ 1 / 2 ∧ q 0 ^ 2 ≤ ((q 0 * q 1)⁻¹) ^ 2 ∧
    q 0 ^ 2 ≤ 4 * q 1 ^ 2 ∧ q 0 ^ 2 ≤ q 0 ^ 2 * q 2 ^ 2 + q 1 ^ 2 ∧
    q 1 ^ 2 ≤ ((q 0 * q 1)⁻¹) ^ 2 ∧ (k5 : ℚ) < q 5 ∧ q 5 < (k5 : ℚ) + 1 ∧ 0 ≤ d ∧
    (k7 : ℚ) + d ≤ q 7 ∧ q 7 ≤ (k7 : ℚ) + 1 - d ∧ 1 / 4 < d ^ 2 * ((q 0 * q 1)⁻¹) ^ 2

instance (q : Fin 8 → ℚ) (k5 k7 : ℤ) (d : ℚ) : Decidable (GoodBounds q k5 k7 d) := by
  unfold GoodBounds; infer_instance

def goodCheck (q : Fin 8 → ℚ) (k5 k7 : ℤ) (d : ℚ) : Bool := decide (GoodBounds q k5 k7 d)

/-- A rational point that passes `goodCheck` is `good`. -/
theorem good_of_check (q : Fin 8 → ℚ) (k5 k7 : ℤ) (d : ℚ) (h : goodCheck q k5 k7 d = true) :
    good (fun i => (q i : ℝ)) := by
  obtain ⟨h0, h1, h2, h3, c1, c2, c3, c4, l5, u5, hd, l7, u7, c5⟩ :=
    (of_decide_eq_true h : GoodBounds q k5 k7 d)
  have r0 := (Rat.cast_lt (K := ℝ)).mpr h0
  have r1 := (Rat.cast_lt (K := ℝ)).mpr h1
  have r2 := (Rat.cast_le (K := ℝ)).mpr h2
  have r3 := (Rat.cast_le (K := ℝ)).mpr h3
  have s1 := (Rat.cast_le (K := ℝ)).mpr c1
  have s2 := (Rat.cast_le (K := ℝ)).mpr c2
  have s3 := (Rat.cast_le (K := ℝ)).mpr c3
  have s4 := (Rat.cast_le (K := ℝ)).mpr c4
  have t5 := (Rat.cast_lt (K := ℝ)).mpr l5
  have v5 := (Rat.cast_lt (K := ℝ)).mpr u5
  have td := (Rat.cast_le (K := ℝ)).mpr hd
  have t7 := (Rat.cast_le (K := ℝ)).mpr l7
  have v7 := (Rat.cast_le (K := ℝ)).mpr u7
  have s5 := (Rat.cast_lt (K := ℝ)).mpr c5
  push_cast at r0 r1 r2 r3 s1 s2 s3 s4 t5 v5 td t7 v7 s5
  exact good_of_bounds (fun i => (q i : ℝ)) r0 r1 r2 r3 s1 s2 s3 s4 k5 t5 v5 k7 (d : ℝ) td t7 v7 s5

end BccSharp.Coulomb.CompactCover
