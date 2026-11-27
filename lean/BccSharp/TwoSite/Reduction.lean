import BccSharp.TwoSite.Coverage
import BccSharp.TwoSite.Reference

set_option autoImplicit false

/-! Rational part of the Series compact reduction. This starts after an
oriented size-reduced shortest-vector basis has been obtained. -/

noncomputable section

namespace BccSharp.Coulomb

private theorem ratio_from_squares {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : (3/4 : ℝ) * a^2 ≤ b^2) : (173/200 : ℝ) * a ≤ b := by
  have hconst : (0 : ℝ) ≤ 3/4 - (173/200 : ℝ)^2 := by norm_num
  have hdiff := mul_nonneg hconst (sq_nonneg a)
  by_contra! hn
  have hpos := mul_pos (sub_pos.mpr hn)
    (add_pos (mul_pos (by norm_num : (0 : ℝ) < 173/200) ha) hb)
  nlinarith

private theorem product_strict {a b c x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : a < x) (hy : b < y) (hz : c < z) :
    a * b * c < x * y * z := by
  have hx' := ha.trans hx
  have hy' := hb.trans hy
  calc
    a * b * c < x * b * c := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hx hb) hc
    _ < x * y * c := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hy hx') hc
    _ < x * y * z := mul_lt_mul_of_pos_left hz (mul_pos hx' hy')

theorem compact_diagonal {r₁ r₂ r₃ : ℝ} (h₁ : (5/8 : ℝ) < r₁) (h₂ : 0 < r₂) (h₃ : 0 < r₃)
    (hdet : r₁ * r₂ * r₃ = 1) (h₁₂ : (3/4 : ℝ) * r₁^2 ≤ r₂^2)
    (h₂₃ : (3/4 : ℝ) * r₂^2 ≤ r₃^2) :
    r₁ ∈ Set.Icc (5/8 : ℝ) (37/32) ∧ r₂ ∈ Set.Icc (1/2 : ℝ) (11/8) := by
  have h₁pos : 0 < r₁ := (by norm_num : (0 : ℝ) < 5/8).trans h₁
  have hp := ratio_from_squares h₁pos h₂ h₁₂
  have hq := ratio_from_squares h₂ h₃ h₂₃
  have h₁hi : r₁ ≤ (37/32 : ℝ) := by
    by_contra! hu
    have ha : (173/200 : ℝ) * (37/32) < r₂ := by linarith
    have hb : (173/200 : ℝ)^2 * (37/32) < r₃ := by linarith
    have h := product_strict (by norm_num) (by norm_num) (by norm_num) hu ha hb
    rw [hdet] at h
    norm_num at h
  have h₂lo : (1/2 : ℝ) ≤ r₂ := by linarith
  have h₂hi : r₂ ≤ (11/8 : ℝ) := by
    by_contra! hu
    have ha : (173/200 : ℝ) * (11/8) < r₃ := by linarith
    have h := product_strict (by norm_num) (by norm_num) (by norm_num) h₁ hu ha
    rw [hdet] at h
    norm_num at h
  exact ⟨⟨h₁.le, h₁hi⟩, ⟨h₂lo, h₂hi⟩⟩

/-- The large chart from size reduction can be narrowed using the uniform
escape and only the two coordinate-vector instances of KZ. -/
theorem compact_of_reduced (p : Chart) (h₁ : (5/8 : ℝ) < p 0) (h₂ : 0 < p 1)
    (hx : p 2 ∈ Set.Icc (0 : ℝ) (1/2)) (hy : p 3 ∈ Set.Icc (0 : ℝ) (1/2))
    (small : ∀ i : Fin 8, 4 ≤ i.val → p i ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hred : reductionInequalities p) : inRoot p := by
  let r₃ := (p 0 * p 1)⁻¹
  have h₁pos : 0 < p 0 := (by norm_num : (0 : ℝ) < 5/8).trans h₁
  have h₃ : 0 < r₃ := inv_pos.mpr (mul_pos h₁pos h₂)
  have hdet : p 0 * p 1 * r₃ = 1 := by
    dsimp [r₃]
    exact mul_inv_cancel₀ (mul_ne_zero h₁pos.ne' h₂.ne')
  have hb₂ : (p 0)^2 ≤ (p 0 * p 2)^2 + (p 1)^2 := by
    have h := hred.1 (![0, 1, 0] : IntVec) (by decide)
    simpa [sq, chartBasis, Matrix.mulVec, dotProduct, castVec, Fin.sum_univ_three] using h
  have hxSq : (p 2)^2 ≤ (1/4 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hx.1 (by norm_num : (0 : ℝ) ≤ 1/2))]
  have h₁₂ : (3/4 : ℝ) * (p 0)^2 ≤ (p 1)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hxSq (sq_nonneg (p 0))]
  have hb₃ : (p 1)^2 ≤ (p 1 * p 4)^2 + r₃^2 := by
    have h := hred.2 0 1 (Or.inr (by decide))
    simpa [r₃, one_div] using h
  have hz := small 4 (by decide)
  have hzSq : (p 4)^2 ≤ (1/4 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2)
      (show 0 ≤ (1/2 : ℝ) + p 4 by linarith [hz.1])]
  have h₂₃ : (3/4 : ℝ) * (p 1)^2 ≤ r₃^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hzSq (sq_nonneg (p 1))]
  obtain ⟨hr₁, hr₂⟩ := compact_diagonal h₁ h₂ h₃ hdet h₁₂ h₂₃
  exact ⟨hr₁, hr₂, hx, hy, small⟩

end BccSharp.Coulomb
