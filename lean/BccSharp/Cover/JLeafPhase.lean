import BccSharp.Cover.JLeafCore

set_option autoImplicit false

/-! Scalar analysis behind the reciprocal terms of the J-leaf energy support.

* `phase_secant`: on an interval that avoids every half-integer,
  `log (1 + cos 2πt)` is concave, so an exponential-affine function lying below
  `1 + cos 2πt` at both endpoints lies below it on the whole interval
  (Stage5b's log-phase secant).
* `g1_tangent`: `exp(-y) / y` times an exponential phase factor is log-convex
  jointly in `(y, ℓ)`, and its tangent plane is a lower bound everywhere.
* `persp_lower`: near an extinction, `1 + cos 2πt = 2 sin²(πz)` is at least a
  multiple of `z²`, which gives the perspective lower bound `2uz − u²R` for every
  real `u`.
* `secant_mul_exp`: `y ↦ y eʸ` lies below its secant on `[y₁, y₂] ⊂ [0, ∞)`.

Nothing here depends on certificate data. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.JLeaf
open Real

theorem one_add_cos_eq (t : ℝ) (k : ℤ) :
    1 + Real.cos (2 * π * t) = 2 * Real.cos (π * (t - k)) ^ 2 := by
  have e : 2 * π * t = 2 * (π * (t - k)) + (k : ℝ) * (2 * π) := by ring
  rw [e, Real.cos_add_int_mul_two_pi, Real.cos_two_mul]
  ring

private theorem cos_pos_window {k : ℤ} {s : ℝ} (lo : (k : ℝ) - 1 / 2 < s)
    (hi : s < (k : ℝ) + 1 / 2) : 0 < Real.cos (π * (s - k)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private theorem window_mem {k : ℤ} {s : ℝ} (lo : (k : ℝ) - 1 / 2 < s)
    (hi : s < (k : ℝ) + 1 / 2) : π * (s - k) ∈ Set.Icc (-(π / 2)) (π / 2) := by
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- Stage5b log-phase secant. -/
theorem phase_secant (k : ℤ) (L R a b c t : ℝ) (hL : (k : ℝ) - 1 / 2 < L)
    (hR : R < (k : ℝ) + 1 / 2) (hLt : L ≤ t) (htR : t ≤ R)
    (eL : Real.exp (a + b * (L - c)) ≤ 1 + Real.cos (2 * π * L))
    (eR : Real.exp (a + b * (R - c)) ≤ 1 + Real.cos (2 * π * R)) :
    Real.exp (a + b * (t - c)) ≤ 1 + Real.cos (2 * π * t) := by
  rcases eq_or_lt_of_le (hLt.trans htR) with same | lt
  · have tL : t = L := le_antisymm (htR.trans_eq same.symm) hLt
    subst tL
    exact eL
  have hR' : R - L > 0 := sub_pos.mpr lt
  set lam := (t - L) / (R - L) with hlam
  have lam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hLt) hR'.le
  have lam1 : lam ≤ 1 := (div_le_one hR').mpr (by linarith)
  have tEq : t = (1 - lam) * L + lam * R := by
    rw [hlam]; field_simp; ring
  have tlo : (k : ℝ) - 1 / 2 < t := hL.trans_le hLt
  have thi : t < (k : ℝ) + 1 / 2 := htR.trans_lt hR
  have Llo := hL
  have Lhi : L < (k : ℝ) + 1 / 2 := (hLt.trans htR).trans_lt hR
  have Rlo : (k : ℝ) - 1 / 2 < R := hL.trans_le (hLt.trans htR)
  have Rhi := hR
  set cL := Real.cos (π * (L - k))
  set cR := Real.cos (π * (R - k))
  set ct := Real.cos (π * (t - k))
  have pL : 0 < cL := cos_pos_window Llo Lhi
  have pR : 0 < cR := cos_pos_window Rlo Rhi
  have pt : 0 < ct := cos_pos_window tlo thi
  -- Concavity of cosine on the window.
  have conc := (strictConcaveOn_cos_Icc).concaveOn.2 (window_mem Llo Lhi) (window_mem Rlo Rhi)
    (sub_nonneg.mpr lam1) lam0 (by ring)
  have argEq : (1 - lam) • (π * (L - k)) + lam • (π * (R - k)) = π * (t - k) := by
    simp only [smul_eq_mul]
    rw [tEq]
    ring
  rw [argEq] at conc
  simp only [smul_eq_mul] at conc
  -- Concavity and monotonicity of the logarithm.
  have mix : 0 < (1 - lam) * cL + lam * cR := by
    rcases eq_or_lt_of_le lam0 with z | z
    · rw [← z]; simpa using pL
    · nlinarith [mul_pos z pR, mul_nonneg (sub_nonneg.mpr lam1) pL.le]
  have logConc := (strictConcaveOn_log_Ioi).concaveOn.2 (Set.mem_Ioi.mpr pL) (Set.mem_Ioi.mpr pR)
    (sub_nonneg.mpr lam1) lam0 (by ring)
  simp only [smul_eq_mul] at logConc
  have logMono : Real.log ((1 - lam) * cL + lam * cR) ≤ Real.log ct :=
    Real.log_le_log mix conc
  -- Endpoint inequalities in logarithmic form.
  have eqL : 1 + Real.cos (2 * π * L) = 2 * cL ^ 2 := one_add_cos_eq L k
  have eqR : 1 + Real.cos (2 * π * R) = 2 * cR ^ 2 := one_add_cos_eq R k
  have eqt : 1 + Real.cos (2 * π * t) = 2 * ct ^ 2 := one_add_cos_eq t k
  have lL : a + b * (L - c) ≤ Real.log 2 + 2 * Real.log cL := by
    have h := (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < 2 * cL ^ 2)).mpr (eqL ▸ eL)
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
  have lR : a + b * (R - c) ≤ Real.log 2 + 2 * Real.log cR := by
    have h := (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < 2 * cR ^ 2)).mpr (eqR ▸ eR)
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
  have line : a + b * (t - c) = (1 - lam) * (a + b * (L - c)) + lam * (a + b * (R - c)) := by
    rw [tEq]; ring
  have bound : a + b * (t - c) ≤ Real.log (2 * ct ^ 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, line]
    have h1 := mul_le_mul_of_nonneg_left lL (sub_nonneg.mpr lam1)
    have h2 := mul_le_mul_of_nonneg_left lR lam0
    push_cast
    nlinarith [logConc, logMono]
  rw [eqt]
  calc Real.exp (a + b * (t - c)) ≤ Real.exp (Real.log (2 * ct ^ 2)) := Real.exp_le_exp.mpr bound
    _ = 2 * ct ^ 2 := Real.exp_log (by positivity)

/-- Tangent plane of the log-convex function `(y, ℓ) ↦ exp(-y + ℓ) / y`. -/
theorem g1_tangent (xb y lb l : ℝ) (hxb : 0 < xb) (hy : 0 < y) :
    Real.exp (-xb + lb) / xb * (1 + (-1 - 1 / xb) * (y - xb) + (l - lb)) ≤
      Real.exp (-y + l) / y := by
  set Y := -y + l - Real.log y
  set Yb := -xb + lb - Real.log xb
  have hY : Real.exp (-y + l) / y = Real.exp Y := by
    simp only [Y]
    rw [Real.exp_sub, Real.exp_log hy]
  have hYb : Real.exp (-xb + lb) / xb = Real.exp Yb := by
    simp only [Yb]
    rw [Real.exp_sub, Real.exp_log hxb]
  rw [hY, hYb]
  have logBound : Real.log y - Real.log xb ≤ (y - xb) / xb := by
    rw [← Real.log_div hy.ne' hxb.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hy hxb)
    have e : y / xb - 1 = (y - xb) / xb := by field_simp
    linarith
  have lin : 1 + (-1 - 1 / xb) * (y - xb) + (l - lb) ≤ 1 + (Y - Yb) := by
    have e : (-1 - 1 / xb) * (y - xb) = -(y - xb) - (y - xb) / xb := by field_simp
    rw [e]
    simp only [Y, Yb]
    linarith
  have tangentExp : Real.exp Yb * (1 + (Y - Yb)) ≤ Real.exp Y := by
    have h := Real.add_one_le_exp (Y - Yb)
    have e : Real.exp Y = Real.exp Yb * Real.exp (Y - Yb) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos Yb).le
    linarith
  exact (mul_le_mul_of_nonneg_left lin (Real.exp_pos Yb).le).trans tangentExp

/-- Chord bound for sine: `sin (π |z|) ≥ (|z| / d) sin (π d)` for `|z| ≤ d ≤ 1`. -/
private theorem sin_chord (z d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) (hz : |z| ≤ d) :
    |z| / d * Real.sin (π * d) ≤ Real.sin (π * |z|) := by
  set lam := |z| / d
  have lam0 : 0 ≤ lam := div_nonneg (abs_nonneg z) hd.le
  have lam1 : lam ≤ 1 := (div_le_one hd).mpr hz
  have m0 : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have m1 : π * d ∈ Set.Icc 0 π := ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have h := (strictConcaveOn_sin_Icc).concaveOn.2 m0 m1 (sub_nonneg.mpr lam1) lam0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at h
  have e : lam * (π * d) = π * |z| := by
    simp only [lam]; field_simp
  rw [e] at h
  linarith

/-- Corner (1): perspective lower bound at an extinction `t = z + k + 1/2`. -/
theorem persp_lower (k : ℤ) (z d κ u y : ℝ) (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hz : |z| ≤ d)
    (hκ : 0 < κ) (hκd : κ * d ^ 2 ≤ 4 * Real.sin (π * d) ^ 2) (hy : 0 < y) :
    2 * u * z - u ^ 2 * (y * Real.exp y / κ) ≤
      2 * ((1 + Real.cos (2 * π * (z + k + 1 / 2))) * (Real.exp (-y) / y)) := by
  -- `1 + cos(2π(z + k + 1/2)) = 2 sin²(πz)`.
  have phase : 1 + Real.cos (2 * π * (z + k + 1 / 2)) = 2 * Real.sin (π * z) ^ 2 := by
    have e : 2 * π * (z + k + 1 / 2) = (2 * (π * z) + π) + (k : ℝ) * (2 * π) := by ring
    rw [e, Real.cos_add_int_mul_two_pi, Real.cos_add_pi, Real.cos_two_mul, Real.cos_sq']
    ring
  -- `4 sin²(πz) ≥ κ z²`.
  have chord := sin_chord z d hd (by linarith) hz
  have sAbs : Real.sin (π * z) ^ 2 = Real.sin (π * |z|) ^ 2 := by
    rcases abs_choice z with h | h
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, neg_sq]
  have sdNonneg : 0 ≤ Real.sin (π * d) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have lhsNonneg : 0 ≤ |z| / d * Real.sin (π * d) := mul_nonneg (div_nonneg (abs_nonneg z) hd.le) sdNonneg
  have sq1 : (|z| / d * Real.sin (π * d)) ^ 2 ≤ Real.sin (π * |z|) ^ 2 :=
    pow_le_pow_left₀ lhsNonneg chord 2
  have kz : κ * z ^ 2 ≤ 4 * Real.sin (π * z) ^ 2 := by
    rw [sAbs]
    have e : (|z| / d * Real.sin (π * d)) ^ 2 = z ^ 2 * Real.sin (π * d) ^ 2 / d ^ 2 := by
      rw [div_mul_eq_mul_div, div_pow, mul_pow, sq_abs]
    rw [e] at sq1
    have d2 : 0 < d ^ 2 := by positivity
    have h1 : κ * z ^ 2 * d ^ 2 ≤ 4 * Real.sin (π * d) ^ 2 * z ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hκd (sq_nonneg z)]
    have h2 : z ^ 2 * Real.sin (π * d) ^ 2 ≤ Real.sin (π * |z|) ^ 2 * d ^ 2 :=
      (div_le_iff₀ d2).mp sq1
    nlinarith
  -- Assemble with `z² / R ≥ 2uz − u²R`, `R = y eʸ / κ`.
  set R := y * Real.exp y / κ with hRdef
  have Rpos : 0 < R := by positivity
  have amgm : 2 * u * z - u ^ 2 * R ≤ z ^ 2 / R := by
    rw [le_div_iff₀ Rpos]
    nlinarith [sq_nonneg (z - u * R)]
  have value : z ^ 2 / R = κ * z ^ 2 * (Real.exp (-y) / y) := by
    rw [hRdef, Real.exp_neg]
    field_simp
  rw [phase]
  have g1 : 0 ≤ Real.exp (-y) / y := by positivity
  have last : κ * z ^ 2 * (Real.exp (-y) / y) ≤ 2 * (2 * Real.sin (π * z) ^ 2 * (Real.exp (-y) / y)) := by
    nlinarith [mul_le_mul_of_nonneg_right kz g1]
  linarith [amgm, value ▸ last]

/-- Secant bound for the convex function `y ↦ y eʸ` on `[y₁, y₂] ⊂ [0, ∞)`. -/
theorem secant_mul_exp (y1 y2 y : ℝ) (h1 : 0 ≤ y1) (hy1 : y1 ≤ y) (hy2 : y ≤ y2) :
    y * Real.exp y * (y2 - y1) ≤ (y2 - y) * (y1 * Real.exp y1) + (y - y1) * (y2 * Real.exp y2) := by
  rcases eq_or_lt_of_le (hy1.trans hy2) with same | lt
  · have : y = y1 := le_antisymm (hy2.trans_eq same.symm) hy1
    subst this
    have : y2 = y := same.symm
    subst this
    simp
  have w : y2 - y1 > 0 := sub_pos.mpr lt
  set lam := (y - y1) / (y2 - y1)
  have lam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hy1) w.le
  have lam1 : lam ≤ 1 := (div_le_one w).mpr (by linarith)
  have yEq : y = (1 - lam) * y1 + lam * y2 := by simp only [lam]; field_simp; ring
  have conv := (convexOn_exp).2 (Set.mem_univ y1) (Set.mem_univ y2) (sub_nonneg.mpr lam1) lam0 (by ring)
  simp only [smul_eq_mul] at conv
  rw [← yEq] at conv
  have ynn : 0 ≤ y := h1.trans hy1
  have step := mul_le_mul_of_nonneg_left conv ynn
  -- Chebyshev: the cross term is nonnegative.
  have cheb : 0 ≤ (y2 - y1) * (Real.exp y2 - Real.exp y1) :=
    mul_nonneg w.le (sub_nonneg.mpr (Real.exp_le_exp.mpr lt.le))
  have key : y * ((1 - lam) * Real.exp y1 + lam * Real.exp y2) ≤
      (1 - lam) * (y1 * Real.exp y1) + lam * (y2 * Real.exp y2) := by
    rw [yEq]
    nlinarith [mul_nonneg (mul_nonneg lam0 (sub_nonneg.mpr lam1)) cheb]
  have lhs := step.trans key
  have e1 : (1 - lam) * (y2 - y1) = y2 - y := by simp only [lam]; field_simp; ring
  have e2 : lam * (y2 - y1) = y - y1 := by simp only [lam]; field_simp
  have := mul_le_mul_of_nonneg_right lhs w.le
  calc y * Real.exp y * (y2 - y1) ≤
        ((1 - lam) * (y1 * Real.exp y1) + lam * (y2 * Real.exp y2)) * (y2 - y1) := this
    _ = (y2 - y) * (y1 * Real.exp y1) + (y - y1) * (y2 * Real.exp y2) := by
        rw [← e1, ← e2]; ring

end BccSharp.Coulomb.CompactCover.JLeaf
