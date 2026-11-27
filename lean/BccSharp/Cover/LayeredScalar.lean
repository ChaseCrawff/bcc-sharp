import BccSharp.Cover.OverlayAxial

set_option autoImplicit false

/-! # Scalar estimates for the layered half-height comparison

The planar layer value of a two-site chart is a sum over waves `m` and axial
pairs `n` (`OverlayPlanar.axialPair`). Only the cross-coset part of a pair
(`crossPair`) depends on the offset. About a half-height anchor (height
`1/2`, lateral phase `u'` with `2u' ∈ ℤ`) its change is
`2 e^{-t(n+1/2)} · pairGain P γₙ a ψ` (`crossPair_sub_anchor`), where
`P = cos(2πu') = ±1`, `γₙ = π(2n+1)w`, `a = t(h−1/2)` and
`ψ = 2π(u−u'+w(h−1/2))`. This module proves the identity, a lower bound of
`pairGain` by its second-order terms with explicit remainders
(`pairGain_lower`), and an absolute bound (`abs_pairGain_le`).

The remainders use `1 − cos x ≥ x²/2 − x⁴/24`, `cosh a − 1 ≤ (a²/2)e^{|a|}`,
`|sinh a − a| ≤ |a|(cosh a − 1)` and Mathlib's `|x − sin x| ≤ |x|³/6`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.OverlayPlanar

/-! ### Trigonometric remainder -/

theorem one_sub_cos_ge (x : ℝ) : x ^ 2 / 2 - x ^ 4 / 24 ≤ 1 - Real.cos x := by
  set y := x / 2 with hy
  have hc : Real.cos x = 1 - 2 * Real.sin y ^ 2 := by
    have h2 : x = 2 * y := by rw [hy]; ring
    rw [h2, Real.cos_two_mul, Real.cos_sq']
    ring
  have hx2 : x ^ 2 = 4 * y ^ 2 := by rw [hy]; ring
  have hx4 : x ^ 4 = 16 * y ^ 4 := by rw [hy]; ring
  rw [hc, hx2, hx4]
  set a := |y| with ha
  have a0 : 0 ≤ a := abs_nonneg y
  have ay2 : a ^ 2 = y ^ 2 := sq_abs y
  have ay4 : a ^ 4 = y ^ 4 := by
    have : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [this, ay2]; ring
  have ssq : Real.sin y ^ 2 = |Real.sin y| ^ 2 := (sq_abs _).symm
  by_cases h : a ^ 2 ≤ 6
  · have hs := Real.abs_sub_sin_le y
    have t := abs_sub_abs_le_abs_sub y (Real.sin y)
    have lower : a - a ^ 3 / 6 ≤ |Real.sin y| := by
      have : |y| - |Real.sin y| ≤ |y| ^ 3 / 6 := t.trans hs
      linarith
    have nn : 0 ≤ a - a ^ 3 / 6 := by
      have : a ^ 3 = a * a ^ 2 := by ring
      rw [this]
      nlinarith
    have sq_le : (a - a ^ 3 / 6) ^ 2 ≤ |Real.sin y| ^ 2 := pow_le_pow_left₀ nn lower 2
    have expand : (a - a ^ 3 / 6) ^ 2 = a ^ 2 - a ^ 4 / 3 + (a ^ 3) ^ 2 / 36 := by ring
    have six : 0 ≤ (a ^ 3) ^ 2 := sq_nonneg _
    rw [expand, ay2, ay4] at sq_le
    rw [ssq]
    linarith
  · push Not at h
    rw [ay2] at h
    have y4 : y ^ 4 = y ^ 2 * y ^ 2 := by ring
    rw [y4]
    nlinarith [sq_nonneg (Real.sin y)]

/-! ### Hyperbolic remainders, in the exponential form of the Overlay axial core -/

theorem coshExp_neg (z : ℝ) : coshExp (-z) = coshExp z := by
  unfold coshExp; rw [neg_neg]; ring

theorem sinhExp_neg (z : ℝ) : sinhExp (-z) = -sinhExp z := by
  unfold sinhExp; rw [neg_neg]; ring

theorem coshExp_zero : coshExp 0 = 1 := by unfold coshExp; simp

theorem sinhExp_zero : sinhExp 0 = 0 := by unfold sinhExp; simp

theorem coshExp_eq (z : ℝ) : coshExp z = Real.cosh z := by
  rw [Real.cosh_eq]; rfl

theorem sinhExp_eq (z : ℝ) : sinhExp z = Real.sinh z := by
  rw [Real.sinh_eq]; rfl

theorem exp_sub_one_le_mul (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have e : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have p := Real.exp_pos y
  nlinarith

theorem sinhExp_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ sinhExp z := by
  unfold sinhExp
  have : Real.exp (-z) ≤ Real.exp z := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem sinhExp_le_of_nonneg {z : ℝ} (hz : 0 ≤ z) : sinhExp z ≤ z * Real.exp z := by
  unfold sinhExp
  have h1 := exp_sub_one_le_mul z
  have h2 : 1 - Real.exp (-z) ≤ z := by have := Real.add_one_le_exp (-z); linarith
  have h3 : z ≤ z * Real.exp z := by
    have := Real.one_le_exp hz
    nlinarith
  linarith

theorem abs_sinhExp_le (z : ℝ) : |sinhExp z| ≤ |z| * Real.exp |z| := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg (sinhExp_nonneg hz), abs_of_nonneg hz]
    exact sinhExp_le_of_nonneg hz
  · have hz' : 0 ≤ -z := by linarith
    have e : sinhExp z = -sinhExp (-z) := by rw [sinhExp_neg, neg_neg]
    rw [e, abs_neg, abs_of_nonneg (sinhExp_nonneg hz'), abs_of_nonpos hz]
    exact sinhExp_le_of_nonneg hz'

theorem coshExp_sub_one_eq (z : ℝ) : coshExp z - 1 = 2 * sinhExp (z / 2) ^ 2 := by
  unfold coshExp sinhExp
  have h1 : Real.exp z = Real.exp (z / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h2 : Real.exp (-z) = Real.exp (-(z / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h3 : Real.exp (z / 2) * Real.exp (-(z / 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [h1, h2]
  nlinarith [h3]

theorem coshExp_sub_one_nonneg (z : ℝ) : 0 ≤ coshExp z - 1 := by
  rw [coshExp_sub_one_eq]; positivity

theorem coshExp_sub_one_le (z : ℝ) : coshExp z - 1 ≤ z ^ 2 / 2 * Real.exp |z| := by
  rw [coshExp_sub_one_eq]
  have h := abs_sinhExp_le (z / 2)
  have h0 : 0 ≤ |sinhExp (z / 2)| := abs_nonneg _
  have sq : sinhExp (z / 2) ^ 2 ≤ (|z / 2| * Real.exp |z / 2|) ^ 2 := by
    rw [← sq_abs (sinhExp (z / 2))]
    exact pow_le_pow_left₀ h0 h 2
  have e1 : (|z / 2| * Real.exp |z / 2|) ^ 2 = z ^ 2 / 4 * Real.exp |z| := by
    rw [mul_pow, sq_abs, ← Real.exp_nat_mul, abs_div, abs_two]
    ring_nf
  rw [e1] at sq
  linarith

/-- `0 ≤ sinh z − z ≤ z (cosh z − 1)` for `z ≥ 0`. -/
theorem sinh_sub_self_le {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ Real.sinh z - z ∧ Real.sinh z - z ≤ z * (Real.cosh z - 1) := by
  constructor
  · have := Real.self_le_sinh_iff.mpr hz
    linarith
  · let f : ℝ → ℝ := fun t => t * Real.cosh t - Real.sinh t
    have hd (t : ℝ) : HasDerivAt f (t * Real.sinh t) t := by
      have h := ((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      convert h using 1
      ring
    have hmono : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact (continuous_id.mul Real.continuous_cosh |>.sub Real.continuous_sinh).continuousOn
      · intro t _
        exact (hd t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hd t).deriv]
        have ht' : 0 < t := ht
        exact mul_nonneg ht'.le (Real.sinh_nonneg_iff.mpr ht'.le)
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz) hz
    simp only [f, zero_mul, Real.sinh_zero, sub_zero] at this
    linarith

theorem abs_sinhExp_sub_le (z : ℝ) : |sinhExp z - z| ≤ |z| * (coshExp z - 1) := by
  rw [sinhExp_eq, coshExp_eq]
  rcases le_total 0 z with hz | hz
  · obtain ⟨h0, h1⟩ := sinh_sub_self_le hz
    rw [abs_of_nonneg h0, abs_of_nonneg hz]
    exact h1
  · have hz' : 0 ≤ -z := by linarith
    obtain ⟨h0, h1⟩ := sinh_sub_self_le hz'
    simp only [Real.sinh_neg, Real.cosh_neg] at h0 h1
    have e : Real.sinh z - z = -(-Real.sinh z - -z) := by ring
    rw [e, abs_neg, abs_of_nonneg h0, abs_of_nonpos hz]
    exact h1

/-! ### Cross pairs -/

/-- The cross-coset part of axial pair `n`: the only part depending on the
lateral phase `u` and the height `h`. -/
def crossPair (t w u h : ℝ) (n : ℕ) : ℝ :=
  axialTerm t ((n : ℝ) + h) (u + ((n : ℝ) + h) * w) +
    axialTerm t ((n : ℝ) + 1 - h) (u - ((n : ℝ) + 1 - h) * w)

theorem axialPair_sub (t w u u' h h' : ℝ) (n : ℕ) :
    axialPair t w u h n - axialPair t w u' h' n = crossPair t w u h n - crossPair t w u' h' n := by
  simp only [axialPair, crossPair]
  ring

theorem crossPair_eq (t w u h : ℝ) (n : ℕ) :
    crossPair t w u h n = 2 * Real.exp (-t * ((n : ℝ) + 1 / 2)) *
      (coshExp (t * (h - 1 / 2)) * Real.cos (2 * Real.pi * (u + w * (h - 1 / 2))) *
          Real.cos (Real.pi * (2 * (n : ℝ) + 1) * w) +
        sinhExp (t * (h - 1 / 2)) * Real.sin (2 * Real.pi * (u + w * (h - 1 / 2))) *
          Real.sin (Real.pi * (2 * (n : ℝ) + 1) * w)) := by
  set δ := h - 1 / 2 with hδ
  set φ := 2 * Real.pi * (u + w * δ) with hφ
  set γ := Real.pi * (2 * (n : ℝ) + 1) * w with hγ
  have c₁ : 2 * Real.pi * (u + ((n : ℝ) + h) * w) = φ + γ := by rw [hφ, hγ, hδ]; ring
  have c₂ : 2 * Real.pi * (u - ((n : ℝ) + 1 - h) * w) = φ - γ := by rw [hφ, hγ, hδ]; ring
  have e₁ : -t * ((n : ℝ) + h) = -t * ((n : ℝ) + 1 / 2) + -(t * δ) := by rw [hδ]; ring
  have e₂ : -t * ((n : ℝ) + 1 - h) = -t * ((n : ℝ) + 1 / 2) + t * δ := by rw [hδ]; ring
  simp only [crossPair, axialTerm, c₁, c₂, e₁, e₂, Real.exp_add, Real.cos_add, Real.cos_sub,
    coshExp, sinhExp]
  ring

/-- The parity `cos (π k)` of an integer, as a real number. -/
def parityR (k : ℤ) : ℝ := if k % 2 = 0 then 1 else -1

theorem parityR_cases (k : ℤ) : parityR k = 1 ∨ parityR k = -1 := by
  unfold parityR; split_ifs <;> simp

theorem cos_pi_int (k : ℤ) : Real.cos (Real.pi * k) = parityR k ∧ Real.sin (Real.pi * k) = 0 := by
  refine ⟨?_, by rw [mul_comm]; exact Real.sin_int_mul_pi k⟩
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · have hk2 : k % 2 = 0 := by omega
    have e : Real.pi * (k : ℝ) = (j : ℝ) * (2 * Real.pi) := by rw [hj]; push_cast; ring
    rw [e, Real.cos_int_mul_two_pi]
    simp [parityR, hk2]
  · have hk2 : k % 2 ≠ 0 := by omega
    have e : Real.pi * (k : ℝ) = (j : ℝ) * (2 * Real.pi) + Real.pi := by rw [hj]; push_cast; ring
    rw [e, Real.cos_add_pi, Real.cos_int_mul_two_pi]
    simp [parityR, hk2]

/-- The change of the pair about a half-height anchor, without its
exponential factor. -/
def pairGain (P γ a ψ : ℝ) : ℝ :=
  P * (Real.cos γ * (coshExp a * Real.cos ψ - 1) + Real.sin γ * sinhExp a * Real.sin ψ)

theorem crossPair_sub_anchor (t w u u' h : ℝ) (n : ℕ) (k : ℤ) (hk : 2 * u' = k) :
    crossPair t w u h n - crossPair t w u' (1 / 2) n =
      2 * Real.exp (-t * ((n : ℝ) + 1 / 2)) *
        pairGain (parityR k) (Real.pi * (2 * (n : ℝ) + 1) * w) (t * (h - 1 / 2))
          (2 * Real.pi * (u - u' + w * (h - 1 / 2))) := by
  rw [crossPair_eq, crossPair_eq]
  obtain ⟨cK, sK⟩ := cos_pi_int k
  set ψ := 2 * Real.pi * (u - u' + w * (h - 1 / 2)) with hψ
  have hφ : 2 * Real.pi * (u + w * (h - 1 / 2)) = Real.pi * k + ψ := by
    rw [hψ, ← hk]; ring
  have hφ' : 2 * Real.pi * (u' + w * (1 / 2 - 1 / 2)) = Real.pi * k := by
    rw [← hk]; ring
  have z : t * (1 / 2 - 1 / 2 : ℝ) = 0 := by ring
  rw [hφ, hφ', z, Real.cos_add, Real.sin_add, cK, sK, coshExp_zero, sinhExp_zero]
  unfold pairGain
  ring

/-! ### Bounds on the pair change -/

theorem pairGain_lower (P γ a ψ A Ψ : ℝ) (hP : P = 1 ∨ P = -1) (ha : |a| ≤ A) (hψ : |ψ| ≤ Ψ) :
    -(P * Real.cos γ) * ψ ^ 2 / 2 - max 0 (-(P * Real.cos γ)) * Ψ ^ 2 * ψ ^ 2 / 24
        - |Real.cos γ| * Real.exp A * a ^ 2 / 2 + P * Real.sin γ * a * ψ
        - |Real.sin γ| * (|a| * |ψ|) * (A ^ 2 * Real.exp A / 2 + Ψ ^ 2 / 6)
      ≤ pairGain P γ a ψ := by
  set C := coshExp a with hC
  set S := sinhExp a with hS
  set x := P * Real.cos γ with hx
  have hPabs : |P| = 1 := by rcases hP with h | h <;> rw [h] <;> norm_num
  have hP2 : P * P = 1 := by rcases hP with h | h <;> rw [h] <;> norm_num
  have A0 : 0 ≤ A := (abs_nonneg a).trans ha
  have Ψ0 : 0 ≤ Ψ := (abs_nonneg ψ).trans hψ
  have expA : Real.exp |a| ≤ Real.exp A := Real.exp_le_exp.mpr ha
  have a2 : a ^ 2 ≤ A ^ 2 := by rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have ψ2 : ψ ^ 2 ≤ Ψ ^ 2 := by rw [← sq_abs ψ]; exact pow_le_pow_left₀ (abs_nonneg ψ) hψ 2
  have split : pairGain P γ a ψ =
      x * (Real.cos ψ - 1) + x * (C - 1) * Real.cos ψ + P * Real.sin γ * a * ψ +
        P * Real.sin γ * (S * Real.sin ψ - a * ψ) := by
    unfold pairGain; rw [hx, hC, hS]; ring
  -- (i) the lateral term
  have t1 : -x * ψ ^ 2 / 2 - max 0 (-x) * Ψ ^ 2 * ψ ^ 2 / 24 ≤ x * (Real.cos ψ - 1) := by
    have lo := Real.one_sub_sq_div_two_le_cos (x := ψ)
    have quart := one_sub_cos_ge ψ
    rcases le_total 0 x with h | h
    · rw [max_eq_left (by linarith : -x ≤ 0)]
      nlinarith
    · rw [max_eq_right (by linarith : 0 ≤ -x)]
      have q4 : ψ ^ 4 ≤ Ψ ^ 2 * ψ ^ 2 := by
        have : ψ ^ 4 = ψ ^ 2 * ψ ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right ψ2 (sq_nonneg _)
      have hx' : 0 ≤ -x := by linarith
      have := mul_le_mul_of_nonneg_left quart hx'
      nlinarith
  -- (ii) the vertical correction
  have t2 : -(|Real.cos γ| * Real.exp A * a ^ 2 / 2) ≤ x * (C - 1) * Real.cos ψ := by
    have c1 : 0 ≤ C - 1 := coshExp_sub_one_nonneg a
    have c2 : C - 1 ≤ a ^ 2 / 2 * Real.exp A :=
      (coshExp_sub_one_le a).trans (mul_le_mul_of_nonneg_left expA (by positivity))
    have hxabs : |x| = |Real.cos γ| := by rw [hx, abs_mul, hPabs, one_mul]
    have bound : |x * (C - 1) * Real.cos ψ| ≤ |Real.cos γ| * (a ^ 2 / 2 * Real.exp A) := by
      rw [abs_mul, abs_mul, hxabs, abs_of_nonneg c1]
      have hc : |Real.cos ψ| ≤ 1 := Real.abs_cos_le_one ψ
      calc |Real.cos γ| * (C - 1) * |Real.cos ψ| ≤ |Real.cos γ| * (C - 1) * 1 :=
            mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) c1)
        _ ≤ |Real.cos γ| * (a ^ 2 / 2 * Real.exp A) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left c2 (abs_nonneg _)
    have := neg_abs_le (x * (C - 1) * Real.cos ψ)
    nlinarith
  -- (iv) the odd remainder
  have t4 : -(|Real.sin γ| * (|a| * |ψ|) * (A ^ 2 * Real.exp A / 2 + Ψ ^ 2 / 6)) ≤
      P * Real.sin γ * (S * Real.sin ψ - a * ψ) := by
    have r1 : |S - a| ≤ |a| * (a ^ 2 / 2 * Real.exp A) := by
      have h1 := abs_sinhExp_sub_le a
      have h2 : coshExp a - 1 ≤ a ^ 2 / 2 * Real.exp A :=
        (coshExp_sub_one_le a).trans (mul_le_mul_of_nonneg_left expA (by positivity))
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg a))
    have r2 : |Real.sin ψ - ψ| ≤ |ψ| ^ 3 / 6 := by
      rw [abs_sub_comm]; exact Real.abs_sub_sin_le ψ
    have r3 : |Real.sin ψ| ≤ |ψ| := Real.abs_sin_le_abs
    have key : |S * Real.sin ψ - a * ψ| ≤ |a| * |ψ| * (A ^ 2 * Real.exp A / 2 + Ψ ^ 2 / 6) := by
      have e : S * Real.sin ψ - a * ψ = (S - a) * Real.sin ψ + a * (Real.sin ψ - ψ) := by ring
      rw [e]
      have p1 : |(S - a) * Real.sin ψ| ≤ |a| * (a ^ 2 / 2 * Real.exp A) * |ψ| := by
        rw [abs_mul]; exact mul_le_mul r1 r3 (abs_nonneg _) (by positivity)
      have p2 : |a * (Real.sin ψ - ψ)| ≤ |a| * (|ψ| ^ 3 / 6) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left r2 (abs_nonneg _)
      have p3 : |ψ| ^ 3 ≤ |ψ| * Ψ ^ 2 := by
        have : |ψ| ^ 3 = |ψ| * |ψ| ^ 2 := by ring
        rw [this, sq_abs]; exact mul_le_mul_of_nonneg_left ψ2 (abs_nonneg _)
      have p4 : a ^ 2 * Real.exp A ≤ A ^ 2 * Real.exp A :=
        mul_le_mul_of_nonneg_right a2 (Real.exp_pos A).le
      have tri := abs_add_le ((S - a) * Real.sin ψ) (a * (Real.sin ψ - ψ))
      have ha0 := abs_nonneg a
      have hψ0 := abs_nonneg ψ
      nlinarith [mul_nonneg ha0 hψ0, mul_le_mul_of_nonneg_left p3 ha0,
        mul_le_mul_of_nonneg_left p4 (mul_nonneg ha0 hψ0)]
    have hb : |P * Real.sin γ * (S * Real.sin ψ - a * ψ)| ≤
        |Real.sin γ| * (|a| * |ψ| * (A ^ 2 * Real.exp A / 2 + Ψ ^ 2 / 6)) := by
      rw [abs_mul, abs_mul, hPabs, one_mul]
      exact mul_le_mul_of_nonneg_left key (abs_nonneg _)
    have := neg_abs_le (P * Real.sin γ * (S * Real.sin ψ - a * ψ))
    nlinarith
  rw [split]
  linarith

theorem abs_pairGain_le (P γ a ψ : ℝ) (hP : P = 1 ∨ P = -1) :
    |pairGain P γ a ψ| ≤ Real.exp |a| * (a ^ 2 + ψ ^ 2) := by
  have hPabs : |P| = 1 := by rcases hP with h | h <;> rw [h] <;> norm_num
  set C := coshExp a
  set S := sinhExp a
  have e1 : 1 ≤ Real.exp |a| := Real.one_le_exp (abs_nonneg a)
  have c1 : 0 ≤ C - 1 := coshExp_sub_one_nonneg a
  have c2 : C - 1 ≤ a ^ 2 / 2 * Real.exp |a| := coshExp_sub_one_le a
  have s1 : |S| ≤ |a| * Real.exp |a| := abs_sinhExp_le a
  have cosψ : 1 - Real.cos ψ ≤ ψ ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := ψ); linarith
  have cosψ' : Real.cos ψ ≤ 1 := Real.cos_le_one ψ
  have hc : |Real.cos ψ| ≤ 1 := Real.abs_cos_le_one ψ
  have first : |C * Real.cos ψ - 1| ≤ (C - 1) + ψ ^ 2 / 2 := by
    have e : C * Real.cos ψ - 1 = (C - 1) * Real.cos ψ + (Real.cos ψ - 1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg c1]
      calc (C - 1) * |Real.cos ψ| ≤ (C - 1) * 1 := mul_le_mul_of_nonneg_left hc c1
        _ = C - 1 := mul_one _
    · rw [abs_of_nonpos (by linarith)]; linarith
  have second : |S * Real.sin ψ| ≤ |a| * Real.exp |a| * |ψ| := by
    rw [abs_mul]; exact mul_le_mul s1 Real.abs_sin_le_abs (abs_nonneg _) (by positivity)
  have amgm : |a| * |ψ| ≤ (a ^ 2 + ψ ^ 2) / 2 := by
    rw [← sq_abs a, ← sq_abs ψ]; nlinarith [sq_nonneg (|a| - |ψ|)]
  have body : |Real.cos γ * (C * Real.cos ψ - 1) + Real.sin γ * S * Real.sin ψ| ≤
      Real.exp |a| * (a ^ 2 + ψ ^ 2) := by
    refine (abs_add_le _ _).trans ?_
    have u1 : |Real.cos γ * (C * Real.cos ψ - 1)| ≤ (C - 1) + ψ ^ 2 / 2 := by
      rw [abs_mul]
      calc |Real.cos γ| * |C * Real.cos ψ - 1| ≤ 1 * |C * Real.cos ψ - 1| :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one γ) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact first
    have u2 : |Real.sin γ * S * Real.sin ψ| ≤ |a| * Real.exp |a| * |ψ| := by
      rw [mul_assoc, abs_mul]
      calc |Real.sin γ| * |S * Real.sin ψ| ≤ 1 * |S * Real.sin ψ| :=
            mul_le_mul_of_nonneg_right (Real.abs_sin_le_one γ) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact second
    have u3 : |a| * Real.exp |a| * |ψ| ≤ Real.exp |a| * ((a ^ 2 + ψ ^ 2) / 2) := by
      have : |a| * Real.exp |a| * |ψ| = Real.exp |a| * (|a| * |ψ|) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left amgm (Real.exp_pos _).le
    have u4 : ψ ^ 2 / 2 ≤ Real.exp |a| * (ψ ^ 2 / 2) := by
      nlinarith [sq_nonneg ψ]
    nlinarith
  unfold pairGain
  rw [abs_mul, hPabs, one_mul]
  exact body

end BccSharp.Coulomb.CompactCover.Layered
