import BccSharp.Cover.LayeredRoute

set_option autoImplicit false

/-! # A sign-aware layered gain for the Adaptive `Q` cells

The layered gain (`Layered.layered_gain`, `Layered.Fix.leafOk_gain`) bounds the
vertical part `x (cosh a − 1) cos ψ` of every retained wave's adjacent axial pair
(`x = P cos γ`, `|a| ≤ A`, `|ψ| ≤ Ψ`) by `−|cos γ| e^A a²/2`, whatever the sign of `x`. On
near-cubic cells (layer spacing `c ≈ 1`, the Adaptive `Q` boxes) that makes the axial curvature
negative. Here the vertical step is:

* when `x ≥ 0` (flag `pos`): `x a²/2 · (1 − cosh A · Ψ²/2)` (`cosh a − 1 ≥ a²/2`,
  `coshExp_sub_one_ge`; `cos ψ ≥ 1 − ψ²/2`);
* otherwise: `−|cos γ| cosh A · a²/2`;
* both from `cosh a − 1 ≤ (a²/2) cosh A` (`coshExp_sub_one_le_cosh`), sharper than
  the `e^A` of the unsigned gain.

`pairGain_lowerS`, `mode_lowerS` and `layered_gainS` are `pairGain_lower`, `mode_lower` and
`layered_gain` with this one term changed, and the interval layer (`muRS`, `muFS`,
`leafOk_gainS`, `splitOkS_gain`) follows: the proofs are theirs, with the vertical step replaced.
The module also gives an anchor-separation bound for `r s ≥ 1` (`anchor_sep2`, `sep2Ok`,
`sep2Ok_sound`) and the PlanarAnchor route with both (`planarAnchorSOk`, `planarAnchorSOk_sound`). -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar

/-- `cosh z − 1 ≥ z²/2`. -/
theorem coshExp_sub_one_ge (z : ℝ) : z ^ 2 / 2 ≤ coshExp z - 1 := by
  rw [coshExp_sub_one_eq, sinhExp_eq]
  have h : (z / 2) ^ 2 ≤ Real.sinh (z / 2) ^ 2 := by
    rcases le_total 0 z with hz | hz
    · have h1 : z / 2 ≤ Real.sinh (z / 2) := Real.self_le_sinh_iff.mpr (by linarith)
      exact pow_le_pow_left₀ (by linarith) h1 2
    · have h1 : -(z / 2) ≤ Real.sinh (-(z / 2)) := Real.self_le_sinh_iff.mpr (by linarith)
      rw [Real.sinh_neg] at h1
      nlinarith
  nlinarith

/-- `cosh z − 1 ≤ z²/2 · cosh A` for `|z| ≤ A`: from `|sinh t − t| ≤ |t| (cosh t − 1)`
(`abs_sinhExp_sub_le`), `|sinh t| ≤ |t| cosh t`, so `cosh z − 1 = 2 sinh²(z/2) ≤
(z²/2) cosh²(z/2) = (z²/2)(cosh z + 1)/2 ≤ (z²/2) cosh z`. -/
theorem coshExp_sub_one_le_cosh (z A : ℝ) (h : |z| ≤ A) : coshExp z - 1 ≤ z ^ 2 / 2 * Real.cosh A := by
  have hs : ∀ t : ℝ, |sinhExp t| ≤ |t| * coshExp t := by
    intro t
    have h1 := abs_sinhExp_sub_le t
    have h2 := abs_sub_abs_le_abs_sub (sinhExp t) t
    have e : |t| * coshExp t = |t| * (coshExp t - 1) + |t| := by ring
    rw [e]
    linarith
  have hz2 := hs (z / 2)
  have sq1 : sinhExp (z / 2) ^ 2 ≤ (|z / 2| * coshExp (z / 2)) ^ 2 := by
    rw [← sq_abs (sinhExp (z / 2))]
    exact pow_le_pow_left₀ (abs_nonneg _) hz2 2
  have hc2 : coshExp (z / 2) ^ 2 = (coshExp z + 1) / 2 := by
    have h1 := coshExp_sub_one_eq z
    have h2 : coshExp (z / 2) ^ 2 = sinhExp (z / 2) ^ 2 + 1 := by
      rw [coshExp_eq, sinhExp_eq]; exact Real.cosh_sq _
    linarith
  have e2 : (|z / 2| * coshExp (z / 2)) ^ 2 = z ^ 2 / 4 * ((coshExp z + 1) / 2) := by
    rw [mul_pow, sq_abs, hc2]; ring
  rw [e2, coshExp_eq] at sq1
  have hzA : Real.cosh z ≤ Real.cosh A := Real.cosh_le_cosh.mpr (h.trans (le_abs_self A))
  have c1 : 1 ≤ Real.cosh z := Real.one_le_cosh z
  rw [coshExp_sub_one_eq]
  have s1 : 2 * sinhExp (z / 2) ^ 2 ≤ z ^ 2 / 2 * ((Real.cosh z + 1) / 2) := by linarith
  have s2 : z ^ 2 / 2 * ((Real.cosh z + 1) / 2) ≤ z ^ 2 / 2 * Real.cosh A :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- `pairLower` with the vertical term `x a²/2 (1 − cosh A Ψ²/2)` when `pos` (then `x ≥ 0`), and
`−|cos γ| cosh A a²/2` otherwise (`cosh A ≤ e^A`). -/
def pairLowerS (pos : Bool) (P γ a ψ A Ψ : ℝ) : ℝ :=
  -(P * Real.cos γ) * ψ ^ 2 / 2 - max 0 (-(P * Real.cos γ)) * Ψ ^ 2 * ψ ^ 2 / 24
    + (if pos then P * Real.cos γ * a ^ 2 / 2 * (1 - Real.cosh A * Ψ ^ 2 / 2)
        else -(|Real.cos γ| * Real.cosh A * a ^ 2 / 2))
    + P * Real.sin γ * a * ψ
    - |Real.sin γ| * (|a| * |ψ|) * (A ^ 2 * Real.exp A / 2 + Ψ ^ 2 / 6)

theorem pairGain_lowerS (pos : Bool) (P γ a ψ A Ψ : ℝ) (hP : P = 1 ∨ P = -1) (ha : |a| ≤ A)
    (hψ : |ψ| ≤ Ψ) (hpos : pos = true → 0 ≤ P * Real.cos γ) :
    pairLowerS pos P γ a ψ A Ψ ≤ pairGain P γ a ψ := by
  unfold pairLowerS
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
  -- (ii) the vertical correction, sign-aware when `pos`
  have t2 : (if pos then P * Real.cos γ * a ^ 2 / 2 * (1 - Real.cosh A * Ψ ^ 2 / 2)
      else -(|Real.cos γ| * Real.cosh A * a ^ 2 / 2)) ≤ x * (C - 1) * Real.cos ψ := by
    have c1 : 0 ≤ C - 1 := coshExp_sub_one_nonneg a
    have c2 : C - 1 ≤ a ^ 2 / 2 * Real.cosh A := coshExp_sub_one_le_cosh a A ha
    cases pos with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hxabs : |x| = |Real.cos γ| := by rw [hx, abs_mul, hPabs, one_mul]
      have bound : |x * (C - 1) * Real.cos ψ| ≤ |Real.cos γ| * (a ^ 2 / 2 * Real.cosh A) := by
        rw [abs_mul, abs_mul, hxabs, abs_of_nonneg c1]
        have hc : |Real.cos ψ| ≤ 1 := Real.abs_cos_le_one ψ
        calc |Real.cos γ| * (C - 1) * |Real.cos ψ| ≤ |Real.cos γ| * (C - 1) * 1 :=
              mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) c1)
          _ ≤ |Real.cos γ| * (a ^ 2 / 2 * Real.cosh A) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left c2 (abs_nonneg _)
      have := neg_abs_le (x * (C - 1) * Real.cos ψ)
      nlinarith
    | true =>
      simp only [ite_true]
      rw [← hx]
      have hx0 : 0 ≤ x := hpos rfl
      have c3 : a ^ 2 / 2 ≤ C - 1 := coshExp_sub_one_ge a
      have cosLo : 1 - ψ ^ 2 / 2 ≤ Real.cos ψ := Real.one_sub_sq_div_two_le_cos
      have s1 : x * (C - 1) * (1 - ψ ^ 2 / 2) ≤ x * (C - 1) * Real.cos ψ :=
        mul_le_mul_of_nonneg_left cosLo (mul_nonneg hx0 c1)
      have s2 : x * (C - 1) * (ψ ^ 2 / 2) ≤ x * (a ^ 2 / 2 * Real.cosh A) * (Ψ ^ 2 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left c2 hx0) (by linarith) (by positivity)
          (mul_nonneg hx0 (by positivity))
      have s3 : x * (a ^ 2 / 2) ≤ x * (C - 1) := mul_le_mul_of_nonneg_left c3 hx0
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


/-- `modeLower` with `pairLowerS`. -/
def modeLowerS (p : Chart) (α₁ α₂ : ℝ) (k : ℤ) (A Ψ : ℝ) (pos : Bool) (m : Wave) : ℝ :=
  let T := tReal p m
  let a := T * (p 7 - 1 / 2)
  let ψ := 2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)
  modeW p m * pairLowerS pos (parityR k) (Real.pi * wReal p m) a ψ A Ψ -
    modeW p m * axialFactor T A * (a ^ 2 + ψ ^ 2)

theorem mode_lowerS (p : Chart) (α₁ α₂ : ℝ) (hr : 0 < p 0) (hs : 0 < p 1)
    (h₀ : 0 < p 7) (h₁ : p 7 < 1) {m : Wave} (hm : m ≠ 0) (k : ℤ)
    (hk : 2 * ((m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂) = k) (A Ψ : ℝ) (pos : Bool)
    (hpos : pos = true → 0 ≤ parityR k * Real.cos (Real.pi * wReal p m))
    (hA : |tReal p m * (p 7 - 1 / 2)| ≤ A)
    (hΨ : |2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)| ≤ Ψ) :
    modeLowerS p α₁ α₂ k A Ψ pos m ≤ 2 * cReal p * (waveValue p m - waveValue (anchorChart p α₁ α₂) m) := by
  have hT := tReal_pos p hr hs hm
  have hκ := waveKappa_pos p hr hs hm
  have hc : 0 < cReal p := inv_pos.mpr (mul_pos hr hs)
  set T := tReal p m with hTdef
  set w := wReal p m
  set a := T * (p 7 - 1 / 2) with hadef
  set ψ := 2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1) with hψdef
  set P := parityR k
  have hP : P = 1 ∨ P = -1 := parityR_cases k
  have hsum := waveTerm_summable P T w a ψ hP hT
  rw [waveValue_sub_anchor p α₁ α₂ hr hs h₀ h₁ hm k hk, hsum.tsum_eq_zero_add]
  -- the adjacent pair
  have first : waveTerm P T w a ψ 0 = 2 * Real.exp (-T / 2) * pairGain P (Real.pi * w) a ψ := by
    unfold waveTerm
    congr 2
    · ring_nf
    · ring_nf
  have lower0 := pairGain_lowerS pos P (Real.pi * w) a ψ A Ψ hP hA hΨ hpos
  -- the further pairs
  have r := Real.exp_lt_one_iff.mpr (by linarith : -T < 0)
  have r0 := (Real.exp_pos (-T)).le
  have hrest : Summable (fun n => waveTerm P T w a ψ (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  let G : ℕ → ℝ := fun n => (2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2)) * Real.exp (-T)) *
    (Real.exp (-T)) ^ n
  have hG : Summable G := (summable_geometric_of_lt_one r0 r).mul_left _
  have bound (n : ℕ) : |waveTerm P T w a ψ (n + 1)| ≤ G n := by
    have := abs_waveTerm_le P T w a ψ hP (n + 1)
    rw [pow_succ (Real.exp (-T)) n] at this
    exact this.trans_eq (by simp only [G]; ring)
  obtain ⟨_, babs⟩ := abs_sum_bound hG bound
  have tG : (∑' n, G n) = 2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2)) *
      (Real.exp (-T) / (1 - Real.exp (-T))) := by
    simp only [G]
    rw [tsum_mul_left, tsum_geometric_of_lt_one r0 r]
    ring
  rw [tG] at babs
  have restLower := neg_abs_le (∑' n, waveTerm P T w a ψ (n + 1))
  have expA : Real.exp |a| ≤ Real.exp A := Real.exp_le_exp.mpr hA
  have den : 0 < 1 - Real.exp (-T) := by linarith
  have q0 : 0 ≤ Real.exp (-T) / (1 - Real.exp (-T)) := div_nonneg r0 den.le
  have sq0 : 0 ≤ a ^ 2 + ψ ^ 2 := by positivity
  have weaken : 2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2)) *
      (Real.exp (-T) / (1 - Real.exp (-T))) ≤
      2 * Real.exp (-T / 2) * (Real.exp A * (a ^ 2 + ψ ^ 2)) * (Real.exp (-T) / (1 - Real.exp (-T))) := by
    have := mul_le_mul_of_nonneg_right expA sq0
    have h2 : 0 ≤ 2 * Real.exp (-T / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h2, mul_nonneg h2 q0]
  -- combine and scale by 2c/κ
  have total : 2 * Real.exp (-T / 2) * pairLowerS pos P (Real.pi * w) a ψ A Ψ -
      2 * Real.exp (-T / 2) * (Real.exp A * (a ^ 2 + ψ ^ 2)) * (Real.exp (-T) / (1 - Real.exp (-T))) ≤
      waveTerm P T w a ψ 0 + ∑' n, waveTerm P T w a ψ (n + 1) := by
    rw [first]
    have e2 : 0 ≤ 2 * Real.exp (-T / 2) := by positivity
    have := mul_le_mul_of_nonneg_left lower0 e2
    linarith
  have scale : 0 ≤ 2 * cReal p / κReal p m := by positivity
  have := mul_le_mul_of_nonneg_left total scale
  have eqL : modeLowerS p α₁ α₂ k A Ψ pos m = 2 * cReal p / κReal p m *
      (2 * Real.exp (-T / 2) * pairLowerS pos P (Real.pi * w) a ψ A Ψ -
        2 * Real.exp (-T / 2) * (Real.exp A * (a ^ 2 + ψ ^ 2)) * (Real.exp (-T) / (1 - Real.exp (-T)))) := by
    unfold modeLowerS modeW axialFactor
    ring
  rw [eqL]
  calc _ ≤ 2 * cReal p / κReal p m * (waveTerm P T w a ψ 0 + ∑' n, waveTerm P T w a ψ (n + 1)) := this
    _ = _ := by field_simp

theorem layered_gainS (p : Chart) (α₁ α₂ : ℝ) (k₁ k₂ : ℤ) (hk₁ : 2 * α₁ = k₁) (hk₂ : 2 * α₂ = k₂)
    (hr : 0 < p 0) (hs : 0 < p 1) {η : ℝ} (hη : |p 7 - 1 / 2| ≤ η) (hη2 : η < 1 / 2)
    (K : ℕ) {B τ : ℝ} (hB₁ : p 0 ≤ B) (hB₂ : secondColumn p ≤ B) (hτ : 0 < τ)
    (hτc : τ ≤ 2 * Real.pi * cReal p / B) (hmono : 2 / (1 / 2 - η) ≤ τ * ((K : ℝ) + 1))
    (hρ : (((K : ℝ) + 2) / ((K : ℝ) + 1)) ^ 2 * Real.exp (-(τ * (1 / 2 - η))) < 1)
    (A Ψ : Wave → ℝ) (hA : ∀ m ∈ waves K, |tReal p m * (p 7 - 1 / 2)| ≤ A m)
    (hΨ : ∀ m ∈ waves K,
      |2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)| ≤ Ψ m)
    (pos : Wave → Bool) (hpos : ∀ m ∈ waves K, pos m = true →
      0 ≤ parityR (m.1 * k₁ + m.2 * k₂) * Real.cos (Real.pi * wReal p m)) :
    2 * Real.pi * cReal p ^ 2 * (p 7 - 1 / 2) ^ 2 +
        (∑ m ∈ waves K, modeLowerS p α₁ α₂ (m.1 * k₁ + m.2 * k₂) (A m) (Ψ m) (pos m) m) -
        outerTail (cReal p) B τ η K * (τ ^ 2 * (p 7 - 1 / 2) ^ 2 +
          8 * Real.pi ^ 2 * (latV p α₁ α₂ 0 ^ 2 + latV p α₁ α₂ 1 ^ 2)) ≤
      2 * ac * (energy (chartPoint p) - energy (chartPoint (anchorChart p α₁ α₂))) := by
  have h₀ : 0 < p 7 := by have := abs_le.mp hη; linarith
  have h₁ : p 7 < 1 := by have := abs_le.mp hη; linarith
  have ha₀ : 0 < anchorChart p α₁ α₂ 7 := by rw [anchorChart_7]; norm_num
  have ha₁ : anchorChart p α₁ α₂ 7 < 1 := by rw [anchorChart_7]; norm_num
  rw [energy_sub_anchor p α₁ α₂ hr hs h₀ h₁]
  let D (m : Wave) := waveValue p m - waveValue (anchorChart p α₁ α₂) m
  have SD : Summable D := (waveValue_summable p hr hs h₀ h₁).sub
    (waveValue_summable (anchorChart p α₁ α₂) hr hs ha₀ ha₁)
  have split := SD.sum_add_tsum_subtype_compl (waveCube K)
  have D0 : D (0, 0) = 0 := by simp only [D, waveValue_zero, sub_self]
  have Deven : ∀ m, D (waveNeg m) = D m := by
    intro m; simp only [D, waveValue_even]
  have cube := sum_waveCube K D D0 Deven
  have tail := outer_tail p α₁ α₂ k₁ k₂ hk₁ hk₂ hr hs hη hη2 K hB₁ hB₂ hτ hτc hmono hρ
  have retained : (∑ m ∈ waves K, modeLowerS p α₁ α₂ (m.1 * k₁ + m.2 * k₂) (A m) (Ψ m) (pos m) m) ≤
      2 * cReal p * ∑ m ∈ waves K, D m := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hm0 : m ≠ 0 := by
      intro e
      rw [e] at hm
      simp [waves] at hm
    have hk : 2 * ((m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂) = ((m.1 * k₁ + m.2 * k₂ : ℤ) : ℝ) := by
      push_cast; rw [← hk₁, ← hk₂]; ring
    exact mode_lowerS p α₁ α₂ hr hs h₀ h₁ hm0 _ hk (A m) (Ψ m) (pos m) (hpos m hm) (hA m hm) (hΨ m hm)
  have e : (∑' m : Wave, D m) = 2 * (∑ m ∈ waves K, D m) +
      ∑' m : {m // m ∉ waveCube K}, D m.val := by
    rw [← split, cube]
  change _ ≤ 2 * Real.pi * cReal p ^ 2 * (p 7 - 1 / 2) ^ 2 + cReal p * ∑' m : Wave, D m
  rw [e]
  have : cReal p * (2 * ∑ m ∈ waves K, D m + ∑' m : {m // m ∉ waveCube K}, D m.val) =
      2 * cReal p * ∑ m ∈ waves K, D m + cReal p * ∑' m : {m // m ∉ waveCube K}, D m.val := by ring
  rw [this]
  linarith

end BccSharp.Coulomb.CompactCover.Layered

/-! ### The fixed-point layer with the sign-aware axial coefficient -/

namespace BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix

/-- A retained wave whose sign factor `cg` is nonnegative on the whole cell. -/
def posF (b : Cell) (an : Anchor) (m : Wave) : Bool := decide (0 ≤ (cgF b an m).lo)

/-- The axial coefficient with the sign-aware vertical term when `pos`, and `cosh A` in place of
`e^A` otherwise. -/
def muRS (p : Chart) (an : Anchor) (A Ψ : ℝ) (pos : Bool) (m : Wave) : ℝ :=
  if pos then
    Layered.modeW p m * tReal p m ^ 2 *
      (cgR p an m / 2 * (1 - Real.cosh A * Ψ ^ 2 / 2) - Layered.axialFactor (tReal p m) A)
  else
    -(Layered.modeW p m * tReal p m ^ 2 *
      (|cgR p an m| * Real.cosh A / 2 + Layered.axialFactor (tReal p m) A))

/-- An enclosure of `cosh (a/S)` for `0 ≤ a`. -/
def coshF (a : ℤ) : FI := halfF ((expPosF a).add (expNegPt a.toNat))

theorem coshF_mem {a : ℤ} (ha : 0 ≤ a) (hlo : 0 < (expNegPt a.toNat).lo) :
    (coshF a).Mem (Real.cosh ((a : ℝ) / Sz)) := by
  have h1 := expPosF_mem ha hlo
  have h2 := expNegPt_mem a.toNat
  have e : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
  rw [e] at h2
  have h := halfF_mem (FI.add_mem h1 h2)
  rw [Real.cosh_eq]
  exact h

/-- Its enclosure: `W T² (cg/2 − cg cosh A Ψ²/4 − af)` when `posF`, else
`−W T² (|cg| cosh A/2 + af)`. -/
def muFS (b : Cell) (an : Anchor) (m : Wave) : FI :=
  if posF b an m then
    FI.mul (FI.mul (wF' b m) (FI.sq (tF b m)))
      ((halfF (cgF b an m)).sub
        ((divNatF (FI.mul (FI.mul (cgF b an m) (coshF (aZ b m))) (FI.sq (ptF (psiZ b an m)))) 4).add
          (afF b m)))
  else
    negF (FI.mul (FI.mul (wF' b m) (FI.sq (tF b m)))
      ((halfF (FI.mul (absF (cgF b an m)) (coshF (aZ b m)))).add (afF b m)))

def m22FS (b : Cell) (an : Anchor) : FI :=
  ((FI.mul twoPiF (FI.sq (cF b))).add (sumW (wavesList an.cube) (muFS b an))).sub
    (FI.mul (FI.sq (ptF (tauZ b))) (outerF b an.cube))

def surplusFS (b : Cell) (an : Anchor) (lam : ℚ) : Sym3 :=
  ⟨subScaled (m00F b an) (g00F b) lam, subScaled (m01F b an) (g01F b) lam,
    subScaled (m11F b an) (g11F b) lam, m02F b an, m12F b an, subScaled (m22FS b an) (g22F b) lam⟩

/-- `leafOk` with the sign-aware axial entry. -/
def leafOkS (b : Cell) (an : Anchor) (lam : ℚ) : Bool :=
  ((guardsOk b && outerOk b an.cube) && (wavesList an.cube).all (waveOk b an)) &&
    pdOk (surplusFS b an lam)

def splitOkS (an : Anchor) (lam : ℚ) : ℕ → Cell → Bool
  | 0, b => leafOkS b an lam
  | d + 1, b =>
    let i := widest b
    splitOkS an lam d (replaceEnd b i (midpoint b i) false) &&
      splitOkS an lam d (replaceEnd b i (midpoint b i) true)

theorem posF_sound {b : Cell} {p : Chart} (hp : b.Mem p) {an : Anchor} {m : Wave}
    (h : posF b an m = true) : 0 ≤ cgR p an m := by
  have hm := cgF_mem' hp (an := an) (m := m)
  have h0 : (0 : ℤ) ≤ (cgF b an m).lo := of_decide_eq_true h
  have : (0 : ℝ) ≤ ((cgF b an m).lo : ℝ) / Sz := div_nonneg (by exact_mod_cast h0) Sz_pos.le
  exact this.trans hm.1

theorem muFS_mem' {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) {an : Anchor} {m : Wave}
    (ok : waveOk b an m = true) :
    (muFS b an m).Mem (muRS p an ((aZ b m : ℝ) / Sz) ((psiZ b an m : ℝ) / Sz) (posF b an m) m) := by
  unfold muFS muRS
  obtain ⟨-, -, -, ha0, -, hlo, -⟩ := waveOk_facts ok
  have hc := cgF_mem' hp (an := an) (m := m)
  have hch := coshF_mem ha0 hlo
  cases hpos : posF b an m with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h := negF_mem (FI.mul_mem (FI.mul_mem (modeW_mem hp g ok) (FI.sq_mem (tF_mem hp g m)))
      (FI.add_mem (halfF_mem (FI.mul_mem (absF_mem hc) hch)) (afF_mem' hp g ok)))
    convert h using 1
  | true =>
    simp only [↓reduceIte]
    have h := FI.mul_mem (FI.mul_mem (modeW_mem hp g ok) (FI.sq_mem (tF_mem hp g m)))
      (FI.sub_mem (halfF_mem hc)
        (FI.add_mem (divNatF_mem (FI.mul_mem (FI.mul_mem hc hch)
          (FI.sq_mem (ptF_mem (psiZ b an m)))) 4 (by norm_num)) (afF_mem' hp g ok)))
    convert h using 1
    push_cast
    ring

/-- `waveQuad` with `muRS` in place of `muR`. -/
def waveQuadS (p : Chart) (an : Anchor) (A Ψ : ℝ) (pos : Bool) (m : Wave) (v₁ v₂ δ : ℝ) : ℝ :=
  waveQuad p an A Ψ m v₁ v₂ δ + (muRS p an A Ψ pos m - muR p an A Ψ m) * δ ^ 2

theorem modeLowerS_eq (p : Chart) (an : Anchor) (A Ψ : ℝ) (pos : Bool) (m : Wave) :
    Layered.modeLowerS p (an.k₁ / 2) (an.k₂ / 2) (kk an m) A Ψ pos m =
      Layered.modeLower p (an.k₁ / 2) (an.k₂ / 2) (kk an m) A Ψ m +
        (muRS p an A Ψ pos m - muR p an A Ψ m) * (p 7 - 1 / 2) ^ 2 := by
  have hP : |Layered.parityR (kk an m)| = 1 := by
    rcases Layered.parityR_cases (kk an m) with h | h <;> rw [h] <;> norm_num
  have hcg : |Real.cos (Real.pi * wReal p m)| = |cgR p an m| := by
    unfold cgR; rw [abs_mul, hP, one_mul]
  dsimp only [Layered.modeLowerS, Layered.modeLower, Layered.pairLowerS, Layered.pairLower]
  unfold muRS muR
  rw [hcg]
  cases pos with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  | true =>
    simp only [↓reduceIte]
    unfold cgR
    ring

theorem modeLower_geS (p : Chart) (an : Anchor) (A Ψ : ℝ) (pos : Bool) (m : Wave)
    (hW : 0 ≤ Layered.modeW p m) (hT : 0 ≤ tReal p m) :
    waveQuadS p an A Ψ pos m (Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0)
        (Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1) (p 7 - 1 / 2) ≤
      Layered.modeLowerS p (an.k₁ / 2) (an.k₂ / 2) (kk an m) A Ψ pos m := by
  rw [modeLowerS_eq]
  unfold waveQuadS
  have := modeLower_ge p an A Ψ m hW hT
  linarith

/-- The axial entry of the sign-aware matrix. -/
def e22S (b : Cell) (an : Anchor) (p : Chart) : ℝ :=
  2 * Real.pi * cReal p ^ 2 + sumL an (fun m => muRS p an (Aw b m) (Ψw b an m) (posF b an m) m) -
    ((tauZ b : ℝ) / Sz) ^ 2 * Hout b an p

theorem leafOk_gainS {b : Cell} {an : Anchor} {lam : ℚ} (ok : leafOkS b an lam = true)
    {p : Chart} (hp : b.Mem p) :
    (lam : ℝ) * layerGram p (an.k₁ / 2) (an.k₂ / 2) ≤
      2 * ac * (energy (chartPoint p) -
        energy (chartPoint (Layered.anchorChart p (an.k₁ / 2) (an.k₂ / 2)))) := by
  simp only [leafOkS, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨hg, ho⟩, hw⟩, hpd⟩ := ok
  have g : Guards b := by
    have := of_decide_eq_true hg
    exact ⟨this.1, this.2.1, this.2.2⟩
  have wok : ∀ m ∈ waves an.cube, waveOk b an m = true := by
    intro m hm
    exact List.all_eq_true.mp hw m ((mem_wavesList _ m).mpr hm)
  have sp := Sz_pos
  have hr : 0 < p 0 := (div_pos (by exact_mod_cast g.r₀) sp).trans_le (cx_mem hp 0).1
  have hs : 0 < p 1 := (div_pos (by exact_mod_cast g.r₁) sp).trans_le (cx_mem hp 1).1
  obtain ⟨B₁, B₂⟩ := columnF_bounds hp
  have hηb : |p 7 - 1 / 2| ≤ (etaZ b : ℝ) / Sz := magZ_bound (deltaF_mem hp)
  -- the analytic lower bound
  have LG := Layered.layered_gainS p (an.k₁ / 2) (an.k₂ / 2) an.k₁ an.k₂ (by ring) (by ring) hr hs hηb
    (eta_lt ho) an.cube B₁ B₂ (tau_pos ho) (tau_le hp g ho) (tau_mono ho) (rho_lt ho)
    (Aw b) (Ψw b an) (fun m _ => aZ_bound hp g (m := m)) (fun m hm => psiZ_bound hp an m)
    (posF b an) (fun m _ h => posF_sound hp h)
  -- the retained waves as quadratic forms
  obtain ⟨v₁, hv₁⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0 := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = p 7 - 1 / 2 := ⟨_, rfl⟩
  have modes : (∑ m ∈ waves an.cube, waveQuadS p an (Aw b m) (Ψw b an m) (posF b an m) m v₁ v₂ δ) ≤
      ∑ m ∈ waves an.cube, Layered.modeLowerS p (an.k₁ / 2) (an.k₂ / 2) (m.1 * an.k₁ + m.2 * an.k₂)
        (Aw b m) (Ψw b an m) (posF b an m) m := by
    apply Finset.sum_le_sum
    intro m hm
    rw [hv₁, hv₂, hδ]
    exact modeLower_geS p an (Aw b m) (Ψw b an m) (posF b an m) m (modeW_nonneg hp g (wok m hm))
      (tReal_nonneg' hp g m)
  have regroup : (∑ m ∈ waves an.cube, waveQuadS p an (Aw b m) (Ψw b an m) (posF b an m) m v₁ v₂ δ) =
      sumL an (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.1 : ℝ) ^ 2) * v₁ ^ 2 +
      sumL an (fun m => 2 * (lamR p an (Aw b m) (Ψw b an m) m * ((m.1 : ℝ) * (m.2 : ℝ)))) * (v₁ * v₂) +
      sumL an (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.2 : ℝ) ^ 2) * v₂ ^ 2 +
      sumL an (fun m => muRS p an (Aw b m) (Ψw b an m) (posF b an m) m) * δ ^ 2 +
      X₁ b an p * (δ * v₁) + X₂ b an p * (δ * v₂) - E₁ b an p * |δ * v₁| - E₂ b an p * |δ * v₂| := by
    unfold X₁ X₂ E₁ E₂ sumL
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    unfold waveQuadS waveQuad
    ring
  have two : sumL an (fun m => 2 * (lamR p an (Aw b m) (Ψw b an m) m * ((m.1 : ℝ) * (m.2 : ℝ)))) =
      2 * e01 b an p := by
    unfold e01 sumL; rw [← Finset.mul_sum]
  -- the matrix with sign-chosen mixed entries
  set a02 := X₁ b an p / 2 - sgn (δ * v₁) * E₁ b an p / 2 with ha02
  set a12 := X₂ b an p / 2 - sgn (δ * v₂) * E₂ b an p / 2 with ha12
  have quadEq : quad6 (e00 b an p) (e01 b an p) (e11 b an p) a02 a12 (e22S b an p) v₁ v₂ δ =
      2 * Real.pi * cReal p ^ 2 * δ ^ 2 +
        (∑ m ∈ waves an.cube, waveQuadS p an (Aw b m) (Ψw b an m) (posF b an m) m v₁ v₂ δ) -
        Hout b an p * (((tauZ b : ℝ) / Sz) ^ 2 * δ ^ 2 + 8 * Real.pi ^ 2 * (v₁ ^ 2 + v₂ ^ 2)) := by
    rw [regroup, two]
    have s1 := sgn_mul (δ * v₁)
    have s2 := sgn_mul (δ * v₂)
    unfold quad6 e00 e11 e22S
    rw [ha02, ha12, ← s1, ← s2]
    ring
  -- the analytic bound in matrix form
  have gainQ : quad6 (e00 b an p) (e01 b an p) (e11 b an p) a02 a12 (e22S b an p) v₁ v₂ δ ≤
      2 * ac * (energy (chartPoint p) -
        energy (chartPoint (Layered.anchorChart p (an.k₁ / 2) (an.k₂ / 2)))) := by
    rw [quadEq]
    rw [← hv₁, ← hv₂, ← hδ] at LG
    unfold Hout
    linarith
  -- enclosures of the six entries
  have encl (f : Wave → FI) (v : Wave → ℝ) (h : ∀ m ∈ waves an.cube, (f m).Mem (v m)) :
      (sumW (wavesList an.cube) f).Mem (sumL an v) := by
    have := sumW_mem (wavesList an.cube) f v (fun m hm => h m ((mem_wavesList _ m).mp hm))
    unfold sumL
    rw [sum_waves_eq]
    exact this
  have hout := outerF_mem hp g ho
  have lamE (c : ℤ) (m : Wave) (hm : m ∈ waves an.cube) :
      (FI.smul c (lamF b an m)).Mem ((c : ℝ) * lamR p an (Aw b m) (Ψw b an m) m) :=
    FI.smul_mem c (lamF_mem' hp g (wok m hm))
  have m00 : (m00F b an).Mem (e00 b an p) := by
    have hs := encl (fun m => FI.smul (m.1 * m.1) (lamF b an m))
      (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.1 : ℝ) ^ 2) (fun m hm => by
        have h := lamE (m.1 * m.1) m hm
        have e : ((m.1 * m.1 : ℤ) : ℝ) * lamR p an (Aw b m) (Ψw b an m) m =
            lamR p an (Aw b m) (Ψw b an m) m * (m.1 : ℝ) ^ 2 := by push_cast; ring
        rw [e] at h
        exact h)
    have h := FI.sub_mem hs (FI.mul_mem (FI.sq_mem twoPiF_mem) (FI.smul_mem 2 hout))
    unfold m00F fourPiSqF e00 Hout
    push_cast at h
    exact h
  have m11 : (m11F b an).Mem (e11 b an p) := by
    have hs := encl (fun m => FI.smul (m.2 * m.2) (lamF b an m))
      (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.2 : ℝ) ^ 2) (fun m hm => by
        have h := lamE (m.2 * m.2) m hm
        have e : ((m.2 * m.2 : ℤ) : ℝ) * lamR p an (Aw b m) (Ψw b an m) m =
            lamR p an (Aw b m) (Ψw b an m) m * (m.2 : ℝ) ^ 2 := by push_cast; ring
        rw [e] at h
        exact h)
    have h := FI.sub_mem hs (FI.mul_mem (FI.sq_mem twoPiF_mem) (FI.smul_mem 2 hout))
    unfold m11F fourPiSqF e11 Hout
    push_cast at h
    exact h
  have m01 : (m01F b an).Mem (e01 b an p) := by
    have hs := encl (fun m => FI.smul (m.1 * m.2) (lamF b an m))
      (fun m => lamR p an (Aw b m) (Ψw b an m) m * ((m.1 : ℝ) * (m.2 : ℝ))) (fun m hm => by
        have h := lamE (m.1 * m.2) m hm
        have e : ((m.1 * m.2 : ℤ) : ℝ) * lamR p an (Aw b m) (Ψw b an m) m =
            lamR p an (Aw b m) (Ψw b an m) m * ((m.1 : ℝ) * (m.2 : ℝ)) := by push_cast; ring
        rw [e] at h
        exact h)
    unfold m01F e01
    exact hs
  have m22 : (m22FS b an).Mem (e22S b an p) := by
    have hs := encl (muFS b an) (fun m => muRS p an (Aw b m) (Ψw b an m) (posF b an m) m)
      (fun m hm => muFS_mem' hp g (wok m hm))
    have h := FI.sub_mem (FI.add_mem (FI.mul_mem twoPiF_mem (FI.sq_mem (cF_mem hp g))) hs)
      (FI.mul_mem (FI.sq_mem (ptF_mem (tauZ b))) hout)
    unfold m22FS e22S Hout
    exact h
  have E1nn : 0 ≤ E₁ b an p := by
    unfold E₁ sumL
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (epsR_nonneg p an _ _ m (modeW_nonneg hp g (wok m hm)) (tReal_nonneg' hp g m))
      (abs_nonneg _)
  have E2nn : 0 ≤ E₂ b an p := by
    unfold E₂ sumL
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (epsR_nonneg p an _ _ m (modeW_nonneg hp g (wok m hm)) (tReal_nonneg' hp g m))
      (abs_nonneg _)
  have chiE (c : Wave → ℤ) (m : Wave) (hm : m ∈ waves an.cube) :
      (FI.smul (c m) (chiF b an m)).Mem (chiR p an (Aw b m) (Ψw b an m) m * ((c m : ℤ) : ℝ)) := by
    have h : (FI.smul (c m) (chiF b an m)).Mem (((c m : ℤ) : ℝ) * chiR p an (Aw b m) (Ψw b an m) m) :=
      FI.smul_mem (c m) (chiF_mem' hp g (wok m hm))
    rw [mul_comm] at h
    exact h
  have epsE (c : Wave → ℤ) (m : Wave) (hm : m ∈ waves an.cube) :
      (FI.smul ((c m).natAbs : ℤ) (epsF b an m)).Mem
        (epsR p an (Aw b m) (Ψw b an m) m * |((c m : ℤ) : ℝ)|) := by
    have h : (FI.smul ((c m).natAbs : ℤ) (epsF b an m)).Mem
        ((((c m).natAbs : ℤ) : ℝ) * epsR p an (Aw b m) (Ψw b an m) m) :=
      FI.smul_mem _ (epsF_mem' hp g (wok m hm))
    have e : ((((c m).natAbs : ℤ) : ℝ)) = |((c m : ℤ) : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    rw [e, mul_comm] at h
    exact h
  have m02 : (m02F b an).Mem a02 := by
    have hX := encl (fun m => FI.smul m.1 (chiF b an m))
      (fun m => chiR p an (Aw b m) (Ψw b an m) m * (m.1 : ℝ)) (fun m hm => chiE (fun m => m.1) m hm)
    have hE := encl (fun m => FI.smul (m.1.natAbs : ℤ) (epsF b an m))
      (fun m => epsR p an (Aw b m) (Ψw b an m) m * |(m.1 : ℝ)|) (fun m hm => epsE (fun m => m.1) m hm)
    have hX' : (sumW (wavesList an.cube) (fun m => FI.smul m.1 (chiF b an m))).Mem (X₁ b an p) := hX
    have hE' : (sumW (wavesList an.cube) (fun m => FI.smul (m.1.natAbs : ℤ) (epsF b an m))).Mem
        (E₁ b an p) := hE
    have hy : |-(sgn (δ * v₁) * E₁ b an p / 2)| ≤ E₁ b an p / 2 := by
      rw [abs_neg, abs_div, abs_mul, abs_sgn, one_mul, abs_of_nonneg E1nn, abs_two]
    have h := FI.add_mem (halfF_mem hX') (symF_mem (halfF_mem hE') hy)
    unfold m02F
    rw [ha02]
    convert h using 1
  have m12 : (m12F b an).Mem a12 := by
    have hX := encl (fun m => FI.smul m.2 (chiF b an m))
      (fun m => chiR p an (Aw b m) (Ψw b an m) m * (m.2 : ℝ)) (fun m hm => chiE (fun m => m.2) m hm)
    have hE := encl (fun m => FI.smul (m.2.natAbs : ℤ) (epsF b an m))
      (fun m => epsR p an (Aw b m) (Ψw b an m) m * |(m.2 : ℝ)|) (fun m hm => epsE (fun m => m.2) m hm)
    have hX' : (sumW (wavesList an.cube) (fun m => FI.smul m.2 (chiF b an m))).Mem (X₂ b an p) := hX
    have hE' : (sumW (wavesList an.cube) (fun m => FI.smul (m.2.natAbs : ℤ) (epsF b an m))).Mem
        (E₂ b an p) := hE
    have hy : |-(sgn (δ * v₂) * E₂ b an p / 2)| ≤ E₂ b an p / 2 := by
      rw [abs_neg, abs_div, abs_mul, abs_sgn, one_mul, abs_of_nonneg E2nn, abs_two]
    have h := FI.add_mem (halfF_mem hX') (symF_mem (halfF_mem hE') hy)
    unfold m12F
    rw [ha12]
    convert h using 1
  -- the Gram enclosures and the surplus
  have g00 : (g00F b).Mem (p 0 ^ 2) := FI.sq_mem (cx_mem hp 0)
  have g01 : (g01F b).Mem (p 0 ^ 2 * p 2) := FI.mul_mem (FI.sq_mem (cx_mem hp 0)) (cx_mem hp 2)
  have g11 : (g11F b).Mem ((p 0 * p 2) ^ 2 + p 1 ^ 2) :=
    FI.add_mem (FI.sq_mem (FI.mul_mem (cx_mem hp 0) (cx_mem hp 2))) (FI.sq_mem (cx_mem hp 1))
  have g22 : (g22F b).Mem (cReal p ^ 2) := FI.sq_mem (cF_mem hp g)
  have hl : (ofRat lam lam).Mem (lam : ℝ) := ofRat_mem ⟨le_rfl, le_rfl⟩
  have sub (x y : FI) (X Y : ℝ) (hx : x.Mem X) (hy : y.Mem Y) :
      (subScaled x y lam).Mem (X - (lam : ℝ) * Y) := FI.sub_mem hx (FI.mul_mem hl hy)
  have pd := pdOk_sound (surplusFS b an lam) hpd (sub _ _ _ _ m00 g00) (sub _ _ _ _ m01 g01)
    (sub _ _ _ _ m11 g11) m02 m12 (sub _ _ _ _ m22 g22) v₁ v₂ δ
  have lin : quad6 (e00 b an p - (lam : ℝ) * p 0 ^ 2) (e01 b an p - (lam : ℝ) * (p 0 ^ 2 * p 2))
      (e11 b an p - (lam : ℝ) * ((p 0 * p 2) ^ 2 + p 1 ^ 2)) a02 a12
      (e22S b an p - (lam : ℝ) * cReal p ^ 2) v₁ v₂ δ =
      quad6 (e00 b an p) (e01 b an p) (e11 b an p) a02 a12 (e22S b an p) v₁ v₂ δ -
        (lam : ℝ) * layerGram p (an.k₁ / 2) (an.k₂ / 2) := by
    unfold layerGram
    rw [← hv₁, ← hv₂, ← hδ]
    unfold quad6
    ring
  rw [lin] at pd
  linarith

theorem splitOkS_gain {an : Anchor} {lam : ℚ} :
    ∀ (d : ℕ) {b : Cell}, splitOkS an lam d b = true → ∀ {p : Chart}, b.Mem p →
      (lam : ℝ) * layerGram p (an.k₁ / 2) (an.k₂ / 2) ≤
        2 * ac * (energy (chartPoint p) -
          energy (chartPoint (Layered.anchorChart p (an.k₁ / 2) (an.k₂ / 2))))
  | 0, b, ok, p, hp => leafOk_gainS ok hp
  | d + 1, b, ok, p, hp => by
    simp only [splitOkS, Bool.and_eq_true] at ok
    rcases two_closed_children b (widest b) (midpoint b (widest b)) p hp with h | h
    · exact splitOkS_gain d ok.1 h
    · exact splitOkS_gain d ok.2 h

end BccSharp.Coulomb.CompactCover.Layered.Fix

/-! ### The PlanarAnchor route with the sign-aware gain -/

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-! ### Anchor separation without `r s < 1`

`anchor_sep` bounds `|B (m + f₀)|²` by its third row alone, which needs `r s < 1`. When
`f₀ 1 = f₀ 2 = −1/2`, the third coordinate `x₂ = m₂ − 1/2` is either `±1/2`, and then the second
row adds `s² (1 − |z|)²/4`, or at least `3/2` in size, and then the third row alone suffices
when `r s < 3`. -/

/-- The largest `|z|` on the cell. -/
def zMax (b : Cell) : ℚ := max |b.lo 4| |b.hi 4|

/-- The separation guard without `r s < 1`: `r s < 3`, `|z| < 1` and
`(s (1 − |z|))² + 1/(r s)² > 1` on the cell. -/
def sep2Ok (b : Cell) : Bool :=
  decide (0 < b.lo 0 ∧ 0 < b.lo 1 ∧ b.hi 0 * b.hi 1 < 3 ∧ zMax b < 1 ∧
    1 < (b.lo 1 * (1 - zMax b)) ^ 2 + 1 / (b.hi 0 * b.hi 1) ^ 2)

theorem anchor_sep2 {p : Chart} (hr : 0 < p 0) (hs : 0 < p 1) (h3 : p 0 * p 1 < 3)
    (hz : |p 4| ≤ 1) (hC : 1 < (p 1 * (1 - |p 4|)) ^ 2 + 1 / (p 0 * p 1) ^ 2)
    (f₀ : Vec) (hf1 : f₀ 1 = -1 / 2) (hf2 : f₀ 2 = -1 / 2) (m : IntVec) :
    (1 / 2 : ℝ) ^ 2 < sq ((chartBasis p).mulVec (castVec m + f₀)) := by
  have hrs0 : 0 < p 0 * p 1 := mul_pos hr hs
  set x := castVec m + f₀ with hxdef
  have hx1 : x 1 = (m 1 : ℝ) - 1 / 2 := by
    show (castVec m + f₀) 1 = _
    simp [castVec, hf1]; ring
  have hx2 : x 2 = (m 2 : ℝ) - 1 / 2 := by
    show (castVec m + f₀) 2 = _
    simp [castVec, hf2]; ring
  have hq := sq_chartBasis p x
  have t3 : (x 2 * (p 0 * p 1)⁻¹) ^ 2 = x 2 ^ 2 / (p 0 * p 1) ^ 2 := by
    rw [mul_pow, inv_pow, div_eq_mul_inv]
  have hden0 : 0 < (p 0 * p 1) ^ 2 := by positivity
  have t1 := sq_nonneg (p 0 * (x 0 + p 2 * x 1 + p 3 * x 2))
  rcases (show (m 2 = 0 ∨ m 2 = 1) ∨ (m 2 ≤ -1 ∨ 2 ≤ m 2) by omega) with hm | hm
  · -- `x₂ = ±1/2`
    have hx2v : x 2 = -1 / 2 ∨ x 2 = 1 / 2 := by
      rcases hm with h | h
      · left; rw [hx2, h]; norm_num
      · right; rw [hx2, h]; norm_num
    have h_abs_2 : |x 2| = 1 / 2 := by
      rcases hx2v with h | h <;> rw [h] <;> norm_num
    have hx2sq : x 2 ^ 2 = 1 / 4 := by
      rcases hx2v with h | h <;> rw [h] <;> norm_num
    have h_abs_1 : (1 / 2 : ℝ) ≤ |x 1| := by
      rw [hx1]
      rcases le_or_gt (m 1) 0 with h | h
      · have : (m 1 : ℝ) ≤ 0 := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
      · have : (1 : ℝ) ≤ m 1 := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    have tri : |x 1| - |p 4 * x 2| ≤ |x 1 + p 4 * x 2| := by
      have := abs_sub_abs_le_abs_sub (x 1) (-(p 4 * x 2))
      rwa [sub_neg_eq_add, abs_neg] at this
    rw [abs_mul, h_abs_2] at tri
    have hrow : (1 - |p 4|) / 2 ≤ |x 1 + p 4 * x 2| := by linarith
    have hrow2 : ((1 - |p 4|) / 2) ^ 2 ≤ (x 1 + p 4 * x 2) ^ 2 := by
      rw [← sq_abs (x 1 + p 4 * x 2)]; exact pow_le_pow_left₀ (by linarith) hrow 2
    have t2 : (p 1 * (1 - |p 4|)) ^ 2 / 4 ≤ (p 1 * (x 1 + p 4 * x 2)) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hrow2 (sq_nonneg (p 1))
      have e1 : (p 1 * (1 - |p 4|)) ^ 2 / 4 = p 1 ^ 2 * ((1 - |p 4|) / 2) ^ 2 := by ring
      have e2 : (p 1 * (x 1 + p 4 * x 2)) ^ 2 = p 1 ^ 2 * (x 1 + p 4 * x 2) ^ 2 := by ring
      rw [e1, e2]; exact this
    have t3' : (x 2 * (p 0 * p 1)⁻¹) ^ 2 = 1 / 4 * (1 / (p 0 * p 1) ^ 2) := by
      rw [t3, hx2sq]; ring
    rw [hq, t3']
    linarith
  · -- `|x₂| ≥ 3/2`
    have habs : (3 / 2 : ℝ) ≤ |x 2| := by
      rw [hx2]
      rcases hm with h | h
      · have : (m 2 : ℝ) ≤ -1 := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
      · have : (2 : ℝ) ≤ m 2 := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    have hx2sq : (3 / 2 : ℝ) ^ 2 ≤ x 2 ^ 2 := by
      rw [← sq_abs (x 2)]; exact pow_le_pow_left₀ (by norm_num) habs 2
    have hden : (p 0 * p 1) ^ 2 < 9 := by nlinarith
    have key : (1 / 2 : ℝ) ^ 2 < x 2 ^ 2 / (p 0 * p 1) ^ 2 := by
      rw [lt_div_iff₀ hden0]; nlinarith
    have t2 := sq_nonneg (p 1 * (x 1 + p 4 * x 2))
    rw [hq, t3]
    linarith

theorem sep2Ok_sound {b : Cell} (h : sep2Ok b = true) {p : Chart} (hp : b.Mem p) (m : IntVec) :
    (1 / 2 : ℝ) ^ 2 < sq ((chartBasis p).mulVec (castVec m + halfAll)) := by
  simp only [sep2Ok, decide_eq_true_eq] at h
  obtain ⟨l0, l1, h3, hz, hC⟩ := h
  have p0 := hp 0
  have p1 := hp 1
  have p4 := hp 4
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast l0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast l1
  have hr : 0 < p 0 := b0.trans_le p0.1
  have hs : 0 < p 1 := b1.trans_le p1.1
  have hzm : |p 4| ≤ ((zMax b : ℚ) : ℝ) := by
    unfold zMax
    push_cast
    rw [abs_le]
    constructor
    · have a1 := neg_abs_le (b.lo 4 : ℝ)
      have a2 := le_max_left |(b.lo 4 : ℝ)| |(b.hi 4 : ℝ)|
      linarith [p4.1]
    · have a1 := le_abs_self (b.hi 4 : ℝ)
      have a2 := le_max_right |(b.lo 4 : ℝ)| |(b.hi 4 : ℝ)|
      linarith [p4.2]
  have hzR : ((zMax b : ℚ) : ℝ) < 1 := by exact_mod_cast hz
  have h3R : ((b.hi 0 : ℚ) : ℝ) * ((b.hi 1 : ℚ) : ℝ) < 3 := by exact_mod_cast h3
  have hi0 : (0 : ℝ) ≤ b.hi 0 := b0.le.trans (p0.1.trans p0.2)
  have prod : p 0 * p 1 ≤ ((b.hi 0 : ℚ) : ℝ) * ((b.hi 1 : ℚ) : ℝ) := mul_le_mul p0.2 p1.2 hs.le hi0
  have hrs : p 0 * p 1 < 3 := lt_of_le_of_lt prod h3R
  have hCR : (1 : ℝ) < (((b.lo 1 : ℚ) : ℝ) * (1 - ((zMax b : ℚ) : ℝ))) ^ 2 +
      1 / (((b.hi 0 : ℚ) : ℝ) * ((b.hi 1 : ℚ) : ℝ)) ^ 2 := by exact_mod_cast hC
  have m1 : ((b.lo 1 : ℚ) : ℝ) * (1 - ((zMax b : ℚ) : ℝ)) ≤ p 1 * (1 - |p 4|) :=
    mul_le_mul p1.1 (by linarith) (by linarith) hs.le
  have m1' : (((b.lo 1 : ℚ) : ℝ) * (1 - ((zMax b : ℚ) : ℝ))) ^ 2 ≤ (p 1 * (1 - |p 4|)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg b1.le (by linarith)) m1 2
  have m2 : 1 / (((b.hi 0 : ℚ) : ℝ) * ((b.hi 1 : ℚ) : ℝ)) ^ 2 ≤ 1 / (p 0 * p 1) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) prod 2)
  have hC' : 1 < (p 1 * (1 - |p 4|)) ^ 2 + 1 / (p 0 * p 1) ^ 2 := by linarith
  have hz1 : |p 4| ≤ 1 := by linarith
  exact anchor_sep2 hr hs hrs hz1 hC' halfAll rfl rfl m

/-- `planarAnchorCertOk` with the sign-aware layered gain (`splitOkS`) and the separation guard
`sepOk b || sep2Ok box`. -/
def planarAnchorSOk (c : PlanarAnchorCert) (box : Cell) (n : IntVec) : Bool :=
  let b := shiftCell box (seamShiftW n)
  let an := anchorW n
  (((decide (0 < c.k) && splitOkS an (lamOf c.k) c.depth b) &&
    (JLeaf.registrationCheck c.reg.B c.reg.N c.reg.U c.reg.f0 &&
      decide (c.reg.w = ![(an.k₁ : ℚ) / 2, (an.k₂ : ℚ) / 2, 1 / 2]))) &&
    ((guardsOk b && (sepOk b || sep2Ok box)) &&
      decide (2 * (100 * (strainF b c.reg.N c.reg.U).hi + 200 * (gramF b an).hi) ≤ Sz)))

/-- The route result of one accepted certificate. -/
theorem planarAnchorSOk_sound (latticeCase : LatticeCase) (c : PlanarAnchorCert) (box : Cell) (n : IntVec)
    (ok : planarAnchorSOk c box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) := by
  simp only [planarAnchorSOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨hk, hsplit⟩, hreg, hw⟩, ⟨hg, hsep⟩, hcost⟩ := ok
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨an, han⟩ : ∃ an, an = anchorW n := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb] at hsplit hg hsep hcost
  rw [← han] at hsplit hcost hw
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  have g : Guards b := by
    have := of_decide_eq_true hg
    exact ⟨this.1, this.2.1, this.2.2⟩
  have sp := Sz_pos
  have e0 : p' 0 = p 0 := by rw [hp'def]; rfl
  have e1 : p' 1 = p 1 := by rw [hp'def]; rfl
  have hr : 0 < p 0 := by
    have := (div_pos (by exact_mod_cast g.r₀) sp).trans_le (cx_mem hp' 0).1
    rwa [e0] at this
  have hs : 0 < p 1 := by
    have := (div_pos (by exact_mod_cast g.r₁) sp).trans_le (cx_mem hp' 1).1
    rwa [e1] at this
  -- the gain
  have gain := splitOkS_gain c.depth hsplit hp'
  have hE : energy (chartPoint p') = energy (chartPoint p) := by
    rw [hp'def, chartPoint_shift, energy_wrap]
  have hA := anchor_chart_wrap p n
  rw [← hp'def, ← han] at hA
  have hEa : energy (chartPoint (anchorChart p' (an.k₁ / 2) (an.k₂ / 2))) =
      energy (anchorOf (chartPoint p) halfAll) := by rw [hA, energy_wrap]
  have hDa : defect (chartPoint (anchorChart p' (an.k₁ / 2) (an.k₂ / 2))) =
      defect (anchorOf (chartPoint p) halfAll) := by rw [hA, defect_wrap]
  have hG := gram_eq p n
  rw [← hp'def, ← han] at hG
  obtain ⟨bq, hbq⟩ : ∃ x, x = sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) :=
    ⟨_, rfl⟩
  rw [← hbq] at hG
  rw [hE, hEa, hG] at gain
  -- the scale and the gap
  obtain ⟨_, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gapB := Constants.reference_gap_checked
  have gap0 : 0 < gap := gapB.2
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := gapB.1.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  -- the anchor defect from the literal registration
  obtain ⟨pa, hpa⟩ : ∃ q, q = anchorChart p' (an.k₁ / 2) (an.k₂ / 2) := ⟨_, rfl⟩
  rw [← hpa] at hEa hDa hA
  have hstrain : JLeaf.strainCost c.reg.N c.reg.U pa = JLeaf.strainCost c.reg.N c.reg.U p' := by
    have h0 : pa 0 = p' 0 := by rw [hpa]; rfl
    have h1 : pa 1 = p' 1 := by rw [hpa]; rfl
    have h2 : pa 2 = p' 2 := by rw [hpa]; rfl
    have h3 : pa 3 = p' 3 := by rw [hpa]; rfl
    have h4 : pa 4 = p' 4 := by rw [hpa]; rfl
    unfold JLeaf.strainCost JLeaf.strainEntry
    rw [h0, h1, h2, h3, h4]
  have himg (i : Fin 3) : JLeaf.img (fun i => -c.reg.w i) true pa i = 0 := by
    rw [hw, hpa]
    fin_cases i <;> simp [JLeaf.img, anchorChart, DirectRoute.offset]
  have hprimal : JLeaf.primalQ (fun i => -c.reg.w i) true pa = 0 := by
    simp only [JLeaf.primalQ, JLeaf.rowA, JLeaf.rowB, JLeaf.rowC, himg]
    ring
  have hregCost : JLeaf.regCost c.reg.N c.reg.U c.reg.w pa = 100 * JLeaf.strainCost c.reg.N c.reg.U p' := by
    unfold JLeaf.regCost
    rw [hprimal, hstrain]
    ring
  have strainUp := (strainF_mem hp' g c.reg.N c.reg.U).2
  have gramUp := (gramF_mem hp' g an).2
  rw [hG] at gramUp
  have hcostR : 2 * (100 * ((strainF b c.reg.N c.reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) ≤ (Sz : ℝ) := by
    exact_mod_cast hcost
  have dUp : 100 * JLeaf.strainCost c.reg.N c.reg.U p' + 200 * bq ≤ 1 / 2 := by
    have q1 : 100 * JLeaf.strainCost c.reg.N c.reg.U p' + 200 * bq ≤
        (100 * ((strainF b c.reg.N c.reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) / Sz := by
      rw [add_div, mul_div_assoc, mul_div_assoc]
      linarith
    have q2 : (100 * ((strainF b c.reg.N c.reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) / Sz ≤ 1 / 2 := by
      rw [div_le_iff₀ sp]; linarith
    linarith
  have hvalid : (chartPoint p).Valid := gp.1
  have paValid : (chartPoint pa).Valid := by
    rw [hA]
    have av := anchor_valid _ hvalid halfAll halfAll_half
    refine ⟨av.1, fun m h => av.2 (m - ![n 0, n 1, 1]) ?_⟩
    simp only [wrap] at h
    rw [JLeaf.castVec_sub', ← h]
    abel
  have regSmall : JLeaf.regCost c.reg.N c.reg.U (fun i => c.reg.f0 i + (c.reg.wrap i : ℚ)) pa ≤ 1 / 2 := by
    show JLeaf.regCost c.reg.N c.reg.U c.reg.w pa ≤ 1 / 2
    rw [hregCost]; linarith
  have dAnchor := JLeaf.defect_le_regCost c.reg.B c.reg.N c.reg.U c.reg.f0 c.reg.wrap hreg pa paValid regSmall
  have dAnchor' : defect (anchorOf (chartPoint p) halfAll) ≤ 100 * JLeaf.strainCost c.reg.N c.reg.U p' := by
    rw [← hDa, ← hregCost]; exact dAnchor
  -- the defect transport
  have hsep₁ := gp.2.2.1
  have asep : ∀ m : IntVec, (1 / 2 : ℝ) ^ 2 < sq ((chartPoint p).basis.mulVec (castVec m + halfAll)) := by
    rcases Bool.or_eq_true_iff.mp hsep with hsep | hsep
    · have hrs : p 0 * p 1 < 1 := by
        have hlt := of_decide_eq_true hsep
        have h1 := FI.mulPos_mem (cx_mem hp' 0) (cx_mem hp' 1)
        have h2 : ((FI.mulPos (cx b 0) (cx b 1)).hi : ℝ) / Sz < 1 := by
          rw [div_lt_one sp]; exact_mod_cast hlt
        rw [e0, e1] at h1
        linarith [h1.2]
      exact fun m => anchor_sep hr hs hrs halfAll rfl m
    · exact fun m => sep2Ok_sound hsep hp m
  have trans := defect_transport (chartPoint p) hvalid hsep₁ halfAll halfAll_half asep n
    (by rw [← hbq]; linarith)
  rw [← hbq] at trans
  -- combine
  have hk0 : (0 : ℝ) < c.k := by exact_mod_cast hk
  have hlam : (2 * ac) * (200 * gap + (c.k : ℝ)) ≤ (lamOf c.k : ℝ) := by
    unfold lamOf
    push_cast
    have h1 : 0 ≤ 200 * gap + (c.k : ℝ) := by positivity
    have h2 : 200 * gap + (c.k : ℝ) ≤ 200 * (Constants.gapBracket.hi : ℝ) + c.k := by linarith
    have h3 : (2 * ac) * (200 * gap + (c.k : ℝ)) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + c.k) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    have h4 : (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + c.k) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + c.k) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (200 * gap + (c.k : ℝ)) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((200 * gap + (c.k : ℝ)) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  have deficitGain : deficit (anchorOf (chartPoint p) halfAll) + ((0 : ℚ) : ℝ) +
      ((c.k : ℚ) : ℝ) * bq ≤ deficit (chartPoint p) := by
    unfold deficit
    have h1 := mul_le_mul_of_nonneg_left trans gap0.le
    push_cast
    nlinarith
  have rel : relativeCheck 0 c.k = true := by
    unfold relativeCheck
    exact decide_eq_true ⟨le_rfl, hk⟩
  exact relativeOptical_route_of_lattice latticeCase p hvalid halfAll n halfAll_half 0 c.k rel (by
    rw [hbq] at deficitGain; exact deficitGain)

end BccSharp.Coulomb.CompactCover.Layered
