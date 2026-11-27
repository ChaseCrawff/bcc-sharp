import BccSharp.TwoSite.DefectInvariance
import BccSharp.Lattice.StarDefect
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false

/-! # A radial gap saturates the defect (the Adaptive FCC-reference `Q` boxes)

Six Adaptive `Q` boxes (stage 5, window 66) have an anchor of class `(−1/2, −1/2, −1/2)` with no BCC
registration, so no defect transport applies, and their anchor is not saturated by counting
(`AdaptiveOptical.innerOk` fails). Their lifts have a **radial gap** instead: no lift is between
`0.914` and `1.229` long. Then every trial matches each of the six unit axis vectors of the
star with a lift whose length is at least `g` away from `1`, so it costs at least `25 · 6 · g²`
(`trial_ge_of_gap`), and the defect is `1` when that is at least `1`
(`defect_eq_one_of_gap`).

`gapOk g b` checks, in exact rationals on a box `b` of the chart, that every lift `B w`
(`w = m ≠ 0` or `w = m + (−1/2, −1/2, −1/2)`, `m ∈ ℤ³`) has `|B w|² ≤ (1 − g)²` or
`(1 + g)² ≤ |B w|²`. The chart basis is upper triangular, so the proof (`gapOk_lift`) is a
case analysis on the size of `w₂`, then `w₁`, then `w₀`: the long lifts are bounded below by
one row (by two for `w = (m₀, ±1, 0)` with `|m₀| ≥ 1`), and the twelve short ones (`(±1, 0, 0)`, `(0, ±1, 0)` and the eight
`(±1/2, ±1/2, ±1/2)`) above by all three. `defect_anchor_gap` gives `defect = 1` for the anchor
on the whole box. -/

open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.AdaptiveGap
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb

/-! ### The defect from a radial gap -/

/-- `|a − b| ≥ g` when `|b| = 1` and `|a|` is at least `g` away from `1` (in squares). -/
theorem sq_sub_ge_of_gap (a b : Vec) (hb : sq b = 1) (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (h : sq a ≤ (1 - g) ^ 2 ∨ (1 + g) ^ 2 ≤ sq a) : g ^ 2 ≤ sq (a - b) := by
  have hsub : sq (a - b) = sq a - 2 * (∑ i, a i * b i) + sq b := by
    simp only [sq, Pi.sub_apply, Fin.sum_univ_three]
    ring
  have cs : (∑ i, a i * b i) ^ 2 ≤ sq a * sq b := by
    simp only [sq, Fin.sum_univ_three]
    nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0),
      sq_nonneg (a 1 * b 2 - a 2 * b 1)]
  rw [hb, mul_one] at cs
  have A0 : 0 ≤ sq a := sq_nonnegative a
  have htt : Real.sqrt (sq a) ^ 2 = sq a := Real.sq_sqrt A0
  have hD : (∑ i, a i * b i) ≤ Real.sqrt (sq a) := by
    have h1 : |∑ i, a i * b i| ≤ Real.sqrt (sq a) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt cs
    exact (le_abs_self _).trans h1
  have key : (Real.sqrt (sq a) - 1) ^ 2 ≤ sq (a - b) := by
    rw [hsub, hb]
    nlinarith
  rcases h with h | h
  · have ht : Real.sqrt (sq a) ≤ 1 - g := by
      have h2 := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq (by linarith)] at h2
    have h3 : g ^ 2 ≤ (1 - Real.sqrt (sq a)) ^ 2 := pow_le_pow_left₀ hg0 (by linarith) 2
    have e : (1 - Real.sqrt (sq a)) ^ 2 = (Real.sqrt (sq a) - 1) ^ 2 := by ring
    linarith
  · have ht : 1 + g ≤ Real.sqrt (sq a) := by
      have h2 := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq (by linarith)] at h2
    have h3 : g ^ 2 ≤ (Real.sqrt (sq a) - 1) ^ 2 := pow_le_pow_left₀ hg0 (by linarith) 2
    linarith

/-- The six unit axis vectors of the star are the labels `8`–`13`. -/
theorem star_axis_sq (j : Fin 14) (hj : 8 ≤ j.val) : sq (star j) = 1 := by
  simp only [sq, Fin.sum_univ_three]
  revert hj
  fin_cases j <;> norm_num [star]

/-- With a radial gap `g`, every trial costs at least `25 · 6 · g²`. -/
theorem trial_ge_of_gap (q : TwoSite) (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (gapH : ∀ v ∈ neighbors q, sq v ≤ (1 - g) ^ 2 ∨ (1 + g) ^ 2 ≤ sq v)
    (U : Mat) (hU : proper U) (σ : Fin 14 ↪ ↥(neighbors q)) : 150 * g ^ 2 ≤ defectTrial U σ := by
  have hterm : ∀ j : Fin 14, 8 ≤ j.val → g ^ 2 ≤ sq ((σ j : Vec) - U.mulVec (star j)) := by
    intro j hj
    apply sq_sub_ge_of_gap _ _ _ g hg0 hg1 (gapH _ (σ j).2)
    rw [sq_orthogonal hU.1]
    exact star_axis_sq j hj
  have hS : (Finset.univ.filter (fun j : Fin 14 => 8 ≤ j.val)).card = 6 := by decide
  have hsum : 6 * g ^ 2 ≤ ∑ j, sq ((σ j : Vec) - U.mulVec (star j)) := by
    calc 6 * g ^ 2 = ∑ j ∈ Finset.univ.filter (fun j : Fin 14 => 8 ≤ j.val), g ^ 2 := by
          rw [Finset.sum_const, hS, nsmul_eq_mul]
          norm_num
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin 14 => 8 ≤ j.val),
            sq ((σ j : Vec) - U.mulVec (star j)) :=
          Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_filter.mp hj).2)
      _ ≤ ∑ j, sq ((σ j : Vec) - U.mulVec (star j)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => sq_nonnegative _)
  have hann : 0 ≤ ∑' v : ↥(neighbors q), (if v ∈ Set.range σ then 0 else annularWeight v.val) := by
    apply tsum_nonneg
    intro v
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  unfold defectTrial
  linarith

/-- **Radial gap.** If no neighbor of a valid configuration has a length within `g` of `1`
and `25 · 6 · g² ≥ 1`, its defect is `1`. -/
theorem defect_eq_one_of_gap (q : TwoSite) (hq : q.Valid) (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hg : 1 ≤ 150 * g ^ 2) (gapH : ∀ v ∈ neighbors q, sq v ≤ (1 - g) ^ 2 ∨ (1 + g) ^ 2 ≤ sq v) :
    defect q = 1 := by
  obtain ⟨hle, -, hatt⟩ := DefectInvariance.defect_eq_min q hq
  rcases hatt with h | ⟨U, hU, σ, hσ⟩
  · exact h
  · refine le_antisymm hle ?_
    rw [← hσ]
    exact hg.trans (trial_ge_of_gap q g hg0 hg1 gapH U hU σ)

/-! ### The gap on a box -/

/-- A bound of `|t|` on `[lo, hi]`. -/
def absMax (lo hi : ℚ) : ℚ := max (-lo) hi

theorem abs_le_absMax {lo hi : ℚ} {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    |t| ≤ ((absMax lo hi : ℚ) : ℝ) := by
  unfold absMax
  push_cast
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact h2.trans (le_max_right _ _)
  · rw [abs_of_nonpos h]
    exact (neg_le_neg h1).trans (le_max_left _ _)

/-- The class `(−1/2, −1/2, −1/2)`. -/
noncomputable def halfV : Vec := fun _ => -1 / 2

/-- No lift of the class `(−1/2, −1/2, −1/2)` has a squared length in `((1 − g)², (1 + g)²)` at
any point of the box (`gapOk_lift`), and `25 · 6 · g² ≥ 1`. With `r, s, x, y, z` the first five
chart coordinates: the third row bounds the lifts with `|w₂| ≥ 1`; the second row those with
`w₂ = 0`, `|w₁| ≥ 2` or `|w₂| = 1/2`, `|w₁| ≥ 3/2`; the first two rows together those with
`w₂ = 0`, `|w₁| = 1`, `|w₀| ≥ 1`; the first row the rest but twelve, which are bounded above. -/
def gapOk (g : ℚ) (b : Cell) : Bool :=
  let r0 := b.lo 0
  let r1 := b.hi 0
  let s0 := b.lo 1
  let s1 := b.hi 1
  let xM := absMax (b.lo 2) (b.hi 2)
  let yM := absMax (b.lo 3) (b.hi 3)
  let zM := absMax (b.lo 4) (b.hi 4)
  let L := (1 - g) ^ 2
  let H := (1 + g) ^ 2
  decide (0 < r0 ∧ 0 < s0 ∧ 0 ≤ g ∧ g ≤ 1 ∧ 1 ≤ 150 * g ^ 2 ∧
    H * (r1 * s1) ^ 2 ≤ 1 ∧
    H ≤ 4 * s0 ^ 2 ∧ H ≤ 4 * r0 ^ 2 ∧ r1 ^ 2 ≤ L ∧ r1 ^ 2 * xM ^ 2 + s1 ^ 2 ≤ L ∧
    xM ≤ 1 ∧ H ≤ r0 ^ 2 * (1 - xM) ^ 2 + s0 ^ 2 ∧
    zM ≤ 3 ∧ H ≤ s0 ^ 2 * (3 / 2 - zM / 2) ^ 2 ∧
    xM + yM ≤ 3 ∧ H ≤ r0 ^ 2 * (3 / 2 - (xM + yM) / 2) ^ 2 ∧
    r1 ^ 2 * (1 / 2 + (xM + yM) / 2) ^ 2 + s1 ^ 2 * (1 / 2 + zM / 2) ^ 2 +
      1 / (4 * (r0 * s0) ^ 2) ≤ L)

/-- An integer is `0`, `±1`, or at least `2` in size. -/
theorem int_cases (k : ℤ) : (k : ℝ) = 0 ∨ |(k : ℝ)| = 1 ∨ 2 ≤ |(k : ℝ)| := by
  rcases (show k ≤ -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with h | h | h | h | h
  · right; right
    have h' : (k : ℝ) ≤ -2 := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith
  · right; left
    subst h
    norm_num
  · left
    subst h
    simp
  · right; left
    subst h
    norm_num
  · right; right
    have h' : (2 : ℝ) ≤ k := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    exact h'

/-- A half-integer `k − 1/2` is `±1/2` or at least `3/2` in size. -/
theorem half_cases (k : ℤ) : |(k : ℝ) + -1 / 2| = 1 / 2 ∨ 3 / 2 ≤ |(k : ℝ) + -1 / 2| := by
  rcases (show k ≤ -1 ∨ k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with h | h | h | h
  · right
    have h' : (k : ℝ) ≤ -1 := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith
  · left
    subst h
    norm_num
  · left
    subst h
    norm_num
  · right
    have h' : (2 : ℝ) ≤ k := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith

/-- `|a + b + c| ≥ |a| − |b| − |c|`. -/
theorem abs_add3_ge (a b c : ℝ) : |a| - |b| - |c| ≤ |a + b + c| := by
  have h := abs_add_three (a + b + c) (-b) (-c)
  rw [show a + b + c + -b + -c = a by ring, abs_neg, abs_neg] at h
  linarith

/-- A row bounded below: `(F u)² ≥ f₀² c²` from `0 ≤ f₀ ≤ F`, `0 ≤ c ≤ |u|`. -/
theorem row_ge {F f0 c u : ℝ} (hf0 : 0 ≤ f0) (hF : f0 ≤ F) (hc : 0 ≤ c) (hu : c ≤ |u|) :
    f0 ^ 2 * c ^ 2 ≤ (F * u) ^ 2 := by
  have h1 : f0 ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hf0 hF 2
  have h2 : c ^ 2 ≤ u ^ 2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ hc hu 2
  rw [mul_pow]
  exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)

/-- A row bounded above: `(F u)² ≤ f₁² c²` from `0 ≤ F ≤ f₁`, `|u| ≤ c`. -/
theorem row_le {F f1 c u : ℝ} (hF0 : 0 ≤ F) (hF : F ≤ f1) (hu : |u| ≤ c) :
    (F * u) ^ 2 ≤ f1 ^ 2 * c ^ 2 := by
  have h1 : F ^ 2 ≤ f1 ^ 2 := pow_le_pow_left₀ hF0 hF 2
  have h2 : u ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg u) hu 2
  rw [mul_pow]
  exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)

/-- The third row of a lift with `|w₂| ≥ 1`. -/
theorem third_ge {H R S r1 s1 t : ℝ} (hH : 0 ≤ H) (hR : 0 < R) (hS : 0 < S) (hR1 : R ≤ r1)
    (hS1 : S ≤ s1) (hT : H * (r1 * s1) ^ 2 ≤ 1) (ht : 1 ≤ |t|) : H ≤ (t * (R * S)⁻¹) ^ 2 := by
  have hRS : 0 < R * S := mul_pos hR hS
  have h1 : (R * S) ^ 2 ≤ (r1 * s1) ^ 2 :=
    pow_le_pow_left₀ hRS.le (mul_le_mul hR1 hS1 hS.le (hR.le.trans hR1)) 2
  have ht2 : 1 ≤ t ^ 2 := (one_le_sq_iff_one_le_abs t).mpr ht
  rw [mul_pow, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hH]

/-- **The gap on a box.** Every lift of the class `(−1/2, −1/2, −1/2)` (`m ≠ 0`, or
`m + (−1/2, −1/2, −1/2)`) has `|B w|² ≤ (1 − g)²` or `|B w|² ≥ (1 + g)²` at every point of the
box. -/
theorem gapOk_lift {g : ℚ} {b : Cell} (h : gapOk g b = true) {p : Chart} (hp : b.Mem p) (w : Vec)
    (hw : (∃ m : IntVec, m ≠ 0 ∧ w = castVec m) ∨ ∃ m : IntVec, w = castVec m + halfV) :
    sq ((chartBasis p).mulVec w) ≤ (1 - (g : ℝ)) ^ 2 ∨
      (1 + (g : ℝ)) ^ 2 ≤ sq ((chartBasis p).mulVec w) := by
  obtain ⟨xM, hxM⟩ : ∃ t, t = absMax (b.lo 2) (b.hi 2) := ⟨_, rfl⟩
  obtain ⟨yM, hyM⟩ : ∃ t, t = absMax (b.lo 3) (b.hi 3) := ⟨_, rfl⟩
  obtain ⟨zM, hzM⟩ : ∃ t, t = absMax (b.lo 4) (b.hi 4) := ⟨_, rfl⟩
  simp only [gapOk, decide_eq_true_eq, ← hxM, ← hyM, ← hzM] at h
  obtain ⟨hr0, hs0, hg0, -, -, hT3, hI2, hI0, hIa, hIb, hx1, hI1, hz3, hO1, hxy3, hO0, hC⟩ := h
  have r0p : (0 : ℝ) < b.lo 0 := by exact_mod_cast hr0
  have s0p : (0 : ℝ) < b.lo 1 := by exact_mod_cast hs0
  have g0 : (0 : ℝ) ≤ g := by exact_mod_cast hg0
  have H0 : (0 : ℝ) ≤ (1 + (g : ℝ)) ^ 2 := sq_nonneg _
  have T3 : (1 + (g : ℝ)) ^ 2 * ((b.hi 0 : ℝ) * (b.hi 1 : ℝ)) ^ 2 ≤ 1 := by exact_mod_cast hT3
  have I2 : (1 + (g : ℝ)) ^ 2 ≤ 4 * (b.lo 1 : ℝ) ^ 2 := by exact_mod_cast hI2
  have I0 : (1 + (g : ℝ)) ^ 2 ≤ 4 * (b.lo 0 : ℝ) ^ 2 := by exact_mod_cast hI0
  have Ia : (b.hi 0 : ℝ) ^ 2 ≤ (1 - (g : ℝ)) ^ 2 := by exact_mod_cast hIa
  have Ib : (b.hi 0 : ℝ) ^ 2 * (xM : ℝ) ^ 2 + (b.hi 1 : ℝ) ^ 2 ≤ (1 - (g : ℝ)) ^ 2 := by
    exact_mod_cast hIb
  have x1 : (xM : ℝ) ≤ 1 := by exact_mod_cast hx1
  have I1 : (1 + (g : ℝ)) ^ 2 ≤ (b.lo 0 : ℝ) ^ 2 * (1 - (xM : ℝ)) ^ 2 + (b.lo 1 : ℝ) ^ 2 := by
    exact_mod_cast hI1
  have z3 : (zM : ℝ) ≤ 3 := by exact_mod_cast hz3
  have O1 := (Rat.cast_le (K := ℝ)).mpr hO1
  push_cast at O1
  have xy3 : (xM : ℝ) + yM ≤ 3 := by exact_mod_cast hxy3
  have O0 := (Rat.cast_le (K := ℝ)).mpr hO0
  push_cast at O0
  have C0 := (Rat.cast_le (K := ℝ)).mpr hC
  push_cast at C0
  -- the point
  obtain ⟨hR0, hR1⟩ := hp 0
  obtain ⟨hS0, hS1⟩ := hp 1
  have hX : |p 2| ≤ (xM : ℝ) := by rw [hxM]; exact abs_le_absMax (hp 2).1 (hp 2).2
  have hY : |p 3| ≤ (yM : ℝ) := by rw [hyM]; exact abs_le_absMax (hp 3).1 (hp 3).2
  have hZ : |p 4| ≤ (zM : ℝ) := by rw [hzM]; exact abs_le_absMax (hp 4).1 (hp 4).2
  have R0 : 0 < p 0 := r0p.trans_le hR0
  have S0 : 0 < p 1 := s0p.trans_le hS0
  have xM0 : (0 : ℝ) ≤ xM := (abs_nonneg _).trans hX
  have yM0 : (0 : ℝ) ≤ yM := (abs_nonneg _).trans hY
  have zM0 : (0 : ℝ) ≤ zM := (abs_nonneg _).trans hZ
  rw [sq_chartBasis]
  rcases hw with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩
  · -- the lattice lifts `m ≠ 0`
    simp only [castVec]
    have c0 := int_cases (m 0)
    have c1 := int_cases (m 1)
    have c2 := int_cases (m 2)
    set u0 : ℝ := (m 0 : ℝ) + p 2 * (m 1 : ℝ) + p 3 * (m 2 : ℝ) with hu0
    set u1 : ℝ := (m 1 : ℝ) + p 4 * (m 2 : ℝ) with hu1
    have nA := sq_nonneg (p 0 * u0)
    have nB := sq_nonneg (p 1 * u1)
    have nC := sq_nonneg ((m 2 : ℝ) * (p 0 * p 1)⁻¹)
    rcases c2 with c2 | c2 | c2
    · have e1 : u1 = (m 1 : ℝ) := by rw [hu1, c2]; ring
      have eC : ((m 2 : ℝ) * (p 0 * p 1)⁻¹) ^ 2 = 0 := by rw [c2]; ring
      rcases c1 with c1 | c1 | c1
      · have e0 : u0 = (m 0 : ℝ) := by rw [hu0, c1, c2]; ring
        have eB : (p 1 * u1) ^ 2 = 0 := by rw [e1, c1]; ring
        rcases c0 with c0 | c0 | c0
        · exfalso
          apply hm
          have z0 : m 0 = 0 := by exact_mod_cast c0
          have z1 : m 1 = 0 := by exact_mod_cast c1
          have z2 : m 2 = 0 := by exact_mod_cast c2
          funext i
          fin_cases i <;> simp [z0, z1, z2]
        · left
          have hA := row_le R0.le hR1 (show |u0| ≤ 1 by rw [e0]; exact c0.le)
          rw [one_pow, mul_one] at hA
          linarith
        · right
          have hA := row_ge r0p.le hR0 (by norm_num) (show (2 : ℝ) ≤ |u0| by rw [e0]; exact c0)
          rw [show (2 : ℝ) ^ 2 = 4 by norm_num] at hA
          linarith
      · have hBlo := row_ge s0p.le hS0 zero_le_one (show (1 : ℝ) ≤ |u1| by rw [e1]; exact c1.ge)
        have hBhi := row_le S0.le hS1 (show |u1| ≤ 1 by rw [e1]; exact c1.le)
        rw [one_pow, mul_one] at hBlo hBhi
        rcases c0 with c0 | c0 | c0
        · left
          have hu : |u0| ≤ (xM : ℝ) := by
            rw [hu0, c0, c2, zero_add, mul_zero, add_zero, abs_mul, c1, mul_one]
            exact hX
          have hA := row_le R0.le hR1 hu
          linarith
        · right
          have hu : 1 - (xM : ℝ) ≤ |u0| := by
            have h3 := abs_add3_ge (m 0 : ℝ) (p 2 * (m 1 : ℝ)) (p 3 * (m 2 : ℝ))
            rw [← hu0, abs_mul, abs_mul, c1, c0, c2, abs_zero, mul_zero] at h3
            linarith
          have hA := row_ge r0p.le hR0 (by linarith) hu
          linarith
        · right
          have hu : 1 - (xM : ℝ) ≤ |u0| := by
            have h3 := abs_add3_ge (m 0 : ℝ) (p 2 * (m 1 : ℝ)) (p 3 * (m 2 : ℝ))
            rw [← hu0, abs_mul, abs_mul, c1, c2, abs_zero, mul_zero] at h3
            linarith
          have hA := row_ge r0p.le hR0 (by linarith) hu
          linarith
      · right
        have hB := row_ge s0p.le hS0 (by norm_num) (show (2 : ℝ) ≤ |u1| by rw [e1]; exact c1)
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num] at hB
        linarith
    · right
      have hC := third_ge H0 R0 S0 hR1 hS1 T3 c2.ge
      linarith
    · right
      have hC := third_ge H0 R0 S0 hR1 hS1 T3 (by linarith)
      linarith
  · -- the half lifts `m + (−1/2, −1/2, −1/2)`
    simp only [castVec, halfV, Pi.add_apply]
    have c0 := half_cases (m 0)
    have c1 := half_cases (m 1)
    have c2 := half_cases (m 2)
    set a0 : ℝ := (m 0 : ℝ) + -1 / 2 with ha0
    set a1 : ℝ := (m 1 : ℝ) + -1 / 2 with ha1
    set a2 : ℝ := (m 2 : ℝ) + -1 / 2 with ha2
    have nA := sq_nonneg (p 0 * (a0 + p 2 * a1 + p 3 * a2))
    have nB := sq_nonneg (p 1 * (a1 + p 4 * a2))
    have nC := sq_nonneg (a2 * (p 0 * p 1)⁻¹)
    rcases c2 with c2 | c2
    · rcases c1 with c1 | c1
      · rcases c0 with c0 | c0
        · -- the eight corners
          left
          have hu0 : |a0 + p 2 * a1 + p 3 * a2| ≤ 1 / 2 + ((xM : ℝ) + yM) / 2 := by
            have h3 := abs_add_three a0 (p 2 * a1) (p 3 * a2)
            rw [abs_mul, abs_mul, c0, c1, c2] at h3
            linarith
          have hu1 : |a1 + p 4 * a2| ≤ 1 / 2 + (zM : ℝ) / 2 := by
            have h3 := abs_add_le a1 (p 4 * a2)
            rw [abs_mul, c1, c2] at h3
            linarith
          have hA := row_le R0.le hR1 hu0
          have hB := row_le S0.le hS1 hu1
          have hw2 : a2 ^ 2 = 1 / 4 := by
            rw [← sq_abs, c2]
            norm_num
          have hC : (a2 * (p 0 * p 1)⁻¹) ^ 2 ≤ 1 / (4 * ((b.lo 0 : ℝ) * (b.lo 1 : ℝ)) ^ 2) := by
            have hRS : (b.lo 0 : ℝ) * b.lo 1 ≤ p 0 * p 1 := mul_le_mul hR0 hS0 s0p.le R0.le
            have hp2 : ((b.lo 0 : ℝ) * b.lo 1) ^ 2 ≤ (p 0 * p 1) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hRS 2
            have e : (a2 * (p 0 * p 1)⁻¹) ^ 2 = 1 / (4 * (p 0 * p 1) ^ 2) := by
              rw [mul_pow, hw2, inv_pow]
              ring
            rw [e]
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
          linarith
        · right
          have hu : 3 / 2 - ((xM : ℝ) + yM) / 2 ≤ |a0 + p 2 * a1 + p 3 * a2| := by
            have h3 := abs_add3_ge a0 (p 2 * a1) (p 3 * a2)
            rw [abs_mul, abs_mul, c1, c2] at h3
            linarith
          have hA := row_ge r0p.le hR0 (by linarith) hu
          linarith
      · right
        have hu : 3 / 2 - (zM : ℝ) / 2 ≤ |a1 + p 4 * a2| := by
          have h3 := abs_add3_ge a1 (p 4 * a2) 0
          rw [abs_mul, c2, abs_zero, add_zero] at h3
          linarith
        have hB := row_ge s0p.le hS0 (by linarith) hu
        linarith
    · right
      have hC := third_ge H0 R0 S0 hR1 hS1 T3 (show (1 : ℝ) ≤ |a2| by linarith)
      linarith

/-- Every neighbor of the anchor of class `(−1/2, −1/2, −1/2)` has the gap, on the whole box. -/
theorem anchor_gap {g : ℚ} {b : Cell} (h : gapOk g b = true) {p : Chart} (hp : b.Mem p) (v : Vec)
    (hv : v ∈ neighbors (anchorOf (chartPoint p) halfV)) :
    sq v ≤ (1 - (g : ℝ)) ^ 2 ∨ (1 + (g : ℝ)) ^ 2 ≤ sq v := by
  obtain ⟨hpts, hv0, -⟩ := hv
  rw [zero_add] at hpts
  rcases hpts with ⟨m, rfl⟩ | ⟨y, ⟨m, rfl⟩, rfl⟩
  · apply gapOk_lift h hp
    left
    refine ⟨m, ?_, rfl⟩
    rintro rfl
    apply hv0
    have e : castVec (0 : IntVec) = 0 := by
      funext i
      simp [castVec]
    show (chartBasis p).mulVec (castVec 0) = 0
    rw [e, Matrix.mulVec_zero]
  · have e : (chartBasis p).mulVec (castVec m) + (chartBasis p).mulVec halfV =
        (chartBasis p).mulVec (castVec m + halfV) := (Matrix.mulVec_add _ _ _).symm
    have h1 := gapOk_lift h hp _ (Or.inr ⟨m, rfl⟩)
    rw [← e] at h1
    exact h1

/-- **The anchor's defect is `1` on a box with `gapOk`.** -/
theorem defect_anchor_gap {g : ℚ} {b : Cell} (h : gapOk g b = true) {p : Chart} (hp : b.Mem p)
    (hv : (chartPoint p).Valid) (half : HalfClass halfV) :
    defect (anchorOf (chartPoint p) halfV) = 1 := by
  have h' := h
  simp only [gapOk, decide_eq_true_eq] at h'
  obtain ⟨-, -, hg0, hg1, hg150, -⟩ := h'
  have g150 := (Rat.cast_le (K := ℝ)).mpr hg150
  push_cast at g150
  exact defect_eq_one_of_gap _ (anchor_valid _ hv _ half) (g : ℝ) (by exact_mod_cast hg0)
    (by exact_mod_cast hg1) g150 (fun v hv' => anchor_gap h hp v hv')

end BccSharp.Coulomb.CompactCover.AdaptiveGap
