import BccSharp.Cover.LayeredScalar
import BccSharp.Cover.OverlayPhysicalIdentity
import BccSharp.Cover.OverlayArea

set_option autoImplicit false

/-! # The optical gain about a half-height anchor, in the planar form

For a seam chart `p` (positive diagonals, height `0 < p 7 < 1`) and lateral
anchor offsets `α₁, α₂` with `2αᵢ ∈ ℤ`, the anchor chart `anchorChart p α₁ α₂`
has the shape of `p`, lateral offsets `α` and height `1/2`. Its point set is a
Bravais lattice (a half translation of the period lattice).

The Overlay planar identity (`chart_energy_planar`) applies to both charts. The
planar regularized term depends only on the shape and cancels; the zero modes
differ by `2πc²δ²` with `δ = p 7 − 1/2`; the layer values differ, wave by wave,
only in the cross-coset part of every axial pair (`Layered.crossPair`), whose
change is `2 e^{−T(n+1/2)} · pairGain` (`Layered.crossPair_sub_anchor`).

`layered_gain` bounds `2 a_c (e(p) − e(anchor))` from below by
* the zero-mode term `2πc²δ²`;
* for every retained wave `m ∈ waves K`, `modeLower`: the second-order part
  of the adjacent axial pair with its explicit remainders, minus an absolute
  bound for the further axial pairs;
* minus `outerTail · (τ²δ² + 8π²|v|²)` for all omitted waves,
where `v = latV p α` is the lateral displacement in the projected
coordinates and every loss is quadratic in `(v, δ)`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar

/-! ### The anchor chart -/

/-- The half-height anchor chart: the shape of `p`, lateral offsets `α`,
height `1/2`. -/
def anchorChart (p : Chart) (α₁ α₂ : ℝ) : Chart := ![p 0, p 1, p 2, p 3, p 4, α₁, α₂, 1 / 2]

section anchor
variable (p : Chart) (α₁ α₂ : ℝ)

theorem anchorChart_0 : anchorChart p α₁ α₂ 0 = p 0 := rfl
theorem anchorChart_1 : anchorChart p α₁ α₂ 1 = p 1 := rfl
theorem anchorChart_7 : anchorChart p α₁ α₂ 7 = 1 / 2 := rfl

theorem anchor_cReal : cReal (anchorChart p α₁ α₂) = cReal p := rfl
theorem anchor_κReal (m : Wave) : κReal (anchorChart p α₁ α₂) m = κReal p m := rfl
theorem anchor_tReal (m : Wave) : tReal (anchorChart p α₁ α₂) m = tReal p m := rfl
theorem anchor_wReal (m : Wave) : wReal (anchorChart p α₁ α₂) m = wReal p m := rfl
theorem anchor_uReal (m : Wave) : uReal (anchorChart p α₁ α₂) m = (m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂ := rfl

theorem anchor_planarRegularized : planarRegularized (anchorChart p α₁ α₂) = planarRegularized p := rfl

theorem zeroMode_sub_anchor :
    zeroMode p - zeroMode (anchorChart p α₁ α₂) = 2 * Real.pi * cReal p ^ 2 * (p 7 - 1 / 2) ^ 2 := by
  unfold zeroMode
  rw [anchor_cReal, anchorChart_7]
  ring

/-- The lateral displacement from the anchor in the projected coordinates
`v = f∥ − α + δ σ`, `σ = (y − x z, z)`, `δ = p 7 − 1/2`. -/
def latV : Fin 2 → ℝ :=
  ![p 5 - α₁ + (p 3 - p 2 * p 4) * (p 7 - 1 / 2), p 6 - α₂ + p 4 * (p 7 - 1 / 2)]

theorem latV_zero : latV p α₁ α₂ 0 = p 5 - α₁ + (p 3 - p 2 * p 4) * (p 7 - 1 / 2) := rfl
theorem latV_one : latV p α₁ α₂ 1 = p 6 - α₂ + p 4 * (p 7 - 1 / 2) := rfl

theorem phase_eq (m : Wave) :
    uReal p m - ((m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂) + wReal p m * (p 7 - 1 / 2) =
      (m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1 := by
  rw [latV_zero, latV_one]
  simp only [uReal, wReal]
  ring

end anchor

/-! ### The energy difference as a sum over waves -/

theorem waveValue_summable (q : Chart) (hr : 0 < q 0) (hs : 0 < q 1) (h₀ : 0 < q 7) (h₁ : q 7 < 1) :
    Summable (waveValue q) := by
  have hB : 0 < max (q 0) (secondColumn q) := lt_max_of_lt_left hr
  have hc : 0 < cReal q := inv_pos.mpr (mul_pos hr hs)
  have hη : 0 < min (q 7) (1 - q 7) := lt_min h₀ (by linarith)
  exact (radialTail_sound (B := max (q 0) (secondColumn q))
    (τ := 2 * Real.pi * cReal q / max (q 0) (secondColumn q)) (η := min (q 7) (1 - q 7)) 0 hr hs
    (le_max_left _ _) (le_max_right _ _) (by positivity) le_rfl hη (min_le_left _ _)
    (by have := min_le_right (q 7) (1 - q 7); linarith)).1

theorem energy_sub_anchor (p : Chart) (α₁ α₂ : ℝ) (hr : 0 < p 0) (hs : 0 < p 1)
    (h₀ : 0 < p 7) (h₁ : p 7 < 1) :
    2 * ac * (energy (chartPoint p) - energy (chartPoint (anchorChart p α₁ α₂))) =
      2 * Real.pi * cReal p ^ 2 * (p 7 - 1 / 2) ^ 2 +
        cReal p * ∑' m : Wave, (waveValue p m - waveValue (anchorChart p α₁ α₂) m) := by
  have ha₀ : 0 < anchorChart p α₁ α₂ 7 := by rw [anchorChart_7]; norm_num
  have ha₁ : anchorChart p α₁ α₂ 7 < 1 := by rw [anchorChart_7]; norm_num
  have E1 := (chart_energy_planar p hr hs h₀ h₁).2
  have E2 := (chart_energy_planar (anchorChart p α₁ α₂) hr hs ha₀ ha₁).2
  have S1 := waveValue_summable p hr hs h₀ h₁
  have S2 := waveValue_summable (anchorChart p α₁ α₂) hr hs ha₀ ha₁
  have Z := zeroMode_sub_anchor p α₁ α₂
  rw [mul_sub, E1, E2, anchor_planarRegularized, S1.tsum_sub S2]
  unfold layerValue
  rw [anchor_cReal]
  linear_combination Z

/-! ### One wave -/

theorem tReal_pos (p : Chart) (hr : 0 < p 0) (hs : 0 < p 1) {m : Wave} (hm : m ≠ 0) :
    0 < tReal p m := by
  have hc : 0 < cReal p := inv_pos.mpr (mul_pos hr hs)
  unfold tReal
  have := waveKappa_pos p hr hs hm
  positivity

/-- The terms of the axial sum of the change of one wave. -/
def waveTerm (P T w a ψ : ℝ) (n : ℕ) : ℝ :=
  2 * Real.exp (-T * ((n : ℝ) + 1 / 2)) * pairGain P (Real.pi * (2 * (n : ℝ) + 1) * w) a ψ

theorem abs_waveTerm_le (P T w a ψ : ℝ) (hP : P = 1 ∨ P = -1) (n : ℕ) :
    |waveTerm P T w a ψ n| ≤
      (2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2))) * (Real.exp (-T)) ^ n := by
  unfold waveTerm
  have e : Real.exp (-T * ((n : ℝ) + 1 / 2)) = Real.exp (-T / 2) * (Real.exp (-T)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (Real.exp_pos _), e]
  have := abs_pairGain_le P (Real.pi * (2 * (n : ℝ) + 1) * w) a ψ hP
  have p1 : 0 ≤ Real.exp (-T / 2) * (Real.exp (-T)) ^ n := by positivity
  calc 2 * (Real.exp (-T / 2) * Real.exp (-T) ^ n) * |pairGain P (Real.pi * (2 * ↑n + 1) * w) a ψ|
      ≤ 2 * (Real.exp (-T / 2) * Real.exp (-T) ^ n) * (Real.exp |a| * (a ^ 2 + ψ ^ 2)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem waveTerm_summable (P T w a ψ : ℝ) (hP : P = 1 ∨ P = -1) (hT : 0 < T) :
    Summable (waveTerm P T w a ψ) := by
  have hr : Real.exp (-T) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (summable_geometric_of_lt_one (Real.exp_pos (-T)).le hr).mul_left
    (2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2)))
  exact hg.of_norm_bounded (fun n => by rw [Real.norm_eq_abs]; exact abs_waveTerm_le P T w a ψ hP n)

theorem waveValue_sub_anchor (p : Chart) (α₁ α₂ : ℝ) (hr : 0 < p 0) (hs : 0 < p 1)
    (h₀ : 0 < p 7) (h₁ : p 7 < 1) {m : Wave} (hm : m ≠ 0) (k : ℤ)
    (hk : 2 * ((m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂) = k) :
    waveValue p m - waveValue (anchorChart p α₁ α₂) m =
      (∑' n : ℕ, waveTerm (parityR k) (tReal p m) (wReal p m) (tReal p m * (p 7 - 1 / 2))
        (2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)) n) / κReal p m := by
  have hT := tReal_pos p hr hs hm
  set T := tReal p m
  set w := wReal p m
  set u := uReal p m
  set u' := (m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂ with hu'
  -- summability of the two axial series
  have hη : (0 : ℝ) ≤ min (p 7) (1 - p 7) := le_min h₀.le (by linarith)
  have sp := (axialTail_sound (t := T) (t₀ := T) w u (p 7) (min (p 7) (1 - p 7)) hT le_rfl hη
    (min_le_left _ _) (by have := min_le_right (p 7) (1 - p 7); linarith)).1
  have sa := (axialTail_sound (t := T) (t₀ := T) w u' (1 / 2) (1 / 2) hT le_rfl (by norm_num)
    le_rfl (by norm_num)).1
  have e1 : waveValue p m = axialSeries T w u (p 7) / κReal p m := rfl
  have e2 : waveValue (anchorChart p α₁ α₂) m = axialSeries T w u' (1 / 2) / κReal p m := by
    unfold waveValue
    rw [anchor_tReal, anchor_wReal, anchor_uReal, anchor_κReal, anchorChart_7]
  rw [e1, e2, ← sub_div]
  congr 1
  unfold axialSeries
  rw [← sp.tsum_sub sa]
  congr 1
  funext n
  rw [axialPair_sub, crossPair_sub_anchor T w u u' (p 7) n k hk]
  unfold waveTerm
  congr 2
  rw [← phase_eq p α₁ α₂ m]

/-! ### Retained waves -/

/-- The second-order lower bound of `pairGain` (`pairGain_lower`). -/
def pairLower (P γ a ψ A Ψ : ℝ) : ℝ :=
  -(P * Real.cos γ) * ψ ^ 2 / 2 - max 0 (-(P * Real.cos γ)) * Ψ ^ 2 * ψ ^ 2 / 24
    - |Real.cos γ| * Real.exp A * a ^ 2 / 2 + P * Real.sin γ * a * ψ
    - |Real.sin γ| * (|a| * |ψ|) * (A ^ 2 * Real.exp A / 2 + Ψ ^ 2 / 6)

/-- The weight `W = (4c/κ) e^{−T/2}` of a wave. -/
def modeW (p : Chart) (m : Wave) : ℝ := 4 * cReal p / κReal p m * Real.exp (-tReal p m / 2)

/-- The factor of the absolute bound for the axial pairs `n ≥ 1`. -/
def axialFactor (T A : ℝ) : ℝ := Real.exp (-T) / (1 - Real.exp (-T)) * Real.exp A

/-- The lower bound of `2c` times the change of a retained wave. -/
def modeLower (p : Chart) (α₁ α₂ : ℝ) (k : ℤ) (A Ψ : ℝ) (m : Wave) : ℝ :=
  let T := tReal p m
  let a := T * (p 7 - 1 / 2)
  let ψ := 2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)
  modeW p m * pairLower (parityR k) (Real.pi * wReal p m) a ψ A Ψ -
    modeW p m * axialFactor T A * (a ^ 2 + ψ ^ 2)

theorem mode_lower (p : Chart) (α₁ α₂ : ℝ) (hr : 0 < p 0) (hs : 0 < p 1)
    (h₀ : 0 < p 7) (h₁ : p 7 < 1) {m : Wave} (hm : m ≠ 0) (k : ℤ)
    (hk : 2 * ((m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂) = k) (A Ψ : ℝ)
    (hA : |tReal p m * (p 7 - 1 / 2)| ≤ A)
    (hΨ : |2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)| ≤ Ψ) :
    modeLower p α₁ α₂ k A Ψ m ≤ 2 * cReal p * (waveValue p m - waveValue (anchorChart p α₁ α₂) m) := by
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
  have lower0 := pairGain_lower P (Real.pi * w) a ψ A Ψ hP hA hΨ
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
  have total : 2 * Real.exp (-T / 2) * pairLower P (Real.pi * w) a ψ A Ψ -
      2 * Real.exp (-T / 2) * (Real.exp A * (a ^ 2 + ψ ^ 2)) * (Real.exp (-T) / (1 - Real.exp (-T))) ≤
      waveTerm P T w a ψ 0 + ∑' n, waveTerm P T w a ψ (n + 1) := by
    rw [first]
    have e2 : 0 ≤ 2 * Real.exp (-T / 2) := by positivity
    have := mul_le_mul_of_nonneg_left lower0 e2
    unfold pairLower
    linarith
  have scale : 0 ≤ 2 * cReal p / κReal p m := by positivity
  have := mul_le_mul_of_nonneg_left total scale
  have eqL : modeLower p α₁ α₂ k A Ψ m = 2 * cReal p / κReal p m *
      (2 * Real.exp (-T / 2) * pairLower P (Real.pi * w) a ψ A Ψ -
        2 * Real.exp (-T / 2) * (Real.exp A * (a ^ 2 + ψ ^ 2)) * (Real.exp (-T) / (1 - Real.exp (-T)))) := by
    unfold modeLower modeW axialFactor
    ring
  rw [eqL]
  calc _ ≤ 2 * cReal p / κReal p m * (waveTerm P T w a ψ 0 + ∑' n, waveTerm P T w a ψ (n + 1)) := this
    _ = _ := by field_simp

/-! ### Omitted waves -/

theorem abs_waveValue_sub_anchor (p : Chart) (α₁ α₂ : ℝ) (hr : 0 < p 0) (hs : 0 < p 1)
    (h₀ : 0 < p 7) (h₁ : p 7 < 1) {m : Wave} (hm : m ≠ 0) (k : ℤ)
    (hk : 2 * ((m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂) = k) :
    |waveValue p m - waveValue (anchorChart p α₁ α₂) m| ≤
      2 / κReal p m * Real.exp (-tReal p m / 2) / (1 - Real.exp (-tReal p m)) *
        (Real.exp |tReal p m * (p 7 - 1 / 2)| * ((tReal p m * (p 7 - 1 / 2)) ^ 2 +
          (2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)) ^ 2)) := by
  have hT := tReal_pos p hr hs hm
  have hκ := waveKappa_pos p hr hs hm
  set T := tReal p m
  set a := T * (p 7 - 1 / 2)
  set ψ := 2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)
  have hP := parityR_cases k
  have r := Real.exp_lt_one_iff.mpr (by linarith : -T < 0)
  have r0 := (Real.exp_pos (-T)).le
  rw [waveValue_sub_anchor p α₁ α₂ hr hs h₀ h₁ hm k hk]
  let G : ℕ → ℝ := fun n => (2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2))) * (Real.exp (-T)) ^ n
  have hG : Summable G := (summable_geometric_of_lt_one r0 r).mul_left _
  obtain ⟨_, babs⟩ := abs_sum_bound hG (abs_waveTerm_le (parityR k) T (wReal p m) a ψ hP)
  have tG : (∑' n, G n) = 2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2)) /
      (1 - Real.exp (-T)) := by
    simp only [G]
    rw [tsum_mul_left, tsum_geometric_of_lt_one r0 r]
    ring
  rw [tG] at babs
  rw [abs_div, abs_of_pos hκ]
  have den : 0 < 1 - Real.exp (-T) := by linarith
  calc _ ≤ 2 * Real.exp (-T / 2) * (Real.exp |a| * (a ^ 2 + ψ ^ 2)) / (1 - Real.exp (-T)) / κReal p m :=
        div_le_div_of_nonneg_right babs hκ.le
    _ = _ := by field_simp

/-- `t² e^{−βt}` decreases on `t ≥ 2/β`. -/
theorem sq_exp_antitone {β s t : ℝ} (hβ : 0 < β) (hs : 2 / β ≤ s) (hst : s ≤ t) :
    t ^ 2 * Real.exp (-β * t) ≤ s ^ 2 * Real.exp (-β * s) := by
  let f : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-β * x)
  have hd (x : ℝ) : HasDerivAt f (x * (2 - β * x) * Real.exp (-β * x)) x := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-β * x)) (Real.exp (-β * x) * (-β * 1)) x :=
      ((hasDerivAt_id' x).const_mul (-β)).exp
    convert h1.mul h2 using 1
    ring
  have hanti : AntitoneOn f (Set.Ici (2 / β)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact (by fun_prop : Continuous f).continuousOn
    · intro x _
      exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have hx' : 2 / β < x := hx
      have x0 : 0 < x := lt_trans (by positivity) hx'
      have : 2 < β * x := by rwa [div_lt_iff₀ hβ, mul_comm] at hx'
      have : x * (2 - β * x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos x0.le (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le
  exact hanti (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr (hs.trans hst)) hst

/-- The constant of the omitted-wave tail: `c · 16 B J² q^J / ((1 − e^{−τ})(1 − ρ))`
with `J = K + 1`, `q = e^{−τ(1/2−η)}` and `ρ = ((J+1)/J)² q`. -/
def outerTail (c B τ η : ℝ) (K : ℕ) : ℝ :=
  let J : ℝ := (K : ℝ) + 1
  let q := Real.exp (-(τ * (1 / 2 - η)))
  c * (16 * B / (1 - Real.exp (-τ)) * (J ^ 2 * q ^ (K + 1) / (1 - ((J + 1) / J) ^ 2 * q)))

/-- The majorant of one omitted wave on the shell `j`. -/
theorem outer_wave_bound (p : Chart) (α₁ α₂ : ℝ) (k₁ k₂ : ℤ) (hk₁ : 2 * α₁ = k₁) (hk₂ : 2 * α₂ = k₂)
    (hr : 0 < p 0) (hs : 0 < p 1) {η : ℝ} (hη : |p 7 - 1 / 2| ≤ η) (hη2 : η < 1 / 2)
    {B τ : ℝ} (hB₁ : p 0 ≤ B) (hB₂ : secondColumn p ≤ B) (hτ : 0 < τ)
    (hτc : τ ≤ 2 * Real.pi * cReal p / B) (j : ℕ) (hj0 : 0 < j)
    (hmono : 2 / (1 / 2 - η) ≤ τ * (j : ℝ)) (m : Wave) (hj : waveRadius m = j) :
    |waveValue p m - waveValue (anchorChart p α₁ α₂) m| ≤
      2 * B / (1 - Real.exp (-τ)) * ((j : ℝ) * Real.exp (-(τ * (1 / 2 - η))) ^ j) *
        (τ ^ 2 * (p 7 - 1 / 2) ^ 2 + 8 * Real.pi ^ 2 * (latV p α₁ α₂ 0 ^ 2 + latV p α₁ α₂ 1 ^ 2)) := by
  have h₀ : 0 < p 7 := by have := abs_le.mp hη; linarith
  have h₁ : p 7 < 1 := by have := abs_le.mp hη; linarith
  have hB := hr.trans_le hB₁
  have jr : (0 : ℝ) < j := by exact_mod_cast hj0
  have hm : m ≠ 0 := by
    intro e
    rw [e] at hj
    simp [waveRadius] at hj
    omega
  have kb := waveRadius_le hr hs m hB₁ hB₂
  rw [hj] at kb
  have hκ := waveKappa_pos p hr hs hm
  have hT := tReal_pos p hr hs hm
  have hc : 0 < cReal p := inv_pos.mpr (mul_pos hr hs)
  have Tj : τ * (j : ℝ) ≤ tReal p m := by
    calc τ * (j : ℝ) ≤ (2 * Real.pi * cReal p / B) * (j : ℝ) := mul_le_mul_of_nonneg_right hτc jr.le
      _ ≤ (2 * Real.pi * cReal p / B) * (κReal p m * B) := mul_le_mul_of_nonneg_left kb (by positivity)
      _ = tReal p m := by unfold tReal; field_simp [hB.ne']
  have hk : 2 * ((m.1 : ℝ) * α₁ + (m.2 : ℝ) * α₂) = ((m.1 * k₁ + m.2 * k₂ : ℤ) : ℝ) := by
    push_cast; rw [← hk₁, ← hk₂]; ring
  have base := abs_waveValue_sub_anchor p α₁ α₂ hr hs h₀ h₁ hm _ hk
  have m1 : (m.1 : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by
    have h : |(m.1 : ℝ)| ≤ (j : ℝ) := by
      rw [← hj]; simp only [waveRadius, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
      exact le_max_left _ _
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have m2 : (m.2 : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by
    have h : |(m.2 : ℝ)| ≤ (j : ℝ) := by
      rw [← hj]; simp only [waveRadius, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
      exact le_max_right _ _
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- name the quantities
  obtain ⟨T, eT⟩ : ∃ T, T = tReal p m := ⟨_, rfl⟩
  obtain ⟨κ, eκ⟩ : ∃ κ, κ = κReal p m := ⟨_, rfl⟩
  obtain ⟨δ, eδ⟩ : ∃ δ, δ = p 7 - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨v₁, e1⟩ : ∃ v, v = latV p α₁ α₂ 0 := ⟨_, rfl⟩
  obtain ⟨v₂, e2⟩ : ∃ v, v = latV p α₁ α₂ 1 := ⟨_, rfl⟩
  obtain ⟨β, eβ⟩ : ∃ β, β = 1 / 2 - η := ⟨_, rfl⟩
  rw [← eT, ← eκ, ← eδ, ← e1, ← e2] at base
  rw [← eδ, ← e1, ← e2]
  rw [← eT] at Tj hT
  rw [← eκ] at kb hκ
  rw [← eβ] at hmono
  have β0 : 0 < β := by rw [eβ]; linarith
  have hηδ : |δ| ≤ η := by rw [eδ]; exact hη
  set ψ := 2 * Real.pi * ((m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂) with hψ
  set V := τ ^ 2 * δ ^ 2 + 8 * Real.pi ^ 2 * (v₁ ^ 2 + v₂ ^ 2) with hV
  have V0 : 0 ≤ V := by positivity
  -- ψ² ≤ 8π² j² |v|²
  have cs : ((m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂) ^ 2 ≤ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2) := by
    have id : ((m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂) ^ 2 =
        ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) * (v₁ ^ 2 + v₂ ^ 2) - ((m.1 : ℝ) * v₂ - (m.2 : ℝ) * v₁) ^ 2 := by
      ring
    rw [id]
    have h1 : ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) * (v₁ ^ 2 + v₂ ^ 2) ≤ (2 * (j : ℝ) ^ 2) * (v₁ ^ 2 + v₂ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [sq_nonneg ((m.1 : ℝ) * v₂ - (m.2 : ℝ) * v₁)]
  have ψb : ψ ^ 2 ≤ 8 * Real.pi ^ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2) := by
    have e : ψ ^ 2 = 4 * Real.pi ^ 2 * ((m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂) ^ 2 := by rw [hψ]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left cs (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
    linarith
  -- the exponential factors
  have ea : Real.exp |T * δ| ≤ Real.exp (T * η) := by
    apply Real.exp_le_exp.mpr
    rw [abs_mul, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left hηδ hT.le
  have eTb : Real.exp (-T / 2) * Real.exp (T * η) = Real.exp (-β * T) := by
    rw [← Real.exp_add]; congr 1; rw [eβ]; ring
  have mono := sq_exp_antitone β0 hmono Tj
  have expj : Real.exp (-β * T) ≤ Real.exp (-β * (τ * (j : ℝ))) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left Tj (by linarith))
  have qj : Real.exp (-β * (τ * (j : ℝ))) = Real.exp (-β * τ) ^ j := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  -- the numerator
  have X_le : Real.exp (-T / 2) * (Real.exp |T * δ| * ((T * δ) ^ 2 + ψ ^ 2)) ≤
      (j : ℝ) ^ 2 * Real.exp (-β * (τ * (j : ℝ))) * V := by
    have s1 : Real.exp |T * δ| * ((T * δ) ^ 2 + ψ ^ 2) ≤
        Real.exp (T * η) * (T ^ 2 * δ ^ 2 + 8 * Real.pi ^ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2)) := by
      have : (T * δ) ^ 2 = T ^ 2 * δ ^ 2 := by ring
      rw [this]
      exact mul_le_mul ea (by linarith) (by positivity) (Real.exp_pos _).le
    have s2 : Real.exp (-T / 2) * (Real.exp |T * δ| * ((T * δ) ^ 2 + ψ ^ 2)) ≤
        (T ^ 2 * Real.exp (-β * T)) * δ ^ 2 +
          Real.exp (-β * T) * (8 * Real.pi ^ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left s1 (Real.exp_pos (-T / 2)).le
      calc _ ≤ Real.exp (-T / 2) * (Real.exp (T * η) *
            (T ^ 2 * δ ^ 2 + 8 * Real.pi ^ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2))) := h
        _ = (Real.exp (-T / 2) * Real.exp (T * η)) *
            (T ^ 2 * δ ^ 2 + 8 * Real.pi ^ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2)) := by ring
        _ = _ := by rw [eTb]; ring
    have b1 := mul_le_mul_of_nonneg_right mono (sq_nonneg δ)
    have b2 := mul_le_mul_of_nonneg_right expj
      (by positivity : (0 : ℝ) ≤ 8 * Real.pi ^ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2))
    have s4 : (τ * (j : ℝ)) ^ 2 * Real.exp (-β * (τ * (j : ℝ))) * δ ^ 2 +
        Real.exp (-β * (τ * (j : ℝ))) * (8 * Real.pi ^ 2 * (j : ℝ) ^ 2 * (v₁ ^ 2 + v₂ ^ 2)) =
        (j : ℝ) ^ 2 * Real.exp (-β * (τ * (j : ℝ))) * V := by rw [hV]; ring
    linarith
  -- the prefactor
  have dT : 0 < 1 - Real.exp (-T) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -T < 0); linarith
  have dτ : 0 < 1 - Real.exp (-τ) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -τ < 0); linarith
  have τT : τ ≤ T := by
    have : τ * 1 ≤ τ * (j : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hj0) hτ.le
    linarith
  have coef : 2 / κ / (1 - Real.exp (-T)) ≤ 2 * B / (j : ℝ) / (1 - Real.exp (-τ)) := by
    have inv : 2 / κ ≤ 2 * B / (j : ℝ) := by
      rw [div_le_div_iff₀ hκ jr]; linarith [kb]
    have den : 1 - Real.exp (-τ) ≤ 1 - Real.exp (-T) := by
      linarith [Real.exp_le_exp.mpr (by linarith : -T ≤ -τ)]
    calc 2 / κ / (1 - Real.exp (-T)) ≤ 2 * B / (j : ℝ) / (1 - Real.exp (-T)) :=
          div_le_div_of_nonneg_right inv dT.le
      _ ≤ 2 * B / (j : ℝ) / (1 - Real.exp (-τ)) :=
          div_le_div_of_nonneg_left (by positivity) dτ den
  calc |waveValue p m - waveValue (anchorChart p α₁ α₂) m|
      ≤ 2 / κ * Real.exp (-T / 2) / (1 - Real.exp (-T)) *
          (Real.exp |T * δ| * ((T * δ) ^ 2 + ψ ^ 2)) := base
    _ = 2 / κ / (1 - Real.exp (-T)) * (Real.exp (-T / 2) * (Real.exp |T * δ| * ((T * δ) ^ 2 + ψ ^ 2))) := by
        ring
    _ ≤ 2 * B / (j : ℝ) / (1 - Real.exp (-τ)) * ((j : ℝ) ^ 2 * Real.exp (-β * (τ * (j : ℝ))) * V) :=
        mul_le_mul coef X_le (by positivity) (by positivity)
    _ = 2 * B / (1 - Real.exp (-τ)) * ((j : ℝ) * Real.exp (-(τ * β)) ^ j) * V := by
        rw [qj, show -(τ * β) = -β * τ by ring]
        field_simp
    _ = _ := by rw [eβ]

/-- The geometric majorant of `∑_{j ≥ J} j² qʲ`. -/
theorem sq_geom_le {q : ℝ} (q0 : 0 ≤ q) (J : ℕ) (hJ : 0 < J) (n : ℕ) :
    ((J + n : ℕ) : ℝ) ^ 2 * q ^ (J + n) ≤ ((J : ℝ) ^ 2 * q ^ J) * ((((J : ℝ) + 1) / J) ^ 2 * q) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have Jr : (0 : ℝ) < J := by exact_mod_cast hJ
    have jn : (0 : ℝ) < ((J + n : ℕ) : ℝ) := by
      have : 0 < J + n := by omega
      exact_mod_cast this
    have ratio : ((((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ)) ^ 2 ≤ (((J : ℝ) + 1) / J) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_div_iff₀ jn Jr]
      push_cast
      nlinarith
    have step : ((J + (n + 1) : ℕ) : ℝ) ^ 2 * q ^ (J + (n + 1)) =
        (((J + n : ℕ) : ℝ) ^ 2 * q ^ (J + n)) * (((((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ)) ^ 2 * q) := by
      have e : ((J + (n + 1) : ℕ) : ℝ) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
      have e2 : q ^ (J + (n + 1)) = q ^ (J + n) * q := by rw [← add_assoc, pow_succ]
      rw [e, e2]
      field_simp
    rw [step, pow_succ]
    have h0 : 0 ≤ ((J + n : ℕ) : ℝ) ^ 2 * q ^ (J + n) := by positivity
    have hr0 : 0 ≤ (((((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ)) ^ 2 * q) := by positivity
    calc (((J + n : ℕ) : ℝ) ^ 2 * q ^ (J + n)) * (((((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ)) ^ 2 * q)
        ≤ ((J : ℝ) ^ 2 * q ^ J * ((((J : ℝ) + 1) / J) ^ 2 * q) ^ n) *
            (((((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ)) ^ 2 * q) := mul_le_mul_of_nonneg_right ih hr0
      _ ≤ ((J : ℝ) ^ 2 * q ^ J * ((((J : ℝ) + 1) / J) ^ 2 * q) ^ n) * ((((J : ℝ) + 1) / J) ^ 2 * q) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ratio q0) (by positivity)
      _ = _ := by ring

theorem outer_tail (p : Chart) (α₁ α₂ : ℝ) (k₁ k₂ : ℤ) (hk₁ : 2 * α₁ = k₁) (hk₂ : 2 * α₂ = k₂)
    (hr : 0 < p 0) (hs : 0 < p 1) {η : ℝ} (hη : |p 7 - 1 / 2| ≤ η) (hη2 : η < 1 / 2)
    (K : ℕ) {B τ : ℝ} (hB₁ : p 0 ≤ B) (hB₂ : secondColumn p ≤ B) (hτ : 0 < τ)
    (hτc : τ ≤ 2 * Real.pi * cReal p / B) (hmono : 2 / (1 / 2 - η) ≤ τ * ((K : ℝ) + 1))
    (hρ : (((K : ℝ) + 2) / ((K : ℝ) + 1)) ^ 2 * Real.exp (-(τ * (1 / 2 - η))) < 1) :
    -(outerTail (cReal p) B τ η K * (τ ^ 2 * (p 7 - 1 / 2) ^ 2 +
        8 * Real.pi ^ 2 * (latV p α₁ α₂ 0 ^ 2 + latV p α₁ α₂ 1 ^ 2))) ≤
      cReal p * ∑' m : {m // m ∉ waveCube K},
        (waveValue p m.val - waveValue (anchorChart p α₁ α₂) m.val) := by
  have hc : 0 < cReal p := inv_pos.mpr (mul_pos hr hs)
  have hB := hr.trans_le hB₁
  obtain ⟨V, hV⟩ : ∃ V, V = τ ^ 2 * (p 7 - 1 / 2) ^ 2 +
      8 * Real.pi ^ 2 * (latV p α₁ α₂ 0 ^ 2 + latV p α₁ α₂ 1 ^ 2) := ⟨_, rfl⟩
  rw [← hV]
  have V0 : 0 ≤ V := by rw [hV]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = Real.exp (-(τ * (1 / 2 - η))) := ⟨_, rfl⟩
  have q0 : 0 ≤ q := by rw [hq]; exact (Real.exp_pos _).le
  have dτ : 0 < 1 - Real.exp (-τ) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -τ < 0); linarith
  let D : Wave → ℝ := fun m => waveValue p m - waveValue (anchorChart p α₁ α₂) m
  let I := Σ n : ℕ, ↥(waveShell (K + 1 + n))
  let g : I → ℝ := fun x =>
    2 * B / (1 - Real.exp (-τ)) * (((K + 1 + x.1 : ℕ) : ℝ) * q ^ (K + 1 + x.1)) * V
  have major (x : I) : |D x.2.val| ≤ g x := by
    obtain ⟨n, m, hmem⟩ := x
    have hj : 0 < K + 1 + n := by omega
    have hwr : waveRadius m = K + 1 + n := (mem_waveShell m hj).mp hmem
    have jge : (K : ℝ) + 1 ≤ ((K + 1 + n : ℕ) : ℝ) := by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hm' : 2 / (1 / 2 - η) ≤ τ * ((K + 1 + n : ℕ) : ℝ) :=
      hmono.trans (mul_le_mul_of_nonneg_left jge hτ.le)
    have := outer_wave_bound p α₁ α₂ k₁ k₂ hk₁ hk₂ hr hs hη hη2 hB₁ hB₂ hτ hτc (K + 1 + n) hj hm' m hwr
    simp only [D, g]
    rw [hq, hV]
    exact this
  -- the shells
  have shellSum (n : ℕ) : (∑' y : ↥(waveShell (K + 1 + n)), g ⟨n, y⟩) =
      16 * B / (1 - Real.exp (-τ)) * V * (((K + 1 + n : ℕ) : ℝ) ^ 2 * q ^ (K + 1 + n)) := by
    have hj : 0 < K + 1 + n := by omega
    simp only [g, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      card_waveShell hj]
    push_cast
    ring
  have Jpos : 0 < K + 1 := by omega
  have hJr : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  set ρ := ((((K + 1 : ℕ) : ℝ) + 1) / ((K + 1 : ℕ) : ℝ)) ^ 2 * q with hρdef
  have hρ' : ρ < 1 := by
    rw [hρdef, hJr, hq]
    convert hρ using 3
    ring
  have ρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hgeo : Summable (fun n : ℕ => ((((K + 1 : ℕ) : ℝ)) ^ 2 * q ^ (K + 1)) * ρ ^ n) :=
    (summable_geometric_of_lt_one ρ0 hρ').mul_left _
  have hshell : Summable (fun n : ℕ => ((K + 1 + n : ℕ) : ℝ) ^ 2 * q ^ (K + 1 + n)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) (sq_geom_le q0 (K + 1) Jpos) hgeo
  have hg : Summable g := (summable_sigma_of_nonneg (fun x => by simp only [g]; positivity)).mpr
    ⟨fun _ => Summable.of_finite, by simpa only [shellSum] using hshell.mul_left _⟩
  obtain ⟨_, ab⟩ := abs_sum_bound hg major
  have ident := (waveTailEquiv K).symm.tsum_eq (fun m : {m // m ∉ waveCube K} => D m.val)
  have total : (∑' x, g x) ≤ 16 * B / (1 - Real.exp (-τ)) * V *
      ((((K + 1 : ℕ) : ℝ)) ^ 2 * q ^ (K + 1) / (1 - ρ)) := by
    rw [hg.tsum_sigma]
    simp only [shellSum]
    rw [tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∑' n : ℕ, ((K + 1 + n : ℕ) : ℝ) ^ 2 * q ^ (K + 1 + n))
        ≤ ∑' n : ℕ, ((((K + 1 : ℕ) : ℝ)) ^ 2 * q ^ (K + 1)) * ρ ^ n :=
          hshell.tsum_le_tsum (sq_geom_le q0 (K + 1) Jpos) hgeo
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one ρ0 hρ', div_eq_mul_inv]
  have absD : |∑' m : {m // m ∉ waveCube K}, D m.val| ≤ 16 * B / (1 - Real.exp (-τ)) * V *
      ((((K + 1 : ℕ) : ℝ)) ^ 2 * q ^ (K + 1) / (1 - ρ)) := by
    have e : (∑' m : {m // m ∉ waveCube K}, D m.val) = ∑' x : I, D x.2.val := by
      rw [← ident]; rfl
    rw [e]
    exact ab.trans total
  have eqT : outerTail (cReal p) B τ η K * V =
      cReal p * (16 * B / (1 - Real.exp (-τ)) * V *
        ((((K + 1 : ℕ) : ℝ)) ^ 2 * q ^ (K + 1) / (1 - ρ))) := by
    unfold outerTail
    rw [hρdef, hJr, hq]
    ring
  rw [eqT]
  have h1 := mul_le_mul_of_nonneg_left absD hc.le
  have h2 := neg_abs_le (∑' m : {m // m ∉ waveCube K}, D m.val)
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  change -(cReal p * _) ≤ cReal p * ∑' m : {m // m ∉ waveCube K}, D m.val
  linarith

/-! ### The gain -/

theorem layered_gain (p : Chart) (α₁ α₂ : ℝ) (k₁ k₂ : ℤ) (hk₁ : 2 * α₁ = k₁) (hk₂ : 2 * α₂ = k₂)
    (hr : 0 < p 0) (hs : 0 < p 1) {η : ℝ} (hη : |p 7 - 1 / 2| ≤ η) (hη2 : η < 1 / 2)
    (K : ℕ) {B τ : ℝ} (hB₁ : p 0 ≤ B) (hB₂ : secondColumn p ≤ B) (hτ : 0 < τ)
    (hτc : τ ≤ 2 * Real.pi * cReal p / B) (hmono : 2 / (1 / 2 - η) ≤ τ * ((K : ℝ) + 1))
    (hρ : (((K : ℝ) + 2) / ((K : ℝ) + 1)) ^ 2 * Real.exp (-(τ * (1 / 2 - η))) < 1)
    (A Ψ : Wave → ℝ) (hA : ∀ m ∈ waves K, |tReal p m * (p 7 - 1 / 2)| ≤ A m)
    (hΨ : ∀ m ∈ waves K,
      |2 * Real.pi * ((m.1 : ℝ) * latV p α₁ α₂ 0 + (m.2 : ℝ) * latV p α₁ α₂ 1)| ≤ Ψ m) :
    2 * Real.pi * cReal p ^ 2 * (p 7 - 1 / 2) ^ 2 +
        (∑ m ∈ waves K, modeLower p α₁ α₂ (m.1 * k₁ + m.2 * k₂) (A m) (Ψ m) m) -
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
  have retained : (∑ m ∈ waves K, modeLower p α₁ α₂ (m.1 * k₁ + m.2 * k₂) (A m) (Ψ m) m) ≤
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
    exact mode_lower p α₁ α₂ hr hs h₀ h₁ hm0 _ hk (A m) (Ψ m) (hA m hm) (hΨ m hm)
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
