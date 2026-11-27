import BccSharp.Cover.LayeredFix
import BccSharp.Cover.OverlayFixSound

set_option autoImplicit false

/-! # Soundness of the layered gain evaluator

For a seam cell `b`, an anchor `an` and a rational `λ`, `leafOk b an λ = true`
implies, at every point `p` of `b`,

  `λ · |R d|² ≤ 2 a_c (e(p) − e(anchor))`,

where the anchor chart is `anchorChart p (k₁/2) (k₂/2)` and
`|R d|² = r²(v₁ + x v₂)² + s² v₂² + c² δ²` (`layerGram`), with `v = latV p α`
and `δ = p 7 − 1/2` (`leafOk_gain`). `splitOk_gain` extends it to the
bisected cells.

The proof:
* fixed-point enclosures of every per-wave coefficient (`lamF_mem'`, …);
* `modeLower_ge`: `Layered.modeLower` is at least the quadratic form
  `λₘ (m·v)² + μₘ δ² + χₘ δ (m·v) − εₘ (|m₁||δ v₁| + |m₂||δ v₂|)`;
* with `Layered.layered_gain`, `2 a_c Δe ≥ quad6 M* z` for a symmetric `M*`
  inside the evaluator's six intervals; its mixed entries choose the sign of
  `|δ vᵢ|`;
* `pdOk_sound`: positive interval `LDLᵀ` pivots make every symmetric matrix
  in the intervals positive semidefinite. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix

/-! ### Interval helpers -/

theorem halfF_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (halfF a).Mem (x / 2) := half_mem hx

theorem negF_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (negF a).Mem (-x) := by
  unfold negF FI.Mem at *
  simp only [Int.cast_neg, neg_div]
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem ptF_mem (z : ℤ) : (ptF z).Mem ((z : ℝ) / Sz) := ⟨le_rfl, le_rfl⟩

theorem ptF_one : (ptF Sz).Mem 1 := by
  have := ptF_mem Sz
  rwa [div_self (ne_of_gt Sz_pos)] at this

theorem divNatF_mem {a : FI} {x : ℝ} (hx : a.Mem x) (n : ℕ) (hn : 0 < n) :
    (divNatF a n).Mem (x / n) := by
  have sp := Sz_pos
  have nz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have nr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold divNatF FI.Mem at *
  constructor
  · have h := fdiv_le a.lo (n : ℤ) nz
    push_cast at h
    calc ((a.lo / (n : ℤ) : ℤ) : ℝ) / Sz ≤ ((a.lo : ℝ) / (n : ℝ)) / Sz :=
          div_le_div_of_nonneg_right h sp.le
      _ = ((a.lo : ℝ) / Sz) / n := by ring
      _ ≤ x / n := div_le_div_of_nonneg_right hx.1 nr.le
  · have h := le_cdiv a.hi (n : ℤ) nz
    push_cast at h
    calc x / n ≤ ((a.hi : ℝ) / Sz) / n := div_le_div_of_nonneg_right hx.2 nr.le
      _ = ((a.hi : ℝ) / (n : ℝ)) / Sz := by ring
      _ ≤ (cdivZ a.hi (n : ℤ) : ℝ) / Sz := div_le_div_of_nonneg_right h sp.le

theorem absF_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (absF a).Mem |x| := by
  have sp := Sz_pos
  unfold absF
  split_ifs with h1 h2
  · have : (0 : ℝ) ≤ x := le_trans (div_nonneg (by exact_mod_cast h1) sp.le) hx.1
    rwa [abs_of_nonneg this]
  · have : x ≤ 0 := le_trans hx.2 (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h2) sp.le)
    rw [abs_of_nonpos this]
    exact negF_mem hx
  · unfold FI.Mem at *
    simp only [Int.cast_zero, zero_div]
    refine ⟨abs_nonneg x, ?_⟩
    have hm1 : ((-a.lo : ℤ) : ℝ) ≤ ((max (-a.lo) a.hi : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hm2 : ((a.hi : ℤ) : ℝ) ≤ ((max (-a.lo) a.hi : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
      exact hx.2.trans (div_le_div_of_nonneg_right hm2 sp.le)
    · rw [abs_of_nonpos h]
      have e : -x ≤ ((-a.lo : ℤ) : ℝ) / Sz := by push_cast; rw [neg_div]; linarith [hx.1]
      exact e.trans (div_le_div_of_nonneg_right hm1 sp.le)

theorem negPartF_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (negPartF a).Mem (max 0 (-x)) := by
  have sp := Sz_pos
  unfold negPartF FI.Mem at *
  have c1 : ((max 0 (-a.hi) : ℤ) : ℝ) / Sz = max 0 (-((a.hi : ℝ) / Sz)) := by
    push_cast; rw [← max_div_div_right sp.le, zero_div, neg_div]
  have c2 : ((max 0 (-a.lo) : ℤ) : ℝ) / Sz = max 0 (-((a.lo : ℝ) / Sz)) := by
    push_cast; rw [← max_div_div_right sp.le, zero_div, neg_div]
  rw [c1, c2]
  exact ⟨max_le_max le_rfl (neg_le_neg hx.2), max_le_max le_rfl (neg_le_neg hx.1)⟩

theorem symF_mem {a : FI} {x y : ℝ} (hx : a.Mem x) (hy : |y| ≤ x) : (symF a).Mem y := by
  unfold symF FI.Mem at *
  push_cast
  rw [neg_div]
  constructor <;> linarith [neg_abs_le y, le_abs_self y, hx.2]

theorem magZ_bound {a : FI} {x : ℝ} (hx : a.Mem x) : |x| ≤ (magZ a : ℝ) / Sz := by
  have sp := Sz_pos
  unfold magZ
  have l : (|a.lo| : ℝ) ≤ ((max |a.lo| |a.hi| : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
  have u : (|a.hi| : ℝ) ≤ ((max |a.lo| |a.hi| : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
  rw [abs_le]
  constructor
  · have : -((max |a.lo| |a.hi| : ℤ) : ℝ) ≤ (a.lo : ℝ) := by
      have := neg_abs_le (a.lo : ℝ); push_cast at l ⊢; linarith
    calc -(((max |a.lo| |a.hi| : ℤ) : ℝ) / Sz) = (-((max |a.lo| |a.hi| : ℤ) : ℝ)) / Sz := by ring
      _ ≤ (a.lo : ℝ) / Sz := div_le_div_of_nonneg_right this sp.le
      _ ≤ x := hx.1
  · have : (a.hi : ℝ) ≤ ((max |a.lo| |a.hi| : ℤ) : ℝ) := by
      have := le_abs_self (a.hi : ℝ); push_cast at u ⊢; linarith
    exact hx.2.trans (div_le_div_of_nonneg_right this sp.le)

theorem magZ_nonneg (a : FI) : 0 ≤ magZ a := le_max_of_le_left (abs_nonneg _)

theorem cosPiF_mem {w : FI} {x : ℝ} (hx : w.Mem x) : (cosPiF w).Mem (Real.cos (Real.pi * x)) := by
  have h := cosRange_mem (halfF_mem hx)
  have e : 2 * Real.pi * (x / 2) = Real.pi * x := by ring
  rw [e] at h
  exact h

theorem sinPiF_mem {w : FI} {x : ℝ} (hx : w.Mem x) : (sinPiF w).Mem (Real.sin (Real.pi * x)) := by
  have hs := shift_mem (halfF_mem hx) (Sz / 4)
  have h := cosRange_mem hs
  rw [quarter_eq] at h
  have e : 2 * Real.pi * (x / 2 - 1 / 4) = Real.pi * x - Real.pi / 2 := by ring
  rw [e, Real.cos_sub_pi_div_two] at h
  exact h

theorem expPosF_mem {a : ℤ} (ha : 0 ≤ a) (hlo : 0 < (expNegPt a.toNat).lo) :
    (expPosF a).Mem (Real.exp ((a : ℝ) / Sz)) := by
  have h := FI.invPos_mem hlo (expNegPt_mem a.toNat)
  have e : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
  rw [e, Real.exp_neg, inv_inv] at h
  exact h

theorem parityZ_cast (k : ℤ) : ((parityZ k : ℤ) : ℝ) = Layered.parityR k := by
  unfold parityZ Layered.parityR
  split_ifs <;> simp

theorem sumW_mem (l : List Wave) (F : Wave → FI) (v : Wave → ℝ) (h : ∀ m ∈ l, (F m).Mem (v m)) :
    (sumW l F).Mem ((l.map v).sum) := sumF_mem l F v h

/-! ### Real coefficients of one retained wave -/

/-- The anchor parity integer `m·k`. -/
def kk (an : Anchor) (m : Wave) : ℤ := m.1 * an.k₁ + m.2 * an.k₂

def cgR (p : Chart) (an : Anchor) (m : Wave) : ℝ :=
  Layered.parityR (kk an m) * Real.cos (Real.pi * wReal p m)
def sgR (p : Chart) (an : Anchor) (m : Wave) : ℝ :=
  Layered.parityR (kk an m) * Real.sin (Real.pi * wReal p m)
def kpR (A Ψ : ℝ) : ℝ := A ^ 2 * Real.exp A / 2 + Ψ ^ 2 / 6

def lamR (p : Chart) (an : Anchor) (A Ψ : ℝ) (m : Wave) : ℝ :=
  -(Layered.modeW p m * (2 * Real.pi) ^ 2 *
    (cgR p an m / 2 + max 0 (-cgR p an m) * Ψ ^ 2 / 24 + Layered.axialFactor (tReal p m) A))
def muR (p : Chart) (an : Anchor) (A _Ψ : ℝ) (m : Wave) : ℝ :=
  -(Layered.modeW p m * tReal p m ^ 2 *
    (|cgR p an m| * Real.exp A / 2 + Layered.axialFactor (tReal p m) A))
def chiR (p : Chart) (an : Anchor) (_A _Ψ : ℝ) (m : Wave) : ℝ :=
  2 * Real.pi * Layered.modeW p m * tReal p m * sgR p an m
def epsR (p : Chart) (an : Anchor) (A Ψ : ℝ) (m : Wave) : ℝ :=
  2 * Real.pi * Layered.modeW p m * tReal p m * |sgR p an m| * kpR A Ψ

/-- The per-wave quadratic form, with every coefficient in front of a
wave-independent monomial. -/
def waveQuad (p : Chart) (an : Anchor) (A Ψ : ℝ) (m : Wave) (v₁ v₂ δ : ℝ) : ℝ :=
  (lamR p an A Ψ m * (m.1 : ℝ) ^ 2) * v₁ ^ 2 + (2 * (lamR p an A Ψ m * ((m.1 : ℝ) * (m.2 : ℝ)))) * (v₁ * v₂) +
    (lamR p an A Ψ m * (m.2 : ℝ) ^ 2) * v₂ ^ 2 + muR p an A Ψ m * δ ^ 2 +
    (chiR p an A Ψ m * (m.1 : ℝ)) * (δ * v₁) + (chiR p an A Ψ m * (m.2 : ℝ)) * (δ * v₂) -
    (epsR p an A Ψ m * |(m.1 : ℝ)|) * |δ * v₁| - (epsR p an A Ψ m * |(m.2 : ℝ)|) * |δ * v₂|

theorem modeLower_ge (p : Chart) (an : Anchor) (A Ψ : ℝ) (m : Wave)
    (hW : 0 ≤ Layered.modeW p m) (hT : 0 ≤ tReal p m) :
    waveQuad p an A Ψ m (Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0)
        (Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1) (p 7 - 1 / 2) ≤
      Layered.modeLower p (an.k₁ / 2) (an.k₂ / 2) (kk an m) A Ψ m := by
  have hP : |Layered.parityR (kk an m)| = 1 := by
    rcases Layered.parityR_cases (kk an m) with h | h <;> rw [h] <;> norm_num
  have hcg : |Real.cos (Real.pi * wReal p m)| = |cgR p an m| := by
    unfold cgR; rw [abs_mul, hP, one_mul]
  have hsg : |Real.sin (Real.pi * wReal p m)| = |sgR p an m| := by
    unfold sgR; rw [abs_mul, hP, one_mul]
  have ha : |tReal p m * (p 7 - 1 / 2)| = tReal p m * |p 7 - 1 / 2| := by
    rw [abs_mul, abs_of_nonneg hT]
  have hψ : |2 * Real.pi * ((m.1 : ℝ) * Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0 +
      (m.2 : ℝ) * Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1)| =
      2 * Real.pi * |(m.1 : ℝ) * Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0 +
      (m.2 : ℝ) * Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  obtain ⟨v₁, hv₁⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0 := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = p 7 - 1 / 2 := ⟨_, rfl⟩
  -- the exact value of modeLower
  have eq : Layered.modeLower p (an.k₁ / 2) (an.k₂ / 2) (kk an m) A Ψ m =
      lamR p an A Ψ m * ((m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂) ^ 2 + muR p an A Ψ m * δ ^ 2 +
        chiR p an A Ψ m * (δ * ((m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂)) -
        epsR p an A Ψ m * (|δ| * |(m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂|) := by
    dsimp only [Layered.modeLower, Layered.pairLower]
    rw [ha, hψ, hcg, hsg]
    rw [← hv₁, ← hv₂, ← hδ]
    unfold lamR muR chiR epsR kpR
    unfold cgR sgR
    ring
  rw [← hv₁, ← hv₂, ← hδ, eq]
  -- |δ| |m·v| ≤ |m₁||δ v₁| + |m₂||δ v₂|
  have hmv : |δ| * |(m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂| ≤ |(m.1 : ℝ)| * |δ * v₁| + |(m.2 : ℝ)| * |δ * v₂| := by
    have t := abs_add_le ((m.1 : ℝ) * v₁) ((m.2 : ℝ) * v₂)
    rw [abs_mul (m.1 : ℝ), abs_mul (m.2 : ℝ)] at t
    have := mul_le_mul_of_nonneg_left t (abs_nonneg δ)
    rw [abs_mul δ v₁, abs_mul δ v₂]
    linarith
  have eps0 : 0 ≤ epsR p an A Ψ m := by
    unfold epsR kpR
    have := Real.exp_pos A
    positivity
  unfold waveQuad
  have e2 : ((m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂) ^ 2 =
      (m.1 : ℝ) ^ 2 * v₁ ^ 2 + 2 * ((m.1 : ℝ) * (m.2 : ℝ)) * (v₁ * v₂) + (m.2 : ℝ) ^ 2 * v₂ ^ 2 := by ring
  rw [e2]
  have := mul_le_mul_of_nonneg_left hmv eps0
  nlinarith

/-! ### Enclosures of one retained wave -/

section Wave
variable {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b)
include hp g

theorem c_pos : 0 < cReal p := by
  have hr : 0 < p 0 := (div_pos (by exact_mod_cast g.r₀) Sz_pos).trans_le (cx_mem hp 0).1
  have hs : 0 < p 1 := (div_pos (by exact_mod_cast g.r₁) Sz_pos).trans_le (cx_mem hp 1).1
  exact inv_pos.mpr (mul_pos hr hs)

theorem tReal_nonneg' (m : Wave) : 0 ≤ tReal p m := by
  have := c_pos hp g
  unfold tReal
  have : 0 ≤ κReal p m := Real.sqrt_nonneg _
  positivity

variable {an : Anchor} {m : Wave} (ok : waveOk b an m = true)
include ok

omit hp g in
theorem waveOk_facts : 0 < (kappaF b m).lo ∧ 0 < (tF b m).lo ∧
    0 < ((ptF Sz).sub (expRange (tF b m).lo (tF b m).hi)).lo ∧
    0 ≤ aZ b m ∧ aZ b m ≤ (S64 : ℤ) ∧ 0 < (expNegPt (aZ b m).toNat).lo ∧ 0 ≤ psiZ b an m := by
  simpa [waveOk] using ok

theorem modeW_mem : (wF' b m).Mem (Layered.modeW p m) := by
  obtain ⟨hκ, -, -, -, -, -, -⟩ := waveOk_facts ok
  have ht := tF_mem hp g m
  have hT2 : 0 ≤ tReal p m / 2 := by have := tReal_nonneg' hp g m; linarith
  have h := FI.mulPos_mem (FI.mulPos_mem (FI.smul_mem 4 (cF_mem hp g)) (FI.invPos_mem hκ (kappaF_mem hp g m)))
    (expRange_mem (half_mem ht) hT2)
  have e : Layered.modeW p m = (((4 : ℤ) : ℝ) * cReal p) * (κReal p m)⁻¹ * Real.exp (-(tReal p m / 2)) := by
    unfold Layered.modeW
    rw [show -tReal p m / 2 = -(tReal p m / 2) by ring]
    push_cast
    ring
  rw [e]
  exact h

theorem modeW_nonneg : 0 ≤ Layered.modeW p m := by
  obtain ⟨hκ, -, -, -, -, -, -⟩ := waveOk_facts ok
  have k0 : 0 < κReal p m := lt_of_lt_of_le (div_pos (by exact_mod_cast hκ) Sz_pos) (kappaF_mem hp g m).1
  unfold Layered.modeW
  have := c_pos hp g
  positivity

omit g ok in
theorem cgF_mem' : (cgF b an m).Mem (cgR p an m) := by
  have h := FI.smul_mem (parityZ (m.1 * an.k₁ + m.2 * an.k₂)) (cosPiF_mem (wF_mem hp m))
  rw [parityZ_cast] at h
  exact h

omit g ok in
theorem sgF_mem' : (sgF b an m).Mem (sgR p an m) := by
  have h := FI.smul_mem (parityZ (m.1 * an.k₁ + m.2 * an.k₂)) (sinPiF_mem (wF_mem hp m))
  rw [parityZ_cast] at h
  exact h

omit ok in
theorem aZ_bound : |tReal p m * (p 7 - 1 / 2)| ≤ (aZ b m : ℝ) / Sz := by
  have sp := Sz_pos
  have ht := tF_mem hp g m
  have T0 := tReal_nonneg' hp g m
  have hd := magZ_bound (deltaF_mem hp)
  have e0 : (0 : ℝ) ≤ (etaZ b : ℝ) := by exact_mod_cast magZ_nonneg (deltaF b)
  rw [abs_mul, abs_of_nonneg T0]
  have h1 : tReal p m * |p 7 - 1 / 2| ≤ ((tF b m).hi : ℝ) / Sz * ((etaZ b : ℝ) / Sz) :=
    mul_le_mul ht.2 hd (abs_nonneg _) (T0.trans ht.2)
  have h2 := le_cdiv ((tF b m).hi * etaZ b) Sz Sz_posZ
  push_cast at h2
  unfold aZ
  calc tReal p m * |p 7 - 1 / 2| ≤ ((tF b m).hi : ℝ) / Sz * ((etaZ b : ℝ) / Sz) := h1
    _ = ((tF b m).hi : ℝ) * (etaZ b : ℝ) / Sz / Sz := by ring
    _ ≤ (cdivZ ((tF b m).hi * etaZ b) Sz : ℝ) / Sz := div_le_div_of_nonneg_right h2 sp.le

theorem afF_mem' : (afF b m).Mem (Layered.axialFactor (tReal p m) ((aZ b m : ℝ) / Sz)) := by
  obtain ⟨-, -, hd, ha0, -, hlo, -⟩ := waveOk_facts ok
  have he := expRange_mem (tF_mem hp g m) (tReal_nonneg' hp g m)
  have hden := FI.sub_mem ptF_one he
  have h := FI.mul_mem (FI.mul_mem he (FI.invPos_mem hd hden)) (expPosF_mem ha0 hlo)
  unfold Layered.axialFactor
  rw [div_eq_mul_inv]
  exact h

omit hp g in
theorem kpF_mem' : (kpF b an m).Mem (kpR ((aZ b m : ℝ) / Sz) ((psiZ b an m : ℝ) / Sz)) := by
  obtain ⟨-, -, -, ha0, -, hlo, -⟩ := waveOk_facts ok
  have h := FI.add_mem (halfF_mem (FI.mul_mem (FI.sq_mem (ptF_mem (aZ b m))) (expPosF_mem ha0 hlo)))
    (divNatF_mem (FI.sq_mem (ptF_mem (psiZ b an m))) 6 (by norm_num))
  unfold kpR
  push_cast at h
  exact h

theorem lamF_mem' : (lamF b an m).Mem (lamR p an ((aZ b m : ℝ) / Sz) ((psiZ b an m : ℝ) / Sz) m) := by
  have hcg := cgF_mem' hp (an := an) (m := m)
  have h := negF_mem (FI.mul_mem (FI.mul_mem (modeW_mem hp g ok) (FI.sq_mem twoPiF_mem))
    (FI.add_mem (FI.add_mem (halfF_mem hcg)
      (divNatF_mem (FI.mul_mem (negPartF_mem hcg) (FI.sq_mem (ptF_mem (psiZ b an m)))) 24 (by norm_num)))
      (afF_mem' hp g ok)))
  unfold lamF fourPiSqF
  push_cast at h
  unfold lamR
  exact h

theorem muF_mem' : (muF b an m).Mem (muR p an ((aZ b m : ℝ) / Sz) ((psiZ b an m : ℝ) / Sz) m) := by
  obtain ⟨-, -, -, ha0, -, hlo, -⟩ := waveOk_facts ok
  have h := negF_mem (FI.mul_mem (FI.mul_mem (modeW_mem hp g ok) (FI.sq_mem (tF_mem hp g m)))
    (FI.add_mem (halfF_mem (FI.mul_mem (absF_mem (cgF_mem' hp (an := an) (m := m))) (expPosF_mem ha0 hlo)))
      (afF_mem' hp g ok)))
  unfold muF
  unfold muR
  exact h

theorem chiF_mem' : (chiF b an m).Mem (chiR p an ((aZ b m : ℝ) / Sz) ((psiZ b an m : ℝ) / Sz) m) := by
  have h := FI.mul_mem (FI.mul_mem (FI.mul_mem twoPiF_mem (modeW_mem hp g ok)) (tF_mem hp g m))
    (sgF_mem' hp (an := an) (m := m))
  unfold chiR
  exact h

theorem epsF_mem' : (epsF b an m).Mem (epsR p an ((aZ b m : ℝ) / Sz) ((psiZ b an m : ℝ) / Sz) m) := by
  have h := FI.mul_mem (FI.mul_mem (FI.mul_mem (FI.mul_mem twoPiF_mem (modeW_mem hp g ok))
    (tF_mem hp g m)) (absF_mem (sgF_mem' hp (an := an) (m := m)))) (kpF_mem' ok)
  unfold epsR
  exact h

end Wave

/-! ### The lateral displacement -/

theorem v₁F_mem {b : Cell} {p : Chart} (hp : b.Mem p) (an : Anchor) :
    (v₁F b an).Mem (Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0) := by
  have ha : (alphaF an.k₁).Mem ((an.k₁ : ℝ) / 2) := by
    have := ptF_mem (an.k₁ * halfS)
    have e : ((an.k₁ * halfS : ℤ) : ℝ) / Sz = (an.k₁ : ℝ) / 2 := by
      have hS : (Sz : ℝ) ≠ 0 := ne_of_gt Sz_pos
      push_cast; rw [halfS_eq]; field_simp
    rwa [e] at this
  have h := FI.add_mem (FI.sub_mem (cx_mem hp 5) ha)
    (FI.mul_mem (FI.sub_mem (cx_mem hp 3) (FI.mul_mem (cx_mem hp 2) (cx_mem hp 4))) (deltaF_mem hp))
  rw [Layered.latV_zero]
  exact h

theorem v₂F_mem {b : Cell} {p : Chart} (hp : b.Mem p) (an : Anchor) :
    (v₂F b an).Mem (Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1) := by
  have ha : (alphaF an.k₂).Mem ((an.k₂ : ℝ) / 2) := by
    have := ptF_mem (an.k₂ * halfS)
    have e : ((an.k₂ * halfS : ℤ) : ℝ) / Sz = (an.k₂ : ℝ) / 2 := by
      have hS : (Sz : ℝ) ≠ 0 := ne_of_gt Sz_pos
      push_cast; rw [halfS_eq]; field_simp
    rwa [e] at this
  have h := FI.add_mem (FI.sub_mem (cx_mem hp 6) ha) (FI.mul_mem (cx_mem hp 4) (deltaF_mem hp))
  rw [Layered.latV_one]
  exact h

theorem psiZ_bound {b : Cell} {p : Chart} (hp : b.Mem p) (an : Anchor) (m : Wave) :
    |2 * Real.pi * ((m.1 : ℝ) * Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0 +
      (m.2 : ℝ) * Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1)| ≤ (psiZ b an m : ℝ) / Sz := by
  have sp := Sz_pos
  have h1 := magZ_bound (v₁F_mem hp an)
  have h2 := magZ_bound (v₂F_mem hp an)
  have r1 : (0 : ℝ) ≤ (rho₁Z b an : ℝ) := by exact_mod_cast magZ_nonneg _
  have r2 : (0 : ℝ) ≤ (rho₂Z b an : ℝ) := by exact_mod_cast magZ_nonneg _
  obtain ⟨v₁, hv₁⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0 := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1 := ⟨_, rfl⟩
  rw [← hv₁] at h1 ⊢
  rw [← hv₂] at h2 ⊢
  have e1 : ((m.1.natAbs : ℤ) : ℝ) = |(m.1 : ℝ)| := by
    rw [Int.natCast_natAbs, Int.cast_abs]
  have e2 : ((m.2.natAbs : ℤ) : ℝ) = |(m.2 : ℝ)| := by
    rw [Int.natCast_natAbs, Int.cast_abs]
  have tri : |(m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂| ≤
      |(m.1 : ℝ)| * ((rho₁Z b an : ℝ) / Sz) + |(m.2 : ℝ)| * ((rho₂Z b an : ℝ) / Sz) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have tp := twoPi_bounds.2
  have hc := le_cdiv (twoPiHi * ((m.1.natAbs : ℤ) * rho₁Z b an + (m.2.natAbs : ℤ) * rho₂Z b an)) Sz Sz_posZ
  unfold psiZ
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have nn : (0 : ℝ) ≤ |(m.1 : ℝ)| * ((rho₁Z b an : ℝ) / Sz) + |(m.2 : ℝ)| * ((rho₂Z b an : ℝ) / Sz) := by
    positivity
  have key : ((twoPiHi * ((m.1.natAbs : ℤ) * rho₁Z b an + (m.2.natAbs : ℤ) * rho₂Z b an) : ℤ) : ℝ) / Sz / Sz =
      (twoPiHi : ℝ) / Sz * (|(m.1 : ℝ)| * ((rho₁Z b an : ℝ) / Sz) + |(m.2 : ℝ)| * ((rho₂Z b an : ℝ) / Sz)) := by
    push_cast
    ring
  calc 2 * Real.pi * |(m.1 : ℝ) * v₁ + (m.2 : ℝ) * v₂|
      ≤ (twoPiHi : ℝ) / Sz * (|(m.1 : ℝ)| * ((rho₁Z b an : ℝ) / Sz) + |(m.2 : ℝ)| * ((rho₂Z b an : ℝ) / Sz)) :=
        mul_le_mul tp tri (abs_nonneg _) (le_trans (by positivity) tp)
    _ = ((twoPiHi * ((m.1.natAbs : ℤ) * rho₁Z b an + (m.2.natAbs : ℤ) * rho₂Z b an) : ℤ) : ℝ) / Sz / Sz :=
        key.symm
    _ ≤ _ := div_le_div_of_nonneg_right hc sp.le

/-! ### Interval `LDLᵀ` -/

/-- `a₀₀z₀² + 2a₀₁z₀z₁ + a₁₁z₁² + 2a₀₂z₀z₂ + 2a₁₂z₁z₂ + a₂₂z₂²`. -/
def quad6 (a00 a01 a11 a02 a12 a22 z0 z1 z2 : ℝ) : ℝ :=
  a00 * z0 ^ 2 + 2 * a01 * (z0 * z1) + a11 * z1 ^ 2 + 2 * a02 * (z0 * z2) + 2 * a12 * (z1 * z2) +
    a22 * z2 ^ 2

theorem pdOk_sound (s : Sym3) (ok : pdOk s = true) {a00 a01 a11 a02 a12 a22 : ℝ}
    (h00 : s.s00.Mem a00) (h01 : s.s01.Mem a01) (h11 : s.s11.Mem a11) (h02 : s.s02.Mem a02)
    (h12 : s.s12.Mem a12) (h22 : s.s22.Mem a22) (z0 z1 z2 : ℝ) :
    0 ≤ quad6 a00 a01 a11 a02 a12 a22 z0 z1 z2 := by
  have sp := Sz_pos
  obtain ⟨p0, p1, p2⟩ : 0 < s.s00.lo ∧ 0 < (pivot₁ s).lo ∧ 0 < (pivot₂ s).lo := by
    simpa [pdOk] using ok
  have d0 : 0 < a00 := lt_of_lt_of_le (div_pos (by exact_mod_cast p0) sp) h00.1
  have hi0 := FI.invPos_mem p0 h00
  have hd1 : (pivot₁ s).Mem (a11 - a01 ^ 2 * a00⁻¹) := FI.sub_mem h11 (FI.mul_mem (FI.sq_mem h01) hi0)
  have d1 : 0 < a11 - a01 ^ 2 * a00⁻¹ := lt_of_lt_of_le (div_pos (by exact_mod_cast p1) sp) hd1.1
  have ht : (tcross s).Mem (a12 - a02 * a01 * a00⁻¹) :=
    FI.sub_mem h12 (FI.mul_mem (FI.mul_mem h02 h01) hi0)
  have hi1 := FI.invPos_mem p1 hd1
  have hd2 : (pivot₂ s).Mem (a22 - a02 ^ 2 * a00⁻¹ -
      (a12 - a02 * a01 * a00⁻¹) ^ 2 * (a11 - a01 ^ 2 * a00⁻¹)⁻¹) :=
    FI.sub_mem (FI.sub_mem h22 (FI.mul_mem (FI.sq_mem h02) hi0)) (FI.mul_mem (FI.sq_mem ht) hi1)
  have d2 : 0 < a22 - a02 ^ 2 * a00⁻¹ - (a12 - a02 * a01 * a00⁻¹) ^ 2 * (a11 - a01 ^ 2 * a00⁻¹)⁻¹ :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast p2) sp) hd2.1
  obtain ⟨e1, he1⟩ : ∃ e, e = a11 - a01 ^ 2 * a00⁻¹ := ⟨_, rfl⟩
  obtain ⟨t, het⟩ : ∃ t, t = a12 - a02 * a01 * a00⁻¹ := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e, e = a22 - a02 ^ 2 * a00⁻¹ - t ^ 2 * e1⁻¹ := ⟨_, rfl⟩
  rw [← he1] at d1
  rw [← het, ← he1, ← he2] at d2
  have key : quad6 a00 a01 a11 a02 a12 a22 z0 z1 z2 =
      a00 * (z0 + a01 / a00 * z1 + a02 / a00 * z2) ^ 2 + e1 * (z1 + t / e1 * z2) ^ 2 + e2 * z2 ^ 2 := by
    have n0 : a00 ≠ 0 := ne_of_gt d0
    have n1 : e1 ≠ 0 := ne_of_gt d1
    have ha11 : a11 = e1 + a01 ^ 2 / a00 := by rw [he1, div_eq_mul_inv]; ring
    have ha12 : a12 = t + a02 * a01 / a00 := by rw [het, div_eq_mul_inv]; ring
    have ha22 : a22 = e2 + a02 ^ 2 / a00 + t ^ 2 / e1 := by rw [he2, div_eq_mul_inv, div_eq_mul_inv]; ring
    unfold quad6
    rw [ha11, ha12, ha22]
    field_simp
    ring
  rw [key]
  positivity

/-! ### The omitted-wave tail -/

theorem powF_mem {a : FI} {x : ℝ} (hx : a.Mem x) : ∀ n : ℕ, (powF a n).Mem (x ^ n)
  | 0 => by
    show (ptF Sz).Mem (x ^ 0)
    rw [pow_zero]
    exact ptF_one
  | n + 1 => by
    show (FI.mulPos (powF a n) a).Mem (x ^ (n + 1))
    rw [pow_succ]
    exact FI.mulPos_mem (powF_mem hx n) hx

section Outer
variable {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) {K : ℕ} (ok : outerOk b K = true)
include ok

theorem outerOk_facts : 0 < tauZ b ∧ 0 < columnF b ∧ (expNegPt (tauZ b).toNat).hi < Sz ∧
    2 * etaZ b < Sz ∧ (2 * Sz * Sz : ℤ) ≤ tauZ b * ((K : ℤ) + 1) * (halfS - etaZ b) ∧
    ((K : ℤ) + 1 + 1) * ((K : ℤ) + 1 + 1) * qUpZ b < ((K : ℤ) + 1) * ((K : ℤ) + 1) * Sz ∧
    0 < Sz - cdivZ (((K : ℤ) + 1 + 1) * ((K : ℤ) + 1 + 1) * qUpZ b) (((K : ℤ) + 1) * ((K : ℤ) + 1)) := by
  simpa [outerOk] using ok

theorem eta_lt : (etaZ b : ℝ) / Sz < 1 / 2 := by
  obtain ⟨-, -, -, h, -⟩ := outerOk_facts ok
  have sp := Sz_pos
  rw [div_lt_iff₀ sp]
  have : (2 * etaZ b : ℝ) < Sz := by exact_mod_cast h
  linarith

theorem tau_pos : 0 < (tauZ b : ℝ) / Sz := by
  obtain ⟨h, -⟩ := outerOk_facts ok
  exact div_pos (by exact_mod_cast h) Sz_pos

theorem tau_mono : 2 / (1 / 2 - (etaZ b : ℝ) / Sz) ≤ (tauZ b : ℝ) / Sz * ((K : ℝ) + 1) := by
  obtain ⟨-, -, -, h2, h5, -⟩ := outerOk_facts ok
  have sp := Sz_pos
  have hS : (Sz : ℝ) ≠ 0 := ne_of_gt sp
  have hη : (0 : ℝ) < 1 / 2 - (etaZ b : ℝ) / Sz := by have := eta_lt ok; linarith
  rw [div_le_iff₀ hη]
  have h5r : (2 * Sz * Sz : ℝ) ≤ (tauZ b : ℝ) * ((K : ℝ) + 1) * ((halfS : ℝ) - (etaZ b : ℝ)) := by
    exact_mod_cast h5
  rw [halfS_eq] at h5r
  have e : (tauZ b : ℝ) / Sz * ((K : ℝ) + 1) * (1 / 2 - (etaZ b : ℝ) / Sz) =
      (tauZ b : ℝ) * ((K : ℝ) + 1) * ((Sz : ℝ) / 2 - (etaZ b : ℝ)) / (Sz * Sz) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

theorem q_le : Real.exp (-((tauZ b : ℝ) / Sz * (1 / 2 - (etaZ b : ℝ) / Sz))) ≤ (qUpZ b : ℝ) / Sz := by
  obtain ⟨t0, -, -, h2, -⟩ := outerOk_facts ok
  have sp := Sz_pos
  have hS : (Sz : ℝ) ≠ 0 := ne_of_gt sp
  set x : ℤ := tauZ b * (halfS - etaZ b) / Sz with hx
  have hpos : 0 ≤ tauZ b * (halfS - etaZ b) := by
    have : 0 ≤ halfS - etaZ b := by
      have : (2 : ℤ) * halfS = Sz := by norm_num [halfS, Sz]
      omega
    exact mul_nonneg t0.le this
  have x0 : 0 ≤ x := Int.ediv_nonneg hpos (by norm_num [Sz])
  have hxr : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg x0
  have hle : (x : ℝ) / Sz ≤ (tauZ b : ℝ) / Sz * (1 / 2 - (etaZ b : ℝ) / Sz) := by
    have f := fdiv_le (tauZ b * (halfS - etaZ b)) Sz Sz_posZ
    have e : (tauZ b : ℝ) / Sz * (1 / 2 - (etaZ b : ℝ) / Sz) =
        ((tauZ b * (halfS - etaZ b) : ℤ) : ℝ) / Sz / Sz := by
      push_cast; rw [halfS_eq]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_right f sp.le
  have m := (expNegPt_mem x.toNat).2
  rw [hxr] at m
  unfold qUpZ
  rw [← hx]
  exact le_trans (Real.exp_le_exp.mpr (by linarith)) m

theorem rho_lt : (((K : ℝ) + 2) / ((K : ℝ) + 1)) ^ 2 *
    Real.exp (-((tauZ b : ℝ) / Sz * (1 / 2 - (etaZ b : ℝ) / Sz))) < 1 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := outerOk_facts ok
  have sp := Sz_pos
  have q := q_le ok
  have J0 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have h6r : ((K : ℝ) + 2) * ((K : ℝ) + 2) * (qUpZ b : ℝ) < ((K : ℝ) + 1) * ((K : ℝ) + 1) * Sz := by
    have h6' : (((K : ℤ) + 1 + 1) * ((K : ℤ) + 1 + 1) * qUpZ b : ℝ) < (((K : ℤ) + 1) * ((K : ℤ) + 1) * Sz : ℤ) := by
      exact_mod_cast h6
    push_cast at h6'
    have e : ((K : ℝ) + 1 + 1) = (K : ℝ) + 2 := by ring
    rw [e] at h6'
    exact h6'
  have qs : ((K : ℝ) + 2) ^ 2 * ((qUpZ b : ℝ) / Sz) < ((K : ℝ) + 1) ^ 2 := by
    rw [mul_div_assoc', div_lt_iff₀ sp]; nlinarith
  calc (((K : ℝ) + 2) / ((K : ℝ) + 1)) ^ 2 * Real.exp (-((tauZ b : ℝ) / Sz * (1 / 2 - (etaZ b : ℝ) / Sz)))
      ≤ (((K : ℝ) + 2) / ((K : ℝ) + 1)) ^ 2 * ((qUpZ b : ℝ) / Sz) :=
        mul_le_mul_of_nonneg_left q (by positivity)
    _ = ((K : ℝ) + 2) ^ 2 * ((qUpZ b : ℝ) / Sz) / ((K : ℝ) + 1) ^ 2 := by rw [div_pow]; ring
    _ < 1 := by rw [div_lt_one (by positivity)]; exact qs

include hp g

theorem tau_le : (tauZ b : ℝ) / Sz ≤ 2 * Real.pi * cReal p / ((columnF b : ℝ) / Sz) := by
  obtain ⟨τ0, B0, -⟩ := outerOk_facts ok
  have sp := Sz_pos
  have hc := cF_mem hp g
  have Bp : (0 : ℝ) < (columnF b : ℝ) / Sz := div_pos (by exact_mod_cast B0) sp
  have q0 : 0 ≤ twoPiLo * (cF b).lo / columnF b := by
    by_contra hq
    unfold tauZ tauN at τ0
    rw [Int.toNat_eq_zero.mpr (le_of_lt (lt_of_not_ge hq))] at τ0
    exact lt_irrefl _ τ0
  have e : ((tauZ b : ℤ) : ℝ) = ((twoPiLo * (cF b).lo / columnF b : ℤ) : ℝ) := by
    unfold tauZ tauN; exact_mod_cast Int.toNat_of_nonneg q0
  rw [e, le_div_iff₀ Bp]
  have f := fdiv_le (twoPiLo * (cF b).lo) (columnF b) B0
  have key : ((twoPiLo : ℝ) / Sz) * (((cF b).lo : ℝ) / Sz) ≤ 2 * Real.pi * cReal p := by
    rcases le_or_gt 0 (cF b).lo with h | h
    · exact mul_le_mul twoPi_bounds.1 hc.1 (div_nonneg (by exact_mod_cast h) sp.le) (by positivity)
    · have : ((twoPiLo : ℝ) / Sz) * (((cF b).lo : ℝ) / Sz) < 0 :=
        mul_neg_of_pos_of_neg (div_pos (by norm_num [twoPiLo]) sp)
          (div_neg_of_neg_of_pos (by exact_mod_cast h) sp)
      have := c_pos hp g
      nlinarith [Real.pi_pos]
  have cF0 : (columnF b : ℝ) ≠ 0 := by exact_mod_cast B0.ne'
  calc ((twoPiLo * (cF b).lo / columnF b : ℤ) : ℝ) / Sz * ((columnF b : ℝ) / Sz)
      ≤ ((twoPiLo * (cF b).lo : ℤ) : ℝ) / columnF b / Sz * ((columnF b : ℝ) / Sz) := by
        gcongr
    _ = ((twoPiLo : ℝ) / Sz) * (((cF b).lo : ℝ) / Sz) := by
        push_cast; field_simp
    _ ≤ _ := key

theorem outerF_mem : (outerF b K).Mem (Layered.outerTail (cReal p) ((columnF b : ℝ) / Sz)
    ((tauZ b : ℝ) / Sz) ((etaZ b : ℝ) / Sz) K) := by
  obtain ⟨τ0, -, eτ, -, -, -, d2pos⟩ := outerOk_facts ok
  have sp := Sz_pos
  have hτr : (((tauZ b).toNat : ℕ) : ℝ) = (tauZ b : ℝ) := by exact_mod_cast Int.toNat_of_nonneg τ0.le
  have he := expNegPt_mem (tauZ b).toNat
  rw [hτr] at he
  have hd1 := FI.sub_mem ptF_one he
  have d1lo : 0 < ((ptF Sz).sub (expNegPt (tauZ b).toNat)).lo := by
    show 0 < Sz - (expNegPt (tauZ b).toNat).hi
    linarith
  have hq : (qF b).Mem (Real.exp (-((tauZ b : ℝ) / Sz * (1 / 2 - (etaZ b : ℝ) / Sz)))) :=
    ⟨by simp only [qF, Int.cast_zero, zero_div]; exact (Real.exp_pos _).le, q_le ok⟩
  have hJ : (0 : ℕ) < (((K : ℤ) + 1) * ((K : ℤ) + 1)).toNat :=
    Int.lt_toNat.mpr (by push_cast; positivity)
  have hratio := divNatF_mem (FI.smul_mem (((K : ℤ) + 1 + 1) * ((K : ℤ) + 1 + 1)) hq)
    (((K : ℤ) + 1) * ((K : ℤ) + 1)).toNat hJ
  have hd2 := FI.sub_mem ptF_one hratio
  have d2lo : 0 < ((ptF Sz).sub (divNatF (FI.smul (((K : ℤ) + 1 + 1) * ((K : ℤ) + 1 + 1)) (qF b))
      (((K : ℤ) + 1) * ((K : ℤ) + 1)).toNat)).lo := by
    have hJ' : ((((K : ℤ) + 1) * ((K : ℤ) + 1)).toNat : ℤ) = ((K : ℤ) + 1) * ((K : ℤ) + 1) := by
      apply Int.toNat_of_nonneg; positivity
    have hs0 : (0 : ℤ) ≤ ((K : ℤ) + 1 + 1) * ((K : ℤ) + 1 + 1) := by positivity
    simp only [FI.sub, ptF, divNatF, FI.smul, qF, hJ', hs0, ite_true]
    linarith
  have h := FI.mul_mem (cF_mem hp g)
    (FI.mulPos_mem (FI.mulPos_mem (FI.smul_mem 16 (ptF_mem (columnF b))) (FI.invPos_mem d1lo hd1))
      (FI.mulPos_mem (FI.smul_mem (((K : ℤ) + 1) * ((K : ℤ) + 1)) (powF_mem hq (K + 1)))
        (FI.invPos_mem d2lo hd2)))
  have hJr : ((((K : ℤ) + 1) * ((K : ℤ) + 1)).toNat : ℝ) = ((K : ℝ) + 1) * ((K : ℝ) + 1) := by
    have : ((((K : ℤ) + 1) * ((K : ℤ) + 1)).toNat : ℤ) = ((K : ℤ) + 1) * ((K : ℤ) + 1) := by
      apply Int.toNat_of_nonneg; positivity
    exact_mod_cast this
  rw [hJr] at h
  unfold outerF
  unfold Layered.outerTail
  push_cast at h ⊢
  convert h using 2
  field_simp

end Outer

/-! ### The gain as a quadratic form -/

section Assembly
variable (b : Cell) (an : Anchor) (p : Chart)

def Aw (m : Wave) : ℝ := (aZ b m : ℝ) / Sz
def Ψw (m : Wave) : ℝ := (psiZ b an m : ℝ) / Sz
def Hout : ℝ := Layered.outerTail (cReal p) ((columnF b : ℝ) / Sz) ((tauZ b : ℝ) / Sz) ((etaZ b : ℝ) / Sz) an.cube

def sumL (f : Wave → ℝ) : ℝ := ∑ m ∈ waves an.cube, f m

def e00 : ℝ := sumL an (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.1 : ℝ) ^ 2) -
  (2 * Real.pi) ^ 2 * (2 * Hout b an p)
def e01 : ℝ := sumL an (fun m => lamR p an (Aw b m) (Ψw b an m) m * ((m.1 : ℝ) * (m.2 : ℝ)))
def e11 : ℝ := sumL an (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.2 : ℝ) ^ 2) -
  (2 * Real.pi) ^ 2 * (2 * Hout b an p)
def e22 : ℝ := 2 * Real.pi * cReal p ^ 2 + sumL an (fun m => muR p an (Aw b m) (Ψw b an m) m) -
  ((tauZ b : ℝ) / Sz) ^ 2 * Hout b an p
def X₁ : ℝ := sumL an (fun m => chiR p an (Aw b m) (Ψw b an m) m * (m.1 : ℝ))
def X₂ : ℝ := sumL an (fun m => chiR p an (Aw b m) (Ψw b an m) m * (m.2 : ℝ))
def E₁ : ℝ := sumL an (fun m => epsR p an (Aw b m) (Ψw b an m) m * |(m.1 : ℝ)|)
def E₂ : ℝ := sumL an (fun m => epsR p an (Aw b m) (Ψw b an m) m * |(m.2 : ℝ)|)

end Assembly

/-- The sign that turns `x` into `|x|`. -/
def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem sgn_mul (x : ℝ) : sgn x * x = |x| := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]; ring

theorem abs_sgn (x : ℝ) : |sgn x| = 1 := by unfold sgn; split_ifs <;> norm_num

/-- `|R d|²` in the coordinates `(v₁, v₂, δ)`. -/
def layerGram (p : Chart) (α₁ α₂ : ℝ) : ℝ :=
  quad6 (p 0 ^ 2) (p 0 ^ 2 * p 2) ((p 0 * p 2) ^ 2 + p 1 ^ 2) 0 0 (cReal p ^ 2)
    (Layered.latV p α₁ α₂ 0) (Layered.latV p α₁ α₂ 1) (p 7 - 1 / 2)

theorem epsR_nonneg (p : Chart) (an : Anchor) (A Ψ : ℝ) (m : Wave) (hW : 0 ≤ Layered.modeW p m)
    (hT : 0 ≤ tReal p m) : 0 ≤ epsR p an A Ψ m := by
  unfold epsR kpR
  have := Real.exp_pos A
  positivity

theorem leafOk_gain {b : Cell} {an : Anchor} {lam : ℚ} (ok : leafOk b an lam = true)
    {p : Chart} (hp : b.Mem p) :
    (lam : ℝ) * layerGram p (an.k₁ / 2) (an.k₂ / 2) ≤
      2 * ac * (energy (chartPoint p) -
        energy (chartPoint (Layered.anchorChart p (an.k₁ / 2) (an.k₂ / 2)))) := by
  simp only [leafOk, Bool.and_eq_true] at ok
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
  have LG := Layered.layered_gain p (an.k₁ / 2) (an.k₂ / 2) an.k₁ an.k₂ (by ring) (by ring) hr hs hηb
    (eta_lt ho) an.cube B₁ B₂ (tau_pos ho) (tau_le hp g ho) (tau_mono ho) (rho_lt ho)
    (Aw b) (Ψw b an) (fun m _ => aZ_bound hp g (m := m)) (fun m hm => psiZ_bound hp an m)
  -- the retained waves as quadratic forms
  obtain ⟨v₁, hv₁⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 0 := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, v = Layered.latV p (an.k₁ / 2) (an.k₂ / 2) 1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = p 7 - 1 / 2 := ⟨_, rfl⟩
  have modes : (∑ m ∈ waves an.cube, waveQuad p an (Aw b m) (Ψw b an m) m v₁ v₂ δ) ≤
      ∑ m ∈ waves an.cube, Layered.modeLower p (an.k₁ / 2) (an.k₂ / 2) (m.1 * an.k₁ + m.2 * an.k₂)
        (Aw b m) (Ψw b an m) m := by
    apply Finset.sum_le_sum
    intro m hm
    rw [hv₁, hv₂, hδ]
    exact modeLower_ge p an (Aw b m) (Ψw b an m) m (modeW_nonneg hp g (wok m hm))
      (tReal_nonneg' hp g m)
  have regroup : (∑ m ∈ waves an.cube, waveQuad p an (Aw b m) (Ψw b an m) m v₁ v₂ δ) =
      sumL an (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.1 : ℝ) ^ 2) * v₁ ^ 2 +
      sumL an (fun m => 2 * (lamR p an (Aw b m) (Ψw b an m) m * ((m.1 : ℝ) * (m.2 : ℝ)))) * (v₁ * v₂) +
      sumL an (fun m => lamR p an (Aw b m) (Ψw b an m) m * (m.2 : ℝ) ^ 2) * v₂ ^ 2 +
      sumL an (fun m => muR p an (Aw b m) (Ψw b an m) m) * δ ^ 2 +
      X₁ b an p * (δ * v₁) + X₂ b an p * (δ * v₂) - E₁ b an p * |δ * v₁| - E₂ b an p * |δ * v₂| := by
    unfold X₁ X₂ E₁ E₂ sumL
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    unfold waveQuad
    ring
  have two : sumL an (fun m => 2 * (lamR p an (Aw b m) (Ψw b an m) m * ((m.1 : ℝ) * (m.2 : ℝ)))) =
      2 * e01 b an p := by
    unfold e01 sumL; rw [← Finset.mul_sum]
  -- the matrix with sign-chosen mixed entries
  set a02 := X₁ b an p / 2 - sgn (δ * v₁) * E₁ b an p / 2 with ha02
  set a12 := X₂ b an p / 2 - sgn (δ * v₂) * E₂ b an p / 2 with ha12
  have quadEq : quad6 (e00 b an p) (e01 b an p) (e11 b an p) a02 a12 (e22 b an p) v₁ v₂ δ =
      2 * Real.pi * cReal p ^ 2 * δ ^ 2 +
        (∑ m ∈ waves an.cube, waveQuad p an (Aw b m) (Ψw b an m) m v₁ v₂ δ) -
        Hout b an p * (((tauZ b : ℝ) / Sz) ^ 2 * δ ^ 2 + 8 * Real.pi ^ 2 * (v₁ ^ 2 + v₂ ^ 2)) := by
    rw [regroup, two]
    have s1 := sgn_mul (δ * v₁)
    have s2 := sgn_mul (δ * v₂)
    unfold quad6 e00 e11 e22
    rw [ha02, ha12, ← s1, ← s2]
    ring
  -- the analytic bound in matrix form
  have gainQ : quad6 (e00 b an p) (e01 b an p) (e11 b an p) a02 a12 (e22 b an p) v₁ v₂ δ ≤
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
  have m22 : (m22F b an).Mem (e22 b an p) := by
    have hs := encl (muF b an) (fun m => muR p an (Aw b m) (Ψw b an m) m)
      (fun m hm => muF_mem' hp g (wok m hm))
    have h := FI.sub_mem (FI.add_mem (FI.mul_mem twoPiF_mem (FI.sq_mem (cF_mem hp g))) hs)
      (FI.mul_mem (FI.sq_mem (ptF_mem (tauZ b))) hout)
    unfold m22F e22 Hout
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
  have pd := pdOk_sound (surplusF b an lam) hpd (sub _ _ _ _ m00 g00) (sub _ _ _ _ m01 g01)
    (sub _ _ _ _ m11 g11) m02 m12 (sub _ _ _ _ m22 g22) v₁ v₂ δ
  have lin : quad6 (e00 b an p - (lam : ℝ) * p 0 ^ 2) (e01 b an p - (lam : ℝ) * (p 0 ^ 2 * p 2))
      (e11 b an p - (lam : ℝ) * ((p 0 * p 2) ^ 2 + p 1 ^ 2)) a02 a12
      (e22 b an p - (lam : ℝ) * cReal p ^ 2) v₁ v₂ δ =
      quad6 (e00 b an p) (e01 b an p) (e11 b an p) a02 a12 (e22 b an p) v₁ v₂ δ -
        (lam : ℝ) * layerGram p (an.k₁ / 2) (an.k₂ / 2) := by
    unfold layerGram
    rw [← hv₁, ← hv₂, ← hδ]
    unfold quad6
    ring
  rw [lin] at pd
  linarith

/-- Every bisected piece passes, so every point of the cell satisfies the
gain bound. -/
theorem splitOk_gain {an : Anchor} {lam : ℚ} :
    ∀ (d : ℕ) {b : Cell}, splitOk an lam d b = true → ∀ {p : Chart}, b.Mem p →
      (lam : ℝ) * layerGram p (an.k₁ / 2) (an.k₂ / 2) ≤
        2 * ac * (energy (chartPoint p) -
          energy (chartPoint (Layered.anchorChart p (an.k₁ / 2) (an.k₂ / 2))))
  | 0, b, ok, p, hp => leafOk_gain ok hp
  | d + 1, b, ok, p, hp => by
    simp only [splitOk, Bool.and_eq_true] at ok
    rcases two_closed_children b (widest b) (midpoint b (widest b)) p hp with h | h
    · exact splitOk_gain d ok.1 h
    · exact splitOk_gain d ok.2 h

end BccSharp.Coulomb.CompactCover.Layered.Fix
