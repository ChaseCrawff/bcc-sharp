import BccSharp.Cover.JLeafCheck
import BccSharp.TwoSite.ScreenedSeries

set_option autoImplicit false

/-! Witness families of the J-leaf energy support at a rational Ewald screening
`s > 0`.

`ScreenedSeries.energy_finite_lower_lex` bounds the energy below by cross modes
with prefactor `s` at the rate `π s²`, period modes of lex-positive indices
with prefactor `2s` at the same rate and wave modes of lex-positive indices
with prefactor `2/s²` at the rate `π/s²`, minus `2s + 2/s²`, all divided by
`2 a_c`. `physicalS` is exactly one such summand. The three witness families of
`BccSharp.Cover.JLeafTerms` carry over with the screening in the rates and the
prefactors; their data types (`DirectW`, `WaveW`, `PerspW`, `Witness`, `Item`)
are reused unchanged, and only the computed terms change:

* `directTermS`: `halfTangent_sound` gives `I − P y ≤ G(1/2, π y)` for all
  `y > 0`. At `y = s² q`, times the prefactor `m s` (`m = 1` for a cross mode,
  `2` for a period mode), the term has constant `m s I` and slope `−m s³ P`.
* `waveTermS`: the joint tangent of `(2/s²)(1 + cos 2πt) G(1, π q/s²)` with
  the log-phase secant of the s = 1 family. The anchor coefficient is
  `H = 2 exp(−x̄ + ℓ̄)/(x̄ s²)` and the `q` coefficient carries `π/s²`.
* `perspTermS`: near an extinction, `persp_lower` with weight `u s²` and
  `y = π q/s²`, divided by `s²`, gives `2uz − u² s² R(y) ≤ physicalS` with
  `R(y) = y eʸ/κ`. `R` is replaced by its secant over the box range of `q`
  (`secant_le`, the s = 1 secant with a general rate).

`support_soundS` bounds `(Σ terms − 2s − 2/s²)/(2 a_c)` by `energy` through
`energy_finite_lower_lex`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf.Screened
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.CompactCover.DirectRoute (offset lexPositive lex_ne diagonalsCheck
  reciprocalDistance reciprocalDistance_sound cross_distance_positive period_distance_positive
  reciprocalPositive endpoints)
open BccSharp.Coulomb.CompactCover.Stage2 (lower96 upper96 lower96_le le_upper96)

/-! ### The screened modes -/

/-- The screened series contribution that a term of this kind bounds. It is
one summand of `ScreenedSeries.energy_finite_lower_lex`, prefactor included:
a cross mode `s G(1/2, π s² Q)`, a period mode `2s G(1/2, π s² Q)` of a
lex-positive index (standing for `±n`), or a wave mode
`(2/s²)(1 + cos 2π n·f) G(1, π Q*/s²)` of a lex-positive index. -/
def physicalS (s : ℚ) (k : Kind) (n : IntVec) (p : Chart) : ℝ :=
  match k with
  | .cross => (s : ℝ) * gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 *
      quad (gram (chartPoint p).basis) (castVec n + (chartPoint p).offset))
  | .period => 2 * (s : ℝ) * gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 *
      quad (gram (chartPoint p).basis) (castVec n))
  | .wave => 2 / (s : ℝ) ^ 2 *
      ((1 + Real.cos (2 * Real.pi * dot (castVec n) (chartPoint p).offset)) *
        gKernel 1 (Real.pi * quad (gram (chartPoint p).basis)⁻¹ (castVec n) / (s : ℝ) ^ 2))

/-- A term is valid at screening `s` on a box when its slope is nonpositive
and it lies below its screened contribution at every valid point of the box. -/
def TermValid (s : ℚ) (b : Cell) (t : LinTerm) : Prop :=
  t.slope ≤ 0 ∧ ∀ p, b.Mem p → (chartPoint p).Valid → t.eval p ≤ physicalS s t.kind t.index p

theorem physicalS_cross (s : ℚ) (n : IntVec) {p : Chart} (hv : (chartPoint p).Valid) :
    physicalS s .cross n p =
      (s : ℝ) * gKernel (1/2) (Real.pi * ((s : ℝ) ^ 2 * termQ .cross n p)) ∧
      0 < termQ .cross n p := by
  obtain ⟨h0, h1⟩ := valid_diag hv
  have e := termQ_cross n p h0 h1
  refine ⟨?_, ?_⟩
  · show (s : ℝ) * gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 *
        quad (gram (chartPoint p).basis) (castVec n + (chartPoint p).offset)) = _
    rw [e, mul_assoc Real.pi]
  · rw [e]
    exact cross_distance_positive hv n

theorem physicalS_period (s : ℚ) (n : IntVec) (lex : lexPositive n) {p : Chart}
    (hv : (chartPoint p).Valid) :
    physicalS s .period n p =
      2 * (s : ℝ) * gKernel (1/2) (Real.pi * ((s : ℝ) ^ 2 * termQ .period n p)) ∧
      0 < termQ .period n p := by
  obtain ⟨h0, h1⟩ := valid_diag hv
  have e := termQ_period n p h0 h1
  refine ⟨?_, ?_⟩
  · show 2 * (s : ℝ) * gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 *
        quad (gram (chartPoint p).basis) (castVec n)) = _
    rw [e, mul_assoc Real.pi]
  · rw [e]
    exact period_distance_positive hv n lex

theorem physicalS_wave (s : ℚ) (n : IntVec) (lex : lexPositive n) {p : Chart}
    (hv : (chartPoint p).Valid) (hs : 0 < s) :
    physicalS s .wave n p = 2 / (s : ℝ) ^ 2 * ((1 + Real.cos (2 * Real.pi * phaseT n p)) *
      (Real.exp (-(Real.pi * termQ .wave n p / (s : ℝ) ^ 2)) /
        (Real.pi * termQ .wave n p / (s : ℝ) ^ 2))) ∧ 0 < termQ .wave n p := by
  obtain ⟨h0, h1⟩ := valid_diag hv
  have e := termQ_wave n p h0 h1
  have pos : 0 < termQ .wave n p := by rw [e]; exact reciprocalPositive hv (lex_ne lex)
  refine ⟨?_, pos⟩
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  have y : 0 < Real.pi * termQ .wave n p / (s : ℝ) ^ 2 := by positivity
  show 2 / (s : ℝ) ^ 2 * ((1 + Real.cos (2 * Real.pi * dot (castVec n) (chartPoint p).offset)) *
      gKernel 1 (Real.pi * quad (gram (chartPoint p).basis)⁻¹ (castVec n) / (s : ℝ) ^ 2)) = _
  rw [phaseT_eq, ← e, gKernel_one y]

/-! ### Direct (cross and period) witnesses -/

/-- The tangent `I − P y ≤ G(1/2, π y)` at `y = s² q`, times the prefactor
`m s`: constant `m s I`, slope `−m s³ P`. -/
def directTermS (s : ℚ) (w : DirectW) : LinTerm :=
  let tg := halfTangent w.root w.terms
  ⟨w.kind, w.index, w.mult * s * tg.intercept, -(w.mult * s ^ 3 * tg.penalty), 0⟩

def directCheckS (s : ℚ) (w : DirectW) : Bool := decide (0 < s) && w.check

theorem directS_valid (s : ℚ) (w : DirectW) (pi : piOk = true) (ok : directCheckS s w = true)
    (S : Cell) : TermValid s S (directTermS s w) := by
  obtain ⟨sok, wok⟩ := Bool.and_eq_true_iff.mp ok
  have hs : 0 < s := of_decide_eq_true sok
  obtain ⟨tok, lexOk⟩ := Bool.and_eq_true_iff.mp wok
  obtain ⟨pen, tan⟩ := halfTangent_sound w.root w.terms pi tok
  set tg := halfTangent w.root w.terms
  have multPos : (0 : ℚ) < w.mult := by unfold DirectW.mult; split <;> norm_num
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  refine ⟨?_, ?_⟩
  · show -(w.mult * s ^ 3 * tg.penalty) ≤ 0
    have := mul_nonneg (mul_nonneg multPos.le (pow_pos hs 3).le) pen
    linarith
  intro p _ hv
  unfold LinTerm.eval directTermS
  simp only
  cases hc : w.cross
  · have kind : w.kind = .period := by simp [DirectW.kind, hc]
    have mult : w.mult = 2 := by simp [DirectW.mult, hc]
    have lex : lexPositive w.index := by simpa [hc] using lexOk
    obtain ⟨phys, qpos⟩ := physicalS_period s w.index lex hv
    rw [kind, mult, phys]
    have b := tan _ (mul_pos (pow_pos sr 2) qpos)
    have bb := mul_le_mul_of_nonneg_left b (by positivity : (0 : ℝ) ≤ 2 * (s : ℝ))
    push_cast
    nlinarith [bb]
  · have kind : w.kind = .cross := by simp [DirectW.kind, hc]
    have mult : w.mult = 1 := by simp [DirectW.mult, hc]
    obtain ⟨phys, qpos⟩ := physicalS_cross s w.index hv
    rw [kind, mult, phys]
    have b := tan _ (mul_pos (pow_pos sr 2) qpos)
    have bb := mul_le_mul_of_nonneg_left b sr.le
    push_cast
    nlinarith [bb]

/-! ### Reciprocal witnesses with a log-phase secant -/

/-- Enclosure of `H = 2 exp(−x̄ + ℓ̄)/(x̄ s²)`. -/
def waveH (s : ℚ) (w : WaveW) (S : Cell) : Ball :=
  (Ball.exact (2 / (w.xbar * (s * s)))).mul (expBall (-w.xbar + w.lbar S))

def waveCq (s : ℚ) (w : WaveW) (S : Cell) : ℚ :=
  lower96 (((waveH s w S).mul ((Ball.exact (-(1 + 1 / w.xbar) / (s * s))).mul Constants.piInput)).lo)

def waveCt (s : ℚ) (w : WaveW) (S : Cell) : ℚ := lower96 ((waveH s w S).mul (Ball.exact w.b)).mid

def waveAt (s : ℚ) (w : WaveW) (S : Cell) (t : ℚ) : ℚ :=
  ((waveH s w S).mul (Ball.exact (2 + w.xbar + w.b * (t - w.tbar)))).lo - waveCt s w S * t

def waveKappa (s : ℚ) (w : WaveW) (S : Cell) : ℚ :=
  lower96 (min (waveAt s w S (w.L S)) (waveAt s w S (w.R S)))

def waveTermS (s : ℚ) (w : WaveW) (S : Cell) : LinTerm :=
  ⟨.wave, w.index, waveKappa s w S, waveCq s w S, waveCt s w S⟩

/-- The s = 1 conditions of `WaveW.Good`, with `0 < s` and the screened `q`
coefficient. -/
def WaveGoodS (s : ℚ) (w : WaveW) (S : Cell) : Prop :=
  0 < s ∧ 0 < w.xbar ∧ lexPositive w.index ∧ (w.k S : ℚ) - 1 / 2 < w.L S ∧
    w.R S < (w.k S : ℚ) + 1 / 2 ∧
    expOk (-w.xbar + w.lbar S) = true ∧ expOk (w.ell S (w.L S)) = true ∧
    expOk (w.ell S (w.R S)) = true ∧ cosGuard (w.L S) (w.k S) = true ∧
    cosGuard (w.R S) (w.k S) = true ∧
    (expBall (w.ell S (w.L S))).hi ≤ onePlusCosLo (w.L S) (w.k S) ∧
    (expBall (w.ell S (w.R S))).hi ≤ onePlusCosLo (w.R S) (w.k S) ∧ waveCq s w S ≤ 0

instance (s : ℚ) (w : WaveW) (S : Cell) : Decidable (WaveGoodS s w S) := by
  unfold WaveGoodS; infer_instance

def waveCheckS (s : ℚ) (w : WaveW) (S : Cell) : Bool := decide (WaveGoodS s w S)

theorem waveS_valid (s : ℚ) (w : WaveW) (S : Cell) (ok : waveCheckS s w S = true) :
    TermValid s S (waveTermS s w S) := by
  have g : WaveGoodS s w S := of_decide_eq_true ok
  obtain ⟨spos, xpos, lex, kL, kR, eH, eL, eR, gL, gR, pL, pR, cqNeg⟩ := g
  refine ⟨cqNeg, ?_⟩
  intro p hp hv
  obtain ⟨phys, qpos⟩ := physicalS_wave s w.index lex hv spos
  obtain ⟨tL, tR⟩ := window_sound S w.index hp
  have xb : (0 : ℝ) < w.xbar := by exact_mod_cast xpos
  have xne : (w.xbar : ℝ) ≠ 0 := xb.ne'
  have sr : (0 : ℝ) < s := by exact_mod_cast spos
  have sne : (s : ℝ) ≠ 0 := sr.ne'
  have s2 : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  -- Names for the real quantities.
  obtain ⟨q, hq⟩ : ∃ q, q = termQ .wave w.index p := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = phaseT w.index p := ⟨_, rfl⟩
  rw [← hq] at phys qpos
  rw [← ht] at phys tL tR
  obtain ⟨y, hy⟩ : ∃ y, y = Real.pi * q / (s : ℝ) ^ 2 := ⟨_, rfl⟩
  rw [← hy] at phys
  have ypos : 0 < y := by rw [hy]; positivity
  have tL' : (w.L S : ℝ) ≤ t := by simpa [WaveW.L] using tL
  have tR' : t ≤ (w.R S : ℝ) := by simpa [WaveW.R] using tR
  -- The exponential-affine phase bound on the window (as at s = 1).
  have ellEq (u : ℚ) : ((w.ell S u : ℚ) : ℝ) = (w.a : ℝ) + (w.b : ℝ) * ((u : ℝ) - (w.c S : ℝ)) := by
    simp [WaveW.ell]
  have endL : Real.exp ((w.a : ℝ) + (w.b : ℝ) * ((w.L S : ℝ) - (w.c S : ℝ))) ≤
      1 + Real.cos (2 * Real.pi * (w.L S : ℝ)) := by
    rw [← ellEq]
    exact ((endpoints (expBall_contains _ eL)).2.trans (by exact_mod_cast pL)).trans
      (onePlusCosLo_sound _ _ gL)
  have endR : Real.exp ((w.a : ℝ) + (w.b : ℝ) * ((w.R S : ℝ) - (w.c S : ℝ))) ≤
      1 + Real.cos (2 * Real.pi * (w.R S : ℝ)) := by
    rw [← ellEq]
    exact ((endpoints (expBall_contains _ eR)).2.trans (by exact_mod_cast pR)).trans
      (onePlusCosLo_sound _ _ gR)
  have kLr : ((w.k S : ℤ) : ℝ) - 1 / 2 < (w.L S : ℝ) := by
    have h : ((((w.k S : ℤ) : ℚ) - 1 / 2 : ℚ) : ℝ) < ((w.L S : ℚ) : ℝ) := Rat.cast_lt.mpr kL
    push_cast at h
    exact h
  have kRr : (w.R S : ℝ) < ((w.k S : ℤ) : ℝ) + 1 / 2 := by
    have h : ((w.R S : ℚ) : ℝ) < ((((w.k S : ℤ) : ℚ) + 1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr kR
    push_cast at h
    exact h
  have phase := phase_secant (w.k S) (w.L S) (w.R S) w.a w.b (w.c S) t kLr kRr tL' tR' endL endR
  -- Joint tangent of `G₁` with the phase factor, at `y = π q/s²`.
  have tang := g1_tangent (w.xbar : ℝ) y
    ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))
    ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) xb ypos
  have g1nn : 0 ≤ Real.exp (-y) / y := by positivity
  have lower1 : 2 / (s : ℝ) ^ 2 *
      (Real.exp (-y + ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ)))) / y) ≤
      physicalS s .wave w.index p := by
    rw [phys, Real.exp_add]
    have m := mul_le_mul_of_nonneg_right phase g1nn
    have e : Real.exp (-y) * Real.exp ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) / y =
        Real.exp ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) * (Real.exp (-y) / y) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left m (by positivity)
  -- Real value of the anchor coefficient.
  obtain ⟨Hr, hHr⟩ : ∃ Hr : ℝ, Hr = 2 / ((w.xbar : ℝ) * (s : ℝ) ^ 2) * Real.exp (-(w.xbar : ℝ) +
      ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))) := ⟨_, rfl⟩
  have hH : (waveH s w S).Contains Hr := by
    have m := Ball.contains_mul (Ball.contains_exact (2 / (w.xbar * (s * s))))
      (expBall_contains _ eH)
    have e : Hr = ((2 / (w.xbar * (s * s)) : ℚ) : ℝ) * Real.exp ((-w.xbar + w.lbar S : ℚ) : ℝ) := by
      rw [hHr]
      simp only [WaveW.lbar]
      push_cast
      ring
    rw [e]
    exact m
  have plane : Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * (t - (w.tbar : ℝ))) +
      Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) * q ≤
      physicalS s .wave w.index p := by
    have e : Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * (t - (w.tbar : ℝ))) +
        Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) * q =
        2 / (s : ℝ) ^ 2 * (Real.exp (-(w.xbar : ℝ) +
          ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))) / (w.xbar : ℝ) *
          (1 + (-1 - 1 / (w.xbar : ℝ)) * (y - (w.xbar : ℝ)) +
            (((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) -
              ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))))) := by
      rw [hHr, hy]
      field_simp
      ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left tang (by positivity)).trans lower1
  -- The `q` coefficient.
  have cqLe : (waveCq s w S : ℝ) ≤ Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) := by
    have m := Ball.contains_mul hH (Ball.contains_mul
      (Ball.contains_exact (-(1 + 1 / w.xbar) / (s * s))) Constants.piInput_sound)
    have lo := (endpoints m).1
    have r := (Rat.cast_le (K := ℝ)).mpr (lower96_le
      (((waveH s w S).mul ((Ball.exact (-(1 + 1 / w.xbar) / (s * s))).mul Constants.piInput)).lo))
    have e : ((waveCq s w S : ℚ) : ℝ) = ((lower96
        (((waveH s w S).mul ((Ball.exact (-(1 + 1 / w.xbar) / (s * s))).mul
          Constants.piInput)).lo) : ℚ) : ℝ) := rfl
    rw [e]
    refine r.trans (lo.trans_eq ?_)
    push_cast
    ring
  -- The constant and phase coefficients at both window ends.
  have atLe (u : ℚ) : ((waveAt s w S u : ℚ) : ℝ) + (waveCt s w S : ℝ) * u ≤
      Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * ((u : ℝ) - (w.tbar : ℝ))) := by
    have m := Ball.contains_mul hH (Ball.contains_exact (2 + w.xbar + w.b * (u - w.tbar)))
    have lo := (endpoints m).1
    have e : ((waveAt s w S u : ℚ) : ℝ) =
        (((waveH s w S).mul (Ball.exact (2 + w.xbar + w.b * (u - w.tbar)))).lo : ℝ) -
          (waveCt s w S : ℝ) * u := by
      simp only [waveAt]
      push_cast
      ring
    rw [e]
    have e2 : Hr * ((((2 + w.xbar + w.b * (u - w.tbar)) : ℚ)) : ℝ) =
        Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * ((u : ℝ) - (w.tbar : ℝ))) := by push_cast; ring
    linarith
  have kap (u : ℚ) (hu : u = w.L S ∨ u = w.R S) :
      ((waveKappa s w S : ℚ) : ℝ) ≤ (waveAt s w S u : ℝ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr
      (lower96_le (min (waveAt s w S (w.L S)) (waveAt s w S (w.R S))))
    have e : ((waveKappa s w S : ℚ) : ℝ) =
        ((lower96 (min (waveAt s w S (w.L S)) (waveAt s w S (w.R S))) : ℚ) : ℝ) := rfl
    rw [e]
    rcases hu with rfl | rfl
    · exact h1.trans (Rat.cast_le.mpr (min_le_left _ _))
    · exact h1.trans (Rat.cast_le.mpr (min_le_right _ _))
  have mid : (waveKappa s w S : ℝ) + (waveCt s w S : ℝ) * t ≤
      (Hr * (2 + (w.xbar : ℝ) - (w.b : ℝ) * (w.tbar : ℝ))) + (Hr * (w.b : ℝ)) * t := by
    apply affine_between (w.L S) (w.R S) t _ _ _ _ tL' tR'
    · have := atLe (w.L S); have := kap (w.L S) (Or.inl rfl); nlinarith
    · have := atLe (w.R S); have := kap (w.R S) (Or.inr rfl); nlinarith
  have cqq := mul_le_mul_of_nonneg_right cqLe qpos.le
  show (waveKappa s w S : ℝ) + (waveCq s w S : ℝ) * termQ .wave w.index p +
    (waveCt s w S : ℝ) * phaseT w.index p ≤ physicalS s .wave w.index p
  rw [← hq, ← ht]
  nlinarith [plane, mid, cqq]

/-! ### The secant of `ρ q e^{ρ q}` -/

private theorem mul_exp_mono' {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x * Real.exp x ≤ y * Real.exp y :=
  mul_le_mul hxy (Real.exp_le_exp.mpr hxy) (Real.exp_pos _).le (hx.trans hxy)

/-- Rational upper bound for `ρ q exp(ρ q)/κ` at a rational `q ≥ 0`, from a
rational `r ≥ ρ`. At `r = π̄` it is the s = 1 `PerspW.A`. -/
def secA (r κ q : ℚ) : ℚ := ((Ball.exact (r * q / κ)).mul (expBall (r * q))).hi

def secBetaRaw (r κ lo hi : ℚ) : ℚ :=
  if lo < hi then max 0 ((secA r κ hi - secA r κ lo) / (hi - lo)) else 0

/-- Secant slope and intercept, rounded up to the 2⁻⁹⁶ grid. Rounding both up
keeps `α + β q` above the secant for `q ≥ 0`. -/
def secBeta (r κ lo hi : ℚ) : ℚ := upper96 (secBetaRaw r κ lo hi)

def secAlpha (r κ lo hi : ℚ) : ℚ := upper96 (secA r κ lo - secBeta r κ lo hi * lo)

theorem secBeta_nonneg (r κ lo hi : ℚ) : 0 ≤ secBeta r κ lo hi := by
  have raw : 0 ≤ secBetaRaw r κ lo hi := by
    unfold secBetaRaw
    split
    · exact le_max_left _ _
    · exact le_rfl
  exact raw.trans (le_upper96 _)

theorem secA_ge {ρ : ℝ} {r κ q : ℚ} (hρ : 0 ≤ ρ) (hr : ρ ≤ r) (hq : 0 ≤ q) (hk : 0 < κ)
    (he : expOk (r * q) = true) : ρ * q * Real.exp (ρ * q) / κ ≤ (secA r κ q : ℝ) := by
  have m := Ball.contains_mul (Ball.contains_exact (r * q / κ)) (expBall_contains _ he)
  have hi := (endpoints m).2
  have kpos : (0 : ℝ) < κ := by exact_mod_cast hk
  have qnn : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have rq : ρ * q ≤ (r : ℝ) * q := mul_le_mul_of_nonneg_right hr qnn
  have mono := mul_exp_mono' (mul_nonneg hρ qnn) rq
  have e : (((r * q / κ : ℚ) : ℝ)) * Real.exp ((r * q : ℚ) : ℝ) =
      (r : ℝ) * q * Real.exp ((r : ℝ) * q) / (κ : ℝ) := by
    push_cast; ring
  rw [e] at hi
  exact (div_le_div_of_nonneg_right mono kpos.le).trans hi

/-- `x ↦ ρ x e^{ρ x}/κ` lies below `secAlpha + secBeta x` on `[lo, hi] ⊂ [0, ∞)`. -/
theorem secant_le {ρ : ℝ} {r κ lo hi : ℚ} {x : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r) (hk : 0 < κ)
    (h0 : 0 ≤ lo) (hlh : lo ≤ hi) (elo : expOk (r * lo) = true) (ehi : expOk (r * hi) = true)
    (hx0 : (lo : ℝ) ≤ x) (hx1 : x ≤ hi) :
    ρ * x * Real.exp (ρ * x) / κ ≤ (secAlpha r κ lo hi : ℝ) + (secBeta r κ lo hi : ℝ) * x := by
  have kr : (0 : ℝ) < κ := by exact_mod_cast hk
  have ρne : ρ ≠ 0 := hρ.ne'
  have Alo := secA_ge hρ.le hr h0 hk elo
  have Ahi := secA_ge hρ.le hr (h0.trans hlh) hk ehi
  have lo0r : (0 : ℝ) ≤ lo := by exact_mod_cast h0
  have sec := secant_mul_exp (ρ * lo) (ρ * hi) (ρ * x) (mul_nonneg hρ.le lo0r)
    (mul_le_mul_of_nonneg_left hx0 hρ.le) (mul_le_mul_of_nonneg_left hx1 hρ.le)
  by_cases strict : lo < hi
  · have beq : secBetaRaw r κ lo hi = max 0 ((secA r κ hi - secA r κ lo) / (hi - lo)) := by
      simp [secBetaRaw, strict]
    have bup : (secBetaRaw r κ lo hi : ℝ) ≤ (secBeta r κ lo hi : ℝ) :=
      Rat.cast_le.mpr (le_upper96 _)
    have wpos : (0 : ℝ) < (hi : ℝ) - (lo : ℝ) := by
      have : ((lo : ℚ) : ℝ) < (hi : ℝ) := by exact_mod_cast strict
      linarith
    have bge : ((secA r κ hi : ℝ) - (secA r κ lo : ℝ)) / ((hi : ℝ) - (lo : ℝ)) ≤
        (secBeta r κ lo hi : ℝ) := by
      refine le_trans ?_ bup
      rw [beq]
      have c : ((((secA r κ hi - secA r κ lo) / (hi - lo) : ℚ)) : ℝ) ≤
          ((max 0 ((secA r κ hi - secA r κ lo) / (hi - lo)) : ℚ) : ℝ) :=
        Rat.cast_le.mpr (le_max_right _ _)
      have e : ((((secA r κ hi - secA r κ lo) / (hi - lo) : ℚ)) : ℝ) =
          ((secA r κ hi : ℝ) - (secA r κ lo : ℝ)) / ((hi : ℝ) - (lo : ℝ)) := by
        push_cast; ring
      rw [← e]
      exact c
    -- Divide the secant inequality by `ρ²`.
    have sec' : x * Real.exp (ρ * x) * ((hi : ℝ) - (lo : ℝ)) ≤
        ((hi : ℝ) - x) * ((lo : ℝ) * Real.exp (ρ * lo)) +
          (x - (lo : ℝ)) * ((hi : ℝ) * Real.exp (ρ * hi)) := by
      have e1 : ρ * x * Real.exp (ρ * x) * (ρ * (hi : ℝ) - ρ * (lo : ℝ)) =
          ρ ^ 2 * (x * Real.exp (ρ * x) * ((hi : ℝ) - (lo : ℝ))) := by ring
      have e2 : (ρ * (hi : ℝ) - ρ * x) * (ρ * (lo : ℝ) * Real.exp (ρ * lo)) +
          (ρ * x - ρ * (lo : ℝ)) * (ρ * (hi : ℝ) * Real.exp (ρ * hi)) =
          ρ ^ 2 * (((hi : ℝ) - x) * ((lo : ℝ) * Real.exp (ρ * lo)) +
            (x - (lo : ℝ)) * ((hi : ℝ) * Real.exp (ρ * hi))) := by ring
      rw [e1, e2] at sec
      exact le_of_mul_le_mul_left sec (by positivity)
    have AloR : (lo : ℝ) * Real.exp (ρ * lo) ≤ (κ : ℝ) * (secA r κ lo : ℝ) / ρ := by
      rw [le_div_iff₀ hρ]
      have := (div_le_iff₀ kr).mp Alo
      linarith
    have AhiR : (hi : ℝ) * Real.exp (ρ * hi) ≤ (κ : ℝ) * (secA r κ hi : ℝ) / ρ := by
      rw [le_div_iff₀ hρ]
      have := (div_le_iff₀ kr).mp Ahi
      linarith
    have sec2 : x * Real.exp (ρ * x) * ((hi : ℝ) - (lo : ℝ)) ≤
        ((hi : ℝ) - x) * ((κ : ℝ) * (secA r κ lo : ℝ) / ρ) +
          (x - (lo : ℝ)) * ((κ : ℝ) * (secA r κ hi : ℝ) / ρ) := by
      have a1 := mul_le_mul_of_nonneg_left AloR (sub_nonneg.mpr hx1)
      have a2 := mul_le_mul_of_nonneg_left AhiR (sub_nonneg.mpr hx0)
      linarith
    -- The secant line lies below `alpha + beta x`.
    have line : ((hi : ℝ) - x) * (secA r κ lo : ℝ) + (x - (lo : ℝ)) * (secA r κ hi : ℝ) ≤
        ((secAlpha r κ lo hi : ℝ) + (secBeta r κ lo hi : ℝ) * x) * ((hi : ℝ) - (lo : ℝ)) := by
      have hal : (secA r κ lo : ℝ) - (secBeta r κ lo hi : ℝ) * (lo : ℝ) ≤
          (secAlpha r κ lo hi : ℝ) := by
        have := (Rat.cast_le (K := ℝ)).mpr (le_upper96 (secA r κ lo - secBeta r κ lo hi * lo))
        push_cast at this
        exact this
      have := (div_le_iff₀ wpos).mp bge
      have h := mul_le_mul_of_nonneg_left this (sub_nonneg.mpr hx0)
      have h3 := mul_le_mul_of_nonneg_right hal wpos.le
      nlinarith [h, h3]
    have final : ρ * x * Real.exp (ρ * x) * ((hi : ℝ) - (lo : ℝ)) ≤
        (κ : ℝ) * (((secAlpha r κ lo hi : ℝ) + (secBeta r κ lo hi : ℝ) * x) *
          ((hi : ℝ) - (lo : ℝ))) := by
      have := mul_le_mul_of_nonneg_left sec2 hρ.le
      have e : ρ * (((hi : ℝ) - x) * ((κ : ℝ) * (secA r κ lo : ℝ) / ρ) +
          (x - (lo : ℝ)) * ((κ : ℝ) * (secA r κ hi : ℝ) / ρ)) =
          (κ : ℝ) * (((hi : ℝ) - x) * (secA r κ lo : ℝ) +
            (x - (lo : ℝ)) * (secA r κ hi : ℝ)) := by
        field_simp
      rw [e] at this
      have h2 := mul_le_mul_of_nonneg_left line kr.le
      linarith [this, h2]
    rw [div_le_iff₀ kr]
    have h2 : ρ * x * Real.exp (ρ * x) * ((hi : ℝ) - (lo : ℝ)) ≤
        ((secAlpha r κ lo hi : ℝ) + (secBeta r κ lo hi : ℝ) * x) * (κ : ℝ) *
          ((hi : ℝ) - (lo : ℝ)) := by
      linarith [final]
    exact le_of_mul_le_mul_right h2 wpos
  · have same : lo = hi := le_antisymm hlh (not_lt.mp strict)
    have xeq : x = (lo : ℝ) := le_antisymm (hx1.trans_eq (by rw [same])) hx0
    have b0 : secBeta r κ lo hi = 0 := by simp [secBeta, secBetaRaw, strict, upper96]
    have hal : (secA r κ lo : ℝ) ≤ (secAlpha r κ lo hi : ℝ) := by
      have h := le_upper96 (secA r κ lo - secBeta r κ lo hi * lo)
      have e : secAlpha r κ lo hi = upper96 (secA r κ lo - secBeta r κ lo hi * lo) := rfl
      rw [e, b0, zero_mul, sub_zero]
      rw [b0, zero_mul, sub_zero] at h
      exact_mod_cast h
    rw [xeq, b0]
    push_cast
    linarith [Alo, hal]

/-! ### Reciprocal witnesses near an extinction -/

/-- Rational upper bound `π̄/s²` of the reciprocal rate `π/s²`. -/
def perspRate (s : ℚ) : ℚ := piUp / (s * s)

def perspAlpha (s : ℚ) (w : PerspW) (S : Cell) : ℚ :=
  secAlpha (perspRate s) (w.kappa S) (w.qlo S) (w.qhi S)

def perspBeta (s : ℚ) (w : PerspW) (S : Cell) : ℚ :=
  secBeta (perspRate s) (w.kappa S) (w.qlo S) (w.qhi S)

/-- `2u(t − z₀) − u² s² (α + β q)`, the perspective bound with `R` replaced by
its secant. -/
def perspTermS (s : ℚ) (w : PerspW) (S : Cell) : LinTerm :=
  ⟨.wave, w.index, -2 * w.u * w.z0 S - w.u ^ 2 * (s * s) * perspAlpha s w S,
    -(w.u ^ 2 * (s * s) * perspBeta s w S), 2 * w.u⟩

/-- The s = 1 conditions of `PerspW.Good`, with `0 < s` and the exponential
guards at the screened rate. -/
def PerspGoodS (s : ℚ) (w : PerspW) (S : Cell) : Prop :=
  0 < s ∧ lexPositive w.index ∧ diagonalsCheck S = true ∧ 0 < w.d S ∧ w.d S ≤ 1 / 2 ∧
    sinGuard (w.d S) = true ∧ 0 < sinLo (w.d S) ∧ 0 < w.kappa S ∧ 0 ≤ w.qlo S ∧
    w.qlo S ≤ w.qhi S ∧ expOk (perspRate s * w.qlo S) = true ∧
    expOk (perspRate s * w.qhi S) = true ∧ piUpOk = true

instance (s : ℚ) (w : PerspW) (S : Cell) : Decidable (PerspGoodS s w S) := by
  unfold PerspGoodS; infer_instance

def perspCheckS (s : ℚ) (w : PerspW) (S : Cell) : Bool := decide (PerspGoodS s w S)

theorem perspS_valid (s : ℚ) (w : PerspW) (S : Cell) (ok : perspCheckS s w S = true) :
    TermValid s S (perspTermS s w S) := by
  have g : PerspGoodS s w S := of_decide_eq_true ok
  obtain ⟨spos, lex, diag, dpos, dhalf, sg, spos', kpos, qlo0, qlohi, elo, ehi, pu⟩ := g
  have sr : (0 : ℝ) < s := by exact_mod_cast spos
  have s2 : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · show -(w.u ^ 2 * (s * s) * perspBeta s w S) ≤ 0
    have hb := secBeta_nonneg (perspRate s) (w.kappa S) (w.qlo S) (w.qhi S)
    have : 0 ≤ w.u ^ 2 * (s * s) * perspBeta s w S :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (mul_self_nonneg _)) hb
    linarith
  intro p hp hv
  obtain ⟨phys, qpos⟩ := physicalS_wave s w.index lex hv spos
  obtain ⟨tL, tR⟩ := window_sound S w.index hp
  obtain ⟨h0, h1⟩ := valid_diag hv
  have qrange := endpoints (reciprocalDistance_sound hp diag w.index)
  have qe : quad (gram (chartBasis p))⁻¹ (castVec w.index) = termQ .wave w.index p :=
    (termQ_wave w.index p h0 h1).symm
  rw [qe] at qrange
  obtain ⟨q, hq⟩ : ∃ q, q = termQ .wave w.index p := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = phaseT w.index p := ⟨_, rfl⟩
  rw [← hq] at phys qpos qrange
  rw [← ht] at phys tL tR
  obtain ⟨y, hy⟩ : ∃ y, y = Real.pi * q / (s : ℝ) ^ 2 := ⟨_, rfl⟩
  rw [← hy] at phys
  have ypos : 0 < y := by rw [hy]; positivity
  have qlo : (w.qlo S : ℝ) ≤ q := qrange.1
  have qhi : q ≤ (w.qhi S : ℝ) := qrange.2
  -- The distance to the extinction (as at s = 1).
  have zbound : |t - (w.z0 S : ℝ)| ≤ (w.d S : ℝ) := by
    have dL : |(w.L S : ℝ) - (w.z0 S : ℝ)| ≤ (w.d S : ℝ) := by
      have := le_max_left |w.L S - w.z0 S| |w.R S - w.z0 S|
      exact_mod_cast this
    have dR : |(w.R S : ℝ) - (w.z0 S : ℝ)| ≤ (w.d S : ℝ) := by
      have := le_max_right |w.L S - w.z0 S| |w.R S - w.z0 S|
      exact_mod_cast this
    have tL' : (w.L S : ℝ) ≤ t := by simpa [PerspW.L] using tL
    have tR' : t ≤ (w.R S : ℝ) := by simpa [PerspW.R] using tR
    rw [abs_le] at dL dR ⊢
    constructor <;> linarith [dL.1, dL.2, dR.1, dR.2]
  -- The secant of `R(π q/s²)` over `[qlo, qhi]`.
  have kr : (0 : ℝ) < w.kappa S := by exact_mod_cast kpos
  have rate : Real.pi / (s : ℝ) ^ 2 ≤ (perspRate s : ℝ) := by
    have h := pi_le_piUp pu
    have e : ((perspRate s : ℚ) : ℝ) = (piUp : ℝ) / (s : ℝ) ^ 2 := by
      simp only [perspRate]; push_cast; ring
    rw [e]
    exact div_le_div_of_nonneg_right h s2.le
  have Rsec := secant_le (ρ := Real.pi / (s : ℝ) ^ 2) (by positivity) rate kpos qlo0 qlohi
    elo ehi qlo qhi
  have ye : Real.pi / (s : ℝ) ^ 2 * q = y := by rw [hy]; ring
  rw [ye] at Rsec
  -- The perspective bound with weight `u s²`.
  have zeq : t = (t - (w.z0 S : ℝ)) + ((w.k S : ℤ) : ℝ) + 1 / 2 := by
    simp only [PerspW.z0]; push_cast; ring
  have kd : (w.kappa S : ℝ) * (w.d S : ℝ) ^ 2 ≤ 4 * Real.sin (Real.pi * (w.d S : ℝ)) ^ 2 := by
    have sl := sinLo_sound (w.d S) sg
    have sp : (0 : ℝ) < sinLo (w.d S) := by exact_mod_cast spos'
    have dp : (0 : ℝ) < w.d S := by exact_mod_cast dpos
    have kle : ((w.kappa S : ℚ) : ℝ) ≤ 4 * (sinLo (w.d S) : ℝ) ^ 2 / (w.d S : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr (lower96_le (4 * (sinLo (w.d S)) ^ 2 / (w.d S) ^ 2))
      have e : ((w.kappa S : ℚ) : ℝ) =
          ((lower96 (4 * (sinLo (w.d S)) ^ 2 / (w.d S) ^ 2) : ℚ) : ℝ) := rfl
      rw [e]
      refine this.trans (le_of_eq ?_)
      push_cast; ring
    have sq := pow_le_pow_left₀ sp.le sl 2
    rw [le_div_iff₀ (by positivity)] at kle
    linarith [kle, sq]
  have pl := persp_lower (w.k S) (t - (w.z0 S : ℝ)) (w.d S) (w.kappa S) ((w.u : ℝ) * (s : ℝ) ^ 2) y
    (by exact_mod_cast dpos)
    (by have h := (Rat.cast_le (K := ℝ)).mpr dhalf; push_cast at h; exact h)
    zbound kr kd ypos
  rw [← zeq] at pl
  -- Divide by `s²`.
  obtain ⟨A, hA⟩ : ∃ A, A = (1 + Real.cos (2 * Real.pi * t)) * (Real.exp (-y) / y) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = y * Real.exp y / (w.kappa S : ℝ) := ⟨_, rfl⟩
  rw [← hA] at pl phys
  rw [← hR] at pl Rsec
  have key : (s : ℝ) ^ 2 * (2 * (w.u : ℝ) * (t - (w.z0 S : ℝ)) -
      (w.u : ℝ) ^ 2 * ((s : ℝ) * (s : ℝ)) * R) ≤ 2 * A := by
    have e : (s : ℝ) ^ 2 * (2 * (w.u : ℝ) * (t - (w.z0 S : ℝ)) -
        (w.u : ℝ) ^ 2 * ((s : ℝ) * (s : ℝ)) * R) =
        2 * ((w.u : ℝ) * (s : ℝ) ^ 2) * (t - (w.z0 S : ℝ)) - ((w.u : ℝ) * (s : ℝ) ^ 2) ^ 2 * R := by
      ring
    rw [e]
    exact pl
  have key2 : 2 * (w.u : ℝ) * (t - (w.z0 S : ℝ)) - (w.u : ℝ) ^ 2 * ((s : ℝ) * (s : ℝ)) * R ≤
      2 / (s : ℝ) ^ 2 * A := by
    rw [div_mul_eq_mul_div, le_div_iff₀ s2, mul_comm]
    exact key
  have u2 : (0 : ℝ) ≤ (w.u : ℝ) ^ 2 * ((s : ℝ) * (s : ℝ)) := by positivity
  have hRs := mul_le_mul_of_nonneg_left Rsec u2
  show ((-2 * w.u * w.z0 S - w.u ^ 2 * (s * s) * perspAlpha s w S : ℚ) : ℝ) +
      ((-(w.u ^ 2 * (s * s) * perspBeta s w S) : ℚ) : ℝ) * termQ .wave w.index p +
      ((2 * w.u : ℚ) : ℝ) * phaseT w.index p ≤ physicalS s .wave w.index p
  rw [← hq, ← ht, phys]
  simp only [perspAlpha, perspBeta]
  push_cast
  nlinarith [key2, hRs]

/-! ### Items and the support bound -/

def witnessTermS (s : ℚ) (S : Cell) : Witness → LinTerm
  | .direct w => directTermS s w
  | .wave w => waveTermS s w S
  | .persp w => perspTermS s w S

def witnessCheckS (s : ℚ) (S : Cell) : Witness → Bool
  | .direct w => directCheckS s w
  | .wave w => waveCheckS s w S
  | .persp w => perspCheckS s w S

theorem witness_validS (s : ℚ) (S : Cell) (pi : piOk = true) (x : Witness)
    (ok : witnessCheckS s S x = true) : TermValid s S (witnessTermS s S x) := by
  cases x with
  | direct w => exact directS_valid s w pi ok S
  | wave w => exact waveS_valid s w S ok
  | persp w => exact perspS_valid s w S ok

/-- A literal term is accepted at screening `s` when its witness passes the
screened check and recomputes exactly the literal. -/
def itemOkS (s : ℚ) (S : Cell) (it : Item) : Bool :=
  witnessCheckS s S it.wit && linEq (witnessTermS s S it.wit) it.lin

theorem item_validS (s : ℚ) (S : Cell) (pi : piOk = true) (it : Item)
    (ok : itemOkS s S it = true) : TermValid s S it.lin := by
  obtain ⟨c, e⟩ := Bool.and_eq_true_iff.mp ok
  rw [← linEq_sound e]
  exact witness_validS s S pi it.wit c

private theorem sum_by_kindS (l : List LinTerm) (g : LinTerm → ℝ) :
    (l.map g).sum = ((l.filter (fun t => decide (t.kind = .cross))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .period))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .wave))).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hk : a.kind <;> simp [hk, ih] <;> ring

private theorem filter_kind_sumS (l : List LinTerm) (k : Kind) (G : Kind → IntVec → ℝ) :
    ((l.filter (fun t => decide (t.kind = k))).map (fun t => G t.kind t.index)).sum =
      ((kindIdx k l).map (fun n => G k n)).sum := by
  induction l with
  | nil => simp [kindIdx]
  | cons a l ih =>
    by_cases hk : a.kind = k
    · simp [hk, kindIdx] at ih ⊢
      rw [ih]
    · simp [hk, kindIdx] at ih ⊢
      exact ih

/-- **Screened support bound.** For terms valid at screening `s` on `S`, with
distinct indices per kind and lex-positive period and wave indices, the sum of
the terms minus `2s + 2/s²`, divided by `2 a_c`, is at most the energy at every
valid point of `S`. Proved from `ScreenedSeries.energy_finite_lower_lex`. -/
theorem support_soundS (s : ℚ) (hs : 0 < s) (S : Cell) (lins : List LinTerm)
    (valid : ∀ t ∈ lins, TermValid s S t) (hst : structureOk lins = true) (p : Chart)
    (hp : S.Mem p) (hv : (chartPoint p).Valid) :
    (linSum lins p - (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2)) / (2 * ac) ≤ energy (chartPoint p) := by
  have st := of_decide_eq_true hst
  obtain ⟨ncross, nperiod, nwave, lexP, lexW⟩ := st
  set q := chartPoint p with hq
  -- Each term lies below its screened contribution.
  have step1 : linSum lins p ≤ (lins.map (fun t => physicalS s t.kind t.index p)).sum := by
    unfold linSum
    apply List.sum_le_sum
    intro t ht
    exact (valid t ht).2 p hp hv
  have fc := filter_kind_sumS lins .cross (fun k n => physicalS s k n p)
  have fp := filter_kind_sumS lins .period (fun k n => physicalS s k n p)
  have fw := filter_kind_sumS lins .wave (fun k n => physicalS s k n p)
  rw [sum_by_kindS lins, fc, fp, fw] at step1
  -- Convert the three list sums into the finite sums of `energy_finite_lower_lex`.
  set X := (kindIdx .cross lins).toFinset
  set P := (kindIdx .period lins).toFinset
  set W := (kindIdx .wave lins).toFinset
  have cross : ((kindIdx .cross lins).map (fun n => physicalS s .cross n p)).sum =
      (s : ℝ) * ∑ n ∈ X,
        gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 * quad (gram q.basis) (castVec n + q.offset)) := by
    rw [Finset.mul_sum, List.sum_toFinset _ ncross]
    rfl
  have period : ((kindIdx .period lins).map (fun n => physicalS s .period n p)).sum =
      2 * (s : ℝ) * ∑ n ∈ P,
        gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 * quad (gram q.basis) (castVec n)) := by
    rw [Finset.mul_sum, List.sum_toFinset _ nperiod]
    rfl
  have wave : ((kindIdx .wave lins).map (fun n => physicalS s .wave n p)).sum =
      2 / (s : ℝ) ^ 2 * ∑ n ∈ W, (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
        gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / (s : ℝ) ^ 2) := by
    rw [Finset.mul_sum, List.sum_toFinset _ nwave]
    rfl
  rw [cross, period, wave] at step1
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  have fl := ScreenedSeries.energy_finite_lower_lex q hv (s : ℝ) sr X P W
    (fun n hn => lexP n (List.mem_toFinset.mp hn)) (fun n hn => lexW n (List.mem_toFinset.mp hn))
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  refine le_trans ?_ fl
  exact div_le_div_of_nonneg_right (by linarith) acpos.le

end BccSharp.Coulomb.CompactCover.JLeaf.Screened
