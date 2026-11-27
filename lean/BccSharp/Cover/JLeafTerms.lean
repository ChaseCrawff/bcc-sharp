import BccSharp.Cover.JLeafPhase
import BccSharp.Cover.JLeafChord

set_option autoImplicit false

/-! Checked witness families for the J-leaf energy support.

A witness is an untrusted proposal: an exact rational anchor and, for the
reciprocal terms, the coefficients of an exponential-affine phase bound. The
checker computes the rational `LinTerm` from it with outward-rounded
enclosures, and each family has a theorem that the computed term lies below its
series contribution at every valid chart point of the support box:

* `DirectW`: tangent of `G(1/2, π q)` at `q = s²/π` for a cross or period mode.
* `WaveW`: joint tangent of `2 (1 + cos 2πt) G(1, π q)` with a log-phase secant.
* `PerspW`: the perspective bound `2uz − u²R(πq)` near an extinction, with
  `R` replaced by its secant over the box range of `q`.

`support_sound` adds the terms of a whole support and bounds the sum by the
full positive series `h₂`, all omitted modes being nonnegative. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.CompactCover.DirectRoute (offset pairedTerm pairedTerm_eq lexPositive
  lex_ne diagonalsCheck reciprocalDistance reciprocalDistance_sound cross_distance_positive
  period_distance_positive reciprocalPositive finite_lower bothSigns sum_pairs even_direct even_pair
  endpoints chartVector)
open BccSharp.Coulomb.CompactCover.Stage2 (lower96 upper96 lower96_le le_upper96)

/-! ### Small helpers -/

theorem valid_diag {p : Chart} (hv : (chartPoint p).Valid) : p 0 ≠ 0 ∧ p 1 ≠ 0 := by
  have hdet := hv.1
  have e : (chartPoint p).basis.det = p 0 * p 1 * (p 0 * p 1)⁻¹ := by
    simp [chartPoint, chartBasis, Matrix.det_fin_three]
  rw [e] at hdet
  constructor
  · intro h; rw [h] at hdet; simp at hdet
  · intro h; rw [h] at hdet; simp at hdet

private theorem scalar_range (c a x b : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (c * a) (c * b) ≤ c * x ∧ c * x ≤ max (c * a) (c * b) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ha hc),
      (mul_le_mul_of_nonneg_left hb hc).trans (le_max_right _ _)⟩
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hb hc'),
      (mul_le_mul_of_nonpos_left ha hc').trans (le_max_left _ _)⟩

/-- Exact range of the phase `n · f` over the offset faces of a box. -/
def windowLo (S : Cell) (n : IntVec) : ℚ :=
  ∑ i : Fin 3, min ((n i : ℚ) * S.lo (offset i)) ((n i : ℚ) * S.hi (offset i))

def windowHi (S : Cell) (n : IntVec) : ℚ :=
  ∑ i : Fin 3, max ((n i : ℚ) * S.lo (offset i)) ((n i : ℚ) * S.hi (offset i))

theorem window_sound (S : Cell) (n : IntVec) {p : Chart} (hp : S.Mem p) :
    (windowLo S n : ℝ) ≤ phaseT n p ∧ phaseT n p ≤ (windowHi S n : ℝ) := by
  unfold windowLo windowHi phaseT
  push_cast
  constructor
  · apply Finset.sum_le_sum
    intro i _
    exact (scalar_range (n i : ℝ) _ _ _ (hp (offset i)).1 (hp (offset i)).2).1
  · apply Finset.sum_le_sum
    intro i _
    exact (scalar_range (n i : ℝ) _ _ _ (hp (offset i)).1 (hp (offset i)).2).2

/-! ### Cosine and sine at rational multiples of π -/

def cosArg (L : ℚ) (k : ℤ) : Ball :=
  RoundedPolynomial.roundBall (Constants.piInput.mul (Ball.exact (2 * (L - k))))

def cosGuard (L : ℚ) (k : ℤ) : Bool := decide (|(cosArg L k).mid| / ((40 + 1 : ℕ) : ℚ) ≤ 1 / 2)

def onePlusCosLo (L : ℚ) (k : ℤ) : ℚ := 1 + (TrigBounds.cosBall (cosArg L k) 40).lo

theorem onePlusCosLo_sound (L : ℚ) (k : ℤ) (g : cosGuard L k = true) :
    (onePlusCosLo L k : ℝ) ≤ 1 + Real.cos (2 * Real.pi * L) := by
  have arg : (cosArg L k).Contains (2 * Real.pi * ((L : ℝ) - k)) := by
    apply RoundedPolynomial.round_contains
    have m := Ball.contains_mul Constants.piInput_sound (Ball.contains_exact (2 * (L - k)))
    convert m using 1
    push_cast
    ring
  have hg : |(cosArg L k).mid| / ((40 + 1 : ℕ) : ℚ) ≤ 1 / 2 := of_decide_eq_true g
  have c := TrigBounds.cos_contains arg (n := 40) (by norm_num) hg
  have per : Real.cos (2 * Real.pi * ((L : ℝ) - k)) = Real.cos (2 * Real.pi * L) := by
    rw [show 2 * Real.pi * ((L : ℝ) - k) = 2 * Real.pi * L - (k : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_sub_int_mul_two_pi _ _
  rw [per] at c
  have lo := (endpoints c).1
  unfold onePlusCosLo
  push_cast
  linarith

def sinArg (d : ℚ) : Ball := RoundedPolynomial.roundBall (Constants.piInput.mul (Ball.exact d))

def sinGuard (d : ℚ) : Bool := decide (|(sinArg d).mid| / ((40 + 1 : ℕ) : ℚ) ≤ 1 / 2)

def sinLo (d : ℚ) : ℚ := (TrigBounds.sinBall (sinArg d) 40).lo

theorem sinLo_sound (d : ℚ) (g : sinGuard d = true) : (sinLo d : ℝ) ≤ Real.sin (Real.pi * d) := by
  have arg : (sinArg d).Contains (Real.pi * d) := by
    apply RoundedPolynomial.round_contains
    exact Ball.contains_mul Constants.piInput_sound (Ball.contains_exact d)
  have hg : |(sinArg d).mid| / ((40 + 1 : ℕ) : ℚ) ≤ 1 / 2 := of_decide_eq_true g
  exact (endpoints (TrigBounds.sin_contains arg (n := 40) (by norm_num) hg)).1

/-! ### Physical values -/

theorem physical_cross (n : IntVec) {p : Chart} (hv : (chartPoint p).Valid) :
    physical .cross n p = gKernel (1/2) (Real.pi * termQ .cross n p) ∧ 0 < termQ .cross n p := by
  obtain ⟨h0, h1⟩ := valid_diag hv
  have e := termQ_cross n p h0 h1
  refine ⟨?_, ?_⟩
  · rw [e]; rfl
  · rw [e]
    exact cross_distance_positive hv n

theorem physical_period (n : IntVec) (lex : lexPositive n) {p : Chart}
    (hv : (chartPoint p).Valid) :
    physical .period n p = 2 * gKernel (1/2) (Real.pi * termQ .period n p) ∧
      0 < termQ .period n p := by
  obtain ⟨h0, h1⟩ := valid_diag hv
  have e := termQ_period n p h0 h1
  refine ⟨?_, ?_⟩
  · rw [e]
    simp [physical, seriesDirectTerm, lex_ne lex]
  · rw [e]
    exact period_distance_positive hv n lex

theorem physical_wave (n : IntVec) (lex : lexPositive n) {p : Chart}
    (hv : (chartPoint p).Valid) :
    physical .wave n p = 2 * ((1 + Real.cos (2 * Real.pi * phaseT n p)) *
      (Real.exp (-(Real.pi * termQ .wave n p)) / (Real.pi * termQ .wave n p))) ∧
      0 < termQ .wave n p := by
  obtain ⟨h0, h1⟩ := valid_diag hv
  have e := termQ_wave n p h0 h1
  have pos : 0 < termQ .wave n p := by rw [e]; exact reciprocalPositive hv (lex_ne lex)
  refine ⟨?_, pos⟩
  have g := gKernel_one (mul_pos Real.pi_pos pos)
  simp only [physical]
  rw [pairedTerm_eq, phaseT_eq]
  congr 2
  rw [seriesReciprocalTerm, if_neg (lex_ne lex), ← e, g]

/-! ### Direct (cross and period) witnesses -/

structure DirectW where
  cross : Bool
  index : IntVec
  root : ℚ
  terms : ℕ

def DirectW.kind (w : DirectW) : Kind := if w.cross then .cross else .period
def DirectW.mult (w : DirectW) : ℚ := if w.cross then 1 else 2

def DirectW.term (w : DirectW) : LinTerm :=
  let tg := halfTangent w.root w.terms
  ⟨w.kind, w.index, w.mult * tg.intercept, -(w.mult * tg.penalty), 0⟩

def DirectW.check (w : DirectW) : Bool :=
  halfTangentOk w.root w.terms && (w.cross || decide (lexPositive w.index))

theorem DirectW.valid (w : DirectW) (pi : piOk = true) (ok : w.check = true) (S : Cell) :
    w.term.Valid S := by
  obtain ⟨tok, lexOk⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨pen, tan⟩ := halfTangent_sound w.root w.terms pi tok
  set tg := halfTangent w.root w.terms
  have multPos : (0 : ℚ) < w.mult := by unfold DirectW.mult; split <;> norm_num
  refine ⟨?_, ?_⟩
  · show -(w.mult * tg.penalty) ≤ 0
    have := mul_nonneg multPos.le pen
    linarith
  intro p _ hv
  unfold LinTerm.eval DirectW.term
  simp only
  cases hc : w.cross
  · have kind : w.kind = .period := by simp [DirectW.kind, hc]
    have mult : w.mult = 2 := by simp [DirectW.mult, hc]
    have lex : lexPositive w.index := by simpa [hc] using lexOk
    obtain ⟨phys, qpos⟩ := physical_period w.index lex hv
    rw [kind, mult, phys]
    have b := tan _ qpos
    push_cast
    nlinarith [b]
  · have kind : w.kind = .cross := by simp [DirectW.kind, hc]
    have mult : w.mult = 1 := by simp [DirectW.mult, hc]
    obtain ⟨phys, qpos⟩ := physical_cross w.index hv
    rw [kind, mult, phys]
    have b := tan _ qpos
    push_cast
    nlinarith [b]

/-! ### Reciprocal witnesses with a log-phase secant -/

structure WaveW where
  index : IntVec
  a : ℚ
  b : ℚ
  xbar : ℚ
  tbar : ℚ

namespace WaveW

def L (w : WaveW) (S : Cell) : ℚ := windowLo S w.index
def R (w : WaveW) (S : Cell) : ℚ := windowHi S w.index
def c (w : WaveW) (S : Cell) : ℚ := (w.L S + w.R S) / 2
def k (w : WaveW) (S : Cell) : ℤ := ⌊w.c S + 1 / 2⌋
def lbar (w : WaveW) (S : Cell) : ℚ := w.a + w.b * (w.tbar - w.c S)
def ell (w : WaveW) (S : Cell) (t : ℚ) : ℚ := w.a + w.b * (t - w.c S)

/-- Enclosure of `H = 2 exp(-x̄ + ℓ̄) / x̄`. -/
def H (w : WaveW) (S : Cell) : Ball := (Ball.exact (2 / w.xbar)).mul (expBall (-w.xbar + w.lbar S))

def cq (w : WaveW) (S : Cell) : ℚ :=
  lower96 (((w.H S).mul ((Ball.exact (-(1 + 1 / w.xbar))).mul Constants.piInput)).lo)

def ct (w : WaveW) (S : Cell) : ℚ := lower96 ((w.H S).mul (Ball.exact w.b)).mid

def atT (w : WaveW) (S : Cell) (t : ℚ) : ℚ :=
  ((w.H S).mul (Ball.exact (2 + w.xbar + w.b * (t - w.tbar)))).lo - w.ct S * t

def kappa (w : WaveW) (S : Cell) : ℚ := lower96 (min (w.atT S (w.L S)) (w.atT S (w.R S)))

def term (w : WaveW) (S : Cell) : LinTerm := ⟨.wave, w.index, w.kappa S, w.cq S, w.ct S⟩

def Good (w : WaveW) (S : Cell) : Prop :=
  0 < w.xbar ∧ lexPositive w.index ∧ (w.k S : ℚ) - 1 / 2 < w.L S ∧ w.R S < (w.k S : ℚ) + 1 / 2 ∧
    expOk (-w.xbar + w.lbar S) = true ∧ expOk (w.ell S (w.L S)) = true ∧
    expOk (w.ell S (w.R S)) = true ∧ cosGuard (w.L S) (w.k S) = true ∧
    cosGuard (w.R S) (w.k S) = true ∧
    (expBall (w.ell S (w.L S))).hi ≤ onePlusCosLo (w.L S) (w.k S) ∧
    (expBall (w.ell S (w.R S))).hi ≤ onePlusCosLo (w.R S) (w.k S) ∧ w.cq S ≤ 0

instance (w : WaveW) (S : Cell) : Decidable (w.Good S) := by unfold Good; infer_instance

def check (w : WaveW) (S : Cell) : Bool := decide (w.Good S)

end WaveW

/-- Affine interpolation: an affine inequality at both ends of `[L, R]`
holds throughout. -/
theorem affine_between (L R t A B C D : ℝ) (hL : L ≤ t) (hR : t ≤ R)
    (atL : A + B * L ≤ C + D * L) (atR : A + B * R ≤ C + D * R) : A + B * t ≤ C + D * t := by
  rcases eq_or_lt_of_le (hL.trans hR) with same | lt
  · have : t = L := le_antisymm (hR.trans_eq same.symm) hL
    rw [this]; exact atL
  · have hw : (0 : ℝ) < R - L := sub_pos.mpr lt
    have key : (A + B * t - (C + D * t)) * (R - L) =
        (R - t) * (A + B * L - (C + D * L)) + (t - L) * (A + B * R - (C + D * R)) := by ring
    have rhs : (R - t) * (A + B * L - (C + D * L)) + (t - L) * (A + B * R - (C + D * R)) ≤ 0 := by
      have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hR) (sub_nonpos.mpr atL)
      have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hL) (sub_nonpos.mpr atR)
      linarith
    have : A + B * t - (C + D * t) ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos hc hw
      linarith
    linarith

theorem WaveW.valid (w : WaveW) (S : Cell) (ok : w.check S = true) : (w.term S).Valid S := by
  have g : w.Good S := of_decide_eq_true ok
  obtain ⟨xpos, lex, kL, kR, eH, eL, eR, gL, gR, pL, pR, cqNeg⟩ := g
  refine ⟨cqNeg, ?_⟩
  intro p hp hv
  obtain ⟨phys, qpos⟩ := physical_wave w.index lex hv
  obtain ⟨tL, tR⟩ := window_sound S w.index hp
  have xb : (0 : ℝ) < w.xbar := by exact_mod_cast xpos
  -- Names for the real quantities.
  obtain ⟨q, hq⟩ : ∃ q, q = termQ .wave w.index p := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = phaseT w.index p := ⟨_, rfl⟩
  rw [← hq] at phys qpos
  rw [← ht] at phys tL tR
  have tL' : (w.L S : ℝ) ≤ t := by simpa [WaveW.L] using tL
  have tR' : t ≤ (w.R S : ℝ) := by simpa [WaveW.R] using tR
  -- The exponential-affine phase bound on the window.
  have ellEq (s : ℚ) : ((w.ell S s : ℚ) : ℝ) = (w.a : ℝ) + (w.b : ℝ) * ((s : ℝ) - (w.c S : ℝ)) := by
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
  -- Joint tangent of G₁ with the phase factor.
  have y := mul_pos Real.pi_pos qpos
  have tang := g1_tangent (w.xbar : ℝ) (Real.pi * q)
    ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))
    ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) xb y
  have g1nn : 0 ≤ Real.exp (-(Real.pi * q)) / (Real.pi * q) := by positivity
  have lower1 : 2 * (Real.exp (-(Real.pi * q) + ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ)))) /
      (Real.pi * q)) ≤ physical .wave w.index p := by
    rw [phys, Real.exp_add]
    have m := mul_le_mul_of_nonneg_right phase g1nn
    have e : Real.exp (-(Real.pi * q)) * Real.exp ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) /
        (Real.pi * q) = Real.exp ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) *
          (Real.exp (-(Real.pi * q)) / (Real.pi * q)) := by ring
    rw [e]
    linarith
  -- Real value of the anchor coefficient.
  obtain ⟨Hr, hHr⟩ : ∃ Hr : ℝ, Hr = 2 * (Real.exp (-(w.xbar : ℝ) +
      ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))) / (w.xbar : ℝ)) := ⟨_, rfl⟩
  have hH : (w.H S).Contains Hr := by
    have m := Ball.contains_mul (Ball.contains_exact (2 / w.xbar)) (expBall_contains _ eH)
    have e : Hr = ((2 / w.xbar : ℚ) : ℝ) * Real.exp ((-w.xbar + w.lbar S : ℚ) : ℝ) := by
      rw [hHr]
      simp only [WaveW.lbar]
      push_cast
      ring
    rw [e]
    exact m
  have plane : Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * (t - (w.tbar : ℝ))) +
      Hr * (-(1 + 1 / (w.xbar : ℝ)) * Real.pi) * q ≤ physical .wave w.index p := by
    have e : Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * (t - (w.tbar : ℝ))) +
        Hr * (-(1 + 1 / (w.xbar : ℝ)) * Real.pi) * q =
        2 * (Real.exp (-(w.xbar : ℝ) + ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))) /
          (w.xbar : ℝ) * (1 + (-1 - 1 / (w.xbar : ℝ)) * (Real.pi * q - (w.xbar : ℝ)) +
            (((w.a : ℝ) + (w.b : ℝ) * (t - (w.c S : ℝ))) -
              ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c S : ℝ)))))) := by
      rw [hHr]
      field_simp
      ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_left tang (by norm_num : (0 : ℝ) ≤ 2), lower1]
  -- The q coefficient.
  have cqLe : (w.cq S : ℝ) ≤ Hr * (-(1 + 1 / (w.xbar : ℝ)) * Real.pi) := by
    have m := Ball.contains_mul hH (Ball.contains_mul (Ball.contains_exact (-(1 + 1 / w.xbar)))
      Constants.piInput_sound)
    have lo := (endpoints m).1
    have r := (Rat.cast_le (K := ℝ)).mpr (lower96_le
      (((w.H S).mul ((Ball.exact (-(1 + 1 / w.xbar))).mul Constants.piInput)).lo))
    have e : ((w.cq S : ℚ) : ℝ) = ((lower96
        (((w.H S).mul ((Ball.exact (-(1 + 1 / w.xbar))).mul Constants.piInput)).lo) : ℚ) : ℝ) := rfl
    rw [e]
    refine r.trans (lo.trans_eq ?_)
    push_cast
    ring
  -- The constant and phase coefficients at both window ends.
  have atLe (s : ℚ) : ((w.atT S s : ℚ) : ℝ) + (w.ct S : ℝ) * s ≤
      Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * ((s : ℝ) - (w.tbar : ℝ))) := by
    have m := Ball.contains_mul hH (Ball.contains_exact (2 + w.xbar + w.b * (s - w.tbar)))
    have lo := (endpoints m).1
    have e : ((w.atT S s : ℚ) : ℝ) =
        (((w.H S).mul (Ball.exact (2 + w.xbar + w.b * (s - w.tbar)))).lo : ℝ) - (w.ct S : ℝ) * s := by
      simp only [WaveW.atT]
      push_cast
      ring
    rw [e]
    have e2 : Hr * ((((2 + w.xbar + w.b * (s - w.tbar)) : ℚ)) : ℝ) =
        Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * ((s : ℝ) - (w.tbar : ℝ))) := by push_cast; ring
    linarith
  have kap (s : ℚ) (hs : s = w.L S ∨ s = w.R S) : ((w.kappa S : ℚ) : ℝ) ≤ (w.atT S s : ℝ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr (lower96_le (min (w.atT S (w.L S)) (w.atT S (w.R S))))
    have e : ((w.kappa S : ℚ) : ℝ) =
        ((lower96 (min (w.atT S (w.L S)) (w.atT S (w.R S))) : ℚ) : ℝ) := rfl
    rw [e]
    rcases hs with rfl | rfl
    · exact h1.trans (Rat.cast_le.mpr (min_le_left _ _))
    · exact h1.trans (Rat.cast_le.mpr (min_le_right _ _))
  have mid : (w.kappa S : ℝ) + (w.ct S : ℝ) * t ≤
      (Hr * (2 + (w.xbar : ℝ) - (w.b : ℝ) * (w.tbar : ℝ))) + (Hr * (w.b : ℝ)) * t := by
    apply affine_between (w.L S) (w.R S) t _ _ _ _ tL' tR'
    · have := atLe (w.L S); have := kap (w.L S) (Or.inl rfl); nlinarith
    · have := atLe (w.R S); have := kap (w.R S) (Or.inr rfl); nlinarith
  have cqq := mul_le_mul_of_nonneg_right cqLe qpos.le
  show (w.kappa S : ℝ) + (w.cq S : ℝ) * termQ .wave w.index p +
    (w.ct S : ℝ) * phaseT w.index p ≤ physical .wave w.index p
  rw [← hq, ← ht]
  nlinarith [plane, mid, cqq]

/-! ### Reciprocal witnesses near an extinction -/

/-- A rational upper bound for π. -/
def piUp : ℚ := 3141592653589793238462643383279502885 / 10 ^ 36

def piUpOk : Bool := decide (Constants.piInput.mid + Constants.piInput.rad ≤ piUp)

theorem pi_le_piUp (h : piUpOk = true) : Real.pi ≤ (piUp : ℝ) := by
  have hle : Constants.piInput.mid + Constants.piInput.rad ≤ piUp := of_decide_eq_true h
  have c := (endpoints Constants.piInput_sound).2
  have : ((Constants.piInput.hi : ℚ) : ℝ) ≤ (piUp : ℝ) := by exact_mod_cast hle
  linarith

structure PerspW where
  index : IntVec
  u : ℚ

namespace PerspW

def L (w : PerspW) (S : Cell) : ℚ := windowLo S w.index
def R (w : PerspW) (S : Cell) : ℚ := windowHi S w.index
def k (w : PerspW) (S : Cell) : ℤ := ⌊(w.L S + w.R S) / 2⌋
def z0 (w : PerspW) (S : Cell) : ℚ := (w.k S : ℚ) + 1 / 2
def d (w : PerspW) (S : Cell) : ℚ := max |w.L S - w.z0 S| |w.R S - w.z0 S|
def kappa (w : PerspW) (S : Cell) : ℚ := lower96 (4 * (sinLo (w.d S)) ^ 2 / (w.d S) ^ 2)
def qlo (w : PerspW) (S : Cell) : ℚ := (reciprocalDistance S w.index).lo
def qhi (w : PerspW) (S : Cell) : ℚ := (reciprocalDistance S w.index).hi

/-- Upper bound for `R(π q) = π q exp(π q) / κ` at a rational `q ≥ 0`. -/
def A (w : PerspW) (S : Cell) (q : ℚ) : ℚ :=
  ((Ball.exact (piUp * q / w.kappa S)).mul (expBall (piUp * q))).hi

def betaRaw (w : PerspW) (S : Cell) : ℚ :=
  if w.qlo S < w.qhi S then max 0 ((w.A S (w.qhi S) - w.A S (w.qlo S)) / (w.qhi S - w.qlo S)) else 0

/-- Secant slope and intercept, rounded up to the 2⁻⁹⁶ grid. Rounding both up
keeps `α + β q` above the secant for `q ≥ 0`. -/
def beta (w : PerspW) (S : Cell) : ℚ := upper96 (w.betaRaw S)

def alpha (w : PerspW) (S : Cell) : ℚ := upper96 (w.A S (w.qlo S) - w.beta S * w.qlo S)

def term (w : PerspW) (S : Cell) : LinTerm :=
  ⟨.wave, w.index, -2 * w.u * w.z0 S - w.u ^ 2 * w.alpha S, -(w.u ^ 2 * w.beta S), 2 * w.u⟩

def Good (w : PerspW) (S : Cell) : Prop :=
  lexPositive w.index ∧ diagonalsCheck S = true ∧ 0 < w.d S ∧ w.d S ≤ 1 / 2 ∧
    sinGuard (w.d S) = true ∧ 0 < sinLo (w.d S) ∧ 0 < w.kappa S ∧ 0 ≤ w.qlo S ∧
    w.qlo S ≤ w.qhi S ∧ expOk (piUp * w.qlo S) = true ∧ expOk (piUp * w.qhi S) = true ∧
    piUpOk = true

instance (w : PerspW) (S : Cell) : Decidable (w.Good S) := by unfold Good; infer_instance

def check (w : PerspW) (S : Cell) : Bool := decide (w.Good S)

end PerspW

private theorem mul_exp_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x * Real.exp x ≤ y * Real.exp y :=
  mul_le_mul hxy (Real.exp_le_exp.mpr hxy) (Real.exp_pos _).le (hx.trans hxy)

theorem PerspW.A_ge (w : PerspW) (S : Cell) (q : ℚ) (hq : 0 ≤ q) (hpi : piUpOk = true)
    (hk : 0 < w.kappa S) (he : expOk (piUp * q) = true) :
    Real.pi * q * Real.exp (Real.pi * q) / (w.kappa S : ℝ) ≤ (w.A S q : ℝ) := by
  have m := Ball.contains_mul (Ball.contains_exact (piUp * q / w.kappa S)) (expBall_contains _ he)
  have hi := (endpoints m).2
  have kpos : (0 : ℝ) < w.kappa S := by exact_mod_cast hk
  have qnn : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have piq : Real.pi * q ≤ (piUp : ℝ) * q := mul_le_mul_of_nonneg_right (pi_le_piUp hpi) qnn
  have mono := mul_exp_mono (mul_nonneg Real.pi_pos.le qnn) piq
  have e : (((piUp * q / w.kappa S : ℚ) : ℝ)) * Real.exp ((piUp * q : ℚ) : ℝ) =
      (piUp : ℝ) * q * Real.exp ((piUp : ℝ) * q) / (w.kappa S : ℝ) := by
    push_cast; ring
  rw [e] at hi
  have : Real.pi * q * Real.exp (Real.pi * q) / (w.kappa S : ℝ) ≤
      (piUp : ℝ) * q * Real.exp ((piUp : ℝ) * q) / (w.kappa S : ℝ) :=
    div_le_div_of_nonneg_right mono kpos.le
  exact this.trans hi

theorem PerspW.valid (w : PerspW) (S : Cell) (ok : w.check S = true) : (w.term S).Valid S := by
  have g : w.Good S := of_decide_eq_true ok
  obtain ⟨lex, diag, dpos, dhalf, sg, spos, kpos, qlo0, qlohi, elo, ehi, pu⟩ := g
  refine ⟨?_, ?_⟩
  · show -(w.u ^ 2 * w.beta S) ≤ 0
    have : 0 ≤ w.beta S := by
      have raw : 0 ≤ w.betaRaw S := by
        unfold PerspW.betaRaw; split
        · exact le_max_left _ _
        · exact le_rfl
      exact raw.trans (le_upper96 _)
    nlinarith [sq_nonneg w.u]
  intro p hp hv
  obtain ⟨phys, qpos⟩ := physical_wave w.index lex hv
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
  have qlo : (w.qlo S : ℝ) ≤ q := qrange.1
  have qhi : q ≤ (w.qhi S : ℝ) := qrange.2
  -- The distance to the extinction.
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
  -- The secant of `R(π q)` over `[qlo, qhi]`.
  have kr : (0 : ℝ) < w.kappa S := by exact_mod_cast kpos
  have Alo := w.A_ge S (w.qlo S) qlo0 pu kpos elo
  have Ahi := w.A_ge S (w.qhi S) (qlo0.trans qlohi) pu kpos ehi
  have Rsec : Real.pi * q * Real.exp (Real.pi * q) / (w.kappa S : ℝ) ≤
      (w.alpha S : ℝ) + (w.beta S : ℝ) * q := by
    have qlo0r : (0 : ℝ) ≤ w.qlo S := by exact_mod_cast qlo0
    have sec := secant_mul_exp (Real.pi * w.qlo S) (Real.pi * w.qhi S) (Real.pi * q)
      (mul_nonneg Real.pi_pos.le qlo0r) (mul_le_mul_of_nonneg_left qlo Real.pi_pos.le)
      (mul_le_mul_of_nonneg_left qhi Real.pi_pos.le)
    by_cases strict : w.qlo S < w.qhi S
    · have beq : w.betaRaw S = max 0 ((w.A S (w.qhi S) - w.A S (w.qlo S)) / (w.qhi S - w.qlo S)) := by
        simp [PerspW.betaRaw, strict]
      have bup : (w.betaRaw S : ℝ) ≤ (w.beta S : ℝ) := Rat.cast_le.mpr (le_upper96 _)
      have wpos : (0 : ℝ) < (w.qhi S : ℝ) - (w.qlo S : ℝ) := by
        have : ((w.qlo S : ℚ) : ℝ) < (w.qhi S : ℝ) := by exact_mod_cast strict
        linarith
      have bge : ((w.A S (w.qhi S) : ℝ) - (w.A S (w.qlo S) : ℝ)) / ((w.qhi S : ℝ) - (w.qlo S : ℝ)) ≤
          (w.beta S : ℝ) := by
        refine le_trans ?_ bup
        rw [beq]
        have := le_max_right (0 : ℚ) ((w.A S (w.qhi S) - w.A S (w.qlo S)) / (w.qhi S - w.qlo S))
        have c : ((((w.A S (w.qhi S) - w.A S (w.qlo S)) / (w.qhi S - w.qlo S) : ℚ)) : ℝ) ≤
            ((max 0 ((w.A S (w.qhi S) - w.A S (w.qlo S)) / (w.qhi S - w.qlo S)) : ℚ) : ℝ) :=
          Rat.cast_le.mpr this
        have e : ((((w.A S (w.qhi S) - w.A S (w.qlo S)) / (w.qhi S - w.qlo S) : ℚ)) : ℝ) =
            ((w.A S (w.qhi S) : ℝ) - (w.A S (w.qlo S) : ℝ)) / ((w.qhi S : ℝ) - (w.qlo S : ℝ)) := by
          push_cast; ring
        rw [← e]
        exact c
      have bnn : (0 : ℝ) ≤ w.beta S := by
        refine le_trans ?_ bup
        rw [beq]; exact_mod_cast le_max_left _ _
      have hpi := Real.pi_pos
      -- Divide the secant inequality by `π (qhi - qlo) κ`.
      have sec' : q * Real.exp (Real.pi * q) * ((w.qhi S : ℝ) - (w.qlo S : ℝ)) ≤
          ((w.qhi S : ℝ) - q) * ((w.qlo S : ℝ) * Real.exp (Real.pi * w.qlo S)) +
            (q - (w.qlo S : ℝ)) * ((w.qhi S : ℝ) * Real.exp (Real.pi * w.qhi S)) := by
        have e1 : Real.pi * q * Real.exp (Real.pi * q) * (Real.pi * (w.qhi S : ℝ) - Real.pi * (w.qlo S : ℝ)) =
            Real.pi ^ 2 * (q * Real.exp (Real.pi * q) * ((w.qhi S : ℝ) - (w.qlo S : ℝ))) := by ring
        have e2 : (Real.pi * (w.qhi S : ℝ) - Real.pi * q) * (Real.pi * (w.qlo S : ℝ) * Real.exp (Real.pi * w.qlo S)) +
            (Real.pi * q - Real.pi * (w.qlo S : ℝ)) * (Real.pi * (w.qhi S : ℝ) * Real.exp (Real.pi * w.qhi S)) =
            Real.pi ^ 2 * (((w.qhi S : ℝ) - q) * ((w.qlo S : ℝ) * Real.exp (Real.pi * w.qlo S)) +
              (q - (w.qlo S : ℝ)) * ((w.qhi S : ℝ) * Real.exp (Real.pi * w.qhi S))) := by ring
        rw [e1, e2] at sec
        exact le_of_mul_le_mul_left sec (by positivity)
      -- Convert to the A bounds.
      have AloR : (w.qlo S : ℝ) * Real.exp (Real.pi * w.qlo S) ≤ (w.kappa S : ℝ) * (w.A S (w.qlo S) : ℝ) / Real.pi := by
        rw [le_div_iff₀ hpi]
        have := (div_le_iff₀ kr).mp Alo
        linarith
      have AhiR : (w.qhi S : ℝ) * Real.exp (Real.pi * w.qhi S) ≤ (w.kappa S : ℝ) * (w.A S (w.qhi S) : ℝ) / Real.pi := by
        rw [le_div_iff₀ hpi]
        have := (div_le_iff₀ kr).mp Ahi
        linarith
      have sec2 : q * Real.exp (Real.pi * q) * ((w.qhi S : ℝ) - (w.qlo S : ℝ)) ≤
          ((w.qhi S : ℝ) - q) * ((w.kappa S : ℝ) * (w.A S (w.qlo S) : ℝ) / Real.pi) +
            (q - (w.qlo S : ℝ)) * ((w.kappa S : ℝ) * (w.A S (w.qhi S) : ℝ) / Real.pi) := by
        have a1 := mul_le_mul_of_nonneg_left AloR (sub_nonneg.mpr qhi)
        have a2 := mul_le_mul_of_nonneg_left AhiR (sub_nonneg.mpr qlo)
        linarith
      -- The secant line lies below `alpha + beta q`.
      have line : ((w.qhi S : ℝ) - q) * (w.A S (w.qlo S) : ℝ) + (q - (w.qlo S : ℝ)) * (w.A S (w.qhi S) : ℝ) ≤
          ((w.alpha S : ℝ) + (w.beta S : ℝ) * q) * ((w.qhi S : ℝ) - (w.qlo S : ℝ)) := by
        have hal : (w.A S (w.qlo S) : ℝ) - (w.beta S : ℝ) * (w.qlo S : ℝ) ≤ (w.alpha S : ℝ) := by
          have := (Rat.cast_le (K := ℝ)).mpr (le_upper96 (w.A S (w.qlo S) - w.beta S * w.qlo S))
          push_cast at this
          exact this
        have := (div_le_iff₀ wpos).mp bge
        have h := mul_le_mul_of_nonneg_left this (sub_nonneg.mpr qlo)
        have h3 := mul_le_mul_of_nonneg_right hal wpos.le
        nlinarith [h, h3]
      have final : Real.pi * q * Real.exp (Real.pi * q) * ((w.qhi S : ℝ) - (w.qlo S : ℝ)) ≤
          (w.kappa S : ℝ) * (((w.alpha S : ℝ) + (w.beta S : ℝ) * q) * ((w.qhi S : ℝ) - (w.qlo S : ℝ))) := by
        have := mul_le_mul_of_nonneg_left sec2 hpi.le
        have e : Real.pi * (((w.qhi S : ℝ) - q) * ((w.kappa S : ℝ) * (w.A S (w.qlo S) : ℝ) / Real.pi) +
            (q - (w.qlo S : ℝ)) * ((w.kappa S : ℝ) * (w.A S (w.qhi S) : ℝ) / Real.pi)) =
            (w.kappa S : ℝ) * (((w.qhi S : ℝ) - q) * (w.A S (w.qlo S) : ℝ) +
              (q - (w.qlo S : ℝ)) * (w.A S (w.qhi S) : ℝ)) := by
          field_simp
        rw [e] at this
        have h2 := mul_le_mul_of_nonneg_left line kr.le
        linarith [this, h2]
      rw [div_le_iff₀ kr]
      have h2 : Real.pi * q * Real.exp (Real.pi * q) * ((w.qhi S : ℝ) - (w.qlo S : ℝ)) ≤
          ((w.alpha S : ℝ) + (w.beta S : ℝ) * q) * (w.kappa S : ℝ) * ((w.qhi S : ℝ) - (w.qlo S : ℝ)) := by
        linarith [final]
      exact le_of_mul_le_mul_right h2 wpos
    · have same : w.qlo S = w.qhi S := le_antisymm qlohi (not_lt.mp strict)
      have qeq : q = (w.qlo S : ℝ) := le_antisymm (qhi.trans_eq (by rw [same])) qlo
      have b0 : w.beta S = 0 := by simp [PerspW.beta, PerspW.betaRaw, strict, upper96]
      have hal : (w.A S (w.qlo S) : ℝ) ≤ (w.alpha S : ℝ) := by
        have h := le_upper96 (w.A S (w.qlo S) - w.beta S * w.qlo S)
        have e : w.alpha S = upper96 (w.A S (w.qlo S) - w.beta S * w.qlo S) := rfl
        rw [e, b0, zero_mul, sub_zero]
        rw [b0, zero_mul, sub_zero] at h
        exact_mod_cast h
      rw [qeq, b0]
      push_cast
      linarith [Alo, hal]
  -- The perspective bound.
  have zeq : t = (t - (w.z0 S : ℝ)) + ((w.k S : ℤ) : ℝ) + 1 / 2 := by
    simp only [PerspW.z0]; push_cast; ring
  have kd : (w.kappa S : ℝ) * (w.d S : ℝ) ^ 2 ≤ 4 * Real.sin (Real.pi * (w.d S : ℝ)) ^ 2 := by
    have sl := sinLo_sound (w.d S) sg
    have sp : (0 : ℝ) < sinLo (w.d S) := by exact_mod_cast spos
    have dp : (0 : ℝ) < w.d S := by exact_mod_cast dpos
    have kle : ((w.kappa S : ℚ) : ℝ) ≤ 4 * (sinLo (w.d S) : ℝ) ^ 2 / (w.d S : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr (lower96_le (4 * (sinLo (w.d S)) ^ 2 / (w.d S) ^ 2))
      have e : ((w.kappa S : ℚ) : ℝ) = ((lower96 (4 * (sinLo (w.d S)) ^ 2 / (w.d S) ^ 2) : ℚ) : ℝ) := rfl
      rw [e]
      refine this.trans (le_of_eq ?_)
      push_cast; ring
    have sq := pow_le_pow_left₀ sp.le sl 2
    rw [le_div_iff₀ (by positivity)] at kle
    linarith [kle, sq]
  have pl := persp_lower (w.k S) (t - (w.z0 S : ℝ)) (w.d S) (w.kappa S) (w.u) (Real.pi * q)
    (by exact_mod_cast dpos)
    (by have h := (Rat.cast_le (K := ℝ)).mpr dhalf; push_cast at h; exact h)
    zbound kr kd (mul_pos Real.pi_pos qpos)
  rw [← zeq] at pl
  have physEq : physical .wave w.index p = 2 * ((1 + Real.cos (2 * Real.pi * t)) *
      (Real.exp (-(Real.pi * q)) / (Real.pi * q))) := phys
  show ((-2 * w.u * w.z0 S - w.u ^ 2 * w.alpha S : ℚ) : ℝ) + ((-(w.u ^ 2 * w.beta S) : ℚ) : ℝ) *
      termQ .wave w.index p + ((2 * w.u : ℚ) : ℝ) * phaseT w.index p ≤ physical .wave w.index p
  rw [← hq, ← ht, physEq]
  push_cast
  have u2 : (0 : ℝ) ≤ (w.u : ℝ) ^ 2 := sq_nonneg _
  have hR := mul_le_mul_of_nonneg_left Rsec u2
  linarith [hR, pl]

/-! ### Items and the support bound -/

inductive Witness where
  | direct (w : DirectW)
  | wave (w : WaveW)
  | persp (w : PerspW)

def Witness.term (S : Cell) : Witness → LinTerm
  | .direct w => w.term
  | .wave w => w.term S
  | .persp w => w.term S

def Witness.check (S : Cell) : Witness → Bool
  | .direct w => w.check
  | .wave w => w.check S
  | .persp w => w.check S

theorem Witness.valid (S : Cell) (pi : piOk = true) (x : Witness) (ok : x.check S = true) :
    (x.term S).Valid S := by
  cases x with
  | direct w => exact w.valid pi ok S
  | wave w => exact w.valid S ok
  | persp w => exact w.valid S ok

def linEq (a b : LinTerm) : Bool :=
  decide (a.kind = b.kind) && decide (a.index = b.index) && decide (a.const = b.const) &&
    decide (a.slope = b.slope) && decide (a.phase = b.phase)

theorem linEq_sound {a b : LinTerm} (h : linEq a b = true) : a = b := by
  simp only [linEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases a; cases b
  simp_all

/-- A literal term together with the witness that justifies it. -/
structure Item where
  wit : Witness
  lin : LinTerm

def itemOk (S : Cell) (it : Item) : Bool := it.wit.check S && linEq (it.wit.term S) it.lin

theorem item_valid (S : Cell) (pi : piOk = true) (it : Item) (ok : itemOk S it = true) :
    it.lin.Valid S := by
  obtain ⟨c, e⟩ := Bool.and_eq_true_iff.mp ok
  rw [← linEq_sound e]
  exact it.wit.valid S pi c

def kindIdx (k : Kind) (lins : List LinTerm) : List IntVec :=
  (lins.filter (fun t => decide (t.kind = k))).map LinTerm.index

def structureOk (lins : List LinTerm) : Bool :=
  decide ((kindIdx .cross lins).Nodup ∧ (kindIdx .period lins).Nodup ∧ (kindIdx .wave lins).Nodup ∧
    (∀ n ∈ kindIdx .period lins, lexPositive n) ∧ (∀ n ∈ kindIdx .wave lins, lexPositive n))

private theorem sum_by_kind (l : List LinTerm) (g : LinTerm → ℝ) :
    (l.map g).sum = ((l.filter (fun t => decide (t.kind = .cross))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .period))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .wave))).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hk : a.kind <;> simp [hk, ih] <;> ring

private theorem filter_kind_sum (l : List LinTerm) (k : Kind) (G : Kind → IntVec → ℝ) :
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

theorem support_sound (S : Cell) (lins : List LinTerm) (valid : ∀ t ∈ lins, t.Valid S)
    (hs : structureOk lins = true) (p : Chart) (hp : S.Mem p) (hv : (chartPoint p).Valid) :
    linSum lins p ≤ h₂ (chartPoint p) := by
  have st := of_decide_eq_true hs
  obtain ⟨ncross, nperiod, nwave, lexP, lexW⟩ := st
  set q := chartPoint p
  -- Each term lies below its physical contribution.
  have step1 : linSum lins p ≤ (lins.map (fun t => physical t.kind t.index p)).sum := by
    unfold linSum
    apply List.sum_le_sum
    intro t ht
    exact (valid t ht).2 p hp hv
  have fc := filter_kind_sum lins .cross (fun k n => physical k n p)
  have fp := filter_kind_sum lins .period (fun k n => physical k n p)
  have fw := filter_kind_sum lins .wave (fun k n => physical k n p)
  rw [sum_by_kind lins, fc, fp, fw] at step1
  -- Convert the three list sums into the finite sums of `finite_lower`.
  set X := (kindIdx .cross lins).toFinset
  set P := (kindIdx .period lins).toFinset
  set W := (kindIdx .wave lins).toFinset
  have cross : ((kindIdx .cross lins).map (fun n => physical .cross n p)).sum =
      ∑ n ∈ X, seriesCrossTerm q n := by
    rw [List.sum_toFinset _ ncross]; rfl
  have period : ((kindIdx .period lins).map (fun n => physical .period n p)).sum =
      ∑ n ∈ bothSigns P, seriesDirectTerm q n := by
    rw [← sum_pairs P (fun n hn => lexP n (List.mem_toFinset.mp hn)) (seriesDirectTerm q) (even_direct q),
      List.sum_toFinset _ nperiod]
    rfl
  have wave : ((kindIdx .wave lins).map (fun n => physical .wave n p)).sum =
      ∑ n ∈ bothSigns W, pairedTerm q n := by
    rw [← sum_pairs W (fun n hn => lexW n (List.mem_toFinset.mp hn)) (pairedTerm q) (even_pair q),
      List.sum_toFinset _ nwave]
    rfl
  rw [cross, period, wave] at step1
  have fl := finite_lower q hv (bothSigns P) X (bothSigns W)
  linarith

end BccSharp.Coulomb.CompactCover.JLeaf

