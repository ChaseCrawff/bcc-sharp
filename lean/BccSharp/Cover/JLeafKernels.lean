import BccSharp.Cover.Stage2Bulk

set_option autoImplicit false

/-! Fast kernel enclosures for the JointDeficit/Continuation J-leaf evaluator.

Every anchor is an exact rational. The half kernel is anchored at a rational
square `s²`, so `√(s²) = s` is exact and erfc is evaluated by the exact term
recurrence `seriesFast`. Exponentials use a rounded Horner bound followed by
rounded squarings. All rounding is outward, and each enclosure has a soundness
theorem for the actual real function. The rational tangent coefficients are
rounded to the 2⁻⁹⁶ grid so later aggregation stays small. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover (KernelKind kernelValue kernelSlope halfKernel_formula)
open BccSharp.Coulomb.CompactCover.Stage2 (globalTangent lower96 upper96 lower96_le le_upper96)
open BccSharp.Coulomb.CompactCover.DirectRoute (endpoints)

/-! ### Exponential at a rational point -/

/-- Repeated rounded squaring. -/
def expSquare : ℕ → Ball → Ball
  | 0, b => b
  | k + 1, b => expSquare k (RoundedPolynomial.roundBall (b.mul b))

theorem expSquare_contains (k : ℕ) (b : Ball) (y : ℝ) (h : b.Contains (Real.exp y)) :
    (expSquare k b).Contains (Real.exp (2 ^ k * y)) := by
  induction k generalizing b y with
  | zero => simpa [expSquare] using h
  | succ k ih =>
    have hs : (RoundedPolynomial.roundBall (b.mul b)).Contains (Real.exp (2 * y)) := by
      apply RoundedPolynomial.round_contains
      have hm := Ball.contains_mul h h
      rwa [← Real.exp_add, ← two_mul] at hm
    have hk := ih _ (2 * y) hs
    rw [show (2 : ℝ) ^ (k + 1) * y = 2 ^ k * (2 * y) by ring]
    simpa [expSquare] using hk

/-- `exp x` from `order` Horner terms at `x / 2^k`, then `k` squarings. -/
def expBallQ (x : ℚ) (k order : ℕ) : Ball :=
  expSquare k (RoundedPolynomial.expBound (x / 2 ^ k) order)

def expGuard (x : ℚ) (k order : ℕ) : Bool := decide (|x / 2 ^ k| ≤ 1 ∧ 0 < order)

theorem expBallQ_contains (x : ℚ) (k order : ℕ) (ok : expGuard x k order = true) :
    (expBallQ x k order).Contains (Real.exp (x : ℝ)) := by
  have h : |x / 2 ^ k| ≤ 1 ∧ 0 < order := of_decide_eq_true ok
  have hb := RoundedPolynomial.expBound_contains h.1 h.2
  have hs := expSquare_contains k _ _ hb
  have e : (2 : ℝ) ^ k * ((x / 2 ^ k : ℚ) : ℝ) = (x : ℝ) := by
    push_cast
    field_simp
  rwa [e] at hs

/-- Automatic parameters: enough squarings that the Horner argument is at
most one half in absolute value, and 26 Horner terms. -/
def expSteps (x : ℚ) : ℕ := (Nat.log 2 (⌈|x|⌉.toNat)) + 2
def expBall (x : ℚ) : Ball := expBallQ x (expSteps x) 26
def expOk (x : ℚ) : Bool := expGuard x (expSteps x) 26

theorem expBall_contains (x : ℚ) (ok : expOk x = true) :
    (expBall x).Contains (Real.exp (x : ℝ)) :=
  expBallQ_contains x _ _ ok

/-! ### erfc at an exact rational root -/

/-- Exact error allowance of the truncated erfc series at `q = s²`. -/
def erfcError (s : ℚ) (n : ℕ) : ℚ :=
  4 * (s + 0) * (Constants.piInverseRoot.mid + Constants.piInverseRoot.rad) * (s * s) ^ n / (n.factorial : ℚ)

/-- Enclosure of `erfc(s)` for rational `s ≥ 0`, using `n` series terms. -/
def erfcBall (s : ℚ) (n : ℕ) : Ball :=
  let b := (Ball.exact 1).sub ((((Ball.exact 2).mul (Ball.exact s)).mul Constants.piInverseRoot).mul
    (Ball.exact (Constants.seriesFast (s * s) n)))
  ⟨b.mid, b.rad + erfcError s n⟩

def erfcGuard (s : ℚ) (n : ℕ) : Bool := decide (0 ≤ s ∧ s * s / (n + 1 : ℕ) ≤ 1 / 2)

/-- The shared π checks: the Constants root of π brackets `√π`. -/
def piOk : Bool := Constants.piRoot.check Constants.piInput

theorem sqrtPi_contains (ok : piOk = true) : Constants.piRoot.ball.Contains (Real.sqrt Real.pi) :=
  Constants.HighPrecision.RootProposal.sound Constants.piRoot Constants.piInput Real.pi Real.pi_pos.le
    Constants.piInput_sound ok

theorem erfcBall_contains (s : ℚ) (n : ℕ) (pi : piOk = true) (ok : erfcGuard s n = true) :
    (erfcBall s n).Contains (Gaussian.erfcIntegral (s : ℝ)) := by
  have h : 0 ≤ s ∧ s * s / (n + 1 : ℕ) ≤ 1 / 2 := of_decide_eq_true ok
  have hq : 0 ≤ s * s := mul_nonneg h.1 h.1
  have hroot : (Ball.exact s).Contains (Real.sqrt ((s * s : ℚ) : ℝ)) := by
    have e : Real.sqrt ((s * s : ℚ) : ℝ) = (s : ℝ) := by
      push_cast
      rw [Real.sqrt_mul_self (by exact_mod_cast h.1)]
    rw [e]
    exact Ball.contains_exact s
  have he : 4 * ((Ball.exact s).mid + (Ball.exact s).rad) *
      (Constants.piInverseRoot.mid + Constants.piInverseRoot.rad) * (s * s) ^ n / (n.factorial : ℚ) ≤
        erfcError s n := by
    simp [erfcError, Ball.exact]
  have enc := Erfc.enclosure hq h.2 hroot (Constants.piInverseRoot_sound pi) he
  have e : Real.sqrt ((s * s : ℚ) : ℝ) = (s : ℝ) := by
    push_cast
    rw [Real.sqrt_mul_self (by exact_mod_cast h.1)]
  rw [e] at enc
  simpa only [erfcBall, Constants.seriesFast_eq] using enc

/-! ### The half kernel at a rational square -/

/-- `G(1/2, s²) = √π erfc(s) / s`. -/
def halfBall (s : ℚ) (n : ℕ) : Ball :=
  RoundedPolynomial.roundBall ((Constants.piRoot.ball.mul (erfcBall s n)).mul (Ball.exact s⁻¹))

theorem halfBall_contains (s : ℚ) (n : ℕ) (pi : piOk = true) (ok : erfcGuard s n = true)
    (pos : 0 < s) : (halfBall s n).Contains (gKernel (1/2) ((s : ℝ) ^ 2)) := by
  have sp : (0 : ℝ) < s := by exact_mod_cast pos
  have form := halfKernel_formula (pow_pos sp 2)
  rw [Real.sqrt_sq sp.le] at form
  rw [form]
  apply RoundedPolynomial.round_contains
  have m := Ball.contains_mul (Ball.contains_mul (sqrtPi_contains pi) (erfcBall_contains s n pi ok))
    (Ball.contains_exact s⁻¹)
  convert m using 1
  push_cast
  ring

/-- Tangent of `G(1/2, ·)` at the exact anchor `s²`, scaled to the variable
`q` with argument `π q`: intercept `(3/2)G + e^{-s²}` and penalty
`π (e^{-s²} + G/2) / s²`. -/
structure Tangent where
  intercept : ℚ
  penalty : ℚ
  deriving DecidableEq, Repr

def halfTangentBalls (s : ℚ) (n : ℕ) : Ball × Ball :=
  let g := halfBall s n
  let e := expBall (-(s * s))
  let x := s * s
  let i := ((Ball.exact (3 / 2)).mul g).add e
  let p := RoundedPolynomial.roundBall
    ((Constants.piInput.mul (e.add ((Ball.exact (1 / 2)).mul g))).mul (Ball.exact x⁻¹))
  (i, p)

def halfTangent (s : ℚ) (n : ℕ) : Tangent :=
  let b := halfTangentBalls s n
  ⟨lower96 (b.1.mid - b.1.rad), upper96 (max 0 (b.2.mid + b.2.rad))⟩

def halfTangentOk (s : ℚ) (n : ℕ) : Bool :=
  decide (0 < s) && erfcGuard s n && expOk (-(s * s))

theorem halfTangent_sound (s : ℚ) (n : ℕ) (pi : piOk = true) (ok : halfTangentOk s n = true) :
    0 ≤ (halfTangent s n).penalty ∧ ∀ q : ℝ, 0 < q →
      ((halfTangent s n).intercept : ℝ) - ((halfTangent s n).penalty : ℝ) * q ≤
        gKernel (1/2) (Real.pi * q) := by
  have h1 := Bool.and_eq_true_iff.mp ok
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have pos : 0 < s := of_decide_eq_true h2.1
  have sp : (0 : ℝ) < s := by exact_mod_cast pos
  have hx : (0 : ℝ) < (s : ℝ) ^ 2 := pow_pos sp 2
  have hg := halfBall_contains s n pi h2.2 pos
  have he := expBall_contains (-(s * s)) h1.2
  have hxq : (((s * s : ℚ)⁻¹ : ℚ) : ℝ) = ((s : ℝ) ^ 2)⁻¹ := by push_cast; ring
  -- Real values of intercept and penalty.
  set G := gKernel (1/2) ((s : ℝ) ^ 2) with hG
  set E := Real.exp (-((s : ℝ) ^ 2)) with hE
  have heE : (expBall (-(s * s))).Contains E := by
    have e : (((-(s * s)) : ℚ) : ℝ) = -((s : ℝ) ^ 2) := by push_cast; ring
    rw [e] at he
    exact he
  have hi : (halfTangentBalls s n).1.Contains (3 / 2 * G + E) := by
    have m := Ball.contains_add (Ball.contains_mul (Ball.contains_exact (3 / 2 : ℚ)) hg) heE
    simpa [halfTangentBalls] using m
  have hp : (halfTangentBalls s n).2.Contains (Real.pi * (E + 1 / 2 * G) * ((s : ℝ) ^ 2)⁻¹) := by
    apply RoundedPolynomial.round_contains
    have m := Ball.contains_mul (Ball.contains_mul Constants.piInput_sound
      (Ball.contains_add heE (Ball.contains_mul (Ball.contains_exact (1 / 2 : ℚ)) hg)))
      (Ball.contains_exact ((s * s)⁻¹))
    rw [hxq] at m
    simpa [halfTangentBalls] using m
  have ilo := (endpoints hi).1
  have phi := (endpoints hp).2
  refine ⟨(le_max_left (0 : ℚ) _).trans (le_upper96 _), ?_⟩
  intro q qpos
  -- Global tangent of the convex half kernel at the anchor `s²`.
  have tan := globalTangent KernelKind.half hx (mul_pos Real.pi_pos qpos)
  have kv : kernelValue KernelKind.half ((s : ℝ) ^ 2) = G := by
    simp [kernelValue, KernelKind.power, hG]
  have kq : kernelValue KernelKind.half (Real.pi * q) = gKernel (1/2) (Real.pi * q) := by
    simp [kernelValue, KernelKind.power]
  have ks : kernelSlope KernelKind.half ((s : ℝ) ^ 2) = -(E + 1 / 2 * G) / (s : ℝ) ^ 2 := by
    simp [kernelSlope, kernelValue, KernelKind.power, hG, hE]
  rw [kv, kq, ks] at tan
  have lin : G + -(E + 1 / 2 * G) / (s : ℝ) ^ 2 * (Real.pi * q - (s : ℝ) ^ 2) =
      (3 / 2 * G + E) - (Real.pi * (E + 1 / 2 * G) * ((s : ℝ) ^ 2)⁻¹) * q := by
    field_simp
    ring
  rw [lin] at tan
  have i96 : ((halfTangent s n).intercept : ℝ) ≤ 3 / 2 * G + E := by
    have a : ((lower96 ((halfTangentBalls s n).1.mid - (halfTangentBalls s n).1.rad) : ℚ) : ℝ) ≤
        (((halfTangentBalls s n).1.lo : ℚ) : ℝ) :=
      Rat.cast_le.mpr (lower96_le _)
    exact a.trans ilo
  have p96 : Real.pi * (E + 1 / 2 * G) * ((s : ℝ) ^ 2)⁻¹ ≤ ((halfTangent s n).penalty : ℝ) := by
    have a : (((halfTangentBalls s n).2.hi : ℚ) : ℝ) ≤
        ((upper96 (max 0 ((halfTangentBalls s n).2.mid + (halfTangentBalls s n).2.rad)) : ℚ) : ℝ) :=
      Rat.cast_le.mpr ((le_max_right _ _).trans (le_upper96 _))
    exact phi.trans a
  have pq := mul_le_mul_of_nonneg_right p96 qpos.le
  linarith only [tan, i96, pq]

end BccSharp.Coulomb.CompactCover.JLeaf
