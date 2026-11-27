import BccSharp.Cover.JensenFixSound

set_option autoImplicit false

/-! # Stage5b phase leaves: profiles, addresses and the witness check

The Stage5b phase pass subdivides each of the 512
ranked Stage5a rectangles at exact midpoints, on the axis of largest weighted
width (`pickAxis`, weights `(4, 4, 1, 1, 1, 2, 2, 2)`, first maximum), and
accepts a leaf when the phase-secant lower bound with one of three profiles
`(screening, cube, mode limit)` exceeds the Constants FCC energy. Its support box is
the leaf itself.

* `descendStage5b` replays the subdivision exactly; `sameCell (descendStage5b root path)
  leaf = true` ties a leaf literal to its ranked root and path.
* `stage5bPhaseCheck` reads witnesses `stage5b/phase/0`, `stage5b/phase/1`,
  `stage5b/phase/2` and `stage5b/whole_above` (the optical sweep's direct whole-box
  test, profile 0) on route `strictFCC` and runs the fixed-point Jensen check
  `Fix.fLeafCheck` on the witness's own cell; `stage5bPhaseCheck_sound` is its
  `SoundCheck`. It rejects every other source. -/

namespace BccSharp.Coulomb.CompactCover.Stage5bPhase
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.Jensen

/-! ### The subdivision -/

def weights : Fin 8 → ℚ := ![4, 4, 1, 1, 1, 2, 2, 2]

def axisScore (b : Cell) (i : Axis) : ℚ := (b.hi i - b.lo i) * weights i

/-- The first axis of largest weighted width. -/
def pickAxis (b : Cell) : Axis :=
  (List.finRange 8).foldl (fun best j => if axisScore b best < axisScore b j then j else best) 0

/-- Exact midpoint descent along a path of child bits (`false` = lower). -/
def descendStage5b : Cell → List Bool → Cell
  | b, [] => b
  | b, bit :: rest => descendStage5b ((Cut.dyadic (pickAxis b)).child b bit) rest

/-- The optical sweep splits only
the five shape axes, with weights `(5/2, 5/2, 1, 1, 1)`, first maximum. -/
def opticalWeights : Fin 8 → ℚ := ![5 / 2, 5 / 2, 1, 1, 1, 0, 0, 0]

def opticalAxis (b : Cell) : Axis :=
  ([0, 1, 2, 3, 4] : List Axis).foldl (fun best a =>
    if (b.hi best - b.lo best) * opticalWeights best < (b.hi a - b.lo a) * opticalWeights a then a
    else best) 0

def descendOptical : Cell → List Bool → Cell
  | b, [] => b
  | b, bit :: rest => descendOptical ((Cut.dyadic (opticalAxis b)).child b bit) rest

/-! ### Boxes without reduced points -/

/-- The reduction test `r₁² ≤ |R e₂|² = r₁² x² + r₂²` fails on the whole box:
`lo₀² (1 - hi₂²) > hi₁²` with nonnegative shape coordinates. -/
def notReducedE2 (b : Cell) : Bool :=
  decide (0 ≤ b.lo 0 ∧ 0 ≤ b.lo 1 ∧ 0 ≤ b.lo 2 ∧ b.hi 2 ≤ 1 ∧
    b.hi 1 ^ 2 < b.lo 0 ^ 2 * (1 - b.hi 2 ^ 2))

/-- A box that passes `notReducedE2` contains no reduced point, so a statement
about its `good` points is vacuous. -/
theorem notReducedE2_sound (b : Cell) (h : notReducedE2 b = true) (p : Chart) (hp : b.Mem p) :
    ¬ reductionInequalities p := by
  obtain ⟨l0, l1, l2, h2, key⟩ := of_decide_eq_true h
  have m0 := hp 0
  have m1 := hp 1
  have m2 := hp 2
  have r0 : (0 : ℝ) ≤ b.lo 0 := by exact_mod_cast l0
  have r1 : (0 : ℝ) ≤ b.lo 1 := by exact_mod_cast l1
  have r2 : (0 : ℝ) ≤ b.lo 2 := by exact_mod_cast l2
  have rh2 : ((b.hi 2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h2
  have rkey : ((b.hi 1 : ℚ) : ℝ) ^ 2 < ((b.lo 0 : ℚ) : ℝ) ^ 2 * (1 - ((b.hi 2 : ℚ) : ℝ) ^ 2) := by
    have := (Rat.cast_lt (K := ℝ)).mpr key
    push_cast at this
    exact this
  intro hr
  have e := hr.1 ![0, 1, 0] (by decide)
  have e2 : BccSharp.Coulomb.sq ((chartBasis p).mulVec (castVec ![0, 1, 0])) =
      (p 0 * p 2) ^ 2 + (p 1) ^ 2 := by
    simp [BccSharp.Coulomb.sq, chartBasis, castVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  rw [e2] at e
  have p0 : 0 ≤ p 0 := r0.trans m0.1
  have p1 : 0 ≤ p 1 := r1.trans m1.1
  have p2 : 0 ≤ p 2 := r2.trans m2.1
  have s0 : ((b.lo 0 : ℚ) : ℝ) ^ 2 ≤ p 0 ^ 2 := pow_le_pow_left₀ r0 m0.1 2
  have s1 : p 1 ^ 2 ≤ ((b.hi 1 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ p1 m1.2 2
  have s2 : p 2 ^ 2 ≤ ((b.hi 2 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ p2 m2.2 2
  have h2' : 0 ≤ 1 - ((b.hi 2 : ℚ) : ℝ) ^ 2 := by nlinarith
  have m : ((b.lo 0 : ℚ) : ℝ) ^ 2 * (1 - ((b.hi 2 : ℚ) : ℝ) ^ 2) ≤ p 0 ^ 2 * (1 - p 2 ^ 2) := by
    have a := mul_le_mul_of_nonneg_right s0 h2'
    have c := mul_le_mul_of_nonneg_left (show 1 - ((b.hi 2 : ℚ) : ℝ) ^ 2 ≤ 1 - p 2 ^ 2 by linarith)
      (sq_nonneg (p 0))
    linarith
  nlinarith

/-! ### Profiles and the witness check -/

/-- `(screening, mode limit, cube)` of the phase sweep. -/
def profile : String → Option (ℚ × ℚ × ℕ)
  | "stage5b/phase/0" => some (6 / 5, 5, 2)
  | "stage5b/phase/1" => some (1, 6, 2)
  | "stage5b/phase/2" => some (6 / 5, 7, 3)
  | "stage5b/whole_above" => some (6 / 5, 5, 2)
  | _ => none

/-- The Stage5b phase witness check: the Jensen support built on the cell itself. -/
def stage5bPhaseCheck (w : WitnessRef) (b : Cell) : Bool :=
  decide (w.route = .strictFCC) &&
    match profile w.source with
    | some (s, L, N) => Fix.fLeafCheck s L N b b
    | none => false

theorem stage5bPhaseCheck_sound : SoundCheck stage5bPhaseCheck := by
  intro w b ok p hp gp
  unfold stage5bPhaseCheck at ok
  obtain ⟨hr, hc⟩ := Bool.and_eq_true_iff.mp ok
  have hroute : w.route = .strictFCC := of_decide_eq_true hr
  rw [hroute]
  split at hc
  · exact Fix.fLeafCheck_route _ _ _ b b hc p hp gp
  · exact absurd hc (by simp)

end BccSharp.Coulomb.CompactCover.Stage5bPhase
