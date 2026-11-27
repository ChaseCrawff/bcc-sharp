import BccSharp.Cover.Stage5bPhase
import BccSharp.Cover.OverlayCorpusPrefix

set_option autoImplicit false

/-! # Stage3–Stage5b share of `later`, and the Stage6 checker

**`later`.** `corpusCheck … later` (`BccSharp.Cover.OverlayCorpusPrefix`) needs a sound
check for the witnesses of Adaptive and the stages Stage3–Stage5b. This module gives
its share:

* `laterStage3Stage5b pending = orCheck stage5bPhaseCheck pending`. The Stage5b phase
  leaves and the optical `whole_above` tiles are checked by the fixed-point
  Jensen evaluator (sources `stage5b/phase/0`, `stage5b/phase/1`, `stage5b/phase/2`,
  `stage5b/whole_above`, route `strictFCC`). The families whose evaluators are
  not written yet (Stage3 `Z` and correlated phase, the Stage4 sources, Stage5a
  `anchored`, the other Stage5b optical tiles) enter through `pending`, any
  sound check. `laterNow` takes `pending` false.
* `laterStage3Stage5b_sound`, `laterNow_sound`: `SoundCheck`.
* `later_compose`: the whole `later` slot is `orCheck adaptiveRoute (laterStage3Stage5b
  pending)` for any sound check `adaptiveRoute` of the Adaptive stages, and is sound.

Dispatch rule: `stage5bPhaseCheck` accepts only the four exact sources above,
with their profiles (`profile_accepted`). Every other source has no profile
(`profile_eq_none`) and gets `false` from it (`stage5bPhaseCheck_rejects`,
`stage5bPhaseCheck_other`); for example `adaptiveRoute`, the tag of the Adaptive check
(`profile_adaptive`). So the composition by `orCheck` needs no ordering.

**Stage6.** `assemble_from_overlay_corpus` needs `Stage6CheckerSound early`.
`stage6Check dEval` checks an `F` entry (`compare = fcc`) with the same Jensen
evaluator on the entry's support box (`source`) and leaf (`target`), with the
proposal's profile, and hands a `D` entry (`compare = deficit`) to a
defect evaluator `dEval`. `stage6Check_sound` proves `Stage6CheckerSound` from
`Stage6DSound dEval` alone. The `D` entries need a registered defect cap; that
evaluator is not written yet. -/

namespace BccSharp.Coulomb.CompactCover.Stage3Stage6
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayCorpus (orCheck orCheck_sound)

/-! ### The `later` share -/

/-- This module\'s share of `later`: the Stage5b phase leaves, and `pending` for
the families still to be written. -/
def laterStage3Stage5b (pending : WitnessRef → Cell → Bool) : WitnessRef → Cell → Bool :=
  orCheck Stage5bPhase.stage5bPhaseCheck pending

theorem laterStage3Stage5b_sound {pending : WitnessRef → Cell → Bool} (h : SoundCheck pending) :
    SoundCheck (laterStage3Stage5b pending) :=
  orCheck_sound Stage5bPhase.stage5bPhaseCheck_sound h

/-- The share with nothing pending. -/
def laterNow : WitnessRef → Cell → Bool := laterStage3Stage5b fun _ _ => false

theorem laterNow_sound : SoundCheck laterNow :=
  laterStage3Stage5b_sound (fun _ _ h => absurd h (by simp))

/-- The Stage5b check rejects every witness whose source has no profile. -/
theorem stage5bPhaseCheck_rejects (w : WitnessRef) (b : Cell)
    (h : Stage5bPhase.profile w.source = none) : Stage5bPhase.stage5bPhaseCheck w b = false := by
  unfold Stage5bPhase.stage5bPhaseCheck
  rw [h]
  simp

/-- The tag `adaptiveRoute` of the Adaptive check has no Stage5b profile (kernel evaluation
of the exact-string match). -/
theorem profile_adaptive : Stage5bPhase.profile "adaptive-source" = none := by decide +kernel

/-- The four accepted sources and their profiles `(screening, mode limit, cube)`
(kernel evaluation of the exact-string match). -/
theorem profile_accepted :
    Stage5bPhase.profile "stage5b/phase/0" = some (6 / 5, 5, 2) ∧
      Stage5bPhase.profile "stage5b/phase/1" = some (1, 6, 2) ∧
      Stage5bPhase.profile "stage5b/phase/2" = some (6 / 5, 7, 3) ∧
      Stage5bPhase.profile "stage5b/whole_above" = some (6 / 5, 5, 2) := by
  decide +kernel

/-- Every source other than the four exact strings has no Stage5b profile. -/
theorem profile_eq_none (src : String) (h0 : src ≠ "stage5b/phase/0")
    (h1 : src ≠ "stage5b/phase/1") (h2 : src ≠ "stage5b/phase/2")
    (h3 : src ≠ "stage5b/whole_above") : Stage5bPhase.profile src = none := by
  unfold Stage5bPhase.profile
  split <;> simp_all

/-- **Dispatch rule.** The Stage5b check rejects every witness whose source is not
one of the four exact strings, whatever its route and cell. -/
theorem stage5bPhaseCheck_other (w : WitnessRef) (b : Cell) (h0 : w.source ≠ "stage5b/phase/0")
    (h1 : w.source ≠ "stage5b/phase/1") (h2 : w.source ≠ "stage5b/phase/2")
    (h3 : w.source ≠ "stage5b/whole_above") : Stage5bPhase.stage5bPhaseCheck w b = false :=
  stage5bPhaseCheck_rejects w b (profile_eq_none _ h0 h1 h2 h3)

/-- **The `later` slot.** Any sound check of the Adaptive stages composes with this
share. -/
theorem later_compose {adaptiveRoute pending : WitnessRef → Cell → Bool} (h17 : SoundCheck adaptiveRoute)
    (hp : SoundCheck pending) : SoundCheck (orCheck adaptiveRoute (laterStage3Stage5b pending)) :=
  orCheck_sound h17 (laterStage3Stage5b_sound hp)

/-! ### The Stage6 checker -/

/-- The three supports, as `(screening, mode limit, cube)`:
`(6/5, 5, 2)` built on the box, the alternative `(1, 6, 2)` and the extended
`(6/5, 7, 3)`. -/
def stage6Profile : Fin 3 → ℚ × ℚ × ℕ := ![(6 / 5, 5, 2), (1, 6, 2), (6 / 5, 7, 3)]

/-- The `F` test: the Jensen support on the entry's support box exceeds `e_FCC`
at every corner of its target box. -/
def stage6FCheck (q : Stage6Request) : Bool :=
  Jensen.Fix.fLeafCheck (stage6Profile q.proposal.profile).1 (stage6Profile q.proposal.profile).2.1
    (stage6Profile q.proposal.profile).2.2 q.proposal.source q.proposal.target

/-- A defect evaluator for the `D` entries is sound when it accepts only
requests whose target box has strictly positive deficit at every good point. -/
def Stage6DSound (dEval : Stage6Request → Bool) : Prop :=
  ∀ q, dEval q = true → ∀ p, q.proposal.target.Mem p → good p → 0 < deficit (chartPoint p)

/-- The Stage6 checker: `F` entries by the Jensen evaluator, `D` entries by `dEval`. -/
def stage6Check (dEval : Stage6Request → Bool) : Stage6Checker := fun q =>
  match q.proposal.compare with
  | .fcc => stage6FCheck q
  | .deficit => dEval q

/-- **`Stage6CheckerSound`** for the Stage6 checker, from the soundness of the defect
evaluator alone. -/
theorem stage6Check_sound {dEval : Stage6Request → Bool} (hd : Stage6DSound dEval) :
    Stage6CheckerSound (stage6Check dEval) := by
  intro q _ ok p hp gp
  unfold stage6Check at ok
  unfold Stage6Proposal.route
  cases hc : q.proposal.compare with
  | fcc =>
    rw [hc] at ok
    exact Jensen.Fix.fLeafCheck_sound _ _ _ _ _ ok p hp gp.1
  | deficit =>
    rw [hc] at ok
    exact hd q ok p hp gp

/-- With no `D` evaluator yet: only `F` entries are accepted. -/
def stage6Now : Stage6Checker := stage6Check fun _ => false

theorem stage6Now_sound : Stage6CheckerSound stage6Now :=
  stage6Check_sound fun _ h => absurd h (by simp)

end BccSharp.Coulomb.CompactCover.Stage3Stage6
