import BccSharp.Cover.Stage3Stage6Hybrid

set_option autoImplicit false

/-! # Stage3: the `Z` and `correlated_phase` leaves

The Stage3 cover closes a terminal leaf by
the ambient margin (label `correlated_phase`) or else by the Adaptive bound
with 3 steps (label `Z`), both against the FCC energy (route `strictFCC`).
Here both labels are read by one hybrid check, as for Stage5b:

* the `supportGainCheck` on a proposed support, when the witness has a hint
  (`hintCheck`);
* when the witness has no hint or the hint fails, the box-built Jensen check of
  `BccSharp.Cover.JensenFix`, with the support built on the leaf itself: profile 2
  (screening `6/5`, mode limit `7`, cube `3`) for `stage3/Z` and profile 0 (`6/5`, `5`, `2`)
  for `stage3/correlated_phase`.

`stage3Check_sound : SoundCheck (stage3Check hint)` for every hint function; the check rejects
every other source (`stage3Check_other`). The hints are data; soundness does not depend on
them. -/

namespace BccSharp.Coulomb.CompactCover.Stage3Stage6
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover

/-- `(screening, mode limit, cube)` of the box-built fallback per Stage3 source. -/
def stage3Profile : String → Option (ℚ × ℚ × ℕ)
  | "stage3/Z" => some (6 / 5, 7, 3)
  | "stage3/correlated_phase" => some (6 / 5, 5, 2)
  | _ => none

theorem stage3Profile_eq_none (src : String) (h0 : src ≠ "stage3/Z")
    (h1 : src ≠ "stage3/correlated_phase") : stage3Profile src = none := by
  unfold stage3Profile
  split
  · exact absurd rfl h0
  · exact absurd rfl h1
  · rfl

/-- **The Stage3 check**: the proposed support first, then the box-built support with the
source's profile. -/
def stage3Check (hint : WitnessRef → Option SupportHint) (w : WitnessRef) (b : Cell) : Bool :=
  decide (w.route = .strictFCC) &&
    match stage3Profile w.source with
    | some (s, L, N) => hintCheck (hint w) b || Jensen.Fix.fLeafCheck s L N b b
    | none => false

theorem stage3Check_sound (hint : WitnessRef → Option SupportHint) : SoundCheck (stage3Check hint) := by
  intro w b ok p hp gp
  unfold stage3Check at ok
  obtain ⟨hr, hc⟩ := Bool.and_eq_true_iff.mp ok
  have hroute : w.route = .strictFCC := of_decide_eq_true hr
  rw [hroute]
  split at hc
  · simp only [Bool.or_eq_true] at hc
    rcases hc with h | h
    · exact hintCheck_sound h p hp gp
    · exact Jensen.Fix.fLeafCheck_route _ _ _ b b h p hp gp
  · exact absurd hc (by simp)

/-- **Dispatch rule.** Every witness whose source is not one of the two Stage3 strings is
rejected, whatever its route, cell and hint. -/
theorem stage3Check_other (hint : WitnessRef → Option SupportHint) (w : WitnessRef) (b : Cell)
    (h0 : w.source ≠ "stage3/Z") (h1 : w.source ≠ "stage3/correlated_phase") :
    stage3Check hint w b = false := by
  unfold stage3Check
  rw [stage3Profile_eq_none _ h0 h1]
  simp

end BccSharp.Coulomb.CompactCover.Stage3Stage6
