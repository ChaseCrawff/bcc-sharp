import BccSharp.Cover.DirectSidecarFix
import BccSharp.Cover.Stage2Table

set_option autoImplicit false

/-! The fixed-point Direct and Stage2 checks in the corpus composition.

`initialWitnessCheckFix`, `checkWithDirectSidecarFix` and `checkWithStage2Fix` are
`initialWitnessCheck`, `checkWithDirectSidecar` and `checkWithStage2`
(`BccSharp.Cover.CoverEarlyDecode`) with the same arguments, the same witness
routing and the same typed operand tables; only the arithmetic at a paid
leaf is the fixed-point check:

* an original direct witness pays its addressed box by
  `DirectFix.directFix` (in place of `DirectRoute.check`);
* a Direct sidecar witness pays by `DirectSidecarFix.exactRealFix` or
  `DirectSidecarFix.momentFix`;
* a Stage2 witness pays by `Stage2Fix.bulkFix` or `Stage2Fix.phaseFix`.

Each is a `SoundCheck`, so a corpus check may use them wherever it uses the
originals. `checkWithStage2FixT` is the Stage2 check with shared tangents
(`Stage2TablePayload`, `bulkFixT`, `phaseFixT`). The `_of` lemmas reduce a paid
leaf of a `Plan` on the original direct and the Stage2 routes to the item
checks of the pilot modules (the sidecar route has none: its witness is a
`DirectSidecarProposal`, checked by `checkFix`). -/

namespace BccSharp.Coulomb.CompactCover.EarlyReplay
open Lean PacketDecode BccSharp BccSharp.Coverage

def DirectSidecarProposal.checkFix (b : Cell) : DirectSidecarProposal → Bool
  | .exactReal row => DirectSidecarFix.exactRealFix b row
  | .moment row => DirectSidecarFix.momentFix b row

theorem DirectSidecarProposal.soundFix (b : Cell) (r : DirectSidecarProposal) (p : Chart)
    (hp : b.Mem p) (gp : good p) (ok : r.checkFix b = true) : Route.result .strictFCC p := by
  cases r with
  | exactReal row => exact DirectSidecarFix.exactRealFix_sound b row p hp gp.1 ok
  | moment row => exact DirectSidecarFix.momentFix_sound b row p hp gp.1 ok

def Stage2Payload.checkFix (r : Stage2Payload) (b : Cell) : Bool :=
  match r.allocations with
  | none => Stage2Fix.bulkFix b r.base
  | some stakes => Stage2Fix.phaseFix b r.base stakes

theorem Stage2Payload.soundFix (r : Stage2Payload) (b : Cell) (p : Chart)
    (hp : b.Mem p) (gp : good p) (ok : r.checkFix b = true) : Route.result .strictFCC p := by
  cases phase : r.allocations with
  | none => exact Stage2Fix.bulkFix_sound b r.base p hp gp.1 (by simpa [Stage2Payload.checkFix, phase] using ok)
  | some stakes =>
    exact Stage2Fix.phaseFix_sound b r.base stakes p hp gp.1 (by simpa [Stage2Payload.checkFix, phase] using ok)

def initialWitnessCheckFix (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (w : WitnessRef) (b : Cell) : Bool :=
  match w.route with
  | .strictFCC =>
    if w.source = originalDirectBank then
      match direct w with
      | some addressed => sameCell addressed b && DirectFix.directFix b
      | none => false
    else false
  | _ => geometryWitnessCheck geometric w b

theorem initialWitnessCheckFix_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) : SoundCheck (initialWitnessCheckFix geometric direct) := by
  intro w b ok p bp gp
  cases w with
  | mk route source record =>
    cases route
    case strictFCC =>
      by_cases pin : source = originalDirectBank
      · subst pin
        cases raw : direct ⟨.strictFCC, originalDirectBank, record⟩ with
        | none => simp [initialWitnessCheckFix, raw] at ok
        | some addressed =>
          have h : (sameCell addressed b && DirectFix.directFix b) = true := by
            simpa [initialWitnessCheckFix, raw] using ok
          exact DirectFix.directFix_sound (Bool.and_eq_true_iff.mp h).2 bp gp.1
      · simp [initialWitnessCheckFix, pin] at ok
    all_goals
      refine geometryWitnessCheck_sound geometric _ b ?_ p bp gp
      exact ok

def checkWithDirectSidecarFix (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (w : WitnessRef) (b : Cell) : Bool :=
  if w.route = .strictFCC ∧ w.source = directSidecarBank then
    match sidecar w with
    | some operands => operands.checkFix b
    | none => false
  else initialWitnessCheckFix geometric direct w b

theorem checkWithDirectSidecarFix_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal) :
    SoundCheck (checkWithDirectSidecarFix geometric direct sidecar) := by
  intro w b ok p bp gp
  by_cases selected : w.route = .strictFCC ∧ w.source = directSidecarBank
  · cases raw : sidecar w with
    | none => simp [checkWithDirectSidecarFix, selected, raw] at ok
    | some operands =>
      have accepted : operands.checkFix b = true := by
        simpa [checkWithDirectSidecarFix, selected, raw] using ok
      rw [selected.1]
      exact DirectSidecarProposal.soundFix b operands p bp gp accepted
  · exact initialWitnessCheckFix_sound geometric direct _ _
      (by simpa [checkWithDirectSidecarFix, selected] using ok) p bp gp

def checkWithStage2Fix (prior : WitnessRef → Cell → Bool) (bulk : WitnessRef → Option Stage2Payload)
    (w : WitnessRef) (b : Cell) : Bool :=
  if w.route = .strictFCC ∧ isStage2Bank w.source = true then
    match bulk w with
    | some row => row.checkFix b
    | none => false
  else prior w b

theorem checkWithStage2Fix_sound {prior : WitnessRef → Cell → Bool} (base : SoundCheck prior)
    (bulk : WitnessRef → Option Stage2Payload) : SoundCheck (checkWithStage2Fix prior bulk) := by
  intro w b ok p bp gp
  by_cases expected : w.route = .strictFCC ∧ isStage2Bank w.source = true
  · cases row : bulk w with
    | none => simp [checkWithStage2Fix, expected, row] at ok
    | some operands =>
      rw [expected.1]
      exact operands.soundFix b p bp gp (by simpa [checkWithStage2Fix, expected, row] using ok)
  · exact base w b (by simpa [checkWithStage2Fix, expected] using ok) p bp gp

/-! ### Paid leaves from the item theorems -/

theorem sameCell_refl (b : Cell) : sameCell b b = true := decide_eq_true fun _ => ⟨rfl, rfl⟩

theorem initialWitnessCheckFix_of (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (owner : Nat) (b : Cell)
    (h : direct ⟨.strictFCC, originalDirectBank, owner⟩ = some b) (pass : DirectFix.directFix b = true) :
    initialWitnessCheckFix geometric direct ⟨.strictFCC, originalDirectBank, owner⟩ b = true := by
  simp [initialWitnessCheckFix, h, pass, sameCell_refl]

theorem checkWithStage2Fix_tangent_of (prior : WitnessRef → Cell → Bool) (bulk : WitnessRef → Option Stage2Payload)
    (w : WitnessRef) (b : Cell) (r : Stage2.Proposal) (route : w.route = .strictFCC)
    (bank : isStage2Bank w.source = true) (h : bulk w = some ⟨r, none⟩) (pass : Stage2Fix.bulkFix b r = true) :
    checkWithStage2Fix prior bulk w b = true := by
  simp [checkWithStage2Fix, route, bank, h, Stage2Payload.checkFix, pass]

theorem checkWithStage2Fix_phase_of (prior : WitnessRef → Cell → Bool) (bulk : WitnessRef → Option Stage2Payload)
    (w : WitnessRef) (b : Cell) (r : Stage2.Proposal) (stakes : Array Stage2.Allocation)
    (route : w.route = .strictFCC) (bank : isStage2Bank w.source = true) (h : bulk w = some ⟨r, some stakes⟩)
    (pass : Stage2Fix.phaseFix b r stakes = true) : checkWithStage2Fix prior bulk w b = true := by
  simp [checkWithStage2Fix, route, bank, h, Stage2Payload.checkFix, pass]

/-! ### Stage2 with shared tangents

`checkWithStage2FixT` is `checkWithStage2Fix` with a payload that also carries one
`Stage2Fix.CheckedTangent` per anchor row (`BccSharp.Cover.Stage2Table`); the rows
refer to shared table entries, so each tangent key is decided once. -/

/-- A Stage2 witness with the checked tangents of its anchor rows. -/
structure Stage2TablePayload where
  base : Stage2.Proposal
  allocations : Option (Array Stage2.Allocation)
  tangents : List Stage2Fix.CheckedTangent

def Stage2TablePayload.checkFix (r : Stage2TablePayload) (b : Cell) : Bool :=
  match r.allocations with
  | none => Stage2Fix.bulkFixT b r.base r.tangents
  | some stakes => Stage2Fix.phaseFixT b r.base stakes r.tangents

theorem Stage2TablePayload.soundFix (r : Stage2TablePayload) (b : Cell) (p : Chart)
    (hp : b.Mem p) (gp : good p) (ok : r.checkFix b = true) : Route.result .strictFCC p := by
  cases phase : r.allocations with
  | none =>
    exact Stage2Fix.bulkFixT_sound b r.base r.tangents p hp gp.1
      (by simpa [Stage2TablePayload.checkFix, phase] using ok)
  | some stakes =>
    exact Stage2Fix.phaseFixT_sound b r.base stakes r.tangents p hp gp.1
      (by simpa [Stage2TablePayload.checkFix, phase] using ok)

def checkWithStage2FixT (prior : WitnessRef → Cell → Bool) (bulk : WitnessRef → Option Stage2TablePayload)
    (w : WitnessRef) (b : Cell) : Bool :=
  if w.route = .strictFCC ∧ isStage2Bank w.source = true then
    match bulk w with
    | some row => row.checkFix b
    | none => false
  else prior w b

theorem checkWithStage2FixT_sound {prior : WitnessRef → Cell → Bool} (base : SoundCheck prior)
    (bulk : WitnessRef → Option Stage2TablePayload) : SoundCheck (checkWithStage2FixT prior bulk) := by
  intro w b ok p bp gp
  by_cases expected : w.route = .strictFCC ∧ isStage2Bank w.source = true
  · cases row : bulk w with
    | none => simp [checkWithStage2FixT, expected, row] at ok
    | some operands =>
      rw [expected.1]
      exact operands.soundFix b p bp gp (by simpa [checkWithStage2FixT, expected, row] using ok)
  · exact base w b (by simpa [checkWithStage2FixT, expected] using ok) p bp gp

theorem checkWithStage2FixT_tangent_of (prior : WitnessRef → Cell → Bool)
    (bulk : WitnessRef → Option Stage2TablePayload) (w : WitnessRef) (b : Cell) (r : Stage2.Proposal)
    (ts : List Stage2Fix.CheckedTangent) (route : w.route = .strictFCC) (bank : isStage2Bank w.source = true)
    (h : bulk w = some ⟨r, none, ts⟩) (pass : Stage2Fix.bulkFixT b r ts = true) :
    checkWithStage2FixT prior bulk w b = true := by
  simp [checkWithStage2FixT, route, bank, h, Stage2TablePayload.checkFix, pass]

theorem checkWithStage2FixT_phase_of (prior : WitnessRef → Cell → Bool)
    (bulk : WitnessRef → Option Stage2TablePayload) (w : WitnessRef) (b : Cell) (r : Stage2.Proposal)
    (stakes : Array Stage2.Allocation) (ts : List Stage2Fix.CheckedTangent) (route : w.route = .strictFCC)
    (bank : isStage2Bank w.source = true) (h : bulk w = some ⟨r, some stakes, ts⟩)
    (pass : Stage2Fix.phaseFixT b r stakes ts = true) : checkWithStage2FixT prior bulk w b = true := by
  simp [checkWithStage2FixT, route, bank, h, Stage2TablePayload.checkFix, pass]

end BccSharp.Coulomb.CompactCover.EarlyReplay
