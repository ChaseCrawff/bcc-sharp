import BccSharp.Cover.CoverEarlyHandoff
import BccSharp.Cover.CoverPacketDecode
import BccSharp.Cover.CoverDirectSeries
import BccSharp.Cover.CoverDirectMoment
import BccSharp.Cover.Stage2Phase

set_option autoImplicit false

/-! Exact typed inputs of the prefix. Labels select
the arithmetic inventory entry. A JSON object does not establish a leaf. -/

namespace BccSharp.Coulomb.CompactCover.EarlyReplay
open Lean PacketDecode BccSharp.Coverage

abbrev WitnessDecoder := Json → Parse WitnessRef

def normalizedProposal (j : Json) : Parse NormalizedProposal := do
  let witness ← j.getObjVal? "witness"
  let m ← get witness "m" (vector 3 Json.getInt?)
  let method ← get witness "kind" Json.getStr?
  let spec ← match method with
    | "full" => pure (BravaisCover.ReductionWitness.full m)
    | "projected" => pure (.projected (m 1) (m 2))
    | _ => throw "unrecognized normalized Direct witness"
  pure ⟨⟨← get j "lo" (vector 5 rat),← get j "hi" (vector 5 rat)⟩,spec,← get witness "upper" rat⟩

/-- The Direct geometry packet shares witnesses across owners. Preserve the
packet and owner as identity and return the exact normalized payload. -/
def decodeReductionEnvelope (j : Json) : Parse (WitnessRef × Option NormalizedProposal) := do
  let source ← get j "bank" Json.getStr?
  let owner ← get j "owner" Json.getNat?
  let payload ← match ← get j "route" Json.getStr? with
    | "invalid_reduced" | "G" => pure none
    | "invalid_normalized" =>
      let rec ← j.getObjVal? "record"
      some <$> position rec 1 normalizedProposal
    | _ => throw "prefix row requires a separate arithmetic evaluator"
  pure (⟨.invalidReduction,source,owner⟩,payload)

def originalDirectBank : String := "direct/global-extended-frontier.json.gz"

def decodeDirectEnvelope (j : Json) : Parse (WitnessRef × Cell) := do
  let source ← get j "bank" Json.getStr?
  let route ← get j "route" Json.getStr?
  if source≠ originalDirectBank ∨ (route≠"energy_direct" ∧ route≠"energy_above_fcc") then
    throw "direct positive packet is for the original Direct route"
  let raw ← j.getObjVal? "record"
  let format ← get raw "format" Json.getStr?
  let cutoffs ← get raw "cutoffs" (fun a => do (← a.getArr?).toList.mapM Json.getNat?)
  if format≠"directRoute-positive-direct-v1" ∨ cutoffs≠[1,2] then throw "unsupported Direct positive sum recipe"
  pure (⟨.strictFCC,source,← get j "owner" Json.getNat?⟩,← get raw "box" box)

def directSidecarBank : String := "direct/direct-moment-sidecar.json"

def readExactOperands (raw : Json) : Parse DirectRoute.ExactRealProposal := do
  let radius ← get raw "n0" Json.getNat?
  let format ← get raw "format" Json.getStr?
  if radius≠1 ∨ format≠"directRoute-radius-one-sidecar-v1" then throw "unsupported Direct sidecar cube"
  let readTerm (row : Json) : Parse DirectRoute.RealOperand := do
    pure ⟨← get row "m" (vector 3 Json.getInt?),← get row "shifted" Json.getBool?,
      ← get row "multiplicity" Json.getNat?,← get row "qmax" rat,
      ← get row "kernel_lower" rat,← get row "slope_lower" rat⟩
  let terms ← get raw "terms" (fun a => do (← a.getArr?).toList.mapM readTerm)
  pure ⟨← get raw "box" box,terms⟩

inductive DirectSidecarProposal where
  | exactReal (row : DirectRoute.ExactRealProposal)
  | moment (row : DirectRoute.MomentProposal)

def decodeDirectSidecarEnvelope (j : Json) : Parse (WitnessRef × DirectSidecarProposal) := do
  let source ← get j "bank" Json.getStr?
  let route ← get j "route" Json.getStr?
  if source≠ directSidecarBank then throw "unexpected Direct sidecar source"
  let raw ← j.getObjVal? "record"
  let data ← readExactOperands raw
  let owner ← get j "owner" Json.getNat?
  let ref : WitnessRef := ⟨.strictFCC,source,owner⟩
  match route with
  | "energy_exact_real_n1" => pure (ref,.exactReal data)
  | "energy_direct_moment_n1" =>
    let geometry ← raw.getObjVal? "geometry"
    pure (ref,.moment ⟨data,← get geometry "maximum" rat,← get geometry "maximizing_corner" (vector 8 rat)⟩)
  | _ => throw "unrecognized Direct sidecar route"

def DirectSidecarProposal.check (b : Cell) : DirectSidecarProposal → Bool
  | .exactReal row => DirectRoute.exactRealCheck b row
  | .moment row => DirectRoute.momentCheck b row

theorem DirectSidecarProposal.sound (b : Cell) (r : DirectSidecarProposal) (p : Chart)
    (hp : b.Mem p) (gp : good p) (ok : r.check b=true) : Route.result .strictFCC p := by
  cases r with
  | exactReal row => exact DirectRoute.exactRealCheck_sound b row p hp gp.1 ok
  | moment row => exact DirectRoute.momentCheck_sound b row p hp gp.1 ok

def isStage2Bank (source : String) : Bool :=
  source.startsWith "overlay/bulk-batches/batch_" && source.endsWith ".json.gz"

structure Stage2Payload where
  base : Stage2.Proposal
  allocations : Option (Array Stage2.Allocation)

def Stage2Payload.check (r : Stage2Payload) (b : Cell) : Bool :=
  match r.allocations with
  | none => Stage2.bulkCheck b r.base
  | some stakes => Stage2.phaseCheck b r.base stakes

theorem Stage2Payload.sound (r : Stage2Payload) (b : Cell) (p : Chart)
    (hp : b.Mem p) (gp : good p) (ok : r.check b=true) : Route.result .strictFCC p := by
  cases phase : r.allocations with
  | none => exact Stage2.bulkCheck_sound b r.base p hp gp.1 (by simpa [Stage2Payload.check,phase] using ok)
  | some stakes => exact Stage2.phaseCheck_sound b r.base stakes p hp gp.1 (by simpa [Stage2Payload.check,phase] using ok)

def decodeStage2Envelope (j : Json) : Parse (WitnessRef × Stage2Payload) := do
  let source ← get j "bank" Json.getStr?
  let route ← get j "route" Json.getStr?
  if ! isStage2Bank source then throw "unexpected Stage2 bulk bank"
  if route≠"bulk_tangent" ∧ route≠"bulk_phase_budget" then throw "unsupported Stage2 route"
  let owner ← get j "owner" Json.getNat?
  let raw ← j.getObjVal? "record"
  let format ← get raw "format" Json.getStr?
  let payloadRoute ← get raw "route" Json.getStr?
  let radius ← get raw "radius" Json.getNat?
  let grid ← get raw "anchor_grid" Json.getNat?
  let bits ← get raw "anchor_policy_bits" Json.getNat?
  let w ← get raw "batch" Json.getNat?
  if format≠"stage2-bulk-v1" ∨ payloadRoute≠route ∨ radius≠2 ∨ grid≠ Stage2.anchorGrid ∨ bits≠256 ∨ owner/32768≠w then
    throw "Stage2 source owner or anchor policy changed"
  let readAnchor (row : Json) : Parse Stage2.AnchorRow := do
    let fam ← match ← get row "family" Json.getStr? with
      | "cross" => pure Stage2.Family.cross
      | "period" => pure Stage2.Family.period
      | "reciprocal" => pure Stage2.Family.reciprocal
      | _ => throw "unknown Stage2 mode family"
    pure ⟨⟨fam,← get row "mode" (vector 3 Json.getInt?)⟩,← get row "ticks" Json.getNat?⟩
  let anchors ← get raw "anchors" (fun a => do (← a.getArr?).toList.mapM readAnchor)
  let base : Stage2.Proposal := ⟨← get raw "box" box,anchors⟩
  if route="bulk_tangent" then
    pure (⟨.strictFCC,source,owner⟩,⟨base,none⟩)
  else
    let readAllocation (row : Json) : Parse Stage2.Allocation := do
      pure ⟨← get row "a" (vector 3 Json.getInt?),← get row "b" (vector 3 Json.getInt?),
        ← get row "c" (vector 3 Json.getInt?),← get row "minus_b" Json.getBool?,
        ← get row "minus_c" Json.getBool?,← get row "amount" rat⟩
    let stakes ← get raw "allocations" (fun a => do (← a.getArr?).mapM readAllocation)
    if stakes.isEmpty then throw "Stage2 phase row has no allocation proposals"
    pure (⟨.strictFCC,source,owner⟩,⟨base,some stakes⟩)

inductive PrefixPayload where
  | geometry (ref : WitnessRef) (normalized : Option NormalizedProposal)
  | direct (ref : WitnessRef) (addressed : Cell)
  | sidecar (ref : WitnessRef) (operands : DirectSidecarProposal)
  | stage2 (ref : WitnessRef) (operands : Stage2Payload)

def PrefixPayload.ref : PrefixPayload → WitnessRef
  | .geometry w _ | .direct w _ | .sidecar w _ | .stage2 w _ => w

def readPrefixPayload (j : Json) : Parse PrefixPayload := do
  match ← get j "route" Json.getStr? with
  | "energy_direct" | "energy_above_fcc" =>
    let (ref,domain) ← decodeDirectEnvelope j
    pure (.direct ref domain)
  | "energy_exact_real_n1" | "energy_direct_moment_n1" =>
    let (ref,operands) ← decodeDirectSidecarEnvelope j
    pure (.sidecar ref operands)
  | "bulk_tangent" | "bulk_phase_budget" =>
    let (ref,operands) ← decodeStage2Envelope j
    pure (.stage2 ref operands)
  | _ =>
    let (ref,normalized) ← decodeReductionEnvelope j
    pure (.geometry ref normalized)

/-- This dispatcher accepts only the reduction and the original Direct
direct route. For a direct record it rechecks all eight box endpoints;
the cutoff and every arithmetic operand are recomputed in Lean. -/
def initialWitnessCheck (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (w : WitnessRef) (b : Cell) : Bool :=
  match w.route with
  | .strictFCC =>
    if w.source= originalDirectBank then
      match direct w with
      | some addressed => sameCell addressed b && DirectRoute.check b
      | none => false
    else false
  | _ => geometryWitnessCheck geometric w b

theorem initialWitnessCheck_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) : SoundCheck (initialWitnessCheck geometric direct) := by
  intro w b ok p bp gp
  cases w with
  | mk route source record =>
    cases route
    case strictFCC =>
      by_cases pin : source= originalDirectBank
      · subst pin
        cases raw : direct ⟨.strictFCC,originalDirectBank,record⟩ with
        | none => simp [initialWitnessCheck,raw] at ok
        | some addressed =>
          have h : (sameCell addressed b && DirectRoute.check b)=true := by
            simpa [initialWitnessCheck,raw] using ok
          exact DirectRoute.check_sound b (Bool.and_eq_true_iff.mp h).2 p bp gp.1
      · simp [initialWitnessCheck,pin] at ok
    -- Every other route is the geometry check of the same witness.
    all_goals
      refine geometryWitnessCheck_sound geometric _ b ?_ p bp gp
      exact ok

def checkWithDirectSidecar (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (w : WitnessRef) (b : Cell) : Bool :=
  if w.route=.strictFCC ∧ w.source= directSidecarBank then
    match sidecar w with
    | some operands => operands.check b
    | none => false
  else initialWitnessCheck geometric direct w b

theorem checkWithDirectSidecar_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal) :
    SoundCheck (checkWithDirectSidecar geometric direct sidecar) := by
  intro w b ok p bp gp
  by_cases selected : w.route=.strictFCC ∧ w.source= directSidecarBank
  · cases raw : sidecar w with
    | none => simp [checkWithDirectSidecar,selected,raw] at ok
    | some operands =>
      have accepted : operands.check b=true := by
        simpa [checkWithDirectSidecar,selected,raw] using ok
      rw [selected.1]
      exact DirectSidecarProposal.sound b operands p bp gp accepted
  · exact initialWitnessCheck_sound geometric direct _ _ (by simpa [checkWithDirectSidecar,selected] using ok) p bp gp

def checkWithStage2 (prior : WitnessRef → Cell → Bool) (bulk : WitnessRef → Option Stage2Payload)
    (w : WitnessRef) (b : Cell) : Bool :=
  if w.route=.strictFCC ∧ isStage2Bank w.source=true then
    match bulk w with
    | some row => row.check b
    | none => false
  else prior w b

theorem checkWithStage2_sound {prior : WitnessRef → Cell → Bool} (base : SoundCheck prior)
    (bulk : WitnessRef → Option Stage2Payload) : SoundCheck (checkWithStage2 prior bulk) := by
  intro w b ok p bp gp
  by_cases expected : w.route=.strictFCC ∧ isStage2Bank w.source=true
  · cases row : bulk w with
    | none => simp [checkWithStage2,expected,row] at ok
    | some operands =>
      rw [expected.1]
      exact operands.sound b p bp gp (by simpa [checkWithStage2,expected,row] using ok)
  · exact base w b (by simpa [checkWithStage2,expected] using ok) p bp gp

def identityMotion : ChartMotion := ⟨false,fun _ => 0⟩

def slotChild (k : Key) (a : Axis) (side : Bool) : Key :=
  let digit := 2*a.val+(if side then 1 else 0)
  let char := Char.ofNat (if digit<10 then '0'.toNat+digit else 'a'.toNat+digit-10)
  if k.replacement=0 then {k with seed := k.seed.push char}
  else {k with path := k.path++[digit]}

def decodePlan (decodeWitness : WitnessDecoder) (shard : String → Option Json) :
    Nat → Cell → Key → Json → Parse Plan
  | 0,_,_,_ => throw "early coverage tree exceeds its decode limit"
  | fuel+1,b,k,j => do
    match ← get j "tag" Json.getStr? with
    | "hold" => pure (.hold k)
    | "close" =>
      let w ← j.getObjVal? "leaf"
      -- A complete hard-root trace is spliced at its actual prefix.
      match (get w "tag" Json.getStr?).toOption with
      | some "closed_tree" => get w "tree" (decodePlan decodeWitness shard fuel b k)
      | some "hold_owner" => pure (.hold ⟨← get w "owner" Json.getNat?,"",0,[]⟩)
      | _ => pure (.pay k ⟨← decodeWitness w,b,identityMotion,b⟩)
    | "shard" =>
      let pre ← get j "path" Json.getStr?
      let s ← (shard pre).getDM (throw "missing Direct root shard")
      let origin ← get s "input" box
      if (decide (pre≠k.seed) || !sameCell origin b) then throw "Direct root shard endpoints or prefix differ"
      get s "trace" (decodePlan decodeWitness shard fuel b k)
    | "split" =>
      let a ← get j "axis" axis
      let cut := Cut.dyadic a
      pure (.split cut
        (← get j "low" (decodePlan decodeWitness shard fuel (cut.child b false) (slotChild k a false)))
        (← get j "high" (decodePlan decodeWitness shard fuel (cut.child b true) (slotChild k a true))))
    | _ => throw "unknown early coverage node"

def decodeStageRow (decodeWitness : WitnessDecoder) (depth : Nat) (j : Json) : Parse StageRow := do
  let parent ← get j "input" atom
  let plan ← get j "trace" (decodePlan decodeWitness (fun _ => none) depth parent.box parent.address)
  pure ⟨parent.asCell,plan⟩

def decodeDirectOverlayStageRow (depth : Nat) (j : Json) : Parse StageRow :=
  decodeStageRow (fun row => PrefixPayload.ref <$> readPrefixPayload row) depth j

def decodeRoot (decodeWitness : WitnessDecoder) (shard : String → Option Json) (depth : Nat)
    (j : Json) : Parse Plan := do
  let b ← get j "input" box
  if !sameCell b root then throw "Direct does not start at the Series root"
  get j "trace" (decodePlan decodeWitness shard depth root ⟨0,"",0,[]⟩)

def indexDirect (rows : List Json) : Parse (Std.HashMap Nat Cell) :=
  rows.foldlM (fun bank row => do
    let (w,b) ← decodeDirectEnvelope row
    if bank.contains w.record then throw "duplicate Direct direct owner"
    pure (bank.insert w.record b)) (∅ : Std.HashMap Nat Cell)

def indexDirectSidecar (rows : List Json) : Parse (Std.HashMap Nat DirectSidecarProposal) :=
  rows.foldlM (fun bank row => do
    let (w,b) ← decodeDirectSidecarEnvelope row
    if bank.contains w.record then throw "duplicate Direct sidecar owner"
    pure (bank.insert w.record b)) (∅ : Std.HashMap Nat DirectSidecarProposal)

def indexStage2 (rows : List Json) : Parse (Std.HashMap Nat Stage2Payload) :=
  rows.foldlM (fun bank row => do
    let (w,b) ← decodeStage2Envelope row
    if bank.contains w.record then throw "duplicate Stage2 bulk owner"
    pure (bank.insert w.record b)) (∅ : Std.HashMap Nat Stage2Payload)

/-- Actual original Direct packet entry point. Addressed scalar rows have a
separate index to allow independently staged owner shards. -/
def decodeDirectRoot (shard : String → Option Json) (depth : Nat) (j : Json) : Parse Plan :=
  decodeRoot (fun row => PrefixPayload.ref <$> readPrefixPayload row) shard depth j

def runDirect (p : Plan) (bank : Std.HashMap Nat Cell) : Option Snapshot :=
  p.run (initialWitnessCheck (fun _ => none) (fun w => bank.get? w.record)) root

theorem runDirect_sound (p : Plan) (bank : Std.HashMap Nat Cell) (out : Snapshot)
    (ok : runDirect p bank=some out) : out.Sound ∧ (∀ x, root.Mem x → out.Covers x) :=
  Plan.run_sound _ (initialWitnessCheck_sound _ _) p root out ok

def decodeCarve (decodeWitness : WitnessDecoder) (input : AddressedCell)
    (paidKey : Key) (nextKey : Nat → Key) (j : Json) : Parse (Nat × ClipRow) := do
  let parent ← get j "parent" box
  if !sameCell input.cell parent then throw "carve starts at other endpoints"
  let paid ← get j "box" box
  let proof ← j.getObjVal? "proof"
  let move : ChartMotion := ⟨← get proof "reflect" Json.getBool?,← get proof "shift" (vector 3 Json.getInt?)⟩
  let certificate : CertifiedClip := ⟨← get proof "witness" decodeWitness,← get proof "canonical" box,move,paid⟩
  let strips ← get j "strips" (fun a => do (← a.getArr?).toList.mapM box)
  let remainder := strips.zipIdx.map fun (cell,i) => (⟨nextKey i,cell⟩ : AddressedCell)
  pure (← get j "at" Json.getNat?,⟨input,certificate,← get proof "window" box,paidKey,remainder⟩)

def decodeRosterOwner (j : Json) : Parse RosterOwner := do
  let owner ← get j "owner" Json.getNat?
  let hull ← get j "owner_hull" box
  let seeds ← get j "seeds" (fun a => do (← a.getArr?).toList.mapM Json.getStr?)
  let keyed ← j.getObjVal? "replacements"
  let slots ← seeds.mapM fun seed => do
    let _ ← (LatePackets.decodeSeed seed).getDM (throw "invalid Stage5b seed")
    let strips ← match keyed.getObjVal? seed with
      | .ok a => some <$> ((← a.getArr?).toList.mapM box)
      | .error _ => pure none
    pure (⟨seed,strips⟩ : SeedSlot)
  pure ⟨owner,hull,slots⟩

end BccSharp.Coulomb.CompactCover.EarlyReplay
