import BccSharp.Cover.OverlayCorpusGlue
import BccSharp.TwoSite.GlobalInputs

set_option autoImplicit false

/-! The Overlay planar banks in the corpus prefix.

* **Prefix check (glue item 2).** `corpusCheck` composes the Direct root, overlay and
  sidecar checks (`checkWithDirectSidecar`), the Stage2 bulk bank (`checkWithStage2`), a slot
  `later` for the checks of Adaptive and the later stages, and the fixed-point Overlay check on
  top (`checkWithOverlay`). `corpusCheck_sound` gives `SoundCheck` from `SoundCheck later`,
  and `assemble_from_overlay_corpus` is `GlobalInputs.assemble_from_cover_corpus_cover` (the
  version with `GlobalAnalyticInputs` proved) with this check. An Overlay bank witness that
  `overlayFixCheck` accepts is accepted (`corpusCheck_of_overlay`). Since `corpusCheck` is
  `checkWithOverlay` of `orCheck (earlyCheck …) later`, a plan proved to run under
  `checkWithOverlay prior` for every `prior` (`rowPlan_run`) runs
  under `corpusCheck` (`corpusCheck_rowPlan_run`). Off the two banks the check is
  `earlyCheck || later` (`corpusCheck_of_not_overlay`).
* **Planar leaves (glue item 1).** `readPrefixPayload` has no case for the route
  `planar`: it rejects planar leaves.
  `readOverlayWitness` adds the case: a planar leaf that names one of the two banks
  decodes to `⟨.strictFCC, bank, owner⟩` (`readOverlayWitness_planar`), and every other
  leaf goes to `readPrefixPayload` (`readOverlayWitness_other`). `decodeOverlayStageRow` is
  `decodeStageRow` with this decoder.
* **Stage rows (glue items 4 and 5).** `passRow a` passes a held atom on unchanged.
  `stageRows pick held` puts the row `pick a` at every held atom that has one and a
  pass-through row at every other. `splitPass_stageRows`: if every chosen row has its
  atom's key and cell and its plan runs there, the `splitPass` edit runs and the held
  list that enters the next stage is `stageHeld` (each chosen atom replaced in place by
  its row's held cells, every other atom unchanged and in place). `Plan.holds` is the
  held list of a plan, equal to the held list of every successful run
  (`Plan.run_held`), and `Plan.reach_hold_mem` puts a hold reached along a digit word at
  `descend b word`. -/

namespace BccSharp.Coulomb.CompactCover
open Lean BccSharp BccSharp.Coverage EarlyReplay PacketDecode OverlayPlanar OverlayPlanar.Fix

/-! ### Plans: held cells and paths -/

namespace EarlyReplay

/-- The held cells of a plan on the cell `b`, in the order `Plan.run` lists them. -/
def Plan.holds (b : Cell) : Plan → List AddressedCell
  | .hold k => [⟨k, b⟩]
  | .pay _ _ => []
  | .split cut l r => l.holds (cut.child b false) ++ r.holds (cut.child b true)

/-- A successful run holds exactly the plan's held cells. -/
theorem Plan.run_held {check : WitnessRef → Cell → Bool} :
    ∀ (P : Plan) (b : Cell) (s : Snapshot), P.run check b = some s → s.held = P.holds b
  | .hold k, b, s, h => by
    have e : (⟨[], [⟨k, b⟩]⟩ : Snapshot) = s := Option.some.inj h
    subst e
    rfl
  | .pay k proof, b, s, h => by
    by_cases accepted : (sameCell b proof.clip && proof.check check) = true
    · have e : (⟨[⟨k, b⟩], []⟩ : Snapshot) = s := by simpa [Plan.run, accepted] using h
      subst e
      rfl
    · simp [Plan.run, accepted] at h
  | .split cut l r, b, s, h => by
    by_cases fits : cut.fits b = true
    · cases left : l.run check (cut.child b false) with
      | none => simp [Plan.run, fits, left] at h
      | some x =>
        cases right : r.run check (cut.child b true) with
        | none => simp [Plan.run, fits, left, right] at h
        | some y =>
          have e : x.join y = s := by simpa [Plan.run, fits, left, right] using h
          subst e
          show x.held ++ y.held = l.holds (cut.child b false) ++ r.holds (cut.child b true)
          rw [Plan.run_held l _ x left, Plan.run_held r _ y right]
    · simp [Plan.run, fits] at h

/-- The subplan reached along a word of split digits: digit `2*a` enters the lower and
`2*a+1` the upper child of a dyadic split on axis `a`. -/
def Plan.reach : Plan → List ℕ → Option Plan
  | P, [] => some P
  | .split (.dyadic a) l r, d :: ds =>
      if d = 2 * a.val then l.reach ds else if d = 2 * a.val + 1 then r.reach ds else none
  | _, _ :: _ => none

end EarlyReplay

namespace OverlayCorpus

theorem digitChild_low (b : Cell) (a : Axis) : digitChild b (2 * a.val) = (Cut.dyadic a).child b false := by
  have ha : (⟨2 * a.val / 2 % 8, Nat.mod_lt _ (by decide)⟩ : Axis) = a :=
    Fin.ext (show 2 * a.val / 2 % 8 = a.val by have := a.isLt; omega)
  have hs : decide (2 * a.val % 2 = 1) = false := by simp
  simp only [digitChild, ha, hs]

theorem digitChild_high (b : Cell) (a : Axis) :
    digitChild b (2 * a.val + 1) = (Cut.dyadic a).child b true := by
  have ha : (⟨(2 * a.val + 1) / 2 % 8, Nat.mod_lt _ (by decide)⟩ : Axis) = a :=
    Fin.ext (show (2 * a.val + 1) / 2 % 8 = a.val by have := a.isLt; omega)
  have hs : decide ((2 * a.val + 1) % 2 = 1) = true := by simp
  simp only [digitChild, ha, hs]

theorem descend_cons (b : Cell) (d : ℕ) (ds : List ℕ) : descend b (d :: ds) = descend (digitChild b d) ds := rfl

theorem descend_append (b : Cell) (p q : List ℕ) : descend b (p ++ q) = descend (descend b p) q := by
  induction p generalizing b with
  | nil => rfl
  | cons d ds ih => exact ih (digitChild b d)

end OverlayCorpus

open OverlayCorpus in
/-- A hold reached along `word` is held at `descend b word`. -/
theorem EarlyReplay.Plan.reach_hold_mem :
    ∀ (P : Plan) (word : List ℕ) (b : Cell) (k : Key), P.reach word = some (.hold k) →
      (⟨k, descend b word⟩ : AddressedCell) ∈ P.holds b
  | P, [], b, k, h => by
    have e : P = .hold k := by simpa [Plan.reach] using h
    subst e
    simp [Plan.holds, descend]
  | .split (.dyadic a) l r, d :: ds, b, k, h => by
    by_cases h0 : d = 2 * a.val
    · subst h0
      have hl : l.reach ds = some (.hold k) := by simpa [Plan.reach] using h
      have m := Plan.reach_hold_mem l ds ((Cut.dyadic a).child b false) k hl
      rw [descend_cons, digitChild_low]
      exact List.mem_append_left _ m
    · by_cases h1 : d = 2 * a.val + 1
      · subst h1
        have hr : r.reach ds = some (.hold k) := by simpa [Plan.reach] using h
        have m := Plan.reach_hold_mem r ds ((Cut.dyadic a).child b true) k hr
        rw [descend_cons, digitChild_high]
        exact List.mem_append_right _ m
      · simp [Plan.reach, h0, h1] at h
  | .split (.rational _ _) _ _, _ :: _, _, _, h => by simp [Plan.reach] at h
  | .hold _, _ :: _, _, _, h => by simp [Plan.reach] at h
  | .pay _ _, _ :: _, _, _, h => by simp [Plan.reach] at h

/-- A plan made from a replacement tree holds exactly the tree's held cells. -/
theorem Tree.toPlan_holds : ∀ (t : Tree) (b : Cell) (k : Key), (t.toPlan b k).holds b = t.holds b
  | .close _, _, _ => rfl
  | .hold _, _, _ => rfl
  | .split (.dyadic a) l r, b, k => by
    simp only [Tree.toPlan, Plan.holds, Tree.holds, Tree.toPlan_holds l, Tree.toPlan_holds r]
  | .split (.rational a v) l r, b, k => by
    simp only [Tree.toPlan, Plan.holds, Tree.holds, Tree.toPlan_holds l, Tree.toPlan_holds r]

namespace OverlayCorpus
open LatePackets

/-! ### The corpus prefix check (glue item 2) -/

/-- A witness is paid when either check pays it. -/
def orCheck (a b : WitnessRef → Cell → Bool) (w : WitnessRef) (c : Cell) : Bool := a w c || b w c

theorem orCheck_sound {a b : WitnessRef → Cell → Bool} (ha : SoundCheck a) (hb : SoundCheck b) :
    SoundCheck (orCheck a b) := by
  intro w c ok p hp gp
  rcases Bool.or_eq_true_iff.mp ok with h | h
  · exact ha w c h p hp gp
  · exact hb w c h p hp gp

/-- The checks of the prefix stages before Overlay: the Direct root and overlay records
(`initialWitnessCheck`), the direct-moment sidecar and the Stage2 bulk bank. -/
def earlyCheck (geometric : WitnessRef → Option NormalizedProposal) (direct : WitnessRef → Option Cell)
    (sidecar : WitnessRef → Option DirectSidecarProposal) (bulk : WitnessRef → Option Stage2Payload) :
    WitnessRef → Cell → Bool :=
  checkWithStage2 (checkWithDirectSidecar geometric direct sidecar) bulk

theorem earlyCheck_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) : SoundCheck (earlyCheck geometric direct sidecar bulk) :=
  checkWithStage2_sound (checkWithDirectSidecar_sound geometric direct sidecar) bulk

/-- The prefix check of the corpus: the fixed-point Overlay check for the two
planar banks, on top of the early checks and `later`, the checks of Adaptive and the later
stages. -/
def corpusCheck (geometric : WitnessRef → Option NormalizedProposal) (direct : WitnessRef → Option Cell)
    (sidecar : WitnessRef → Option DirectSidecarProposal) (bulk : WitnessRef → Option Stage2Payload)
    (later : WitnessRef → Cell → Bool) : WitnessRef → Cell → Bool :=
  checkWithOverlay (orCheck (earlyCheck geometric direct sidecar bulk) later)

theorem corpusCheck_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later : WitnessRef → Cell → Bool} (laterSound : SoundCheck later) :
    SoundCheck (corpusCheck geometric direct sidecar bulk later) :=
  checkWithOverlay_sound (orCheck_sound (earlyCheck_sound geometric direct sidecar bulk) laterSound)

/-- An Overlay bank witness accepted by `overlayFixCheck` is accepted by the prefix check. -/
theorem corpusCheck_of_overlay (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) (later : WitnessRef → Cell → Bool) {w : WitnessRef} {b : Cell}
    (bank : isOverlayBank w.source = true) (h : overlayFixCheck w b = true) :
    corpusCheck geometric direct sidecar bulk later w b = true :=
  checkWithOverlay_of_overlay _ bank h

/-- Off the two Overlay banks, the prefix check is the early check or `later`. -/
theorem corpusCheck_of_not_overlay (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) (later : WitnessRef → Cell → Bool) {w : WitnessRef} {b : Cell}
    (other : isOverlayBank w.source = false) :
    corpusCheck geometric direct sidecar bulk later w b =
      (earlyCheck geometric direct sidecar bulk w b || later w b) := by
  have off : ¬(w.route = .strictFCC ∧ isOverlayBank w.source = true) := by simp [other]
  unfold corpusCheck checkWithOverlay
  rw [ite_eq_right off]
  rfl

/-- The Overlay stage rows run under the prefix check: it is `checkWithOverlay` of a prior check. -/
theorem corpusCheck_rowPlan_run (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) (later : WitnessRef → Cell → Bool) {t : Tree} {root : Cell}
    (h : t.check overlayFixCheck root = true)
    (bank : t.witnessesAll (fun w => isOverlayBank w.source) = true) (k : Key) :
    ∃ paid, (t.toPlan root k).run (corpusCheck geometric direct sidecar bulk later) root =
      some ⟨paid, t.holds root⟩ :=
  rowPlan_run _ h bank k

end OverlayCorpus

end BccSharp.Coulomb.CompactCover

namespace BccSharp.Coulomb
open CompactCover CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus

/-- the two-site theorem from the corpus whose prefix runs under the Overlay prefix check: the early
checks, the Overlay planar banks and any sound check `later` for Adaptive and the later stages. -/
theorem assemble_from_overlay_corpus (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later : WitnessRef → Cell → Bool} (laterSound : SoundCheck later)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early) (sLate : CheckerSound late)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom)
    (rStage5b : pre.run (corpusCheck geometric direct sidecar bulk later) = some stage5b)
    (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage6 : runRows (runStage6 early) stage5b rows = some stage6) (closed : corp.run late stage6 = some []) :
    Statement :=
  GlobalInputs.assemble_from_cover_corpus_cover (corpusCheck_sound geometric direct sidecar bulk laterSound)
    sEarly sLate pre stage5b stage6 rStage5b rows corp rStage6 closed

end BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.OverlayCorpus
open Lean BccSharp BccSharp.Coverage EarlyReplay PacketDecode OverlayPlanar OverlayPlanar.Fix

/-! ### Planar leaves (glue item 1) -/

/-- A planar leaf `leaf_ref(bank, "planar", owner, seed, path,
raw)` names an Overlay bank and its original owner and is paid on route `.strictFCC`. -/
def decodePlanarLeaf (j : Json) : Parse WitnessRef := do
  let source ← get j "bank" Json.getStr?
  if isOverlayBank source then pure ⟨.strictFCC, source, ← get j "owner" Json.getNat?⟩
  else throw "planar leaf names an unpinned bank"

/-- The prefix witness reader with the planar route of the two Overlay banks. -/
def readOverlayWitness : WitnessDecoder := fun j => do
  match ← get j "route" Json.getStr? with
  | "planar" => decodePlanarLeaf j
  | _ => PrefixPayload.ref <$> readPrefixPayload j

/-- A stage row whose leaves may be Overlay planar leaves. -/
def decodeOverlayStageRow (depth : Nat) (j : Json) : Parse StageRow :=
  decodeStageRow readOverlayWitness depth j

theorem readOverlayWitness_planar {j : Json} {source : String} {owner : Nat}
    (route : get j "route" Json.getStr? = .ok "planar") (bank : get j "bank" Json.getStr? = .ok source)
    (pinned : isOverlayBank source = true) (record : get j "owner" Json.getNat? = .ok owner) :
    readOverlayWitness j = .ok ⟨.strictFCC, source, owner⟩ := by
  have planar : readOverlayWitness j = decodePlanarLeaf j := by
    simp only [readOverlayWitness, route]
    rfl
  rw [planar]
  simp [decodePlanarLeaf, bank, record, pinned, bind, Except.bind, pure, Except.pure]

theorem readOverlayWitness_other {j : Json} {r : String} (route : get j "route" Json.getStr? = .ok r)
    (other : r ≠ "planar") : readOverlayWitness j = PrefixPayload.ref <$> readPrefixPayload j := by
  simp only [readOverlayWitness, route, bind, Except.bind]

/-! ### Stage rows (glue items 4 and 5) -/

theorem sameAddressedCell_self (a : AddressedCell) : sameAddressedCell a a = true := by
  simp [sameAddressedCell, sameCell_self]

/-- The pass-through row of a held atom: its plan holds the atom unchanged. -/
def passRow (a : AddressedCell) : StageRow := ⟨a, .hold a.key⟩

theorem passRow_run (check : WitnessRef → Cell → Bool) (a : AddressedCell) :
    (passRow a).plan.run check a.cell = some ⟨[], [a]⟩ := rfl

/-- The rows of one `splitPass` edit on the held list `held`: the row `pick a` at every
atom that has one, a pass-through row at every other. -/
def stageRows (pick : AddressedCell → Option StageRow) (held : List AddressedCell) : List StageRow :=
  held.map fun a => (pick a).getD (passRow a)

/-- The held list after that edit, when the row chosen at `a` holds `out a`. -/
def stageHeld (pick : AddressedCell → Option StageRow) (out : AddressedCell → List AddressedCell)
    (held : List AddressedCell) : List AddressedCell :=
  held.flatMap fun a => if (pick a).isSome then out a else [a]

/-- The row chosen at `a`, if any, has `a`'s key and cell and its plan runs on `a`'s
cell, holding `out a`. -/
def RowFits (check : WitnessRef → Cell → Bool) (pick : AddressedCell → Option StageRow)
    (out : AddressedCell → List AddressedCell) (a : AddressedCell) : Prop :=
  ∀ row, pick a = some row →
    sameAddressedCell a row.input = true ∧ ∃ paid, row.plan.run check a.cell = some ⟨paid, out a⟩

theorem replayStage_stageRows {check : WitnessRef → Cell → Bool} {pick : AddressedCell → Option StageRow}
    {out : AddressedCell → List AddressedCell} :
    ∀ held : List AddressedCell, (∀ a ∈ held, RowFits check pick out a) →
      ∃ paid, replayStage check held (stageRows pick held) = some ⟨paid, stageHeld pick out held⟩
  | [], _ => ⟨[], rfl⟩
  | a :: rest, fits => by
    obtain ⟨paidRest, hrest⟩ :=
      replayStage_stageRows rest (fun x hx => fits x (List.mem_cons_of_mem a hx))
    have hrows : stageRows pick (a :: rest) = (pick a).getD (passRow a) :: stageRows pick rest := rfl
    have hheld : stageHeld pick out (a :: rest) =
        (if (pick a).isSome then out a else [a]) ++ stageHeld pick out rest := List.flatMap_cons
    rw [hrows, hheld]
    cases hp : pick a with
    | none =>
      have same : sameAddressedCell a (passRow a).input = true := sameAddressedCell_self a
      refine ⟨[] ++ paidRest, ?_⟩
      simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [replayStage, ite_eq_left same, passRow_run, hrest]
      rfl
    | some row =>
      obtain ⟨same, paid, run⟩ := fits a List.mem_cons_self row hp
      refine ⟨paid ++ paidRest, ?_⟩
      simp only [Option.getD_some, Option.isSome_some, ite_true]
      rw [replayStage, ite_eq_left same, run, hrest]
      rfl

/-- A `splitPass` edit with the chosen rows and pass-through rows elsewhere runs, and
passes on `stageHeld`. -/
theorem splitPass_stageRows {check : WitnessRef → Cell → Bool} {pick : AddressedCell → Option StageRow}
    {out : AddressedCell → List AddressedCell} (s : Snapshot) (fits : ∀ a ∈ s.held, RowFits check pick out a) :
    ∃ paid, (Edit.splitPass (stageRows pick s.held)).run check s = some ⟨s.paid ++ paid, stageHeld pick out s.held⟩ := by
  obtain ⟨paid, h⟩ := replayStage_stageRows s.held fits
  exact ⟨paid, by simp [Edit.run, Snapshot.advance, h]⟩

/-- An atom without a chosen row passes the edit unchanged. -/
theorem mem_stageHeld_of_none {pick : AddressedCell → Option StageRow} {out : AddressedCell → List AddressedCell}
    {held : List AddressedCell} {a : AddressedCell} (ha : a ∈ held) (none : pick a = none) :
    a ∈ stageHeld pick out held :=
  List.mem_flatMap.mpr ⟨a, ha, by simp [none]⟩

/-- In a held list with distinct keys, an atom pins the cell of every atom with its key. -/
theorem cell_of_key_nodup {held : List AddressedCell} (nodup : (held.map AddressedCell.key).Nodup)
    {a b : AddressedCell} (ha : a ∈ held) (hb : b ∈ held) (key : b.key = a.key) : b = a := by
  induction held with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at nodup
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (key ▸ List.mem_map_of_mem hb') nodup.1
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (key.symm ▸ List.mem_map_of_mem ha') nodup.1
      · exact ih nodup.2 ha' hb'

/-- A hold of a plan, reached along `word`, is held after any successful run. -/
theorem held_of_reach {check : WitnessRef → Cell → Bool} {P : Plan} {b : Cell} {s : Snapshot} {word : List ℕ}
    {k : Key} (run : P.run check b = some s) (reach : P.reach word = some (.hold k)) :
    (⟨k, descend b word⟩ : AddressedCell) ∈ s.held := by
  rw [Plan.run_held P b s run]
  exact Plan.reach_hold_mem P word b k reach

end BccSharp.Coulomb.CompactCover.OverlayCorpus
