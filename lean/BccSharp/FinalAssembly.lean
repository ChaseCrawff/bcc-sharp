import BccSharp.Lattice.Atlas.LatticeCase
import BccSharp.Cover.ReplayCompose
import BccSharp.Cover.PrefixFixGlue
import BccSharp.Cover.AdaptiveCheck
import BccSharp.Cover.Stage3Stage6Hybrid
import BccSharp.Cover.LateChecker
import BccSharp.TwoSite.StatementFull
import BccSharp.Cover.Stage6Deficit
import BccSharp.Cover.Stage3
import BccSharp.Cover.Stage5bOptical
import BccSharp.Cover.Stage4Stage5a
import BccSharp.Cover.Stage5aAnchored

set_option autoImplicit false

/-! # Final assembly of the two-site theorem: `StatementFull` from the premises of the replay

`FinalAssembly.statementFull_of_replay` joins the merged sound checkers of the cover,
with the fixed-point Direct and Stage2 checks in place of the exact ones, and proves
`StatementFull` (every clause of the two-site theorem, `BccSharp.TwoSite.StatementFull`) from exactly
the remaining premises: the soundness of the checks whose evaluators are not merged into it, and the three run equalities of the replay.
`FinalAssembly.statementFull_of_replay_merged` is the instance of its `latePending` form
(`statementFull_of_replay_latePending`) with the further merged checks in the slots
(section "The merged form"); the merged late checks run inside `lateChecker`. The module
imports `BccSharp.Lattice.Atlas.LatticeCase`.

## The checks

* **Prefix** (`CorpusPrefix.run`, through Stage5b): `corpusCheckFix geometric direct sidecar
  bulkT later`, which is `checkWithOverlay (orCheck (earlyCheckFix geometric direct sidecar
  bulkT) later)` (`corpusCheckFix_eq`). It is `corpusCheck` of `BccSharp.Cover.OverlayCorpusPrefix`
  with the fixed-point Direct and Stage2 checks of `BccSharp.Cover.PrefixFixGlue` in place of the
  exact rational ones: `earlyCheckFix geometric direct sidecar bulkT` is
  `checkWithStage2FixT (checkWithDirectSidecarFix geometric direct sidecar) bulkT`. The fixed-point
  Overlay check sits on top. The `later` slot is
  `orCheck (adaptiveFull adaptiveHint) (laterHybrid stage5bHint pending)`: every Adaptive letter (source
  `"adaptiveRoute"`); the Stage5b phase and `whole_above` leaves (the four exact Stage5b sources), by a
  proposed support first and the box-built support second; and `pending`.
* **Stage6 binding** (`runRows (runStage6 early)`): `early = stage6HybridCheck stage6Hint dEval`;
  `F` entries by the hybrid Jensen check, `D` entries by `dEval`.
* **Late corpus** (`Corpus.run`): `lateChecker t` (`BccSharp.Cover.LateChecker`), which runs, by
  family, the far J/F/D leaf check; for HalfShift `halfShiftCheck`, `halfShiftCheckFar` and `halfShiftCheckCat`
  (`transportCheck`); for the layered family `planarAnchorCheck`, `planarAnchorCheckFar` and `planarFibreCheckFar`
  (`layeredCheck`); `planarFibreTriCheck` for the PlanarFibre triangular requests; and `centeredCheck` for
  the PlanarAnchor centered requests, whose atlas is valid by the field `atlasValid` of the tables.

The checks are sound for all of their tables and hints, the prefix check once `pending` is
and the Stage6 checker once `dEval` is (`prefix_sound`, `stage6HybridCheck_sound`,
`late_sound`), so tables and hints are proposal data, never trusted. `LatticeCase` is
discharged by `StrainAtlas.latticeCase_proved` in
`adaptiveFull_sound` (`later_sound`) and in `lateChecker_sound` (`late_sound`).
`GlobalInputs.assemble_from_cover_corpus_cover`, the generic path behind
`assemble_from_overlay_corpus`, supplies `GlobalAnalyticInputs`, and
`statementFull_of_statement` gives `StatementFull`.

## The premises of `statementFull_of_replay`

1. `pendingSound : SoundCheck pending`, for the prefix checks that `later` does not run
   itself, joined with `orCheck`: those of Stage3, the Stage4 and Stage5a sources and
   the Stage5b optical tiles other than `whole_above`
   (`statementFull_of_replay_merged` puts their merged checks here).
2. `dSound : Stage6DSound dEval`, for the evaluator of the Stage6 `D` entries (`stage6DEval dhint`
   in the merged form).
3. `rStage5b: pre.run (corpusCheckFix geometric direct sidecar bulkT (orCheck (adaptiveFull
   adaptiveHint) (laterHybrid stage5bHint pending))) = some stage5b`: the prefix through Stage5b.
4. `rStage6: runRows (runStage6 (stage6HybridCheck stage6Hint dEval)) stage5b rows = some stage6`: the
   Stage6 binding.
5. `closed : corp.run (lateChecker t) stage6 = some []`: the late corpus. `lateChecker` runs
   every merged late check, but no merged check accepts the HalfShift and PlanarFibre directional and
   above_fcc requests; the HalfShift bits-011 relative requests, the PlanarFibre saturated layered
   requests with a basin result and the six centered PlanarAnchor requests over the cost budget
   fit a check's form but have no known certificate; no certificate is known to pass for the PlanarFibre layered requests; and some
   HalfShift, PlanarFibre and PlanarAnchor requests are known failures of the checks tried.
   This equality needs those evaluators and certificates first; the form
   `statementFull_of_replay_latePending` takes further evaluators as one more sound checker
   instead.

The tables (`geometric`, `direct`, `sidecar`, `bulkT`), the hints (`adaptiveHint`, `stage5bHint`,
`stage6Hint`), `pending`, `dEval`, the late tables `t`, the prefix `pre`, the Stage6 rows and
the late corpus are free parameters. A new prefix check slots in through `pending`, a `D`
evaluator through `dEval`, and the literal data through `pre`, the rows and the corpus,
without changing the theorem. A new kind of Stage6 `F` certificate would change
`stage6HybridCheck`, and a new late evaluator `lateChecker`, unless it enters through
`statementFull_of_replay_latePending`.

## Other forms

* `statementFull_of_runs`: `pending` and `dEval` the empty checks, which are sound, so the
  two soundness premises are slots, not assumptions: with the slots empty,
  `StatementFull` follows from the three run equalities. On the data these cannot
  hold: with `pending` and `dEval` empty, nothing in this form pays the Stage3, Stage4 and Stage5a
  witnesses or the Stage5b optical tiles other than `whole_above`, whose checks enter through
  `pending`, and no Stage6 `D` entry closes (the Stage6 checker is then `stage6HybridNow`, which
  rejects them all). The evaluators of premises 1 and 2 enter through
  `statementFull_of_replay` (`statementFull_of_replay_merged` with the merged ones); this
  form fits only data that its checks close with nothing in `pending` and `dEval`.
* `statementFull_of_replay_chunks`: the Stage6 binding and the late corpus chunk by chunk
  (`LateChunk`, `late_chunks`), as in `assemble_from_late_chunks`. The prefix must end in
  the chunks' Stage5b slices, in order.
* `statementFull_of_replay_steps`: the same, with the prefix from its seven steps
  (`CorpusPrefix.run_of`).
* `statementFull_of_replay_latePending`: the late checker `eitherCheck (lateChecker t)
  latePending` for any `latePending` with `CheckerSound latePending`, so a late evaluator
  can be added without changing `lateChecker`. It is `statementFull_of_replay_lateSound`,
  which takes the soundness of `lateChecker t` as a premise `lateSound`, with `lateSound:=
  late_sound t`.

## The merged form

`statementFull_of_replay_merged` is `statementFull_of_replay_latePending` with the
merged checks in its slots, so their soundness premises are discharged. It is
`statementFull_of_replay_merged_lateSound`, which takes `lateSound: CheckerSound
(lateChecker t)` as a premise, with `lateSound:= late_sound t`. So if `lateChecker_sound`
gains premises, only `late_sound` and the theorems that use it, directly or through another
form, change; the forms that take `lateSound` do not. The slots are filled as follows:

* `pending := orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'`, where
  `mergedPending` is `orCheck (stage3Check stage3Hint) (orCheck (stage5bOpticalCheck stage5bOptHint)
  (stage4stage5aCheck kHint))`: the Stage3 leaves `Z` and `correlated_phase` (`BccSharp.Cover.Stage3`), the
  Stage5b optical tiles of the four sources `whole_defect`, `screened_anchor`, `taylor_anchor`
  and `optical_lattice` (`BccSharp.Cover.Stage5bOptical`) and the Stage4 and Stage5a sources
  (`BccSharp.Cover.Stage4Stage5a`). `mergedPending_sound` holds for all hints, with `LatticeCase`
  discharged for the last two checks.
* `dEval := stage6DEval dhint` (`BccSharp.Cover.Stage6Deficit`), sound for all `dhint`
  (`stage6DEval_sound`); the Stage6 checker is then `stage6FullCheck stage6Hint dhint` by
  definition.
* `latePending := latePending'`: the merged late checks (the far-annulus checks
  `halfShiftCheckFar`, `planarAnchorCheckFar` and `planarFibreCheckFar`, the catalogue check `halfShiftCheckCat`, the
  triangular check `planarFibreTriCheck` and the centered check `centeredCheck`) run inside
  `lateChecker`, with their tables in `LateTables`, and
  `late_sound` covers them.

The premises left are `SoundCheck pending'`, `CheckerSound latePending'` and the three run
equalities. `pending'` is the slot for prefix witnesses that no merged check pays (such as
the Stage4 and Stage5a sources that no merged payment covers; `stage5aCheck ev hint` of
`BccSharp.Cover.Stage5aAnchored`, sound once `AnchorSound ev` and on route `strictDeficit` only, is
meant for some of them, and `isOverlayBank_of_stage5a` gives `prefix_of_pending'` its source
premise), and `latePending'` the slot for late requests that `lateChecker` does not accept
(such as the directional and above_fcc requests, the HalfShift bits-011 relative requests, the
PlanarFibre saturated layered requests with a basin result and the centered PlanarAnchor requests over the
cost budget). No Adaptive `Q` needs `pending'`: all 471 pass
`adaptiveFull` in the kernel. Each merged prefix check reads exact source strings and routes;
the literal data must use them.

`statementFull_of_replay_merged_chunks` and `statementFull_of_replay_merged_steps` are the
merged form with the Stage6 binding and the late corpus chunk by chunk (`late_chunks`), and
with the prefix from its seven steps as well (`CorpusPrefix.run_of`); like
`statementFull_of_replay_merged_lateSound` they take `lateSound`, which `late_sound t`
supplies. `statementFull_of_runs_merged` is `statementFull_of_replay` with the merged
checks and nothing pending (`pending'` empty, the late corpus under `lateChecker t`
alone), so `StatementFull` follows from the three run equalities alone; on the data
that needs a merged check for every witness and request the two slots would hold.

## How the prefix equality decomposes

`CorpusPrefix.run_of` (`BccSharp.Cover.ReplayCompose`) splits `pre.run check = some atoms` into
seven steps. Each step decomposes by lemmas that are generic in the data, of
`BccSharp.Cover.ReplayCompose` unless another module is named. Theorems that are specific to the literal data, and are not part of this
package, cover the root plan, the stage edits through Overlay and the order into Adaptive.

* the root plan: `Tree.toPlan_run_of_closes` (`BccSharp.Cover.DataPath`); for the Direct root data,
  shard by shard (data-specific);
* the stage edits (`splitPass`) before the mirror, on the positive side and after it:
  `runEdits_cons_of` and `runEdits_append_of`; per stage `splitPass_chunks` or
  `splitPass_chunks_exists`; per row the row's plan (`Tree.toPlan_run_of_closes`, or
  `replayStage_maskRows` and `replayStage_streamRows` of `BccSharp.Cover.DataPathPacker`); for
  the three early stages and Overlay, data-specific theorems;
* merges and clips: `runEdits_framed` (each chunk's edits, built by `mergeAt` and `clipAt`
  of `BccSharp.Cover.DataPathPacker`, run on that chunk's own list), and `ClipRow.check_of` for
  one clip row;
* rotations: `rotation_run` (`BccSharp.Cover.DataPathPacker`) and `rotate_chunks`; for the order
  into Adaptive, a data-specific theorem;
* the positive selection: `selectPositive_chunks`, `filter_positive_self`,
  `filter_positive_nil`; the `insideCheck` test: `all_chunks`;
* the mirror: `mirror_chunks` with `filterMap_clip_far` and `flatten_map_filter`;
* the Stage5b binding: `bindStage5b_chunks` and `eq_some_getD_of_isSome`, then `bind_late_glue`
  for its output as the late chunks' input.

## Per-item results

An evaluator states that its check is `true` on an item's own cell. Lifts to the checks
above:

* prefix, Adaptive: `prefix_of_adaptive` from `adaptiveFull adaptiveHint w b = true`;
* prefix, Stage5b phase and `whole_above`: `prefix_of_stage5b` from
  `stage5bHybridCheck stage5bHint w b = true`. Neither needs a source premise: the sources
  these checks accept are not Overlay banks (`isOverlayBank_of_adaptiveFull`,
  `isOverlayBank_of_stage5bHybrid`);
* prefix, `pending`: `prefix_of_pending`, given `isOverlayBank w.source = false`;
* prefix, Direct root and overlay, Direct sidecar and Stage2: `corpusCheckFix_of_early`, given
  `isOverlayBank w.source = false`;
* prefix, Overlay rows: `corpusCheckFix_rowPlan_run` and `corpusCheckFix_of_overlay`; the data
  path's theorems for `checkWithOverlay prior` apply after rewriting with `corpusCheckFix_eq`;
* Stage6: `stage6_of_fcc` and `stage6_of_deficit`, then `runStage6_close`;
* late, from the check of the request's family: `late_of_leaf`; `late_of_transport`,
  `late_of_transportFar`, `late_of_transportCat` (HalfShift); `late_of_layered`,
  `late_of_layeredFar`, `late_of_layeredPlanarFibreFar` (layered); `late_of_triangular`;
  `late_of_centered` (or the request-level `lateChecker_halfShift`, `lateChecker_halfShiftFar`,
  `lateChecker_halfShiftCat`, `lateChecker_planarAnchor`, `lateChecker_planarAnchorFar`, `lateChecker_planarFibreFar`,
  `lateChecker_planarFibre` and `lateChecker_centered` of `BccSharp.Cover.LateChecker`), then
  `closeCheck_of`; in the `latePending` form and the merged form, `eitherCheck_of_left`
  and `eitherCheck_of_right`;
* merged form, prefix: `prefix_of_stage3`, `prefix_of_stage5bOptical` and `prefix_of_stage4stage5a`
  with no source premise (`isOverlayBank_of_stage3`, `isOverlayBank_of_stage5bOptical`,
  `isOverlayBank_of_stage4stage5a`), and `prefix_of_pending'` given `isOverlayBank w.source = false`
  (from `isOverlayBank_of_stage5a` when the item is paid by `stage5aCheck`);
  `prefix_of_adaptive`, `prefix_of_stage5b` and the `corpusCheckFix_*` lifts apply with `pending:=
  orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'`;
* merged form, Stage6: `stage6_of_fcc`, and `stage6_of_deficit` with `dEval := stage6DEval dhint`.

For a tree `t` on its cell `b`, the per-leaf facts `∀ x ∈ t.closes b, check x.1 x.2 = true`
lift pointwise and feed `Tree.toPlan_run_of_closes`.

The prefix-check part (namespace `OverlayCorpus`) needs no `LatticeCase`. A module of
`s` or `DataPath` that must not import this library can state its facts for a
generic check or for `checkWithOverlay prior`, as the data path does; or the part can move next
to `corpusCheck`. The same holds for the late lifts (`late_of_*`, `eitherCheck_of_left` and
`eitherCheck_of_right`), which could move next to `lateChecker` and `eitherCheck`. -/

namespace BccSharp.Coulomb.CompactCover.OverlayCorpus
open Lean BccSharp BccSharp.Coverage EarlyReplay PacketDecode OverlayPlanar OverlayPlanar.Fix

/-! ### The prefix check with the fixed-point Direct and Stage2 checks -/

/-- The checks of the prefix stages before Overlay, with fixed-point arithmetic: the Direct root
and overlay records (`initialWitnessCheckFix`), the direct-moment sidecar
(`checkWithDirectSidecarFix`) and the Stage2 bulk bank with shared tangents
(`checkWithStage2FixT`). This is `earlyCheck` with the fixed-point checks. -/
def earlyCheckFix (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) : WitnessRef → Cell → Bool :=
  checkWithStage2FixT (checkWithDirectSidecarFix geometric direct sidecar) bulkT

theorem earlyCheckFix_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) :
    SoundCheck (earlyCheckFix geometric direct sidecar bulkT) :=
  checkWithStage2FixT_sound (checkWithDirectSidecarFix_sound geometric direct sidecar) bulkT

/-- The prefix check of the corpus with the fixed-point early checks: the fixed-point
Overlay check for the two planar banks, on top of `earlyCheckFix` and `later`, the
checks of Adaptive and the later stages. This is `corpusCheck` with `earlyCheckFix` in place of
`earlyCheck`. -/
def corpusCheckFix (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) (later : WitnessRef → Cell → Bool) :
    WitnessRef → Cell → Bool :=
  checkWithOverlay (orCheck (earlyCheckFix geometric direct sidecar bulkT) later)

/-- The prefix check is `checkWithOverlay` of a prior check, so every theorem stated for
`checkWithOverlay prior` applies to it. -/
theorem corpusCheckFix_eq (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) (later : WitnessRef → Cell → Bool) :
    corpusCheckFix geometric direct sidecar bulkT later =
      checkWithOverlay (orCheck (earlyCheckFix geometric direct sidecar bulkT) later) :=
  rfl

theorem corpusCheckFix_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) {later : WitnessRef → Cell → Bool}
    (laterSound : SoundCheck later) :
    SoundCheck (corpusCheckFix geometric direct sidecar bulkT later) :=
  checkWithOverlay_sound (orCheck_sound (earlyCheckFix_sound geometric direct sidecar bulkT) laterSound)

/-- An Overlay bank witness accepted by `overlayFixCheck` is accepted by the prefix check. -/
theorem corpusCheckFix_of_overlay (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) (later : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (bank : isOverlayBank w.source = true) (h : overlayFixCheck w b = true) :
    corpusCheckFix geometric direct sidecar bulkT later w b = true :=
  checkWithOverlay_of_overlay _ bank h

/-- Off the two Overlay banks, the prefix check is the early check or `later`. -/
theorem corpusCheckFix_of_not_overlay (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) (later : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (other : isOverlayBank w.source = false) :
    corpusCheckFix geometric direct sidecar bulkT later w b =
      (earlyCheckFix geometric direct sidecar bulkT w b || later w b) := by
  have off : ¬(w.route = .strictFCC ∧ isOverlayBank w.source = true) := by simp [other]
  unfold corpusCheckFix checkWithOverlay
  rw [ite_eq_right off]
  rfl

/-- The Overlay stage rows run under the prefix check: it is `checkWithOverlay` of a prior check. -/
theorem corpusCheckFix_rowPlan_run (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) (later : WitnessRef → Cell → Bool) {t : Tree}
    {root : Cell} (h : t.check overlayFixCheck root = true)
    (bank : t.witnessesAll (fun w => isOverlayBank w.source) = true) (k : Key) :
    ∃ paid, (t.toPlan root k).run (corpusCheckFix geometric direct sidecar bulkT later) root =
      some ⟨paid, t.holds root⟩ :=
  rowPlan_run _ h bank k

/-- **A `later` result is a prefix-check result** off the two Overlay banks. -/
theorem corpusCheckFix_of_later (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) {later : WitnessRef → Cell → Bool}
    {w : WitnessRef} {b : Cell} (other : isOverlayBank w.source = false) (h : later w b = true) :
    corpusCheckFix geometric direct sidecar bulkT later w b = true := by
  rw [corpusCheckFix_of_not_overlay geometric direct sidecar bulkT later other, h, Bool.or_true]

/-- **An early result is a prefix-check result** off the two Overlay banks: the Direct root and
overlay, the Direct sidecar and the Stage2 leaves. -/
theorem corpusCheckFix_of_early (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload) (later : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (other : isOverlayBank w.source = false)
    (h : earlyCheckFix geometric direct sidecar bulkT w b = true) :
    corpusCheckFix geometric direct sidecar bulkT later w b = true := by
  rw [corpusCheckFix_of_not_overlay geometric direct sidecar bulkT later other, h, Bool.true_or]

end BccSharp.Coulomb.CompactCover.OverlayCorpus

namespace BccSharp.Coulomb.FinalAssembly
open BccSharp BccSharp.Coverage
open CompactCover CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus
open CompactCover.OverlayPlanar.Fix

/-! ### Dispatch: the Adaptive and Stage5b checks accept no Overlay bank witness -/

/-- The Adaptive source tag is not an Overlay bank (kernel evaluation of the exact-string match). -/
theorem adaptiveSource_not_overlay : isOverlayBank AdaptiveSupport.adaptiveSource = false := by
  decide +kernel

/-- The four Stage5b sources are not Overlay banks (kernel evaluation of the exact-string match). -/
theorem stage5bSources_not_overlay :
    isOverlayBank "stage5b/phase/0" = false ∧ isOverlayBank "stage5b/phase/1" = false ∧
      isOverlayBank "stage5b/phase/2" = false ∧ isOverlayBank "stage5b/whole_above" = false := by
  decide +kernel

/-- A witness that the Adaptive check accepts has the source `"adaptiveRoute"`, so it is not an Overlay bank
witness. -/
theorem isOverlayBank_of_adaptiveFull {hint : WitnessRef → Option AdaptiveSupport.AdaptiveHint} {w : WitnessRef}
    {b : Cell} (h : AdaptiveSupport.adaptiveFull hint w b = true) : isOverlayBank w.source = false := by
  by_cases tag : w.source = AdaptiveSupport.adaptiveSource
  · rw [tag]
    exact adaptiveSource_not_overlay
  · rw [AdaptiveSupport.adaptiveFull_off hint b tag] at h
    exact absurd h (by decide)

/-- A witness that the hybrid Stage5b check accepts has one of the four Stage5b sources, so it is
not an Overlay bank witness. -/
theorem isOverlayBank_of_stage5bHybrid {hint : WitnessRef → Option Stage3Stage6.SupportHint}
    {w : WitnessRef} {b : Cell} (h : Stage3Stage6.stage5bHybridCheck hint w b = true) :
    isOverlayBank w.source = false := by
  obtain ⟨s0, s1, s2, s3⟩ := stage5bSources_not_overlay
  by_cases h0 : w.source = "stage5b/phase/0"
  · rw [h0]
    exact s0
  by_cases h1 : w.source = "stage5b/phase/1"
  · rw [h1]
    exact s1
  by_cases h2 : w.source = "stage5b/phase/2"
  · rw [h2]
    exact s2
  by_cases h3 : w.source = "stage5b/whole_above"
  · rw [h3]
    exact s3
  rw [Stage3Stage6.stage5bHybridCheck_other hint w b h0 h1 h2 h3] at h
  exact absurd h (by decide)

/-! ### Soundness of the three checks, with `LatticeCase` discharged -/

/-- **The `later` slot**: every Adaptive letter, the Stage5b phase and `whole_above` leaves (a
proposed support first, the box-built one second), and `pending`. Sound for all hints once
`pending` is; `LatticeCase` (needed by `adaptiveFull_sound` for the letters `Q` and `X`) is
`latticeCase_proved`. -/
theorem later_sound (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) {pending : WitnessRef → Cell → Bool}
    (pendingSound : SoundCheck pending) :
    SoundCheck (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending)) :=
  Stage3Stage6.later_compose_hybrid stage5bHint
    (AdaptiveSupport.adaptiveFull_sound BravaisCover.StrainAtlas.latticeCase_proved adaptiveHint) pendingSound

/-- **The prefix check** of the final assembly is sound for all tables and hints once
`pending` is. -/
theorem prefix_sound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) {pending : WitnessRef → Cell → Bool}
    (pendingSound : SoundCheck pending) :
    SoundCheck (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending))) :=
  corpusCheckFix_sound geometric direct sidecar bulkT (later_sound adaptiveHint stage5bHint pendingSound)

/-- **The late checker** is sound for all tables; `LatticeCase` is `latticeCase_proved`. -/
theorem late_sound (t : LateTables) : CheckerSound (lateChecker t) :=
  lateChecker_sound BravaisCover.StrainAtlas.latticeCase_proved t

/-! ### Per-item results -/

/-- An Adaptive item is a prefix-check result. -/
theorem prefix_of_adaptive (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    {adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint}
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) (pending : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (h : AdaptiveSupport.adaptiveFull adaptiveHint w b = true) :
    corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending)) w b = true :=
  corpusCheckFix_of_later geometric direct sidecar bulkT (isOverlayBank_of_adaptiveFull h) (orCheck_of_left h)

/-- A Stage5b phase or `whole_above` item is a prefix-check result. -/
theorem prefix_of_stage5b (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    {stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint} (pending : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (h : Stage3Stage6.stage5bHybridCheck stage5bHint w b = true) :
    corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending)) w b = true :=
  corpusCheckFix_of_later geometric direct sidecar bulkT (isOverlayBank_of_stage5bHybrid h)
    (orCheck_of_right (orCheck_of_left h))

/-- A `pending` item off the two Overlay banks is a prefix-check result. -/
theorem prefix_of_pending (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) {pending : WitnessRef → Cell → Bool}
    {w : WitnessRef} {b : Cell} (other : isOverlayBank w.source = false) (h : pending w b = true) :
    corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending)) w b = true :=
  corpusCheckFix_of_later geometric direct sidecar bulkT other (orCheck_of_right (orCheck_of_right h))

/-- A Stage6 `F` entry accepted by the hybrid `F` test is accepted by the Stage6 checker. -/
theorem stage6_of_fcc {stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint}
    {dEval : Stage6Request → Bool} {q : Stage6Request} (hc : q.proposal.compare = .fcc)
    (h : Stage3Stage6.stage6FHybrid stage6Hint q = true) : Stage3Stage6.stage6HybridCheck stage6Hint dEval q = true := by
  unfold Stage3Stage6.stage6HybridCheck
  rw [hc]
  exact h

/-- A Stage6 `D` entry accepted by `dEval` is accepted by the Stage6 checker. -/
theorem stage6_of_deficit {stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint}
    {dEval : Stage6Request → Bool} {q : Stage6Request} (hc : q.proposal.compare = .deficit)
    (h : dEval q = true) : Stage3Stage6.stage6HybridCheck stage6Hint dEval q = true := by
  unfold Stage3Stage6.stage6HybridCheck
  rw [hc]
  exact h

/-- A request the first checker accepts is accepted by `eitherCheck`. -/
theorem eitherCheck_of_left {a b : Checker} {q : Request} (h : a q = true) :
    eitherCheck a b q = true := by
  simp [eitherCheck, h]

/-- A request the second checker accepts is accepted by `eitherCheck`. -/
theorem eitherCheck_of_right {a b : Checker} {q : Request} (h : b q = true) :
    eitherCheck a b q = true := by
  simp [eitherCheck, h]

/-- A late request of the leaf family (Corner corners, JointDeficit and Continuation round-one corners and
joints) that the far J/F/D leaf check accepts is accepted by the late checker. -/
theorem late_of_leaf (t : LateTables) {q : Request} (hf : q.family = .leaf)
    (h : LeafFix.lateCheckFar t.leaf q = true) : lateChecker t q = true := by
  unfold lateChecker familyCheck
  rw [hf]
  exact h

/-- A late request of the transport family (HalfShift) that the HalfShift check accepts is accepted by
the late checker. -/
theorem late_of_transport (t : LateTables) {q : Request} (hf : q.family = .transport)
    (h : Layered.halfShiftCheck t.halfShift q = true) : lateChecker t q = true :=
  lateChecker_of_transport t hf (by simp [transportCheck, eitherCheck, h])

/-- A late request of the transport family (HalfShift) that the far-annulus HalfShift check accepts is
accepted by the late checker. -/
theorem late_of_transportFar (t : LateTables) {q : Request} (hf : q.family = .transport)
    (h : Layered.halfShiftCheckFar t.halfShiftFar q = true) : lateChecker t q = true :=
  lateChecker_of_transport t hf (by simp [transportCheck, eitherCheck, h])

/-- A late request of the transport family (HalfShift) that the catalogue check accepts is
accepted by the late checker. -/
theorem late_of_transportCat (t : LateTables) {q : Request} (hf : q.family = .transport)
    (h : Layered.halfShiftCheckCat t.halfShiftCat q = true) : lateChecker t q = true :=
  lateChecker_of_transport t hf (by simp [transportCheck, eitherCheck, h])

/-- A late request of the layered family that the PlanarAnchor check accepts is accepted by the late
checker. -/
theorem late_of_layered (t : LateTables) {q : Request} (hf : q.family = .layered)
    (h : Layered.planarAnchorCheck t.planarAnchor q = true) : lateChecker t q = true :=
  lateChecker_of_layered t hf (by simp [layeredCheck, eitherCheck, h])

/-- A late request of the layered family that the far-annulus PlanarAnchor check accepts is accepted
by the late checker. -/
theorem late_of_layeredFar (t : LateTables) {q : Request} (hf : q.family = .layered)
    (h : Layered.planarAnchorCheckFar t.planarAnchorFar q = true) : lateChecker t q = true :=
  lateChecker_of_layered t hf (by simp [layeredCheck, eitherCheck, h])

/-- A late request of the layered family (a PlanarFibre layered request) that the far-annulus PlanarFibre
check accepts is accepted by the late checker. -/
theorem late_of_layeredPlanarFibreFar (t : LateTables) {q : Request} (hf : q.family = .layered)
    (h : Layered.planarFibreCheckFar t.planarFibreFar q = true) : lateChecker t q = true :=
  lateChecker_of_layered t hf (by simp [layeredCheck, eitherCheck, h])

/-- A late request of the triangular family (PlanarFibre) that the triangular check accepts is
accepted by the late checker. -/
theorem late_of_triangular (t : LateTables) {q : Request} (hf : q.family = .triangular)
    (h : PlanarFibreTri.planarFibreTriCheck t.tri q = true) : lateChecker t q = true := by
  unfold lateChecker familyCheck
  rw [hf]
  exact h

/-- A late request of the centered family (PlanarAnchor) that the centered check accepts is accepted
by the late checker. -/
theorem late_of_centered (t : LateTables) {q : Request} (hf : q.family = .centered)
    (h : Layered.centeredCheck t.atlas t.centered q = true) : lateChecker t q = true := by
  unfold lateChecker familyCheck
  rw [hf]
  exact h

/-! ### The final theorem and its forms -/

/-- **The two-site theorem in full from the premises of the replay.** The premises are the soundness of
the checks still pending (`pendingSound` for the rest of the prefix through Stage5b, `dSound`
for the Stage6 `D` entries) and the three run equalities: the prefix through Stage5b under the
fixed-point prefix check with every merged `later` check (`rStage5b`), the Stage6 binding
(`rStage6`) and the late corpus (`closed`). Tables, hints, late tables and the replay data are
free. -/
theorem statementFull_of_replay (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) (pending : WitnessRef → Cell → Bool)
    (pendingSound : SoundCheck pending) (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dEval : Stage6Request → Bool) (dSound : Stage3Stage6.Stage6DSound dEval) (t : LateTables)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending))) = some stage5b)
    (rStage6 : runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint dEval)) stage5b rows = some stage6)
    (closed : corp.run (lateChecker t) stage6 = some []) :
    Full.StatementFull :=
  Full.statementFull_of_statement
    (GlobalInputs.assemble_from_cover_corpus_cover
      (prefix_sound geometric direct sidecar bulkT adaptiveHint stage5bHint pendingSound)
      (Stage3Stage6.stage6HybridCheck_sound stage6Hint dSound) (late_sound t)
      pre stage5b stage6 rStage5b rows corp rStage6 closed)

/-- **With nothing pending.** The empty checks fill the two slots (`pending` pays nothing and
`dEval` accepts nothing, so both are sound), and `StatementFull` follows from the three run
equalities alone, with the slots empty. On the data these cannot hold: in this form
nothing pays the Stage3, Stage4 and Stage5a witnesses or the Stage5b optical tiles other than
`whole_above`, whose checks enter through `pending`, and with `dEval` empty the Stage6 checker
is `stage6HybridNow`, which closes no `D` entry. Evaluators for `pending` and `dEval` enter
through `statementFull_of_replay` (`statementFull_of_replay_merged` with the merged ones);
this form fits only data that its checks close with nothing in `pending` and `dEval`. -/
theorem statementFull_of_runs (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint) (t : LateTables)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint fun _ _ => false))) =
        some stage5b)
    (rStage6 : runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint fun _ => false)) stage5b rows =
      some stage6)
    (closed : corp.run (lateChecker t) stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay geometric direct sidecar bulkT adaptiveHint stage5bHint (fun _ _ => false)
    (fun _ _ h => absurd h (by simp)) stage6Hint (fun _ => false) (fun _ h => absurd h (by simp)) t
    pre stage5b stage6 rows corp rStage5b rStage6 closed

/-- **The same with the late side in chunks** (`late_chunks`): each chunk's Stage6 rows and
late corpus rows run on the chunk's slice of the Stage5b roster, and the prefix ends in the
chunks' slices, in order. -/
theorem statementFull_of_replay_chunks (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) (pending : WitnessRef → Cell → Bool)
    (pendingSound : SoundCheck pending) (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dEval : Stage6Request → Bool) (dSound : Stage3Stage6.Stage6DSound dEval) (t : LateTables)
    (pre : CorpusPrefix) (cs : List LateChunk)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending))) =
        some (cs.flatMap LateChunk.stage5b))
    (hStage6 : ∀ c ∈ cs, runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint dEval)) c.stage5b c.rows =
      some c.stage6)
    (hcorp : ∀ c ∈ cs, c.corp.run (lateChecker t) c.stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay geometric direct sidecar bulkT adaptiveHint stage5bHint pending pendingSound
    stage6Hint dEval dSound t pre _ _ _ _ rStage5b (late_chunks cs hStage6 hcorp).1 (late_chunks cs hStage6 hcorp).2

/-- **The same with the prefix from its seven steps** (`CorpusPrefix.run_of`): the root plan,
the edits before the mirror, the positive selection and its edits, the `insideCheck` test,
the mirror, the edits after it, and the Stage5b binding, which ends in the late chunks'
slices. -/
theorem statementFull_of_replay_steps (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) (pending : WitnessRef → Cell → Bool)
    (pendingSound : SoundCheck pending) (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dEval : Stage6Request → Bool) (dSound : Stage3Stage6.Stage6DSound dEval) (t : LateTables)
    (pre : CorpusPrefix) (cs : List LateChunk) {directRoute old positive mirrored latest : Snapshot}
    (h0 : pre.originalRoot.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending))) root =
        some directRoute)
    (h1 : runEdits (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending)))
        directRoute pre.beforeMirror = some old)
    (h2 : runEdits (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending)))
        old.selectPositive pre.positiveStage = some positive)
    (h3 : positive.held.all (fun a => insideCheck a.cell root) = true)
    (h4 : mirror pre.mirrorKey old positive = some mirrored)
    (h5 : runEdits (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending)))
        mirrored pre.afterMirror = some latest)
    (h6 : bindStage5b latest pre.stage5b = some (cs.flatMap LateChunk.stage5b))
    (hStage6 : ∀ c ∈ cs, runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint dEval)) c.stage5b c.rows =
      some c.stage6)
    (hcorp : ∀ c ∈ cs, c.corp.run (lateChecker t) c.stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay_chunks geometric direct sidecar bulkT adaptiveHint stage5bHint pending
    pendingSound stage6Hint dEval dSound t pre cs (CorpusPrefix.run_of pre h0 h1 h2 h3 h4 h5 h6)
    hStage6 hcorp

/-- **The same with one more sound late checker, and the soundness of `lateChecker t` as a
premise.** The late corpus runs under `eitherCheck (lateChecker t) latePending`, and
`lateSound : CheckerSound (lateChecker t)` is a premise, which `late_sound t` supplies
(`statementFull_of_replay_latePending`). A change in the premises of `lateChecker_sound`
changes `late_sound` and the theorems that use it, not this one. -/
theorem statementFull_of_replay_lateSound (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) (pending : WitnessRef → Cell → Bool)
    (pendingSound : SoundCheck pending) (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dEval : Stage6Request → Bool) (dSound : Stage3Stage6.Stage6DSound dEval) (t : LateTables)
    (lateSound : CheckerSound (lateChecker t))
    (latePending : Checker) (latePendingSound : CheckerSound latePending)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending))) = some stage5b)
    (rStage6 : runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint dEval)) stage5b rows = some stage6)
    (closed : corp.run (eitherCheck (lateChecker t) latePending) stage6 = some []) :
    Full.StatementFull :=
  Full.statementFull_of_statement
    (GlobalInputs.assemble_from_cover_corpus_cover
      (prefix_sound geometric direct sidecar bulkT adaptiveHint stage5bHint pendingSound)
      (Stage3Stage6.stage6HybridCheck_sound stage6Hint dSound)
      (eitherCheck_sound lateSound latePendingSound)
      pre stage5b stage6 rStage5b rows corp rStage6 closed)

/-- **The same with one more sound late checker**: the late corpus runs under
`eitherCheck (lateChecker t) latePending`, so an evaluator for the late requests that
`lateChecker` does not accept enters as `latePending`
with `CheckerSound latePending`, without changing `lateChecker`.
`statementFull_of_replay_lateSound` with `lateSound := late_sound t`. -/
theorem statementFull_of_replay_latePending (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint) (pending : WitnessRef → Cell → Bool)
    (pendingSound : SoundCheck pending) (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dEval : Stage6Request → Bool) (dSound : Stage3Stage6.Stage6DSound dEval) (t : LateTables)
    (latePending : Checker) (latePendingSound : CheckerSound latePending)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint pending))) = some stage5b)
    (rStage6 : runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint dEval)) stage5b rows = some stage6)
    (closed : corp.run (eitherCheck (lateChecker t) latePending) stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay_lateSound geometric direct sidecar bulkT adaptiveHint stage5bHint pending
    pendingSound stage6Hint dEval dSound t (late_sound t) latePending latePendingSound pre stage5b stage6
    rows corp rStage5b rStage6 closed

/-! ### The merged form: the merged checks in the slots -/

/-- The two Stage3 sources are not Overlay banks (kernel evaluation of the exact-string match). -/
theorem stage3Sources_not_overlay :
    isOverlayBank "stage3/Z" = false ∧ isOverlayBank "stage3/correlated_phase" = false := by
  decide +kernel

/-- The four Stage5b optical sources are not Overlay banks (kernel evaluation of the exact-string
match). -/
theorem stage5bOpticalSources_not_overlay :
    isOverlayBank "stage5b/whole_defect" = false ∧ isOverlayBank "stage5b/screened_anchor" = false ∧
      isOverlayBank "stage5b/taylor_anchor" = false ∧ isOverlayBank "stage5b/optical_lattice" = false := by
  decide +kernel

/-- A witness that the Stage3 check accepts has one of the two Stage3 sources, so it is not an Overlay
bank witness. -/
theorem isOverlayBank_of_stage3 {hint : WitnessRef → Option Stage3Stage6.SupportHint} {w : WitnessRef}
    {b : Cell} (h : Stage3Stage6.stage3Check hint w b = true) : isOverlayBank w.source = false := by
  obtain ⟨s0, s1⟩ := stage3Sources_not_overlay
  by_cases h0 : w.source = "stage3/Z"
  · rw [h0]
    exact s0
  by_cases h1 : w.source = "stage3/correlated_phase"
  · rw [h1]
    exact s1
  rw [Stage3Stage6.stage3Check_other hint w b h0 h1] at h
  exact absurd h (by decide)

/-- A witness that the Stage5b optical check accepts has one of the four optical sources, so it
is not an Overlay bank witness. -/
theorem isOverlayBank_of_stage5bOptical {hint : WitnessRef → Option Stage5bOptical.OpticalHint}
    {w : WitnessRef} {b : Cell} (h : Stage5bOptical.stage5bOpticalCheck hint w b = true) :
    isOverlayBank w.source = false := by
  obtain ⟨s0, s1, s2, s3⟩ := stage5bOpticalSources_not_overlay
  by_cases h0 : w.source = "stage5b/whole_defect"
  · rw [h0]
    exact s0
  by_cases h1 : w.source = "stage5b/screened_anchor"
  · rw [h1]
    exact s1
  by_cases h2 : w.source = "stage5b/taylor_anchor"
  · rw [h2]
    exact s2
  by_cases h3 : w.source = "stage5b/optical_lattice"
  · rw [h3]
    exact s3
  have off : Stage5bOptical.opticalSource w.source = false := by
    simp [Stage5bOptical.opticalSource, h0, h1, h2, h3]
  rw [Stage5bOptical.stage5bOpticalCheck_other hint w b off] at h
  exact absurd h (by decide)

/-- A witness that the Stage4 and Stage5a check accepts has one of its four sources, so it is not
an Overlay bank witness. -/
theorem isOverlayBank_of_stage4stage5a {hint : WitnessRef → Option Stage4Stage5a.KHint} {w : WitnessRef}
    {b : Cell} (h : Stage4Stage5a.stage4stage5aCheck hint w b = true) : isOverlayBank w.source = false := by
  obtain ⟨s0, s1, s2, s3⟩ := Stage4Stage5a.isOverlayBank_own
  by_cases h0 : w.source = "stage4/optical"
  · rw [h0]
    exact s0
  by_cases h1 : w.source = "stage4/atlas"
  · rw [h1]
    exact s1
  by_cases h2 : w.source = "stage4/taylor"
  · rw [h2]
    exact s2
  by_cases h3 : w.source = "stage5a/anchored"
  · rw [h3]
    exact s3
  rw [Stage4Stage5a.stage4stage5aCheck_other hint b (Stage4Stage5a.ownSource_eq_false _ h0 h1 h2 h3)] at h
  exact absurd h (by decide)

/-- A witness that the anchored check `stage5aCheck` accepts has one of the four Stage4 and Stage5a
sources, so it is not an Overlay bank witness. `stage5aCheck` is not merged into `mergedPending` (it
needs an anchor-deficit evaluator `ev` with `AnchorSound ev`); this gives the source premise of
`prefix_of_pending'` when it is part of `pending'`. -/
theorem isOverlayBank_of_stage5a {ev : WitnessRef → Cell → ℚ → Bool}
    {hint : WitnessRef → Option Stage4Stage5a.AHint} {w : WitnessRef} {b : Cell}
    (h : Stage4Stage5a.stage5aCheck ev hint w b = true) : isOverlayBank w.source = false := by
  obtain ⟨s0, s1, s2, s3⟩ := Stage4Stage5a.isOverlayBank_own
  by_cases h0 : w.source = "stage4/optical"
  · rw [h0]
    exact s0
  by_cases h1 : w.source = "stage4/atlas"
  · rw [h1]
    exact s1
  by_cases h2 : w.source = "stage4/taylor"
  · rw [h2]
    exact s2
  by_cases h3 : w.source = "stage5a/anchored"
  · rw [h3]
    exact s3
  rw [Stage4Stage5a.stage5aCheck_other ev hint b (Stage4Stage5a.ownSource_eq_false _ h0 h1 h2 h3)] at h
  exact absurd h (by decide)

/-- **The merged prefix checks for `pending`**: the Stage3 leaves (`stage3Check`), the Stage5b
optical tiles (`stage5bOpticalCheck`) and the Stage4 and Stage5a sources (`stage4stage5aCheck`). Each
check accepts only its own exact sources. -/
def mergedPending (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint) : WitnessRef → Cell → Bool :=
  orCheck (Stage3Stage6.stage3Check stage3Hint)
    (orCheck (Stage5bOptical.stage5bOpticalCheck stage5bOptHint) (Stage4Stage5a.stage4stage5aCheck kHint))

/-- The merged prefix checks are sound for all hints; `LatticeCase` (needed by the Stage5b optical
and the Stage4 and Stage5a checks) is `latticeCase_proved`. -/
theorem mergedPending_sound (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint) :
    SoundCheck (mergedPending stage3Hint stage5bOptHint kHint) :=
  orCheck_sound (Stage3Stage6.stage3Check_sound stage3Hint)
    (orCheck_sound
      (Stage5bOptical.stage5bOpticalCheck_sound BravaisCover.StrainAtlas.latticeCase_proved stage5bOptHint)
      (Stage4Stage5a.stage4stage5aCheck_sound BravaisCover.StrainAtlas.latticeCase_proved kHint))

/-- A Stage3 item is a prefix-check result of the merged form. -/
theorem prefix_of_stage3 (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    {stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint}
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint) (pending' : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (h : Stage3Stage6.stage3Check stage3Hint w b = true) :
    corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'))) w b = true :=
  prefix_of_pending geometric direct sidecar bulkT adaptiveHint stage5bHint (isOverlayBank_of_stage3 h)
    (orCheck_of_left (orCheck_of_left h))

/-- A Stage5b optical item is a prefix-check result of the merged form. -/
theorem prefix_of_stage5bOptical (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    {stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint}
    (kHint : WitnessRef → Option Stage4Stage5a.KHint) (pending' : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (h : Stage5bOptical.stage5bOpticalCheck stage5bOptHint w b = true) :
    corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'))) w b = true :=
  prefix_of_pending geometric direct sidecar bulkT adaptiveHint stage5bHint (isOverlayBank_of_stage5bOptical h)
    (orCheck_of_left (orCheck_of_right (orCheck_of_left h)))

/-- A Stage4 or Stage5a item is a prefix-check result of the merged form. -/
theorem prefix_of_stage4stage5a (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    {kHint : WitnessRef → Option Stage4Stage5a.KHint} (pending' : WitnessRef → Cell → Bool)
    {w : WitnessRef} {b : Cell} (h : Stage4Stage5a.stage4stage5aCheck kHint w b = true) :
    corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'))) w b = true :=
  prefix_of_pending geometric direct sidecar bulkT adaptiveHint stage5bHint (isOverlayBank_of_stage4stage5a h)
    (orCheck_of_left (orCheck_of_right (orCheck_of_right h)))

/-- An item of the remaining slot `pending'` off the two Overlay banks is a prefix-check result of
the merged form. -/
theorem prefix_of_pending' (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint) {pending' : WitnessRef → Cell → Bool}
    {w : WitnessRef} {b : Cell} (other : isOverlayBank w.source = false) (h : pending' w b = true) :
    corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'))) w b = true :=
  prefix_of_pending geometric direct sidecar bulkT adaptiveHint stage5bHint other (orCheck_of_right h)

/-- **The merged form, with the soundness of `lateChecker t` as a premise.**
`statementFull_of_replay_lateSound` with `pending:= orCheck (mergedPending stage3Hint
stage5bOptHint kHint) pending'`, `dEval:= stage6DEval dhint` and `latePending:= latePending'`.
The soundness of every merged prefix and Stage6 check is discharged (`mergedPending_sound`,
`stage6DEval_sound`, with `LatticeCase` as `latticeCase_proved`); the merged late checks are in
`lateChecker` itself. `lateSound` is left as a premise, so that a change in the premises of
`lateChecker_sound` does not change this theorem; `statementFull_of_replay_merged` supplies it
with `late_sound t`. -/
theorem statementFull_of_replay_merged_lateSound
    (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint)
    (pending' : WitnessRef → Cell → Bool) (pendingSound' : SoundCheck pending')
    (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dhint : Stage6Request → Option Stage3Stage6.DHint) (t : LateTables)
    (lateSound : CheckerSound (lateChecker t))
    (latePending' : Checker) (latePendingSound' : CheckerSound latePending')
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending')))) = some stage5b)
    (rStage6 : runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint (Stage3Stage6.stage6DEval dhint)))
      stage5b rows = some stage6)
    (closed : corp.run (eitherCheck (lateChecker t) latePending') stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay_lateSound geometric direct sidecar bulkT adaptiveHint stage5bHint
    (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending')
    (orCheck_sound (mergedPending_sound stage3Hint stage5bOptHint kHint) pendingSound') stage6Hint
    (Stage3Stage6.stage6DEval dhint) (Stage3Stage6.stage6DEval_sound dhint) t lateSound latePending'
    latePendingSound' pre stage5b stage6 rows corp rStage5b rStage6 closed

/-- **The two-site theorem in full with the merged checks.** `statementFull_of_replay_latePending`
with `pending := orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'`,
`dEval := stage6DEval dhint` and `latePending := latePending'`; the merged late checks are in
`lateChecker` itself. The soundness of every merged check is discharged
(`mergedPending_sound`, `stage6DEval_sound`, `late_sound t`, with `LatticeCase` as
`latticeCase_proved`). The premises left are the soundness of the two remaining slots,
`pending'` for prefix witnesses and `latePending'` for late requests that no merged check
accepts, and the three run equalities. Tables, hints, late tables and the replay data are
free. It is `statementFull_of_replay_merged_lateSound` with `lateSound := late_sound t`. -/
theorem statementFull_of_replay_merged (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint)
    (pending' : WitnessRef → Cell → Bool) (pendingSound' : SoundCheck pending')
    (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dhint : Stage6Request → Option Stage3Stage6.DHint) (t : LateTables)
    (latePending' : Checker) (latePendingSound' : CheckerSound latePending')
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending')))) = some stage5b)
    (rStage6 : runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint (Stage3Stage6.stage6DEval dhint)))
      stage5b rows = some stage6)
    (closed : corp.run (eitherCheck (lateChecker t) latePending') stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay_merged_lateSound geometric direct sidecar bulkT adaptiveHint stage5bHint
    stage3Hint stage5bOptHint kHint pending' pendingSound' stage6Hint dhint t (late_sound t)
    latePending' latePendingSound' pre stage5b stage6 rows corp rStage5b rStage6 closed

/-- **The merged form with the late side in chunks** (`late_chunks`): each chunk's Stage6 rows
and late corpus rows run under the merged checks on the chunk's slice of the Stage5b roster, and
the prefix ends in the chunks' slices, in order. `lateSound` is a premise, as in
`statementFull_of_replay_merged_lateSound`; `late_sound t` supplies it. -/
theorem statementFull_of_replay_merged_chunks
    (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint)
    (pending' : WitnessRef → Cell → Bool) (pendingSound' : SoundCheck pending')
    (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dhint : Stage6Request → Option Stage3Stage6.DHint) (t : LateTables)
    (lateSound : CheckerSound (lateChecker t))
    (latePending' : Checker) (latePendingSound' : CheckerSound latePending')
    (pre : CorpusPrefix) (cs : List LateChunk)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending')))) =
        some (cs.flatMap LateChunk.stage5b))
    (hStage6 : ∀ c ∈ cs, runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint
      (Stage3Stage6.stage6DEval dhint))) c.stage5b c.rows = some c.stage6)
    (hcorp : ∀ c ∈ cs, c.corp.run (eitherCheck (lateChecker t) latePending') c.stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay_merged_lateSound geometric direct sidecar bulkT adaptiveHint stage5bHint
    stage3Hint stage5bOptHint kHint pending' pendingSound' stage6Hint dhint t lateSound latePending'
    latePendingSound' pre _ _ _ _ rStage5b (late_chunks cs hStage6 hcorp).1 (late_chunks cs hStage6 hcorp).2

/-- **The merged form with the prefix from its seven steps** (`CorpusPrefix.run_of`) and the
late side in chunks: the root plan, the edits before the mirror, the positive selection and
its edits, the `insideCheck` test, the mirror, the edits after it, and the Stage5b binding, which
ends in the late chunks' slices. `lateSound` is a premise; `late_sound t` supplies it. -/
theorem statementFull_of_replay_merged_steps
    (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint)
    (pending' : WitnessRef → Cell → Bool) (pendingSound' : SoundCheck pending')
    (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dhint : Stage6Request → Option Stage3Stage6.DHint) (t : LateTables)
    (lateSound : CheckerSound (lateChecker t))
    (latePending' : Checker) (latePendingSound' : CheckerSound latePending')
    (pre : CorpusPrefix) (cs : List LateChunk) {directRoute old positive mirrored latest : Snapshot}
    (h0 : pre.originalRoot.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending')))) root = some directRoute)
    (h1 : runEdits (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'))))
        directRoute pre.beforeMirror = some old)
    (h2 : runEdits (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'))))
        old.selectPositive pre.positiveStage = some positive)
    (h3 : positive.held.all (fun a => insideCheck a.cell root) = true)
    (h4 : mirror pre.mirrorKey old positive = some mirrored)
    (h5 : runEdits (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) pending'))))
        mirrored pre.afterMirror = some latest)
    (h6 : bindStage5b latest pre.stage5b = some (cs.flatMap LateChunk.stage5b))
    (hStage6 : ∀ c ∈ cs, runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint
      (Stage3Stage6.stage6DEval dhint))) c.stage5b c.rows = some c.stage6)
    (hcorp : ∀ c ∈ cs, c.corp.run (eitherCheck (lateChecker t) latePending') c.stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay_merged_chunks geometric direct sidecar bulkT adaptiveHint stage5bHint
    stage3Hint stage5bOptHint kHint pending' pendingSound' stage6Hint dhint t lateSound latePending'
    latePendingSound' pre cs (CorpusPrefix.run_of pre h0 h1 h2 h3 h4 h5 h6) hStage6 hcorp

/-- **The merged form with nothing remaining.** The empty check fills `pending'` (it is sound),
there is no late slot, and `StatementFull` follows from the three run equalities alone, under
the merged checks: `statementFull_of_replay` with `pending:= orCheck (mergedPending stage3Hint
stage5bOptHint kHint) (fun _ _ => false)` and `dEval:= stage6DEval dhint`. On the data these
hold only once a merged check pays every prefix witness and `lateChecker` accepts every late
request; until then the missing checks enter
through the slots of `statementFull_of_replay_merged`. -/
theorem statementFull_of_runs_merged (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulkT : WitnessRef → Option Stage2TablePayload)
    (adaptiveHint : WitnessRef → Option AdaptiveSupport.AdaptiveHint)
    (stage5bHint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage3Hint : WitnessRef → Option Stage3Stage6.SupportHint)
    (stage5bOptHint : WitnessRef → Option Stage5bOptical.OpticalHint)
    (kHint : WitnessRef → Option Stage4Stage5a.KHint)
    (stage6Hint : Stage6Request → Option Stage3Stage6.SupportHint)
    (dhint : Stage6Request → Option Stage3Stage6.DHint) (t : LateTables)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage5b : pre.run (corpusCheckFix geometric direct sidecar bulkT
      (orCheck (AdaptiveSupport.adaptiveFull adaptiveHint) (Stage3Stage6.laterHybrid stage5bHint
        (orCheck (mergedPending stage3Hint stage5bOptHint kHint) fun _ _ => false)))) = some stage5b)
    (rStage6 : runRows (runStage6 (Stage3Stage6.stage6HybridCheck stage6Hint (Stage3Stage6.stage6DEval dhint)))
      stage5b rows = some stage6)
    (closed : corp.run (lateChecker t) stage6 = some []) :
    Full.StatementFull :=
  statementFull_of_replay geometric direct sidecar bulkT adaptiveHint stage5bHint
    (orCheck (mergedPending stage3Hint stage5bOptHint kHint) fun _ _ => false)
    (orCheck_sound (mergedPending_sound stage3Hint stage5bOptHint kHint) (fun _ _ h => absurd h (by simp)))
    stage6Hint (Stage3Stage6.stage6DEval dhint) (Stage3Stage6.stage6DEval_sound dhint) t pre stage5b stage6 rows corp
    rStage5b rStage6 closed

end BccSharp.Coulomb.FinalAssembly
