import BccSharp.Cover.DataPathLater

set_option autoImplicit false

/-! # Lifting a stage's per-item facts to the prefix check

The run theorems of `BccSharp.Cover.DataPathLater` take the arithmetic as a hypothesis on any check.
The prefix runs under `corpusCheck geometric direct sidecar bulk later`, and the evaluator
modules state their results for their own component of `later` (`stage5bHybridCheck hint`, …).
These lemmas make the step from one to the other a single term, so a chunk's run fact needs
one Bool evaluation of its items under the component check.

* `orderedCheck`: a cell's endpoints are ordered, as one Bool (`orderedCell_of_check`).
* `replayStage_treeRows_corpus`: a sparse tree stage on a chunk runs under the prefix check when
  every closed leaf is off the two Overlay banks and accepted by a check that `later` accepts.
* `runEdits_clipEdits_corpus`: the same for a chunk's clips, with the arithmetic per source. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay OverlayPlanar OverlayPlanar.Fix OverlayCorpus

namespace DataPath.Later

/-- A cell's endpoints are ordered on every axis, as one Bool. -/
def orderedCheck (b : Cell) : Bool := (List.finRange 8).all fun i => decide (b.lo i ≤ b.hi i)

theorem orderedCell_of_check {b : Cell} (h : orderedCheck b = true) : OrderedCell b := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

theorem mem_of_mem_maskHits : ∀ {held : List AddressedCell} {m : ℕ} {a : AddressedCell},
    a ∈ maskHits held m → a ∈ held
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: rest, m, a, h => by
    simp only [maskHits] at h
    rcases List.mem_append.mp h with h | h
    · split at h
      · exact List.mem_singleton.mp h ▸ List.mem_cons_self
      · exact absurd h List.not_mem_nil
    · exact List.mem_cons_of_mem _ (mem_of_mem_maskHits h)

/-- Every atom of a chunk has ordered endpoints, from one Bool. -/
theorem ordered_of_all {held : List AddressedCell} (h : held.all (fun a => orderedCheck a.cell) = true)
    (m : ℕ) : ∀ a ∈ maskHits held m, OrderedCell a.cell :=
  fun a ha => orderedCell_of_check (List.all_eq_true.mp h a (mem_of_mem_maskHits ha))

/-- **A sparse tree stage under the prefix check.** If every closed leaf of the chunk is off the
two Overlay banks and accepted by `mine`, and `later` accepts what `mine` accepts, the chunk's rows
replay under `corpusCheck … later`. -/
theorem replayStage_treeRows_corpus (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later mine : WitnessRef → Cell → Bool}
    (hl : ∀ w b, mine w b = true → later w b = true) (kinds : List (Route × String)) (fuel : ℕ)
    (held : List AddressedCell) (m s r : ℕ) (ho : ∀ a ∈ maskHits held m, OrderedCell a.cell)
    (hc : (treeCloses kinds fuel held m s r).all (fun x => ! isOverlayBank x.1.source && mine x.1 x.2) = true) :
    ∃ paid, replayStage (corpusCheck geometric direct sidecar bulk later) held (treeRows kinds fuel held m s r) =
      some ⟨paid, treeOut kinds fuel held m s r⟩ :=
  replayStage_treeRows kinds fuel held m s r ho fun x hx => by
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc x hx)
    have h1' : isOverlayBank x.1.source = false := by simpa using h1
    exact corpusCheck_of_later geometric direct sidecar bulk h1' (hl _ _ h2)

/-- **A chunk's clips under the prefix check.** -/
theorem runEdits_clipEdits_corpus (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later mine : WitnessRef → Cell → Bool}
    (hl : ∀ w b, mine w b = true → later w b = true) (cs : List ClipSpec) (q held : List AddressedCell)
    (hg : clipsGeom cs held = true)
    (ha : cs.all (fun c => ! isOverlayBank c.receipt.source && mine c.receipt c.source) = true) :
    runEdits (corpusCheck geometric direct sidecar bulk later) ⟨q, held⟩ (clipEdits cs held) =
      some ⟨q ++ clipsPaid cs held, clipsOut cs held⟩ :=
  runEdits_clipEdits cs q held hg fun c hc => by
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ha c hc)
    have h1' : isOverlayBank c.receipt.source = false := by simpa using h1
    exact corpusCheck_of_later geometric direct sidecar bulk h1' (hl _ _ h2)

end DataPath.Later

end BccSharp.Coulomb.CompactCover
