import BccSharp.Cover.DataPathLaterChecks
import BccSharp.Cover.DataPathLaterMirror

set_option autoImplicit false

/-! # Chunk facts with literal outputs, as single terms

A chunk's output is compared with the expected one by one Bool (`sameRoster`), and the run fact
then names the literal output. The step from the Bool to the run fact must not be a tactic on
the chunk's data: `rw` or `simpa` there make the elaborator unify, and so evaluate, the data
terms. The lemmas below take the data as variables, so their proofs never see it, and a
chunk's fact is one term application whose instances are syntactic:

* `replayStage_treeRows_rest`: a sparse tree chunk with a given held list;
* `runEdits_clipEdits_rest`: a clip chunk with a given residue;
* `runRows_close_all`: Stage6 atoms that one entry closes;
* `bindStage5b_one`: one Stage5b binding chunk;
* `Trie.clips_of_near`: a positive atom's mirror clips over a checked trie. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay OverlayPlanar OverlayPlanar.Fix OverlayCorpus

namespace DataPath.Later

/-- **A sparse tree chunk with a given held list.** -/
theorem replayStage_treeRows_rest {check : WitnessRef → Cell → Bool} (kinds : List (Route × String))
    (fuel : ℕ) (held : List AddressedCell) (m s r : ℕ) (out : List AddressedCell)
    (ho : ∀ a ∈ maskHits held m, OrderedCell a.cell)
    (hout : sameRoster (treeOut kinds fuel held m s r) out = true)
    (hc : ∀ x ∈ treeCloses kinds fuel held m s r, check x.1 x.2 = true) :
    ∃ paid, replayStage check held (treeRows kinds fuel held m s r) = some ⟨paid, out⟩ := by
  rw [← sameRoster_exact _ _ hout]
  exact replayStage_treeRows kinds fuel held m s r ho hc

/-- **A clip chunk with a given residue.** -/
theorem runEdits_clipEdits_rest {check : WitnessRef → Cell → Bool} (cs : List ClipSpec)
    (held rest : List AddressedCell) (hg : clipsGeom cs held = true)
    (hout : sameRoster (clipsOut cs held) rest = true) (ha : ∀ c ∈ cs, check c.receipt c.source = true) :
    runEdits check ⟨[], held⟩ (clipEdits cs held) = some ⟨clipsPaid cs held, rest⟩ := by
  rw [← sameRoster_exact _ _ hout]
  simpa using runEdits_clipEdits cs [] held hg ha

/-- **Stage6 atoms that one entry closes**: rows `⟨a, .close w⟩` read by `runRows`. -/
theorem runRows_close_all {early : Stage6Checker} (w : Stage6Proposal) (atoms : List LatePackets.Atom)
    (hg : atoms.all (fun a => (⟨a, w⟩ : Stage6Request).geometry) = true)
    (ha : ∀ a ∈ atoms, early ⟨a, w⟩ = true) :
    LatePackets.runRows (runStage6 early) atoms (atoms.map fun a => ⟨a, .close w⟩) = some [] := by
  have h := LatePackets.runRows_items (run := runStage6 early)
    (atoms.map fun a => (a, Stage6Trace.close w, ([] : List LatePackets.Atom))) fun x hx => by
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hx
      exact runStage6_close a w (List.all_eq_true.mp hg a ha') (ha a ha')
  have e1 : (atoms.map fun a => (a, Stage6Trace.close w, ([] : List LatePackets.Atom))).map Prod.fst = atoms := by
    rw [List.map_map]
    exact List.map_id atoms
  have e2 : (atoms.map fun a => (a, Stage6Trace.close w, ([] : List LatePackets.Atom))).map
      (fun x => (⟨x.1, x.2.1⟩ : LatePackets.Row Stage6Trace)) = atoms.map fun a => ⟨a, .close w⟩ := by
    simp
  have e3 : (atoms.map fun a => (a, Stage6Trace.close w, ([] : List LatePackets.Atom))).flatMap
      (fun x => x.2.2) = [] := by
    simp
  rw [e1, e2, e3] at h
  exact h

/-- **One Stage5b binding chunk**: a snapshot holding `held` binds the roster entries `owners`
when their decode succeeds and its cells are `held`'s. -/
theorem bindStage5b_one (s : Snapshot) (held : List AddressedCell) (owners : List RosterOwner)
    (hs : s.held = held) (hd : (owners.mapM RosterOwner.atoms).isSome = true)
    (hr : relabelCheck held (((owners.mapM RosterOwner.atoms).getD []).flatten.map LatePackets.Atom.asCell) = true) :
    bindStage5b s owners = some ((owners.mapM RosterOwner.atoms).getD []).flatten := by
  have h := bindStage5b_chunks s [⟨held, owners, (owners.mapM RosterOwner.atoms).getD []⟩] (by simpa using hs)
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact eq_some_getD_of_isSome [] hd)
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact hr)
  simpa using h

end DataPath.Later

namespace DataPath.LaterMirror

/-- **A positive atom's clips over a checked trie**, from its search's clips (one Bool). -/
theorem Trie.clips_of_near (key : Key → Key → Key) (chunkAt : ℕ → List AddressedCell) (a : AddressedCell)
    (t : Trie) (b : Cell) (hb : DataPath.Later.orderedCheck b = true)
    (hv : (t.leafCells b).all (Trie.checkChunk chunkAt) = true) (expected : List AddressedCell)
    (hn : sameRoster ((t.near a.cell b).map (chunkClips key chunkAt a)).flatten expected = true) :
    (t.chunks.map (chunkClips key chunkAt a)).flatten = expected := by
  rw [Trie.clips_near key chunkAt a a.cell (insideCheck_self _) t b (DataPath.Later.orderedCell_of_check hb)
    (List.all_eq_true.mp hv)]
  exact sameRoster_exact _ _ hn

end DataPath.LaterMirror

end BccSharp.Coulomb.CompactCover
