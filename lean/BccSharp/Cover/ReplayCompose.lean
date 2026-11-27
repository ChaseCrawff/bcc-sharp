import BccSharp.Cover.DataPathPacker

set_option autoImplicit false

/-! Compositional replay: the three run equalities of `assemble_from_overlay_corpus`

* `pre.run (corpusCheck … later) = some stage5b`, the prefix through Stage5b;
* `runRows (runStage6 early) stage5b rows = some stage6`, the Stage6 binding;
* `corp.run late stage6 = some []`, the late corpus

from per-chunk and per-item facts. With about 17 million items none of the three can be one
kernel evaluation. Every lemma here is generic in the data: its proof evaluates nothing, and
applying it to chunk facts re-evaluates no chunk.

* **Late side.** `runRows_append`, `runRows_chunks` (a pass from its chunks),
  `runRows_items` (rows built from the atoms they read, so no atom comparison is
  evaluated); `Corpus.append`, `Corpus.concat`, `Corpus.run_append`, `Corpus.run_chunks`;
  `LateChunk` and `late_chunks` (the Stage6 binding and the late corpus together). Per item:
  `runStage6_keep`, `runStage6_close`, `closeCheck_of`, `Tree.run_of_requests` (a late tree
  from its closed leaves' requests), `Join.run_keep`, `Join.run_close`,
  `WholeOverlay.run_primary`, `WholeOverlay.run_fiber` and `WholeOverlay.run_hold_fiber`
  (a `.hold` primary under a closing PlanarFibre fiber), `terminal_run`.
* **Prefix.** `CorpusPrefix.run_of` (the prefix from its seven steps); `StageChunk`,
  `replayStage_chunks`, `splitPass_chunks` (a stage edit from per-chunk `replayStage`
  runs), and `replayStage_chunks_exists`, `splitPass_chunks_exists` for row theorems that
  give only `∃ paid`; `runEdits_cons_of`, `runEdits_append_of`; merges and clips on one
  chunk: `Edit.isLocal`, `frameEdit`, `sameRoster_frame`, `frame_run`, `local_run_shift`,
  `runEdits_shift`, `runEdits_frame`, `EditChunk`, `framedEdits`, `runEdits_framed`; a clip
  row from its geometry and its certificate's arithmetic: `ClipRow.check_of`; chunks after
  a rotation: `rotate_chunks`; `selectPositive_chunks`, `filter_positive_self`,
  `filter_positive_nil`, `all_chunks` (the positive selection and the `insideCheck` test by
  chunks); `relabelCheck_append`, `mapM_chunks`, `BindChunk`, `bindStage5b_chunks`,
  `eq_some_getD_of_isSome` (the Stage5b binding from per-chunk roster decodes and relabel
  checks), `bind_late_glue` (its output as the late chunks' input).
* **Mirror.** The intended route, with no global index: `mirror_chunks` (clips chunk by
  chunk), `positiveCell_mono2`, `filterMap_clip_far`, `flatten_map_filter` (far chunks
  dropped by a bounding-box test). The alternative `mirror_candidates` (clips from candidate
  indices into one roster) with `off_of_buckets`, `gridBins_sound`, `gridBins_sound_any`,
  `prodBuckets_sound` would need chunk-local indices to be efficient.
* **Checks.** `orCheck_of_left`, `orCheck_of_right`, `corpusCheck_of_later`.
-/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay

/-! ### The late side: `runRows`, the Stage6 binding and the late corpus -/

namespace LatePackets

theorem sameAtom_self (a : Atom) : sameAtom a a = true := by
  simp [sameAtom, sameAddressedCell, sameCell_self]

/-- **Rows over appended inputs.** Two runs of `runRows` give the run over the appended atoms and
rows, with the appended outputs. -/
theorem runRows_append {α : Type} {run : Atom → α → Option (List Atom)} :
    ∀ (xs ys : List Atom) (rs ss : List (Row α)) (o₁ o₂ : List Atom),
      runRows run xs rs = some o₁ → runRows run ys ss = some o₂ →
        runRows run (xs ++ ys) (rs ++ ss) = some (o₁ ++ o₂)
  | [], ys, [], ss, o₁, o₂, h₁, h₂ => by
      simp only [runRows, Option.some.injEq] at h₁
      subst h₁
      simpa using h₂
  | [], _, _ :: _, _, _, _, h₁, _ => by simp [runRows] at h₁
  | _ :: _, _, [], _, _, _, h₁, _ => by simp [runRows] at h₁
  | a :: xs, ys, r :: rs, ss, o₁, o₂, h₁, h₂ => by
      by_cases key : sameAtom a r.input = true
      · cases hr : run a r.trace with
        | none => simp [runRows, key, hr] at h₁
        | some x =>
          cases ht : runRows run xs rs with
          | none => simp [runRows, key, hr, ht] at h₁
          | some t =>
            have e : x ++ t = o₁ := by simpa [runRows, key, hr, ht] using h₁
            subst e
            have ih := runRows_append xs ys rs ss t o₂ ht h₂
            simp [runRows, key, hr, ih]
      · simp [runRows, key] at h₁

/-- A chunk of a `runRows` pass: its input atoms, its rows and its output. -/
structure RowsChunk (α : Type) where
  input : List Atom
  rows : List (Row α)
  output : List Atom

/-- **A pass from its chunks.** -/
theorem runRows_chunks {α : Type} {run : Atom → α → Option (List Atom)} :
    ∀ cs : List (RowsChunk α), (∀ c ∈ cs, runRows run c.input c.rows = some c.output) →
      runRows run (cs.flatMap RowsChunk.input) (cs.flatMap RowsChunk.rows) =
        some (cs.flatMap RowsChunk.output)
  | [], _ => by simp [runRows]
  | c :: cs, h => by
      simp only [List.flatMap_cons]
      exact runRows_append _ _ _ _ _ _ (h c (by simp))
        (runRows_chunks cs fun d hd => h d (by simp [hd]))

/-- **Rows built from their own atoms.** An item is an atom, its trace and its output. The rows
read the items' atoms, so `runRows` compares each atom with itself (`sameAtom_self`) and
evaluates no geometry; only the items' own runs are needed. -/
theorem runRows_items {α : Type} {run : Atom → α → Option (List Atom)} :
    ∀ items : List (Atom × α × List Atom), (∀ x ∈ items, run x.1 x.2.1 = some x.2.2) →
      runRows run (items.map Prod.fst) (items.map fun x => ⟨x.1, x.2.1⟩) =
        some (items.flatMap fun x => x.2.2)
  | [], _ => by simp [runRows]
  | x :: items, h => by
      have hx := h x (by simp)
      have ih := runRows_items items fun y hy => h y (by simp [hy])
      simp [runRows, sameAtom_self, hx, ih]

/-- A closed leaf's request passes when its three data checks and the arithmetic do. -/
theorem closeCheck_of {check : Checker} {q : Request} (pre : q.prefixCheck = true)
    (profile : q.profileCheck = true) (scope : q.scopeCheck = true) (arith : check q = true) :
    closeCheck check q = true := by
  simp [closeCheck, pre, profile, scope, arith]

/-- The requests a late tree's closed leaves make, in order. -/
def Tree.requests (packet : Packet) (atom : Atom) : Path → Tree → List Request
  | _, .hold => []
  | path, .close leaf => [⟨packet, atom, path, leaf⟩]
  | path, .split i low high =>
      Tree.requests packet atom (path ++ [⟨i, false⟩]) low ++
        Tree.requests packet atom (path ++ [⟨i, true⟩]) high

/-- The atoms a late tree holds, in order. -/
def Tree.holdsAt (atom : Atom) : Path → Tree → List Atom
  | path, .hold => [atom.atPath path]
  | _, .close _ => []
  | path, .split i low high =>
      Tree.holdsAt atom (path ++ [⟨i, false⟩]) low ++ Tree.holdsAt atom (path ++ [⟨i, true⟩]) high

/-- **A late tree from its closed leaves.** If every closed leaf's request passes
`closeCheck`, the tree runs and holds `holdsAt`; no geometry is evaluated. -/
theorem Tree.run_of_requests {check : Checker} (packet : Packet) (atom : Atom) :
    ∀ (t : Tree) (path : Path), (∀ q ∈ Tree.requests packet atom path t, closeCheck check q = true) →
      t.run check packet atom path = some (Tree.holdsAt atom path t)
  | .hold, _, _ => rfl
  | .close leaf, path, h => by
      have hq := h ⟨packet, atom, path, leaf⟩ (by simp [Tree.requests])
      simp [Tree.run, Tree.holdsAt, hq]
  | .split i low high, path, h => by
      have hl := Tree.run_of_requests packet atom low (path ++ [⟨i, false⟩])
        fun q hq => h q (by simp [Tree.requests, hq])
      have hh := Tree.run_of_requests packet atom high (path ++ [⟨i, true⟩])
        fun q hq => h q (by simp [Tree.requests, hq])
      simp [Tree.run, Tree.holdsAt, hl, hh]

/-- A join row with no proposal keeps its atom. -/
theorem Join.run_keep {check : Checker} (a : Atom) : (⟨none, none⟩ : Join).run check a = some [a] := by
  simp [Join.run]

/-- A join row with a proposal closes its atom when each present lane's request passes. Under
the choice below, an atom with both a Corner and a HalfShift proposal gets only the Corner one. -/
theorem Join.run_close {check : Checker} (a : Atom) (q : Join)
    (present : (q.corner.isSome || q.optical.isSome) = true)
    (corner : ∀ v, q.corner = some v → closeCheck check ⟨.cornerRule, a, [], v⟩ = true)
    (optical : ∀ w, q.optical = some w → closeCheck check ⟨.halfShift, a, [], w⟩ = true) :
    q.run check a = some [] := by
  rcases q with ⟨c, o⟩
  cases c <;> cases o <;> simp_all [Join.run]

/-- The packet of a PlanarFibre fiber on an atom. -/
def planarFibrePacket (a : Atom) : Packet := if a.label = .saturated then .planarFibreSaturated else .planarFibreOther

/-- An adaptive row without a fiber holds what its primary tree holds. -/
theorem WholeOverlay.run_primary {check : Checker} (a : Atom) (primary : Tree)
    (h : ∀ q ∈ Tree.requests .jointDeficit a [] primary, closeCheck check q = true) :
    (⟨primary, none⟩ : WholeOverlay).run check a = some (Tree.holdsAt a [] primary) := by
  simp [WholeOverlay.run, Tree.run_of_requests .jointDeficit a primary [] h]

/-- An adaptive row with a PlanarFibre fiber that holds nothing closes its atom; its primary tree
must still run. -/
theorem WholeOverlay.run_fiber {check : Checker} (a : Atom) (primary fiber : Tree)
    (hp : ∀ q ∈ Tree.requests .jointDeficit a [] primary, closeCheck check q = true)
    (hf : ∀ q ∈ Tree.requests (planarFibrePacket a) a [] fiber, closeCheck check q = true)
    (closed : Tree.holdsAt a [] fiber = []) :
    (⟨primary, some fiber⟩ : WholeOverlay).run check a = some [] := by
  have h1 := Tree.run_of_requests .jointDeficit a primary [] hp
  have h2 := Tree.run_of_requests (planarFibrePacket a) a fiber [] hf
  simp only [planarFibrePacket] at h2
  simp [WholeOverlay.run, h1, h2, closed]

/-- **The choice under the PlanarFibre roots.** A `.hold` primary always runs, and a
fiber that holds nothing then closes the atom: the JointDeficit work under those roots is not needed. -/
theorem WholeOverlay.run_hold_fiber {check : Checker} (a : Atom) (fiber : Tree)
    (hf : ∀ q ∈ Tree.requests (planarFibrePacket a) a [] fiber, closeCheck check q = true)
    (closed : Tree.holdsAt a [] fiber = []) :
    (⟨.hold, some fiber⟩ : WholeOverlay).run check a = some [] :=
  WholeOverlay.run_fiber a .hold fiber (by simp [Tree.requests]) hf closed

/-- A terminal (PlanarAnchor) row closes its atom when its request passes. -/
theorem terminal_run {check : Checker} (a : Atom) (w : LeafProposal)
    (h : closeCheck check ⟨.planarAnchor, a, [], w⟩ = true) :
    Tree.run check .planarAnchor a [] (.close w) = some [] := by
  simp [Tree.run, h]

/-- The field-wise concatenation of two late corpora. -/
def Corpus.append (c d : Corpus) : Corpus :=
  ⟨c.joint ++ d.joint, c.adaptive ++ d.adaptive, c.round1 ++ d.round1, c.terminal ++ d.terminal⟩

/-- The late corpus with no rows. -/
def Corpus.empty : Corpus := ⟨[], [], [], []⟩

/-- The late corpus of a list of chunks. -/
def Corpus.concat (cs : List Corpus) : Corpus := cs.foldr Corpus.append Corpus.empty

/-- **The late corpus over appended inputs.** -/
theorem Corpus.run_append {check : Checker} {x y o₁ o₂ : List Atom} {c d : Corpus}
    (hc : c.run check x = some o₁) (hd : d.run check y = some o₂) :
    (c.append d).run check (x ++ y) = some (o₁ ++ o₂) := by
  simp only [Corpus.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at hc hd ⊢
  obtain ⟨a₁, hJ, b₁, hA, r₁, hR, hT⟩ := hc
  obtain ⟨a₂, hJ', b₂, hA', r₂, hR', hT'⟩ := hd
  exact ⟨a₁ ++ a₂, runRows_append _ _ _ _ _ _ hJ hJ', b₁ ++ b₂, runRows_append _ _ _ _ _ _ hA hA',
    r₁ ++ r₂, runRows_append _ _ _ _ _ _ hR hR', runRows_append _ _ _ _ _ _ hT hT'⟩

/-- **The late corpus from its chunks.** Each chunk is its input atoms and its corpus rows. -/
theorem Corpus.run_chunks {check : Checker} :
    ∀ cs : List (List Atom × Corpus), (∀ x ∈ cs, x.2.run check x.1 = some []) →
      (Corpus.concat (cs.map Prod.snd)).run check (cs.flatMap Prod.fst) = some []
  | [], _ => by simp [Corpus.concat, Corpus.empty, Corpus.run, runRows]
  | x :: cs, h => by
      have := Corpus.run_append (h x (by simp)) (Corpus.run_chunks cs fun y hy => h y (by simp [hy]))
      simpa [Corpus.concat] using this

end LatePackets

open LatePackets

/-- A kept Stage6 atom is relabelled. -/
theorem runStage6_keep {check : Stage6Checker} (a : Atom) (label : InputClass) :
    runStage6 check a (.keep label) = some [{a with label := label}] := rfl

/-- A closed Stage6 atom: the request's geometry (a data check) and the Stage6 checker. -/
theorem runStage6_close {check : Stage6Checker} (a : Atom) (w : Stage6Proposal)
    (geometry : (⟨a, w⟩ : Stage6Request).geometry = true) (arith : check ⟨a, w⟩ = true) :
    runStage6 check a (.close w) = some [] := by
  simp [runStage6, geometry, arith]

/-- A chunk of the late replay: a slice of the Stage5b roster, its Stage6 rows, the atoms they
leave, and the late corpus rows on those atoms. -/
structure LateChunk where
  stage5b : List Atom
  rows : List (Row Stage6Trace)
  stage6 : List Atom
  corp : Corpus

/-- **The Stage6 binding and the late corpus from chunks.** -/
theorem late_chunks {early : Stage6Checker} {late : Checker} (cs : List LateChunk)
    (hStage6 : ∀ c ∈ cs, runRows (runStage6 early) c.stage5b c.rows = some c.stage6)
    (hcorp : ∀ c ∈ cs, c.corp.run late c.stage6 = some []) :
    runRows (runStage6 early) (cs.flatMap LateChunk.stage5b) (cs.flatMap LateChunk.rows) =
        some (cs.flatMap LateChunk.stage6) ∧
      (Corpus.concat (cs.map LateChunk.corp)).run late (cs.flatMap LateChunk.stage6) = some [] := by
  constructor
  · have h := runRows_chunks (run := runStage6 early) (cs.map fun c => ⟨c.stage5b, c.rows, c.stage6⟩)
      (by simpa using hStage6)
    simpa [List.flatMap_map] using h
  · have h := Corpus.run_chunks (check := late) (cs.map fun c => (c.stage6, c.corp)) (by simpa using hcorp)
    simpa [List.flatMap_map, List.map_map, Function.comp_def] using h

/-! ### The prefix: `CorpusPrefix.run` from its steps, stages from chunks -/

namespace EarlyReplay

/-- **The prefix from its seven steps**: the root plan, the edits before the mirror, the
positive selection and its edits, the `insideCheck` test, the mirror, the edits after it,
and the Stage5b binding. -/
theorem CorpusPrefix.run_of {check : WitnessRef → Cell → Bool} (c : CorpusPrefix)
    {directRoute old positive mirrored latest : Snapshot} {atoms : List Atom}
    (h0 : c.originalRoot.run check root = some directRoute)
    (h1 : runEdits check directRoute c.beforeMirror = some old)
    (h2 : runEdits check old.selectPositive c.positiveStage = some positive)
    (h3 : positive.held.all (fun a => insideCheck a.cell root) = true)
    (h4 : mirror c.mirrorKey old positive = some mirrored)
    (h5 : runEdits check mirrored c.afterMirror = some latest)
    (h6 : bindStage5b latest c.stage5b = some atoms) :
    c.run check = some atoms := by
  simp [CorpusPrefix.run, h0, h1, h2, h4, h5, h6]
  exact List.all_eq_true.mp h3

/-- `replayStage` fails unless it consumes atoms and rows in lockstep. -/
theorem replayStage_length {check : WitnessRef → Cell → Bool} :
    ∀ (xs : List AddressedCell) (rs : List StageRow) (o : Snapshot),
      replayStage check xs rs = some o → xs.length = rs.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [replayStage] at h
  | _ :: _, [], _, h => by simp [replayStage] at h
  | a :: xs, r :: rs, o, h => by
      by_cases geom : sameAddressedCell a r.input = true
      · cases hp : r.plan.run check a.cell with
        | none => simp [replayStage, geom, hp] at h
        | some f =>
          cases ht : replayStage check xs rs with
          | none => simp [replayStage, geom, hp, ht] at h
          | some t => simp [replayStage_length xs rs t ht]
      · simp [replayStage, geom] at h

/-- A chunk of a stage: its held atoms, their rows, and the snapshot they produce. -/
structure StageChunk where
  held : List AddressedCell
  rows : List StageRow
  out : Snapshot

/-- **A stage replay from its chunks.** -/
theorem replayStage_chunks {check : WitnessRef → Cell → Bool} :
    ∀ cs : List StageChunk, (∀ c ∈ cs, replayStage check c.held c.rows = some c.out) →
      replayStage check (cs.flatMap StageChunk.held) (cs.flatMap StageChunk.rows) =
        some ⟨cs.flatMap fun c => c.out.paid, cs.flatMap fun c => c.out.held⟩
  | [], _ => rfl
  | c :: cs, h => by
      have hc := h c (by simp)
      have ih := replayStage_chunks cs fun d hd => h d (by simp [hd])
      simp only [List.flatMap_cons]
      rw [DataPath.replayStage_append _ _ _ _ (replayStage_length _ _ _ hc), hc, ih]
      rfl

/-- **A stage edit from its chunks.** If the held list is the chunks' atoms in order and each
chunk replays, the `splitPass` edit of all the rows runs. -/
theorem splitPass_chunks {check : WitnessRef → Cell → Bool} (s : Snapshot) (cs : List StageChunk)
    (held : s.held = cs.flatMap StageChunk.held)
    (h : ∀ c ∈ cs, replayStage check c.held c.rows = some c.out) :
    (Edit.splitPass (cs.flatMap StageChunk.rows)).run check s =
      some ⟨s.paid ++ cs.flatMap (fun c => c.out.paid), cs.flatMap fun c => c.out.held⟩ := by
  simp [Edit.run, Snapshot.advance, held, replayStage_chunks cs h]

/-- One edit, then the rest. -/
theorem runEdits_cons_of {check : WitnessRef → Cell → Bool} {s t : Snapshot} {e : Edit} {es : List Edit}
    (h : e.run check s = some t) : runEdits check s (e :: es) = runEdits check t es := by
  simp [runEdits, h]

/-- Two runs of edits, one after the other. -/
theorem runEdits_append_of {check : WitnessRef → Cell → Bool} {s t u : Snapshot} {xs ys : List Edit}
    (h₁ : runEdits check s xs = some t) (h₂ : runEdits check t ys = some u) :
    runEdits check s (xs ++ ys) = some u := by
  rw [DataPath.runEdits_append, h₁]
  exact h₂

/-- **A stage replay from its chunks, paid lists existential.** The row and segment run
theorems (`Tree.toPlan_run_of_closes`, `replayStage_maskRows`, `replayStage_streamRows`) give
only `∃ paid`; this form joins them. -/
theorem replayStage_chunks_exists {check : WitnessRef → Cell → Bool} :
    ∀ cs : List (List AddressedCell × List StageRow × List AddressedCell),
      (∀ c ∈ cs, ∃ paid, replayStage check c.1 c.2.1 = some ⟨paid, c.2.2⟩) →
      ∃ paid, replayStage check (cs.flatMap Prod.fst) (cs.flatMap fun c => c.2.1) =
        some ⟨paid, cs.flatMap fun c => c.2.2⟩
  | [], _ => ⟨[], rfl⟩
  | c :: cs, h => by
    obtain ⟨p, hc⟩ := h c (by simp)
    obtain ⟨q, ih⟩ := replayStage_chunks_exists cs fun d hd => h d (by simp [hd])
    refine ⟨p ++ q, ?_⟩
    simp only [List.flatMap_cons]
    rw [DataPath.replayStage_append _ _ _ _ (replayStage_length _ _ _ hc), hc, ih]
    rfl

/-- **A stage edit from its chunks, paid lists existential.** -/
theorem splitPass_chunks_exists {check : WitnessRef → Cell → Bool} (s : Snapshot)
    (cs : List (List AddressedCell × List StageRow × List AddressedCell))
    (held : s.held = cs.flatMap Prod.fst)
    (h : ∀ c ∈ cs, ∃ paid, replayStage check c.1 c.2.1 = some ⟨paid, c.2.2⟩) :
    ∃ paid, (Edit.splitPass (cs.flatMap fun c => c.2.1)).run check s =
      some ⟨s.paid ++ paid, cs.flatMap fun c => c.2.2⟩ := by
  obtain ⟨paid, hr⟩ := replayStage_chunks_exists cs h
  exact ⟨paid, by simp [Edit.run, Snapshot.advance, held, hr]⟩

/-! #### Merges and clips on one chunk: frames

A merge or clip edit names the held list's prefix and suffix around the atoms it changes, so
on the whole list `mergeAt_run` and `clipAt_run` must reduce `s.held.drop i`. A frame keeps
the change local: the edit on `A ++ X ++ B`, with `A` and `B` prepended and appended to its
own prefix and suffix, runs exactly as the edit on `X`, with `A` and `B` carried by
`sameRoster_frame`. `framedEdits` strings the chunks of a held list together, each chunk's
merges and clips framed by the outputs before it and the inputs after it; `runEdits_framed`
runs them from per-chunk runs, so no chunk is read twice and no list is evaluated whole. -/

/-- Merge and clip edits: the ones a frame applies to. -/
def Edit.isLocal : Edit → Bool
  | .merge .. => true
  | .clip .. => true
  | _ => false

/-- The edit on `A ++ X ++ B` that acts on `X` as `e` does. -/
def frameEdit (A B : List AddressedCell) : Edit → Edit
  | .merge pre between suffix row => .merge (A ++ pre) between (suffix ++ B) row
  | .clip before after row => .clip (A ++ before) (after ++ B) row
  | e => e

theorem sameRoster_iff (a b : List AddressedCell) : sameRoster a b = true ↔ a = b :=
  ⟨sameRoster_exact a b, fun h => h ▸ DataPath.sameRoster_self a⟩

theorem sameRoster_frame (A L M B : List AddressedCell) :
    sameRoster (A ++ L ++ B) (A ++ M ++ B) = sameRoster L M := by
  apply Bool.eq_iff_iff.mpr
  rw [sameRoster_iff, sameRoster_iff, List.append_cancel_right_eq, List.append_cancel_left_eq]

/-- **One framed edit.** -/
theorem frame_run {check : WitnessRef → Cell → Bool} (A B : List AddressedCell) :
    ∀ (e : Edit), e.isLocal = true → ∀ (q X : List AddressedCell),
      (frameEdit A B e).run check ⟨q, A ++ X ++ B⟩ =
        (e.run check ⟨q, X⟩).map fun t => ⟨t.paid, A ++ t.held ++ B⟩
  | .merge pre between suffix row, _, q, X => by
      have e1 : A ++ pre ++ [row.low] ++ between ++ [row.high] ++ (suffix ++ B) =
          A ++ (pre ++ [row.low] ++ between ++ [row.high] ++ suffix) ++ B := by
        simp only [List.append_assoc]
      simp only [frameEdit, Edit.run, MergeRow.run]
      rw [e1, sameRoster_frame]
      simp [List.append_assoc]
  | .clip before after row, _, q, X => by
      have e1 : A ++ before ++ row.input :: (after ++ B) = A ++ (before ++ row.input :: after) ++ B := by
        simp
      simp only [frameEdit, Edit.run, Snapshot.applyClip]
      rw [e1, sameRoster_frame]
      by_cases hc : (sameRoster X (before ++ row.input :: after) && row.check check) = true
      · simp [hc, List.append_assoc]
      · simp [hc]
  | .splitPass _, h, _, _ => by simp [Edit.isLocal] at h
  | .updateOrder _, h, _, _ => by simp [Edit.isLocal] at h

/-- A merge or clip edit only appends to the paid list. -/
theorem local_run_shift {check : WitnessRef → Cell → Bool} :
    ∀ (e : Edit), e.isLocal = true → ∀ (q X : List AddressedCell),
      e.run check ⟨q, X⟩ = (e.run check ⟨[], X⟩).map fun t => ⟨q ++ t.paid, t.held⟩
  | .merge pre between suffix row, _, q, X => by
      simp only [Edit.run, MergeRow.run]
      simp
  | .clip before after row, _, q, X => by
      simp only [Edit.run, Snapshot.applyClip]
      by_cases hc : (sameRoster X (before ++ row.input :: after) && row.check check) = true
      · simp [hc]
      · simp [hc]
  | .splitPass _, h, _, _ => by simp [Edit.isLocal] at h
  | .updateOrder _, h, _, _ => by simp [Edit.isLocal] at h

/-- Merges and clips only append to the paid list. -/
theorem runEdits_shift {check : WitnessRef → Cell → Bool} :
    ∀ (es : List Edit), (∀ e ∈ es, e.isLocal = true) → ∀ (q X : List AddressedCell),
      runEdits check ⟨q, X⟩ es = (runEdits check ⟨[], X⟩ es).map fun t => ⟨q ++ t.paid, t.held⟩
  | [], _, q, X => by simp [runEdits]
  | e :: es, h, q, X => by
      have he := h e (by simp)
      have hes : ∀ f ∈ es, f.isLocal = true := fun f hf => h f (by simp [hf])
      simp only [runEdits, Option.bind_eq_bind]
      rw [local_run_shift e he q X]
      cases hr : e.run check ⟨[], X⟩ with
      | none => simp
      | some t =>
        simp only [Option.map_some, Option.bind_some]
        rw [runEdits_shift es hes (q ++ t.paid) t.held, runEdits_shift es hes t.paid t.held]
        cases runEdits check ⟨[], t.held⟩ es <;> simp [List.append_assoc]

/-- **A run of framed edits.** -/
theorem runEdits_frame {check : WitnessRef → Cell → Bool} (A B : List AddressedCell) :
    ∀ (es : List Edit), (∀ e ∈ es, e.isLocal = true) → ∀ (q X : List AddressedCell),
      runEdits check ⟨q, A ++ X ++ B⟩ (es.map (frameEdit A B)) =
        (runEdits check ⟨q, X⟩ es).map fun t => ⟨t.paid, A ++ t.held ++ B⟩
  | [], _, q, X => by simp [runEdits]
  | e :: es, h, q, X => by
      have he := h e (by simp)
      have hes : ∀ f ∈ es, f.isLocal = true := fun f hf => h f (by simp [hf])
      simp only [List.map_cons, runEdits, Option.bind_eq_bind]
      rw [frame_run A B e he q X]
      cases e.run check ⟨q, X⟩ with
      | none => simp
      | some t =>
        simp only [Option.map_some, Option.bind_some]
        exact runEdits_frame A B es hes t.paid t.held

/-- A chunk of merges and clips: its held atoms, its edits (local to the chunk), and the paid
list and atoms they leave when run from an empty paid list. -/
structure EditChunk where
  held : List AddressedCell
  edits : List Edit
  paid : List AddressedCell
  out : List AddressedCell

/-- The chunks' edits, each framed by the outputs of the chunks before it and the inputs of the
chunks after it. -/
def framedEdits : List AddressedCell → List EditChunk → List Edit
  | _, [] => []
  | A, c :: cs => c.edits.map (frameEdit A (cs.flatMap EditChunk.held)) ++ framedEdits (A ++ c.out) cs

/-- **Merges and clips from per-chunk runs.** -/
theorem runEdits_framed {check : WitnessRef → Cell → Bool} :
    ∀ (cs : List EditChunk) (A q : List AddressedCell), (∀ c ∈ cs, ∀ e ∈ c.edits, e.isLocal = true) →
      (∀ c ∈ cs, runEdits check ⟨[], c.held⟩ c.edits = some ⟨c.paid, c.out⟩) →
      runEdits check ⟨q, A ++ cs.flatMap EditChunk.held⟩ (framedEdits A cs) =
        some ⟨q ++ cs.flatMap EditChunk.paid, A ++ cs.flatMap EditChunk.out⟩
  | [], A, q, _, _ => by simp [framedEdits, runEdits]
  | c :: cs, A, q, hl, hr => by
      have hc := hl c (by simp)
      have run0 := hr c (by simp)
      have first : runEdits check ⟨q, A ++ c.held ++ cs.flatMap EditChunk.held⟩
          (c.edits.map (frameEdit A (cs.flatMap EditChunk.held))) =
          some ⟨q ++ c.paid, A ++ c.out ++ cs.flatMap EditChunk.held⟩ := by
        rw [runEdits_frame A _ c.edits hc q c.held, runEdits_shift c.edits hc q c.held, run0]
        rfl
      have rest := runEdits_framed cs (A ++ c.out) (q ++ c.paid)
        (fun d hd => hl d (by simp [hd])) (fun d hd => hr d (by simp [hd]))
      have e1 : A ++ (c :: cs).flatMap EditChunk.held = A ++ c.held ++ cs.flatMap EditChunk.held := by
        simp [List.append_assoc]
      rw [e1, framedEdits, runEdits_append_of first rest]
      simp [List.append_assoc]

/-- **A clip row from its geometry and its certificate's arithmetic.** The evaluator states
`check row.certificate.receipt row.certificate.source = true` on the certificate's own source
cell; the data path proves the geometry (`checkedSubtract`, `sameBoxes`, `sameCell`, the two
`insideCheck`s). -/
theorem ClipRow.check_of {check : WitnessRef → Cell → Bool} (row : ClipRow) {strips : List Cell} {paid : Cell}
    (sub : checkedSubtract row.input.cell row.window = some (strips, some paid))
    (geom : ((sameBoxes strips row.remainder && sameCell paid row.certificate.clip) &&
      insideCheck row.window (row.certificate.motion.image row.certificate.source)) = true)
    (inside : insideCheck row.certificate.clip (row.certificate.motion.image row.certificate.source) = true)
    (arith : check row.certificate.receipt row.certificate.source = true) :
    row.check check = true := by
  delta ClipRow.check
  rw [sub]
  simp only [geom, CertifiedClip.check, inside, arith, Bool.and_self]

/-- **Chunks after a rotation.** Rotating a chunked list by the total length of its leading
chunks rotates the chunks. Nothing is evaluated when the rotation amount is this length term
itself; equating it with a literal evaluates the leading chunks. -/
theorem rotate_chunks {α : Type} (cs : List (List α)) (k : ℕ) :
    cs.flatten.drop ((cs.take k).flatten.length) ++ cs.flatten.take ((cs.take k).flatten.length) =
      (cs.drop k).flatten ++ (cs.take k).flatten := by
  have e : cs.flatten = (cs.take k).flatten ++ (cs.drop k).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [e, List.drop_left, List.take_left]

/-- The positive selection of a held list given in chunks. -/
theorem selectPositive_chunks (s : Snapshot) (cs : List (List AddressedCell)) (held : s.held = cs.flatten) :
    s.selectPositive = ⟨s.paid, (cs.map fun c => c.filter fun a => decide (0 ≤ a.cell.lo 5)).flatten⟩ := by
  simp [Snapshot.selectPositive, held, List.filter_flatten]

/-- A chunk on the positive side is kept whole. -/
theorem filter_positive_self {c : List AddressedCell} (h : c.all (fun a => decide (0 ≤ a.cell.lo 5)) = true) :
    c.filter (fun a => decide (0 ≤ a.cell.lo 5)) = c :=
  List.filter_eq_self.mpr (by simpa using h)

/-- A chunk on the negative side is dropped whole. -/
theorem filter_positive_nil {c : List AddressedCell} (h : c.all (fun a => decide (a.cell.lo 5 < 0)) = true) :
    c.filter (fun a => decide (0 ≤ a.cell.lo 5)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro a ha
  have := List.all_eq_true.mp h a ha
  simp only [decide_eq_true_eq] at this
  simp [not_le.mpr this]

/-- A test over a list given in chunks, chunk by chunk. -/
theorem all_chunks {α : Type} (p : α → Bool) (cs : List (List α)) (h : ∀ c ∈ cs, c.all p = true) :
    cs.flatten.all p = true := by
  simp only [List.all_eq_true, List.mem_flatten] at h ⊢
  rintro x ⟨c, hc, hx⟩
  exact h c hc x hx

/-- Relabel checks over appended lists. -/
theorem relabelCheck_append :
    ∀ (a₁ b₁ a₂ b₂ : List AddressedCell), relabelCheck a₁ b₁ = true → relabelCheck a₂ b₂ = true →
      relabelCheck (a₁ ++ a₂) (b₁ ++ b₂) = true
  | [], [], _, _, _, h => by simpa using h
  | [], _ :: _, _, _, h, _ => by simp [relabelCheck] at h
  | _ :: _, [], _, _, h, _ => by simp [relabelCheck] at h
  | x :: xs, y :: ys, a₂, b₂, h₁, h₂ => by
      simp only [relabelCheck, Bool.and_eq_true] at h₁
      simp only [List.cons_append, relabelCheck, Bool.and_eq_true]
      exact ⟨h₁.1, relabelCheck_append xs ys a₂ b₂ h₁.2 h₂⟩

/-- `mapM` in `Option` over a list given in chunks. -/
theorem mapM_chunks {α β : Type} (f : α → Option β) :
    ∀ cs : List (List α × List β), (∀ c ∈ cs, c.1.mapM f = some c.2) →
      (cs.flatMap Prod.fst).mapM f = some (cs.flatMap Prod.snd)
  | [], _ => by simp
  | c :: cs, h => by
      simp only [List.flatMap_cons, List.mapM_append, h c (by simp),
        mapM_chunks f cs (fun d hd => h d (by simp [hd]))]
      rfl

/-- A chunk of the Stage5b binding: held atoms, the roster owners covering them, and the atoms
those owners decode to (one list per owner). -/
structure BindChunk where
  held : List AddressedCell
  owners : List RosterOwner
  atoms : List (List Atom)

/-- **The Stage5b binding from its chunks.** -/
theorem bindStage5b_chunks (s : Snapshot) (cs : List BindChunk) (held : s.held = cs.flatMap BindChunk.held)
    (decode : ∀ c ∈ cs, c.owners.mapM RosterOwner.atoms = some c.atoms)
    (relabel : ∀ c ∈ cs, relabelCheck c.held (c.atoms.flatten.map Atom.asCell) = true) :
    bindStage5b s (cs.flatMap BindChunk.owners) = some (cs.flatMap BindChunk.atoms).flatten := by
  have hm := mapM_chunks RosterOwner.atoms (cs.map fun c => (c.owners, c.atoms)) (by simpa using decode)
  simp only [List.flatMap_map] at hm
  have hr : ∀ ds : List BindChunk, (∀ c ∈ ds, relabelCheck c.held (c.atoms.flatten.map Atom.asCell) = true) →
      relabelCheck (ds.flatMap BindChunk.held) ((ds.flatMap BindChunk.atoms).flatten.map Atom.asCell) = true := by
    intro ds
    induction ds with
    | nil => intro _; rfl
    | cons d ds ih =>
      intro h
      simp only [List.flatMap_cons, List.flatten_append, List.map_append]
      exact relabelCheck_append _ _ _ _ (h d (by simp)) (ih fun e he => h e (by simp [he]))
  simp [bindStage5b, hm, held]
  simpa using hr cs relabel

/-! ### The mirror: two routes

`mirror` keeps, for each positive atom, its positive-width clips with every reflected atom
(`MirrorClips`): all pairs. The intended route is `mirror_chunks` (below): clips chunk by
chunk, far chunks dropped by a bounding-box test, no index. The alternative here,
`mirror_candidates`, reads the clips of each positive atom from a list of candidate indices
into the one reflected roster, given that every other index meets the atom with no positive
width (`off`); `off_of_buckets` gives `off` from a bucket function with `BucketSound`, a
directory listing under each bucket every reflected atom in it (`complete`), and candidate
lists containing the directory's entries for each bucket of their atom (`covers`). As it
stands it is not efficient: kernel list indexing is linear in the index, and every
reflected atom sharing a bucket with a positive atom is a candidate, so every such pair is
evaluated; it would need chunk-local indices. `gridBins` (one axis) and `prodBuckets`
(several) are sound bucket functions. -/

/-- The clip of a positive atom with a reflected one, when it has positive width. -/
def clipOf (key : Key → Key → Key) (a b : AddressedCell) : Option AddressedCell :=
  if positiveCell (intersection a.cell b.cell) then some ⟨key a.key b.key, intersection a.cell b.cell⟩
  else none

theorem MirrorClips_eq (key : Key → Key → Key) (pos opp : List AddressedCell) :
    MirrorClips key pos opp = pos.flatMap fun a => opp.filterMap (clipOf key a) := rfl

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
      have ih : l.flatMap f = l.flatMap g := flatMap_congr' (l := l) fun a ha => h a (List.mem_cons_of_mem _ ha)
      rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih]

/-- `filterMap` over a list equals `filterMap` over a sublist when the dropped elements give
`none`. -/
theorem filterMap_eq_of_sublist {α β : Type} (g : α → Option β) {idx L : List α} (sub : idx.Sublist L)
    (nd : L.Nodup) (off : ∀ x ∈ L, x ∉ idx → g x = none) : L.filterMap g = idx.filterMap g := by
  induction sub with
  | slnil => rfl
  | cons a s ih =>
    have nd' := List.nodup_cons.mp nd
    have ha : g a = none := off a (by simp) fun h => nd'.1 (s.subset h)
    rw [List.filterMap_cons_none ha]
    exact ih nd'.2 fun x hx hn => off x (by simp [hx]) hn
  | cons_cons a s ih =>
    have nd' := List.nodup_cons.mp nd
    have e := ih nd'.2 fun x hx hn => off x (by simp [hx]) (by
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => nd'.1 (h ▸ hx), hn⟩)
    cases h : g a <;> simp [h, e]

/-- `filterMap` over a list by its indices. -/
theorem filterMap_indices {β γ : Type} (f : β → Option γ) :
    ∀ l : List β, l.filterMap f = (List.range l.length).filterMap fun j => l[j]?.bind f
  | [] => rfl
  | b :: l => by
      have tail : (List.map Nat.succ (List.range l.length)).filterMap (fun j => (b :: l)[j]?.bind f) =
          l.filterMap f := by
        rw [List.filterMap_map, filterMap_indices f l]
        congr 1
      rw [List.length_cons, List.range_succ_eq_map]
      cases hb : f b with
      | none => simp [hb, tail]
      | some y => simp [hb, tail]

/-- A list of naturals in strictly increasing order (one comparison per entry). -/
def increasing : List ℕ → Bool
  | a :: b :: l => decide (a < b) && increasing (b :: l)
  | _ => true

theorem increasing_pairwise : ∀ l : List ℕ, increasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
      simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := increasing_pairwise (b :: l) h.2
      refine List.pairwise_cons.mpr ⟨fun c hc => ?_, ih⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- A strictly increasing list of indices in `[m, m + k)` is a sublist of `List.range' m k`. -/
theorem sublist_range' : ∀ (k m : ℕ) (idx : List ℕ), idx.Pairwise (· < ·) →
    (∀ j ∈ idx, m ≤ j ∧ j < m + k) → idx.Sublist (List.range' m k)
  | 0, _, [], _, _ => List.Sublist.slnil
  | 0, m, j :: _, _, h => by
      have := h j (by simp)
      omega
  | k + 1, _, [], _, _ => List.nil_sublist _
  | k + 1, m, j :: idx, inc, h => by
      rw [List.range'_succ]
      have rest := List.pairwise_cons.mp inc
      have hj := h j (by simp)
      by_cases e : j = m
      · subst e
        exact (sublist_range' k (j + 1) idx rest.2 fun i hi => by
          have := rest.1 i hi
          have := h i (by simp [hi])
          omega).cons_cons j
      · exact (sublist_range' k (m + 1) (j :: idx) inc fun i hi => by
          rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · have := rest.1 i hi
            have := h i (by simp [hi])
            omega).cons m

/-- A strictly increasing list of indices below `n` is a sublist of `List.range n`. -/
theorem sublist_range {idx : List ℕ} {n : ℕ} (inc : idx.Pairwise (· < ·)) (lt : ∀ j ∈ idx, j < n) :
    idx.Sublist (List.range n) := by
  rw [List.range_eq_range']
  exact sublist_range' n 0 idx inc fun j hj => ⟨Nat.zero_le _, by simpa using lt j hj⟩

/-- **The mirror from candidate lists.** If the mirror's admissibility tests pass, and the
candidate indices of each positive atom are increasing, in range, and include every
reflected atom meeting it with positive width, the mirror's clips are read from the
candidates alone. -/
theorem mirror_candidates (key : Key → Key → Key) (old positive : Snapshot) (cand : AddressedCell → List ℕ)
    (admissible : ((halvesCheck old &&
        positive.held.all (fun a => positiveCell a.cell && decide (0 ≤ a.cell.lo 5))) &&
      (reflectedRoster (nonpositive old.held)).all fun a => positiveCell a.cell) = true)
    (inc : ∀ a ∈ positive.held, increasing (cand a) = true)
    (bound : ∀ a ∈ positive.held, ∀ j ∈ cand a, j < (reflectedRoster (nonpositive old.held)).length)
    (off : ∀ a ∈ positive.held, ∀ (j : ℕ) (hj : j < (reflectedRoster (nonpositive old.held)).length),
      j ∉ cand a → positiveCell (intersection a.cell (reflectedRoster (nonpositive old.held))[j].cell) = false) :
    mirror key old positive = some ⟨positive.paid ++ reflectedRoster old.paid,
      positive.held.flatMap fun a => (cand a).filterMap fun j =>
        (reflectedRoster (nonpositive old.held))[j]?.bind (clipOf key a)⟩ := by
  have hclips : MirrorClips key positive.held (reflectedRoster (nonpositive old.held)) =
      positive.held.flatMap fun a => (cand a).filterMap fun j =>
        (reflectedRoster (nonpositive old.held))[j]?.bind (clipOf key a) := by
    rw [MirrorClips_eq]
    apply flatMap_congr'
    intro a ha
    rw [filterMap_indices]
    apply filterMap_eq_of_sublist
    · exact sublist_range (increasing_pairwise _ (inc a ha)) (bound a ha)
    · exact List.nodup_range
    · intro j hj hn
      have hj' := List.mem_range.mp hj
      simp [List.getElem?_eq_getElem hj', clipOf, off a ha j hj' hn]
  unfold mirror
  simp only [admissible, ↓reduceIte, hclips]

/-! #### The mirror over chunked rosters, with bounding boxes

`mirror_candidates` indexes one global reflected roster, and kernel list indexing is linear,
so its cost grows with the roster's length per candidate. `mirror_chunks` needs no index: with
the old held list given in chunks, each positive atom's clips are its clips with each chunk's
reflected atoms, chunk by chunk. A chunk whose cells lie in a box that meets the positive
atom's box with no positive width contributes nothing (`filterMap_clip_far`), and
`flatten_map_filter` drops such chunks by one box test each, so only the near chunks' pairs
are evaluated. -/

/-- Positive-width meeting is monotone in both cells. -/
theorem positiveCell_mono2 {a b A B : Cell} (ha : insideCheck a A = true) (hb : insideCheck b B = true)
    (h : positiveCell (intersection a b) = true) : positiveCell (intersection A B) = true := by
  have ha' : ∀ i, A.lo i ≤ a.lo i ∧ a.hi i ≤ A.hi i := of_decide_eq_true ha
  have hb' : ∀ i, B.lo i ≤ b.lo i ∧ b.hi i ≤ B.hi i := of_decide_eq_true hb
  have h' : ∀ i, (intersection a b).lo i < (intersection a b).hi i := of_decide_eq_true h
  refine decide_eq_true fun i => ?_
  have hi : max (a.lo i) (b.lo i) < min (a.hi i) (b.hi i) := h' i
  show max (A.lo i) (B.lo i) < min (A.hi i) (B.hi i)
  calc max (A.lo i) (B.lo i) ≤ max (a.lo i) (b.lo i) := max_le_max (ha' i).1 (hb' i).1
    _ < min (a.hi i) (b.hi i) := hi
    _ ≤ min (A.hi i) (B.hi i) := min_le_min (ha' i).2 (hb' i).2

/-- **The mirror over a chunked roster.** -/
theorem mirror_chunks (key : Key → Key → Key) (old positive : Snapshot) (chunks : List (List AddressedCell))
    (held : old.held = chunks.flatten)
    (admissible : ((halvesCheck old &&
        positive.held.all (fun a => positiveCell a.cell && decide (0 ≤ a.cell.lo 5))) &&
      (reflectedRoster (nonpositive old.held)).all fun a => positiveCell a.cell) = true) :
    mirror key old positive = some ⟨positive.paid ++ reflectedRoster old.paid,
      positive.held.flatMap fun a =>
        (chunks.map fun ch => (reflectedRoster (nonpositive ch)).filterMap (clipOf key a)).flatten⟩ := by
  have e : ∀ a : AddressedCell, (reflectedRoster (nonpositive old.held)).filterMap (clipOf key a) =
      (chunks.map fun ch => (reflectedRoster (nonpositive ch)).filterMap (clipOf key a)).flatten := by
    intro a
    simp only [held, nonpositive, reflectedRoster, List.filter_flatten, List.map_flatten,
      List.filterMap_flatten, List.map_map, Function.comp_def]
  unfold mirror
  simp only [admissible, ↓reduceIte, MirrorClips_eq, e]

/-- A chunk whose cells lie in a box `B` that meets the box `A` of the positive atom with no
positive width gives no clip. -/
theorem filterMap_clip_far (key : Key → Key → Key) {a : AddressedCell} {ch : List AddressedCell} {A B : Cell}
    (ina : insideCheck a.cell A = true) (inb : ∀ b ∈ ch, insideCheck b.cell B = true)
    (far : positiveCell (intersection A B) = false) : ch.filterMap (clipOf key a) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro b hb
  simp only [clipOf]
  cases h : positiveCell (intersection a.cell b.cell) with
  | false => rfl
  | true => exact absurd (positiveCell_mono2 ina (inb b hb) h) (by simp [far])

/-- Dropping the chunks that contribute nothing, by a test on each chunk. -/
theorem flatten_map_filter {α β : Type} (near : α → Bool) (g : α → List β) :
    ∀ l : List α, (∀ x ∈ l, near x = false → g x = []) → (l.map g).flatten = ((l.filter near).map g).flatten
  | [], _ => rfl
  | x :: l, h => by
      have ih := flatten_map_filter near g l fun y hy => h y (by simp [hy])
      cases hx : near x
      · simp [hx, h x (by simp) hx, ih]
      · simp [hx, ih]

/-- A bucket function on cells: two cells whose intersection has positive width share a
bucket. -/
def BucketSound {β : Type} (bk : Cell → List β) : Prop :=
  ∀ x y : Cell, positiveCell (intersection x y) = true → ∃ k ∈ bk x, k ∈ bk y

/-- **Candidate lists are complete by buckets.** A directory that lists, under each bucket,
every reflected atom in it, and candidates that contain the directory's entries for each
bucket of their atom, leave out only reflected atoms that meet the atom with no positive
width. -/
theorem off_of_buckets {β : Type} {bk : Cell → List β} (sound : BucketSound bk) (opp : List AddressedCell)
    (dir : β → List ℕ) (complete : ∀ (j : ℕ) (hj : j < opp.length), ∀ k ∈ bk opp[j].cell, j ∈ dir k)
    (a : AddressedCell) (cand : List ℕ) (covers : ∀ k ∈ bk a.cell, ∀ j ∈ dir k, j ∈ cand) :
    ∀ (j : ℕ) (hj : j < opp.length), j ∉ cand → positiveCell (intersection a.cell opp[j].cell) = false := by
  intro j hj hn
  cases h : positiveCell (intersection a.cell opp[j].cell) with
  | false => rfl
  | true =>
    obtain ⟨k, ka, kb⟩ := sound _ _ h
    exact absurd (covers k ka j (complete j hj k kb)) hn

/-- The bins of a grid on axis `i` that a cell's open interval meets: bin `k < n` is
`(r + w k, r + w (k + 1))`, the first and last bins unbounded. -/
def gridBins (i : Axis) (r w : ℚ) (n : ℕ) (c : Cell) : List ℕ :=
  (List.range n).filter fun k => decide ((k = 0 ∨ r + w * k < c.hi i) ∧ (k + 1 = n ∨ c.lo i < r + w * (k + 1)))

/-- Every rational lies in a grid bin. -/
theorem grid_bin (r w : ℚ) (n : ℕ) (hw : 0 < w) (hn : 0 < n) (m : ℚ) :
    ∃ k < n, (k = 0 ∨ r + w * k ≤ m) ∧ (k + 1 = n ∨ m < r + w * (k + 1)) := by
  by_cases hneg : m < r
  · refine ⟨0, hn, Or.inl rfl, ?_⟩
    rcases Nat.lt_or_ge 1 n with h | h
    · right
      push_cast
      linarith
    · left
      omega
  · rw [not_lt] at hneg
    have f0 : 0 ≤ ⌊(m - r) / w⌋ := Int.floor_nonneg.mpr (div_nonneg (by linarith) hw.le)
    have fle : (⌊(m - r) / w⌋ : ℚ) ≤ (m - r) / w := Int.floor_le _
    have flt : (m - r) / w < ⌊(m - r) / w⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hw] at fle
    rw [div_lt_iff₀ hw] at flt
    have hc : ((⌊(m - r) / w⌋.toNat : ℕ) : ℚ) = ⌊(m - r) / w⌋ := by
      exact_mod_cast Int.toNat_of_nonneg f0
    have hz : ((⌊(m - r) / w⌋.toNat : ℕ) : ℤ) = ⌊(m - r) / w⌋ := Int.toNat_of_nonneg f0
    by_cases big : n ≤ ⌊(m - r) / w⌋.toNat + 1
    · refine ⟨n - 1, by omega, Or.inr ?_, Or.inl (by omega)⟩
      have h1 : ((n - 1 : ℕ) : ℚ) ≤ ⌊(m - r) / w⌋ := by
        rw [← hc]
        exact_mod_cast (by omega : n - 1 ≤ ⌊(m - r) / w⌋.toNat)
      nlinarith
    · refine ⟨⌊(m - r) / w⌋.toNat, by omega, Or.inr ?_, Or.inr ?_⟩
      · rw [hc]
        linarith
      · rw [hc]
        linarith

/-- **A grid on one axis is a sound bucket function.** -/
theorem gridBins_sound (i : Axis) (r w : ℚ) (n : ℕ) (hw : 0 < w) (hn : 0 < n) :
    BucketSound (gridBins i r w n) := by
  intro x y hxy
  have hpos : ∀ j, (intersection x y).lo j < (intersection x y).hi j := of_decide_eq_true hxy
  have hi : max (x.lo i) (y.lo i) < min (x.hi i) (y.hi i) := hpos i
  obtain ⟨k, hk, lower, upper⟩ := grid_bin r w n hw hn (max (x.lo i) (y.lo i))
  have mem : ∀ c : Cell, c.lo i ≤ max (x.lo i) (y.lo i) → max (x.lo i) (y.lo i) < c.hi i →
      k ∈ gridBins i r w n c := by
    intro c hl hh
    simp only [gridBins, List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨hk, ?_, ?_⟩
    · rcases lower with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_lt h hh)
    · rcases upper with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_lt hl h)
  exact ⟨k, mem x (le_max_left _ _) (lt_of_lt_of_le hi (min_le_left _ _)),
    mem y (le_max_right _ _) (lt_of_lt_of_le hi (min_le_right _ _))⟩

/-- For `w ≤ 0` the grid is sound too: two overlapping cells share the last or the first bin.
-/
theorem gridBins_sound_nonpos (i : Axis) (r w : ℚ) (n : ℕ) (hw : w ≤ 0) (hn : 0 < n) :
    BucketSound (gridBins i r w n) := by
  intro x y hxy
  have hpos : ∀ j, (intersection x y).lo j < (intersection x y).hi j := of_decide_eq_true hxy
  have hi : max (x.lo i) (y.lo i) < min (x.hi i) (y.hi i) := hpos i
  have mem : ∀ k, k < n → (∀ c : Cell, c.lo i ≤ max (x.lo i) (y.lo i) →
      min (x.hi i) (y.hi i) ≤ c.hi i →
      (k = 0 ∨ r + w * k < c.hi i) ∧ (k + 1 = n ∨ c.lo i < r + w * (k + 1))) →
      k ∈ gridBins i r w n x ∧ k ∈ gridBins i r w n y := by
    intro k hk h
    simp only [gridBins, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨⟨hk, h x (le_max_left _ _) (min_le_left _ _)⟩,
      ⟨hk, h y (le_max_right _ _) (min_le_right _ _)⟩⟩
  by_cases top : r + w * ((n - 1 : ℕ) : ℚ) < min (x.hi i) (y.hi i)
  · obtain ⟨hx, hy⟩ := mem (n - 1) (by omega) fun c _ hc =>
      ⟨Or.inr (lt_of_lt_of_le top hc), Or.inl (by omega)⟩
    exact ⟨n - 1, hx, hy⟩
  · rw [not_lt] at top
    obtain ⟨hx, hy⟩ := mem 0 hn fun c hc _ => by
      refine ⟨Or.inl rfl, ?_⟩
      rcases Nat.lt_or_ge 1 n with h | h
      · right
        have h1 : (1 : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ n - 1)
        have h2 : w * ((n - 1 : ℕ) : ℚ) ≤ w * 1 := mul_le_mul_of_nonpos_left h1 hw
        simp only [Nat.cast_zero, zero_add]
        linarith
      · left
        omega
    exact ⟨0, hx, hy⟩

/-- **A grid on one axis is a sound bucket function for every width**: only `0 < n` is
needed. -/
theorem gridBins_sound_any (i : Axis) (r w : ℚ) (n : ℕ) (hn : 0 < n) : BucketSound (gridBins i r w n) := by
  rcases lt_or_ge 0 w with hw | hw
  · exact gridBins_sound i r w n hw hn
  · exact gridBins_sound_nonpos i r w n hw hn

/-- The product of bucket functions: a bucket is one bucket of each. -/
def prodBuckets {β : Type} (bks : List (Cell → List β)) (c : Cell) : List (List β) :=
  (bks.map fun bk => bk c).sections

/-- **A product of sound bucket functions is sound.** -/
theorem prodBuckets_sound {β : Type} :
    ∀ bks : List (Cell → List β), (∀ bk ∈ bks, BucketSound bk) → BucketSound (prodBuckets bks)
  | [], _ => fun x y _ => ⟨[], by simp [prodBuckets, List.sections], by simp [prodBuckets, List.sections]⟩
  | bk :: bks, h => fun x y hxy => by
      obtain ⟨k, hkx, hky⟩ := h bk (by simp) x y hxy
      obtain ⟨s, hsx, hsy⟩ := prodBuckets_sound bks (fun b hb => h b (by simp [hb])) x y hxy
      simp only [prodBuckets, List.mem_sections] at hsx hsy
      refine ⟨k :: s, ?_, ?_⟩
      · simp only [prodBuckets, List.map_cons, List.mem_sections]
        exact List.Forall₂.cons hkx hsx
      · simp only [prodBuckets, List.map_cons, List.mem_sections]
        exact List.Forall₂.cons hky hsy

/-- An option known to be `some` is `some` of its value: how a chunk's decoded roster atoms
are discharged (`BindChunk.atoms := (owners.mapM RosterOwner.atoms).getD []`, with `isSome`
by `decide +kernel`, since `Atom` has no decidable equality). -/
theorem eq_some_getD_of_isSome {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o <;> simp_all

end EarlyReplay

/-- **The Stage5b binding's output is the late chunks' input** when each late chunk's Stage5b slice
is its binding chunk's atoms. -/
theorem bind_late_glue (bcs : List EarlyReplay.BindChunk) (f : EarlyReplay.BindChunk → LateChunk)
    (hf : ∀ c, (f c).stage5b = c.atoms.flatten) :
    (bcs.flatMap EarlyReplay.BindChunk.atoms).flatten = (bcs.map f).flatMap LateChunk.stage5b := by
  induction bcs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.flatten_append, ih, List.map_cons, List.flatMap_cons, hf]

/-! ### Lifting per-family results to the prefix check -/

namespace OverlayCorpus
open OverlayPlanar.Fix

theorem orCheck_of_left {a b : WitnessRef → Cell → Bool} {w : WitnessRef} {c : Cell} (h : a w c = true) :
    orCheck a b w c = true := by
  simp [orCheck, h]

theorem orCheck_of_right {a b : WitnessRef → Cell → Bool} {w : WitnessRef} {c : Cell} (h : b w c = true) :
    orCheck a b w c = true := by
  simp [orCheck, h]

/-- **A `later` result is a prefix-check result** off the two Overlay banks. Evaluator modules
state `later w b = true` for their own check (or a component of an `orCheck`), and this
lemma lifts it. -/
theorem corpusCheck_of_later (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later : WitnessRef → Cell → Bool} {w : WitnessRef} {b : Cell}
    (other : isOverlayBank w.source = false) (h : later w b = true) :
    corpusCheck geometric direct sidecar bulk later w b = true := by
  rw [corpusCheck_of_not_overlay geometric direct sidecar bulk later other, h, Bool.or_true]

end OverlayCorpus

end BccSharp.Coulomb.CompactCover

namespace BccSharp.Coulomb
open CompactCover CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus

/-- **the two-site theorem from a chunked late replay.** `assemble_from_overlay_corpus` with the Stage6 binding and
the late corpus given chunk by chunk (`late_chunks`): the prefix must end in the chunks' Stage5b
slices, in order. -/
theorem assemble_from_late_chunks (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later : WitnessRef → Cell → Bool} (laterSound : SoundCheck later)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early) (sLate : CheckerSound late)
    (pre : CorpusPrefix) (cs : List LateChunk)
    (rStage5b : pre.run (corpusCheck geometric direct sidecar bulk later) = some (cs.flatMap LateChunk.stage5b))
    (hStage6 : ∀ c ∈ cs, runRows (runStage6 early) c.stage5b c.rows = some c.stage6)
    (hcorp : ∀ c ∈ cs, c.corp.run late c.stage6 = some []) : Statement :=
  assemble_from_overlay_corpus geometric direct sidecar bulk laterSound sEarly sLate pre _ _ rStage5b _ _
    (late_chunks cs hStage6 hcorp).1 (late_chunks cs hStage6 hcorp).2

end BccSharp.Coulomb
