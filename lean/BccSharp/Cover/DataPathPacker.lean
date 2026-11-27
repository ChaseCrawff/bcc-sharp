import BccSharp.Cover.DataPath

set_option autoImplicit false

/-! The batch packer: sparse stage events as checked `Edit`s.

A prefix stage changes few of the held atoms. The edits here are built from the held list
itself, so the kernel never compares an unchanged atom with a row, and their run theorems
are generic: the only hypotheses are the arithmetic at the changed atoms.

* **Masked passes** (`maskRows`, `maskOut`, `maskHits`). A `splitPass` edit whose row at the
  `j`-th held atom is `⟨a, mk a⟩` when bit `j` of the mask is set and the pass-through row
  `passRow a` otherwise. Its input matches the atom by construction, so `replayStage`
  needs only that each chosen plan runs (`replayStage_maskRows`); the held list afterwards
  is `maskOut`, each chosen atom replaced in place by its plan's held cells.
* **Segments** (`segRows`, `segOut`, `splitPass_segRows`). A held list cut into segments,
  one mask per segment; the edit is the concatenation of the segments' rows, and runs
  segment by segment (`replayStage_append`). The Direct root's shards are the segments of the
  early prefix.
* **Exact closes** (`closeMk`). A row that is a pay node on the
  atom's own cell with the atom's key. It runs when the check accepts the witness on the
  cell (`closeMk_run`), and a pass of closes keeps a sublist of the held list
  (`maskOut_closeMk_sublist`), so distinct keys stay distinct. An atom whose key no chosen
  atom carries passes through (`mem_maskOut_of_key`).
* **Rotation** (`rotation`, `rotation_run`). An `updateOrder` edit that moves the first `n`
  held atoms to the end. Both index lists are terms, not literals, and `Reorder.run`
  succeeds by a generic proof (`indicesCheck_of_get`), so the order into Adaptive costs no kernel
  evaluation.
* **Position maps** (`mergeAt`, `mergeAt_run`, `MergeRow.check_descend`). A coalescing edit
  at positions `i < j`: the prefix, the atoms between and the suffix are `take`/`drop` of
  the held list, so `sameRoster` holds by a generic proof; when the cells are
  `descend b (w ++ [2a])`, `descend b (w ++ [2a+1])` and `descend b w`, the merge check
  holds too, with no evaluation. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay OverlayPlanar OverlayCorpus

namespace DataPath

/-! ### Masked passes -/

/-- The rows of a masked `splitPass`: bit `j` of `m` chooses the plan `mk a` at the `j`-th
atom; every other atom gets its pass-through row. -/
def maskRows (mk : AddressedCell → Plan) : List AddressedCell → ℕ → List StageRow
  | [], _ => []
  | a :: rest, m => (if m % 2 = 1 then ⟨a, mk a⟩ else passRow a) :: maskRows mk rest (m / 2)

/-- The held list after a masked pass. -/
def maskOut (mk : AddressedCell → Plan) : List AddressedCell → ℕ → List AddressedCell
  | [], _ => []
  | a :: rest, m => (if m % 2 = 1 then (mk a).holds a.cell else [a]) ++ maskOut mk rest (m / 2)

/-- The atoms a mask chooses. -/
def maskHits : List AddressedCell → ℕ → List AddressedCell
  | [], _ => []
  | a :: rest, m => (if m % 2 = 1 then [a] else []) ++ maskHits rest (m / 2)

theorem maskRows_length (mk : AddressedCell → Plan) :
    ∀ (held : List AddressedCell) (m : ℕ), (maskRows mk held m).length = held.length
  | [], _ => rfl
  | _ :: rest, m => by simp only [maskRows, List.length_cons, maskRows_length mk rest]

/-- **Masked pass.** If the plan chosen at every masked atom runs on its cell, the masked
rows replay on the held list and hold `maskOut`. -/
theorem replayStage_maskRows {check : WitnessRef → Cell → Bool} {mk : AddressedCell → Plan} :
    ∀ (held : List AddressedCell) (m : ℕ), (∀ a ∈ maskHits held m, ∃ s, (mk a).run check a.cell = some s) →
      ∃ paid, replayStage check held (maskRows mk held m) = some ⟨paid, maskOut mk held m⟩
  | [], _, _ => ⟨[], rfl⟩
  | a :: rest, m, h => by
    have hrest : ∀ x ∈ maskHits rest (m / 2), ∃ s, (mk x).run check x.cell = some s :=
      fun x hx => h x (by simp only [maskHits]; exact List.mem_append_right _ hx)
    obtain ⟨paid, hr⟩ := replayStage_maskRows rest (m / 2) hrest
    by_cases bit : m % 2 = 1
    · obtain ⟨s, hs⟩ := h a (by simp [maskHits, bit])
      have held := Plan.run_held (mk a) a.cell s hs
      refine ⟨s.paid ++ paid, ?_⟩
      simp only [maskRows, maskOut, bit, ite_true]
      rw [replayStage, ite_eq_left (sameAddressedCell_self a)]
      simp only [hs, hr, Option.bind_eq_bind, Option.bind_some]
      rw [← held]
      rfl
    · refine ⟨[] ++ paid, ?_⟩
      have g : sameAddressedCell a (passRow a).input = true := sameAddressedCell_self a
      simp only [maskRows, maskOut, bit, ite_false]
      rw [replayStage, ite_eq_left g, passRow_run, hr]
      rfl

/-! ### Segments -/

theorem replayStage_append {check : WitnessRef → Cell → Bool} :
    ∀ (xs ys : List AddressedCell) (rs ss : List StageRow), xs.length = rs.length →
      replayStage check (xs ++ ys) (rs ++ ss) =
        (replayStage check xs rs).bind fun a => (replayStage check ys ss).map fun b => a.join b
  | [], ys, [], ss, _ => by
    cases h : replayStage check ys ss <;>
      simp [replayStage, h, Snapshot.join, Snapshot.empty]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | x :: xs, ys, r :: rs, ss, h => by
    have hl : xs.length = rs.length := by simpa using h
    simp only [List.cons_append, replayStage]
    by_cases g : sameAddressedCell x r.input = true
    · rw [ite_eq_left g, ite_eq_left g, replayStage_append xs ys rs ss hl]
      cases e1 : r.plan.run check x.cell with
      | none => simp
      | some f =>
        cases e2 : replayStage check xs rs with
        | none => simp
        | some t =>
          cases e3 : replayStage check ys ss with
          | none => simp
          | some u =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some]
            simp [Snapshot.join, List.append_assoc]
    · rw [ite_eq_right g, ite_eq_right g]
      rfl

/-- The rows of a stage over a held list cut in segments, one mask per segment. -/
def segRows (mk : AddressedCell → Plan) (segs : List (List AddressedCell × ℕ)) : List StageRow :=
  segs.flatMap fun x => maskRows mk x.1 x.2

/-- The segments after that stage. -/
def segOut (mk : AddressedCell → Plan) (segs : List (List AddressedCell × ℕ)) : List (List AddressedCell) :=
  segs.map fun x => maskOut mk x.1 x.2

theorem replayStage_segRows {check : WitnessRef → Cell → Bool} {mk : AddressedCell → Plan} :
    ∀ segs : List (List AddressedCell × ℕ),
      (∀ x ∈ segs, ∀ a ∈ maskHits x.1 x.2, ∃ s, (mk a).run check a.cell = some s) →
      ∃ paid, replayStage check (segs.map Prod.fst).flatten (segRows mk segs) = some ⟨paid, (segOut mk segs).flatten⟩
  | [], _ => ⟨[], rfl⟩
  | x :: rest, h => by
    obtain ⟨p1, h1⟩ := replayStage_maskRows x.1 x.2 (h x List.mem_cons_self)
    obtain ⟨p2, h2⟩ := replayStage_segRows rest fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨p1 ++ p2, ?_⟩
    simp only [segRows, segOut, List.map_cons, List.flatten_cons, List.flatMap_cons] at h2 ⊢
    rw [replayStage_append _ _ _ _ (maskRows_length mk x.1 x.2).symm, h1]
    simp only [Option.bind_some, h2, Option.map_some]
    rfl

/-- **Segmented pass.** A snapshot whose held list is the segments in order: the edit of
their masked rows runs and holds the segments' outputs in order. -/
theorem splitPass_segRows {check : WitnessRef → Cell → Bool} {mk : AddressedCell → Plan}
    (s : Snapshot) (segs : List (List AddressedCell × ℕ)) (held : s.held = (segs.map Prod.fst).flatten)
    (h : ∀ x ∈ segs, ∀ a ∈ maskHits x.1 x.2, ∃ r, (mk a).run check a.cell = some r) :
    ∃ paid, (Edit.splitPass (segRows mk segs)).run check s = some ⟨s.paid ++ paid, (segOut mk segs).flatten⟩ := by
  obtain ⟨paid, hr⟩ := replayStage_segRows segs h
  exact ⟨paid, by simp [Edit.run, Snapshot.advance, held, hr]⟩

/-! ### Exact closes -/

/-- The row plan of an exact close: pay the atom's own cell with the witness of its key. -/
def closeMk (w : Key → WitnessRef) (a : AddressedCell) : Plan :=
  .pay a.key ⟨w a.key, a.cell, identityMotion, a.cell⟩

theorem closeMk_run {check : WitnessRef → Cell → Bool} (w : Key → WitnessRef) (a : AddressedCell)
    (h : check (w a.key) a.cell = true) :
    (closeMk w a).run check a.cell = some ⟨[⟨a.key, a.cell⟩], []⟩ := by
  have c : (sameCell a.cell a.cell && CertifiedClip.check ⟨w a.key, a.cell, identityMotion, a.cell⟩ check) = true := by
    simp only [sameCell_self, CertifiedClip.check, insideCheck_identity, Bool.true_and]
    exact h
  simp only [closeMk, Plan.run, c, ite_true]

theorem maskOut_closeMk_sublist (w : Key → WitnessRef) :
    ∀ (held : List AddressedCell) (m : ℕ), (maskOut (closeMk w) held m).Sublist held
  | [], _ => List.Sublist.slnil
  | a :: rest, m => by
    have ih := maskOut_closeMk_sublist w rest (m / 2)
    by_cases bit : m % 2 = 1
    · simp only [maskOut, bit, ite_true, closeMk, Plan.holds, List.nil_append]
      exact ih.cons a
    · simp only [maskOut, bit, ite_false, List.singleton_append]
      exact ih.cons_cons a

/-- An atom whose key no masked atom carries passes the masked pass. -/
theorem mem_maskOut_of_key (mk : AddressedCell → Plan) {a : AddressedCell} :
    ∀ (held : List AddressedCell) (m : ℕ), a ∈ held → a.key ∉ (maskHits held m).map AddressedCell.key →
      a ∈ maskOut mk held m
  | [], _, h, _ => absurd h List.not_mem_nil
  | x :: rest, m, h, nk => by
    have nk' : a.key ∉ (maskHits rest (m / 2)).map AddressedCell.key := fun hk =>
      nk (by simp only [maskHits, List.map_append]; exact List.mem_append_right _ hk)
    rcases List.mem_cons.mp h with rfl | hr
    · by_cases bit : m % 2 = 1
      · exact absurd (by simp [maskHits, bit]) nk
      · simp only [maskOut, bit, ite_false]
        exact List.mem_append_left _ (List.mem_singleton_self _)
    · simp only [maskOut]
      exact List.mem_append_right _ (mem_maskOut_of_key mk rest (m / 2) hr nk')

/-- The masked atoms of a close pass, with the witness each must be paid with. -/
theorem segRows_close_run {check : WitnessRef → Cell → Bool} (w : Key → WitnessRef)
    (segs : List (List AddressedCell × ℕ))
    (h : ∀ x ∈ segs, ∀ a ∈ maskHits x.1 x.2, check (w a.key) a.cell = true) :
    ∀ x ∈ segs, ∀ a ∈ maskHits x.1 x.2, ∃ r, (closeMk w a).run check a.cell = some r :=
  fun x hx a ha => ⟨_, closeMk_run w a (h x hx a ha)⟩

/-! ### Dense stages: one tree per held atom, from one stream -/

/-- The held cells of a dyadic tree on an ordered cell are ordered. -/
theorem Tree.holds_ordered : ∀ (t : Tree) (b : Cell), OrderedCell b → t.Dyadic →
    ∀ x ∈ t.holds b, OrderedCell x.cell
  | .close _, _, _, _, x, h => absurd h List.not_mem_nil
  | .hold _, b, hb, _, x, h => by
    have e : x = ⟨_, b⟩ := List.mem_singleton.mp h
    rw [e]
    exact hb
  | .split (.dyadic a) l r, b, hb, hd, x, h => by
    rcases List.mem_append.mp h with hl | hr
    · exact Tree.holds_ordered l _ (orderedCell_child hb a false) hd.1 x hl
    · exact Tree.holds_ordered r _ (orderedCell_child hb a true) hd.2 x hr
  | .split (.rational _ _) _ _, _, _, hd, _, _ => hd.elim

/-- The rows of a dense stage: the trees of one stream, one per held atom in order, each
decoded with the atom's key and with witnesses that may depend on the atom. An atom the
stage leaves alone has the one-symbol tree `9`, a hold with its own key. -/
def streamRows (ws : AddressedCell → List WitnessRef) (fuel : ℕ) :
    List AddressedCell → ℕ → List StageRow × ℕ
  | [], s => ([], s)
  | a :: rest, s =>
    let T := tree (ws a) fuel a.key s
    let R := streamRows ws fuel rest T.2
    (⟨a, T.1.toPlan a.cell a.key⟩ :: R.1, R.2)

/-- The held list after a dense stage. -/
def streamOut (ws : AddressedCell → List WitnessRef) (fuel : ℕ) : List AddressedCell → ℕ → List AddressedCell
  | [], _ => []
  | a :: rest, s => (tree (ws a) fuel a.key s).1.holds a.cell ++ streamOut ws fuel rest (tree (ws a) fuel a.key s).2

/-- The closed leaves of a dense stage, with their cells: the arithmetic it needs. -/
def streamCloses (ws : AddressedCell → List WitnessRef) (fuel : ℕ) :
    List AddressedCell → ℕ → List (WitnessRef × Cell)
  | [], _ => []
  | a :: rest, s =>
    (tree (ws a) fuel a.key s).1.closes a.cell ++ streamCloses ws fuel rest (tree (ws a) fuel a.key s).2

/-- **Dense stage.** On held atoms with ordered cells, under any check paying the closed
leaves, the stream's rows replay and hold `streamOut`. -/
theorem replayStage_streamRows {check : WitnessRef → Cell → Bool} (ws : AddressedCell → List WitnessRef)
    (fuel : ℕ) : ∀ (held : List AddressedCell) (s : ℕ), (∀ a ∈ held, OrderedCell a.cell) →
      (∀ x ∈ streamCloses ws fuel held s, check x.1 x.2 = true) →
      ∃ paid, replayStage check held (streamRows ws fuel held s).1 = some ⟨paid, streamOut ws fuel held s⟩
  | [], _, _, _ => ⟨[], rfl⟩
  | a :: rest, s, ho, hc => by
    have hc1 : ∀ x ∈ (tree (ws a) fuel a.key s).1.closes a.cell, check x.1 x.2 = true :=
      fun x hx => hc x (by simp only [streamCloses]; exact List.mem_append_left _ hx)
    have hc2 : ∀ x ∈ streamCloses ws fuel rest (tree (ws a) fuel a.key s).2, check x.1 x.2 = true :=
      fun x hx => hc x (by simp only [streamCloses]; exact List.mem_append_right _ hx)
    obtain ⟨p1, h1⟩ := Tree.toPlan_run_of_closes _ a.cell a.key (ho a List.mem_cons_self)
      (tree_dyadic _ _ _ _) hc1
    obtain ⟨p2, h2⟩ := replayStage_streamRows ws fuel rest _ (fun x hx => ho x (List.mem_cons_of_mem a hx)) hc2
    refine ⟨p1 ++ p2, ?_⟩
    simp only [streamRows, streamOut]
    rw [replayStage, ite_eq_left (sameAddressedCell_self a)]
    simp only [h1, h2, Option.bind_eq_bind, Option.bind_some]
    rfl

/-- The held cells after a dense stage stay ordered. -/
theorem streamOut_ordered (ws : AddressedCell → List WitnessRef) (fuel : ℕ) :
    ∀ (held : List AddressedCell) (s : ℕ), (∀ a ∈ held, OrderedCell a.cell) →
      ∀ x ∈ streamOut ws fuel held s, OrderedCell x.cell
  | [], _, _, x, h => absurd h List.not_mem_nil
  | a :: rest, s, ho, x, h => by
    simp only [streamOut] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact Tree.holds_ordered _ _ (ho a List.mem_cons_self) (tree_dyadic _ _ _ _) x h1
    · exact streamOut_ordered ws fuel rest _ (fun y hy => ho y (List.mem_cons_of_mem a hy)) x h2

/-! ### Edit lists -/

theorem runEdits_append {check : WitnessRef → Cell → Bool} :
    ∀ (s : Snapshot) (xs ys : List Edit),
      runEdits check s (xs ++ ys) = (runEdits check s xs).bind fun t => runEdits check t ys
  | s, [], ys => rfl
  | s, e :: xs, ys => by
    simp only [List.cons_append, runEdits]
    cases e.run check s with
    | none => rfl
    | some t => exact runEdits_append t xs ys

theorem runEdits_single {check : WitnessRef → Cell → Bool} (s : Snapshot) (e : Edit) :
    runEdits check s [e] = e.run check s := by
  simp only [runEdits]
  cases e.run check s <;> rfl

/-! ### Rotation: the order into Adaptive -/

/-- `indicesCheck` holds when the index of every source atom points at that very atom. -/
theorem indicesCheck_of_get (target : List AddressedCell) :
    ∀ (source : List AddressedCell) (indices : List ℕ), indices.length = source.length →
      (∀ j (hj : j < source.length) (hi : j < indices.length), target[indices[j]]? = some source[j]) →
      indicesCheck target.toArray source indices = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: tail, i :: more, hl, hg => by
    have h0 := hg 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ht : indicesCheck target.toArray tail more = true :=
      indicesCheck_of_get target tail more (by simpa using hl) fun j hj hi => by
        have := hg (j + 1) (by simpa using hj) (by simpa using hi)
        simpa only [List.getElem_cons_succ] using this
    simp only [indicesCheck, List.getElem?_toArray, h0, sameCell_self, ht, Bool.and_self]

/-- Move the first `n` atoms of the held list to its end. -/
def rotation (n : ℕ) (held : List AddressedCell) : Reorder :=
  ⟨held.drop n ++ held.take n,
    (List.range held.length).map fun i => (i + (held.length - n)) % held.length,
    (List.range held.length).map fun j => (j + n) % held.length⟩

theorem getElem?_rotate (held : List AddressedCell) (n i : ℕ) (hn : n ≤ held.length) (hi : i < held.length) :
    (held.drop n ++ held.take n)[(i + (held.length - n)) % held.length]? = some held[i] := by
  have hlen : (held.drop n ++ held.take n).length = held.length := by
    simp only [List.length_append, List.length_drop, List.length_take]; omega
  by_cases c : n ≤ i
  · have e : (i + (held.length - n)) % held.length = i - n := by
      rw [show i + (held.length - n) = (i - n) + held.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e, List.getElem?_append_left (by simp; omega), List.getElem?_drop, show n + (i - n) = i by omega,
      List.getElem?_eq_getElem hi]
  · have e : (i + (held.length - n)) % held.length = i + (held.length - n) :=
      Nat.mod_eq_of_lt (by omega)
    rw [e, List.getElem?_append_right (by simp only [List.length_drop]; omega)]
    simp only [List.length_drop]
    rw [show i + (held.length - n) - (held.length - n) = i by omega, List.getElem?_take]
    simp [show i < n by omega, List.getElem?_eq_getElem hi]

theorem getElem?_unrotate (held : List AddressedCell) (n j : ℕ) (hn : n ≤ held.length)
    (hj : j < (held.drop n ++ held.take n).length) :
    held[(j + n) % held.length]? = some (held.drop n ++ held.take n)[j] := by
  have hlen : (held.drop n ++ held.take n).length = held.length := by
    simp only [List.length_append, List.length_drop, List.length_take]; omega
  rw [← List.getElem?_eq_getElem]
  by_cases c : j < held.length - n
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_drop,
      Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_take]
    simp only [List.length_drop]
    have e : (j + n) % held.length = j - (held.length - n) := by
      rw [show j + n = (j - (held.length - n)) + held.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e]
    simp [show j - (held.length - n) < n by omega]

/-- **Rotation.** The rotation edit runs on any snapshot and leaves the held list rotated. -/
theorem rotation_run (s : Snapshot) (n : ℕ) (hn : n ≤ s.held.length) :
    (rotation n s.held).run s = some {s with held := s.held.drop n ++ s.held.take n} := by
  have hlen : (s.held.drop n ++ s.held.take n).length = s.held.length := by
    simp only [List.length_append, List.length_drop, List.length_take]; omega
  have fwd : indicesCheck (s.held.drop n ++ s.held.take n).toArray s.held
      ((List.range s.held.length).map fun i => (i + (s.held.length - n)) % s.held.length) = true :=
    indicesCheck_of_get _ _ _ (by simp) fun j hj _ => by
      simpa using getElem?_rotate s.held n j hn hj
  have bwd : indicesCheck s.held.toArray (s.held.drop n ++ s.held.take n)
      ((List.range s.held.length).map fun j => (j + n) % s.held.length) = true :=
    indicesCheck_of_get _ _ _ (by simp [hlen]) fun j hj _ => by
      simpa using getElem?_unrotate s.held n j hn hj
  simp only [Reorder.run, rotation, fwd, bwd, Bool.and_self, ite_true]

/-! ### Position maps for coalescing -/

/-- The coalescing edit at held positions `i < j`, merging the atoms there into `parent`. -/
def mergeAt (held : List AddressedCell) (i j : ℕ) (parent : AddressedCell) (axis : Axis) : Option Edit :=
  match held.drop i, held.drop j with
  | low :: _, high :: _ =>
    some (.merge (held.take i) ((held.drop (i + 1)).take (j - i - 1)) (held.drop (j + 1)) ⟨low, high, parent, axis⟩)
  | _, _ => none

theorem sameRoster_self : ∀ a : List AddressedCell, sameRoster a a = true
  | [] => rfl
  | x :: xs => by simp only [sameRoster, sameAddressedCell_self, sameRoster_self xs, Bool.and_self]

theorem split_at_two (held : List AddressedCell) (i j : ℕ) (hij : i < j) {low high : AddressedCell}
    {r1 r2 : List AddressedCell} (hi : held.drop i = low :: r1) (hj : held.drop j = high :: r2) :
    held = held.take i ++ [low] ++ (held.drop (i + 1)).take (j - i - 1) ++ [high] ++ held.drop (j + 1) := by
  have e1 : held = held.take i ++ low :: r1 := by rw [← hi, List.take_append_drop]
  have e2 : held.drop (i + 1) = r1 := by
    rw [← List.drop_drop, hi, List.drop_one, List.tail_cons]
  have e3 : r1.drop (j - i - 1) = high :: r2 := by
    rw [← e2, List.drop_drop, show i + 1 + (j - i - 1) = j by omega, hj]
  have e4 : held.drop (j + 1) = r2 := by
    rw [← List.drop_drop, hj, List.drop_one, List.tail_cons]
  rw [e2, e4]
  conv_lhs => rw [e1]
  have e5 : r1 = r1.take (j - i - 1) ++ high :: r2 := by rw [← e3, List.take_append_drop]
  conv_lhs => rw [e5]
  simp

/-- **Merge at positions.** The edit runs when its merge check passes, and replaces the two
atoms by the parent at the first position. -/
theorem mergeAt_run {check : WitnessRef → Cell → Bool} (s : Snapshot) (i j : ℕ) (hij : i < j)
    (parent : AddressedCell) (axis : Axis) (e : Edit) (he : mergeAt s.held i j parent axis = some e) :
    ∃ low high r1 r2, s.held.drop i = low :: r1 ∧ s.held.drop j = high :: r2 ∧
      e = .merge (s.held.take i) ((s.held.drop (i + 1)).take (j - i - 1)) (s.held.drop (j + 1))
        ⟨low, high, parent, axis⟩ ∧
      (MergeRow.check ⟨low, high, parent, axis⟩ = true →
        e.run check s = some ⟨s.paid, s.held.take i ++ [parent] ++
          (s.held.drop (i + 1)).take (j - i - 1) ++ s.held.drop (j + 1)⟩) := by
  unfold mergeAt at he
  split at he
  · rename_i low r1 high r2 hi hj
    cases he
    refine ⟨low, high, r1, r2, hi, hj, rfl, fun hc => ?_⟩
    have split := split_at_two s.held i j hij hi hj
    simp only [Edit.run, MergeRow.run]
    rw [← split, sameRoster_self, hc]
    rfl
  · cases he

/-- Coalescing on dyadic words is geometrically exact with no evaluation: the two halves of
`descend b w` along axis `a` are `descend b (w ++ [2a])` and `descend b (w ++ [2a+1])`. -/
theorem MergeRow.check_descend (b : Cell) (hb : OrderedCell b) (w : List ℕ) (a : Axis) (k₁ k₂ k : Key) :
    MergeRow.check ⟨⟨k₁, descend b (w ++ [2 * a.val])⟩, ⟨k₂, descend b (w ++ [2 * a.val + 1])⟩,
      ⟨k, descend b w⟩, a⟩ = true := by
  simp only [MergeRow.check, descend_append, descend, digitChild_low, digitChild_high,
    fits_dyadic (orderedCell_descend w hb), sameCell_self, Bool.and_self]

/-! ### Position maps for clips -/

/-- The clip edit at held position `i`: `before` and `after` are `take`/`drop` of the held
list and the clipped atom is the one there. -/
def clipAt (held : List AddressedCell) (i : ℕ) (mk : AddressedCell → ClipRow) : Option Edit :=
  match held.drop i with
  | a :: _ => some (.clip (held.take i) (held.drop (i + 1)) (mk a))
  | [] => none

/-- **Clip at a position.** When the row built on the atom at position `i` has that atom as
input and passes its check, the edit runs and replaces the atom by the row's strips. -/
theorem clipAt_run {check : WitnessRef → Cell → Bool} (s : Snapshot) (i : ℕ) (mk : AddressedCell → ClipRow)
    (e : Edit) (he : clipAt s.held i mk = some e) :
    ∃ a rest, s.held.drop i = a :: rest ∧ e = .clip (s.held.take i) (s.held.drop (i + 1)) (mk a) ∧
      ((mk a).input = a → (mk a).check check = true →
        e.run check s = some ⟨s.paid ++ (mk a).result.paid, (s.held.take i ++ (mk a).remainder) ++ s.held.drop (i + 1)⟩) := by
  unfold clipAt at he
  split at he
  · rename_i a rest hd
    cases he
    refine ⟨a, rest, hd, rfl, fun hin hc => ?_⟩
    have split : s.held = s.held.take i ++ (mk a).input :: s.held.drop (i + 1) := by
      rw [hin]
      conv_lhs => rw [← List.take_append_drop i s.held, hd]
      rw [← List.drop_drop, hd, List.drop_one, List.tail_cons]
    simp only [Edit.run, Snapshot.applyClip]
    rw [← split, sameRoster_self, hc]
    rfl
  · cases he

end DataPath

end BccSharp.Coulomb.CompactCover
