import BccSharp.Cover.ReplayCompose

set_option autoImplicit false

/-! # The data path from Stage3 to Stage5b: sparse tree stages and clip stages

Generic definitions and run theorems for the literal data of the prefix after Adaptive. Every theorem is generic in the data: its proof evaluates nothing, and the
only hypotheses are the arithmetic at closed leaves and clip sources and two data checks: for
tree stages, ordered endpoints of the atoms that get a tree (one Bool where the cells are not
dyadic cells of the root, as the Stage5b phase pieces), and for clips, one Bool geometry check per
chunk.

* **Records.** `rtree` reads a replacement tree whose closed leaves take consecutive record
  numbers: symbol `10 + i` closes a leaf of kind `kinds[i]` (its route and exact source string)
  with the next record number. A chunk's first record number is
  given, and chunks have disjoint ranges (Stage3: the stage's closed leaves counted
  in held order; Stage5b phase: 65,536 × the root's index, one root per chunk), so a leaf's
  `(source, route, record)` names it uniquely and per-witness hint tables (`stage5bHybridCheck`)
  can key on it. The decoder makes only dyadic cuts
  (`rtree_dyadic`).
* **Sparse tree stages** (Stage3, the Stage5b phase sweep): `treeRows` gives the `j`-th atom of a
  chunk the next tree of a stream when bit `j` of the chunk's mask is set, and its pass-through
  row otherwise. `replayStage_treeRows`: the rows replay under any check paying the closed
  leaves (`treeCloses`), and hold `treeOut`; `replayStage_passRows` for a chunk with no tree.
* **Clip stages** (Stage4, Stage5a, Stage5b optical): `clipRowOf` builds a clip row from the atom it
  cuts, so its input is the atom, its paid cell and remainder strips are those of
  `checkedSubtract`; `clipRowOf_check`: the row passes when the Bool geometry `clipGeom` holds
  and the check accepts the certificate's receipt on its source cell (per source, not per
  clip). A chunk's clips are a list of `ClipSpec`s applied in order, each at a position of the
  list the earlier ones leave (`clipEdits`); `runEdits_clipEdits`: they run from one geometry
  evaluation of the chunk (`clipsGeom`) and the sources' arithmetic, and leave `clipsOut`. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay OverlayPlanar OverlayCorpus

namespace DataPath.Later

/-! ### Trees whose closed leaves take consecutive record numbers -/

/-- A packed replacement tree with fuel `n`, parent key `k`, stream `s` and next record `r`:
the tree, the rest of the stream and the next record. Symbols (radix 17, least significant
first): `1`–`8` a dyadic split on axis `0`–`7` (low child first), `9` a hold with the key
`slotChild` derives, `10 + i` a closed leaf of kind `kinds[i]` with record `r`. An early end,
exhausted fuel or a kind out of range gives the error hold `errTree`. -/
def rtree (kinds : List (Route × String)) : ℕ → Key → ℕ → ℕ → Tree × ℕ × ℕ
  | 0, _, s, r => (errTree, s, r)
  | n + 1, k, s, r =>
    let c := s % 17
    if c = 0 then (errTree, s, r)
    else if c ≤ 8 then
      let L := rtree kinds n (slotChild k (axisOf c) false) (s / 17) r
      let H := rtree kinds n (slotChild k (axisOf c) true) L.2.1 L.2.2
      (.split (.dyadic (axisOf c)) L.1 H.1, H.2.1, H.2.2)
    else if c = 9 then (.hold k, s / 17, r)
    else
      match kinds[c - 10]? with
      | some kr => (.close ⟨kr.1, kr.2, r⟩, s / 17, r + 1)
      | none => (errTree, s / 17, r)

theorem rtree_dyadic (kinds : List (Route × String)) :
    ∀ (n : ℕ) (k : Key) (s r : ℕ), (rtree kinds n k s r).1.Dyadic
  | 0, _, _, _ => trivial
  | n + 1, k, s, r => by
    simp only [rtree]
    split_ifs
    · trivial
    · exact ⟨rtree_dyadic kinds n _ _ _, rtree_dyadic kinds n _ _ _⟩
    · trivial
    · split <;> trivial

/-! ### Sparse tree stages -/

/-- The rows of a sparse tree stage on a chunk: bit `j` of the mask `m` gives the `j`-th atom
the next tree of the stream `s`, decoded with the atom's key and records from `r`; every other
atom gets its pass-through row. -/
def treeRows (kinds : List (Route × String)) (fuel : ℕ) :
    List AddressedCell → ℕ → ℕ → ℕ → List StageRow
  | [], _, _, _ => []
  | a :: rest, m, s, r =>
    if m % 2 = 1 then
      ⟨a, (rtree kinds fuel a.key s r).1.toPlan a.cell a.key⟩ ::
        treeRows kinds fuel rest (m / 2) (rtree kinds fuel a.key s r).2.1 (rtree kinds fuel a.key s r).2.2
    else passRow a :: treeRows kinds fuel rest (m / 2) s r

/-- The held list after that stage. -/
def treeOut (kinds : List (Route × String)) (fuel : ℕ) :
    List AddressedCell → ℕ → ℕ → ℕ → List AddressedCell
  | [], _, _, _ => []
  | a :: rest, m, s, r =>
    if m % 2 = 1 then
      (rtree kinds fuel a.key s r).1.holds a.cell ++
        treeOut kinds fuel rest (m / 2) (rtree kinds fuel a.key s r).2.1 (rtree kinds fuel a.key s r).2.2
    else a :: treeOut kinds fuel rest (m / 2) s r

/-- The closed leaves of that stage with their cells: the arithmetic it needs. -/
def treeCloses (kinds : List (Route × String)) (fuel : ℕ) :
    List AddressedCell → ℕ → ℕ → ℕ → List (WitnessRef × Cell)
  | [], _, _, _ => []
  | a :: rest, m, s, r =>
    if m % 2 = 1 then
      (rtree kinds fuel a.key s r).1.closes a.cell ++
        treeCloses kinds fuel rest (m / 2) (rtree kinds fuel a.key s r).2.1 (rtree kinds fuel a.key s r).2.2
    else treeCloses kinds fuel rest (m / 2) s r

/-- **Sparse tree stage.** If the chosen atoms' cells are ordered and the check pays every
closed leaf, the rows replay on the chunk and hold `treeOut`. -/
theorem replayStage_treeRows {check : WitnessRef → Cell → Bool} (kinds : List (Route × String))
    (fuel : ℕ) : ∀ (held : List AddressedCell) (m s r : ℕ), (∀ a ∈ maskHits held m, OrderedCell a.cell) →
      (∀ x ∈ treeCloses kinds fuel held m s r, check x.1 x.2 = true) →
      ∃ paid, replayStage check held (treeRows kinds fuel held m s r) =
        some ⟨paid, treeOut kinds fuel held m s r⟩
  | [], _, _, _, _, _ => ⟨[], rfl⟩
  | a :: rest, m, s, r, ho, hc => by
    by_cases bit : m % 2 = 1
    · have hc1 : ∀ x ∈ (rtree kinds fuel a.key s r).1.closes a.cell, check x.1 x.2 = true :=
        fun x hx => hc x (by simp only [treeCloses, bit, ite_true]; exact List.mem_append_left _ hx)
      have hc2 : ∀ x ∈ treeCloses kinds fuel rest (m / 2) (rtree kinds fuel a.key s r).2.1
          (rtree kinds fuel a.key s r).2.2, check x.1 x.2 = true :=
        fun x hx => hc x (by simp only [treeCloses, bit, ite_true]; exact List.mem_append_right _ hx)
      have ha : OrderedCell a.cell := ho a (by simp [maskHits, bit])
      have hrest : ∀ x ∈ maskHits rest (m / 2), OrderedCell x.cell :=
        fun x hx => ho x (by simp only [maskHits]; exact List.mem_append_right _ hx)
      obtain ⟨p1, h1⟩ := Tree.toPlan_run_of_closes _ a.cell a.key ha (rtree_dyadic _ _ _ _ _) hc1
      obtain ⟨p2, h2⟩ := replayStage_treeRows kinds fuel rest (m / 2) _ _ hrest hc2
      refine ⟨p1 ++ p2, ?_⟩
      simp only [treeRows, treeOut, bit, ite_true]
      rw [replayStage, ite_eq_left (sameAddressedCell_self a)]
      simp only [h1, h2, Option.bind_eq_bind, Option.bind_some]
      rfl
    · have hc2 : ∀ x ∈ treeCloses kinds fuel rest (m / 2) s r, check x.1 x.2 = true :=
        fun x hx => hc x (by simp only [treeCloses, bit, ite_false]; exact hx)
      have hrest : ∀ x ∈ maskHits rest (m / 2), OrderedCell x.cell :=
        fun x hx => ho x (by simp only [maskHits, bit, ite_false]; exact List.mem_append_right _ hx)
      obtain ⟨p2, h2⟩ := replayStage_treeRows kinds fuel rest (m / 2) s r hrest hc2
      refine ⟨[] ++ p2, ?_⟩
      have g : sameAddressedCell a (passRow a).input = true := sameAddressedCell_self a
      simp only [treeRows, treeOut, bit, ite_false]
      rw [replayStage, ite_eq_left g, passRow_run, h2]
      rfl

/-- **A chunk with no tree.** Pass-through rows replay and keep the chunk. -/
theorem replayStage_passRows {check : WitnessRef → Cell → Bool} :
    ∀ held : List AddressedCell, replayStage check held (held.map passRow) = some ⟨[], held⟩
  | [] => rfl
  | a :: rest => by
    have g : sameAddressedCell a (passRow a).input = true := sameAddressedCell_self a
    simp only [List.map_cons]
    rw [replayStage, ite_eq_left g, passRow_run, replayStage_passRows rest]
    rfl

/-! ### Clip stages -/

theorem sameBoxes_map (k : Key) : ∀ strips : List Cell,
    sameBoxes strips (strips.map fun c => (⟨k, c⟩ : AddressedCell)) = true
  | [] => rfl
  | c :: cs => by simp only [List.map_cons, sameBoxes, sameCell_self, sameBoxes_map k cs, Bool.and_self]

/-- The clip of the atom `a` by `window`, paid by the certificate on `source` moved by
`motion`: the paid cell and the remainder strips are `checkedSubtract`'s, with the atom's key.
(When `checkedSubtract` gives no paid cell the row is built anyway, and fails its check.) -/
def clipRowOf (w : WitnessRef) (source : Cell) (motion : ChartMotion) (window : Cell)
    (a : AddressedCell) : ClipRow :=
  match checkedSubtract a.cell window with
  | some (strips, some paid) => ⟨a, ⟨w, source, motion, paid⟩, window, a.key, strips.map fun c => ⟨a.key, c⟩⟩
  | _ => ⟨a, ⟨w, source, motion, a.cell⟩, window, a.key, [a]⟩

theorem clipRowOf_input (w : WitnessRef) (source : Cell) (motion : ChartMotion) (window : Cell)
    (a : AddressedCell) : (clipRowOf w source motion window a).input = a := by
  unfold clipRowOf
  split <;> rfl

/-- The geometry of that clip: the window meets the atom's cell with positive width and the
carve works (`checkedSubtract`), and the window lies in the certificate's image of its source
(so does the paid cell, which `checkedSubtract` keeps inside the window). One Bool, evaluated on
the atom's cell. -/
def clipGeom (source : Cell) (motion : ChartMotion) (window cell : Cell) : Bool :=
  match checkedSubtract cell window with
  | some (_, some _) => insideCheck window (motion.image source)
  | _ => false

theorem insideCheck_trans {x y z : Cell} (h1 : insideCheck x y = true) (h2 : insideCheck y z = true) :
    insideCheck x z = true := by
  have e1 : ∀ i, y.lo i ≤ x.lo i ∧ x.hi i ≤ y.hi i := of_decide_eq_true h1
  have e2 : ∀ i, z.lo i ≤ y.lo i ∧ y.hi i ≤ z.hi i := of_decide_eq_true h2
  exact decide_eq_true fun i => ⟨(e2 i).1.trans (e1 i).1, (e1 i).2.trans (e2 i).2⟩

/-- The paid cell of `checkedSubtract` lies in the window. -/
theorem checkedSubtract_inside (parent source : Cell) (rest : List Cell) (paid : Cell)
    (ok : checkedSubtract parent source = some (rest, some paid)) : insideCheck paid source = true := by
  simp only [checkedSubtract] at ok
  by_cases live : positiveCell (intersection parent source) = true
  · rw [ite_eq_left live] at ok
    cases he : carve parent (clipSteps parent (intersection parent source)) with
    | none =>
      rw [he] at ok
      simp at ok
    | some result =>
      rcases result with ⟨slabs, reached⟩
      rw [he] at ok
      change (if (sameCell reached (intersection parent source) && insideCheck reached source) = true
        then some (slabs, some reached) else none) = some (rest, some paid) at ok
      by_cases bounded : (sameCell reached (intersection parent source) && insideCheck reached source) = true
      · rw [ite_eq_left bounded] at ok
        have e : reached = paid := by
          have h := Option.some.inj ok
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          exact h.2
        rw [← e]
        exact (Bool.and_eq_true_iff.mp bounded).2
      · rw [ite_eq_right bounded] at ok
        simp at ok
  · rw [ite_eq_right live] at ok
    simp at ok

/-- **A clip row from its geometry and its source's arithmetic.** -/
theorem clipRowOf_check {check : WitnessRef → Cell → Bool} (w : WitnessRef) (source : Cell)
    (motion : ChartMotion) (window : Cell) (a : AddressedCell)
    (geom : clipGeom source motion window a.cell = true) (arith : check w source = true) :
    (clipRowOf w source motion window a).check check = true := by
  unfold clipGeom at geom
  unfold clipRowOf
  split
  · rename_i strips paid h
    rw [h] at geom
    have hp : insideCheck paid (motion.image source) = true :=
      insideCheck_trans (checkedSubtract_inside _ _ _ _ h) geom
    exact ClipRow.check_of _ (strips := strips) (paid := paid) h
      (by simp only [sameBoxes_map, sameCell_self, geom, Bool.and_self]) hp arith
  · rename_i h
    split at geom
    · rename_i strips paid h'
      exact absurd h' (h strips paid)
    · simp at geom

/-- A clip of a chunk's clip sequence: the position of the piece it cuts in the list the earlier
clips leave, and its certificate and window. -/
structure ClipSpec where
  pos : ℕ
  receipt : WitnessRef
  source : Cell
  motion : ChartMotion
  window : Cell

/-- The clip row of a spec on the atom it cuts. -/
def ClipSpec.row (c : ClipSpec) (a : AddressedCell) : ClipRow :=
  clipRowOf c.receipt c.source c.motion c.window a

/-- The clip edits of a chunk, each built on the list the earlier ones leave. -/
def clipEdits : List ClipSpec → List AddressedCell → List Edit
  | [], _ => []
  | c :: cs, held =>
    match held.drop c.pos with
    | a :: _ => .clip (held.take c.pos) (held.drop (c.pos + 1)) (c.row a) ::
        clipEdits cs (held.take c.pos ++ (c.row a).remainder ++ held.drop (c.pos + 1))
    | [] => []

/-- The geometry of a chunk's clips, in order: every position names a piece of the current list
and every clip's geometry holds. One kernel evaluation per chunk. -/
def clipsGeom : List ClipSpec → List AddressedCell → Bool
  | [], _ => true
  | c :: cs, held =>
    match held.drop c.pos with
    | a :: _ => clipGeom c.source c.motion c.window a.cell &&
        clipsGeom cs (held.take c.pos ++ (c.row a).remainder ++ held.drop (c.pos + 1))
    | [] => false

/-- The paid cells of a chunk's clips. -/
def clipsPaid : List ClipSpec → List AddressedCell → List AddressedCell
  | [], _ => []
  | c :: cs, held =>
    match held.drop c.pos with
    | a :: _ => (c.row a).result.paid ++
        clipsPaid cs (held.take c.pos ++ (c.row a).remainder ++ held.drop (c.pos + 1))
    | [] => []

/-- The list a chunk's clips leave. -/
def clipsOut : List ClipSpec → List AddressedCell → List AddressedCell
  | [], held => held
  | c :: cs, held =>
    match held.drop c.pos with
    | a :: _ => clipsOut cs (held.take c.pos ++ (c.row a).remainder ++ held.drop (c.pos + 1))
    | [] => held

theorem clipEdits_local : ∀ (cs : List ClipSpec) (held : List AddressedCell),
    ∀ e ∈ clipEdits cs held, e.isLocal = true
  | [], _, e, h => absurd h List.not_mem_nil
  | c :: cs, held, e, h => by
    unfold clipEdits at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact clipEdits_local cs _ e h
    · exact absurd h List.not_mem_nil

/-- **A chunk's clips from one geometry evaluation and the sources' arithmetic.** -/
theorem runEdits_clipEdits {check : WitnessRef → Cell → Bool} :
    ∀ (cs : List ClipSpec) (q held : List AddressedCell), clipsGeom cs held = true →
      (∀ c ∈ cs, check c.receipt c.source = true) →
      runEdits check ⟨q, held⟩ (clipEdits cs held) = some ⟨q ++ clipsPaid cs held, clipsOut cs held⟩
  | [], q, held, _, _ => by simp [clipEdits, clipsPaid, clipsOut, runEdits]
  | c :: cs, q, held, hg, ha => by
    unfold clipsGeom at hg
    split at hg
    · rename_i a rest hd
      obtain ⟨g1, g2⟩ := Bool.and_eq_true_iff.mp hg
      have arith : check c.receipt c.source = true := ha c (by simp)
      have rowOk : (c.row a).check check = true :=
        clipRowOf_check c.receipt c.source c.motion c.window a g1 arith
      have split : held = held.take c.pos ++ (c.row a).input :: held.drop (c.pos + 1) := by
        rw [show (c.row a).input = a from clipRowOf_input _ _ _ _ a]
        conv_lhs => rw [← List.take_append_drop c.pos held, hd]
        rw [← List.drop_drop, hd, List.drop_one, List.tail_cons]
      have step : (Edit.clip (held.take c.pos) (held.drop (c.pos + 1)) (c.row a)).run check ⟨q, held⟩ =
          some ⟨q ++ (c.row a).result.paid,
            held.take c.pos ++ (c.row a).remainder ++ held.drop (c.pos + 1)⟩ := by
        simp only [Edit.run, Snapshot.applyClip]
        rw [← split, DataPath.sameRoster_self, rowOk]
        rfl
      have ih := runEdits_clipEdits cs (q ++ (c.row a).result.paid)
        (held.take c.pos ++ (c.row a).remainder ++ held.drop (c.pos + 1)) g2
        (fun d hd => ha d (List.mem_cons_of_mem _ hd))
      simp only [clipEdits, clipsPaid, clipsOut, hd]
      rw [runEdits_cons_of step, ih, List.append_assoc]
    · simp at hg

end DataPath.Later

end BccSharp.Coulomb.CompactCover
