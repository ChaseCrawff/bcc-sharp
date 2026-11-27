import BccSharp.Cover.ReplayCompose

set_option autoImplicit false

/-! # The stage-3 mirror over a dyadic trie of the old held list

`mirror_chunks` (`BccSharp.Cover.ReplayCompose`) states the mirror chunk by chunk, and
`filterMap_clip_far` drops a chunk whose box meets a positive atom with no positive width.
Flat chunks of consecutive held atoms have loose 8-D boxes, so that test drops too little. Here the old held
list's chunks are the leaves of a dyadic
trie in held order: each node's box is its dyadic cell, read from the trie path (no box is
stored), and a search with a positive atom's cell drops every subtree whose reflected cell
meets it with no positive width (`Trie.near`).

* `Trie`: `leaf is` is the run of chunks `is`, `split n l r` halves the current cell on axis
  `n % 8` (low child first), `pair l r` puts two tries on the same cell (the held list's two
  runs), `empty` has no chunk.
* `Trie.leafCells`: every chunk index with its leaf's cell. The data check
  `Trie.checkChunk`: every nonpositive atom of the chunk lies in that cell (one kernel
  evaluation per chunk).
* `Trie.clips_near`: on an ordered cell, with every chunk checked, the clips of an atom inside
  `A` with all chunks are its clips with the chunks `t.near A b`.
* **`mirror_trie`**: the mirror from a trie over the old held list, each positive atom
  searching with its own cell. Nothing is evaluated by these proofs. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay OverlayPlanar OverlayCorpus

namespace DataPath.LaterMirror

/-! ### Cells -/

theorem insideCheck_self (b : Cell) : insideCheck b b = true :=
  decide_eq_true fun _ => ⟨le_refl _, le_refl _⟩

theorem insideCheck_trans {x y z : Cell} (h1 : insideCheck x y = true) (h2 : insideCheck y z = true) :
    insideCheck x z = true := by
  have e1 : ∀ i, y.lo i ≤ x.lo i ∧ x.hi i ≤ y.hi i := of_decide_eq_true h1
  have e2 : ∀ i, z.lo i ≤ y.lo i ∧ y.hi i ≤ z.hi i := of_decide_eq_true h2
  exact decide_eq_true fun i => ⟨(e2 i).1.trans (e1 i).1, (e1 i).2.trans (e2 i).2⟩

theorem insideCheck_reflect {x y : Cell} (h : insideCheck x y = true) :
    insideCheck (reflectCell x) (reflectCell y) = true := by
  have e : ∀ i, y.lo i ≤ x.lo i ∧ x.hi i ≤ y.hi i := of_decide_eq_true h
  refine decide_eq_true fun i => ?_
  simp only [reflectCell]
  by_cases hi : i.val < 5
  · simp only [hi, ite_true]
    exact e i
  · simp only [hi, ite_false]
    exact ⟨neg_le_neg (e i).2, neg_le_neg (e i).1⟩

/-- The axis of a trie split, a plain natural number taken mod 8 (so trie literals need no
`Fin` elaboration). -/
def axisOfN (n : ℕ) : Axis := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

/-- The dyadic child of a cell on the axis `n % 8`. -/
def dchild (b : Cell) (n : ℕ) (u : Bool) : Cell := (Cut.dyadic (axisOfN n)).child b u

theorem insideCheck_dchild {b : Cell} (h : OrderedCell b) (n : ℕ) (u : Bool) :
    insideCheck (dchild b n u) b = true := by
  refine decide_eq_true fun i => ?_
  have ha := h (axisOfN n)
  simp only [dchild, Cut.child, Cut.position, replaceEnd, midpoint]
  by_cases e : i = axisOfN n
  · subst e
    cases u <;> simp <;> linarith
  · cases u <;> simp [e]

theorem orderedCell_dchild {b : Cell} (h : OrderedCell b) (n : ℕ) (u : Bool) : OrderedCell (dchild b n u) :=
  orderedCell_child h (axisOfN n) u

/-! ### The trie -/

/-- A dyadic trie over the chunks of a held list, in held order. -/
inductive Trie where
  | empty
  | leaf (chunks : List ℕ)
  | split (axis : ℕ) (low high : Trie)
  | pair (first second : Trie)

/-- The chunk indices of a trie, in order. -/
def Trie.chunks : Trie → List ℕ
  | .empty => []
  | .leaf is => is
  | .split _ l r => l.chunks ++ r.chunks
  | .pair l r => l.chunks ++ r.chunks

/-- Every chunk index with the cell of its leaf, for the trie on the cell `b`. -/
def Trie.leafCells (b : Cell) : Trie → List (ℕ × Cell)
  | .empty => []
  | .leaf is => is.map fun i => (i, b)
  | .split n l r => l.leafCells (dchild b n false) ++ r.leafCells (dchild b n true)
  | .pair l r => l.leafCells b ++ r.leafCells b

/-- The data check of one chunk: its nonpositive atoms lie in its leaf's cell. -/
def Trie.checkChunk (chunkAt : ℕ → List AddressedCell) (x : ℕ × Cell) : Bool :=
  (nonpositive (chunkAt x.1)).all fun a => insideCheck a.cell x.2

/-- The chunks whose leaf's reflected cell meets `A` with positive width; a subtree is dropped
as soon as its reflected cell does not. -/
def Trie.near (A : Cell) (b : Cell) : Trie → List ℕ
  | .empty => []
  | .leaf is => if positiveCell (intersection A (reflectCell b)) then is else []
  | .split n l r =>
    if positiveCell (intersection A (reflectCell b)) then
      l.near A (dchild b n false) ++ r.near A (dchild b n true)
    else []
  | .pair l r =>
    if positiveCell (intersection A (reflectCell b)) then l.near A b ++ r.near A b else []

theorem Trie.leafCells_inside : ∀ (t : Trie) (b : Cell), OrderedCell b →
    ∀ x ∈ t.leafCells b, insideCheck x.2 b = true
  | .empty, _, _, x, h => absurd h List.not_mem_nil
  | .leaf is, b, _, x, h => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    exact insideCheck_self b
  | .split n l r, b, hb, x, h => by
    rcases List.mem_append.mp h with h | h
    · exact insideCheck_trans (Trie.leafCells_inside l _ (orderedCell_dchild hb n false) x h)
        (insideCheck_dchild hb n false)
    · exact insideCheck_trans (Trie.leafCells_inside r _ (orderedCell_dchild hb n true) x h)
        (insideCheck_dchild hb n true)
  | .pair l r, b, hb, x, h => by
    rcases List.mem_append.mp h with h | h
    · exact Trie.leafCells_inside l b hb x h
    · exact Trie.leafCells_inside r b hb x h

theorem Trie.mem_leafCells_chunks : ∀ (t : Trie) (b : Cell) (i : ℕ), i ∈ t.chunks →
    ∃ c, (i, c) ∈ t.leafCells b
  | .empty, _, _, h => absurd h List.not_mem_nil
  | .leaf is, b, i, h => ⟨b, List.mem_map.mpr ⟨i, h, rfl⟩⟩
  | .split n l r, b, i, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨c, hc⟩ := Trie.mem_leafCells_chunks l _ i h
      exact ⟨c, List.mem_append_left _ hc⟩
    · obtain ⟨c, hc⟩ := Trie.mem_leafCells_chunks r _ i h
      exact ⟨c, List.mem_append_right _ hc⟩
  | .pair l r, b, i, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨c, hc⟩ := Trie.mem_leafCells_chunks l b i h
      exact ⟨c, List.mem_append_left _ hc⟩
    · obtain ⟨c, hc⟩ := Trie.mem_leafCells_chunks r b i h
      exact ⟨c, List.mem_append_right _ hc⟩

/-- The clips of `a` with the reflected nonpositive atoms of chunk `i`. -/
def chunkClips (key : Key → Key → Key) (chunkAt : ℕ → List AddressedCell) (a : AddressedCell) (i : ℕ) :
    List AddressedCell :=
  (reflectedRoster (nonpositive (chunkAt i))).filterMap (clipOf key a)

/-- A checked chunk inside a cell whose reflection is far from `A` gives no clip. -/
theorem chunkClips_far (key : Key → Key → Key) (chunkAt : ℕ → List AddressedCell) {a : AddressedCell}
    {A b c : Cell} (ha : insideCheck a.cell A = true) (i : ℕ)
    (hi : Trie.checkChunk chunkAt (i, c) = true) (hc : insideCheck c b = true)
    (far : positiveCell (intersection A (reflectCell b)) = false) : chunkClips key chunkAt a i = [] := by
  apply filterMap_clip_far key ha _ far
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hy' : insideCheck y.cell c = true := List.all_eq_true.mp hi y hy
  exact insideCheck_reflect (insideCheck_trans hy' hc)

theorem flatten_map_nil {α β : Type} (g : α → List β) :
    ∀ l : List α, (∀ x ∈ l, g x = []) → (l.map g).flatten = []
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, List.flatten_cons, h x (by simp), List.nil_append]
    exact flatten_map_nil g l fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **Clips over a trie.** On an ordered cell, with every chunk checked, the clips of an atom
inside `A` with all chunks are its clips with the chunks the search keeps. -/
theorem Trie.clips_near (key : Key → Key → Key) (chunkAt : ℕ → List AddressedCell) (a : AddressedCell)
    (A : Cell) (ha : insideCheck a.cell A = true) :
    ∀ (t : Trie) (b : Cell), OrderedCell b → (∀ x ∈ t.leafCells b, Trie.checkChunk chunkAt x = true) →
      (t.chunks.map (chunkClips key chunkAt a)).flatten = ((t.near A b).map (chunkClips key chunkAt a)).flatten := by
  intro t
  induction t with
  | empty => intro _ _ _; rfl
  | leaf is =>
    intro b hb hv
    by_cases hn : positiveCell (intersection A (reflectCell b)) = true
    · simp only [Trie.chunks, Trie.near, hn, ite_true]
    · have far : positiveCell (intersection A (reflectCell b)) = false := by simpa using hn
      simp only [Trie.chunks, Trie.near, far, Bool.false_eq_true, ite_false, List.map_nil, List.flatten_nil]
      exact flatten_map_nil _ is fun i hi =>
        chunkClips_far key chunkAt ha i (hv (i, b) (List.mem_map.mpr ⟨i, hi, rfl⟩)) (insideCheck_self b) far
  | split n l r ihl ihr =>
    intro b hb hv
    by_cases hn : positiveCell (intersection A (reflectCell b)) = true
    · simp only [Trie.chunks, Trie.near, hn, ite_true, List.map_append, List.flatten_append]
      rw [ihl _ (orderedCell_dchild hb n false) fun x hx => hv x (List.mem_append_left _ hx),
        ihr _ (orderedCell_dchild hb n true) fun x hx => hv x (List.mem_append_right _ hx)]
    · have far : positiveCell (intersection A (reflectCell b)) = false := by simpa using hn
      simp only [Trie.near, far, Bool.false_eq_true, ite_false, List.map_nil, List.flatten_nil]
      refine flatten_map_nil _ _ fun i hi => ?_
      obtain ⟨c, hc⟩ := Trie.mem_leafCells_chunks (.split n l r) b i hi
      exact chunkClips_far key chunkAt ha i (hv _ hc) (Trie.leafCells_inside _ b hb _ hc) far
  | pair l r ihl ihr =>
    intro b hb hv
    by_cases hn : positiveCell (intersection A (reflectCell b)) = true
    · simp only [Trie.chunks, Trie.near, hn, ite_true, List.map_append, List.flatten_append]
      rw [ihl b hb fun x hx => hv x (List.mem_append_left _ hx),
        ihr b hb fun x hx => hv x (List.mem_append_right _ hx)]
    · have far : positiveCell (intersection A (reflectCell b)) = false := by simpa using hn
      simp only [Trie.near, far, Bool.false_eq_true, ite_false, List.map_nil, List.flatten_nil]
      refine flatten_map_nil _ _ fun i hi => ?_
      obtain ⟨c, hc⟩ := Trie.mem_leafCells_chunks (.pair l r) b i hi
      exact chunkClips_far key chunkAt ha i (hv _ hc) (Trie.leafCells_inside _ b hb _ hc) far

/-- **The mirror over a trie.** If the old held list is the trie's chunks in order and every
chunk is checked, each positive atom's clips are its clips with the chunks its own cell's
search keeps. -/
theorem mirror_trie (key : Key → Key → Key) (old positive : Snapshot) (t : Trie)
    (chunkAt : ℕ → List AddressedCell) (held : old.held = (t.chunks.map chunkAt).flatten)
    (valid : ∀ x ∈ t.leafCells root, Trie.checkChunk chunkAt x = true)
    (admissible : ((halvesCheck old &&
        positive.held.all (fun a => positiveCell a.cell && decide (0 ≤ a.cell.lo 5))) &&
      (reflectedRoster (nonpositive old.held)).all fun a => positiveCell a.cell) = true) :
    mirror key old positive = some ⟨positive.paid ++ reflectedRoster old.paid,
      positive.held.flatMap fun a => ((t.near a.cell root).map (chunkClips key chunkAt a)).flatten⟩ := by
  have e : ∀ a ∈ positive.held, ((t.chunks.map chunkAt).map fun ch =>
      (reflectedRoster (nonpositive ch)).filterMap (clipOf key a)).flatten =
      ((t.near a.cell root).map (chunkClips key chunkAt a)).flatten := by
    intro a _
    rw [List.map_map]
    exact Trie.clips_near key chunkAt a a.cell (insideCheck_self a.cell) t root root_ordered valid
  rw [mirror_chunks key old positive (t.chunks.map chunkAt) held admissible, flatMap_congr' e]

end DataPath.LaterMirror

end BccSharp.Coulomb.CompactCover
