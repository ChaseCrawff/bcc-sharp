import BccSharp.Cover.OverlayCorpusTrace

set_option autoImplicit false

/-! Kernel-friendly literal data for the cover replay.

The two-site theorem `Statement` never mentions the JSON data: the kernel only has to check that
some literal data forms a valid cover. This module gives the format of that data and the
generic facts that make its geometry free in the kernel.

* **Packed streams.** A tree is a natural number read from its least significant digit in
  radix 17, one symbol per digit, in preorder (low child first). Symbols are `1`–`15`; `0`
  ends the stream. The `.olean` stores about half a byte per node. Radix 17 rather than 16:
  the kernel hashes a natural-number literal by its low 64 bits, and the Direct streams are
  periodic, so in radix 16 the successive values `s / 16^k` of one stream share their hashes
  and the kernel's caches degrade; a power of 17 mixes every digit into the low bits.
* **Replacement trees** (`DataPath.tree`): `1`–`8` a dyadic split on axis `0`–`7`, `9` a
  hold whose key is derived from the parent's by `slotChild` (as `decodePlan` derives it),
  `10 + i` a closed leaf with witness `ws[i]`. `Tree.beq` compares a decoded tree with a
  tree literal in one kernel evaluation (`Tree.eq_of_beq`).
* **Geometry without evaluation.** A dyadic cut fits every cell with ordered endpoints, and
  its children are ordered again (`fits_dyadic`, `orderedCell_child`). So a tree with only
  dyadic cuts passes `Tree.check check b` when `check` accepts every closed leaf on its
  cell (`Tree.check_of_closes`), and its plan then runs with the tree's held list
  (`Tree.toPlan_run_of_closes`). The arithmetic at the closed leaves is the only
  parameter; no cut, midpoint or cell is evaluated. The decoders only make dyadic cuts
  (`tree_dyadic`, `shard_dyadic`, `Skel.plug_dyadic`).
* **Shards** (`Skel`, `Skel.plug`, `Skel.slots`): a skeleton of splits whose leaves are
  shard slots, filled in order from a list of trees. Held cells, closed leaves and hold keys
  of the plugged tree are those of the shards on their slot cells, in order
  (`Skel.plug_holds`, `Skel.plug_closes`, `Tree.keys_plug`), so kernel checks split by
  shard.
* **The Direct root format** (`Direct.shard`): symbols `9` a `hold_owner` leaf, `10` an
  `invalid_reduced` leaf, `11` `energy_direct`, `12` `energy_above_fcc`; the owner of a leaf
  is the next owner number of its depth, read from a counter word (21-bit fields: a running
  leaf count, then depths 9, 10, …) and bumped after the leaf. The Direct archive numbers its
  leaves by depth, then by split word, so per-shard counter words give the archive numbers
  without storing any.
* **Distinct keys** (`keyCheck`, `nodup_of_keyCheck`): keys `⟨o, "", 0, []⟩` whose owners
  appear in strictly increasing order within every class (any function of the number) are
  duplicate free. The state is packed in one natural number (`slot`, `setSlot`), and the
  check splits at literal intermediate states (`keyCheck_append`), so one check over a long
  list becomes several bounded kernel evaluations.
* **Reach** (`Tree.reachHold`, `Tree.reachHold_mem`): the hold reached along a word of
  split digits is held at `descend b word`. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay OverlayPlanar OverlayCorpus

/-! ### Trees: dyadic cuts, closed leaves, keys, reach and equality -/

/-- Every cut of the tree is dyadic. -/
def Tree.Dyadic : Tree → Prop
  | .close _ => True
  | .hold _ => True
  | .split (.dyadic _) l r => l.Dyadic ∧ r.Dyadic
  | .split (.rational _ _) _ _ => False

/-- The closed leaves of a tree on the cell `b`, with their cells, in decode order. -/
def Tree.closes (b : Cell) : Tree → List (WitnessRef × Cell)
  | .close w => [(w, b)]
  | .hold _ => []
  | .split cut l r => l.closes (cut.child b false) ++ r.closes (cut.child b true)

/-- The keys of the holds of a tree, in decode order. -/
def Tree.keys : Tree → List Key
  | .close _ => []
  | .hold k => [k]
  | .split _ l r => l.keys ++ r.keys

theorem Tree.holds_keys : ∀ (t : Tree) (b : Cell), (t.holds b).map AddressedCell.key = t.keys
  | .close _, _ => rfl
  | .hold _, _ => rfl
  | .split cut l r, b => by
    simp only [Tree.holds, Tree.keys, List.map_append, Tree.holds_keys l, Tree.holds_keys r]

/-- The keys of a tree consed onto a list, without nested appends. -/
def Tree.keysOnto : Tree → List Key → List Key
  | .close _, acc => acc
  | .hold k, acc => k :: acc
  | .split _ l r, acc => l.keysOnto (r.keysOnto acc)

theorem Tree.keysOnto_eq : ∀ (t : Tree) (acc : List Key), t.keysOnto acc = t.keys ++ acc
  | .close _, _ => rfl
  | .hold _, _ => rfl
  | .split _ l r, acc => by
    simp only [Tree.keysOnto, Tree.keys, Tree.keysOnto_eq l, Tree.keysOnto_eq r, List.append_assoc]

/-- A cell whose endpoints are ordered on every axis. -/
def OrderedCell (b : Cell) : Prop := ∀ i, b.lo i ≤ b.hi i

theorem fits_dyadic {b : Cell} (h : OrderedCell b) (a : Axis) : (Cut.dyadic a).fits b = true := by
  have ha := h a
  simp only [Cut.fits, Cut.position, midpoint]
  exact decide_eq_true ⟨by linarith, by linarith⟩

theorem orderedCell_child {b : Cell} (h : OrderedCell b) (a : Axis) (u : Bool) :
    OrderedCell ((Cut.dyadic a).child b u) := by
  intro i
  have hi := h i
  have ha := h a
  simp only [Cut.child, Cut.position, replaceEnd, midpoint]
  by_cases e : i = a
  · subst e
    cases u <;> simp <;> linarith
  · cases u <;> simp [e] <;> exact hi

theorem orderedCell_descend : ∀ (word : List ℕ) {b : Cell}, OrderedCell b → OrderedCell (descend b word)
  | [], _, h => h
  | d :: ds, b, h => orderedCell_descend ds (orderedCell_child h ⟨d / 2 % 8, Nat.mod_lt _ (by decide)⟩ _)

theorem root_ordered : OrderedCell root := by
  intro i
  fin_cases i <;> norm_num [root]

/-- A dyadic tree passes `Tree.check` when `check` accepts every closed leaf on its cell:
no cut is evaluated. -/
theorem Tree.check_of_closes {check : WitnessRef → Cell → Bool} :
    ∀ (t : Tree) (b : Cell), OrderedCell b → t.Dyadic → (∀ x ∈ t.closes b, check x.1 x.2 = true) →
      t.check check b = true
  | .close w, b, _, _, hc => hc (w, b) (by simp [Tree.closes])
  | .hold _, _, _, _, _ => rfl
  | .split (.dyadic a) l r, b, hb, hd, hc => by
    have hl := Tree.check_of_closes l _ (orderedCell_child hb a false) hd.1
      (fun x hx => hc x (List.mem_append_left _ hx))
    have hr := Tree.check_of_closes r _ (orderedCell_child hb a true) hd.2
      (fun x hx => hc x (List.mem_append_right _ hx))
    simp only [Tree.check, fits_dyadic hb, hl, hr, Bool.and_self]
  | .split (.rational _ _) _ _, _, _, hd, _ => hd.elim

theorem Tree.witnessesAll_true : ∀ t : Tree, t.witnessesAll (fun _ => true) = true
  | .close _ => rfl
  | .hold _ => rfl
  | .split _ l r => by simp only [Tree.witnessesAll, Tree.witnessesAll_true l, Tree.witnessesAll_true r, Bool.and_self]

/-- **Run theorem.** The plan of a dyadic tree on an ordered cell runs under any check that
accepts every closed leaf on its cell, and holds exactly the tree's held cells. -/
theorem Tree.toPlan_run_of_closes {check : WitnessRef → Cell → Bool} (t : Tree) (b : Cell) (k : Key)
    (hb : OrderedCell b) (hd : t.Dyadic) (hc : ∀ x ∈ t.closes b, check x.1 x.2 = true) :
    ∃ paid, (t.toPlan b k).run check b = some ⟨paid, t.holds b⟩ :=
  Tree.toPlan_run (check := check) (check' := check) (P := fun _ => true) (fun _ _ _ h => h) t b k
    (Tree.witnessesAll_true t) (Tree.check_of_closes t b hb hd hc)

/-- The key of the hold reached along a word of split digits (digit `2a` to the low,
`2a+1` to the high child of a dyadic split on axis `a`). -/
def Tree.reachHold : Tree → List ℕ → Option Key
  | .hold k, [] => some k
  | .split (.dyadic a) l r, d :: ds =>
    if d = 2 * a.val then l.reachHold ds else if d = 2 * a.val + 1 then r.reachHold ds else none
  | _, _ => none

theorem Tree.reachHold_mem : ∀ (t : Tree) (word : List ℕ) (b : Cell) (k : Key),
    t.reachHold word = some k → (⟨k, descend b word⟩ : AddressedCell) ∈ t.holds b
  | .hold k', [], b, k, h => by
    have e : k' = k := by simpa [Tree.reachHold] using h
    subst e
    simp [Tree.holds, descend]
  | .close _, [], _, _, h => by simp [Tree.reachHold] at h
  | .split _ _ _, [], _, _, h => by simp [Tree.reachHold] at h
  | .close _, _ :: _, _, _, h => by simp [Tree.reachHold] at h
  | .hold _, _ :: _, _, _, h => by simp [Tree.reachHold] at h
  | .split (.rational _ _) _ _, _ :: _, _, _, h => by simp [Tree.reachHold] at h
  | .split (.dyadic a) l r, d :: ds, b, k, h => by
    by_cases h0 : d = 2 * a.val
    · subst h0
      have hl : l.reachHold ds = some k := by simpa [Tree.reachHold] using h
      have m := Tree.reachHold_mem l ds ((Cut.dyadic a).child b false) k hl
      rw [descend_cons, digitChild_low]
      exact List.mem_append_left _ m
    · by_cases h1 : d = 2 * a.val + 1
      · subst h1
        have hr : r.reachHold ds = some k := by simpa [Tree.reachHold, h0] using h
        have m := Tree.reachHold_mem r ds ((Cut.dyadic a).child b true) k hr
        rw [descend_cons, digitChild_high]
        exact List.mem_append_right _ m
      · simp [Tree.reachHold, h0, h1] at h

/-- Structural equality of cuts, decided in the kernel. -/
def Cut.beq : Cut → Cut → Bool
  | .dyadic a, .dyadic b => decide (a = b)
  | .rational a v, .rational b u => decide (a = b) && decide (v = u)
  | _, _ => false

theorem Cut.eq_of_beq : ∀ {c d : Cut}, c.beq d = true → c = d
  | .dyadic a, .dyadic b, h => by
    have e : a = b := of_decide_eq_true h
    rw [e]
  | .rational a v, .rational b u, h => by
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    rw [of_decide_eq_true h1, of_decide_eq_true h2]
  | .dyadic _, .rational _ _, h => by simp [Cut.beq] at h
  | .rational _ _, .dyadic _, h => by simp [Cut.beq] at h

/-- Structural equality of trees, decided in the kernel. -/
def Tree.beq : Tree → Tree → Bool
  | .close w, .close v => decide (w = v)
  | .hold k, .hold j => decide (k = j)
  | .split c l r, .split d l' r' => c.beq d && (l.beq l' && r.beq r')
  | _, _ => false

theorem Tree.eq_of_beq : ∀ {t u : Tree}, t.beq u = true → t = u
  | .close w, .close v, h => by rw [of_decide_eq_true h]
  | .hold k, .hold j, h => by rw [of_decide_eq_true h]
  | .split c l r, .split d l' r', h => by
    obtain ⟨hc, hlr⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hlr
    rw [Cut.eq_of_beq hc, Tree.eq_of_beq hl, Tree.eq_of_beq hr]
  | .close _, .hold _, h => by simp [Tree.beq] at h
  | .close _, .split _ _ _, h => by simp [Tree.beq] at h
  | .hold _, .close _, h => by simp [Tree.beq] at h
  | .hold _, .split _ _ _, h => by simp [Tree.beq] at h
  | .split _ _ _, .close _, h => by simp [Tree.beq] at h
  | .split _ _ _, .hold _, h => by simp [Tree.beq] at h

namespace DataPath

/-! ### Packed streams and replacement trees -/

/-- The axis of a split symbol `1`–`8`. -/
def axisOf (c : ℕ) : Axis := ⟨(c - 1) % 8, Nat.mod_lt _ (by decide)⟩

/-- The leaf put where a stream ends early, runs out of fuel or names no witness. A hold
with the seed `"error"` stays in the held list, where it is visible. -/
def errTree : Tree := .hold ⟨0, "error", 0, []⟩

/-- A packed replacement tree with fuel `n`, parent key `k` and stream `s`: the tree and
the rest of the stream. Symbols: `1`–`8` a dyadic split on axis `0`–`7`, `9` a hold with
the derived key, `10 + i` a closed leaf with witness `ws[i]`. -/
def tree (ws : List WitnessRef) : ℕ → Key → ℕ → Tree × ℕ
  | 0, _, s => (errTree, s)
  | n + 1, k, s =>
    let c := s % 17
    if c = 0 then (errTree, s)
    else if c ≤ 8 then
      let L := tree ws n (slotChild k (axisOf c) false) (s / 17)
      let H := tree ws n (slotChild k (axisOf c) true) L.2
      (.split (.dyadic (axisOf c)) L.1 H.1, H.2)
    else if c = 9 then (.hold k, s / 17)
    else
      match ws[c - 10]? with
      | some w => (.close w, s / 17)
      | none => (errTree, s / 17)

theorem tree_dyadic (ws : List WitnessRef) : ∀ (n : ℕ) (k : Key) (s : ℕ), (tree ws n k s).1.Dyadic
  | 0, _, _ => trivial
  | n + 1, k, s => by
    simp only [tree]
    split_ifs
    · trivial
    · exact ⟨tree_dyadic ws n _ _, tree_dyadic ws n _ _⟩
    · trivial
    · split <;> trivial

/-! ### Shards -/

/-- A skeleton of dyadic splits whose leaves are shard slots. -/
inductive Skel where
  | shard
  | split (a : Axis) (l r : Skel)

namespace Skel

/-- The number of shard slots. -/
def count : Skel → ℕ
  | .shard => 1
  | .split _ l r => l.count + r.count

/-- Fill the shard slots with the trees of a list, in order; return the rest of the list. -/
def plug : Skel → List Tree → Tree × List Tree
  | .shard, t :: ts => (t, ts)
  | .shard, [] => (errTree, [])
  | .split a l r, ts =>
    let L := l.plug ts
    let H := r.plug L.2
    (.split (.dyadic a) L.1 H.1, H.2)

/-- The slots of `plug` on the cell `b`: each slot's cell and the tree put there. -/
def slots (b : Cell) : Skel → List Tree → List (Cell × Tree) × List Tree
  | .shard, t :: ts => ([(b, t)], ts)
  | .shard, [] => ([(b, errTree)], [])
  | .split a l r, ts =>
    let L := l.slots ((Cut.dyadic a).child b false) ts
    let H := r.slots ((Cut.dyadic a).child b true) L.2
    (L.1 ++ H.1, H.2)

/-- The split words of the shard slots. -/
def paths : Skel → List (List ℕ)
  | .shard => [[]]
  | .split a l r => l.paths.map (List.cons (2 * a.val)) ++ r.paths.map (List.cons (2 * a.val + 1))

/-- The depths of the shard slots, below a skeleton at depth `d`. -/
def depths (d : ℕ) : Skel → List ℕ
  | .shard => [d]
  | .split _ l r => l.depths (d + 1) ++ r.depths (d + 1)

theorem plug_snd (b : Cell) : ∀ (s : Skel) (ts : List Tree), (s.plug ts).2 = (s.slots b ts).2
  | .shard, [] => rfl
  | .shard, _ :: _ => rfl
  | .split a l r, ts => by
    simp only [plug, slots]
    rw [plug_snd ((Cut.dyadic a).child b false) l ts, plug_snd ((Cut.dyadic a).child b true) r]

theorem plug_holds : ∀ (s : Skel) (b : Cell) (ts : List Tree),
    (s.plug ts).1.holds b = (s.slots b ts).1.flatMap fun x => x.2.holds x.1
  | .shard, b, [] => by simp [plug, slots]
  | .shard, b, _ :: _ => by simp [plug, slots]
  | .split a l r, b, ts => by
    simp only [plug, slots, Tree.holds, List.flatMap_append]
    rw [plug_holds l, plug_holds r, plug_snd ((Cut.dyadic a).child b false) l ts]

theorem plug_closes : ∀ (s : Skel) (b : Cell) (ts : List Tree),
    (s.plug ts).1.closes b = (s.slots b ts).1.flatMap fun x => x.2.closes x.1
  | .shard, b, [] => by simp [plug, slots]
  | .shard, b, _ :: _ => by simp [plug, slots]
  | .split a l r, b, ts => by
    simp only [plug, slots, Tree.closes, List.flatMap_append]
    rw [plug_closes l, plug_closes r, plug_snd ((Cut.dyadic a).child b false) l ts]

/-- The trees in the slots are the first `count` trees of the list. -/
theorem slots_trees : ∀ (s : Skel) (b : Cell) (ts : List Tree), s.count ≤ ts.length →
    (s.slots b ts).1.map Prod.snd = ts.take s.count ∧ (s.slots b ts).2 = ts.drop s.count
  | .shard, b, [], h => by simp [count] at h
  | .shard, b, t :: ts, _ => by simp [slots, count]
  | .split a l r, b, ts, h => by
    simp only [count] at h
    obtain ⟨hl1, hl2⟩ := slots_trees l ((Cut.dyadic a).child b false) ts (by omega)
    have hlen : r.count ≤ (ts.drop l.count).length := by simp; omega
    obtain ⟨hr1, hr2⟩ := slots_trees r ((Cut.dyadic a).child b true) (ts.drop l.count) hlen
    simp only [slots, List.map_append]
    rw [hl2, hl1, hr1, hr2, List.drop_drop]
    simp only [count]
    exact ⟨(List.take_add ..).symm, trivial⟩

/-- The cells of the slots are the root cell along the slots' split words. -/
theorem slots_cells : ∀ (s : Skel) (b : Cell) (ts : List Tree),
    (s.slots b ts).1.map Prod.fst = s.paths.map (descend b)
  | .shard, b, [] => by simp [slots, paths, descend]
  | .shard, b, _ :: _ => by simp [slots, paths, descend]
  | .split a l r, b, ts => by
    simp only [slots, paths, List.map_append, List.map_map]
    rw [slots_cells l, slots_cells r]
    congr 1
    · exact List.map_congr_left fun p _ => by
        simp only [Function.comp, descend_cons, digitChild_low]
    · exact List.map_congr_left fun p _ => by
        simp only [Function.comp, descend_cons, digitChild_high]

theorem plug_dyadic_aux : ∀ (s : Skel) (ts : List Tree), (∀ t ∈ ts, t.Dyadic) →
    (s.plug ts).1.Dyadic ∧ ∀ t ∈ (s.plug ts).2, t.Dyadic
  | .shard, [], _ => ⟨trivial, fun _ h => absurd h List.not_mem_nil⟩
  | .shard, t :: _, h => ⟨h t List.mem_cons_self, fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
  | .split a l r, ts, h => by
    obtain ⟨hl, hl2⟩ := plug_dyadic_aux l ts h
    obtain ⟨hr, hr2⟩ := plug_dyadic_aux r _ hl2
    exact ⟨⟨hl, hr⟩, hr2⟩

theorem plug_dyadic (s : Skel) (ts : List Tree) (h : ∀ t ∈ ts, t.Dyadic) : (s.plug ts).1.Dyadic :=
  (plug_dyadic_aux s ts h).1

/-- A skeleton in a packed stream: `1`–`8` a split on axis `0`–`7`; any other symbol, the
end of the stream and exhausted fuel all give a shard slot (the data uses `13`). A malformed
skeleton is caught by the kernel checks on the data, not by the decoder. -/
def decode : ℕ → ℕ → Skel × ℕ
  | 0, s => (.shard, s)
  | n + 1, s =>
    let c := s % 17
    if 1 ≤ c ∧ c ≤ 8 then
      let L := decode n (s / 17)
      let H := decode n L.2
      (.split (axisOf c) L.1 H.1, H.2)
    else (.shard, s / 17)

end Skel

theorem Tree.keys_plug (s : Skel) (ts : List Tree) (h : s.count ≤ ts.length) :
    (s.plug ts).1.keys = (ts.take s.count).flatMap Tree.keys := by
  rw [← Tree.holds_keys _ root, Skel.plug_holds, List.map_flatMap, ← (Skel.slots_trees s root ts h).1,
    List.flatMap_map]
  exact List.flatMap_congr fun x _ => Tree.holds_keys x.2 x.1

/-! ### Distinct keys by classes

The check keeps, for each class of owner numbers, the least number the next owner of that class
may have, in 21-bit slots of one natural number. A list state (`List.set`, `List.getD`) needed
more than 9 GB of kernel memory on 30,000 keys; the packed state needs about 2.5 GB. -/

/-- Slot `c` (21 bits) of a packed state. -/
def slot (st c : ℕ) : ℕ := st / 2 ^ (21 * c) % 2 ^ 21

/-- Raise slot `c` of a packed state to `v`. -/
def setSlot (st c v : ℕ) : ℕ := st + (v - slot st c) * 2 ^ (21 * c)

theorem slot_setSlot (st c c' v : ℕ) (hv : v < 2 ^ 21) (hs : slot st c ≤ v) :
    slot (setSlot st c v) c' = if c' = c then v else slot st c' := by
  simp only [setSlot, slot] at *
  have hP : 0 < 2 ^ (21 * c) := by positivity
  by_cases e : c' = c
  · subst e
    rw [ite_eq_left rfl, Nat.add_mul_div_right _ _ hP]
    generalize st / 2 ^ (21 * c') = X at *
    omega
  · rw [ite_eq_right e]
    rcases Nat.lt_or_gt_of_ne e with lt | gt
    · -- A lower slot: the change is a multiple of `2^21` units of that slot.
      have hP' : 0 < 2 ^ (21 * c') := by positivity
      have split : 2 ^ (21 * c) = 2 ^ (21 * c') * (2 ^ (21 * (c - c' - 1)) * 2 ^ 21) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      generalize v - st / 2 ^ (21 * c) % 2 ^ 21 = δ
      rw [split, show δ * (2 ^ (21 * c') * (2 ^ (21 * (c - c' - 1)) * 2 ^ 21)) =
          δ * 2 ^ (21 * (c - c' - 1)) * 2 ^ 21 * 2 ^ (21 * c') by ring,
        Nat.add_mul_div_right _ _ hP', Nat.add_mul_mod_self_right]
    · -- A higher slot: the change stays below it.
      have hPB : 0 < 2 ^ (21 * c) * 2 ^ 21 := by positivity
      have hQ : 2 ^ (21 * c') = 2 ^ (21 * c) * 2 ^ 21 * 2 ^ (21 * (c' - c - 1)) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have hmod : st % (2 ^ (21 * c) * 2 ^ 21) =
          2 ^ (21 * c) * (st / 2 ^ (21 * c) % 2 ^ 21) + st % 2 ^ (21 * c) := by
        have := Nat.div_add_mod (st % (2 ^ (21 * c) * 2 ^ 21)) (2 ^ (21 * c))
        rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod] at this
        exact this.symm
      have hr : st % 2 ^ (21 * c) < 2 ^ (21 * c) := Nat.mod_lt _ hP
      generalize hs' : st / 2 ^ (21 * c) % 2 ^ 21 = s at hs hmod
      have low : st % (2 ^ (21 * c) * 2 ^ 21) + (v - s) * 2 ^ (21 * c) < 2 ^ (21 * c) * 2 ^ 21 := by
        rw [hmod]
        have h1 : 2 ^ (21 * c) * s + st % 2 ^ (21 * c) + (v - s) * 2 ^ (21 * c) =
            v * 2 ^ (21 * c) + st % 2 ^ (21 * c) := by
          rw [Nat.mul_comm (2 ^ (21 * c)) s, Nat.add_right_comm, ← Nat.add_mul, Nat.add_sub_cancel' hs]
        rw [h1]
        calc v * 2 ^ (21 * c) + st % 2 ^ (21 * c) < v * 2 ^ (21 * c) + 2 ^ (21 * c) := by omega
          _ = (v + 1) * 2 ^ (21 * c) := by ring
          _ ≤ 2 ^ 21 * 2 ^ (21 * c) := Nat.mul_le_mul_right _ hv
          _ = 2 ^ (21 * c) * 2 ^ 21 := Nat.mul_comm _ _
      generalize (v - s) * 2 ^ (21 * c) = δ at low ⊢
      have key : st + δ = (st % (2 ^ (21 * c) * 2 ^ 21) + δ) +
          st / (2 ^ (21 * c) * 2 ^ 21) * (2 ^ (21 * c) * 2 ^ 21) := by
        have := Nat.mod_add_div st (2 ^ (21 * c) * 2 ^ 21)
        rw [Nat.mul_comm (st / _)]
        omega
      have same : (st + δ) / (2 ^ (21 * c) * 2 ^ 21) = st / (2 ^ (21 * c) * 2 ^ 21) := by
        rw [key, Nat.add_mul_div_right _ _ hPB, Nat.div_eq_of_lt low, Nat.zero_add]
      rw [hQ, ← Nat.div_div_eq_div_mul, same, Nat.div_div_eq_div_mul]

/-- The class-monotone check of a list of keys from the packed state `st`: every key is
`⟨o, "", 0, []⟩` with `o + 1 < 2^21`, and `o` is at least the slot of its class, which then
moves to `o + 1`. A direct recursion: each step is decided before the next. -/
def keyCheck (cls : ℕ → ℕ) : ℕ → List Key → Option ℕ
  | st, [] => some st
  | st, k :: ks =>
    if k.seed = "" ∧ k.replacement = 0 ∧ k.path = [] ∧ k.original + 1 < 2 ^ 21 ∧
        slot st (cls k.original) ≤ k.original then
      keyCheck cls (setSlot st (cls k.original) (k.original + 1)) ks
    else none

theorem keyCheck_append (cls : ℕ → ℕ) :
    ∀ (xs ys : List Key) (st : ℕ), keyCheck cls st (xs ++ ys) = (keyCheck cls st xs).bind fun s => keyCheck cls s ys
  | [], ys, st => rfl
  | k :: xs, ys, st => by
    simp only [List.cons_append, keyCheck]
    split_ifs
    · exact keyCheck_append cls xs ys _
    · rfl

theorem keyCheck_spec (cls : ℕ → ℕ) : ∀ (ks : List Key) (st st' : ℕ), keyCheck cls st ks = some st' →
    (∀ k ∈ ks, k = ⟨k.original, "", 0, []⟩) ∧ (ks.map Key.original).Nodup ∧
      ∀ k ∈ ks, slot st (cls k.original) ≤ k.original
  | [], _, _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | k :: ks, st, st', h => by
    simp only [keyCheck] at h
    split_ifs at h with ok
    obtain ⟨fs, fr, fp, fit, ge⟩ := ok
    obtain ⟨form, nd, bound⟩ := keyCheck_spec cls ks _ st' h
    have upd : ∀ c', slot (setSlot st (cls k.original) (k.original + 1)) c' =
        if c' = cls k.original then k.original + 1 else slot st c' :=
      fun c' => slot_setSlot st _ c' _ fit (by omega)
    have step : ∀ k' ∈ ks, cls k'.original = cls k.original → k.original + 1 ≤ k'.original := by
      intro k' hk' hc
      have b := bound k' hk'
      rwa [upd, ite_eq_left hc] at b
    refine ⟨fun k' hk' => ?_, ?_, fun k' hk' => ?_⟩
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · cases k'
        simp only at fs fr fp
        subst fs fr fp
        rfl
      · exact form k' hk'
    · refine List.nodup_cons.mpr ⟨fun mem => ?_, nd⟩
      obtain ⟨k', hk', e⟩ := List.mem_map.mp mem
      have := step k' hk' (by rw [e])
      omega
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · exact ge
      · by_cases hc : cls k'.original = cls k.original
        · have := step k' hk' hc
          rw [hc]
          omega
        · have b := bound k' hk'
          rwa [upd, ite_eq_right hc] at b

/-- A successful check: the keys are distinct. -/
theorem nodup_of_keyCheck (cls : ℕ → ℕ) (ks : List Key) (st st' : ℕ) (h : keyCheck cls st ks = some st') :
    ks.Nodup := by
  obtain ⟨form, nd, -⟩ := keyCheck_spec cls ks st st' h
  have e : ks = (ks.map Key.original).map fun o => (⟨o, "", 0, []⟩ : Key) := by
    rw [List.map_map]
    exact ((List.map_congr_left fun k hk => (form k hk).symm).trans (List.map_id ks)).symm
  rw [e]
  exact nd.map fun a b hab => by simpa using hab

theorem flatMap_keys_foldr (f : ℕ × ℕ → Tree) (xs : List (ℕ × ℕ)) :
    (xs.map f).flatMap Tree.keys = xs.foldr (fun x acc => (f x).keysOnto acc) [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.flatMap_cons, List.foldr_cons, ih, Tree.keysOnto_eq]

theorem Skel.paths_length : ∀ s : Skel, s.paths.length = s.count
  | .shard => rfl
  | .split _ l r => by
    simp only [Skel.paths, Skel.count, List.length_append, List.length_map, Skel.paths_length l,
      Skel.paths_length r]

/-- Two lists of length `n`, zipped, read by index. -/
theorem zip_eq_range {α β : Type} (xs : List α) (ys : List β) (n : ℕ) (hx : xs.length = n) (hy : ys.length = n)
    (dx : α) (dy : β) : xs.zip ys = (List.range n).map fun i => (xs.getD i dx, ys.getD i dy) := by
  apply List.ext_getElem
  · simp [hx, hy]
  · intro i h1 h2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
    have hi : i < n := by simpa using h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < xs.length by omega),
      List.getElem?_eq_getElem (show i < ys.length by omega)]

/-- A check holds on a list when it holds on the consecutive chunks of length `n` that cover
it: a long kernel check splits into bounded ones. -/
theorem all_of_chunks {α : Type} (p : α → Bool) (n : ℕ) :
    ∀ (m : ℕ) (L : List α), L.length ≤ m * n → (∀ k < m, ((L.drop (k * n)).take n).all p = true) →
      L.all p = true
  | 0, L, hl, _ => by
    have e : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [e]
  | m + 1, L, hl, h => by
    have h0 := h 0 (Nat.succ_pos m)
    simp only [Nat.zero_mul, List.drop_zero] at h0
    have hr : (L.drop n).all p = true :=
      all_of_chunks p n m (L.drop n) (by rw [List.length_drop]; rw [Nat.succ_mul] at hl; omega) fun k hk => by
        have hk' := h (k + 1) (by omega)
        rwa [Nat.succ_mul, Nat.add_comm, ← List.drop_drop] at hk'
    rw [← List.take_append_drop n L, List.all_append, h0, hr]
    rfl

/-- Elementwise sublists flatten to a sublist. -/
theorem flatten_map_sublist {α : Type} (f g : ℕ → List α) (h : ∀ i, (f i).Sublist (g i)) :
    ∀ L : List ℕ, ((L.map f).flatten).Sublist ((L.map g).flatten)
  | [] => List.Sublist.slnil
  | i :: L => by
    simp only [List.map_cons, List.flatten_cons]
    exact (h i).append (flatten_map_sublist f g h L)

/-! ### The Direct root format -/

namespace Direct

/-- The original Direct frontier, the source of every Direct root witness. -/
def bank : String := originalDirectBank

/-- The next owner number of depth `d` in a counter word. The word has 21-bit fields: the
lowest counts the leaves decoded so far, the next ones hold the next owner number of depths 9,
10, 11, …; the running count keeps every counter word distinct in its low bits. -/
def field (h d : ℕ) : ℕ := h / 2 ^ (21 * (d - 8)) % 2 ^ 21

/-- The counter word after a leaf of depth `d`. -/
def bump (h d : ℕ) : ℕ := h + 1 + 2 ^ (21 * (d - 8))

/-- A Direct leaf of symbol `c` and owner `o`, as `decodePlan` reads the leaf:
`hold_owner` holds `⟨o, "", 0, []⟩`; `invalid_reduced` is the reduction witness of `o`;
`energy_direct` and `energy_above_fcc` are its direct witness. -/
def leafOf (c o : ℕ) : Tree :=
  if c = 9 then .hold ⟨o, "", 0, []⟩
  else if c = 10 then .close ⟨.invalidReduction, bank, o⟩
  else if c = 11 ∨ c = 12 then .close ⟨.strictFCC, bank, o⟩
  else errTree

/-- A Direct root shard with fuel `n` at depth `d`, counter word `h` and stream `s`: the tree,
the counter word and the rest of the stream. -/
def shard : ℕ → ℕ → ℕ → ℕ → Tree × ℕ × ℕ
  | 0, _, h, s => (errTree, h, s)
  | n + 1, d, h, s =>
    let c := s % 17
    if c = 0 then (errTree, h, s)
    else if c ≤ 8 then
      let L := shard n (d + 1) h (s / 17)
      let H := shard n (d + 1) L.2.1 L.2.2
      (.split (.dyadic (axisOf c)) L.1 H.1, H.2)
    else (leafOf c (field h d), bump h d, s / 17)

theorem leafOf_dyadic (c o : ℕ) : (leafOf c o).Dyadic := by
  unfold leafOf
  split_ifs <;> trivial

theorem shard_dyadic : ∀ (n d h s : ℕ), (shard n d h s).1.Dyadic
  | 0, _, _, _ => trivial
  | n + 1, d, h, s => by
    simp only [shard]
    split_ifs
    · trivial
    · exact ⟨shard_dyadic n _ _ _, shard_dyadic n _ _ _⟩
    · exact leafOf_dyadic _ _

/-- Decode fuel for a shard; the deepest shard is 11 splits deep. -/
def shardFuel : ℕ := 16

/-- A shard record `(header, stream)`: the header is the shard's depth plus 32 times its
starting counter word. -/
def shardTree (x : ℕ × ℕ) : Tree := (shard shardFuel (x.1 % 32) (x.1 / 32) x.2).1

theorem shardTree_dyadic (x : ℕ × ℕ) : (shardTree x).Dyadic := shard_dyadic _ _ _ _

/-- One endpoint of a packed shard box: the `i`-th 19-bit field `f`, read as `(f - 2^18) / 2^17`.
Every Direct shard endpoint is a multiple of `2^-17` of absolute value below `2`. -/
def unpackQ (n i : ℕ) : ℚ := (((n / 2 ^ (19 * i) % 2 ^ 19 : ℕ) : ℚ) - 2 ^ 18) / 2 ^ 17

/-- A packed shard box: the eight lower endpoints, then the eight upper ones. -/
def unpackBox (n : ℕ) : Cell := ⟨fun i => unpackQ n i.val, fun i => unpackQ n (8 + i.val)⟩

/-- The keys of a shard are all of the form `⟨o, "", 0, []⟩`; return their owners, or
`none` if a key has another form. -/
def owners : List Key → Option (List ℕ)
  | [] => some []
  | k :: ks => if k.seed = "" ∧ k.replacement = 0 ∧ k.path = [] then (owners ks).map (k.original :: ·) else none

theorem owners_eq : ∀ (ks : List Key) (os : List ℕ), owners ks = some os → ks = os.map fun o => ⟨o, "", 0, []⟩
  | [], os, h => by
    simp only [owners, Option.some.injEq] at h
    subst h
    rfl
  | k :: ks, os, h => by
    simp only [owners] at h
    split_ifs at h with hk
    · cases e : owners ks with
      | none => rw [e] at h; cases h
      | some os' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨s, r, p⟩ := hk
        rw [owners_eq ks os' e]
        cases k
        simp only at s r p
        subst s r p
        rfl

end Direct

end DataPath

end BccSharp.Coulomb.CompactCover
