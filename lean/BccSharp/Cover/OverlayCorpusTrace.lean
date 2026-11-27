import BccSharp.Cover.OverlayCorpusPrefix

set_option autoImplicit false

/-! What `decodePlan` makes of the traces around Overlay.

* **Overlay traces (glue item 3).** Each Overlay stage
  row is a JSON trace of holds, planar leaves, dyadic splits and, in the hard row,
  spliced closed trees. `Trace` is that shape. `Trace.Matches dec t j` says that `j`
  has the shape `t` as far as `decodePlan` reads it: the lookups of `tag`, `axis`,
  `low`, `high`, `leaf` and `tree`, and every leaf object decodes to its witness and has
  no string-valued `tag` (`get o "tag" Json.getStr?` fails). This is sufficient for
  `decodePlan`, not necessary (it would also pay leaves with other string tags), and
  exact for the JSON traces of the rows. Nothing else about `j` matters, so a JSON
  object parsed in any key order, and leaf objects with any further fields (the
  traces of the rows carry `seed`, `path` and the raw `record`), qualify.
  `decodePlan_matches`: `decodePlan` returns `Trace.plan`.
  Its held list is the hold paths of the trace, with the keys `slotChild` derives and
  the cells `descend` gives (`Trace.plan_holds`). `trace_holds_eq` turns a kernel check
  of a held list against hold paths into: every JSON trace with these hold paths
  decodes to a plan holding exactly that list. `Trace.json_matches`
  builds one such JSON.
* **The Direct root (glue item 4).** `JsonReach` follows a JSON trace along split digits
  and Direct root shards. `decodePlan_reach`: a decoded trace that reaches a `hold_owner`
  leaf of original `o` along `word` reaches `.hold ⟨o, "", 0, []⟩` there.
  `direct_holdOwner_held` puts the atom `⟨⟨o, "", 0, []⟩, descend b word⟩` in the held
  list of the run, and `decodeRoot_reach` starts from the entry point `decodeRoot`.
* **The Overlay stage (glue item 5).** An `OverlayRow` is a stage row with its owner, the owner's
  Direct split word, the cells it holds, the hold paths of its trace and the
  seeds Adaptive reads. `splitPass_table`: if every row's plan runs on its input cell, then
  on any snapshot whose atoms with a row's key have the row's cell, the `splitPass`
  edit with the table's rows and pass-through rows runs and passes on `stageHeld`,
  every Overlay atom replaced in place by its row's held cells. That hypothesis also holds
  on a snapshot without Overlay atoms, where the edit only passes atoms on;
  `splitPass_table_present` also assumes that every row's input is held, with
  distinct keys among the rows, and adds that every row's held cells reach the next
  stage (`splitPass_table_present_of_nodup`: the same from distinct keys in the whole
  held list). `table_held_cells` gives those cells below the Direct root,
  `table_decode_holds` and `table_input_of_direct` are items 3 and 4 for a table row. -/

namespace BccSharp.Coulomb.CompactCover.OverlayCorpus
open Lean BccSharp BccSharp.Coverage EarlyReplay PacketDecode OverlayPlanar OverlayPlanar.Fix

/-! ### One node of `decodePlan` -/

theorem bind_eq_ok {α β : Type} {e : Parse α} {f : α → Parse β} {y : β} (h : (e >>= f) = .ok y) :
    ∃ x, e = .ok x ∧ f x = .ok y := by
  cases he : e with
  | error err => rw [he] at h; cases h
  | ok x => rw [he] at h; exact ⟨x, rfl, h⟩

theorem axis_num (a : Axis) : axis (Json.num a.val) = .ok a := by
  have g : (Json.num a.val).getNat? = .ok a.val := rfl
  show ((Json.num a.val).getNat? >>= fun i =>
    if h : i < 8 then (pure ⟨i, h⟩ : Parse Axis) else throw "axis outside compact chart") = _
  rw [g]
  show (if h : a.val < 8 then (pure ⟨a.val, h⟩ : Parse Axis) else throw "axis outside compact chart") = _
  rw [dite_eq_left a.isLt]
  rfl

section Nodes
variable {dec : WitnessDecoder} {sh : String → Option Json} {n : ℕ} {b : Cell} {k : Key} {j : Json}

theorem decodePlan_zero {P : Plan} : decodePlan dec sh 0 b k j ≠ .ok P := by
  intro h
  cases h

theorem decodePlan_of_hold (tag : get j "tag" Json.getStr? = .ok "hold") :
    decodePlan dec sh (n + 1) b k j = .ok (.hold k) := by
  simp only [decodePlan, tag, bind, Except.bind]
  rfl

theorem decodePlan_of_close {o : Json} (tag : get j "tag" Json.getStr? = .ok "close")
    (leaf : j.getObjVal? "leaf" = .ok o) (notag : (get o "tag" Json.getStr?).toOption = none) :
    decodePlan dec sh (n + 1) b k j = (dec o >>= fun w => pure (.pay k ⟨w, b, identityMotion, b⟩)) := by
  simp only [decodePlan, tag, leaf, notag, bind, Except.bind]

theorem decodePlan_of_splice {o jt : Json} (tag : get j "tag" Json.getStr? = .ok "close")
    (leaf : j.getObjVal? "leaf" = .ok o) (closed : (get o "tag" Json.getStr?).toOption = some "closed_tree")
    (tree : o.getObjVal? "tree" = .ok jt) : decodePlan dec sh (n + 1) b k j = decodePlan dec sh n b k jt := by
  have e : decodePlan dec sh (n + 1) b k j = get o "tree" (decodePlan dec sh n b k) := by
    simp only [decodePlan, tag, leaf, closed, bind, Except.bind]
  rw [e]
  show (o.getObjVal? "tree" >>= decodePlan dec sh n b k) = _
  rw [tree]
  rfl

theorem decodePlan_of_split (tag : get j "tag" Json.getStr? = .ok "split") :
    decodePlan dec sh (n + 1) b k j = (get j "axis" axis >>= fun a =>
      get j "low" (decodePlan dec sh n ((Cut.dyadic a).child b false) (slotChild k a false)) >>= fun pl =>
      get j "high" (decodePlan dec sh n ((Cut.dyadic a).child b true) (slotChild k a true)) >>= fun ph =>
      pure (.split (.dyadic a) pl ph)) := by
  simp only [decodePlan, tag, bind, Except.bind]

theorem decodePlan_of_shard {s : Json} {pre : String} (tag : get j "tag" Json.getStr? = .ok "shard")
    (path : get j "path" Json.getStr? = .ok pre) (look : sh pre = some s) :
    decodePlan dec sh (n + 1) b k j = (get s "input" box >>= fun origin =>
      if (decide (pre ≠ k.seed) || !sameCell origin b) then throw "Direct root shard endpoints or prefix differ"
      else get s "trace" (decodePlan dec sh n b k)) := by
  simp only [decodePlan, tag, path, look, Option.getDM, bind, Except.bind]
  rfl

end Nodes

/-! ### Overlay traces (glue item 3) -/

/-- The JSON nodes of an Overlay trace. -/
def holdJ : Json := Json.mkObj [("tag", Json.str "hold")]
def closeJ (leaf : Json) : Json := Json.mkObj [("tag", Json.str "close"), ("leaf", leaf)]
def splitJ (a : Nat) (low high : Json) : Json :=
  Json.mkObj [("tag", Json.str "split"), ("axis", Json.num a), ("low", low), ("high", high)]
def spliceJ (tree : Json) : Json :=
  closeJ (Json.mkObj [("tag", Json.str "closed_tree"), ("tree", tree)])

/-- The shape of an Overlay trace. -/
inductive Trace where
  | hold
  | leaf (w : WitnessRef)
  | split (a : Axis) (low high : Trace)
  | splice (t : Trace)

namespace Trace

/-- `j` has the shape `t` as far as `decodePlan` reads it. -/
def Matches (dec : WitnessDecoder) : Trace → Json → Prop
  | .hold, j => get j "tag" Json.getStr? = .ok "hold"
  | .leaf w, j => get j "tag" Json.getStr? = .ok "close" ∧ ∃ o, j.getObjVal? "leaf" = .ok o ∧
      (get o "tag" Json.getStr?).toOption = none ∧ dec o = .ok w
  | .split a l h, j => get j "tag" Json.getStr? = .ok "split" ∧ get j "axis" axis = .ok a ∧
      (∃ jl, j.getObjVal? "low" = .ok jl ∧ l.Matches dec jl) ∧
      (∃ jh, j.getObjVal? "high" = .ok jh ∧ h.Matches dec jh)
  | .splice t, j => get j "tag" Json.getStr? = .ok "close" ∧ ∃ o, j.getObjVal? "leaf" = .ok o ∧
      (get o "tag" Json.getStr?).toOption = some "closed_tree" ∧
      ∃ jt, o.getObjVal? "tree" = .ok jt ∧ t.Matches dec jt

/-- A JSON of the trace; `obj p` is the object of the leaf at path `p`. -/
def json (obj : List ℕ → Json) : List ℕ → Trace → Json
  | _, .hold => holdJ
  | p, .leaf _ => closeJ (obj p)
  | p, .split a l h => splitJ a.val (l.json obj (p ++ [2 * a.val])) (h.json obj (p ++ [2 * a.val + 1]))
  | p, .splice t => spliceJ (t.json obj p)

/-- Every leaf object decodes to its witness and has no string-valued `tag`. -/
def LeavesOK (dec : WitnessDecoder) (obj : List ℕ → Json) : List ℕ → Trace → Prop
  | _, .hold => True
  | p, .leaf w => (get (obj p) "tag" Json.getStr?).toOption = none ∧ dec (obj p) = .ok w
  | p, .split a l h => l.LeavesOK dec obj (p ++ [2 * a.val]) ∧ h.LeavesOK dec obj (p ++ [2 * a.val + 1])
  | p, .splice t => t.LeavesOK dec obj p

/-- The decode fuel the trace needs. -/
def depth : Trace → ℕ
  | .hold => 1
  | .leaf _ => 1
  | .split _ l h => max l.depth h.depth + 1
  | .splice t => t.depth + 1

/-- The plan `decodePlan` makes of the trace on the cell `b` with key `k`. -/
def plan : Cell → Key → Trace → Plan
  | _, k, .hold => .hold k
  | b, k, .leaf w => .pay k ⟨w, b, identityMotion, b⟩
  | b, k, .split a l h => .split (.dyadic a) (l.plan ((Cut.dyadic a).child b false) (slotChild k a false))
      (h.plan ((Cut.dyadic a).child b true) (slotChild k a true))
  | b, k, .splice t => t.plan b k

/-- The paths of the holds, in the order of the plan's held list. -/
def holdPaths : Trace → List (List ℕ)
  | .hold => [[]]
  | .leaf _ => []
  | .split a l h => l.holdPaths.map (List.cons (2 * a.val)) ++ h.holdPaths.map (List.cons (2 * a.val + 1))
  | .splice t => t.holdPaths

end Trace

/-- has the shape of its trace. -/
theorem Trace.json_matches {dec : WitnessDecoder} {obj : List ℕ → Json} :
    ∀ (t : Trace) (p : List ℕ), t.LeavesOK dec obj p → t.Matches dec (t.json obj p)
  | .hold, _, _ => rfl
  | .leaf _, p, ok => ⟨rfl, obj p, rfl, ok.1, ok.2⟩
  | .split a l h, p, ok =>
    ⟨rfl, axis_num a, ⟨_, rfl, Trace.json_matches l (p ++ [2 * a.val]) ok.1⟩,
      ⟨_, rfl, Trace.json_matches h (p ++ [2 * a.val + 1]) ok.2⟩⟩
  | .splice t, p, ok => ⟨rfl, _, rfl, rfl, _, rfl, Trace.json_matches t p ok⟩

/-- `decodePlan` on a JSON trace of shape `t` returns the plan of `t`. -/
theorem decodePlan_matches (dec : WitnessDecoder) (sh : String → Option Json) :
    ∀ (t : Trace) (j : Json) (fuel : ℕ) (b : Cell) (k : Key), t.depth ≤ fuel → t.Matches dec j →
      decodePlan dec sh fuel b k j = .ok (t.plan b k)
  | .hold, j, fuel, b, k, hd, m => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp only [Trace.depth] at hd; omega⟩
    exact decodePlan_of_hold m
  | .leaf w, j, fuel, b, k, hd, m => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp only [Trace.depth] at hd; omega⟩
    obtain ⟨tag, o, leaf, notag, hw⟩ := m
    rw [decodePlan_of_close tag leaf notag, hw]
    rfl
  | .split a l h, j, fuel, b, k, hd, m => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp only [Trace.depth] at hd; omega⟩
    obtain ⟨tag, ax, ⟨jl, hl, ml⟩, ⟨jh, hh, mh⟩⟩ := m
    have dl : l.depth ≤ n := by simp only [Trace.depth] at hd; omega
    have dh : h.depth ≤ n := by simp only [Trace.depth] at hd; omega
    have gl : get j "low" (decodePlan dec sh n ((Cut.dyadic a).child b false) (slotChild k a false)) =
        .ok (l.plan ((Cut.dyadic a).child b false) (slotChild k a false)) := by
      show (j.getObjVal? "low" >>= _) = _
      rw [hl]
      exact decodePlan_matches dec sh l jl n _ _ dl ml
    have gh : get j "high" (decodePlan dec sh n ((Cut.dyadic a).child b true) (slotChild k a true)) =
        .ok (h.plan ((Cut.dyadic a).child b true) (slotChild k a true)) := by
      show (j.getObjVal? "high" >>= _) = _
      rw [hh]
      exact decodePlan_matches dec sh h jh n _ _ dh mh
    rw [decodePlan_of_split tag, ax]
    show (get j "low" (decodePlan dec sh n ((Cut.dyadic a).child b false) (slotChild k a false)) >>= fun pl =>
      get j "high" (decodePlan dec sh n ((Cut.dyadic a).child b true) (slotChild k a true)) >>= fun ph =>
      (pure (Plan.split (Cut.dyadic a) pl ph) : Parse Plan)) = _
    rw [gl, gh]
    rfl
  | .splice t, j, fuel, b, k, hd, m => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp only [Trace.depth] at hd; omega⟩
    obtain ⟨tag, o, leaf, closed, jt, tree, mt⟩ := m
    have dt : t.depth ≤ n := by simp only [Trace.depth] at hd; omega
    rw [decodePlan_of_splice tag leaf closed tree]
    exact decodePlan_matches dec sh t jt n b k dt mt

/-- `decodePlan` on `Trace.json` returns the plan of the trace. -/
theorem decodePlan_trace (dec : WitnessDecoder) (sh : String → Option Json) (obj : List ℕ → Json)
    (t : Trace) (p : List ℕ) (fuel : ℕ) (b : Cell) (k : Key) (hd : t.depth ≤ fuel) (ok : t.LeavesOK dec obj p) :
    decodePlan dec sh fuel b k (t.json obj p) = .ok (t.plan b k) :=
  decodePlan_matches dec sh t _ fuel b k hd (t.json_matches p ok)

/-- The axis of a split digit, as `digitChild` reads it. -/
def digitAxis (d : ℕ) : Axis := ⟨d / 2 % 8, Nat.mod_lt _ (by decide)⟩

/-- The key `decodePlan` derives along a word of split digits. -/
def deriveKey (k : Key) : List ℕ → Key
  | [] => k
  | d :: ds => deriveKey (slotChild k (digitAxis d) (decide (d % 2 = 1))) ds

/-- The held atom at the end of a word of split digits. -/
def derivedAtom (k : Key) (b : Cell) (p : List ℕ) : AddressedCell := ⟨deriveKey k p, descend b p⟩

theorem digitAxis_low (a : Axis) : digitAxis (2 * a.val) = a :=
  Fin.ext (show 2 * a.val / 2 % 8 = a.val by have := a.isLt; omega)

theorem digitAxis_high (a : Axis) : digitAxis (2 * a.val + 1) = a :=
  Fin.ext (show (2 * a.val + 1) / 2 % 8 = a.val by have := a.isLt; omega)

theorem derivedAtom_low (k : Key) (b : Cell) (a : Axis) (p : List ℕ) :
    derivedAtom k b (2 * a.val :: p) = derivedAtom (slotChild k a false) ((Cut.dyadic a).child b false) p := by
  have hs : decide (2 * a.val % 2 = 1) = false := by simp
  simp only [derivedAtom, deriveKey, digitAxis_low, hs, descend_cons, digitChild_low]

theorem derivedAtom_high (k : Key) (b : Cell) (a : Axis) (p : List ℕ) :
    derivedAtom k b ((2 * a.val + 1) :: p) = derivedAtom (slotChild k a true) ((Cut.dyadic a).child b true) p := by
  have hs : decide ((2 * a.val + 1) % 2 = 1) = true := by simp
  simp only [derivedAtom, deriveKey, digitAxis_high, hs, descend_cons, digitChild_high]

/-- The held list of a trace's plan: its hold paths, with derived keys and cells. -/
theorem Trace.plan_holds (t : Trace) :
    ∀ (b : Cell) (k : Key), (t.plan b k).holds b = t.holdPaths.map (derivedAtom k b) := by
  induction t with
  | hold => intro b k; rfl
  | leaf _ => intro b k; rfl
  | split a l h ihl ihh =>
    intro b k
    have el : (l.holdPaths.map (List.cons (2 * a.val))).map (derivedAtom k b) =
        l.holdPaths.map (derivedAtom (slotChild k a false) ((Cut.dyadic a).child b false)) := by
      rw [List.map_map]
      exact List.map_congr_left fun p _ => derivedAtom_low k b a p
    have eh : (h.holdPaths.map (List.cons (2 * a.val + 1))).map (derivedAtom k b) =
        h.holdPaths.map (derivedAtom (slotChild k a true) ((Cut.dyadic a).child b true)) := by
      rw [List.map_map]
      exact List.map_congr_left fun p _ => derivedAtom_high k b a p
    show (l.plan ((Cut.dyadic a).child b false) (slotChild k a false)).holds ((Cut.dyadic a).child b false) ++
        (h.plan ((Cut.dyadic a).child b true) (slotChild k a true)).holds ((Cut.dyadic a).child b true) =
      (l.holdPaths.map (List.cons (2 * a.val)) ++ h.holdPaths.map (List.cons (2 * a.val + 1))).map
        (derivedAtom k b)
    rw [ihl, ihh, List.map_append, el, eh]
  | splice t ih => intro b k; exact ih b k

/-- A held list that is the derived atoms of `paths`: every JSON trace of a shape with
these hold paths decodes to a plan holding exactly that list. -/
theorem trace_holds_eq {dec : WitnessDecoder} {sh : String → Option Json} {j : Json} {fuel : ℕ}
    {b : Cell} {k : Key} {t : Trace} {held : List AddressedCell} {paths : List (List ℕ)}
    (m : t.Matches dec j) (hp : t.holdPaths = paths) (hd : t.depth ≤ fuel)
    (hist : held = paths.map (derivedAtom k b)) :
    ∃ P, decodePlan dec sh fuel b k j = .ok P ∧ P.holds b = held :=
  ⟨t.plan b k, decodePlan_matches dec sh t j fuel b k hd m, by rw [Trace.plan_holds, hp, hist]⟩

/-- A stage row whose trace has the shape `t` decodes to the plan of `t` on its input atom. -/
theorem decodeStageRow_matches {dec : WitnessDecoder} {depth : ℕ} {j tr : Json} {parent : LatePackets.Atom}
    {t : Trace} (input : get j "input" atom = .ok parent) (trace : j.getObjVal? "trace" = .ok tr)
    (hd : t.depth ≤ depth) (m : t.Matches dec tr) :
    decodeStageRow dec depth j = .ok ⟨parent.asCell, t.plan parent.box parent.address⟩ := by
  have gt : get j "trace" (decodePlan dec (fun _ => none) depth parent.box parent.address) =
      .ok (t.plan parent.box parent.address) := by
    show (j.getObjVal? "trace" >>= decodePlan dec (fun _ => none) depth parent.box parent.address) = _
    rw [trace]
    exact decodePlan_matches dec _ t tr depth _ _ hd m
  simp only [decodeStageRow, input, gt, bind, Except.bind]
  rfl

/-! ### The Direct root and its `hold_owner` leaves (glue item 4) -/

/-- The closed leaf of an unresolved Direct original `o`: `{"tag": "close", "leaf":
{"tag": "hold_owner", "owner": o}}`. -/
def HoldOwnerJ (j : Json) (o : ℕ) : Prop :=
  get j "tag" Json.getStr? = .ok "close" ∧ ∃ w, j.getObjVal? "leaf" = .ok w ∧
    (get w "tag" Json.getStr?).toOption = some "hold_owner" ∧ get w "owner" Json.getNat? = .ok o

/-- `j` reaches `j'` along a word of split digits: a split node on axis `a` passes digit
`2*a` to `low` and `2*a+1` to `high`; a Direct root shard reference continues at the stored
trace of its shard. -/
inductive JsonReach (sh : String → Option Json) : Json → List ℕ → Json → Prop
  | here (j : Json) : JsonReach sh j [] j
  | low {j l j' : Json} {ds : List ℕ} (a : Axis) (tag : get j "tag" Json.getStr? = .ok "split")
      (ax : get j "axis" axis = .ok a) (child : j.getObjVal? "low" = .ok l) (rest : JsonReach sh l ds j') :
      JsonReach sh j (2 * a.val :: ds) j'
  | high {j h j' : Json} {ds : List ℕ} (a : Axis) (tag : get j "tag" Json.getStr? = .ok "split")
      (ax : get j "axis" axis = .ok a) (child : j.getObjVal? "high" = .ok h) (rest : JsonReach sh h ds j') :
      JsonReach sh j ((2 * a.val + 1) :: ds) j'
  | shard {j s t j' : Json} {pre : String} {ds : List ℕ} (tag : get j "tag" Json.getStr? = .ok "shard")
      (path : get j "path" Json.getStr? = .ok pre) (look : sh pre = some s)
      (trace : s.getObjVal? "trace" = .ok t) (rest : JsonReach sh t ds j') : JsonReach sh j ds j'

theorem decodePlan_of_holdOwner {dec : WitnessDecoder} {sh : String → Option Json} {n : ℕ} {b : Cell}
    {k : Key} {j : Json} {o : ℕ} (leaf : HoldOwnerJ j o) :
    decodePlan dec sh (n + 1) b k j = .ok (.hold ⟨o, "", 0, []⟩) := by
  obtain ⟨tag, w, hw, wtag, owner⟩ := leaf
  simp only [decodePlan, tag, hw, wtag, owner, bind, Except.bind]
  rfl

/-- A decoded trace that reaches a `hold_owner` leaf of `o` along `word` reaches the hold
`⟨o, "", 0, []⟩` there. -/
theorem decodePlan_reach {dec : WitnessDecoder} {sh : String → Option Json} :
    ∀ {j : Json} {word : List ℕ} {j' : Json}, JsonReach sh j word j' →
      ∀ {fuel : ℕ} {b : Cell} {k : Key} {P : Plan} {o : ℕ}, HoldOwnerJ j' o →
        decodePlan dec sh fuel b k j = .ok P → P.reach word = some (.hold ⟨o, "", 0, []⟩)
  | _, _, _, .here j, fuel, b, k, P, o, leaf, h => by
    cases fuel with
    | zero => exact absurd h decodePlan_zero
    | succ n =>
      rw [decodePlan_of_holdOwner leaf] at h
      cases h
      rfl
  | _, _, _, .low (j := j) (l := l) (ds := ds) a tag ax child rest, fuel, b, k, P, o, leaf, h => by
    cases fuel with
    | zero => exact absurd h decodePlan_zero
    | succ n =>
      rw [decodePlan_of_split tag, ax] at h
      obtain ⟨a', ha, h⟩ := bind_eq_ok h
      cases ha
      obtain ⟨pl, hl, h⟩ := bind_eq_ok h
      obtain ⟨ph, _, h⟩ := bind_eq_ok h
      cases h
      have hl' : decodePlan dec sh n ((Cut.dyadic a).child b false) (slotChild k a false) l = .ok pl := by
        simpa [PacketDecode.get, child, bind, Except.bind] using hl
      simpa [Plan.reach] using decodePlan_reach rest leaf hl'
  | _, _, _, .high (j := j) (h := hh) (ds := ds) a tag ax child rest, fuel, b, k, P, o, leaf, h => by
    cases fuel with
    | zero => exact absurd h decodePlan_zero
    | succ n =>
      rw [decodePlan_of_split tag, ax] at h
      obtain ⟨a', ha, h⟩ := bind_eq_ok h
      cases ha
      obtain ⟨pl, _, h⟩ := bind_eq_ok h
      obtain ⟨ph, hr, h⟩ := bind_eq_ok h
      cases h
      have hr' : decodePlan dec sh n ((Cut.dyadic a).child b true) (slotChild k a true) hh = .ok ph := by
        simpa [PacketDecode.get, child, bind, Except.bind] using hr
      have ne : 2 * a.val + 1 ≠ 2 * a.val := by omega
      simpa [Plan.reach, ne] using decodePlan_reach rest leaf hr'
  | _, _, _, .shard (s := s) (t := t) (pre := pre) tag path look trace rest, fuel, b, k, P, o, leaf, h => by
    cases fuel with
    | zero => exact absurd h decodePlan_zero
    | succ n =>
      rw [decodePlan_of_shard tag path look] at h
      obtain ⟨origin, _, h⟩ := bind_eq_ok h
      by_cases bad : (decide (pre ≠ k.seed) || !sameCell origin b) = true
      · rw [ite_eq_left bad] at h
        cases h
      · rw [ite_eq_right bad] at h
        have ht : decodePlan dec sh n b k t = .ok P := by
          simpa [PacketDecode.get, trace, bind, Except.bind] using h
        exact decodePlan_reach rest leaf ht

/-- An unresolved Direct original whose `hold_owner` leaf the root trace reaches along
`word` is held after the root plan runs: key `⟨o, "", 0, []⟩`, cell `descend b word`. -/
theorem direct_holdOwner_held {dec : WitnessDecoder} {sh : String → Option Json} {j j' : Json} {word : List ℕ}
    {o fuel : ℕ} {b : Cell} {k : Key} {P : Plan} {check : WitnessRef → Cell → Bool} {s : Snapshot}
    (reach : JsonReach sh j word j') (leaf : HoldOwnerJ j' o) (decoded : decodePlan dec sh fuel b k j = .ok P)
    (run : P.run check b = some s) : (⟨⟨o, "", 0, []⟩, descend b word⟩ : AddressedCell) ∈ s.held :=
  held_of_reach run (decodePlan_reach reach leaf decoded)

/-- The same from the Direct root entry point `decodeRoot`, which starts at `root`. -/
theorem decodeRoot_reach {dec : WitnessDecoder} {sh : String → Option Json} {depth : ℕ} {j tr j' : Json}
    {word : List ℕ} {o : ℕ} {P : Plan} (decoded : decodeRoot dec sh depth j = .ok P)
    (trace : j.getObjVal? "trace" = .ok tr) (reach : JsonReach sh tr word j') (leaf : HoldOwnerJ j' o) :
    P.reach word = some (.hold ⟨o, "", 0, []⟩) := by
  unfold decodeRoot at decoded
  obtain ⟨b, _, h⟩ := bind_eq_ok decoded
  by_cases off : (!sameCell b root) = true
  · rw [ite_eq_left off] at h
    cases h
  · rw [ite_eq_right off] at h
    have ht : decodePlan dec sh depth root ⟨0, "", 0, []⟩ tr = .ok P := by
      simpa [PacketDecode.get, trace, bind, Except.bind] using h
    exact decodePlan_reach reach leaf ht

/-! ### The Overlay stage (glue item 5) -/

/-- An Overlay stage row with its original owner, the owner's Direct split word, the cells its
plan holds, the hold paths of the trace and the seeds that Adaptive reads. -/
structure OverlayRow where
  owner : ℕ
  word : List ℕ
  row : StageRow
  held : List AddressedCell
  hist : List (List ℕ)
  seeds : List String

/-- The table entry whose row has the atom's key. -/
def tableEntry (table : List OverlayRow) (a : AddressedCell) : Option OverlayRow :=
  table.find? fun e => decide (e.row.input.key = a.key)

def tablePick (table : List OverlayRow) (a : AddressedCell) : Option StageRow :=
  (tableEntry table a).map OverlayRow.row

def tableOut (table : List OverlayRow) (a : AddressedCell) : List AddressedCell :=
  ((tableEntry table a).map OverlayRow.held).getD [a]

/-- Every row's input is its owner's unresolved Direct atom. -/
def TableInputs (table : List OverlayRow) : Prop :=
  ∀ e ∈ table, e.row.input = ⟨⟨e.owner, "", 0, []⟩, descend root e.word⟩

/-- Every row's plan runs on its input cell and holds the row's cells. -/
def TableRuns (check : WitnessRef → Cell → Bool) (table : List OverlayRow) : Prop :=
  ∀ e ∈ table, ∃ paid, e.row.plan.run check e.row.input.cell = some ⟨paid, e.held⟩

/-- Every row holds the derived atoms of its hold paths. -/
def TableHist (table : List OverlayRow) : Prop :=
  ∀ e ∈ table, e.held = e.hist.map (derivedAtom e.row.input.key e.row.input.cell)

/-- Every row's held keys are `⟨owner, seed, 0, []⟩` for its seeds, in order. -/
def TableSeeds (table : List OverlayRow) : Prop :=
  ∀ e ∈ table, e.held.map AddressedCell.key = e.seeds.map fun s => ⟨e.owner, s, 0, []⟩

theorem tableInputs_nil : TableInputs [] := fun _ h => absurd h List.not_mem_nil
theorem tableRuns_nil (check : WitnessRef → Cell → Bool) : TableRuns check [] := fun _ h => absurd h List.not_mem_nil
theorem tableHist_nil : TableHist [] := fun _ h => absurd h List.not_mem_nil
theorem tableSeeds_nil : TableSeeds [] := fun _ h => absurd h List.not_mem_nil

theorem tableInputs_cons {e : OverlayRow} {t : List OverlayRow}
    (h : e.row.input = ⟨⟨e.owner, "", 0, []⟩, descend root e.word⟩) (ht : TableInputs t) : TableInputs (e :: t) :=
  List.forall_mem_cons.mpr ⟨h, ht⟩

theorem tableRuns_cons {check : WitnessRef → Cell → Bool} {e : OverlayRow} {t : List OverlayRow}
    (h : ∃ paid, e.row.plan.run check e.row.input.cell = some ⟨paid, e.held⟩) (ht : TableRuns check t) :
    TableRuns check (e :: t) :=
  List.forall_mem_cons.mpr ⟨h, ht⟩

theorem tableHist_cons {e : OverlayRow} {t : List OverlayRow}
    (h : e.held = e.hist.map (derivedAtom e.row.input.key e.row.input.cell)) (ht : TableHist t) :
    TableHist (e :: t) :=
  List.forall_mem_cons.mpr ⟨h, ht⟩

theorem tableSeeds_cons {e : OverlayRow} {t : List OverlayRow}
    (h : e.held.map AddressedCell.key = e.seeds.map fun s => ⟨e.owner, s, 0, []⟩) (ht : TableSeeds t) :
    TableSeeds (e :: t) :=
  List.forall_mem_cons.mpr ⟨h, ht⟩

/-- Glue item 3 for a table row: every JSON trace of a shape with the row's
hold paths decodes, on the row's input cell and key, to a plan holding exactly the row's
held cells. -/
theorem table_decode_holds {table : List OverlayRow} (hist : TableHist table) {e : OverlayRow} (he : e ∈ table)
    {dec : WitnessDecoder} {sh : String → Option Json} {j : Json} {fuel : ℕ} {t : Trace}
    (m : t.Matches dec j) (hp : t.holdPaths = e.hist) (hd : t.depth ≤ fuel) :
    ∃ P, decodePlan dec sh fuel e.row.input.cell e.row.input.key j = .ok P ∧ P.holds e.row.input.cell = e.held :=
  trace_holds_eq m hp hd (hist e he)

/-- The cells a table row passes on: each hold path below the owner's word, with the key
that `decodePlan` derives from `⟨owner, "", 0, []⟩`. -/
theorem table_held_cells {table : List OverlayRow} (inputs : TableInputs table) (hist : TableHist table)
    {e : OverlayRow} (he : e ∈ table) :
    e.held = e.hist.map fun p => ⟨deriveKey ⟨e.owner, "", 0, []⟩ p, descend root (e.word ++ p)⟩ := by
  rw [hist e he, inputs e he]
  exact List.map_congr_left fun p _ => by simp only [derivedAtom, descend_append]

/-- Glue item 4 for a table row: when the Direct root trace reaches the `hold_owner` leaf of
the row's owner along the row's word, the row's input is held after the root plan runs. -/
theorem table_input_of_direct {table : List OverlayRow} (inputs : TableInputs table) {e : OverlayRow} (he : e ∈ table)
    {dec : WitnessDecoder} {sh : String → Option Json} {j j' : Json} {fuel : ℕ} {k : Key} {P : Plan}
    {check : WitnessRef → Cell → Bool} {s : Snapshot} (reach : JsonReach sh j e.word j')
    (leaf : HoldOwnerJ j' e.owner) (decoded : decodePlan dec sh fuel root k j = .ok P)
    (run : P.run check root = some s) : e.row.input ∈ s.held := by
  rw [inputs e he]
  exact direct_holdOwner_held reach leaf decoded run

/-- The Overlay `splitPass` edit on a snapshot whose atoms carrying a row's key have the
row's cell: it runs and passes on every Overlay atom replaced in place by its row's held
cells, every other atom unchanged and in place. -/
theorem splitPass_table {check : WitnessRef → Cell → Bool} {table : List OverlayRow}
    (runs : TableRuns check table) (s : Snapshot)
    (cells : ∀ a ∈ s.held, ∀ e ∈ table, e.row.input.key = a.key → a.cell = e.row.input.cell) :
    ∃ paid, (Edit.splitPass (stageRows (tablePick table) s.held)).run check s =
      some ⟨s.paid ++ paid, stageHeld (tablePick table) (tableOut table) s.held⟩ := by
  refine splitPass_stageRows s fun a ha row hrow => ?_
  cases he : tableEntry table a with
  | none => simp [tablePick, he] at hrow
  | some e =>
    have er : e.row = row := by simpa [tablePick, he] using hrow
    subst er
    obtain ⟨mem, key⟩ : e ∈ table ∧ e.row.input.key = a.key := by
      have h := List.find?_some he
      exact ⟨List.mem_of_find?_eq_some he, of_decide_eq_true h⟩
    have cell := cells a ha e mem key
    refine ⟨?_, ?_⟩
    · simp [sameAddressedCell, key, cell, sameCell_self]
    · obtain ⟨paid, run⟩ := runs e mem
      exact ⟨paid, by rw [cell, run]; simp [tableOut, he]⟩

/-- With distinct keys, the Overlay rows' inputs in the held list give the cell hypothesis of
`splitPass_table`. -/
theorem table_cells {table : List OverlayRow} {held : List AddressedCell} (nodup : (held.map AddressedCell.key).Nodup)
    (present : ∀ e ∈ table, e.row.input ∈ held) :
    ∀ a ∈ held, ∀ e ∈ table, e.row.input.key = a.key → a.cell = e.row.input.cell := by
  intro a ha e he key
  rw [cell_of_key_nodup nodup (present e he) ha key.symm]

/-- The Overlay edit on a snapshot that holds every row's input, whose atoms carrying a row's
key have the row's cell, with distinct keys among the rows: it runs, and every row's held
cells reach the next stage. -/
theorem splitPass_table_present {check : WitnessRef → Cell → Bool} {table : List OverlayRow}
    (runs : TableRuns check table) (keys : (table.map fun e => e.row.input.key).Nodup) (s : Snapshot)
    (cells : ∀ a ∈ s.held, ∀ e ∈ table, e.row.input.key = a.key → a.cell = e.row.input.cell)
    (present : ∀ e ∈ table, e.row.input ∈ s.held) :
    ∃ paid, (Edit.splitPass (stageRows (tablePick table) s.held)).run check s =
        some ⟨s.paid ++ paid, stageHeld (tablePick table) (tableOut table) s.held⟩ ∧
      ∀ e ∈ table, ∀ a ∈ e.held, a ∈ stageHeld (tablePick table) (tableOut table) s.held := by
  obtain ⟨paid, h⟩ := splitPass_table runs s cells
  refine ⟨paid, h, fun e he a ha => ?_⟩
  have entry : tableEntry table e.row.input = some e := by
    cases hf : tableEntry table e.row.input with
    | none =>
      have := List.find?_eq_none.mp hf e he
      simp at this
    | some e' =>
      have mem' := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      have key' : e'.row.input.key = e.row.input.key := of_decide_eq_true hp
      rw [List.inj_on_of_nodup_map keys mem' he key']
  exact List.mem_flatMap.mpr ⟨e.row.input, present e he, by simp [tablePick, tableOut, entry, ha]⟩

/-- `splitPass_table_present` when all keys of the held list are distinct. -/
theorem splitPass_table_present_of_nodup {check : WitnessRef → Cell → Bool} {table : List OverlayRow}
    (runs : TableRuns check table) (keys : (table.map fun e => e.row.input.key).Nodup) (s : Snapshot)
    (nodup : (s.held.map AddressedCell.key).Nodup) (present : ∀ e ∈ table, e.row.input ∈ s.held) :
    ∃ paid, (Edit.splitPass (stageRows (tablePick table) s.held)).run check s =
        some ⟨s.paid ++ paid, stageHeld (tablePick table) (tableOut table) s.held⟩ ∧
      ∀ e ∈ table, ∀ a ∈ e.held, a ∈ stageHeld (tablePick table) (tableOut table) s.held :=
  splitPass_table_present runs keys s (table_cells nodup present) present

end BccSharp.Coulomb.CompactCover.OverlayCorpus
