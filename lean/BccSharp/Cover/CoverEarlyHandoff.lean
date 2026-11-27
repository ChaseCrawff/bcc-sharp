import BccSharp.Cover.CoverEarlyMirror
import BccSharp.Cover.CoverNormalized

set_option autoImplicit false

/-! Closed clip steps and the independently derived Stage6 input atoms.
The final assembly obtains its earlier cover from the same atoms that
the Stage6 evaluator receives. This module still requires arithmetic for
every credited family in the prefix. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.EarlyReplay
open BccSharp.Coverage
open LatePackets

structure ClipRow where
  input : AddressedCell
  certificate : CertifiedClip
  window : Cell
  paidKey : Key
  remainder : List AddressedCell

def sameBoxes : List Cell → List AddressedCell → Bool
  | [],[] => true
  | b::bs,a::as => sameCell b a.cell && sameBoxes bs as
  | _,_ => false

theorem sameBoxes_exact (s : List Cell) (t : List AddressedCell) (ok : sameBoxes s t=true) :
    s=t.map AddressedCell.cell := by
  induction s generalizing t with
  | nil => cases t <;> simp_all [sameBoxes]
  | cons b bs ih =>
    cases t with
    | nil => simp [sameBoxes] at ok
    | cons a rest =>
      obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp ok
      simp only [List.map_cons,sameCell_sound h1,ih rest h2]

def ClipRow.check (check : WitnessRef → Cell → Bool) (row : ClipRow) : Bool :=
  match checkedSubtract row.input.cell row.window with
  | some (strips,some paid) =>
    ((sameBoxes strips row.remainder && sameCell paid row.certificate.clip) &&
      insideCheck row.window (row.certificate.motion.image row.certificate.source)) && row.certificate.check check
  | _ => false

def ClipRow.result (row : ClipRow) : Snapshot := ⟨[⟨row.paidKey,row.certificate.clip⟩],row.remainder⟩

theorem ClipRow.sound {check : WitnessRef → Cell → Bool} (sound : SoundCheck check)
    (row : ClipRow) (ok : row.check check=true) :
    row.result.Sound ∧ (∀ p, row.input.cell.Mem p → row.result.Covers p) := by
  let c := row.certificate
  -- `rw`/`simp` with the equation lemma whnf-evaluate the `checkedSubtract`
  -- discriminant and time out; plain delta-unfolding avoids that.
  delta ClipRow.check at ok
  cases pick : checkedSubtract row.input.cell row.window with
  | none =>
    rw [pick] at ok
    simp at ok
  | some candidate =>
    rcases candidate with ⟨rest,credit⟩
    cases credit with
    | none =>
      rw [pick] at ok
      simp at ok
    | some paid =>
      have accept : (((sameBoxes rest row.remainder && sameCell paid c.clip) &&
          insideCheck row.window (c.motion.image c.source)) && c.check check)=true := by
        rw [pick] at ok
        exact ok
      obtain ⟨bounded,checked⟩ := Bool.and_eq_true_iff.mp accept
      obtain ⟨geometry,_⟩ := Bool.and_eq_true_iff.mp bounded
      obtain ⟨slabs,boxEq⟩ := Bool.and_eq_true_iff.mp geometry
      have eqRest := sameBoxes_exact _ _ slabs
      have eqPaid := sameCell_sound boxEq
      constructor
      · intro p h gp
        obtain ⟨a,ha,hm⟩ := h
        have ea : a=⟨row.paidKey,c.clip⟩ := by simpa [ClipRow.result,c] using ha
        subst a
        exact c.sound sound checked p hm gp
      · intro p hi
        have covers := checkedSubtract_sound _ _ _ _ pick p hi
        rw [eqRest] at covers
        rcases covers with ⟨b,hb,hbP⟩ | ⟨b,eh,hbP,_⟩
        · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
          exact Or.inr ⟨a,ha,hbP⟩
        · have e : paid=b := Option.some.inj eh
          subst b
          exact Or.inl ⟨⟨row.paidKey,c.clip⟩,by simp [ClipRow.result,c],eqPaid ▸ hbP⟩

def sameRoster : List AddressedCell → List AddressedCell → Bool
  | [],[] => true
  | a::as,b::bs => sameAddressedCell a b && sameRoster as bs
  | _,_ => false

theorem sameRoster_exact (a b : List AddressedCell) (h : sameRoster a b=true) : a=b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [sameRoster]
  | cons x xs ih =>
    cases b with
    | nil => simp [sameRoster] at h
    | cons y ys =>
      obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
      rw [sameAddressedCell_sound head,ih ys tail]

/-- Matched indices can be computed by an untrusted sort. Both directions
are checked against exact endpoints, including when a seed is renamed. -/
def indicesCheck (target : Array AddressedCell) (source : List AddressedCell) (indices : List Nat) : Bool :=
  match source,indices with
  | [],[] => true
  | a::tail,i::more =>
    match target[i]? with
    | none => false
    | some b => sameCell a.cell b.cell && indicesCheck target tail more
  | _,_ => false

theorem indicesCheck_sound (target : List AddressedCell) (source : List AddressedCell) (indices : List Nat)
    (h : indicesCheck target.toArray source indices=true) (p : Chart) (inside : Held source p) : Held target p := by
  induction source generalizing indices with
  | nil => simp [Held] at inside
  | cons a tail ih =>
    cases indices with
    | nil => simp [indicesCheck] at h
    | cons i more =>
      cases leaf : target.toArray[i]? with
      | none => simp [indicesCheck,leaf] at h
      | some b =>
        obtain ⟨geom,later⟩ := Bool.and_eq_true_iff.mp (show (sameCell a.cell b.cell &&
          indicesCheck target.toArray tail more)=true by simpa [indicesCheck,leaf] using h)
        obtain ⟨c,hc,hp⟩ := inside
        rcases List.mem_cons.mp hc with hca | ht
        · subst c
          have member : b∈target := by
            have e : target[i]?=some b := by simpa using leaf
            exact List.mem_of_getElem? e
          exact ⟨b,member,sameCell_sound geom ▸ hp⟩
        · exact ih more later ⟨c,ht,hp⟩

structure Reorder where
  rows : List AddressedCell
  forward : List Nat
  backward : List Nat

def Reorder.run (r : Reorder) (s : Snapshot) : Option Snapshot :=
  if indicesCheck r.rows.toArray s.held r.forward && indicesCheck s.held.toArray r.rows r.backward then
    some {s with held := r.rows}
  else none

theorem Reorder.sound (r : Reorder) (s out : Snapshot) (hs : s.Sound) (ok : r.run s=some out) :
    out.Sound ∧ (∀ p, s.Covers p → out.Covers p) := by
  by_cases h : (indicesCheck r.rows.toArray s.held r.forward && indicesCheck s.held.toArray r.rows r.backward)=true
  · have e : {s with held := r.rows}=out := by simpa [Reorder.run,h] using ok
    subst out
    exact ⟨hs,fun p hp => hp.imp_right (indicesCheck_sound _ _ _ (Bool.and_eq_true_iff.mp h).1 p)⟩
  · simp [Reorder.run,h] at ok

def Snapshot.selectPositive (s : Snapshot) : Snapshot :=
  ⟨s.paid,s.held.filter (fun a => decide (0≤a.cell.lo 5))⟩

theorem selectPositive_sound (s : Snapshot) (hs : s.Sound) (sep : halvesCheck s=true)
    (rootCover : ∀ p, root.Mem p → s.Covers p) : s.selectPositive.Sound ∧
      (∀ p, p∈positiveHalf → s.selectPositive.Covers p) := by
  constructor
  · exact hs
  · intro p hp
    have width : positiveCell (replaceEnd root 5 0 true)=true := by
      refine decide_eq_true fun i => ?_
      fin_cases i <;> norm_num [replaceEnd,root]
    have onHalf : (replaceEnd root 5 0 true).Mem p := by
      intro i
      by_cases h : i=5
      · subst i
        simpa [replaceEnd] using And.intro hp.2 (hp.1 5).2
      · simpa [replaceEnd,h] using hp.1 i
    apply closed_mem_from_strict _ width (covers_closed s.selectPositive) _ p onHalf
    intro q hq
    have nz : 0<q 5 := by simpa [CellStrict,replaceEnd] using (hq 5).1
    have within : root.Mem q := by
      intro i
      by_cases h : i=5
      · subst i
        have r : (root.lo 5 : ℝ)≤0 := by norm_num [root]
        refine ⟨r.trans nz.le,?_⟩
        simpa [CellStrict,replaceEnd] using (hq 5).2.le
      · simpa [replaceEnd,h] using hq.mem i
    rcases rootCover q within with paid | ⟨a,ha,hpA⟩
    · exact Or.inl paid
    have sides : 0≤a.cell.lo 5 ∨ a.cell.hi 5≤0 := of_decide_eq_true (List.all_eq_true.mp sep a ha)
    have pos := sides.resolve_right fun h => by
      have r : (a.cell.hi 5 : ℝ)≤0 := by exact_mod_cast h
      linarith only [r,nz,(hpA 5).2]
    exact Or.inr ⟨a,List.mem_filter.mpr ⟨ha,decide_eq_true pos⟩,hpA⟩

def MergeRow.run (r : MergeRow) (s : Snapshot)
    (pre between suffix : List AddressedCell) : Option Snapshot :=
  if sameRoster s.held (pre++[r.low]++between++[r.high]++suffix) && r.check then
    some {s with held := pre++[r.parent]++between++suffix}
  else none

private theorem held_one (a : AddressedCell) (p : Chart) : Held [a] p ↔ a.cell.Mem p := by
  simp [Held]

theorem MergeRow.run_sound (r : MergeRow) (s out : Snapshot) (hs : s.Sound)
    (pre middle post : List AddressedCell) (ok : r.run s pre middle post=some out) :
    out.Sound ∧ (∀ p, s.Covers p → out.Covers p) := by
  by_cases accepted : (sameRoster s.held (pre++[r.low]++middle++[r.high]++post) && r.check)=true
  · have e : {s with held := pre++[r.parent]++middle++post}=out := by
      rw [MergeRow.run,ite_eq_left accepted] at ok
      exact Option.some.inj ok
    subst out
    obtain ⟨input,geom⟩ := Bool.and_eq_true_iff.mp accepted
    refine ⟨hs,fun p h => h.imp_right ?_⟩
    rw [sameRoster_exact _ _ input]
    simp only [held_append,held_one,r.exact geom p]
    tauto
  · rw [MergeRow.run,ite_eq_right accepted] at ok
    simp at ok

/-- The clip consumes one exact current entry. The rest of the worklist
is unchanged and each output strip is checked in the stored axis order. -/
def Snapshot.applyClip (check : WitnessRef → Cell → Bool) (s : Snapshot)
    (before after : List AddressedCell) (row : ClipRow) : Option Snapshot :=
  if sameRoster s.held (before++row.input::after) && row.check check then
    some ⟨s.paid++row.result.paid,(before++row.remainder)++after⟩
  else none

theorem Snapshot.applyClip_sound {check : WitnessRef → Cell → Bool} (checkSound : SoundCheck check)
    (s out : Snapshot) (hs : s.Sound) (before after : List AddressedCell) (row : ClipRow)
    (ok : s.applyClip check before after row=some out) :
    out.Sound ∧ (∀ p, s.Covers p → out.Covers p) := by
  by_cases goodClip : (sameRoster s.held (before++row.input::after) && row.check check)=true
  · have eo : (⟨s.paid++row.result.paid,(before++row.remainder)++after⟩ : Snapshot)=out := by simpa [Snapshot.applyClip,goodClip] using ok
    subst out
    obtain ⟨geom,arith⟩ := Bool.and_eq_true_iff.mp goodClip
    obtain ⟨rowS,rowC⟩ := row.sound checkSound arith
    have geom' := sameRoster_exact _ _ geom
    constructor
    · intro p hp gp
      rcases held_append.mp hp with old | fresh
      · exact hs p old gp
      · exact rowS p fresh gp
    · intro p hp
      rcases hp with paid | rest
      · exact Or.inl (held_append.mpr (Or.inl paid))
      rw [geom'] at rest
      rcases held_append.mp rest with prior | currentOrAfter
      · exact Or.inr (held_append.mpr (Or.inl (held_append.mpr (Or.inl prior))))
      obtain ⟨a,ha,hpa⟩ := currentOrAfter
      rcases List.mem_cons.mp ha with ea | tail
      · subst a
        rcases rowC p hpa with h | h
        · exact Or.inl (held_append.mpr (Or.inr h))
        · exact Or.inr (held_append.mpr (Or.inl (held_append.mpr (Or.inr h))))
      · exact Or.inr (held_append.mpr (Or.inr ⟨a,tail,hpa⟩))
  · simp [Snapshot.applyClip,goodClip] at ok

structure SeedSlot where
  seed : String
  /-- `none` is the unchanged dyadic seed. `some []` is a fully paid seed. -/
  replacement : Option (List Cell)

structure RosterOwner where
  owner : Nat
  hull : Cell
  seeds : List SeedSlot

def SeedSlot.atoms (owner : Nat) (hull : Cell) (r : SeedSlot) : Option (List Atom) := do
  let path ← decodeSeed r.seed
  let box := restrict hull path
  let base : Atom := ⟨⟨owner,r.seed,0,[]⟩,.other,box,hull⟩
  match r.replacement with
  | none => if positiveCell box then some [base] else none
  | some replacements =>
    if replacements.all (fun b => positiveCell b && insideCheck b box) then
      some (replacements.zipIdx.map fun (b,i) => { base with
        address := {base.address with replacement := i+1}, box := b })
    else none

def RosterOwner.atoms (r : RosterOwner) : Option (List Atom) := do
  let seeds ← r.seeds.mapM (SeedSlot.atoms r.owner r.hull)
  pure seeds.flatten

def bindStage5b (s : Snapshot) (proposed : List RosterOwner) : Option (List Atom) := do
  let rows ← proposed.mapM RosterOwner.atoms
  let atoms := rows.flatten
  if relabelCheck s.held (atoms.map Atom.asCell) then some atoms else none

theorem bindStage5b_sound (s : Snapshot) (proposed : List RosterOwner) (atoms : List Atom)
    (check : bindStage5b s proposed=some atoms) (hs : s.Sound)
    (hc : ∀ p, p∈positiveHalf → s.Covers p) : Handoff positiveHalf {p | Slots atoms p} := by
  cases out : proposed.mapM RosterOwner.atoms with
  | none => simp [bindStage5b,out] at check
  | some rows =>
    have unfolded : (if relabelCheck s.held (rows.flatten.map Atom.asCell)=true then some rows.flatten
        else none)=some atoms := by
      rw [bindStage5b,out] at check
      exact check
    by_cases eq : relabelCheck s.held (rows.flatten.map Atom.asCell)=true
    · have he : rows.flatten=atoms := by
        rw [ite_eq_left eq] at unfolded
        exact Option.some.inj unfolded
      subst atoms
      intro p hp gp
      rcases hc p hp with paid | residual
      · exact Or.inl (hs p paid gp)
      · exact Or.inr ((relabel_sound _ _ eq p).mp residual)
    · rw [ite_eq_right eq] at unfolded
      simp at unfolded

def geometryWitnessCheck (normalized : WitnessRef → Option NormalizedProposal) (w : WitnessRef) (b : Cell) : Bool :=
  match w.route with
  | .invalidReduction =>
    match normalized w with
    | some row => row.check b
    | none => compactReductionCheck b || normalizedStencilCheck b
  | _ => false

theorem geometryWitnessCheck_sound (normalized : WitnessRef → Option NormalizedProposal) :
    SoundCheck (geometryWitnessCheck normalized) := by
  intro w b checked p hp _
  cases w with
  | mk route source record =>
    cases route <;> simp [geometryWitnessCheck] at checked
    case invalidReduction =>
      cases hw : normalized ⟨.invalidReduction,source,record⟩ with
      | none =>
        have ok : (compactReductionCheck b || normalizedStencilCheck b)=true := by simpa [hw] using checked
        rcases Bool.or_eq_true_iff.mp ok with original | normalized
        · exact compactReductionCheck_sound b original p hp
        · exact normalizedStencilCheck_sound b normalized p hp
      | some row => exact row.sound b (by simpa [hw] using checked) p hp

private def tightenCut (b : Cell) (axis : Axis) (right : Bool) :
    Nat → ℚ → ℚ → Option SlabCut → Option SlabCut
  | 0,_,_,best => best
  | n+1,fromEdge,towardCenter,best =>
    let mid := (fromEdge+towardCenter)/2
    let cut : SlabCut := ⟨axis,mid,!right⟩
    if normalizedStencilCheck (cut.slab b) then
      tightenCut b axis right n mid towardCenter (some cut)
    else tightenCut b axis right n fromEdge mid best

def reductionContract (b : Cell) : List SlabCut × Cell :=
  let moves := (List.finRange 5).flatMap fun i =>
    [((Fin.castLE (by decide : 5≤8) i),false),(Fin.castLE (by decide : 5≤8) i,true)]
  moves.foldl (fun (prior,cur) (axis,right) =>
    let edge := if right then cur.hi axis else cur.lo axis
    let other := if right then cur.lo axis else cur.hi axis
    let face : SlabCut := ⟨axis,edge,!right⟩
    if edge=other then (prior,cur)
    else if normalizedStencilCheck (face.slab cur) then
      match tightenCut cur axis right 4 edge other none with
      | none => (prior,cur)
      | some cut => (prior++[cut],cut.keep cur)
    else (prior,cur)) ([],b)

/-- An Adaptive clipped route pays only when the reported survivor is the
literal closed complement of the independently checked invalid slabs. -/
def reducedRegionCheck (b survivor : Cell) : Bool :=
  let (cuts,reported) := reductionContract b
  match carve b cuts with
  | none => false
  | some (slabs,kept) => (sameCell kept reported && sameCell kept survivor) && slabs.all normalizedStencilCheck

theorem reducedRegionCheck_sound (b survivor : Cell) (ok : reducedRegionCheck b survivor=true)
    (p : Chart) (hp : b.Mem p) (gp : good p) : survivor.Mem p := by
  -- Keep `reductionContract b` opaque: reducing the match on it unfolds the
  -- stencil search and times out.
  delta reducedRegionCheck at ok
  generalize reductionContract b = t at ok
  obtain ⟨cuts,reported⟩ := t
  cases h : carve b cuts with
  | none => simp only [h,Bool.false_eq_true] at ok
  | some result =>
    rcases result with ⟨slabs,kept⟩
    have checked : ((sameCell kept reported && sameCell kept survivor) &&
        slabs.all normalizedStencilCheck)=true := by
      simpa only [h] using ok
    obtain ⟨fit,paid⟩ := Bool.and_eq_true_iff.mp checked
    rcases carve_cover b cuts slabs kept h p hp with ⟨slab,hs,inSlab⟩ | uncut
    · exact False.elim (normalizedStencilCheck_sound slab (List.all_eq_true.mp paid slab hs) p inSlab gp.2.1)
    · exact sameCell_sound (Bool.and_eq_true_iff.mp fit).2 ▸ uncut

def checkReducedSurvivor (check : WitnessRef → Cell → Bool)
    (w : WitnessRef) (root survivor : Cell) : Bool := reducedRegionCheck root survivor && check w survivor

theorem checkReducedSurvivor_sound {check : WitnessRef → Cell → Bool} (sound : SoundCheck check)
    (w : WitnessRef) (root survivor : Cell) (h : checkReducedSurvivor check w root survivor=true)
    (p : Chart) (hp : root.Mem p) (gp : good p) : w.route.result p := by
  obtain ⟨geometry,arith⟩ := Bool.and_eq_true_iff.mp h
  exact sound w survivor arith p (reducedRegionCheck_sound root survivor geometry p hp gp) gp

inductive Edit where
  | splitPass (rows : List StageRow)
  | updateOrder (rows : Reorder)
  | clip (pre suffix : List AddressedCell) (row : ClipRow)
  | merge (pre between suffix : List AddressedCell) (row : MergeRow)

def Edit.run (check : WitnessRef → Cell → Bool) (s : Snapshot) : Edit → Option Snapshot
  | .splitPass rows => s.advance check rows
  | .updateOrder rows => rows.run s
  | .clip pre post row => s.applyClip check pre post row
  | .merge pre inner post row => row.run s pre inner post

theorem Edit.sound {check : WitnessRef → Cell → Bool} (sound : SoundCheck check)
    (s t : Snapshot) (hs : s.Sound) (e : Edit) (ok : e.run check s=some t) :
    t.Sound ∧ (∀ p, s.Covers p → t.Covers p) := by
  cases e with
  | splitPass rows => exact s.advance_sound hs sound rows t ok
  | updateOrder rows => exact rows.sound s t hs ok
  | clip pre post row => exact Snapshot.applyClip_sound sound s t hs pre post row ok
  | merge pre middle post row => exact row.run_sound s t hs pre middle post ok

def runEdits (check : WitnessRef → Cell → Bool) : Snapshot → List Edit → Option Snapshot
  | s,[] => some s
  | s,e::es => e.run check s >>= fun next => runEdits check next es

theorem runEdits_sound {check : WitnessRef → Cell → Bool} (sound : SoundCheck check)
    (edits : List Edit) (s t : Snapshot) (hs : s.Sound) (ok : runEdits check s edits=some t) :
    t.Sound ∧ (∀ p, s.Covers p → t.Covers p) := by
  induction edits generalizing s t with
  | nil =>
    have eq : s=t := Option.some.inj ok
    subst t
    exact ⟨hs,fun _ h => h⟩
  | cons e es ih =>
    cases step : e.run check s with
    | none => simp [runEdits,step] at ok
    | some next =>
      obtain ⟨sn,cn⟩ := e.sound sound s next hs step
      obtain ⟨st,ct⟩ := ih next t sn (by simpa [runEdits,step] using ok)
      exact ⟨st,fun p hp => ct p (cn p hp)⟩

structure CorpusPrefix where
  originalRoot : Plan
  beforeMirror : List Edit
  positiveStage : List Edit
  mirrorKey : Key → Key → Key
  afterMirror : List Edit
  stage5b : List RosterOwner

def CorpusPrefix.run (c : CorpusPrefix) (check : WitnessRef → Cell → Bool) : Option (List Atom) := do
  let directRoute ← c.originalRoot.run check root
  let old ← runEdits check directRoute c.beforeMirror
  let positive ← runEdits check old.selectPositive c.positiveStage
  if !positive.held.all (fun a => insideCheck a.cell root) then none else do
    let mirrored ← mirror c.mirrorKey old positive
    let latest ← runEdits check mirrored c.afterMirror
    bindStage5b latest c.stage5b

theorem CorpusPrefix.sound (c : CorpusPrefix) {check : WitnessRef → Cell → Bool} (sound : SoundCheck check)
    (atoms : List Atom) (ok : c.run check=some atoms) : Handoff positiveHalf {p | Slots atoms p} := by
  cases rootCheck : c.originalRoot.run check root with
  | none => simp [CorpusPrefix.run,rootCheck] at ok
  | some initial =>
    cases pre : runEdits check initial c.beforeMirror with
    | none => simp [CorpusPrefix.run,rootCheck,pre] at ok
    | some full =>
      cases pos : runEdits check full.selectPositive c.positiveStage with
      | none => simp [CorpusPrefix.run,rootCheck,pre,pos] at ok
      | some half =>
        simp only [CorpusPrefix.run,rootCheck,pre,pos,Option.bind_eq_bind,Option.bind_some] at ok
        cases within : half.held.all (fun a => insideCheck a.cell root) with
        | false =>
          rw [within] at ok
          simp at ok
        | true =>
          rw [within] at ok
          cases mid : mirror c.mirrorKey full half with
          | none => simp [mid] at ok
          | some mirrored =>
            cases after : runEdits check mirrored c.afterMirror with
            | none => simp [mid,after] at ok
            | some latest =>
              have linked : bindStage5b latest c.stage5b=some atoms := by
                simpa [mid,after] using ok
              obtain ⟨s0,c0⟩ := c.originalRoot.run_sound check sound root initial rootCheck
              obtain ⟨s1,c1⟩ := runEdits_sound sound c.beforeMirror initial full s0 pre
              have fullRoot : ∀ p, root.Mem p → full.Covers p := fun p h => c1 p (c0 p h)
              have sep : halvesCheck full=true := by
                by_contra! fail
                simp [mirror,fail] at mid
              obtain ⟨s2,c2⟩ := selectPositive_sound full s1 sep fullRoot
              obtain ⟨s3,c3⟩ := runEdits_sound sound c.positiveStage _ half s2 pos
              obtain ⟨s4,c4⟩ := mirror_sound c.mirrorKey full half mirrored s1 s3 fullRoot
                (fun p h => c3 p (c2 p h)) within mid
              obtain ⟨s5,c5⟩ := runEdits_sound sound c.afterMirror mirrored latest s4 after
              exact bindStage5b_sound latest c.stage5b atoms linked s5 (fun p h => c5 p (c4 p h))

end BccSharp.Coulomb.CompactCover.EarlyReplay

namespace BccSharp.Coulomb
open CompactCover CompactCover.LatePackets CompactCover.EarlyReplay

theorem assemble_from_cover_corpus (analytic : GlobalAnalyticInputs)
    {prefixCheck : WitnessRef → Cell → Bool} (prefixSound : SoundCheck prefixCheck)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early) (sLate : CheckerSound late)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rStage5b : pre.run prefixCheck=some stage5b)
    (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage6 : runRows (runStage6 early) stage5b rows=some stage6) (closed : corp.run late stage6=some []) : Statement :=
  assemble_from_checked_cover analytic sEarly sLate stage5b stage6 rows corp
    (pre.sound prefixSound stage5b rStage5b) rStage6 closed

end BccSharp.Coulomb
