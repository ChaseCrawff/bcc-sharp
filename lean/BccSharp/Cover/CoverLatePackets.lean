import BccSharp.TwoSite.Assembly

set_option autoImplicit false

/-! Addressed checker for the Stage6-to-PlanarAnchor continuation.
The binary trees derive their boxes and held addresses. Every accepted
leaf calls the arithmetic checker with that specific rectangle and the
rectangle of any inherited support. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover
namespace LatePackets
open BccSharp.Coverage

inductive Packet where
  | cornerRule | halfShift | jointDeficit | planarFibreOther | planarFibreSaturated | continuationR1 | planarAnchor
  deriving DecidableEq, Repr

inductive InputClass where
  | other | saturated
  deriving DecidableEq, Repr

structure Atom where
  address : Key
  label : InputClass
  box : Cell
  ownerHull : Cell

def Atom.asCell (a : Atom) : AddressedCell := ⟨a.address,a.box⟩

def sameAtom (a b : Atom) : Bool :=
  (decide (a.label=b.label) && sameAddressedCell a.asCell b.asCell) && sameCell a.ownerHull b.ownerHull

structure SplitStep where
  axis : Axis
  upper : Bool
  deriving DecidableEq, Repr

def SplitStep.code (s : SplitStep) : Nat := 2*s.axis.val + if s.upper then 1 else 0

abbrev Path := List SplitStep

def decodeStep (code : Nat) : Option SplitStep :=
  if h : code/2<8 then some ⟨⟨code/2,h⟩,decide (code%2=1)⟩ else none

def decodeSeed (seed : String) : Option Path :=
  seed.toList.mapM fun c =>
    if '0'≤ c ∧ c≤ '9' then decodeStep (c.toNat-'0'.toNat)
    else if 'a'≤ c ∧ c≤ 'f' then decodeStep (10+c.toNat-'a'.toNat)
    else none

def restrict (b : Cell) (path : Path) : Cell :=
  path.foldl (fun c s => (Cut.dyadic s.axis).child c s.upper) b

theorem restrict_append_step (b : Cell) (path : Path) (st : SplitStep) :
    restrict b (path++[st]) = (Cut.dyadic st.axis).child (restrict b path) st.upper := by
  simp [restrict,List.foldl_append]

def Atom.atPath (root : Atom) (path : Path) : Atom :=
  ⟨{root.address with path := root.address.path ++ path.map SplitStep.code}, root.label,
    restrict root.box path,root.ownerHull⟩

@[simp] theorem Atom.atPath_nil (root : Atom) : root.atPath []=root := by
  cases root with
  | mk address label box hull => cases address; simp [Atom.atPath,restrict]

def Slots (atoms : List Atom) (p : Chart) : Prop := Held (atoms.map Atom.asCell) p

private theorem slots_cons {a : Atom} {b : List Atom} {p : Chart} :
    Slots (a::b) p ↔ a.box.Mem p ∨ Slots b p := by
  simp only [Slots,List.map_cons,Held,List.mem_cons]
  constructor
  · rintro ⟨x,hx,hp⟩
    rcases hx with rfl | hx
    · exact Or.inl hp
    · exact Or.inr ⟨x,hx,hp⟩
  · rintro (hp | ⟨x,hx,hp⟩)
    · exact ⟨a.asCell,Or.inl rfl,hp⟩
    · exact ⟨x,Or.inr hx,hp⟩

private theorem slots_append {a b : List Atom} {p : Chart} :
    Slots (a++b) p ↔ Slots a p ∨ Slots b p := by
  simp only [Slots,List.map_append,held_append]

inductive Comparison where
  | fcc | deficit
  deriving DecidableEq, Repr

inductive OpticalMethod where
  | transport (screen : Nat)
  | layered
  deriving DecidableEq, Repr

inductive OpticalResult where
  | fcc | basin | directional | projective
  deriving DecidableEq, Repr

inductive CenteredMethod where
  | absoluteDefect | anchorSlack
  deriving DecidableEq, Repr

structure HalfWitness where
  bits : Fin 3 → Bool
  wrap : IntVec

def HalfWitness.anchor (h : HalfWitness) : Vec := fun i => if h.bits i then -1/2 else 0

theorem HalfWitness.anchor_sound (h : HalfWitness) (live : ∃ i, h.bits i=true) : HalfClass h.anchor := by
  refine ⟨⟨fun i => if h.bits i then -1 else 0,?_⟩,?_⟩
  · funext i
    cases e : h.bits i <;> norm_num [HalfWitness.anchor,e,castVec,Pi.smul_apply,smul_eq_mul]
  · intro n eq
    obtain ⟨i,hi⟩ := live
    have h := congrFun eq i
    simp only [HalfWitness.anchor,hi,ite_true,castVec] at h
    have falseInt : (-1 : ℤ)=2*n i := by
      exact_mod_cast (show (-1 : ℝ)=2*(n i : ℝ) by linarith)
    omega

structure JointParameters where
  catalogue : Nat
  wrap : IntVec
  quaternion : Fin 4 → ℤ
  weight : Nat

inductive Proposal where
  | corner (compare : Comparison) (steps : List (Nat × Nat)) (hint : Option ℚ)
  | joint (steps : List (Nat × Nat)) (parameters : JointParameters) (hint : ℚ)
  | optical (method : OpticalMethod) (result : OpticalResult) (half : HalfWitness) (hint : ℚ)
  | triangular (radius hint : ℚ)
  | centered (method : CenteredMethod) (wrap : IntVec) (hint slack : ℚ)

def Proposal.route : Proposal → Route
  | .corner .fcc _ _ | .triangular _ _ | .optical _ .fcc _ _ => .strictFCC
  | .corner .deficit _ _ | .optical _ .directional _ _ | .optical _ .projective _ _ => .strictDeficit
  | .joint _ _ _ => .strictJoint
  | .optical _ .basin _ _ => .relativeOptical
  | .centered .absoluteDefect _ _ _ => .absoluteDefect
  | .centered .anchorSlack _ _ _ => .anchorSlack

structure LeafProposal where
  /-- Local path within this packet's root, to the tangent support. -/
  ancestor : Path
  payload : Proposal

structure Request where
  packet : Packet
  root : Atom
  path : Path
  proposal : LeafProposal

def Request.target (q : Request) : Atom := q.root.atPath q.path
def Request.support (q : Request) : Cell := restrict q.root.box q.proposal.ancestor

def Request.prefixCheck (q : Request) : Bool :=
  decide (q.proposal.ancestor=q.path.take q.proposal.ancestor.length)

def boxInside (inner outer : Cell) : Bool :=
  decide (∀ i, outer.lo i≤ inner.lo i ∧ inner.hi i≤outer.hi i)

theorem boxInside_sound {inner outer : Cell} (h : boxInside inner outer=true) {p : Chart}
    (hp : inner.Mem p) : outer.Mem p := by
  have hs : ∀ i, outer.lo i≤ inner.lo i ∧ inner.hi i≤outer.hi i := of_decide_eq_true h
  intro i
  exact ⟨(by exact_mod_cast (hs i).1 : (outer.lo i : ℝ)≤ inner.lo i).trans (hp i).1,
    (hp i).2.trans (by exact_mod_cast (hs i).2)⟩

def Request.scopeCheck (q : Request) : Bool :=
  (boxInside q.target.box q.support && boxInside q.support q.root.box) && boxInside q.root.box q.root.ownerHull

theorem Request.scopeCheck_sound (q : Request) (ok : q.scopeCheck=true) {p : Chart}
    (hp : q.target.box.Mem p) : q.support.Mem p ∧ q.root.box.Mem p ∧ q.root.ownerHull.Mem p := by
  obtain ⟨h,owner⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨loc,rt⟩ := Bool.and_eq_true_iff.mp h
  have hs := boxInside_sound loc hp
  have hr := boxInside_sound rt hs
  exact ⟨hs,hr,boxInside_sound owner hr⟩

def Request.profileCheck (q : Request) : Bool :=
  let whole := q.path.isEmpty && q.proposal.ancestor.isEmpty
  let other := decide (q.root.label=.other)
  match q.packet,q.proposal.payload with
  | .cornerRule,.corner .fcc _ none => whole
  | .cornerRule,.corner .deficit _ none => whole && other
  | .halfShift,.optical (.transport 0) _ half _ => whole && decide (∃ i, half.bits i=true)
  | .jointDeficit,.corner .fcc _ (some _) | .continuationR1,.corner .fcc _ (some _) => true
  | .jointDeficit,.corner .deficit _ (some _) | .continuationR1,.corner .deficit _ (some _) => other
  | .jointDeficit,.joint _ par _ | .continuationR1,.joint _ par _ => other && decide (par.weight≤4096)
  | .planarFibreOther,.optical .layered _ half _ => other && q.proposal.ancestor.isEmpty && decide (∃ i, half.bits i=true)
  | .planarFibreSaturated,.optical .layered _ half _ => !other && q.proposal.ancestor.isEmpty && decide (∃ i, half.bits i=true)
  | .planarFibreOther,.triangular _ _ => other && q.proposal.ancestor.isEmpty
  | .planarFibreSaturated,.triangular _ _ => !other && q.proposal.ancestor.isEmpty
  | .planarAnchor,.optical .layered .basin half _ => whole && other && decide (∀ i, half.bits i=true)
  | .planarAnchor,.centered _ _ _ _ => whole && other
  | _,_ => false

abbrev Checker := Request → Bool

/-- The arithmetic soundness obligation uses the exact derived cell.
Published margins and hash receipts do not inhabit this proposition. -/
def CheckerSound (check : Checker) : Prop :=
  ∀ q, q.prefixCheck=true → q.profileCheck=true → q.scopeCheck=true → check q=true →
    ∀ p, q.target.box.Mem p → good p → q.proposal.payload.route.result p

def closeCheck (check : Checker) (q : Request) : Bool :=
  ((q.prefixCheck && q.profileCheck) && q.scopeCheck) && check q

theorem closeCheck_sound {check : Checker} (sound : CheckerSound check) (q : Request)
    (ok : closeCheck check q=true) (p : Chart) (hp : q.target.box.Mem p) (goodP : good p) :
    LeafProof (chartPoint p) := by
  obtain ⟨shape, arithmetic⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨syntaxOK, scope⟩ := Bool.and_eq_true_iff.mp shape
  obtain ⟨pre,profile⟩ := Bool.and_eq_true_iff.mp syntaxOK
  exact q.proposal.payload.route.toLeaf p goodP (sound q pre profile scope arithmetic p hp goodP)

inductive Tree where
  | hold
  | close (leaf : LeafProposal)
  | split (axis : Axis) (low high : Tree)

def Tree.run (check : Checker) (packet : Packet) (atom : Atom) (path : Path) :
    Tree → Option (List Atom)
  | .hold => some [atom.atPath path]
  | .close leaf => if closeCheck check ⟨packet,atom,path,leaf⟩ then some [] else none
  | .split i low high => do
      let lowHolds ← low.run check packet atom (path++[⟨i,false⟩])
      let highHolds ← high.run check packet atom (path++[⟨i,true⟩])
      pure (lowHolds++highHolds)

theorem Tree.run_sound {check : Checker} (sound : CheckerSound check)
    (packet : Packet) (atom : Atom) (tree : Tree) (path : Path) (holds : List Atom)
    (ok : tree.run check packet atom path=some holds) (p : Chart) (goodP : good p)
    (hp : (atom.atPath path).box.Mem p) : LeafProof (chartPoint p) ∨ Slots holds p := by
  induction tree generalizing path holds with
  | hold =>
      have eq : [atom.atPath path]=holds := Option.some.inj ok
      rw [← eq]
      exact Or.inr (slots_cons.mpr (Or.inl hp))
  | close leaf =>
      by_cases accepted : closeCheck check ⟨packet,atom,path,leaf⟩=true
      · exact Or.inl (closeCheck_sound sound ⟨packet,atom,path,leaf⟩ accepted p hp goodP)
      · simp [Tree.run,accepted] at ok
  | split i low high il ih =>
      cases el : low.run check packet atom (path++[⟨i,false⟩]) with
      | none => simp [Tree.run,el] at ok
      | some left =>
        cases er : high.run check packet atom (path++[⟨i,true⟩]) with
        | none => simp [Tree.run,el,er] at ok
        | some right =>
          have eq : left++right=holds := by simpa [Tree.run,el,er] using ok
          rw [← eq]
          rcases two_closed_children (restrict atom.box path) i (midpoint (restrict atom.box path) i) p hp with l | h
          · have L : (atom.atPath (path++[⟨i,false⟩])).box.Mem p := by
              simpa only [Atom.atPath,restrict_append_step,Cut.child,Cut.position] using l
            exact (il _ _ el L).imp_right fun h => slots_append.mpr (Or.inl h)
          · have H : (atom.atPath (path++[⟨i,true⟩])).box.Mem p := by
              simpa only [Atom.atPath,restrict_append_step,Cut.child,Cut.position] using h
            exact (ih _ _ er H).imp_right fun h => slots_append.mpr (Or.inr h)

structure Join where
  corner : Option LeafProposal
  optical : Option LeafProposal

def Join.run (check : Checker) (a : Atom) (q : Join) : Option (List Atom) :=
  let lane (packet : Packet) (leaf : Option LeafProposal) :=
    match leaf with | none => true | some v => closeCheck check ⟨packet,a,[],v⟩
  if lane .cornerRule q.corner && lane .halfShift q.optical then
    if q.corner.isSome || q.optical.isSome then some [] else some [a]
  else none

theorem Join.run_sound {check : Checker} (sound : CheckerSound check) (a : Atom) (q : Join)
    (out : List Atom) (ok : q.run check a=some out) (p : Chart) (gp : good p) (hp : a.box.Mem p) :
    LeafProof (chartPoint p) ∨ Slots out p := by
  have live (packet : Packet) (v : LeafProposal) (h : closeCheck check ⟨packet,a,[],v⟩=true) :
      LeafProof (chartPoint p) := closeCheck_sound sound _ h p (by simpa [Request.target] using hp) gp
  rcases q with ⟨corner,optical⟩
  cases corner with
  | none =>
      cases optical with
      | none =>
          have e : [a]=out := by simpa [Join.run] using ok
          rw [← e]
          exact Or.inr (slots_cons.mpr (Or.inl hp))
      | some w =>
          by_cases valid : closeCheck check ⟨.halfShift,a,[],w⟩=true
          · exact Or.inl (live _ w valid)
          · simp [Join.run,valid] at ok
  | some v =>
      by_cases valid : closeCheck check ⟨.cornerRule,a,[],v⟩=true
      · exact Or.inl (live _ v valid)
      · cases optical <;> simp [Join.run,valid] at ok

structure WholeOverlay where
  primary : Tree
  fiber : Option Tree

/-- PlanarFibre runs on the JointDeficit input root. Its result can remove all of that
root's JointDeficit holds only when its independent closed tree leaves no hold. -/
def WholeOverlay.run (check : Checker) (a : Atom) (job : WholeOverlay) : Option (List Atom) := do
  let undecided ← job.primary.run check .jointDeficit a []
  match job.fiber with
  | none => pure undecided
  | some fiber =>
      let packet := if a.label=.saturated then Packet.planarFibreSaturated else .planarFibreOther
      let out ← fiber.run check packet a []
      if out.isEmpty then pure [] else none

theorem WholeOverlay.run_sound {check : Checker} (sound : CheckerSound check) (a : Atom)
    (q : WholeOverlay) (out : List Atom) (ok : q.run check a=some out)
    (p : Chart) (gp : good p) (hp : a.box.Mem p) : LeafProof (chartPoint p) ∨ Slots out p := by
  have inside : (a.atPath []).box.Mem p := by simpa using hp
  cases h : q.primary.run check .jointDeficit a [] with
  | none => simp [WholeOverlay.run,h] at ok
  | some result =>
      cases f : q.fiber with
      | none => exact q.primary.run_sound sound .jointDeficit a [] out (by simpa [WholeOverlay.run,h,f] using ok) p gp inside
      | some t =>
          let tag := if a.label=.saturated then Packet.planarFibreSaturated else .planarFibreOther
          cases lt : t.run check tag a [] with
          | none => simp [WholeOverlay.run,h,f,tag,lt] at ok
          | some tail =>
              have nocells : tail=[] := by
                cases tail with
                | nil => rfl
                | cons first more => simp [WholeOverlay.run,h,f,tag,lt] at ok
              have fiberOut := t.run_sound sound tag a [] [] (nocells ▸ lt) p gp inside
              exact Or.inl (fiberOut.resolve_right (by simp [Slots,Held]))

structure Row (α : Type) where
  input : Atom
  trace : α

/-- The current roster drives iteration. Packet rows cannot drop a held
atom by omitting it, moving it, or substituting any endpoint. -/
def runRows {α : Type} (run : Atom → α → Option (List Atom)) : List Atom → List (Row α) → Option (List Atom)
  | [], [] => some []
  | a::rest, job::jobs =>
      if sameAtom a job.input then do
        let h ← run a job.trace
        let t ← runRows run rest jobs
        pure (h++t)
      else none
  | _,_ => none

theorem runRows_sound {α : Type} {run : Atom → α → Option (List Atom)}
    (sound : ∀ a trace out, run a trace=some out → ∀ p, good p → a.box.Mem p →
      LeafProof (chartPoint p) ∨ Slots out p)
    (entry : List Atom) (rows : List (Row α)) (out : List Atom) (ok : runRows run entry rows=some out)
    (p : Chart) (gp : good p) (hp : Slots entry p) : LeafProof (chartPoint p) ∨ Slots out p := by
  induction entry generalizing rows out with
  | nil => simp [Slots,Held] at hp
  | cons a rest ih =>
      cases rows with
      | nil => simp [runRows] at ok
      | cons job jobs =>
        by_cases key : sameAtom a job.input=true
        · cases h : run a job.trace with
          | none => simp [runRows,key,h] at ok
          | some first =>
            cases t : runRows run rest jobs with
            | none => simp [runRows,key,h,t] at ok
            | some last =>
              have eq : first++last=out := by simpa [runRows,key,h,t] using ok
              rw [← eq]
              rcases slots_cons.mp hp with here | later
              · exact (sound a job.trace first h p gp here).imp_right (fun e => slots_append.mpr (Or.inl e))
              · exact (ih jobs last t later).imp_right (fun e => slots_append.mpr (Or.inr e))
        · simp [runRows,key] at ok

structure Corpus where
  joint : List (Row Join)
  adaptive : List (Row WholeOverlay)
  round1 : List (Row Tree)
  terminal : List (Row LeafProposal)

def Corpus.run (check : Checker) (fromStage6 : List Atom) (corp : Corpus) : Option (List Atom) := do
  let a ← runRows (Join.run check) fromStage6 corp.joint
  let b ← runRows (WholeOverlay.run check) a corp.adaptive
  let c ← runRows (fun a t => Tree.run check .continuationR1 a [] t) b corp.round1
  runRows (fun a w => Tree.run check .planarAnchor a [] (.close w)) c corp.terminal

/-- The checked post-Stage6 tail supplies the compact cover. The earlier
handoff and arithmetic evaluator remain independent proof obligations. -/
theorem Corpus.cover {check : Checker} (sound : CheckerSound check) (fromStage6 : List Atom) (corp : Corpus)
    (ok : corp.run check fromStage6=some []) : Handoff {p | Slots fromStage6 p} ∅ := by
  intro p hp gp
  unfold Corpus.run at ok
  cases hJ : runRows (Join.run check) fromStage6 corp.joint with
  | none => simp [hJ] at ok
  | some a =>
    cases hA : runRows (WholeOverlay.run check) a corp.adaptive with
    | none => simp [hJ,hA] at ok
    | some b =>
      cases hR : runRows (fun a t => Tree.run check .continuationR1 a [] t) b corp.round1 with
      | none => simp [hJ,hA,hR] at ok
      | some c =>
        have hF : runRows (fun a w => Tree.run check .planarAnchor a [] (.close w)) c corp.terminal=some [] := by simpa [hJ,hA,hR] using ok
        have adapt packet (a : Atom) (t : Tree) (out : List Atom) (h : t.run check packet a []=some out)
            (p : Chart) (gp : good p) (hp : a.box.Mem p) := t.run_sound sound packet a [] out h p gp (by simpa using hp)
        rcases runRows_sound (Join.run_sound sound) _ _ _ hJ p gp hp with done | hj
        · exact Or.inl done
        rcases runRows_sound (WholeOverlay.run_sound sound) _ _ _ hA p gp hj with done | ha
        · exact Or.inl done
        rcases runRows_sound (adapt .continuationR1) _ _ _ hR p gp ha with done | hr
        · exact Or.inl done
        have last := runRows_sound (fun a w out h p gp hp => adapt .planarAnchor a (.close w) out h p gp hp) _ _ _ hF p gp hr
        exact Or.inl (last.resolve_right (by simp [Slots,Held]))

theorem Corpus.onChart {check : Checker} (sound : CheckerSound check) (fromStage6 : List Atom) (corp : Corpus)
    (upstream : Handoff chartRoot {p | Slots fromStage6 p})
    (closed : corp.run check fromStage6=some []) (p : Chart) (hRoot : inRoot p) (gp : good p) :
    LeafProof (chartPoint p) :=
  Handoff.final (Handoff.trans upstream (corp.cover sound fromStage6 closed)) p ((inRoot_iff p).mp hRoot) gp

end LatePackets
end BccSharp.Coulomb.CompactCover
