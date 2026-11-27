import BccSharp.Cover.CoverEarlyTransport

set_option autoImplicit false

/-! Proof-producing prefix replay. Geometry and paid regions are
tracked separately so that the mirror step can use closed boxes, without
taking the closure of a set of strict numerical conclusions. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.EarlyReplay
open BccSharp.Coverage

structure Snapshot where
  paid : List AddressedCell
  held : List AddressedCell

def Snapshot.empty : Snapshot := ⟨[],[]⟩
def Snapshot.join (x y : Snapshot) : Snapshot := ⟨x.paid++y.paid,x.held++y.held⟩
def Snapshot.Covers (s : Snapshot) (p : Chart) : Prop := Held s.paid p ∨ Held s.held p
def Snapshot.Sound (s : Snapshot) : Prop := ∀ p, Held s.paid p → good p → LeafProof (chartPoint p)

theorem Snapshot.join_sound (x y : Snapshot) (hx : x.Sound) (hy : y.Sound) : (x.join y).Sound := by
  intro p live gp
  rcases held_append.mp live with a | b
  · exact hx p a gp
  · exact hy p b gp

theorem Snapshot.covers_join_left (x y : Snapshot) (p : Chart) (h : x.Covers p) : (x.join y).Covers p :=
  h.imp (fun h => held_append.mpr (Or.inl h)) (fun h => held_append.mpr (Or.inl h))

theorem Snapshot.covers_join_right (x y : Snapshot) (p : Chart) (h : y.Covers p) : (x.join y).Covers p :=
  h.imp (fun h => held_append.mpr (Or.inr h)) (fun h => held_append.mpr (Or.inr h))

structure CertifiedClip where
  receipt : WitnessRef
  source : Cell
  motion : ChartMotion
  clip : Cell

def CertifiedClip.check (c : CertifiedClip) (check : WitnessRef → Cell → Bool) : Bool :=
  insideCheck c.clip (c.motion.image c.source) && check c.receipt c.source

theorem CertifiedClip.sound (c : CertifiedClip) {check : WitnessRef → Cell → Bool}
    (hc : SoundCheck check) (ok : c.check check=true) (p : Chart) (hp : c.clip.Mem p) (gp : good p) :
    LeafProof (chartPoint p) := by
  obtain ⟨subset,arith⟩ := Bool.and_eq_true_iff.mp ok
  let x := c.motion.preimage p
  have inSource : c.source.Mem x := c.motion.pull_mem _ p (insideCheck_sound subset hp)
  have goodSource : good x := c.motion.pull_good p gp
  exact c.motion.push_leaf p (c.receipt.route.toLeaf x goodSource (hc _ _ arith x inSource goodSource))

/-- A hold's endpoints and a pay node's exact leaf are derived from the
incoming rectangle. The pay certificate may refer to a larger canonical
box whose closed image covers the exact leaf. -/
inductive Plan where
  | hold (key : Key)
  | pay (key : Key) (proof : CertifiedClip)
  | split (cut : Cut) (left right : Plan)

def Plan.run (check : WitnessRef → Cell → Bool) (b : Cell) : Plan → Option Snapshot
  | .hold k => some ⟨[],[⟨k,b⟩]⟩
  | .pay k proof =>
      if sameCell b proof.clip && proof.check check then some ⟨[⟨k,b⟩],[]⟩ else none
  | .split cut l r =>
      if cut.fits b then do
        let joinedLeft ← l.run check (cut.child b false)
        let joinedRight ← r.run check (cut.child b true)
        pure (joinedLeft.join joinedRight)
      else none

private theorem single_mem (key : Key) {b : Cell} {p : Chart} (hp : b.Mem p) : Held [⟨key,b⟩] p :=
  ⟨⟨key,b⟩,by simp,hp⟩

theorem Plan.run_sound (check : WitnessRef → Cell → Bool) (hr : SoundCheck check)
    (r : Plan) (b : Cell) (out : Snapshot) (h : r.run check b=some out) :
    out.Sound ∧ (∀ p, b.Mem p → out.Covers p) := by
  induction r generalizing b out with
  | hold k =>
      have e : (⟨[],[⟨k,b⟩]⟩ : Snapshot)=out := Option.some.inj h
      cases e
      exact ⟨by simp [Snapshot.Sound,Held],fun p hp => Or.inr (single_mem k hp)⟩
  | pay k cert =>
      by_cases accepted : (sameCell b cert.clip && cert.check check)=true
      · have e : (⟨[⟨k,b⟩],[]⟩ : Snapshot)=out := by simpa [Plan.run,accepted] using h
        cases e
        obtain ⟨same,valid⟩ := Bool.and_eq_true_iff.mp accepted
        refine ⟨?_,fun p hp => Or.inl (single_mem k hp)⟩
        intro p hp gp
        obtain ⟨a,ha,inside⟩ := hp
        have eq : a=⟨k,b⟩ := by simpa using ha
        subst a
        exact cert.sound hr valid p (sameCell_sound same ▸ inside) gp
      · simp [Plan.run,accepted] at h
  | split cut l r il ir =>
      by_cases fits : cut.fits b=true
      · cases left : l.run check (cut.child b false) with
        | none => simp [Plan.run,fits,left] at h
        | some a =>
          cases right : r.run check (cut.child b true) with
          | none => simp [Plan.run,fits,left,right] at h
          | some c =>
            have e : a.join c=out := by simpa [Plan.run,fits,left,right] using h
            cases e
            obtain ⟨sL,cL⟩ := il _ _ left
            obtain ⟨sR,cR⟩ := ir _ _ right
            refine ⟨a.join_sound c sL sR,?_⟩
            intro p hp
            rcases two_closed_children b (cut.position b).1 (cut.position b).2 p hp with hL | hR
            · exact a.covers_join_left c p (cL p hL)
            · exact a.covers_join_right c p (cR p hR)
      · simp [Plan.run,fits] at h

structure StageRow where
  input : AddressedCell
  plan : Plan

def replayStage (check : WitnessRef → Cell → Bool) : List AddressedCell → List StageRow → Option Snapshot
  | [],[] => some .empty
  | a::more,row::rows =>
      if sameAddressedCell a row.input then do
        let first ← row.plan.run check a.cell
        let tail ← replayStage check more rows
        pure (first.join tail)
      else none
  | _,_ => none

theorem replayStage_sound {check : WitnessRef → Cell → Bool} (checkSound : SoundCheck check)
    (start : List AddressedCell) (rows : List StageRow) (out : Snapshot)
    (h : replayStage check start rows=some out) : out.Sound ∧ (∀ p, Held start p → out.Covers p) := by
  induction start generalizing rows out with
  | nil =>
      cases rows with
      | nil =>
        have e : Snapshot.empty=out := Option.some.inj h
        cases e
        simp [Snapshot.empty,Snapshot.Sound,Held]
      | cons r rows => simp [replayStage] at h
  | cons a more ih =>
      cases rows with
      | nil => simp [replayStage] at h
      | cons row rows =>
        by_cases geom : sameAddressedCell a row.input=true
        · cases head : row.plan.run check a.cell with
          | none => simp [replayStage,geom,head] at h
          | some f =>
            cases rest : replayStage check more rows with
            | none => simp [replayStage,geom,head,rest] at h
            | some t =>
              have e : f.join t=out := by simpa [replayStage,geom,head,rest] using h
              cases e
              obtain ⟨fS,fC⟩ := row.plan.run_sound check checkSound a.cell f head
              obtain ⟨tS,tC⟩ := ih rows t rest
              refine ⟨f.join_sound t fS tS,?_⟩
              intro p inside
              rcases (held_append (a := [a]) (b := more)).mp inside with first | tail
              · obtain ⟨b,hb,hbP⟩ := first
                have eq : b=a := by simpa using hb
                subst b
                exact f.covers_join_left t p (fC p hbP)
              · exact f.covers_join_right t p (tC p tail)
        · simp [replayStage,geom] at h

def Snapshot.advance (s : Snapshot) (check : WitnessRef → Cell → Bool) (rows : List StageRow) : Option Snapshot := do
  let out ← replayStage check s.held rows
  pure ⟨s.paid++out.paid,out.held⟩

theorem Snapshot.advance_sound (s : Snapshot) (hs : s.Sound) {check : WitnessRef → Cell → Bool}
    (checkSound : SoundCheck check) (rows : List StageRow) (out : Snapshot)
    (h : s.advance check rows=some out) : out.Sound ∧ ∀ p, s.Covers p → out.Covers p := by
  cases e : replayStage check s.held rows with
  | none => simp [Snapshot.advance,e] at h
  | some step =>
    have eq : (⟨s.paid++step.paid,step.held⟩ : Snapshot)=out := by simpa [Snapshot.advance,e] using h
    cases eq
    obtain ⟨sound,cover⟩ := replayStage_sound checkSound s.held rows step e
    refine ⟨?_,?_⟩
    · intro p hp gp
      rcases held_append.mp hp with a | b
      · exact hs p a gp
      · exact sound p b gp
    · intro p hp
      rcases hp with a | b
      · exact Or.inl (held_append.mpr (Or.inl a))
      · exact (cover p b).imp_left (fun h => held_append.mpr (Or.inr h))

/-- Successor tuples may use the original seed and fragment numbering.
Every relabeling must preserve both endpoints. There is no volume test. -/
def relabelCheck : List AddressedCell → List AddressedCell → Bool
  | [],[] => true
  | x::xs,y::ys => sameCell x.cell y.cell && relabelCheck xs ys
  | _,_ => false

theorem relabel_sound (a b : List AddressedCell) (ok : relabelCheck a b=true) (p : Chart) :
    Held a p ↔ Held b p := by
  induction a generalizing b with
  | nil => cases b <;> simp [relabelCheck] at ok ⊢
  | cons x xs ih =>
    cases b with
    | nil => simp [relabelCheck] at ok
    | cons y ys =>
      obtain ⟨e,t⟩ := Bool.and_eq_true_iff.mp ok
      have s : Held [x] p ↔ Held [y] p := by
        simp [Held,sameCell_sound e]
      rw [show x::xs=[x]++xs by rfl,show y::ys=[y]++ys by rfl,held_append,held_append,s,ih ys t]

structure MergeRow where
  low : AddressedCell
  high : AddressedCell
  parent : AddressedCell
  axis : Axis

def MergeRow.check (m : MergeRow) : Bool :=
  let cut := Cut.dyadic m.axis
  (cut.fits m.parent.cell && sameCell m.low.cell (cut.child m.parent.cell false)) &&
    sameCell m.high.cell (cut.child m.parent.cell true)

theorem MergeRow.exact (m : MergeRow) (h : m.check=true) (p : Chart) :
    m.parent.cell.Mem p ↔ m.low.cell.Mem p ∨ m.high.cell.Mem p := by
  obtain ⟨left,high⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨fits,low⟩ := Bool.and_eq_true_iff.mp left
  rw [sameCell_sound low,sameCell_sound high]
  exact coalesce_closed_siblings _ _ fits p

end BccSharp.Coulomb.CompactCover.EarlyReplay
