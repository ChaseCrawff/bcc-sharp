import BccSharp.Cover.CoverEarlyDecode
import BccSharp.Cover.OverlayDecodeBase

set_option autoImplicit false

/-! How a decoded Overlay row enters the corpus prefix.

`assemble_from_cover_corpus` runs a `CorpusPrefix` under one prefix check
`prefixCheck` with `SoundCheck prefixCheck`. The Overlay rows are stage rows of
that prefix: the hard owner 790397 and the 41 credited adaptive owners, each a
`StageRow` whose `Plan` covers the owner's cell.

* `checkWithOverlay prior` adds the fixed-point Overlay check to any prior check for
  witnesses on route `.strictFCC` from the two planar banks
  (`checkWithOverlay_sound`).
* `Tree.toPlan b k` turns a replacement tree into a `Plan`: a closed leaf
  becomes a pay node whose certificate is the leaf itself (identity motion),
  a hold keeps its recorded key, and a dyadic cut keeps the cut and derives
  child keys with `slotChild`, as `decodePlan` does.
* `Tree.toPlan_run`: if the tree passes `Tree.check check b` and the prefix
  check accepts every leaf `check` accepts, the plan runs on `b` and its held
  list is exactly `t.holds b`.

So a row theorem `tree.check overlayFixCheck root = true` (from the generated row modules)
gives a stage-row plan that runs under `checkWithOverlay prior` and hands the
holds, at their addresses, to the next stage. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay

namespace OverlayPlanar.Fix

def isOverlayBank (source : String) : Bool := source = hardBank || source = adaptiveBank

/-- The prior check, with Overlay planar witnesses paid by `fixPass`. -/
def checkWithOverlay (prior : WitnessRef → Cell → Bool) (w : WitnessRef) (b : Cell) : Bool :=
  if w.route = .strictFCC ∧ isOverlayBank w.source = true then fixPass b else prior w b

theorem checkWithOverlay_sound {prior : WitnessRef → Cell → Bool} (base : SoundCheck prior) :
    SoundCheck (checkWithOverlay prior) := by
  intro w b ok p bp gp
  by_cases c : w.route = .strictFCC ∧ isOverlayBank w.source = true
  · rw [c.1]
    exact energy_fcc_lt_of_fixPass (by simpa [checkWithOverlay, c] using ok) bp
  · exact base w b (by simpa [checkWithOverlay, c] using ok) p bp gp

/-- An Overlay bank witness accepted by `overlayFixCheck` is accepted by `checkWithOverlay`. -/
theorem checkWithOverlay_of_overlay (prior : WitnessRef → Cell → Bool) {w : WitnessRef} {b : Cell}
    (bank : isOverlayBank w.source = true) (h : overlayFixCheck w b = true) : checkWithOverlay prior w b = true := by
  obtain ⟨route, pass⟩ := Bool.and_eq_true_iff.mp h
  have r : w.route = .strictFCC := of_decide_eq_true route
  simp [checkWithOverlay, r, bank, pass]

end OverlayPlanar.Fix

/-- A replacement tree as an early-replay plan on the cell `b` with key `k`. -/
def Tree.toPlan (b : Cell) (k : Key) : Tree → Plan
  | .close w => .pay k ⟨w, b, identityMotion, b⟩
  | .hold key => .hold key
  | .split (.dyadic a) l r =>
      .split (.dyadic a) (l.toPlan ((Cut.dyadic a).child b false) (slotChild k a false))
        (r.toPlan ((Cut.dyadic a).child b true) (slotChild k a true))
  | .split (.rational a v) l r =>
      .split (.rational a v) (l.toPlan ((Cut.rational a v).child b false) k)
        (r.toPlan ((Cut.rational a v).child b true) k)

theorem sameCell_self (b : Cell) : sameCell b b = true :=
  decide_eq_true fun _ => ⟨rfl, rfl⟩

theorem insideCheck_identity (b : Cell) : insideCheck b (identityMotion.image b) = true := by
  refine decide_eq_true fun i => ?_
  simp [identityMotion, ChartMotion.image, shiftCell, shiftAmount]
  fin_cases i <;> simp

/-- Every closed leaf's witness satisfies `P`. -/
def Tree.witnessesAll (P : WitnessRef → Bool) : Tree → Bool
  | .close w => P w
  | .hold _ => true
  | .split _ l r => l.witnessesAll P && r.witnessesAll P

theorem Tree.toPlan_run {check check' : WitnessRef → Cell → Bool} {P : WitnessRef → Bool}
    (hcc : ∀ w c, P w = true → check w c = true → check' w c = true) (t : Tree) (b : Cell) (k : Key)
    (hP : t.witnessesAll P = true) (h : t.check check b = true) :
    ∃ paid, (t.toPlan b k).run check' b = some ⟨paid, t.holds b⟩ := by
  induction t generalizing b k with
  | close w =>
    refine ⟨[⟨k, b⟩], ?_⟩
    have c : (sameCell b b && (CertifiedClip.check ⟨w, b, identityMotion, b⟩ check')) = true := by
      simp only [sameCell_self, CertifiedClip.check, insideCheck_identity, Bool.true_and]
      exact hcc w b hP h
    simp only [Tree.toPlan, Plan.run, c, ite_true, Tree.holds]
  | hold key => exact ⟨[], by simp [Tree.toPlan, Plan.run, Tree.holds]⟩
  | split cut l r ihl ihr =>
    obtain ⟨fits, both⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp both
    obtain ⟨pl', pr'⟩ := Bool.and_eq_true_iff.mp hP
    cases cut with
    | dyadic a =>
      obtain ⟨pl, el⟩ := ihl _ (slotChild k a false) pl' hl
      obtain ⟨pr, er⟩ := ihr _ (slotChild k a true) pr' hr
      refine ⟨pl ++ pr, ?_⟩
      simp only [Tree.toPlan, Plan.run, fits, ite_true, el, er, Tree.holds]
      rfl
    | rational a v =>
      obtain ⟨pl, el⟩ := ihl _ k pl' hl
      obtain ⟨pr, er⟩ := ihr _ k pr' hr
      refine ⟨pl ++ pr, ?_⟩
      simp only [Tree.toPlan, Plan.run, fits, ite_true, el, er, Tree.holds]
      rfl

/-- A checked Overlay row as a stage row of the corpus prefix: under any prior check, its
plan runs on the row's cell and passes on exactly the row's held cells. -/
theorem OverlayPlanar.Fix.rowPlan_run (prior : WitnessRef → Cell → Bool) {t : Tree} {root : Cell}
    (h : t.check overlayFixCheck root = true)
    (bank : t.witnessesAll (fun w => OverlayPlanar.Fix.isOverlayBank w.source) = true) (k : Key) :
    ∃ paid, (t.toPlan root k).run (OverlayPlanar.Fix.checkWithOverlay prior) root = some ⟨paid, t.holds root⟩ :=
  Tree.toPlan_run (check := overlayFixCheck) (check' := OverlayPlanar.Fix.checkWithOverlay prior)
    (P := fun w => OverlayPlanar.Fix.isOverlayBank w.source)
    (fun _ _ hb hc => OverlayPlanar.Fix.checkWithOverlay_of_overlay prior hb hc) t root k bank h

end BccSharp.Coulomb.CompactCover
