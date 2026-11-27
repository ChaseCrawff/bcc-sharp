import BccSharp.Cover.Stage3Stage6Compose
import BccSharp.Cover.AdaptiveGain

set_option autoImplicit false

/-! # Hybrid Stage5b and Stage6 `F` checks: proposed support first, box-built support second

Two sound checks prove `energy fcc < energy` on a box from a log-convex Jensen
support:

* `AdaptiveSupport.supportGainCheck` (`BccSharp.Cover.AdaptiveGain`) takes
  *proposed* anchors, constant phase floors, an optional reduction cut and the
  phase-triad gain, in about 1.1 s of kernel time per item;
* `Jensen.Fix.fLeafCheck` (`BccSharp.Cover.JensenFix`) builds every anchor from the box and
  uses sloped phase secants, in 17–30 s.

On the thin items proved here, most items certify with the proposals in the
kernel; the rest need the sloped secants. The hybrid checks
try a proposal, given as a hint per item, and fall back to the box-built check.
Boolean `||` reduces its left argument first, so an item whose hint passes
costs only the proposed check.

* `roundOut b`: the box rounded outward to the `2⁻⁶⁴` grid, which the
  fixed-point guard of `supportValue` needs; `mem_roundOut`.
* `SupportHint` (terms, cut, allocations) and `hintCheck h b`, sound for every
  hint (`hintCheck_sound`).
* `stage5bHybridCheck hint`: the dispatch of `stage5bPhaseCheck`
  (`stage5bHybridCheck_other`), sound for every hint function
  (`stage5bHybridCheck_sound`); `laterHybrid hint pending` and
  `later_compose_hybrid` as for `laterStage3Stage5b`. With no hint it is
  `stage5bPhaseCheck` (`stage5bHybridCheck_none`), and a hint only adds acceptance
  (`stage5bHybridCheck_of_phase`).
* `stage6FHybrid hint` and `stage6HybridCheck hint dEval`, with
  `stage6HybridCheck_sound : Stage6DSound dEval → Stage6CheckerSound …` for every
  hint function. With no hint it is `stage6Check` (`stage6HybridCheck_none`).

The hints are data; soundness does not
depend on them. -/

namespace BccSharp.Coulomb.CompactCover.Stage3Stage6
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayCorpus (orCheck orCheck_sound)

/-! ### Outward rounding to the `2⁻⁶⁴` grid -/

/-- `q` rounded down to the `2⁻⁶⁴` grid. -/
def floor64 (q : ℚ) : ℚ := (⌊q * 18446744073709551616⌋ : ℚ) / 18446744073709551616

/-- `q` rounded up to the `2⁻⁶⁴` grid. -/
def ceil64 (q : ℚ) : ℚ := (⌈q * 18446744073709551616⌉ : ℚ) / 18446744073709551616

theorem floor64_le (q : ℚ) : floor64 q ≤ q := by
  unfold floor64
  rw [div_le_iff₀ (by norm_num)]
  exact Int.floor_le _

theorem le_ceil64 (q : ℚ) : q ≤ ceil64 q := by
  unfold ceil64
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _

/-- The box rounded outward to the `2⁻⁶⁴` grid. -/
def roundOut (b : Cell) : Cell := ⟨fun i => floor64 (b.lo i), fun i => ceil64 (b.hi i)⟩

theorem mem_roundOut {b : Cell} {p : Chart} (hp : b.Mem p) : (roundOut b).Mem p := by
  intro i
  obtain ⟨h1, h2⟩ := hp i
  have c1 : ((floor64 (b.lo i) : ℚ) : ℝ) ≤ ((b.lo i : ℚ) : ℝ) := by
    exact_mod_cast floor64_le (b.lo i)
  have c2 : ((b.hi i : ℚ) : ℝ) ≤ ((ceil64 (b.hi i) : ℚ) : ℝ) := by
    exact_mod_cast le_ceil64 (b.hi i)
  exact ⟨c1.trans h1, h2.trans c2⟩

/-! ### The proposed support as a hint -/

/-- A proposed log-convex Jensen support for one item (`AdaptiveSupport`): the terms
with their anchors, the optional reduction cut and the phase-triad allocations. -/
structure SupportHint where
  terms : List AdaptiveSupport.Term
  cut : Option AdaptiveSupport.Cut
  allocs : List AdaptiveSupport.Alloc

/-- The hint's check on the box rounded outward; `false` without a hint. -/
def hintCheck (h : Option SupportHint) (b : Cell) : Bool :=
  match h with
  | some h => AdaptiveSupport.supportGainCheck (roundOut b) h.terms h.cut h.allocs
  | none => false

/-- Every accepted hint proves `energy fcc < energy` at every `good` point of the box. -/
theorem hintCheck_sound {h : Option SupportHint} {b : Cell} (ok : hintCheck h b = true)
    (p : Chart) (hp : b.Mem p) (gp : good p) : energy fcc < energy (chartPoint p) := by
  cases h with
  | none => simp [hintCheck] at ok
  | some h =>
    exact AdaptiveSupport.supportGainCheck_sound _ _ _ _ ok p (mem_roundOut hp) gp

/-! ### The Stage5b phase and `whole_above` witnesses -/

/-- The Stage5b check with hints: the proposed support first, then the box-built
Jensen support with the source's profile. The dispatch is that of
`Stage5bPhase.stage5bPhaseCheck`. -/
def stage5bHybridCheck (hint : WitnessRef → Option SupportHint) (w : WitnessRef) (b : Cell) :
    Bool :=
  decide (w.route = .strictFCC) &&
    match Stage5bPhase.profile w.source with
    | some (s, L, N) => hintCheck (hint w) b || Jensen.Fix.fLeafCheck s L N b b
    | none => false

theorem stage5bHybridCheck_sound (hint : WitnessRef → Option SupportHint) :
    SoundCheck (stage5bHybridCheck hint) := by
  intro w b ok p hp gp
  unfold stage5bHybridCheck at ok
  obtain ⟨hr, hc⟩ := Bool.and_eq_true_iff.mp ok
  have hroute : w.route = .strictFCC := of_decide_eq_true hr
  rw [hroute]
  split at hc
  · simp only [Bool.or_eq_true] at hc
    rcases hc with h | h
    · exact hintCheck_sound h p hp gp
    · exact Jensen.Fix.fLeafCheck_route _ _ _ b b h p hp gp
  · exact absurd hc (by simp)

/-- **Dispatch rule.** The hybrid check rejects every witness whose source is not
one of the four exact Stage5b strings, whatever its route, cell and hint. -/
theorem stage5bHybridCheck_other (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (b : Cell) (h0 : w.source ≠ "stage5b/phase/0") (h1 : w.source ≠ "stage5b/phase/1")
    (h2 : w.source ≠ "stage5b/phase/2") (h3 : w.source ≠ "stage5b/whole_above") :
    stage5bHybridCheck hint w b = false := by
  unfold stage5bHybridCheck
  rw [profile_eq_none _ h0 h1 h2 h3]
  simp

/-- With no hint, the hybrid check is the box-built check `stage5bPhaseCheck`. -/
theorem stage5bHybridCheck_none : stage5bHybridCheck (fun _ => none) = Stage5bPhase.stage5bPhaseCheck := by
  funext w b
  unfold stage5bHybridCheck Stage5bPhase.stage5bPhaseCheck
  generalize Stage5bPhase.profile w.source = o
  rcases o with _ | ⟨s, L, N⟩ <;> rfl

/-- A hint only adds acceptance: whatever `stage5bPhaseCheck` accepts, the hybrid
check accepts for every hint function. -/
theorem stage5bHybridCheck_of_phase (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (b : Cell) (h : Stage5bPhase.stage5bPhaseCheck w b = true) : stage5bHybridCheck hint w b = true := by
  unfold Stage5bPhase.stage5bPhaseCheck at h
  unfold stage5bHybridCheck
  generalize Stage5bPhase.profile w.source = o at h ⊢
  rcases o with _ | ⟨s, L, N⟩
  · simp at h
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨h.1, Or.inr h.2⟩

/-- This module\'s share of `later` with hints. -/
def laterHybrid (hint : WitnessRef → Option SupportHint) (pending : WitnessRef → Cell → Bool) :
    WitnessRef → Cell → Bool :=
  orCheck (stage5bHybridCheck hint) pending

theorem laterHybrid_sound (hint : WitnessRef → Option SupportHint)
    {pending : WitnessRef → Cell → Bool} (h : SoundCheck pending) :
    SoundCheck (laterHybrid hint pending) :=
  orCheck_sound (stage5bHybridCheck_sound hint) h

/-- **The `later` slot with hints.** Any sound check of the Adaptive stages composes
with this share, for every hint function. -/
theorem later_compose_hybrid (hint : WitnessRef → Option SupportHint)
    {adaptiveRoute pending : WitnessRef → Cell → Bool} (h17 : SoundCheck adaptiveRoute) (hp : SoundCheck pending) :
    SoundCheck (orCheck adaptiveRoute (laterHybrid hint pending)) :=
  orCheck_sound h17 (laterHybrid_sound hint hp)

/-! ### The Stage6 checker with hints -/

/-- The Stage6 `F` test with a hint: the proposed support on the target box first,
then the box-built support on the entry's support box (`stage6FCheck`). -/
def stage6FHybrid (hint : Stage6Request → Option SupportHint) (q : Stage6Request) : Bool :=
  hintCheck (hint q) q.proposal.target || stage6FCheck q

/-- The Stage6 checker with hints: `F` entries by `stage6FHybrid`, `D` entries by `dEval`. -/
def stage6HybridCheck (hint : Stage6Request → Option SupportHint) (dEval : Stage6Request → Bool) :
    Stage6Checker := fun q =>
  match q.proposal.compare with
  | .fcc => stage6FHybrid hint q
  | .deficit => dEval q

/-- **`Stage6CheckerSound`** for the checker with hints, for every hint function,
from the soundness of the defect evaluator alone. -/
theorem stage6HybridCheck_sound (hint : Stage6Request → Option SupportHint)
    {dEval : Stage6Request → Bool} (hd : Stage6DSound dEval) :
    Stage6CheckerSound (stage6HybridCheck hint dEval) := by
  intro q _ ok p hp gp
  unfold stage6HybridCheck at ok
  unfold Stage6Proposal.route
  cases hc : q.proposal.compare with
  | fcc =>
    rw [hc] at ok
    unfold stage6FHybrid at ok
    simp only [Bool.or_eq_true] at ok
    rcases ok with h | h
    · exact hintCheck_sound h p hp gp
    · exact Jensen.Fix.fLeafCheck_sound _ _ _ _ _ h p hp gp.1
  | deficit =>
    rw [hc] at ok
    exact hd q ok p hp gp

/-- With no hint, the Stage6 checker with hints is `stage6Check`. -/
theorem stage6HybridCheck_none (dEval : Stage6Request → Bool) :
    stage6HybridCheck (fun _ => none) dEval = stage6Check dEval := by
  funext q
  unfold stage6HybridCheck stage6Check stage6FHybrid
  generalize q.proposal.compare = c
  cases c <;> rfl

/-- With no `D` evaluator yet: only `F` entries are accepted. -/
def stage6HybridNow (hint : Stage6Request → Option SupportHint) : Stage6Checker :=
  stage6HybridCheck hint fun _ => false

theorem stage6HybridNow_sound (hint : Stage6Request → Option SupportHint) :
    Stage6CheckerSound (stage6HybridNow hint) :=
  stage6HybridCheck_sound hint fun _ h => absurd h (by simp)

end BccSharp.Coulomb.CompactCover.Stage3Stage6
