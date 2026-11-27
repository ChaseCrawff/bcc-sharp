import BccSharp.Cover.DataPathLaterRun

set_option autoImplicit false

/-! # One sound checker for many chunks

`assemble_from_late_chunks` takes one prefix check `later`, one Stage6 checker `early` and one
late checker `late`, each with its soundness. The literal data's chunks carry their own hints
and tables, and state their run facts for any checker that accepts what their own check
accepts. The assembly's checkers are then
finite disjunctions of the chunks' checks, and a disjunction is sound when every disjunct is:

* `anyLater cs` for prefix witnesses: `anyLater_sound` from `SoundCheck` of each check (as
  `orCheck_sound` does for two);
* `anyStage6 cs` for Stage6 requests: `anyStage6_sound` from `Stage6CheckerSound` of each, and
  `orStage6`, `orStage6_sound` for two;
* `anyLate cs` for late requests: `anyLate_sound` from `LatePackets.CheckerSound` of each, and
  `orLate`, `orLate_sound` for two.

A disjunction accepts what any of its disjuncts accepts (`anyLater_of_mem`, `anyStage6_of_mem`,
`anyLate_of_mem`), which is each chunk's `hl`. Nothing here depends on the checks' contents.

**Clips paid source by source** (`clips_paid_of_sources`): many clips share a source (Stage4:
36,805 clips of 120 sources), and a clip's arithmetic is its source's. A chunk lists its
distinct (receipt, source cell) pairs once; one Bool per clip finds its pair in the list, and
the check runs once per listed source. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage EarlyReplay OverlayPlanar OverlayPlanar.Fix OverlayCorpus

namespace DataPath.Later

/-! ### Clips paid source by source -/

/-- **A chunk's clips, paid source by source**: when every clip's receipt and source cell are
among `srcs` and the check pays every listed pair, it pays every clip, in the form
`runEdits_clipEdits_corpus` takes. -/
theorem clips_paid_of_sources (mine : WitnessRef → Cell → Bool) (cs : List ClipSpec)
    (srcs : List (WitnessRef × Cell))
    (hm : cs.all (fun c => srcs.any fun x => decide (x.1 = c.receipt) && sameCell x.2 c.source) = true)
    (hs : srcs.all (fun x => ! isOverlayBank x.1.source && mine x.1 x.2) = true) :
    cs.all (fun c => ! isOverlayBank c.receipt.source && mine c.receipt c.source) = true := by
  rw [List.all_eq_true] at hm hs ⊢
  intro c hc
  obtain ⟨x, hx, hxc⟩ := List.any_eq_true.mp (hm c hc)
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hxc
  have e1 : x.1 = c.receipt := of_decide_eq_true h1
  have e2 : x.2 = c.source := sameCell_sound h2
  rw [← e1, ← e2]
  exact hs x hx

/-! ### Prefix witnesses -/

/-- A prefix witness is paid when one of the checks pays it. -/
def anyLater (cs : List (WitnessRef → Cell → Bool)) (w : WitnessRef) (b : Cell) : Bool :=
  cs.any fun c => c w b

theorem anyLater_sound (cs : List (WitnessRef → Cell → Bool)) (h : ∀ c ∈ cs, SoundCheck c) :
    SoundCheck (anyLater cs) := by
  intro w b ok p hp gp
  obtain ⟨c, hc, hcw⟩ := List.any_eq_true.mp ok
  exact h c hc w b hcw p hp gp

theorem anyLater_of_mem {cs : List (WitnessRef → Cell → Bool)} {c : WitnessRef → Cell → Bool}
    (hc : c ∈ cs) (w : WitnessRef) (b : Cell) (h : c w b = true) : anyLater cs w b = true :=
  List.any_eq_true.mpr ⟨c, hc, h⟩

/-! ### Stage6 requests -/

/-- A Stage6 request is paid when either check pays it. -/
def orStage6 (a b : Stage6Checker) : Stage6Checker := fun q => a q || b q

theorem orStage6_sound {a b : Stage6Checker} (ha : Stage6CheckerSound a) (hb : Stage6CheckerSound b) :
    Stage6CheckerSound (orStage6 a b) := by
  intro q hg ok p hp gp
  rcases Bool.or_eq_true_iff.mp ok with h | h
  · exact ha q hg h p hp gp
  · exact hb q hg h p hp gp

/-- A Stage6 request is paid when one of the checks pays it. -/
def anyStage6 (cs : List Stage6Checker) : Stage6Checker := fun q => cs.any fun c => c q

theorem anyStage6_sound (cs : List Stage6Checker) (h : ∀ c ∈ cs, Stage6CheckerSound c) :
    Stage6CheckerSound (anyStage6 cs) := by
  intro q hg ok p hp gp
  obtain ⟨c, hc, hcq⟩ := List.any_eq_true.mp ok
  exact h c hc q hg hcq p hp gp

theorem anyStage6_of_mem {cs : List Stage6Checker} {c : Stage6Checker} (hc : c ∈ cs) (q : Stage6Request)
    (h : c q = true) : anyStage6 cs q = true :=
  List.any_eq_true.mpr ⟨c, hc, h⟩

/-! ### Late requests -/

/-- A late request is paid when either check pays it. -/
def orLate (a b : LatePackets.Checker) : LatePackets.Checker := fun q => a q || b q

theorem orLate_sound {a b : LatePackets.Checker} (ha : LatePackets.CheckerSound a)
    (hb : LatePackets.CheckerSound b) : LatePackets.CheckerSound (orLate a b) := by
  intro q h1 h2 h3 ok p hp gp
  rcases Bool.or_eq_true_iff.mp ok with h | h
  · exact ha q h1 h2 h3 h p hp gp
  · exact hb q h1 h2 h3 h p hp gp

/-- A late request is paid when one of the checks pays it. -/
def anyLate (cs : List LatePackets.Checker) : LatePackets.Checker := fun q => cs.any fun c => c q

theorem anyLate_sound (cs : List LatePackets.Checker) (h : ∀ c ∈ cs, LatePackets.CheckerSound c) :
    LatePackets.CheckerSound (anyLate cs) := by
  intro q h1 h2 h3 ok p hp gp
  obtain ⟨c, hc, hcq⟩ := List.any_eq_true.mp ok
  exact h c hc q h1 h2 h3 hcq p hp gp

theorem anyLate_of_mem {cs : List LatePackets.Checker} {c : LatePackets.Checker} (hc : c ∈ cs)
    (q : LatePackets.Request) (h : c q = true) : anyLate cs q = true :=
  List.any_eq_true.mpr ⟨c, hc, h⟩

/-- A request that passes `closeCheck` under a check passes it under any check accepting at
least as much (the data checks do not depend on the check). -/
theorem closeCheck_mono {a b : LatePackets.Checker} (h : ∀ q, a q = true → b q = true)
    {q : LatePackets.Request} (ok : LatePackets.closeCheck a q = true) : LatePackets.closeCheck b q = true := by
  unfold LatePackets.closeCheck at ok ⊢
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp ok
  rw [h1, h q h2]
  rfl

end DataPath.Later

end BccSharp.Coulomb.CompactCover
