import BccSharp.Cover.AdaptiveScreened
import BccSharp.Cover.AdaptiveDeficit
import BccSharp.Cover.AdaptiveOptical
import BccSharp.Cover.CoverEarlyHandoff
import BccSharp.Cover.CoverReductionLeaves
import BccSharp.Cover.OverlayFixSound

set_option autoImplicit false

/-! The Adaptive part of the `later` slot of `corpusCheck`: one sound check for the terminal
marks of the Adaptive passes of stage 3.

An Adaptive witness carries the short source tag `adaptiveSource` (`"adaptiveRoute"`); a decoder of the Adaptive
batches maps every terminal of the 14 primary manifests to this tag, with the route of
its letter and a record number. The check reads the recipe of the terminal from a hint map
(`AdaptiveHint`) and is sound for every hint map (`adaptiveCheck_sound`), so the hints are proposal
data only:

* `direct pay` (letters `T J U Z R L I`): pay the leaf box on route `strictFCC`;
* `clipped cuts pay` (letter `K`): carve the proposed slab cuts off the box (`carve`),
  check that every carved slab has no reduced point (`normalizedStencilCheck`), then pay
  the rest on route `strictFCC`. The cuts are a KZ clip;
  nothing about them is trusted;
* `survivor pay` (letter `K`, without cut data): the same clip found by the kernel's own
  search (`reductionContract`, `reducedRegionCheck`), then pay the survivor box;
* `geometry` (letter `G`): `compactReductionCheck` or `normalizedStencilCheck`, route
  `invalidReduction`;
* `deficit pay` (letter `V`): the direct BCC-star comparison on route
  `strictDeficit` (`DPay`, `BccSharp.Cover.AdaptiveDeficit`): the support bound of `h₂`, a whole-box
  defect cap from one literal registration, and `0 < deficit` from both;
* `optical pay` (letters `Q`, `X`): the half-shift optical comparisons on route
  `relativeOptical` (`AdaptiveOptical.OPay`). They need `LatticeCase`, so `adaptiveCheck` rejects them and
  the separate check `adaptiveRelCheck` accepts them; `adaptiveFull` is the union of the two
  (`adaptiveFull_sound : LatticeCase → SoundCheck (adaptiveFull hint)`).

A box is paid (`AdaptivePay`) by `support ts c rs` (`supportGainCheck`: the log-convex support of
the terms `ts` with the optional reduction cut `c`, plus the phase-triad gain of the
allocations `rs`; with `rs = []` it is `supportCheck`), by `screened ts c rs`
(`screenGainCheck`: the same at Ewald screening `11/10`, letter `I`), by `planar` (the
fixed-point Overlay planar check `fixPass`), by `empty` (the geometry checks: the box has no
reduced point, so no `good` point, and every route result holds there), or by `split k r l u`
(the two closed halves of the box at `x_k = r`, paid by `l` and `u`).

Every other source, route or hint is rejected, so `orCheck (adaptiveCheck hint) other` composes
with any check that does not accept the tag `"adaptiveRoute"`. -/

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BccSharp.Coverage EarlyReplay

/-- The source tag of Adaptive witnesses. -/
def adaptiveSource : String := "adaptive-source"

/-- How a box is paid on route `strictFCC`. `split k r left right` pays the two closed
halves `x_k ≤ r` (by `left`) and `x_k ≥ r` (by `right`). -/
inductive AdaptivePay where
  | support (ts : List Term) (c : Option Cut) (rs : List Alloc)
  | screened (ts : List Term) (c : Option Cut) (rs : List Alloc)
  | planar
  | empty
  | split (k : Axis) (r : ℚ) (left right : AdaptivePay)

/-- How an Adaptive terminal is paid. -/
inductive AdaptiveHint where
  | direct (pay : AdaptivePay)
  | clipped (cuts : List SlabCut) (pay : AdaptivePay)
  | survivor (pay : AdaptivePay)
  | geometry
  | deficit (pay : DPay)
  | optical (pay : AdaptiveOptical.OPay)

def AdaptivePay.check : AdaptivePay → Cell → Bool
  | .support ts c rs, b => supportGainCheck b ts c rs
  | .screened ts c rs, b => screenGainCheck b ts c rs
  | .planar, b => OverlayPlanar.Fix.fixPass b
  | .empty, b => compactReductionCheck b || normalizedStencilCheck b
  | .split k r left right, b => left.check (replaceEnd b k r false) && right.check (replaceEnd b k r true)

theorem AdaptivePay.sound (pay : AdaptivePay) (b : Cell) (ok : pay.check b = true) (p : Chart) (hp : b.Mem p)
    (gp : good p) : energy fcc < energy (chartPoint p) := by
  induction pay generalizing b with
  | support ts c rs => exact supportGainCheck_sound b ts c rs ok p hp gp
  | screened ts c rs => exact screenGainCheck_sound b ts c rs ok p hp gp
  | planar => exact OverlayPlanar.Fix.energy_fcc_lt_of_fixPass ok hp
  | empty =>
    have none : ¬ reductionInequalities p := by
      rcases Bool.or_eq_true_iff.mp ok with o | o
      · exact compactReductionCheck_sound b o p hp
      · exact normalizedStencilCheck_sound b o p hp
    exact (none gp.2.1).elim
  | split k r left right ihl ihr =>
    obtain ⟨okl, okr⟩ := Bool.and_eq_true_iff.mp ok
    rcases two_closed_children b k r p hp with h | h
    · exact ihl _ okl h
    · exact ihr _ okr h

/-- The survivor of the exact KZ slab clip of a box. -/
def survivorBox (b : Cell) : Cell := (reductionContract b).2

/-- Carve the cuts off the box; every carved slab must have no reduced point; pay the rest. -/
def clipPay (cuts : List SlabCut) (pay : AdaptivePay) (b : Cell) : Bool :=
  match carve b cuts with
  | some (slabs, kept) => slabs.all normalizedStencilCheck && pay.check kept
  | none => false

theorem clipPay_sound (cuts : List SlabCut) (pay : AdaptivePay) (b : Cell) (ok : clipPay cuts pay b = true)
    (p : Chart) (hp : b.Mem p) (gp : good p) : energy fcc < energy (chartPoint p) := by
  unfold clipPay at ok
  cases h : carve b cuts with
  | none => rw [h] at ok; simp at ok
  | some result =>
    rcases result with ⟨slabs, kept⟩
    rw [h] at ok
    obtain ⟨paid, rest⟩ := Bool.and_eq_true_iff.mp ok
    rcases carve_cover b cuts slabs kept h p hp with ⟨slab, hs, inSlab⟩ | uncut
    · exact False.elim (normalizedStencilCheck_sound slab (List.all_eq_true.mp paid slab hs) p inSlab gp.2.1)
    · exact pay.sound kept rest p uncut gp

/-- **The Adaptive check.** -/
def adaptiveCheck (hint : WitnessRef → Option AdaptiveHint) (w : WitnessRef) (b : Cell) : Bool :=
  if w.source = adaptiveSource then
    match w.route, hint w with
    | .strictFCC, some (.direct pay) => pay.check b
    | .strictFCC, some (.clipped cuts pay) => clipPay cuts pay b
    | .strictFCC, some (.survivor pay) => reducedRegionCheck b (survivorBox b) && pay.check (survivorBox b)
    | .invalidReduction, some .geometry => compactReductionCheck b || normalizedStencilCheck b
    | .strictDeficit, some (.deficit pay) => pay.check b
    | _, _ => false
  else false

/-- **Soundness**, for every hint map. -/
theorem adaptiveCheck_sound (hint : WitnessRef → Option AdaptiveHint) : SoundCheck (adaptiveCheck hint) := by
  intro w b ok p hp gp
  unfold adaptiveCheck at ok
  split_ifs at ok with tag
  generalize hh : hint w = h at ok
  cases h with
  | none => cases hr : w.route <;> simp [hr] at ok
  | some h =>
    cases h with
    | direct pay =>
      cases hr : w.route <;> simp [hr] at ok
      exact pay.sound b ok p hp gp
    | clipped cuts pay =>
      cases hr : w.route <;> simp [hr] at ok
      exact clipPay_sound cuts pay b ok p hp gp
    | survivor pay =>
      cases hr : w.route <;> simp [hr] at ok
      exact pay.sound _ ok.2 p (reducedRegionCheck_sound b _ ok.1 p hp gp) gp
    | geometry =>
      cases hr : w.route <;> simp [hr] at ok
      rcases ok with o | o
      · exact compactReductionCheck_sound b o p hp
      · exact normalizedStencilCheck_sound b o p hp
    | deficit pay =>
      cases hr : w.route <;> simp [hr] at ok
      exact pay.sound b ok p hp gp
    | optical pay =>
      cases hr : w.route <;> simp [hr] at ok

/-- Off the tag the check rejects. -/
theorem adaptiveCheck_off (hint : WitnessRef → Option AdaptiveHint) {w : WitnessRef} (b : Cell)
    (h : w.source ≠ adaptiveSource) : adaptiveCheck hint w b = false := by
  unfold adaptiveCheck
  simp [h]

/-! ### The Lattice-relative routes -/

/-- **The Adaptive optical check** (letters `Q`, `X`, route `relativeOptical`). -/
def adaptiveRelCheck (hint : WitnessRef → Option AdaptiveHint) (w : WitnessRef) (b : Cell) : Bool :=
  if w.source = adaptiveSource then
    match w.route, hint w with
    | .relativeOptical, some (.optical pay) => pay.check b
    | _, _ => false
  else false

/-- **Soundness** of the optical check, for every hint map, from `LatticeCase`. -/
theorem adaptiveRelCheck_sound (latticeCase : LatticeCase) (hint : WitnessRef → Option AdaptiveHint) :
    SoundCheck (adaptiveRelCheck hint) := by
  intro w b ok p hp gp
  unfold adaptiveRelCheck at ok
  split_ifs at ok with tag
  generalize hh : hint w = h at ok
  cases h with
  | none => cases hr : w.route <;> simp [hr] at ok
  | some h =>
    cases h with
    | optical pay =>
      cases hr : w.route <;> simp [hr] at ok
      exact pay.sound latticeCase b ok p hp gp
    | _ => cases hr : w.route <;> simp [hr] at ok

theorem adaptiveRelCheck_off (hint : WitnessRef → Option AdaptiveHint) {w : WitnessRef} (b : Cell)
    (h : w.source ≠ adaptiveSource) : adaptiveRelCheck hint w b = false := by
  unfold adaptiveRelCheck
  simp [h]

/-- **Every Adaptive letter**: `adaptiveCheck` or `adaptiveRelCheck`. -/
def adaptiveFull (hint : WitnessRef → Option AdaptiveHint) (w : WitnessRef) (b : Cell) : Bool :=
  adaptiveCheck hint w b || adaptiveRelCheck hint w b

theorem adaptiveFull_sound (latticeCase : LatticeCase) (hint : WitnessRef → Option AdaptiveHint) :
    SoundCheck (adaptiveFull hint) := by
  intro w b ok p hp gp
  rcases Bool.or_eq_true_iff.mp ok with h | h
  · exact adaptiveCheck_sound hint w b h p hp gp
  · exact adaptiveRelCheck_sound latticeCase hint w b h p hp gp

theorem adaptiveFull_off (hint : WitnessRef → Option AdaptiveHint) {w : WitnessRef} (b : Cell)
    (h : w.source ≠ adaptiveSource) : adaptiveFull hint w b = false := by
  unfold adaptiveFull
  rw [adaptiveCheck_off hint b h, adaptiveRelCheck_off hint b h]
  rfl

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
