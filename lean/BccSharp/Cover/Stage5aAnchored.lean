import BccSharp.Cover.Stage4Stage5a

set_option autoImplicit false

/-! # The anchored route of Stage5a (route `strictDeficit`)

A Stage5a `anchored` source is paid by `deficit(anchor) − loss > 0`: a positive lower bound of the anchor's
deficit (its Taylor bound of `e(a) − e_BCC − g·Q(a)` over the shape box, `1.6·10⁻⁵` to
`5.6·10⁻⁵`) and the optical change, whose surplus over `200 g |h|²` it bounds below by
`−0.092` to `−0.037`. Lean's layered gain does better: `BccSharp.Cover.Stage4Stage5a` is forecast
(`#eval`, untrusted) to pay all but one Stage5a source on the relative route, and nine Stage5a
sources are kernel items there. This module is meant for sources that
no relative payment pays: by the forecast, one Stage5a source (through split depth 2) and
twelve Stage4 Taylor sources (through depth 3), and possibly the five wide cubic-reference
Stage4 sources; the two wide FCC sources need an FCC transport instead. Its payment is the layered gain with a negative coefficient, paid by the
anchor's deficit.

It proves the part that does not depend on the anchor bound and states the anchor bound as
an interface:

* `deficit_of_gain`: a layered gain with any `λ ≥ 2 a_c (200 g + k)` and
  `D(p) ≤ D(a) + 200 |h|²` give `deficit(a) + k |h|² ≤ deficit(p)` at the all-half
  anchor `a`, for every sign of `k` and of `200 g + k`; `lamS k` is such a `λ`
  (`lamS_bound`), with `a_c⁻` in place of `a_c⁺` when `200 g⁺ + k < 0` (for example on the
  Stage5a sources with `k` at the surplus, where `200 g⁺ ≈ 0.0111`);
  `gainOkK` is the gain check with `λ = lamS k`;
* `AnchorSound ev`: `ev w box m = true` certifies `m ≤ deficit(a)` at every good point of
  the box. `anchorZero` (`m ≤ 0`, from `LatticeCase`) is sound but only a sanity instance:
  with it `anchoredOk` is `false` on every input, so `stage5aCheck anchorZero` accepts nothing;
* `anchoredOk ev w signed cubic c m box n`: the gain (`gainOkK`), the far transport
  (`transOk`), `ev w box m` and `0 < m + min 0 (k b⁺)` with `b⁺` the seam cell's bound of
  `|h|²`; `anchoredOk_sound` gives `0 < deficit` at every good point;
* `stage5aCheck ev hint`: the exact sources of `BccSharp.Cover.Stage4Stage5a` on route `strictDeficit`,
  with `stage5aCheck_sound : AnchorSound ev → SoundCheck (stage5aCheck ev hint)`; it composes by
  `orCheck`.

No anchor evaluator strong enough for those sources is part of this module (by `#eval`
probes they need `m` of about `2·10⁻⁷` for the Taylor sources, and `5·10⁻⁸` for the Stage5a
source with the gain at split depth 2). -/

open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Stage4Stage5a
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-! ### The gain coefficient for any sign -/

/-- The layered gain parameter for the deficit coefficient `k`: `2 a_c⁺ (200 g⁺ + k)` when
`200 g⁺ + k ≥ 0` (this is `lamOf k`), else `2 a_c⁻ (200 g⁺ + k)`. The energy gain
coefficient `200 g + k` may be negative, for example on the Stage5a sources with `k` at the
surplus. -/
def lamS (k : ℚ) : ℚ :=
  if 0 ≤ 200 * Constants.gapBracket.hi + k then 2 * DirectRoute.scaleWitness.upper * (200 * Constants.gapBracket.hi + k)
  else 2 * DirectRoute.scaleWitness.lower * (200 * Constants.gapBracket.hi + k)

theorem lamS_bound (k : ℚ) : (2 * ac) * (200 * gap + (k : ℝ)) ≤ (lamS k : ℝ) := by
  obtain ⟨acLo, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := Constants.reference_gap_checked.1.2
  have h1 : (2 * ac) * (200 * gap + (k : ℝ)) ≤ (2 * ac) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  unfold lamS
  split_ifs with h
  · have hX : (0 : ℝ) ≤ 200 * (Constants.gapBracket.hi : ℝ) + k := by exact_mod_cast h
    push_cast
    have h2 : (2 * ac) * (200 * (Constants.gapBracket.hi : ℝ) + k) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
      mul_le_mul_of_nonneg_right (by linarith) hX
    linarith
  · have hX : 200 * (Constants.gapBracket.hi : ℝ) + k < 0 := by exact_mod_cast (not_le.mp h)
    push_cast
    have h2 : (2 * ac) * (200 * (Constants.gapBracket.hi : ℝ) + k) ≤
        (2 * (DirectRoute.scaleWitness.lower : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
      mul_le_mul_of_nonpos_right (by linarith) hX.le
    linarith

/-- The layered gain with `λ = lamS k`: `splitOk` or (`signed`) `splitOkS`. -/
def gainOkK (signed : Bool) (c : PlanarAnchorCert) (box : Cell) (n : IntVec) : Bool :=
  if signed then splitOkS (anchorW n) (lamS c.k) c.depth (shiftCell box (seamShiftW n))
  else splitOk (anchorW n) (lamS c.k) c.depth (shiftCell box (seamShiftW n))

theorem gainOkK_sound {signed : Bool} {c : PlanarAnchorCert} {box : Cell} {n : IntVec}
    (ok : gainOkK signed c box n = true) :
    GainOn (lamS c.k) (anchorW n) (shiftCell box (seamShiftW n)) := by
  intro p hp
  cases signed
  · exact splitOk_gain c.depth (by simpa [gainOkK] using ok) hp
  · exact splitOkS_gain c.depth (by simpa [gainOkK] using ok) hp

/-! ### The relative inequality for any sign of `k` -/

theorem deficit_of_gain (k lam : ℚ) (box : Cell) (n : IntVec)
    (hlam : (2 * ac) * (200 * gap + (k : ℝ)) ≤ (lam : ℝ))
    (hgain : GainOn lam (anchorW n) (shiftCell box (seamShiftW n)))
    (p : Chart) (hp : box.Mem p)
    (trans : defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n))) :
    deficit (anchorOf (chartPoint p) halfAll) +
      (k : ℝ) * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) ≤
        deficit (chartPoint p) := by
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨an, han⟩ : ∃ an, an = anchorW n := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb, ← han] at hgain
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  have gain := hgain hp'
  have hE : energy (chartPoint p') = energy (chartPoint p) := by
    rw [hp'def, chartPoint_shift, energy_wrap]
  have hA := anchor_chart_wrap p n
  rw [← hp'def, ← han] at hA
  have hEa : energy (chartPoint (anchorChart p' (an.k₁ / 2) (an.k₂ / 2))) =
      energy (anchorOf (chartPoint p) halfAll) := by rw [hA, energy_wrap]
  have hG := gram_eq p n
  rw [← hp'def, ← han] at hG
  obtain ⟨bq, hbq⟩ : ∃ x, x =
      sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) :=
    ⟨_, rfl⟩
  rw [← hbq] at hG trans
  rw [← hbq]
  rw [hE, hEa, hG] at gain
  have ac0 : 0 < ac := ac_positive
  have gap0 : 0 < gap := Constants.reference_gap_checked.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (200 * gap + (k : ℝ)) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((200 * gap + (k : ℝ)) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  unfold deficit
  have h1 := mul_le_mul_of_nonneg_left trans gap0.le
  nlinarith

/-! ### Anchor bounds -/

/-- `ev w box m = true` certifies `m ≤ deficit (anchorOf (chartPoint p) halfAll)` at every
good point `p` of `box`. -/
def AnchorSound (ev : WitnessRef → Cell → ℚ → Bool) : Prop :=
  ∀ w box m, ev w box m = true → ∀ p, box.Mem p → good p →
    (m : ℝ) ≤ deficit (anchorOf (chartPoint p) halfAll)

/-- The trivial anchor bound `m ≤ 0`: sound, but `anchoredOk` needs `0 < m + min 0 (k b⁺)`,
so with it `anchoredOk` never holds; a sanity instance of `AnchorSound` only. -/
def anchorZero (_w : WitnessRef) (_box : Cell) (m : ℚ) : Bool := decide (m ≤ 0)

theorem anchorZero_sound (latticeCase : LatticeCase) : AnchorSound anchorZero := by
  intro w box m ok p _ gp
  have hm : (m : ℝ) ≤ 0 := by exact_mod_cast of_decide_eq_true ok
  have h := bravais_comparison_from_lattice latticeCase (anchorOf (chartPoint p) halfAll)
    (anchor_valid _ gp.1 halfAll halfAll_half) halfAll_half
  linarith [h.1]

/-! ### The anchored payment -/

/-- Either transport check contains the guards of the seam cell. -/
theorem transOk_guards {cubic : Bool} {reg : JLeaf.RegData} {box : Cell} {n : IntVec}
    (ok : transOk cubic reg box n = true) : guardsOk (shiftCell box (seamShiftW n)) = true := by
  cases cubic
  · simp only [transOk, Bool.false_eq_true, ↓reduceIte, farTransportOk, Bool.and_eq_true] at ok
    exact ok.2.1.1
  · simp only [transOk, ↓reduceIte, farTransportOkC, Bool.and_eq_true] at ok
    exact ok.2.1.1

/-- The bound `b⁺` of `|R (f − f₀ − n)|²` on the box (from the seam cell, `gramF_mem`). -/
def gramHi (box : Cell) (n : IntVec) : ℚ :=
  ((gramF (shiftCell box (seamShiftW n)) (anchorW n)).hi : ℚ) / Sz

/-- **The anchored payment.** -/
def anchoredOk (ev : WitnessRef → Cell → ℚ → Bool) (w : WitnessRef) (signed cubic : Bool)
    (c : PlanarAnchorCert) (m : ℚ) (box : Cell) (n : IntVec) : Bool :=
  (gainOkK signed c box n && transOk cubic c.reg box n) &&
    (ev w box m && decide (0 < m + min 0 (c.k * gramHi box n)))

theorem anchoredOk_sound {ev : WitnessRef → Cell → ℚ → Bool} (hev : AnchorSound ev)
    (w : WitnessRef) (signed cubic : Bool) (c : PlanarAnchorCert) (m : ℚ) (box : Cell) (n : IntVec)
    (ok : anchoredOk ev w signed cubic c m box n = true) (p : Chart) (hp : box.Mem p)
    (gp : good p) : 0 < deficit (chartPoint p) := by
  simp only [anchoredOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hgain, htr⟩, hev', hpos⟩ := ok
  have rel := deficit_of_gain c.k (lamS c.k) box n (lamS_bound c.k) (gainOkK_sound hgain) p hp
    (transOk_sound htr p hp gp)
  have anc := hev w box m hev' p hp gp
  -- `|h|² ≤ b⁺` on the box
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  have hg : guardsOk b = true := by rw [hb]; exact transOk_guards htr
  have g : Guards b := by
    have := of_decide_eq_true hg
    exact ⟨this.1, this.2.1, this.2.2⟩
  have gramUp := (gramF_mem hp' g (anchorW n)).2
  have hG := gram_eq p n
  rw [← hp'def] at hG
  rw [hb] at gramUp
  rw [hG] at gramUp
  set bq := sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) with hbq
  have bq0 : 0 ≤ bq := sq_nonnegative _
  have bqHi : bq ≤ ((gramHi box n : ℚ) : ℝ) := by
    unfold gramHi
    push_cast
    exact gramUp
  have hposR : (0 : ℝ) < m + min 0 ((c.k : ℝ) * ((gramHi box n : ℚ) : ℝ)) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hpos
    push_cast at this
    exact this
  have hkb : min 0 ((c.k : ℝ) * ((gramHi box n : ℚ) : ℝ)) ≤ (c.k : ℝ) * bq := by
    rcases le_total 0 (c.k : ℝ) with hk | hk
    · exact (min_le_left _ _).trans (mul_nonneg hk bq0)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left bqHi hk)
  linarith

/-! ### The check -/

/-- The payment of one anchored witness. -/
structure AHint where
  signed : Bool
  cubic : Bool
  cert : PlanarAnchorCert
  margin : ℚ
  wrap : IntVec

/-- **The anchored check**: the four exact sources of `stage4stage5aCheck`, route
`strictDeficit`, with an anchor bound `ev`. -/
def stage5aCheck (ev : WitnessRef → Cell → ℚ → Bool) (hint : WitnessRef → Option AHint)
    (w : WitnessRef) (b : Cell) : Bool :=
  if ownSource w.source then
    match w.route, hint w with
    | .strictDeficit, some h => anchoredOk ev w h.signed h.cubic h.cert h.margin b h.wrap
    | _, _ => false
  else false

theorem stage5aCheck_sound {ev : WitnessRef → Cell → ℚ → Bool} (hev : AnchorSound ev)
    (hint : WitnessRef → Option AHint) : SoundCheck (stage5aCheck ev hint) := by
  intro w b ok p hp gp
  unfold stage5aCheck at ok
  split_ifs at ok with tag
  generalize hh : hint w = h at ok
  cases h with
  | none => cases hr : w.route <;> simp [hr] at ok
  | some h =>
    cases hr : w.route <;> simp [hr] at ok
    exact anchoredOk_sound hev w h.signed h.cubic h.cert h.margin b h.wrap ok p hp gp

theorem stage5aCheck_other (ev : WitnessRef → Cell → ℚ → Bool) (hint : WitnessRef → Option AHint)
    {w : WitnessRef} (b : Cell) (h : ownSource w.source = false) : stage5aCheck ev hint w b = false := by
  unfold stage5aCheck
  simp [h]

end BccSharp.Coulomb.CompactCover.Stage4Stage5a
