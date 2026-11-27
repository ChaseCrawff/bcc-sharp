import BccSharp.Cover.AdaptiveScreened
import BccSharp.Cover.LeafFixFar

set_option autoImplicit false

/-! # The Adaptive direct BCC-star comparison (letter `V`, route `strictDeficit`)

A box is marked `V` in the Adaptive cover when its finite Ewald energy exceeds `e_BCC + g D⁺` on the whole box, where `D⁺` is an
upper bound of the capped defect from one BCC registration. This module checks such a box on
route `strictDeficit` (`0 < deficit` at every `good` point):

* the energy side is the Jensen support of `BccSharp.Cover.AdaptiveSupport` with the phase-triad gain
  (`lowH`: `supportValue + gainValue`, or the screened `screenValue + gainValueI + screenConstS`
  with `screenConstS/S = ⌊89 S/605⌋/S ≤ 89/605`), a certified lower bound `H/S ≤ h₂` at every
  `good` point of the box (`lowH_sound`);
* the defect side is a whole-box cap `defect ≤ cap/S` from one literal registration
  (`capOk`): the guards of `CompactCover.LeafFix.regGuards`, the registered cost `costAt` at all
  256 corners at most `cap`, and either `annFarOk` (`defect_le_cap_far`, any cap) or
  `2 cap ≤ S` (`defect_le_cap`) (`capOk_sound`);
* the comparison is `dCornerOk`'s, at scale `S³`:
  `2 a_c (e_BCC⁺ + g⁺ cap/S) < H/S − 4`, with `energy = (h₂ − 4)/(2 a_c)` (`vLeaf_sound`).

`DPay` adds the closed halving `split k r l u` of `AdaptivePay`. Nothing in the payment data is
trusted: the kernel recomputes every bound from the box. -/

open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BccSharp.Coverage BravaisCover DirectRoute Stage2 OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf (RegData regCost)

/-! ### The h₂ lower bound -/

/-- The certified lower bound of `S h₂` on the box from the (screened, if `scr`) support of
`ts` with cut `c` and the triad gain of `rs`. -/
def lowH (b : Cell) (scr : Bool) (ts : List Term) (c : Option Cut) (rs : List Alloc) : Option ℤ :=
  if scr then
    match screenValue b ts c, gainValueI b ts rs with
    | some L, some g => some (L + g + screenConstS)
    | _, _ => none
  else
    match supportValue b ts c, gainValue b ts rs with
    | some L, some g => some (L + g)
    | _, _ => none

theorem lowH_sound (b : Cell) (scr : Bool) (ts : List Term) (c : Option Cut) (rs : List Alloc)
    (H : ℤ) (hH : lowH b scr ts c rs = some H) (p : Chart) (hp : b.Mem p) (gp : good p) :
    (H : ℝ) / Sz ≤ h₂ (chartPoint p) := by
  have sp := Sz_pos
  unfold lowH at hH
  cases scr with
  | true =>
    simp only [ite_true] at hH
    cases hL : screenValue b ts c with
    | none => rw [hL] at hH; simp at hH
    | some L =>
      cases hg : gainValueI b ts rs with
      | none => rw [hL, hg] at hH; simp at hH
      | some g =>
        rw [hL, hg] at hH
        simp only [Option.some.injEq] at hH
        subst hH
        obtain ⟨hd, inc, allOk, ⟨B, hB, pos⟩, bound⟩ := screenValue_sound b ts c L hL p hp gp
        have gain := gainValueI_sound b ts rs g hg hd allOk
          (fun B' hB' => by rw [hB] at hB'; cases hB'; exact pos) p hp gp.1
        have split : (ts.map fun t => tCI b t * Real.exp (tXI p t)).sum + (ts.map (residI b p)).sum ≤
            (ts.map fun t => t.screened (chartPoint p)).sum := by
          rw [← lsum_add]
          exact sum_le_map (fun t ht => term_splitI b hd t (allOk t ht) hp gp.1)
        have phys := screened_le ts inc allOk _ gp.1
        have cst : (screenConstS : ℝ) / Sz ≤ 89 / 605 := by
          have f := fdiv_le (89 * Sz) 605 (by norm_num)
          unfold screenConstS
          rw [div_le_iff₀ sp]
          calc ((89 * Sz / 605 : ℤ) : ℝ) ≤ ((89 * Sz : ℤ) : ℝ) / ((605 : ℤ) : ℝ) := f
            _ = 89 / 605 * Sz := by push_cast; ring
        push_cast
        rw [add_div, add_div]
        linarith
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hH
    cases hL : supportValue b ts c with
    | none => rw [hL] at hH; simp at hH
    | some L =>
      cases hg : gainValue b ts rs with
      | none => rw [hL, hg] at hH; simp at hH
      | some g =>
        rw [hL, hg] at hH
        simp only [Option.some.injEq] at hH
        subst hH
        obtain ⟨hd, inc, allOk, ⟨B, hB, pos⟩, bound⟩ := supportValue_sound b ts c L hL p hp gp
        have gain := gainValue_sound b ts rs g hg hd allOk
          (fun B' hB' => by rw [hB] at hB'; cases hB'; exact pos) p hp gp.1
        have split : (ts.map fun t => tC b t * Real.exp (tX p t)).sum + (ts.map (resid b p)).sum ≤
            (ts.map fun t => t.mode.term (chartPoint p)).sum := by
          rw [← lsum_add]
          exact sum_le_map (fun t ht => term_split b hd t (allOk t ht) hp gp.1)
        have phys := physical_le ts inc allOk _ gp.1
        push_cast
        rw [add_div]
        linarith

/-! ### The whole-box defect cap -/

/-- The registered cost at the eight offset corners of one shape corner is at most `cap`. -/
def capOffsets (reg : RegData) (b : Cell) (sh : LeafFix.Shape) (strain cap : ℤ) : Bool :=
  LeafFix.bools.all fun b5 => LeafFix.bools.all fun b6 => LeafFix.bools.all fun b7 =>
    decide (LeafFix.costAt reg sh strain b b5 b6 b7 ≤ cap)

def capShape (reg : RegData) (b : Cell) (cap : ℤ) (sh : LeafFix.Shape) : Bool :=
  LeafFix.shapeGuard sh && capOffsets reg b sh (LeafFix.strainHi reg sh) cap

/-- **The whole-box defect cap** `cap/S` from the registration `reg`. -/
def capOk (reg : RegData) (b : Cell) (cap : ℤ) : Bool :=
  (decide (0 < b.lo 0) && decide (0 < b.lo 1) && decide (∀ i, b.lo i ≤ b.hi i) &&
      LeafFix.regGuards reg b && (JLeaf.Cutoff.annFarOk reg.N reg.w b || decide (2 * cap ≤ Sz))) &&
    LeafFix.bools.all fun b0 => LeafFix.bools.all fun b1 => LeafFix.bools.all fun b2 =>
      LeafFix.bools.all fun b3 => LeafFix.bools.all fun b4 =>
        capShape reg b cap (LeafFix.shapeOf b b0 b1 b2 b3 b4)

theorem capOk_sound (reg : RegData) (b : Cell) (cap : ℤ) (ok : capOk reg b cap = true) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) : defect (chartPoint p) ≤ (cap : ℝ) / Sz := by
  unfold capOk at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨l0, l1⟩, ord⟩, hrg⟩, hfar⟩, hall⟩ := ok
  have sp := Sz_pos
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast l0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast l1
  have ordR : ∀ i, (b.lo i : ℝ) ≤ b.hi i := fun i => by exact_mod_cast ord i
  have hc : ∀ bits, regCost reg.N reg.U reg.w (corner b bits) ≤ (cap : ℝ) / Sz := by
    intro bits
    have h5 := LeafFix.all_bool (LeafFix.all_bool (LeafFix.all_bool (LeafFix.all_bool
      (LeafFix.all_bool hall (bits 0)) (bits 1)) (bits 2)) (bits 3)) (bits 4)
    simp only [capShape, Bool.and_eq_true] at h5
    obtain ⟨hg, hoff⟩ := h5
    have hm := LeafFix.shapeOf_mem b bits hg
    have c0 := (LeafFix.corner_pos b bits 0 b0 (ordR 0)).ne'
    have c1 := (LeafFix.corner_pos b bits 1 b1 (ordR 1)).ne'
    have hcost := LeafFix.cost_ge reg b bits hm c0 c1
    have h8 := LeafFix.all_bool (LeafFix.all_bool (LeafFix.all_bool hoff (bits 5)) (bits 6)) (bits 7)
    simp only [decide_eq_true_eq] at h8
    have h8R : (LeafFix.costAt reg (LeafFix.shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))
        (LeafFix.strainHi reg (LeafFix.shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b
        (bits 5) (bits 6) (bits 7) : ℝ) ≤ cap := by exact_mod_cast h8
    rw [le_div_iff₀ sp]
    linarith
  rcases hfar with hf | hh
  · exact LeafFix.defect_le_cap_far reg b cap hrg hf b0 b1 hc p hp
  · exact LeafFix.defect_le_cap reg b cap hrg b0 b1 hh hc p hp hv

/-! ### The deficit comparison -/

/-- **The V leaf check**: `0 ≤ cap`, the comparison
`2 a_c (e_BCC⁺ + g⁺ cap/S) < H/S − 4` at scale `S³`, and the whole-box cap. -/
def vLeaf (b : Cell) (scr : Bool) (ts : List Term) (c : Option Cut) (rs : List Alloc) (reg : RegData)
    (cap : ℤ) : Bool :=
  match lowH b scr ts c rs with
  | some H =>
    decide (0 ≤ cap) && decide (LeafFix.acMulHi (LeafFix.bccHiZ * Sz + LeafFix.gapHiZ * cap) <
      (H - 4 * Sz) * Sz * Sz) && capOk reg b cap
  | none => false

theorem vLeaf_sound (b : Cell) (scr : Bool) (ts : List Term) (c : Option Cut) (rs : List Alloc)
    (reg : RegData) (cap : ℤ) (ok : vLeaf b scr ts c rs reg cap = true) (p : Chart) (hp : b.Mem p)
    (gp : good p) : 0 < deficit (chartPoint p) := by
  unfold vLeaf at ok
  cases hL : lowH b scr ts c rs with
  | none => rw [hL] at ok; simp at ok
  | some H =>
    rw [hL] at ok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨cap0, cmp⟩, capok⟩ := ok
    have sp := Sz_pos
    have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
    have hh := lowH_sound b scr ts c rs H hL p hp gp
    have hD := capOk_sound reg b cap capok p hp gp.1
    have X := LeafFix.acMulHi_ge (LeafFix.bccHiZ * Sz + LeafFix.gapHiZ * cap)
    have cmpR : (LeafFix.acMulHi (LeafFix.bccHiZ * Sz + LeafFix.gapHiZ * cap) : ℝ) <
        (((H - 4 * Sz) * Sz * Sz : ℤ) : ℝ) := by exact_mod_cast cmp
    push_cast at cmpR X
    have gle := LeafFix.gap_le
    have ble := LeafFix.bcc_le
    have g0 := LeafFix.gap_pos.le
    have cap0R : (0 : ℝ) ≤ cap := by exact_mod_cast cap0
    set Y : ℝ := (LeafFix.bccHiZ : ℝ) * Sz + (LeafFix.gapHiZ : ℝ) * cap with hY
    have s1 : 2 * ac * Y < ((H : ℝ) - 4 * Sz) * Sz := by
      have h1 : Sz * (2 * ac * Y) < Sz * (((H : ℝ) - 4 * Sz) * Sz) := by
        have e1 : Sz * (2 * ac * Y) = Sz * (2 * ac) * Y := by ring
        have e2 : Sz * (((H : ℝ) - 4 * Sz) * Sz) = ((H : ℝ) - 4 * Sz) * Sz * Sz := by ring
        rw [e1, e2]
        exact lt_of_le_of_lt X cmpR
      exact lt_of_mul_lt_mul_left h1 sp.le
    have gD : gap * defect (chartPoint p) ≤ (LeafFix.gapHiZ : ℝ) * cap / (Sz * Sz) := by
      calc gap * defect (chartPoint p) ≤ gap * ((cap : ℝ) / Sz) := mul_le_mul_of_nonneg_left hD g0
        _ ≤ ((LeafFix.gapHiZ : ℝ) / Sz) * ((cap : ℝ) / Sz) :=
          mul_le_mul_of_nonneg_right gle (div_nonneg cap0R sp.le)
        _ = (LeafFix.gapHiZ : ℝ) * cap / (Sz * Sz) := by rw [div_mul_div_comm]
    have sum : energy bcc + gap * defect (chartPoint p) ≤ Y / (Sz * Sz) := by
      have e2 : Y / (Sz * Sz) = (LeafFix.bccHiZ : ℝ) / Sz + (LeafFix.gapHiZ : ℝ) * cap / (Sz * Sz) := by
        rw [hY]
        field_simp
      rw [e2]
      linarith
    have s2 : 2 * ac * (Y / (Sz * Sz)) < ((H : ℝ) - 4 * Sz) / Sz := by
      have e3 : 2 * ac * (Y / (Sz * Sz)) = (2 * ac * Y / Sz) / Sz := by
        field_simp
      rw [e3]
      apply div_lt_div_of_pos_right _ sp
      rw [div_lt_iff₀ sp]
      exact s1
    have hl : ((H : ℝ) - 4 * Sz) / Sz ≤ h₂ (chartPoint p) - 4 := by
      have e4 : ((H : ℝ) - 4 * Sz) / Sz = (H : ℝ) / Sz - 4 := by
        field_simp
      rw [e4]
      linarith
    have s3 : 2 * ac * (energy bcc + gap * defect (chartPoint p)) < h₂ (chartPoint p) - 4 :=
      calc 2 * ac * (energy bcc + gap * defect (chartPoint p)) ≤ 2 * ac * (Y / (Sz * Sz)) :=
            mul_le_mul_of_nonneg_left sum acpos.le
        _ < ((H : ℝ) - 4 * Sz) / Sz := s2
        _ ≤ h₂ (chartPoint p) - 4 := hl
    have s4 : energy bcc + gap * defect (chartPoint p) < (h₂ (chartPoint p) - 4) / (2 * ac) := by
      rw [lt_div_iff₀ acpos]
      linarith
    have e : energy (chartPoint p) = (h₂ (chartPoint p) - 4) / (2 * ac) := rfl
    unfold deficit
    rw [e]
    linarith

/-! ### Payments with halving -/

/-- How a box is paid on route `strictDeficit`: a V leaf, or the two closed halves
`x_k ≤ r` and `x_k ≥ r`. -/
inductive DPay where
  | leaf (scr : Bool) (ts : List Term) (c : Option Cut) (rs : List Alloc) (reg : RegData) (cap : ℤ)
  | split (k : Axis) (r : ℚ) (left right : DPay)

def DPay.check : DPay → Cell → Bool
  | .leaf scr ts c rs reg cap, b => vLeaf b scr ts c rs reg cap
  | .split k r left right, b => left.check (replaceEnd b k r false) && right.check (replaceEnd b k r true)

theorem DPay.sound (pay : DPay) (b : Cell) (ok : pay.check b = true) (p : Chart) (hp : b.Mem p)
    (gp : good p) : 0 < deficit (chartPoint p) := by
  induction pay generalizing b with
  | leaf scr ts c rs reg cap => exact vLeaf_sound b scr ts c rs reg cap ok p hp gp
  | split k r left right ihl ihr =>
    obtain ⟨okl, okr⟩ := Bool.and_eq_true_iff.mp ok
    rcases two_closed_children b k r p hp with h | h
    · exact ihl _ okl h
    · exact ihr _ okr h

/-! ### Boxes off the grid `2^-64`

`toIBox` accepts only endpoints on the grid `2^-64`, so `supportValue` and `screenValue` are
`none` on any other box. `roundOut b` rounds the box outward to that grid; it contains `b`
(`roundOut_mem`), so a support check of `roundOut b` pays every point of `b`. -/

def floor64 (q : ℚ) : ℚ := ((⌊q * 18446744073709551616⌋ : ℤ) : ℚ) / 18446744073709551616
def ceil64 (q : ℚ) : ℚ := ((⌈q * 18446744073709551616⌉ : ℤ) : ℚ) / 18446744073709551616

/-- The box rounded outward to the grid `2^-64`. -/
def roundOut (b : Cell) : Cell := ⟨fun i => floor64 (b.lo i), fun i => ceil64 (b.hi i)⟩

theorem floor64_le (q : ℚ) : floor64 q ≤ q := by
  unfold floor64
  rw [div_le_iff₀ (by norm_num)]
  exact Int.floor_le _

theorem le_ceil64 (q : ℚ) : q ≤ ceil64 q := by
  unfold ceil64
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _

theorem roundOut_mem {b : Cell} {p : Chart} (hp : b.Mem p) : (roundOut b).Mem p := by
  intro i
  have h := hp i
  have l : ((floor64 (b.lo i) : ℚ) : ℝ) ≤ ((b.lo i : ℚ) : ℝ) := by exact_mod_cast floor64_le (b.lo i)
  have u : ((b.hi i : ℚ) : ℝ) ≤ ((ceil64 (b.hi i) : ℚ) : ℝ) := by exact_mod_cast le_ceil64 (b.hi i)
  exact ⟨l.trans h.1, h.2.trans u⟩

/-- The support check of the rounded box pays every point of the box. -/
theorem supportGainCheck_roundOut_sound (b : Cell) (ts : List Term) (c : Option Cut) (rs : List Alloc)
    (ok : supportGainCheck (roundOut b) ts c rs = true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  supportGainCheck_sound (roundOut b) ts c rs ok p (roundOut_mem hp) gp

theorem screenGainCheck_roundOut_sound (b : Cell) (ts : List Term) (c : Option Cut) (rs : List Alloc)
    (ok : screenGainCheck (roundOut b) ts c rs = true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  screenGainCheck_sound (roundOut b) ts c rs ok p (roundOut_mem hp) gp

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
