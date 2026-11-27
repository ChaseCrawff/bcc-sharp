import BccSharp.Cover.LeafFixSound
import BccSharp.TwoSite.DefectCutoffBox

set_option autoImplicit false

/-! # Fixed-point J and D leaf checks with the far-annulus defect bound

The J and D checks of `BccSharp.Cover.LeafFix` bound the capped defect by the
registered cost through `defect_le_regCost`, which needs that cost to be at most
`1/2`. They therefore test `2 C ≤ S` at every J corner and `2 cap ≤ S` for a D
cap. About 7.5 % of the late leaves of Corner, JointDeficit and Continuation round one have a
registered cost above `1/2`. This module gives J and D checks
without that limit. Instead, each checks `annFarOk reg.N reg.w b` on the leaf
box (`BccSharp.TwoSite.DefectCutoffBox`): all twelve annular images of the registration
are at least `13/10` long on the whole box, so `defect ≤ regCost` at every point
of the box, whatever the size of the cost (`defect_le_box_far`).

* `jLeafFarOk`: the guards of `jLeafOk`, the guard `annFarOk`, and the corner
  comparison of `jCornerOk` without `2 C ≤ S` (`jCornerFarOk`). The mixing
  weight `t = n/4096` combines `defect ≤ 1` and `defect ≤ regCost` as before,
  so a corner whose cost exceeds 1 passes when its comparison holds.
* `dLeafFarOk`: the guards of `dLeafOk` with `annFarOk` in place of
  `2 cap ≤ S`; the corners compare as in `dShape`.
* `jleafFar_sound` and `dleafFar_sound` conclude as `jleafFix_sound` and
  `dleafFix_sound` (`0 < deficit` at every valid point of the leaf box), and
  their `_good` forms give the routes `strictJoint` and `strictDeficit`.
  `defect_le_cap_far` is the whole-box defect cap for any `cap`.
* Certificates: `FarKind` is a `LeafKind` of `BccSharp.Cover.LeafFixSound` or one of
  the two new checks, and `FarCert` is `LeafCert` with that kind.
  `certCheckFar_sound : SoundCheck (certCheckFar T)` and
  `lateCheckFar_sound : LatePackets.CheckerSound (lateCheckFar T)` keep the
  shapes of `certCheck_sound` and `lateCheck_sound`. `FarCert.ofLeafCert`
  embeds the old certificates with the same check
  (`FarCert.check_ofLeafCert`, `certCheckFar_ofLeafCert`).

The checks and theorems of `BccSharp.Cover.LeafFix` and `BccSharp.Cover.LeafFixSound` are
unchanged. -/

open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.LeafFix
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Screened
open BccSharp.Coulomb.CompactCover.JLeaf.Cutoff (annFarOk defect_le_box_far)

/-! ### The checks -/

/-- The J comparison at one corner without a limit on the cost:
`sig/S² > 2 a_c (e_BCC + g (1 − n/4096 + (n/4096) C))`. -/
def jCornerFarOk (n : ℤ) (sig C : ℤ) : Bool :=
  decide (acMulHi (bccHiZ * Sz * 4096 + gapHiZ * ((4096 - n) * Sz + n * C)) < sig * Sz * 4096)

def jOffsetsFar (n : ℤ) (reg : RegData) (b : Cell) (sh : Shape) (base strain : ℤ) (c : OffC) :
    Bool :=
  bools.all fun b5 => bools.all fun b6 => bools.all fun b7 =>
    jCornerFarOk n (sigAt base c b b5 b6 b7) (costAt reg sh strain b b5 b6 b7)

def jShapeFar (s : ℚ) (n : ℤ) (agg : Agg) (reg : RegData) (b : Cell) (sh : Shape) : Bool :=
  shapeGuard sh && nlOk s agg.nls sh &&
    jOffsetsFar n reg b sh (baseOf s agg sh) (strainHi reg sh) (offCoef agg.lin sh)

/-- **The J leaf check with the far-annulus bound** at screening `s`, mixing
weight `n ≤ 4096`. -/
def jLeafFarOk (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (n : ℕ) : Bool :=
  (leafGuards box b && regGuards reg b && annFarOk reg.N reg.w b && decide (n ≤ 4096) &&
      nlsNonneg agg.nls) &&
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
      bools.all fun b4 => jShapeFar s n agg reg b (shapeOf b b0 b1 b2 b3 b4)

/-- **The D leaf check with the far-annulus bound**: a whole-box defect cap
`cap/S` of any size from one registration, and the strict deficit comparison
against it at every corner. -/
def dLeafFarOk (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (cap : ℤ) : Bool :=
  (leafGuards box b && regGuards reg b && annFarOk reg.N reg.w b && nlsNonneg agg.nls) &&
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
      bools.all fun b4 => dShape s cap agg reg b (shapeOf b b0 b1 b2 b3 b4)

/-! ### The whole-box defect cap -/

/-- **Whole-box defect cap, far annulus.** If a registration passes `regGuards`
and `annFarOk` on a box with positive radial coordinates, and its registered
cost is at most `cap/S` at every corner, then the actual capped defect is at
most `cap/S` at every point of the box. Nothing limits the size of `cap`. -/
theorem defect_le_cap_far (reg : RegData) (b : Cell) (cap : ℤ) (hr : regGuards reg b = true)
    (hf : annFarOk reg.N reg.w b = true) (b0 : (0 : ℝ) < b.lo 0) (b1 : (0 : ℝ) < b.lo 1)
    (hc : ∀ bits, regCost reg.N reg.U reg.w (corner b bits) ≤ (cap : ℝ) / Sz)
    (p : Chart) (hp : b.Mem p) : defect (chartPoint p) ≤ (cap : ℝ) / Sz := by
  obtain ⟨hreg, unit, cond⟩ := regGuards_sound hr
  have chord := regCost_chord reg.N reg.U reg.w b b0 b1 unit cond
  have hpC := le_of_corners chord hc p hp
  have hD := defect_le_box_far reg b hreg hf p hp
  linarith

/-! ### The J leaf -/

/-- **Soundness of the far-annulus J leaf check.** -/
theorem jleafFar_sound (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (n : ℕ)
    (hs : SupportFacts s box agg) (hl : jLeafFarOk s box b agg reg n = true) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) : 0 < deficit (chartPoint p) := by
  unfold jLeafFarOk at hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨⟨hgd, hrg⟩, hfar⟩, hn⟩, hnn⟩, hall⟩ := hl
  obtain ⟨inside, b0, b1, ord⟩ := leafGuards_sound hgd
  obtain ⟨hreg, unit, cond⟩ := regGuards_sound hrg
  have sp := Sz_pos
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  set T := minorant s agg with hT
  set C : Chart → ℝ := regCost reg.N reg.U reg.w with hC
  set t : ℝ := (n : ℝ) / 4096 with ht
  have t0 : 0 ≤ t := by positivity
  have t1 : t ≤ 1 := by
    rw [ht, div_le_one (by norm_num)]
    exact_mod_cast hn
  have g0 := gap_pos.le
  have gle := gap_le
  have ble := bcc_le
  -- the corners
  have corners : ∀ bits,
      0 < T (corner b bits) - energy bcc - gap * (1 - t + t * C (corner b bits)) := by
    intro bits
    have h5 := all_bool (all_bool (all_bool (all_bool (all_bool hall (bits 0)) (bits 1)) (bits 2))
      (bits 3)) (bits 4)
    simp only [jShapeFar, Bool.and_eq_true] at h5
    obtain ⟨⟨hg, hok⟩, hoff⟩ := h5
    obtain ⟨hm, c0, c1, hsig⟩ := corner_facts s hs.pos agg b bits b0 b1 ord hg hok hnn
    have hcost := cost_ge reg b bits hm c0 c1
    rw [← hC] at hcost
    have h8 := all_bool (all_bool (all_bool hoff (bits 5)) (bits 6)) (bits 7)
    simp only [jCornerFarOk, decide_eq_true_eq] at h8
    set Cz := costAt reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))
      (strainHi reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hCz
    set sig := sigAt (baseOf s agg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)))
      (offCoef agg.lin (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hsigd
    have cNn : 0 ≤ C (corner b bits) := regCost_nonneg _ _ _ _
    have X := acMulHi_ge (bccHiZ * Sz * 4096 + gapHiZ * ((4096 - (n : ℤ)) * Sz + (n : ℤ) * Cz))
    have hcmpR : (acMulHi (bccHiZ * Sz * 4096 + gapHiZ * ((4096 - (n : ℤ)) * Sz + (n : ℤ) * Cz)) : ℝ) <
        (sig : ℝ) * Sz * 4096 := by exact_mod_cast h8
    -- `T > X/(S² 4096)`
    set Xr : ℝ := ((bccHiZ * Sz * 4096 + gapHiZ * ((4096 - (n : ℤ)) * Sz + (n : ℤ) * Cz) : ℤ) : ℝ)
      with hXr
    have step1 : Sz * (2 * ac) * Xr < Sz * Sz * (2 * ac * T (corner b bits)) * Sz * 4096 := by
      have := mul_le_mul_of_nonneg_right hsig (by norm_num : (0 : ℝ) ≤ 4096)
      have h2 : (sig : ℝ) * Sz * 4096 ≤ Sz * Sz * (2 * ac * T (corner b bits)) * Sz * 4096 := by
        have := mul_le_mul_of_nonneg_right hsig (by positivity : (0 : ℝ) ≤ Sz * 4096)
        linarith
      linarith
    have step2 : Xr < Sz * Sz * T (corner b bits) * 4096 := by
      have hpos : 0 < Sz * (2 * ac) := mul_pos sp acpos
      have e : Sz * Sz * (2 * ac * T (corner b bits)) * Sz * 4096 =
          Sz * (2 * ac) * (Sz * Sz * T (corner b bits) * 4096) := by ring
      rw [e] at step1
      exact lt_of_mul_lt_mul_left step1 hpos.le
    -- `X/(S² 4096) ≥ e_BCC + g (1 − t + t C)`
    have nR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have mixLe : Sz * (1 - t + t * C (corner b bits)) * 4096 ≤
        (4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz := by
      rw [ht]
      have := mul_le_mul_of_nonneg_left hcost nR
      field_simp
      nlinarith
    have mix0 : 0 ≤ 1 - t + t * C (corner b bits) := by nlinarith
    have gapM : Sz * Sz * (gap * (1 - t + t * C (corner b bits))) * 4096 ≤
        (gapHiZ : ℝ) * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) := by
      rw [le_div_iff₀ sp] at gle
      have hM := mul_le_mul_of_nonneg_left mixLe g0
      have hG : gap * Sz * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) ≤
          (gapHiZ : ℝ) * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) := by
        apply mul_le_mul_of_nonneg_right gle
        have := mul_nonneg (mul_nonneg sp.le mix0) (by norm_num : (0 : ℝ) ≤ 4096)
        linarith
      nlinarith
    have bccM : Sz * Sz * energy bcc * 4096 ≤ (bccHiZ : ℝ) * Sz * 4096 := by
      rw [le_div_iff₀ sp] at ble
      nlinarith
    have Xe : Xr = (bccHiZ : ℝ) * Sz * 4096 + (gapHiZ : ℝ) * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) := by
      rw [hXr]; push_cast; ring
    rw [Xe] at step2
    have fin : Sz * Sz * (energy bcc + gap * (1 - t + t * C (corner b bits))) * 4096 <
        Sz * Sz * T (corner b bits) * 4096 := by
      nlinarith
    have hpos : (0 : ℝ) < Sz * Sz * 4096 := by positivity
    have : energy bcc + gap * (1 - t + t * C (corner b bits)) < T (corner b bits) := by
      have e1 : Sz * Sz * (energy bcc + gap * (1 - t + t * C (corner b bits))) * 4096 =
          (Sz * Sz * 4096) * (energy bcc + gap * (1 - t + t * C (corner b bits))) := by ring
      have e2 : Sz * Sz * T (corner b bits) * 4096 = (Sz * Sz * 4096) * T (corner b bits) := by ring
      rw [e1, e2] at fin
      exact lt_of_mul_lt_mul_left fin hpos.le
    linarith
  -- chords
  have hTc : ChordLower b T := hs.chord b b0 b1
  have hCc : ChordUpper b C := regCost_chord reg.N reg.U reg.w b b0 b1 unit cond
  set f : Chart → ℝ := fun x => T x - energy bcc - gap * (1 - t + t * C x) with hf
  have fc : ChordLower b f := by
    have h1 := chordLower_add hTc (chordLower_const b (-(energy bcc) - gap * (1 - t)))
    have h2 := chordLower_negSmul (c := -(gap * t)) (by nlinarith) hCc
    exact chordLower_congr (fun x => by simp only [hf]; ring) (chordLower_add h1 h2)
  have fpos := pos_of_corners fc (fun bits => corners bits) p hp
  -- the deficit: `defect ≤ regCost` on the whole box, whatever the cost
  have hE := hs.lower p (boxIn_sound inside hp) hv
  have hD := defect_le_box_far reg b hreg hfar p hp
  have hd := defect_range (chartPoint p)
  have cap : defect (chartPoint p) ≤ 1 - t + t * C p := by
    have c1 := mul_le_mul_of_nonneg_left hd.2 (sub_nonneg.mpr t1)
    have c2 := mul_le_mul_of_nonneg_left hD t0
    show defect (chartPoint p) ≤ 1 - t + t * regCost reg.N reg.U reg.w p
    nlinarith
  have credit := mul_le_mul_of_nonneg_left cap g0
  have fp : 0 < T p - energy bcc - gap * (1 - t + t * C p) := fpos
  unfold deficit
  linarith

theorem jleafFar_sound_good (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (n : ℕ)
    (hs : SupportFacts s box agg) (hl : jLeafFarOk s box b agg reg n = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) : Route.result .strictJoint p :=
  jleafFar_sound s box b agg reg n hs hl p hp gp.1

/-! ### The D leaf -/

/-- **Soundness of the far-annulus D leaf check**, with its whole-box defect cap. -/
theorem dleafFar_sound (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (cap : ℤ)
    (hs : SupportFacts s box agg) (hl : dLeafFarOk s box b agg reg cap = true) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) : 0 < deficit (chartPoint p) := by
  unfold dLeafFarOk at hl
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨⟨⟨hgd, hrg⟩, hfar⟩, hnn⟩, hall⟩ := hl
  obtain ⟨inside, b0, b1, ord⟩ := leafGuards_sound hgd
  have sp := Sz_pos
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  set T := minorant s agg with hT
  set C : Chart → ℝ := regCost reg.N reg.U reg.w with hC
  have g0 := gap_pos.le
  have gle := gap_le
  have ble := bcc_le
  have corners : ∀ bits, C (corner b bits) ≤ (cap : ℝ) / Sz ∧
      0 < T (corner b bits) - energy bcc - gap * ((cap : ℝ) / Sz) := by
    intro bits
    have h5 := all_bool (all_bool (all_bool (all_bool (all_bool hall (bits 0)) (bits 1)) (bits 2))
      (bits 3)) (bits 4)
    simp only [dShape, Bool.and_eq_true] at h5
    obtain ⟨⟨hg, hok⟩, hoff⟩ := h5
    obtain ⟨hm, c0, c1, hsig⟩ := corner_facts s hs.pos agg b bits b0 b1 ord hg hok hnn
    have hcost := cost_ge reg b bits hm c0 c1
    rw [← hC] at hcost
    have h8 := all_bool (all_bool (all_bool hoff (bits 5)) (bits 6)) (bits 7)
    simp only [dCornerOk, Bool.and_eq_true, decide_eq_true_eq] at h8
    obtain ⟨hCc, hcmp⟩ := h8
    set Cz := costAt reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))
      (strainHi reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hCz
    set sig := sigAt (baseOf s agg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)))
      (offCoef agg.lin (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hsigd
    have hCcr : (Cz : ℝ) ≤ cap := by exact_mod_cast hCc
    have cLe : C (corner b bits) ≤ (cap : ℝ) / Sz := by
      rw [le_div_iff₀ sp]
      linarith
    have cap0 : (0 : ℝ) ≤ (cap : ℝ) := by
      have := regCost_nonneg reg.N reg.U reg.w (corner b bits)
      have := mul_nonneg sp.le this
      linarith
    refine ⟨cLe, ?_⟩
    have X := acMulHi_ge (bccHiZ * Sz + gapHiZ * cap)
    have hcmpR : (acMulHi (bccHiZ * Sz + gapHiZ * cap) : ℝ) < (sig : ℝ) * Sz := by exact_mod_cast hcmp
    have step2 : ((bccHiZ * Sz + gapHiZ * cap : ℤ) : ℝ) < Sz * Sz * T (corner b bits) := by
      have h2 : (sig : ℝ) * Sz ≤ Sz * Sz * (2 * ac * T (corner b bits)) * Sz :=
        mul_le_mul_of_nonneg_right hsig sp.le
      have hpos : 0 < Sz * (2 * ac) := mul_pos sp acpos
      have e : Sz * Sz * (2 * ac * T (corner b bits)) * Sz = Sz * (2 * ac) * (Sz * Sz * T (corner b bits)) := by
        ring
      have : Sz * (2 * ac) * ((bccHiZ * Sz + gapHiZ * cap : ℤ) : ℝ) <
          Sz * (2 * ac) * (Sz * Sz * T (corner b bits)) := by linarith
      exact lt_of_mul_lt_mul_left this hpos.le
    push_cast at step2
    have gapM : Sz * Sz * (gap * ((cap : ℝ) / Sz)) ≤ (gapHiZ : ℝ) * cap := by
      rw [le_div_iff₀ sp] at gle
      have e : Sz * Sz * (gap * ((cap : ℝ) / Sz)) = gap * Sz * cap := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right gle cap0
    have bccM : Sz * Sz * energy bcc ≤ (bccHiZ : ℝ) * Sz := by
      rw [le_div_iff₀ sp] at ble
      nlinarith
    have hpos : (0 : ℝ) < Sz * Sz := by positivity
    have : energy bcc + gap * ((cap : ℝ) / Sz) < T (corner b bits) := by
      have fin : (Sz * Sz) * (energy bcc + gap * ((cap : ℝ) / Sz)) < (Sz * Sz) * T (corner b bits) := by
        nlinarith
      exact lt_of_mul_lt_mul_left fin hpos.le
    linarith
  have hTc : ChordLower b T := hs.chord b b0 b1
  set f : Chart → ℝ := fun x => T x - energy bcc - gap * ((cap : ℝ) / Sz) with hf
  have fc : ChordLower b f :=
    chordLower_congr (fun x => by simp only [hf]; ring)
      (chordLower_add hTc (chordLower_const b (-(energy bcc) - gap * ((cap : ℝ) / Sz))))
  have fpos := pos_of_corners fc (fun bits => (corners bits).2) p hp
  have hD := defect_le_cap_far reg b cap hrg hfar b0 b1 (fun bits => (corners bits).1) p hp
  have hE := hs.lower p (boxIn_sound inside hp) hv
  have credit := mul_le_mul_of_nonneg_left hD g0
  have fp : 0 < T p - energy bcc - gap * ((cap : ℝ) / Sz) := fpos
  unfold deficit
  linarith

theorem dleafFar_sound_good (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (cap : ℤ)
    (hs : SupportFacts s box agg) (hl : dLeafFarOk s box b agg reg cap = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) : Route.result .strictDeficit p :=
  dleafFar_sound s box b agg reg cap hs hl p hp gp.1

/-! ### Certificates in the shape of the cover composition -/

/-- The leaf comparison of a far certificate: a comparison of `LeafKind`, or
one of the two far-annulus checks. -/
inductive FarKind where
  | base (k : LeafKind)
  | dFar (reg : RegData) (cap : ℤ)
  | jFar (reg : RegData) (weight : ℕ)

def FarKind.route : FarKind → Route
  | .base k => k.route
  | .dFar _ _ => .strictDeficit
  | .jFar _ _ => .strictJoint

/-- A fixed-point leaf certificate whose J or D comparison may use the
far-annulus bound: screening, support box, witnesses, aggregate, leaf box and
leaf comparison. -/
structure FarCert where
  s : ℚ
  support : Cell
  wits : List Wit
  agg : Agg
  leaf : Cell
  kind : FarKind

/-- An old certificate as a far certificate with the same comparison. -/
def FarCert.ofLeafCert (c : LeafCert) : FarCert :=
  ⟨c.s, c.support, c.wits, c.agg, c.leaf, .base c.kind⟩

def FarCert.leafOk (c : FarCert) : Bool :=
  match c.kind with
  | .base k => LeafCert.leafOk ⟨c.s, c.support, c.wits, c.agg, c.leaf, k⟩
  | .dFar reg cap => dLeafFarOk c.s c.support c.leaf c.agg reg cap
  | .jFar reg n => jLeafFarOk c.s c.support c.leaf c.agg reg n

def FarCert.check (c : FarCert) : Bool := supportOk c.s c.support c.wits c.agg && c.leafOk

theorem FarCert.check_ofLeafCert (c : LeafCert) : (FarCert.ofLeafCert c).check = c.check := rfl

theorem FarCert.route_ofLeafCert (c : LeafCert) :
    (FarCert.ofLeafCert c).kind.route = c.kind.route := rfl

/-- A certificate whose support facts are already known (for a support shared
by several leaves) proves its route result on its leaf box. -/
theorem FarCert.sound_of_facts (c : FarCert) (hs : SupportFacts c.s c.support c.agg)
    (h : c.leafOk = true) (p : Chart) (hp : c.leaf.Mem p) (gp : good p) : c.kind.route.result p := by
  unfold FarCert.leafOk at h
  cases hk : c.kind with
  | base k =>
    rw [hk] at h
    exact LeafCert.sound_of_facts ⟨c.s, c.support, c.wits, c.agg, c.leaf, k⟩ hs h p hp gp
  | dFar reg cap =>
    rw [hk] at h
    exact dleafFar_sound_good c.s c.support c.leaf c.agg reg cap hs h p hp gp
  | jFar reg n =>
    rw [hk] at h
    exact jleafFar_sound_good c.s c.support c.leaf c.agg reg n hs h p hp gp

theorem FarCert.sound (c : FarCert) (h : c.check = true) (p : Chart) (hp : c.leaf.Mem p)
    (gp : good p) : c.kind.route.result p := by
  obtain ⟨hs, hl⟩ := Bool.and_eq_true_iff.mp h
  exact c.sound_of_facts (support_facts hs) hl p hp gp

/-- A `SoundCheck` from a table of far certificates indexed by witness
references. -/
def certCheckFar (table : WitnessRef → Option FarCert) (w : WitnessRef) (b : Cell) : Bool :=
  match table w with
  | some c => decide (c.kind.route = w.route) && sameCell c.leaf b && c.check
  | none => false

theorem certCheckFar_sound (table : WitnessRef → Option FarCert) :
    SoundCheck (certCheckFar table) := by
  intro w b h p hp gp
  unfold certCheckFar at h
  cases hw : table w with
  | none => rw [hw] at h; exact absurd h (by simp)
  | some c =>
    rw [hw] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hc⟩, hk⟩ := h
    have e := sameCell_sound hc
    rw [← e] at hp
    rw [← hr]
    exact c.sound hk p hp gp

/-- The far table of an old table checks exactly as the old one. -/
theorem certCheckFar_ofLeafCert (table : WitnessRef → Option LeafCert) :
    certCheckFar (fun w => (table w).map FarCert.ofLeafCert) = certCheck table := by
  funext w b
  unfold certCheckFar certCheck
  dsimp only
  cases table w <;> rfl

/-- A `LatePackets.Checker` from a table of far certificates indexed by
requests. -/
def lateCheckFar (table : LatePackets.Request → Option FarCert) (q : LatePackets.Request) : Bool :=
  match table q with
  | some c => decide (c.kind.route = q.proposal.payload.route) && sameCell c.leaf q.target.box && c.check
  | none => false

theorem lateCheckFar_sound (table : LatePackets.Request → Option FarCert) :
    LatePackets.CheckerSound (lateCheckFar table) := by
  intro q _ _ _ h p hp gp
  unfold lateCheckFar at h
  cases hq : table q with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some c =>
    rw [hq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hc⟩, hk⟩ := h
    have e := sameCell_sound hc
    rw [← e] at hp
    rw [← hr]
    exact c.sound hk p hp gp

/-- The far table of an old table checks exactly as the old one. -/
theorem lateCheckFar_ofLeafCert (table : LatePackets.Request → Option LeafCert) :
    lateCheckFar (fun q => (table q).map FarCert.ofLeafCert) = lateCheck table := by
  funext q
  unfold lateCheckFar lateCheck
  dsimp only
  cases table q <;> rfl

end BccSharp.Coulomb.CompactCover.LeafFix
