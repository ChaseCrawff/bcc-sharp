import BccSharp.Cover.AdaptiveLayeredSign
import BccSharp.Cover.LayeredFarRoute

set_option autoImplicit false

/-! # The over-budget Adaptive `Q` boxes: the far transport with the sign-aware gain

`BccSharp.Cover.LayeredFarRoute` drops the registration-cost budget `1/2` of the PlanarAnchor
route: `farTransportOk` (literal registration of the all-half class, strain at most `1/40`,
`annFarOk`, the seam cell's separation) gives `D(p) ≤ D(anchor) + 200 |R (f − f₀ − n)|²` with
no cost condition, and `planarAnchorCertOkFar` pairs it with the unsigned layered gain. This module makes
two changes, and nothing else (the gain is the one the Adaptive `Q` cells need; the wider separation
guard is for uniformity with `planarAnchorSOk`: `sepOk` already holds on all 232 tested boxes):

* `farTransportSOk`, `farTransportSOk_sound`: `farTransportOk` and its soundness with the
  separation guard `sepOk b || sep2Ok box` (`CompactCover.Layered.sep2Ok_sound` for
  `r s ≥ 1`);
* `planarAnchorSFarOk`, `planarAnchorSFarOk_sound`: `planarAnchorCertOkFar` and its soundness with the sign-aware gain
  `splitOkS` (`splitOkS_gain`) and `farTransportSOk`.

The proofs are those of `BccSharp.Cover.LayeredFarRoute`, with these steps replaced. -/

open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-- `farTransportOk` with the separation guard `sepOk b || sep2Ok box`. -/
def farTransportSOk (reg : JLeaf.RegData) (box : Cell) (n : IntVec) : Bool :=
  let b := shiftCell box (seamShiftW n)
  (JLeaf.registrationCheck reg.B reg.N reg.U reg.f0 && decide (reg.f0 = halfQ)) &&
    ((guardsOk b && (sepOk b || sep2Ok box)) &&
      (decide (200 * (strainF b reg.N reg.U).hi ≤ 5 * Sz) &&
        JLeaf.Cutoff.annFarOk reg.N (fun i => reg.f0 i + (n i : ℚ)) box))

/-- **The relative defect bound on a box, with no cost condition.** If
`farTransportSOk reg box n`, then at every good point of the box
`D(p) ≤ D(a) + 200 |R (f − f₀ − n)|²` with the all-half anchor
`a = anchorOf (chartPoint p) (−1/2, −1/2, −1/2)`. -/
theorem farTransportSOk_sound (reg : JLeaf.RegData) (box : Cell) (n : IntVec)
    (ok : farTransportSOk reg box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) := by
  simp only [farTransportSOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hreg, hf0⟩, ⟨hg, hsep⟩, hstr, hfar⟩ := ok
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb] at hg hsep hstr
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  have g : Guards b := by
    have := of_decide_eq_true hg
    exact ⟨this.1, this.2.1, this.2.2⟩
  have sp := Sz_pos
  have e0 : p' 0 = p 0 := by rw [hp'def]; rfl
  have e1 : p' 1 = p 1 := by rw [hp'def]; rfl
  have hr : 0 < p 0 := by
    have := (div_pos (by exact_mod_cast g.r₀) sp).trans_le (cx_mem hp' 0).1
    rwa [e0] at this
  have hs : 0 < p 1 := by
    have := (div_pos (by exact_mod_cast g.r₁) sp).trans_le (cx_mem hp' 1).1
    rwa [e1] at this
  -- the strain of the registration at `p`
  have strainUp := (strainF_mem hp' g reg.N reg.U).2
  have hstrainEq : JLeaf.strainCost reg.N reg.U p' = JLeaf.strainCost reg.N reg.U p := by
    have h2 : p' 2 = p 2 := by rw [hp'def]; rfl
    have h3 : p' 3 = p 3 := by rw [hp'def]; rfl
    have h4 : p' 4 = p 4 := by rw [hp'def]; rfl
    unfold JLeaf.strainCost JLeaf.strainEntry
    rw [e0, e1, h2, h3, h4]
  have hstrainP : 100 * JLeaf.strainCost reg.N reg.U p ≤ 5 / 2 := by
    rw [← hstrainEq]
    have hR : 200 * ((strainF b reg.N reg.U).hi : ℝ) ≤ 5 * (Sz : ℝ) := by exact_mod_cast hstr
    have q2 : ((strainF b reg.N reg.U).hi : ℝ) / Sz ≤ 1 / 40 := by
      rw [div_le_iff₀ sp]
      linarith
    linarith
  -- the separations
  have hvalid : (chartPoint p).Valid := gp.1
  have hsep₁ := gp.2.2.1
  have asep : ∀ m : IntVec,
      (1 / 2 : ℝ) ^ 2 < sq ((chartPoint p).basis.mulVec (castVec m + halfAll)) := by
    rcases Bool.or_eq_true_iff.mp hsep with hsep | hsep
    · have hrs : p 0 * p 1 < 1 := by
        have hlt := of_decide_eq_true hsep
        have h1 := FI.mulPos_mem (cx_mem hp' 0) (cx_mem hp' 1)
        have h2 : ((FI.mulPos (cx b 0) (cx b 1)).hi : ℝ) / Sz < 1 := by
          rw [div_lt_one sp]; exact_mod_cast hlt
        rw [e0, e1] at h1
        linarith [h1.2]
      exact fun m => anchor_sep hr hs hrs halfAll rfl m
    · exact fun m => sep2Ok_sound hsep hp m
  have hf0r : (fun i => (reg.f0 i : ℝ)) = halfAll := by
    rw [hf0]
    exact halfQ_cast
  -- the far-annulus transport
  have trans0 := defect_transport_annulus reg.B reg.N reg.U reg.f0 n hreg p hstrainP
    hvalid hsep₁ (by rw [hf0r]; exact halfAll_half) (by rw [hf0r]; exact asep)
  have phi : JLeaf.Cutoff.annPhi reg.N (fun i => reg.f0 i + (n i : ℚ)) p ≤ 0 := by
    have h := JLeaf.Cutoff.annPhi_le_annCap reg.N (fun i => reg.f0 i + (n i : ℚ)) box
      (fun _ => 13 / 10) (JLeaf.Cutoff.annFarOk_annBoxOk hfar) p hp
    rw [JLeaf.Cutoff.annCap_far] at h
    simpa using h
  rw [hf0r] at trans0
  linarith

/-- `planarAnchorCertOkFar` with the sign-aware gain `splitOkS` and `farTransportSOk`. -/
def planarAnchorSFarOk (c : PlanarAnchorCert) (box : Cell) (n : IntVec) : Bool :=
  (decide (0 < c.k) && splitOkS (anchorW n) (lamOf c.k) c.depth (shiftCell box (seamShiftW n))) &&
    farTransportSOk c.reg box n

/-- The route result of one certificate accepted by `planarAnchorSFarOk`. -/
theorem planarAnchorSFarOk_sound (latticeCase : LatticeCase) (c : PlanarAnchorCert) (box : Cell) (n : IntVec)
    (ok : planarAnchorSFarOk c box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) := by
  simp only [planarAnchorSFarOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hk, hsplit⟩, hdef⟩ := ok
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨an, han⟩ : ∃ an, an = anchorW n := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb, ← han] at hsplit
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  -- the gain
  have gain := splitOkS_gain c.depth hsplit hp'
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
  rw [← hbq] at hG
  rw [hE, hEa, hG] at gain
  -- the scale and the gap
  obtain ⟨_, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gapB := Constants.reference_gap_checked
  have gap0 : 0 < gap := gapB.2
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := gapB.1.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  -- the defect transport
  have hvalid : (chartPoint p).Valid := gp.1
  have trans := farTransportSOk_sound c.reg box n hdef p hp gp
  rw [← hbq] at trans
  -- combine
  have hk0 : (0 : ℝ) < c.k := by exact_mod_cast hk
  have hlam : (2 * ac) * (200 * gap + (c.k : ℝ)) ≤ (lamOf c.k : ℝ) := by
    unfold lamOf
    push_cast
    have h1 : 0 ≤ 200 * gap + (c.k : ℝ) := by positivity
    have h2 : 200 * gap + (c.k : ℝ) ≤ 200 * (Constants.gapBracket.hi : ℝ) + c.k := by linarith
    have h3 : (2 * ac) * (200 * gap + (c.k : ℝ)) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + c.k) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    have h4 : (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + c.k) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + c.k) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (200 * gap + (c.k : ℝ)) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((200 * gap + (c.k : ℝ)) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  have deficitGain : deficit (anchorOf (chartPoint p) halfAll) + ((0 : ℚ) : ℝ) +
      ((c.k : ℚ) : ℝ) * bq ≤ deficit (chartPoint p) := by
    unfold deficit
    have h1 := mul_le_mul_of_nonneg_left trans gap0.le
    push_cast
    nlinarith
  have rel : relativeCheck 0 c.k = true := by
    unfold relativeCheck
    exact decide_eq_true ⟨le_rfl, hk⟩
  exact relativeOptical_route_of_lattice latticeCase p hvalid halfAll n halfAll_half 0 c.k rel (by
    rw [hbq] at deficitGain; exact deficitGain)

end BccSharp.Coulomb.CompactCover.Layered
