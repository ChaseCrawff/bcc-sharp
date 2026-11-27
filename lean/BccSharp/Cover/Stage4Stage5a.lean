import BccSharp.Cover.AdaptiveOptical
import BccSharp.Cover.AdaptiveDeficit
import BccSharp.Cover.LayeredFarRoute
import BccSharp.Cover.OverlayCorpusPrefix

set_option autoImplicit false

/-! # The Stage4 and Stage5a sources (part of `later`)

Stage4 credits rectangles of the Stage3 complement by the Stage 7 equality and optical
bank and Stage5a by 609 registered `anchored` sources around two
sub-FCC controls. A clip row calls its check on the receipt and the *source* box
(`CertifiedClip.check`), so one check per source pays every clip cut from it.

**Payments on route `relativeOptical`** (`KPay`, from `LatticeCase`):

* `opay`: the Adaptive optical payments of `BccSharp.Cover.AdaptiveOptical` (`planarAnchor`, `planarAnchors`,
  `saturated`, `split`);
* `far signed cubic c n` (`farOk`): a layered gain on the seam cell, `splitOk` or (`signed`)
  the sign-aware `splitOkS` of `BccSharp.Cover.AdaptiveLayeredSign`, with the far-annulus defect
  transport of `BccSharp.Cover.LayeredFarRoute` (no cost budget); with `cubic` the anchor coset
  separation is proved for shapes near the cubic BCC reference (`r s` up to `3`,
  `sepCubicOk`, `anchor_sep_cubic`) instead of from `r s < 1` (`sepOk`), which fails at the
  reference `r = s = 1`. `far false false` is `Layered.planarAnchorCertOkFar` (`farOk_false_false`);
* `split`: the two closed halves.

The atlas tiles contain the exact BCC and FCC centres. They can be paid on route
`relativeOptical` too: at a centre the anchor is BCC or FCC, `h = 0`, and the equality
case of `OpticalEvidence` holds by `LatticeCase`; no local atlas is needed (one tile
per reference is a kernel item; all 28 pass the `#eval` forecast).

**Payments on route `strictDeficit`**: `AdaptiveSupport.DPay` (Jensen support against
`e_BCC + g·cap` with a registered cap, `BccSharp.Cover.AdaptiveDeficit`); no item uses it. By the
`#eval` forecast (untrusted) no relative payment pays one Stage5a source and twelve Stage4
Taylor sources, through split depth 3 (2 for the Stage5a source); they are meant for a
separate check, `stage5aCheck` of `BccSharp.Cover.Stage5aAnchored`: the layered gain with a negative
coefficient plus a positive anchor-deficit bound. Seven wide Stage4 sources need other work.

**Dispatch.** `stage4stage5aCheck hint` accepts only the four exact sources `stage4/optical`,
`stage4/atlas`, `stage4/taylor` and `stage5a/anchored` (`ownSource`; no string prefixes), with
an optical payment on route `relativeOptical` or a deficit payment on route
`strictDeficit`. Every other source is rejected (`stage4stage5aCheck_other`), in particular
`adaptiveRoute` and the Stage5b sources (`ownSource_others`), so the check composes with the other
`later` checks by `orCheck` (`later_compose_stage4stage5a`); the other checks reject the four
strings in turn (`AdaptiveSupport.adaptiveFull_off`, `Stage3Stage6.stage5bPhaseCheck_other`). -/

open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Stage4Stage5a
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-! ### Anchor coset separation near the cubic BCC shape -/

/-- The largest `|p 4|` on the box. -/
def zMax (b : Cell) : ℚ := max (-(b.lo 4)) (b.hi 4)

/-- The all-half anchor coset is separated by more than `1/2` on the box: positive
`r`, `s`, `r s < 3`, `|z| ≤ 1` and `1 < 1/(r s)⁺² + s⁻² (1 − |z|⁺)²`. -/
def sepCubicOk (b : Cell) : Bool :=
  decide (0 < b.lo 0) && decide (0 < b.lo 1) && decide (b.hi 0 * b.hi 1 < 3) &&
    decide (zMax b ≤ 1) && decide (1 < 1 / (b.hi 0 * b.hi 1) ^ 2 + b.lo 1 ^ 2 * (1 - zMax b) ^ 2)

/-- The real inequality behind `anchor_sep_cubic`: the third component alone when
`|t| ≥ 3/2`, the second and third when `|t| = 1/2`. -/
theorem sep_core (A s z t u k R Z slo : ℝ) (hA : 0 ≤ A) (hkR : 1 / R ≤ k) (hRpos : 0 < R)
    (hR3 : R < 3) (hs : slo ≤ s) (hslo : 0 < slo) (hz : -Z ≤ z) (hz' : z ≤ Z) (hZ1 : Z ≤ 1)
    (hmain : 1 < 1 / R ^ 2 + slo ^ 2 * (1 - Z) ^ 2)
    (hu : u ≤ -1 / 2 ∨ 1 / 2 ≤ u) (ht : t ≤ -3 / 2 ∨ t = -1 / 2 ∨ t = 1 / 2 ∨ 3 / 2 ≤ t) :
    (1 / 2 : ℝ) ^ 2 < A + (s * (u + z * t)) ^ 2 + (t * k) ^ 2 := by
  have hR1 : 1 / 3 < 1 / R := one_div_lt_one_div_of_lt hRpos hR3
  have hk3 : 1 / 3 < k := hR1.trans_le hkR
  have hk0 : 0 < k := by linarith
  have hB0 : 0 ≤ (s * (u + z * t)) ^ 2 := sq_nonneg _
  have hRk : 0 < 1 / R := by positivity
  have hRk2 : (1 / R) ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hRk.le hkR 2
  have e : (1 / R) ^ 2 = 1 / R ^ 2 := by rw [div_pow, one_pow]
  have mid : ∀ τ : ℝ, (τ = -1 / 2 ∨ τ = 1 / 2) →
      slo ^ 2 * (1 - Z) ^ 2 / 4 ≤ (s * (u + z * τ)) ^ 2 := by
    intro τ hτ
    have hzt : -(Z / 2) ≤ z * τ ∧ z * τ ≤ Z / 2 := by
      rcases hτ with rfl | rfl <;> constructor <;> linarith
    have hv : (1 - Z) / 2 ≤ |u + z * τ| := by
      rcases hu with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    have hv2 : ((1 - Z) / 2) ^ 2 ≤ (u + z * τ) ^ 2 := by
      rw [← sq_abs (u + z * τ)]
      exact pow_le_pow_left₀ (by linarith) hv 2
    have hs2 : slo ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hslo.le hs 2
    have hm := mul_le_mul hs2 hv2 (sq_nonneg _) (sq_nonneg _)
    calc slo ^ 2 * (1 - Z) ^ 2 / 4 = slo ^ 2 * ((1 - Z) / 2) ^ 2 := by ring
      _ ≤ s ^ 2 * (u + z * τ) ^ 2 := hm
      _ = (s * (u + z * τ)) ^ 2 := by ring
  rcases ht with h | h | h | h
  · have h1 : 1 / 2 < -(t * k) := by
      nlinarith [mul_nonneg hk0.le (show 0 ≤ -t - 3 / 2 by linarith)]
    have h2 : (1 / 2 : ℝ) ^ 2 < (-(t * k)) ^ 2 :=
      pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    rw [neg_sq] at h2
    linarith
  · have hm := mid t (Or.inl h)
    have hc : (t * k) ^ 2 = k ^ 2 / 4 := by rw [h]; ring
    rw [hc]
    linarith
  · have hm := mid t (Or.inr h)
    have hc : (t * k) ^ 2 = k ^ 2 / 4 := by rw [h]; ring
    rw [hc]
    linarith
  · have h1 : 1 / 2 < t * k := by
      nlinarith [mul_nonneg hk0.le (show 0 ≤ t - 3 / 2 by linarith)]
    have h2 : (1 / 2 : ℝ) ^ 2 < (t * k) ^ 2 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    linarith

theorem anchor_sep_cubic {b : Cell} (h : sepCubicOk b = true) {p : Chart} (hp : b.Mem p)
    (m : IntVec) : (1 / 2 : ℝ) ^ 2 < sq ((chartBasis p).mulVec (castVec m + halfAll)) := by
  simp only [sepCubicOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨l0, l1⟩, hrs3⟩, hz1⟩, hmain⟩ := h
  have bl0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast l0
  have bl1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast l1
  have r0 : (b.lo 0 : ℝ) ≤ p 0 := (hp 0).1
  have r1 : p 0 ≤ (b.hi 0 : ℝ) := (hp 0).2
  have s0 : (b.lo 1 : ℝ) ≤ p 1 := (hp 1).1
  have s1 : p 1 ≤ (b.hi 1 : ℝ) := (hp 1).2
  have z0 : (b.lo 4 : ℝ) ≤ p 4 := (hp 4).1
  have z1 : p 4 ≤ (b.hi 4 : ℝ) := (hp 4).2
  have hr : 0 < p 0 := bl0.trans_le r0
  have hs : 0 < p 1 := bl1.trans_le s0
  have hrs : 0 < p 0 * p 1 := mul_pos hr hs
  have hR : p 0 * p 1 ≤ (b.hi 0 : ℝ) * b.hi 1 :=
    mul_le_mul r1 s1 hs.le (bl0.trans_le (r0.trans r1)).le
  have hR3 : (b.hi 0 : ℝ) * b.hi 1 < 3 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hrs3
    push_cast at this
    exact this
  have hRpos : (0 : ℝ) < (b.hi 0 : ℝ) * b.hi 1 := hrs.trans_le hR
  have hZ1 : ((zMax b : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hz1
  have hzlo : -((zMax b : ℚ) : ℝ) ≤ p 4 := by
    have : -(b.lo 4 : ℝ) ≤ ((zMax b : ℚ) : ℝ) := by
      unfold zMax; push_cast; exact le_max_left _ _
    linarith
  have hzhi : p 4 ≤ ((zMax b : ℚ) : ℝ) := by
    have : (b.hi 4 : ℝ) ≤ ((zMax b : ℚ) : ℝ) := by
      unfold zMax; push_cast; exact le_max_right _ _
    linarith
  have hmainR : (1 : ℝ) < 1 / ((b.hi 0 : ℝ) * b.hi 1) ^ 2 +
      (b.lo 1 : ℝ) ^ 2 * (1 - ((zMax b : ℚ) : ℝ)) ^ 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hmain
    push_cast at this
    exact this
  have hkR : 1 / ((b.hi 0 : ℝ) * b.hi 1) ≤ (p 0 * p 1)⁻¹ := by
    rw [one_div]; exact inv_anti₀ hrs hR
  have hu : (m 1 : ℝ) - 1 / 2 ≤ -1 / 2 ∨ 1 / 2 ≤ (m 1 : ℝ) - 1 / 2 := by
    rcases (show m 1 ≤ 0 ∨ 1 ≤ m 1 by omega) with h1 | h1
    · left
      have : (m 1 : ℝ) ≤ 0 := by exact_mod_cast h1
      linarith
    · right
      have : (1 : ℝ) ≤ m 1 := by exact_mod_cast h1
      linarith
  have ht : (m 2 : ℝ) - 1 / 2 ≤ -3 / 2 ∨ (m 2 : ℝ) - 1 / 2 = -1 / 2 ∨
      (m 2 : ℝ) - 1 / 2 = 1 / 2 ∨ 3 / 2 ≤ (m 2 : ℝ) - 1 / 2 := by
    rcases (show m 2 ≤ -1 ∨ m 2 = 0 ∨ m 2 = 1 ∨ 2 ≤ m 2 by omega) with h2 | h2 | h2 | h2
    · left
      have : (m 2 : ℝ) ≤ -1 := by exact_mod_cast h2
      linarith
    · right; left
      have : (m 2 : ℝ) = 0 := by exact_mod_cast h2
      linarith
    · right; right; left
      have : (m 2 : ℝ) = 1 := by exact_mod_cast h2
      linarith
    · right; right; right
      have : (2 : ℝ) ≤ m 2 := by exact_mod_cast h2
      linarith
  have hd1 : (castVec m + halfAll) 1 = (m 1 : ℝ) - 1 / 2 := by
    simp [castVec, halfAll]; ring
  have hd2 : (castVec m + halfAll) 2 = (m 2 : ℝ) - 1 / 2 := by
    simp [castVec, halfAll]; ring
  rw [sq_chartBasis, hd1, hd2]
  exact sep_core _ (p 1) (p 4) ((m 2 : ℝ) - 1 / 2) ((m 1 : ℝ) - 1 / 2) (p 0 * p 1)⁻¹
    ((b.hi 0 : ℝ) * b.hi 1) ((zMax b : ℚ) : ℝ) (b.lo 1) (sq_nonneg _) hkR hRpos hR3 s0 bl1
    hzlo hzhi hZ1 hmainR hu ht

/-! ### The relative route from the layered gain and any defect transport -/

/-- The layered gain on the seam cell, as `Layered.Fix.splitOk_gain` and
`splitOkS_gain` state it. -/
def GainOn (lam : ℚ) (an : Anchor) (b : Cell) : Prop :=
  ∀ {p : Chart}, b.Mem p → (lam : ℝ) * layerGram p (an.k₁ / 2) (an.k₂ / 2) ≤
    2 * ac * (energy (chartPoint p) - energy (chartPoint (Layered.anchorChart p (an.k₁ / 2) (an.k₂ / 2))))

/-- The argument of `planarAnchorCertOkFar_sound` with the gain and the defect transport as
hypotheses: the layered gain with `λ = lamOf k`, `0 < k`, and
`D(p) ≤ D(anchor) + 200 |R d|²` give the route result. -/
theorem optical_of_gain (latticeCase : LatticeCase) (k : ℚ) (box : Cell) (n : IntVec)
    (hk : 0 < k) (hgain : GainOn (lamOf k) (anchorW n) (shiftCell box (seamShiftW n)))
    (p : Chart) (hp : box.Mem p) (gp : good p)
    (trans : defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n))) :
    OpticalEvidence (chartPoint p) := by
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
  -- the gain
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
  rw [← hbq] at hG
  rw [hE, hEa, hG] at gain
  -- the scale and the gap
  obtain ⟨_, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gapB := Constants.reference_gap_checked
  have gap0 : 0 < gap := gapB.2
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := gapB.1.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  have hvalid : (chartPoint p).Valid := gp.1
  rw [← hbq] at trans
  -- combine
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam : (2 * ac) * (200 * gap + (k : ℝ)) ≤ (lamOf k : ℝ) := by
    unfold lamOf
    push_cast
    have h1 : 0 ≤ 200 * gap + (k : ℝ) := by positivity
    have h2 : 200 * gap + (k : ℝ) ≤ 200 * (Constants.gapBracket.hi : ℝ) + k := by linarith
    have h3 : (2 * ac) * (200 * gap + (k : ℝ)) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + k) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    have h4 : (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + k) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (200 * gap + (k : ℝ)) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((200 * gap + (k : ℝ)) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  have deficitGain : deficit (anchorOf (chartPoint p) halfAll) + ((0 : ℚ) : ℝ) +
      ((k : ℚ) : ℝ) * bq ≤ deficit (chartPoint p) := by
    unfold deficit
    have h1 := mul_le_mul_of_nonneg_left trans gap0.le
    push_cast
    nlinarith
  have rel : relativeCheck 0 k = true := by
    unfold relativeCheck
    exact decide_eq_true ⟨le_rfl, hk⟩
  exact relativeOptical_route_of_lattice latticeCase p hvalid halfAll n halfAll_half 0 k rel (by
    rw [hbq] at deficitGain; exact deficitGain)

/-! ### The far-annulus transport near the cubic shape -/

/-- `Layered.farTransportOk` with `sepCubicOk` of the box in place of `sepOk`. -/
def farTransportOkC (reg : JLeaf.RegData) (box : Cell) (n : IntVec) : Bool :=
  let b := shiftCell box (seamShiftW n)
  (JLeaf.registrationCheck reg.B reg.N reg.U reg.f0 && decide (reg.f0 = halfQ)) &&
    ((guardsOk b && sepCubicOk box) &&
      (decide (200 * (strainF b reg.N reg.U).hi ≤ 5 * Sz) &&
        JLeaf.Cutoff.annFarOk reg.N (fun i => reg.f0 i + (n i : ℚ)) box))

/-- The argument of `Layered.farTransportOk_sound`, with the coset separation from
`anchor_sep_cubic`. -/
theorem farTransportOkC_sound (reg : JLeaf.RegData) (box : Cell) (n : IntVec)
    (ok : farTransportOkC reg box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) := by
  simp only [farTransportOkC, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hreg, hf0⟩, ⟨hg, hsep⟩, hstr, hfar⟩ := ok
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb] at hg hstr
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
      (1 / 2 : ℝ) ^ 2 < sq ((chartPoint p).basis.mulVec (castVec m + halfAll)) :=
    fun m => anchor_sep_cubic hsep hp m
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

/-! ### The far payment: either gain, either separation -/

/-- The layered gain on the seam cell: `splitOk` (`signed = false`) or the sign-aware
`splitOkS` of `BccSharp.Cover.AdaptiveLayeredSign` (`signed = true`), with `λ = lamOf k`. -/
def gainOk (signed : Bool) (c : PlanarAnchorCert) (box : Cell) (n : IntVec) : Bool :=
  if signed then splitOkS (anchorW n) (lamOf c.k) c.depth (shiftCell box (seamShiftW n))
  else splitOk (anchorW n) (lamOf c.k) c.depth (shiftCell box (seamShiftW n))

theorem gainOk_sound {signed : Bool} {c : PlanarAnchorCert} {box : Cell} {n : IntVec}
    (ok : gainOk signed c box n = true) :
    GainOn (lamOf c.k) (anchorW n) (shiftCell box (seamShiftW n)) := by
  intro p hp
  cases signed
  · exact splitOk_gain c.depth (by simpa [gainOk] using ok) hp
  · exact splitOkS_gain c.depth (by simpa [gainOk] using ok) hp

/-- The far-annulus transport with the anchor separation from `r s < 1` (`sepOk`,
`cubic = false`) or from `sepCubicOk` (`cubic = true`). -/
def transOk (cubic : Bool) (reg : JLeaf.RegData) (box : Cell) (n : IntVec) : Bool :=
  if cubic then farTransportOkC reg box n else farTransportOk reg box n

theorem transOk_sound {cubic : Bool} {reg : JLeaf.RegData} {box : Cell} {n : IntVec}
    (ok : transOk cubic reg box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) := by
  cases cubic
  · exact farTransportOk_sound reg box n (by simpa [transOk] using ok) p hp gp
  · exact farTransportOkC_sound reg box n (by simpa [transOk] using ok) p hp gp

/-- **The far payment.** With `signed = false` and `cubic = false` it is
`Layered.planarAnchorCertOkFar` (`farOk_false_false`). -/
def farOk (signed cubic : Bool) (c : PlanarAnchorCert) (box : Cell) (n : IntVec) : Bool :=
  (decide (0 < c.k) && gainOk signed c box n) && transOk cubic c.reg box n

theorem farOk_sound (latticeCase : LatticeCase) (signed cubic : Bool) (c : PlanarAnchorCert) (box : Cell)
    (n : IntVec) (ok : farOk signed cubic c box n = true) (p : Chart) (hp : box.Mem p)
    (gp : good p) : OpticalEvidence (chartPoint p) := by
  simp only [farOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hk, hgain⟩, htr⟩ := ok
  exact optical_of_gain latticeCase c.k box n hk (gainOk_sound hgain) p hp gp (transOk_sound htr p hp gp)

theorem farOk_false_false (c : PlanarAnchorCert) (box : Cell) (n : IntVec) :
    farOk false false c box n = planarAnchorCertOkFar c box n := by
  simp [farOk, gainOk, transOk, planarAnchorCertOkFar]

/-! ### Payments -/

/-- How a source box is paid on route `relativeOptical`. -/
inductive KPay where
  | opay (pay : AdaptiveOptical.OPay)
  | far (signed cubic : Bool) (c : PlanarAnchorCert) (n : IntVec)
  | split (ax : Axis) (r : ℚ) (left right : KPay)

def KPay.check : KPay → Cell → Bool
  | .opay pay, b => pay.check b
  | .far signed cubic c n, b => farOk signed cubic c b n
  | .split ax r left right, b => left.check (replaceEnd b ax r false) && right.check (replaceEnd b ax r true)

theorem KPay.sound (latticeCase : LatticeCase) (pay : KPay) (b : Cell) (ok : pay.check b = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) : OpticalEvidence (chartPoint p) := by
  induction pay generalizing b with
  | opay pay => exact AdaptiveOptical.OPay.sound latticeCase pay b ok p hp gp
  | far signed cubic c n => exact farOk_sound latticeCase signed cubic c b n ok p hp gp
  | split ax r left right ihl ihr =>
    obtain ⟨okl, okr⟩ := Bool.and_eq_true_iff.mp ok
    rcases two_closed_children b ax r p hp with h | h
    · exact ihl _ okl h
    · exact ihr _ okr h

/-- The payment of one witness. -/
inductive KHint where
  | optical (pay : KPay)
  | deficit (pay : AdaptiveSupport.DPay)

/-! ### Exact sources and the check -/

def stage4Optical : String := "stage4/optical"
def stage4Atlas : String := "stage4/atlas"
def stage4Taylor : String := "stage4/taylor"
def stage5aAnchored : String := "stage5a/anchored"

/-- The four exact sources of this check. -/
def ownSource (s : String) : Bool :=
  decide (s = stage4Optical) || decide (s = stage4Atlas) || decide (s = stage4Taylor) ||
    decide (s = stage5aAnchored)

/-- **The Stage4 and Stage5a check.** -/
def stage4stage5aCheck (hint : WitnessRef → Option KHint) (w : WitnessRef) (b : Cell) : Bool :=
  if ownSource w.source then
    match w.route, hint w with
    | .relativeOptical, some (.optical pay) => pay.check b
    | .strictDeficit, some (.deficit pay) => pay.check b
    | _, _ => false
  else false

/-- **Soundness**, for every hint map, from `LatticeCase`. -/
theorem stage4stage5aCheck_sound (latticeCase : LatticeCase) (hint : WitnessRef → Option KHint) :
    SoundCheck (stage4stage5aCheck hint) := by
  intro w b ok p hp gp
  unfold stage4stage5aCheck at ok
  split_ifs at ok with tag
  generalize hh : hint w = h at ok
  cases h with
  | none => cases hr : w.route <;> simp [hr] at ok
  | some h =>
    cases h with
    | optical pay =>
      cases hr : w.route <;> simp [hr] at ok
      exact pay.sound latticeCase b ok p hp gp
    | deficit pay =>
      cases hr : w.route <;> simp [hr] at ok
      exact AdaptiveSupport.DPay.sound pay b ok p hp gp

/-! ### Dispatch -/

/-- **Dispatch rule.** The check rejects every witness whose source is not one of the four
exact strings, whatever its route and cell. -/
theorem stage4stage5aCheck_other (hint : WitnessRef → Option KHint) {w : WitnessRef} (b : Cell)
    (h : ownSource w.source = false) : stage4stage5aCheck hint w b = false := by
  unfold stage4stage5aCheck
  simp [h]

theorem ownSource_eq_false (s : String) (h0 : s ≠ "stage4/optical") (h1 : s ≠ "stage4/atlas")
    (h2 : s ≠ "stage4/taylor") (h3 : s ≠ "stage5a/anchored") : ownSource s = false := by
  simp [ownSource, stage4Optical, stage4Atlas, stage4Taylor, stage5aAnchored, h0, h1, h2, h3]

/-- The four sources are accepted (kernel evaluation of the exact-string match). -/
theorem ownSource_accepted :
    ownSource "stage4/optical" = true ∧ ownSource "stage4/atlas" = true ∧
      ownSource "stage4/taylor" = true ∧ ownSource "stage5a/anchored" = true := by
  decide +kernel

/-- The Adaptive tag and the Stage5b sources of the Stage3–Stage5b check are
not accepted (kernel evaluation). -/
theorem ownSource_others :
    ownSource "adaptive-source" = false ∧ ownSource "stage5b/phase/0" = false ∧ ownSource "stage5b/phase/1" = false ∧
      ownSource "stage5b/phase/2" = false ∧ ownSource "stage5b/whole_above" = false := by
  decide +kernel

/-- None of the four sources is an Overlay bank, so `checkWithOverlay` passes their witnesses on
(with `OverlayCorpus.corpusCheck_of_not_overlay`, for every route). -/
theorem isOverlayBank_own :
    isOverlayBank "stage4/optical" = false ∧ isOverlayBank "stage4/atlas" = false ∧
      isOverlayBank "stage4/taylor" = false ∧ isOverlayBank "stage5a/anchored" = false := by
  decide +kernel

/-! ### Composition -/

open BccSharp.Coulomb.CompactCover.OverlayCorpus (orCheck orCheck_sound corpusCheck) in
/-- **The `later` composition**: with any sound check of the other `later` families. -/
theorem later_compose_stage4stage5a (latticeCase : LatticeCase) {other : WitnessRef → Cell → Bool}
    (h : SoundCheck other) (hint : WitnessRef → Option KHint) :
    SoundCheck (orCheck other (stage4stage5aCheck hint)) :=
  orCheck_sound h (stage4stage5aCheck_sound latticeCase hint)

open BccSharp.Coulomb.CompactCover.OverlayCorpus (orCheck corpusCheck) in
/-- A witness on a route other than `strictFCC` that `later` accepts is accepted by the
prefix check. `corpusCheck` is `checkWithOverlay (orCheck earlyCheck later)`, and only
`checkWithOverlay` can intercept `later`, for `strictFCC` witnesses of an Overlay bank
(`checkWithStage2` lies inside `earlyCheck`, the left side of `orCheck`). For the four sources
of this check `OverlayCorpus.corpusCheck_of_not_overlay` with `isOverlayBank_own` gives the same on
every route. -/
theorem corpusCheck_of_later {geometric direct sidecar bulk} {later : WitnessRef → Cell → Bool}
    {w : WitnessRef} {b : Cell} (hr : w.route ≠ .strictFCC) (h : later w b = true) :
    corpusCheck geometric direct sidecar bulk later w b = true := by
  unfold corpusCheck checkWithOverlay
  simp [hr, orCheck, h]

end BccSharp.Coulomb.CompactCover.Stage4Stage5a
