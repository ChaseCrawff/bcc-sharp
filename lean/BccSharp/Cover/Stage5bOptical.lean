import BccSharp.Cover.Stage6Deficit
import BccSharp.Cover.LayeredRoute
import BccSharp.Cover.LayeredFarRoute

set_option autoImplicit false

/-! # The Stage5b optical tiles: the whole-tile and anchor deficit routes, and the relative route

The Stage5b optical sweep accepts a tile of
a projected BCC neighbourhood (in the standard frame, anchor class `(−1/2, −1/2, −1/2)`,
wrap `0`) by one of these routes. Here each is a check on the tile with a hint.

* **Whole tile** (`whole_defect`, route `strictDeficit`): `wholeOk`, the Stage6 `D` check with
  the support built on the tile itself, profile `(6/5, 5, 2)`: a registered cap on the tile
  (`capOk`) and the Jensen check against `e_BCC⁺ + g⁺ · cap/S`.
* **Anchor** (`screened_anchor`, and `taylor_anchor` where it suffices; route
  `strictDeficit`): `anchorOk`. With the anchor `a = (shape of p, −1/2, −1/2, −1/2)` and
  `h = R (f − f₀)`:
  * the Jensen check on the anchor cell (the tile's shape box, offsets `−1/2`), support
    built on that cell, against `e_BCC⁺ + g⁺ · cap/S + m`: `e(a) > e_BCC⁺ + g⁺ cap/S + m`;
  * a registration with `w = f₀`: its corner costs on the anchor cell give
    `100 ‖R N − U‖² ≤ cap/S` (the shift term vanishes there), and the far annulus on the
    tile gives `D(p) ≤ 100 ‖R N − U‖² + 200 |h|²` (`defect_le_box_far`);
  * The layered gain on the seam cell (`Layered.Fix.splitOk_gain`) with
    `λ = lamS k`: `e(p) − e(a) ≥ (200 g + k) |h|²`. Here `k = anchorK m G = −m/G⁺`, the most
    negative coefficient the margin absorbs, where `G⁺ ≥ |h|²` on the tile (`gramF`); `lamS`
    takes the lower or upper scale bound by the sign of `200 g⁺ + k`;
  * the closing inequality `0 ≤ m` and `0 ≤ m + min(0, k) · G⁺`.

  Then `deficit(p) > m + k |h|² ≥ 0`. This is the `screened_anchor` inequality with
  the signed optical change bounded by the layered gain.
  `anchorTreeOk` runs the anchor check on the pieces of a bisection of the tile's shape box
  (`Stage5bPhase.opticalAxis`, exact midpoints), with a hint per piece.
* **Relative** (`optical_lattice`, route `relativeOptical`): `Layered.planarAnchorCertOk` (cost at most
  `1/2`) or `Layered.planarAnchorCertOkFar` (the far-annulus transport, any cost) with wrap `0`,
  unchanged (they need `LatticeCase`).

`stage5bOpticalCheck hint` reads the four sources `stage5b/whole_defect`, `stage5b/screened_anchor`,
`stage5b/taylor_anchor` and `stage5b/optical_lattice` with a hint per witness, and
`stage5bOpticalCheck_sound latticeCase hint : SoundCheck (stage5bOpticalCheck hint)`. The hints are data;
soundness does not depend on them. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Stage5bOptical
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Cutoff
open BccSharp.Coulomb.CompactCover.Stage3Stage6

/-! ### The whole tile -/

/-- The whole-tile deficit check: the registered cap on the tile and the Jensen check with
the support built on the tile, profile `(6/5, 5, 2)`, against `e_BCC⁺ + g⁺ · cap/S`. -/
def wholeOk (h : DHint) (b : Cell) : Bool :=
  (decide (0 ≤ h.cap) && capOk h.reg b h.cap) &&
    Jensen.Fix.tLeafCheck (6 / 5) 5 2 b b (dThreshold h.cap)

theorem wholeOk_sound (h : DHint) (b : Cell) (ok : wholeOk h b = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) : 0 < deficit (chartPoint p) := by
  simp only [wholeOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨h0, hc⟩, he⟩ := ok
  exact deficit_pos_of_checks h.reg h.cap h0 hc he p hp gp

/-! ### The anchor -/

/-- The anchor chart: the point's shape with every offset at `−1/2`. -/
def anchorPt (p : Chart) : Chart := ![p 0, p 1, p 2, p 3, p 4, -1 / 2, -1 / 2, -1 / 2]

/-- The anchor cell: the tile's shape box with every offset at `−1/2`. -/
def anchorCell (b : Cell) : Cell :=
  ⟨![b.lo 0, b.lo 1, b.lo 2, b.lo 3, b.lo 4, -1 / 2, -1 / 2, -1 / 2],
    ![b.hi 0, b.hi 1, b.hi 2, b.hi 3, b.hi 4, -1 / 2, -1 / 2, -1 / 2]⟩

theorem anchorPt_mem {b : Cell} {p : Chart} (hp : b.Mem p) : (anchorCell b).Mem (anchorPt p) := by
  intro i
  fin_cases i
  · exact hp 0
  · exact hp 1
  · exact hp 2
  · exact hp 3
  · exact hp 4
  all_goals simp [anchorCell, anchorPt]

theorem chartBasis_anchorPt (p : Chart) : chartBasis (anchorPt p) = chartBasis p := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem chartPoint_anchorPt (p : Chart) : chartPoint (anchorPt p) = anchorOf (chartPoint p) halfAll := by
  have hB := chartBasis_anchorPt p
  unfold chartPoint anchorOf
  rw [hB]
  congr 1
  funext i
  fin_cases i <;> simp [anchorPt, halfAll]

/-- The anchor offsets as a rational registration offset. -/
def halfW : Fin 3 → ℚ := ![-1 / 2, -1 / 2, -1 / 2]

theorem halfW_cast : (fun i => ((halfW i : ℚ) : ℝ)) = halfAll := by
  funext i
  fin_cases i <;> simp [halfW, halfAll]

/-- `regCost` at a point is its value at the anchor plus `200 |R (f − f₀)|²`. -/
theorem regCost_anchor_split (N U : Fin 3 → Fin 3 → ℚ) (p : Chart) :
    regCost N U halfW p = regCost N U halfW (anchorPt p) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec 0)) := by
  rw [regCost_eq, regCost_eq, halfW_cast, chartBasis_anchorPt]
  have hoff : (chartPoint (anchorPt p)).offset - halfAll = 0 := by
    funext i
    fin_cases i <;> simp [chartPoint, anchorPt, halfAll]
  have hc : castVec (0 : IntVec) = 0 := by
    funext i
    simp [castVec]
  have hz : sq (0 : Vec) = 0 := by simp [sq]
  rw [hoff, hc, sub_zero, Matrix.mulVec_zero, hz]
  show _ = _ + 200 * sq ((chartBasis p).mulVec ((chartPoint p).offset - halfAll))
  ring

/-- `λ` of the gain check for a coefficient `k` of either sign: the upper scale bound when
`200 g⁺ + k ≥ 0`, the lower one otherwise, so that `2 a_c (200 g + k) ≤ λ`. -/
def lamS (k : ℚ) : ℚ :=
  if 0 ≤ 200 * Constants.gapBracket.hi + k then
    2 * DirectRoute.scaleWitness.upper * (200 * Constants.gapBracket.hi + k)
  else 2 * DirectRoute.scaleWitness.lower * (200 * Constants.gapBracket.hi + k)

theorem lamS_ge (k : ℚ) : (2 * ac) * (200 * gap + (k : ℝ)) ≤ (lamS k : ℝ) := by
  obtain ⟨acLo, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gapB := Constants.reference_gap_checked
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := gapB.1.2
  have step : (2 * ac) * (200 * gap + (k : ℝ)) ≤ (2 * ac) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold lamS
  split_ifs with hx
  · have hx' : (0 : ℝ) ≤ 200 * (Constants.gapBracket.hi : ℝ) + k := by exact_mod_cast hx
    push_cast
    have h2 : (2 * ac) * (200 * (Constants.gapBracket.hi : ℝ) + k) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
      mul_le_mul_of_nonneg_right (by linarith) hx'
    linarith
  · have hx' : 200 * (Constants.gapBracket.hi : ℝ) + k < 0 := by
      have h1 : 200 * Constants.gapBracket.hi + k < 0 := lt_of_not_ge hx
      exact_mod_cast h1
    push_cast
    have h2 : (2 * ac) * (200 * (Constants.gapBracket.hi : ℝ) + k) ≤
        (2 * (DirectRoute.scaleWitness.lower : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
      mul_le_mul_of_nonpos_right (by linarith) hx'.le
    linarith

/-- The anchor hint: a registration with `w = f₀ = (−1/2, −1/2, −1/2)` (rotation `U`,
`N = B⁻¹`), the strain cap `cap/S` on the anchor cell, the anchor margin `m` and the split
depth of the gain check. -/
structure AnchorHint where
  reg : RegData
  cap : ℤ
  margin : ℚ
  depth : ℕ

/-- The gain coefficient of the anchor route: the most negative `k` that the margin `m`
absorbs on the tile, `k = −m · S / G` with `G/S ≥ |h|²` (`gramF`), and `0` when `G ≤ 0`. -/
def anchorK (m : ℚ) (G : ℤ) : ℚ := if 0 < G then -(m * Sz / G) else 0

/-- The anchor route on a tile (standard frame, wrap `0`). -/
def anchorOk (h : AnchorHint) (box : Cell) : Bool :=
  let b := shiftCell box (seamShiftW 0)
  let an := anchorW 0
  let A := anchorCell box
  let k := anchorK h.margin (gramF b an).hi
  (((splitOk an (lamS k) h.depth b && guardsOk b) &&
      ((registrationCheck h.reg.B h.reg.N h.reg.U h.reg.f0 && decide (h.reg.w = halfW)) &&
        annFarOk h.reg.N h.reg.w box)) &&
    ((((LeafFix.regGuards h.reg A && decide (0 < A.lo 0)) && decide (0 < A.lo 1)) &&
        decide (∀ i, A.lo i ≤ A.hi i)) && capCorners h.reg A h.cap)) &&
  ((Jensen.Fix.tLeafCheck (6 / 5) 5 2 A A (dThreshold h.cap + h.margin) &&
      (decide (0 ≤ h.cap) && decide (0 ≤ h.margin))) &&
    decide (0 ≤ h.margin + min 0 k * (((gramF b an).hi : ℚ) / Sz)))

theorem anchorOk_sound (h : AnchorHint) (box : Cell) (ok : anchorOk h box = true) (p : Chart)
    (hp : box.Mem p) (gp : good p) : 0 < deficit (chartPoint p) := by
  simp only [anchorOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨hsplit, hg⟩, ⟨hreg, hw⟩, hfar⟩, ⟨⟨⟨hrg, a0⟩, a1⟩, aord⟩, hcor⟩,
    ⟨he, hc0, hm0⟩, hclose⟩ := ok
  -- the seam frame (wrap `0`)
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW 0) := ⟨_, rfl⟩
  obtain ⟨an, han⟩ : ∃ an, an = anchorW 0 := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW 0) := ⟨_, rfl⟩
  rw [← hb] at hsplit hg hclose
  rw [← han] at hsplit hclose
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have e : shiftChart p' (-seamShiftW 0) = p := by
      rw [hp'def]
      funext i
      fin_cases i <;> simp [shiftChart, seamShiftW]
    rw [e]
    exact hp
  have g : Guards b := by
    have := of_decide_eq_true hg
    exact ⟨this.1, this.2.1, this.2.2⟩
  have sp := Sz_pos
  -- the gain over the anchor
  have gain := splitOk_gain h.depth hsplit hp'
  have hE : energy (chartPoint p') = energy (chartPoint p) := by
    rw [hp'def, chartPoint_shift, energy_wrap]
  have hA := anchor_chart_wrap p 0
  rw [← hp'def, ← han] at hA
  have hEa : energy (chartPoint (anchorChart p' (an.k₁ / 2) (an.k₂ / 2))) =
      energy (anchorOf (chartPoint p) halfAll) := by rw [hA, energy_wrap]
  have hG := gram_eq p 0
  rw [← hp'def, ← han] at hG
  obtain ⟨bq, hbq⟩ : ∃ x, x = sq ((chartPoint p).basis.mulVec
      ((chartPoint p).offset - halfAll - castVec 0)) := ⟨_, rfl⟩
  rw [← hbq] at hG
  rw [hE, hEa, hG] at gain
  have gramUp := (gramF_mem hp' g an).2
  rw [hG] at gramUp
  set k := anchorK h.margin (gramF b an).hi with hk
  -- constants
  have ac0 : 0 < ac := ac_positive
  have h2ac : 0 < 2 * ac := by positivity
  have gapB := Constants.reference_gap_checked
  have gap0 : 0 < gap := gapB.2
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := gapB.1.2
  have bccU : energy bcc ≤ (Constants.bccBracket.hi : ℝ) := (Constants.reference_bounds .bcc).2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  have gainE : (200 * gap + (k : ℝ)) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right (lamS_ge k) bq0
    have e : (2 * ac) * ((200 * gap + (k : ℝ)) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  -- the anchor energy
  have hv : (chartPoint p).Valid := gp.1
  have paMem : (anchorCell box).Mem (anchorPt p) := anchorPt_mem hp
  have paEq := chartPoint_anchorPt p
  have paValid : (chartPoint (anchorPt p)).Valid := by
    rw [paEq]
    exact anchor_valid _ hv halfAll halfAll_half
  have hEnergy := Jensen.Fix.tLeafCheck_sound _ _ _ _ _ _ he (anchorPt p) paMem paValid
  rw [paEq] at hEnergy
  -- the strain cap at the anchor
  have A0 : (0 : ℝ) < (anchorCell box).lo 0 := by exact_mod_cast a0
  have A1 : (0 : ℝ) < (anchorCell box).lo 1 := by exact_mod_cast a1
  have Aord : ∀ i, ((anchorCell box).lo i : ℝ) ≤ (anchorCell box).hi i := fun i => by
    exact_mod_cast aord i
  obtain ⟨_, unit, cond⟩ := LeafFix.regGuards_sound hrg
  have hc := capCorners_sound hcor A0 A1 Aord
  have chord := regCost_chord h.reg.N h.reg.U h.reg.w (anchorCell box) A0 A1 unit cond
  have hpa := LeafFix.le_of_corners chord hc (anchorPt p) paMem
  -- the defect on the tile
  have hD := defect_le_box_far h.reg box hreg hfar p hp
  rw [hw] at hD hpa
  have hsplitC := regCost_anchor_split h.reg.N h.reg.U p
  rw [← hbq] at hsplitC
  have hD' : defect (chartPoint p) ≤ (h.cap : ℝ) / Sz + 200 * bq := by linarith
  -- close
  have hcap0 : (0 : ℝ) ≤ (h.cap : ℝ) / Sz := by
    have : (0 : ℝ) ≤ h.cap := by exact_mod_cast hc0
    positivity
  have hT : ((dThreshold h.cap + h.margin : ℚ) : ℝ) =
      (Constants.bccBracket.hi : ℝ) + (Constants.gapBracket.hi : ℝ) * ((h.cap : ℝ) / Sz) + h.margin := by
    unfold dThreshold
    push_cast
    ring
  rw [hT] at hEnergy
  have hm0' : (0 : ℝ) ≤ h.margin := by exact_mod_cast hm0
  have hcl : (0 : ℝ) ≤ (h.margin : ℝ) + min 0 (k : ℝ) * (((gramF b an).hi : ℝ) / Sz) := by
    have := (Rat.cast_le (K := ℝ)).mpr hclose
    push_cast at this
    exact this
  have gD : gap * defect (chartPoint p) ≤ gap * ((h.cap : ℝ) / Sz + 200 * bq) :=
    mul_le_mul_of_nonneg_left hD' gap0.le
  have gC : gap * ((h.cap : ℝ) / Sz) ≤ (Constants.gapBracket.hi : ℝ) * ((h.cap : ℝ) / Sz) :=
    mul_le_mul_of_nonneg_right gapHi hcap0
  have kb : min 0 (k : ℝ) * bq ≤ (k : ℝ) * bq :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) bq0
  have kG : min 0 (k : ℝ) * (((gramF b an).hi : ℝ) / Sz) ≤ min 0 (k : ℝ) * bq :=
    mul_le_mul_of_nonpos_left gramUp (min_le_left _ _)
  unfold deficit
  nlinarith

/-! ### Split tiles -/

/-- Anchor hints on a bisection of the tile's shape box (`Stage5bPhase.opticalAxis`, the
optical sweep's own axis rule, at exact midpoints). -/
inductive AnchorTree where
  | leaf (h : AnchorHint)
  | split (lower upper : AnchorTree)

def anchorTreeOk : AnchorTree → Cell → Bool
  | .leaf h, b => anchorOk h b
  | .split l u, b =>
    anchorTreeOk l (replaceEnd b (Stage5bPhase.opticalAxis b) (midpoint b (Stage5bPhase.opticalAxis b)) false) &&
      anchorTreeOk u (replaceEnd b (Stage5bPhase.opticalAxis b) (midpoint b (Stage5bPhase.opticalAxis b)) true)

/-- A split tree's check from its children's checks on literal boxes (so that each piece
can be checked in its own declaration). -/
theorem anchorTreeOk_split (l u : AnchorTree) (b lo hi : Cell)
    (hl : sameCell (replaceEnd b (Stage5bPhase.opticalAxis b) (midpoint b (Stage5bPhase.opticalAxis b)) false) lo = true)
    (hu : sameCell (replaceEnd b (Stage5bPhase.opticalAxis b) (midpoint b (Stage5bPhase.opticalAxis b)) true) hi = true)
    (okl : anchorTreeOk l lo = true) (oku : anchorTreeOk u hi = true) :
    anchorTreeOk (.split l u) b = true := by
  simp only [anchorTreeOk, sameCell_sound hl, sameCell_sound hu, okl, oku, Bool.and_self]

theorem anchorTreeOk_sound : ∀ (t : AnchorTree) (b : Cell), anchorTreeOk t b = true →
    ∀ p, b.Mem p → good p → 0 < deficit (chartPoint p)
  | .leaf h, b, ok, p, hp, gp => anchorOk_sound h b ok p hp gp
  | .split l u, b, ok, p, hp, gp => by
    simp only [anchorTreeOk, Bool.and_eq_true] at ok
    rcases two_closed_children b (Stage5bPhase.opticalAxis b) (midpoint b (Stage5bPhase.opticalAxis b)) p hp
      with h | h
    · exact anchorTreeOk_sound l _ ok.1 p h gp
    · exact anchorTreeOk_sound u _ ok.2 p h gp

/-! ### The witness check -/

/-- A hint for one Stage5b optical witness. -/
inductive OpticalHint where
  | whole (h : DHint)
  | anchor (t : AnchorTree)
  | relative (c : PlanarAnchorCert)

/-- One hint on a tile, for the witness's route. -/
def opticalOk (h : OpticalHint) (route : Route) (b : Cell) : Bool :=
  match h with
  | .whole d => decide (route = .strictDeficit) && wholeOk d b
  | .anchor t => decide (route = .strictDeficit) && anchorTreeOk t b
  | .relative c => decide (route = .relativeOptical) && (planarAnchorCertOk c b 0 || planarAnchorCertOkFar c b 0)

/-- The Stage5b optical sources (exact strings). -/
def opticalSource (s : String) : Bool :=
  (s == "stage5b/whole_defect" || s == "stage5b/screened_anchor") ||
    (s == "stage5b/taylor_anchor" || s == "stage5b/optical_lattice")

/-- **The Stage5b optical witness check**: one of the four sources, and its hint on the
witness's own cell. -/
def stage5bOpticalCheck (hint : WitnessRef → Option OpticalHint) (w : WitnessRef) (b : Cell) : Bool :=
  opticalSource w.source &&
    match hint w with
    | some h => opticalOk h w.route b
    | none => false

theorem opticalOk_sound (latticeCase : LatticeCase) (h : OpticalHint) (route : Route) (b : Cell)
    (ok : opticalOk h route b = true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    route.result p := by
  cases h with
  | whole d =>
    simp only [opticalOk, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨hr, hw⟩ := ok
    rw [hr]
    exact wholeOk_sound d b hw p hp gp
  | anchor t =>
    simp only [opticalOk, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨hr, ha⟩ := ok
    rw [hr]
    exact anchorTreeOk_sound t b ha p hp gp
  | relative c =>
    simp only [opticalOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ok
    obtain ⟨hr, hc⟩ := ok
    rw [hr]
    rcases hc with hc | hc
    · exact planarAnchorCertOk_sound latticeCase c b 0 hc p hp gp
    · exact planarAnchorCertOkFar_sound latticeCase c b 0 hc p hp gp

theorem stage5bOpticalCheck_sound (latticeCase : LatticeCase) (hint : WitnessRef → Option OpticalHint) :
    SoundCheck (stage5bOpticalCheck hint) := by
  intro w b ok p hp gp
  unfold stage5bOpticalCheck at ok
  obtain ⟨_, hc⟩ := Bool.and_eq_true_iff.mp ok
  cases hh : hint w with
  | none => rw [hh] at hc; simp at hc
  | some h =>
    rw [hh] at hc
    exact opticalOk_sound latticeCase h w.route b hc p hp gp

/-- Every other source is rejected. -/
theorem stage5bOpticalCheck_other (hint : WitnessRef → Option OpticalHint) (w : WitnessRef) (b : Cell)
    (h : opticalSource w.source = false) : stage5bOpticalCheck hint w b = false := by
  simp [stage5bOpticalCheck, h]

end BccSharp.Coulomb.CompactCover.Stage5bOptical
