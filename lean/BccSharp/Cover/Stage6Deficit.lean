import BccSharp.Cover.Stage3Stage6Hybrid
import BccSharp.Cover.LeafFixFar
import BccSharp.TwoSite.DefectCutoffBox

set_option autoImplicit false

/-! # The Stage6 `D` entries: a deficit Jensen check against a registered defect cap

A Stage6 `D` entry is accepted when the Stage5b Jensen support on the entry's
support box, evaluated at the corners of its target box, exceeds
`e_BCC + g · D⁺`, where `D⁺` is a registered cap on the actual defect over the
target box.

* `Jensen.jensen_corners_lower`, `Jensen.Fix.tLeafCheck` and
  `tLeafCheck_sound`: the box-built Jensen check of `BccSharp.Cover.JensenFix`
  against any rational threshold `T`, giving `T < energy` at every valid point.
* `capOk reg b cap`: the registered cost of one registration, bounded at the
  256 corners in fixed point (`LeafFix.costAt`, `LeafFix.cost_ge`), plus one of
  three defect bounds: the far annulus (`annFarOk`, any cost), the cutoff `1/2`
  (`2·cap ≤ S`), or the cutoff `d♯` (`det N = 1`, `cutoffOk`). `capOk_sound`:
  `defect ≤ cap/S` at every valid point of the box.
* `stage6DEval dhint`: with a hint (registration and cap) per request, the cap
  check on the target box and the Jensen check with the request's profile
  against `e_BCC⁺ + g⁺ · cap/S`. `stage6DEval_sound : Stage6DSound (stage6DEval dhint)`
  for every hint function, so `stage6FullCheck hint dhint` (the hybrid `F` check
  and this `D` check) satisfies `Stage6CheckerSound`.

The hints are data; soundness does not depend on them. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Jensen
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover (cubeRootCheck)
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.DirectRoute (lexPositive cornerRat scaleInput scaleWitness)

/-- **The Jensen corner bound against any threshold.** As `jensen_fcc_corners`,
with `T` in place of the FCC energy. -/
theorem jensen_corners_lower (s : ℚ) (hs : 0 < s) (S b : Cell) (ts : List JTerm)
    (valid : ∀ t ∈ ts, t.Valid s S) (rhi : ∀ t ∈ ts, 0 ≤ t.rhi)
    (hst : structureOk (ts.map JTerm.lin) = true) (hM : 0 < mass ts)
    (inside : boxIn b S = true) (lo0 : 0 < b.lo 0) (lo1 : 0 < b.lo 1)
    (ord : ∀ i, b.lo i ≤ b.hi i) (E : (Axis → Bool) → ℚ)
    (hE : ∀ bits, (E bits : ℝ) ≤ Real.exp (((centerConst ts + aggValueQ (aggConst (ts.map JTerm.lin))
        (fun j => aggWeight (ts.map JTerm.lin) j) (cornerRat b bits) : ℚ) : ℝ) / mass ts))
    (hsc : cubeRootCheck scaleWitness scaleInput = true) (hlo : 0 < scaleWitness.lower)
    (T : ℚ) (final : ∀ bits, T < divScale (mass ts * E bits - (2 * s + 2 / s ^ 2)))
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    (T : ℝ) < energy (chartPoint p) := by
  obtain ⟨bits, hbits⟩ := lin_corner_exists S b ts s valid rhi lo0 lo1 ord p hp
  have sup := jensen_support s hs S ts valid hst hM p (boxIn_sound inside hp) hv
  have Mr : (0 : ℝ) < mass ts := by exact_mod_cast hM
  have e1 := (hE bits).trans (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hbits Mr.le))
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  have dv := divScale_le (mass ts * E bits - (2 * s + 2 / s ^ 2)) hsc hlo
  have low : (divScale (mass ts * E bits - (2 * s + 2 / s ^ 2)) : ℝ) ≤ energy (chartPoint p) := by
    refine dv.trans (le_trans ?_ sup)
    refine div_le_div_of_nonneg_right ?_ acpos.le
    push_cast
    have m1 := mul_le_mul_of_nonneg_left e1 Mr.le
    linarith
  have fr : (T : ℝ) < divScale (mass ts * E bits - (2 * s + 2 / s ^ 2)) := by
    exact_mod_cast final bits
  linarith

end BccSharp.Coulomb.CompactCover.Jensen

namespace BccSharp.Coulomb.CompactCover.Jensen.Fix
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.DirectRoute (lexPositive cornerRat scaleInput scaleWitness
  offset)
open BccSharp.Coulomb.BravaisCover (cubeRootCheck)

/-- The threshold comparison at one corner. -/
def tCornerOk (s : ℚ) (a : Agg) (c : Fin 8 → ℚ) (T : ℚ) : Bool :=
  decide (T < divScale (a.M * ((expLoZ (cornerValue a c / a.M) : ℚ) / Sz) - (2 * s + 2 / s ^ 2)))

/-- **The threshold leaf check**: the Jensen support built on `S` exceeds `T`
at every corner of the leaf `b ⊆ S`. -/
def tLeafCheckAgg (s : ℚ) (a : Agg) (S b : Cell) (T : ℚ) : Bool :=
  (decide (0 < s) && decide (0 < a.M) && leafGuards S b) &&
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
      bools.all fun b4 => bools.all fun b5 => bools.all fun b6 => bools.all fun b7 =>
        tCornerOk s a (cornerOf b b0 b1 b2 b3 b4 b5 b6 b7) T

def tLeafCheck (s L : ℚ) (N : ℕ) (S b : Cell) (T : ℚ) : Bool :=
  tLeafCheckAgg s (aggOf (buildSupport s L N S)) S b T

/-- **Soundness of the threshold check**: every valid point of the leaf has
energy strictly above `T`. -/
theorem tLeafCheck_sound (s L : ℚ) (N : ℕ) (S b : Cell) (T : ℚ) (ok : tLeafCheck s L N S b T = true)
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) : (T : ℝ) < energy (chartPoint p) := by
  unfold tLeafCheck tLeafCheckAgg at ok
  obtain ⟨guards, corners⟩ := Bool.and_eq_true_iff.mp ok
  unfold leafGuards at guards
  simp only [Bool.and_eq_true, decide_eq_true_eq] at guards
  obtain ⟨⟨hs, hM⟩, ⟨⟨⟨⟨⟨inside, lo0⟩, lo1⟩, ord⟩, hsc⟩, hlo⟩⟩ := guards
  set ts := buildSupport s L N S
  have hval := buildSupport_valid s L N S
  have hMts : 0 < mass ts := hM
  have cornerOk : ∀ bits : Axis → Bool, tCornerOk s (aggOf ts) (cornerRat b bits) T = true := by
    intro bits
    have h := bools_all (bools_all (bools_all (bools_all (bools_all (bools_all (bools_all
      (bools_all corners (bits 0)) (bits 1)) (bits 2)) (bits 3)) (bits 4)) (bits 5)) (bits 6)) (bits 7)
    unfold cornerOf at h
    rw [vec8_eta] at h
    exact h
  refine Jensen.jensen_corners_lower s hs S b ts (fun t ht => (hval t ht).2) (fun t ht => (hval t ht).1)
    (buildSupport_structure s L N S) hMts inside lo0 lo1 ord
    (fun bits => ((expLoZ (cornerValue (aggOf ts) (cornerRat b bits) / (aggOf ts).M) : ℚ) / Sz))
    ?_ hsc hlo T ?_ p hp hv
  · intro bits
    have e := expLoZ_le (cornerValue (aggOf ts) (cornerRat b bits) / (aggOf ts).M)
    have hm : (aggOf ts).M = mass ts := rfl
    have hc : (((cornerValue (aggOf ts) (cornerRat b bits) / (aggOf ts).M : ℚ)) : ℝ) =
        (((centerConst ts + aggValueQ (aggConst (ts.map JTerm.lin))
          (fun j => aggWeight (ts.map JTerm.lin) j) (cornerRat b bits) : ℚ)) : ℝ) / (mass ts : ℝ) := by
      rw [cornerValue_eq, hm]
      push_cast
      ring
    rw [hc] at e
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    exact e
  · intro bits
    have h := cornerOk bits
    unfold tCornerOk at h
    exact of_decide_eq_true h

end BccSharp.Coulomb.CompactCover.Jensen.Fix

namespace BccSharp.Coulomb.CompactCover.Stage3Stage6
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix (Sz Sz_pos)
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Cutoff

/-! ### A registered defect cap on a whole box -/

/-- The registered cost at the eight offset corners of one shape corner is at most `cap/S`. -/
def capOffsets (reg : RegData) (b : Cell) (sh : LeafFix.Shape) (strain cap : ℤ) : Bool :=
  LeafFix.bools.all fun b5 => LeafFix.bools.all fun b6 => LeafFix.bools.all fun b7 =>
    decide (LeafFix.costAt reg sh strain b b5 b6 b7 ≤ cap)

/-- The shape guard and the corner costs at one shape corner. -/
def capShape (reg : RegData) (b : Cell) (cap : ℤ) (sh : LeafFix.Shape) : Bool :=
  LeafFix.shapeGuard sh && capOffsets reg b sh (LeafFix.strainHi reg sh) cap

/-- The registered cost is at most `cap/S` at all 256 corners. -/
def capCorners (reg : RegData) (b : Cell) (cap : ℤ) : Bool :=
  LeafFix.bools.all fun b0 => LeafFix.bools.all fun b1 => LeafFix.bools.all fun b2 =>
    LeafFix.bools.all fun b3 => LeafFix.bools.all fun b4 =>
      capShape reg b cap (LeafFix.shapeOf b b0 b1 b2 b3 b4)

theorem capCorners_sound {reg : RegData} {b : Cell} {cap : ℤ} (h : capCorners reg b cap = true)
    (b0 : (0 : ℝ) < b.lo 0) (b1 : (0 : ℝ) < b.lo 1) (ord : ∀ i, (b.lo i : ℝ) ≤ b.hi i)
    (bits : Axis → Bool) : regCost reg.N reg.U reg.w (corner b bits) ≤ (cap : ℝ) / Sz := by
  have h5 := LeafFix.all_bool (LeafFix.all_bool (LeafFix.all_bool (LeafFix.all_bool
    (LeafFix.all_bool h (bits 0)) (bits 1)) (bits 2)) (bits 3)) (bits 4)
  unfold capShape at h5
  obtain ⟨hg, ho⟩ := Bool.and_eq_true_iff.mp h5
  unfold capOffsets at ho
  have h8 := LeafFix.all_bool (LeafFix.all_bool (LeafFix.all_bool ho (bits 5)) (bits 6)) (bits 7)
  have hcost := of_decide_eq_true h8
  have hm := LeafFix.shapeOf_mem b bits hg
  have c0 := (LeafFix.corner_pos b bits 0 b0 (ord 0)).ne'
  have c1 := (LeafFix.corner_pos b bits 1 b1 (ord 1)).ne'
  have hge := LeafFix.cost_ge reg b bits hm c0 c1
  have sp : (0 : ℝ) < Sz := Sz_pos
  have hc : (LeafFix.costAt reg (LeafFix.shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))
      (LeafFix.strainHi reg (LeafFix.shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b
      (bits 5) (bits 6) (bits 7) : ℝ) ≤ (cap : ℝ) := by exact_mod_cast hcost
  rw [le_div_iff₀ sp]
  linarith

/-- **Whole-box defect cap.** One registration with its corner costs, and one of
three defect bounds: the far annulus (any cost), the cutoff `1/2`, or the cutoff
`d♯` with `det N = 1`. -/
def capOk (reg : RegData) (b : Cell) (cap : ℤ) : Bool :=
  LeafFix.regGuards reg b && decide (0 < b.lo 0) && decide (0 < b.lo 1) &&
    decide (∀ i, b.lo i ≤ b.hi i) && capCorners reg b cap &&
    (annFarOk reg.N reg.w b || decide (2 * cap ≤ Sz) ||
      (decide (det3Q reg.N = 1) && cutoffOk ((cap : ℚ) / Sz)))

theorem capOk_sound {reg : RegData} {b : Cell} {cap : ℤ} (h : capOk reg b cap = true) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) : defect (chartPoint p) ≤ (cap : ℝ) / Sz := by
  unfold capOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hr, l0⟩, l1⟩, ord⟩, hcor⟩, hbound⟩ := h
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast l0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast l1
  have ordR : ∀ i, (b.lo i : ℝ) ≤ b.hi i := fun i => by exact_mod_cast ord i
  have hc := capCorners_sound hcor b0 b1 ordR
  rcases hbound with (hf | hhalf) | ⟨hN, hcut⟩
  · exact LeafFix.defect_le_cap_far reg b cap hr hf b0 b1 hc p hp
  · exact LeafFix.defect_le_cap reg b cap hr b0 b1 hhalf hc p hp hv
  · obtain ⟨hreg, unit, cond⟩ := LeafFix.regGuards_sound hr
    have hcq : ∀ bits, regCost reg.N reg.U reg.w (corner b bits) ≤ (((cap : ℚ) / Sz : ℚ) : ℝ) := by
      intro bits
      push_cast
      exact hc bits
    have hD := defect_le_box_cutoff reg b ((cap : ℚ) / Sz) hreg hN hcut b0 b1 unit cond hcq p hp hv
    have chord := regCost_chord reg.N reg.U reg.w b b0 b1 unit cond
    have hpC := LeafFix.le_of_corners chord hc p hp
    linarith

/-! ### The `D` evaluator -/

/-- A registration and a cap `cap/S` for one `D` entry's target box. -/
structure DHint where
  reg : RegData
  cap : ℤ

/-- The deficit threshold `e_BCC⁺ + g⁺ · cap/S`. -/
def dThreshold (cap : ℤ) : ℚ := Constants.bccBracket.hi + Constants.gapBracket.hi * ((cap : ℚ) / Sz)

/-- **`0 < deficit` from a cap and a threshold check on the same box.** -/
theorem deficit_pos_of_checks (reg : RegData) (cap : ℤ) (h0 : 0 ≤ cap) {s L : ℚ} {N : ℕ}
    {S b : Cell} (hcap : capOk reg b cap = true)
    (he : Jensen.Fix.tLeafCheck s L N S b (dThreshold cap) = true) (p : Chart) (hp : b.Mem p)
    (gp : good p) : 0 < deficit (chartPoint p) := by
  have hD := capOk_sound hcap p hp gp.1
  have hE := Jensen.Fix.tLeafCheck_sound _ _ _ _ _ _ he p hp gp.1
  have bccU : energy bcc ≤ (Constants.bccBracket.hi : ℝ) := (Constants.reference_bounds .bcc).2
  have gapU : gap ≤ (Constants.gapBracket.hi : ℝ) := Constants.reference_gap_checked.1.2
  have gap0 : 0 < gap := Constants.reference_gap_checked.2
  have sp : (0 : ℝ) < Sz := Sz_pos
  have c0 : (0 : ℝ) ≤ (cap : ℝ) / Sz := div_nonneg (by exact_mod_cast h0) sp.le
  have hT : ((dThreshold cap : ℚ) : ℝ) =
      (Constants.bccBracket.hi : ℝ) + (Constants.gapBracket.hi : ℝ) * ((cap : ℝ) / Sz) := by
    unfold dThreshold
    push_cast
    ring
  rw [hT] at hE
  have m1 : gap * defect (chartPoint p) ≤ gap * ((cap : ℝ) / Sz) :=
    mul_le_mul_of_nonneg_left hD gap0.le
  have m2 : gap * ((cap : ℝ) / Sz) ≤ (Constants.gapBracket.hi : ℝ) * ((cap : ℝ) / Sz) :=
    mul_le_mul_of_nonneg_right gapU c0
  unfold deficit
  linarith

/-- **The Stage6 `D` evaluator**: the cap on the target box and the Jensen
support on the support box, with the request's profile, above the threshold at
every corner of the target box. -/
def stage6DEval (dhint : Stage6Request → Option DHint) (q : Stage6Request) : Bool :=
  match dhint q with
  | some h =>
    decide (0 ≤ h.cap) && capOk h.reg q.proposal.target h.cap &&
      Jensen.Fix.tLeafCheck (stage6Profile q.proposal.profile).1 (stage6Profile q.proposal.profile).2.1
        (stage6Profile q.proposal.profile).2.2 q.proposal.source q.proposal.target (dThreshold h.cap)
  | none => false

/-- **`Stage6DSound`** for the `D` evaluator, for every hint function. -/
theorem stage6DEval_sound (dhint : Stage6Request → Option DHint) : Stage6DSound (stage6DEval dhint) := by
  intro q ok p hp gp
  unfold stage6DEval at ok
  split at ok
  · rename_i h _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨h0, hcap⟩, ht⟩ := ok
    exact deficit_pos_of_checks h.reg h.cap h0 hcap ht p hp gp
  · simp at ok

/-! ### The Stage6 checker with `F` and `D` evaluators -/

/-- The Stage6 checker: `F` entries by the hybrid check, `D` entries by `stage6DEval`. -/
def stage6FullCheck (hint : Stage6Request → Option SupportHint) (dhint : Stage6Request → Option DHint) :
    Stage6Checker :=
  stage6HybridCheck hint (stage6DEval dhint)

/-- **`Stage6CheckerSound`** for the full checker, for every pair of hint functions. -/
theorem stage6FullCheck_sound (hint : Stage6Request → Option SupportHint)
    (dhint : Stage6Request → Option DHint) : Stage6CheckerSound (stage6FullCheck hint dhint) :=
  stage6HybridCheck_sound hint (stage6DEval_sound dhint)

end BccSharp.Coulomb.CompactCover.Stage3Stage6
