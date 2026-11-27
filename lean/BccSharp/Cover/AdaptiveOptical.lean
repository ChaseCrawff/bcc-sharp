import BccSharp.Cover.AdaptiveFarQ
import BccSharp.Cover.AdaptiveGap
import BccSharp.TwoSite.DefectCutoffBox
import BccSharp.TwoSite.DefectInvariance

set_option autoImplicit false

/-! # The Adaptive half-shift optical comparisons (letters `Q`, `X`, route `relativeOptical`)

A box is marked `Q` or `X` in the Adaptive cover when the deficit
grows at least quadratically away from a half-shift anchor `f₀ + n` whose deficit the lattice case bounds.
Every Adaptive reference has third offset `−1/2`, so every such anchor is a half-height anchor and
the layered gain (`Layered.Fix.splitOk_gain`) applies. This module pays such a
box on route `relativeOptical` from `LatticeCase`:

* `OPay.planarAnchor c n`: `Layered.planarAnchorCertOk` unchanged (anchor class `(−1/2, −1/2, −1/2)`, defect
  transport with a literal registration, `Layered.planarAnchorCertOk_sound`);
* `OPay.saturated h₀ h₁ depth k labels n`: the anchor class `halfOf h₀ h₁`
  (lateral halves by the bits, third `−1/2`) with a **saturated anchor**: eighteen distinct
  lifts of the anchor lie within `51/40` on the whole box (`innerOk`), so the anchor's defect is
  `1` (`defect_eq_one_of_inner`), the defect cannot grow, and the layered gain alone
  (`splitOk` with `λ = 2 a_c⁺ k`) gives `deficit(anchor) + k |R d|² ≤ deficit`
  (`satOk_sound`);
* `OPay.planarAnchors c n`: `Layered.planarAnchorSOk`, the PlanarAnchor certificate with the sign-aware layered gain
  of `BccSharp.Cover.AdaptiveLayeredSign` (`Layered.planarAnchorSOk_sound`), for the near-cubic `Q` cells;
* `OPay.planarAnchorsFar c n`: `Layered.planarAnchorSFarOk`, the far transport with the
  sign-aware gain (`BccSharp.Cover.AdaptiveFarQ`, `Layered.planarAnchorSFarOk_sound`), for the `Q` boxes whose
  registered cost exceeds `1/2`;
* `OPay.split`: the two closed halves of the box;
* `OPay.gapSat depth k g n`: the anchor class `(−1/2, −1/2, −1/2)` with a **radial gap**: no
  lift of the anchor has a length within `g` of `1` on the whole box (`AdaptiveGap.gapOk`), so its
  defect is `1` (`AdaptiveGap.defect_anchor_gap`), and the layered gain gives the rest as for a
  saturated anchor (`gapSatOk_sound`), for the `Q` boxes of the FCC reference.

`saturated_route` is the common step of the last and of `OPay.saturated`: the layered gain and
an anchor of defect `1`.

`anchor_chart_wrapG` and `gram_eqG` are `Layered.anchor_chart_wrap` and `Layered.gram_eq` for
the anchor classes `halfOf h₀ h₁` (`halfOf_true_true : halfOf true true = Layered.halfAll`). -/

open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.AdaptiveOptical
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-! ### Saturated defect -/

section Saturation
open Classical

theorem annularWeight_ge {v : Vec} (h : sq v ≤ (51 / 40 : ℝ) ^ 2) : (1 / 4 : ℝ) ≤ annularWeight v := by
  unfold annularWeight
  have hs : Real.sqrt (sq v) ≤ 51 / 40 := by
    calc Real.sqrt (sq v) ≤ Real.sqrt ((51 / 40 : ℝ) ^ 2) := Real.sqrt_le_sqrt h
      _ = 51 / 40 := Real.sqrt_sq (by norm_num)
  have h1 : (1 / 4 : ℝ) ≤ min 1 (13 - 10 * Real.sqrt (sq v)) := le_min (by norm_num) (by linarith)
  exact h1.trans (le_max_right _ _)

/-- Every trial leaves at least four of eighteen distinct lifts within `51/40` unmatched. -/
theorem trial_ge_one (q : TwoSite) (hq : q.Valid) (v : Fin 18 → Vec) (inj : Function.Injective v)
    (mem : ∀ i, v i ∈ neighbors q) (small : ∀ i, sq (v i) ≤ (51 / 40 : ℝ) ^ 2)
    (U : Mat) (σ : Fin 14 ↪ ↥(neighbors q)) : 1 ≤ defectTrial U σ := by
  have hfin := GlobalInputs.twoSite_neighbors_finite q hq
  have : Fintype ↥(neighbors q) := hfin.fintype
  let w : Fin 18 → ↥(neighbors q) := fun i => ⟨v i, mem i⟩
  have winj : Function.Injective w := fun i j h => inj (congrArg Subtype.val h)
  let s : Finset (Fin 18) := Finset.univ.filter (fun i => w i ∉ Set.range σ)
  let t : Finset (Fin 18) := Finset.univ.filter (fun i => ¬ (w i ∉ Set.range σ))
  have hst : s.card + t.card = 18 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 18)))
      (fun i => w i ∉ Set.range σ)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  have ht : t.card ≤ 14 := by
    let g : Fin 18 → Fin 14 := fun i =>
      if h : w i ∈ Set.range σ then Classical.choose h else 0
    have hg : ∀ i ∈ t, σ (g i) = w i := by
      intro i hi
      have hi' : w i ∈ Set.range σ := by
        have := (Finset.mem_filter.mp hi).2
        exact not_not.mp this
      simp only [g]
      rw [dite_eq_left hi']
      exact Classical.choose_spec hi'
    have inj' : Set.InjOn g ↑t := by
      intro i hi j hj e
      apply winj
      rw [← hg i hi, ← hg j hj, e]
    have maps : Set.MapsTo g ↑t ↑(Finset.univ : Finset (Fin 14)) := by
      intro i _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    have h := Finset.card_le_card_of_injOn g maps inj'
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hs4 : (4 : ℝ) ≤ s.card := by
    have : 4 ≤ s.card := by omega
    exact_mod_cast this
  have hsum : (s.card : ℝ) * (1 / 4) ≤
      ∑ y : ↥(neighbors q), (if y ∈ Set.range σ then 0 else annularWeight y.val) := by
    have f0 : ∀ y : ↥(neighbors q), 0 ≤ (if y ∈ Set.range σ then 0 else annularWeight y.val) := by
      intro y
      split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    calc (s.card : ℝ) * (1 / 4) = ∑ i ∈ s, (1 / 4 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, (if w i ∈ Set.range σ then 0 else annularWeight (w i).val) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          rw [ite_eq_right hi']
          exact annularWeight_ge (small i)
      _ = ∑ y ∈ s.map ⟨w, winj⟩, (if y ∈ Set.range σ then 0 else annularWeight y.val) := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ y : ↥(neighbors q), (if y ∈ Set.range σ then 0 else annularWeight y.val) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => f0 y)
  unfold defectTrial
  rw [tsum_fintype]
  have h25 : 0 ≤ 25 * ∑ j, sq ((σ j : Vec) - U.mulVec (star j)) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => sq_nonnegative _))
  have h1 : (1 : ℝ) ≤ (s.card : ℝ) * (1 / 4) := by linarith
  exact h1.trans (hsum.trans (le_add_of_nonneg_left h25))

/-- **Saturation.** Eighteen distinct lifts within `51/40` give `defect = 1`. -/
theorem defect_eq_one_of_inner (q : TwoSite) (hq : q.Valid) (v : Fin 18 → Vec)
    (inj : Function.Injective v) (mem : ∀ i, v i ∈ neighbors q)
    (small : ∀ i, sq (v i) ≤ (51 / 40 : ℝ) ^ 2) : defect q = 1 := by
  obtain ⟨hle, -, hatt⟩ := DefectInvariance.defect_eq_min q hq
  rcases hatt with h | ⟨U, -, σ, hσ⟩
  · exact h
  · refine le_antisymm hle ?_
    rw [← hσ]
    exact trial_ge_one q hq v inj mem small U σ

end Saturation

/-! ### Upper bounds of squared lengths on a box -/

/-- A bound of `|t|` on `[lo, hi]`. -/
def greatestAbs (lo hi : ℚ) : ℚ := max (-lo) hi

theorem sq_le_greatestAbs (lo hi : ℚ) (t : ℝ) (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    t ^ 2 ≤ ((greatestAbs lo hi : ℚ) : ℝ) ^ 2 := by
  unfold greatestAbs
  push_cast
  have m : |t| ≤ max (-(lo : ℝ)) (hi : ℝ) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]; exact h2.trans (le_max_right _ _)
    · rw [abs_of_nonpos h]; exact (neg_le_neg h1).trans (le_max_left _ _)
  calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    _ ≤ (max (-(lo : ℝ)) (hi : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) m 2

/-- Whole-box upper bound of `primalQ v false` (for `0 < b.lo 0`, `0 < b.lo 1`). -/
def primalHi (v : Fin 3 → ℚ) (b : Cell) : ℚ :=
  b.hi 0 ^ 2 * greatestAbs (JLeaf.Cutoff.rowALo v false b) (JLeaf.Cutoff.rowAHi v false b) ^ 2 +
    b.hi 1 ^ 2 * greatestAbs (JLeaf.Cutoff.rowBLo v false b) (JLeaf.Cutoff.rowBHi v false b) ^ 2 +
    greatestAbs (JLeaf.Cutoff.imgLo v false b 2) (JLeaf.Cutoff.imgHi v false b 2) ^ 2 /
      (b.lo 0 ^ 2 * b.lo 1 ^ 2)

theorem primalQ_le_primalHi (v : Fin 3 → ℚ) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) (p : Chart) (hp : b.Mem p) :
    JLeaf.primalQ v false p ≤ ((primalHi v b : ℚ) : ℝ) := by
  have i0 := JLeaf.Cutoff.imgInterval_mem v false b p hp 0
  have i1 := JLeaf.Cutoff.imgInterval_mem v false b p hp 1
  have i2 := JLeaf.Cutoff.imgInterval_mem v false b p hp 2
  have m2 := JLeaf.Cutoff.mulLo_le (b.lo 2) (b.hi 2) (JLeaf.Cutoff.imgLo v false b 1)
    (JLeaf.Cutoff.imgHi v false b 1) (p 2) (JLeaf.img v false p 1) (hp 2).1 (hp 2).2 i1.1 i1.2
  have m3 := JLeaf.Cutoff.mulLo_le (b.lo 3) (b.hi 3) (JLeaf.Cutoff.imgLo v false b 2)
    (JLeaf.Cutoff.imgHi v false b 2) (p 3) (JLeaf.img v false p 2) (hp 3).1 (hp 3).2 i2.1 i2.2
  have m4 := JLeaf.Cutoff.mulLo_le (b.lo 4) (b.hi 4) (JLeaf.Cutoff.imgLo v false b 2)
    (JLeaf.Cutoff.imgHi v false b 2) (p 4) (JLeaf.img v false p 2) (hp 4).1 (hp 4).2 i2.1 i2.2
  have rA : ((JLeaf.Cutoff.rowALo v false b : ℚ) : ℝ) ≤ JLeaf.rowA v false p ∧
      JLeaf.rowA v false p ≤ ((JLeaf.Cutoff.rowAHi v false b : ℚ) : ℝ) := by
    unfold JLeaf.Cutoff.rowALo JLeaf.Cutoff.rowAHi JLeaf.rowA
    push_cast
    constructor <;> linarith [i0.1, i0.2, m2.1, m2.2, m3.1, m3.2]
  have rB : ((JLeaf.Cutoff.rowBLo v false b : ℚ) : ℝ) ≤ JLeaf.rowB v false p ∧
      JLeaf.rowB v false p ≤ ((JLeaf.Cutoff.rowBHi v false b : ℚ) : ℝ) := by
    unfold JLeaf.Cutoff.rowBLo JLeaf.Cutoff.rowBHi JLeaf.rowB
    push_cast
    constructor <;> linarith [i1.1, i1.2, m4.1, m4.2]
  have sA := sq_le_greatestAbs _ _ _ rA.1 rA.2
  have sB := sq_le_greatestAbs _ _ _ rB.1 rB.2
  have sC := sq_le_greatestAbs _ _ (JLeaf.rowC v false p) i2.1 i2.2
  have p0 : (b.lo 0 : ℝ) ≤ p 0 := (hp 0).1
  have p1 : (b.lo 1 : ℝ) ≤ p 1 := (hp 1).1
  have q0 : p 0 ≤ (b.hi 0 : ℝ) := (hp 0).2
  have q1 : p 1 ≤ (b.hi 1 : ℝ) := (hp 1).2
  have pp0 : 0 < p 0 := h0.trans_le p0
  have pp1 : 0 < p 1 := h1.trans_le p1
  have e0 : p 0 ^ 2 ≤ (b.hi 0 : ℝ) ^ 2 := pow_le_pow_left₀ pp0.le q0 2
  have e1 : p 1 ^ 2 ≤ (b.hi 1 : ℝ) ^ 2 := pow_le_pow_left₀ pp1.le q1 2
  have tA : p 0 ^ 2 * JLeaf.rowA v false p ^ 2 ≤ (b.hi 0 : ℝ) ^ 2 *
      ((greatestAbs (JLeaf.Cutoff.rowALo v false b) (JLeaf.Cutoff.rowAHi v false b) : ℚ) : ℝ) ^ 2 :=
    mul_le_mul e0 sA (sq_nonneg _) (sq_nonneg _)
  have tB : p 1 ^ 2 * JLeaf.rowB v false p ^ 2 ≤ (b.hi 1 : ℝ) ^ 2 *
      ((greatestAbs (JLeaf.Cutoff.rowBLo v false b) (JLeaf.Cutoff.rowBHi v false b) : ℚ) : ℝ) ^ 2 :=
    mul_le_mul e1 sB (sq_nonneg _) (sq_nonneg _)
  have den : (b.lo 0 : ℝ) ^ 2 * (b.lo 1 : ℝ) ^ 2 ≤ p 0 ^ 2 * p 1 ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ h0.le p0 2) (pow_le_pow_left₀ h1.le p1 2) (by positivity)
      (by positivity)
  have dpos : 0 < (b.lo 0 : ℝ) ^ 2 * (b.lo 1 : ℝ) ^ 2 := by positivity
  have tC : JLeaf.rowC v false p ^ 2 / (p 0 ^ 2 * p 1 ^ 2) ≤
      ((greatestAbs (JLeaf.Cutoff.imgLo v false b 2) (JLeaf.Cutoff.imgHi v false b 2) : ℚ) : ℝ) ^ 2 /
        ((b.lo 0 : ℝ) ^ 2 * (b.lo 1 : ℝ) ^ 2) :=
    div_le_div₀ (sq_nonneg _) sC dpos den
  unfold primalHi JLeaf.primalQ
  push_cast
  linarith

/-! ### The anchor classes `(h₀, h₁, 1)` -/

/-- The half class with lateral halves by the bits and third coordinate `−1/2`. -/
noncomputable def halfOf (h₀ h₁ : Bool) : Vec := ![if h₀ then -1 / 2 else 0, if h₁ then -1 / 2 else 0, -1 / 2]

def halfQ (h₀ h₁ : Bool) : Fin 3 → ℚ := ![if h₀ then -1 / 2 else 0, if h₁ then -1 / 2 else 0, -1 / 2]

def bitZ (h : Bool) : ℤ := if h then 1 else 0

/-- The layered anchor of the class `halfOf h₀ h₁` and wrap `n`, in the seam chart. -/
def anchorG (h₀ h₁ : Bool) (n : IntVec) : Anchor := ⟨2 * n 0 - bitZ h₀, 2 * n 1 - bitZ h₁, 3⟩

theorem halfQ_cast (h₀ h₁ : Bool) (i : Fin 3) : ((halfQ h₀ h₁ i : ℚ) : ℝ) = halfOf h₀ h₁ i := by
  fin_cases i <;> cases h₀ <;> cases h₁ <;> norm_num [halfQ, halfOf]

/-- The all-half class of `PlanarAnchor`. -/
theorem halfOf_true_true : halfOf true true = halfAll := by
  funext i
  fin_cases i <;> norm_num [halfOf, halfAll]

theorem halfOf_half (h₀ h₁ : Bool) : HalfClass (halfOf h₀ h₁) := by
  refine ⟨⟨![-(bitZ h₀), -(bitZ h₁), -1], ?_⟩, ?_⟩
  · funext i
    fin_cases i <;> cases h₀ <;> cases h₁ <;> norm_num [halfOf, bitZ, castVec]
  · intro n h
    have h2 := congrFun h 2
    simp only [halfOf, castVec] at h2
    norm_num at h2
    have e : (2 * n 2 : ℝ) = -1 := by linarith
    have : (2 * n 2 : ℤ) = -1 := by exact_mod_cast e
    omega

theorem anchor_chart_wrapG (p : Chart) (n : IntVec) (h₀ h₁ : Bool) :
    chartPoint (anchorChart (shiftChart p (seamShiftW n)) ((anchorG h₀ h₁ n).k₁ / 2)
        ((anchorG h₀ h₁ n).k₂ / 2)) =
      wrap (anchorOf (chartPoint p) (halfOf h₀ h₁)) ![n 0, n 1, 1] := by
  have hB : chartBasis (anchorChart (shiftChart p (seamShiftW n)) ((anchorG h₀ h₁ n).k₁ / 2)
      ((anchorG h₀ h₁ n).k₂ / 2)) = chartBasis p := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  unfold chartPoint
  rw [hB]
  simp only [wrap, anchorOf]
  congr 1
  funext i
  fin_cases i <;> cases h₀ <;> cases h₁ <;> simp [anchorChart, anchorG, halfOf, bitZ, castVec] <;> ring

theorem gram_eqG (p : Chart) (n : IntVec) (h₀ h₁ : Bool) :
    layerGram (shiftChart p (seamShiftW n)) ((anchorG h₀ h₁ n).k₁ / 2) ((anchorG h₀ h₁ n).k₂ / 2) =
      sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfOf h₀ h₁ - castVec n)) := by
  rw [show (chartPoint p).basis = chartBasis p from rfl, sq_chartBasis]
  unfold layerGram quad6
  rw [latV_zero, latV_one]
  have s0 : shiftChart p (seamShiftW n) 0 = p 0 := rfl
  have s1 : shiftChart p (seamShiftW n) 1 = p 1 := rfl
  have s2 : shiftChart p (seamShiftW n) 2 = p 2 := rfl
  have s3 : shiftChart p (seamShiftW n) 3 = p 3 := rfl
  have s4 : shiftChart p (seamShiftW n) 4 = p 4 := rfl
  have s5 : shiftChart p (seamShiftW n) 5 = p 5 := by simp [shiftChart, seamShiftW]
  have s6 : shiftChart p (seamShiftW n) 6 = p 6 := by simp [shiftChart, seamShiftW]
  have s7 : shiftChart p (seamShiftW n) 7 = p 7 + 1 - (n 2 : ℝ) := by
    simp [shiftChart, seamShiftW]; ring
  have hc : cReal (shiftChart p (seamShiftW n)) = (p 0 * p 1)⁻¹ := rfl
  have k1 : ((anchorG h₀ h₁ n).k₁ : ℝ) = 2 * (n 0 : ℝ) - ((bitZ h₀ : ℤ) : ℝ) := by
    simp [anchorG]
  have k2 : ((anchorG h₀ h₁ n).k₂ : ℝ) = 2 * (n 1 : ℝ) - ((bitZ h₁ : ℤ) : ℝ) := by
    simp [anchorG]
  have d0 : ((chartPoint p).offset - halfOf h₀ h₁ - castVec n) 0 =
      p 5 - halfOf h₀ h₁ 0 - (n 0 : ℝ) := by
    show (chartPoint p).offset 0 - halfOf h₀ h₁ 0 - castVec n 0 = _
    simp [chartPoint, castVec]
  have d1 : ((chartPoint p).offset - halfOf h₀ h₁ - castVec n) 1 =
      p 6 - halfOf h₀ h₁ 1 - (n 1 : ℝ) := by
    show (chartPoint p).offset 1 - halfOf h₀ h₁ 1 - castVec n 1 = _
    simp [chartPoint, castVec]
  have d2 : ((chartPoint p).offset - halfOf h₀ h₁ - castVec n) 2 = p 7 + 1 / 2 - (n 2 : ℝ) := by
    show (chartPoint p).offset 2 - halfOf h₀ h₁ 2 - castVec n 2 = _
    simp [chartPoint, halfOf, castVec]; ring
  rw [s0, s1, s2, s3, s4, s5, s6, s7, hc, k1, k2, d0, d1, d2]
  cases h₀ <;> cases h₁ <;> norm_num [halfOf, bitZ] <;> ring

/-! ### Saturated anchors on a box -/

/-- The coordinates `m + [odd] f₀` of a label `(m, odd)`. -/
def labelVec (h₀ h₁ : Bool) (l : IntVec × Bool) : Fin 3 → ℚ :=
  fun i => (l.1 i : ℚ) + if l.2 then halfQ h₀ h₁ i else 0

/-- Eighteen distinct nonzero labels whose lifts are at most `51/40` long on the box. -/
def innerOk (h₀ h₁ : Bool) (labels : Fin 18 → IntVec × Bool) (b : Cell) : Bool :=
  decide (0 < b.lo 0) && decide (0 < b.lo 1) &&
    decide (Function.Injective fun i => labelVec h₀ h₁ (labels i)) &&
    decide (∀ i, labelVec h₀ h₁ (labels i) ≠ 0 ∧
      primalHi (labelVec h₀ h₁ (labels i)) b ≤ (51 / 40) ^ 2)

theorem chartBasis_injective (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    Function.Injective (chartBasis p).mulVec := by
  apply Matrix.mulVec_injective_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp [chartBasis, Matrix.det_fin_three, h0, h1]

theorem anchor_saturated (h₀ h₁ : Bool) (labels : Fin 18 → IntVec × Bool) (b : Cell)
    (hin : innerOk h₀ h₁ labels b = true) (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    defect (anchorOf (chartPoint p) (halfOf h₀ h₁)) = 1 := by
  simp only [innerOk, Bool.and_eq_true, decide_eq_true_eq] at hin
  obtain ⟨⟨⟨l0, l1⟩, hinj⟩, hall⟩ := hin
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast l0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast l1
  have pp0 : 0 < p 0 := b0.trans_le (hp 0).1
  have pp1 : 0 < p 1 := b1.trans_le (hp 1).1
  set f₀ := halfOf h₀ h₁
  set a := anchorOf (chartPoint p) f₀
  have ha : a.Valid := anchor_valid (chartPoint p) hv f₀ (halfOf_half h₀ h₁)
  let ℓ : Fin 18 → Vec := fun i j => ((labelVec h₀ h₁ (labels i) j : ℚ) : ℝ)
  let v : Fin 18 → Vec := fun i => (chartBasis p).mulVec (ℓ i)
  have Binj := chartBasis_injective p pp0.ne' pp1.ne'
  have ℓinj : Function.Injective ℓ := by
    intro i j e
    apply hinj
    funext k
    have := congrFun e k
    simp only [ℓ] at this
    show labelVec h₀ h₁ (labels i) k = labelVec h₀ h₁ (labels j) k
    exact_mod_cast this
  have vinj : Function.Injective v := fun i j e => ℓinj (Binj e)
  have hsq : ∀ i, sq (v i) ≤ (51 / 40 : ℝ) ^ 2 := by
    intro i
    have e := JLeaf.primalQ_eq (labelVec h₀ h₁ (labels i)) false p pp0.ne' pp1.ne'
    have himg : (fun k => JLeaf.img (labelVec h₀ h₁ (labels i)) false p k) = ℓ i := by
      funext k
      simp [JLeaf.img, ℓ]
    rw [himg] at e
    have hb := primalQ_le_primalHi (labelVec h₀ h₁ (labels i)) b b0 b1 p hp
    have hh : ((primalHi (labelVec h₀ h₁ (labels i)) b : ℚ) : ℝ) ≤ (51 / 40 : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr (hall i).2
      push_cast at this
      exact this
    show sq ((chartBasis p).mulVec (ℓ i)) ≤ _
    rw [← e]
    exact hb.trans hh
  have hmem : ∀ i, v i ∈ neighbors a := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · rw [zero_add]
      have hℓ : ℓ i = castVec (labels i).1 + (if (labels i).2 then f₀ else 0) := by
        funext k
        simp only [ℓ, labelVec, castVec, Pi.add_apply]
        split_ifs
        · push_cast
          rw [halfQ_cast]
        · simp
      show (chartBasis p).mulVec (ℓ i) ∈ a.points
      rw [hℓ, Matrix.mulVec_add]
      split_ifs
      · exact Or.inr ⟨(chartBasis p).mulVec (castVec (labels i).1), ⟨(labels i).1, rfl⟩, rfl⟩
      · rw [Matrix.mulVec_zero, add_zero]
        exact Or.inl ⟨(labels i).1, rfl⟩
    · intro h0
      apply (hall i).1
      have : ℓ i = 0 := Binj (h0.trans (Matrix.mulVec_zero _).symm)
      funext k
      have := congrFun this k
      simp only [ℓ, Pi.zero_apply] at this
      exact_mod_cast this
    · exact (hsq i).trans_lt (by norm_num)
  exact defect_eq_one_of_inner a ha v vinj hmem hsq

/-! ### The saturated payment -/

/-- The layered gain about the anchor of class `halfOf h₀ h₁` with `λ = 2 a_c⁺ k`, and a
saturated anchor. -/
def satOk (h₀ h₁ : Bool) (depth : ℕ) (k : ℚ) (labels : Fin 18 → IntVec × Bool) (box : Cell)
    (n : IntVec) : Bool :=
  (decide (0 < k) &&
      splitOk (anchorG h₀ h₁ n) (2 * DirectRoute.scaleWitness.upper * k) depth
        (shiftCell box (seamShiftW n))) &&
    innerOk h₀ h₁ labels box

/-- **The saturated route.** The layered gain about the anchor of class `halfOf h₀ h₁` with
`λ = 2 a_c⁺ k`, and an anchor of defect `1`, give the relative optical evidence. -/
theorem saturated_route (latticeCase : LatticeCase) (h₀ h₁ : Bool) (depth : ℕ) (k : ℚ) (box : Cell)
    (n : IntVec) (hk : 0 < k)
    (hsplit : splitOk (anchorG h₀ h₁ n) (2 * DirectRoute.scaleWitness.upper * k) depth
      (shiftCell box (seamShiftW n)) = true)
    (p : Chart) (hp : box.Mem p) (gp : good p)
    (hsat : defect (anchorOf (chartPoint p) (halfOf h₀ h₁)) = 1) :
    OpticalEvidence (chartPoint p) := by
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  have hp' : (shiftCell box (seamShiftW n)).Mem p' := by
    rw [shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  have gain := splitOk_gain depth hsplit hp'
  have hE : energy (chartPoint p') = energy (chartPoint p) := by
    rw [hp'def, chartPoint_shift, energy_wrap]
  have hEa : energy (chartPoint (anchorChart p' ((anchorG h₀ h₁ n).k₁ / 2) ((anchorG h₀ h₁ n).k₂ / 2))) =
      energy (anchorOf (chartPoint p) (halfOf h₀ h₁)) := by
    rw [hp'def, anchor_chart_wrapG, energy_wrap]
  have hG := gram_eqG p n h₀ h₁
  rw [← hp'def] at hG
  obtain ⟨bq, hbq⟩ : ∃ x, x = sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfOf h₀ h₁ -
      castVec n)) := ⟨_, rfl⟩
  rw [← hbq] at hG
  rw [hE, hEa, hG] at gain
  obtain ⟨_, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gap0 : 0 < gap := Constants.reference_gap_checked.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam : 2 * ac * (k : ℝ) ≤ ((2 * DirectRoute.scaleWitness.upper * k : ℚ) : ℝ) := by
    push_cast
    nlinarith
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (k : ℝ) * bq ≤ energy (chartPoint p) - energy (anchorOf (chartPoint p) (halfOf h₀ h₁)) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((k : ℝ) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) (halfOf h₀ h₁))) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  have hDq := (defect_range (chartPoint p)).2
  have deficitGain : deficit (anchorOf (chartPoint p) (halfOf h₀ h₁)) + ((0 : ℚ) : ℝ) +
      ((k : ℚ) : ℝ) * bq ≤ deficit (chartPoint p) := by
    unfold deficit
    rw [hsat]
    have := mul_le_mul_of_nonneg_left hDq gap0.le
    push_cast
    linarith
  have rel : relativeCheck 0 k = true := by
    unfold relativeCheck
    exact decide_eq_true ⟨le_rfl, hk⟩
  exact relativeOptical_route_of_lattice latticeCase p gp.1 (halfOf h₀ h₁) n (halfOf_half h₀ h₁) 0 k rel (by
    rw [hbq] at deficitGain; exact deficitGain)

theorem satOk_sound (latticeCase : LatticeCase) (h₀ h₁ : Bool) (depth : ℕ) (k : ℚ)
    (labels : Fin 18 → IntVec × Bool) (box : Cell) (n : IntVec)
    (ok : satOk h₀ h₁ depth k labels box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) := by
  simp only [satOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hk, hsplit⟩, hinner⟩ := ok
  exact saturated_route latticeCase h₀ h₁ depth k box n hk hsplit p hp gp
    (anchor_saturated h₀ h₁ labels box hinner p hp gp.1)

/-! ### Anchors with a radial gap -/

theorem halfOf_true_true_eq_halfV : halfOf true true = AdaptiveGap.halfV := by
  funext i
  fin_cases i <;> norm_num [halfOf, AdaptiveGap.halfV]

/-- The layered gain about the anchor of class `(−1/2, −1/2, −1/2)` with `λ = 2 a_c⁺ k`, and a
radial gap `g` of the anchor's lifts on the box (`AdaptiveGap.gapOk`). -/
def gapSatOk (depth : ℕ) (k g : ℚ) (box : Cell) (n : IntVec) : Bool :=
  (decide (0 < k) &&
      splitOk (anchorG true true n) (2 * DirectRoute.scaleWitness.upper * k) depth
        (shiftCell box (seamShiftW n))) &&
    AdaptiveGap.gapOk g box

theorem gapSatOk_sound (latticeCase : LatticeCase) (depth : ℕ) (k g : ℚ) (box : Cell) (n : IntVec)
    (ok : gapSatOk depth k g box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) := by
  simp only [gapSatOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hk, hsplit⟩, hgap⟩ := ok
  have half : HalfClass AdaptiveGap.halfV := by
    rw [← halfOf_true_true_eq_halfV]
    exact halfOf_half true true
  refine saturated_route latticeCase true true depth k box n hk hsplit p hp gp ?_
  rw [halfOf_true_true_eq_halfV]
  exact AdaptiveGap.defect_anchor_gap hgap hp gp.1 half

/-! ### Payments -/

/-- How a box is paid on route `relativeOptical`. -/
inductive OPay where
  | planarAnchor (c : PlanarAnchorCert) (n : IntVec)
  | planarAnchors (c : PlanarAnchorCert) (n : IntVec)
  | planarAnchorsFar (c : PlanarAnchorCert) (n : IntVec)
  | saturated (h₀ h₁ : Bool) (depth : ℕ) (k : ℚ) (labels : Fin 18 → IntVec × Bool) (n : IntVec)
  | split (ax : Axis) (r : ℚ) (left right : OPay)
  | gapSat (depth : ℕ) (k g : ℚ) (n : IntVec)

def OPay.check : OPay → Cell → Bool
  | .planarAnchor c n, b => planarAnchorCertOk c b n
  | .planarAnchors c n, b => planarAnchorSOk c b n
  | .planarAnchorsFar c n, b => planarAnchorSFarOk c b n
  | .saturated h₀ h₁ depth k labels n, b => satOk h₀ h₁ depth k labels b n
  | .split ax r left right, b => left.check (replaceEnd b ax r false) && right.check (replaceEnd b ax r true)
  | .gapSat depth k g n, b => gapSatOk depth k g b n

theorem OPay.sound (latticeCase : LatticeCase) (pay : OPay) (b : Cell) (ok : pay.check b = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) : OpticalEvidence (chartPoint p) := by
  induction pay generalizing b with
  | planarAnchor c n => exact planarAnchorCertOk_sound latticeCase c b n ok p hp gp
  | planarAnchors c n => exact planarAnchorSOk_sound latticeCase c b n ok p hp gp
  | planarAnchorsFar c n => exact planarAnchorSFarOk_sound latticeCase c b n ok p hp gp
  | saturated h₀ h₁ depth k labels n => exact satOk_sound latticeCase h₀ h₁ depth k labels b n ok p hp gp
  | gapSat depth k g n => exact gapSatOk_sound latticeCase depth k g b n ok p hp gp
  | split ax r left right ihl ihr =>
    obtain ⟨okl, okr⟩ := Bool.and_eq_true_iff.mp ok
    rcases two_closed_children b ax r p hp with h | h
    · exact ihl _ okl h
    · exact ihr _ okr h

end BccSharp.Coulomb.CompactCover.AdaptiveOptical
