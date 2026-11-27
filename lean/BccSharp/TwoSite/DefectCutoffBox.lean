import BccSharp.TwoSite.DefectCutoff
import BccSharp.Cover.JLeafCheck

set_option autoImplicit false

/-! # Whole-box forms of the cutoff and annulus bounds

The fixed-point J and D leaf checks bound the actual defect on a whole leaf box
from the registered cost at the 256 corners: `regCost` is separately convex
(`regCost_chord`), so a bound at the corners holds on the box. This module
gives the two new bounds in that shape.

* **Cutoff** (`defect_le_box_cutoff`): if a registration passes
  `registrationCheck`, `det N = 1`, the row and unit conditions of
  `regCost_chord`, and its registered cost is at most `c` at every corner with
  `cutoffOk c` (`c ≤ d♯`), then `defect ≤ regCost` at every valid point of the
  box (`defect_le_regCost_cutoff`).
* **Annulus** (`defect_le_box_annulus`): if `annBoxOk N w b ℓ` holds, then
  `defect ≤ regCost + annCap ℓ` at every point of the box (validity is not
  needed), for every registration passing `registrationCheck`. `annBoxOk` checks witnesses
  `ℓ_j ≥ 0` with `ℓ_j² ≤ primalLo`, an exact rational interval lower bound of
  the squared length `primalQ (annVec N w j) (annOdd N j)` of the `j`-th
  annular image on the box (`sq_annImage`, `primalLo_le`), and
  `annCap ℓ = Σ_j max 0 (13 − 10 ℓ_j)` bounds `Φ` on the box
  (`annPhi_le_annCap`). No condition on the size of the registered cost is
  needed: above `q = 1` the cap `defect ≤ 1` gives the bound.
* `defect_le_cap_annulus`: the D-leaf form, a whole-box cap
  `cap + annCap ℓ` from corner bounds `regCost ≤ cap`.
* **Far annulus** (`defect_le_box_far`): if `annFarOk N w b` holds (all twelve
  interval lengths are at least `13/10` on the box), then `defect ≤ regCost` at
  every point of the box, whatever the size of the cost. This is the annulus
  bound with `ℓ_j = 13/10` and `annCap = 0`.

On the box hull, the three image rows
are enclosed by interval sums and products, and each squared row is bounded
below by the square of its least absolute value (`leastAbs`). -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf.Cutoff
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.DirectRoute (offset)

/-! ### The annular images as squared chart lengths -/

theorem sq_annImage (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (j : Fin 12) (p : Chart)
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    sq (annImage N w j p) = primalQ (annVec N w j) (annOdd N j) p :=
  (primalQ_eq (annVec N w j) (annOdd N j) p h0 h1).symm

/-- An annular weight is at most `(13 − 10 ℓ)₊` for any `ℓ ≥ 0` below the
length. -/
theorem annularWeight_le (v : Vec) (ℓ : ℝ) (h0 : 0 ≤ ℓ) (h : ℓ ^ 2 ≤ sq v) :
    annularWeight v ≤ max 0 (13 - 10 * ℓ) := by
  have hl : ℓ ≤ Real.sqrt (sq v) := by
    have hs := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq h0] at hs
  unfold annularWeight
  apply max_le_max le_rfl
  have := min_le_right (1 : ℝ) (13 - 10 * Real.sqrt (sq v))
  linarith

/-- `Φ ≤ Σ_j (13 − 10 ℓ_j)₊` from pointwise length bounds of the annular
images. -/
theorem annPhi_le_of_len (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (p : Chart) (ℓ : Fin 12 → ℝ)
    (h0 : ∀ j, 0 ≤ ℓ j) (h : ∀ j, ℓ j ^ 2 ≤ sq (annImage N w j p)) :
    annPhi N w p ≤ ∑ j : Fin 12, max 0 (13 - 10 * ℓ j) :=
  Finset.sum_le_sum (fun j _ => annularWeight_le _ _ (h0 j) (h j))

/-! ### Interval lower bounds of a squared chart length -/

/-- Lower end of the product of two intervals. -/
def mulLo (a1 a2 b1 b2 : ℚ) : ℚ := min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2))

/-- Upper end of the product of two intervals. -/
def mulHi (a1 a2 b1 b2 : ℚ) : ℚ := max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2))

/-- The least absolute value on `[lo, hi]`. -/
def leastAbs (lo hi : ℚ) : ℚ := max 0 (max lo (-hi))

/-- Lower and upper ends of `img v s p i` on the box. -/
def imgLo (v : Fin 3 → ℚ) (s : Bool) (b : Cell) (i : Fin 3) : ℚ :=
  v i + if s then b.lo (offset i) else 0

def imgHi (v : Fin 3 → ℚ) (s : Bool) (b : Cell) (i : Fin 3) : ℚ :=
  v i + if s then b.hi (offset i) else 0

/-- Lower and upper ends of `rowA` and `rowB` on the box. -/
def rowALo (v : Fin 3 → ℚ) (s : Bool) (b : Cell) : ℚ :=
  imgLo v s b 0 + mulLo (b.lo 2) (b.hi 2) (imgLo v s b 1) (imgHi v s b 1) +
    mulLo (b.lo 3) (b.hi 3) (imgLo v s b 2) (imgHi v s b 2)

def rowAHi (v : Fin 3 → ℚ) (s : Bool) (b : Cell) : ℚ :=
  imgHi v s b 0 + mulHi (b.lo 2) (b.hi 2) (imgLo v s b 1) (imgHi v s b 1) +
    mulHi (b.lo 3) (b.hi 3) (imgLo v s b 2) (imgHi v s b 2)

def rowBLo (v : Fin 3 → ℚ) (s : Bool) (b : Cell) : ℚ :=
  imgLo v s b 1 + mulLo (b.lo 4) (b.hi 4) (imgLo v s b 2) (imgHi v s b 2)

def rowBHi (v : Fin 3 → ℚ) (s : Bool) (b : Cell) : ℚ :=
  imgHi v s b 1 + mulHi (b.lo 4) (b.hi 4) (imgLo v s b 2) (imgHi v s b 2)

/-- Whole-box lower bound of `primalQ v s` (for `0 < b.lo 0`, `0 < b.lo 1`). -/
def primalLo (v : Fin 3 → ℚ) (s : Bool) (b : Cell) : ℚ :=
  b.lo 0 ^ 2 * leastAbs (rowALo v s b) (rowAHi v s b) ^ 2 +
    b.lo 1 ^ 2 * leastAbs (rowBLo v s b) (rowBHi v s b) ^ 2 +
    leastAbs (imgLo v s b 2) (imgHi v s b 2) ^ 2 / (b.hi 0 ^ 2 * b.hi 1 ^ 2)

theorem mulInterval_mem (a1 a2 b1 b2 x y : ℝ) (hx1 : a1 ≤ x) (hx2 : x ≤ a2) (hy1 : b1 ≤ y)
    (hy2 : y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ x * y ∧
      x * y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  have lo1 : min (a1 * y) (a2 * y) ≤ x * y := by
    rcases le_total 0 y with hy | hy
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact (min_le_right _ _).trans (by nlinarith)
  have lo2 : ∀ a : ℝ, min (a * b1) (a * b2) ≤ a * y := by
    intro a
    rcases le_total 0 a with ha | ha
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact (min_le_right _ _).trans (by nlinarith)
  have hi1 : x * y ≤ max (a1 * y) (a2 * y) := by
    rcases le_total 0 y with hy | hy
    · exact (by nlinarith : x * y ≤ a2 * y).trans (le_max_right _ _)
    · exact (by nlinarith : x * y ≤ a1 * y).trans (le_max_left _ _)
  have hi2 : ∀ a : ℝ, a * y ≤ max (a * b1) (a * b2) := by
    intro a
    rcases le_total 0 a with ha | ha
    · exact (by nlinarith : a * y ≤ a * b2).trans (le_max_right _ _)
    · exact (by nlinarith : a * y ≤ a * b1).trans (le_max_left _ _)
  exact ⟨(min_le_min (lo2 a1) (lo2 a2)).trans lo1, hi1.trans (max_le_max (hi2 a1) (hi2 a2))⟩

theorem mulLo_le (a1 a2 b1 b2 : ℚ) (x y : ℝ) (hx1 : (a1 : ℝ) ≤ x) (hx2 : x ≤ a2)
    (hy1 : (b1 : ℝ) ≤ y) (hy2 : y ≤ b2) :
    (mulLo a1 a2 b1 b2 : ℝ) ≤ x * y ∧ x * y ≤ (mulHi a1 a2 b1 b2 : ℝ) := by
  have h := mulInterval_mem (a1 : ℝ) a2 b1 b2 x y hx1 hx2 hy1 hy2
  unfold mulLo mulHi
  push_cast
  exact h

theorem leastAbs_sq_le (lo hi : ℚ) (t : ℝ) (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    ((leastAbs lo hi : ℚ) : ℝ) ^ 2 ≤ t ^ 2 := by
  unfold leastAbs
  push_cast
  have m0 : (0 : ℝ) ≤ max 0 (max (lo : ℝ) (-(hi : ℝ))) := le_max_left _ _
  have m1 : max 0 (max (lo : ℝ) (-(hi : ℝ))) ≤ |t| := by
    apply max_le (abs_nonneg t)
    apply max_le
    · exact h1.trans (le_abs_self t)
    · exact (neg_le_neg h2).trans (neg_le_abs t)
  calc max 0 (max (lo : ℝ) (-(hi : ℝ))) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ m0 m1 2
    _ = t ^ 2 := sq_abs t

theorem imgInterval_mem (v : Fin 3 → ℚ) (s : Bool) (b : Cell) (p : Chart) (hp : b.Mem p)
    (i : Fin 3) :
    ((imgLo v s b i : ℚ) : ℝ) ≤ img v s p i ∧ img v s p i ≤ ((imgHi v s b i : ℚ) : ℝ) := by
  have h := hp (offset i)
  unfold imgLo imgHi img
  cases s
  · simp
  · simp only [ite_true]
    push_cast
    constructor <;> linarith [h.1, h.2]

/-- **The interval bound.** `primalLo v s b ≤ primalQ v s p` on the box. -/
theorem primalLo_le (v : Fin 3 → ℚ) (s : Bool) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) (p : Chart) (hp : b.Mem p) :
    ((primalLo v s b : ℚ) : ℝ) ≤ primalQ v s p := by
  have i0 := imgInterval_mem v s b p hp 0
  have i1 := imgInterval_mem v s b p hp 1
  have i2 := imgInterval_mem v s b p hp 2
  have m2 := mulLo_le (b.lo 2) (b.hi 2) (imgLo v s b 1) (imgHi v s b 1) (p 2) (img v s p 1)
    (hp 2).1 (hp 2).2 i1.1 i1.2
  have m3 := mulLo_le (b.lo 3) (b.hi 3) (imgLo v s b 2) (imgHi v s b 2) (p 3) (img v s p 2)
    (hp 3).1 (hp 3).2 i2.1 i2.2
  have m4 := mulLo_le (b.lo 4) (b.hi 4) (imgLo v s b 2) (imgHi v s b 2) (p 4) (img v s p 2)
    (hp 4).1 (hp 4).2 i2.1 i2.2
  have rA : ((rowALo v s b : ℚ) : ℝ) ≤ rowA v s p ∧ rowA v s p ≤ ((rowAHi v s b : ℚ) : ℝ) := by
    unfold rowALo rowAHi rowA
    push_cast
    constructor <;> linarith [i0.1, i0.2, m2.1, m2.2, m3.1, m3.2]
  have rB : ((rowBLo v s b : ℚ) : ℝ) ≤ rowB v s p ∧ rowB v s p ≤ ((rowBHi v s b : ℚ) : ℝ) := by
    unfold rowBLo rowBHi rowB
    push_cast
    constructor <;> linarith [i1.1, i1.2, m4.1, m4.2]
  have sA := leastAbs_sq_le (rowALo v s b) (rowAHi v s b) (rowA v s p) rA.1 rA.2
  have sB := leastAbs_sq_le (rowBLo v s b) (rowBHi v s b) (rowB v s p) rB.1 rB.2
  have sC := leastAbs_sq_le (imgLo v s b 2) (imgHi v s b 2) (rowC v s p) i2.1 i2.2
  have p0 : (b.lo 0 : ℝ) ≤ p 0 := (hp 0).1
  have p1 : (b.lo 1 : ℝ) ≤ p 1 := (hp 1).1
  have q0 : p 0 ≤ (b.hi 0 : ℝ) := (hp 0).2
  have q1 : p 1 ≤ (b.hi 1 : ℝ) := (hp 1).2
  have pp0 : 0 < p 0 := h0.trans_le p0
  have pp1 : 0 < p 1 := h1.trans_le p1
  have e0 : (b.lo 0 : ℝ) ^ 2 ≤ p 0 ^ 2 := pow_le_pow_left₀ h0.le p0 2
  have e1 : (b.lo 1 : ℝ) ^ 2 ≤ p 1 ^ 2 := pow_le_pow_left₀ h1.le p1 2
  have tA : (b.lo 0 : ℝ) ^ 2 * ((leastAbs (rowALo v s b) (rowAHi v s b) : ℚ) : ℝ) ^ 2 ≤
      p 0 ^ 2 * rowA v s p ^ 2 :=
    mul_le_mul e0 sA (sq_nonneg _) (sq_nonneg _)
  have tB : (b.lo 1 : ℝ) ^ 2 * ((leastAbs (rowBLo v s b) (rowBHi v s b) : ℚ) : ℝ) ^ 2 ≤
      p 1 ^ 2 * rowB v s p ^ 2 :=
    mul_le_mul e1 sB (sq_nonneg _) (sq_nonneg _)
  have den : p 0 ^ 2 * p 1 ^ 2 ≤ (b.hi 0 : ℝ) ^ 2 * (b.hi 1 : ℝ) ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ pp0.le q0 2) (pow_le_pow_left₀ pp1.le q1 2) (by positivity)
      (by positivity)
  have dpos : 0 < p 0 ^ 2 * p 1 ^ 2 := by positivity
  have tC : ((leastAbs (imgLo v s b 2) (imgHi v s b 2) : ℚ) : ℝ) ^ 2 /
      ((b.hi 0 : ℝ) ^ 2 * (b.hi 1 : ℝ) ^ 2) ≤ rowC v s p ^ 2 / (p 0 ^ 2 * p 1 ^ 2) :=
    div_le_div₀ (sq_nonneg _) sC dpos den
  unfold primalLo primalQ
  push_cast
  linarith

/-! ### The annulus cap on a box -/

/-- The annulus check on a box: witnesses `ℓ_j ≥ 0` below the interval lengths
of the twelve annular images. -/
def annBoxOk (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (b : Cell) (ℓ : Fin 12 → ℚ) : Bool :=
  decide (0 < b.lo 0) && decide (0 < b.lo 1) &&
    decide (∀ j : Fin 12, 0 ≤ ℓ j ∧ ℓ j ^ 2 ≤ primalLo (annVec N w j) (annOdd N j) b)

/-- The box annulus cap `Σ_j (13 − 10 ℓ_j)₊`. -/
def annCap (ℓ : Fin 12 → ℚ) : ℚ := ∑ j : Fin 12, max 0 (13 - 10 * ℓ j)

theorem annCap_nonneg (ℓ : Fin 12 → ℚ) : 0 ≤ annCap ℓ :=
  Finset.sum_nonneg (fun _ _ => le_max_left _ _)

theorem annBoxOk_sound {N : Fin 3 → Fin 3 → ℚ} {w : Fin 3 → ℚ} {b : Cell} {ℓ : Fin 12 → ℚ}
    (h : annBoxOk N w b ℓ = true) :
    (0 : ℝ) < b.lo 0 ∧ (0 : ℝ) < b.lo 1 ∧
      ∀ j : Fin 12, 0 ≤ ℓ j ∧ ℓ j ^ 2 ≤ primalLo (annVec N w j) (annOdd N j) b := by
  simp only [annBoxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1, h2⟩

/-- **`Φ` on a box.** -/
theorem annPhi_le_annCap (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (b : Cell) (ℓ : Fin 12 → ℚ)
    (h : annBoxOk N w b ℓ = true) (p : Chart) (hp : b.Mem p) :
    annPhi N w p ≤ ((annCap ℓ : ℚ) : ℝ) := by
  obtain ⟨h0, h1, hj⟩ := annBoxOk_sound h
  have pp0 : 0 < p 0 := h0.trans_le (hp 0).1
  have pp1 : 0 < p 1 := h1.trans_le (hp 1).1
  have hlen : ∀ j, ((ℓ j : ℚ) : ℝ) ^ 2 ≤ sq (annImage N w j p) := by
    intro j
    rw [sq_annImage N w j p pp0.ne' pp1.ne']
    have hq : ((ℓ j ^ 2 : ℚ) : ℝ) ≤ ((primalLo (annVec N w j) (annOdd N j) b : ℚ) : ℝ) := by
      exact_mod_cast (hj j).2
    push_cast at hq
    exact hq.trans (primalLo_le _ _ b h0 h1 p hp)
  have hb := annPhi_le_of_len N w p (fun j => ((ℓ j : ℚ) : ℝ))
    (fun j => by exact_mod_cast (hj j).1) hlen
  unfold annCap
  push_cast
  exact hb

/-- The far-annulus check: every annular image is at least `13/10` long on the
whole box (`annBoxOk` with `ℓ_j = 13/10`), so `Φ = 0` there. -/
def annFarOk (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (b : Cell) : Bool :=
  decide (0 < b.lo 0) && decide (0 < b.lo 1) &&
    decide (∀ j : Fin 12, 169 / 100 ≤ primalLo (annVec N w j) (annOdd N j) b)

theorem annFarOk_annBoxOk {N : Fin 3 → Fin 3 → ℚ} {w : Fin 3 → ℚ} {b : Cell}
    (h : annFarOk N w b = true) : annBoxOk N w b (fun _ => 13 / 10) = true := by
  simp only [annFarOk, annBoxOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨⟨h0, h1⟩, fun j => ⟨by norm_num, ?_⟩⟩
  have e : ((13 / 10 : ℚ)) ^ 2 = 169 / 100 := by norm_num
  rw [e]
  exact h2 j

theorem annCap_far : annCap (fun _ => (13 / 10 : ℚ)) = 0 := by
  norm_num [annCap]

/-! ### Whole-box defect bounds -/

/-- **Annulus, whole box.** At every point of the box,
`defect ≤ regCost + annCap ℓ`. -/
theorem defect_le_box_annulus (reg : RegData) (b : Cell) (ℓ : Fin 12 → ℚ)
    (hr : registrationCheck reg.B reg.N reg.U reg.f0 = true)
    (ha : annBoxOk reg.N reg.w b ℓ = true) (p : Chart) (hp : b.Mem p) :
    defect (chartPoint p) ≤ regCost reg.N reg.U reg.w p + ((annCap ℓ : ℚ) : ℝ) := by
  have hd := defect_le_annulus reg.B reg.N reg.U reg.f0 reg.wrap hr p
  have e : (fun i => reg.f0 i + (reg.wrap i : ℚ)) = reg.w := rfl
  rw [e] at hd
  have hc := annPhi_le_annCap reg.N reg.w b ℓ ha p hp
  linarith

/-- **Cutoff, whole box.** If the registered cost is at most `c ≤ d♯` at the 256
corners of a box with positive radial coordinates, under the conditions of
`regCost_chord`, then `defect ≤ regCost` at every valid point of the box. -/
theorem defect_le_box_cutoff (reg : RegData) (b : Cell) (c : ℚ)
    (hr : registrationCheck reg.B reg.N reg.U reg.f0 = true) (hN : det3Q reg.N = 1)
    (hc : cutoffOk c = true) (b0 : (0 : ℝ) < b.lo 0) (b1 : (0 : ℝ) < b.lo 1)
    (unit : ∀ i, ∑ j, (reg.U i j) ^ 2 = 1)
    (cond : 4 * (b.hi 0 * b.hi 1) ^ 2 ≤ 9 * ∑ j, (reg.N 2 j) ^ 2)
    (hcorner : ∀ bits, regCost reg.N reg.U reg.w (corner b bits) ≤ (c : ℝ))
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    defect (chartPoint p) ≤ regCost reg.N reg.U reg.w p := by
  have chord := regCost_chord reg.N reg.U reg.w b b0 b1 unit cond
  obtain ⟨bits, hb⟩ := corner_le b (fun x => -regCost reg.N reg.U reg.w x) chord p hp
  have hb' : -regCost reg.N reg.U reg.w (corner b bits) ≤ -regCost reg.N reg.U reg.w p := hb
  have hpc : regCost reg.N reg.U reg.w p ≤ (c : ℝ) := by
    have := hcorner bits
    linarith
  have hq : regCost reg.N reg.U (fun i => reg.f0 i + (reg.wrap i : ℚ)) p ≤ dSharp :=
    hpc.trans (cutoffOk_sound hc)
  exact defect_le_regCost_cutoff reg.B reg.N reg.U reg.f0 reg.wrap hr hN p hv hq

/-- **D-leaf cap.** If the registered cost is at most `cap` at the 256 corners,
under the conditions of `regCost_chord`, and `annBoxOk` holds, the actual
defect is at most `cap + annCap ℓ` at every point of the box. -/
theorem defect_le_cap_annulus (reg : RegData) (b : Cell) (cap : ℚ) (ℓ : Fin 12 → ℚ)
    (hr : registrationCheck reg.B reg.N reg.U reg.f0 = true)
    (ha : annBoxOk reg.N reg.w b ℓ = true)
    (unit : ∀ i, ∑ j, (reg.U i j) ^ 2 = 1)
    (cond : 4 * (b.hi 0 * b.hi 1) ^ 2 ≤ 9 * ∑ j, (reg.N 2 j) ^ 2)
    (hcorner : ∀ bits, regCost reg.N reg.U reg.w (corner b bits) ≤ (cap : ℝ))
    (p : Chart) (hp : b.Mem p) :
    defect (chartPoint p) ≤ ((cap + annCap ℓ : ℚ) : ℝ) := by
  obtain ⟨b0, b1, -⟩ := annBoxOk_sound ha
  have chord := regCost_chord reg.N reg.U reg.w b b0 b1 unit cond
  obtain ⟨bits, hb⟩ := corner_le b (fun x => -regCost reg.N reg.U reg.w x) chord p hp
  have hb' : -regCost reg.N reg.U reg.w (corner b bits) ≤ -regCost reg.N reg.U reg.w p := hb
  have hpc : regCost reg.N reg.U reg.w p ≤ (cap : ℝ) := by
    have := hcorner bits
    linarith
  have hd := defect_le_box_annulus reg b ℓ hr ha p hp
  push_cast
  linarith

/-- **Far annulus, whole box.** If every annular image is at least `13/10`
long on the box (`annFarOk`), the actual defect is at most the registered cost
at every point of the box, whatever the size of the cost. -/
theorem defect_le_box_far (reg : RegData) (b : Cell)
    (hr : registrationCheck reg.B reg.N reg.U reg.f0 = true)
    (hf : annFarOk reg.N reg.w b = true) (p : Chart) (hp : b.Mem p) :
    defect (chartPoint p) ≤ regCost reg.N reg.U reg.w p := by
  have h := defect_le_box_annulus reg b (fun _ => 13 / 10) hr (annFarOk_annBoxOk hf) p hp
  rw [annCap_far] at h
  simpa using h

end BccSharp.Coulomb.CompactCover.JLeaf.Cutoff
