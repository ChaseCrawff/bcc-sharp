import BccSharp.Lattice.TangentCover

set_option autoImplicit false

/-! Tangent leaves for the Lattice strain atlases.

In strain coordinates the metric of a chart point `w` is `λ J` with `J = 1 + S(w)` and
`λ = det(J)^(-1/3)` (`reconstructedMetric`). In the coordinates `s = (a, b, u, v, z)` of
`strainTensor` (a fixed positive rescaling of `w`), `J = sJ s` is affine. A certified tangent
aggregate (`TangentE1.Certified`) bounds the positive series below by `A - G(s)` with

`G(s) = c₁ λ ⟨P', J⟩ + c₂ λ² ⟨D', adj J⟩ (+ γ ‖λ J - 1‖²)`,

where `P'`, `D'` are the aggregate's matrices in the cubic frame and `c₁ c₂ = 1` are powers of
`2^(2/3)`. `G` is not convex in each coordinate in general, so its maximum over an `s`-box is
bounded by the maximum over the 32 corners plus `Σ_i M_i d_i²/8`, where `-M_i` is a lower bound
of `∂²G/∂s_i²` on the box (`line_bound`, `box_bound`). The second derivatives along coordinate
lines are explicit (`lineDerivs`) and enclosed by interval arithmetic on the box; the corners
are evaluated exactly, with a checked cube-root bracket for `λ`. The optional `γ` term is the
defect bound near BCC. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.StrainTangent
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentE1
open BccSharp.Coulomb.BravaisCover.TangentCover
open BccSharp.Coulomb.CompactCover

/-! ## Rational endpoint intervals -/

structure QI where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace QI

def Mem (a : QI) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

def exact (q : ℚ) : QI := ⟨q, q⟩
def add (a b : QI) : QI := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : QI) : QI := ⟨-a.hi, -a.lo⟩
def sub (a b : QI) : QI := ⟨a.lo - b.hi, a.hi - b.lo⟩
def mul (a b : QI) : QI :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
    max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩
def scale (c : ℚ) (a : QI) : QI := ⟨min (c * a.lo) (c * a.hi), max (c * a.lo) (c * a.hi)⟩
def sq (a : QI) : QI :=
  if 0 ≤ a.lo then ⟨a.lo * a.lo, a.hi * a.hi⟩
  else if a.hi ≤ 0 then ⟨a.hi * a.hi, a.lo * a.lo⟩
  else ⟨0, max (a.lo * a.lo) (a.hi * a.hi)⟩
/-- `x⁻¹` on an interval with positive lower end. -/
def inv (a : QI) : QI := ⟨a.hi⁻¹, a.lo⁻¹⟩
/-- Outward rounding to the grid `2^-64`. -/
def round (a : QI) : QI := ⟨FixedLocal.dyadicFloor 64 a.lo, FixedLocal.dyadicCeil 64 a.hi⟩

theorem mem_exact (q : ℚ) : (exact q).Mem (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem mem_add {a b : QI} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.add b).Mem (x + y) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  constructor <;> simp only [add, Rat.cast_add] <;> linarith

theorem mem_neg {a : QI} {x : ℝ} (ha : a.Mem x) : a.neg.Mem (-x) := by
  obtain ⟨h1, h2⟩ := ha
  constructor <;> simp only [neg, Rat.cast_neg] <;> linarith

theorem mem_sub {a b : QI} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.sub b).Mem (x - y) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  constructor <;> simp only [sub, Rat.cast_sub] <;> linarith

theorem mul_bounds_real {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hxy : min (x*c) (x*d) ≤ x*y ∧ x*y ≤ max (x*c) (x*d) := by
    rcases le_total 0 x with h | h
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 h),
        (mul_le_mul_of_nonneg_left hy.2 h).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 h),
        (mul_le_mul_of_nonpos_left hy.1 h).trans (le_max_left _ _)⟩
  have hc : min (a*c) (b*c) ≤ x*c ∧ x*c ≤ max (a*c) (b*c) := by
    rcases le_total 0 c with h | h
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 h),
        (mul_le_mul_of_nonneg_right hx.2 h).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 h),
        (mul_le_mul_of_nonpos_right hx.1 h).trans (le_max_left _ _)⟩
  have hd : min (a*d) (b*d) ≤ x*d ∧ x*d ≤ max (a*d) (b*d) := by
    rcases le_total 0 d with h | h
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 h),
        (mul_le_mul_of_nonneg_right hx.2 h).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 h),
        (mul_le_mul_of_nonpos_right hx.1 h).trans (le_max_left _ _)⟩
  constructor
  · refine le_trans ?_ hxy.1
    refine le_min (le_trans ?_ hc.1) (le_trans ?_ hd.1)
    · exact le_min ((min_le_left _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_left _ _))
    · exact le_min ((min_le_left _ _).trans (min_le_right _ _))
        ((min_le_right _ _).trans (min_le_right _ _))
  · refine le_trans hxy.2 ?_
    refine max_le (le_trans hc.2 ?_) (le_trans hd.2 ?_)
    · exact max_le ((le_max_left (a*c) (a*d)).trans (le_max_left _ _))
        ((le_max_left (b*c) (b*d)).trans (le_max_right _ _))
    · exact max_le ((le_max_right (a*c) (a*d)).trans (le_max_left _ _))
        ((le_max_right (b*c) (b*d)).trans (le_max_right _ _))

theorem mem_mul {a b : QI} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.mul b).Mem (x * y) := by
  have h := mul_bounds_real ha hb
  constructor
  · simp only [mul, Rat.cast_min, Rat.cast_mul]
    exact h.1
  · simp only [mul, Rat.cast_max, Rat.cast_mul]
    exact h.2

theorem mem_scale (c : ℚ) {a : QI} {x : ℝ} (ha : a.Mem x) : (a.scale c).Mem ((c : ℝ) * x) := by
  obtain ⟨h1, h2⟩ := ha
  unfold scale
  constructor <;> simp only [Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  · rcases le_total 0 (c : ℝ) with hc | hc
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 hc)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 hc)
  · rcases le_total 0 (c : ℝ) with hc | hc
    · exact (mul_le_mul_of_nonneg_left h2 hc).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left h1 hc).trans (le_max_left _ _)

theorem mem_sq {a : QI} {x : ℝ} (ha : a.Mem x) : a.sq.Mem (x * x) := by
  obtain ⟨h1, h2⟩ := ha
  unfold sq
  split_ifs with hl hu
  · have hl' : (0 : ℝ) ≤ a.lo := by exact_mod_cast hl
    constructor <;> simp only [Rat.cast_mul] <;> nlinarith
  · have hu' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hu
    constructor <;> simp only [Rat.cast_mul] <;> nlinarith
  · constructor
    · simp only [Rat.cast_zero]
      exact mul_self_nonneg x
    · simp only [Rat.cast_max, Rat.cast_mul]
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (by nlinarith)
      · exact le_max_of_le_left (by nlinarith)

theorem mem_inv {a : QI} {x : ℝ} (hpos : 0 < a.lo) (ha : a.Mem x) : a.inv.Mem x⁻¹ := by
  obtain ⟨h1, h2⟩ := ha
  have hl : (0 : ℝ) < a.lo := by exact_mod_cast hpos
  have hx : 0 < x := hl.trans_le h1
  constructor <;> simp only [inv, Rat.cast_inv]
  · exact inv_anti₀ hx h2
  · exact inv_anti₀ hl h1

theorem mem_round {a : QI} {x : ℝ} (ha : a.Mem x) : a.round.Mem x := by
  obtain ⟨h1, h2⟩ := ha
  constructor
  · exact le_trans (by exact_mod_cast FixedLocal.dyadicFloor_le 64 a.lo) h1
  · exact le_trans h2 (by exact_mod_cast FixedLocal.le_dyadicCeil 64 a.hi)

end QI

/-! ## Strain coordinates -/

/-- `1 + strainTensor` in the coordinates `s = (a, b, u, v, z)`. -/
def sJ (s : Fin 5 → ℝ) : Mat :=
  !![1 + s 0 + s 1, s 2, s 3; s 2, 1 + s 1 - s 0, s 4; s 3, s 4, 1 - 2 * s 1]

def sScale (ref : Reference) (i : Fin 5) : ℝ :=
  if i = 0 then (whitenE ref : ℝ) * (1 / Real.sqrt 2)
  else if i = 1 then (whitenE ref : ℝ) * (1 / Real.sqrt 6)
  else (whitenT ref : ℝ) * (1 / Real.sqrt 2)

def sOf (ref : Reference) (w : Point) : Fin 5 → ℝ := fun i => sScale ref i * w i

theorem one_add_strainTensor (ref : Reference) (w : Point) :
    1 + strainTensor ref w = sJ (sOf ref w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [strainTensor, sJ, sOf, sScale, div_eq_mul_inv] <;> ring

def invSqrt2Lo : ℚ := 13043817825332782212 / 2^64
def invSqrt2Hi : ℚ := 13043817825332782213 / 2^64
def invSqrt6Lo : ℚ := 7530851732716320752 / 2^64
def invSqrt6Hi : ℚ := 7530851732716320753 / 2^64

theorem inv_sqrt_bounds {c : ℝ} (hc : 0 < c) {l u : ℚ} (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hl2 : (l : ℝ)^2 * c ≤ 1) (hu2 : 1 ≤ (u : ℝ)^2 * c) :
    (l : ℝ) ≤ 1 / Real.sqrt c ∧ 1 / Real.sqrt c ≤ u := by
  have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have e : 1 / Real.sqrt c = Real.sqrt c⁻¹ := by rw [one_div, Real.sqrt_inv]
  rw [e]
  constructor
  · rw [← Real.sqrt_sq hl']
    apply Real.sqrt_le_sqrt
    rw [← one_div, le_div_iff₀ hc]
    exact hl2
  · rw [← Real.sqrt_sq hu']
    apply Real.sqrt_le_sqrt
    rw [inv_le_iff_one_le_mul₀ hc]
    simpa [mul_comm] using hu2

theorem invSqrt2_bounds : (invSqrt2Lo : ℝ) ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 ≤ (invSqrt2Hi : ℝ) :=
  inv_sqrt_bounds (by norm_num) (by norm_num [invSqrt2Lo]) (by norm_num [invSqrt2Hi])
    (by norm_num [invSqrt2Lo]) (by norm_num [invSqrt2Hi])

theorem invSqrt6_bounds : (invSqrt6Lo : ℝ) ≤ 1 / Real.sqrt 6 ∧ 1 / Real.sqrt 6 ≤ (invSqrt6Hi : ℝ) :=
  inv_sqrt_bounds (by norm_num) (by norm_num [invSqrt6Lo]) (by norm_num [invSqrt6Hi])
    (by norm_num [invSqrt6Lo]) (by norm_num [invSqrt6Hi])

def sLo (ref : Reference) (i : Fin 5) : ℚ :=
  if i = 0 then whitenE ref * invSqrt2Lo else if i = 1 then whitenE ref * invSqrt6Lo
  else whitenT ref * invSqrt2Lo

def sHi (ref : Reference) (i : Fin 5) : ℚ :=
  if i = 0 then whitenE ref * invSqrt2Hi else if i = 1 then whitenE ref * invSqrt6Hi
  else whitenT ref * invSqrt2Hi

theorem whiten_pos (ref : Reference) : (0 : ℝ) < whitenE ref ∧ (0 : ℝ) < whitenT ref := by
  cases ref <;> norm_num [whitenE, whitenT]

theorem sScale_bounds (ref : Reference) (i : Fin 5) :
    0 ≤ sLo ref i ∧ (sLo ref i : ℝ) ≤ sScale ref i ∧ sScale ref i ≤ sHi ref i := by
  obtain ⟨hE, hT⟩ := whiten_pos ref
  have hE' : (0 : ℚ) ≤ whitenE ref := by exact_mod_cast hE.le
  have hT' : (0 : ℚ) ≤ whitenT ref := by exact_mod_cast hT.le
  unfold sLo sHi sScale
  split_ifs
  · refine ⟨mul_nonneg hE' (by norm_num [invSqrt2Lo]), ?_, ?_⟩ <;> push_cast
    · exact mul_le_mul_of_nonneg_left invSqrt2_bounds.1 hE.le
    · exact mul_le_mul_of_nonneg_left invSqrt2_bounds.2 hE.le
  · refine ⟨mul_nonneg hE' (by norm_num [invSqrt6Lo]), ?_, ?_⟩ <;> push_cast
    · exact mul_le_mul_of_nonneg_left invSqrt6_bounds.1 hE.le
    · exact mul_le_mul_of_nonneg_left invSqrt6_bounds.2 hE.le
  · refine ⟨mul_nonneg hT' (by norm_num [invSqrt2Lo]), ?_, ?_⟩ <;> push_cast
    · exact mul_le_mul_of_nonneg_left invSqrt2_bounds.1 hT.le
    · exact mul_le_mul_of_nonneg_left invSqrt2_bounds.2 hT.le

def sLoBnd (ref : Reference) (b : Rectangle) (i : Fin 5) : ℚ :=
  FixedLocal.dyadicFloor 64 (min (sLo ref i * b.lo i) (sHi ref i * b.lo i))

def sHiBnd (ref : Reference) (b : Rectangle) (i : Fin 5) : ℚ :=
  FixedLocal.dyadicCeil 64 (max (sLo ref i * b.hi i) (sHi ref i * b.hi i))

/-- An `s`-box containing the image of a `w`-box, rounded outward to `2^-64`. The ends are
stored as vector literals so that the kernel evaluates each once. -/
def sBox (ref : Reference) (b : Rectangle) : Rectangle :=
  ⟨![sLoBnd ref b 0, sLoBnd ref b 1, sLoBnd ref b 2, sLoBnd ref b 3, sLoBnd ref b 4],
    ![sHiBnd ref b 0, sHiBnd ref b 1, sHiBnd ref b 2, sHiBnd ref b 3, sHiBnd ref b 4]⟩

theorem sBox_ends (ref : Reference) (b : Rectangle) (i : Fin 5) :
    (sBox ref b).lo i = sLoBnd ref b i ∧ (sBox ref b).hi i = sHiBnd ref b i := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

theorem sBox_mem (ref : Reference) (b : Rectangle) (w : Point) (hw : b.Mem w) :
    (sBox ref b).Mem (sOf ref w) := by
  intro i
  rw [(sBox_ends ref b i).1, (sBox_ends ref b i).2, sLoBnd, sHiBnd]
  obtain ⟨h0, hl, hh⟩ := sScale_bounds ref i
  have h0' : (0 : ℝ) ≤ sLo ref i := by exact_mod_cast h0
  have hc : 0 ≤ sScale ref i := h0'.trans hl
  obtain ⟨w1, w2⟩ := hw i
  have lower : ((min (sLo ref i * b.lo i) (sHi ref i * b.lo i) : ℚ) : ℝ) ≤ sScale ref i * b.lo i := by
    push_cast
    rcases le_total 0 (b.lo i : ℝ) with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hh h)
  have upper : sScale ref i * b.hi i ≤ ((max (sLo ref i * b.hi i) (sHi ref i * b.hi i) : ℚ) : ℝ) := by
    push_cast
    rcases le_total 0 (b.hi i : ℝ) with h | h
    · exact (mul_le_mul_of_nonneg_right hh h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hl h).trans (le_max_left _ _)
  constructor
  · refine le_trans (by exact_mod_cast FixedLocal.dyadicFloor_le 64 _) (lower.trans ?_)
    exact mul_le_mul_of_nonneg_left w1 hc
  · refine le_trans ?_ (le_trans upper (by exact_mod_cast FixedLocal.le_dyadicCeil 64 _))
    exact mul_le_mul_of_nonneg_left w2 hc

/-! ## 3×3 algebra -/

section Algebra
variable {R : Type} [CommRing R]

/-- The adjugate of a 3×3 matrix, written out. -/
def adj3 (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  !![X 1 1 * X 2 2 - X 1 2 * X 2 1, X 0 2 * X 2 1 - X 0 1 * X 2 2, X 0 1 * X 1 2 - X 0 2 * X 1 1;
     X 1 2 * X 2 0 - X 1 0 * X 2 2, X 0 0 * X 2 2 - X 0 2 * X 2 0, X 0 2 * X 1 0 - X 0 0 * X 1 2;
     X 1 0 * X 2 1 - X 1 1 * X 2 0, X 0 1 * X 2 0 - X 0 0 * X 2 1, X 0 0 * X 1 1 - X 0 1 * X 1 0]

/-- The derivative of `adj3` at `X` in the direction `E` (bilinear). -/
def dadj3 (X E : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  !![X 1 1 * E 2 2 + E 1 1 * X 2 2 - X 1 2 * E 2 1 - E 1 2 * X 2 1,
     X 0 2 * E 2 1 + E 0 2 * X 2 1 - X 0 1 * E 2 2 - E 0 1 * X 2 2,
     X 0 1 * E 1 2 + E 0 1 * X 1 2 - X 0 2 * E 1 1 - E 0 2 * X 1 1;
     X 1 2 * E 2 0 + E 1 2 * X 2 0 - X 1 0 * E 2 2 - E 1 0 * X 2 2,
     X 0 0 * E 2 2 + E 0 0 * X 2 2 - X 0 2 * E 2 0 - E 0 2 * X 2 0,
     X 0 2 * E 1 0 + E 0 2 * X 1 0 - X 0 0 * E 1 2 - E 0 0 * X 1 2;
     X 1 0 * E 2 1 + E 1 0 * X 2 1 - X 1 1 * E 2 0 - E 1 1 * X 2 0,
     X 0 1 * E 2 0 + E 0 1 * X 2 0 - X 0 0 * E 2 1 - E 0 0 * X 2 1,
     X 0 0 * E 1 1 + E 0 0 * X 1 1 - X 0 1 * E 1 0 - E 0 1 * X 1 0]

/-- `det X` by the first-row cofactor expansion. -/
def det3 (X : Matrix (Fin 3) (Fin 3) R) : R := X 0 0 * adj3 X 0 0 + X 0 1 * adj3 X 1 0 + X 0 2 * adj3 X 2 0

/-- `Σ_ij A_ij X_ij`. -/
def dot3 (A X : Matrix (Fin 3) (Fin 3) R) : R := ∑ i, ∑ j, A i j * X i j

end Algebra

theorem det3_eq (X : Mat) : det3 X = X.det := by
  simp [det3, adj3, Matrix.det_fin_three]
  ring

theorem mul_adj3 (X : Mat) : X * adj3 X = det3 X • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj3, det3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

def castM (M : Matrix (Fin 3) (Fin 3) ℚ) : Mat := fun i j => (M i j : ℝ)

theorem castM_adj3 (M : Matrix (Fin 3) (Fin 3) ℚ) : castM (adj3 M) = adj3 (castM M) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [castM, adj3]

theorem cast_det3 (M : Matrix (Fin 3) (Fin 3) ℚ) : ((det3 M : ℚ) : ℝ) = det3 (castM M) := by
  simp [det3, adj3, castM]

theorem cast_dot3 (A M : Matrix (Fin 3) (Fin 3) ℚ) : ((dot3 A M : ℚ) : ℝ) = dot3 (castM A) (castM M) := by
  simp [dot3, castM]

/-! ## Frames of the two references -/

def dirFrame : Reference → Matrix (Fin 3) (Fin 3) ℚ
  | .bcc => !![1, 0, 1/2; 0, 1, 1/2; 0, 0, 1/2]
  | .fcc => !![1, 1, 0; 1, 0, 1; 0, 1, 1]

def dualFrame : Reference → Matrix (Fin 3) (Fin 3) ℚ
  | .bcc => !![1, 0, 0; 0, 1, 0; -1, -1, 2]
  | .fcc => !![1/2, 1/2, -1/2; 1/2, -1/2, 1/2; -1/2, 1/2, 1/2]

def framePow : Reference → ℝ
  | .bcc => Constants.fccLength
  | .fcc => Constants.fccLength⁻¹

def qmul (M : Matrix (Fin 3) (Fin 3) ℚ) (n : IntVec) : Vec := fun i => ∑ j, (M i j : ℝ) * (n j : ℝ)

theorem linearImage_frame (ref : Reference) (n : IntVec) :
    linearImage (cubicBasis ref) n = framePow ref • qmul (dirFrame ref) n := by
  cases ref
  · rw [bccCubic_short]
    congr 1
    funext i
    fin_cases i <;> simp [bccFrameDirect, qmul, dirFrame, Fin.sum_univ_three] <;> ring
  · funext i
    fin_cases i <;>
      simp [linearImage, cubicBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three, castVec, qmul,
        dirFrame, framePow, Matrix.smul_apply] <;> ring

theorem cycleFrequency_frame (ref : Reference) (n : IntVec) :
    cycleFrequency (cubicBasis ref) n = (framePow ref)⁻¹ • qmul (dualFrame ref) n := by
  cases ref
  · rw [bccCubic_dual]
    simp only [framePow]
    congr 1
    funext i
    fin_cases i <;> simp [bccFrameDual, qmul, dualFrame, Fin.sum_univ_three]; ring
  · have hinv (k i : Fin 3) :
        (cubicBasis .fcc)⁻¹ k i = Constants.fccLength * (cubicInverseQ .fcc k i : ℝ) := by
      rw [cubicInverse_eq]
      rfl
    funext i
    simp only [cycleFrequency, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
      hinv, framePow, inv_inv, Pi.smul_apply, smul_eq_mul, qmul, castVec]
    fin_cases i <;> simp [cubicInverseQ, dualFrame] <;> ring

/-! ## The closed form along the strain chart -/

def dS (s : Fin 5 → ℝ) : ℝ := det3 (sJ s)
def lamS (s : Fin 5 → ℝ) : ℝ := dS s ^ (-(1/3 : ℝ))

/-- `‖X‖²` as `dot3 X X`. -/
theorem frobSq_eq_dot3 (X : Mat) : frobSq X = dot3 X X := by
  simp [frobSq, dot3, pow_two]

/-- The penalty matrices in the cubic frames: `P' = M P Mᵀ`, `D' = M_d D M_dᵀ`. -/
def Pmat (g : Aggregate) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![g.p00, g.p01, g.p02; g.p01, g.p11, g.p12; g.p02, g.p12, g.p22]
def Dmat (g : Aggregate) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![g.d00, g.d01, g.d02; g.d01, g.d11, g.d12; g.d02, g.d12, g.d22]
/-- `A B`, written out for the kernel. -/
def mul3 (A B : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 0 2 * B 2 0, A 0 0 * B 0 1 + A 0 1 * B 1 1 + A 0 2 * B 2 1,
      A 0 0 * B 0 2 + A 0 1 * B 1 2 + A 0 2 * B 2 2;
     A 1 0 * B 0 0 + A 1 1 * B 1 0 + A 1 2 * B 2 0, A 1 0 * B 0 1 + A 1 1 * B 1 1 + A 1 2 * B 2 1,
      A 1 0 * B 0 2 + A 1 1 * B 1 2 + A 1 2 * B 2 2;
     A 2 0 * B 0 0 + A 2 1 * B 1 0 + A 2 2 * B 2 0, A 2 0 * B 0 1 + A 2 1 * B 1 1 + A 2 2 * B 2 1,
      A 2 0 * B 0 2 + A 2 1 * B 1 2 + A 2 2 * B 2 2]

def tr3 (A : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![A 0 0, A 1 0, A 2 0; A 0 1, A 1 1, A 2 1; A 0 2, A 1 2, A 2 2]

theorem mul3_eq (A B : Matrix (Fin 3) (Fin 3) ℚ) : mul3 A B = A * B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul3, Matrix.mul_apply, Fin.sum_univ_three]

theorem tr3_eq (A : Matrix (Fin 3) (Fin 3) ℚ) : tr3 A = A.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def Pframe (ref : Reference) (g : Aggregate) : Matrix (Fin 3) (Fin 3) ℚ :=
  mul3 (mul3 (dirFrame ref) (Pmat g)) (tr3 (dirFrame ref))
def Dframe (ref : Reference) (g : Aggregate) : Matrix (Fin 3) (Fin 3) ℚ :=
  mul3 (mul3 (dualFrame ref) (Dmat g)) (tr3 (dualFrame ref))

theorem Pframe_eq (ref : Reference) (g : Aggregate) :
    Pframe ref g = dirFrame ref * Pmat g * (dirFrame ref).transpose := by
  rw [Pframe, mul3_eq, mul3_eq, tr3_eq]

theorem Dframe_eq (ref : Reference) (g : Aggregate) :
    Dframe ref g = dualFrame ref * Dmat g * (dualFrame ref).transpose := by
  rw [Dframe, mul3_eq, mul3_eq, tr3_eq]

/-- `G(s) = c₁ λ ⟨P', J⟩ + c₂ λ² ⟨D', adj J⟩ + γ (λ² ‖J‖² - 6 λ + 3)`, `c₁ = ℓ^{2e}`, `c₂ = ℓ^{-2e}`. -/
def Gs (ref : Reference) (g : Aggregate) (γ : ℝ) (s : Fin 5 → ℝ) : ℝ :=
  framePow ref ^ 2 * lamS s * dot3 (castM (Pframe ref g)) (sJ s) +
    (framePow ref ^ 2)⁻¹ * lamS s ^ 2 * dot3 (castM (Dframe ref g)) (adj3 (sJ s)) +
    γ * (lamS s ^ 2 * dot3 (sJ s) (sJ s) - 6 * lamS s + 3)

/-! ### The tangent lower bound in strain coordinates -/

def aggDir (g : Aggregate) (Y : Mat) : ℝ :=
  g.p00 * Y 0 0 + g.p11 * Y 1 1 + g.p22 * Y 2 2 + g.p01 * (Y 0 1 + Y 1 0) +
    g.p02 * (Y 0 2 + Y 2 0) + g.p12 * (Y 1 2 + Y 2 1)

def aggDual (g : Aggregate) (Y : Mat) : ℝ :=
  g.d00 * Y 0 0 + g.d11 * Y 1 1 + g.d22 * Y 2 2 + g.d01 * (Y 0 1 + Y 1 0) +
    g.d02 * (Y 0 2 + Y 2 0) + g.d12 * (Y 1 2 + Y 2 1)

theorem foldl_addDir_at (l : List Term) (g : Aggregate) (Y Y' : Mat) :
    aggDir (l.foldl Aggregate.addDir g) Y =
        aggDir g Y + (l.map fun x => (x.2.penalty : ℝ) * quad Y (castVec x.1)).sum ∧
      aggDual (l.foldl Aggregate.addDir g) Y' = aggDual g Y' ∧
      ((l.foldl Aggregate.addDir g).a : ℝ) = g.a + (l.map fun x => (x.2.intercept : ℝ)).sum := by
  induction l generalizing g with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (g.addDir x)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      simp only [aggDir, Aggregate.addDir, quad, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        castVec]
      push_cast
      ring
    · rw [h2]
      simp only [aggDual, Aggregate.addDir]
    · rw [h3]
      simp only [Aggregate.addDir]
      push_cast
      ring

theorem foldl_addDual_at (l : List Term) (g : Aggregate) (Y Y' : Mat) :
    aggDual (l.foldl Aggregate.addDual g) Y' =
        aggDual g Y' + (l.map fun x => (x.2.penalty : ℝ) * quad Y' (castVec x.1)).sum ∧
      aggDir (l.foldl Aggregate.addDual g) Y = aggDir g Y ∧
      ((l.foldl Aggregate.addDual g).a : ℝ) = g.a + (l.map fun x => (x.2.intercept : ℝ)).sum := by
  induction l generalizing g with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (g.addDual x)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      simp only [aggDual, Aggregate.addDual, quad, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        castVec]
      push_cast
      ring
    · rw [h2]
      simp only [aggDir, Aggregate.addDual]
    · rw [h3]
      simp only [Aggregate.addDual]
      push_cast
      ring

theorem aggregate_at (s : TermSet) (Y Y' : Mat) :
    aggDir s.aggregate Y = (s.dir.map fun x => (x.2.penalty : ℝ) * quad Y (castVec x.1)).sum ∧
      aggDual s.aggregate Y' = (s.dual.map fun x => (x.2.penalty : ℝ) * quad Y' (castVec x.1)).sum ∧
      (s.aggregate.a : ℝ) = (s.dir.map fun x => (x.2.intercept : ℝ)).sum +
        (s.dual.map fun x => (x.2.intercept : ℝ)).sum := by
  obtain ⟨d1, d2, d3⟩ := foldl_addDir_at s.dir Aggregate.zero Y Y'
  obtain ⟨u1, u2, u3⟩ := foldl_addDual_at s.dual (s.dir.foldl Aggregate.addDir Aggregate.zero) Y Y'
  have z1 : aggDir Aggregate.zero Y = 0 := by simp [Aggregate.zero, aggDir]
  have z2 : aggDual Aggregate.zero Y' = 0 := by simp [Aggregate.zero, aggDual]
  unfold TermSet.aggregate
  refine ⟨?_, ?_, ?_⟩
  · rw [u2, d1, z1, zero_add]
  · rw [u1, d2, z2, zero_add]
  · rw [u3, d3]
    simp [Aggregate.zero]

/-- `quad X (M n)` through the aggregate entries. -/
theorem dirAt_frame (ref : Reference) (g : Aggregate) (X : Mat) :
    dot3 (castM (Pframe ref g)) X =
      aggDir g (fun k l => ∑ i, ∑ j, (dirFrame ref i k : ℝ) * X i j * (dirFrame ref j l : ℝ)) := by
  rw [Pframe_eq]
  simp only [dot3, castM, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Pmat,
    aggDir]
  simp
  ring

theorem dualAt_frame (ref : Reference) (g : Aggregate) (X : Mat) :
    dot3 (castM (Dframe ref g)) X =
      aggDual g (fun k l => ∑ i, ∑ j, (dualFrame ref i k : ℝ) * X i j * (dualFrame ref j l : ℝ)) := by
  rw [Dframe_eq]
  simp only [dot3, castM, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Dmat,
    aggDual]
  simp
  ring

theorem quad_qmul (M : Matrix (Fin 3) (Fin 3) ℚ) (X : Mat) (n : IntVec) :
    quad X (qmul M n) =
      quad (fun k l => ∑ i, ∑ j, (M i k : ℝ) * X i j * (M j l : ℝ)) (castVec n) := by
  simp only [quad, qmul, Matrix.mulVec, dotProduct, Fin.sum_univ_three, castVec]
  ring

theorem quad_smul_left (c : ℝ) (X : Mat) (v : Vec) : quad (c • X) v = c * quad X v := by
  simp only [quad, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quad_smul_right (c : ℝ) (X : Mat) (v : Vec) : quad X (c • v) = c ^ 2 * quad X v := by
  simp only [quad, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kernelValue_half (x : ℝ) : kernelValue .half x = gKernel (1/2) x := by
  norm_num [kernelValue, KernelKind.power]

theorem kernelValue_one (x : ℝ) : kernelValue .one x = gKernel 1 x := by
  norm_num [kernelValue, KernelKind.power]

private theorem sq_pos_of_ne {v : Vec} (hv : v ≠ 0) : 0 < sq v :=
  lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hv))

/-- A valid term set bounds the positive series of any invertible basis below. -/
theorem lowerR_le (s : TermSet) (hs : s.Valid) (R : Mat) (hR : R.det ≠ 0) :
    (s.dir.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) * sq (linearImage R x.1)).sum +
      (s.dual.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) * sq (cycleFrequency R x.1)).sum ≤
    positiveSeries R := by
  classical
  obtain ⟨nd, nu, vd, vu⟩ := hs
  have shortSum : (s.dir.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) *
      sq (linearImage R x.1)).sum ≤ ∑' n, shortKernel R n := by
    calc _ ≤ (s.dir.map fun x => shortKernel R x.1).sum := by
          apply List.sum_le_sum
          intro x hx
          obtain ⟨hn, hv⟩ := vd x hx
          have hi : linearImage R x.1 ≠ 0 := by
            intro hz
            apply hn
            apply (periodIndices R hR).injective
            apply Subtype.ext
            change linearImage R x.1 = linearImage R 0
            rw [hz, linearImage, castVec_zero, Matrix.mulVec_zero]
          rw [shortKernel_eq R hR x.1 hn, ← kernelValue_half]
          exact hv.2 _ (sq_pos_of_ne hi)
      _ = ∑ n ∈ (s.dir.map Prod.fst).toFinset, shortKernel R n := by
          rw [List.sum_toFinset _ nd, List.map_map]
          rfl
      _ ≤ ∑' n, shortKernel R n :=
          (shortKernel_summable R hR).sum_le_tsum _ (fun n _ => shortKernel_nonnegative R n)
  have dualSum : (s.dual.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) *
      sq (cycleFrequency R x.1)).sum ≤ ∑' n, dualKernel R n := by
    calc _ ≤ (s.dual.map fun x => dualKernel R x.1).sum := by
          apply List.sum_le_sum
          intro x hx
          obtain ⟨hn, hv⟩ := vu x hx
          have hc : cycleFrequency R x.1 ≠ 0 := fun z =>
            hn (cycleFrequency_injective R hR (z.trans (cycleFrequency_zero R).symm))
          rw [dualKernel_eq R hR x.1 hn, ← kernelValue_one]
          exact hv.2 _ (sq_pos_of_ne hc)
      _ = ∑ n ∈ (s.dual.map Prod.fst).toFinset, dualKernel R n := by
          rw [List.sum_toFinset _ nu, List.map_map]
          rfl
      _ ≤ ∑' n, dualKernel R n :=
          (dualKernel_summable R hR).sum_le_tsum _ (fun n _ => dualKernel_nonnegative R n)
  unfold positiveSeries
  exact add_le_add shortSum dualSum

private theorem sum_map_sub' {ι : Type} (l : List ι) (f g : ι → ℝ) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private theorem sum_map_scale {ι : Type} (l : List ι) (f g : ι → ℝ) (c : ℝ) :
    (l.map fun x => f x * (c * g x)).sum = c * (l.map fun x => f x * g x).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem cube_lamS (s : Fin 5 → ℝ) (hd : 0 < dS s) : lamS s ^ 3 * dS s = 1 := by
  unfold lamS
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hd.ne']

theorem lamS_pos (s : Fin 5 → ℝ) (hd : 0 < dS s) : 0 < lamS s := Real.rpow_pos_of_pos hd _

theorem metric_eq (ref : Reference) (w : Point) :
    reconstructedMetric ref w = lamS (sOf ref w) • sJ (sOf ref w) := by
  unfold reconstructedMetric lamS dS
  dsimp only
  rw [one_add_strainTensor, det3_eq]

theorem metric_inv (s : Fin 5 → ℝ) (hd : 0 < dS s) :
    (lamS s • sJ s)⁻¹ = lamS s ^ 2 • adj3 (sJ s) := by
  apply Matrix.inv_eq_right_inv
  have h := cube_lamS s hd
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_adj3, smul_smul]
  have e : lamS s * lamS s ^ 2 * det3 (sJ s) = 1 := by
    have : lamS s * lamS s ^ 2 = lamS s ^ 3 := by ring
    rw [this]
    exact h
  rw [e, one_smul]

theorem frob_metric (s : Fin 5 → ℝ) :
    frobSq (lamS s • sJ s - 1) = lamS s ^ 2 * dot3 (sJ s) (sJ s) - 6 * lamS s + 3 := by
  simp only [frobSq, dot3, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  simp [sJ]
  ring

theorem cubicBasis_det_ne (ref : Reference) : (cubicBasis ref).det ≠ 0 := by
  intro h
  have v := cubicBasis_unitVolume ref
  rw [volumeOf, h, abs_zero] at v
  exact zero_ne_one v

/-- The tangent lower bound in strain coordinates: for a certified aggregate `g`, a strain `w`
with `0 < det J` and a basis `A` with `det A = 1` and the metric of `w`,
`g.a - Gs ref g γ (sOf ref w) ≤ positiveSeries (A * cubicBasis ref) - γ ‖gram A - 1‖²`. -/
theorem strain_lower (ref : Reference) (g : Aggregate) (hg : Certified g) (γ : ℝ) (w : Point)
    (hpos : 0 < dS (sOf ref w)) (A : Mat) (hA : A.det = 1)
    (hGram : gram A = reconstructedMetric ref w) :
    (g.a : ℝ) - Gs ref g γ (sOf ref w) ≤
      positiveSeries (A * cubicBasis ref) - γ * frobSq (gram A - 1) := by
  obtain ⟨s, hs, rfl⟩ := hg
  set p := sOf ref w with hp
  set X := sJ p with hX
  set l := lamS p with hl
  have hC : gram A = l • X := by rw [hGram, metric_eq]
  have hR : (A * cubicBasis ref).det ≠ 0 := by
    rw [Matrix.det_mul, hA, one_mul]
    exact cubicBasis_det_ne ref
  have lower := lowerR_le s hs (A * cubicBasis ref) hR
  have hinv : (gram A)⁻¹ = l ^ 2 • adj3 X := by rw [hC]; exact metric_inv p hpos
  have dirTerm (n : IntVec) : sq (linearImage (A * cubicBasis ref) n) =
      (framePow ref ^ 2 * l) *
        quad (fun k m => ∑ i, ∑ j, (dirFrame ref i k : ℝ) * X i j * (dirFrame ref j m : ℝ)) (castVec n) := by
    rw [(strain_norms ref A (gram A) rfl n).1, linearImage_frame, quad_smul_right, hC, quad_smul_left,
      quad_qmul]
    ring
  have dualTerm (n : IntVec) : sq (cycleFrequency (A * cubicBasis ref) n) =
      ((framePow ref ^ 2)⁻¹ * l ^ 2) *
        quad (fun k m => ∑ i, ∑ j, (dualFrame ref i k : ℝ) * adj3 X i j * (dualFrame ref j m : ℝ))
          (castVec n) := by
    rw [(strain_norms ref A (gram A) rfl n).2, cycleFrequency_frame, quad_smul_right, hinv, quad_smul_left,
      quad_qmul, inv_pow]
    ring
  obtain ⟨aD, aU, aA⟩ := aggregate_at s
    (fun k m => ∑ i, ∑ j, (dirFrame ref i k : ℝ) * X i j * (dirFrame ref j m : ℝ))
    (fun k m => ∑ i, ∑ j, (dualFrame ref i k : ℝ) * adj3 X i j * (dualFrame ref j m : ℝ))
  rw [sum_map_sub', sum_map_sub'] at lower
  simp only [dirTerm, dualTerm] at lower
  rw [sum_map_scale, sum_map_scale, ← aD, ← aU, ← dirAt_frame, ← dualAt_frame] at lower
  have hf : frobSq (gram A - 1) = l ^ 2 * dot3 X X - 6 * l + 3 := by rw [hC]; exact frob_metric p
  rw [hf]
  unfold Gs
  rw [aA]
  linarith

/-! ## Derivatives along coordinate lines -/

/-! ### Scalar chain rules for `λ A + λ² B` with `λ = d^(-1/3)` -/

def lamF (d : ℝ → ℝ) (x : ℝ) : ℝ := d x ^ (-(1/3 : ℝ))
def lam1F (d d1 : ℝ → ℝ) (x : ℝ) : ℝ := -(1/3) * d1 x * lamF d x / d x
def lam2F (d d1 d2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  lamF d x * ((4/9) * (d1 x / d x) ^ 2 - (1/3) * (d2 x / d x))
def G0F (d A B : ℝ → ℝ) (k : ℝ) (x : ℝ) : ℝ := lamF d x * A x + lamF d x ^ 2 * B x + k
def G1F (d d1 A A1 B B1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  lam1F d d1 x * A x + lamF d x * A1 x + 2 * lamF d x * lam1F d d1 x * B x + lamF d x ^ 2 * B1 x
def G2F (d d1 d2 A A1 B B1 B2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  lam2F d d1 d2 x * A x + 2 * lam1F d d1 x * A1 x + 2 * lam1F d d1 x ^ 2 * B x +
    2 * lamF d x * lam2F d d1 d2 x * B x + 4 * lamF d x * lam1F d d1 x * B1 x + lamF d x ^ 2 * B2 x

theorem lamF_deriv {d d1 : ℝ → ℝ} {t : ℝ} (hd : HasDerivAt d (d1 t) t) (hpos : 0 < d t) :
    HasDerivAt (lamF d) (lam1F d d1 t) t := by
  have h := hd.rpow_const (p := -(1/3 : ℝ)) (Or.inl hpos.ne')
  have e : lamF d = fun y => d y ^ (-(1/3 : ℝ)) := rfl
  rw [e]
  convert h using 1
  unfold lam1F lamF
  rw [Real.rpow_sub_one hpos.ne']
  ring

theorem lam1F_deriv {d d1 d2 : ℝ → ℝ} {t : ℝ} (hd : HasDerivAt d (d1 t) t)
    (hd1 : HasDerivAt d1 (d2 t) t) (hpos : 0 < d t) :
    HasDerivAt (lam1F d d1) (lam2F d d1 d2 t) t := by
  have hl := lamF_deriv hd hpos
  have h := ((hd1.const_mul (-(1/3 : ℝ))).mul hl).div hd hpos.ne'
  have e : lam1F d d1 = fun x => -(1/3) * d1 x * lamF d x / d x := rfl
  rw [e]
  convert h using 1
  simp only [Pi.mul_apply]
  unfold lam2F lam1F
  field_simp
  ring

theorem G0F_deriv {d d1 A A1 B B1 : ℝ → ℝ} {t : ℝ} (k : ℝ) (hd : HasDerivAt d (d1 t) t) (hpos : 0 < d t)
    (hA : HasDerivAt A (A1 t) t) (hB : HasDerivAt B (B1 t) t) :
    HasDerivAt (G0F d A B k) (G1F d d1 A A1 B B1 t) t := by
  have hl := lamF_deriv hd hpos
  have h := ((hl.mul hA).add ((hl.pow 2).mul hB)).add_const k
  have e : G0F d A B k = fun x => lamF d x * A x + lamF d x ^ 2 * B x + k := rfl
  rw [e]
  convert h using 1
  simp only [Pi.pow_apply]
  unfold G1F
  push_cast
  ring

theorem G1F_deriv {d d1 d2 A A1 B B1 B2 : ℝ → ℝ} {t : ℝ} (hd : HasDerivAt d (d1 t) t)
    (hd1 : HasDerivAt d1 (d2 t) t) (hpos : 0 < d t) (hA : HasDerivAt A (A1 t) t)
    (hA1 : HasDerivAt A1 0 t) (hB : HasDerivAt B (B1 t) t) (hB1 : HasDerivAt B1 (B2 t) t) :
    HasDerivAt (G1F d d1 A A1 B B1) (G2F d d1 d2 A A1 B B1 B2 t) t := by
  have hl := lamF_deriv hd hpos
  have hl1 := lam1F_deriv hd hd1 hpos
  have h := (((hl1.mul hA).add (hl.mul hA1)).add (((hl.const_mul 2).mul hl1).mul hB)).add
    ((hl.pow 2).mul hB1)
  have e : G1F d d1 A A1 B B1 = fun x => lam1F d d1 x * A x + lamF d x * A1 x +
      2 * lamF d x * lam1F d d1 x * B x + lamF d x ^ 2 * B1 x := rfl
  rw [e]
  convert h using 1
  simp only [Pi.mul_apply, Pi.pow_apply]
  unfold G2F
  push_cast
  ring

/-! ### Polynomial identities along a line `X + u E` -/

/-- `tr (A B)`. -/
def trm (A B : Mat) : ℝ := ∑ i, ∑ j, A i j * B j i

theorem line_det (X E : Mat) (u : ℝ) :
    det3 (X + u • E) = det3 X + trm (adj3 X) E * u + trm (adj3 E) X * u ^ 2 + det3 E * u ^ 3 := by
  simp [det3, adj3, trm, Fin.sum_univ_three]
  ring

theorem line_det1 (X E : Mat) (u : ℝ) :
    trm (adj3 (X + u • E)) E = trm (adj3 X) E + 2 * trm (adj3 E) X * u + 3 * det3 E * u ^ 2 + 0 * u ^ 3 := by
  simp [det3, adj3, trm, Fin.sum_univ_three]
  ring

theorem line_adj (D X E : Mat) (u : ℝ) :
    dot3 D (adj3 (X + u • E)) = dot3 D (adj3 X) + dot3 D (dadj3 X E) * u + dot3 D (adj3 E) * u ^ 2 + 0 * u ^ 3 := by
  simp [dot3, adj3, dadj3, Fin.sum_univ_three]
  ring

theorem line_dadj (D X E : Mat) (u : ℝ) :
    dot3 D (dadj3 (X + u • E) E) = dot3 D (dadj3 X E) + 2 * dot3 D (adj3 E) * u + 0 * u ^ 2 + 0 * u ^ 3 := by
  simp [dot3, adj3, dadj3, Fin.sum_univ_three]
  ring

theorem line_dot (P X E : Mat) (u : ℝ) :
    dot3 P (X + u • E) = dot3 P X + dot3 P E * u + 0 * u ^ 2 + 0 * u ^ 3 := by
  simp [dot3, Fin.sum_univ_three]
  ring

theorem line_frob (X E : Mat) (u : ℝ) :
    dot3 (X + u • E) (X + u • E) = dot3 X X + 2 * dot3 X E * u + dot3 E E * u ^ 2 + 0 * u ^ 3 := by
  simp [dot3, Fin.sum_univ_three]
  ring

theorem line_frob1 (X E : Mat) (u : ℝ) :
    dot3 (X + u • E) E = dot3 X E + dot3 E E * u + 0 * u ^ 2 + 0 * u ^ 3 := by
  simp [dot3, Fin.sum_univ_three]
  ring

theorem line_poly (Φ : Mat → ℝ) (X E : Mat) (t0 c0 c1 c2 c3 : ℝ)
    (h : ∀ u : ℝ, Φ (X + u • E) = c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3) :
    HasDerivAt (fun t => Φ (X + (t - t0) • E)) c1 t0 := by
  have e : (fun t => Φ (X + (t - t0) • E)) =
      fun t => c0 + c1 * (t - t0) + c2 * (t - t0) ^ 2 + c3 * (t - t0) ^ 3 := by
    funext t
    exact h (t - t0)
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => t - t0) 1 t0 := (hasDerivAt_id t0).sub_const t0
  have h2 := (((h1.const_mul c1).const_add c0).add ((h1.pow 2).const_mul c2)).add ((h1.pow 3).const_mul c3)
  convert h2 using 1
  simp

/-! ### The coordinate directions of `sJ` -/

def Ecoord (i : Fin 5) : Matrix (Fin 3) (Fin 3) ℚ :=
  if i = 0 then !![1, 0, 0; 0, -1, 0; 0, 0, 0]
  else if i = 1 then !![1, 0, 0; 0, 1, 0; 0, 0, -2]
  else if i = 2 then !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  else if i = 3 then !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  else !![0, 0, 0; 0, 0, 1; 0, 1, 0]

theorem sJ_update (s : Fin 5 → ℝ) (i : Fin 5) (t : ℝ) :
    sJ (Function.update s i t) = sJ s + (t - s i) • castM (Ecoord i) := by
  ext k l
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [sJ, castM, Ecoord] <;> ring

/-! ### Pointwise first and second derivatives of `G` along coordinate `i` -/

section Pointwise
variable (ref : Reference) (g : Aggregate) (γ : ℝ)

def c1R : ℝ := framePow ref ^ 2
def c2R : ℝ := (framePow ref ^ 2)⁻¹

def d1P (i : Fin 5) (q : Fin 5 → ℝ) : ℝ := trm (adj3 (sJ q)) (castM (Ecoord i))
def d2P (i : Fin 5) (q : Fin 5 → ℝ) : ℝ := 2 * trm (adj3 (castM (Ecoord i))) (sJ q)
def AP (q : Fin 5 → ℝ) : ℝ := c1R ref * dot3 (castM (Pframe ref g)) (sJ q) - 6 * γ
def A1P (i : Fin 5) : ℝ := c1R ref * dot3 (castM (Pframe ref g)) (castM (Ecoord i))
def BP (q : Fin 5 → ℝ) : ℝ :=
  c2R ref * dot3 (castM (Dframe ref g)) (adj3 (sJ q)) + γ * dot3 (sJ q) (sJ q)
def B1P (i : Fin 5) (q : Fin 5 → ℝ) : ℝ :=
  c2R ref * dot3 (castM (Dframe ref g)) (dadj3 (sJ q) (castM (Ecoord i))) +
    γ * (2 * dot3 (sJ q) (castM (Ecoord i)))
def B2P (i : Fin 5) : ℝ :=
  c2R ref * (2 * dot3 (castM (Dframe ref g)) (adj3 (castM (Ecoord i)))) +
    γ * (2 * dot3 (castM (Ecoord i)) (castM (Ecoord i)))

/-- The first derivative of `G` along coordinate `i` at `q`. -/
def F1 (i : Fin 5) (q : Fin 5 → ℝ) : ℝ :=
  G1F (fun _ => dS q) (fun _ => d1P i q) (fun _ => AP ref g γ q) (fun _ => A1P ref g i)
    (fun _ => BP ref g γ q) (fun _ => B1P ref g γ i q) 0

/-- The second derivative of `G` along coordinate `i` at `q`. -/
def F2 (i : Fin 5) (q : Fin 5 → ℝ) : ℝ :=
  G2F (fun _ => dS q) (fun _ => d1P i q) (fun _ => d2P i q) (fun _ => AP ref g γ q)
    (fun _ => A1P ref g i) (fun _ => BP ref g γ q) (fun _ => B1P ref g γ i q) (fun _ => B2P ref g γ i) 0

end Pointwise

theorem Gs_split (ref : Reference) (g : Aggregate) (γ : ℝ) (q : Fin 5 → ℝ) :
    Gs ref g γ q = lamS q * AP ref g γ q + lamS q ^ 2 * BP ref g γ q + 3 * γ := by
  unfold Gs AP BP c1R c2R
  ring

theorem lineDerivs (ref : Reference) (g : Aggregate) (γ : ℝ) (i : Fin 5) (p : Fin 5 → ℝ)
    (hpos : 0 < dS p) :
    HasDerivAt (fun t => Gs ref g γ (Function.update p i t)) (F1 ref g γ i p) (p i) ∧
      HasDerivAt (fun t => F1 ref g γ i (Function.update p i t)) (F2 ref g γ i p) (p i) := by
  set X := sJ p
  set E := castM (Ecoord i)
  have hJ (t : ℝ) : sJ (Function.update p i t) = X + (t - p i) • E := sJ_update p i t
  have hp : Function.update p i (p i) = p := Function.update_eq_self i p
  let d := fun t => dS (Function.update p i t)
  let d1 := fun t => d1P i (Function.update p i t)
  let d2 := fun t => d2P i (Function.update p i t)
  let A := fun t => AP ref g γ (Function.update p i t)
  let A1 := fun _ : ℝ => A1P ref g i
  let B := fun t => BP ref g γ (Function.update p i t)
  let B1 := fun t => B1P ref g γ i (Function.update p i t)
  let B2 := fun _ : ℝ => B2P ref g γ i
  have hd : HasDerivAt d (d1 (p i)) (p i) := by
    have e : d = fun t => det3 (X + (t - p i) • E) := by
      funext t
      simp only [d, dS, hJ]
    rw [e]
    have h := line_poly det3 X E (p i) _ _ _ _ (line_det X E)
    simpa [d1, d1P, hp] using h
  have hd1 : HasDerivAt d1 (d2 (p i)) (p i) := by
    have e : d1 = fun t => trm (adj3 (X + (t - p i) • E)) E := by
      funext t
      simp only [d1, d1P, hJ]; rfl
    rw [e]
    have h := line_poly (fun Y => trm (adj3 Y) E) X E (p i) _ _ _ _ (line_det1 X E)
    simpa [d2, d2P, hp] using h
  have hA : HasDerivAt A (A1 (p i)) (p i) := by
    have e : A = fun t => c1R ref * dot3 (castM (Pframe ref g)) (X + (t - p i) • E) - 6 * γ := by
      funext t
      simp only [A, AP, hJ]
    rw [e]
    have h := line_poly (fun Y => c1R ref * dot3 (castM (Pframe ref g)) Y - 6 * γ) X E (p i)
      (c1R ref * dot3 (castM (Pframe ref g)) X - 6 * γ) (c1R ref * dot3 (castM (Pframe ref g)) E) 0 0
      (fun u => by rw [line_dot]; ring)
    simpa [A1, A1P] using h
  have hA1 : HasDerivAt A1 0 (p i) := hasDerivAt_const _ _
  have hB : HasDerivAt B (B1 (p i)) (p i) := by
    have e : B = fun t => c2R ref * dot3 (castM (Dframe ref g)) (adj3 (X + (t - p i) • E)) +
        γ * dot3 (X + (t - p i) • E) (X + (t - p i) • E) := by
      funext t
      simp only [B, BP, hJ]
    rw [e]
    have h := line_poly (fun Y => c2R ref * dot3 (castM (Dframe ref g)) (adj3 Y) + γ * dot3 Y Y) X E (p i)
      (c2R ref * dot3 (castM (Dframe ref g)) (adj3 X) + γ * dot3 X X)
      (c2R ref * dot3 (castM (Dframe ref g)) (dadj3 X E) + γ * (2 * dot3 X E))
      (c2R ref * dot3 (castM (Dframe ref g)) (adj3 E) + γ * dot3 E E) 0
      (fun u => by rw [line_adj, line_frob]; ring)
    simpa [B1, B1P, hp] using h
  have hB1 : HasDerivAt B1 (B2 (p i)) (p i) := by
    have e : B1 = fun t => c2R ref * dot3 (castM (Dframe ref g)) (dadj3 (X + (t - p i) • E) E) +
        γ * (2 * dot3 (X + (t - p i) • E) E) := by
      funext t
      simp only [B1, B1P, hJ]; rfl
    rw [e]
    have h := line_poly (fun Y => c2R ref * dot3 (castM (Dframe ref g)) (dadj3 Y E) + γ * (2 * dot3 Y E))
      X E (p i)
      (c2R ref * dot3 (castM (Dframe ref g)) (dadj3 X E) + γ * (2 * dot3 X E))
      (c2R ref * (2 * dot3 (castM (Dframe ref g)) (adj3 E)) + γ * (2 * dot3 E E)) 0 0
      (fun u => by rw [line_dadj, line_frob1]; ring)
    simpa [B2, B2P] using h
  have hpos' : 0 < d (p i) := by simpa [d, hp] using hpos
  constructor
  · have e : (fun t => Gs ref g γ (Function.update p i t)) = G0F d A B (3 * γ) := by
      funext t
      rw [Gs_split]
      rfl
    rw [e]
    have h := G0F_deriv (3 * γ) hd hpos' hA hB
    convert h using 1
    simp only [F1, G1F, lam1F, lamF, d, d1, A, A1, B, B1, hp]
  · have e : (fun t => F1 ref g γ i (Function.update p i t)) = G1F d d1 A A1 B B1 := by
      funext t
      rfl
    rw [e]
    have h := G1F_deriv hd hd1 hpos' hA hA1 hB hB1
    convert h using 1
    simp only [F2, G2F, lam2F, lam1F, lamF, d, d1, d2, A, A1, B, B1, B2, hp]

/-! ## Maximum over a box: corners plus a curvature correction -/

theorem line_bound {f f1 f2 : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (h1 : ∀ t ∈ Set.Icc a b, HasDerivAt f (f1 t) t) (h2 : ∀ t ∈ Set.Icc a b, HasDerivAt f1 (f2 t) t)
    (lower : ∀ t ∈ Set.Icc a b, -M ≤ f2 t) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    f t ≤ max (f a) (f b) + M * (b - a) ^ 2 / 8 := by
  have hint : interior (Set.Icc a b) = Set.Ioo a b := interior_Icc
  have hq (x : ℝ) : HasDerivAt (fun y : ℝ => M / 2 * ((y - a) * (y - b))) (M / 2 * (2 * x - a - b)) x := by
    have h := (((hasDerivAt_id' x).sub_const a).mul ((hasDerivAt_id' x).sub_const b)).const_mul (M / 2)
    convert h using 1
    ring
  have hq' (x : ℝ) : HasDerivAt (fun y : ℝ => M / 2 * (2 * y - a - b)) M x := by
    have h := ((((hasDerivAt_id' x).const_mul 2).sub_const a).sub_const b).const_mul (M / 2)
    convert h using 1
    ring
  have cvx : ConvexOn ℝ (Set.Icc a b) (fun x => f x + M / 2 * ((x - a) * (x - b))) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
      (f' := fun x => f1 x + M / 2 * (2 * x - a - b)) (f'' := fun x => f2 x + M)
    · intro x hx
      exact ((h1 x hx).continuousAt.add (hq x).continuousAt).continuousWithinAt
    · intro x hx
      rw [hint] at hx
      exact ((h1 x (Set.Ioo_subset_Icc_self hx)).add (hq x)).hasDerivWithinAt
    · intro x hx
      rw [hint] at hx
      exact ((h2 x (Set.Ioo_subset_Icc_self hx)).add (hq' x)).hasDerivWithinAt
    · intro x hx
      rw [hint] at hx
      have := lower x (Set.Ioo_subset_Icc_self hx)
      linarith
  have seg : t ∈ _root_.segment ℝ a b := by
    rw [segment_eq_Icc hab]
    exact ht
  have hmax := cvx.le_on_segment (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) seg
  simp only [sub_self, zero_mul, mul_zero, add_zero] at hmax
  have hqb : -((t - a) * (t - b)) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * t - a - b)]
  nlinarith [mul_le_mul_of_nonneg_left hqb (by linarith : (0 : ℝ) ≤ M / 2)]

/-- Every point of a box is bounded by a corner value plus `Σ M_i d_i²/8`. -/
theorem box_bound (b : Rectangle) (F : (Fin 5 → ℝ) → ℝ) (F1' F2' : Fin 5 → (Fin 5 → ℝ) → ℝ)
    (M : Fin 5 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (d1 : ∀ i p, b.Mem p → HasDerivAt (fun t => F (Function.update p i t)) (F1' i p) (p i))
    (d2 : ∀ i p, b.Mem p → HasDerivAt (fun t => F1' i (Function.update p i t)) (F2' i p) (p i))
    (lower : ∀ i p, b.Mem p → -M i ≤ F2' i p)
    (p : Fin 5 → ℝ) (hp : b.Mem p) :
    ∃ c : Fin 5 → Bool, F p ≤ F (TangentE1.corner b c) + ∑ i, M i * ((b.hi i : ℝ) - b.lo i) ^ 2 / 8 := by
  classical
  let corr := fun k : ℕ => ∑ i : Fin 5, if i.val < k then M i * ((b.hi i : ℝ) - b.lo i) ^ 2 / 8 else 0
  let mix (c : Fin 5 → Bool) (k : ℕ) : Fin 5 → ℝ := fun i => if i.val < k then TangentE1.corner b c i else p i
  have side (i : Fin 5) : (b.lo i : ℝ) ≤ b.hi i := (hp i).1.trans (hp i).2
  have mem (c : Fin 5 → Bool) (k : ℕ) : b.Mem (mix c k) := by
    intro i
    simp only [mix, TangentE1.corner]
    split_ifs
    · exact ⟨side i, le_rfl⟩
    · exact ⟨le_rfl, side i⟩
    · exact hp i
  have step : ∀ k ≤ 5, ∃ c, F p ≤ F (mix c k) + corr k := by
    intro k hk
    induction k with
    | zero => exact ⟨fun _ => false, by simp [corr, mix]⟩
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih (by omega)
      let i : Fin 5 := ⟨k, by omega⟩
      have hq := mem c k
      have line_mem (t : ℝ) (ht : t ∈ Set.Icc (b.lo i : ℝ) (b.hi i)) :
          b.Mem (Function.update (mix c k) i t) := by
        intro j
        by_cases hj : j = i
        · subst hj
          simpa using ht
        · simpa [Function.update_of_ne hj] using hq j
      have hline := line_bound (f := fun t => F (Function.update (mix c k) i t))
        (f1 := fun t => F1' i (Function.update (mix c k) i t))
        (f2 := fun t => F2' i (Function.update (mix c k) i t)) (side i) (hM i)
        (fun t ht => by
          have h := d1 i _ (line_mem t ht)
          simp only [Function.update_idem, Function.update_self] at h
          exact h)
        (fun t ht => by
          have h := d2 i _ (line_mem t ht)
          simp only [Function.update_idem, Function.update_self] at h
          exact h)
        (fun t ht => lower i _ (line_mem t ht)) (mix c k i) (hq i)
      simp only [Function.update_eq_self] at hline
      have upd (v : Bool) : Function.update (mix c k) i (TangentE1.corner b (Function.update c i v) i) =
          mix (Function.update c i v) (k + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [mix, i]
        · have hjk : j.val ≠ k := fun e => hj (Fin.ext e)
          simp only [Function.update_of_ne hj, mix, TangentE1.corner]
          by_cases hlt : j.val < k
          · have : j.val < k + 1 := by omega
            simp [hlt, this]
          · have : ¬ j.val < k + 1 := by omega
            simp [hlt, this]
      have hcorr : corr (k + 1) = corr k + M i * ((b.hi i : ℝ) - b.lo i) ^ 2 / 8 := by
        simp only [corr]
        rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
        · simp [i]
        · intro j _ hj
          have hjk : j.val ≠ k := fun e => hj (Fin.ext e)
          by_cases hlt : j.val < k
          · simp [hlt, show j.val < k + 1 by omega]
          · simp [hlt, show ¬ j.val < k + 1 by omega]
        · simp
      by_cases hb : F (Function.update (mix c k) i (b.lo i)) ≤ F (Function.update (mix c k) i (b.hi i))
      · refine ⟨Function.update c i true, ?_⟩
        rw [hcorr, ← upd true]
        simp only [TangentE1.corner, Function.update_self, ite_true]
        rw [max_eq_right hb] at hline
        linarith
      · refine ⟨Function.update c i false, ?_⟩
        rw [hcorr, ← upd false]
        simp only [TangentE1.corner, Function.update_self]
        rw [max_eq_left (le_of_not_ge hb)] at hline
        simp only [Bool.false_eq_true, ite_false]
        linarith
  obtain ⟨c, hc⟩ := step 5 le_rfl
  refine ⟨c, ?_⟩
  have e1 : mix c 5 = TangentE1.corner b c := by
    funext i
    simp [mix, i.isLt]
  have e2 : corr 5 = ∑ i, M i * ((b.hi i : ℝ) - b.lo i) ^ 2 / 8 := by
    simp only [corr]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  rw [e1, e2] at hc
  exact hc

/-! ## Interval enclosures on an `s`-box -/

abbrev QM := Matrix (Fin 3) (Fin 3) QI

def QM.Mem (A : QM) (X : Mat) : Prop := ∀ i j, (A i j).Mem (X i j)

theorem QI.mem_congr {a : QI} {x y : ℝ} (h : a.Mem x) (e : x = y) : a.Mem y := e ▸ h

def sIv (sb : Rectangle) (i : Fin 5) : QI := ⟨sb.lo i, sb.hi i⟩

def boxJ (sb : Rectangle) : QM :=
  let s0 := sIv sb 0
  let s1 := sIv sb 1
  let s2 := sIv sb 2
  let s3 := sIv sb 3
  let s4 := sIv sb 4
  !![((QI.exact 1).add s0).add s1, s2, s3;
     s2, ((QI.exact 1).add s1).sub s0, s4;
     s3, s4, (QI.exact 1).sub (s1.scale 2)]

theorem boxJ_mem (sb : Rectangle) (q : Fin 5 → ℝ) (hq : sb.Mem q) : QM.Mem (boxJ sb) (sJ q) := by
  have hs (i : Fin 5) : (sIv sb i).Mem (q i) := hq i
  have one : (QI.exact 1).Mem (1 : ℝ) := by simpa using QI.mem_exact 1
  have e00 := QI.mem_add (QI.mem_add one (hs 0)) (hs 1)
  have e11 := QI.mem_sub (QI.mem_add one (hs 1)) (hs 0)
  have e22 := QI.mem_congr (QI.mem_sub one (QI.mem_scale 2 (hs 1))) (by push_cast; ring :
    (1 : ℝ) - ((2 : ℚ) : ℝ) * q 1 = 1 - 2 * q 1)
  intro i j
  fin_cases i <;> fin_cases j
  · exact e00
  · exact hs 2
  · exact hs 3
  · exact hs 2
  · exact e11
  · exact hs 4
  · exact hs 3
  · exact hs 4
  · exact e22

def adj3I (X : QM) : QM :=
  !![((X 1 1).mul (X 2 2)).sub ((X 1 2).mul (X 2 1)), ((X 0 2).mul (X 2 1)).sub ((X 0 1).mul (X 2 2)),
      ((X 0 1).mul (X 1 2)).sub ((X 0 2).mul (X 1 1));
     ((X 1 2).mul (X 2 0)).sub ((X 1 0).mul (X 2 2)), ((X 0 0).mul (X 2 2)).sub ((X 0 2).mul (X 2 0)),
      ((X 0 2).mul (X 1 0)).sub ((X 0 0).mul (X 1 2));
     ((X 1 0).mul (X 2 1)).sub ((X 1 1).mul (X 2 0)), ((X 0 1).mul (X 2 0)).sub ((X 0 0).mul (X 2 1)),
      ((X 0 0).mul (X 1 1)).sub ((X 0 1).mul (X 1 0))]

theorem adj3I_mem {X : QM} {Y : Mat} (h : QM.Mem X Y) : QM.Mem (adj3I X) (adj3 Y) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    exact QI.mem_sub (QI.mem_mul (h _ _) (h _ _)) (QI.mem_mul (h _ _) (h _ _))

def det3I (X A : QM) : QI :=
  (((X 0 0).mul (A 0 0)).add ((X 0 1).mul (A 1 0))).add ((X 0 2).mul (A 2 0))

theorem det3I_mem {X A : QM} {Y : Mat} (hX : QM.Mem X Y) (hA : QM.Mem A (adj3 Y)) :
    (det3I X A).Mem (det3 Y) :=
  QI.mem_add (QI.mem_add (QI.mem_mul (hX 0 0) (hA 0 0)) (QI.mem_mul (hX 0 1) (hA 1 0)))
    (QI.mem_mul (hX 0 2) (hA 2 0))

def rowI (P : Matrix (Fin 3) (Fin 3) ℚ) (X : QM) (i : Fin 3) : QI :=
  (((X i 0).scale (P i 0)).add ((X i 1).scale (P i 1))).add ((X i 2).scale (P i 2))

/-- `Σ_ij P_ij X_ij` for a rational `P`. -/
def dotI (P : Matrix (Fin 3) (Fin 3) ℚ) (X : QM) : QI :=
  ((rowI P X 0).add (rowI P X 1)).add (rowI P X 2)

theorem dotI_mem (P : Matrix (Fin 3) (Fin 3) ℚ) {X : QM} {Y : Mat} (h : QM.Mem X Y) :
    (dotI P X).Mem (dot3 (castM P) Y) := by
  have row (i : Fin 3) : (rowI P X i).Mem (∑ j, castM P i j * Y i j) := by
    rw [Fin.sum_univ_three]
    exact QI.mem_add (QI.mem_add (QI.mem_scale _ (h i 0)) (QI.mem_scale _ (h i 1)))
      (QI.mem_scale _ (h i 2))
  unfold dot3
  rw [Fin.sum_univ_three]
  exact QI.mem_add (QI.mem_add (row 0) (row 1)) (row 2)

def rowSqI (X : QM) (i : Fin 3) : QI := (((X i 0).sq).add ((X i 1).sq)).add ((X i 2).sq)

/-- `Σ_ij X_ij²`. -/
def dotSqI (X : QM) : QI := ((rowSqI X 0).add (rowSqI X 1)).add (rowSqI X 2)

theorem dotSqI_mem {X : QM} {Y : Mat} (h : QM.Mem X Y) : (dotSqI X).Mem (dot3 Y Y) := by
  have row (i : Fin 3) : (rowSqI X i).Mem (∑ j, Y i j * Y i j) := by
    rw [Fin.sum_univ_three]
    exact QI.mem_add (QI.mem_add (QI.mem_sq (h i 0)) (QI.mem_sq (h i 1))) (QI.mem_sq (h i 2))
  unfold dot3
  rw [Fin.sum_univ_three]
  exact QI.mem_add (QI.mem_add (row 0) (row 1)) (row 2)

/-! ## Explicit rational contractions -/

def dotQ (A X : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  A 0 0 * X 0 0 + A 0 1 * X 0 1 + A 0 2 * X 0 2 + (A 1 0 * X 1 0 + A 1 1 * X 1 1 + A 1 2 * X 1 2) +
    (A 2 0 * X 2 0 + A 2 1 * X 2 1 + A 2 2 * X 2 2)

theorem cast_dotQ (A X : Matrix (Fin 3) (Fin 3) ℚ) :
    ((dotQ A X : ℚ) : ℝ) = dot3 (castM A) (castM X) := by
  simp only [dotQ, dot3, castM, Fin.sum_univ_three]
  push_cast
  ring

/-! ## Cube-root brackets and constants -/

def icbrtLoop (N : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x =>
    let y := (2 * x + N / (x * x)) / 3
    if y < x then icbrtLoop N fuel y else x

/-- A proposed integer cube root (Newton from above); only its check matters. -/
def icbrt (N : ℕ) : ℕ := icbrtLoop N 100 (2 ^ 66)

/-- A proposed bracket `[m, m+1]/2^64` of `d^(-1/3)`. -/
def lamBracket (d : ℚ) : QI :=
  let m := icbrt ((2 ^ 192 * d.den) / d.num.toNat)
  ⟨(m : ℚ) / 2 ^ 64, ((m : ℚ) + 1) / 2 ^ 64⟩

/-- `L` brackets `d^(-1/3)` for every `d ∈ [dl, du]`. -/
def lamOK (dl du : ℚ) (L : QI) : Bool :=
  decide (0 < dl ∧ 0 ≤ L.lo ∧ L.lo ^ 3 * du ≤ 1 ∧ 1 ≤ L.hi ^ 3 * dl)

theorem lam_mem (dl du : ℚ) (L : QI) (ok : lamOK dl du L = true) (d : ℝ) (h1 : (dl : ℝ) ≤ d)
    (h2 : d ≤ du) : 0 < d ∧ L.Mem (d ^ (-(1/3 : ℝ))) := by
  obtain ⟨hdl, hlo, hl, hu⟩ := of_decide_eq_true ok
  have hdl' : (0 : ℝ) < dl := by exact_mod_cast hdl
  have hd : 0 < d := hdl'.trans_le h1
  have hlo' : (0 : ℝ) ≤ L.lo := by exact_mod_cast hlo
  have hl' : (L.lo : ℝ) ^ 3 * du ≤ 1 := by exact_mod_cast hl
  have hu' : 1 ≤ (L.hi : ℝ) ^ 3 * dl := by exact_mod_cast hu
  set x := d ^ (-(1/3 : ℝ)) with hx
  have xpos : 0 < x := Real.rpow_pos_of_pos hd _
  have cube : x ^ 3 * d = 1 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
    rw [Real.rpow_neg_one, inv_mul_cancel₀ hd.ne']
  refine ⟨hd, ?_, ?_⟩
  · apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) xpos.le
    have : (L.lo : ℝ) ^ 3 * d ≤ 1 :=
      (mul_le_mul_of_nonneg_left h2 (pow_nonneg hlo' 3)).trans hl'
    nlinarith
  · have hhi : 0 ≤ (L.hi : ℝ) := by
      by_contra hneg
      push Not at hneg
      have : (L.hi : ℝ) ^ 3 < 0 := by
        have h3 : (L.hi : ℝ) ^ 3 = -((-(L.hi : ℝ)) ^ 3) := by ring
        rw [h3]
        have : 0 < (-(L.hi : ℝ)) ^ 3 := pow_pos (by linarith) 3
        linarith
      nlinarith
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hhi
    have : 1 ≤ (L.hi : ℝ) ^ 3 * d :=
      hu'.trans (mul_le_mul_of_nonneg_left h1 (pow_nonneg hhi 3))
    nlinarith

def cbrt4Lo : ℚ := 29282380947994691627 / 2^64
def cbrt4Hi : ℚ := 29282380947994691628 / 2^64

theorem fccLength_sq_bounds : (cbrt4Lo : ℝ) ≤ Constants.fccLength ^ 2 ∧ Constants.fccLength ^ 2 ≤ cbrt4Hi := by
  have h6 : (Constants.fccLength ^ 2) ^ 3 = 4 := by
    have := referenceLength_cube
    calc (Constants.fccLength ^ 2) ^ 3 = (Constants.fccLength ^ 3) ^ 2 := by ring
      _ = 4 := by rw [this]; norm_num
  constructor
  · apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
    rw [h6]
    norm_num [cbrt4Lo]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by norm_num [cbrt4Hi])
    rw [h6]
    norm_num [cbrt4Hi]

def c1I : Reference → QI
  | .bcc => ⟨cbrt4Lo, cbrt4Hi⟩
  | .fcc => ⟨cbrt4Hi⁻¹, cbrt4Lo⁻¹⟩

def c2I : Reference → QI
  | .bcc => ⟨cbrt4Hi⁻¹, cbrt4Lo⁻¹⟩
  | .fcc => ⟨cbrt4Lo, cbrt4Hi⟩

theorem c_mem (ref : Reference) : (c1I ref).Mem (c1R ref) ∧ (c2I ref).Mem (c2R ref) := by
  obtain ⟨lo, hi⟩ := fccLength_sq_bounds
  have hl : (0 : ℝ) < cbrt4Lo := by norm_num [cbrt4Lo]
  have hpos : 0 < Constants.fccLength ^ 2 := by unfold Constants.fccLength; positivity
  have inv : ((cbrt4Hi⁻¹ : ℚ) : ℝ) ≤ (Constants.fccLength ^ 2)⁻¹ ∧ (Constants.fccLength ^ 2)⁻¹ ≤ ((cbrt4Lo⁻¹ : ℚ) : ℝ) := by
    push_cast
    exact ⟨inv_anti₀ hpos hi, inv_anti₀ hl lo⟩
  cases ref
  · exact ⟨⟨lo, hi⟩, by simpa [c2I, c2R, framePow, QI.Mem] using inv⟩
  · refine ⟨?_, ?_⟩
    · have e : c1R .fcc = (Constants.fccLength ^ 2)⁻¹ := by simp [c1R, framePow, inv_pow]
      rw [e]
      exact inv
    · have e : c2R .fcc = Constants.fccLength ^ 2 := by simp [c2R, framePow, inv_pow]
      rw [e]
      exact ⟨lo, hi⟩

/-! ## Direction data -/

/-- `tr (Y E_i)` from the entries of `Y` (each `E_i` is symmetric and sparse). -/
def d1I (i : Fin 5) (A : QM) : QI :=
  if i = 0 then (A 0 0).sub (A 1 1)
  else if i = 1 then ((A 0 0).add (A 1 1)).sub ((A 2 2).scale 2)
  else if i = 2 then (A 0 1).add (A 1 0)
  else if i = 3 then (A 0 2).add (A 2 0)
  else (A 1 2).add (A 2 1)

theorem d1I_mem (i : Fin 5) {A : QM} {Y : Mat} (h : QM.Mem A Y) :
    (d1I i A).Mem (trm Y (castM (Ecoord i))) := by
  fin_cases i
  · exact QI.mem_congr (QI.mem_sub (h 0 0) (h 1 1))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three]; ring)
  · exact QI.mem_congr (QI.mem_sub (QI.mem_add (h 0 0) (h 1 1)) (QI.mem_scale 2 (h 2 2)))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three]; ring)
  · exact QI.mem_congr (QI.mem_add (h 0 1) (h 1 0))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three])
  · exact QI.mem_congr (QI.mem_add (h 0 2) (h 2 0))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three])
  · exact QI.mem_congr (QI.mem_add (h 1 2) (h 2 1))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three])

/-- `2 tr (adj(E_i) Y)`. -/
def d2I (i : Fin 5) (J : QM) : QI :=
  if i = 0 then (J 2 2).scale (-2)
  else if i = 1 then (((J 0 0).scale (-4)).add ((J 1 1).scale (-4))).add ((J 2 2).scale 2)
  else if i = 2 then (J 2 2).scale (-2)
  else if i = 3 then (J 1 1).scale (-2)
  else (J 0 0).scale (-2)

theorem d2I_mem (i : Fin 5) {J : QM} {Y : Mat} (h : QM.Mem J Y) :
    (d2I i J).Mem (2 * trm (adj3 (castM (Ecoord i))) Y) := by
  fin_cases i
  · exact QI.mem_congr (QI.mem_scale (-2) (h 2 2))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])
  · exact QI.mem_congr (QI.mem_add (QI.mem_add (QI.mem_scale (-4) (h 0 0)) (QI.mem_scale (-4) (h 1 1)))
      (QI.mem_scale 2 (h 2 2))) (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three]; ring)
  · exact QI.mem_congr (QI.mem_scale (-2) (h 2 2))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])
  · exact QI.mem_congr (QI.mem_scale (-2) (h 1 1))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])
  · exact QI.mem_congr (QI.mem_scale (-2) (h 0 0))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])

/-- `⟨D, dadj(Y, E_i)⟩ = ⟨W_i D, Y⟩`. -/
def Wmat (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  if i = 0 then !![-D 2 2, 0, D 0 2; 0, D 2 2, -D 1 2; D 2 0, -D 2 1, -D 0 0 + D 1 1]
  else if i = 1 then
    !![-2 * D 1 1 + D 2 2, 2 * D 0 1, -D 0 2; 2 * D 1 0, -2 * D 0 0 + D 2 2, -D 1 2;
      -D 2 0, -D 2 1, D 0 0 + D 1 1]
  else if i = 2 then !![0, -D 2 2, D 1 2; -D 2 2, 0, D 0 2; D 2 1, D 2 0, -D 0 1 - D 1 0]
  else if i = 3 then !![0, D 2 1, -D 1 1; D 1 2, -D 0 2 - D 2 0, D 1 0; -D 1 1, D 0 1, 0]
  else !![-D 1 2 - D 2 1, D 0 2, D 0 1; D 2 0, 0, -D 0 0; D 1 0, -D 0 0, 0]

theorem Wmat_eq (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℚ) (Y : Mat) :
    dot3 (castM D) (dadj3 Y (castM (Ecoord i))) = dot3 (castM (Wmat i D)) Y := by
  fin_cases i <;> simp [dot3, dadj3, Wmat, Ecoord, castM, Fin.sum_univ_three] <;> ring

theorem dotE_trm (i : Fin 5) (Y : Mat) : dot3 Y (castM (Ecoord i)) = trm Y (castM (Ecoord i)) := by
  fin_cases i <;> simp [dot3, trm, Ecoord, castM, Fin.sum_univ_three]

/-- `⟨P, E_i⟩`. -/
def dirEQ (i : Fin 5) (P : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  if i = 0 then P 0 0 - P 1 1 else if i = 1 then P 0 0 + P 1 1 - 2 * P 2 2
  else if i = 2 then P 0 1 + P 1 0 else if i = 3 then P 0 2 + P 2 0 else P 1 2 + P 2 1

/-- `⟨D, adj E_i⟩`. -/
def adjEQ (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  if i = 0 then -D 2 2 else if i = 1 then -2 * D 0 0 - 2 * D 1 1 + D 2 2
  else if i = 2 then -D 2 2 else if i = 3 then -D 1 1 else -D 0 0

/-- `‖E_i‖²`. -/
def frobEQ (i : Fin 5) : ℚ := if i = 1 then 6 else 2

theorem dirEQ_eq (i : Fin 5) (P : Matrix (Fin 3) (Fin 3) ℚ) :
    dot3 (castM P) (castM (Ecoord i)) = ((dirEQ i P : ℚ) : ℝ) := by
  fin_cases i <;> simp [dot3, dirEQ, Ecoord, castM, Fin.sum_univ_three] <;> ring

theorem adjEQ_eq (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℚ) :
    dot3 (castM D) (adj3 (castM (Ecoord i))) = ((adjEQ i D : ℚ) : ℝ) := by
  fin_cases i <;> simp [dot3, adjEQ, adj3, Ecoord, castM, Fin.sum_univ_three]; ring

theorem frobEQ_eq (i : Fin 5) :
    dot3 (castM (Ecoord i)) (castM (Ecoord i)) = ((frobEQ i : ℚ) : ℝ) := by
  fin_cases i <;> simp [dot3, frobEQ, Ecoord, castM, Fin.sum_univ_three] <;> norm_num

/-! ## The second-derivative enclosure on a box -/

structure BoxData where
  J : QM
  A : QM
  d : QI
  lam : QI
  dinv : QI
  AI : QI
  BI : QI

/-- All direction-independent box data, evaluated once per leaf. -/
def boxData (ref : Reference) (P D : Matrix (Fin 3) (Fin 3) ℚ) (γ : ℚ) (sb : Rectangle) : BoxData :=
  let J := boxJ sb
  let A := adj3I J
  let d := det3I J A
  let AI := (((c1I ref).mul (dotI P J).round).sub (QI.exact (6 * γ))).round
  let BI := (((c2I ref).mul (dotI D A).round).add ((dotSqI J).round.scale γ)).round
  ⟨J, A, d, ⟨(lamBracket d.hi).lo, (lamBracket d.lo).hi⟩, d.inv.round, AI, BI⟩

def F2I (ref : Reference) (P D : Matrix (Fin 3) (Fin 3) ℚ) (γ : ℚ) (bd : BoxData) (i : Fin 5) : QI :=
  let ρ := ((d1I i bd.A).mul bd.dinv).round
  let σ := ((d2I i bd.J).mul bd.dinv).round
  let A1I := (c1I ref).scale (dirEQ i P)
  let B1I := (((c2I ref).mul (dotI (Wmat i D) bd.J)).add ((d1I i bd.J).scale (2 * γ))).round
  let B2I := ((c2I ref).scale (2 * adjEQ i D)).add (QI.exact (γ * (2 * frobEQ i)))
  let ρ2 := ρ.sq
  let t1 := (ρ2.scale (4/9)).sub (σ.scale (1/3))
  let t2 := (ρ2.scale (10/9)).sub (σ.scale (2/3))
  let in1 := ((t1.mul bd.AI).sub ((ρ.mul A1I).scale (2/3))).round
  let in2 := (((t2.mul bd.BI).sub ((ρ.mul B1I).scale (4/3))).add B2I).round
  (bd.lam.mul in1).add (bd.lam.sq.mul in2)

theorem trm_castM (Y : Mat) (E : Matrix (Fin 3) (Fin 3) ℚ) :
    trm Y (castM E) = dot3 (castM E.transpose) Y := by
  simp only [trm, dot3, castM, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

theorem dot3_comm (X Y : Mat) : dot3 X Y = dot3 Y X := by
  simp only [dot3, Fin.sum_univ_three]
  ring

theorem F2_formula (ref : Reference) (g : Aggregate) (γ : ℝ) (i : Fin 5) (q : Fin 5 → ℝ) (hd : 0 < dS q) :
    F2 ref g γ i q =
      lamS q * ((4/9 * ((d1P i q * (dS q)⁻¹) * (d1P i q * (dS q)⁻¹)) - 1/3 * (d2P i q * (dS q)⁻¹)) *
          AP ref g γ q - 2/3 * ((d1P i q * (dS q)⁻¹) * A1P ref g i)) +
        (lamS q * lamS q) * ((10/9 * ((d1P i q * (dS q)⁻¹) * (d1P i q * (dS q)⁻¹)) -
          2/3 * (d2P i q * (dS q)⁻¹)) * BP ref g γ q - 4/3 * ((d1P i q * (dS q)⁻¹) * B1P ref g γ i q) +
          B2P ref g γ i) := by
  have hl : lamF (fun _ => dS q) 0 = lamS q := rfl
  unfold F2 G2F lam2F lam1F
  rw [hl]
  field_simp
  ring

theorem box_lam (ref : Reference) (P D : Matrix (Fin 3) (Fin 3) ℚ) (γ : ℚ) (sb : Rectangle)
    (ok : lamOK (boxData ref P D γ sb).d.lo (boxData ref P D γ sb).d.hi (boxData ref P D γ sb).lam = true)
    (q : Fin 5 → ℝ) (hq : sb.Mem q) : 0 < dS q ∧ (boxData ref P D γ sb).lam.Mem (lamS q) := by
  have hJ := boxJ_mem sb q hq
  have hdet := det3I_mem hJ (adj3I_mem hJ)
  exact lam_mem _ _ _ ok (dS q) hdet.1 hdet.2

theorem F2I_mem (ref : Reference) (g : Aggregate) (γ : ℚ) (sb : Rectangle)
    (lamok : lamOK (boxData ref (Pframe ref g) (Dframe ref g) γ sb).d.lo
      (boxData ref (Pframe ref g) (Dframe ref g) γ sb).d.hi
      (boxData ref (Pframe ref g) (Dframe ref g) γ sb).lam = true)
    (i : Fin 5) (q : Fin 5 → ℝ) (hq : sb.Mem q) :
    0 < dS q ∧ (F2I ref (Pframe ref g) (Dframe ref g) γ (boxData ref (Pframe ref g) (Dframe ref g) γ sb) i).Mem
      (F2 ref g (γ : ℝ) i q) := by
  set bd := boxData ref (Pframe ref g) (Dframe ref g) γ sb with hbd
  have hJ : QM.Mem bd.J (sJ q) := boxJ_mem sb q hq
  have hA : QM.Mem bd.A (adj3 (sJ q)) := adj3I_mem hJ
  have hdet : bd.d.Mem (det3 (sJ q)) := det3I_mem hJ hA
  obtain ⟨dpos, hlam0⟩ := lam_mem _ _ _ lamok (dS q) hdet.1 hdet.2
  have hlam : bd.lam.Mem (lamS q) := hlam0
  have dlo : 0 < bd.d.lo := (of_decide_eq_true lamok).1
  refine ⟨dpos, ?_⟩
  have hdinv : bd.dinv.Mem (dS q)⁻¹ := QI.mem_round (QI.mem_inv dlo hdet)
  obtain ⟨c1m, c2m⟩ := c_mem ref
  have hd1 : (d1I i bd.A).Mem (d1P i q) := d1I_mem i hA
  have hd2 : (d2I i bd.J).Mem (d2P i q) := d2I_mem i hJ
  have hρ := QI.mem_round (QI.mem_mul hd1 hdinv)
  have hσ := QI.mem_round (QI.mem_mul hd2 hdinv)
  have hAI : bd.AI.Mem (AP ref g γ q) :=
    QI.mem_round (QI.mem_congr (QI.mem_sub (QI.mem_mul c1m (QI.mem_round (dotI_mem _ hJ))) (QI.mem_exact _))
      (by unfold AP; push_cast; ring))
  have hBI : bd.BI.Mem (BP ref g γ q) :=
    QI.mem_round (QI.mem_congr (QI.mem_add (QI.mem_mul c2m (QI.mem_round (dotI_mem _ hA)))
      (QI.mem_scale _ (QI.mem_round (dotSqI_mem hJ)))) (by unfold BP; ring))
  have hA1 : ((c1I ref).scale (dirEQ i (Pframe ref g))).Mem (A1P ref g i) :=
    QI.mem_congr (QI.mem_scale _ c1m) (by unfold A1P; rw [dirEQ_eq]; ring)
  have hB1 : ((((c2I ref).mul (dotI (Wmat i (Dframe ref g)) bd.J)).add
      ((d1I i bd.J).scale (2 * γ))).round).Mem (B1P ref g γ i q) :=
    QI.mem_round (QI.mem_congr (QI.mem_add (QI.mem_mul c2m (dotI_mem _ hJ))
      (QI.mem_scale _ (d1I_mem i hJ)))
      (by unfold B1P; rw [Wmat_eq, dotE_trm]; push_cast; ring))
  have hB2 : (((c2I ref).scale (2 * adjEQ i (Dframe ref g))).add
      (QI.exact (γ * (2 * frobEQ i)))).Mem (B2P ref g γ i) :=
    QI.mem_congr (QI.mem_add (QI.mem_scale _ c2m) (QI.mem_exact _))
      (by unfold B2P; push_cast; rw [adjEQ_eq, frobEQ_eq]; ring)
  have ht1 := QI.mem_sub (QI.mem_scale (4/9) (QI.mem_sq hρ)) (QI.mem_scale (1/3) hσ)
  have ht2 := QI.mem_sub (QI.mem_scale (10/9) (QI.mem_sq hρ)) (QI.mem_scale (2/3) hσ)
  have hin1 := QI.mem_round (QI.mem_sub (QI.mem_mul ht1 hAI) (QI.mem_scale (2/3) (QI.mem_mul hρ hA1)))
  have hin2 := QI.mem_round
    (QI.mem_add (QI.mem_sub (QI.mem_mul ht2 hBI) (QI.mem_scale (4/3) (QI.mem_mul hρ hB1))) hB2)
  rw [F2_formula ref g γ i q dpos]
  unfold F2I
  simp only
  refine QI.mem_congr (QI.mem_add (QI.mem_mul hlam hin1) (QI.mem_mul (QI.mem_sq hlam) hin2)) ?_
  push_cast
  ring

/-! ## Corners -/

def sJQ (s : Fin 5 → ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 + s 0 + s 1, s 2, s 3; s 2, 1 + s 1 - s 0, s 4; s 3, s 4, 1 - 2 * s 1]

theorem castM_sJQ (s : Fin 5 → ℚ) : castM (sJQ s) = sJ (fun i => (s i : ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [castM, sJQ, sJ]

/-- The corner `c` of an `s`-box, as a vector literal. -/
def cornerS (sb : Rectangle) (c : Fin 5 → Bool) : Fin 5 → ℚ :=
  ![if c 0 then sb.hi 0 else sb.lo 0, if c 1 then sb.hi 1 else sb.lo 1, if c 2 then sb.hi 2 else sb.lo 2,
    if c 3 then sb.hi 3 else sb.lo 3, if c 4 then sb.hi 4 else sb.lo 4]

theorem cornerS_eq (sb : Rectangle) (c : Fin 5 → Bool) : cornerS sb c = cornerQ sb c := by
  funext i
  fin_cases i <;> rfl

/-- An upper bound of `c x` for `c ∈ C`. -/
def upMul (C : QI) (x : ℚ) : ℚ := if 0 ≤ x then C.hi * x else C.lo * x

theorem upMul_sound {C : QI} {c : ℝ} (hc : C.Mem c) (x : ℚ) : c * x ≤ upMul C x := by
  unfold upMul
  split_ifs with hx
  · have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    push_cast
    exact mul_le_mul_of_nonneg_right hc.2 hx'
  · have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hx))
    push_cast
    exact mul_le_mul_of_nonpos_right hc.1 hx'

/-- `γ ‖J‖²` rounded up (skipped when `γ = 0`). -/
def gammaFrob (γ : ℚ) (J : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  if γ = 0 then 0 else γ * FixedLocal.dyadicCeil 64 (dotQ J J)

theorem gammaFrob_sound (γ : ℚ) (hγ : 0 ≤ γ) (J : Matrix (Fin 3) (Fin 3) ℚ) :
    (γ : ℝ) * dot3 (castM J) (castM J) ≤ gammaFrob γ J := by
  unfold gammaFrob
  split_ifs with h0
  · simp [h0]
  · have hγ' : (0 : ℝ) ≤ γ := by exact_mod_cast hγ
    push_cast
    apply mul_le_mul_of_nonneg_left _ hγ'
    rw [← cast_dotQ]
    exact_mod_cast FixedLocal.le_dyadicCeil 64 _

/-- An upper bound of `G` at the corner `c` of the `s`-box, with a checked bracket of `λ`.
For `γ ≥ 0`, `G` increases with `⟨P', J⟩`, `⟨D', adj J⟩` and `‖J‖²`, which are rounded up. -/
def cornerUpper (ref : Reference) (P D : Matrix (Fin 3) (Fin 3) ℚ) (γ : ℚ) (sb : Rectangle)
    (c : Fin 5 → Bool) : Option ℚ :=
  let J := sJQ (cornerS sb c)
  let A := adj3 J
  let d := J 0 0 * A 0 0 + J 0 1 * A 1 0 + J 0 2 * A 2 0
  let L := lamBracket d
  if lamOK d d L && decide (0 ≤ γ) then
    let α := FixedLocal.dyadicCeil 64 (dotQ P J)
    let β := FixedLocal.dyadicCeil 64 (dotQ D A)
    let Ah := upMul (c1I ref) α - 6 * γ
    let Bh := upMul (c2I ref) β + gammaFrob γ J
    some (upMul L Ah + upMul ⟨L.lo * L.lo, L.hi * L.hi⟩ Bh + 3 * γ)
  else none

theorem cornerUpper_sound (ref : Reference) (g : Aggregate) (γ : ℚ) (sb : Rectangle) (c : Fin 5 → Bool)
    (u : ℚ) (h : cornerUpper ref (Pframe ref g) (Dframe ref g) γ sb c = some u) :
    Gs ref g (γ : ℝ) (TangentE1.corner sb c) ≤ u := by
  unfold cornerUpper at h
  simp only at h
  split_ifs at h with hok
  obtain ⟨hlamok, hγq⟩ := Bool.and_eq_true_iff.mp hok
  have hγ : (0 : ℝ) ≤ γ := by exact_mod_cast of_decide_eq_true hγq
  have hu := Option.some.inj h
  set J := sJQ (cornerS sb c) with hJdef
  have hJ : sJ (TangentE1.corner sb c) = castM J := by
    rw [hJdef, cornerS_eq, ← cornerQ_cast, castM_sJQ]
  have hd : J 0 0 * adj3 J 0 0 + J 0 1 * adj3 J 1 0 + J 0 2 * adj3 J 2 0 = det3 J := rfl
  rw [hd] at hlamok hu
  have hdS : dS (TangentE1.corner sb c) = ((det3 J : ℚ) : ℝ) := by
    unfold dS
    rw [hJ, cast_det3]
  obtain ⟨_, hlam0⟩ := lam_mem _ _ _ hlamok (dS (TangentE1.corner sb c)) (le_of_eq hdS.symm)
    (le_of_eq hdS)
  set q := TangentE1.corner sb c with hq
  set L := lamBracket (det3 J) with hL
  have hlam : L.Mem (lamS q) := hlam0
  have hlpos : 0 ≤ lamS q := (Real.rpow_pos_of_pos (by rw [hdS]; exact_mod_cast
    (of_decide_eq_true hlamok).1) _).le
  have hlo : (0 : ℝ) ≤ L.lo := by exact_mod_cast (of_decide_eq_true hlamok).2.1
  have hlam2 : (⟨L.lo * L.lo, L.hi * L.hi⟩ : QI).Mem (lamS q ^ 2) := by
    constructor
    · push_cast
      nlinarith [hlam.1]
    · push_cast
      nlinarith [hlam.1, hlam.2]
  obtain ⟨c1m, c2m⟩ := c_mem ref
  have c1pos : 0 ≤ c1R ref := by unfold c1R; positivity
  have c2pos : 0 ≤ c2R ref := by unfold c2R; positivity
  have hα : dot3 (castM (Pframe ref g)) (sJ q) ≤ (FixedLocal.dyadicCeil 64 (dotQ (Pframe ref g) J) : ℝ) := by
    rw [hJ, ← cast_dotQ]
    exact_mod_cast FixedLocal.le_dyadicCeil 64 _
  have hβ : dot3 (castM (Dframe ref g)) (adj3 (sJ q)) ≤
      (FixedLocal.dyadicCeil 64 (dotQ (Dframe ref g) (adj3 J)) : ℝ) := by
    rw [hJ, ← castM_adj3, ← cast_dotQ]
    exact_mod_cast FixedLocal.le_dyadicCeil 64 _
  have hf : (γ : ℝ) * dot3 (sJ q) (sJ q) ≤ gammaFrob γ J := by
    rw [hJ]
    exact gammaFrob_sound γ (of_decide_eq_true hγq) J
  have hA : AP ref g γ q ≤ ((upMul (c1I ref) (FixedLocal.dyadicCeil 64 (dotQ (Pframe ref g) J)) -
      6 * γ : ℚ) : ℝ) := by
    unfold AP
    push_cast
    have := upMul_sound c1m (FixedLocal.dyadicCeil 64 (dotQ (Pframe ref g) J))
    nlinarith [mul_le_mul_of_nonneg_left hα c1pos]
  have hB : BP ref g γ q ≤ ((upMul (c2I ref) (FixedLocal.dyadicCeil 64 (dotQ (Dframe ref g) (adj3 J))) +
      gammaFrob γ J : ℚ) : ℝ) := by
    unfold BP
    push_cast
    have := upMul_sound c2m (FixedLocal.dyadicCeil 64 (dotQ (Dframe ref g) (adj3 J)))
    nlinarith [mul_le_mul_of_nonneg_left hβ c2pos]
  rw [Gs_split, ← hu]
  push_cast
  have t1 := (mul_le_mul_of_nonneg_left hA hlpos).trans (by
    have := upMul_sound hlam (upMul (c1I ref) (FixedLocal.dyadicCeil 64 (dotQ (Pframe ref g) J)) - 6 * γ)
    push_cast at this ⊢
    linarith)
  have t2 := (mul_le_mul_of_nonneg_left hB (pow_nonneg hlpos 2)).trans (by
    have := upMul_sound hlam2 (upMul (c2I ref) (FixedLocal.dyadicCeil 64 (dotQ (Dframe ref g) (adj3 J))) +
      gammaFrob γ J)
    push_cast at this ⊢
    linarith)
  linarith

/-! ## The strain leaf check -/

/-- E1 (`false`): above FCC. E2 (`true`, BCC only): above BCC by the defect bound. -/
def modeGamma (e2 : Bool) : ℚ := if e2 then gapFactorUpper * kappaUpper else 0
def modeTarget (e2 : Bool) : ℚ := if e2 then HbccUpper else HfccUpper

def corrTerm (ref : Reference) (P D : Matrix (Fin 3) (Fin 3) ℚ) (γ : ℚ) (sb : Rectangle) (bd : BoxData)
    (i : Fin 5) : ℚ :=
  max 0 (-(F2I ref P D γ bd i).lo) * (sb.hi i - sb.lo i) ^ 2 / 8

def corrOf (ref : Reference) (P D : Matrix (Fin 3) (Fin 3) ℚ) (γ : ℚ) (sb : Rectangle) (bd : BoxData) : ℚ :=
  corrTerm ref P D γ sb bd 0 + corrTerm ref P D γ sb bd 1 + corrTerm ref P D γ sb bd 2 +
    corrTerm ref P D γ sb bd 3 + corrTerm ref P D γ sb bd 4

/-- Balls containing the metric `λ J` on the box (for the spectral guard). -/
def cBalls (bd : BoxData) : MetricBalls := fun i j =>
  let c := bd.lam.mul (bd.J i j)
  ballOf c.lo c.hi

/-- The leaf check for a certified aggregate `g` on the `w`-box `b`. -/
def strainLeafCheck (ref : Reference) (e2 : Bool) (g : Aggregate) (b : Rectangle) : Bool :=
  let sb := sBox ref b
  let P := Pframe ref g
  let D := Dframe ref g
  let γ := modeGamma e2
  let bd := boxData ref P D γ sb
  let corr := corrOf ref P D γ sb bd
  (lamOK bd.d.lo bd.d.hi bd.lam &&
      (!e2 || (decide (ref = .bcc) && spectralCheck (cBalls bd) (automaticUpperPad (cBalls bd))))) &&
    allCorners fun c => match cornerUpper ref P D γ sb c with
      | some u => decide (modeTarget e2 < g.a - u - corr)
      | none => false

theorem strainLeafCheck_sound (ref : Reference) (e2 : Bool) (g : Aggregate) (hg : Certified g)
    (b : Rectangle) (ok : strainLeafCheck ref e2 g b = true) (w : Point) (hw : b.Mem w) :
    strainSharp ref w := by
  unfold strainLeafCheck at ok
  simp only at ok
  obtain ⟨⟨hlam, hmode⟩, hcorners⟩ := Bool.and_eq_true_iff.mp ok |>.imp_left Bool.and_eq_true_iff.mp
  set sb := sBox ref b with hsb
  set γ := modeGamma e2 with hγ
  set p := sOf ref w with hpdef
  set bd := boxData ref (Pframe ref g) (Dframe ref g) γ sb with hbd
  have hp : sb.Mem p := sBox_mem ref b w hw
  let M : Fin 5 → ℝ := fun i => ((max 0 (-(F2I ref (Pframe ref g) (Dframe ref g) γ bd i).lo) : ℚ) : ℝ)
  have hM (i : Fin 5) : 0 ≤ M i := by
    simp only [M]
    exact_mod_cast le_max_left _ _
  obtain ⟨c, hc⟩ := box_bound sb (Gs ref g γ) (F1 ref g γ) (F2 ref g γ) M hM
    (fun i q hq => (lineDerivs ref g γ i q (F2I_mem ref g γ sb hlam i q hq).1).1)
    (fun i q hq => (lineDerivs ref g γ i q (F2I_mem ref g γ sb hlam i q hq).1).2)
    (fun i q hq => by
      have h := (F2I_mem ref g γ sb hlam i q hq).2.1
      have : (-(max 0 (-(F2I ref (Pframe ref g) (Dframe ref g) γ bd i).lo)) : ℚ) ≤
          (F2I ref (Pframe ref g) (Dframe ref g) γ bd i).lo := by
        have := le_max_right (0 : ℚ) (-(F2I ref (Pframe ref g) (Dframe ref g) γ bd i).lo)
        linarith
      simp only [M]
      have h' : ((-(max 0 (-(F2I ref (Pframe ref g) (Dframe ref g) γ bd i).lo)) : ℚ) : ℝ) ≤
          ((F2I ref (Pframe ref g) (Dframe ref g) γ bd i).lo : ℝ) := by exact_mod_cast this
      push_cast at h' ⊢
      linarith)
    p hp
  have hcorner := allCorners_sound _ hcorners c
  cases hcu : cornerUpper ref (Pframe ref g) (Dframe ref g) γ sb c with
  | none => simp [hcu] at hcorner
  | some u =>
    simp only [hcu] at hcorner
    have ht : modeTarget e2 < g.a - u - corrOf ref (Pframe ref g) (Dframe ref g) γ sb bd :=
      of_decide_eq_true hcorner
    have hG := cornerUpper_sound ref g γ sb c u hcu
    have hcorr : ((corrOf ref (Pframe ref g) (Dframe ref g) γ sb bd : ℚ) : ℝ) =
        ∑ i, M i * ((sb.hi i : ℝ) - sb.lo i) ^ 2 / 8 := by
      simp only [corrOf, corrTerm, M, Fin.sum_univ_five]
      push_cast
      ring
    have htR : (modeTarget e2 : ℝ) < g.a - u - corrOf ref (Pframe ref g) (Dframe ref g) γ sb bd := by
      exact_mod_cast ht
    have bound : (modeTarget e2 : ℝ) < g.a - Gs ref g γ p := by
      rw [hcorr] at htR
      linarith
    intro A hA hGram
    obtain ⟨dpos, hlamp⟩ := box_lam ref (Pframe ref g) (Dframe ref g) γ sb hlam p hp
    have low := strain_lower ref g hg γ w dpos A hA hGram
    rw [← hpdef] at low
    have hvol : volumeOf (A * cubicBasis ref) = 1 := by
      unfold volumeOf
      rw [Matrix.det_mul, hA, one_mul]
      exact cubicBasis_unitVolume ref
    cases e2 with
    | false =>
      have hγ0 : (γ : ℝ) * frobSq (gram A - 1) = 0 := by simp [hγ, modeGamma]
      have ht0 : (modeTarget false : ℝ) = HfccUpper := by simp [modeTarget]
      rw [ht0] at bound
      exact unitVolume_above_fcc_of_series (A * cubicBasis ref) hvol (by linarith)
    | true =>
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hmode
      obtain ⟨href, hspec⟩ := hmode
      have href' : ref = .bcc := of_decide_eq_true href
      subst href'
      have hγ1 : (γ : ℝ) = gapFactorUpper * kappaUpper := by simp [hγ, modeGamma]
      have ht1 : (modeTarget true : ℝ) = HbccUpper := by simp [modeTarget]
      rw [ht1] at bound
      have hC : (cBalls bd).Contains (gram A) := by
        intro i j
        rw [hGram, metric_eq]
        have hJ := boxJ_mem sb p hp
        exact ballOf_sound (QI.mem_mul hlamp (hJ i j))
      have hdet : (A * cubicBasis .bcc).det = 1 := by rw [Matrix.det_mul, hA, bccCubic_det, one_mul]
      have upper := defectPointwiseUpper_sound (Constants.fccLength⁻¹ • (A * cubicBasis .bcc)) A
        (by rw [hA]; norm_num) (bcc_strain_points A) (cBalls bd) hC _ hspec
      apply strict_e2_from_same_point (A * cubicBasis .bcc) hdet ((kappaUpper : ℝ) * frobSq (gram A - 1)) upper
      have e : (γ : ℝ) * frobSq (gram A - 1) = gapFactorUpper * (kappaUpper * frobSq (gram A - 1)) := by
        rw [hγ1]
        ring
      linarith

end BccSharp.Coulomb.BravaisCover.StrainTangent
