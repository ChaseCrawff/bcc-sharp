import BccSharp.Cover.JLeafCore

set_option autoImplicit false

/-! Identities, separate convexity and feature aggregation for the J-leaf
evaluator, in the original (unsquared) chart coordinates.

* `primalQ`, `dualQ` and `phaseT` equal the quadratic forms and phases used by
  the series (`termQ_cross`, `termQ_period`, `termQ_wave`, `phaseT_eq`).
* Every squared length is separately convex on a box with positive diagonal
  lower endpoints (`primalQ_chord`, `dualQ_chord`), the phase is affine along
  every axis, and a list of terms with nonpositive slopes is separately concave
  (`linSum_chord`).
* The JointDeficit registered cost is separately convex when
  `4 (r₁⁺ r₂⁺)² ≤ 9 |row₃ B⁻¹|²` and the rows of `U` are unit vectors
  (`regCost_chord`). Along a diagonal coordinate, the third strain row is
  `α/r² - 2β/r + γ`, which is convex on `(0, M]` whenever `2βM ≤ 3α`.
* Each squared length and phase is a rational linear form in the 19 features
  (`termQ_feat`, `phaseT_feat`), so a term list collapses to one constant and
  19 weights (`linSum_feat`). Corner values are rational evaluations
  (`featGen_cast`, `regCostQ_cast`, `cornerRat_cast`). -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.DirectRoute (offset pairedTerm affineSq_chord)

private theorem offset_zero : offset 0 = 5 := rfl
private theorem offset_one : offset 1 = 6 := rfl
private theorem offset_two : offset 2 = 7 := rfl

/-! ### Identities with the Series quadratic forms -/

theorem primalQ_eq (v : Fin 3 → ℚ) (s : Bool) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    primalQ v s p = sq ((chartBasis p).mulVec (fun i => img v s p i)) := by
  simp [primalQ, rowA, rowB, rowC, sq, chartBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  field_simp

private theorem img_cross (n : IntVec) (p : Chart) :
    (fun i => img (intVec n) true p i) = castVec n + (chartPoint p).offset := by
  funext i
  simp [img, intVec, castVec, DirectRoute.offset_eq]

private theorem img_period (n : IntVec) (p : Chart) :
    (fun i => img (intVec n) false p i) = castVec n := by
  funext i
  simp [img, intVec, castVec]

theorem termQ_cross (n : IntVec) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    termQ .cross n p = quad (gram (chartPoint p).basis) (castVec n + (chartPoint p).offset) := by
  show primalQ (intVec n) true p = quad (gram (chartBasis p)) (castVec n + (chartPoint p).offset)
  rw [← img_cross, ← sq_mulVec_gram]
  exact primalQ_eq _ _ _ h0 h1

theorem termQ_period (n : IntVec) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    termQ .period n p = quad (gram (chartPoint p).basis) (castVec n) := by
  show primalQ (intVec n) false p = quad (gram (chartBasis p)) (castVec n)
  rw [← img_period, ← sq_mulVec_gram]
  exact primalQ_eq _ _ _ h0 h1

theorem dualQ_eq_radial (m : IntVec) (p : Chart) :
    dualQ m p = Stage2.dualRadial m (DirectRoute.squarePoint p) := by
  simp only [dualQ, dualB, dualC, Stage2.dualRadial, Stage2.dualB, Stage2.dualC, DirectRoute.squarePoint]
  norm_num

theorem termQ_wave (n : IntVec) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    termQ .wave n p = quad (gram (chartPoint p).basis)⁻¹ (castVec n) := by
  show dualQ n p = quad (gram (chartBasis p))⁻¹ (castVec n)
  rw [dualQ_eq_radial]
  exact Stage2.dualRadial_eq n p h0 h1

theorem phaseT_eq (n : IntVec) (p : Chart) : phaseT n p = dot (castVec n) (chartPoint p).offset := by
  simp [phaseT, dot, castVec, DirectRoute.offset_eq]

/-! ### Convexity along a segment -/

/-- Convexity of a scalar function along the segment `[lo, hi]`, in chord form. -/
def LineConvex (φ : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → φ ((1 - t) * lo + t * hi) ≤ (1 - t) * φ lo + t * φ hi

theorem LineConvex.congr {φ ψ : ℝ → ℝ} {lo hi : ℝ} (h : ∀ a, φ a = ψ a)
    (hψ : LineConvex ψ lo hi) : LineConvex φ lo hi := by
  intro t t0 t1
  rw [h, h, h]
  exact hψ t t0 t1

theorem LineConvex.add {φ ψ : ℝ → ℝ} {lo hi : ℝ} (hφ : LineConvex φ lo hi)
    (hψ : LineConvex ψ lo hi) : LineConvex (fun a => φ a + ψ a) lo hi := by
  intro t t0 t1
  have a := hφ t t0 t1
  have c := hψ t t0 t1
  show φ _ + ψ _ ≤ (1 - t) * (φ lo + ψ lo) + t * (φ hi + ψ hi)
  linarith

theorem LineConvex.smul {φ : ℝ → ℝ} {lo hi c : ℝ} (hc : 0 ≤ c) (hφ : LineConvex φ lo hi) :
    LineConvex (fun a => c * φ a) lo hi := by
  intro t t0 t1
  have a := mul_le_mul_of_nonneg_left (hφ t t0 t1) hc
  show c * φ _ ≤ (1 - t) * (c * φ lo) + t * (c * φ hi)
  calc c * φ ((1 - t) * lo + t * hi) ≤ c * ((1 - t) * φ lo + t * φ hi) := a
    _ = (1 - t) * (c * φ lo) + t * (c * φ hi) := by ring

theorem LineConvex.const (c lo hi : ℝ) : LineConvex (fun _ => c) lo hi := by
  intro t _ _
  show c ≤ (1 - t) * c + t * c
  linarith

theorem LineConvex.sqAffine (A B lo hi : ℝ) : LineConvex (fun a => (A + B * a) ^ 2) lo hi := by
  intro t t0 t1
  have h := affineSq_chord (A + B * lo) (A + B * hi) t t0 t1
  have e : A + B * ((1 - t) * lo + t * hi) = (1 - t) * (A + B * lo) + t * (A + B * hi) := by ring
  show (A + B * ((1 - t) * lo + t * hi)) ^ 2 ≤ (1 - t) * (A + B * lo) ^ 2 + t * (A + B * hi) ^ 2
  rw [e]
  exact h

theorem LineConvex.sum {ι : Type} (s : Finset ι) (φ : ι → ℝ → ℝ) {lo hi : ℝ}
    (h : ∀ j ∈ s, LineConvex (φ j) lo hi) : LineConvex (fun a => ∑ j ∈ s, φ j a) lo hi := by
  classical
  induction s using Finset.induction_on with
  | empty => exact LineConvex.congr (fun a => by simp) (LineConvex.const 0 lo hi)
  | @insert j s hj ih =>
    have hs := (h j (Finset.mem_insert_self j s)).add
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))
    exact LineConvex.congr (fun a => Finset.sum_insert hj) hs

private theorem recip_remainder (α β x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    α / y ^ 2 - 2 * β / y - (α / x ^ 2 - 2 * β / x) - (-2 * α / x ^ 3 + 2 * β / x ^ 2) * (y - x) =
      (y - x) ^ 2 * (α * (2 * y + x) - 2 * β * x * y) / (x ^ 3 * y ^ 2) := by
  field_simp
  ring

/-- `α/a² - 2β/a` is convex on `[lo, hi] ⊂ (0, ∞)` when `2β·hi ≤ 3α`. -/
theorem LineConvex.recip (α β lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hα : 0 ≤ α)
    (hβ : 2 * β * hi ≤ 3 * α) : LineConvex (fun a => α / a ^ 2 - 2 * β / a) lo hi := by
  intro t t0 t1
  show α / ((1 - t) * lo + t * hi) ^ 2 - 2 * β / ((1 - t) * lo + t * hi) ≤
    (1 - t) * (α / lo ^ 2 - 2 * β / lo) + t * (α / hi ^ 2 - 2 * β / hi)
  have hhi : 0 < hi := hlo.trans_le hle
  have hxlo : lo ≤ (1 - t) * lo + t * hi := by nlinarith
  have hxhi : (1 - t) * lo + t * hi ≤ hi := by nlinarith
  set x := (1 - t) * lo + t * hi with hxdef
  have hx : 0 < x := hlo.trans_le hxlo
  have key (y : ℝ) (hy : 0 < y) (hyh : y ≤ hi) : 0 ≤ α * (2 * y + x) - 2 * β * x * y := by
    have g : 0 ≤ (2 * y + x) * hi - 3 * x * y := by
      rcases le_total x y with hxy | hxy
      · nlinarith [mul_le_mul_of_nonneg_left hyh hx.le]
      · nlinarith [mul_le_mul_of_nonneg_left hxhi hy.le]
    have hxy := mul_pos hx hy
    rcases le_or_gt β 0 with hb | hb
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) hxy.le, mul_nonneg hα (by linarith : 0 ≤ 2 * y + x)]
    · have h1 : 2 * β * x * y * hi ≤ 3 * α * x * y := by
        have := mul_le_mul_of_nonneg_right hβ hxy.le
        nlinarith
      have h2 : 3 * α * x * y ≤ α * ((2 * y + x) * hi) := by
        have := mul_le_mul_of_nonneg_left g hα
        nlinarith
      have h3 : (2 * β * x * y) * hi ≤ (α * (2 * y + x)) * hi := by nlinarith
      have h4 := le_of_mul_le_mul_right h3 hhi
      linarith
  have r0 := recip_remainder α β x lo hx hlo
  have r1 := recip_remainder α β x hi hx hhi
  have n0 : 0 ≤ (lo - x) ^ 2 * (α * (2 * lo + x) - 2 * β * x * lo) / (x ^ 3 * lo ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (key lo hlo hle)) (mul_pos (pow_pos hx 3) (pow_pos hlo 2)).le
  have n1 : 0 ≤ (hi - x) ^ 2 * (α * (2 * hi + x) - 2 * β * x * hi) / (x ^ 3 * hi ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (key hi hhi le_rfl)) (mul_pos (pow_pos hx 3) (pow_pos hhi 2)).le
  have lin : (1 - t) * (lo - x) + t * (hi - x) = 0 := by rw [hxdef]; ring
  have e : (1 - t) * (α / lo ^ 2 - 2 * β / lo) + t * (α / hi ^ 2 - 2 * β / hi) - (α / x ^ 2 - 2 * β / x) =
      (1 - t) * ((lo - x) ^ 2 * (α * (2 * lo + x) - 2 * β * x * lo) / (x ^ 3 * lo ^ 2)) +
      t * ((hi - x) ^ 2 * (α * (2 * hi + x) - 2 * β * x * hi) / (x ^ 3 * hi ^ 2)) +
      (-2 * α / x ^ 3 + 2 * β / x ^ 2) * ((1 - t) * (lo - x) + t * (hi - x)) := by
    rw [← r0, ← r1]
    ring
  rw [lin, mul_zero, add_zero] at e
  have s := add_nonneg (mul_nonneg (sub_nonneg.mpr t1) n0) (mul_nonneg t0 n1)
  linarith

theorem LineConvex.invSq (α lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hα : 0 ≤ α) :
    LineConvex (fun a => α / a ^ 2) lo hi :=
  LineConvex.congr (fun a => by ring)
    (LineConvex.recip α 0 lo hi hlo hle hα (by linarith))

theorem LineConvex.sq (c lo hi : ℝ) (hc : 0 ≤ c) : LineConvex (fun a => c * a ^ 2) lo hi :=
  LineConvex.congr (fun a => by ring) (LineConvex.smul hc (LineConvex.sqAffine 0 1 lo hi))

/-! ### From lines to chords on a box -/

theorem chordLower_congr {b : Cell} {F G : Chart → ℝ} (h : ∀ p, F p = G p)
    (hG : ChordLower b G) : ChordLower b F := by
  intro p hp i t t0 t1 e
  have := hG p hp i t t0 t1 e
  rw [h, h, h]
  exact this

theorem chordUpper_congr {b : Cell} {F G : Chart → ℝ} (h : ∀ p, F p = G p)
    (hG : ChordUpper b G) : ChordUpper b F :=
  chordLower_congr (fun p => by simp only [h p]) hG

theorem chordLower_add {b : Cell} {f g : Chart → ℝ} (hf : ChordLower b f) (hg : ChordLower b g) :
    ChordLower b (fun p => f p + g p) := by
  intro p hp i t t0 t1 e
  have a := hf p hp i t t0 t1 e
  have c := hg p hp i t t0 t1 e
  show (1 - t) * (f _ + g _) + t * (f _ + g _) ≤ f p + g p
  linarith

theorem chordLower_smul {b : Cell} {f : Chart → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : ChordLower b f) :
    ChordLower b (fun p => c * f p) := by
  intro p hp i t t0 t1 e
  have a := mul_le_mul_of_nonneg_left (hf p hp i t t0 t1 e) hc
  show (1 - t) * (c * f _) + t * (c * f _) ≤ c * f p
  calc (1 - t) * (c * f (atLower b p i)) + t * (c * f (atUpper b p i)) =
      c * ((1 - t) * f (atLower b p i) + t * f (atUpper b p i)) := by ring
    _ ≤ c * f p := a

theorem chordLower_const (b : Cell) (c : ℝ) : ChordLower b (fun _ => c) := by
  intro p hp i t t0 t1 e
  show (1 - t) * c + t * c ≤ c
  linarith

theorem chordUpper_add {b : Cell} {f g : Chart → ℝ} (hf : ChordUpper b f) (hg : ChordUpper b g) :
    ChordUpper b (fun p => f p + g p) :=
  chordLower_congr (fun p => by ring) (chordLower_add hf hg)

theorem chordUpper_smul {b : Cell} {f : Chart → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : ChordUpper b f) :
    ChordUpper b (fun p => c * f p) :=
  chordLower_congr (fun p => by ring) (chordLower_smul hc hf)

/-- A nonpositive multiple of a separately convex function is separately concave. -/
theorem chordLower_negSmul {b : Cell} {f : Chart → ℝ} {c : ℝ} (hc : c ≤ 0) (hf : ChordUpper b f) :
    ChordLower b (fun p => c * f p) :=
  chordLower_congr (fun p => by ring) (chordLower_smul (neg_nonneg.mpr hc) hf)

theorem chordUpper_of_line (b : Cell) (F : Chart → ℝ)
    (h : ∀ p, b.Mem p → ∀ i : Axis,
      LineConvex (fun a => F (Function.update p i a)) (b.lo i) (b.hi i)) :
    ChordUpper b F := by
  intro p hp i t t0 t1 e
  have hl := h p hp i t t0 t1
  have self : Function.update p i ((1 - t) * (b.lo i : ℝ) + t * (b.hi i : ℝ)) = p := by
    rw [← e, Function.update_eq_self]
  simp only [self] at hl
  show (1 - t) * (-F (atLower b p i)) + t * (-F (atUpper b p i)) ≤ -F p
  simp only [atLower, atUpper]
  linarith

/-- A function that is affine along every axis is both separately convex and
separately concave. -/
theorem chord_of_affine (b : Cell) (F : Chart → ℝ)
    (h : ∀ p (i : Axis), ∃ c d : ℝ, ∀ a, F (Function.update p i a) = c + d * a) :
    ChordLower b F ∧ ChordUpper b F := by
  have eq : ∀ p, b.Mem p → ∀ (i : Axis) (t : ℝ), p i = (1 - t) * (b.lo i : ℝ) + t * (b.hi i : ℝ) →
      (1 - t) * F (atLower b p i) + t * F (atUpper b p i) = F p := by
    intro p _ i t e
    obtain ⟨c, d, hcd⟩ := h p i
    have self : F p = c + d * p i := by
      have := hcd (p i)
      rwa [Function.update_eq_self] at this
    simp only [atLower, atUpper, hcd, self, e]
    ring
  constructor
  · intro p hp i t _ _ e
    exact (eq p hp i t e).le
  · intro p hp i t _ _ e
    have := eq p hp i t e
    show (1 - t) * (-F (atLower b p i)) + t * (-F (atUpper b p i)) ≤ -F p
    linarith

/-! ### Affine dependence on each coordinate -/

private theorem axis_cases (i : Axis) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
  fin_cases i <;> simp

theorem rowA_affine (v : Fin 3 → ℚ) (s : Bool) (p : Chart) (i : Axis) :
    ∃ c d : ℝ, ∀ a, rowA v s (Function.update p i a) = c + d * a := by
  refine ⟨rowA v s (Function.update p i 0),
    rowA v s (Function.update p i 1) - rowA v s (Function.update p i 0), fun a => ?_⟩
  rcases axis_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases s <;>
    simp only [rowA, img, offset_zero, offset_one, offset_two, Function.update_apply,
      Fin.reduceEq, ↓reduceIte, Bool.false_eq_true] <;> ring

theorem rowB_affine (v : Fin 3 → ℚ) (s : Bool) (p : Chart) (i : Axis) :
    ∃ c d : ℝ, ∀ a, rowB v s (Function.update p i a) = c + d * a := by
  refine ⟨rowB v s (Function.update p i 0),
    rowB v s (Function.update p i 1) - rowB v s (Function.update p i 0), fun a => ?_⟩
  rcases axis_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases s <;>
    simp only [rowB, img, offset_one, offset_two, Function.update_apply,
      Fin.reduceEq, ↓reduceIte, Bool.false_eq_true] <;> ring

theorem rowC_affine (v : Fin 3 → ℚ) (s : Bool) (p : Chart) (i : Axis) :
    ∃ c d : ℝ, ∀ a, rowC v s (Function.update p i a) = c + d * a := by
  refine ⟨rowC v s (Function.update p i 0),
    rowC v s (Function.update p i 1) - rowC v s (Function.update p i 0), fun a => ?_⟩
  rcases axis_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases s <;>
    simp only [rowC, img, offset_two, Function.update_apply,
      Fin.reduceEq, ↓reduceIte, Bool.false_eq_true] <;> ring

theorem dualB_affine (m : IntVec) (p : Chart) (i : Axis) :
    ∃ c d : ℝ, ∀ a, dualB m (Function.update p i a) = c + d * a := by
  refine ⟨dualB m (Function.update p i 0),
    dualB m (Function.update p i 1) - dualB m (Function.update p i 0), fun a => ?_⟩
  rcases axis_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dualB, Function.update_apply, Fin.reduceEq, ↓reduceIte] <;> ring

theorem dualC_affine (m : IntVec) (p : Chart) (i : Axis) :
    ∃ c d : ℝ, ∀ a, dualC m (Function.update p i a) = c + d * a := by
  refine ⟨dualC m (Function.update p i 0),
    dualC m (Function.update p i 1) - dualC m (Function.update p i 0), fun a => ?_⟩
  rcases axis_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dualC, Function.update_apply, Fin.reduceEq, ↓reduceIte] <;> ring

theorem phaseT_affine (m : IntVec) (p : Chart) (i : Axis) :
    ∃ c d : ℝ, ∀ a, phaseT m (Function.update p i a) = c + d * a := by
  refine ⟨phaseT m (Function.update p i 0),
    phaseT m (Function.update p i 1) - phaseT m (Function.update p i 0), fun a => ?_⟩
  rcases axis_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [phaseT, Fin.sum_univ_three, offset_zero, offset_one, offset_two,
      Function.update_apply, Fin.reduceEq, ↓reduceIte] <;> ring

theorem strainEntry_affine (N : Fin 3 → Fin 3 → ℚ) (p : Chart) (k : Axis) (i j : Fin 3)
    (h : i ≠ 2 ∨ (k ≠ 0 ∧ k ≠ 1)) :
    ∃ c d : ℝ, ∀ a, strainEntry N (Function.update p k a) i j = c + d * a := by
  refine ⟨strainEntry N (Function.update p k 0) i j,
    strainEntry N (Function.update p k 1) i j - strainEntry N (Function.update p k 0) i j,
    fun a => ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · rcases axis_cases k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [strainEntry, Function.update_apply, Fin.reduceEq, ↓reduceIte] <;> ring
  · rcases axis_cases k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [strainEntry, Function.update_apply, Fin.reduceEq, ↓reduceIte] <;> ring
  · rcases h with h | ⟨k0, k1⟩
    · exact absurd rfl h
    · have u0 : ∀ a : ℝ, Function.update p k a 0 = p 0 :=
        fun a => Function.update_of_ne (Ne.symm k0) _ _
      have u1 : ∀ a : ℝ, Function.update p k a 1 = p 1 :=
        fun a => Function.update_of_ne (Ne.symm k1) _ _
      simp only [strainEntry, Fin.reduceEq, ↓reduceIte, u0, u1]
      ring

/-! ### Separate convexity of the squared lengths -/

private theorem box_facts {b : Cell} {p : Chart} (hp : b.Mem p) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) :
    0 < p 0 ∧ 0 < p 1 ∧ (b.lo 0 : ℝ) ≤ b.hi 0 ∧ (b.lo 1 : ℝ) ≤ b.hi 1 ∧
      p 0 ≤ b.hi 0 ∧ p 1 ≤ b.hi 1 :=
  ⟨h0.trans_le (hp 0).1, h1.trans_le (hp 1).1, (hp 0).1.trans (hp 0).2,
    (hp 1).1.trans (hp 1).2, (hp 0).2, (hp 1).2⟩

private theorem upd_ne (p : Chart) (k j : Axis) (h : j ≠ k) (a : ℝ) :
    Function.update p k a j = p j := Function.update_of_ne h _ _

theorem primalQ_chord (v : Fin 3 → ℚ) (s : Bool) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) : ChordUpper b (primalQ v s) := by
  apply chordUpper_of_line
  intro p hp i
  obtain ⟨p0, p1, le0, le1, _, _⟩ := box_facts hp h0 h1
  by_cases i0 : i = 0
  · subst i0
    have rA : ∀ a : ℝ, rowA v s (Function.update p 0 a) = rowA v s p := by
      intro a
      cases s <;> simp only [rowA, img, offset_zero, offset_one, offset_two,
        Function.update_apply, Fin.reduceEq, ↓reduceIte, Bool.false_eq_true]
    have rB : ∀ a : ℝ, rowB v s (Function.update p 0 a) = rowB v s p := by
      intro a
      cases s <;> simp only [rowB, img, offset_one, offset_two,
        Function.update_apply, Fin.reduceEq, ↓reduceIte, Bool.false_eq_true]
    have rC : ∀ a : ℝ, rowC v s (Function.update p 0 a) = rowC v s p := by
      intro a
      cases s <;> simp only [rowC, img, offset_two,
        Function.update_apply, Fin.reduceEq, ↓reduceIte, Bool.false_eq_true]
    have q1 : ∀ a : ℝ, Function.update p 0 a 1 = p 1 := upd_ne p 0 1 (by decide)
    refine LineConvex.congr (ψ := fun a => (rowA v s p) ^ 2 * a ^ 2 +
        ((rowC v s p) ^ 2 / (p 1) ^ 2) / a ^ 2 + (p 1) ^ 2 * (rowB v s p) ^ 2) ?_ ?_
    · intro a
      simp only [primalQ, rA, rB, rC, q1, Function.update_self]
      ring
    · exact ((LineConvex.sq _ _ _ (sq_nonneg _)).add
        (LineConvex.invSq _ _ _ h0 le0 (div_nonneg (sq_nonneg _) (sq_nonneg _)))).add
        (LineConvex.const _ _ _)
  by_cases i1 : i = 1
  · subst i1
    have rA : ∀ a : ℝ, rowA v s (Function.update p 1 a) = rowA v s p := by
      intro a
      cases s <;> simp only [rowA, img, offset_zero, offset_one, offset_two,
        Function.update_apply, Fin.reduceEq, ↓reduceIte, Bool.false_eq_true]
    have rB : ∀ a : ℝ, rowB v s (Function.update p 1 a) = rowB v s p := by
      intro a
      cases s <;> simp only [rowB, img, offset_one, offset_two,
        Function.update_apply, Fin.reduceEq, ↓reduceIte, Bool.false_eq_true]
    have rC : ∀ a : ℝ, rowC v s (Function.update p 1 a) = rowC v s p := by
      intro a
      cases s <;> simp only [rowC, img, offset_two,
        Function.update_apply, Fin.reduceEq, ↓reduceIte, Bool.false_eq_true]
    have q0 : ∀ a : ℝ, Function.update p 1 a 0 = p 0 := upd_ne p 1 0 (by decide)
    refine LineConvex.congr (ψ := fun a => (rowB v s p) ^ 2 * a ^ 2 +
        ((rowC v s p) ^ 2 / (p 0) ^ 2) / a ^ 2 + (p 0) ^ 2 * (rowA v s p) ^ 2) ?_ ?_
    · intro a
      simp only [primalQ, rA, rB, rC, q0, Function.update_self]
      ring
    · exact ((LineConvex.sq _ _ _ (sq_nonneg _)).add
        (LineConvex.invSq _ _ _ h1 le1 (div_nonneg (sq_nonneg _) (sq_nonneg _)))).add
        (LineConvex.const _ _ _)
  obtain ⟨ca, da, ha⟩ := rowA_affine v s p i
  obtain ⟨cb, db, hb⟩ := rowB_affine v s p i
  obtain ⟨cc, dc, hc⟩ := rowC_affine v s p i
  have q0 : ∀ a : ℝ, Function.update p i a 0 = p 0 := upd_ne p i 0 (Ne.symm i0)
  have q1 : ∀ a : ℝ, Function.update p i a 1 = p 1 := upd_ne p i 1 (Ne.symm i1)
  refine LineConvex.congr (ψ := fun a => (p 0) ^ 2 * (ca + da * a) ^ 2 +
      (p 1) ^ 2 * (cb + db * a) ^ 2 + ((p 0) ^ 2 * (p 1) ^ 2)⁻¹ * (cc + dc * a) ^ 2) ?_ ?_
  · intro a
    simp only [primalQ, q0, q1, ha, hb, hc]
    ring
  · exact ((LineConvex.smul (sq_nonneg _) (LineConvex.sqAffine _ _ _ _)).add
      (LineConvex.smul (sq_nonneg _) (LineConvex.sqAffine _ _ _ _))).add
      (LineConvex.smul (inv_nonneg.mpr (by positivity)) (LineConvex.sqAffine _ _ _ _))

theorem dualQ_chord (m : IntVec) (b : Cell) (h0 : (0 : ℝ) < b.lo 0) (h1 : (0 : ℝ) < b.lo 1) :
    ChordUpper b (dualQ m) := by
  apply chordUpper_of_line
  intro p hp i
  obtain ⟨p0, p1, le0, le1, _, _⟩ := box_facts hp h0 h1
  by_cases i0 : i = 0
  · subst i0
    have dB : ∀ a : ℝ, dualB m (Function.update p 0 a) = dualB m p := by
      intro a
      simp only [dualB, Function.update_apply, Fin.reduceEq, ↓reduceIte]
    have dC : ∀ a : ℝ, dualC m (Function.update p 0 a) = dualC m p := by
      intro a
      simp only [dualC, Function.update_apply, Fin.reduceEq, ↓reduceIte]
    have q1 : ∀ a : ℝ, Function.update p 0 a 1 = p 1 := upd_ne p 0 1 (by decide)
    refine LineConvex.congr (ψ := fun a => ((m 0 : ℝ) ^ 2) / a ^ 2 +
        ((p 1) ^ 2 * (dualC m p) ^ 2) * a ^ 2 + (dualB m p) ^ 2 / (p 1) ^ 2) ?_ ?_
    · intro a
      simp only [dualQ, dB, dC, q1, Function.update_self]
      ring
    · exact ((LineConvex.invSq _ _ _ h0 le0 (sq_nonneg _)).add
        (LineConvex.sq _ _ _ (by positivity))).add (LineConvex.const _ _ _)
  by_cases i1 : i = 1
  · subst i1
    have dB : ∀ a : ℝ, dualB m (Function.update p 1 a) = dualB m p := by
      intro a
      simp only [dualB, Function.update_apply, Fin.reduceEq, ↓reduceIte]
    have dC : ∀ a : ℝ, dualC m (Function.update p 1 a) = dualC m p := by
      intro a
      simp only [dualC, Function.update_apply, Fin.reduceEq, ↓reduceIte]
    have q0 : ∀ a : ℝ, Function.update p 1 a 0 = p 0 := upd_ne p 1 0 (by decide)
    refine LineConvex.congr (ψ := fun a => (dualB m p) ^ 2 / a ^ 2 +
        ((p 0) ^ 2 * (dualC m p) ^ 2) * a ^ 2 + ((m 0 : ℝ) ^ 2) / (p 0) ^ 2) ?_ ?_
    · intro a
      simp only [dualQ, dB, dC, q0, Function.update_self]
      ring
    · exact ((LineConvex.invSq _ _ _ h1 le1 (sq_nonneg _)).add
        (LineConvex.sq _ _ _ (by positivity))).add (LineConvex.const _ _ _)
  obtain ⟨cb, db, hb⟩ := dualB_affine m p i
  obtain ⟨cc, dc, hc⟩ := dualC_affine m p i
  have q0 : ∀ a : ℝ, Function.update p i a 0 = p 0 := upd_ne p i 0 (Ne.symm i0)
  have q1 : ∀ a : ℝ, Function.update p i a 1 = p 1 := upd_ne p i 1 (Ne.symm i1)
  refine LineConvex.congr (ψ := fun a => ((m 0 : ℝ) ^ 2) / (p 0) ^ 2 +
      ((p 1) ^ 2)⁻¹ * (cb + db * a) ^ 2 + ((p 0) ^ 2 * (p 1) ^ 2) * (cc + dc * a) ^ 2) ?_ ?_
  · intro a
    simp only [dualQ, q0, q1, hb, hc]
    ring
  · exact ((LineConvex.const _ _ _).add
      (LineConvex.smul (inv_nonneg.mpr (sq_nonneg _)) (LineConvex.sqAffine _ _ _ _))).add
      (LineConvex.smul (by positivity) (LineConvex.sqAffine _ _ _ _))

theorem phaseT_chordLower (m : IntVec) (b : Cell) : ChordLower b (phaseT m) :=
  (chord_of_affine b (phaseT m) (phaseT_affine m)).1

theorem phaseT_chordUpper (m : IntVec) (b : Cell) : ChordUpper b (phaseT m) :=
  (chord_of_affine b (phaseT m) (phaseT_affine m)).2

theorem termQ_chord (k : Kind) (n : IntVec) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) : ChordUpper b (termQ k n) := by
  cases k
  · exact primalQ_chord _ _ b h0 h1
  · exact primalQ_chord _ _ b h0 h1
  · exact dualQ_chord _ b h0 h1

theorem linTerm_chord (t : LinTerm) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) (neg : t.slope ≤ 0) : ChordLower b t.eval := by
  have hq := chordLower_negSmul (c := (t.slope : ℝ)) (by exact_mod_cast neg)
    (termQ_chord t.kind t.index b h0 h1)
  have hph := (chord_of_affine b (fun p => (t.phase : ℝ) * phaseT t.index p) (fun p i => by
    obtain ⟨c, d, h⟩ := phaseT_affine t.index p i
    exact ⟨(t.phase : ℝ) * c, (t.phase : ℝ) * d, fun a => by rw [h]; ring⟩)).1
  exact chordLower_congr (fun p => rfl) (chordLower_add (chordLower_add
    (chordLower_const b (t.const : ℝ)) hq) hph)

theorem linSum_chord (terms : List LinTerm) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) (neg : ∀ t ∈ terms, t.slope ≤ 0) : ChordLower b (linSum terms) := by
  induction terms with
  | nil => exact chordLower_congr (fun p => by simp [linSum]) (chordLower_const b 0)
  | cons t rest ih =>
    have ht := linTerm_chord t b h0 h1 (neg t (List.mem_cons_self))
    have hr := ih (fun u hu => neg u (List.mem_cons_of_mem _ hu))
    exact chordLower_congr (fun p => by simp [linSum]) (chordLower_add ht hr)

/-! ### Separate convexity of the registered cost -/

private theorem cauchy3 (a b : Fin 3 → ℝ) :
    (∑ j, a j * b j) ^ 2 ≤ (∑ j, a j ^ 2) * ∑ j, b j ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0),
    sq_nonneg (a 1 * b 2 - a 2 * b 1)]

/-- The third-row coefficients satisfy the convexity bound `2βM ≤ 3α` of
`LineConvex.recip`, for `α = A/P²`, `β = c/P`, `c² ≤ A`, `0 < P ≤ H`. -/
private theorem row3_condition (A c M P H : ℝ) (hA : 0 ≤ A) (hc : c ^ 2 ≤ A) (hM : 0 < M)
    (hP : 0 < P) (hPH : P ≤ H) (cond : 4 * (M * H) ^ 2 ≤ 9 * A) :
    2 * (c / P) * M ≤ 3 * (A / P ^ 2) := by
  have key : 2 * c * M * P ≤ 3 * A := by
    rcases le_or_gt c 0 with hc0 | hc0
    · nlinarith [mul_pos hM hP]
    · have hsq : (2 * c * M * P) ^ 2 ≤ (3 * A) ^ 2 := by
        have e1 : (2 * c * M * P) ^ 2 = 4 * c ^ 2 * (M ^ 2 * P ^ 2) := by ring
        have e2 : M ^ 2 * P ^ 2 ≤ (M * H) ^ 2 := by
          have : P ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hP.le hPH 2
          nlinarith [sq_nonneg M]
        have e3 : 4 * c ^ 2 * (M ^ 2 * P ^ 2) ≤ 4 * A * (M * H) ^ 2 := by
          have := mul_le_mul hc e2 (by positivity) hA
          nlinarith
        nlinarith
      have h3A : 0 ≤ 3 * A := by linarith
      nlinarith [sq_nonneg (2 * c * M * P - 3 * A), sq_nonneg (2 * c * M * P + 3 * A)]
  have hP2 : 0 < P ^ 2 := pow_pos hP 2
  rw [show 2 * (c / P) * M = (2 * c * M * P) / P ^ 2 by field_simp]
  rw [show 3 * (A / P ^ 2) = 3 * A / P ^ 2 by ring]
  exact div_le_div_of_nonneg_right key hP2.le

private theorem strain_split (N U : Fin 3 → Fin 3 → ℚ) (q : Chart) :
    strainCost N U q = (∑ j, (strainEntry N q 0 j - (U 0 j : ℝ)) ^ 2) +
      (∑ j, (strainEntry N q 1 j - (U 1 j : ℝ)) ^ 2) +
      (∑ j, (strainEntry N q 2 j - (U 2 j : ℝ)) ^ 2) := by
  simp only [strainCost, Fin.sum_univ_three]

theorem strainCost_chord (N U : Fin 3 → Fin 3 → ℚ) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) (unit2 : ∑ j, (U 2 j) ^ 2 = 1)
    (cond : 4 * (b.hi 0 * b.hi 1) ^ 2 ≤ 9 * ∑ j, (N 2 j) ^ 2) : ChordUpper b (strainCost N U) := by
  apply chordUpper_of_line
  intro p hp k
  obtain ⟨p0, p1, le0, le1, ph0, ph1⟩ := box_facts hp h0 h1
  set A : ℝ := ∑ j, ((N 2 j : ℚ) : ℝ) ^ 2 with hAdef
  set c : ℝ := ∑ j, ((N 2 j : ℚ) : ℝ) * ((U 2 j : ℚ) : ℝ) with hcdef
  set G : ℝ := ∑ j, ((U 2 j : ℚ) : ℝ) ^ 2 with hGdef
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hG1 : G = 1 := by
    rw [hGdef]
    exact_mod_cast unit2
  have hcA : c ^ 2 ≤ A := by
    have := cauchy3 (fun j => ((N 2 j : ℚ) : ℝ)) (fun j => ((U 2 j : ℚ) : ℝ))
    rw [← hAdef, ← hcdef, ← hGdef, hG1, mul_one] at this
    exact this
  have condR : 4 * ((b.hi 0 : ℝ) * (b.hi 1 : ℝ)) ^ 2 ≤ 9 * A := by
    rw [hAdef]
    exact_mod_cast cond
  have hhi0 : (0 : ℝ) < b.hi 0 := h0.trans_le le0
  have hhi1 : (0 : ℝ) < b.hi 1 := h1.trans_le le1
  -- Rows 0 and 1 are affine along every axis.
  have rowConvex (i : Fin 3) (hi : i ≠ 2 ∨ (k ≠ 0 ∧ k ≠ 1)) :
      LineConvex (fun a => ∑ j, (strainEntry N (Function.update p k a) i j - (U i j : ℝ)) ^ 2)
        (b.lo k) (b.hi k) := by
    apply LineConvex.sum
    intro j _
    obtain ⟨cj, dj, hj⟩ := strainEntry_affine N p k i j hi
    exact LineConvex.congr (fun a => by rw [hj a]; ring_nf)
      (LineConvex.sqAffine (cj - (U i j : ℝ)) dj _ _)
  have r0 := rowConvex 0 (Or.inl (by decide))
  have r1 := rowConvex 1 (Or.inl (by decide))
  refine LineConvex.congr (fun a => strain_split N U (Function.update p k a)) ?_
  by_cases k0 : k = 0
  · subst k0
    have q1 : ∀ a : ℝ, Function.update p 0 a 1 = p 1 := upd_ne p 0 1 (by decide)
    have third : LineConvex (fun a => ∑ j, (strainEntry N (Function.update p 0 a) 2 j - (U 2 j : ℝ)) ^ 2)
        (b.lo 0) (b.hi 0) := by
      refine LineConvex.congr (ψ := fun a => ((A / (p 1) ^ 2) / a ^ 2 - 2 * (c / p 1) / a) + G) ?_ ?_
      · intro a
        simp only [strainEntry, Fin.reduceEq, ↓reduceIte, Function.update_self, q1, hAdef, hcdef,
          hGdef, Fin.sum_univ_three]
        ring
      · exact (LineConvex.recip _ _ _ _ h0 le0 (div_nonneg hA (sq_nonneg _))
          (row3_condition A c (b.hi 0) (p 1) (b.hi 1) hA hcA hhi0 p1 ph1 condR)).add
          (LineConvex.const _ _ _)
    exact (r0.add r1).add third
  by_cases k1 : k = 1
  · subst k1
    have q0 : ∀ a : ℝ, Function.update p 1 a 0 = p 0 := upd_ne p 1 0 (by decide)
    have condR' : 4 * ((b.hi 1 : ℝ) * (b.hi 0 : ℝ)) ^ 2 ≤ 9 * A := by
      have e : (b.hi 1 : ℝ) * (b.hi 0 : ℝ) = (b.hi 0 : ℝ) * (b.hi 1 : ℝ) := mul_comm _ _
      rw [e]
      exact condR
    have third : LineConvex (fun a => ∑ j, (strainEntry N (Function.update p 1 a) 2 j - (U 2 j : ℝ)) ^ 2)
        (b.lo 1) (b.hi 1) := by
      refine LineConvex.congr (ψ := fun a => ((A / (p 0) ^ 2) / a ^ 2 - 2 * (c / p 0) / a) + G) ?_ ?_
      · intro a
        simp only [strainEntry, Fin.reduceEq, ↓reduceIte, Function.update_self, q0, hAdef, hcdef,
          hGdef, Fin.sum_univ_three]
        ring
      · exact (LineConvex.recip _ _ _ _ h1 le1 (div_nonneg hA (sq_nonneg _))
          (row3_condition A c (b.hi 1) (p 0) (b.hi 0) hA hcA hhi1 p0 ph0 condR')).add
          (LineConvex.const _ _ _)
    exact (r0.add r1).add third
  have r2 := rowConvex 2 (Or.inr ⟨k0, k1⟩)
  exact (r0.add r1).add r2

theorem regCost_chord (N U : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (b : Cell)
    (h0 : (0 : ℝ) < b.lo 0) (h1 : (0 : ℝ) < b.lo 1) (unit : ∀ i, ∑ j, (U i j) ^ 2 = 1)
    (cond : 4 * (b.hi 0 * b.hi 1) ^ 2 ≤ 9 * ∑ j, (N 2 j) ^ 2) : ChordUpper b (regCost N U w) := by
  have hs := strainCost_chord N U b h0 h1 (unit 2) cond
  have hd := primalQ_chord (fun i => -w i) true b h0 h1
  exact chordUpper_congr (fun p => rfl)
    (chordUpper_add (chordUpper_smul (by norm_num : (0 : ℝ) ≤ 100) hs)
      (chordUpper_smul (by norm_num : (0 : ℝ) ≤ 200) hd))

/-! ### Features and aggregation -/

theorem featGen_cast (c : Fin 8 → ℚ) (j : Fin 19) :
    ((featGen c j : ℚ) : ℝ) = featGen (fun i => (c i : ℝ)) j := by
  fin_cases j <;> simp [featGen]

theorem termQ_feat (k : Kind) (n : IntVec) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    termQ k n p = ∑ j : Fin 19, (qForm k n j : ℝ) * featGen p j := by
  cases k <;>
    simp [termQ, primalQ, dualQ, dualB, dualC, rowA, rowB, rowC, img, intVec, qForm, mom,
      featGen, Fin.sum_univ_succ, offset_zero, offset_one, offset_two] <;>
    field_simp <;> ring

theorem phaseT_feat (n : IntVec) (p : Chart) :
    phaseT n p = ∑ j : Fin 19, (tForm n j : ℝ) * featGen p j := by
  simp [phaseT, tForm, featGen, Fin.sum_univ_succ, offset_zero, offset_one, offset_two]

theorem linSum_feat (terms : List LinTerm) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    linSum terms p = (aggConst terms : ℝ) + ∑ j : Fin 19, (aggWeight terms j : ℝ) * featGen p j := by
  induction terms with
  | nil => simp [linSum, aggConst, aggWeight]
  | cons t rest ih =>
    have hs : linSum (t :: rest) p = t.eval p + linSum rest p := by simp [linSum]
    have hc : aggConst (t :: rest) = t.const + aggConst rest := by simp [aggConst]
    have hw : ∀ j, aggWeight (t :: rest) j =
        (t.slope * qForm t.kind t.index j + t.phase * tForm t.index j) + aggWeight rest j := by
      intro j
      simp [aggWeight]
    rw [hs, ih, hc]
    simp only [hw, LinTerm.eval, termQ_feat t.kind t.index p h0 h1, phaseT_feat t.index p]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf

theorem regCostQ_cast (N U : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (c : Fin 8 → ℚ)
    (h0 : c 0 ≠ 0) (h1 : c 1 ≠ 0) :
    ((regCostQ N U w c : ℚ) : ℝ) = regCost N U w (fun i => (c i : ℝ)) := by
  simp only [regCostQ, regCost, strainCost, strainEntryQ, strainEntry, primalQQ, primalQ,
    rowA, rowB, rowC, img, imgQ, Fin.sum_univ_three, Fin.reduceEq, ↓reduceIte, offset_zero,
    offset_one, offset_two]
  push_cast
  ring

theorem cornerRat_cast (b : Cell) (bits : Axis → Bool) :
    (fun i => ((DirectRoute.cornerRat b bits i : ℚ) : ℝ)) = corner b bits := by
  funext i
  simp only [DirectRoute.cornerRat, corner]
  split_ifs <;> rfl

end BccSharp.Coulomb.CompactCover.JLeaf
