import BccSharp.TwoSite.DefectInvariance

set_option autoImplicit false

/-! Independent statement of the defect side of the two-site theorem, and its agreement with
the interface.

Part 1 (namespace `TwoSiteSpec`) restates the definitions of the two-site theorem:

* the actual defect `D` at length unit `a`: the BCC star as the nonzero
  points of the BCC lattice of cube side `a` inside `r_out = 13a/10`; the lift
  vectors of a site; injections of the star into the lifts; proper rotations
  `SO(3)`; the strain normalization `a⁻²`, `s⋆ = 1/5`; the annular weight
  `min{1, (r_out − r)/(r_out − r_in)}` with `r_in = (1 + s⋆) a`; the matched
  strain `s = +∞` below fourteen lifts; `D = min{1, s/s⋆²}`;
* the conventional BCC and FCC lattices at the same density;
* rigid motions (distance-preserving bijections of space);
* unions of two distinct translates of a lattice of covolume `8π/3`;
* the registration bound (3.10).

It uses Mathlib's Euclidean space, special orthogonal group, isometries,
finite sums and extended reals, and no definition of the interface.

Part 2 (namespace `BccSharp.Coulomb.SpecBridge`) proves that these
agree with the interface's `defect`, `IsBCC`, `IsFCC` and `Registration`. -/

noncomputable section
open scoped BigOperators ENNReal

/-! ## Part 1. Definitions of the statement -/

namespace TwoSiteSpec

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Real 3×3 matrices. -/
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

/-- A matrix acting on Euclidean three-space. -/
def transform (R : M3) (x : E3) : E3 := Matrix.toEuclideanLin R x

/-- The point with integer coordinates `n`. -/
def intPoint (n : Fin 3 → ℤ) : E3 := WithLp.toLp 2 (fun i => (n i : ℝ))

/-- Dilation of a point set by `a`. -/
def dilate (a : ℝ) (X : Set E3) : Set E3 := (fun x => a • x) '' X

/-- The conventional BCC lattice with cube side one: cube corners and cube
centres. -/
def bccUnit : Set E3 :=
  {x | ∃ n : Fin 3 → ℤ, (∀ i, x i = n i) ∨ (∀ i, x i = n i + 1 / 2)}

/-- The corner and the three face centres of the unit cube. -/
def faceCentre : Fin 4 → Fin 3 → ℝ :=
  ![![0, 0, 0], ![0, 1 / 2, 1 / 2], ![1 / 2, 0, 1 / 2], ![1 / 2, 1 / 2, 0]]

/-- The conventional FCC lattice with two points per unit volume, the density
of `bccUnit`: cube side `2^(1/3)`, cube corners and face centres. -/
def fccUnit : Set E3 :=
  {x | ∃ (n : Fin 3 → ℤ) (c : Fin 4), ∀ i, x i = (2 : ℝ) ^ (1 / 3 : ℝ) * (n i + faceCentre c i)}

/-! ### Definitions at length unit `a` (the conventional cube side; `a = a_c` at
density `3/(4π)`) -/

/-- The strain normalization `s⋆`. -/
def sStar : ℝ := 1 / 5

/-- The inner radius `r_in = (1 + s⋆) a`. -/
def rIn (a : ℝ) : ℝ := (1 + sStar) * a

/-- The outer radius `r_out = (13/10) a`. -/
def rOut (a : ℝ) : ℝ := 13 / 10 * a

/-- The BCC star: the nonzero points of the BCC lattice with cube side `a`
inside `r_out`. -/
def specStar (a : ℝ) : Set E3 := {e | e ∈ dilate a bccUnit ∧ 0 < ‖e‖ ∧ ‖e‖ < rOut a}

/-- The annular weight `w(r) = min{1, (r_out − r)/(r_out − r_in)}`. -/
def specWeight (a r : ℝ) : ℝ := min 1 ((rOut a - r) / (rOut a - rIn a))

/-- The lift vectors of the site `x` of the point set `X` (Spec's `Y_i`): the
displacements to the other points within `r_out`. Spec defines `Y_i` for
configurations on a cubic torus `ℝ³/Γ_k`, as a multiset over the lifts of all
particles; for the periodic point set of such a configuration, whose points
are distinct, this set is exactly `Y_i`. -/
def liftVectors (a : ℝ) (X : Set E3) (x : E3) : Set E3 :=
  {y | x + y ∈ X ∧ y ≠ 0 ∧ ‖y‖ < rOut a}

/-- The cost of a rotation `R` and an injection `σ` of the star into the lifts:
`a⁻² Σ_e |σ(e) − R e|² + s⋆² Σ_{y unmatched} w(|y|)`. The point sets used here
are locally finite, so their lift sets are finite and `∑ᶠ` is a finite sum;
on an infinite lift set `∑ᶠ` would be `0`. -/
def specCost (a : ℝ) {Y : Set E3} (R : M3) (σ : ↥(specStar a) ↪ ↥Y) : ℝ :=
  a⁻¹ ^ 2 * (∑ᶠ e : ↥(specStar a), ‖(σ e : E3) - transform R e‖ ^ 2) +
    sStar ^ 2 * ∑ᶠ y ∈ Y \ Set.range (fun e => (σ e : E3)), specWeight a ‖y‖

/-- The matched strain `s_i`: `+∞` with fewer than fourteen lifts, otherwise
the infimum of the cost over proper rotations and injections. -/
def specStrain (a : ℝ) (Y : Set E3) : ℝ≥0∞ :=
  if Y.encard < 14 then ⊤ else
    ⨅ (R : M3) (_ : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (σ : ↥(specStar a) ↪ ↥Y),
      ENNReal.ofReal (specCost a R σ)

/-- The defect `D_i = min{1, s_i/s⋆²}`. -/
def specDefect (a : ℝ) (Y : Set E3) : ℝ :=
  (min 1 (specStrain a Y / ENNReal.ofReal (sStar ^ 2))).toReal

/-- The defect at the site `x` of the point set `X`, at length unit `a`. -/
def specSiteDefect (a : ℝ) (X : Set E3) (x : E3) : ℝ := specDefect a (liftVectors a X x)

/-! ### Configurations, rigid motions and registration -/

/-- The lattice spanned by the columns of `A`. -/
def latticeOf (A : M3) : Set E3 := Set.range (fun n : Fin 3 → ℤ => transform A (intPoint n))

/-- A set together with its translate by `τ`. -/
def withTranslate (L : Set E3) (τ : E3) : Set E3 := L ∪ (fun y => y + τ) '' L

/-- The union `L ∪ (L + τ)` of a lattice `L` of covolume `8π/3` and a distinct
translate of it: two points per cell of volume `8π/3`,
density `3/(4π)`. It contains the origin. -/
def TwoCosetConfig (X : Set E3) : Prop :=
  ∃ (A : M3) (τ : E3), |A.det| = 8 * Real.pi / 3 ∧ τ ∉ latticeOf A ∧
    X = withTranslate (latticeOf A) τ

/-- A union `(L + a) ∪ (L + b)` of two distinct translates of a lattice `L` of
covolume `8π/3`. Each is a translate of a
`TwoCosetConfig`. -/
def TwoTranslates (X : Set E3) : Prop :=
  ∃ (A : M3) (a b : E3), |A.det| = 8 * Real.pi / 3 ∧ b - a ∉ latticeOf A ∧
    X = (fun y => y + a) '' latticeOf A ∪ (fun y => y + b) '' latticeOf A

/-- `X` is the image of `Y` under a rigid motion: a distance-preserving
bijection of space. -/
def RigidImage (X Y : Set E3) : Prop := ∃ φ : E3 ≃ᵢ E3, X = φ '' Y

/-- An index-two period basis `B` of the conventional BCC lattice and the
corresponding nonzero half translation `f₀`. -/
def IndexTwoBasis (B : M3) (f₀ : Fin 3 → ℝ) : Prop :=
  B.det = 1 ∧ (∃ m : Fin 3 → ℤ, ∀ i, 2 * f₀ i = m i) ∧ (∀ m : Fin 3 → ℤ, ∃ i, f₀ i ≠ m i) ∧
    bccUnit = withTranslate (latticeOf B) (transform B (WithLp.toLp 2 f₀))

/-- Inequality (3.10) for the period basis `R` and offset `f` (normalized
lengths) with defect value `D`: strain and optical displacement against an
index-two BCC basis, its half translation, an integer wrap and a proper
rotation. -/
def RegisteredBound (R : M3) (f : Fin 3 → ℝ) (D : ℝ) : Prop :=
  ∃ (B : M3) (f₀ : Fin 3 → ℝ) (n : Fin 3 → ℤ) (U : M3),
    IndexTwoBasis B f₀ ∧ U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
    100 * (∑ i, ∑ j, ((R * B⁻¹) i j - U i j) ^ 2) +
      200 * ‖transform R (WithLp.toLp 2 (f - f₀ - fun i => (n i : ℝ)))‖ ^ 2 ≤ D

end TwoSiteSpec

/-! ## Part 2. Agreement with the interface -/

namespace BccSharp.Coulomb.SpecBridge
open TwoSiteSpec
open BccSharp.Coulomb.DefectInvariance
open BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.BravaisCover

/-! ### Vectors -/

/-- The interface's vectors as points of Euclidean space. -/
def toE3 (v : Vec) : E3 := WithLp.toLp 2 v

@[simp] theorem toE3_apply (v : Vec) (i : Fin 3) : toE3 v i = v i := rfl

theorem toE3_injective : Function.Injective toE3 := fun _ _ h => congrArg WithLp.ofLp h

theorem exists_toE3 (x : E3) : ∃ v : Vec, x = toE3 v := ⟨WithLp.ofLp x, rfl⟩

theorem toE3_add (u v : Vec) : toE3 (u + v) = toE3 u + toE3 v := rfl
theorem toE3_sub (u v : Vec) : toE3 (u - v) = toE3 u - toE3 v := rfl
theorem toE3_smul (t : ℝ) (u : Vec) : toE3 (t • u) = t • toE3 u := rfl
theorem toE3_zero : toE3 0 = 0 := rfl

theorem toE3_neg (u : Vec) : toE3 (-u) = -toE3 u := by
  rw [show -u = 0 - u by abel, toE3_sub, toE3_zero, zero_sub]

theorem norm_toE3_sq (v : Vec) : ‖toE3 v‖ ^ 2 = sq v :=
  (EuclideanSpace.real_norm_sq_eq (toE3 v)).trans rfl

theorem norm_toE3 (v : Vec) : ‖toE3 v‖ = Real.sqrt (sq v) := by
  rw [← norm_toE3_sq, Real.sqrt_sq (norm_nonneg _)]

theorem norm_toE3_lt (v : Vec) {r : ℝ} (hr : 0 < r) : ‖toE3 v‖ < r ↔ sq v < r ^ 2 := by
  rw [norm_toE3, Real.sqrt_lt' hr]

theorem transform_toE3 (R : Mat) (v : Vec) : transform R (toE3 v) = toE3 (R.mulVec v) := rfl

theorem transform_sub (R : Mat) (x y : E3) : transform R x - transform R y = transform R (x - y) :=
  (map_sub (Matrix.toEuclideanLin R) x y).symm

theorem transform_smul (R : Mat) (t : ℝ) (x : E3) : transform R (t • x) = t • transform R x :=
  map_smul (Matrix.toEuclideanLin R) t x

theorem transform_smul_matrix (t : ℝ) (R : Mat) (x : E3) :
    transform (t • R) x = t • transform R x := by
  obtain ⟨v, rfl⟩ := exists_toE3 x
  rw [transform_toE3, transform_toE3, Matrix.smul_mulVec, toE3_smul]

theorem intPoint_eq (n : IntVec) : intPoint n = toE3 (castVec n) := rfl

theorem norm_transform {U : Mat} (hU : orthogonal U) (x : E3) : ‖transform U x‖ = ‖x‖ := by
  obtain ⟨v, rfl⟩ := exists_toE3 x
  rw [transform_toE3, norm_toE3, norm_toE3, sq_orthogonal hU]

theorem mem_SO3_iff (R : Mat) : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ↔ proper R := by
  show _ ↔ (R.transpose * R = 1 ∧ R.det = 1)
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']

/-! ### Dilations -/

theorem dilate_image_toE3 (t : ℝ) (S : Set Vec) :
    dilate t (toE3 '' S) = toE3 '' ((fun x => t • x) '' S) := by
  unfold dilate
  rw [Set.image_image, Set.image_image]
  rfl

theorem dilate_dilate (s t : ℝ) (X : Set E3) : dilate s (dilate t X) = dilate (s * t) X := by
  unfold dilate
  rw [Set.image_image]
  simp only [smul_smul]

theorem dilate_one (X : Set E3) : dilate 1 X = X := by
  simp [dilate]

theorem mem_dilate {t : ℝ} (ht : t ≠ 0) {X : Set E3} {x : E3} : x ∈ dilate t X ↔ t⁻¹ • x ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [smul_smul, inv_mul_cancel₀ ht, one_smul]
  · intro hx
    refine ⟨t⁻¹ • x, hx, ?_⟩
    show t • (t⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ ht, one_smul]

theorem smul_injective_E3 {t : ℝ} (ht : t ≠ 0) : Function.Injective (fun x : E3 => t • x) := by
  intro x y h
  have e := congrArg (fun z : E3 => t⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ ht] using e

/-! ### Lattices and two-coset configurations -/

theorem latticeOf_eq (A : Mat) : latticeOf A = toE3 '' lattice A := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨A.mulVec (castVec n), ⟨n, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

theorem withTranslate_eq (S : Set Vec) (t : Vec) :
    withTranslate (toE3 '' S) (toE3 t) = toE3 '' (S ∪ translate t S) := by
  ext x
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨_, ⟨y, hy, rfl⟩, rfl⟩)
    · exact ⟨y, Or.inl hy, rfl⟩
    · exact ⟨y + t, Or.inr ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, hy | ⟨y, hy, rfl⟩, rfl⟩
    · exact Or.inl ⟨_, hy, rfl⟩
    · exact Or.inr ⟨toE3 y, ⟨y, hy, rfl⟩, rfl⟩

/-- The normalized point set of `q` in Euclidean space. -/
def specPoints (q : TwoSite) : Set E3 := toE3 '' q.points

/-- The physical point set of `q`: lengths in Wigner–Seitz units. -/
def physPoints (q : TwoSite) : Set E3 := dilate ac (specPoints q)

theorem specPoints_eq (q : TwoSite) :
    specPoints q = withTranslate (latticeOf q.basis) (transform q.basis (toE3 q.offset)) := by
  rw [latticeOf_eq, transform_toE3, withTranslate_eq]
  rfl

theorem dilate_withTranslate (t : ℝ) (L : Set E3) (τ : E3) :
    dilate t (withTranslate L τ) = withTranslate (dilate t L) (t • τ) := by
  unfold dilate withTranslate
  rw [Set.image_union, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro y _
  rw [smul_add]

theorem latticeOf_smul (t : ℝ) (A : Mat) : latticeOf (t • A) = dilate t (latticeOf A) := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨transform A (intPoint n), ⟨n, rfl⟩, (transform_smul_matrix t A _).symm⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, transform_smul_matrix t A _⟩

/-- The physical point set of a configuration as a union of two translates. -/
theorem physPoints_eq (q : TwoSite) :
    physPoints q = withTranslate (latticeOf (ac • q.basis)) (transform (ac • q.basis) (toE3 q.offset)) := by
  rw [physPoints, specPoints_eq, dilate_withTranslate, ← latticeOf_smul, ← transform_smul_matrix]

/-- Every valid configuration is a union of two distinct translates of a
lattice of covolume `8π/3`. -/
theorem twoCoset_of_valid (q : TwoSite) (hq : q.Valid) : TwoCosetConfig (physPoints q) := by
  refine ⟨ac • q.basis, transform (ac • q.basis) (toE3 q.offset), ?_, ?_, physPoints_eq q⟩
  · rw [Matrix.det_smul, Fintype.card_fin, hq.1, mul_one, abs_of_pos (pow_pos ac_positive 3),
      ac_cube]
  · rintro ⟨n, hn⟩
    have hu : IsUnit (ac • q.basis) := (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (series_physical_basis_nonsingular q hq))
    have e : (ac • q.basis).mulVec (castVec n) = (ac • q.basis).mulVec q.offset :=
      toE3_injective hn
    exact hq.2 n (Matrix.mulVec_injective_of_isUnit hu e).symm

/-- Reflection of the first basis vector. -/
def flipD : Mat := Matrix.diagonal ![-1, 1, 1]

def flipZ (n : IntVec) : IntVec := ![-n 0, n 1, n 2]

theorem flipD_mulVec (n : IntVec) : flipD.mulVec (castVec n) = castVec (flipZ n) := by
  funext i
  fin_cases i <;> simp [flipD, flipZ, castVec, Matrix.mulVec_diagonal]

theorem flipZ_flipZ (n : IntVec) : flipZ (flipZ n) = n := by
  funext i
  fin_cases i <;> simp [flipZ]

theorem flipD_det : flipD.det = -1 := by
  simp [flipD, Matrix.det_diagonal, Fin.prod_univ_three]

theorem latticeOf_flip (A : Mat) : latticeOf (A * flipD) = latticeOf A := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨flipZ n, ?_⟩
    show toE3 (A.mulVec (castVec (flipZ n))) = toE3 ((A * flipD).mulVec (castVec n))
    rw [← Matrix.mulVec_mulVec, flipD_mulVec]
  · rintro ⟨n, rfl⟩
    refine ⟨flipZ n, ?_⟩
    show toE3 ((A * flipD).mulVec (castVec (flipZ n))) = toE3 (A.mulVec (castVec n))
    rw [← Matrix.mulVec_mulVec, flipD_mulVec, flipZ_flipZ]

/-- Every union of a lattice of covolume `8π/3` and a distinct translate of it
is the physical point set of a valid configuration: the interface covers
every shape and every noncoincident shift. -/
theorem valid_of_twoCoset {X : Set E3} (hX : TwoCosetConfig X) :
    ∃ q : TwoSite, q.Valid ∧ physPoints q = X := by
  obtain ⟨A, τ, hdet, hτ, rfl⟩ := hX
  obtain ⟨A', hA'det, hA'lat⟩ : ∃ A' : Mat, A'.det = 8 * Real.pi / 3 ∧ latticeOf A' = latticeOf A := by
    rcases le_or_gt 0 A.det with h | h
    · exact ⟨A, (abs_of_nonneg h).symm.trans hdet, rfl⟩
    · refine ⟨A * flipD, ?_, latticeOf_flip A⟩
      rw [Matrix.det_mul, flipD_det, ← hdet, abs_of_neg h]
      ring
  have hac3 : ac ^ 3 = 8 * Real.pi / 3 := ac_cube
  have hA'ne : A'.det ≠ 0 := by rw [hA'det]; positivity
  have hA'u : IsUnit A' := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA'ne)
  let f : Vec := (A'⁻¹).mulVec (WithLp.ofLp τ)
  have hτf : transform A' (toE3 f) = τ := by
    rw [transform_toE3]
    show toE3 (A'.mulVec ((A'⁻¹).mulVec (WithLp.ofLp τ))) = τ
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA'u),
      Matrix.one_mulVec]
    rfl
  have hsmul : ac • (ac⁻¹ • A') = A' := by
    rw [smul_smul, mul_inv_cancel₀ ac_positive.ne', one_smul]
  refine ⟨⟨ac⁻¹ • A', f⟩, ⟨?_, ?_⟩, ?_⟩
  · show (ac⁻¹ • A').det = 1
    rw [Matrix.det_smul, Fintype.card_fin, hA'det, inv_pow, hac3,
      inv_mul_cancel₀ (by positivity)]
  · intro n hn
    apply hτ
    rw [← hA'lat]
    refine ⟨n, ?_⟩
    rw [← hτf]
    show transform A' (toE3 (castVec n)) = transform A' (toE3 f)
    rw [← hn]
  · rw [physPoints_eq]
    show withTranslate (latticeOf (ac • (ac⁻¹ • A'))) (transform (ac • (ac⁻¹ • A')) (toE3 f)) =
      withTranslate (latticeOf A) τ
    rw [hsmul, hA'lat, hτf]

/-! ### The reference lattices -/

theorem dilate_bccUnit_mem (x : E3) :
    x ∈ bccUnit ↔ ∃ n : IntVec, (∀ i, x i = n i) ∨ (∀ i, x i = n i + 1 / 2) := Iff.rfl

theorem bcc_points_iff (v : Vec) :
    v ∈ bcc.points ↔ ∃ n : IntVec, (∀ i, v i = n i) ∨ (∀ i, v i = n i + 1 / 2) := by
  constructor
  · rintro (⟨n, hn⟩ | ⟨_, ⟨n, rfl⟩, rfl⟩)
    · refine ⟨n, Or.inl fun i => ?_⟩
      have e : (1 : Mat).mulVec (castVec n) = v := hn
      rw [Matrix.one_mulVec] at e
      rw [← e]
      rfl
    · refine ⟨n, Or.inr fun i => ?_⟩
      show ((1 : Mat).mulVec (castVec n) + (1 : Mat).mulVec (fun _ => 1 / 2)) i = n i + 1 / 2
      rw [Matrix.one_mulVec, Matrix.one_mulVec]
      rfl
  · rintro ⟨n, hn | hn⟩
    · refine Or.inl ⟨n, ?_⟩
      show (1 : Mat).mulVec (castVec n) = v
      rw [Matrix.one_mulVec]
      funext i
      exact (hn i).symm
    · refine Or.inr ⟨castVec n, ⟨n, ?_⟩, ?_⟩
      · show (1 : Mat).mulVec (castVec n) = castVec n
        rw [Matrix.one_mulVec]
      show v = castVec n + (1 : Mat).mulVec (fun _ => 1 / 2)
      rw [Matrix.one_mulVec]
      funext i
      rw [hn i]
      rfl

/-- The conventional BCC lattice is the interface's BCC point set. -/
theorem bccUnit_eq : bccUnit = specPoints bcc := by
  ext x
  obtain ⟨v, rfl⟩ := exists_toE3 x
  constructor
  · intro hx
    exact ⟨v, (bcc_points_iff v).mpr hx, rfl⟩
  · rintro ⟨w, hw, e⟩
    rw [← toE3_injective e]
    exact (bcc_points_iff w).mp hw

/-- Integer vectors with even coordinate sum, scaled by `s`. -/
def evenLattice (s : ℝ) : Set Vec :=
  {v | ∃ k : IntVec, (k 0 + k 1 + k 2) % 2 = 0 ∧ ∀ i, v i = s * k i}

theorem fcc_primitive_apply (n : IntVec) (i : Fin 3) :
    (Constants.primitiveNormalized .fcc).mulVec (castVec n) i =
      Constants.fccLength / 2 * ((n 0 + n 1 + n 2 - n i : ℤ) : ℝ) := by
  fin_cases i <;>
    simp [Constants.primitiveNormalized, Constants.Reference.naturalBasis, castVec, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three] <;> ring

theorem fcc_points_even : fcc.points = evenLattice (Constants.fccLength / 2) := by
  rw [← Constants.fcc_primitive_points]
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨fun i => n 0 + n 1 + n 2 - n i, ?_, fun i => fcc_primitive_apply n i⟩
    show (n 0 + n 1 + n 2 - n 0 + (n 0 + n 1 + n 2 - n 1) + (n 0 + n 1 + n 2 - n 2)) % 2 = 0
    omega
  · rintro ⟨k, hk, hv⟩
    obtain ⟨h, hh⟩ : ∃ h : ℤ, 2 * h = k 0 + k 1 + k 2 := ⟨(k 0 + k 1 + k 2) / 2, by omega⟩
    refine ⟨fun i => h - k i, ?_⟩
    funext i
    show (Constants.primitiveNormalized .fcc).mulVec (castVec (fun i => h - k i)) i = v i
    rw [fcc_primitive_apply, hv i]
    have e : h - k 0 + (h - k 1) + (h - k 2) - (h - k i) = k i := by omega
    simp only [e]

/-- Twice the face centres, as integer vectors. -/
def faceInt : Fin 4 → Fin 3 → ℤ := ![![0, 0, 0], ![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]

theorem faceCentre_eq : ∀ (c : Fin 4) (i : Fin 3), faceCentre c i = (faceInt c i : ℝ) / 2 := by
  intro c i
  fin_cases c <;> fin_cases i <;> norm_num [faceCentre, faceInt]

theorem faceInt_even : ∀ c : Fin 4, (faceInt c 0 + faceInt c 1 + faceInt c 2) % 2 = 0 := by
  decide

theorem int_split (z : ℤ) : (z : ℝ) = 2 * ((z / 2 : ℤ) : ℝ) + ((z % 2 : ℤ) : ℝ) := by
  have e : z % 2 + 2 * (z / 2) = z := Int.emod_add_mul_ediv z 2
  have e' := congrArg (fun w : ℤ => (w : ℝ)) e
  push_cast at e'
  linarith

theorem fccUnit_even (x : E3) : x ∈ fccUnit ↔ WithLp.ofLp x ∈ evenLattice (Constants.fccLength / 2) := by
  constructor
  · rintro ⟨n, c, hx⟩
    refine ⟨fun i => 2 * n i + faceInt c i, ?_, fun i => ?_⟩
    · have hc := faceInt_even c
      show (2 * n 0 + faceInt c 0 + (2 * n 1 + faceInt c 1) + (2 * n 2 + faceInt c 2)) % 2 = 0
      omega
    · show x i = _
      rw [hx i, faceCentre_eq]
      unfold Constants.fccLength
      push_cast
      ring
  · rintro ⟨k, hk, hx⟩
    have hx' : ∀ i, x i = Constants.fccLength / 2 * k i := hx
    have key : ∀ c : Fin 4, (∀ i, ((k i % 2 : ℤ) : ℝ) / 2 = faceCentre c i) → x ∈ fccUnit := by
      intro c hc
      refine ⟨fun i => k i / 2, c, fun i => ?_⟩
      rw [hx' i, int_split (k i), ← hc i]
      unfold Constants.fccLength
      ring
    rcases Int.emod_two_eq_zero_or_one (k 0) with h0 | h0 <;>
      rcases Int.emod_two_eq_zero_or_one (k 1) with h1 | h1
    · have h2 : k 2 % 2 = 0 := by omega
      apply key 0
      intro i
      fin_cases i <;> simp [faceCentre, h0, h1, h2]
    · have h2 : k 2 % 2 = 1 := by omega
      apply key 1
      intro i
      fin_cases i <;> simp [faceCentre, h0, h1, h2]
    · have h2 : k 2 % 2 = 1 := by omega
      apply key 2
      intro i
      fin_cases i <;> simp [faceCentre, h0, h1, h2]
    · have h2 : k 2 % 2 = 0 := by omega
      apply key 3
      intro i
      fin_cases i <;> simp [faceCentre, h0, h1, h2]

/-- The conventional FCC lattice is the interface's FCC point set. -/
theorem fccUnit_eq : fccUnit = specPoints fcc := by
  ext x
  rw [fccUnit_even, specPoints, fcc_points_even]
  constructor
  · intro h
    exact ⟨WithLp.ofLp x, h, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact hw

/-! ### The star -/

/-- Doubled BCC points with equal coordinate parities and squared length at
most six are exactly the doubled labels of the interface's star. -/
theorem doubled_star : ∀ a b c : Fin 5,
    (((a : ℤ) - (b : ℤ)) % 2 = 0 ∧ ((b : ℤ) - (c : ℤ)) % 2 = 0 ∧
      0 < ((a : ℤ) - 2) ^ 2 + ((b : ℤ) - 2) ^ 2 + ((c : ℤ) - 2) ^ 2 ∧
      ((a : ℤ) - 2) ^ 2 + ((b : ℤ) - 2) ^ 2 + ((c : ℤ) - 2) ^ 2 ≤ 6) →
    ∃ j : Fin 14, starTwice j 0 = (a : ℤ) - 2 ∧ starTwice j 1 = (b : ℤ) - 2 ∧
      starTwice j 2 = (c : ℤ) - 2 := by
  decide

theorem doubled_star_int (u v w : ℤ) (hu : -2 ≤ u ∧ u ≤ 2) (hv : -2 ≤ v ∧ v ≤ 2)
    (hw : -2 ≤ w ∧ w ≤ 2) (h1 : (u - v) % 2 = 0) (h2 : (v - w) % 2 = 0)
    (h3 : 0 < u ^ 2 + v ^ 2 + w ^ 2) (h4 : u ^ 2 + v ^ 2 + w ^ 2 ≤ 6) :
    ∃ j : Fin 14, starTwice j 0 = u ∧ starTwice j 1 = v ∧ starTwice j 2 = w := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 5, (a : ℤ) - 2 = u :=
    ⟨⟨(u + 2).toNat, by omega⟩, by simp only; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin 5, (b : ℤ) - 2 = v :=
    ⟨⟨(v + 2).toNat, by omega⟩, by simp only; omega⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin 5, (c : ℤ) - 2 = w :=
    ⟨⟨(w + 2).toNat, by omega⟩, by simp only; omega⟩
  subst ha hb hc
  exact doubled_star a b c ⟨by omega, by omega, h3, h4⟩

theorem starTwice_facts : ∀ j : Fin 14,
    ((starTwice j 0 - starTwice j 1) % 2 = 0 ∧ (starTwice j 1 - starTwice j 2) % 2 = 0) ∧
    (starTwice j 0 ^ 2 + starTwice j 1 ^ 2 + starTwice j 2 ^ 2 = 3 ∨
      starTwice j 0 ^ 2 + starTwice j 1 ^ 2 + starTwice j 2 ^ 2 = 4) := by
  decide

/-- Points of the unit BCC lattice have doubled integer coordinates of equal
parity. -/
theorem bccUnit_doubled {x : E3} (hx : x ∈ bccUnit) :
    ∃ w : IntVec, (w 0 - w 1) % 2 = 0 ∧ (w 1 - w 2) % 2 = 0 ∧ ∀ i, x i = (w i : ℝ) / 2 := by
  obtain ⟨n, hn | hn⟩ := hx
  · refine ⟨fun i => 2 * n i, ?_, ?_, fun i => ?_⟩
    · show (2 * n 0 - 2 * n 1) % 2 = 0
      omega
    · show (2 * n 1 - 2 * n 2) % 2 = 0
      omega
    · rw [hn i]
      push_cast
      ring
  · refine ⟨fun i => 2 * n i + 1, ?_, ?_, fun i => ?_⟩
    · show (2 * n 0 + 1 - (2 * n 1 + 1)) % 2 = 0
      omega
    · show (2 * n 1 + 1 - (2 * n 2 + 1)) % 2 = 0
      omega
    · rw [hn i]
      push_cast
      ring

theorem bccUnit_of_doubled {x : E3} (w : IntVec) (h01 : (w 0 - w 1) % 2 = 0)
    (h12 : (w 1 - w 2) % 2 = 0) (hx : ∀ i, x i = (w i : ℝ) / 2) : x ∈ bccUnit := by
  rcases Int.emod_two_eq_zero_or_one (w 0) with h0 | h0
  · refine ⟨fun i => w i / 2, Or.inl fun i => ?_⟩
    have hi : w i % 2 = 0 := by
      fin_cases i
      · exact h0
      · show w 1 % 2 = 0
        omega
      · show w 2 % 2 = 0
        omega
    have e : w i / 2 * 2 = w i := by omega
    have e' := congrArg (fun z : ℤ => (z : ℝ)) e
    push_cast at e'
    rw [hx i]
    show (w i : ℝ) / 2 = ((w i / 2 : ℤ) : ℝ)
    linarith
  · refine ⟨fun i => (w i - 1) / 2, Or.inr fun i => ?_⟩
    have hi : w i % 2 = 1 := by
      fin_cases i
      · exact h0
      · show w 1 % 2 = 1
        omega
      · show w 2 % 2 = 1
        omega
    have e : (w i - 1) / 2 * 2 + 1 = w i := by omega
    have e' := congrArg (fun z : ℤ => (z : ℝ)) e
    push_cast at e'
    rw [hx i]
    show (w i : ℝ) / 2 = (((w i - 1) / 2 : ℤ) : ℝ) + 1 / 2
    linarith

theorem sq_doubled (v : Vec) (w : IntVec) (hw : ∀ i, v i = (w i : ℝ) / 2) :
    sq v = ((w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 : ℤ) : ℝ) / 4 := by
  simp only [sq, Fin.sum_univ_three]
  rw [hw 0, hw 1, hw 2]
  push_cast
  ring

theorem star_doubled (j : Fin 14) : ∀ i, star j i = (starTwice j i : ℝ) / 2 := by
  intro i
  rw [starTwice_eq]
  ring

theorem sq_star (j : Fin 14) : sq (star j) = 3 / 4 ∨ sq (star j) = 1 := by
  rw [sq_doubled (star j) (starTwice j) (star_doubled j)]
  rcases (starTwice_facts j).2 with h | h
  · left
    rw [h]
    norm_num
  · right
    rw [h]
    norm_num

theorem rOut_one : rOut 1 = 13 / 10 := by norm_num [rOut]

theorem star_mem_specStar (j : Fin 14) : toE3 (star j) ∈ specStar 1 := by
  have hf := (starTwice_facts j).1
  refine ⟨?_, ?_, ?_⟩
  · rw [dilate_one]
    exact bccUnit_of_doubled (starTwice j) hf.1 hf.2 (fun i => star_doubled j i)
  · rw [norm_toE3]
    apply Real.sqrt_pos.mpr
    rcases sq_star j with h | h <;> rw [h] <;> norm_num
  · rw [rOut_one, norm_toE3_lt _ (by norm_num)]
    rcases sq_star j with h | h <;> rw [h] <;> norm_num

theorem specStar_one_sub {e : E3} (he : e ∈ specStar 1) : ∃ j : Fin 14, toE3 (star j) = e := by
  obtain ⟨hB, hpos, hlt⟩ := he
  rw [dilate_one] at hB
  obtain ⟨w, h01, h12, hw⟩ := bccUnit_doubled hB
  obtain ⟨v, rfl⟩ := exists_toE3 e
  have hsq := sq_doubled v w hw
  have hlt' : sq v < (13 / 10) ^ 2 := by
    rw [rOut_one, norm_toE3_lt _ (by norm_num)] at hlt
    exact hlt
  have hpos' : 0 < sq v := by
    rw [norm_toE3] at hpos
    exact Real.sqrt_pos.mp hpos
  rw [hsq] at hlt' hpos'
  have hpos'' : 0 < w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
    have : (0 : ℝ) < ((w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  have hle : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 ≤ 6 := by
    have : ((w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 : ℤ) : ℝ) < 7 := by nlinarith
    have h7 : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 < 7 := by exact_mod_cast this
    omega
  have b0 : -2 ≤ w 0 ∧ w 0 ≤ 2 := by
    have hs : w 0 ^ 2 ≤ 6 := by nlinarith [sq_nonneg (w 1), sq_nonneg (w 2)]
    constructor <;> nlinarith
  have b1 : -2 ≤ w 1 ∧ w 1 ≤ 2 := by
    have hs : w 1 ^ 2 ≤ 6 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 2)]
    constructor <;> nlinarith
  have b2 : -2 ≤ w 2 ∧ w 2 ≤ 2 := by
    have hs : w 2 ^ 2 ≤ 6 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    constructor <;> nlinarith
  obtain ⟨j, hj0, hj1, hj2⟩ := doubled_star_int (w 0) (w 1) (w 2) b0 b1 b2 h01 h12 hpos'' hle
  have hw' : ∀ i, v i = (w i : ℝ) / 2 := hw
  refine ⟨j, congrArg toE3 (funext fun i => ?_)⟩
  rw [star_doubled j i, hw' i]
  fin_cases i
  · show (starTwice j 0 : ℝ) / 2 = (w 0 : ℝ) / 2
    rw [hj0]
  · show (starTwice j 1 : ℝ) / 2 = (w 1 : ℝ) / 2
    rw [hj1]
  · show (starTwice j 2 : ℝ) / 2 = (w 2 : ℝ) / 2
    rw [hj2]

/-- The star of Spec at unit length is the interface's fourteen labels. -/
theorem specStar_one : specStar 1 = Set.range (fun j => toE3 (star j)) := by
  ext e
  constructor
  · intro he
    exact specStar_one_sub he
  · rintro ⟨j, rfl⟩
    exact star_mem_specStar j

/-- The labelling of the unit star by the interface's labels. -/
def label1 : Fin 14 ≃ ↥(specStar 1) :=
  Equiv.ofBijective (fun j => ⟨toE3 (star j), star_mem_specStar j⟩)
    ⟨fun j k h => star_injective (toE3_injective (congrArg Subtype.val h)),
     fun e => by
       obtain ⟨j, hj⟩ := specStar_one_sub e.property
       exact ⟨j, Subtype.ext hj⟩⟩

theorem label1_apply (j : Fin 14) : (label1 j : E3) = toE3 (star j) := rfl

/-! ### The defect at unit length -/

theorem weight_one {v : Vec} (hv : sq v < (13 / 10) ^ 2) :
    specWeight 1 ‖toE3 v‖ = annularWeight v := by
  have hr : Real.sqrt (sq v) < 13 / 10 := by
    rw [Real.sqrt_lt' (by norm_num)]
    exact hv
  unfold specWeight annularWeight
  rw [norm_toE3, rOut_one]
  have hin : rIn 1 = 6 / 5 := by norm_num [rIn, sStar]
  rw [hin, show (13 / 10 - Real.sqrt (sq v)) / (13 / 10 - 6 / 5) = 13 - 10 * Real.sqrt (sq v) by ring]
  rw [max_eq_right]
  exact le_min (by norm_num) (by linarith)

/-- The interface's lifts as a subset of Euclidean space. -/
def liftEquiv (Y : Set Vec) : ↥Y ≃ ↥(toE3 '' Y) := Equiv.Set.image toE3 Y toE3_injective

/-- An interface trial as an injection of the Spec star. -/
def specOfTrial {Y : Set Vec} (σ : Fin 14 ↪ ↥Y) : ↥(specStar 1) ↪ ↥(toE3 '' Y) :=
  (label1.symm.toEmbedding.trans σ).trans (liftEquiv Y).toEmbedding

/-- A Spec injection as an interface trial. -/
def trialOfSpec {Y : Set Vec} (τ : ↥(specStar 1) ↪ ↥(toE3 '' Y)) : Fin 14 ↪ ↥Y :=
  (label1.toEmbedding.trans τ).trans (liftEquiv Y).symm.toEmbedding

theorem specOfTrial_trialOfSpec {Y : Set Vec} (τ : ↥(specStar 1) ↪ ↥(toE3 '' Y)) :
    specOfTrial (trialOfSpec τ) = τ := by
  ext e
  simp [specOfTrial, trialOfSpec]

theorem specOfTrial_apply {Y : Set Vec} (σ : Fin 14 ↪ ↥Y) (j : Fin 14) :
    (specOfTrial σ (label1 j) : E3) = toE3 (σ j : Vec) := by
  simp [specOfTrial, liftEquiv]

theorem range_specOfTrial {Y : Set Vec} (σ : Fin 14 ↪ ↥Y) :
    Set.range (fun e => (specOfTrial σ e : E3)) = toE3 '' Set.range (fun j => (σ j : Vec)) := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨j, rfl⟩ := label1.surjective e
    exact ⟨σ j, ⟨j, rfl⟩, (specOfTrial_apply σ j).symm⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨label1 j, specOfTrial_apply σ j⟩

theorem unmatched_eq {Y : Set Vec} (hY : Y.Finite) (hcut : ∀ v ∈ Y, sq v < (13 / 10) ^ 2)
    (σ : Fin 14 ↪ ↥Y) :
    (∑ᶠ y ∈ toE3 '' Y \ Set.range (fun e => (specOfTrial σ e : E3)), specWeight 1 ‖y‖) =
      ∑' v : ↥Y, if v ∈ Set.range σ then 0 else annularWeight v.val := by
  let R : Set Vec := Set.range (fun j => (σ j : Vec))
  have hdiff : toE3 '' Y \ Set.range (fun e => (specOfTrial σ e : E3)) = toE3 '' (Y \ R) := by
    rw [range_specOfTrial, Set.image_sdiff toE3_injective]
  rw [hdiff, finsum_mem_image toE3_injective.injOn]
  have hw : (∑ᶠ v ∈ Y \ R, specWeight 1 ‖toE3 v‖) = ∑ᶠ v ∈ Y \ R, annularWeight v :=
    finsum_mem_congr rfl (fun v hv => weight_one (hcut v hv.1))
  rw [hw]
  have hfin : Finite ↥Y := hY.to_subtype
  rw [tsum_eq_finsum (Set.toFinite _)]
  have hmem (v : ↥Y) : v ∈ Set.range σ ↔ v.val ∈ R := by
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, Subtype.ext hj⟩
  have hset : (∑ᶠ v : ↥Y, (if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val)) =
      ∑ᶠ x ∈ Y, (if x ∈ R then (0 : ℝ) else annularWeight x) := by
    rw [← finsum_set_coe_eq_finsum_mem Y]
    apply finsum_congr
    intro v
    simp only [hmem]
  rw [hset, finsum_mem_def, finsum_mem_def]
  congr 1
  funext x
  by_cases hxY : x ∈ Y <;> by_cases hxR : x ∈ R <;>
    simp [Set.indicator, hxY, hxR]

/-- The Spec cost of the corresponding injection is the interface's trial cost
divided by `25`. -/
theorem cost_specOfTrial {Y : Set Vec} (hY : Y.Finite) (hcut : ∀ v ∈ Y, sq v < (13 / 10) ^ 2)
    (R : Mat) (σ : Fin 14 ↪ ↥Y) :
    25 * specCost 1 R (specOfTrial σ) = defectTrial R σ := by
  unfold specCost defectTrial
  rw [unmatched_eq hY hcut σ]
  have hsum : (∑ᶠ e : ↥(specStar 1), ‖(specOfTrial σ e : E3) - transform R e‖ ^ 2) =
      ∑ j, sq ((σ j : Vec) - R.mulVec (star j)) := by
    rw [← finsum_comp_equiv label1, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro j _
    rw [specOfTrial_apply, label1_apply, transform_toE3, ← toE3_sub, norm_toE3_sq]
  rw [hsum]
  norm_num [sStar]
  ring

theorem toReal_min_eq {m : ℝ≥0∞} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlow : ENNReal.ofReal c ≤ m) (hup : c = 1 ∨ m ≤ ENNReal.ofReal c) :
    (min 1 m).toReal = c := by
  have h1 : min 1 m = ENNReal.ofReal c := by
    apply le_antisymm
    · rcases hup with h | h
      · rw [h, ENNReal.ofReal_one]
        exact min_le_left _ _
      · exact min_le_of_right_le h
    · exact le_min (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc1) hlow
  rw [h1, ENNReal.toReal_ofReal hc0]

theorem div_sStar_sq (x : ℝ≥0∞) : x / ENNReal.ofReal (sStar ^ 2) = 25 * x := by
  have h : ENNReal.ofReal (sStar ^ 2) = (25 : ℝ≥0∞)⁻¹ := by
    rw [show sStar ^ 2 = (25 : ℝ)⁻¹ by norm_num [sStar], ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h, div_eq_mul_inv, inv_inv, mul_comm]

theorem ofReal_25 (c : ℝ) : 25 * ENNReal.ofReal (c / 25) = ENNReal.ofReal c := by
  rw [show (25 : ℝ≥0∞) = ENNReal.ofReal 25 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem encard_ge_of_embedding {Y : Set Vec} (σ : Fin 14 ↪ ↥Y) : 14 ≤ (toE3 '' Y).encard := by
  rw [toE3_injective.encard_image]
  have hinj : Function.Injective (fun j => (σ j : Vec)) :=
    fun a b h => σ.injective (Subtype.ext h)
  have hsub : Set.range (fun j => (σ j : Vec)) ⊆ Y := by
    rintro _ ⟨j, rfl⟩
    exact (σ j).property
  calc (14 : ℕ∞) = (Set.range (fun j => (σ j : Vec))).encard := by
        rw [hinj.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
        rfl
    _ ≤ Y.encard := Set.encard_le_encard hsub

/-- Spec's defect of a finite lift set inside the cutoff, at unit length, is the
interface's capped defect. -/
theorem specDefect_one (Y : Set Vec) (hY : Y.Finite) (hcut : ∀ v ∈ Y, sq v < (13 / 10) ^ 2) :
    specDefect 1 (toE3 '' Y) = cappedDefect Y := by
  unfold specDefect
  rw [div_sStar_sq]
  obtain ⟨hc0, hc1⟩ := cappedDefect_range Y
  apply toReal_min_eq hc0 hc1
  · unfold specStrain
    split_ifs with hcard
    · rw [ENNReal.mul_top (by norm_num)]
      exact le_top
    · have key : ENNReal.ofReal (cappedDefect Y / 25) ≤
          ⨅ (R : M3) (_ : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
            (τ : ↥(specStar 1) ↪ ↥(toE3 '' Y)), ENNReal.ofReal (specCost 1 R τ) := by
        refine le_iInf fun R => le_iInf fun hR => le_iInf fun τ => ?_
        apply ENNReal.ofReal_le_ofReal
        have h := cappedDefect_le_trial R ((mem_SO3_iff R).mp hR) (trialOfSpec τ)
        rw [← cost_specOfTrial hY hcut R (trialOfSpec τ), specOfTrial_trialOfSpec] at h
        linarith
      calc ENNReal.ofReal (cappedDefect Y) = 25 * ENNReal.ofReal (cappedDefect Y / 25) :=
            (ofReal_25 _).symm
        _ ≤ _ := by gcongr
  · rcases Set.mem_insert_iff.mp (cappedDefect_mem hY) with h1 | ⟨R, hR, σ, hσ⟩
    · exact Or.inl h1
    · right
      have hcard : ¬ (toE3 '' Y).encard < 14 := not_lt.mpr (encard_ge_of_embedding σ)
      unfold specStrain
      rw [ite_eq_right hcard]
      have hle : (⨅ (R : M3) (_ : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
            (τ : ↥(specStar 1) ↪ ↥(toE3 '' Y)), ENNReal.ofReal (specCost 1 R τ)) ≤
          ENNReal.ofReal (specCost 1 R (specOfTrial σ)) :=
        iInf_le_of_le R (iInf_le_of_le ((mem_SO3_iff R).mpr hR) (iInf_le _ (specOfTrial σ)))
      have hcost : specCost 1 R (specOfTrial σ) = cappedDefect Y / 25 := by
        rw [hσ, ← cost_specOfTrial hY hcut R σ]
        ring
      calc 25 * (⨅ (R : M3) (_ : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
            (τ : ↥(specStar 1) ↪ ↥(toE3 '' Y)), ENNReal.ofReal (specCost 1 R τ))
          ≤ 25 * ENNReal.ofReal (specCost 1 R (specOfTrial σ)) := by gcongr
        _ = ENNReal.ofReal (cappedDefect Y) := by rw [hcost, ofReal_25]

/-! ### Dilation: other densities use the dilated reference star -/

theorem rOut_mul (t a : ℝ) : rOut (t * a) = t * rOut a := by
  unfold rOut
  ring

theorem norm_inv_smul {t : ℝ} (ht : 0 < t) (y : E3) : ‖t⁻¹ • y‖ = t⁻¹ * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]

theorem lt_scaled {t r : ℝ} (ht : 0 < t) {y : E3} :
    t⁻¹ * ‖y‖ < r ↔ ‖y‖ < t * r := by
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h ht
    rwa [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at this
  · intro h
    have := mul_lt_mul_of_pos_left h (inv_pos.mpr ht)
    rwa [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul] at this

theorem specStar_dilate {a t : ℝ} (ht : 0 < t) : specStar (t * a) = dilate t (specStar a) := by
  ext x
  rw [mem_dilate ht.ne']
  constructor
  · rintro ⟨hB, hpos, hlt⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← dilate_dilate] at hB
      exact (mem_dilate ht.ne').mp hB
    · rw [norm_inv_smul ht]
      positivity
    · rw [norm_inv_smul ht, lt_scaled ht, ← rOut_mul]
      exact hlt
  · rintro ⟨hB, hpos, hlt⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← dilate_dilate]
      exact (mem_dilate ht.ne').mpr hB
    · rw [norm_inv_smul ht] at hpos
      have := mul_pos ht hpos
      rwa [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at this
    · rw [norm_inv_smul ht, lt_scaled ht, ← rOut_mul] at hlt
      exact hlt

theorem specWeight_mul {a t : ℝ} (ht : 0 < t) (r : ℝ) : specWeight (t * a) (t * r) = specWeight a r := by
  unfold specWeight rIn rOut
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    simp
  · congr 1
    field_simp

/-- The star at length unit `t a` is the star at length unit `a` dilated by `t`. -/
def starDilate {a t : ℝ} (ht : 0 < t) : ↥(specStar a) ≃ ↥(specStar (t * a)) :=
  (Equiv.Set.image (fun x : E3 => t • x) (specStar a) (smul_injective_E3 ht.ne')).trans
    (Equiv.subtypeEquivRight (fun x => Set.ext_iff.mp (specStar_dilate ht).symm x))

theorem starDilate_apply {a t : ℝ} (ht : 0 < t) (e : ↥(specStar a)) :
    ((starDilate ht e : ↥(specStar (t * a))) : E3) = t • (e : E3) := rfl

/-- Lifts dilated by `t`. -/
def liftDilate {t : ℝ} (ht : 0 < t) (Y : Set E3) : ↥Y ≃ ↥(dilate t Y) :=
  Equiv.Set.image (fun x : E3 => t • x) Y (smul_injective_E3 ht.ne')

theorem liftDilate_apply {t : ℝ} (ht : 0 < t) {Y : Set E3} (y : ↥Y) :
    ((liftDilate ht Y y : ↥(dilate t Y)) : E3) = t • (y : E3) := rfl

theorem dilated_apply {a t : ℝ} (ht : 0 < t) {Y : Set E3} (σ : ↥(specStar a) ↪ ↥Y)
    (e : ↥(specStar a)) :
    ((Equiv.embeddingCongr (starDilate (a := a) ht) (liftDilate ht Y) σ (starDilate ht e) :
      ↥(dilate t Y)) : E3) = t • (σ e : E3) := by
  show ((liftDilate ht Y) (σ ((starDilate (a := a) ht).symm (starDilate ht e))) : E3) =
    t • (σ e : E3)
  rw [Equiv.symm_apply_apply]
  rfl

theorem cost_dilate {a t : ℝ} (ht : 0 < t) {Y : Set E3} (R : M3) (σ : ↥(specStar a) ↪ ↥Y) :
    specCost (t * a) R (Equiv.embeddingCongr (starDilate (a := a) ht) (liftDilate ht Y) σ) =
      specCost a R σ := by
  let τ := Equiv.embeddingCongr (starDilate (a := a) ht) (liftDilate ht Y) σ
  have hsum : (∑ᶠ e : ↥(specStar (t * a)), ‖(τ e : E3) - transform R e‖ ^ 2) =
      t ^ 2 * ∑ᶠ e : ↥(specStar a), ‖(σ e : E3) - transform R e‖ ^ 2 := by
    rw [← finsum_comp_equiv (starDilate (a := a) ht), mul_finsum]
    apply finsum_congr
    intro e
    rw [dilated_apply ht σ e, starDilate_apply, transform_smul, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, mul_pow]
  have hrange : Set.range (fun e => (τ e : E3)) =
      (fun x : E3 => t • x) '' Set.range (fun e => (σ e : E3)) := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      obtain ⟨e', rfl⟩ := (starDilate (a := a) ht).surjective e
      exact ⟨σ e', ⟨e', rfl⟩, (dilated_apply ht σ e').symm⟩
    · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
      exact ⟨starDilate ht e, dilated_apply ht σ e⟩
  have hdiff : dilate t Y \ Set.range (fun e => (τ e : E3)) =
      (fun x : E3 => t • x) '' (Y \ Set.range (fun e => (σ e : E3))) := by
    rw [hrange, dilate, Set.image_sdiff (smul_injective_E3 ht.ne')]
  have hw : (∑ᶠ y ∈ Y \ Set.range (fun e => (σ e : E3)), specWeight (t * a) ‖t • y‖) =
      ∑ᶠ y ∈ Y \ Set.range (fun e => (σ e : E3)), specWeight a ‖y‖ := by
    apply finsum_mem_congr rfl
    intro y _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, specWeight_mul ht]
  unfold specCost
  change (t * a)⁻¹ ^ 2 * (∑ᶠ e : ↥(specStar (t * a)), ‖(τ e : E3) - transform R e‖ ^ 2) +
      sStar ^ 2 * (∑ᶠ y ∈ dilate t Y \ Set.range (fun e => (τ e : E3)), specWeight (t * a) ‖y‖) = _
  rw [hsum, hdiff, finsum_mem_image (smul_injective_E3 ht.ne').injOn, hw]
  congr 1
  rw [← mul_assoc]
  congr 1
  field_simp

theorem specStrain_dilate {a t : ℝ} (ht : 0 < t) (Y : Set E3) :
    specStrain (t * a) (dilate t Y) = specStrain a Y := by
  unfold specStrain
  have hcard : (dilate t Y).encard = Y.encard := (smul_injective_E3 ht.ne').encard_image Y
  rw [hcard]
  split_ifs
  · rfl
  · apply iInf_congr
    intro R
    apply iInf_congr
    intro _
    exact (Equiv.iInf_congr (Equiv.embeddingCongr (starDilate (a := a) ht) (liftDilate ht Y))
      (fun σ => by rw [cost_dilate ht R σ])).symm

/-- Dilating the lifts together with the length unit leaves `D` unchanged. -/
theorem specDefect_dilate {a t : ℝ} (ht : 0 < t) (Y : Set E3) :
    specDefect (t * a) (dilate t Y) = specDefect a Y := by
  unfold specDefect
  rw [specStrain_dilate ht]

theorem liftVectors_dilate {a t : ℝ} (ht : 0 < t) (X : Set E3) (x : E3) :
    liftVectors (t * a) (dilate t X) (t • x) = dilate t (liftVectors a X x) := by
  ext y
  rw [mem_dilate ht.ne']
  have hsum : t⁻¹ • (t • x + y) = x + t⁻¹ • y := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  constructor
  · rintro ⟨hy, hy0, hlt⟩
    refine ⟨?_, smul_ne_zero (inv_ne_zero ht.ne') hy0, ?_⟩
    · rw [← hsum]
      exact (mem_dilate ht.ne').mp hy
    · rw [norm_inv_smul ht, lt_scaled ht, ← rOut_mul]
      exact hlt
  · rintro ⟨hy, hy0, hlt⟩
    refine ⟨?_, fun h => hy0 (by rw [h, smul_zero]), ?_⟩
    · rw [mem_dilate ht.ne', hsum]
      exact hy
    · rw [norm_inv_smul ht, lt_scaled ht, ← rOut_mul] at hlt
      exact hlt

theorem liftVectors_toE3 (S : Set Vec) (x : Vec) :
    liftVectors 1 (toE3 '' S) (toE3 x) = toE3 '' liftedNeighbors S x := by
  ext y
  obtain ⟨v, rfl⟩ := exists_toE3 y
  rw [toE3_injective.mem_set_image]
  show (toE3 x + toE3 v ∈ toE3 '' S ∧ toE3 v ≠ 0 ∧ ‖toE3 v‖ < rOut 1) ↔
    (x + v ∈ S ∧ v ≠ 0 ∧ sq v < (13 / 10) ^ 2)
  have h0 : toE3 v ≠ 0 ↔ v ≠ 0 := by
    rw [← toE3_zero]
    exact toE3_injective.ne_iff
  rw [← toE3_add, toE3_injective.mem_set_image, rOut_one, norm_toE3_lt _ (by norm_num), h0]

/-! ### Spec's defect of a configuration -/

/-- Spec's defect at every point of a valid configuration, in units where the
conventional cube side is `s`, is the interface's `D`. -/
theorem specSiteDefect_eq (q : TwoSite) (hq : q.Valid) {x : Vec} (hx : x ∈ q.points) {s : ℝ}
    (hs : 0 < s) : specSiteDefect s (dilate s (specPoints q)) (s • toE3 x) = defect q := by
  unfold specSiteDefect
  have e1 := liftVectors_dilate (a := 1) hs (specPoints q) (toE3 x)
  rw [mul_one] at e1
  have e2 := specDefect_dilate (a := 1) hs (liftVectors 1 (specPoints q) (toE3 x))
  rw [mul_one] at e2
  rw [e1, e2, specPoints, liftVectors_toE3,
    specDefect_one _ (siteNeighbors_finite q hq hx) (fun v hv => hv.2.2)]
  exact siteDefect_of_mem q hx

/-- At the two-site theorem density: every point of the physical configuration has Spec's
defect `D`. -/
theorem spec_physical (q : TwoSite) (hq : q.Valid) {y : E3} (hy : y ∈ physPoints q) :
    specSiteDefect ac (physPoints q) y = defect q := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  exact specSiteDefect_eq q hq hx ac_positive

/-- At every other density, with the dilated reference star. -/
theorem spec_dilated (q : TwoSite) (hq : q.Valid) {t : ℝ} (ht : 0 < t) {y : E3}
    (hy : y ∈ dilate t (physPoints q)) :
    specSiteDefect (t * ac) (dilate t (physPoints q)) y = defect q := by
  rw [physPoints, dilate_dilate] at hy ⊢
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  exact specSiteDefect_eq q hq hx (mul_pos ht ac_positive)

/-- The lift sets of a valid configuration are finite at every point, so the
unmatched sums in `specCost` are finite sums. -/
theorem liftVectors_physical_finite (q : TwoSite) (hq : q.Valid) {y : E3} (hy : y ∈ physPoints q) :
    (liftVectors ac (physPoints q) y).Finite := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  have e1 := liftVectors_dilate (a := 1) ac_positive (specPoints q) (toE3 x)
  rw [mul_one] at e1
  rw [physPoints, e1, specPoints, liftVectors_toE3]
  exact ((siteNeighbors_finite q hq hx).image toE3).image _

/-! ### Translates -/

/-- Every union of two distinct translates is a translate of a union of a
lattice and a distinct translate of it, and conversely. -/
theorem twoTranslates_iff (X : Set E3) :
    TwoTranslates X ↔ ∃ (v : E3) (Y : Set E3), TwoCosetConfig Y ∧ X = (fun y => y + v) '' Y := by
  constructor
  · rintro ⟨A, a, b, hdet, hba, rfl⟩
    refine ⟨a, withTranslate (latticeOf A) (b - a), ⟨A, b - a, hdet, hba, rfl⟩, ?_⟩
    rw [withTranslate, Set.image_union, Set.image_image]
    congr 1
    apply Set.image_congr
    intro y _
    abel
  · rintro ⟨v, Y, ⟨A, τ, hdet, hτ, rfl⟩, rfl⟩
    refine ⟨A, v, τ + v, hdet, by rwa [add_sub_cancel_right], ?_⟩
    rw [withTranslate, Set.image_union, Set.image_image]
    congr 1
    apply Set.image_congr
    intro y _
    abel

theorem liftVectors_translate (a : ℝ) (X : Set E3) (x v : E3) :
    liftVectors a ((fun y => y + v) '' X) (x + v) = liftVectors a X x := by
  ext y
  constructor
  · rintro ⟨⟨z, hz, hzv⟩, h0, hlt⟩
    refine ⟨?_, h0, hlt⟩
    have e : z + v = (x + y) + v := by
      rw [show x + y + v = x + v + y by abel]
      exact hzv
    rwa [← add_right_cancel e]
  · rintro ⟨h, h0, hlt⟩
    refine ⟨⟨x + y, h, ?_⟩, h0, hlt⟩
    show x + y + v = x + v + y
    abel

/-- Spec's defect is translation covariant. -/
theorem specSiteDefect_translate (a : ℝ) (X : Set E3) (x v : E3) :
    specSiteDefect a ((fun y => y + v) '' X) (x + v) = specSiteDefect a X x := by
  unfold specSiteDefect
  rw [liftVectors_translate]

/-- Every point of a union of two distinct translates has Spec's defect `D` of a
valid configuration whose point set it translates. -/
theorem spec_translates {X : Set E3} (hX : TwoTranslates X) :
    ∃ q : TwoSite, q.Valid ∧ ∃ v : E3, X = (fun y => y + v) '' physPoints q ∧
      ∀ y ∈ X, specSiteDefect ac X y = defect q := by
  obtain ⟨v, Y, hY, rfl⟩ := (twoTranslates_iff X).mp hX
  obtain ⟨q, hq, rfl⟩ := valid_of_twoCoset hY
  refine ⟨q, hq, v, rfl, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [specSiteDefect_translate]
  exact spec_physical q hq hy

/-! ### Rigid motions -/

/-- The rigid motion `x ↦ U x + v` of an orthogonal matrix `U`. -/
def motion {U : Mat} (hU : orthogonal U) (v : E3) : E3 ≃ᵢ E3 where
  toFun x := transform U x + v
  invFun x := transform U.transpose (x - v)
  left_inv x := by
    obtain ⟨w, rfl⟩ := exists_toE3 x
    show transform U.transpose (transform U (toE3 w) + v - v) = toE3 w
    rw [add_sub_cancel_right, transform_toE3, transform_toE3, mulVec_transpose_mulVec hU]
  right_inv x := by
    show transform U (transform U.transpose (x - v)) + v = x
    obtain ⟨w, hw⟩ := exists_toE3 (x - v)
    rw [hw, transform_toE3, transform_toE3, mulVec_mulVec_transpose hU, ← hw, sub_add_cancel]
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    show dist (transform U x + v) (transform U y + v) = dist x y
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, transform_sub, norm_transform hU]

theorem transform_add_toE3 (U : Mat) (z w : Vec) :
    transform U (toE3 z) + toE3 w = toE3 (U.mulVec z + w) := rfl

/-- Mazur–Ulam in Euclidean three-space: a rigid motion is an orthogonal map
followed by a translation. -/
theorem isometry_affine (φ : E3 ≃ᵢ E3) :
    ∃ U : Mat, orthogonal U ∧ ∀ x, φ x = transform U x + φ 0 := by
  let L := φ.toRealLinearIsometryEquiv
  obtain ⟨U, hUdef⟩ : ∃ U : Mat, U = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (L.toLinearEquiv : E3 →ₗ[ℝ] E3) := ⟨_, rfl⟩
  have hmem := LinearIsometryEquiv.toMatrix_mem_unitaryGroup L (EuclideanSpace.basisFun (Fin 3) ℝ)
    (EuclideanSpace.basisFun (Fin 3) ℝ)
  rw [← hUdef] at hmem
  have h := Matrix.toLin_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (L.toLinearEquiv : E3 →ₗ[ℝ] E3)
  rw [← hUdef, ← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h
  have hL : ∀ x, L x = transform U x := by
    intro x
    show L x = Matrix.toEuclideanLin U x
    rw [h]
    rfl
  refine ⟨U, ?_, fun x => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at hmem
    exact hmem
  · rw [← hL, IsometryEquiv.toRealLinearIsometryEquiv_apply, sub_add_cancel]

/-- For a centrosymmetric point set, a translated proper rotation and a rigid
motion give the same copies. -/
theorem rigidCopy_iff_rigidImage (S T : Set Vec) (hT : ∀ x ∈ T, -x ∈ T) :
    rigidCopy S T ↔ RigidImage (toE3 '' S) (toE3 '' T) := by
  constructor
  · rintro ⟨v, U, hU, rfl⟩
    refine ⟨motion hU.1 (toE3 v), ?_⟩
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      exact ⟨toE3 z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨U.mulVec z + v, ⟨U.mulVec z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨φ, hφ⟩
    obtain ⟨U, hU, hφU⟩ := isometry_affine φ
    obtain ⟨w, hw⟩ := exists_toE3 (φ 0)
    have hS : S = translate w (U.mulVec '' T) := by
      apply Set.image_injective.mpr toE3_injective
      rw [hφ]
      ext y
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨U.mulVec z + w, ⟨U.mulVec z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
        rw [hφU, hw, transform_add_toE3]
      · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
        refine ⟨toE3 z, ⟨z, hz, rfl⟩, ?_⟩
        rw [hφU, hw, transform_add_toE3]
    rcases orthogonal_det hU with hd | hd
    · exact ⟨w, U, ⟨hU, hd⟩, hS⟩
    · refine ⟨w, -U, proper_neg_of_det hU hd, ?_⟩
      rw [hS]
      congr 1
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨-z, hT z hz, by rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨-z, hT z hz, by rw [Matrix.mulVec_neg, Matrix.neg_mulVec]⟩

theorem bcc_points_neg (x : Vec) (hx : x ∈ bcc.points) : -x ∈ bcc.points := by
  rw [← Constants.bcc_primitive_points] at hx ⊢
  exact lattice_neg_mem _ hx

theorem fcc_points_neg (x : Vec) (hx : x ∈ fcc.points) : -x ∈ fcc.points := by
  rw [← Constants.fcc_primitive_points] at hx ⊢
  exact lattice_neg_mem _ hx

/-- `IsBCC`: the point set is a rigid image (reflections allowed) of the
conventional BCC lattice. -/
theorem isBCC_iff (q : TwoSite) : IsBCC q ↔ RigidImage (specPoints q) bccUnit := by
  rw [bccUnit_eq]
  exact rigidCopy_iff_rigidImage q.points bcc.points bcc_points_neg

/-- `IsFCC`: the point set is a rigid image of the conventional FCC lattice at
the same density. -/
theorem isFCC_iff (q : TwoSite) : IsFCC q ↔ RigidImage (specPoints q) fccUnit := by
  rw [fccUnit_eq]
  exact rigidCopy_iff_rigidImage q.points fcc.points fcc_points_neg

/-- Conjugating a rigid motion by a dilation gives a rigid motion. -/
def conjDilate {t : ℝ} (ht : 0 < t) (φ : E3 ≃ᵢ E3) : E3 ≃ᵢ E3 where
  toFun x := t • φ (t⁻¹ • x)
  invFun x := t • φ.symm (t⁻¹ • x)
  left_inv x := by
    simp [smul_smul, ht.ne']
  right_inv x := by
    simp [smul_smul, ht.ne']
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    show dist (t • φ (t⁻¹ • x)) (t • φ (t⁻¹ • y)) = dist x y
    rw [dist_smul₀, IsometryEquiv.dist_eq, dist_smul₀, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ht, abs_of_pos (inv_pos.mpr ht), ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

theorem rigidImage_dilate {t : ℝ} (ht : 0 < t) {X Y : Set E3} (h : RigidImage X Y) :
    RigidImage (dilate t X) (dilate t Y) := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨conjDilate ht φ, ?_⟩
  unfold dilate
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro y _
  show t • φ y = t • φ (t⁻¹ • (t • y))
  rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

theorem rigidImage_dilate_iff {t : ℝ} (ht : 0 < t) {X Y : Set E3} :
    RigidImage (dilate t X) (dilate t Y) ↔ RigidImage X Y := by
  constructor
  · intro h
    have h' := rigidImage_dilate (inv_pos.mpr ht) h
    rwa [dilate_dilate, dilate_dilate, inv_mul_cancel₀ ht.ne', dilate_one, dilate_one] at h'
  · exact rigidImage_dilate ht

/-- In physical units: BCC at Wigner–Seitz radius one. -/
theorem isBCC_iff_physical (q : TwoSite) :
    IsBCC q ↔ RigidImage (physPoints q) (dilate ac bccUnit) := by
  rw [isBCC_iff, physPoints, rigidImage_dilate_iff ac_positive]

theorem isFCC_iff_physical (q : TwoSite) :
    IsFCC q ↔ RigidImage (physPoints q) (dilate ac fccUnit) := by
  rw [isFCC_iff, physPoints, rigidImage_dilate_iff ac_positive]

theorem rigidImage_refl (X : Set E3) : RigidImage X X :=
  ⟨IsometryEquiv.refl E3, (Set.image_id X).symm⟩

theorem rigidImage_symm {X Y : Set E3} (h : RigidImage X Y) : RigidImage Y X := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.symm, ?_⟩
  rw [Set.image_image]
  simp

theorem rigidImage_trans {X Y Z : Set E3} (h1 : RigidImage X Y) (h2 : RigidImage Y Z) :
    RigidImage X Z := by
  obtain ⟨φ, rfl⟩ := h1
  obtain ⟨ψ, rfl⟩ := h2
  refine ⟨ψ.trans φ, ?_⟩
  rw [Set.image_image]
  rfl

/-- A translate of `X` is a rigid image of `X`. -/
theorem rigidImage_translate (v : E3) (X : Set E3) : RigidImage ((fun y => y + v) '' X) X :=
  ⟨IsometryEquiv.addRight v, rfl⟩

/-! ### Registration -/

theorem indexTwoBasis_iff (B : Mat) (f₀ : Vec) : IndexTwoBasis B f₀ ↔ IndexTwoBCC B f₀ := by
  have hbcc : (bccUnit = withTranslate (latticeOf B) (transform B (WithLp.toLp 2 f₀))) ↔
      bcc.points = lattice B ∪ translate (B.mulVec f₀) (lattice B) := by
    rw [bccUnit_eq, specPoints, latticeOf_eq, show WithLp.toLp 2 f₀ = toE3 f₀ from rfl,
      transform_toE3, withTranslate_eq]
    exact (Set.image_injective.mpr toE3_injective).eq_iff
  have hhalf : (∃ m : Fin 3 → ℤ, ∀ i, 2 * f₀ i = m i) ↔
      ∃ n : IntVec, (2 : ℝ) • f₀ = castVec n := by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, funext fun i => by simp [hm i, castVec]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, fun i => by simpa [castVec] using congrFun hn i⟩
  have hnot : (∀ m : Fin 3 → ℤ, ∃ i, f₀ i ≠ m i) ↔ ∀ n : IntVec, f₀ ≠ castVec n := by
    constructor
    · intro h n hn
      obtain ⟨i, hi⟩ := h n
      exact hi (congrFun hn i)
    · intro h m
      by_contra! hc
      exact h m (funext hc)
  constructor
  · rintro ⟨hdet, hh, hn, hb⟩
    refine ⟨hdet, ⟨hhalf.mp hh, hnot.mp hn⟩, ?_, hbcc.mp hb⟩
    rintro ⟨m, hm⟩
    have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one)
    exact hnot.mp hn m (Matrix.mulVec_injective_of_isUnit hu hm).symm
  · rintro ⟨hdet, ⟨hh, hn⟩, _, hb⟩
    exact ⟨hdet, hhalf.mpr hh, hnot.mpr hn, hbcc.mpr hb⟩

theorem registeredBound_iff (R : Mat) (f : Vec) (D : ℝ) :
    RegisteredBound R f D ↔ ∃ (B : Mat) (f₀ : Vec) (n : IntVec) (U : Mat), IndexTwoBCC B f₀ ∧
      proper U ∧ 100 * frobSq (R * B⁻¹ - U) + 200 * sq (R.mulVec (f - f₀ - castVec n)) ≤ D := by
  have hnorm (f₀ : Vec) (n : IntVec) :
      ‖transform R (WithLp.toLp 2 (f - f₀ - fun i => (n i : ℝ)))‖ ^ 2 =
        sq (R.mulVec (f - f₀ - castVec n)) := by
    rw [show WithLp.toLp 2 (f - f₀ - fun i => (n i : ℝ)) = toE3 (f - f₀ - castVec n) from rfl,
      transform_toE3, norm_toE3_sq]
  have hfrob (B U : Mat) : (∑ i, ∑ j, ((R * B⁻¹) i j - U i j) ^ 2) = frobSq (R * B⁻¹ - U) := rfl
  unfold RegisteredBound
  simp only [hnorm, hfrob, indexTwoBasis_iff, mem_SO3_iff]

/-- The interface's `Registration` is inequality (3.10) in a reduced frame. -/
theorem registration_iff (q : TwoSite) :
    Registration q ↔ ∃ p, ReducedRepresentative q p ∧
      RegisteredBound (chartBasis p) (chartPoint p).offset (defect q) := by
  unfold Registration
  simp only [registeredBound_iff]

end BccSharp.Coulomb.SpecBridge
