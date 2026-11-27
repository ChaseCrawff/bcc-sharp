import BccSharp.TwoSite.GlobalInputs
import BccSharp.TwoSite.ExpectedStatement

set_option autoImplicit false

/-! Invariances of the actual capped defect `D` and of the energy that the
interface `Statement` does not state.

* Orthogonal images: `cappedDefect_proper_image`, `cappedDefect_neg_image`
  and `cappedDefect_orthogonal_image`. The inversion case relabels a trial by
  `e ↦ −y_{−e}` (`invertTrial`, `defectTrial_inversion`): the reference star is
  centrosymmetric and the annular weight is even.
* Either-site identity: the inversion `x ↦ t − x` about the midpoint of the
  two sites `0` and `t = B f` maps the point set onto itself
  (`points_inversion`) and the lifts of site `t` onto the negated lifts of
  site `0` (`liftedNeighbors_second_site`). Hence both sites have the same
  defect (`siteDefect_second_site`), and so does every point of the
  configuration (`siteDefect_of_mem`).
* Basis change, wrapping, coset interchange and rotation of the frame:
  `defect_rebase`, `defect_wrap`, `defect_swap`, `defect_rotate`.
* Rigid motions, reflections included: `defect_of_isometric`, and for the
  energy of valid configurations `energy_of_isometric` (through
  `energy_of_points_eq`: valid configurations with one point set have one
  energy).
* Finite-index repetition: the normalized lifted neighbours of every site of
  a commensurate supercell are those of the two-site configuration
  (`repetition_liftedNeighbors`), so every site has the defect `D`
  (`repetition_siteDefect`).
* Density scaling: `unitSiteDefect_dilate`; the physical defect at the two-site theorem
  density is `D` (`unitSiteDefect_physical`).
* Finiteness inside the cutoff at every site (`siteNeighbors_finite`),
  attainment (`defect_attained`, `defect_eq_min`) and saturation when fewer
  than fourteen lifts exist (`defect_eq_one_of_few`). -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.DefectInvariance
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.KZ
open BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.CompactCover

/-! ### Orthogonal matrices -/

/-- An orthogonal matrix, proper or improper. -/
def orthogonal (U : Mat) : Prop := U.transpose * U = 1

theorem orthogonal_mul_transpose {U : Mat} (hU : orthogonal U) : U * U.transpose = 1 :=
  mul_eq_one_comm.mp hU

theorem proper_transpose' {U : Mat} (hU : proper U) : proper U.transpose :=
  ⟨by rw [Matrix.transpose_transpose]; exact orthogonal_mul_transpose hU.1,
   by rw [Matrix.det_transpose]; exact hU.2⟩

theorem proper_mul' {U V : Mat} (hU : proper U) (hV : proper V) : proper (U * V) := by
  refine ⟨?_, by rw [Matrix.det_mul, hU.2, hV.2, one_mul]⟩
  rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc U.transpose U V, hU.1, one_mul, hV.1]

theorem orthogonal_det {U : Mat} (hU : orthogonal U) : U.det = 1 ∨ U.det = -1 := by
  have h := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have h2 : (U.det - 1) * (U.det + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    linarith
  · right
    linarith

theorem orthogonal_neg {U : Mat} (hU : orthogonal U) : orthogonal (-U) := by
  unfold orthogonal
  rw [Matrix.transpose_neg, neg_mul_neg]
  exact hU

theorem proper_neg_of_det {U : Mat} (hU : orthogonal U) (hd : U.det = -1) : proper (-U) := by
  refine ⟨orthogonal_neg hU, ?_⟩
  rw [Matrix.det_neg, Fintype.card_fin, hd]
  norm_num

theorem mulVec_transpose_mulVec {U : Mat} (hU : orthogonal U) (v : Vec) :
    U.transpose.mulVec (U.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem mulVec_mulVec_transpose {U : Mat} (hU : orthogonal U) (v : Vec) :
    U.mulVec (U.transpose.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, orthogonal_mul_transpose hU, Matrix.one_mulVec]

theorem orthogonal_injective {U : Mat} (hU : orthogonal U) : Function.Injective U.mulVec := by
  intro x y h
  have e := congrArg U.transpose.mulVec h
  rwa [mulVec_transpose_mulVec hU, mulVec_transpose_mulVec hU] at e

theorem sq_neg_vector (v : Vec) : sq (-v) = sq v := by
  simp [sq]

theorem annularWeight_orthogonal {U : Mat} (hU : orthogonal U) (v : Vec) :
    annularWeight (U.mulVec v) = annularWeight v := by
  simp only [annularWeight, sq_orthogonal hU]

theorem annularWeight_neg (v : Vec) : annularWeight (-v) = annularWeight v := by
  simp only [annularWeight, sq_neg_vector]

/-! ### The capped defect of an orthogonal image -/

theorem candidates_proper_image (U : Mat) (hU : proper U) (Y : Set Vec) :
    defectCandidates Y ⊆ defectCandidates (U.mulVec '' Y) := by
  intro c hc
  rcases Set.mem_insert_iff.mp hc with rfl | ⟨O, hO, σ, rfl⟩
  · exact Set.mem_insert _ _
  apply Set.mem_insert_of_mem
  let e : ↥Y ≃ ↥(U.mulVec '' Y) := Equiv.Set.image U.mulVec Y (orthogonal_injective hU.1)
  refine ⟨U * O, proper_mul' hU hO, σ.trans e.toEmbedding, ?_⟩
  unfold defectTrial
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    change sq ((σ j : Vec) - O.mulVec (star j)) =
      sq (U.mulVec (σ j : Vec) - (U * O).mulVec (star j))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, sq_orthogonal hU.1]
  · conv_rhs => rw [← e.tsum_eq]
    apply tsum_congr
    intro v
    have hr : (e v ∈ Set.range (σ.trans e.toEmbedding)) ↔ v ∈ Set.range σ := by
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, e.injective hj⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, rfl⟩
    by_cases hv : v ∈ Set.range σ
    · rw [ite_eq_left hv, ite_eq_left (hr.mpr hv)]
    · rw [ite_eq_right hv, ite_eq_right (fun h => hv (hr.mp h))]
      change annularWeight v.val = annularWeight (U.mulVec v.val)
      rw [annularWeight_orthogonal hU.1]

/-- The inversion relabelling of a trial: the lift matched to the label `e` is
`−y_{−e}`, where `y` is the original assignment. -/
def invertTrial {Y : Set Vec} (σ : Fin 14 ↪ ↥Y) : Fin 14 ↪ ↥((fun v : Vec => -v) '' Y) :=
  (negEquiv.toEmbedding.trans σ).trans
    (Equiv.Set.image (fun v : Vec => -v) Y neg_injective).toEmbedding

theorem invertTrial_apply {Y : Set Vec} (σ : Fin 14 ↪ ↥Y) (j : Fin 14) :
    (invertTrial σ j : Vec) = -(σ (negLabel j) : Vec) := rfl

/-- Inversion with the relabelling `e ↦ −y_{−e}` preserves every trial cost. -/
theorem defectTrial_inversion {Y : Set Vec} (U : Mat) (σ : Fin 14 ↪ ↥Y) :
    defectTrial U (invertTrial σ) = defectTrial U σ := by
  unfold defectTrial
  congr 1
  · congr 1
    have h (j : Fin 14) : sq ((invertTrial σ j : Vec) - U.mulVec (star j)) =
        sq ((σ (negEquiv j) : Vec) - U.mulVec (star (negEquiv j))) := by
      rw [invertTrial_apply]
      change sq (-(σ (negLabel j) : Vec) - U.mulVec (star j)) =
        sq ((σ (negLabel j) : Vec) - U.mulVec (star (negLabel j)))
      rw [star_negLabel, Matrix.mulVec_neg,
        show -(σ (negLabel j) : Vec) - U.mulVec (star j) =
          -((σ (negLabel j) : Vec) - -U.mulVec (star j)) by abel, sq_neg_vector]
    rw [Finset.sum_congr rfl (fun j _ => h j)]
    exact negEquiv.sum_comp (fun j => sq ((σ j : Vec) - U.mulVec (star j)))
  · let e : ↥Y ≃ ↥((fun v : Vec => -v) '' Y) := Equiv.Set.image (fun v : Vec => -v) Y neg_injective
    conv_lhs => rw [← e.tsum_eq]
    apply tsum_congr
    intro v
    have hr : (e v ∈ Set.range (invertTrial σ)) ↔ v ∈ Set.range σ := by
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨negLabel j, e.injective hj⟩
      · rintro ⟨j, rfl⟩
        refine ⟨negLabel j, ?_⟩
        apply Subtype.ext
        rw [invertTrial_apply, negLabel_negLabel]
        rfl
    by_cases hv : v ∈ Set.range σ
    · rw [ite_eq_left hv, ite_eq_left (hr.mpr hv)]
    · rw [ite_eq_right hv, ite_eq_right (fun h => hv (hr.mp h))]
      change annularWeight (-v.val) = annularWeight v.val
      exact annularWeight_neg v.val

theorem candidates_neg_image (Y : Set Vec) :
    defectCandidates Y ⊆ defectCandidates ((fun v : Vec => -v) '' Y) := by
  intro c hc
  rcases Set.mem_insert_iff.mp hc with rfl | ⟨O, hO, σ, rfl⟩
  · exact Set.mem_insert _ _
  exact Set.mem_insert_of_mem _ ⟨O, hO, invertTrial σ, (defectTrial_inversion O σ).symm⟩

theorem neg_image_neg_image (Y : Set Vec) :
    (fun v : Vec => -v) '' ((fun v : Vec => -v) '' Y) = Y := by
  rw [Set.image_image]
  simp

theorem transpose_image_image {U : Mat} (hU : orthogonal U) (Y : Set Vec) :
    U.transpose.mulVec '' (U.mulVec '' Y) = Y := by
  rw [Set.image_image]
  simp [mulVec_transpose_mulVec hU]

/-- Inversion of the neighbour set preserves the capped defect. -/
theorem cappedDefect_neg_image (Y : Set Vec) :
    cappedDefect ((fun v : Vec => -v) '' Y) = cappedDefect Y := by
  unfold cappedDefect
  congr 1
  apply Set.Subset.antisymm
  · have h := candidates_neg_image ((fun v : Vec => -v) '' Y)
    rwa [neg_image_neg_image] at h
  · exact candidates_neg_image Y

/-- A proper rotation of the neighbour set preserves the capped defect. -/
theorem cappedDefect_proper_image (U : Mat) (hU : proper U) (Y : Set Vec) :
    cappedDefect (U.mulVec '' Y) = cappedDefect Y := by
  unfold cappedDefect
  congr 1
  apply Set.Subset.antisymm
  · have h := candidates_proper_image U.transpose (proper_transpose' hU) (U.mulVec '' Y)
    rwa [transpose_image_image hU.1] at h
  · exact candidates_proper_image U hU Y

/-- Every orthogonal image of the neighbour set, reflections included, has the
same capped defect. -/
theorem cappedDefect_orthogonal_image (U : Mat) (hU : orthogonal U) (Y : Set Vec) :
    cappedDefect (U.mulVec '' Y) = cappedDefect Y := by
  rcases orthogonal_det hU with hd | hd
  · exact cappedDefect_proper_image U ⟨hU, hd⟩ Y
  · have himg : U.mulVec '' Y = (fun v : Vec => -v) '' ((-U).mulVec '' Y) := by
      rw [Set.image_image]
      apply Set.image_congr
      intro v _
      rw [Matrix.neg_mulVec, neg_neg]
    rw [himg, cappedDefect_neg_image, cappedDefect_proper_image _ (proper_neg_of_det hU hd)]

/-! ### Lifted neighbours under orthogonal maps -/

theorem liftedNeighbors_orthogonal {U : Mat} (hU : orthogonal U) (S : Set Vec) (x : Vec) :
    liftedNeighbors (U.mulVec '' S) (U.mulVec x) = U.mulVec '' liftedNeighbors S x := by
  ext v
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hv0, hlen⟩
    refine ⟨U.transpose.mulVec v, ⟨?_, ?_, ?_⟩, mulVec_mulVec_transpose hU v⟩
    · have e : x + U.transpose.mulVec v = y := by
        apply orthogonal_injective hU
        rw [Matrix.mulVec_add, mulVec_mulVec_transpose hU, hxy]
      rw [e]
      exact hy
    · intro h0
      apply hv0
      rw [← mulVec_mulVec_transpose hU v, h0, Matrix.mulVec_zero]
    · rwa [← sq_orthogonal hU (U.transpose.mulVec v), mulVec_mulVec_transpose hU]
  · rintro ⟨w, ⟨hw, hw0, hlen⟩, rfl⟩
    refine ⟨⟨x + w, hw, by rw [Matrix.mulVec_add]⟩, ?_, ?_⟩
    · intro h0
      apply hw0
      apply orthogonal_injective hU
      rw [h0, Matrix.mulVec_zero]
    · rwa [sq_orthogonal hU]

/-! ### Translates and point sets -/

theorem translate_union (v : Vec) (A B : Set Vec) :
    translate v (A ∪ B) = translate v A ∪ translate v B := by
  ext x
  constructor
  · rintro ⟨y, hy | hy, rfl⟩
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, Or.inl hy, rfl⟩
    · exact ⟨y, Or.inr hy, rfl⟩

theorem translate_translate (u v : Vec) (A : Set Vec) :
    translate u (translate v A) = translate (v + u) A := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by abel⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z + v, ⟨z, hz, rfl⟩, by abel⟩

theorem translate_zero (A : Set Vec) : translate 0 A = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x, hx, by simp⟩

theorem translate_lattice_add (B : Mat) (t a : Vec) (ha : a ∈ lattice B) :
    translate (t + a) (lattice B) = translate t (lattice B) :=
  translate_period_add (periodGroup B) t a ha

theorem translate_lattice (B : Mat) {y : Vec} (hy : y ∈ lattice B) :
    translate y (lattice B) = lattice B := by
  have h := translate_lattice_add B 0 y hy
  rwa [zero_add, translate_zero] at h

theorem lattice_neg_mem (B : Mat) {y : Vec} (hy : y ∈ lattice B) : -y ∈ lattice B :=
  (periodGroup B).neg_mem hy

/-- A period of the configuration translates its point set onto itself. -/
theorem points_translate_period (q : TwoSite) {y : Vec} (hy : y ∈ lattice q.basis) :
    translate y q.points = q.points := by
  show translate y (lattice q.basis ∪ translate (q.basis.mulVec q.offset) (lattice q.basis)) =
    lattice q.basis ∪ translate (q.basis.mulVec q.offset) (lattice q.basis)
  rw [translate_union, translate_translate, translate_lattice_add q.basis _ y hy,
    translate_lattice q.basis hy]

theorem toRealMatrix_mul_one (K K' : Matrix (Fin 3) (Fin 3) ℤ) (h : K * K' = 1) :
    toRealMatrix K * toRealMatrix K' = 1 := by
  unfold toRealMatrix
  rw [← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem points_rebase (B : Mat) (f : Vec) (K K' : Matrix (Fin 3) (Fin 3) ℤ) (h1 : K * K' = 1) :
    (⟨B * toRealMatrix K, (toRealMatrix K').mulVec f⟩ : TwoSite).points =
      (⟨B, f⟩ : TwoSite).points := by
  have hl : lattice (B * toRealMatrix K) = lattice B := rebase_sameLattice B K K' h1
  show lattice (B * toRealMatrix K) ∪ translate ((B * toRealMatrix K).mulVec
      ((toRealMatrix K').mulVec f)) (lattice (B * toRealMatrix K)) =
    lattice B ∪ translate (B.mulVec f) (lattice B)
  rw [hl, Matrix.mulVec_mulVec, mul_assoc, toRealMatrix_mul_one K K' h1, mul_one]

theorem points_rotate (U : Mat) (q : TwoSite) :
    (⟨U * q.basis, q.offset⟩ : TwoSite).points = U.mulVec '' q.points := by
  show lattice (U * q.basis) ∪ translate ((U * q.basis).mulVec q.offset) (lattice (U * q.basis)) =
    U.mulVec '' (lattice q.basis ∪ translate (q.basis.mulVec q.offset) (lattice q.basis))
  rw [lattice_left_mul, ← Matrix.mulVec_mulVec, translate_image, Set.image_union]

/-- Coset interchange is a translation by the second site. -/
theorem points_swap (q : TwoSite) :
    (offsetSwap q).points = translate (-(q.basis.mulVec q.offset)) q.points := by
  show lattice q.basis ∪ translate (q.basis.mulVec (-q.offset)) (lattice q.basis) =
    translate (-(q.basis.mulVec q.offset))
      (lattice q.basis ∪ translate (q.basis.mulVec q.offset) (lattice q.basis))
  rw [Matrix.mulVec_neg, translate_union, translate_translate, add_neg_cancel, translate_zero,
    Set.union_comm]

/-- Coset interchange is also the inversion through the origin. -/
theorem points_swap_neg (q : TwoSite) :
    (offsetSwap q).points = (fun x : Vec => -x) '' q.points := by
  ext x
  constructor
  · rintro (hx | ⟨y, hy, rfl⟩)
    · exact ⟨-x, Or.inl (lattice_neg_mem _ hx), neg_neg x⟩
    · refine ⟨-y + q.basis.mulVec q.offset, Or.inr ⟨-y, lattice_neg_mem _ hy, rfl⟩, ?_⟩
      show -(-y + q.basis.mulVec q.offset) = y + q.basis.mulVec (-q.offset)
      rw [Matrix.mulVec_neg]
      abel
  · rintro ⟨y, hy | ⟨z, hz, rfl⟩, rfl⟩
    · exact Or.inl (lattice_neg_mem _ hy)
    · refine Or.inr ⟨-z, lattice_neg_mem _ hz, ?_⟩
      show -(z + q.basis.mulVec q.offset) = -z + q.basis.mulVec (-q.offset)
      rw [Matrix.mulVec_neg]
      abel

/-- The inversion `x ↦ t − x` about the midpoint of the two sites `0` and
`t = B f` maps the point set onto itself. -/
theorem points_inversion (q : TwoSite) :
    (fun x => q.basis.mulVec q.offset - x) '' q.points = q.points := by
  ext x
  constructor
  · rintro ⟨y, hy | ⟨z, hz, rfl⟩, rfl⟩
    · refine Or.inr ⟨-y, lattice_neg_mem _ hy, ?_⟩
      show q.basis.mulVec q.offset - y = -y + q.basis.mulVec q.offset
      abel
    · refine Or.inl ?_
      show q.basis.mulVec q.offset - (z + q.basis.mulVec q.offset) ∈ lattice q.basis
      rw [show q.basis.mulVec q.offset - (z + q.basis.mulVec q.offset) = -z by abel]
      exact lattice_neg_mem _ hz
  · rintro (hx | ⟨z, hz, rfl⟩)
    · refine ⟨-x + q.basis.mulVec q.offset, Or.inr ⟨-x, lattice_neg_mem _ hx, rfl⟩, ?_⟩
      show q.basis.mulVec q.offset - (-x + q.basis.mulVec q.offset) = x
      abel
    · refine ⟨-z, Or.inl (lattice_neg_mem _ hz), ?_⟩
      show q.basis.mulVec q.offset - -z = z + q.basis.mulVec q.offset
      abel

theorem mem_points_inversion (q : TwoSite) (w : Vec) :
    w ∈ q.points ↔ q.basis.mulVec q.offset - w ∈ q.points := by
  constructor
  · intro hw
    rw [← points_inversion q]
    exact ⟨w, hw, rfl⟩
  · intro hw
    rw [← points_inversion q] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    have e : y = w := sub_right_injective hyw
    rwa [← e]

/-- The lifts of the second site are the negated lifts of the first site. -/
theorem liftedNeighbors_second_site (q : TwoSite) :
    liftedNeighbors q.points (q.basis.mulVec q.offset) =
      (fun v : Vec => -v) '' liftedNeighbors q.points 0 := by
  ext v
  constructor
  · rintro ⟨hv, hv0, hlen⟩
    refine ⟨-v, ⟨?_, neg_ne_zero.mpr hv0, by rwa [sq_neg_vector]⟩, neg_neg v⟩
    rw [zero_add]
    have h := (mem_points_inversion q _).mp hv
    rwa [show q.basis.mulVec q.offset - (q.basis.mulVec q.offset + v) = -v by abel] at h
  · rintro ⟨w, ⟨hw, hw0, hlen⟩, rfl⟩
    refine ⟨?_, neg_ne_zero.mpr hw0, by rwa [sq_neg_vector]⟩
    rw [zero_add] at hw
    apply (mem_points_inversion q _).mpr
    rwa [show q.basis.mulVec q.offset - (q.basis.mulVec q.offset + -w) = w by abel]

/-! ### The defect at every site -/

/-- The actual capped defect at the site `x` of the point set `S`. -/
def siteDefect (S : Set Vec) (x : Vec) : ℝ := cappedDefect (liftedNeighbors S x)

theorem defect_eq_siteDefect (q : TwoSite) : defect q = siteDefect q.points 0 := rfl

theorem siteDefect_translate_site (S : Set Vec) (x t : Vec) :
    siteDefect (translate t S) (x + t) = siteDefect S x :=
  Coulomb.siteDefect_translate S x t

theorem siteDefect_lattice (q : TwoSite) {y : Vec} (hy : y ∈ lattice q.basis) :
    siteDefect q.points y = defect q := by
  have h := siteDefect_translate_site q.points 0 y
  rw [points_translate_period q hy, zero_add] at h
  exact h

/-- Either-site identity: the second site has the defect of the first. -/
theorem siteDefect_second_site (q : TwoSite) :
    siteDefect q.points (q.basis.mulVec q.offset) = defect q := by
  unfold siteDefect
  rw [liftedNeighbors_second_site, cappedDefect_neg_image]
  rfl

/-- Every point of the configuration has the defect `D`. -/
theorem siteDefect_of_mem (q : TwoSite) {x : Vec} (hx : x ∈ q.points) :
    siteDefect q.points x = defect q := by
  rcases hx with hx | ⟨y, hy, rfl⟩
  · exact siteDefect_lattice q hx
  · have h := siteDefect_translate_site q.points (q.basis.mulVec q.offset) y
    rw [points_translate_period q hy] at h
    rw [add_comm, h]
    exact siteDefect_second_site q

theorem siteDefect_isometry {U : Mat} (hU : orthogonal U) (S : Set Vec) (x v : Vec) :
    siteDefect (translate v (U.mulVec '' S)) (U.mulVec x + v) = siteDefect S x := by
  rw [siteDefect_translate_site]
  unfold siteDefect
  rw [liftedNeighbors_orthogonal hU, cappedDefect_orthogonal_image U hU]

/-! ### Defect of transformed configurations -/

theorem defect_eq_of_points {q q' : TwoSite} (h : q.points = q'.points) : defect q = defect q' := by
  rw [defect_eq_siteDefect, defect_eq_siteDefect, h]

/-- Rigid motions, reflections included, preserve the defect. -/
theorem defect_of_isometric {q q' : TwoSite} {U : Mat} (hU : orthogonal U) {v : Vec}
    (h : q.points = translate v (U.mulVec '' q'.points)) : defect q = defect q' := by
  have h0 : (0 : Vec) ∈ translate v (U.mulVec '' q'.points) := by
    rw [← h]
    exact zero_mem_points q
  obtain ⟨_, ⟨x, hx, rfl⟩, hx0⟩ := h0
  rw [defect_eq_siteDefect, h, hx0, siteDefect_isometry hU, siteDefect_of_mem q' hx]

theorem defect_of_rigidCopy {q q' : TwoSite} (h : rigidCopy q.points q'.points) :
    defect q = defect q' := by
  obtain ⟨v, U, hU, hpts⟩ := h
  exact defect_of_isometric hU.1 hpts

theorem defect_wrap (q : TwoSite) (n : IntVec) : defect (wrap q n) = defect q :=
  defect_eq_of_points (points_wrap q n)

theorem defect_rebase (B : Mat) (f : Vec) (K K' : Matrix (Fin 3) (Fin 3) ℤ) (h1 : K * K' = 1) :
    defect ⟨B * toRealMatrix K, (toRealMatrix K').mulVec f⟩ = defect ⟨B, f⟩ :=
  defect_eq_of_points (points_rebase B f K K' h1)

theorem defect_rotate {U : Mat} (hU : orthogonal U) (q : TwoSite) :
    defect ⟨U * q.basis, q.offset⟩ = defect q := by
  apply defect_of_isometric hU (v := 0)
  rw [points_rotate, translate_zero]

/-- Coset interchange preserves the defect (through the either-site identity). -/
theorem defect_swap (q : TwoSite) : defect (offsetSwap q) = defect q := by
  rw [defect_eq_siteDefect, points_swap]
  have h := siteDefect_translate_site q.points (q.basis.mulVec q.offset)
    (-(q.basis.mulVec q.offset))
  rw [add_neg_cancel] at h
  exact h.trans (siteDefect_second_site q)

/-! ### Finite-index repetition -/

/-- Normalize a physical point set by the length unit `a`. -/
def normalize (a : ℝ) (X : Set Vec) : Set Vec := (fun y => a⁻¹ • y) '' X

/-- The actual defect at the site `x` of a physical point set `X` whose
length unit (the conventional BCC cube side) is `a`. -/
def unitSiteDefect (a : ℝ) (X : Set Vec) (x : Vec) : ℝ := siteDefect (normalize a X) (a⁻¹ • x)

theorem normalize_scaled {a : ℝ} (ha : a ≠ 0) (S : Set Vec) :
    normalize a ((fun x => a • x) '' S) = S := by
  unfold normalize
  rw [Set.image_image]
  simp [smul_smul, inv_mul_cancel₀ ha]

theorem repetition_points (q : TwoSite) {C : Mat} {κ : Type}
    (rep : PeriodRepetition (physicalBasis q) C κ) :
    periodicPoints C (repeatedSites rep (physicalTwoPositions q)) =
      (fun x => ac • x) '' q.points :=
  (rep.same_periodic_points _).trans (Constants.physical_points_eq_twoSite q)

/-- The normalized lifted neighbours of every point of a commensurate
repetition are those of the same point of the two-site configuration. -/
theorem repetition_liftedNeighbors (q : TwoSite) {C : Mat} {κ : Type}
    (rep : PeriodRepetition (physicalBasis q) C κ) (x : Vec) :
    liftedNeighbors (normalize ac (periodicPoints C (repeatedSites rep (physicalTwoPositions q))))
        (ac⁻¹ • x) = liftedNeighbors q.points (ac⁻¹ • x) := by
  rw [repetition_points, normalize_scaled ac_positive.ne']

theorem scaled_mem {a : ℝ} (ha : a ≠ 0) {S : Set Vec} {x : Vec}
    (hx : x ∈ (fun y => a • y) '' S) : a⁻¹ • x ∈ S := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Every point of a commensurate repetition has the defect `D`. -/
theorem repetition_siteDefect (q : TwoSite) {C : Mat} {κ : Type}
    (rep : PeriodRepetition (physicalBasis q) C κ) {x : Vec}
    (hx : x ∈ periodicPoints C (repeatedSites rep (physicalTwoPositions q))) :
    unitSiteDefect ac (periodicPoints C (repeatedSites rep (physicalTwoPositions q))) x =
      defect q := by
  unfold unitSiteDefect siteDefect
  rw [repetition_liftedNeighbors q rep x]
  rw [repetition_points] at hx
  exact siteDefect_of_mem q (scaled_mem ac_positive.ne' hx)

/-- The sites of a commensurate repetition are points of it. -/
theorem repeatedSite_mem {ι κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ) (s : ι → Vec)
    (i : ι × κ) : repeatedSites rep s i ∈ periodicPoints C (repeatedSites rep s) :=
  ⟨i, 0, by simp [linearImage, castVec_zero]⟩

/-! ### Density scaling -/

theorem normalize_dilate {a t : ℝ} (ht : t ≠ 0) (X : Set Vec) :
    normalize (t * a) ((fun y => t • y) '' X) = normalize a X := by
  unfold normalize
  rw [Set.image_image]
  apply Set.image_congr
  intro y _
  rw [smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht, mul_one]

/-- Dilating a configuration and its length unit together leaves every site
defect unchanged. -/
theorem unitSiteDefect_dilate {a t : ℝ} (ht : t ≠ 0) (X : Set Vec) (x : Vec) :
    unitSiteDefect (t * a) ((fun y => t • y) '' X) (t • x) = unitSiteDefect a X x := by
  unfold unitSiteDefect
  rw [normalize_dilate ht, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht, mul_one]

/-- The physical defect at every point of the configuration, at the two-site theorem
density, is `D`. -/
theorem unitSiteDefect_physical (q : TwoSite) {x : Vec} (hx : x ∈ q.points) :
    unitSiteDefect ac ((fun y => ac • y) '' q.points) (ac • x) = defect q := by
  unfold unitSiteDefect
  rw [normalize_scaled ac_positive.ne', smul_smul, inv_mul_cancel₀ ac_positive.ne', one_smul]
  exact siteDefect_of_mem q hx

/-! ### Finiteness inside the cutoff and attainment -/

/-- The lifts of every point inside the cutoff form a finite set. -/
theorem siteNeighbors_finite (q : TwoSite) (hq : q.Valid) {x : Vec} (hx : x ∈ q.points) :
    (liftedNeighbors q.points x).Finite := by
  have h0 : (neighbors q).Finite := twoSite_neighbors_finite q hq
  rcases hx with hx | ⟨y, hy, rfl⟩
  · have h := liftedNeighbors_translate q.points 0 x
    rw [points_translate_period q hx, zero_add] at h
    rw [h]
    exact h0
  · have h := liftedNeighbors_translate q.points (q.basis.mulVec q.offset) y
    rw [points_translate_period q hy] at h
    rw [add_comm, h, liftedNeighbors_second_site]
    exact h0.image _

theorem cappedDefect_mem {Y : Set Vec} (hY : Y.Finite) : cappedDefect Y ∈ defectCandidates Y :=
  (defectCandidates_compact hY).sInf_mem ⟨1, Set.mem_insert _ _⟩

/-- The defect is attained: it is the cap or the cost of an actual trial. -/
theorem defect_attained (q : TwoSite) (hq : q.Valid) :
    defect q = 1 ∨ ∃ U : Mat, proper U ∧ ∃ σ : Fin 14 ↪ ↥(neighbors q), defectTrial U σ = defect q := by
  rcases Set.mem_insert_iff.mp (cappedDefect_mem (twoSite_neighbors_finite q hq)) with h | ⟨U, hU, σ, hσ⟩
  · exact Or.inl h
  · exact Or.inr ⟨U, hU, σ, hσ.symm⟩

/-- `D` is the minimum of the cap and of every trial cost. -/
theorem defect_eq_min (q : TwoSite) (hq : q.Valid) :
    defect q ≤ 1 ∧
      (∀ U : Mat, proper U → ∀ σ : Fin 14 ↪ ↥(neighbors q), defect q ≤ defectTrial U σ) ∧
      (defect q = 1 ∨ ∃ U : Mat, proper U ∧ ∃ σ : Fin 14 ↪ ↥(neighbors q), defectTrial U σ = defect q) :=
  ⟨(defect_range q).2, fun U hU σ => cappedDefect_le_trial U hU σ, defect_attained q hq⟩

/-- Fewer than fourteen lifts inside the cutoff (a vacancy) saturate the defect. -/
theorem defect_eq_one_of_few (q : TwoSite) (hfin : (neighbors q).Finite)
    (h : Nat.card ↥(neighbors q) < 14) : defect q = 1 := by
  have : Finite ↥(neighbors q) := hfin.to_subtype
  have hc : defectCandidates (neighbors q) = {1} := by
    ext c
    constructor
    · rintro (hc | ⟨U, hU, σ, rfl⟩)
      · exact hc
      · exfalso
        have hle := Finite.card_le_of_embedding σ
        rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
        omega
    · intro hc
      exact Or.inl hc
  show sInf (defectCandidates (neighbors q)) = 1
  rw [hc, csInf_singleton]

/-! ### The energy depends only on the point set, modulo rigid motions -/

/-- Without a half-integral offset, every period of the point set is a
period of the representation. -/
theorem lattice_subset_of_points {q q' : TwoSite} (hq : q.Valid)
    (half : ¬ ∃ n : IntVec, (2 : ℝ) • q.offset = castVec n) (h : q'.points = q.points) :
    lattice q'.basis ⊆ lattice q.basis := by
  intro y hy
  have hT : translate y q.points = q.points := by
    rw [← h]
    exact points_translate_period q' hy
  have hyS : y ∈ q.points := by
    rw [← hT]
    exact ⟨0, zero_mem_points q, by rw [zero_add]⟩
  rcases hyS with hyL | ⟨z, ⟨m, rfl⟩, rfl⟩
  · exact hyL
  · exfalso
    have hinj := basis_injective q hq
    have h2 : q.basis.mulVec q.offset +
        (q.basis.mulVec (castVec m) + q.basis.mulVec q.offset) ∈ q.points := by
      rw [← hT]
      exact ⟨q.basis.mulVec q.offset, offset_mem_points q, by abel⟩
    rcases h2 with ⟨k, hk⟩ | ⟨w, ⟨k, rfl⟩, hk⟩
    · apply half
      have hk' : q.basis.mulVec (castVec k) = q.basis.mulVec q.offset +
          (q.basis.mulVec (castVec m) + q.basis.mulVec q.offset) := hk
      refine ⟨k - m, hinj ?_⟩
      rw [castVec_sub', Matrix.mulVec_sub, hk', two_smul, Matrix.mulVec_add]
      abel
    · apply hq.2 (k - m)
      apply hinj
      rw [castVec_sub', Matrix.mulVec_sub]
      have hk' : q.basis.mulVec q.offset + (q.basis.mulVec (castVec m) + q.basis.mulVec q.offset) =
          q.basis.mulVec (castVec k) + q.basis.mulVec q.offset := hk
      have hk2 : q.basis.mulVec (castVec k) = q.basis.mulVec (castVec m) + q.basis.mulVec q.offset := by
        have e2 : q.basis.mulVec (castVec k) + q.basis.mulVec q.offset =
            (q.basis.mulVec (castVec m) + q.basis.mulVec q.offset) + q.basis.mulVec q.offset := by
          rw [← hk']
          abel
        exact add_right_cancel e2
      rw [hk2]
      abel

theorem toRealMatrix_det (K : Matrix (Fin 3) (Fin 3) ℤ) : (toRealMatrix K).det = ((K.det : ℤ) : ℝ) := by
  rw [show toRealMatrix K = (Int.castRingHom ℝ).mapMatrix K from rfl, ← RingHom.map_det]
  rfl

/-- Two valid representations of one point set have the same energy. -/
theorem energy_of_points_eq {q q' : TwoSite} (hq : q.Valid) (hq' : q'.Valid)
    (h : q'.points = q.points) : energy q' = energy q := by
  by_cases half : ∃ n : IntVec, (2 : ℝ) • q.offset = castVec n
  · have hc : HalfClass q.offset := ⟨half, hq.2⟩
    obtain ⟨model⟩ := primitive_anchor_exists q hq hc
    have hc' : HalfClass q'.offset :=
      halfClass_of_lattice q' hq' model.basis (h.trans model.points.symm)
    obtain ⟨model'⟩ := primitive_anchor_exists q' hq' hc'
    rw [← model.sameEnergy, ← model'.sameEnergy]
    have hm : model.basis.det ≠ 0 := by rw [model.volume]; norm_num
    have hm' : model'.basis.det ≠ 0 := by rw [model'.volume]; norm_num
    exact oneSiteEnergy_sameLattice _ _ hm hm' (by rw [model.points, model'.points, h])
  · have hsub := lattice_subset_of_points hq half h
    obtain ⟨K, hK⟩ := exists_integer_rebase q.basis q'.basis hsub
    have hdetR : (toRealMatrix K).det = 1 := by
      have e := congrArg Matrix.det hK
      rw [Matrix.det_mul, hq.1, hq'.1, one_mul] at e
      exact e.symm
    have hdetK : K.det = 1 := by
      have e : ((K.det : ℤ) : ℝ) = 1 := by rw [← toRealMatrix_det]; exact hdetR
      exact_mod_cast e
    have h1 : K * K.adjugate = 1 := by rw [Matrix.mul_adjugate, hdetK, one_smul]
    have h2 : K.adjugate * K = 1 := by rw [Matrix.adjugate_mul, hdetK, one_smul]
    have hL : lattice q'.basis = lattice q.basis := by
      rw [hK]
      exact rebase_sameLattice q.basis K K.adjugate h1
    have ht' : q'.basis.mulVec q'.offset ∈ q.points := by
      rw [← h]
      exact offset_mem_points q'
    rcases ht' with hin | ⟨w, ⟨m, rfl⟩, hm⟩
    · exfalso
      rw [← hL] at hin
      obtain ⟨n, hn⟩ := hin
      exact hq'.2 n (basis_injective q' hq' hn).symm
    · have hoff : q'.offset = (toRealMatrix K.adjugate).mulVec (q.offset + castVec m) := by
        have e1 : q.basis.mulVec ((toRealMatrix K).mulVec q'.offset) =
            q.basis.mulVec (q.offset + castVec m) := by
          rw [Matrix.mulVec_mulVec, ← hK, hm, Matrix.mulVec_add, add_comm]
        have e2 := basis_injective q hq e1
        rw [← e2, Matrix.mulVec_mulVec, toRealMatrix_mul_one K.adjugate K h2, Matrix.one_mulVec]
      have hq'eq : q' = ⟨q.basis * toRealMatrix K, (toRealMatrix K.adjugate).mulVec
          (q.offset + castVec m)⟩ := by
        cases q'
        simp only at hK hoff
        rw [hK, hoff]
      rw [hq'eq, energy_rebase q.basis (q.offset + castVec m) K K.adjugate h1 h2]
      exact energy_wrap q m

theorem valid_swap {q : TwoSite} (hq : q.Valid) : (offsetSwap q).Valid := by
  refine ⟨hq.1, fun n hn => hq.2 (-n) ?_⟩
  rw [castVec_neg, ← hn]
  show q.offset = -(-q.offset)
  rw [neg_neg]

theorem valid_rotate {q : TwoSite} (hq : q.Valid) {U : Mat} (hU : U.det = 1) :
    (⟨U * q.basis, q.offset⟩ : TwoSite).Valid :=
  ⟨by rw [Matrix.det_mul, hU, hq.1, one_mul], hq.2⟩

/-- Rigid motions, reflections included, preserve the energy of valid
configurations. -/
theorem energy_of_isometric {q q' : TwoSite} (hq : q.Valid) (hq' : q'.Valid) {U : Mat}
    (hU : orthogonal U) {v : Vec} (h : q.points = translate v (U.mulVec '' q'.points)) :
    energy q = energy q' := by
  have h0 : (0 : Vec) ∈ translate v (U.mulVec '' q'.points) := by
    rw [← h]
    exact zero_mem_points q
  obtain ⟨_, ⟨x, hx, rfl⟩, hx0⟩ := h0
  have hv : v = U.mulVec (-x) := by
    rw [Matrix.mulVec_neg]
    exact eq_neg_of_add_eq_zero_right hx0.symm
  -- move the chosen point of `q'` to the origin
  obtain ⟨q₁, hq₁, hE₁, hP₁⟩ : ∃ q₁ : TwoSite, q₁.Valid ∧ energy q₁ = energy q' ∧
      q₁.points = translate (-x) q'.points := by
    rcases hx with hxL | ⟨y, hy, rfl⟩
    · exact ⟨q', hq', rfl, (points_translate_period q' (lattice_neg_mem _ hxL)).symm⟩
    · refine ⟨offsetSwap q', valid_swap hq', energy_offsetSwap q', ?_⟩
      rw [points_swap, neg_add, ← translate_translate,
        points_translate_period q' (lattice_neg_mem _ hy)]
  have hP : q.points = U.mulVec '' q₁.points := by
    rw [h, hP₁, hv, translate_image]
  -- rotate the frame of `q₁` onto `q`
  obtain ⟨q₂, hq₂, hE₂, hP₂⟩ : ∃ q₂ : TwoSite, q₂.Valid ∧ energy q₂ = energy q₁ ∧
      q₂.points = q.points := by
    rcases orthogonal_det hU with hd | hd
    · refine ⟨⟨U * q₁.basis, q₁.offset⟩, valid_rotate hq₁ hd, energy_rotate U q₁.basis hU _, ?_⟩
      rw [points_rotate, hP]
    · have hP' := proper_neg_of_det hU hd
      refine ⟨⟨(-U) * (offsetSwap q₁).basis, (offsetSwap q₁).offset⟩,
        valid_rotate (valid_swap hq₁) hP'.2, ?_, ?_⟩
      · rw [energy_rotate (-U) (offsetSwap q₁).basis hP'.1]
        exact energy_offsetSwap q₁
      · rw [points_rotate, points_swap_neg, Set.image_image, hP]
        apply Set.image_congr
        intro y _
        rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
  rw [← energy_of_points_eq hq hq₂ hP₂, hE₂, hE₁]

theorem energy_of_rigidCopy {q q' : TwoSite} (hq : q.Valid) (hq' : q'.Valid)
    (h : rigidCopy q.points q'.points) : energy q = energy q' := by
  obtain ⟨v, U, hU, hpts⟩ := h
  exact energy_of_isometric hq hq' hU.1 hpts

end BccSharp.Coulomb.DefectInvariance
