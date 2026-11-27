import BccSharp.TwoSite.Spec
import BccSharp.Cover.OverlayCorpusPrefix

set_option autoImplicit false

/-! `StatementFull`: every clause of the two-site theorem, in one proposition.

`Statement` (`BccSharp.TwoSite.Interface`) states the inequality (1.1), its equality
cases, the unique minimizer, sharpness and the registration (3.10) in a reduced
frame. `StatementFull` adds the clauses `Statement` does not state:

* the physical model: every valid configuration is the union `L ∪ (L + τ)` of
  a lattice of covolume `8π/3` (density `3/(4π)`) and a distinct translate,
  and every such union, of any shape and any noncoincident shift, is a valid
  configuration; every union of two distinct translates `(L + a) ∪ (L + b)` is
  a translate of one; the energy is the neutral Ewald energy per particle with
  the regular self term, at every screening, of the configuration's point set;
* energy and defect are functions of the point set modulo rigid motions,
  reflections included;
* every commensurate repetition of either coset representation has the same
  energy and, at every site, the same defect;
* any site has the same defect;
* another density: the dilated reference star gives the same defect, and
  energies and the gap scale by the inverse length dilation;
* `D` is Spec's defect, written independently (`TwoSiteSpec.specSiteDefect`), and
  lies in `[0, 1]`; it is a minimum, attained, over rotations and injections;
* the equality cases and the minimizer as rigid images (`TwoSiteSpec.RigidImage`)
  of the conventional BCC and FCC lattices (`TwoSiteSpec.bccUnit`,
  `TwoSiteSpec.fccUnit`);
* `D(BCC) = 0`, `D(FCC) = 1`, and the numerical value of the gap;
* the registration (3.10), written independently (`TwoSiteSpec.RegisteredBound`),
  in every oriented frame of the configuration, not only a reduced one.

`statementFull_of_statement` proves `StatementFull` from `Statement`, so the
two are equivalent (`statementFull_iff`): the added clauses are unconditional
theorems and independent definitions, not a stronger conditional result. The
`assemble_full_*` theorems are the corresponding corollaries of the assembly
theorems. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.Full
open TwoSiteSpec
open BccSharp.Coulomb.DefectInvariance
open BccSharp.Coulomb.SpecBridge
open BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.CompactCover

/-! ### Screening independence of the Ewald energy -/

open Classical in
theorem greenPerParticle_screening {ι : Type} [Fintype ι] {B : Mat} (hB : B.det ≠ 0)
    {s : ι → Vec} (hs : distinctModulo B s) {α β : ℝ} (ha : 0 < α) (hb : 0 < β) :
    greenPerParticle α B s = greenPerParticle β B s := by
  unfold greenPerParticle greenCellEnergy
  have hpair : ∀ i j, (if i = j then 0 else periodicGreen α B (s i - s j)) =
      (if i = j then 0 else periodicGreen β B (s i - s j)) := by
    intro i j
    by_cases h : i = j
    · simp [h]
    · rw [ite_eq_right h, ite_eq_right h,
        periodicGreen_screening_independent α β B hB ha hb (hs i j h)]
  simp_rw [hpair, ewaldRegularSelf_screening_independent α β B hB ha hb]

/-- The energy is the neutral Ewald energy per particle at every screening. -/
theorem ewald_energy (q : TwoSite) (hq : q.Valid) {α : ℝ} (ha : 0 < α) :
    greenPerParticle α (physicalBasis q) (physicalTwoPositions q) = energy q := by
  have hk : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  rw [greenPerParticle_screening (series_physical_basis_nonsingular q hq)
    (Constants.physical_positions_distinct q hq) ha hk]
  exact green_two_eq_energy q hq

/-! ### Rigid images of point sets -/

/-- A rigid image of point sets is an orthogonal map followed by a translation. -/
theorem isometric_of_rigidImage {S T : Set Vec} (h : RigidImage (toE3 '' S) (toE3 '' T)) :
    ∃ (U : Mat) (w : Vec), orthogonal U ∧ S = translate w (U.mulVec '' T) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨U, hU, hφU⟩ := isometry_affine φ
  obtain ⟨w, hw⟩ := exists_toE3 (φ 0)
  refine ⟨U, w, hU, ?_⟩
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

theorem energy_of_rigidImage {q q' : TwoSite} (hq : q.Valid) (hq' : q'.Valid)
    (h : RigidImage (specPoints q) (specPoints q')) : energy q = energy q' := by
  obtain ⟨U, w, hU, hS⟩ := isometric_of_rigidImage h
  exact energy_of_isometric hq hq' hU hS

theorem defect_of_rigidImage {q q' : TwoSite} (h : RigidImage (specPoints q) (specPoints q')) :
    defect q = defect q' := by
  obtain ⟨U, w, hU, hS⟩ := isometric_of_rigidImage h
  exact defect_of_isometric hU hS

/-! ### Registration in every oriented frame -/

/-- Inequality (3.10) in the frame of any valid configuration whose defect is
below one and whose energy is at most the FCC energy: the registration does
not depend on a reduced frame. -/
theorem register_frame (q : TwoSite) (hq : q.Valid) (he : energy q ≤ energy fcc)
    (hD : defect q < 1) : RegisteredBound q.basis q.offset (defect q) := by
  rw [registeredBound_iff]
  have hsep : separated q := separated_of_energy q hq he
  obtain ⟨O, hO, σ, hσ⟩ := cappedDefect_attained (twoSite_neighbors_finite q hq) hD
  have hmem : ∀ j, (σ j : Vec) ∈ q.points := by
    intro j
    have h := (σ j).property.1
    simpa only [zero_add] using h
  have htail : 0 ≤ ∑' v : ↥(neighbors q),
      if v ∈ Set.range σ then 0 else annularWeight v.val := by
    apply tsum_nonneg
    intro v
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  have htrial : 25 * ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) ≤ defect q := by
    show _ ≤ cappedDefect (neighbors q)
    rw [← hσ]
    unfold defectTrial
    linarith
  have hsmall : ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) < 1 / 25 := by linarith
  let T : Trial q := ⟨O, hO, fun j => (σ j : Vec), hmem, hsmall⟩
  obtain ⟨A, f₀, hdetA, half, hlat, hcost⟩ := T.core hq hsep
  have hAu : IsUnit A.det := by
    rw [hdetA]
    exact isUnit_one
  have hRu : IsUnit q.basis.det := by
    rw [hq.1]
    exact isUnit_one
  have hBdet : (A⁻¹ * q.basis).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdetA, hq.1]
    simp
  refine ⟨A⁻¹ * q.basis, f₀, 0, O, ⟨hBdet, half, ?_, ?_⟩, hO, ?_⟩
  · rintro ⟨n, hn⟩
    have hBu : IsUnit (A⁻¹ * q.basis).det := by
      rw [hBdet]
      exact isUnit_one
    have e := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hBu) hn
    exact half.2 n e.symm
  · rw [lattice_left_mul, ← Matrix.mulVec_mulVec, translate_image, ← Set.image_union, ← hlat,
      lattice_left_mul, Set.image_image]
    have hid : (fun x => A⁻¹.mulVec (A.mulVec x)) = id := by
      funext x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]
      rfl
    rw [hid, Set.image_id, bccPrimitive_lattice]
  · have hRB : q.basis * (A⁻¹ * q.basis)⁻¹ = A := by
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hAu, ← mul_assoc,
        Matrix.mul_nonsing_inv _ hRu, one_mul]
    have htrial' : 25 * ∑ j, sq (T.err j) ≤ defect q := htrial
    rw [hRB, castVec_zero, sub_zero]
    change 100 * frobSq (A - T.O) + 200 * sq (q.basis.mulVec (q.offset - f₀)) ≤ defect q
    rw [hcost] at htrial'
    linarith

/-! ### The full statement -/

/-- Every clause of the two-site theorem. Lengths of the physical configuration are
in Wigner–Seitz units: `physPoints q` has density `3/(4π)` and the
conventional BCC cube side `a_c = (8π/3)^(1/3)`. -/
structure StatementFull : Prop where
  /-- The interface statement: inequality (1.1), its equality cases, the unique
  minimizer, sharpness and the registration (3.10) in a reduced frame. -/
  statement : Statement
  /-- Every valid configuration is the union `L ∪ (L + τ)` of a lattice of
  covolume `8π/3` and a distinct translate of it. -/
  model : ∀ q : TwoSite, q.Valid → TwoCosetConfig (physPoints q)
  /-- Every union `L ∪ (L + τ)` of a lattice of covolume `8π/3` and a distinct
  translate, of any shape and with any noncoincident shift, is a valid
  configuration. -/
  arbitrary : ∀ X : Set E3, TwoCosetConfig X → ∃ q : TwoSite, q.Valid ∧ physPoints q = X
  /-- Every union `(L + a) ∪ (L + b)` of two distinct translates of a lattice of
  covolume `8π/3` is a translate of a valid configuration, and Spec's defect at
  each of its points is that configuration's `D`. -/
  translates : ∀ X : Set E3, TwoTranslates X → ∃ q : TwoSite, q.Valid ∧ ∃ v : E3,
    X = (fun y => y + v) '' physPoints q ∧ ∀ y ∈ X, specSiteDefect ac X y = defect q
  /-- The energy is the neutral Ewald (Wigner–Seitz) energy per particle with the
  regular self term, at every screening. -/
  ewald : ∀ q : TwoSite, q.Valid → ∀ α : ℝ, 0 < α →
    greenPerParticle α (physicalBasis q) (physicalTwoPositions q) = energy q
  /-- The periodic configuration in `ewald` has the point set `physPoints q`,
  and its two sites are distinct modulo the period lattice. -/
  ewaldPoints : ∀ q : TwoSite, q.Valid →
    toE3 '' periodicPoints (physicalBasis q) (physicalTwoPositions q) = physPoints q ∧
      distinctModulo (physicalBasis q) (physicalTwoPositions q)
  /-- The kernel in `ewald` has the Fourier coefficients of the zero-mean periodic
  Coulomb kernel on the period cell: `4π/|k|²`, and `0` at `k = 0`. These fix it
  only almost everywhere; `periodicGreen` itself is the explicit Ewald sum. -/
  greenKernel : ∀ q : TwoSite, ∀ hq : q.Valid, ∀ α : ℝ, 0 < α → ∀ n : IntVec,
    cellFourier (physicalBasis q) (series_physical_basis_nonsingular q hq)
      (fun x => (periodicGreen α (physicalBasis q) x : ℂ)) n =
      if n = 0 then 0 else ((4 * Real.pi / sq (dualWave (physicalBasis q) n) : ℝ) : ℂ)
  /-- The self term in `ewald` is the regular part of the kernel at the origin. -/
  regularSelf : ∀ q : TwoSite, q.Valid → ∀ α : ℝ, 0 < α →
    Filter.Tendsto (fun x => periodicGreen α (physicalBasis q) x - 1 / Real.sqrt (sq x))
      (nhdsWithin (0 : Vec) (Set.univ \ lattice (physicalBasis q)))
      (nhds (ewaldRegularSelf α (physicalBasis q)))
  /-- The energy is a function of the point set modulo rigid motions,
  reflections included. -/
  energyRigid : ∀ q q' : TwoSite, q.Valid → q'.Valid →
    RigidImage (specPoints q) (specPoints q') → energy q = energy q'
  /-- So is the defect. -/
  defectRigid : ∀ q q' : TwoSite, RigidImage (specPoints q) (specPoints q') → defect q = defect q'
  /-- Either coset representation. -/
  eitherCoset : ∀ q : TwoSite, q.Valid →
    (offsetSwap q).Valid ∧ energy (offsetSwap q) = energy q ∧ defect (offsetSwap q) = defect q
  /-- Every commensurate repetition has the same energy per particle. -/
  repetitionEnergy : ∀ q : TwoSite, q.Valid → ∀ (C : Mat) (κ : Type) [Fintype κ],
    0 < Fintype.card κ → C.det ≠ 0 → ∀ rep : PeriodRepetition (physicalBasis q) C κ,
      ∀ α : ℝ, 0 < α → greenPerParticle α C (repeatedSites rep (physicalTwoPositions q)) = energy q
  /-- Every site of every commensurate repetition has Spec's defect `D`. -/
  repetitionDefect : ∀ q : TwoSite, q.Valid → ∀ (C : Mat) (κ : Type)
    (rep : PeriodRepetition (physicalBasis q) C κ),
      ∀ y ∈ periodicPoints C (repeatedSites rep (physicalTwoPositions q)),
        specSiteDefect ac (toE3 '' periodicPoints C (repeatedSites rep (physicalTwoPositions q)))
          (toE3 y) = defect q
  /-- Any site gives the same value of `D`, and that value is Spec's defect. -/
  anySite : ∀ q : TwoSite, q.Valid → ∀ y ∈ physPoints q, specSiteDefect ac (physPoints q) y = defect q
  /-- `D` lies in `[0, 1]`. -/
  defectRange : ∀ q : TwoSite, 0 ≤ defect q ∧ defect q ≤ 1
  /-- `D` is a minimum over rotations and injections of the finitely many lifts
  inside the cutoff, capped at one, and it is attained. -/
  defectMin : ∀ q : TwoSite, q.Valid → (neighbors q).Finite ∧
    (∀ U : Mat, proper U → ∀ σ : Fin 14 ↪ ↥(neighbors q), defect q ≤ defectTrial U σ) ∧
    (defect q = 1 ∨ ∃ U : Mat, proper U ∧ ∃ σ : Fin 14 ↪ ↥(neighbors q), defectTrial U σ = defect q)
  /-- Spec's lift sets are finite at every point, so its sums are finite sums. -/
  liftsFinite : ∀ q : TwoSite, q.Valid → ∀ y ∈ physPoints q, (liftVectors ac (physPoints q) y).Finite
  /-- Another density: with the dilated reference star the defect is unchanged. -/
  densityDefect : ∀ q : TwoSite, q.Valid → ∀ t : ℝ, 0 < t → ∀ y ∈ dilate t (physPoints q),
    specSiteDefect (t * ac) (dilate t (physPoints q)) y = defect q
  /-- Another density: energies scale by the inverse length dilation. -/
  densityEnergy : ∀ q : TwoSite, q.Valid → ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α →
    greenPerParticle α (t • physicalBasis q) (fun i => t • physicalTwoPositions q i) = energy q / t
  /-- Another density: so does the gap. -/
  densityGap : ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α →
    greenPerParticle α (t • physicalBasis fcc) (fun i => t • physicalTwoPositions fcc i) -
      greenPerParticle α (t • physicalBasis bcc) (fun i => t • physicalTwoPositions bcc i) = gap / t
  /-- The sharp inequality (1.1) with Spec's defect at any site. -/
  inequality : ∀ q : TwoSite, q.Valid → ∀ y ∈ physPoints q,
    gap * specSiteDefect ac (physPoints q) y ≤ energy q - energy bcc
  /-- Equality holds exactly for rigid images of BCC and FCC. -/
  equality : ∀ q : TwoSite, q.Valid → (energy q - energy bcc = gap * defect q ↔
    RigidImage (physPoints q) (dilate ac bccUnit) ∨ RigidImage (physPoints q) (dilate ac fccUnit))
  /-- BCC alone minimizes the energy, up to rigid motion. -/
  minimum : ∀ q : TwoSite, q.Valid → energy bcc ≤ energy q ∧
    (energy q = energy bcc ↔ RigidImage (physPoints q) (dilate ac bccUnit))
  /-- The constant is optimal. -/
  sharp : ∀ k : ℝ, (∀ q : TwoSite, q.Valid → k * defect q ≤ energy q - energy bcc) → k ≤ gap
  /-- The reference configurations. -/
  references : bcc.Valid ∧ fcc.Valid ∧ specPoints bcc = bccUnit ∧ specPoints fcc = fccUnit ∧
    defect bcc = 0 ∧ defect fcc = 1
  /-- The Constants reference energies in Wigner–Seitz units:
  `e_BCC = −0.89592925568176528916…` and `e_FCC = −0.89587361519510845989…`. -/
  referenceEnergies : Constants.bccBracket.contains (energy bcc) ∧ Constants.fccBracket.contains (energy fcc)
  /-- `g = e_FCC − e_BCC = 5.5640486656829268757…·10⁻⁵`. -/
  gapValue : (55640486656829268757 : ℝ) / 10 ^ 24 ≤ gap ∧ gap ≤ (55640486656829268758 : ℝ) / 10 ^ 24
  /-- Registration (3.10) below the FCC energy, in every oriented frame, with
  `D ≤ (e − e_BCC)/g < 1`. -/
  registration : ∀ q : TwoSite, q.Valid → energy q < energy fcc →
    RegisteredBound q.basis q.offset (defect q) ∧
      defect q ≤ (energy q - energy bcc) / gap ∧ (energy q - energy bcc) / gap < 1

theorem gap_value : (55640486656829268757 : ℝ) / 10 ^ 24 ≤ gap ∧
    gap ≤ (55640486656829268758 : ℝ) / 10 ^ 24 := by
  obtain ⟨⟨hlo, hhi⟩, _⟩ := Constants.reference_gap_checked
  have elo : ((55640486656829268757 : ℚ) / 10 ^ 24 : ℚ) ≤ Constants.gapBracket.lo := by
    norm_num [Constants.gapBracket, Constants.Interval.sub, Constants.bccBracket, Constants.fccBracket]
  have ehi : Constants.gapBracket.hi ≤ ((55640486656829268758 : ℚ) / 10 ^ 24 : ℚ) := by
    norm_num [Constants.gapBracket, Constants.Interval.sub, Constants.bccBracket, Constants.fccBracket]
  have elo' : ((55640486656829268757 : ℝ) / 10 ^ 24) ≤ (Constants.gapBracket.lo : ℝ) := by
    have h1 : (((55640486656829268757 : ℚ) / 10 ^ 24 : ℚ) : ℝ) ≤ (Constants.gapBracket.lo : ℝ) :=
      Rat.cast_le.mpr elo
    have h2 : (((55640486656829268757 : ℚ) / 10 ^ 24 : ℚ) : ℝ) =
        (55640486656829268757 : ℝ) / 10 ^ 24 := by
      push_cast
      ring
    rwa [h2] at h1
  have ehi' : (Constants.gapBracket.hi : ℝ) ≤ ((55640486656829268758 : ℝ) / 10 ^ 24) := by
    have h1 : (Constants.gapBracket.hi : ℝ) ≤ (((55640486656829268758 : ℚ) / 10 ^ 24 : ℚ) : ℝ) :=
      Rat.cast_le.mpr ehi
    have h2 : (((55640486656829268758 : ℚ) / 10 ^ 24 : ℚ) : ℝ) =
        (55640486656829268758 : ℝ) / 10 ^ 24 := by
      push_cast
      ring
    rwa [h2] at h1
  exact ⟨elo'.trans hlo, hhi.trans ehi'⟩

theorem bcc_isBCC : IsBCC bcc := by
  refine ⟨0, 1, proper_one, ?_⟩
  have hid : Matrix.mulVec (1 : Mat) = id := funext Matrix.one_mulVec
  rw [translate_zero, hid, Set.image_id]

theorem density_energy (q : TwoSite) (hq : q.Valid) {t : ℝ} (ht : 0 < t) {α : ℝ} (ha : 0 < α) :
    greenPerParticle α (t • physicalBasis q) (fun i => t • physicalTwoPositions q i) =
      energy q / t := by
  have h := greenPerParticle_scale (α * t) t ht (physicalBasis q)
    (series_physical_basis_nonsingular q hq) (physicalTwoPositions q)
  rw [show α * t / t = α by field_simp] at h
  rw [h, ewald_energy q hq (mul_pos ha ht)]

/-- `StatementFull` follows from `Statement`. -/
theorem statementFull_of_statement (h : Statement) : StatementFull where
  statement := h
  model := twoCoset_of_valid
  arbitrary := fun _ hX => valid_of_twoCoset hX
  translates := fun _ hX => spec_translates hX
  ewald := fun q hq _ ha => ewald_energy q hq ha
  ewaldPoints := fun q hq => ⟨by
    rw [Constants.physical_points_eq_twoSite, physPoints, specPoints, dilate_image_toE3],
    Constants.physical_positions_distinct q hq⟩
  greenKernel := fun q hq α ha n => periodicGreen_fourier_on_cell α ha (physicalBasis q)
    (series_physical_basis_nonsingular q hq) n
  regularSelf := fun q hq α ha => periodicGreen_regular_limit α ha (physicalBasis q)
    (series_physical_basis_nonsingular q hq)
  energyRigid := fun _ _ hq hq' hr => energy_of_rigidImage hq hq' hr
  defectRigid := fun _ _ hr => defect_of_rigidImage hr
  eitherCoset := fun q hq => ⟨valid_swap hq, energy_offsetSwap q, defect_swap q⟩
  repetitionEnergy := by
    intro q hq C κ _ hκ hC rep α ha
    rw [greenPerParticle_repetition rep (series_physical_basis_nonsingular q hq) hC α ha
      (physicalTwoPositions q) hκ (by simp)]
    exact ewald_energy q hq ha
  repetitionDefect := by
    intro q hq C κ rep y hy
    have hpts : toE3 '' periodicPoints C (repeatedSites rep (physicalTwoPositions q)) =
        physPoints q := by
      rw [repetition_points, physPoints, specPoints, dilate_image_toE3]
    rw [hpts]
    apply spec_physical q hq
    rw [← hpts]
    exact ⟨y, hy, rfl⟩
  anySite := fun q hq _ hy => spec_physical q hq hy
  defectRange := defect_range
  defectMin := fun q hq => ⟨twoSite_neighbors_finite q hq, (defect_eq_min q hq).2.1,
    (defect_eq_min q hq).2.2⟩
  liftsFinite := fun q hq _ hy => liftVectors_physical_finite q hq hy
  densityDefect := fun q hq _ ht _ hy => spec_dilated q hq ht hy
  densityEnergy := fun q hq _ ht _ ha => density_energy q hq ht ha
  densityGap := by
    intro t ht α ha
    rw [density_energy fcc (Constants.refTwo_valid .fcc) ht ha,
      density_energy bcc (Constants.refTwo_valid .bcc) ht ha, gap]
    ring
  inequality := by
    intro q hq y hy
    rw [spec_physical q hq hy]
    exact h.inequality q hq
  equality := by
    intro q hq
    rw [← isBCC_iff_physical, ← isFCC_iff_physical, ← h.equality q hq]
    unfold deficit
    constructor
    · intro e
      linarith
    · intro e
      linarith
  minimum := by
    intro q hq
    rw [← isBCC_iff_physical]
    exact h.minimum q hq
  sharp := h.sharp
  references := ⟨Constants.refTwo_valid .bcc, Constants.refTwo_valid .fcc, bccUnit_eq.symm, fccUnit_eq.symm,
    (bccValues_proof bcc (Constants.refTwo_valid .bcc) bcc_isBCC).2, fccSaturated_proof⟩
  referenceEnergies := ⟨Constants.reference_bounds .bcc, Constants.reference_bounds .fcc⟩
  gapValue := gap_value
  registration := by
    intro q hq he
    obtain ⟨_, hupper, hlt⟩ := h.registration q hq he
    exact ⟨register_frame q hq (le_of_lt he) (lt_of_le_of_lt hupper hlt), hupper, hlt⟩

/-- `StatementFull` and `Statement` are equivalent: the added clauses are
unconditional theorems and independent definitions. -/
theorem statementFull_iff : StatementFull ↔ Statement :=
  ⟨fun h => h.statement, statementFull_of_statement⟩

/-- The statement on point sets. For every union `X` of two distinct translates
of a lattice of covolume `8π/3` there is a valid configuration `q` whose point
set translates to `X`; every such configuration has the same energy and
defect; Spec's defect at every point of `X` is that defect; and (1.1), its
equality cases and the unique minimizer hold, with the equality cases and the
minimizer as rigid images of BCC and FCC at Wigner–Seitz radius one. -/
theorem StatementFull.physical (h : StatementFull) (X : Set E3) (hX : TwoTranslates X) :
    ∃ q : TwoSite, q.Valid ∧ (∃ v : E3, X = (fun y => y + v) '' physPoints q) ∧
      (∀ (q' : TwoSite) (v' : E3), q'.Valid → X = (fun y => y + v') '' physPoints q' →
        energy q' = energy q ∧ defect q' = defect q) ∧
      (∀ y ∈ X, specSiteDefect ac X y = defect q) ∧
      gap * defect q ≤ energy q - energy bcc ∧
      (energy q - energy bcc = gap * defect q ↔
        RigidImage X (dilate ac bccUnit) ∨ RigidImage X (dilate ac fccUnit)) ∧
      (energy q = energy bcc ↔ RigidImage X (dilate ac bccUnit)) := by
  obtain ⟨q, hq, v, hXv, hD⟩ := h.translates X hX
  have hXP : RigidImage X (physPoints q) := by
    rw [hXv]
    exact rigidImage_translate v _
  have hPX : RigidImage (physPoints q) X := rigidImage_symm hXP
  have hiff (Y : Set E3) : RigidImage X Y ↔ RigidImage (physPoints q) Y :=
    ⟨fun hy => rigidImage_trans hPX hy, fun hy => rigidImage_trans hXP hy⟩
  refine ⟨q, hq, ⟨v, hXv⟩, ?_, hD, h.statement.inequality q hq, ?_, ?_⟩
  · intro q' v' hq' hX'
    have hXP' : RigidImage X (physPoints q') := by
      rw [hX']
      exact rigidImage_translate v' _
    have hP'P : RigidImage (physPoints q') (physPoints q) :=
      rigidImage_trans (rigidImage_symm hXP') hXP
    have hr : RigidImage (specPoints q') (specPoints q) :=
      (rigidImage_dilate_iff ac_positive).mp hP'P
    exact ⟨h.energyRigid q' q hq' hq hr, h.defectRigid q' q hr⟩
  · rw [hiff, hiff]
    exact h.equality q hq
  · rw [hiff]
    exact (h.minimum q hq).2

/-! ### Corollaries of the assembly theorems -/

theorem assemble_full (input : Inputs) : StatementFull :=
  statementFull_of_statement (assemble input)

theorem assemble_full_from_short (anal : GlobalAnalyticInputs) (cover : CompactCover.ShortRoute) :
    StatementFull :=
  statementFull_of_statement (assemble_from_short anal cover)

theorem assemble_full_from_short_cover (cover : ShortRoute) : StatementFull :=
  statementFull_of_statement (assemble_from_short_cover cover)

open CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus in
theorem assemble_full_from_checked_cover (analytic : GlobalAnalyticInputs)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early)
    (sLate : CheckerSound late)
    (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (upstream : Handoff positiveHalf {p | Slots stage5b p})
    (rStage6 : runRows (runStage6 early) stage5b rows = some stage6) (closed : corp.run late stage6 = some []) :
    StatementFull :=
  statementFull_of_statement
    (assemble_from_checked_cover analytic sEarly sLate stage5b stage6 rows corp upstream rStage6 closed)

open CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus in
theorem assemble_full_from_cover_corpus (analytic : GlobalAnalyticInputs)
    {prefixCheck : WitnessRef → Cell → Bool} (prefixSound : SoundCheck prefixCheck)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early)
    (sLate : CheckerSound late)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rStage5b : pre.run prefixCheck = some stage5b)
    (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage6 : runRows (runStage6 early) stage5b rows = some stage6) (closed : corp.run late stage6 = some []) :
    StatementFull :=
  statementFull_of_statement
    (assemble_from_cover_corpus analytic prefixSound sEarly sLate pre stage5b stage6 rStage5b rows corp rStage6
      closed)

open CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus in
theorem assemble_full_from_checked_cover_cover
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early)
    (sLate : CheckerSound late)
    (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (upstream : Handoff positiveHalf {p | Slots stage5b p})
    (rStage6 : runRows (runStage6 early) stage5b rows = some stage6) (closed : corp.run late stage6 = some []) :
    StatementFull :=
  statementFull_of_statement
    (assemble_from_checked_cover_cover sEarly sLate stage5b stage6 rows corp upstream rStage6 closed)

open CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus in
theorem assemble_full_from_cover_corpus_cover
    {prefixCheck : WitnessRef → Cell → Bool} (prefixSound : SoundCheck prefixCheck)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early)
    (sLate : CheckerSound late)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rStage5b : pre.run prefixCheck = some stage5b)
    (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage6 : runRows (runStage6 early) stage5b rows = some stage6) (closed : corp.run late stage6 = some []) :
    StatementFull :=
  statementFull_of_statement
    (assemble_from_cover_corpus_cover prefixSound sEarly sLate pre stage5b stage6 rStage5b rows corp rStage6 closed)

open CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus in
/-- the two-site theorem in full from the corpus whose prefix runs under the Overlay prefix check. -/
theorem assemble_full_from_overlay_corpus (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later : WitnessRef → Cell → Bool}
    (laterSound : SoundCheck later)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early)
    (sLate : CheckerSound late)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom)
    (rStage5b : pre.run (corpusCheck geometric direct sidecar bulk later) = some stage5b)
    (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage6 : runRows (runStage6 early) stage5b rows = some stage6) (closed : corp.run late stage6 = some []) :
    StatementFull :=
  statementFull_of_statement
    (assemble_from_overlay_corpus geometric direct sidecar bulk laterSound sEarly sLate pre stage5b stage6
      rStage5b rows corp rStage6 closed)

end BccSharp.Coulomb.Full
