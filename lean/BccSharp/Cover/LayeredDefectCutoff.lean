import BccSharp.Cover.LayeredDefect
import BccSharp.TwoSite.DefectCutoffBox

set_option autoImplicit false

/-! # The relative defect bound past cost 1/2 (Stage5b cutoff and annulus)

`Layered.defect_transport` (`BccSharp.Cover.LayeredDefect`) proves, for the anchor
`a = anchorOf q f₀` and the displacement `h = R (f − f₀ − n)`,

  `D(q) ≤ D(a) + 200 |h|²` when `D(a) + 200 |h|² ≤ 1/2`.

This module extends it past `1/2` in two ways.

* `defect_transport_cutoff`: the same bound when `D(a) + 200 |h|² ≤ d♯ =
  (600/11)(√2 − 13/10)²`. The anchor's optimal trial is registered by
  `GlobalInputs.Trial.core` (`anchor_registered`): a basis `A` of determinant
  one, within `‖A − O‖²_F ≤ D(a)/100` of a proper rotation `O`, with
  `lattice (A · bccPrimitive) = lattice R ∪ (R f₀ + lattice R)`. Moved by `h`
  on its odd labels it is a trial at `q` of cost `100 ‖A − O‖² + 200 |h|²`
  (`transport_bound`). A BCC point that is neither zero, a star vector nor an
  annular vector has `|e|² ≥ 11/4` (`bcc_point_cases4`), so its image is longer
  than `13/10`; the twelve annular images clear `13/10`
  (`JLeaf.Cutoff.annular_far`). So every lifted neighbour of `q` is matched and
  no annular weight enters (`cutoff_cover`). No literal registration is used.
* `defect_transport_annulus`: at a chart point, for a literal registration
  `(B, N, U, f₀, n)` that passes `registrationCheck` and has strain
  `100 ‖R N − U‖² ≤ 5/2`, `D(q) ≤ D(a) + 200 |h|² + Φ`, where `Φ = annPhi N w p`
  (`w = f₀ + n`) is the sum of the annular weights of the registration's twelve
  annular images at `q`. There is no cost condition: if `D(a) + 200 |h|² ≥ 1`
  the bound is the cap `D(q) ≤ 1`. Otherwise every star image of the
  registration is a star image of the anchor's optimal trial, with the same
  parity (`annulus_cover`, first step), so a lifted neighbour of `q` that the
  transported trial leaves unmatched is one of the registration's annular
  images.
* Whole-box forms: `defect_transport_box_far` (`annFarOk`, so `Φ = 0` and
  `D(q) ≤ D(a) + 200 |h|²` with no cost condition), `defect_transport_box_annulus`
  (`annBoxOk`, `Φ ≤ annCap ℓ`) and `defect_transport_cutoff_of` (a rational `c`
  with `cutoffOk c`). -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.CompactCover.JLeaf (nrm nrm_nonneg nrm_sq nrm_add_le nrm_sub_le nrm_neg
  nrm_zero nrm_mulVec_lower nrm_mulVec_upper frobSq_nonneg star_gap BCCInt half_sq
  half_eq_star registrationCheck ofQ ofQ_mul_eq_one ofQ_orth labelOdd labelInt N_star zVec zVec_cast
  zVec_bcc f0_not_int strainCost strainEntry RegData)
open BccSharp.Coulomb.CompactCover.JLeaf.Cutoff (dSharp ann annTwice bcc_norm11 half_eq_ann
  annular_far annularWeight_nonneg annularWeight_eq_zero annImage annImage_eq annOdd annOdd_eq annPhi
  annPhi_nonneg annFarOk annBoxOk annCap annPhi_le_annCap annFarOk_annBoxOk annCap_far cutoffOk
  cutoffOk_sound)

/-! ### Constants and the BCC shells -/

theorem dSharp_lt : dSharp < 713 / 1000 := by
  unfold dSharp
  have h1 : 13 / 10 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2 : Real.sqrt 2 < 14143 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h3 : (Real.sqrt 2 - 13 / 10) ^ 2 < (1143 / 10000) ^ 2 :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
  have h4 : 600 / 11 * (Real.sqrt 2 - 13 / 10) ^ 2 < 600 / 11 * (1143 / 10000) ^ 2 :=
    mul_lt_mul_of_pos_left h3 (by norm_num)
  have h5 : (600 / 11 : ℝ) * (1143 / 10000) ^ 2 < 713 / 1000 := by norm_num
  linarith

/-- A point of the BCC lattice is zero, a star vector, an annular vector, or has
squared length at least `11/4`. -/
theorem bcc_point_cases4 (z : IntVec) :
    bccPrimitive.mulVec (castVec z) = 0 ∨ (∃ j, bccPrimitive.mulVec (castVec z) = star j) ∨
      (∃ j, bccPrimitive.mulVec (castVec z) = ann j) ∨
      11 / 4 ≤ sq (bccPrimitive.mulVec (castVec z)) := by
  rw [bccPrimitive_mulVec]
  by_cases h0 : bccTwice z = 0
  · left
    funext i
    simp [h0]
  by_cases hs : ∃ j, bccTwice z = starTwice j
  · obtain ⟨j, hj⟩ := hs
    exact Or.inr (Or.inl ⟨j, half_eq_star _ j hj⟩)
  by_cases ha : ∃ j, bccTwice z = annTwice j
  · obtain ⟨j, hj⟩ := ha
    exact Or.inr (Or.inr (Or.inl ⟨j, half_eq_ann _ j hj⟩))
  push Not at hs ha
  right; right; right
  have n11 := bcc_norm11 (bccTwice z) (bccTwice_bcc z) h0 hs ha
  rw [half_sq]
  have : (11 : ℝ) ≤ ((bccTwice z 0 ^ 2 + bccTwice z 1 ^ 2 + bccTwice z 2 ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast n11
  linarith

/-! ### The anchor's registered optimal trial -/

/-- **The anchor's optimal trial, registered.** If `D(a) < 1`, an optimal trial
at the anchor `a = anchorOf q f₀` is registered by `GlobalInputs.Trial.core`: a
basis `A` with `det A = 1` and
`lattice (A · bccPrimitive) = lattice R ∪ (R f₀ + lattice R)`, a proper rotation
`O` with `100 ‖A − O‖²_F ≤ D(a)`, and the parities `ε` of the fourteen star
images (eight odd, balanced; odd images in the odd coset). -/
theorem anchor_registered (q : TwoSite) (hq : q.Valid)
    (hsep₁ : ∀ n : IntVec, n ≠ 0 → (5 / 8 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n)))
    (f₀ : Vec) (half : HalfClass f₀)
    (asep : ∀ n : IntVec, (1 / 2 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n + f₀)))
    (hD : defect (anchorOf q f₀) < 1) :
    ∃ (A O : Mat) (ε : Fin 14 → ℝ), proper O ∧ A.det = 1 ∧
      lattice (A * bccPrimitive) =
        lattice q.basis ∪ translate (q.basis.mulVec f₀) (lattice q.basis) ∧
      100 * frobSq (A - O) ≤ defect (anchorOf q f₀) ∧
      (∀ j, ε j = 0 ∨ ε j = 1) ∧ (∑ j, ε j = 8) ∧ (∀ k : Fin 3, ∑ j, ε j * star j k = 0) ∧
      ∀ j, (ε j = 0 → A.mulVec (star j) ∈ lattice q.basis) ∧
        (ε j = 1 → A.mulVec (star j) ∈ translate (q.basis.mulVec f₀) (lattice q.basis)) := by
  set R := q.basis with hR
  set a := anchorOf q f₀ with haDef
  have ha : a.Valid := anchor_valid q hq f₀ half
  have hsepA : separated a := ⟨hsep₁, asep⟩
  have hinj : Function.Injective R.mulVec := basis_injective q hq
  set D := defect a with hDdef
  have hD1 : cappedDefect (neighbors a) < 1 := hD
  obtain ⟨O, hO, σ, hσ⟩ := cappedDefect_attained (twoSite_neighbors_finite a ha) hD1
  have htail : 0 ≤ ∑' v : ↥(neighbors a),
      if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val := by
    apply tsum_nonneg
    intro v
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  have htrial : 25 * ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) ≤ D := by
    have e : defectTrial O σ = D := hσ
    unfold defectTrial at e
    linarith
  have hsmall : ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) < 1 / 25 := by
    linarith only [htrial, hD]
  have hmem : ∀ j, (σ j : Vec) ∈ a.points := by
    intro j
    have := (σ j).property.1
    simpa only [zero_add] using this
  let T : Trial a := ⟨O, hO, fun j => (σ j : Vec), hmem, hsmall⟩
  obtain ⟨A, f₁, hdetA, half₁, hlat, hcost⟩ := T.core ha hsepA
  have hcost' : 100 * frobSq (A - O) + 200 * sq (R.mulVec (f₀ - f₁)) ≤ D := by
    have e : 25 * ∑ j, sq (T.err j) ≤ D := htrial
    rw [hcost] at e
    have e2 : sq (a.basis.mulVec (a.offset - f₁)) = sq (R.mulVec (f₀ - f₁)) := rfl
    rw [e2] at e
    linarith only [e]
  -- the registered half class is the anchor's
  have hf : f₁ = f₀ := by
    obtain ⟨m, hm⟩ := half.1
    obtain ⟨m', hm'⟩ := half₁.1
    by_cases hz : m - m' = 0
    · have : (2 : ℝ) • f₀ = (2 : ℝ) • f₁ := by rw [hm, hm', sub_eq_zero.mp hz]
      exact (smul_right_injective Vec (two_ne_zero) this).symm
    · have hs := hsep₁ _ hz
      have e : R.mulVec (castVec (m - m')) = (2 : ℝ) • R.mulVec (f₀ - f₁) := by
        rw [castVec_sub', ← hm, ← hm', ← smul_sub, Matrix.mulVec_smul]
      rw [e, sq_smul] at hs
      have hf0 := frobSq_nonneg (A - O)
      nlinarith
  rw [hf] at hlat hcost'
  have hlatR : lattice (A * bccPrimitive) = lattice R ∪ translate (R.mulVec f₀) (lattice R) := hlat
  obtain ⟨ε, h01, hcount, hbal, hcos⟩ := registered_parity R A f₀ half hinj hlatR
  refine ⟨A, O, ε, hO, hdetA, hlatR, ?_, h01, hcount, hbal, hcos⟩
  have : 200 * sq (R.mulVec (f₀ - f₀)) = 0 := by simp [sq]
  linarith

/-! ### The transported trial -/

/-- **The transported trial.** With registered anchor data as in
`anchor_registered`, if `100 ‖A − O‖² < 1` and `200 |h|² < 1`, the star images
moved by `h` on the odd labels form a trial at `q` of raw cost
`100 ‖A − O‖² + 200 |h|²`. If every lifted neighbour of `q` is one of these
images or one of twelve given vectors `img k`, then
`D(q) ≤ 100 ‖A − O‖² + 200 |h|² + Σₖ annularWeight (img k)`. -/
theorem transport_bound (q : TwoSite) (f₀ : Vec) (n : IntVec)
    (A O : Mat) (hO : proper O) (ε : Fin 14 → ℝ)
    (h01 : ∀ j, ε j = 0 ∨ ε j = 1) (hcount : ∑ j, ε j = 8)
    (hbal : ∀ k : Fin 3, ∑ j, ε j * star j k = 0)
    (hcos : ∀ j, (ε j = 0 → A.mulVec (star j) ∈ lattice q.basis) ∧
      (ε j = 1 → A.mulVec (star j) ∈ translate (q.basis.mulVec f₀) (lattice q.basis)))
    (hX : 100 * frobSq (A - O) < 1)
    (hY : 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) < 1)
    (img : Fin 12 → Vec)
    (cover : ∀ v ∈ neighbors q,
      (∃ j, A.mulVec (star j) + ε j • q.basis.mulVec (q.offset - f₀ - castVec n) = v) ∨
        ∃ k, img k = v) :
    defect q ≤ 100 * frobSq (A - O) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) +
      ∑ k, annularWeight (img k) := by
  set R := q.basis with hR
  set h : Vec := R.mulVec (q.offset - f₀ - castVec n) with hh
  set X := frobSq (A - O) with hXdef
  set Y := sq h with hYdef
  have hX0 : 0 ≤ X := frobSq_nonneg _
  have hY0 : 0 ≤ Y := sq_nonnegative h
  set x := Real.sqrt X with hx
  set yy := Real.sqrt Y with hyy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ yy := Real.sqrt_nonneg _
  have hxb : x ≤ 1 / 10 := by
    rw [hx, Real.sqrt_le_left (by norm_num)]
    linarith
  have hyb : yy ≤ 71 / 1000 := by
    rw [hyy, Real.sqrt_le_left (by norm_num)]
    linarith
  have hny : nrm h = yy := rfl
  have UU : O.transpose * O = 1 := hO.1
  have lowerA : ∀ v : Vec, (1 - x) * nrm v ≤ nrm (A.mulVec v) := nrm_mulVec_lower A O UU
  have upperA : ∀ v : Vec, nrm (A.mulVec v) ≤ (1 + x) * nrm v := nrm_mulVec_upper A O UU
  set y : Fin 14 → Vec := fun j => A.mulVec (star j) + ε j • h with hy
  have chiNorm : ∀ j, nrm (ε j • h) ≤ yy := by
    intro j
    rcases h01 j with e | e <;> rw [e]
    · rw [zero_smul, nrm_zero]; exact hy0
    · rw [one_smul]; exact le_of_eq hny
  have starNrm : ∀ j : Fin 14, Real.sqrt (3 / 4) ≤ nrm (star j) ∧ nrm (star j) ≤ 1 := by
    intro j
    obtain ⟨lo, hi⟩ := JLeaf.star_sq_bounds j
    exact ⟨Real.sqrt_le_sqrt lo, by rw [nrm, Real.sqrt_le_left (by norm_num)]; linarith⟩
  have r34 : 866 / 1000 ≤ Real.sqrt (3 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  -- the images are lifted neighbours of `q`
  have ySmall : ∀ j, sq (y j) < (13 / 10) ^ 2 := by
    intro j
    have t := nrm_add_le (A.mulVec (star j)) (ε j • h)
    have u := upperA (star j)
    have c := chiNorm j
    have s := (starNrm j).2
    have m : (1 + x) * nrm (star j) ≤ (1 + x) * 1 :=
      mul_le_mul_of_nonneg_left s (by linarith only [hx0])
    have bound : nrm (y j) ≤ 6 / 5 := by
      show nrm (A.mulVec (star j) + ε j • h) ≤ 6 / 5
      linarith only [t, u, c, m, hxb, hyb]
    rw [← nrm_sq]
    nlinarith only [bound, nrm_nonneg (y j)]
  have yNe : ∀ j, y j ≠ 0 := by
    intro j e0
    have t := nrm_sub_le (A.mulVec (star j)) (ε j • h)
    have l := lowerA (star j)
    have c := chiNorm j
    have s := (starNrm j).1
    have z : nrm (A.mulVec (star j) + ε j • h) = 0 := by
      have : A.mulVec (star j) + ε j • h = 0 := e0
      rw [this, nrm_zero]
    have m : (1 - x) * (866 / 1000) ≤ (1 - x) * nrm (star j) :=
      mul_le_mul_of_nonneg_left (r34.trans s) (by linarith only [hxb])
    linarith only [t, l, c, z, m, hxb, hyb]
  have yInj : ∀ i j, y i = y j → i = j := by
    intro i j e
    by_contra hij
    have gap := star_gap i j hij
    have e' : A.mulVec (star i) + ε i • h = A.mulVec (star j) + ε j • h := e
    have d : A.mulVec (star i - star j) = ε j • h - ε i • h := by
      rw [Matrix.mulVec_sub, sub_eq_sub_iff_add_eq_add, e', add_comm]
    have l := lowerA (star i - star j)
    have ndist : Real.sqrt (3 / 4) ≤ nrm (star i - star j) := Real.sqrt_le_sqrt gap
    have rhs : nrm (ε j • h - ε i • h) ≤ yy := by
      rcases h01 i with ei | ei <;> rcases h01 j with ej | ej <;> rw [ei, ej]
      · simp only [zero_smul, sub_self, nrm_zero]; exact hy0
      · simp only [one_smul, zero_smul, sub_zero]; exact le_of_eq hny
      · simp only [one_smul, zero_smul, zero_sub, nrm_neg]; exact le_of_eq hny
      · simp only [sub_self, nrm_zero]; exact hy0
    rw [d] at l
    have m : (1 - x) * (866 / 1000) ≤ (1 - x) * nrm (star i - star j) :=
      mul_le_mul_of_nonneg_left (r34.trans ndist) (by linarith only [hxb])
    linarith only [l, m, rhs, hxb, hyb]
  have yMem : ∀ j, y j ∈ q.points := by
    intro j
    rcases h01 j with e | e
    · have hl := (hcos j).1 e
      show A.mulVec (star j) + ε j • h ∈ q.points
      rw [e, zero_smul, add_zero]
      exact Or.inl hl
    · obtain ⟨w, ⟨ℓ, rfl⟩, hw⟩ := (hcos j).2 e
      show A.mulVec (star j) + ε j • h ∈ q.points
      rw [e, one_smul, hw, hh]
      right
      refine ⟨R.mulVec (castVec (ℓ - n)), ⟨ℓ - n, rfl⟩, ?_⟩
      rw [castVec_sub', Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_sub]
      abel
  have yNb : ∀ j, y j ∈ neighbors q := fun j => ⟨by simpa using yMem j, yNe j, ySmall j⟩
  let σ' : Fin 14 ↪ ↥(neighbors q) :=
    ⟨fun j => ⟨y j, yNb j⟩, fun i j e => yInj i j (congrArg Subtype.val e)⟩
  -- the trial cost
  have trialEq : defectTrial O σ' = 100 * X + 200 * Y +
      ∑' v : ↥(neighbors q), (if v ∈ Set.range σ' then (0 : ℝ) else annularWeight v.val) := by
    unfold defectTrial
    congr 1
    have terms : ∀ j, (σ' j : Vec) - O.mulVec (star j) = (A - O).mulVec (star j) + ε j • h := by
      intro j
      show A.mulVec (star j) + ε j • h - O.mulVec (star j) = _
      rw [Matrix.sub_mulVec]
      abel
    simp_rw [terms]
    rw [registered_cost (A - O) h ε h01 hcount hbal]
    ring
  -- the unmatched sum is at most the twelve given weights
  obtain ⟨W, hWdef⟩ : ∃ W : Fin 12 → ℝ, W = fun k => annularWeight (img k) := ⟨_, rfl⟩
  have hWk : ∀ k, W k = annularWeight (img k) := fun k => by rw [hWdef]
  have W0 : ∀ k, 0 ≤ W k := fun k => by rw [hWk]; exact annularWeight_nonneg _
  have tailLe : (∑' v : ↥(neighbors q),
      (if v ∈ Set.range σ' then (0 : ℝ) else annularWeight v.val)) ≤ ∑ k : Fin 12, W k := by
    apply Real.tsum_le_of_sum_le
    · intro v
      by_cases hvr : v ∈ Set.range σ'
      · simp [hvr]
      · simp [hvr, annularWeight_nonneg]
    · intro s
      have dom : ∀ v : ↥(neighbors q),
          (if v ∈ Set.range σ' then (0 : ℝ) else annularWeight v.val) ≤
            ∑ k : Fin 12, (if v.val = img k then W k else 0) := by
        intro v
        have nn : ∀ k : Fin 12, 0 ≤ (if v.val = img k then W k else 0) := by
          intro k
          split_ifs
          · exact W0 k
          · exact le_rfl
        split_ifs with hσ
        · exact Finset.sum_nonneg (fun k _ => nn k)
        · rcases cover v.val v.property with ⟨j, hj⟩ | ⟨k, hk⟩
          · exact absurd ⟨j, Subtype.ext hj⟩ hσ
          · have hterm : (if v.val = img k then W k else 0) = annularWeight v.val := by
              split_ifs with hc
              · rw [hWk, hk]
              · exact absurd hk.symm hc
            rw [← hterm]
            exact Finset.single_le_sum (fun k' _ => nn k') (Finset.mem_univ k)
      have atMostOne : ∀ k : Fin 12,
          ∑ v ∈ s, (if v.val = img k then W k else 0) ≤ W k := by
        intro k
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hc : (s.filter (fun v : ↥(neighbors q) => v.val = img k)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          exact Subtype.ext (ha.2.trans hb.2.symm)
        have hcr : ((s.filter (fun v : ↥(neighbors q) => v.val = img k)).card : ℝ) ≤ 1 := by
          exact_mod_cast hc
        nlinarith [W0 k]
      calc ∑ v ∈ s, (if v ∈ Set.range σ' then (0 : ℝ) else annularWeight v.val)
          ≤ ∑ v ∈ s, ∑ k : Fin 12, (if v.val = img k then W k else 0) :=
            Finset.sum_le_sum (fun v _ => dom v)
        _ = ∑ k : Fin 12, ∑ v ∈ s, (if v.val = img k then W k else 0) := Finset.sum_comm
        _ ≤ ∑ k : Fin 12, W k := Finset.sum_le_sum (fun k _ => atMostOne k)
  -- conclusion
  have bdd : BddBelow (defectCandidates (neighbors q)) := by
    refine ⟨0, fun c hc => ?_⟩
    rcases Set.mem_insert_iff.mp hc with rfl | ⟨U', _, τ, rfl⟩
    · norm_num
    · apply add_nonneg
      · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => sq_nonnegative _))
      · apply tsum_nonneg
        intro v
        split_ifs
        · exact le_rfl
        · exact le_max_left _ _
  have memC : defectTrial O σ' ∈ defectCandidates (neighbors q) :=
    Set.mem_insert_of_mem _ ⟨O, hO, σ', rfl⟩
  have le := csInf_le bdd memC
  rw [trialEq] at le
  have hsum : ∑ k, annularWeight (img k) = ∑ k : Fin 12, W k :=
    Finset.sum_congr rfl (fun k _ => (hWk k).symm)
  rw [hsum]
  unfold defect cappedDefect
  linarith

/-! ### The cutoff form -/

/-- Below the cutoff every lifted neighbour of `q` is a transported star image. -/
theorem cutoff_cover (q : TwoSite) (hq : q.Valid) (f₀ : Vec) (half : HalfClass f₀) (n : IntVec)
    (A O : Mat) (hO : proper O) (hdetA : A.det = 1) (ε : Fin 14 → ℝ)
    (h01 : ∀ j, ε j = 0 ∨ ε j = 1)
    (hcos : ∀ j, (ε j = 0 → A.mulVec (star j) ∈ lattice q.basis) ∧
      (ε j = 1 → A.mulVec (star j) ∈ translate (q.basis.mulVec f₀) (lattice q.basis)))
    (hlat : lattice (A * bccPrimitive) =
      lattice q.basis ∪ translate (q.basis.mulVec f₀) (lattice q.basis))
    (hX : 100 * frobSq (A - O) < 1)
    (hY : 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) < 1)
    (hfar : 100 * frobSq (A - O) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤ dSharp)
    (img : Fin 12 → Vec) :
    ∀ v ∈ neighbors q,
      (∃ j, A.mulVec (star j) + ε j • q.basis.mulVec (q.offset - f₀ - castVec n) = v) ∨
        ∃ k, img k = v := by
  intro v hvn
  left
  set R := q.basis with hR
  set h : Vec := R.mulVec (q.offset - f₀ - castVec n) with hh
  set X := frobSq (A - O) with hXdef
  set Y := sq h with hYdef
  have hX0 : 0 ≤ X := frobSq_nonneg _
  have hY0 : 0 ≤ Y := sq_nonnegative h
  set x := Real.sqrt X with hx
  set yy := Real.sqrt Y with hyy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ yy := Real.sqrt_nonneg _
  have hxb : x ≤ 1 / 10 := by
    rw [hx, Real.sqrt_le_left (by norm_num)]
    linarith
  have hyb : yy ≤ 71 / 1000 := by
    rw [hyy, Real.sqrt_le_left (by norm_num)]
    linarith
  have hny : nrm h = yy := rfl
  have UU : O.transpose * O = 1 := hO.1
  have lowerA : ∀ v : Vec, (1 - x) * nrm v ≤ nrm (A.mulVec v) := nrm_mulVec_lower A O UU
  set s11 := Real.sqrt (11 / 4) with hs11d
  have hs11b : 1658 / 1000 ≤ s11 := by
    rw [hs11d, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have far : 13 / 10 < (1 - x) * s11 - yy := by
    have m : (1 - x) * (1658 / 1000) ≤ (1 - x) * s11 :=
      mul_le_mul_of_nonneg_left hs11b (by linarith only [hxb])
    linarith only [m, hxb, hyb]
  have hinj : Function.Injective R.mulVec := basis_injective q hq
  have htn : R.mulVec f₀ ∉ lattice R := by
    rintro ⟨k, hk⟩
    exact half.2 k (hinj hk).symm
  have farImage : ∀ z : IntVec, 11 / 4 ≤ sq (bccPrimitive.mulVec (castVec z)) →
      (1 - x) * s11 ≤ nrm (A.mulVec (bccPrimitive.mulVec (castVec z))) := by
    intro z hz
    have ne : s11 ≤ nrm (bccPrimitive.mulVec (castVec z)) := Real.sqrt_le_sqrt hz
    have l := lowerA (bccPrimitive.mulVec (castVec z))
    have m : (1 - x) * s11 ≤ (1 - x) * nrm (bccPrimitive.mulVec (castVec z)) :=
      mul_le_mul_of_nonneg_left ne (by linarith only [hxb])
    linarith only [l, m]
  have inLattice : ∀ w : Vec, w ∈ lattice R ∪ translate (R.mulVec f₀) (lattice R) →
      ∃ z : IntVec, w = A.mulVec (bccPrimitive.mulVec (castVec z)) := by
    intro w hw
    rw [← hlat] at hw
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, by rw [← hz, Matrix.mulVec_mulVec]⟩
  have annFar : ∀ (k : Fin 12) (χ : Bool),
      13 / 10 ≤ nrm (A.mulVec (ann k) + if χ then h else 0) :=
    annular_far A O UU hdetA h hfar
  obtain ⟨hpt, hv0, hvs⟩ := hvn
  rw [zero_add] at hpt
  have big : ∀ t : ℝ, 13 / 10 ≤ t → t ≤ nrm v → False := by
    intro t ht tv
    have lt : (13 / 10 : ℝ) ≤ nrm v := le_trans ht tv
    have sqv : (13 / 10 : ℝ) ^ 2 ≤ sq v := by
      rw [← nrm_sq]
      nlinarith [nrm_nonneg v]
    exact absurd hvs (not_lt.mpr sqv)
  rcases hpt with hl | ht
  · -- an even point
    obtain ⟨z, hz⟩ := inLattice v (Or.inl hl)
    rcases bcc_point_cases4 z with h0 | ⟨j, hj⟩ | ⟨k, hk⟩ | h11
    · exact absurd (by rw [hz, h0, Matrix.mulVec_zero]) hv0
    · rw [hj] at hz
      refine ⟨j, ?_⟩
      rcases h01 j with e | e
      · rw [e, zero_smul, add_zero, hz]
      · exfalso
        obtain ⟨w, hw, hwe⟩ := (hcos j).2 e
        have hin : A.mulVec (star j) ∈ lattice R := by rw [← hz]; exact hl
        rw [hwe] at hin
        have := lattice_sub R hin hw
        rw [add_sub_cancel_left] at this
        exact htn this
    · exfalso
      rw [hk] at hz
      have hf := annFar k false
      simp only [Bool.false_eq_true, ite_false, add_zero] at hf
      rw [← hz] at hf
      exact big _ le_rfl hf
    · exfalso
      have fi := farImage z h11
      rw [← hz] at fi
      exact big _ (by linarith only [far, hy0]) fi
  · -- an odd point: `v − h` is an odd point of the anchor lattice
    obtain ⟨u, ⟨ℓ, rfl⟩, hu⟩ := ht
    have hvh : v - h ∈ translate (R.mulVec f₀) (lattice R) := by
      refine ⟨R.mulVec (castVec (ℓ + n)), ⟨ℓ + n, rfl⟩, ?_⟩
      rw [hu, hh, castVec_add, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub]
      abel
    obtain ⟨z, hz⟩ := inLattice (v - h) (Or.inr hvh)
    have notEven : v - h ∉ lattice R := by
      intro hin
      obtain ⟨w, hw, hwe⟩ := hvh
      rw [hwe] at hin
      have := lattice_sub R hin hw
      rw [add_sub_cancel_left] at this
      exact htn this
    rcases bcc_point_cases4 z with h0 | ⟨j, hj⟩ | ⟨k, hk⟩ | h11
    · exfalso
      apply notEven
      rw [hz, h0, Matrix.mulVec_zero]
      exact lattice_zero R
    · rw [hj] at hz
      refine ⟨j, ?_⟩
      rcases h01 j with e | e
      · exfalso
        exact notEven (by rw [hz]; exact (hcos j).1 e)
      · rw [e, one_smul, ← hz]
        abel
    · exfalso
      rw [hk] at hz
      have hf := annFar k true
      simp only [ite_true] at hf
      have e : A.mulVec (ann k) + h = v := by
        rw [← hz]
        abel
      rw [e] at hf
      exact big _ le_rfl hf
    · exfalso
      have fi := farImage z h11
      rw [← hz] at fi
      have t := nrm_add_le v (-h)
      rw [nrm_neg, ← sub_eq_add_neg, hny] at t
      exact big ((1 - x) * s11 - yy) far.le (by linarith only [t, fi])

/-- **The relative defect bound up to the Stage5b cutoff.** If
`D(a) + 200 |h|² ≤ d♯ = (600/11)(√2 − 13/10)²`, then `D(q) ≤ D(a) + 200 |h|²`,
with `a = anchorOf q f₀` and `h = R (f − f₀ − n)`. The hypotheses are those of
`defect_transport`; no literal registration is used. -/
theorem defect_transport_cutoff (q : TwoSite) (hq : q.Valid)
    (hsep₁ : ∀ n : IntVec, n ≠ 0 → (5 / 8 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n)))
    (f₀ : Vec) (half : HalfClass f₀)
    (asep : ∀ n : IntVec, (1 / 2 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n + f₀)))
    (n : IntVec)
    (cut : defect (anchorOf q f₀) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤
      dSharp) :
    defect q ≤ defect (anchorOf q f₀) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) := by
  have hb0 : 0 ≤ sq (q.basis.mulVec (q.offset - f₀ - castVec n)) := sq_nonnegative _
  have hda : 0 ≤ defect (anchorOf q f₀) := (defect_range _).1
  have hds := dSharp_lt
  have hD : defect (anchorOf q f₀) < 1 := by linarith
  obtain ⟨A, O, ε, hO, hdetA, hlat, hXD, h01, hcount, hbal, hcos⟩ :=
    anchor_registered q hq hsep₁ f₀ half asep hD
  have hX : 100 * frobSq (A - O) < 1 := by linarith
  have hY : 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) < 1 := by linarith
  have hfar : 100 * frobSq (A - O) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤
      dSharp := by
    linarith
  have cover := cutoff_cover q hq f₀ half n A O hO hdetA ε h01 hcos hlat hX hY hfar
    (fun k => A.mulVec (ann k) + q.basis.mulVec (q.offset - f₀ - castVec n))
  have bound := transport_bound q f₀ n A O hO ε h01 hcount hbal hcos hX hY
    (fun k => A.mulVec (ann k) + q.basis.mulVec (q.offset - f₀ - castVec n)) cover
  have zero : ∑ k : Fin 12,
      annularWeight (A.mulVec (ann k) + q.basis.mulVec (q.offset - f₀ - castVec n)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply annularWeight_eq_zero
    have hk := annular_far A O hO.1 hdetA _ hfar k true
    simpa using hk
  rw [zero, add_zero] at bound
  linarith

/-- The cutoff form with a rational bound: if `D(a) ≤ dA` and
`dA + 200 |h|² ≤ c` with `cutoffOk c`, then `D(q) ≤ D(a) + 200 |h|²`. -/
theorem defect_transport_cutoff_of (q : TwoSite) (hq : q.Valid)
    (hsep₁ : ∀ n : IntVec, n ≠ 0 → (5 / 8 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n)))
    (f₀ : Vec) (half : HalfClass f₀)
    (asep : ∀ n : IntVec, (1 / 2 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n + f₀)))
    (n : IntVec) (dA : ℝ) (hdA : defect (anchorOf q f₀) ≤ dA) (c : ℚ) (hc : cutoffOk c = true)
    (hle : dA + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤ (c : ℝ)) :
    defect q ≤ defect (anchorOf q f₀) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) :=
  defect_transport_cutoff q hq hsep₁ f₀ half asep n (by
    have := cutoffOk_sound hc
    linarith)

/-! ### The annulus form with a literal registration -/

/-- `chartBasis p · N` entrywise. -/
theorem chartMul_entry (N : Fin 3 → Fin 3 → ℚ) (p : Chart) (i j : Fin 3) :
    (chartBasis p * ofQ N) i j = strainEntry N p i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> simp [strainEntry, chartBasis, ofQ] <;> ring

theorem strainCost_eq_frobSq (N U : Fin 3 → Fin 3 → ℚ) (p : Chart) :
    strainCost N U p = frobSq (chartBasis p * ofQ N - ofQ U) := by
  unfold strainCost frobSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.sub_apply, chartMul_entry]
  simp [ofQ]

/-- **Classification for the annulus form.** With the anchor data of
`anchor_registered` (`100 ‖A − O‖² < 1`, `200 |h|² < 1`) and a literal
registration of strain `100 ‖R N − U‖² ≤ 5/2`, every lifted neighbour of `q` is a
transported star image or one of the registration's annular images. -/
theorem annulus_cover (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (n : IntVec)
    (ok : registrationCheck B N U f0 = true) (p : Chart)
    (hstrain : 100 * strainCost N U p ≤ 5 / 2) (hv : (chartPoint p).Valid)
    (A O : Mat) (hO : proper O) (ε : Fin 14 → ℝ) (h01 : ∀ j, ε j = 0 ∨ ε j = 1)
    (hcos : ∀ j, (ε j = 0 → A.mulVec (star j) ∈ lattice (chartPoint p).basis) ∧
      (ε j = 1 → A.mulVec (star j) ∈
        translate ((chartPoint p).basis.mulVec (fun i => (f0 i : ℝ))) (lattice (chartPoint p).basis)))
    (hlat : lattice (A * bccPrimitive) = lattice (chartPoint p).basis ∪
      translate ((chartPoint p).basis.mulVec (fun i => (f0 i : ℝ))) (lattice (chartPoint p).basis))
    (hX : 100 * frobSq (A - O) < 1)
    (hY : 200 * sq ((chartPoint p).basis.mulVec
      ((chartPoint p).offset - (fun i => (f0 i : ℝ)) - castVec n)) < 1) :
    ∀ v ∈ neighbors (chartPoint p),
      (∃ j, A.mulVec (star j) + ε j • (chartPoint p).basis.mulVec
          ((chartPoint p).offset - (fun i => (f0 i : ℝ)) - castVec n) = v) ∨
        ∃ k, annImage N (fun i => f0 i + (n i : ℚ)) k p = v := by
  intro v hvn
  unfold registrationCheck at ok
  obtain ⟨hNB, hBN, hUU, hdet, h2B, hcol, h2Bf, hzf, hf0, hshift, hcnt, hbal⟩ :=
    of_decide_eq_true ok
  set R : Mat := (chartPoint p).basis with hR
  set f : Vec := (chartPoint p).offset with hf
  set f0r : Vec := fun i => (f0 i : ℝ) with hf0r
  set Br := ofQ B with hBr
  set Nr := ofQ N with hNr
  set Ur := ofQ U with hUr
  set A' : Mat := R * Nr with hA'
  set h : Vec := R.mulVec (f - f0r - castVec n) with hh
  have NB : Nr * Br = 1 := ofQ_mul_eq_one N B hNB
  have UU' : Ur.transpose * Ur = 1 := ofQ_orth U hUU
  have AB : ∀ u : Vec, A'.mulVec (Br.mulVec u) = R.mulVec u := by
    intro u
    rw [hA', Matrix.mulVec_mulVec, Matrix.mul_assoc, NB, Matrix.mul_one]
  have NBv : ∀ u : Vec, Nr.mulVec (Br.mulVec u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, NB, Matrix.one_mulVec]
  have notInt : ∀ m : IntVec, f0r ≠ castVec m := f0_not_int f0 hf0
  have hinj : Function.Injective R.mulVec := basis_injective (chartPoint p) hv
  have htn : R.mulVec f0r ∉ lattice R := by
    rintro ⟨k, hk⟩
    exact notInt k (hinj hk).symm
  -- Star data of the registration.
  have Ns : ∀ j : Fin 14, Nr.mulVec (star j) =
      castVec (labelInt N f0 j) + (if labelOdd N j then f0r else 0) :=
    N_star N f0 hshift
  have parity : ∀ (j : Fin 14) (κ : IntVec) (c : Bool),
      Nr.mulVec (star j) = castVec κ + (if c then f0r else 0) → labelOdd N j = c := by
    intro j κ c e
    rw [Ns j] at e
    cases hj : labelOdd N j <;> cases c
    · rfl
    · rw [hj] at e
      exfalso
      apply notInt (labelInt N f0 j - κ)
      have e' : castVec (labelInt N f0 j) = castVec κ + f0r := by simpa using e
      funext i
      have := congrFun e' i
      simp only [Pi.add_apply, Pi.sub_apply, castVec, Int.cast_sub] at this ⊢
      linarith only [this]
    · rw [hj] at e
      exfalso
      apply notInt (κ - labelInt N f0 j)
      have e' : castVec (labelInt N f0 j) + f0r = castVec κ := by simpa using e
      funext i
      have := congrFun e' i
      simp only [Pi.add_apply, Pi.sub_apply, castVec, Int.cast_sub] at this ⊢
      linarith only [this]
    · rfl
  have starAlt : ∀ k : Fin 14, A'.mulVec (star k) =
      R.mulVec (castVec (labelInt N f0 k)) + (if labelOdd N k then R.mulVec f0r else 0) := by
    intro k
    have hs : star k = Br.mulVec (Nr.mulVec (star k)) := by
      rw [Matrix.mulVec_mulVec, ofQ_mul_eq_one B N hBN, Matrix.one_mulVec]
    rw [hs, AB, Ns k]
    cases labelOdd N k
    · simp
    · simp [Matrix.mulVec_add]
  -- Lengths.
  set X := frobSq (A - O) with hXdef
  set X' := frobSq (A' - Ur) with hX'def
  set Y := sq h with hYdef
  have hX0 : 0 ≤ X := frobSq_nonneg _
  have hX'0 : 0 ≤ X' := frobSq_nonneg _
  have hY0 : 0 ≤ Y := sq_nonnegative h
  have hX'le : X' ≤ 1 / 40 := by
    have e := strainCost_eq_frobSq N U p
    have e2 : X' = frobSq (chartBasis p * ofQ N - ofQ U) := rfl
    linarith
  set x := Real.sqrt X with hx
  set x' := Real.sqrt X' with hx'
  set yy := Real.sqrt Y with hyy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx'0 : 0 ≤ x' := Real.sqrt_nonneg _
  have hy0 : 0 ≤ yy := Real.sqrt_nonneg _
  have hxb : x ≤ 1 / 10 := by
    rw [hx, Real.sqrt_le_left (by norm_num)]
    linarith
  have hx'b : x' ≤ 1582 / 10000 := by
    rw [hx', Real.sqrt_le_left (by norm_num)]
    linarith
  have hyb : yy ≤ 71 / 1000 := by
    rw [hyy, Real.sqrt_le_left (by norm_num)]
    linarith
  have hny : nrm h = yy := rfl
  have UU : O.transpose * O = 1 := hO.1
  have lowerA : ∀ u : Vec, (1 - x) * nrm u ≤ nrm (A.mulVec u) := nrm_mulVec_lower A O UU
  have lowerA' : ∀ u : Vec, (1 - x') * nrm u ≤ nrm (A'.mulVec u) := nrm_mulVec_lower A' Ur UU'
  have upperA' : ∀ u : Vec, nrm (A'.mulVec u) ≤ (1 + x') * nrm u := nrm_mulVec_upper A' Ur UU'
  have starNrm : ∀ j : Fin 14, Real.sqrt (3 / 4) ≤ nrm (star j) ∧ nrm (star j) ≤ 1 := by
    intro j
    obtain ⟨lo, hi⟩ := JLeaf.star_sq_bounds j
    exact ⟨Real.sqrt_le_sqrt lo, by rw [nrm, Real.sqrt_le_left (by norm_num)]; linarith⟩
  have r34 : 866 / 1000 ≤ Real.sqrt (3 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  set s2 := Real.sqrt 2 with hs2d
  have hs2b : 14142 / 10000 ≤ s2 := by
    rw [hs2d, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  set s11 := Real.sqrt (11 / 4) with hs11d
  have hs11b : 1658 / 1000 ≤ s11 := by
    rw [hs11d, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have far' : 13 / 10 < (1 - x') * s11 - yy := by
    have m : (1 - x') * (1658 / 1000) ≤ (1 - x') * s11 :=
      mul_le_mul_of_nonneg_left hs11b (by linarith only [hx'b])
    linarith only [m, hx'b, hyb]
  -- The registration's star images are star images of `A`, with the same parity.
  have starCo : ∀ k : Fin 14, ∃ j, A'.mulVec (star k) = A.mulVec (star j) ∧
      (ε j = 1 ↔ labelOdd N k = true) := by
    intro k
    have hmem : A'.mulVec (star k) ∈ lattice R ∪ translate (R.mulVec f0r) (lattice R) := by
      rw [starAlt k]
      cases labelOdd N k
      · left
        exact ⟨labelInt N f0 k, by simp⟩
      · right
        exact ⟨R.mulVec (castVec (labelInt N f0 k)), ⟨labelInt N f0 k, rfl⟩, by simp⟩
    rw [← hlat] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hz' : A'.mulVec (star k) = A.mulVec (bccPrimitive.mulVec (castVec z)) := by
      rw [← hz, Matrix.mulVec_mulVec]
    rcases bcc_point_cases z with h0 | ⟨j, hj⟩ | h2
    · exfalso
      rw [h0, Matrix.mulVec_zero] at hz'
      have l := lowerA' (star k)
      have s := (starNrm k).1
      rw [hz', nrm_zero] at l
      have m : (1 - x') * (866 / 1000) ≤ (1 - x') * nrm (star k) :=
        mul_le_mul_of_nonneg_left (r34.trans s) (by linarith only [hx'b])
      linarith only [l, m, hx'b]
    · rw [hj] at hz'
      refine ⟨j, hz', ?_⟩
      constructor
      · intro e1
        by_contra hk
        have hkf : labelOdd N k = false := by simpa using hk
        obtain ⟨w', hw', hwe⟩ := (hcos j).2 e1
        have hin : A.mulVec (star j) ∈ lattice R := by
          rw [← hz', starAlt k, hkf]
          simp only [Bool.false_eq_true, ite_false, add_zero]
          exact ⟨labelInt N f0 k, rfl⟩
        rw [hwe] at hin
        have := lattice_sub R hin hw'
        rw [add_sub_cancel_left] at this
        exact htn this
      · intro hk
        rcases h01 j with e0 | e1
        · exfalso
          have hin := (hcos j).1 e0
          rw [← hz', starAlt k, hk] at hin
          simp only [ite_true] at hin
          have := lattice_sub R hin ⟨labelInt N f0 k, rfl⟩
          rw [add_sub_cancel_left] at this
          exact htn this
        · exact e1
    · exfalso
      have u := upperA' (star k)
      have s := (starNrm k).2
      have ne : s2 ≤ nrm (bccPrimitive.mulVec (castVec z)) := Real.sqrt_le_sqrt h2
      have l := lowerA (bccPrimitive.mulVec (castVec z))
      rw [← hz'] at l
      have m1 : (1 + x') * nrm (star k) ≤ (1 + x') * 1 :=
        mul_le_mul_of_nonneg_left s (by linarith only [hx'0])
      have m2 : (1 - x) * s2 ≤ (1 - x) * nrm (bccPrimitive.mulVec (castVec z)) :=
        mul_le_mul_of_nonneg_left ne (by linarith only [hxb])
      have m3 : (1 - x) * (14142 / 10000) ≤ (1 - x) * s2 :=
        mul_le_mul_of_nonneg_left hs2b (by linarith only [hxb])
      linarith only [u, m1, m2, m3, l, hxb, hx'b]
  -- The registration's annular images.
  have annOddImg : ∀ j, annOdd N j = true →
      annImage N (fun i => f0 i + (n i : ℚ)) j p = A'.mulVec (ann j) + h := by
    intro j hj
    rw [annImage_eq, hj]
    simp only [ite_true]
    congr 1
    rw [hh]
    congr 1
    funext i
    simp only [Pi.sub_apply, hf, hf0r, castVec]
    push_cast
    ring
  have annEvenImg : ∀ j, annOdd N j = false →
      annImage N (fun i => f0 i + (n i : ℚ)) j p = A'.mulVec (ann j) := by
    intro j hj
    rw [annImage_eq, hj]
    simp only [Bool.false_eq_true, ite_false, add_zero]
    rfl
  -- Points of `2 · BCC` outside the star and the annulus.
  have farImage : ∀ (e : Vec) (z : IntVec), BCCInt z → z ≠ 0 → (∀ j, z ≠ starTwice j) →
      (∀ j, z ≠ annTwice j) → e = (fun i => ((z i : ℤ) : ℝ) / 2) →
      (1 - x') * s11 ≤ nrm (A'.mulVec e) := by
    intro e z hz z0 zs za he
    have n11 := bcc_norm11 z hz z0 zs za
    have se : 11 / 4 ≤ sq e := by
      rw [he, half_sq]
      have : (11 : ℝ) ≤ ((z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 : ℤ) : ℝ) := by exact_mod_cast n11
      linarith only [this]
    have ne : s11 ≤ nrm e := Real.sqrt_le_sqrt se
    have l := lowerA' e
    have m : (1 - x') * s11 ≤ (1 - x') * nrm e :=
      mul_le_mul_of_nonneg_left ne (by linarith only [hx'b])
    linarith only [l, m]
  -- The classification.
  obtain ⟨hpt, hv0, hvs⟩ := hvn
  rw [zero_add] at hpt
  have big : ∀ t : ℝ, 13 / 10 < t → t ≤ nrm v → False := by
    intro t ht tv
    have lt : (13 / 10 : ℝ) < nrm v := lt_of_lt_of_le ht tv
    have sqv : (13 / 10 : ℝ) ^ 2 < nrm v ^ 2 := pow_lt_pow_left₀ lt (by norm_num) (by norm_num)
    rw [nrm_sq] at sqv
    exact absurd hvs (not_lt.mpr sqv.le)
  rcases hpt with hl | ht
  · -- `v = R k`
    obtain ⟨k, hk⟩ := hl
    have hk' : R.mulVec (castVec k) = v := hk
    set e := Br.mulVec (castVec k + (if false then f0r else 0)) with he
    have ze := zVec_cast B f0 k false h2B h2Bf
    have Ae : A'.mulVec e = v := by
      rw [he, AB]
      simpa using hk'
    have Ne : Nr.mulVec e = castVec k + (if false then f0r else 0) := NBv _
    by_cases hs : ∃ j, zVec B f0 k false = starTwice j
    · obtain ⟨j₀, hj₀⟩ := hs
      have es : e = star j₀ := by
        rw [he, ze]
        exact half_eq_star _ j₀ hj₀
      have odd := parity j₀ k false (by rw [← es]; exact Ne)
      obtain ⟨j, hAj, hpar⟩ := starCo j₀
      have ej : ε j = 0 := by
        rcases h01 j with e0 | e1
        · exact e0
        · exfalso
          rw [odd] at hpar
          exact Bool.false_ne_true (hpar.mp e1)
      left
      refine ⟨j, ?_⟩
      rw [ej, zero_smul, add_zero, ← hAj, ← es]
      exact Ae
    · push Not at hs
      by_cases ha : ∃ j, zVec B f0 k false = annTwice j
      · obtain ⟨j, hj⟩ := ha
        have ea : e = ann j := by
          rw [he, ze]
          exact half_eq_ann _ j hj
        have odd := annOdd_eq N f0 hf0 j k false (by rw [← ea]; exact Ne)
        right
        refine ⟨j, ?_⟩
        rw [annEvenImg j odd, ← ea]
        exact Ae
      · push Not at ha
        have z0 : zVec B f0 k false ≠ 0 := by
          intro z0
          apply hv0
          rw [← Ae, he, ze, z0]
          have : (fun i : Fin 3 => (((0 : IntVec) i : ℤ) : ℝ) / 2) = 0 := by
            funext i
            simp
          rw [this, Matrix.mulVec_zero]
        have fi := farImage e (zVec B f0 k false) (zVec_bcc B f0 k false hcol hzf) z0 hs ha
          (by rw [he, ze])
        rw [Ae] at fi
        exact (big _ (by linarith only [far', hy0]) fi).elim
  · -- `v = R k + R f`
    obtain ⟨yv, ⟨k, hk⟩, hyv⟩ := ht
    have hk' : R.mulVec (castVec k) = yv := hk
    set κ : IntVec := k + n with hκ
    set e := Br.mulVec (castVec κ + (if true then f0r else 0)) with he
    have ze := zVec_cast B f0 κ true h2B h2Bf
    have Ae : A'.mulVec e + h = v := by
      rw [he, AB, hyv, ← hk', hh, hκ, castVec_add]
      simp only [ite_true, Matrix.mulVec_add, Matrix.mulVec_sub]
      abel
    have Ne : Nr.mulVec e = castVec κ + (if true then f0r else 0) := NBv _
    by_cases hs : ∃ j, zVec B f0 κ true = starTwice j
    · obtain ⟨j₀, hj₀⟩ := hs
      have es : e = star j₀ := by
        rw [he, ze]
        exact half_eq_star _ j₀ hj₀
      have odd := parity j₀ κ true (by rw [← es]; exact Ne)
      obtain ⟨j, hAj, hpar⟩ := starCo j₀
      have ej : ε j = 1 := hpar.mpr odd
      left
      refine ⟨j, ?_⟩
      rw [ej, one_smul, ← hAj, ← es]
      exact Ae
    · push Not at hs
      by_cases ha : ∃ j, zVec B f0 κ true = annTwice j
      · obtain ⟨j, hj⟩ := ha
        have ea : e = ann j := by
          rw [he, ze]
          exact half_eq_ann _ j hj
        have odd := annOdd_eq N f0 hf0 j κ true (by rw [← ea]; exact Ne)
        right
        refine ⟨j, ?_⟩
        rw [annOddImg j odd, ← ea]
        exact Ae
      · push Not at ha
        have z0 : zVec B f0 κ true ≠ 0 := by
          intro z0
          have e0 : e = 0 := by
            rw [he, ze, z0]
            funext i
            simp
          have hz : castVec κ + f0r = 0 := by
            have h1 := Ne
            rw [e0, Matrix.mulVec_zero] at h1
            simpa using h1.symm
          apply notInt (-κ)
          rw [castVec_neg]
          funext i
          have := congrFun hz i
          simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at this ⊢
          linarith only [this]
        have fi := farImage e (zVec B f0 κ true) (zVec_bcc B f0 κ true hcol hzf) z0 hs ha
          (by rw [he, ze])
        have t := nrm_sub_le (A'.mulVec e) h
        rw [Ae, hny] at t
        exact (big ((1 - x') * s11 - yy) far' (by linarith only [t, fi])).elim

/-- **The relative defect bound with annulus penalties.** For a literal
registration `(B, N, U, f₀, n)` passing `registrationCheck` with strain
`100 ‖R N − U‖² ≤ 5/2` at a valid chart point `p` (with the separations of
`defect_transport`, the anchor class `f₀`): `D(q) ≤ D(a) + 200 |h|² + Φ`, where
`a = anchorOf q f₀`, `h = R (f − f₀ − n)` and `Φ = annPhi N (f₀ + n) p`. There is
no condition on the cost. -/
theorem defect_transport_annulus (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (n : IntVec)
    (ok : registrationCheck B N U f0 = true) (p : Chart)
    (hstrain : 100 * strainCost N U p ≤ 5 / 2) (hv : (chartPoint p).Valid)
    (hsep₁ : ∀ m : IntVec, m ≠ 0 →
      (5 / 8 : ℝ) ^ 2 < sq ((chartPoint p).basis.mulVec (castVec m)))
    (half : HalfClass (fun i => (f0 i : ℝ)))
    (asep : ∀ m : IntVec, (1 / 2 : ℝ) ^ 2 <
      sq ((chartPoint p).basis.mulVec (castVec m + fun i => (f0 i : ℝ)))) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) (fun i => (f0 i : ℝ))) +
      200 * sq ((chartPoint p).basis.mulVec
        ((chartPoint p).offset - (fun i => (f0 i : ℝ)) - castVec n)) +
      annPhi N (fun i => f0 i + (n i : ℚ)) p := by
  have phi0 := annPhi_nonneg N (fun i => f0 i + (n i : ℚ)) p
  have hda := (defect_range (anchorOf (chartPoint p) (fun i => (f0 i : ℝ)))).1
  have hY0 : 0 ≤ sq ((chartPoint p).basis.mulVec
      ((chartPoint p).offset - (fun i => (f0 i : ℝ)) - castVec n)) := sq_nonnegative _
  by_cases big : 1 ≤ defect (anchorOf (chartPoint p) (fun i => (f0 i : ℝ))) +
      200 * sq ((chartPoint p).basis.mulVec
        ((chartPoint p).offset - (fun i => (f0 i : ℝ)) - castVec n))
  · have := (defect_range (chartPoint p)).2
    linarith
  push Not at big
  have hD : defect (anchorOf (chartPoint p) (fun i => (f0 i : ℝ))) < 1 := by linarith
  have hY : 200 * sq ((chartPoint p).basis.mulVec
      ((chartPoint p).offset - (fun i => (f0 i : ℝ)) - castVec n)) < 1 := by linarith
  obtain ⟨A, O, ε, hO, _hdetA, hlat, hXD, h01, hcount, hbal, hcos⟩ :=
    anchor_registered (chartPoint p) hv hsep₁ (fun i => (f0 i : ℝ)) half asep hD
  have hX : 100 * frobSq (A - O) < 1 := by linarith
  have cover := annulus_cover B N U f0 n ok p hstrain hv A O hO ε h01 hcos hlat hX hY
  have bound := transport_bound (chartPoint p) (fun i => (f0 i : ℝ)) n A O hO ε h01 hcount hbal
    hcos hX hY (fun k => annImage N (fun i => f0 i + (n i : ℚ)) k p) cover
  have e : (∑ k, annularWeight (annImage N (fun i => f0 i + (n i : ℚ)) k p)) =
      annPhi N (fun i => f0 i + (n i : ℚ)) p := rfl
  rw [e] at bound
  linarith

/-! ### Whole-box forms -/

/-- **Annulus, transported, whole box.** At every point of the box where the
pointwise hypotheses hold (validity, the two separations, the half class and the
strain bound), `D(q) ≤ D(a) + 200 |h|² + annCap ℓ`. -/
theorem defect_transport_box_annulus (reg : RegData) (b : Cell) (ℓ : Fin 12 → ℚ)
    (hr : registrationCheck reg.B reg.N reg.U reg.f0 = true)
    (ha : annBoxOk reg.N reg.w b ℓ = true) (p : Chart) (hp : b.Mem p)
    (hstrain : 100 * strainCost reg.N reg.U p ≤ 5 / 2) (hv : (chartPoint p).Valid)
    (hsep₁ : ∀ m : IntVec, m ≠ 0 →
      (5 / 8 : ℝ) ^ 2 < sq ((chartPoint p).basis.mulVec (castVec m)))
    (half : HalfClass (fun i => (reg.f0 i : ℝ)))
    (asep : ∀ m : IntVec, (1 / 2 : ℝ) ^ 2 <
      sq ((chartPoint p).basis.mulVec (castVec m + fun i => (reg.f0 i : ℝ)))) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) (fun i => (reg.f0 i : ℝ))) +
      200 * sq ((chartPoint p).basis.mulVec
        ((chartPoint p).offset - (fun i => (reg.f0 i : ℝ)) - castVec reg.wrap)) +
      ((annCap ℓ : ℚ) : ℝ) := by
  have hd := defect_transport_annulus reg.B reg.N reg.U reg.f0 reg.wrap hr p hstrain hv hsep₁
    half asep
  have e : (fun i => reg.f0 i + (reg.wrap i : ℚ)) = reg.w := rfl
  rw [e] at hd
  have hc := annPhi_le_annCap reg.N reg.w b ℓ ha p hp
  linarith

/-- **Far annulus, transported, whole box.** If every annular image of the
registration clears `13/10` on the box (`annFarOk`), then
`D(q) ≤ D(a) + 200 |h|²` at every point of the box where the pointwise
hypotheses hold (validity, the two separations, the half class and the strain
bound), whatever the size of the right side. -/
theorem defect_transport_box_far (reg : RegData) (b : Cell)
    (hr : registrationCheck reg.B reg.N reg.U reg.f0 = true)
    (hf : annFarOk reg.N reg.w b = true) (p : Chart) (hp : b.Mem p)
    (hstrain : 100 * strainCost reg.N reg.U p ≤ 5 / 2) (hv : (chartPoint p).Valid)
    (hsep₁ : ∀ m : IntVec, m ≠ 0 →
      (5 / 8 : ℝ) ^ 2 < sq ((chartPoint p).basis.mulVec (castVec m)))
    (half : HalfClass (fun i => (reg.f0 i : ℝ)))
    (asep : ∀ m : IntVec, (1 / 2 : ℝ) ^ 2 <
      sq ((chartPoint p).basis.mulVec (castVec m + fun i => (reg.f0 i : ℝ)))) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) (fun i => (reg.f0 i : ℝ))) +
      200 * sq ((chartPoint p).basis.mulVec
        ((chartPoint p).offset - (fun i => (reg.f0 i : ℝ)) - castVec reg.wrap)) := by
  have h := defect_transport_box_annulus reg b (fun _ => 13 / 10) hr (annFarOk_annBoxOk hf) p hp
    hstrain hv hsep₁ half asep
  rw [annCap_far] at h
  simpa using h

end BccSharp.Coulomb.CompactCover.Layered
