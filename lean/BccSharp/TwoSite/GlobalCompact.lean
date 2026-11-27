import BccSharp.TwoSite.GlobalValues

set_option autoImplicit false

/-! The compact reduction for every valid two-site configuration at or
below the FCC energy. The series is invariant under a unimodular change
of the period basis, a proper rotation and an integer wrap of the offset.
The two strict collision exclusions follow from positive terms of the series
and two checked half-kernel bounds against the Constants FCC bracket. The oriented
KZ chart of the Lattice chain then gives a reduced representative. This
discharges the `compact` field of `GlobalAnalyticInputs`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BccSharp.Coulomb.GlobalInputs
open BccSharp
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.KZ
open BccSharp.Intervals (Ball)

/-! ### The series as a function of the Gram matrix and offset -/

/-- The series of `h₂`, written for an arbitrary Gram matrix. -/
def seriesSeries (M : Mat) (f : Vec) : ℝ :=
  (∑' n : IntVec, if n = 0 then 0 else gKernel (1/2) (Real.pi * quad M (castVec n))) +
  (∑' n : IntVec, gKernel (1/2) (Real.pi * quad M (castVec n + f))) +
  (∑' n : IntVec, if n = 0 then 0 else
    (1 + Real.cos (2 * Real.pi * dot (castVec n) f)) * gKernel 1 (Real.pi * quad M⁻¹ (castVec n)))

theorem h₂_eq_series (q : TwoSite) : h₂ q = seriesSeries (q.basis.transpose * q.basis) q.offset := rfl

private theorem castIndex_mul' (G : Matrix (Fin 3) (Fin 3) ℤ) (n : IntVec) :
    castVec (G.mulVec n)=(toRealMatrix G).mulVec (castVec n) := by
  funext i
  simp [toRealMatrix,Matrix.mulVec,dotProduct,Matrix.map_apply,castVec]

private theorem realProduct (A B : Matrix (Fin 3) (Fin 3) ℤ) (h : A*B=1) :
    toRealMatrix A*toRealMatrix B=1 := by
  have e : toRealMatrix (A*B) = toRealMatrix A*toRealMatrix B := Matrix.map_mul
  rw [← e, h]
  ext i j
  by_cases hij : i=j <;> simp [toRealMatrix,Matrix.one_apply,hij]

theorem quad_conj (N A : Mat) (v : Vec) : quad (A.transpose * N * A) v = quad N (A.mulVec v) := by
  have h1 : ∀ (M : Mat) (w : Vec), quad M w = w ⬝ᵥ M.mulVec w := fun _ _ => rfl
  rw [h1, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem dot_mulVec_right (v f : Vec) (C : Mat) : dot v (C.mulVec f) = dot (C.transpose.mulVec v) f := by
  have h1 : ∀ (a b : Vec), dot a b = a ⬝ᵥ b := fun _ _ => rfl
  rw [h1, h1, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.transpose_transpose]

private def indexEquiv (K K' : Matrix (Fin 3) (Fin 3) ℤ) (h1 : K*K'=1) (h2 : K'*K=1) :
    IntVec ≃ IntVec where
  toFun := K.mulVec
  invFun := K'.mulVec
  left_inv n := by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  right_inv n := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

private theorem indexEquiv_zero (K K' : Matrix (Fin 3) (Fin 3) ℤ) (h1 : K*K'=1) (h2 : K'*K=1)
    (n : IntVec) : indexEquiv K K' h1 h2 n = 0 ↔ n = 0 := by
  have e : indexEquiv K K' h1 h2 0 = 0 := Matrix.mulVec_zero K
  constructor
  · intro h
    exact (indexEquiv K K' h1 h2).injective (h.trans e.symm)
  · rintro rfl
    exact e

/-- The series is invariant under a unimodular change of period basis. -/
theorem seriesSeries_rebase (M : Mat) (f : Vec) (K K' : Matrix (Fin 3) (Fin 3) ℤ)
    (h1 : K*K'=1) (h2 : K'*K=1) :
    seriesSeries ((toRealMatrix K).transpose * M * toRealMatrix K) ((toRealMatrix K').mulVec f) =
      seriesSeries M f := by
  set Kr := toRealMatrix K with hKr
  set K'r := toRealMatrix K' with hK'r
  have r1 : Kr*K'r=1 := realProduct K K' h1
  have r2 : K'r*Kr=1 := realProduct K' K h2
  have hinv : (Kr.transpose * M * Kr)⁻¹ = K'r.transpose.transpose * M⁻¹ * K'r.transpose := by
    have ht : Kr.transpose⁻¹ = K'r.transpose :=
      Matrix.inv_eq_right_inv (by rw [← Matrix.transpose_mul, r2, Matrix.transpose_one])
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv r1, ht,
      Matrix.transpose_transpose, mul_assoc]
  have ht1 : K'.transpose * K.transpose = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have ht2 : K.transpose * K'.transpose = 1 := by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  let e1 := indexEquiv K K' h1 h2
  let e3 := indexEquiv K'.transpose K.transpose ht1 ht2
  have hcast3 (n : IntVec) : castVec (e3 n) = K'r.transpose.mulVec (castVec n) := by
    change castVec (K'.transpose.mulVec n) = _
    rw [castIndex_mul', hK'r, toRealMatrix, Matrix.transpose_map]
    rfl
  have hcast1 (n : IntVec) : castVec (e1 n) = Kr.mulVec (castVec n) := castIndex_mul' K n
  have s1 : (∑' n : IntVec, if n = 0 then 0 else
        gKernel (1/2) (Real.pi * quad (Kr.transpose * M * Kr) (castVec n))) =
      ∑' n : IntVec, if n = 0 then 0 else gKernel (1/2) (Real.pi * quad M (castVec n)) := by
    rw [← e1.tsum_eq (fun m : IntVec => if m = 0 then 0 else
      gKernel (1/2) (Real.pi * quad M (castVec m)))]
    apply tsum_congr
    intro n
    have hz : e1 n = 0 ↔ n = 0 := indexEquiv_zero K K' h1 h2 n
    by_cases hn : n = 0
    · rw [ite_eq_left hn, ite_eq_left (hz.mpr hn)]
    · rw [ite_eq_right hn, ite_eq_right (fun h => hn (hz.mp h)), quad_conj, hcast1]
  have s2 : (∑' n : IntVec, gKernel (1/2) (Real.pi * quad (Kr.transpose * M * Kr) (castVec n + K'r.mulVec f))) =
      ∑' n : IntVec, gKernel (1/2) (Real.pi * quad M (castVec n + f)) := by
    rw [← e1.tsum_eq (fun m : IntVec => gKernel (1/2) (Real.pi * quad M (castVec m + f)))]
    apply tsum_congr
    intro n
    rw [quad_conj, Matrix.mulVec_add, Matrix.mulVec_mulVec, r1, Matrix.one_mulVec, hcast1]
  have s3 : (∑' n : IntVec, if n = 0 then 0 else
        (1 + Real.cos (2 * Real.pi * dot (castVec n) (K'r.mulVec f))) *
          gKernel 1 (Real.pi * quad (Kr.transpose * M * Kr)⁻¹ (castVec n))) =
      ∑' n : IntVec, if n = 0 then 0 else
        (1 + Real.cos (2 * Real.pi * dot (castVec n) f)) * gKernel 1 (Real.pi * quad M⁻¹ (castVec n)) := by
    rw [← e3.tsum_eq (fun m : IntVec => if m = 0 then 0 else
      (1 + Real.cos (2 * Real.pi * dot (castVec m) f)) * gKernel 1 (Real.pi * quad M⁻¹ (castVec m)))]
    apply tsum_congr
    intro n
    have hz : e3 n = 0 ↔ n = 0 := indexEquiv_zero K'.transpose K.transpose ht1 ht2 n
    by_cases hn : n = 0
    · rw [ite_eq_left hn, ite_eq_left (hz.mpr hn)]
    · rw [ite_eq_right hn, ite_eq_right (fun h => hn (hz.mp h)), hinv, quad_conj, dot_mulVec_right,
        hcast3]
  unfold seriesSeries
  rw [s1, s2, s3]

theorem energy_rebase (B : Mat) (f : Vec) (K K' : Matrix (Fin 3) (Fin 3) ℤ)
    (h1 : K*K'=1) (h2 : K'*K=1) :
    energy ⟨B * toRealMatrix K, (toRealMatrix K').mulVec f⟩ = energy ⟨B, f⟩ := by
  have hg : (B * toRealMatrix K).transpose * (B * toRealMatrix K) =
      (toRealMatrix K).transpose * (B.transpose * B) * toRealMatrix K := by
    rw [Matrix.transpose_mul]
    simp only [mul_assoc]
  unfold energy
  rw [h₂_eq_series, h₂_eq_series]
  simp only
  rw [hg, seriesSeries_rebase _ _ K K' h1 h2]

theorem energy_rotate (U B : Mat) (hU : U.transpose * U = 1) (f : Vec) :
    energy ⟨U * B, f⟩ = energy ⟨B, f⟩ := by
  have hg : (U * B).transpose * (U * B) = B.transpose * B := by
    rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc U.transpose U B, hU, one_mul]
  unfold energy
  rw [h₂_eq_series, h₂_eq_series]
  simp only
  rw [hg]

/-! ### Positive terms and the two strict collision exclusions -/

theorem gKernel_nonneg (a t : ℝ) : 0 ≤ gKernel a t := by
  unfold gKernel
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg (zero_le_one.trans (le_of_lt (Set.mem_Ioi.mp hu))) _)

private theorem seriesScreen_positive : 0 < seriesScreen :=
  div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive

theorem seriesDirect_summable (q : TwoSite) (hq : q.Valid) : Summable (seriesDirectTerm q) := by
  have h := screened_lattice_summable seriesScreen seriesScreen_positive (physicalBasis q)
    (series_physical_basis_nonsingular q hq) 0
  simp only [zero_add] at h
  have h' : Summable (fun n : IntVec =>
      if n = 0 then 0 else screened seriesScreen (linearImage (physicalBasis q) n)) := by
    apply h.summable_of_eq_zero_or_self
    intro n
    by_cases hn : n = 0 <;> simp [hn]
  exact (h'.mul_left ac).congr (fun n => (series_direct_mode q hq n).symm)

theorem seriesCross_summable (q : TwoSite) (hq : q.Valid) : Summable (seriesCrossTerm q) := by
  have h := screened_lattice_summable seriesScreen seriesScreen_positive (physicalBasis q)
    (series_physical_basis_nonsingular q hq) (physicalTwoPositions q 1)
  exact (h.mul_left ac).congr (fun n => (series_cross_mode q hq n).symm)

theorem seriesDirect_nonneg (q : TwoSite) (n : IntVec) : 0 ≤ seriesDirectTerm q n := by
  unfold seriesDirectTerm
  split_ifs
  · exact le_rfl
  · exact gKernel_nonneg _ _

theorem seriesCross_nonneg (q : TwoSite) (n : IntVec) : 0 ≤ seriesCrossTerm q n :=
  gKernel_nonneg _ _

theorem seriesReciprocal_nonneg (q : TwoSite) (n : IntVec) : 0 ≤ seriesReciprocalTerm q n := by
  unfold seriesReciprocalTerm
  split_ifs
  · exact le_rfl
  · exact gKernel_nonneg _ _

/-- Every finite sum of direct terms and every cross term is below `h₂`. -/
theorem h₂_lower (q : TwoSite) (hq : q.Valid) (s : Finset IntVec) (m : IntVec) :
    (∑ n ∈ s, seriesDirectTerm q n) ≤ h₂ q ∧ seriesCrossTerm q m ≤ h₂ q := by
  have modes := series_modes q hq
  rw [series_reciprocal_split q modes.reciprocalSummable modes.cosineSummable]
  have hD := (seriesDirect_summable q hq).sum_le_tsum s (fun n _ => seriesDirect_nonneg q n)
  have hD0 : 0 ≤ ∑' n, seriesDirectTerm q n := tsum_nonneg (seriesDirect_nonneg q)
  have hC := (seriesCross_summable q hq).le_tsum m (fun n _ => seriesCross_nonneg q n)
  have hC0 : 0 ≤ ∑' n, seriesCrossTerm q n := tsum_nonneg (seriesCross_nonneg q)
  have hT : 0 ≤ (∑' n, seriesReciprocalTerm q n) + ∑' n, seriesCosineTerm q n := by
    rw [← modes.reciprocalSummable.tsum_add modes.cosineSummable]
    apply tsum_nonneg
    intro n
    have hc : seriesReciprocalTerm q n + seriesCosineTerm q n =
        (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) * seriesReciprocalTerm q n := by
      unfold seriesCosineTerm
      ring
    rw [hc]
    exact mul_nonneg (by linarith [Real.neg_one_le_cos (2 * Real.pi * dot (castVec n) q.offset)])
      (seriesReciprocal_nonneg q n)
  exact ⟨by linarith, by linarith⟩

theorem h₂_ge_pair (q : TwoSite) (hq : q.Valid) (n : IntVec) (hn : n ≠ 0) :
    2 * gKernel (1/2) (Real.pi * sq (q.basis.mulVec (castVec n))) ≤ h₂ q := by
  have hnn : n ≠ -n := by
    intro e
    apply hn
    funext i
    have h := congrFun e i
    change n i = -(n i) at h
    change n i = 0
    omega
  have h := (h₂_lower q hq {n, -n} 0).1
  rw [Finset.sum_pair hnn] at h
  have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
  have e1 : seriesDirectTerm q n = gKernel (1/2) (Real.pi * sq (q.basis.mulVec (castVec n))) := by
    rw [seriesDirectTerm, ite_eq_right hn, sq_mulVec_gram]
  have e2 : seriesDirectTerm q (-n) = gKernel (1/2) (Real.pi * sq (q.basis.mulVec (castVec n))) := by
    rw [seriesDirectTerm, ite_eq_right hneg, ← sq_mulVec_gram, castVec_neg, Matrix.mulVec_neg]
    congr 2
    simp [sq, Pi.neg_apply]
  linarith

theorem h₂_ge_cross (q : TwoSite) (hq : q.Valid) (n : IntVec) :
    gKernel (1/2) (Real.pi * sq (q.basis.mulVec (castVec n + q.offset))) ≤ h₂ q := by
  have h := (h₂_lower q hq ∅ n).2
  rw [seriesCrossTerm, ← sq_mulVec_gram] at h
  exact h

/-- Rational lower bound for `a_c` from `π > 3.14159265358979323846`. -/
def acLower : ℚ := 203098/100000

theorem acLower_le : (acLower : ℝ) ≤ ac := by
  have hcube : (acLower : ℝ)^3 ≤ ac^3 := by
    rw [ac_cube]
    have hp := Real.pi_gt_d20
    norm_num [acLower]
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) ac_positive.le hcube

/-- Outward rational upper bound for `h₂(FCC) = 4 + 2 a_c e_FCC`. -/
def H2fccUpper : ℚ := 4 + 2 * acLower * Constants.fccBracket.hi

theorem h₂_fcc_upper : h₂ fcc ≤ (H2fccUpper : ℝ) := by
  have he : h₂ fcc = 4 + 2 * ac * energy fcc := by
    have hac := ac_positive.ne'
    unfold energy
    field_simp
    ring
  have hb : energy fcc ≤ (Constants.fccBracket.hi : ℝ) := (Constants.reference_bounds .fcc).2
  have hneg : (Constants.fccBracket.hi : ℝ) ≤ 0 := by norm_num [Constants.fccBracket]
  have hlo := acLower_le
  have hlo0 : (0 : ℝ) ≤ acLower := by norm_num [acLower]
  have hE0 : energy fcc ≤ 0 := hb.trans hneg
  have step1 : ac * energy fcc ≤ (acLower : ℝ) * energy fcc :=
    mul_le_mul_of_nonpos_right hlo hE0
  have step2 : (acLower : ℝ) * energy fcc ≤ (acLower : ℝ) * (Constants.fccBracket.hi : ℝ) :=
    mul_le_mul_of_nonneg_left hb hlo0
  rw [he]
  unfold H2fccUpper
  push_cast
  linarith

def shortArgument : Ball := Ball.exact (25/64)
def shortWitness : HalfLower :=
  .check (automaticErfc (Constants.piInput.mul shortArgument).hi)

def shortEscapeCheck : Bool :=
  match halfLower shortArgument shortWitness with
  | some t => decide (H2fccUpper < 2*t)
  | none => false

theorem shortEscape_checked : shortEscapeCheck = true := by
  decide +kernel

theorem shortEscape_scalar : (H2fccUpper : ℝ) < 2*gKernel (1/2) (Real.pi*(25/64)) := by
  obtain ⟨t,ht,hc⟩ : ∃ t, halfLower shortArgument shortWitness = some t ∧ H2fccUpper < 2*t := by
    cases e : halfLower shortArgument shortWitness with
    | none =>
      have h := shortEscape_checked
      simp [shortEscapeCheck,e] at h
    | some t =>
      refine ⟨t,rfl,?_⟩
      exact of_decide_eq_true (by simpa [shortEscapeCheck,e] using shortEscape_checked)
  have h := halfLower_sound (q := shortArgument) (x := (25/64 : ℝ))
    (by simpa [shortArgument] using (Ball.contains_exact (25/64 : ℚ))) (by norm_num)
    shortWitness t ht
  exact (by exact_mod_cast hc : (H2fccUpper : ℝ)<2*(t : ℝ)).trans_le
    (mul_le_mul_of_nonneg_left h (by norm_num))

def crossArgument : Ball := Ball.exact (1/4)
def crossWitness : HalfLower :=
  .check (automaticErfc (Constants.piInput.mul crossArgument).hi)

def crossEscapeCheck : Bool :=
  match halfLower crossArgument crossWitness with
  | some t => decide (H2fccUpper < t)
  | none => false

theorem crossEscape_checked : crossEscapeCheck = true := by
  decide +kernel

theorem crossEscape_scalar : (H2fccUpper : ℝ) < gKernel (1/2) (Real.pi*(1/4)) := by
  obtain ⟨t,ht,hc⟩ : ∃ t, halfLower crossArgument crossWitness = some t ∧ H2fccUpper < t := by
    cases e : halfLower crossArgument crossWitness with
    | none =>
      have h := crossEscape_checked
      simp [crossEscapeCheck,e] at h
    | some t =>
      refine ⟨t,rfl,?_⟩
      exact of_decide_eq_true (by simpa [crossEscapeCheck,e] using crossEscape_checked)
  have h := halfLower_sound (q := crossArgument) (x := (1/4 : ℝ))
    (by simpa [crossArgument] using (Ball.contains_exact (1/4 : ℚ))) (by norm_num)
    crossWitness t ht
  exact (by exact_mod_cast hc : (H2fccUpper : ℝ)<(t : ℝ)).trans_le h

theorem h₂_le_of_energy (q : TwoSite) (he : energy q ≤ energy fcc) : h₂ q ≤ (H2fccUpper : ℝ) := by
  have hac : 0 < 2 * ac := mul_pos two_pos ac_positive
  have h : h₂ q - 4 ≤ h₂ fcc - 4 := by
    unfold energy at he
    exact (div_le_div_iff_of_pos_right hac).mp he
  linarith [h₂_fcc_upper]

/-- The Series strict collision exclusions at or below the FCC energy. -/
theorem separated_of_energy (q : TwoSite) (hq : q.Valid) (he : energy q ≤ energy fcc) :
    separated q := by
  have hH := h₂_le_of_energy q he
  have hu : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hq.1]; exact isUnit_one)
  have inj := Matrix.mulVec_injective_of_isUnit hu
  constructor
  · intro n hn
    by_contra! hle
    have hne : q.basis.mulVec (castVec n) ≠ 0 := by
      intro h0
      apply hn
      have h' := inj (h0.trans (Matrix.mulVec_zero q.basis).symm)
      funext i
      have e := congrFun h' i
      change ((n i : ℤ) : ℝ) = 0 at e
      exact_mod_cast e
    have hpos : 0 < sq (q.basis.mulVec (castVec n)) :=
      lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hne))
    have hk := halfKernel_decreasing (mul_pos Real.pi_pos hpos)
      (mul_le_mul_of_nonneg_left (hle.trans (by norm_num : ((5:ℝ)/8)^2 ≤ 25/64)) Real.pi_pos.le)
    have hp := h₂_ge_pair q hq n hn
    linarith [shortEscape_scalar]
  · intro n
    by_contra! hle
    have hne : q.basis.mulVec (castVec n + q.offset) ≠ 0 := by
      intro h0
      have h' := inj (h0.trans (Matrix.mulVec_zero q.basis).symm)
      apply hq.2 (-n)
      rw [castVec_neg]
      calc q.offset = castVec n + q.offset - castVec n := by abel
        _ = -castVec n := by rw [h', zero_sub]
    have hpos : 0 < sq (q.basis.mulVec (castVec n + q.offset)) :=
      lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hne))
    have hk := halfKernel_decreasing (mul_pos Real.pi_pos hpos)
      (mul_le_mul_of_nonneg_left (hle.trans (by norm_num : ((1:ℝ)/2)^2 ≤ 1/4)) Real.pi_pos.le)
    have hp := h₂_ge_cross q hq n
    linarith [crossEscape_scalar]

/-! ### The reduced chart representative -/

theorem translate_image (U : Mat) (x : Vec) (S : Set Vec) :
    translate (U.mulVec x) (U.mulVec '' S) = U.mulVec '' translate x S := by
  ext z
  constructor
  · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨s+x,⟨s,hs,rfl⟩,by rw [Matrix.mulVec_add]⟩
  · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨U.mulVec s,⟨s,hs,rfl⟩,by rw [Matrix.mulVec_add]⟩

theorem chartBasis_congr (p p' : Chart) (h : ∀ i : Fin 8, i.val < 5 → p i = p' i) :
    chartBasis p = chartBasis p' := by
  unfold chartBasis
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem reductionInequalities_congr (p p' : Chart) (h : ∀ i : Fin 8, i.val < 5 → p i = p' i) :
    reductionInequalities p ↔ reductionInequalities p' := by
  have hb := chartBasis_congr p p' h
  unfold reductionInequalities
  rw [hb, h 0 (by decide), h 1 (by decide), h 4 (by decide)]

private theorem first_column_length (p : Chart) :
    sq ((chartBasis p).mulVec (castVec (![1,0,0] : IntVec))) = (p 0)^2 := by
  norm_num [sq,chartBasis,castVec,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

/-- Every valid configuration at or below the FCC energy has a reduced
representative in the closed Series root chart. -/
theorem compact_proof (q : TwoSite) (hq : q.Valid) (he : energy q ≤ energy fcc) :
    ∃ p, ReducedRepresentative q p := by
  obtain ⟨rep⟩ := oriented_chart q.basis hq.1
  set N := normalizedChart rep.point with hN
  set U := rep.rotation with hU
  set Hr := toRealMatrix rep.basisChange with hHr
  set Gr := toRealMatrix rep.inverseChange with hGr
  have hHG : Hr * Gr = 1 := realProduct _ _ rep.leftInverse
  have hGH : Gr * Hr = 1 := realProduct _ _ rep.rightInverse
  have hB : q.basis = U * N * Gr := by
    calc q.basis = q.basis * Hr * Gr := by rw [mul_assoc, hHG, mul_one]
      _ = U * N * Gr := by rw [rep.basisEquation]
  set g := Gr.mulVec q.offset with hg
  let m : IntVec := fun i => centerInteger (g i)
  let g' : Vec := g - castVec m
  have hgg : g = g' + castVec m := by simp [g']
  have hbound (i : Fin 3) : g' i ∈ Set.Icc (-1/2 : ℝ) (1/2) := by
    have h := center_remainder (g i)
    have e : g' i = g i - (centerInteger (g i) : ℝ) := rfl
    rw [e]
    constructor <;> linarith [abs_le.mp h]
  let p : Chart := ![rep.point 0, rep.point 1, rep.point 2, rep.point 3, rep.point 4, g' 0, g' 1, g' 2]
  have hfirst : ∀ i : Fin 8, i.val < 5 → p i = coordLift rep.point i := by
    intro i hi
    have hp : ∀ k : Fin 5, p (Fin.castLE (by decide) k) = rep.point k := by
      intro k
      fin_cases k <;> rfl
    have hc : ∀ k : Fin 5, coordLift rep.point (Fin.castLE (by decide) k) = rep.point k := by
      intro k
      fin_cases k <;> rfl
    have e : i = Fin.castLE (by decide) (⟨i.val, hi⟩ : Fin 5) := Fin.ext rfl
    rw [e, hp, hc]
  have hchart : chartBasis p = N := chartBasis_congr p (coordLift rep.point) hfirst
  have hcp : chartPoint p = ⟨N, g'⟩ := by
    unfold chartPoint
    rw [hchart]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hfg : Hr.mulVec g = q.offset := by
    rw [hg, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
  have hr0 := rep.r1Positive
  have hr1 := rep.r2Positive
  have hNdet : N.det = 1 := normalizedChart_det rep.point hr0.ne' hr1.ne'
  -- energy
  have hE : energy (chartPoint p) = energy q := by
    have e1 : energy q = energy ⟨U * N * Gr, Hr.mulVec g⟩ := by
      rw [hfg, ← hB]
    have e2 : energy (⟨U * N * Gr, Hr.mulVec g⟩ : TwoSite) = energy ⟨U * N, g⟩ :=
      energy_rebase (U * N) g rep.inverseChange rep.basisChange rep.rightInverse rep.leftInverse
    have e3 : energy (⟨U * N, g⟩ : TwoSite) = energy ⟨N, g⟩ :=
      energy_rotate U N rep.properRotation.1 g
    have e4 : energy (⟨N, g⟩ : TwoSite) = energy ⟨N, g'⟩ := by
      rw [hgg]
      exact energy_wrap ⟨N, g'⟩ m
    rw [hcp, e1, e2, e3, e4]
  -- points
  have hP : q.points = U.mulVec '' (chartPoint p).points := by
    have hlat : lattice q.basis = U.mulVec '' lattice N := by
      rw [hB, rebase_sameLattice (U * N) rep.inverseChange rep.basisChange rep.rightInverse,
        lattice_left_mul]
    have hoff : q.basis.mulVec q.offset = U.mulVec (N.mulVec g') + (U * N).mulVec (castVec m) := by
      rw [← hfg, hB, Matrix.mulVec_mulVec, mul_assoc, hGH, mul_one, hgg, Matrix.mulVec_add,
        ← Matrix.mulVec_mulVec]
    have htr : translate (q.basis.mulVec q.offset) (lattice q.basis) =
        U.mulVec '' translate (N.mulVec g') (lattice N) := by
      rw [hoff]
      have hl : lattice q.basis = lattice (U * N) := by
        rw [hB, rebase_sameLattice (U * N) rep.inverseChange rep.basisChange rep.rightInverse]
      have hper : translate (U.mulVec (N.mulVec g') + (U * N).mulVec (castVec m)) (lattice (U * N)) =
          translate (U.mulVec (N.mulVec g')) (lattice (U * N)) :=
        translate_period_add (periodGroup (U * N)) _ _ ⟨m, rfl⟩
      rw [hl, hper, lattice_left_mul, translate_image]
    rw [hcp]
    show lattice q.basis ∪ translate (q.basis.mulVec q.offset) (lattice q.basis) =
      U.mulVec '' (lattice N ∪ translate (N.mulVec g') (lattice N))
    rw [Set.image_union, htr, hlat]
  -- validity
  have hvalid : (chartPoint p).Valid := by
    rw [hcp]
    refine ⟨hNdet, fun k hk => ?_⟩
    apply hq.2 (rep.basisChange.mulVec (k + m))
    rw [castIndex_mul', castVec_add, ← hk, ← hgg, hfg]
  have hsep := separated_of_energy (chartPoint p) hvalid (hE.symm ▸ he)
  have hred : reductionInequalities p :=
    (reductionInequalities_congr p (coordLift rep.point) hfirst).mpr rep.reducedPoint
  have h₁ : (5/8 : ℝ) < p 0 := by
    have h := hsep.1 (![1,0,0] : IntVec) (by decide)
    change (5/8 : ℝ)^2 < sq ((chartBasis p).mulVec (castVec (![1,0,0] : IntVec))) at h
    rw [first_column_length] at h
    exact lt_of_pow_lt_pow_left₀ 2 hr0.le h
  have hroot : inRoot p := by
    apply compact_of_reduced p h₁ hr1 rep.xBound rep.yBound _ hred
    intro i hi
    fin_cases i
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact rep.zBound
    · exact hbound 0
    · exact hbound 1
    · exact hbound 2
  refine ⟨p, ⟨hroot, hred, hvalid, hsep, ?_, hE, ?_⟩⟩
  · refine ⟨0, U, rep.properRotation, ?_⟩
    rw [hP]
    ext x
    simp [translate]
  · show cappedDefect (liftedNeighbors (chartPoint p).points 0) =
      cappedDefect (liftedNeighbors q.points 0)
    rw [hP, cappedDefect_proper U rep.properRotation]

end BccSharp.Coulomb.GlobalInputs
