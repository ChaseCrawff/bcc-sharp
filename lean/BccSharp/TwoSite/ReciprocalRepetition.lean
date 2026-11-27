import BccSharp.TwoSite.PeriodRepetition

set_option autoImplicit false

/-! Reciprocal supercell calculation. The actual plane wave annihilator
is the reciprocal lattice. The finite sum is carried by a representative
permutation, so it applies to every finite-index period presentation. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

def physicalWave (k x : Vec) : ℂ := Complex.exp ((dot k x : ℂ) * Complex.I)

theorem physicalWave_add (k x y : Vec) : physicalWave k (x+y) = physicalWave k x * physicalWave k y := by
  unfold physicalWave
  rw [dot_add_right, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem physicalWave_eq_one (k x : Vec) :
    physicalWave k x = 1 ↔ ∃ n : ℤ, dot k x = (n : ℝ)*(2*Real.pi) := by
  unfold physicalWave
  constructor
  · intro h
    obtain ⟨n, h⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hi := congrArg Complex.im h
    simpa [Complex.mul_im, Complex.mul_re] using hi
  · rintro ⟨n, hn⟩
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring

theorem dot_mulVec_eq (B : Mat) (k u : Vec) : dot k (B.mulVec u) = dot (B.transpose.mulVec k) u := by
  change (k ⬝ᵥ B.mulVec u) = (B.transpose.mulVec k ⬝ᵥ u)
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem dot_left_smul (c : ℝ) (u v : Vec) : dot (c • u) v = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem transpose_mul_dual (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    B.transpose.mulVec (dualWave B n) = (2*Real.pi) • castVec n := by
  unfold dualWave
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB)]
  simp

theorem dual_iff_annihilates (B : Mat) (hB : B.det ≠ 0) (k : Vec) :
    (∀ x ∈ lattice B, physicalWave k x = 1) ↔ ∃ n : IntVec, dualWave B n = k := by
  constructor
  · intro h
    have coord i : ∃ z : ℤ, B.transpose.mulVec k i = (z : ℝ)*(2*Real.pi) := by
      let ei : IntVec := Pi.single i 1
      have hx := (physicalWave_eq_one k (linearImage B ei)).mp (h _ ⟨ei, rfl⟩)
      unfold linearImage at hx
      rw [dot_mulVec_eq] at hx
      have hei : castVec ei = Pi.single i (1 : ℝ) := by
        funext j
        by_cases hj : j = i <;> simp [hj, castVec, ei]
      rw [hei] at hx
      simpa [dot, Pi.single_apply, mul_ite] using hx
    choose n hn using coord
    refine ⟨n, ?_⟩
    have hb : IsUnit B.transpose := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact isUnit_iff_ne_zero.mpr hB
    apply Matrix.mulVec_injective_of_isUnit hb
    rw [transpose_mul_dual B hB]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, castVec]
    rw [hn i, mul_comm]
  · rintro ⟨n, rfl⟩ x ⟨m, rfl⟩
    apply (physicalWave_eq_one _ _).mpr
    refine ⟨∑ i, n i*m i, ?_⟩
    rw [dot_mulVec_eq, transpose_mul_dual B hB n, dot_left_smul, dot_integer]
    ring

def PeriodRepetition.shiftIndex {ι : Type} {B C : Mat} (rep : PeriodRepetition B C ι)
    (v : periodGroup B) (i : ι) : ι :=
  Classical.choose (rep.uniquePeriod (v.val + rep.representative i)
    ((periodGroup B).add_mem v.property (rep.representativesInPeriod i)))

theorem PeriodRepetition.shiftIndex_spec {ι : Type} {B C : Mat} (rep : PeriodRepetition B C ι)
    (v : periodGroup B) (i : ι) :
    v.val + rep.representative i - rep.representative (rep.shiftIndex v i) ∈ lattice C :=
  (Classical.choose_spec (rep.uniquePeriod _ ((periodGroup B).add_mem v.property (rep.representativesInPeriod i)))).1

theorem PeriodRepetition.shiftIndex_unique {ι : Type} {B C : Mat} (rep : PeriodRepetition B C ι)
    (v : periodGroup B) (i j : ι)
    (h : v.val + rep.representative i - rep.representative j ∈ lattice C) : j = rep.shiftIndex v i :=
  (Classical.choose_spec (rep.uniquePeriod _ ((periodGroup B).add_mem v.property (rep.representativesInPeriod i)))).2 j h

theorem PeriodRepetition.shiftIndex_inverse {ι : Type} {B C : Mat} (rep : PeriodRepetition B C ι)
    (v : periodGroup B) (i : ι) : rep.shiftIndex (-v) (rep.shiftIndex v i) = i := by
  have h : -(v.val + rep.representative i - rep.representative (rep.shiftIndex v i)) ∈ lattice C :=
    (periodGroup C).neg_mem (rep.shiftIndex_spec v i)
  symm
  apply rep.shiftIndex_unique
  change -v.val + rep.representative (rep.shiftIndex v i) - rep.representative i ∈ lattice C
  convert h using 1
  abel

def PeriodRepetition.shiftEquiv {ι : Type} {B C : Mat} (rep : PeriodRepetition B C ι)
    (v : periodGroup B) : ι ≃ ι where
  toFun := rep.shiftIndex v
  invFun := rep.shiftIndex (-v)
  left_inv := rep.shiftIndex_inverse v
  right_inv i := by simpa only [neg_neg] using rep.shiftIndex_inverse (-v) i

theorem PeriodRepetition.phase_shift {ι : Type} {B C : Mat} (rep : PeriodRepetition B C ι)
    (k : Vec) (periodic : ∀ x ∈ lattice C, physicalWave k x = 1)
    (v : periodGroup B) (i : ι) :
    physicalWave k (rep.representative (rep.shiftIndex v i)) =
      physicalWave k v.val * physicalWave k (rep.representative i) := by
  let j := rep.shiftIndex v i
  let u := v.val + rep.representative i - rep.representative j
  have h : physicalWave k u = 1 := periodic u (rep.shiftIndex_spec v i)
  calc
    _ = physicalWave k (rep.representative j) * physicalWave k u := by rw [h, mul_one]
    _ = physicalWave k (rep.representative j + u) := (physicalWave_add k _ _).symm
    _ = physicalWave k (v.val + rep.representative i) := by congr 1; unfold u; abel
    _ = _ := physicalWave_add k _ _

theorem PeriodRepetition.relative_phase_sum {ι : Type} [Fintype ι] {B C : Mat}
    (rep : PeriodRepetition B C ι) (k : Vec) (periodic : ∀ x ∈ lattice C, physicalWave k x = 1) :
    (∑ i, physicalWave k (rep.representative i)) =
      if ∀ x ∈ lattice B, physicalWave k x = 1 then (Fintype.card ι : ℂ) else 0 := by
  classical
  by_cases h : ∀ x ∈ lattice B, physicalWave k x = 1
  · rw [if_pos h]
    have all (i : ι) : physicalWave k (rep.representative i) = 1 := h _ (rep.representativesInPeriod i)
    simp [all]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨x, hx, nontrivial⟩ := h
    let v : periodGroup B := ⟨x, hx⟩
    have hs : (∑ i, physicalWave k (rep.representative (rep.shiftIndex v i))) =
        ∑ i, physicalWave k (rep.representative i) :=
      (rep.shiftEquiv v).sum_comp (fun i => physicalWave k (rep.representative i))
    simp_rw [rep.phase_shift k periodic v, ← Finset.mul_sum] at hs
    have hprod : (physicalWave k x - 1) * (∑ i, physicalWave k (rep.representative i)) = 0 := by
      change physicalWave k x * (∑ i, physicalWave k (rep.representative i)) = _ at hs
      rw [sub_mul, one_mul, hs, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr nontrivial)

def siteAmplitude {ι : Type} [Fintype ι] (k : Vec) (s : ι → Vec) : ℂ :=
  ∑ i, physicalWave k (s i)

theorem repeated_amplitude {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (s : ι → Vec) (k : Vec) :
    siteAmplitude k (repeatedSites rep s) = siteAmplitude k s *
      (∑ j, physicalWave k (rep.representative j)) := by
  unfold siteAmplitude
  rw [Fintype.sum_prod_type]
  simp_rw [repeatedSites, physicalWave_add, ← Finset.mul_sum, ← Finset.sum_mul]

theorem repeated_reciprocal_selection {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0) (s : ι → Vec) (n : IntVec) :
    siteAmplitude (dualWave C n) (repeatedSites rep s) =
      if (∃ m : IntVec, dualWave B m = dualWave C n) then
        siteAmplitude (dualWave C n) s * (Fintype.card κ : ℂ) else 0 := by
  have periodic := (dual_iff_annihilates C hC (dualWave C n)).mpr ⟨n, rfl⟩
  rw [repeated_amplitude, rep.relative_phase_sum _ periodic, dual_iff_annihilates B hB]
  split_ifs <;> simp

theorem dualWave_injective (B : Mat) (hB : B.det ≠ 0) : Function.Injective (dualWave B) := by
  intro m n h
  have eq := congrArg B.transpose.mulVec h
  rw [transpose_mul_dual B hB, transpose_mul_dual B hB] at eq
  funext i
  have e := congrFun eq i
  change (2*Real.pi) * (m i : ℝ) = (2*Real.pi) * (n i : ℝ) at e
  exact_mod_cast mul_left_cancel₀ (by positivity : (2*Real.pi : ℝ) ≠ 0) e

theorem dualWave_zero (B : Mat) : dualWave B 0 = 0 := by simp [dualWave, castVec_zero]

theorem PeriodRepetition.index_exists {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ)
    (hB : B.det ≠ 0) (hC : C.det ≠ 0) (n : IntVec) : ∃ j, dualWave C j = dualWave B n := by
  have hb := (dual_iff_annihilates B hB (dualWave B n)).mpr ⟨n, rfl⟩
  exact (dual_iff_annihilates C hC _).mp (fun x hx => hb x (rep.subperiod hx))

def PeriodRepetition.reciprocalIndex {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ)
    (hB : B.det ≠ 0) (hC : C.det ≠ 0) : IntVec ↪ IntVec where
  toFun n := Classical.choose (rep.index_exists hB hC n)
  inj' := by
    intro m n h
    change Classical.choose (rep.index_exists hB hC m) =
      Classical.choose (rep.index_exists hB hC n) at h
    apply dualWave_injective B hB
    rw [← Classical.choose_spec (rep.index_exists hB hC m),
      ← Classical.choose_spec (rep.index_exists hB hC n), h]

theorem PeriodRepetition.reciprocalIndex_wave {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ)
    (hB : B.det ≠ 0) (hC : C.det ≠ 0) (n : IntVec) :
    dualWave C (rep.reciprocalIndex hB hC n) = dualWave B n :=
  Classical.choose_spec (rep.index_exists hB hC n)

theorem PeriodRepetition.reciprocalIndex_eq_zero {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ)
    (hB : B.det ≠ 0) (hC : C.det ≠ 0) (n : IntVec) :
    rep.reciprocalIndex hB hC n = 0 ↔ n = 0 := by
  constructor
  · intro h
    apply dualWave_injective B hB
    rw [← rep.reciprocalIndex_wave hB hC n, h, dualWave_zero, dualWave_zero]
  · rintro rfl
    apply dualWave_injective C hC
    rw [rep.reciprocalIndex_wave, dualWave_zero, dualWave_zero]

def reciprocalObjectiveTerm {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec) (n : IntVec) : ℝ :=
  reciprocalGreenTerm α B n * ‖siteAmplitude (dualWave B n) s‖^2

def reciprocalObjectiveSum {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec) : ℝ :=
  ∑' n, reciprocalObjectiveTerm α B s n

theorem reciprocalTerm_on_image {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0) (α : ℝ) (s : ι → Vec) (n : IntVec) :
    reciprocalObjectiveTerm α C (repeatedSites rep s) (rep.reciprocalIndex hB hC n) =
      (Fintype.card κ : ℝ)^2 * reciprocalObjectiveTerm α B s n := by
  let j := rep.reciprocalIndex hB hC n
  have hk : dualWave C j = dualWave B n := rep.reciprocalIndex_wave hB hC n
  have phase := repeated_reciprocal_selection rep hB hC s j
  rw [if_pos ⟨n, hk.symm⟩] at phase
  have green : reciprocalGreenTerm α C j = reciprocalGreenTerm α B n := by
    have hj : j = 0 ↔ n = 0 := rep.reciprocalIndex_eq_zero hB hC n
    unfold reciprocalGreenTerm
    simp only [hk]
    by_cases hn : n = 0
    · simp [hn, hj.mpr hn]
    · simp [hn, mt hj.mp hn]
  change reciprocalObjectiveTerm α C (repeatedSites rep s) j = _
  unfold reciprocalObjectiveTerm
  rw [green, phase, hk, norm_mul]
  simp only [Complex.norm_natCast, mul_pow]
  ring

theorem reciprocalTerm_off_image {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0) (α : ℝ) (s : ι → Vec)
    (j : IntVec) (h : j ∉ Set.range (rep.reciprocalIndex hB hC)) :
    reciprocalObjectiveTerm α C (repeatedSites rep s) j = 0 := by
  have no : ¬ ∃ n, dualWave B n = dualWave C j := by
    rintro ⟨n, hn⟩
    apply h
    refine ⟨n, dualWave_injective C hC ?_⟩
    exact (rep.reciprocalIndex_wave hB hC n).trans hn
  unfold reciprocalObjectiveTerm
  rw [repeated_reciprocal_selection rep hB hC s j, if_neg no]
  simp

/-- All enlarged reciprocal frequencies, including the exact zero-mode
mask, reorganize into the original reciprocal sum. -/
theorem reciprocal_sum_repetition {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0) (α : ℝ) (s : ι → Vec) :
    reciprocalObjectiveSum α C (repeatedSites rep s) =
      (Fintype.card κ : ℝ)^2 * reciprocalObjectiveSum α B s := by
  let embed := rep.reciprocalIndex hB hC
  let f := reciprocalObjectiveTerm α C (repeatedSites rep s)
  have support : Function.support f ⊆ Set.range embed := by
    intro j h
    by_contra out
    exact h (reciprocalTerm_off_image rep hB hC α s j out)
  calc
    _ = ∑' j : Set.range embed, f j.val := (tsum_subtype_eq_of_support_subset support).symm
    _ = ∑' n : IntVec, f (embed n) :=
      ((Equiv.ofInjective embed embed.injective).tsum_eq (fun w => f w.val)).symm
    _ = _ := by
      unfold reciprocalObjectiveSum
      rw [← tsum_mul_left]
      exact tsum_congr (reciprocalTerm_on_image rep hB hC α s)

end BccSharp.Coulomb
