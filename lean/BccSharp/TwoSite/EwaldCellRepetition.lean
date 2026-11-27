import BccSharp.TwoSite.RepetitionVolume

set_option autoImplicit false

/-! Real and reciprocal cell-sum normalization under period
repetition. Absolute convergence is explicit where the sums are interchanged. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

theorem dot_sub_right (k x y : Vec) : dot k (x-y) = dot k x - dot k y := by
  simp [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem amplitude_real {ι : Type} [Fintype ι] (k : Vec) (s : ι → Vec) :
    (siteAmplitude k s).re = ∑ i, Real.cos (dot k (s i)) := by
  simp [siteAmplitude, physicalWave, Complex.exp_ofReal_mul_I_re]

theorem amplitude_imag {ι : Type} [Fintype ι] (k : Vec) (s : ι → Vec) :
    (siteAmplitude k s).im = ∑ i, Real.sin (dot k (s i)) := by
  simp [siteAmplitude, physicalWave, Complex.exp_ofReal_mul_I_im]

theorem reciprocal_pair_phase {ι : Type} [Fintype ι] (k : Vec) (s : ι → Vec) :
    (∑ i, ∑ j, Real.cos (dot k (s i-s j))) = ‖siteAmplitude k s‖^2 := by
  simp_rw [dot_sub_right, Real.cos_sub, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Complex.sq_norm, Complex.normSq_apply, amplitude_real, amplitude_imag]

def reciprocalPair (α : ℝ) (B : Mat) (v : Vec) : ℝ :=
  ∑' n, reciprocalGreenTerm α B n * Real.cos (dot (dualWave B n) v)

theorem reciprocalPair_summable (α : ℝ) (B : Mat) (v : Vec)
    (h : Summable (reciprocalGreenTerm α B)) :
    Summable (fun n => reciprocalGreenTerm α B n * Real.cos (dot (dualWave B n) v)) := by
  apply h.norm.of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

theorem reciprocal_pairs_eq_objective {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec)
    (summable : Summable (reciprocalGreenTerm α B)) :
    (∑ i, ∑ j, reciprocalPair α B (s i-s j)) = reciprocalObjectiveSum α B s := by
  let f (i j : ι) (n : IntVec) := reciprocalGreenTerm α B n * Real.cos (dot (dualWave B n) (s i-s j))
  have h i j : Summable (f i j) := reciprocalPair_summable α B (s i-s j) summable
  have inner (i : ι) : (∑ j, reciprocalPair α B (s i-s j)) = ∑' n, ∑ j, f i j n := by
    change (∑ j, ∑' n, f i j n) = _
    exact (Summable.tsum_finsetSum (fun j _ => h i j)).symm
  have outer (i : ι) : Summable (fun n => ∑ j, f i j n) :=
    summable_sum (fun j _ => h i j)
  simp_rw [inner]
  rw [← Summable.tsum_finsetSum (fun i _ => outer i)]
  apply tsum_congr
  intro n
  simp only [f, ← Finset.mul_sum, reciprocal_pair_phase, reciprocalObjectiveTerm]

def periodIndices (B : Mat) (hB : B.det ≠ 0) : IntVec ≃ periodGroup B :=
  Equiv.ofBijective (fun n => ⟨linearImage B n, ⟨n,rfl⟩⟩) (by
    constructor
    · intro m n h
      have eq : B.mulVec (castVec m) = B.mulVec (castVec n) := congrArg Subtype.val h
      have hinj := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB))
      have he := hinj eq
      funext i
      have c : (m i : ℝ) = (n i : ℝ) := congrFun he i
      exact_mod_cast c
    · rintro ⟨_,⟨n,rfl⟩⟩
      exact ⟨n,rfl⟩)

def realPair (α : ℝ) (B : Mat) (v : Vec) : ℝ :=
  ∑' l : periodGroup B, screened α (v+l.val)

theorem realPair_eq_integer (α : ℝ) (B : Mat) (hB : B.det ≠ 0) (v : Vec) :
    realPair α B v = ∑' n, screened α (v+linearImage B n) :=
  ((periodIndices B hB).tsum_eq (fun l => screened α (v+l.val))).symm

def PeriodRepetition.rowPeriodEquiv {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ) (i : κ) :
    (κ × periodGroup C) ≃ periodGroup B :=
  let sign : periodGroup C ≃ periodGroup C := ⟨fun a => -a, fun a => -a, neg_neg, neg_neg⟩
  let v : periodGroup B := ⟨rep.representative i, rep.representativesInPeriod i⟩
  let sheet : periodGroup B ≃ periodGroup B := ⟨fun a => v-a, fun a => v-a,
    fun a => sub_sub_cancel v a, fun a => sub_sub_cancel v a⟩
  ((Equiv.prodCongr (Equiv.refl κ) sign).trans rep.periodEquiv).trans sheet

theorem PeriodRepetition.rowPeriod_apply {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ)
    (i j : κ) (z : periodGroup C) :
    (rep.rowPeriodEquiv i (j,z)).val = rep.representative i-rep.representative j+z.val := by
  change rep.representative i-(rep.representative j + -z.val) = _
  abel

theorem real_row_repetition {κ : Type} [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (i : κ) (α : ℝ) (v : Vec)
    (summable : Summable (fun l : periodGroup B => screened α (v+l.val))) :
    (∑ j, realPair α C (v+rep.representative i-rep.representative j)) = realPair α B v := by
  let e := rep.rowPeriodEquiv i
  let f (z : κ × periodGroup C) := screened α (v + (e z).val)
  have hs : Summable f := e.summable_iff.mpr summable
  unfold realPair
  calc
    _ = ∑' j : κ, ∑' l : periodGroup C, f (j,l) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro j _
      apply tsum_congr
      intro l
      unfold f e
      rw [rep.rowPeriod_apply]
      congr 1
      abel
    _ = ∑' z : κ × periodGroup C, f z := hs.tsum_prod.symm
    _ = _ := e.tsum_eq (fun l => screened α (v+l.val))

def realCellEnergy {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec) : ℝ :=
  (1/2) * ∑ i, ∑ j, realPair α B (s i-s j)

theorem real_cell_repetition {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (α : ℝ) (s : ι → Vec)
    (summable : ∀ i j, Summable (fun l : periodGroup B => screened α (s i-s j+l.val))) :
    realCellEnergy α C (repeatedSites rep s) = (Fintype.card κ : ℝ) * realCellEnergy α B s := by
  unfold realCellEnergy
  have hrow (i : ι) (k : κ) (j : ι) :
      (∑ l : κ, realPair α C (repeatedSites rep s (i,k)-repeatedSites rep s (j,l))) =
        realPair α B (s i-s j) := by
    have hs : (∑ l : κ, realPair α C (repeatedSites rep s (i,k)-repeatedSites rep s (j,l))) =
        ∑ l : κ, realPair α C (s i-s j+rep.representative k-rep.representative l) := by
      apply Finset.sum_congr rfl
      intro l _
      unfold repeatedSites
      congr 1
      abel
    rw [hs]
    exact real_row_repetition rep k α (s i-s j) (summable i j)
  simp_rw [Fintype.sum_prod_type, hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

theorem screened_zero (α : ℝ) : screened α 0 = 0 := by simp [screened, sq]

theorem green_at_zero_split (α : ℝ) (B : Mat) :
    periodicGreen α B 0 = ewaldRegularSelf α B + 2*α/Real.sqrt Real.pi := by
  have hreal : (∑' n, screened α (linearImage B n)) =
      ∑' n : IntVec, if n=0 then 0 else screened α (linearImage B n) := by
    apply tsum_congr
    intro n
    by_cases hn : n=0
    · simp [hn, linearImage, castVec_zero, screened_zero]
    · simp [hn]
  unfold periodicGreen ewaldRegularSelf
  simp only [zero_add, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.cos_zero, mul_one]
  rw [hreal]
  ring

private theorem add_diagonal {ι : Type} [Fintype ι] (f : ι → ι → ℝ) (d : ℝ)
    (diag : ∀ i, f i i = d) :
    (∑ i, ∑ j, if i=j then 0 else f i j) + (Fintype.card ι : ℝ)*d = ∑ i, ∑ j, f i j := by
  have hc : (Fintype.card ι : ℝ)*d = ∑ i : ι, ∑ j : ι, if i=j then d else 0 := by
    simp [Finset.sum_ite_eq, nsmul_eq_mul]
  rw [hc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i=j
  · subst j; simp [diag]
  · simp [h]

def neutralCell {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec) : ℝ :=
  realCellEnergy α B s + reciprocalCellEnergy α B s -
    (Fintype.card ι : ℝ)*α/Real.sqrt Real.pi -
    greenBackground α B*(Fintype.card ι : ℝ)^2/2

theorem greenCell_eq_neutral {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (hB : B.det ≠ 0) (s : ι → Vec)
    (hs : Summable (reciprocalGreenTerm α B)) : greenCellEnergy α B s = neutralCell α B s := by
  let G (i j : ι) := periodicGreen α B (s i-s j)
  have split := add_diagonal G (periodicGreen α B 0) (fun i => by simp [G])
  have hp (v : Vec) : periodicGreen α B v = realPair α B v +
      (4*Real.pi/volumeOf B)*reciprocalPair α B v - greenBackground α B := by
    unfold periodicGreen reciprocalPair
    rw [realPair_eq_integer α B hB]
  have hfull : (∑ i, ∑ j, G i j) = (∑ i, ∑ j, realPair α B (s i-s j)) +
      (4*Real.pi/volumeOf B)*(∑ i, ∑ j, reciprocalPair α B (s i-s j)) -
      greenBackground α B*(Fintype.card ι : ℝ)^2 := by
    unfold G
    simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hfull, green_at_zero_split] at split
  simp only [greenCellEnergy,neutralCell,realCellEnergy,reciprocalCellEnergy]
  rw [← reciprocal_pairs_eq_objective α B s hs]
  unfold G at split
  linear_combination (1/2 : ℝ) * split

theorem screened_per_particle_repetition {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0) (α : ℝ) (s : ι → Vec)
    (mPos : 0 < Fintype.card κ) (nPos : 0 < Fintype.card ι)
    (realConv : ∀ i j, Summable (fun l : periodGroup B => screened α (s i-s j+l.val)))
    (recipB : Summable (reciprocalGreenTerm α B)) (recipC : Summable (reciprocalGreenTerm α C)) :
    greenPerParticle α C (repeatedSites rep s) = greenPerParticle α B s := by
  unfold greenPerParticle
  rw [greenCell_eq_neutral α C hC _ recipC, greenCell_eq_neutral α B hB s recipB, Fintype.card_prod]
  have bg : greenBackground α C = greenBackground α B/(Fintype.card κ : ℝ) := by
    have hm : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast mPos.ne'
    unfold greenBackground
    rw [rep.volume_eq hB hC]
    by_cases ha : α=0
    · simp [ha]
    · field_simp [hm, ha, ((abs_pos.mpr hB).ne' : volumeOf B ≠ 0)] <;> ring
  unfold neutralCell
  rw [real_cell_repetition rep α s realConv, reciprocal_cell_repetition rep hB hC α s,
    bg, Fintype.card_prod]
  push_cast
  have hm : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast mPos.ne'
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast nPos.ne'
  field_simp [hm, hn] <;> ring

end BccSharp.Coulomb
