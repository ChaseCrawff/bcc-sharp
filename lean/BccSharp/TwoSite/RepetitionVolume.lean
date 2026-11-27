import BccSharp.TwoSite.ReciprocalRepetition
import Mathlib.Algebra.Module.ZLattice.Covolume

set_option autoImplicit false

/-! Extension of the repository's PeriodLattice index/covolume
argument to every invertible basis matrix. -/

noncomputable section
open scoped BigOperators
open Classical MeasureTheory

namespace BccSharp.Coulomb

def periodModule (B : Mat) : Submodule ℤ Vec := (periodGroup B).toIntSubmodule

def matrixLinearEquiv (B : Mat) (hB : B.det ≠ 0) : Vec ≃ₗ[ℝ] Vec := by
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)
  exact LinearEquiv.ofBijective (Matrix.toLin' B) ⟨Matrix.mulVec_injective_of_isUnit hunit,
    Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩

def matrixBasis (B : Mat) (hB : B.det ≠ 0) : Module.Basis (Fin 3) ℝ Vec :=
  (Pi.basisFun ℝ (Fin 3)).map (matrixLinearEquiv B hB)

theorem matrixBasis_apply (B : Mat) (hB : B.det ≠ 0) (i : Fin 3) :
    matrixBasis B hB i = B.mulVec (Pi.single i 1) := by
  rw [matrixBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  show Matrix.toLin' B (Pi.single i 1) = B.mulVec (Pi.single i 1)
  exact Matrix.toLin'_apply B (Pi.single i 1)

theorem matrixBasis_column (B : Mat) (hB : B.det ≠ 0) (i j : Fin 3) : matrixBasis B hB i j = B j i := by
  rw [matrixBasis_apply, Matrix.mulVec_single_one, Matrix.col_apply]

theorem periodModule_eq_span (B : Mat) (hB : B.det ≠ 0) :
    periodModule B = Submodule.span ℤ (Set.range (matrixBasis B hB)) := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    have hsum : B.mulVec (castVec n) = ∑ i, (n i) • matrixBasis B hB i := by
      funext j
      rw [Finset.sum_apply, Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      show B j i * (n i : ℝ) = n i • matrixBasis B hB i j
      rw [matrixBasis_column, zsmul_eq_mul, mul_comm]
    show B.mulVec (castVec n) ∈ _
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    have h : castVec (Pi.single i 1) = Pi.single i (1 : ℝ) := by
      funext j
      by_cases e : i=j <;> simp [castVec, Pi.single_apply, e]
    show B.mulVec (castVec (Pi.single i 1)) = matrixBasis B hB i
    rw [h, matrixBasis_apply]

theorem periodModule_discrete (B : Mat) (hB : B.det ≠ 0) : DiscreteTopology (periodModule B) := by
  rw [periodModule_eq_span B hB]
  infer_instance

theorem periodModule_lattice (B : Mat) (hB : B.det ≠ 0) [DiscreteTopology (periodModule B)] :
    IsZLattice ℝ (periodModule B) := by
  constructor
  rw [periodModule_eq_span B hB]
  exact ZSpan.span_top (matrixBasis B hB)

theorem period_covolume_eq (B : Mat) (hB : B.det ≠ 0) [DiscreteTopology (periodModule B)]
    [IsZLattice ℝ (periodModule B)] : ZLattice.covolume (periodModule B) = volumeOf B := by
  rw [periodModule_eq_span B hB]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (matrixBasis B hB) volume), ZSpan.volume_real_fundamentalDomain]
  have hmat : (Matrix.of (matrixBasis B hB)) = B.transpose := by
    ext i j
    exact matrixBasis_column B hB i j
  rw [hmat, Matrix.det_transpose]
  rfl

abbrev PeriodQuotient (B C : Mat) := periodGroup B ⧸ (periodGroup C).addSubgroupOf (periodGroup B)

def PeriodRepetition.toCoset {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ) (i : κ) :
    PeriodQuotient B C := QuotientAddGroup.mk ⟨rep.representative i, rep.representativesInPeriod i⟩

theorem PeriodRepetition.toCoset_bijective {κ : Type} {B C : Mat} (rep : PeriodRepetition B C κ) :
    Function.Bijective rep.toCoset := by
  constructor
  · intro i j eq
    have mem : rep.representative i - rep.representative j ∈ lattice C :=
      QuotientAddGroup.eq_iff_sub_mem.mp eq
    obtain ⟨_, _, unique⟩ := rep.uniquePeriod (rep.representative i) (rep.representativesInPeriod i)
    have self : rep.representative i - rep.representative i ∈ lattice C := by
      rw [sub_self]
      exact (periodGroup C).zero_mem
    exact (unique i self).trans (unique j mem).symm
  · intro x
    refine Quotient.inductionOn x ?_
    intro v
    obtain ⟨i, same, _⟩ := rep.uniquePeriod v.val v.property
    refine ⟨i, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
    change rep.representative i - v.val ∈ lattice C
    rw [← neg_sub]
    exact (periodGroup C).neg_mem same

theorem PeriodRepetition.volume_eq {κ : Type} [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0) :
    volumeOf C = (Fintype.card κ : ℝ) * volumeOf B := by
  letI := periodModule_discrete B hB
  letI := periodModule_discrete C hC
  letI := periodModule_lattice B hB
  letI := periodModule_lattice C hC
  have h := ZLattice.covolume_div_covolume_eq_relIndex (periodModule C) (periodModule B) rep.subperiod
  have card : (periodGroup C).relIndex (periodGroup B) = Fintype.card κ := by
    change ((periodGroup C).addSubgroupOf (periodGroup B)).index = Fintype.card κ
    rw [AddSubgroup.index_eq_card]
    exact (Nat.card_congr (Equiv.ofBijective rep.toCoset rep.toCoset_bijective).symm).trans Nat.card_eq_fintype_card
  change ZLattice.covolume (periodModule C) / ZLattice.covolume (periodModule B) =
    ((periodGroup C).relIndex (periodGroup B) : ℝ) at h
  rw [period_covolume_eq C hC, period_covolume_eq B hB, card] at h
  exact (div_eq_iff (abs_pos.mpr hB).ne').mp h

def reciprocalCellEnergy {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec) : ℝ :=
  (2*Real.pi/volumeOf B) * reciprocalObjectiveSum α B s

theorem reciprocal_cell_repetition {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0) (α : ℝ) (s : ι → Vec) :
    reciprocalCellEnergy α C (repeatedSites rep s) = (Fintype.card κ : ℝ) * reciprocalCellEnergy α B s := by
  unfold reciprocalCellEnergy
  rw [reciprocal_sum_repetition rep hB hC, rep.volume_eq hB hC]
  by_cases hz : (Fintype.card κ : ℝ) = 0
  · simp [hz]
  · have hvol : volumeOf B ≠ 0 := (abs_pos.mpr hB).ne'
    field_simp

end BccSharp.Coulomb
