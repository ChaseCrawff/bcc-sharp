module

public import BccSharp.Analysis.TorusLattice
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-! Euclidean realization of every finite-index bcc period lattice. The
fundamental-domain volume is derived from its index, rather than assumed. -/
@[expose] public section
noncomputable section
namespace BccSharp.PeriodLattice
open Ewald TorusLattice Module MeasureTheory
open scoped BigOperators

/-- The primitive bcc coordinate change has determinant 1/2. -/
def primitiveLinear : Vec ≃ₗ[ℝ] Vec where
  toFun x := ![x 0+x 2/2,x 1+x 2/2,x 2/2]
  invFun x := ![x 0-x 2,x 1-x 2,2*x 2]
  left_inv x := by ext i; fin_cases i <;> simp; ring
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

def basis : Basis (Fin 3) ℝ Vec := (Pi.basisFun ℝ (Fin 3)).map primitiveLinear

def spatial (Γ : AddSubgroup Lattice) : Submodule ℤ Vec := (Γ.map position).toIntSubmodule

def full : Submodule ℤ Vec := spatial ⊤

theorem mem_spatial (Γ : AddSubgroup Lattice) (x : Vec) :
    x ∈ spatial Γ ↔ ∃ z : Lattice, z ∈ Γ ∧ position z=x := Iff.rfl

theorem spatial_le_full (Γ : AddSubgroup Lattice) : spatial Γ ≤ full := by
  rintro x ⟨z,_,rfl⟩
  exact ⟨z,by trivial,rfl⟩

theorem position_injective : Function.Injective position := by
  intro x y he
  apply Subtype.ext
  have h (i : Fin 3) := congrFun he i
  apply Prod.ext
  · have hh := h 0
    change (1/2 : ℝ)*(x.val.1 : ℝ)=(1/2 : ℝ)*(y.val.1 : ℝ) at hh
    exact_mod_cast (mul_left_cancel₀ (by norm_num : (1/2 : ℝ) ≠ 0) hh)
  · apply Prod.ext
    · have hh := h 1
      change (1/2 : ℝ)*(x.val.2.1 : ℝ)=(1/2 : ℝ)*(y.val.2.1 : ℝ) at hh
      exact_mod_cast (mul_left_cancel₀ (by norm_num : (1/2 : ℝ) ≠ 0) hh)
    · have hh := h 2
      change (1/2 : ℝ)*(x.val.2.2 : ℝ)=(1/2 : ℝ)*(y.val.2.2 : ℝ) at hh
      exact_mod_cast (mul_left_cancel₀ (by norm_num : (1/2 : ℝ) ≠ 0) hh)

def primitiveIndex (i : Fin 3) : Lattice := primitive
  (if i=0 then (1,0,0) else if i=1 then (0,1,0) else (0,0,1))

theorem basis_eq_position (i : Fin 3) : basis i=position (primitiveIndex i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis,primitiveLinear,primitiveIndex,position,primitive,LatticeNeighborhood.center,coord,Pi.basisFun_apply]

theorem full_eq_span : full=Submodule.span ℤ (Set.range basis) := by
  apply le_antisymm
  · rintro x ⟨z,_,rfl⟩
    let a := coordinates z
    have hz : primitive a=z := primitiveEquiv.apply_symm_apply z
    have he : position z = (a.1 : ℤ) • basis 0 + (a.2.1 : ℤ) • basis 1 + (a.2.2 : ℤ) • basis 2 := by
      rw [← hz]
      ext i
      fin_cases i <;>
        simp [position,primitive,LatticeNeighborhood.center,coord,basis,primitiveLinear,Pi.basisFun_apply] <;> ring
    rw [he]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2,rfl⟩))
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact ⟨primitiveIndex i,by trivial,(basis_eq_position i).symm⟩

instance full_discrete : DiscreteTopology full := by
  rw [full_eq_span]
  infer_instance

instance spatial_discrete (Γ : AddSubgroup Lattice) : DiscreteTopology (spatial Γ) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology full) (spatial_le_full Γ)

instance full_lattice : IsZLattice ℝ full := by
  constructor
  rw [full_eq_span]
  exact ZSpan.span_top basis

instance spatial_lattice (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)] : IsZLattice ℝ (spatial Γ) := by
  constructor
  apply top_unique
  rw [← basis.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  let N := Fintype.card (Torus Γ)
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (N : ℝ) • basis i ∈ spatial Γ := by
    refine ⟨N • primitiveIndex i,index_multiple_mem Γ _,?_⟩
    rw [map_nsmul,← basis_eq_position]
    exact (Nat.cast_smul_eq_nsmul ℝ N (basis i)).symm
  have hs := (Submodule.span ℝ (spatial Γ : Set Vec)).smul_mem (1/(N : ℝ))
    (Submodule.subset_span hm)
  have he : (1/(N : ℝ)) • ((N : ℝ) • basis i)=basis i := by
    rw [smul_smul,one_div,inv_mul_cancel₀ hN,one_smul]
  rw [he] at hs
  exact hs

theorem covolume_full : ZLattice.covolume full = 1/2 := by
  rw [full_eq_span]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain basis volume),ZSpan.volume_real_fundamentalDomain]
  norm_num [basis,primitiveLinear,Pi.basisFun_apply,Matrix.det_fin_three]

theorem spatial_relIndex (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)] :
    (spatial Γ).toAddSubgroup.relIndex full.toAddSubgroup=Fintype.card (Torus Γ) := by
  change (Γ.map position).relIndex ((⊤ : AddSubgroup Lattice).map position)=_
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ position_injective,
    AddSubgroup.relIndex_top_right,AddSubgroup.index_eq_card,Nat.card_eq_fintype_card]

/-- The actual volume of a torus with N bcc sites is N/2. -/
theorem covolume_spatial (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)] :
    ZLattice.covolume (spatial Γ)=(Fintype.card (Torus Γ) : ℝ)/2 := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex (spatial Γ) full (spatial_le_full Γ)
  rw [covolume_full,spatial_relIndex] at h
  linarith

def fundamental (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)] : Set Vec :=
  ZSpan.fundamentalDomain ((IsZLattice.basis (spatial Γ)).ofZLatticeBasis ℝ)

theorem fundamental_domain (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)] :
    IsAddFundamentalDomain (spatial Γ) (fundamental Γ) volume :=
  ZLattice.isAddFundamentalDomain (IsZLattice.basis (spatial Γ)) volume

theorem fundamental_volume (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)] :
    volume.real (fundamental Γ)=(Fintype.card (Torus Γ) : ℝ)/2 := by
  rw [← ZLattice.covolume_eq_measure_fundamentalDomain _ volume (fundamental_domain Γ),covolume_spatial]

end BccSharp.PeriodLattice
