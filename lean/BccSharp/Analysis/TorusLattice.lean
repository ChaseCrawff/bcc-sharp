module

public import BccSharp.Analysis.PeriodicPotential
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-! Every commensurate bcc torus is a finite quotient of the actual bcc
additive lattice. Its reciprocal vectors lie in a proved rational grid. -/
@[expose] public section
namespace BccSharp.TorusLattice
open Real Ewald LatticeTails

def bccSubgroup : AddSubgroup Triple where
  carrier := {z | bcc z}
  zero_mem' := by decide
  add_mem' := by
    intro a b ha hb
    change a.1%2=a.2.1%2 ∧ a.2.1%2=a.2.2%2 at ha
    change b.1%2=b.2.1%2 ∧ b.2.1%2=b.2.2%2 at hb
    change (a.1+b.1)%2=(a.2.1+b.2.1)%2 ∧ (a.2.1+b.2.1)%2=(a.2.2+b.2.2)%2
    omega
  neg_mem' := by
    intro a ha
    change a.1%2=a.2.1%2 ∧ a.2.1%2=a.2.2%2 at ha
    change (-a.1)%2=(-a.2.1)%2 ∧ (-a.2.1)%2=(-a.2.2)%2
    omega

abbrev Lattice := bccSubgroup

noncomputable def position : Lattice →+ Vec where
  toFun z := LatticeNeighborhood.center z.val
  map_zero' := by ext i; fin_cases i <;> simp [LatticeNeighborhood.center,coord]
  map_add' a b := by
    ext i
    simp only [LatticeNeighborhood.center,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      AddSubgroup.coe_add,coord_add]
    ring

def primitive (a : Triple) : Lattice :=
  ⟨(2*a.1+a.2.2,2*a.2.1+a.2.2,a.2.2),by
    change (2*a.1+a.2.2)%2 = (2*a.2.1+a.2.2)%2 ∧ (2*a.2.1+a.2.2)%2 = a.2.2%2
    omega⟩

def coordinates (z : Lattice) : Triple := ((z.val.1-z.val.2.2)/2,(z.val.2.1-z.val.2.2)/2,z.val.2.2)

def primitiveEquiv : Triple ≃+ Lattice where
  toFun := primitive
  invFun := coordinates
  left_inv a := by
    apply Prod.ext
    · simp [coordinates,primitive]
    · apply Prod.ext <;> simp [coordinates,primitive]
  right_inv z := by
    apply Subtype.ext
    have hz := z.property
    change z.val.1%2=z.val.2.1%2 ∧ z.val.2.1%2=z.val.2.2%2 at hz
    apply Prod.ext
    · simp only [primitive,coordinates]
      omega
    · apply Prod.ext
      · simp only [primitive,coordinates]
        omega
      · rfl
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext
    · simp only [primitive,Prod.fst_add,Prod.snd_add,AddSubgroup.coe_add]
      ring
    · apply Prod.ext <;> simp [primitive]
      all_goals ring

abbrev Torus (Γ : AddSubgroup Lattice) := Lattice ⧸ Γ

noncomputable def periodPredicate (Γ : AddSubgroup Lattice) (z : Triple) : Prop :=
  ∃ hz : bcc z, (⟨z,hz⟩ : Lattice) ∈ Γ

/-- Frequencies are expressed in u-units, so the reciprocal condition has
integer pairings rather than an additional factor of 2π. -/
def Reciprocal (Γ : AddSubgroup Lattice) (u : Vec) : Prop :=
  ∀ z : Lattice, z ∈ Γ → ∃ n : ℤ, dot u (position z) = n

theorem index_multiple_mem (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)] (z : Lattice) :
    Fintype.card (Torus Γ) • z ∈ Γ := by
  have h : Fintype.card (Torus Γ) • (QuotientAddGroup.mk z : Torus Γ) = 0 := card_nsmul_eq_zero
  rw [← QuotientAddGroup.mk_nsmul] at h
  exact (QuotientAddGroup.eq_zero_iff _).mp h

theorem dot_position_nsmul (u : Vec) (n : ℕ) (z : Lattice) :
    dot u (position (n • z)) = (n : ℝ)*dot u (position z) := by
  rw [map_nsmul]
  simp [dot,Fin.sum_univ_three,nsmul_eq_mul]
  ring

/-- Every reciprocal vector of an arbitrary finite-index bcc period lattice
is on the scaled fcc grid with denominator equal to the number of cells. -/
theorem reciprocal_grid (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)]
    {u : Vec} (hu : Reciprocal Γ u) :
    ∃ z : Triple, reciprocal z ∧ u = ReciprocalSeries.frequency (Fintype.card (Torus Γ)) z := by
  let N := Fintype.card (Torus Γ)
  obtain ⟨a,ha⟩ := hu (N • primitive (1,0,0)) (index_multiple_mem Γ _)
  obtain ⟨b,hb⟩ := hu (N • primitive (0,1,0)) (index_multiple_mem Γ _)
  obtain ⟨c,hc⟩ := hu (N • primitive (0,0,1)) (index_multiple_mem Γ _)
  rw [dot_position_nsmul] at ha hb hc
  norm_num [position,primitive,LatticeNeighborhood.center,coord,dot,Fin.sum_univ_three] at ha hb hc
  refine ⟨(a,b,2*c-a-b),?_,?_⟩
  · change (a+b+(2*c-a-b))%2=0
    omega
  · have hN : (N : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    funext i
    fin_cases i
    · change u 0 = (1/(N : ℝ))*(a : ℝ)
      field_simp [hN]
      nlinarith
    · change u 1 = (1/(N : ℝ))*(b : ℝ)
      field_simp [hN]
      nlinarith
    · change u 2 = (1/(N : ℝ))*((2*c-a-b : ℤ) : ℝ)
      push_cast
      field_simp [hN]
      nlinarith

theorem frequency_injective {m : ℝ} (hm : 0 < m) :
    Function.Injective (ReciprocalSeries.frequency m) := by
  intro z w he
  have hc (i : Fin 3) : coord z i = coord w i := by
    have h := congrFun he i
    change (1/m)*coord z i = (1/m)*coord w i at h
    exact mul_left_cancel₀ (by positivity : (1/m : ℝ) ≠ 0) h
  apply Prod.ext
  · simpa [coord] using hc 0
  · apply Prod.ext
    · simpa [coord] using hc 1
    · simpa [coord] using hc 2

end BccSharp.TorusLattice
