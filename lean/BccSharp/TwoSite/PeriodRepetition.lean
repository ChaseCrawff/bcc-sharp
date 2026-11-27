import BccSharp.TwoSite.Bravais

set_option autoImplicit false

/-! Exact parts of the physical supercell calculation. The lattice
reindexing and finite-character cancellation precede the general Ewald-series
and quotient-character identification. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

def PeriodRepetition.insertPeriod {ι : Type} {B enlarged : Mat}
    (rep : PeriodRepetition B enlarged ι) (v : ι × periodGroup enlarged) : periodGroup B :=
  ⟨rep.representative v.1 + v.2.val, (periodGroup B).add_mem
    (rep.representativesInPeriod _) (rep.subperiod v.2.property)⟩

theorem PeriodRepetition.insertPeriod_bijective {ι : Type} {B enlarged : Mat}
    (rep : PeriodRepetition B enlarged ι) : Function.Bijective rep.insertPeriod := by
  constructor
  · intro a b same
    let x := rep.insertPeriod a
    obtain ⟨i, _, unique⟩ := rep.uniquePeriod x.val x.property
    have ha : x.val - rep.representative a.1 ∈ lattice enlarged := by
      change rep.representative a.1 + a.2.val - rep.representative a.1 ∈ lattice enlarged
      rw [show rep.representative a.1 + a.2.val - rep.representative a.1 = a.2.val by abel]
      exact a.2.property
    have hb : x.val - rep.representative b.1 ∈ lattice enlarged := by
      change (rep.insertPeriod a).val - rep.representative b.1 ∈ lattice enlarged
      rw [same]
      change rep.representative b.1 + b.2.val - rep.representative b.1 ∈ lattice enlarged
      rw [show rep.representative b.1 + b.2.val - rep.representative b.1 = b.2.val by abel]
      exact b.2.property
    have index : a.1 = b.1 := (unique a.1 ha).trans (unique b.1 hb).symm
    have point := congrArg Subtype.val same
    change rep.representative a.1 + a.2.val = rep.representative b.1 + b.2.val at point
    rw [index] at point
    exact Prod.ext index (Subtype.ext (add_left_cancel point))
  · intro x
    obtain ⟨i, hi, _⟩ := rep.uniquePeriod x.val x.property
    refine ⟨(i, ⟨x.val - rep.representative i, hi⟩), Subtype.ext ?_⟩
    change rep.representative i + (x.val - rep.representative i) = x.val
    abel

def PeriodRepetition.periodEquiv {ι : Type} {B enlarged : Mat}
    (rep : PeriodRepetition B enlarged ι) : (ι × periodGroup enlarged) ≃ periodGroup B :=
  Equiv.ofBijective rep.insertPeriod rep.insertPeriod_bijective

theorem PeriodRepetition.real_space_reindex {ι : Type} {B enlarged : Mat}
    (rep : PeriodRepetition B enlarged ι) (term : Vec → ℝ) :
    (∑' z : ι × periodGroup enlarged, term (rep.representative z.1 + z.2.val)) =
      ∑' z : periodGroup B, term z.val := by
  exact rep.periodEquiv.tsum_eq (fun z => term z.val)

def repeatedSites {ι κ : Type} {B enlarged : Mat} (rep : PeriodRepetition B enlarged κ)
    (s : ι → Vec) (pair : ι × κ) : Vec := s pair.1 + rep.representative pair.2

theorem PeriodRepetition.same_periodic_points {ι κ : Type} {B enlarged : Mat}
    (rep : PeriodRepetition B enlarged κ) (s : ι → Vec) :
    periodicPoints enlarged (repeatedSites rep s) = periodicPoints B s := by
  ext x
  constructor
  · rintro ⟨⟨i, j⟩, n, he⟩
    have hp : rep.representative j + linearImage enlarged n ∈ periodGroup B :=
      (periodGroup B).add_mem (rep.representativesInPeriod j) (rep.subperiod ⟨n, rfl⟩)
    rcases hp with ⟨m, hm⟩
    have hm' : linearImage B m = rep.representative j + linearImage enlarged n := hm
    refine ⟨i, m, ?_⟩
    rw [hm']
    dsimp [repeatedSites] at he
    rw [he]
    abel
  · rintro ⟨i, n, he⟩
    have hp : linearImage B n ∈ lattice B := ⟨n, rfl⟩
    obtain ⟨j, ⟨m, hm⟩, _⟩ := rep.uniquePeriod (linearImage B n) hp
    refine ⟨(i, j), m, ?_⟩
    have eq : linearImage enlarged m = linearImage B n - rep.representative j := hm
    change x = (s i + rep.representative j) + linearImage enlarged m
    rw [eq, he]
    abel

theorem PeriodRepetition.same_actual_defect {ι κ : Type} {B enlarged : Mat}
    (rep : PeriodRepetition B enlarged κ) (s : ι → Vec) (x : Vec) :
    cappedDefect (liftedNeighbors (periodicPoints enlarged (repeatedSites rep s)) x) =
      cappedDefect (liftedNeighbors (periodicPoints B s) x) :=
  samePointSet_sameSiteDefect (rep.same_periodic_points s) x

section FinitePhase

variable {G : Type} [AddCommGroup G] [Fintype G]

def phaseTranslate (g : G) : G ≃ G where
  toFun x := g + x
  invFun x := -g + x
  left_inv x := neg_add_cancel_left g x
  right_inv x := add_neg_cancel_left g x

theorem phase_sum_zero (phase : G → ℂ)
    (hom : ∀ x y, phase (x + y) = phase x * phase y) {g : G} (hg : phase g ≠ 1) :
    (∑ x, phase x) = 0 := by
  have permuted : (∑ x, phase (g + x)) = ∑ x, phase x := (phaseTranslate g).sum_comp phase
  have eq : phase g * (∑ x, phase x) = ∑ x, phase x := by
    simp only [hom, ← Finset.mul_sum] at permuted
    exact permuted
  have prodZero : (phase g - 1) * (∑ x, phase x) = 0 := by
    rw [sub_mul, one_mul, eq, sub_self]
  exact (mul_eq_zero.mp prodZero).resolve_left (sub_ne_zero.mpr hg)

theorem phase_sum_trivial (phase : G → ℂ) (trivialPhase : ∀ x, phase x = 1) :
    (∑ x, phase x) = (Fintype.card G : ℂ) := by
  simp [trivialPhase]

end FinitePhase
end BccSharp.Coulomb
