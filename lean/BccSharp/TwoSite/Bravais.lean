import BccSharp.TwoSite.Physical
import BccSharp.TwoSite.ScalarChecks

set_option autoImplicit false

/-! Exact half-period and equality route. the lattice theorem's analytic inequality
and complete finite cover enter under `BravaisComparison`. -/

noncomputable section
open Classical

namespace BccSharp.Coulomb

theorem castVec_zero : castVec 0 = 0 := by
  funext i
  simp [castVec]

def periodGroup (B : Mat) : AddSubgroup Vec where
  carrier := lattice B
  zero_mem' := ⟨0, by
    show B.mulVec (castVec 0) = 0
    rw [castVec_zero, Matrix.mulVec_zero]⟩
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by
      show B.mulVec (castVec (m + n)) = B.mulVec (castVec m) + B.mulVec (castVec n)
      rw [castVec_add, Matrix.mulVec_add]⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, by
      show B.mulVec (castVec (-n)) = -B.mulVec (castVec n)
      rw [castVec_neg, Matrix.mulVec_neg]⟩

/-- Exact index-two extension as an additive subgroup. Distinctness and
bounded covolume are separate facts. -/
def halfExtension (L : AddSubgroup Vec) (t : Vec) (ht : t + t ∈ L) : AddSubgroup Vec where
  carrier := (L : Set Vec) ∪ translate t L
  zero_mem' := Or.inl L.zero_mem
  add_mem' := by
    intro x y hx hy
    rcases hx with hx | ⟨u, hu, rfl⟩ <;> rcases hy with hy | ⟨v, hv, rfl⟩
    · exact Or.inl (L.add_mem hx hy)
    · exact Or.inr ⟨x + v, L.add_mem hx hv, by abel⟩
    · exact Or.inr ⟨u + y, L.add_mem hu hy, by abel⟩
    · exact Or.inl (show (u + t) + (v + t) ∈ L from by
        convert L.add_mem (L.add_mem hu hv) ht using 1 <;> abel)
  neg_mem' := by
    intro x hx
    rcases hx with hx | ⟨u, hu, rfl⟩
    · exact Or.inl (L.neg_mem hx)
    · exact Or.inr ⟨-u - (t + t), L.sub_mem (L.neg_mem hu) ht, by abel⟩

theorem halfExtension_disjoint (L : AddSubgroup Vec) {t : Vec} (ht : t ∉ L) :
    Disjoint (L : Set Vec) (translate t L) := by
  refine Set.disjoint_left.mpr ?_
  rintro x hx ⟨u, hu, he⟩
  have h : x - u ∈ L := L.sub_mem hx hu
  rw [he, show u + t - u = t by abel] at h
  exact ht h

theorem translate_period_add (L : AddSubgroup Vec) (t a : Vec) (ha : a ∈ L) :
    translate (t + a) L = translate t L := by
  ext x
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨u + a, L.add_mem hu ha, he.trans (by abel)⟩
  · rintro ⟨u, hu, he⟩
    exact ⟨u - a, L.sub_mem hu ha, he.trans (by abel)⟩

def anchorOf (q : TwoSite) (f₀ : Vec) : TwoSite := ⟨q.basis, f₀⟩

theorem anchor_valid (q : TwoSite) (hq : q.Valid) (f₀ : Vec) (half : HalfClass f₀) :
    (anchorOf q f₀).Valid := ⟨hq.1, half.2⟩

theorem exact_half_extension (q : TwoSite) (f₀ : Vec) (half : HalfClass f₀)
    (injective : Function.Injective q.basis.mulVec) :
    ∃ H : AddSubgroup Vec, (H : Set Vec) = (anchorOf q f₀).points ∧
      Disjoint (lattice q.basis) (translate (q.basis.mulVec f₀) (lattice q.basis)) := by
  let t := q.basis.mulVec f₀
  have htwo : t + t ∈ periodGroup q.basis := by
    obtain ⟨n, hn⟩ := half.1
    refine ⟨n, ?_⟩
    show q.basis.mulVec (castVec n) = t + t
    rw [← hn, two_smul, Matrix.mulVec_add]
  have hnot : t ∉ periodGroup q.basis := by
    rintro ⟨n, hn⟩
    exact half.2 n (injective hn.symm)
  exact ⟨halfExtension (periodGroup q.basis) t htwo, rfl,
    halfExtension_disjoint _ hnot⟩

theorem zero_displacement_same_points (q : TwoSite) (f₀ : Vec) (n : IntVec)
    (injective : Function.Injective q.basis.mulVec)
    (h : sq (q.basis.mulVec (q.offset - f₀ - castVec n)) = 0) :
    q.points = (anchorOf q f₀).points := by
  have hzero : q.offset - f₀ - castVec n = 0 := injective (by
    simpa using (sq_eq_zero_iff _).mp h)
  have hoffset : q.offset = f₀ + castVec n := by
    calc
      q.offset = (q.offset - f₀ - castVec n) + (f₀ + castVec n) := by abel
      _ = f₀ + castVec n := by rw [hzero, zero_add]
  have hn : q.basis.mulVec (castVec n) ∈ periodGroup q.basis := ⟨n, rfl⟩
  have key : translate (q.basis.mulVec f₀ + q.basis.mulVec (castVec n)) (lattice q.basis) =
      translate (q.basis.mulVec f₀) (lattice q.basis) :=
    translate_period_add (periodGroup q.basis) _ _ hn
  unfold TwoSite.points anchorOf
  rw [hoffset, Matrix.mulVec_add, key]

/-- The exact the lattice theorem interface needed here. Discharge by transporting the
one-site latticeCase proof from a primitive basis of covolume one half. -/
def BravaisComparison : Prop :=
  ∀ q : TwoSite, q.Valid → HalfClass q.offset →
    0 ≤ deficit q ∧ (deficit q = 0 → IsBCC q ∨ IsFCC q)

def oneSiteDefect (P : Mat) : ℝ := cappedDefect (liftedNeighbors (lattice P) 0)

/-- `P` has covolume one half in two-site normalized lengths. Multiplying
by `ac` gives covolume 4π/3 in WS units. -/
def oneSiteEnergy (P : Mat) : ℝ :=
  greenPerParticle seriesScreen (ac • P) (fun _ : Fin 1 => (0 : Vec))

theorem oneSite_energy_is_self (P : Mat) :
    oneSiteEnergy P = ewaldRegularSelf seriesScreen (ac • P) / 2 := by
  simp [oneSiteEnergy, greenPerParticle, greenCellEnergy, Fin.sum_univ_one]

structure PrimitiveAnchorModel (q : TwoSite) where
  basis : Mat
  volume : basis.det = 1/2
  points : lattice basis = q.points
  sameEnergy : oneSiteEnergy basis = energy q

theorem anchor_same_defect {q : TwoSite} (model : PrimitiveAnchorModel q) :
    oneSiteDefect model.basis = defect q :=
  samePointSet_sameSiteDefect model.points 0

def oneSiteDeficit (P : Mat) : ℝ := oneSiteEnergy P - energy bcc - gap * oneSiteDefect P

def LatticeCase : Prop :=
  ∀ P : Mat, P.det = 1/2 →
    0 ≤ oneSiteDeficit P ∧ (oneSiteDeficit P = 0 →
      rigidCopy (lattice P) bcc.points ∨ rigidCopy (lattice P) fcc.points)

theorem bravais_of_one_site (oneSite : LatticeCase)
    (identify : ∀ q : TwoSite, q.Valid → HalfClass q.offset → Nonempty (PrimitiveAnchorModel q)) :
    BravaisComparison := by
  intro q hq half
  obtain ⟨model⟩ := identify q hq half
  have hd : oneSiteDeficit model.basis = deficit q := by
    simp only [oneSiteDeficit, deficit, model.sameEnergy, anchor_same_defect model]
  have claim := oneSite model.basis model.volume
  rw [hd, model.points] at claim
  exact claim

theorem optical_from_Bravais (bravais : BravaisComparison) (q : TwoSite) (hq : q.Valid)
    (injective : Function.Injective q.basis.mulVec)
    (f₀ : Vec) (n : IntVec) (half : HalfClass f₀) (uniformMargin curvature : ℚ)
    (hcheck : relativeCheck uniformMargin curvature = true)
    (hGain : deficit (anchorOf q f₀) + (uniformMargin : ℝ) +
      (curvature : ℝ) * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤ deficit q) :
    LeafProof q := by
  have hAnchor := bravais (anchorOf q f₀) (anchor_valid q hq f₀ half) half
  apply relativeSound q f₀ n uniformMargin curvature hcheck half hAnchor.1 hGain
  intro deficitZero displacementZero
  have hs := zero_displacement_same_points q f₀ n injective displacementZero
  simpa only [IsBCC, IsFCC, hs] using hAnchor.2 deficitZero

end BccSharp.Coulomb
