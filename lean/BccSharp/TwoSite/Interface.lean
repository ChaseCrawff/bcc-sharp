import Mathlib

set_option autoImplicit false

/-! Mathematical interface for the classical two-site theorem. The definitions below
are proposed targets. In particular, the positive-series identification,
compact reduction, registration, and the global certificate are still inputs
to the assembly lemmas, with each obligation visible in its type. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

abbrev Vec := Fin 3 → ℝ
abbrev IntVec := Fin 3 → ℤ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
abbrev Chart := Fin 8 → ℝ

def castVec (n : IntVec) : Vec := fun i => n i
def sq (v : Vec) : ℝ := ∑ i, (v i)^2
def frobSq (M : Mat) : ℝ := ∑ i, ∑ j, (M i j)^2
def ac : ℝ := (8 * Real.pi / 3) ^ (1 / 3 : ℝ)

theorem sq_nonnegative (v : Vec) : 0 ≤ sq v := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

theorem sq_eq_zero_iff (v : Vec) : sq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hle : (v i)^2 ≤ sq v := by
      unfold sq
      exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have hz : v i = 0 := by nlinarith [sq_nonneg (v i)]
    exact hz
  · rintro rfl
    simp [sq]

structure TwoSite where
  basis : Mat
  offset : Vec

def TwoSite.Valid (q : TwoSite) : Prop :=
  q.basis.det = 1 ∧ ∀ n : IntVec, q.offset ≠ castVec n

def lattice (B : Mat) : Set Vec := Set.range (fun n : IntVec => B.mulVec (castVec n))
def translate (v : Vec) (s : Set Vec) : Set Vec := {x | ∃ y ∈ s, x = y + v}

def TwoSite.points (q : TwoSite) : Set Vec :=
  lattice q.basis ∪ translate (q.basis.mulVec q.offset) (lattice q.basis)

def proper (U : Mat) : Prop := U.transpose * U = 1 ∧ U.det = 1

def rigidCopy (s t : Set Vec) : Prop :=
  ∃ v : Vec, ∃ U : Mat, proper U ∧ s = translate v (U.mulVec '' t)

def bcc : TwoSite := ⟨1, fun _ => 1 / 2⟩

/-- The normalized FCC primitive basis has entries 2^(1/3)/2 off the
diagonal. Doubling its first column gives the two-site period basis. -/
def fcc : TwoSite :=
  ⟨fun i j => if i = j then 0 else
    (2 : ℝ) ^ (1 / 3 : ℝ) / 2 * (if j = 0 then 2 else 1),
    fun i => if i = 0 then 1 / 2 else 0⟩

def IsBCC (q : TwoSite) : Prop := rigidCopy q.points bcc.points
def IsFCC (q : TwoSite) : Prop := rigidCopy q.points fcc.points

def gKernel (a t : ℝ) : ℝ :=
  ∫ u in Set.Ioi (1 : ℝ), Real.exp (-t * u) * u ^ (a - 1)

def quad (M : Mat) (v : Vec) : ℝ := ∑ i, v i * M.mulVec v i
def dot (v w : Vec) : ℝ := ∑ i, v i * w i

/-- Series positive Ewald series. The proof obligations include summability and
identification with the physical WS energy, with the regular self term. -/
def h₂ (q : TwoSite) : ℝ :=
  let M := q.basis.transpose * q.basis
  (∑' n : IntVec, if n = 0 then 0 else gKernel (1/2) (Real.pi * quad M (castVec n))) +
  (∑' n : IntVec, gKernel (1/2) (Real.pi * quad M (castVec n + q.offset))) +
  (∑' n : IntVec, if n = 0 then 0 else
    (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
      gKernel 1 (Real.pi * quad M⁻¹ (castVec n)))

def energy (q : TwoSite) : ℝ := (h₂ q - 4) / (2 * ac)
def gap : ℝ := energy fcc - energy bcc

def star (label : Fin 14) : Vec := fun i =>
  if label.val < 8 then
    if label.val / (2 ^ i.val) % 2 = 0 then -(1 / 2 : ℝ) else 1 / 2
  else if i.val = (label.val - 8) / 2 then
    if label.val % 2 = 0 then -1 else 1
  else 0

def liftedNeighbors (S : Set Vec) (site : Vec) : Set Vec :=
  {v | site + v ∈ S ∧ v ≠ 0 ∧ sq v < (13 / 10 : ℝ)^2}

def neighbors (q : TwoSite) : Set Vec := liftedNeighbors q.points 0

def annularWeight (v : Vec) : ℝ := max 0 (min 1 (13 - 10 * Real.sqrt (sq v)))

/-- Include the cap as a candidate to handle an empty set of injections.
For valid q, prove finiteness of the neighbor subtype, boundedness and
attainment before using this expression as the physical defect. -/
def defectTrial {Y : Set Vec} (U : Mat) (σ : Fin 14 ↪ ↥Y) : ℝ :=
  25 * (∑ j, sq ((σ j : Vec) - U.mulVec (star j))) +
    ∑' v : ↥Y, if v ∈ Set.range σ then 0 else annularWeight v.val

def defectCandidates (Y : Set Vec) : Set ℝ :=
  insert 1 {c | ∃ U : Mat, proper U ∧ ∃ σ : Fin 14 ↪ ↥Y, c = defectTrial U σ}

def cappedDefect (Y : Set Vec) : ℝ := sInf (defectCandidates Y)

def defect (q : TwoSite) : ℝ := cappedDefect (neighbors q)

theorem cappedDefect_range (Y : Set Vec) : 0 ≤ cappedDefect Y ∧ cappedDefect Y ≤ 1 := by
  have hOne : (1 : ℝ) ∈ defectCandidates Y := Set.mem_insert _ _
  have hLower : ∀ c ∈ defectCandidates Y, 0 ≤ c := by
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | ⟨U, _, σ, rfl⟩
    · norm_num
    · apply add_nonneg
      · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => sq_nonnegative _))
      · apply tsum_nonneg
        intro v
        split_ifs
        · exact le_rfl
        · exact le_max_left _ _
  exact ⟨le_csInf ⟨1, hOne⟩ hLower, csInf_le ⟨0, hLower⟩ hOne⟩

theorem defect_range (q : TwoSite) : 0 ≤ defect q ∧ defect q ≤ 1 :=
  cappedDefect_range (neighbors q)

def deficit (q : TwoSite) : ℝ := energy q - energy bcc - gap * defect q

def chartBasis (p : Chart) : Mat :=
  !![p 0, p 0 * p 2, p 0 * p 3;
     0,   p 1,       p 1 * p 4;
     0,   0,         (p 0 * p 1)⁻¹]

def chartPoint (p : Chart) : TwoSite := ⟨chartBasis p, ![p 5, p 6, p 7]⟩

def inRoot (p : Chart) : Prop :=
  p 0 ∈ Set.Icc (5/8 : ℝ) (37/32) ∧ p 1 ∈ Set.Icc (1/2 : ℝ) (11/8) ∧
  p 2 ∈ Set.Icc (0 : ℝ) (1/2) ∧ p 3 ∈ Set.Icc (0 : ℝ) (1/2) ∧
  ∀ i : Fin 8, 4 ≤ i.val → p i ∈ Set.Icc (-1/2 : ℝ) (1/2)

def reductionInequalities (p : Chart) : Prop :=
  (∀ n : IntVec, n ≠ 0 → (p 0)^2 ≤ sq ((chartBasis p).mulVec (castVec n))) ∧
  (∀ j k : ℤ, j ≠ 0 ∨ k ≠ 0 →
    (p 1)^2 ≤ (p 1 * ((j : ℝ) + p 4 * (k : ℝ)))^2 +
      ((k : ℝ) / (p 0 * p 1))^2)

def separated (q : TwoSite) : Prop :=
  (∀ n : IntVec, n ≠ 0 → (5/8 : ℝ)^2 < sq (q.basis.mulVec (castVec n))) ∧
  (∀ n : IntVec, (1/2 : ℝ)^2 < sq (q.basis.mulVec (castVec n + q.offset)))

structure ReducedRepresentative (q : TwoSite) (p : Chart) : Prop where
  root : inRoot p
  reduced : reductionInequalities p
  valid : (chartPoint p).Valid
  separation : separated (chartPoint p)
  samePoints : rigidCopy q.points (chartPoint p).points
  sameEnergy : energy (chartPoint p) = energy q
  sameDefect : defect (chartPoint p) = defect q

def HalfClass (f₀ : Vec) : Prop :=
  (∃ n : IntVec, (2 : ℝ) • f₀ = castVec n) ∧ ∀ n : IntVec, f₀ ≠ castVec n

def IndexTwoBCC (B : Mat) (f₀ : Vec) : Prop :=
  B.det = 1 ∧ HalfClass f₀ ∧ B.mulVec f₀ ∉ lattice B ∧
  bcc.points = lattice B ∪ translate (B.mulVec f₀) (lattice B)

def Registration (q : TwoSite) : Prop :=
  ∃ p, ReducedRepresentative q p ∧
    ∃ (B : Mat) (f₀ : Vec) (n : IntVec) (U : Mat), IndexTwoBCC B f₀ ∧ proper U ∧
      100 * frobSq (chartBasis p * B⁻¹ - U) +
      200 * sq ((chartBasis p).mulVec ((chartPoint p).offset - f₀ - castVec n)) ≤ defect q

/-- A local result used by the cover. An exact half shift denotes a Bravais
anchor of the same total density. A displacement coefficient belongs in the
witness even when the recorded uniform margin is zero. -/
inductive LeafProof (q : TwoSite) : Prop
  | strictFCC (positive : energy fcc < energy q)
  | strictDeficit (positive : 0 < deficit q)
  | classifiedNonnegative (nonnegative : 0 ≤ deficit q)
      (equality : deficit q = 0 → IsBCC q ∨ IsFCC q)
  | localBasin (cost coefficient : ℝ) (coefficientPos : 0 < coefficient) (costNonneg : 0 ≤ cost)
      (bound : coefficient * cost ≤ deficit q)
      (center : cost = 0 → IsBCC q ∨ IsFCC q)
  | optical (f₀ : Vec) (n : IntVec) (coefficient : ℝ)
      (half : HalfClass f₀) (coefficientPos : 0 < coefficient)
      (anchorNonneg : 0 ≤ deficit (⟨q.basis, f₀⟩ : TwoSite))
      (comparison : deficit (⟨q.basis, f₀⟩ : TwoSite) +
        coefficient * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤ deficit q)
      (anchorEquality : deficit (⟨q.basis, f₀⟩ : TwoSite) = 0 →
        sq (q.basis.mulVec (q.offset - f₀ - castVec n)) = 0 → IsBCC q ∨ IsFCC q)

theorem leaf_of_nonpositive (q : TwoSite) (hgap : 0 < gap) (cap : defect q ≤ 1)
    (h : deficit q ≤ 0) (witness : LeafProof q) :
    deficit q = 0 ∧ (IsBCC q ∨ IsFCC q) := by
  cases witness with
  | strictFCC positive =>
      have hcap := mul_le_mul_of_nonneg_left cap (le_of_lt hgap)
      unfold deficit gap at h
      unfold gap at hcap
      linarith
  | strictDeficit positive => exact (not_lt_of_ge h positive).elim
  | classifiedNonnegative nonneg eqCase =>
      have zero := le_antisymm h nonneg
      exact ⟨zero, eqCase zero⟩
  | localBasin cost coefficient positive nonneg bound center =>
      have hprod := mul_nonneg (le_of_lt positive) nonneg
      have zeroCost : cost = 0 := by
        by_contra hz
        have hp := mul_pos positive (lt_of_le_of_ne nonneg (Ne.symm hz))
        linarith
      exact ⟨le_antisymm h (le_trans hprod bound), center zeroCost⟩
  | optical f₀ n coefficient half positive hn bound eqCase =>
      let t := sq (q.basis.mulVec (q.offset - f₀ - castVec n))
      have ht : 0 ≤ t := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hprod := mul_nonneg (le_of_lt positive) ht
      change deficit (⟨q.basis, f₀⟩ : TwoSite) + coefficient * t ≤ deficit q at bound
      have zeroT : t = 0 := by
        by_contra hz
        have hp := mul_pos positive (lt_of_le_of_ne ht (Ne.symm hz))
        linarith
      have zeroAnchor : deficit (⟨q.basis, f₀⟩ : TwoSite) = 0 := by linarith
      exact ⟨by linarith, eqCase zeroAnchor zeroT⟩

theorem subFCC_of_deficit (q : TwoSite) (hgap : 0 < gap)
    (hd : 0 ≤ deficit q) (he : energy q < energy fcc) :
    defect q ≤ (energy q - energy bcc) / gap ∧ (energy q - energy bcc) / gap < 1 := by
  constructor
  · apply (le_div_iff₀ hgap).2
    unfold deficit at hd
    linarith [mul_comm (defect q) gap]
  · apply (div_lt_iff₀ hgap).2
    unfold gap
    linarith

structure Statement : Prop where
  gapPositive : 0 < gap
  inequality : ∀ q, q.Valid → gap * defect q ≤ energy q - energy bcc
  equality : ∀ q, q.Valid → (deficit q = 0 ↔ IsBCC q ∨ IsFCC q)
  minimum : ∀ q, q.Valid → energy bcc ≤ energy q ∧ (energy q = energy bcc ↔ IsBCC q)
  sharp : ∀ k : ℝ, (∀ q, q.Valid → k * defect q ≤ energy q - energy bcc) → k ≤ gap
  registration : ∀ q, q.Valid → energy q < energy fcc →
    Registration q ∧ defect q ≤ (energy q - energy bcc) / gap ∧
      (energy q - energy bcc) / gap < 1

/-- Explicit assembly parameters. `chartCover` denotes a typed geometric and
arithmetic proof of the cover. A receipt or totals cannot construct it. -/
structure Inputs : Prop where
  gapPositive : 0 < gap
  defectRange : ∀ q, q.Valid → 0 ≤ defect q ∧ defect q ≤ 1
  compact : ∀ q, q.Valid → energy q ≤ energy fcc → ∃ p, ReducedRepresentative q p
  chartCover : ∀ q p, ReducedRepresentative q p → LeafProof q
  bccValues : ∀ q, q.Valid → IsBCC q → energy q = energy bcc ∧ defect q = 0
  fccValues : ∀ q, q.Valid → IsFCC q → energy q = energy fcc ∧ defect q = 1
  fccValid : fcc.Valid
  fccSaturated : defect fcc = 1
  register : ∀ q p, ReducedRepresentative q p → defect q < 1 → Registration q

theorem assemble (input : Inputs) : Statement := by
  have nonpositive (q : TwoSite) (hq : q.Valid) (h : deficit q ≤ 0) :
      deficit q = 0 ∧ (IsBCC q ∨ IsFCC q) := by
    have cap := (input.defectRange q hq).2
    have hc : energy q ≤ energy fcc := by
      have hcap := mul_le_mul_of_nonneg_left cap (le_of_lt input.gapPositive)
      have hd := h
      unfold deficit gap at hd
      unfold gap at hcap
      linarith
    obtain ⟨p, hp⟩ := input.compact q hq hc
    exact leaf_of_nonpositive q input.gapPositive cap h (input.chartCover q p hp)
  have deficitNonneg (q : TwoSite) (hq : q.Valid) : 0 ≤ deficit q := by
    by_contra hn
    have hlt : deficit q < 0 := lt_of_not_ge hn
    exact (ne_of_lt hlt) (nonpositive q hq (le_of_lt hlt)).1
  refine ⟨input.gapPositive, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hd := deficitNonneg q hq
    unfold deficit at hd
    linarith
  · intro q hq
    constructor
    · intro hz
      exact (nonpositive q hq (le_of_eq hz)).2
    · rintro (hb | hf)
      · rcases input.bccValues q hq hb with ⟨he, hD⟩
        simp [deficit, he, hD]
      · rcases input.fccValues q hq hf with ⟨he, hD⟩
        simp [deficit, he, hD, gap]
  · intro q hq
    have hd := deficitNonneg q hq
    have hprod := mul_nonneg (le_of_lt input.gapPositive) (input.defectRange q hq).1
    have hmin : energy bcc ≤ energy q := by unfold deficit at hd; linarith
    refine ⟨hmin, ?_, fun hb => (input.bccValues q hq hb).1⟩
    intro he
    have hzero : deficit q = 0 := by unfold deficit at hd ⊢; linarith
    rcases (nonpositive q hq (le_of_eq hzero)).2 with hb | hf
    · exact hb
    · have hEf := (input.fccValues q hq hf).1
      have hg := input.gapPositive
      unfold gap at hg
      linarith
  · intro k all
    simpa [input.fccSaturated, gap] using all fcc input.fccValid
  · intro q hq he
    obtain ⟨hupper, hlt⟩ := subFCC_of_deficit q input.gapPositive (deficitNonneg q hq) he
    obtain ⟨p, hp⟩ := input.compact q hq (le_of_lt he)
    exact ⟨input.register q p hp (lt_of_le_of_lt hupper hlt), hupper, hlt⟩

end BccSharp.Coulomb
