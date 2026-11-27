import BccSharp.TwoSite.ReferencePhysical
import BccSharp.TwoSite.SeriesModes
import BccSharp.TwoSite.RegularLimit

set_option autoImplicit false

/-! Exact point-set bridge between the primitive Constants reference cells
and the normalized/physical two-site BCC and FCC representatives. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.Constants

def refTwo : Reference → TwoSite
  | .bcc => bcc
  | .fcc => fcc

def fccLength : ℝ := (2 : ℝ) ^ (1/3 : ℝ)
def primitiveNormalized : Reference → Mat
  | .bcc => Reference.naturalBasis .bcc
  | .fcc => fccLength • Reference.naturalBasis .fcc

private def zsum (n : IntVec) : ℤ := n 0+n 1+n 2

private theorem bcc_columnSum (n : IntVec) (i : Fin 3) :
    (Reference.naturalBasis .bcc).mulVec (castVec n) i = ((zsum n : ℤ) : ℝ)/2 - (n i : ℝ) := by
  fin_cases i <;> norm_num [Reference.naturalBasis, Matrix.mulVec, dotProduct, castVec,
    Fin.sum_univ_three, zsum] <;> ring

private theorem bcc_half_period (m : IntVec) (r : ℤ) :
    (Reference.naturalBasis .bcc).mulVec (castVec (fun i => zsum m - m i+r)) =
      castVec m + (fun _ => (r : ℝ)/2) := by
  funext i
  rw [bcc_columnSum]
  simp only [castVec, Pi.add_apply, zsum]
  push_cast
  ring

theorem bcc_primitive_points : lattice (primitiveNormalized .bcc) = bcc.points := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    let s := zsum n
    let p : IntVec := fun i => s/2 - n i
    have hParity : s = 2*(s/2) ∨ s = 2*(s/2)+1 := by omega
    rcases hParity with even | odd
    · left
      refine ⟨p, ?_⟩
      simp only [bcc, Matrix.one_mulVec, primitiveNormalized]
      funext i
      rw [bcc_columnSum]
      change ((s/2-n i : ℤ) : ℝ) = ((s : ℤ) : ℝ)/2 - (n i : ℝ)
      have he : (s : ℝ) = 2*((s/2 : ℤ) : ℝ) := by exact_mod_cast even
      push_cast
      linarith
    · right
      refine ⟨castVec p, ⟨p, by simp [bcc]⟩, ?_⟩
      simp only [bcc, Matrix.one_mulVec, primitiveNormalized]
      funext i
      rw [bcc_columnSum]
      change (s : ℝ)/2-(n i : ℝ) = ((s/2-n i : ℤ) : ℝ)+1/2
      have ho : (s : ℝ) = 2*((s/2 : ℤ) : ℝ)+1 := by exact_mod_cast odd
      push_cast
      linarith
  · rintro (⟨m, rfl⟩ | ⟨_, ⟨m, rfl⟩, rfl⟩)
    · refine ⟨fun i => zsum m - m i, ?_⟩
      simpa [primitiveNormalized, bcc, ← Pi.zero_def] using bcc_half_period m 0
    · refine ⟨fun i => zsum m - m i + 1, ?_⟩
      simpa [primitiveNormalized, bcc] using bcc_half_period m 1

private def doubleFirst (n : IntVec) (r : ℤ) : IntVec := fun i => if i=0 then 2*n i + r else n i

private theorem fcc_half_period (n : IntVec) (r : ℤ) :
    (primitiveNormalized .fcc).mulVec (castVec (doubleFirst n r)) =
      fcc.basis.mulVec (castVec n) + (r : ℝ) • fcc.basis.mulVec fcc.offset := by
  funext i
  fin_cases i <;> norm_num [primitiveNormalized, fcc, fccLength, Reference.naturalBasis, castVec,
    doubleFirst, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;>
    push_cast <;> ring

theorem fcc_primitive_points : lattice (primitiveNormalized .fcc) = fcc.points := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    let m : IntVec := fun i => if i=0 then n i/2 else n i
    have hParity : n 0 = 2*(n 0/2) ∨ n 0 = 2*(n 0/2)+1 := by omega
    rcases hParity with he | ho
    · have hm : doubleFirst m 0 = n := by
        funext i
        by_cases hi : i=0
        · subst i; simpa [doubleFirst,m] using he.symm
        · simp [doubleFirst,m,hi]
      left
      exact ⟨m, by simpa [hm] using (fcc_half_period m 0).symm⟩
    · have hm : doubleFirst m 1 = n := by
        funext i
        by_cases hi : i=0
        · subst i; simpa [doubleFirst,m] using ho.symm
        · simp [doubleFirst,m,hi]
      right
      exact ⟨fcc.basis.mulVec (castVec m), ⟨m,rfl⟩, by simpa [hm] using fcc_half_period m 1⟩
  · rintro (⟨m,rfl⟩ | ⟨_,⟨m,rfl⟩,rfl⟩)
    · exact ⟨doubleFirst m 0, by simpa using fcc_half_period m 0⟩
    · exact ⟨doubleFirst m 1, by simpa using fcc_half_period m 1⟩

private theorem cube_eq_positive {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x^3=y^3) : x=y := by
  have factor : (x-y)*(x*x+x*y+y*y)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_right (by positivity))

private theorem fccLength_pos : 0 < fccLength := by unfold fccLength; positivity

private theorem fccLength_cube : fccLength^3 = 2 := by
  rw [fccLength, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem wsBasis_eq (ref : Reference) : (ref.wsFactor)⁻¹ • ref.naturalBasis = ac • primitiveNormalized ref := by
  have invcube : ((ref.wsFactor)⁻¹)^3 = (3*(ref.naturalVolume : ℝ)/(4*Real.pi))⁻¹ := by
    rw [inv_pow, wsFactor_cube]
  cases ref with
  | bcc =>
    have hs : (Reference.wsFactor .bcc)⁻¹ = ac := by
      apply cube_eq_positive (inv_pos.mpr (wsFactor_positive .bcc)) ac_positive
      rw [invcube, ac_cube]
      norm_num [Reference.naturalVolume]
      field_simp [Real.pi_pos.ne'] <;> ring
    rw [hs]
    rfl
  | fcc =>
    have hs : (Reference.wsFactor .fcc)⁻¹ = ac*fccLength := by
      apply cube_eq_positive (inv_pos.mpr (wsFactor_positive .fcc)) (mul_pos ac_positive fccLength_pos)
      rw [invcube, mul_pow, ac_cube, fccLength_cube]
      norm_num [Reference.naturalVolume]
      field_simp [Real.pi_pos.ne'] <;> ring
    rw [hs, primitiveNormalized, smul_smul]

theorem scaled_lattice (t : ℝ) (B : Mat) : lattice (t • B) = (fun x => t • x) '' lattice B := by
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨linearImage B n, ⟨n,rfl⟩, (linearImage_scale t B n).symm⟩
  · rintro ⟨_,⟨n,rfl⟩,rfl⟩
    exact ⟨n,linearImage_scale t B n⟩

theorem primitive_reference_physical_points (ref : Reference) :
    lattice ((ref.wsFactor)⁻¹ • ref.naturalBasis) = (fun x => ac • x) '' (refTwo ref).points := by
  rw [wsBasis_eq ref, scaled_lattice]
  cases ref
  · exact congrArg (_ '' ·) bcc_primitive_points
  · exact congrArg (_ '' ·) fcc_primitive_points

def primitiveWSBasis (ref : Reference) : Mat := (ref.wsFactor)⁻¹ • ref.naturalBasis

theorem primitiveWSBasis_nonsingular (ref : Reference) : (primitiveWSBasis ref).det ≠ 0 := by
  have hn : ref.naturalBasis.det ≠ 0 := by rw [naturalBasis_det]; cases ref <;> norm_num [Reference.naturalVolume]
  rw [primitiveWSBasis, Matrix.det_smul, Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero _ (inv_pos.mpr (wsFactor_positive ref)).ne') hn

theorem refTwo_valid (ref : Reference) : (refTwo ref).Valid := by
  cases ref with
  | bcc =>
    refine ⟨Matrix.det_one, fun n h => ?_⟩
    have he : (1 : ℝ)/2 = (n 0 : ℝ) := congrFun h 0
    have e : (2 : ℝ)*(n 0 : ℝ) = 1 := by linarith
    have ez : (2 : ℤ)*n 0 = 1 := by exact_mod_cast e
    omega
  | fcc =>
    refine ⟨?_, fun n h => ?_⟩
    · change fcc.basis.det = 1
      have hd : fcc.basis.det = fccLength^3/2 := by
        rw [Matrix.det_fin_three]
        norm_num [fcc, fccLength] <;> ring
      rw [hd, fccLength_cube]
      norm_num
    · have he : (1 : ℝ)/2 = (n 0 : ℝ) := congrFun h 0
      have e : (2 : ℝ)*(n 0 : ℝ) = 1 := by linarith
      have ez : (2 : ℤ)*n 0 = 1 := by exact_mod_cast e
      omega

theorem physical_positions_distinct (q : TwoSite) (hq : q.Valid) :
    distinctModulo (physicalBasis q) (physicalTwoPositions q) := by
  have zero : physicalTwoPositions q 0 = 0 := by simp [physicalTwoPositions, normalizedTwoPositions]
  have one : physicalTwoPositions q 1 = (physicalBasis q).mulVec q.offset := by
    simp [physicalTwoPositions, normalizedTwoPositions, physicalBasis, Matrix.smul_mulVec]
  have no : physicalTwoPositions q 1 ∉ lattice (physicalBasis q) := by
    rintro ⟨n, hn⟩
    rw [one] at hn
    have hu : IsUnit (physicalBasis q) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (series_physical_basis_nonsingular q hq))
    exact hq.2 n (Matrix.mulVec_injective_of_isUnit hu hn).symm
  intro i j hij
  have cases2 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  rcases cases2 i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [zero, zero_sub]
    intro h
    have h' := (periodGroup (physicalBasis q)).neg_mem h
    rw [neg_neg] at h'
    exact no h'
  · rw [zero, sub_zero]
    exact no

theorem physical_points_eq_twoSite (q : TwoSite) :
    periodicPoints (physicalBasis q) (physicalTwoPositions q) = (fun x => ac • x) '' q.points := by
  have site0 : normalizedTwoPositions q 0 = 0 := by simp [normalizedTwoPositions]
  have site1 : normalizedTwoPositions q 1 = q.basis.mulVec q.offset := by simp [normalizedTwoPositions]
  have hlin (n : IntVec) : linearImage (physicalBasis q) n = ac • linearImage q.basis n :=
    linearImage_scale ac q.basis n
  ext x
  constructor
  · rintro ⟨i, n, hx⟩
    rw [physicalTwoPositions, hlin, ← smul_add] at hx
    refine ⟨normalizedTwoPositions q i+linearImage q.basis n, ?_, hx.symm⟩
    have cases2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases cases2 i with rfl | rfl
    · rw [site0, zero_add]
      exact Or.inl ⟨n, rfl⟩
    · rw [site1]
      exact Or.inr ⟨linearImage q.basis n, ⟨n,rfl⟩, add_comm _ _⟩
  · rintro ⟨_, ⟨n,rfl⟩ | ⟨_,⟨n,rfl⟩,rfl⟩, rfl⟩
    · exact ⟨0,n,by rw [physicalTwoPositions,site0,smul_zero,zero_add,hlin] <;> rfl⟩
    · exact ⟨1,n,by rw [physicalTwoPositions,site1,hlin,← smul_add,add_comm] <;> rfl⟩

def pointsRepetition (B : Mat) (q : TwoSite) (hq : q.Valid)
    (hp : lattice B = periodicPoints (physicalBasis q) (physicalTwoPositions q)) :
    PeriodRepetition B (physicalBasis q) (Fin 2) where
  representative := physicalTwoPositions q
  uniquePeriod := by
    intro x hx
    have hx' : x ∈ periodicPoints (physicalBasis q) (physicalTwoPositions q) := by rwa [← hp]
    obtain ⟨i,n,hn⟩ := hx'
    have hi : x-physicalTwoPositions q i ∈ lattice (physicalBasis q) :=
      ⟨n, by rw [hn]; abel⟩
    refine ⟨i,hi,fun j hj => ?_⟩
    by_contra hij
    have hd := (periodGroup (physicalBasis q)).sub_mem hi hj
    have he : (x-physicalTwoPositions q i)-(x-physicalTwoPositions q j) =
        physicalTwoPositions q j-physicalTwoPositions q i := by abel
    rw [he] at hd
    exact physical_positions_distinct q hq j i hij hd
  representativesInPeriod := by
    intro i
    rw [hp]
    exact ⟨i,0,by simp [linearImage,castVec_zero]⟩
  subperiod := by
    rintro x ⟨n,rfl⟩
    rw [hp]
    exact ⟨0,n,by simp [physicalTwoPositions,normalizedTwoPositions,linearImage]⟩

theorem pointsRepetition_energy (B : Mat) (hB : B.det ≠ 0) (q : TwoSite) (hq : q.Valid)
    (hp : lattice B = periodicPoints (physicalBasis q) (physicalTwoPositions q))
    (α : ℝ) (hα : 0 < α) :
    greenPerParticle α (physicalBasis q) (physicalTwoPositions q) =
    greenPerParticle α B (fun _ : Fin 1 => (0 : Vec)) := by
  have h := greenPerParticle_repetition (pointsRepetition B q hq hp)
    hB (series_physical_basis_nonsingular q hq)
    α hα (fun _ : Fin 1 => (0 : Vec)) (by simp) (by simp)
  simpa [greenPerParticle, greenCellEnergy, repeatedSites, pointsRepetition,
    Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.card_prod] using h

theorem reference_repeated_at_same_screen (ref : Reference) (α : ℝ) (hα : 0 < α) :
    greenPerParticle α (physicalBasis (refTwo ref)) (physicalTwoPositions (refTwo ref)) =
    greenPerParticle α (primitiveWSBasis ref) (fun _ : Fin 1 => (0 : Vec)) := by
  apply pointsRepetition_energy _ (primitiveWSBasis_nonsingular ref) _ (refTwo_valid ref) _ α hα
  exact (primitive_reference_physical_points ref).trans (physical_points_eq_twoSite (refTwo ref)).symm

def referenceWSScreen (ref : Reference) : ℝ := (ref.alpha : ℝ) / (ref.wsFactor)⁻¹

theorem reference_primitive_singleton (α : ℝ) (B : Mat) :
    greenPerParticle α B (fun _ : Fin 1 => (0 : Vec)) = ewaldRegularSelf α B / 2 := by
  simp [greenPerParticle, greenCellEnergy, Fin.sum_univ_one]

theorem referenceWSScreen_positive (ref : Reference) : 0 < referenceWSScreen ref := by
  have ha : (0 : ℝ) < ref.alpha := by cases ref <;> norm_num [Reference.alpha]
  exact div_pos ha (inv_pos.mpr (wsFactor_positive ref))

/-- Endpoint transfer through the actual screened self identity and the
explicit index-two repetition. -/
theorem reference_bounds (ref : Reference) : ref.bracket.contains ref.energy := by
  have hp : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  have hs := ewaldRegularSelf_screening_independent seriesScreen (referenceWSScreen ref) (primitiveWSBasis ref)
    (primitiveWSBasis_nonsingular ref) hp (referenceWSScreen_positive ref)
  have h : ref.primitiveWS = ref.energy := by
    calc
      _ = greenPerParticle (referenceWSScreen ref) (primitiveWSBasis ref) (fun _ : Fin 1 => (0 : Vec)) :=
        primitiveWS_eq_scaled_cell ref
      _ = greenPerParticle seriesScreen (primitiveWSBasis ref) (fun _ : Fin 1 => (0 : Vec)) := by
        rw [reference_primitive_singleton, reference_primitive_singleton, hs]
      _ = greenPerParticle seriesScreen (physicalBasis (refTwo ref)) (physicalTwoPositions (refTwo ref)) :=
        (reference_repeated_at_same_screen ref seriesScreen hp).symm
      _ = ref.energy := by
        rw [green_two_eq_energy _ (refTwo_valid ref)]
        cases ref <;> rfl
  rw [← h]
  cases ref
  · exact bcc_primitive_enclosed
  · exact fcc_primitive_enclosed

theorem reference_gap_checked : gapBracket.contains gap ∧ 0 < gap :=
  gap_of_reference_bounds (reference_bounds .bcc) (reference_bounds .fcc)

end BccSharp.Coulomb.Constants
