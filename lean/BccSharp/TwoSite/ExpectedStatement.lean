import BccSharp.TwoSite.SeriesModes

set_option autoImplicit false

/-! Independent physical declaration types for the final audit. They
are propositions, not proofs. The proof root must discharge all seven types. -/

noncomputable section

namespace BccSharp.TwoSiteTarget.ExpectedStatement
open BccSharp.Coulomb

def physicalEnergy (q : TwoSite) : ℝ :=
  greenPerParticle seriesScreen (physicalBasis q) (physicalTwoPositions q)

def physicalGap : ℝ := physicalEnergy fcc - physicalEnergy bcc

def sharpActualDefect : Prop :=
  0 < physicalGap ∧ ∀ q : TwoSite, q.Valid →
    physicalGap * defect q ≤ physicalEnergy q - physicalEnergy bcc

def bccFccEquality : Prop :=
  ∀ q : TwoSite, q.Valid →
    (physicalEnergy q - physicalEnergy bcc = physicalGap * defect q ↔ IsBCC q ∨ IsFCC q)

def uniqueBCC : Prop :=
  ∀ q : TwoSite, q.Valid → physicalEnergy bcc ≤ physicalEnergy q ∧
    (physicalEnergy q = physicalEnergy bcc ↔ IsBCC q)

def optimalCoefficient : Prop :=
  ∀ c : ℝ, (∀ q : TwoSite, q.Valid → c * defect q ≤ physicalEnergy q - physicalEnergy bcc) →
    c ≤ physicalGap

def subFCCRegistration : Prop :=
  ∀ q : TwoSite, q.Valid → physicalEnergy q < physicalEnergy fcc →
    Registration q ∧ defect q ≤ (physicalEnergy q - physicalEnergy bcc) / physicalGap ∧
      (physicalEnergy q - physicalEnergy bcc) / physicalGap < 1

def periodRepetition : Prop :=
  ∀ (q : TwoSite) (B : Mat) (n : ℕ), q.Valid → 0 < n → B.det ≠ 0 →
    ∀ rep : PeriodRepetition (physicalBasis q) B (Fin n),
      greenPerParticle seriesScreen B (repeatedSites rep (physicalTwoPositions q)) = physicalEnergy q

def densityScaling : Prop :=
  ∀ q : TwoSite, q.Valid → ∀ scale : ℝ, 0 < scale →
    greenPerParticle (seriesScreen / scale) (scale • physicalBasis q)
      (fun i => scale • physicalTwoPositions q i) = physicalEnergy q / scale

theorem physicalEnergy_eq_reduced (q : TwoSite) (hq : q.Valid) : physicalEnergy q = energy q :=
  green_two_eq_energy q hq

theorem periodRepetition_screened : periodRepetition := by
  intro q B n hq hn hB rep
  have hα : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  exact greenPerParticle_repetition rep (series_physical_basis_nonsingular q hq) hB
    seriesScreen hα (physicalTwoPositions q) (by simpa using hn) (by simp)

theorem densityScaling_screened : densityScaling := by
  intro q hq scale hs
  exact greenPerParticle_scale seriesScreen scale hs (physicalBasis q)
    (series_physical_basis_nonsingular q hq) (physicalTwoPositions q)

end BccSharp.TwoSiteTarget.ExpectedStatement
