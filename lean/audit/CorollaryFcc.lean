import BccSharp.TwoSite.StatementFull

set_option autoImplicit false

/-! Supplementary check, not part of the development and not a module of the build.

`StatementFull` has no clause for the corollary "if `D = 1` then `e ≥ e_FCC`, with equality
exactly for FCC". This file derives it from the clauses `inequality` (through
`statement`), `equality`, `minimum` and `gapPositive`, so the conclusion of the reduction
theorems implies it. Run from the Lake package directory after the build:

  lake env lean <this file>
-/

open BccSharp.Coulomb BccSharp.Coulomb.Full TwoSiteSpec
open BccSharp.Coulomb.SpecBridge

/-- The corollary for configurations with defect one. -/
theorem corollaryFcc_of_statementFull (h : StatementFull) (q : TwoSite) (hq : q.Valid)
    (hD : defect q = 1) :
    energy fcc ≤ energy q ∧
      (energy q = energy fcc ↔ RigidImage (physPoints q) (dilate ac fccUnit)) := by
  have hineq := h.statement.inequality q hq
  rw [hD, mul_one] at hineq
  have hge : energy fcc ≤ energy q := by
    unfold gap at hineq
    linarith
  have heq := h.equality q hq
  rw [hD, mul_one] at heq
  refine ⟨hge, ?_, ?_⟩
  · intro he
    have hgap : energy q - energy bcc = gap := by
      unfold gap
      linarith
    rcases heq.mp hgap with hb | hf
    · have hmin := (h.minimum q hq).2.mpr hb
      have hg := h.statement.gapPositive
      unfold gap at hg
      linarith
    · exact hf
  · intro hf
    have hgap := heq.mpr (Or.inr hf)
    unfold gap at hgap
    linarith

set_option pp.fullNames true in
#check @corollaryFcc_of_statementFull
#print axioms corollaryFcc_of_statementFull
