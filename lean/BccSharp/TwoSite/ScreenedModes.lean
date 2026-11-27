import BccSharp.TwoSite.ScreenedSeries

set_option autoImplicit false

/-! Per-mode lower bounds for the series at a rational screening `s > 0`.

The checked kernel bounds `halfLower_sound` and `oneLower_sound`
(`BccSharp.Lattice.StrictLeaves`) bound `G(1/2, π x)` and `G(1, π x)` from below for
`x` in a rational ball. At screening `s` the modes of
`ScreenedSeries.h₂_screened` are `G(1/2, π s² Q)` and `G(1, π Q*/s²)`, so the
same bounds apply to the balls `s² · [Q]` and `[Q*] / s²` (`scaleBall`), after
`π s² Q = π (s² Q)` and `π Q*/s² = π (Q*/s²)`.

* `crossTerm_lower`, `periodTerm_lower`, `recipTerm_lower`, `waveTerm_lower`:
  lower bounds for the terms of `BccSharp.TwoSite.ScreenedSeries`, given a ball for the
  rescaled argument.
* `crossLowerS_sound`, `periodLowerS_sound`, `waveLowerS_sound`: the same at
  every valid point of a chart cell, from the Direct enclosures `realDistance`,
  `reciprocalDistance` and `phaseTurns`; the evaluators are the s = 1
  evaluators `directLower`, `reciprocalLower` and `phaseLower` applied to the
  rescaled balls.
* `finiteValueS_sound`: their sum over the Direct index lists, with the prefactors
  `s`, `2s` and `2/s²` and the constant `2s + 2/s²`, is a lower bound for
  `h₂ − 4` (through `finite_lower_lex`). It is the screened form of
  `DirectRoute.finiteValue_sound`; `finiteValueS_energy` is the energy form. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.ScreenedSeries
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover (HalfLower OneLower halfLower oneLower halfLower_sound
  oneLower_sound)
open BccSharp.Coulomb.CompactCover (Cell)
open BccSharp.Coulomb.CompactCover.DirectRoute (diagonalsCheck realDistance realDistance_sound
  reciprocalDistance reciprocalDistance_sound phaseTurns phaseTurns_sound phaseLower phaseLower_sound
  phaseLower_nonnegative directLower reciprocalLower lexPositive lex_ne cross_distance_positive
  period_distance_positive reciprocalPositive sumLower sumLower_sound directIndices pairedIndices)

/-! ### Rescaled balls -/

/-- A ball for `c x` from a ball for `x`. -/
def scaleBall (c : ℚ) (b : Ball) : Ball := (Ball.exact c).mul b

theorem scaleBall_contains (c : ℚ) {b : Ball} {x : ℝ} (h : b.Contains x) :
    (scaleBall c b).Contains ((c : ℝ) * x) :=
  Ball.contains_mul (Ball.contains_exact c) h

/-! ### The kernel bounds at the screened rates -/

theorem crossTerm_lower (s : ℝ) (q : TwoSite) (n : IntVec) {b : Ball}
    (hb : b.Contains (s ^ 2 * quad (gram q.basis) (castVec n + q.offset)))
    (hpos : 0 < s ^ 2 * quad (gram q.basis) (castVec n + q.offset))
    (w : HalfLower) (l : ℚ) (ok : halfLower b w = some l) : (l : ℝ) ≤ crossTerm s q n := by
  have h := halfLower_sound hb hpos w l ok
  rw [crossTerm, mul_assoc Real.pi]
  exact h

theorem periodTerm_lower (s : ℝ) (q : TwoSite) {n : IntVec} (hn : n ≠ 0) {b : Ball}
    (hb : b.Contains (s ^ 2 * quad (gram q.basis) (castVec n)))
    (hpos : 0 < s ^ 2 * quad (gram q.basis) (castVec n))
    (w : HalfLower) (l : ℚ) (ok : halfLower b w = some l) : (l : ℝ) ≤ periodTerm s q n := by
  have h := halfLower_sound hb hpos w l ok
  rw [periodTerm, ite_eq_right hn, mul_assoc Real.pi]
  exact h

theorem recipTerm_lower (s : ℝ) (q : TwoSite) {n : IntVec} (hn : n ≠ 0) {b : Ball}
    (hb : b.Contains (quad (gram q.basis)⁻¹ (castVec n) / s ^ 2))
    (hpos : 0 < quad (gram q.basis)⁻¹ (castVec n) / s ^ 2)
    (w : OneLower) (l : ℚ) (ok : oneLower b w = some l) : (l : ℝ) ≤ recipTerm s q n := by
  have h := oneLower_sound hb hpos w l ok
  rw [recipTerm, ite_eq_right hn, mul_div_assoc]
  exact h

theorem waveTerm_lower (s : ℝ) (q : TwoSite) (n : IntVec) {c l : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) (hl0 : 0 ≤ l)
    (hl : l ≤ recipTerm s q n) : c * l ≤ waveTerm s q n := by
  rw [waveTerm_eq]
  exact mul_le_mul hc hl hl0 (hc0.trans hc)

private theorem oneLower_nonneg' {z : Ball} {w : OneLower} {l : ℚ} (ok : oneLower z w = some l) :
    0 ≤ l := by
  cases w with
  | «omit» =>
    have hl : l = 0 := (Option.some.inj ok).symm
    exact le_of_eq hl.symm
  | check w =>
    simp only [oneLower] at ok
    split_ifs at ok
    rw [← Option.some.inj ok]
    exact le_max_left _ _

/-! ### Per-mode bounds on a chart cell -/

/-- Cross mode at screening `s`: the direct bound of the ball `s² · [Q]`. -/
def crossLowerS (s : ℚ) (b : Cell) (n : IntVec) : Option ℚ :=
  directLower (scaleBall (s * s) (realDistance b true n))

/-- Period mode at screening `s`: the direct bound of the ball `s² · [Q]`. -/
def periodLowerS (s : ℚ) (b : Cell) (n : IntVec) : Option ℚ :=
  directLower (scaleBall (s * s) (realDistance b false n))

/-- `1/s²`, kept folded so that `simp` leaves the ball arguments alone. -/
def invSq (s : ℚ) : ℚ := 1 / (s * s)

/-- Wave mode at screening `s`: the Direct phase bound times the reciprocal bound
of the ball `[Q*] / s²`. -/
def waveLowerS (s : ℚ) (b : Cell) (n : IntVec) : Option ℚ := do
  let a ← phaseLower (phaseTurns b n)
  let c ← reciprocalLower (scaleBall (invSq s) (reciprocalDistance b n))
  pure (a * c)

theorem crossLowerS_sound (s : ℚ) (hs : 0 < s) {b : Cell} {p : Chart} (hp : b.Mem p)
    (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) (n : IntVec) (v : ℚ)
    (e : crossLowerS s b n = some v) : (v : ℝ) ≤ crossTerm (s : ℝ) (chartPoint p) n := by
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  have hb := scaleBall_contains (s * s) (realDistance_sound hp hd true n)
  have hq : 0 < quad (gram (chartPoint p).basis) (castVec n + (chartPoint p).offset) :=
    cross_distance_positive hv n
  have hb' : (scaleBall (s * s) (realDistance b true n)).Contains
      ((s : ℝ) ^ 2 * quad (gram (chartPoint p).basis) (castVec n + (chartPoint p).offset)) := by
    have e2 : ((s * s : ℚ) : ℝ) = (s : ℝ) ^ 2 := by push_cast; ring
    rw [← e2]
    exact hb
  unfold crossLowerS directLower at e
  exact crossTerm_lower (s : ℝ) (chartPoint p) n hb' (mul_pos (pow_pos sr 2) hq) _ v e

theorem periodLowerS_sound (s : ℚ) (hs : 0 < s) {b : Cell} {p : Chart} (hp : b.Mem p)
    (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) (n : IntVec) (hn : lexPositive n)
    (v : ℚ) (e : periodLowerS s b n = some v) : (v : ℝ) ≤ periodTerm (s : ℝ) (chartPoint p) n := by
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  have hb := scaleBall_contains (s * s) (realDistance_sound hp hd false n)
  have hq : 0 < quad (gram (chartPoint p).basis) (castVec n) := period_distance_positive hv n hn
  have hb' : (scaleBall (s * s) (realDistance b false n)).Contains
      ((s : ℝ) ^ 2 * quad (gram (chartPoint p).basis) (castVec n)) := by
    have e2 : ((s * s : ℚ) : ℝ) = (s : ℝ) ^ 2 := by push_cast; ring
    rw [← e2]
    exact hb
  unfold periodLowerS directLower at e
  exact periodTerm_lower (s : ℝ) (chartPoint p) (lex_ne hn) hb' (mul_pos (pow_pos sr 2) hq) _ v e

theorem waveLowerS_sound (s : ℚ) (hs : 0 < s) {b : Cell} {p : Chart} (hp : b.Mem p)
    (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) (n : IntVec) (hn : lexPositive n)
    (v : ℚ) (e : waveLowerS s b n = some v) : (v : ℝ) ≤ waveTerm (s : ℝ) (chartPoint p) n := by
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  cases phase : phaseLower (phaseTurns b n) with
  | none => simp [waveLowerS, phase] at e
  | some a =>
    cases recip : reciprocalLower (scaleBall (invSq s) (reciprocalDistance b n)) with
    | none => simp [waveLowerS, phase, recip] at e
    | some c =>
      have eq : v = a * c := by simpa [waveLowerS, phase, recip, eq_comm] using e
      have hA := phaseLower_sound (phaseTurns_sound hp n) a phase
      have hQ : 0 < quad (gram (chartPoint p).basis)⁻¹ (castVec n) :=
        reciprocalPositive hv (lex_ne hn)
      have hb := scaleBall_contains (invSq s) (reciprocalDistance_sound hp hd n)
      have hb' : (scaleBall (invSq s) (reciprocalDistance b n)).Contains
          (quad (gram (chartPoint p).basis)⁻¹ (castVec n) / (s : ℝ) ^ 2) := by
        have e2 : ∀ x : ℝ, x / (s : ℝ) ^ 2 = ((invSq s : ℚ) : ℝ) * x := by
          intro x
          simp only [invSq]
          push_cast
          ring
        rw [e2]
        exact hb
      have hC := recipTerm_lower (s : ℝ) (chartPoint p) (lex_ne hn) hb'
        (div_pos hQ (pow_pos sr 2)) _ c recip
      have c0 : (0 : ℝ) ≤ c := by exact_mod_cast oneLower_nonneg' recip
      have a0 : (0 : ℝ) ≤ a := by exact_mod_cast phaseLower_nonnegative phase
      rw [eq, Rat.cast_mul]
      exact waveTerm_lower (s : ℝ) (chartPoint p) n a0 hA c0 hC

/-! ### The screened finite value -/

/-- Screened form of `DirectRoute.finiteValue`: per-mode lower bounds over the
Direct index lists, with the prefactors `s`, `2s`, `2/s²` and the constant
`2s + 2/s²`. -/
def finiteValueS (s : ℚ) (b : Cell) (radius : Nat) : Option ℚ := do
  let c ← sumLower (crossLowerS s b) (directIndices radius)
  let h ← sumLower (periodLowerS s b) (pairedIndices radius)
  let r ← sumLower (waveLowerS s b) (pairedIndices radius)
  pure (s * c + 2 * s * h + 2 / (s * s) * r - (2 * s + 2 / (s * s)))

theorem finiteValueS_sound (s : ℚ) (hs : 0 < s) (b : Cell) (radius : Nat) (p : Chart)
    (hp : b.Mem p) (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid)
    (nd : (directIndices radius).Nodup ∧ (pairedIndices radius).Nodup)
    (v : ℚ) (ok : finiteValueS s b radius = some v) : (v : ℝ) ≤ h₂ (chartPoint p) - 4 := by
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  cases ec : sumLower (crossLowerS s b) (directIndices radius) with
  | none => simp [finiteValueS, ec] at ok
  | some cv =>
    cases ep : sumLower (periodLowerS s b) (pairedIndices radius) with
    | none => simp [finiteValueS, ec, ep] at ok
    | some pv =>
      cases er : sumLower (waveLowerS s b) (pairedIndices radius) with
      | none => simp [finiteValueS, ec, ep, er] at ok
      | some rv =>
        have pos (n : IntVec) (hn : n ∈ pairedIndices radius) : lexPositive n :=
          of_decide_eq_true (List.mem_filter.mp hn).2
        have hC := sumLower_sound (crossLowerS s b) (fun n => crossTerm (s : ℝ) (chartPoint p) n) _
          nd.1 (fun n _ x e => crossLowerS_sound s hs hp hd hv n x e) cv ec
        have hP := sumLower_sound (periodLowerS s b) (fun n => periodTerm (s : ℝ) (chartPoint p) n) _
          nd.2 (fun n hn x e => periodLowerS_sound s hs hp hd hv n (pos n hn) x e) pv ep
        have hW := sumLower_sound (waveLowerS s b) (fun n => waveTerm (s : ℝ) (chartPoint p) n) _
          nd.2 (fun n hn x e => waveLowerS_sound s hs hp hd hv n (pos n hn) x e) rv er
        have fl := finite_lower_lex (chartPoint p) hv (s : ℝ) sr (directIndices radius).toFinset
          (pairedIndices radius).toFinset (pairedIndices radius).toFinset
          (fun n hn => pos n (List.mem_toFinset.mp hn)) (fun n hn => pos n (List.mem_toFinset.mp hn))
        have eq : v = s * cv + 2 * s * pv + 2 / (s * s) * rv - (2 * s + 2 / (s * s)) := by
          simpa [finiteValueS, ec, ep, er, eq_comm] using ok
        have m1 := mul_le_mul_of_nonneg_left hC sr.le
        have m2 := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 2 * (s : ℝ))
        have m3 := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ 2 / (s : ℝ) ^ 2)
        have e2 : (2 : ℝ) / ((s : ℝ) * (s : ℝ)) = 2 / (s : ℝ) ^ 2 := by ring
        rw [eq]
        push_cast
        rw [e2]
        linarith [fl, m1, m2, m3]

/-- The energy form of `finiteValueS_sound`. -/
theorem finiteValueS_energy (s : ℚ) (hs : 0 < s) (b : Cell) (radius : Nat) (p : Chart)
    (hp : b.Mem p) (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid)
    (nd : (directIndices radius).Nodup ∧ (pairedIndices radius).Nodup)
    (v : ℚ) (ok : finiteValueS s b radius = some v) :
    (v : ℝ) / (2 * ac) ≤ energy (chartPoint p) := by
  unfold energy
  exact div_le_div_of_nonneg_right (finiteValueS_sound s hs b radius p hp hd hv nd v ok)
    (mul_pos two_pos ac_positive).le

end BccSharp.Coulomb.ScreenedSeries
