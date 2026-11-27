import BccSharp.TwoSite.Physical

set_option autoImplicit false

/-! Constants reference checker and Series escape composition. The finite
rational decisions are executable definitions. The real enclosures enter
through explicit memberships until the Ewald interval evaluator is connected. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb
namespace Constants

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Interval.contains (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def Interval.add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Interval.sub (a b : Interval) : Interval := ⟨a.lo - b.hi, a.hi - b.lo⟩
def Interval.inside (a b : Interval) : Bool := decide (b.lo ≤ a.lo ∧ a.hi ≤ b.hi)

theorem Interval.add_sound {a b : Interval} {x y : ℝ} (hx : a.contains x) (hy : b.contains y) :
    (a.add b).contains (x + y) := by
  simpa [Interval.contains, Interval.add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem Interval.sub_sound {a b : Interval} {x y : ℝ} (hx : a.contains x) (hy : b.contains y) :
    (a.sub b).contains (x - y) := by
  simpa [Interval.contains, Interval.sub] using
    And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

theorem Interval.inside_sound {a b : Interval} {x : ℝ}
    (hc : a.inside b = true) (hx : a.contains x) : b.contains x := by
  have h : b.lo ≤ a.lo ∧ a.hi ≤ b.hi := of_decide_eq_true hc
  have hlo : (b.lo : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast h.1
  have hhi : (a.hi : ℝ) ≤ (b.hi : ℝ) := by exact_mod_cast h.2
  exact ⟨le_trans hlo hx.1, le_trans hx.2 hhi⟩

/-- Literal `e_ws_certified.lower` and `.upper` from the Constants receipt. -/
def bccBracket : Interval :=
  ⟨-0.89592925568176528916624546293829460538061046722070,
   -0.89592925568176528916624546293829460538061046722066⟩

def fccBracket : Interval :=
  ⟨-0.89587361519510845989748779611028534450181510608894,
   -0.89587361519510845989748779611028534450181510608890⟩

def gapBracket : Interval := fccBracket.sub bccBracket

theorem bracket_gap_positive : 0 < gapBracket.lo := by
  norm_num [gapBracket, Interval.sub, bccBracket, fccBracket]

theorem gap_of_reference_bounds (hB : bccBracket.contains (energy bcc))
    (hF : fccBracket.contains (energy fcc)) : gapBracket.contains gap ∧ 0 < gap := by
  have h := Interval.sub_sound hF hB
  have hlo : (0 : ℝ) < (gapBracket.lo : ℝ) := by exact_mod_cast bracket_gap_positive
  exact ⟨h, hlo.trans_le h.1⟩

inductive Reference where | bcc | fcc
  deriving DecidableEq, Repr

def Reference.energy : Reference → ℝ
  | .bcc => BccSharp.Coulomb.energy BccSharp.Coulomb.bcc
  | .fcc => BccSharp.Coulomb.energy BccSharp.Coulomb.fcc

def Reference.bracket : Reference → Interval
  | .bcc => bccBracket
  | .fcc => fccBracket

def Reference.alpha : Reference → ℚ
  | .bcc => 457 / 250
  | .fcc => 2303 / 1000

def Reference.realCut : Reference → ℚ
  | .bcc => 10000000 / 208849
  | .fcc => 160000000 / 5303809

def Reference.reciprocalCut : Reference → ℚ
  | .bcc => 54171721 / 1000000
  | .fcc => 42991057 / 500000

def Reference.naturalVolume : Reference → ℚ
  | .bcc => 1 / 2
  | .fcc => 1 / 4

def Reference.naturalBasis : Reference → Mat
  | .bcc => !![-1/2, 1/2, 1/2; 1/2, -1/2, 1/2; 1/2, 1/2, -1/2]
  | .fcc => !![0, 1/2, 1/2; 1/2, 0, 1/2; 1/2, 1/2, 0]

theorem naturalBasis_det (ref : Reference) : ref.naturalBasis.det = (ref.naturalVolume : ℝ) := by
  cases ref <;> norm_num [Reference.naturalBasis, Reference.naturalVolume, Matrix.det_fin_three]

def Reference.directGram : Reference → Mat
  | .bcc => fun i j => if i = j then 3/4 else -1/4
  | .fcc => fun i j => if i = j then 1/2 else 1/4

def Reference.reciprocalGram : Reference → Mat
  | .bcc => fun i j => if i = j then 2 else 1
  | .fcc => fun i j => if i = j then 3 else -1

theorem natural_gram_eq (ref : Reference) : gram ref.naturalBasis = ref.directGram := by
  ext i j
  cases ref <;> fin_cases i <;> fin_cases j <;>
    norm_num [gram, Reference.naturalBasis, Reference.directGram, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_three]

theorem gram_dual_product (ref : Reference) : ref.directGram * ref.reciprocalGram = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  cases ref <;> fin_cases i <;> fin_cases j <;>
    norm_num [Reference.directGram, Reference.reciprocalGram, Matrix.one_apply]

def Reference.realCount : Reference → Nat
  | .bcc => 2732
  | .fcc => 2778

def Reference.reciprocalCount : Reference → Nat
  | .bcc => 886
  | .fcc => 868

def qSquare (n : IntVec) : ℚ := ∑ i, ((n i : ℤ) : ℚ)^2
def qSum (n : IntVec) : ℚ := ∑ i, ((n i : ℤ) : ℚ)

def Reference.directForm (ref : Reference) (n : IntVec) : ℚ :=
  match ref with
  | .bcc => qSquare n - qSum n ^ 2 / 4
  | .fcc => (qSquare n + qSum n ^ 2) / 4

def Reference.dualForm (ref : Reference) (n : IntVec) : ℚ :=
  match ref with
  | .bcc => qSquare n + qSum n ^ 2
  | .fcc => 4 * qSquare n - qSum n ^ 2

theorem direct_quad_eq (ref : Reference) (n : IntVec) :
    quad (gram ref.naturalBasis) (castVec n) = (ref.directForm n : ℝ) := by
  rw [natural_gram_eq]
  cases ref <;>
    simp [quad, Matrix.mulVec, dotProduct, Reference.directGram, Reference.directForm,
      qSquare, qSum, castVec, Fin.sum_univ_three] <;> push_cast <;> ring

theorem reciprocal_quad_eq (ref : Reference) (n : IntVec) :
    quad ref.reciprocalGram (castVec n) = (ref.dualForm n : ℝ) := by
  cases ref <;>
    simp [quad, Matrix.mulVec, dotProduct, Reference.reciprocalGram, Reference.dualForm,
      qSquare, qSum, castVec, Fin.sum_univ_three] <;> push_cast <;> ring

private theorem bccForm_coordinate (x y z : ℚ) :
    x^2 / 2 ≤ x^2 + y^2 + z^2 - (x + y + z)^2 / 4 := by
  nlinarith [sq_nonneg (2*y - x), sq_nonneg (2*z - x), sq_nonneg (y-z)]

private theorem fccForm_coordinate (x y z : ℚ) :
    x^2 / 3 ≤ (x^2 + y^2 + z^2 + (x + y + z)^2) / 4 := by
  let s := x + y + z
  nlinarith [sq_nonneg (s + y), sq_nonneg (s + z), sq_nonneg (y-z)]

def Reference.directDiagonal : Reference → ℚ
  | .bcc => 2
  | .fcc => 3

def Reference.dualDiagonal : Reference → ℚ
  | .bcc => 3/4
  | .fcc => 1/2

theorem direct_coordinate_bound (ref : Reference) (n : IntVec) (i : Fin 3) :
    (n i : ℚ)^2 ≤ ref.directDiagonal * ref.directForm n := by
  have b (j k l : Fin 3) := bccForm_coordinate (n j : ℚ) (n k : ℚ) (n l : ℚ)
  have f (j k l : Fin 3) := fccForm_coordinate (n j : ℚ) (n k : ℚ) (n l : ℚ)
  cases ref <;> fin_cases i <;>
    simp [Reference.directDiagonal, Reference.directForm, qSquare, qSum, Fin.sum_univ_three] <;>
    nlinarith [b 0 1 2, b 1 0 2, b 2 0 1, f 0 1 2, f 1 0 2, f 2 0 1]

theorem reciprocal_coordinate_bound (ref : Reference) (n : IntVec) (i : Fin 3) :
    (n i : ℚ)^2 ≤ ref.dualDiagonal * ref.dualForm n := by
  cases ref
  · have h := direct_coordinate_bound .fcc n i
    unfold Reference.directDiagonal Reference.directForm at h
    unfold Reference.dualDiagonal Reference.dualForm
    linarith
  · have h := direct_coordinate_bound .bcc n i
    unfold Reference.directDiagonal Reference.directForm at h
    unfold Reference.dualDiagonal Reference.dualForm
    linarith

private theorem int_bound_of_square (n k : ℤ) (hk : 0 ≤ k) (h : (n : ℚ)^2 ≤ (k : ℚ)^2) :
    -k ≤ n ∧ n ≤ k := by
  have hkq : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  constructor
  · by_contra! hn
    have hh : (n : ℚ) < -(k : ℚ) := by exact_mod_cast hn
    have hp := mul_pos (show 0 < -(n : ℚ) - (k : ℚ) by linarith)
      (show 0 < -(n : ℚ) + (k : ℚ) by linarith)
    nlinarith
  · by_contra! hn
    have hh : (k : ℚ) < (n : ℚ) := by exact_mod_cast hn
    have hp := mul_pos (sub_pos.mpr hh) (show 0 < (n : ℚ) + (k : ℚ) by linarith)
    nlinarith

theorem direct_cube_complete (ref : Reference) (n : IntVec)
    (hcut : ref.directForm n ≤ ref.realCut) (i : Fin 3) : -10 ≤ n i ∧ n i ≤ 10 := by
  have hD : 0 ≤ ref.directDiagonal := by cases ref <;> norm_num [Reference.directDiagonal]
  have hCut : ref.directDiagonal * ref.realCut ≤ (10 : ℚ)^2 := by
    cases ref <;> norm_num [Reference.directDiagonal, Reference.realCut]
  exact int_bound_of_square _ _ (by decide) (le_trans (direct_coordinate_bound ref n i)
    (le_trans (mul_le_mul_of_nonneg_left hcut hD) hCut))

theorem reciprocal_cube_complete (ref : Reference) (n : IntVec)
    (hcut : ref.dualForm n ≤ ref.reciprocalCut) (i : Fin 3) : -7 ≤ n i ∧ n i ≤ 7 := by
  have hD : 0 ≤ ref.dualDiagonal := by cases ref <;> norm_num [Reference.dualDiagonal]
  have hCut : ref.dualDiagonal * ref.reciprocalCut ≤ (7 : ℚ)^2 := by
    cases ref <;> norm_num [Reference.dualDiagonal, Reference.reciprocalCut]
  exact int_bound_of_square _ _ (by decide) (le_trans (reciprocal_coordinate_bound ref n i)
    (le_trans (mul_le_mul_of_nonneg_left hcut hD) hCut))

abbrev Triple := ℤ × ℤ × ℤ
def asVector (n : Triple) : IntVec := ![n.1, n.2.1, n.2.2]

def cube (r : ℤ) : Finset Triple :=
  (Finset.Icc (-r) r) ×ˢ ((Finset.Icc (-r) r) ×ˢ (Finset.Icc (-r) r))

def Reference.directPoints (ref : Reference) : Finset Triple :=
  (cube 10).filter (fun n => n ≠ 0 ∧ ref.directForm (asVector n) ≤ ref.realCut)

def Reference.reciprocalPoints (ref : Reference) : Finset Triple :=
  (cube 7).filter (fun n => n ≠ 0 ∧ ref.dualForm (asVector n) ≤ ref.reciprocalCut)

def Reference.checkCounts (ref : Reference) : Bool :=
  decide (ref.directPoints.card = ref.realCount ∧
    ref.reciprocalPoints.card = ref.reciprocalCount)

theorem first_real_cut_exact (ref : Reference) : ref.alpha ^ 2 * ref.realCut = 160 := by
  cases ref <;> norm_num [Reference.alpha, Reference.realCut]

def Reference.wsFactor (ref : Reference) : ℝ :=
  (3 * (ref.naturalVolume : ℝ) / (4 * Real.pi)) ^ (1/3 : ℝ)

def Reference.directValue (ref : Reference) (radiusSq : ℚ) : ℝ :=
  let r := Real.sqrt (radiusSq : ℝ)
  erfcIntegral ((ref.alpha : ℝ) * r) / (2 * r)

def Reference.reciprocalValue (ref : Reference) (dualSq : ℚ) : ℝ :=
  Real.exp (- (Real.pi ^ 2 * (dualSq : ℝ) / (ref.alpha : ℝ)^2)) /
    (2 * Real.pi * (ref.naturalVolume : ℝ) * (dualSq : ℝ))

def Reference.finiteEnergy (ref : Reference) : ℝ :=
  ref.wsFactor *
    ((∑ n ∈ ref.directPoints, ref.directValue (ref.directForm (asVector n))) +
      (∑ n ∈ ref.reciprocalPoints, ref.reciprocalValue (ref.dualForm (asVector n))) -
      (ref.alpha : ℝ) / Real.sqrt Real.pi -
      Real.pi / (2 * (ref.naturalVolume : ℝ) * (ref.alpha : ℝ)^2))

/-- The tail endpoint covers both positive tails after WS scaling. Direct
and reciprocal analytic bounds must supply the membership. Receipt float
tail summaries do not supply endpoints for this check. -/
structure ReferenceProposal where
  finite : Interval
  tailUpper : ℚ
  deriving Repr

def ReferenceProposal.total (p : ReferenceProposal) : Interval :=
  p.finite.add ⟨0, p.tailUpper⟩

def ReferenceProposal.check (p : ReferenceProposal) (ref : Reference) : Bool :=
  decide (0 ≤ p.tailUpper) && p.total.inside ref.bracket

theorem ReferenceProposal.sound (p : ReferenceProposal) (ref : Reference)
    (hc : p.check ref = true) (hFinite : p.finite.contains ref.finiteEnergy)
    (hTail : (⟨0, p.tailUpper⟩ : Interval).contains (ref.energy - ref.finiteEnergy)) :
    ref.bracket.contains ref.energy := by
  have hc' := (Bool.and_eq_true_iff.mp hc).2
  have h := Interval.add_sound hFinite hTail
  rw [show ref.finiteEnergy + (ref.energy - ref.finiteEnergy) = ref.energy by ring] at h
  exact Interval.inside_sound hc' h

end Constants

def seriesPeriodThreshold : ℝ := 2 * gKernel (1/2) (25 * Real.pi / 64)
def seriesCollisionThreshold : ℝ := gKernel (1/2) (Real.pi / 4)

structure SeriesThresholdProofs : Prop where
  acPositive : 0 < ac
  periodAbove : 4 + 2 * ac * energy fcc < seriesPeriodThreshold
  collisionAbove : 4 + 2 * ac * energy fcc < seriesCollisionThreshold
  periodTerm : ∀ q : TwoSite, q.Valid → ∀ n : IntVec, n ≠ 0 →
    sq (q.basis.mulVec (castVec n)) ≤ (5/8 : ℝ)^2 → seriesPeriodThreshold ≤ h₂ q
  collisionTerm : ∀ q : TwoSite, q.Valid → ∀ n : IntVec,
    sq (q.basis.mulVec (castVec n + q.offset)) ≤ (1/2 : ℝ)^2 → seriesCollisionThreshold ≤ h₂ q

theorem belowFCC_separated (K : SeriesThresholdProofs) (q : TwoSite) (hv : q.Valid)
    (he : energy q ≤ energy fcc) : separated q := by
  have hscaled : h₂ q ≤ 4 + 2 * ac * energy fcc := by
    unfold energy at he
    change (h₂ q - 4) / (2 * ac) ≤ energy fcc at he
    have h := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) K.acPositive)).mp he
    linarith [mul_comm (energy fcc) (2 * ac)]
  constructor
  · intro n hn
    by_contra! hs
    exact (not_lt_of_ge (le_trans (K.periodTerm q hv n hn hs) hscaled)) K.periodAbove
  · intro n
    by_contra! hs
    exact (not_lt_of_ge (le_trans (K.collisionTerm q hv n hs) hscaled)) K.collisionAbove

end BccSharp.Coulomb
