import BccSharp.Lattice.FixedLocal
import BccSharp.Cover.Stage2Tangents

set_option autoImplicit false

/-! Tangent lower-bound functions for the Lattice E1 leaves.

The two positive-series kernels are convex, so a tangent line anchored at any
positive argument bounds a kernel term from below for every lattice
(`Stage2.globalTangent`). A finite set of tangent terms (`TermSet`) therefore gives
one lower bound `A - F(p)` of the positive series, valid at every chart point.
`F` is a nonnegative combination of squared direct and dual lengths, and each
squared length is convex in every chart coordinate separately on a box whose
first two coordinates are positive. The maximum of `F` over such a box is then
attained at one of its 32 corners (`corner_max`).

A term set is summarized by an `Aggregate` (`A` and two symmetric 3×3 matrices),
so an E1 leaf needs one certified aggregate and 32 exact rational evaluations
(`leafCheck`). Aggregates are certified by computation (`Proposal.check`): the
tangents come from the fixed-point kernel evaluator of `BccSharp.Lattice.FixedLocal`
at proposed rational anchors. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.TangentE1
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.CompactCover

/-! ## Certified tangents -/

/-- A line `intercept - penalty q` below the kernel term `kernelValue kind (π q)`
for every `q > 0`. -/
def ValidTangent (kind : KernelKind) (t : Stage2.Tangent) : Prop :=
  0 ≤ t.penalty ∧ ∀ q : ℝ, 0 < q →
    (t.intercept : ℝ) - (t.penalty : ℝ) * q ≤ kernelValue kind (Real.pi * q)

theorem proposeKernel_kind (kind : KernelKind) (t : Ball) :
    (FixedLocal.proposeKernel kind t).kind = kind := by
  cases kind <;> rfl

/-- A ball containing `π x`, rounded outward to the `2^-64` grid. -/
def piBall (x : ℚ) : Ball := FixedLocal.roundOut (Constants.piInput.mul (Ball.exact x))

/-- The tangent of `q ↦ kernelValue kind (π q)` at the anchor `q = x`, with a
directed intercept and an upward-rounded penalty, from the fast kernel
evaluator. -/
def fastTangent (kind : KernelKind) (x : ℚ) : Option Stage2.Tangent :=
  let b := piBall x
  let w := FixedLocal.proposeKernel kind b
  if decide (0 < x) && w.check b then
    let k := FixedLocal.fastEvaluate w b
    let s := Constants.piInput.mul k.slope.neg
    some ⟨Stage2.lower96 (k.value.lo + s.lo * x), Stage2.upper96 (max 0 s.hi)⟩
  else none

theorem fastTangent_sound (kind : KernelKind) (x : ℚ) (r : Stage2.Tangent)
    (ok : fastTangent kind x = some r) : ValidTangent kind r := by
  unfold fastTangent at ok
  dsimp only at ok
  split_ifs at ok with h
  obtain ⟨positive, arithmetic⟩ := Bool.and_eq_true_iff.mp h
  have xPosQ : 0 < x := of_decide_eq_true positive
  have xPos : (0 : ℝ) < x := by exact_mod_cast xPosQ
  have input : (piBall x).Contains (Real.pi * (x : ℝ)) :=
    FixedLocal.roundOut_contains (Ball.contains_mul Constants.piInput_sound (Ball.contains_exact x))
  have e := FixedLocal.fastEvaluate_sound _ input arithmetic
  rw [proposeKernel_kind] at e
  have es := Ball.contains_mul Constants.piInput_sound (Ball.contains_neg e.2.1)
  have ev := DirectRoute.endpoints e.1
  have es' := DirectRoute.endpoints es
  rw [← Option.some.inj ok]
  refine ⟨(le_max_left (0 : ℚ) _).trans (Stage2.le_upper96 _), ?_⟩
  intro q qPos
  have lo := (Rat.cast_le (K := ℝ)).mpr (Stage2.lower96_le
    ((FixedLocal.fastEvaluate (FixedLocal.proposeKernel kind (piBall x)) (piBall x)).value.lo +
      (Constants.piInput.mul (FixedLocal.fastEvaluate (FixedLocal.proposeKernel kind (piBall x))
        (piBall x)).slope.neg).lo * x))
  have pen := (Rat.cast_le (K := ℝ)).mpr ((le_max_right (0 : ℚ) _).trans (Stage2.le_upper96
    (max 0 (Constants.piInput.mul (FixedLocal.fastEvaluate (FixedLocal.proposeKernel kind (piBall x))
      (piBall x)).slope.neg).hi)))
  push_cast at lo pen
  have anchor := Stage2.globalTangent kind (mul_pos Real.pi_pos xPos) (mul_pos Real.pi_pos qPos)
  have m1 := mul_le_mul_of_nonneg_right es'.1 xPos.le
  have m2 := mul_le_mul_of_nonneg_right (es'.2.trans pen) qPos.le
  dsimp only
  linarith [ev.1, m1, m2, anchor, lo]

/-! ## Squared lengths and the series terms -/

/-- The squared dual length `|B^{-T} n|^2` in chart coordinates. -/
def dualLength (p : Point) (n : IntVec) : ℝ :=
  ((p 0)⁻¹ * (n 0 : ℝ))^2 + ((p 1)⁻¹ * ((n 1 : ℝ) - p 2 * (n 0 : ℝ)))^2 +
    ((p 0 * p 1) * ((n 2 : ℝ) - p 3 * (n 0 : ℝ) + p 4 * (p 2 * (n 0 : ℝ) - (n 1 : ℝ))))^2

theorem dualLength_eq (p : Point) (n : IntVec) : dualLength p n = sq (dualVector p n) := by
  simp [dualLength, sq, dualVector, Fin.sum_univ_three]

private theorem sq_pos' {v : Vec} (hv : v ≠ 0) : 0 < sq v :=
  lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hv))

theorem series_terms (p : Point) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (n : IntVec) (hn : n ≠ 0) :
    0 < firstLength p n ∧
      shortKernel (normalizedChart p) n = kernelValue .half (Real.pi * firstLength p n) ∧
    0 < dualLength p n ∧
      dualKernel (normalizedChart p) n = kernelValue .one (Real.pi * dualLength p n) := by
  set R := normalizedChart p with hR
  have hd : R.det ≠ 0 := by rw [hR, normalizedChart_det p h0 h1]; exact one_ne_zero
  have hi : linearImage R n ≠ 0 := by
    intro hz
    apply hn
    apply (periodIndices R hd).injective
    apply Subtype.ext
    change linearImage R n = linearImage R 0
    rw [hz, linearImage, castVec_zero, Matrix.mulVec_zero]
  have hc : cycleFrequency R n ≠ 0 := fun z =>
    hn (cycleFrequency_injective R hd (z.trans (cycleFrequency_zero R).symm))
  have fl : firstLength p n = sq (linearImage R n) := firstLength_eq p n
  have dl : dualLength p n = sq (cycleFrequency R n) := by
    rw [dualLength_eq, dualVector_eq p h0 h1]
  refine ⟨fl ▸ sq_pos' hi, ?_, dl ▸ sq_pos' hc, ?_⟩
  · rw [shortKernel_eq R hd n hn, fl]
    norm_num [kernelValue, KernelKind.power]
  · rw [dualKernel_eq R hd n hn, dl]
    norm_num [kernelValue, KernelKind.power]

/-! ## Term sets and their lower bound -/

abbrev Term := IntVec × Stage2.Tangent

structure TermSet where
  dir : List Term
  dual : List Term

def TermSet.Valid (s : TermSet) : Prop :=
  (s.dir.map Prod.fst).Nodup ∧ (s.dual.map Prod.fst).Nodup ∧
    (∀ x ∈ s.dir, x.1 ≠ 0 ∧ ValidTangent .half x.2) ∧
    (∀ x ∈ s.dual, x.1 ≠ 0 ∧ ValidTangent .one x.2)

def TermSet.lower (s : TermSet) (p : Point) : ℝ :=
  (s.dir.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) * firstLength p x.1).sum +
    (s.dual.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) * dualLength p x.1).sum

theorem TermSet.lower_le (s : TermSet) (hs : s.Valid) (p : Point) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    s.lower p ≤ positiveSeries (normalizedChart p) := by
  classical
  obtain ⟨nd, nu, vd, vu⟩ := hs
  set R := normalizedChart p with hR
  have hd : R.det ≠ 0 := by rw [hR, normalizedChart_det p h0 h1]; exact one_ne_zero
  have shortSum : (s.dir.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) * firstLength p x.1).sum ≤
      ∑' n, shortKernel R n := by
    calc _ ≤ (s.dir.map fun x => shortKernel R x.1).sum := by
          apply List.sum_le_sum
          intro x hx
          obtain ⟨hn, hv⟩ := vd x hx
          obtain ⟨hq, he, -, -⟩ := series_terms p h0 h1 x.1 hn
          rw [he]
          exact hv.2 _ hq
      _ = ∑ n ∈ (s.dir.map Prod.fst).toFinset, shortKernel R n := by
          rw [List.sum_toFinset _ nd, List.map_map]
          rfl
      _ ≤ ∑' n, shortKernel R n :=
          (shortKernel_summable R hd).sum_le_tsum _ (fun n _ => shortKernel_nonnegative R n)
  have dualSum : (s.dual.map fun x => (x.2.intercept : ℝ) - (x.2.penalty : ℝ) * dualLength p x.1).sum ≤
      ∑' n, dualKernel R n := by
    calc _ ≤ (s.dual.map fun x => dualKernel R x.1).sum := by
          apply List.sum_le_sum
          intro x hx
          obtain ⟨hn, hv⟩ := vu x hx
          obtain ⟨-, -, hq, he⟩ := series_terms p h0 h1 x.1 hn
          rw [he]
          exact hv.2 _ hq
      _ = ∑ n ∈ (s.dual.map Prod.fst).toFinset, dualKernel R n := by
          rw [List.sum_toFinset _ nu, List.map_map]
          rfl
      _ ≤ ∑' n, dualKernel R n :=
          (dualKernel_summable R hd).sum_le_tsum _ (fun n _ => dualKernel_nonnegative R n)
  unfold TermSet.lower positiveSeries
  exact add_le_add shortSum dualSum

/-! ## Aggregates -/

/-- `A`, the direct penalty matrix `P = Σ c n nᵀ` and the dual one `D`. -/
structure Aggregate where
  a : ℚ
  p00 : ℚ
  p01 : ℚ
  p02 : ℚ
  p11 : ℚ
  p12 : ℚ
  p22 : ℚ
  d00 : ℚ
  d01 : ℚ
  d02 : ℚ
  d11 : ℚ
  d12 : ℚ
  d22 : ℚ
  deriving DecidableEq, Repr

def Aggregate.zero : Aggregate := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def Aggregate.addDir (g : Aggregate) (x : Term) : Aggregate :=
  let c := x.2.penalty
  let a0 : ℚ := x.1 0
  let a1 : ℚ := x.1 1
  let a2 : ℚ := x.1 2
  ⟨g.a + x.2.intercept, g.p00 + c * (a0 * a0), g.p01 + c * (a0 * a1), g.p02 + c * (a0 * a2),
    g.p11 + c * (a1 * a1), g.p12 + c * (a1 * a2), g.p22 + c * (a2 * a2),
    g.d00, g.d01, g.d02, g.d11, g.d12, g.d22⟩

def Aggregate.addDual (g : Aggregate) (x : Term) : Aggregate :=
  let c := x.2.penalty
  let a0 : ℚ := x.1 0
  let a1 : ℚ := x.1 1
  let a2 : ℚ := x.1 2
  ⟨g.a + x.2.intercept, g.p00, g.p01, g.p02, g.p11, g.p12, g.p22,
    g.d00 + c * (a0 * a0), g.d01 + c * (a0 * a1), g.d02 + c * (a0 * a2),
    g.d11 + c * (a1 * a1), g.d12 + c * (a1 * a2), g.d22 + c * (a2 * a2)⟩

def TermSet.aggregate (s : TermSet) : Aggregate :=
  s.dual.foldl Aggregate.addDual (s.dir.foldl Aggregate.addDir Aggregate.zero)

/-- `Σ c |B n|^2 + Σ c |B^{-T} n|^2` written through the two matrices. -/
def Aggregate.F (g : Aggregate) (p : Point) : ℝ :=
  (p 0)^2 * ((g.p00 : ℝ) + 2 * p 2 * g.p01 + 2 * p 3 * g.p02 + (p 2)^2 * g.p11 +
      2 * (p 2 * p 3) * g.p12 + (p 3)^2 * g.p22) +
    (p 1)^2 * ((g.p11 : ℝ) + 2 * p 4 * g.p12 + (p 4)^2 * g.p22) +
    ((p 0 * p 1)⁻¹)^2 * (g.p22 : ℝ) +
    ((p 0)⁻¹)^2 * (g.d00 : ℝ) +
    ((p 1)⁻¹)^2 * ((g.d11 : ℝ) - 2 * p 2 * g.d01 + (p 2)^2 * g.d00) +
    (p 0 * p 1)^2 * ((p 4 * p 2 - p 3)^2 * g.d00 + (p 4)^2 * g.d11 + g.d22 -
      2 * ((p 4 * p 2 - p 3) * p 4) * g.d01 + 2 * (p 4 * p 2 - p 3) * g.d02 - 2 * p 4 * g.d12)

def Aggregate.FQ (g : Aggregate) (p : Fin 5 → ℚ) : ℚ :=
  (p 0)^2 * (g.p00 + 2 * p 2 * g.p01 + 2 * p 3 * g.p02 + (p 2)^2 * g.p11 +
      2 * (p 2 * p 3) * g.p12 + (p 3)^2 * g.p22) +
    (p 1)^2 * (g.p11 + 2 * p 4 * g.p12 + (p 4)^2 * g.p22) +
    ((p 0 * p 1)⁻¹)^2 * g.p22 +
    ((p 0)⁻¹)^2 * g.d00 +
    ((p 1)⁻¹)^2 * (g.d11 - 2 * p 2 * g.d01 + (p 2)^2 * g.d00) +
    (p 0 * p 1)^2 * ((p 4 * p 2 - p 3)^2 * g.d00 + (p 4)^2 * g.d11 + g.d22 -
      2 * ((p 4 * p 2 - p 3) * p 4) * g.d01 + 2 * (p 4 * p 2 - p 3) * g.d02 - 2 * p 4 * g.d12)

theorem Aggregate.FQ_cast (g : Aggregate) (p : Fin 5 → ℚ) :
    ((g.FQ p : ℚ) : ℝ) = g.F (fun i => (p i : ℝ)) := by
  simp only [Aggregate.FQ, Aggregate.F]
  push_cast
  ring

theorem Aggregate.addDir_F (g : Aggregate) (x : Term) (p : Point) :
    (g.addDir x).F p = g.F p + (x.2.penalty : ℝ) * firstLength p x.1 := by
  simp only [Aggregate.addDir, Aggregate.F, firstLength]
  push_cast
  ring

theorem Aggregate.addDual_F (g : Aggregate) (x : Term) (p : Point) :
    (g.addDual x).F p = g.F p + (x.2.penalty : ℝ) * dualLength p x.1 := by
  simp only [Aggregate.addDual, Aggregate.F, dualLength]
  push_cast
  ring

theorem Aggregate.zero_F (p : Point) : Aggregate.zero.F p = 0 := by
  simp [Aggregate.zero, Aggregate.F]

theorem foldl_addDir (l : List Term) (g : Aggregate) (p : Point) :
    (l.foldl Aggregate.addDir g).F p = g.F p + (l.map fun x => (x.2.penalty : ℝ) * firstLength p x.1).sum ∧
    ((l.foldl Aggregate.addDir g).a : ℝ) = g.a + (l.map fun x => (x.2.intercept : ℝ)).sum := by
  induction l generalizing g with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hF, ha⟩ := ih (g.addDir x)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    refine ⟨?_, ?_⟩
    · rw [hF, Aggregate.addDir_F]
      ring
    · rw [ha]
      simp only [Aggregate.addDir]
      push_cast
      ring

theorem foldl_addDual (l : List Term) (g : Aggregate) (p : Point) :
    (l.foldl Aggregate.addDual g).F p = g.F p + (l.map fun x => (x.2.penalty : ℝ) * dualLength p x.1).sum ∧
    ((l.foldl Aggregate.addDual g).a : ℝ) = g.a + (l.map fun x => (x.2.intercept : ℝ)).sum := by
  induction l generalizing g with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hF, ha⟩ := ih (g.addDual x)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    refine ⟨?_, ?_⟩
    · rw [hF, Aggregate.addDual_F]
      ring
    · rw [ha]
      simp only [Aggregate.addDual]
      push_cast
      ring

/-- The penalty part of a term set. -/
def TermSet.F (s : TermSet) (p : Point) : ℝ :=
  (s.dir.map fun x => (x.2.penalty : ℝ) * firstLength p x.1).sum +
    (s.dual.map fun x => (x.2.penalty : ℝ) * dualLength p x.1).sum

theorem TermSet.aggregate_F (s : TermSet) (p : Point) : s.aggregate.F p = s.F p := by
  unfold TermSet.aggregate TermSet.F
  rw [(foldl_addDual _ _ p).1, (foldl_addDir _ _ p).1, Aggregate.zero_F, zero_add]

private theorem list_sum_map_sub {ι : Type} (l : List ι) (f g : ι → ℝ) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem TermSet.aggregate_lower (s : TermSet) (p : Point) :
    (s.aggregate.a : ℝ) - s.F p = s.lower p := by
  unfold TermSet.aggregate TermSet.F TermSet.lower
  rw [(foldl_addDual _ _ p).2, (foldl_addDir _ _ p).2]
  rw [list_sum_map_sub s.dir (fun x => (x.2.intercept : ℝ)) (fun x => (x.2.penalty : ℝ) * firstLength p x.1),
    list_sum_map_sub s.dual (fun x => (x.2.intercept : ℝ)) (fun x => (x.2.penalty : ℝ) * dualLength p x.1)]
  simp only [Aggregate.zero, Rat.cast_zero, zero_add]
  ring

/-! ## Convexity in each coordinate -/

theorem convexOn_sq_affine (s : Set ℝ) (hs : Convex ℝ s) (a b : ℝ) :
    ConvexOn ℝ s (fun t => (a * t + b)^2) := by
  refine ⟨hs, fun x _ y _ u v hu hv huv => ?_⟩
  simp only [smul_eq_mul]
  have e : a * (u * x + v * y) + b = u * (a * x + b) + v * (a * y + b) := by
    linear_combination (-b) * huv
  rw [e]
  have hv' : v = 1 - u := by linarith
  subst hv'
  nlinarith [mul_nonneg (mul_nonneg hu hv) (sq_nonneg ((a * x + b) - (a * y + b)))]

theorem convexOn_const_mul {s : Set ℝ} {f : ℝ → ℝ} (c : ℝ) (hc : 0 ≤ c) (hf : ConvexOn ℝ s f) :
    ConvexOn ℝ s (fun t => c * f t) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  nlinarith [mul_le_mul_of_nonneg_left h hc]

theorem convexOn_add' {s : Set ℝ} {f g : ℝ → ℝ} (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (fun t => f t + g t) :=
  hf.add hg

theorem convexOn_sq_inv (c : ℝ) : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ => (c * t⁻¹)^2) := by
  have h : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun t : ℝ => t ^ (-2 : ℤ)) := convexOn_zpow (-2)
  refine (convexOn_const_mul (c^2) (sq_nonneg c) h).congr ?_
  intro t _
  simp only
  rw [zpow_neg, zpow_ofNat, mul_pow, inv_pow]

/-- `(a₁t+b₁)² + (a₂t+b₂)² + (a₃t+b₃)² + (c/t)²`. -/
def shape (a1 b1 a2 b2 a3 b3 c : ℝ) (t : ℝ) : ℝ :=
  (a1 * t + b1)^2 + (a2 * t + b2)^2 + (a3 * t + b3)^2 + (c * t⁻¹)^2

theorem shape_convex (a1 b1 a2 b2 a3 b3 c lo hi : ℝ) (h : 0 < lo ∨ c = 0) :
    ConvexOn ℝ (Set.Icc lo hi) (shape a1 b1 a2 b2 a3 b3 c) := by
  have hs : Convex ℝ (Set.Icc lo hi) := convex_Icc lo hi
  have inv : ConvexOn ℝ (Set.Icc lo hi) (fun t : ℝ => (c * t⁻¹)^2) := by
    rcases h with h | h
    · exact (convexOn_sq_inv c).subset (fun t ht => lt_of_lt_of_le h ht.1) hs
    · subst h
      simpa using convexOn_const (0 : ℝ) hs
  exact convexOn_add' (convexOn_add' (convexOn_add' (convexOn_sq_affine _ hs a1 b1)
    (convexOn_sq_affine _ hs a2 b2)) (convexOn_sq_affine _ hs a3 b3)) inv

theorem firstLength_shape (p : Point) (m : IntVec) (i : Fin 5) :
    ∃ a1 b1 a2 b2 a3 b3 c : ℝ, (2 ≤ i.val → c = 0) ∧
      ∀ t, firstLength (Function.update p i t) m = shape a1 b1 a2 b2 a3 b3 c t := by
  fin_cases i
  · exact ⟨(m 0 : ℝ) + p 2 * m 1 + p 3 * m 2, 0, 0, p 1 * ((m 1 : ℝ) + p 4 * m 2), 0, 0,
      (p 1)⁻¹ * m 2, by simp, fun t => by simp [firstLength, shape, Function.update]; ring⟩
  · exact ⟨0, p 0 * ((m 0 : ℝ) + p 2 * m 1 + p 3 * m 2), (m 1 : ℝ) + p 4 * m 2, 0, 0, 0,
      (p 0)⁻¹ * m 2, by simp, fun t => by simp [firstLength, shape, Function.update]; ring⟩
  · exact ⟨p 0 * m 1, p 0 * ((m 0 : ℝ) + p 3 * m 2), 0, p 1 * ((m 1 : ℝ) + p 4 * m 2), 0,
      (p 0 * p 1)⁻¹ * m 2, 0, by simp, fun t => by simp [firstLength, shape, Function.update]; ring⟩
  · exact ⟨p 0 * m 2, p 0 * ((m 0 : ℝ) + p 2 * m 1), 0, p 1 * ((m 1 : ℝ) + p 4 * m 2), 0,
      (p 0 * p 1)⁻¹ * m 2, 0, by simp, fun t => by simp [firstLength, shape, Function.update]; ring⟩
  · exact ⟨0, p 0 * ((m 0 : ℝ) + p 2 * m 1 + p 3 * m 2), p 1 * m 2, p 1 * m 1, 0,
      (p 0 * p 1)⁻¹ * m 2, 0, by simp, fun t => by simp [firstLength, shape, Function.update]; ring⟩

theorem dualLength_shape (p : Point) (n : IntVec) (i : Fin 5) :
    ∃ a1 b1 a2 b2 a3 b3 c : ℝ, (2 ≤ i.val → c = 0) ∧
      ∀ t, dualLength (Function.update p i t) n = shape a1 b1 a2 b2 a3 b3 c t := by
  fin_cases i
  · exact ⟨0, (p 1)⁻¹ * ((n 1 : ℝ) - p 2 * n 0),
      p 1 * ((n 2 : ℝ) - p 3 * n 0 + p 4 * (p 2 * n 0 - n 1)), 0, 0, 0, (n 0 : ℝ),
      by simp, fun t => by simp [dualLength, shape, Function.update]; ring⟩
  · exact ⟨0, (p 0)⁻¹ * n 0, p 0 * ((n 2 : ℝ) - p 3 * n 0 + p 4 * (p 2 * n 0 - n 1)), 0, 0, 0,
      (n 1 : ℝ) - p 2 * n 0, by simp, fun t => by simp [dualLength, shape, Function.update]; ring⟩
  · exact ⟨-((p 1)⁻¹ * n 0), (p 1)⁻¹ * n 1, p 0 * p 1 * p 4 * n 0,
      p 0 * p 1 * ((n 2 : ℝ) - p 3 * n 0 - p 4 * n 1), 0, (p 0)⁻¹ * n 0, 0,
      by simp, fun t => by simp [dualLength, shape, Function.update]; ring⟩
  · exact ⟨0, (p 0)⁻¹ * n 0, -(p 0 * p 1 * n 0),
      p 0 * p 1 * ((n 2 : ℝ) + p 4 * (p 2 * n 0 - n 1)), 0, (p 1)⁻¹ * ((n 1 : ℝ) - p 2 * n 0), 0,
      by simp, fun t => by simp [dualLength, shape, Function.update]; ring⟩
  · exact ⟨0, (p 0)⁻¹ * n 0, p 0 * p 1 * (p 2 * n 0 - n 1), p 0 * p 1 * ((n 2 : ℝ) - p 3 * n 0), 0,
      (p 1)⁻¹ * ((n 1 : ℝ) - p 2 * n 0), 0,
      by simp, fun t => by simp [dualLength, shape, Function.update]; ring⟩

private theorem shape_side (b : Rectangle) (pos : 0 < (b.lo 0 : ℝ) ∧ 0 < (b.lo 1 : ℝ)) (i : Fin 5)
    (c : ℝ) (hc : 2 ≤ i.val → c = 0) : 0 < (b.lo i : ℝ) ∨ c = 0 := by
  fin_cases i
  · exact Or.inl pos.1
  · exact Or.inl pos.2
  all_goals exact Or.inr (hc (by decide))

theorem firstLength_convex (b : Rectangle) (pos : 0 < (b.lo 0 : ℝ) ∧ 0 < (b.lo 1 : ℝ))
    (p : Point) (m : IntVec) (i : Fin 5) :
    ConvexOn ℝ (Set.Icc (b.lo i : ℝ) (b.hi i)) (fun t => firstLength (Function.update p i t) m) := by
  obtain ⟨a1, b1, a2, b2, a3, b3, c, hc, he⟩ := firstLength_shape p m i
  rw [show (fun t => firstLength (Function.update p i t) m) = shape a1 b1 a2 b2 a3 b3 c from funext he]
  exact shape_convex _ _ _ _ _ _ _ _ _ (shape_side b pos i c hc)

theorem dualLength_convex (b : Rectangle) (pos : 0 < (b.lo 0 : ℝ) ∧ 0 < (b.lo 1 : ℝ))
    (p : Point) (n : IntVec) (i : Fin 5) :
    ConvexOn ℝ (Set.Icc (b.lo i : ℝ) (b.hi i)) (fun t => dualLength (Function.update p i t) n) := by
  obtain ⟨a1, b1, a2, b2, a3, b3, c, hc, he⟩ := dualLength_shape p n i
  rw [show (fun t => dualLength (Function.update p i t) n) = shape a1 b1 a2 b2 a3 b3 c from funext he]
  exact shape_convex _ _ _ _ _ _ _ _ _ (shape_side b pos i c hc)

theorem convexOn_list_sum {ι : Type} (s : Set ℝ) (hs : Convex ℝ s) (l : List ι) (w : ι → ℝ)
    (f : ι → ℝ → ℝ) (hw : ∀ x ∈ l, 0 ≤ w x) (hf : ∀ x ∈ l, ConvexOn ℝ s (f x)) :
    ConvexOn ℝ s (fun t => (l.map fun x => w x * f x t).sum) := by
  induction l with
  | nil => simpa using convexOn_const (0 : ℝ) hs
  | cons x l ih =>
    have h := convexOn_add' (convexOn_const_mul (w x) (hw x (by simp)) (hf x (by simp)))
      (ih (fun y hy => hw y (by simp [hy])) (fun y hy => hf y (by simp [hy])))
    simpa only [List.map_cons, List.sum_cons] using h

theorem TermSet.F_convex (s : TermSet) (hs : s.Valid) (b : Rectangle)
    (pos : 0 < (b.lo 0 : ℝ) ∧ 0 < (b.lo 1 : ℝ)) (p : Point) (i : Fin 5) :
    ConvexOn ℝ (Set.Icc (b.lo i : ℝ) (b.hi i)) (fun t => s.F (Function.update p i t)) := by
  have hc : Convex ℝ (Set.Icc (b.lo i : ℝ) (b.hi i)) := convex_Icc _ _
  have hd := convexOn_list_sum _ hc s.dir (fun x => (x.2.penalty : ℝ))
    (fun x t => firstLength (Function.update p i t) x.1)
    (fun x hx => by exact_mod_cast (hs.2.2.1 x hx).2.1)
    (fun x _ => firstLength_convex b pos p x.1 i)
  have hu := convexOn_list_sum _ hc s.dual (fun x => (x.2.penalty : ℝ))
    (fun x t => dualLength (Function.update p i t) x.1)
    (fun x hx => by exact_mod_cast (hs.2.2.2 x hx).2.1)
    (fun x _ => dualLength_convex b pos p x.1 i)
  exact convexOn_add' hd hu

/-! ## The maximum over a box is attained at a corner -/

def corner (b : Rectangle) (c : Fin 5 → Bool) : Point :=
  fun i => if c i then (b.hi i : ℝ) else (b.lo i : ℝ)

theorem corner_max (b : Rectangle) (f : Point → ℝ)
    (cvx : ∀ i : Fin 5, ∀ p, b.Mem p →
      ConvexOn ℝ (Set.Icc (b.lo i : ℝ) (b.hi i)) (fun t => f (Function.update p i t)))
    (p : Point) (hp : b.Mem p) : ∃ c : Fin 5 → Bool, f p ≤ f (corner b c) := by
  classical
  let mix (c : Fin 5 → Bool) (k : ℕ) : Point := fun i => if i.val < k then corner b c i else p i
  have side (i : Fin 5) : (b.lo i : ℝ) ≤ b.hi i := (hp i).1.trans (hp i).2
  have mem (c : Fin 5 → Bool) (k : ℕ) : b.Mem (mix c k) := by
    intro i
    simp only [mix, corner]
    split_ifs
    · exact ⟨side i, le_rfl⟩
    · exact ⟨le_rfl, side i⟩
    · exact hp i
  have step : ∀ k ≤ 5, ∃ c, f p ≤ f (mix c k) := by
    intro k hk
    induction k with
    | zero => exact ⟨fun _ => false, le_of_eq (by congr 1)⟩
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih (by omega)
      let i : Fin 5 := ⟨k, by omega⟩
      have hq := mem c k
      have seg : mix c k i ∈ _root_.segment ℝ (b.lo i : ℝ) (b.hi i) := by
        rw [_root_.segment_eq_Icc (side i)]
        exact hq i
      have h := (cvx i (mix c k) hq).le_on_segment (Set.left_mem_Icc.mpr (side i))
        (Set.right_mem_Icc.mpr (side i)) seg
      rw [Function.update_eq_self] at h
      have upd (v : Bool) : Function.update (mix c k) i (corner b (Function.update c i v) i) =
          mix (Function.update c i v) (k + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [mix, i]
        · have hjk : j.val ≠ k := fun e => hj (Fin.ext e)
          simp only [Function.update_of_ne hj, mix, corner]
          by_cases hlt : j.val < k
          · have : j.val < k + 1 := by omega
            simp [hlt, this]
          · have : ¬ j.val < k + 1 := by omega
            simp [hlt, this]
      by_cases hb : f (Function.update (mix c k) i (b.lo i)) ≤ f (Function.update (mix c k) i (b.hi i))
      · refine ⟨Function.update c i true, hc.trans (h.trans ?_)⟩
        rw [max_eq_right hb, ← upd true]
        simp [corner]
      · refine ⟨Function.update c i false, hc.trans (h.trans ?_)⟩
        rw [max_eq_left (le_of_not_ge hb), ← upd false]
        simp [corner]
  obtain ⟨c, hc⟩ := step 5 le_rfl
  refine ⟨c, hc.trans (le_of_eq ?_)⟩
  congr 1
  funext i
  simp [mix, i.isLt]

/-! ## The E1 leaf check -/

def cornerQ (b : Rectangle) (c : Fin 5 → Bool) : Fin 5 → ℚ :=
  fun i => if c i then b.hi i else b.lo i

theorem cornerQ_cast (b : Rectangle) (c : Fin 5 → Bool) :
    (fun i => ((cornerQ b c i : ℚ) : ℝ)) = corner b c := by
  funext i
  simp only [cornerQ, corner]
  split_ifs <;> rfl

def allCorners (f : (Fin 5 → Bool) → Bool) : Bool :=
  [false, true].all fun c0 => [false, true].all fun c1 => [false, true].all fun c2 =>
    [false, true].all fun c3 => [false, true].all fun c4 => f ![c0, c1, c2, c3, c4]

theorem allCorners_sound (f : (Fin 5 → Bool) → Bool) (h : allCorners f = true)
    (c : Fin 5 → Bool) : f c = true := by
  have e : c = ![c 0, c 1, c 2, c 3, c 4] := by
    funext i
    fin_cases i <;> rfl
  rw [e]
  have mem (x : Bool) : x ∈ [false, true] := by cases x <;> simp
  simp only [allCorners, List.all_eq_true] at h
  exact h _ (mem _) _ (mem _) _ (mem _) _ (mem _) _ (mem _)

/-- An aggregate of a valid term set. -/
def Certified (g : Aggregate) : Prop := ∃ s : TermSet, s.Valid ∧ s.aggregate = g

def leafCheck (g : Aggregate) (b : Rectangle) : Bool :=
  decide (0 < b.lo 0 ∧ 0 < b.lo 1) &&
    allCorners fun c => decide (HfccUpper < g.a - g.FQ (cornerQ b c))

theorem leafCheck_sound (g : Aggregate) (hg : Certified g) (b : Rectangle)
    (ok : leafCheck g b = true) (p : Point) (hp : b.Mem p) : Sharp (primitiveChart p) := by
  obtain ⟨s, hs, rfl⟩ := hg
  have h := Bool.and_eq_true_iff.mp ok
  have pos : 0 < b.lo 0 ∧ 0 < b.lo 1 := of_decide_eq_true h.1
  have pos' : 0 < (b.lo 0 : ℝ) ∧ 0 < (b.lo 1 : ℝ) :=
    ⟨by exact_mod_cast pos.1, by exact_mod_cast pos.2⟩
  have h0 : 0 < p 0 := pos'.1.trans_le (hp 0).1
  have h1 : 0 < p 1 := pos'.2.trans_le (hp 1).1
  obtain ⟨c, hc⟩ := corner_max b s.F (fun i q _ => s.F_convex hs b pos' q i) p hp
  have hcorner : HfccUpper < s.aggregate.a - s.aggregate.FQ (cornerQ b c) :=
    of_decide_eq_true (allCorners_sound _ h.2 c)
  have cast : (((s.aggregate.a - s.aggregate.FQ (cornerQ b c) : ℚ)) : ℝ) =
      s.aggregate.a - s.F (corner b c) := by
    rw [Rat.cast_sub, Aggregate.FQ_cast, cornerQ_cast, TermSet.aggregate_F]
  have hcR := (Rat.cast_lt (K := ℝ)).mpr hcorner
  rw [cast] at hcR
  have lower : (HfccUpper : ℝ) < s.lower p := by
    rw [← TermSet.aggregate_lower]
    linarith
  exact chart_above_fcc_of_series p h0.ne' h1.ne' (lower.trans_le (s.lower_le hs p h0.ne' h1.ne'))

/-! ## Certifying an aggregate by computation -/

def tangentsFor (kind : KernelKind) : List (IntVec × ℚ) → Option (List Term)
  | [] => some []
  | x :: rest =>
    match fastTangent kind x.2, tangentsFor kind rest with
    | some t, some ts => some ((x.1, t) :: ts)
    | _, _ => none

theorem tangentsFor_sound (kind : KernelKind) (l : List (IntVec × ℚ)) (ts : List Term)
    (h : tangentsFor kind l = some ts) :
    ts.map Prod.fst = l.map Prod.fst ∧ ∀ x ∈ ts, ValidTangent kind x.2 := by
  induction l generalizing ts with
  | nil =>
    simp only [tangentsFor, Option.some.injEq] at h
    subst h
    simp
  | cons x rest ih =>
    simp only [tangentsFor] at h
    split at h
    next t ts' ht hts =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨e, v⟩ := ih ts' hts
      refine ⟨by simp [e], ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fastTangent_sound kind x.2 t ht
      · exact v y hy
    next => contradiction

def lexLt (a b : IntVec) : Bool :=
  decide (a 0 < b 0) || (decide (a 0 = b 0) && (decide (a 1 < b 1) || (decide (a 1 = b 1) && decide (a 2 < b 2))))

theorem lexLt_iff (a b : IntVec) : lexLt a b = true ↔
    (a 0 < b 0 ∨ (a 0 = b 0 ∧ (a 1 < b 1 ∨ (a 1 = b 1 ∧ a 2 < b 2)))) := by
  simp [lexLt]

theorem lexLt_trans {a b c : IntVec} (h1 : lexLt a b = true) (h2 : lexLt b c = true) : lexLt a c = true := by
  rw [lexLt_iff] at *
  omega

theorem lexLt_irrefl (a : IntVec) : lexLt a a = false := by
  have h : ¬ (lexLt a a = true) := by rw [lexLt_iff]; omega
  simpa using h

def sortedStrict : List IntVec → Bool
  | a :: b :: rest => lexLt a b && sortedStrict (b :: rest)
  | _ => true

theorem sortedStrict_below (a : IntVec) (l : List IntVec) (h : sortedStrict (a :: l) = true) :
    ∀ x ∈ l, lexLt a x = true := by
  induction l generalizing a with
  | nil => simp
  | cons b rest ih =>
    have hs := Bool.and_eq_true_iff.mp h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs.1
    · exact lexLt_trans hs.1 (ih b hs.2 x hx)

theorem sortedStrict_nodup (l : List IntVec) (h : sortedStrict l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    refine List.nodup_cons.mpr ⟨fun ha => ?_, ih ?_⟩
    · have := sortedStrict_below a rest h a ha
      rw [lexLt_irrefl] at this
      contradiction
    · cases rest with
      | nil => rfl
      | cons b rest => exact (Bool.and_eq_true_iff.mp h).2

def nonzeroB (n : IntVec) : Bool := !(decide (n 0 = 0) && decide (n 1 = 0) && decide (n 2 = 0))

theorem nonzeroB_sound (n : IntVec) (h : nonzeroB n = true) : n ≠ 0 := by
  intro hz
  subst hz
  simp [nonzeroB] at h

/-- Proposed indices with anchors; the tangents are computed and checked here. -/
structure Proposal where
  dir : List (IntVec × ℚ)
  dual : List (IntVec × ℚ)

def Proposal.check (pr : Proposal) (g : Aggregate) : Bool :=
  ((sortedStrict (pr.dir.map Prod.fst) && sortedStrict (pr.dual.map Prod.fst)) &&
    ((pr.dir.all fun x => nonzeroB x.1) && (pr.dual.all fun x => nonzeroB x.1))) &&
  match tangentsFor .half pr.dir, tangentsFor .one pr.dual with
  | some d, some u => decide ((TermSet.mk d u).aggregate = g)
  | _, _ => false

theorem Proposal.check_sound (pr : Proposal) (g : Aggregate) (ok : pr.check g = true) :
    Certified g := by
  unfold Proposal.check at ok
  obtain ⟨hstruct, hagg⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hsort, hnz⟩ := Bool.and_eq_true_iff.mp hstruct
  obtain ⟨sd, su⟩ := Bool.and_eq_true_iff.mp hsort
  obtain ⟨zd, zu⟩ := Bool.and_eq_true_iff.mp hnz
  split at hagg
  next d u hd hu =>
    obtain ⟨ed, vd⟩ := tangentsFor_sound .half pr.dir d hd
    obtain ⟨eu, vu⟩ := tangentsFor_sound .one pr.dual u hu
    refine ⟨⟨d, u⟩, ⟨?_, ?_, ?_, ?_⟩, of_decide_eq_true hagg⟩
    · rw [ed]; exact sortedStrict_nodup _ sd
    · rw [eu]; exact sortedStrict_nodup _ su
    · intro x hx
      refine ⟨?_, vd x hx⟩
      have hmem : x.1 ∈ pr.dir.map Prod.fst := ed ▸ List.mem_map_of_mem hx
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
      rw [← hyx]
      exact nonzeroB_sound _ (List.all_eq_true.mp zd y hy)
    · intro x hx
      refine ⟨?_, vu x hx⟩
      have hmem : x.1 ∈ pr.dual.map Prod.fst := eu ▸ List.mem_map_of_mem hx
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
      rw [← hyx]
      exact nonzeroB_sound _ (List.all_eq_true.mp zu y hy)
  next => contradiction

end BccSharp.Coulomb.BravaisCover.TangentE1
