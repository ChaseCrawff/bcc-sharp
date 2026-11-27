import BccSharp.Cover.CoverDirectSeries
import BccSharp.Lattice.KernelJet

set_option autoImplicit false

/-! Global positive-anchor tangents for the two Stage2 kernels.
The anchor is a proposal on a dyadic grid. A directed
intercept and an upper slope prove a bound on either side of the anchor. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.Stage2
open BccSharp BravaisCover DirectRoute
open BccSharp.Intervals (Ball)

theorem value_nonnegative (kind : KernelKind) {t : ℝ} (ht : 0<t) : 0≤kernelValue kind t := by
  cases kind with
  | half =>
    unfold kernelValue
    norm_num [KernelKind.power]
    rw [halfKernel_formula ht]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Ewald.erfc_nonneg _)) (Real.sqrt_nonneg _)
  | one =>
    unfold kernelValue
    norm_num [KernelKind.power]
    rw [gKernel_one ht]
    exact div_nonneg (Real.exp_pos _).le ht.le

theorem value_decreases (kind : KernelKind) {x y : ℝ} (hx : 0<x) (xy : x≤y) :
    kernelValue kind y≤kernelValue kind x := by
  cases kind with
  | half => simpa [kernelValue,KernelKind.power] using halfKernel_decreasing hx xy
  | one => simpa [kernelValue,KernelKind.power] using oneKernel_decreasing hx xy

theorem slope_increases (kind : KernelKind) {x y : ℝ} (hx : 0<x) (xy : x≤y) :
    kernelSlope kind x≤kernelSlope kind y := by
  have hPower : (0:ℝ)≤kind.power := by cases kind <;> norm_num [KernelKind.power]
  let f (t : ℝ) := Real.exp (-t)+(kind.power : ℝ)*kernelValue kind t
  have zero : 0≤f y := add_nonneg (Real.exp_pos _).le (mul_nonneg hPower (value_nonnegative kind (hx.trans_le xy)))
  have order : f y≤f x := add_le_add (Real.exp_le_exp.mpr (neg_le_neg xy))
    (mul_le_mul_of_nonneg_left (value_decreases kind hx xy) hPower)
  have d := (div_le_div_of_nonneg_left zero hx xy).trans (div_le_div_of_nonneg_right order hx.le)
  simpa only [kernelSlope,f,neg_div] using neg_le_neg d

private theorem kernel_secant (kind : KernelKind) {x y : ℝ} (hx : 0<x) (xy : x<y) :
    ∃ z∈Set.Ioo x y, kernelSlope kind z*(y-x)=kernelValue kind y-kernelValue kind x := by
  have c : ContinuousOn (kernelValue kind) (Set.Icc x y) :=
    fun z hz => (kernelValue_hasDerivAt kind (hx.trans_le hz.1)).continuousAt.continuousWithinAt
  have derivative : ∀ z∈Set.Ioo x y, HasDerivAt (kernelValue kind) (kernelSlope kind z) z :=
    fun z hz => kernelValue_hasDerivAt kind (hx.trans hz.1)
  obtain ⟨z,hz,h⟩ := exists_hasDerivAt_eq_slope (kernelValue kind) (kernelSlope kind) xy c derivative
  exact ⟨z,hz,(eq_div_iff (sub_ne_zero.mpr xy.ne')).mp h⟩

theorem globalTangent (kind : KernelKind) {anchor x : ℝ} (ha : 0<anchor) (hx : 0<x) :
    kernelValue kind anchor+kernelSlope kind anchor*(x-anchor)≤kernelValue kind x := by
  rcases lt_trichotomy x anchor with below | equal | above
  · obtain ⟨z,hz,h⟩ := kernel_secant kind hx below
    have s := mul_le_mul_of_nonneg_right (slope_increases kind (hx.trans hz.1) hz.2.le) (sub_nonneg.mpr below.le)
    linear_combination s-h
  · subst x
    simp
  · obtain ⟨z,hz,h⟩ := kernel_secant kind ha above
    have s := mul_le_mul_of_nonneg_right (slope_increases kind ha hz.1.le) (sub_nonneg.mpr above.le)
    linarith only [s,h]

def anchorGrid : ℕ := 2^30
def anchorOf (ticks : ℕ) : ℚ := ticks/((anchorGrid : ℕ) : ℚ)

def expRange (t : Ball) : ExpBounds.Witness :=
  let l := expEndpoint t.lo
  let u := expEndpoint t.hi
  ⟨l.lower,u.upper,ballOf l.result.lo u.result.hi⟩

def anchorEval (kind : KernelKind) (a : Ball) : KernelWitness :=
  match kind with
  | .half => .half (halfProposal a.lo) (halfProposal a.hi) (expRange a.neg)
  | .one => .one (expRange a.neg)

theorem anchorEval_kind (kind : KernelKind) (a : Ball) : (anchorEval kind a).kind=kind := by cases kind <;> rfl

def coefficientGrid : ℚ := 2^96
def lower96 (x : ℚ) : ℚ := (⌊x*coefficientGrid⌋ : ℤ)/coefficientGrid
def upper96 (x : ℚ) : ℚ := (⌈x*coefficientGrid⌉ : ℤ)/coefficientGrid

theorem lower96_le (x : ℚ) : lower96 x≤x :=
  (div_le_iff₀ (by norm_num [coefficientGrid])).2 (Int.floor_le _)
theorem le_upper96 (x : ℚ) : x≤upper96 x :=
  (le_div_iff₀ (by norm_num [coefficientGrid])).2 (Int.le_ceil _)

structure Tangent where
  intercept : ℚ
  penalty : ℚ

def tangent (kind : KernelKind) (ticks : ℕ) : Option Tangent := do
  let x := anchorOf ticks
  let b := Constants.piInput.mul (Ball.exact x)
  let w := anchorEval kind b
  if decide (ticks>0) && w.check b then
    let k := w.evaluate b
    let s := Constants.piInput.mul k.slope.neg
    pure ⟨lower96 (k.value.lo+s.lo*x),upper96 (max 0 s.hi)⟩
  else none

theorem tangent_sound (kind : KernelKind) (ticks : ℕ) (r : Tangent) (ok : tangent kind ticks=some r) :
    0≤ r.penalty ∧ ∀ q : ℝ, 0<q →
      (r.intercept : ℝ)-(r.penalty : ℝ)*q≤kernelValue kind (Real.pi*q) := by
  let x := anchorOf ticks
  let b := Constants.piInput.mul (Ball.exact x)
  let w := anchorEval kind b
  by_cases h : (decide (ticks>0) && w.check b)=true
  · obtain ⟨positive,arithmetic⟩ := Bool.and_eq_true_iff.mp h
    let k := w.evaluate b
    let s := Constants.piInput.mul k.slope.neg
    have eq : r=⟨lower96 (k.value.lo+s.lo*x),upper96 (max 0 s.hi)⟩ := by
      simpa [tangent,x,b,w,h,k,s,eq_comm] using ok
    subst r
    have hticks : 0<ticks := of_decide_eq_true positive
    have xPosQ : 0<x := by dsimp [x,anchorOf,anchorGrid]; positivity
    have xPos : (0:ℝ)<x := by exact_mod_cast xPosQ
    have input : b.Contains (Real.pi*(x : ℝ)) := Ball.contains_mul Constants.piInput_sound (Ball.contains_exact x)
    have e := w.evaluate_sound input arithmetic
    have ev : k.value.Contains (kernelValue kind (Real.pi*(x : ℝ))) := by
      simpa only [w,anchorEval_kind] using e.1
    have es : s.Contains (-Real.pi*kernelSlope kind (Real.pi*(x : ℝ))) := by
      have t := Ball.contains_mul Constants.piInput_sound (Ball.contains_neg e.2.1)
      simpa only [s,w,k,anchorEval_kind,mul_neg,neg_mul] using t
    have lo : (lower96 (k.value.lo+s.lo*x) : ℝ)≤
        kernelValue kind (Real.pi*(x : ℝ))+(-Real.pi*kernelSlope kind (Real.pi*(x : ℝ)))*(x : ℝ) := by
      refine (Rat.cast_le.mpr (lower96_le _)).trans ?_
      push_cast
      exact add_le_add (endpoints ev).1 (mul_le_mul_of_nonneg_right (endpoints es).1 xPos.le)
    have pen : -Real.pi*kernelSlope kind (Real.pi*(x : ℝ))≤(upper96 (max 0 s.hi) : ℝ) :=
      (endpoints es).2.trans (Rat.cast_le.mpr ((le_max_right _ _).trans (le_upper96 _)))
    refine ⟨(le_max_left (0:ℚ) _).trans (le_upper96 _),?_⟩
    intro q qPos
    have anchor := globalTangent kind (mul_pos Real.pi_pos xPos) (mul_pos Real.pi_pos qPos)
    have loss := mul_le_mul_of_nonneg_right pen qPos.le
    linear_combination lo+loss+anchor
  · simp [tangent,x,b,w,h] at ok

end BccSharp.Coulomb.CompactCover.Stage2
