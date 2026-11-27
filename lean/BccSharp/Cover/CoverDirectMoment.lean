import BccSharp.Cover.CoverExactReal
import BccSharp.Lattice.KernelJet

set_option autoImplicit false

/-! Correlated direct-image route used by the remaining Direct sidecar
owners. The recorded nonnegative slopes determine the exact joint moment.
If a checked scalar lower is weaker, a proved finite adjustment reduces
the intercept; the archived geometry is never recomputed with other slopes. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.DirectRoute
open BccSharp.Coverage BravaisCover
open BccSharp.Intervals (Ball)

private theorem half_nonnegative {x : ℝ} (h : 0<x) : 0≤gKernel (1/2) x := by
  rw [halfKernel_formula h]
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (BccSharp.Ewald.erfc_nonneg _)) (Real.sqrt_nonneg _)

private theorem half_value (x : ℝ) : kernelValue .half x=gKernel (1/2) x := by
  norm_num [kernelValue,KernelKind.power]

private theorem half_slope (x : ℝ) : kernelSlope .half x =
    -(Real.exp (-x)+(1/2:ℝ)*gKernel (1/2) x)/x := by
  norm_num [kernelSlope,half_value,KernelKind.power]

private theorem halfSlope_mono {x y : ℝ} (hx : 0<x) (h : x≤y) :
    kernelSlope .half x≤kernelSlope .half y := by
  let num (t : ℝ) := Real.exp (-t)+(1/2:ℝ)*gKernel (1/2) t
  have nn : 0≤num y := add_nonneg (Real.exp_pos _).le
    (mul_nonneg (by norm_num) (half_nonnegative (hx.trans_le h)))
  have decrease : num y≤num x := add_le_add (Real.exp_le_exp.mpr (neg_le_neg h))
    (mul_le_mul_of_nonneg_left (halfKernel_decreasing hx h) (by norm_num))
  have desc := (div_le_div_of_nonneg_left nn hx h).trans (div_le_div_of_nonneg_right decrease hx.le)
  rw [half_slope,half_slope]
  simpa only [num,neg_div] using neg_le_neg desc

private theorem halfTangent {x y : ℝ} (hx : 0<x) (h : x≤y) :
    kernelValue .half y-kernelSlope .half y*(y-x)≤kernelValue .half x := by
  rcases eq_or_lt_of_le h with rfl | strict
  · simp
  · have continuous : ContinuousOn (kernelValue .half) (Set.Icc x y) := fun z hz =>
      (kernelValue_hasDerivAt .half (hx.trans_le hz.1)).continuousAt.continuousWithinAt
    have derivatives : ∀ z∈Set.Ioo x y, HasDerivAt (kernelValue .half) (kernelSlope .half z) z :=
      fun z hz => kernelValue_hasDerivAt .half (hx.trans hz.1)
    obtain ⟨z,hz,hm⟩ := exists_hasDerivAt_eq_slope (kernelValue .half) (kernelSlope .half)
      strict continuous derivatives
    have slope := mul_le_mul_of_nonneg_right (halfSlope_mono (hx.trans hz.1) hz.2.le) (sub_nonneg.mpr h)
    have m := (eq_div_iff (sub_ne_zero.mpr strict.ne')).mp hm
    linarith only [m,slope]

def slopeAt (u a c : ℚ) : ℚ := max 0 (Constants.piInput.lo * max 0 c+max 0 a/(2*u))

private theorem slopeAt_sound (u a c : ℚ) (hu : (0:ℝ)<u)
    (ha : directLower (Ball.exact u)=some a) (hc : reciprocalLower (Ball.exact u)=some c) :
    (slopeAt u a c : ℝ)≤-Real.pi*kernelSlope .half (Real.pi*(u : ℝ)) := by
  let t := Real.pi*(u : ℝ)
  have ht : 0<t := mul_pos Real.pi_pos hu
  have pLo := (endpoints Constants.piInput_sound).1
  have na : 0≤gKernel (1/2) t := half_nonnegative ht
  have nc : 0≤gKernel 1 t := by rw [gKernel_one ht]; exact div_nonneg (Real.exp_pos _).le ht.le
  have lowerA : (max 0 a : ℝ)≤gKernel (1/2) t := by
    push_cast
    exact max_le na (halfLower_sound (Ball.contains_exact u) hu _ _ ha)
  have lowerC : (max 0 c : ℝ)≤gKernel 1 t := by
    push_cast
    exact max_le nc (oneLower_sound (Ball.contains_exact u) hu _ _ hc)
  have prod := mul_le_mul pLo lowerC (by push_cast; exact le_max_left _ _) Real.pi_pos.le
  have div := div_le_div_of_nonneg_right lowerA (by positivity : 0≤2*(u : ℝ))
  have equality : Real.pi*gKernel 1 t+gKernel (1/2) t/(2*(u : ℝ)) = -Real.pi*kernelSlope .half t := by
    rw [gKernel_one ht,half_slope]
    dsimp only [t]
    field_simp [Real.pi_pos.ne',hu.ne'] <;> ring
  unfold slopeAt
  push_cast
  apply max_le
  · rw [←equality]; positivity
  · exact (add_le_add prod div).trans_eq equality

structure MomentProposal where
  exactReal : ExactRealProposal
  maximum : ℚ
  maximizingCorner : Axis → ℚ

def momentWeight (w : ExactRealProposal) (cross : Bool) (n : IntVec) : ℚ :=
  match readDistance w cross n with | none => 0 | some row => max 0 row.slopeLower

def momentConstant (b : Cell) (w : ExactRealProposal) (cross : Bool) (n : IntVec) : Option ℚ := do
  let row ← readDistance w cross n
  if exactUpperCheck b cross n row.upper then
    let a ← directLower (Ball.exact row.upper)
    let c ← reciprocalLower (Ball.exact row.upper)
    pure (min row.kernelLower a+min (max 0 row.slopeLower) (slopeAt row.upper a c)*row.upper)
  else none

private theorem momentConstant_sound (b : Cell) (w : ExactRealProposal) (s : Bool) (n : IntVec)
    (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b=true) (pos : 0<quad (gram (chartBasis p)) (chartVector p s n))
    (v : ℚ) (ok : momentConstant b w s n=some v) :
    let q := quad (gram (chartBasis p)) (chartVector p s n)
    (v : ℝ)≤gKernel (1/2) (Real.pi*q)+(momentWeight w s n : ℝ)*q := by
  let q := quad (gram (chartBasis p)) (chartVector p s n)
  change (v : ℝ)≤gKernel (1/2) (Real.pi*q)+(momentWeight w s n : ℝ)*q
  cases proposal : readDistance w s n with
  | none => simp [momentConstant,proposal] at ok
  | some row =>
    by_cases tested : exactUpperCheck b s n row.upper=true
    · cases eh : directLower (Ball.exact row.upper) with
      | none => simp [momentConstant,proposal,tested,eh] at ok
      | some a =>
        cases er : reciprocalLower (Ball.exact row.upper) with
        | none => simp [momentConstant,proposal,tested,eh,er] at ok
        | some c =>
          let weight := min (max 0 row.slopeLower) (slopeAt row.upper a c)
          have eq : v=min row.kernelLower a+weight*row.upper := by
            simp [momentConstant,proposal,tested,eh,er] at ok
            exact ok.symm
          have upper := exactUpperCheck_sound b s n row.upper tested hd p hp
          have upos := pos.trans_le upper
          have aLo := halfLower_sound (Ball.contains_exact row.upper) upos _ _ eh
          have k : ((min row.kernelLower a : ℚ) : ℝ)≤gKernel (1/2) (Real.pi*(row.upper : ℝ)) :=
            (Rat.cast_le.mpr (min_le_right _ _)).trans aLo
          have sLo := slopeAt_sound row.upper a c upos eh er
          have lower : (weight : ℝ)≤ -Real.pi*kernelSlope .half (Real.pi*(row.upper : ℝ)) :=
            (Rat.cast_le.mpr (min_le_right _ _)).trans sLo
          have smaller : (weight : ℝ)≤(momentWeight w s n : ℝ) := by
            rw [momentWeight,proposal]
            exact_mod_cast min_le_left (max 0 row.slopeLower) (slopeAt row.upper a c)
          have tangent := halfTangent (mul_pos Real.pi_pos pos)
            (mul_le_mul_of_nonneg_left upper Real.pi_pos.le)
          simp only [half_value] at tangent
          have along := mul_le_mul_of_nonneg_right lower (sub_nonneg.mpr upper)
          have atPoint := mul_le_mul_of_nonneg_right smaller pos.le
          rw [eq]
          push_cast at k ⊢
          linear_combination k+along+tangent+atPoint
    · simp [momentConstant,proposal,tested] at ok

private def family (cross : Bool) : Finset IntVec :=
  (if cross then directIndices 1 else pairedIndices 1).toFinset

def momentReal (w : ExactRealProposal) (p : Chart) : ℝ :=
  (∑ n ∈ family true,(momentWeight w true n : ℝ)*squaredRadial true n p)+
    2*(∑ n ∈ family false,(momentWeight w false n : ℝ)*squaredRadial false n p)

theorem momentReal_chord (b : Cell) (w : ExactRealProposal) (hd : diagonalsCheck b=true) :
    ChordUpper (squareDiag b) (momentReal w) := by
  intro p hp i t lo hi atAxis
  let l := atLower (squareDiag b) p i
  let r := atUpper (squareDiag b) p i
  let f (s : Bool) (x : Chart) := ∑ n ∈ family s,(momentWeight w s n : ℝ)*(-squaredRadial s n x)
  have hF (s : Bool) : (1-t)*f s l+t*f s r≤f s p := by
    unfold f
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    have e : 0≤ momentWeight w s n := by
      unfold momentWeight
      split
      · exact le_rfl
      · exact le_max_left _ _
    have eR : (0:ℝ)≤ momentWeight w s n := by exact_mod_cast e
    have term := squaredRadial_chord s n b hd p hp i t lo hi atAxis
    have weighted := mul_le_mul_of_nonneg_left term eR
    linear_combination weighted
  have fneg (s : Bool) (x : Chart) :
      f s x = -(∑ n ∈ family s,(momentWeight w s n : ℝ)*squaredRadial s n x) := by
    simp [f,mul_neg,Finset.sum_neg_distrib]
  simp only [fneg] at hF
  change (1-t)*(-momentReal w l)+t*(-momentReal w r)≤-momentReal w p
  unfold momentReal
  linear_combination hF true + 2*hF false

def momentCorner (b : Cell) (w : ExactRealProposal) (bits : Axis → Bool) : ℚ :=
  (∑ n ∈ family true,momentWeight w true n*cornerDistance b bits true n)+
    2*(∑ n ∈ family false,momentWeight w false n*cornerDistance b bits false n)

theorem momentCorner_eq (b : Cell) (w : ExactRealProposal) (bits : Axis → Bool) :
    (momentCorner b w bits : ℝ)=momentReal w (corner (squareDiag b) bits) := by
  unfold momentCorner momentReal
  push_cast
  simp_rw [cornerDistance_eq]

def maximumCheck (b : Cell) (w : MomentProposal) : Bool :=
  decide ((∀ bits : Axis → Bool, momentCorner b w.exactReal bits≤w.maximum) ∧
    ∃ bits : Axis → Bool, momentCorner b w.exactReal bits=w.maximum ∧
      ∀ i, cornerRat b bits i=w.maximizingCorner i)

theorem maximumCheck_sound (b : Cell) (w : MomentProposal) (p : Chart) (hp : b.Mem p)
    (hd : diagonalsCheck b=true) (ok : maximumCheck b w=true) :
    momentReal w.exactReal (squarePoint p)≤(w.maximum : ℝ) := by
  have numeric : (∀ bits : Axis → Bool, momentCorner b w.exactReal bits≤w.maximum) ∧
      ∃ bits : Axis → Bool, momentCorner b w.exactReal bits=w.maximum ∧
        ∀ i, cornerRat b bits i=w.maximizingCorner i := of_decide_eq_true ok
  obtain ⟨bits,hbits⟩ := corner_le (squareDiag b) (fun q => -momentReal w.exactReal q)
    (momentReal_chord b w.exactReal hd) _ (squarePoint_mem hp hd)
  rw [←momentCorner_eq] at hbits
  exact (neg_le_neg_iff.mp hbits).trans (by exact_mod_cast numeric.1 bits)

def momentValue (b : Cell) (w : MomentProposal) : Option ℚ := do
  let v ← finiteValueWith b 1 (momentConstant b w.exactReal true) (momentConstant b w.exactReal false)
  pure (v-w.maximum)

def momentCheck (b : Cell) (w : MomentProposal) : Bool :=
  ((sameCell w.exactReal.ownerBox b && operandRoster w.exactReal) &&
    (diagonalsCheck b && cubeRootCheck scaleWitness scaleInput)) &&
  ((maximumCheck b w && decide ((directIndices 1).Nodup ∧ (pairedIndices 1).Nodup)) &&
    match momentValue b w with
    | some v => decide (fccHUpper<v)
    | none => false)

theorem momentCheck_sound (b : Cell) (w : MomentProposal) (p : Chart) (hp : b.Mem p)
    (valid : (chartPoint p).Valid) (ok : momentCheck b w=true) : energy fcc<energy (chartPoint p) := by
  obtain ⟨data,work⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨_,constants⟩ := Bool.and_eq_true_iff.mp data
  obtain ⟨hd,scale⟩ := Bool.and_eq_true_iff.mp constants
  obtain ⟨geo,compared⟩ := Bool.and_eq_true_iff.mp work
  obtain ⟨top,nd⟩ := Bool.and_eq_true_iff.mp geo
  cases ev : finiteValueWith b 1 (momentConstant b w.exactReal true) (momentConstant b w.exactReal false) with
  | none => simp [momentValue,ev] at compared
  | some u =>
    have strict : fccHUpper<u-w.maximum := of_decide_eq_true (by simpa [momentValue,ev] using compared)
    let extra (s : Bool) (n : IntVec) := (momentWeight w.exactReal s n : ℝ)*squaredRadial s n (squarePoint p)
    have bound := finiteValueWith_extra_sound b 1 _ _ p hp hd valid (of_decide_eq_true nd) (extra true) (extra false)
      (fun n _ a e => by simpa [extra,squaredRadial_eq,seriesCrossTerm,chartVector,chartPoint] using
        momentConstant_sound b w.exactReal true n p hp hd (cross_distance_positive valid n) a e)
      (fun n hn a e => by simpa [extra,squaredRadial_eq,seriesDirectTerm,lex_ne hn,chartVector,chartPoint] using
        momentConstant_sound b w.exactReal false n p hp hd (period_distance_positive valid n hn) a e)
      u ev
    have maximum := maximumCheck_sound b w p hp hd top
    change (u : ℝ)≤h₂ (chartPoint p)+momentReal w.exactReal (squarePoint p) at bound
    apply aboveFCC_of_lower _ scale _ strict
    push_cast
    linarith only [bound,maximum]

theorem momentCheck_physical (b : Cell) (w : MomentProposal) (p : Chart) (hp : b.Mem p)
    (valid : (chartPoint p).Valid) (ok : momentCheck b w=true) :
    greenPerParticle seriesScreen (physicalBasis fcc) (physicalTwoPositions fcc)<
      greenPerParticle seriesScreen (physicalBasis (chartPoint p)) (physicalTwoPositions (chartPoint p)) := by
  rw [green_two_eq_energy fcc (Constants.refTwo_valid .fcc),green_two_eq_energy _ valid]
  exact momentCheck_sound b w p hp valid ok

end BccSharp.Coulomb.CompactCover.DirectRoute
