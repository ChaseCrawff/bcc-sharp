import BccSharp.Lattice.Polar
import BccSharp.Lattice.Curvature
import BccSharp.Lattice.Escape

set_option autoImplicit false

/-! E2 comparison against Constants, including the exact spectral guard
and outward Frobenius penalty. The metric intervals are supplied by the
chart evaluator, not by a reported margin. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Intervals (Ball)

abbrev MetricBalls := Fin 3 → Fin 3 → Ball
def MetricBalls.Contains (B : MetricBalls) (C : Mat) : Prop :=
  ∀ i j, (B i j).Contains (C i j)

def mu : ℚ := 9/10
def nu : ℚ := 169/100

theorem hessianQuadratic_eq_quad (C : Mat) (v : Vec) :
    hessianQuadratic C v=quad C v := by
  unfold hessianQuadratic quad
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem quad_scaledI_sub (t : ℝ) (C : Mat) (x : Vec) :
    quad (t • (1 : Mat)-C) x=t*sq x-quad C x := by
  unfold quad sq
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def upperDifference (B : MetricBalls) : MetricBalls :=
  fun i j => (Ball.exact (if i=j then nu else 0)).sub (B i j)

def spectralCheck (B : MetricBalls) (upperPad : ℚ) : Bool :=
  curvatureCheck mu B && curvatureCheck upperPad (upperDifference B)

theorem spectralCheck_sound (B : MetricBalls) (C : Mat) (hC : B.Contains C) (upperPad : ℚ)
    (ok : spectralCheck B upperPad = true) :
    (∀ x : Vec, (mu : ℝ)*sq x ≤ quad C x) ∧
    (∀ x : Vec, x≠0 → quad C x < (13/10 : ℝ)^2*sq x) := by
  have h := Bool.and_eq_true_iff.mp ok
  have hU : (upperDifference B).Contains ((nu : ℝ) • (1 : Mat)-C) := by
    intro i j
    have e := Ball.contains_sub (Ball.contains_exact (if i=j then nu else 0)) (hC i j)
    by_cases hij : i=j <;> simpa [upperDifference,Matrix.one_apply,Matrix.sub_apply,
      Matrix.smul_apply,smul_eq_mul,hij] using e
  refine ⟨fun x => ?_,fun x hx => ?_⟩
  · have e := curvatureCheck_sound mu B h.1 C hC x
    rwa [hessianQuadratic_eq_quad] at e
  · have e := curvatureCheck_strict upperPad (upperDifference B) h.2 _ hU x hx
    rw [hessianQuadratic_eq_quad,quad_scaledI_sub] at e
    norm_num [nu] at e ⊢
    linarith

def kappaUpper : ℚ := 100/(1+94868329805051379959/10^20)^2

theorem kappaUpper_sound : 100/(1+Real.sqrt (mu : ℝ))^2 ≤ (kappaUpper : ℝ) := by
  have hlo : (94868329805051379959/10^20 : ℝ) ≤ Real.sqrt (mu : ℝ) := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num [mu])]
    norm_num [mu]
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1+94868329805051379959/10^20)
    (add_le_add_right hlo 1) 2
  unfold kappaUpper
  push_cast
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq

def frobDifferenceUpper (B : MetricBalls) : ℚ :=
  ∑ i, ∑ j, (let b := (B i j).sub (Ball.exact (if i=j then 1 else 0)); sqUpper b.lo b.hi)

theorem frobDifferenceUpper_sound (B : MetricBalls) (C : Mat) (hC : B.Contains C) :
    frobSq (C-1) ≤ (frobDifferenceUpper B : ℝ) := by
  unfold frobSq frobDifferenceUpper
  push_cast
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  let b := (B i j).sub (Ball.exact (if i=j then 1 else 0))
  have e : b.Contains ((C-1) i j) := by
    have h := Ball.contains_sub (hC i j) (Ball.contains_exact (if i=j then (1 : ℚ) else 0))
    by_cases hij : i=j <;> simpa [b,Matrix.one_apply,Matrix.sub_apply,hij] using h
  apply sqUpper_sound (l := b.lo) (u := b.hi)
  simpa [Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints b _).mp e

def defectUpper (B : MetricBalls) : ℚ := kappaUpper*frobDifferenceUpper B

theorem defectPointwiseUpper_sound (B : Mat) (A : Mat) (ha : 0<A.det)
    (points : lattice B = A.mulVec '' bcc.points) (C : MetricBalls) (hC : C.Contains (gram A))
    (pad : ℚ) (ok : spectralCheck C pad = true) :
    oneSiteDefect B ≤ (kappaUpper : ℝ)*frobSq (gram A-1) := by
  have hg := spectralCheck_sound C (gram A) hC pad ok
  have hq := bcc_deformed_defect_bound B A ha (mu : ℝ) (by norm_num [mu]) points
    (fun x => by rw [sq_mulVec_gram]; exact hg.1 x)
    (fun x hx => by rw [sq_mulVec_gram]; exact hg.2 x hx)
  exact hq.trans (mul_le_mul_of_nonneg_right kappaUpper_sound (by unfold frobSq; positivity))

theorem defectUpper_sound (B : Mat) (A : Mat) (ha : 0<A.det)
    (points : lattice B = A.mulVec '' bcc.points) (C : MetricBalls) (hC : C.Contains (gram A))
    (pad : ℚ) (ok : spectralCheck C pad = true) : oneSiteDefect B ≤ (defectUpper C : ℝ) := by
  have hf := frobDifferenceUpper_sound C (gram A) hC
  unfold defectUpper
  push_cast
  exact (defectPointwiseUpper_sound B A ha points C hC pad ok).trans
    (mul_le_mul_of_nonneg_left hf (by unfold kappaUpper; positivity))

def scaleLo : ℚ := 1611991954016469/10^15
def scaleHi : ℚ := 1611991954016470/10^15

private theorem cube_monotone_nonnegative {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (h : a^3≤b^3) : a≤b := by
  by_contra! hlt
  have hp := mul_pos (sub_pos.mpr hlt) (show 0 < a^2+a*b+b^2 by
    have hh := hb.trans_lt hlt
    positivity)
  nlinarith

theorem bravaisScale_between : (scaleLo : ℝ) ≤ bravaisScale ∧ bravaisScale ≤ (scaleHi : ℝ) := by
  have lo : (0 : ℝ) ≤ scaleLo := by norm_num [scaleLo]
  have hi : (0 : ℝ) ≤ scaleHi := by norm_num [scaleHi]
  constructor
  · apply cube_monotone_nonnegative lo bravaisScale_positive.le
    rw [bravaisScale_cube]
    norm_num [scaleLo]
    linarith [Real.pi_gt_d20]
  · apply cube_monotone_nonnegative bravaisScale_positive.le hi
    rw [bravaisScale_cube]
    norm_num [scaleHi]
    linarith [Real.pi_lt_d20]

def HbccUpper : ℚ := 3+2*scaleLo* Constants.bccBracket.hi
def gapFactorUpper : ℚ := 2*scaleHi* Constants.gapBracket.hi

theorem HbccUpper_sound : 3+2*bravaisScale*energy bcc ≤ (HbccUpper : ℝ) := by
  have hb : energy bcc ≤ (Constants.bccBracket.hi : ℝ) := (Constants.reference_bounds .bcc).2
  have hneg : (Constants.bccBracket.hi : ℝ)≤0 := by norm_num [Constants.bccBracket]
  have h₁ := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*bravaisScale from (mul_pos two_pos bravaisScale_positive).le)
  have h₂ := mul_le_mul_of_nonpos_right
    (mul_le_mul_of_nonneg_left bravaisScale_between.1 (by norm_num : (0 : ℝ)≤2)) hneg
  unfold HbccUpper
  push_cast
  linarith

theorem gapFactorUpper_sound : 2*bravaisScale*gap ≤ (gapFactorUpper : ℝ) := by
  have hb := Constants.reference_gap_checked.1.2
  have hp := Constants.reference_gap_checked.2
  have h : 0 ≤ (2*scaleHi : ℝ) := by norm_num [scaleHi]
  unfold gapFactorUpper
  push_cast
  exact mul_le_mul (mul_le_mul_of_nonneg_left bravaisScale_between.2 (by norm_num)) hb hp.le h

theorem strict_e2_from_same_point (R : Mat) (hR : R.det=1) (Q : ℝ)
    (upper : oneSiteDefect (Constants.fccLength⁻¹ • R) ≤ Q)
    (hc : (HbccUpper : ℝ)+(gapFactorUpper : ℝ)*Q<positiveSeries R) :
    Sharp (Constants.fccLength⁻¹ • R) := by
  let P := Constants.fccLength⁻¹ • R
  have hD : 0 ≤ oneSiteDefect P := (cappedDefect_range _).1
  have hgp : 0 ≤ (gapFactorUpper : ℝ) :=
    (mul_nonneg (mul_pos two_pos bravaisScale_positive).le Constants.reference_gap_checked.2.le).trans gapFactorUpper_sound
  have hQ := mul_le_mul gapFactorUpper_sound upper hD hgp
  have hEnergy : (energy bcc+gap*oneSiteDefect P)*(2*bravaisScale) < positiveSeries R-3 := by
    nlinarith [HbccUpper_sound,hQ,hc]
  have hE := (lt_div_iff₀ (mul_pos two_pos bravaisScale_positive : (0 : ℝ) < 2*bravaisScale)).2 hEnergy
  rw [← oneSiteEnergy_from_normalized R hR] at hE
  have h : 0<oneSiteDeficit P := by unfold oneSiteDeficit; linarith
  exact ⟨h.le,fun z => (h.ne' z).elim⟩

theorem strict_e2_from_series (R : Mat) (hR : R.det=1) (E Q : ℚ)
    (lower : (E : ℝ) ≤ positiveSeries R) (upper : oneSiteDefect (Constants.fccLength⁻¹ • R) ≤ (Q : ℝ))
    (ok : HbccUpper+gapFactorUpper*Q<E) : Sharp (Constants.fccLength⁻¹ • R) :=
  strict_e2_from_same_point R hR Q upper
    ((by exact_mod_cast ok : (HbccUpper : ℝ)+(gapFactorUpper : ℝ)*(Q : ℝ)<(E : ℝ)).trans_le lower)

end BccSharp.Coulomb.BravaisCover
