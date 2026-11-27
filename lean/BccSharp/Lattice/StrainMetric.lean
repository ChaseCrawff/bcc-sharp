import BccSharp.Lattice.E2Core
import BccSharp.Lattice.StrainChart

set_option autoImplicit false

/-! Enclosure of the actual Lattice strain metric and its inverse.
The determinant is tested strictly positive before either division. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

def detBall (A : MetricBalls) : Ball :=
  let a := (A 0 0).mul (((A 1 1).mul (A 2 2)).sub ((A 1 2).mul (A 2 1)))
  let b := (A 0 1).mul (((A 1 0).mul (A 2 2)).sub ((A 1 2).mul (A 2 0)))
  let c := (A 0 2).mul (((A 1 0).mul (A 2 1)).sub ((A 1 1).mul (A 2 0)))
  (a.sub b).add c

theorem detBall_sound (A : MetricBalls) (M : Mat) (h : A.Contains M) : (detBall A).Contains M.det := by
  have a := Ball.contains_mul (h 0 0) (Ball.contains_sub (Ball.contains_mul (h 1 1) (h 2 2))
    (Ball.contains_mul (h 1 2) (h 2 1)))
  have b := Ball.contains_mul (h 0 1) (Ball.contains_sub (Ball.contains_mul (h 1 0) (h 2 2))
    (Ball.contains_mul (h 1 2) (h 2 0)))
  have c := Ball.contains_mul (h 0 2) (Ball.contains_sub (Ball.contains_mul (h 1 0) (h 2 1))
    (Ball.contains_mul (h 1 1) (h 2 0)))
  rw [Matrix.det_fin_three]
  convert Ball.contains_add (Ball.contains_sub a b) c using 1
  all_goals first | rfl | ring

def cyclicAdj (M : Mat) : Mat := fun i j =>
  M (j+1) (i+1) * M (j+2) (i+2) - M (j+1) (i+2) * M (j+2) (i+1)

def cyclicAdjBall (A : MetricBalls) : MetricBalls := fun i j =>
  ((A (j+1) (i+1)).mul (A (j+2) (i+2))).sub ((A (j+1) (i+2)).mul (A (j+2) (i+1)))

theorem cyclicAdjBall_sound {A : MetricBalls} {M : Mat} (h : A.Contains M) :
    (cyclicAdjBall A).Contains (cyclicAdj M) := fun i j =>
  Ball.contains_sub (Ball.contains_mul (h _ _) (h _ _)) (Ball.contains_mul (h _ _) (h _ _))

theorem cyclicAdj_right (M : Mat) : M*cyclicAdj M=M.det • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicAdj,Matrix.mul_apply,Matrix.det_fin_three,Fin.sum_univ_three,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul] <;> ring

def cubeRootCheck (w : RootProposal) (b : Ball) : Bool :=
  decide (0 < w.lower ∧ 0 < w.upper ∧ w.lower^3 ≤ b.lo ∧ b.hi ≤ w.upper^3 ∧ w.ball.invertible)

private theorem cubeReflect {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (h : a^3≤b^3) : a≤b := by
  by_contra! hlt
  have hp := mul_pos (sub_pos.mpr hlt) (show 0<a^2+a*b+b^2 by
    have hpos := hb.trans_lt hlt
    positivity)
  nlinarith [show (a-b)*(a^2+a*b+b^2)=a^3-b^3 by ring]

theorem cubeRoot_sound (w : RootProposal) (b : Ball) (x : ℝ) (hx : 0≤x) (h : b.Contains x)
    (ok : cubeRootCheck w b = true) : w.ball.Contains (x^(1/3 : ℝ)) := by
  have e : 0 < w.lower ∧ 0 < w.upper ∧ w.lower^3 ≤ b.lo ∧ b.hi ≤ w.upper^3 ∧ w.ball.invertible :=
    of_decide_eq_true ok
  have hx3 : (x^(1/3 : ℝ))^3=x := by rw [← Real.rpow_natCast,← Real.rpow_mul hx]; norm_num
  have hx0 : 0≤x^(1/3 : ℝ) := Real.rpow_nonneg hx _
  have lo0 : (0 : ℝ)≤w.lower := by exact_mod_cast e.1.le
  have hi0 : (0 : ℝ)≤w.upper := by exact_mod_cast e.2.1.le
  have hlo : (w.lower : ℝ)^3 ≤ (b.lo : ℝ) := by exact_mod_cast e.2.2.1
  have hhi : (b.hi : ℝ) ≤ (w.upper : ℝ)^3 := by exact_mod_cast e.2.2.2.1
  have hb : (b.lo : ℝ)≤x ∧ x≤(b.hi : ℝ) := by
    simpa [Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints b x).mp h
  have lo := cubeReflect lo0 hx0 (by rw [hx3]; exact hlo.trans hb.1)
  have hi := cubeReflect hx0 hi0 (by rw [hx3]; exact hb.2.trans hhi)
  exact ballOf_sound ⟨lo,hi⟩

theorem cubeRoot_invertible (w : RootProposal) (b : Ball) (ok : cubeRootCheck w b = true) :
    w.ball.invertible :=
  (of_decide_eq_true ok : 0 < w.lower ∧ 0 < w.upper ∧ w.lower^3 ≤ b.lo ∧ b.hi ≤ w.upper^3 ∧
    w.ball.invertible).2.2.2.2

structure StrainMetricWitness where
  sqrt₂ : RootProposal
  sqrt₆ : RootProposal
  determinantRoot : RootProposal

def strainTensorBall (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : MetricBalls :=
  let c (n : Fin 5) (factor : ℚ) (root : RootProposal) :=
    ((Ball.exact factor).mul (coordinateBall b n)).mul root.ball.inv
  let a := c 0 (whitenE ref) w.sqrt₂
  let d := c 1 (whitenE ref) w.sqrt₆
  let u := c 2 (whitenT ref) w.sqrt₂
  let v := c 3 (whitenT ref) w.sqrt₂
  let z := c 4 (whitenT ref) w.sqrt₂
  ![![a.add d,u,v],![u,d.sub a,z],![v,z,(Ball.exact (-2)).mul d]]

theorem strainTensorBall_sound (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (h₂ : w.sqrt₂.check (Ball.exact 2) = true) (h₆ : w.sqrt₆.check (Ball.exact 6) = true)
    (p : Point) (hp : b.Mem p) : (strainTensorBall ref b w).Contains (strainTensor ref p) := by
  have s₂ := RootProposal.inverse_sound w.sqrt₂ (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) h₂
  have s₆ := RootProposal.inverse_sound w.sqrt₆ (Ball.exact 6) 6 (by norm_num) (Ball.contains_exact 6) h₆
  have h₀ := Ball.contains_mul (Ball.contains_mul (Ball.contains_exact (whitenE ref)) (coordinateBall_sound hp 0)) s₂
  have h₁ := Ball.contains_mul (Ball.contains_mul (Ball.contains_exact (whitenE ref)) (coordinateBall_sound hp 1)) s₆
  have h₂' := Ball.contains_mul (Ball.contains_mul (Ball.contains_exact (whitenT ref)) (coordinateBall_sound hp 2)) s₂
  have h₃ := Ball.contains_mul (Ball.contains_mul (Ball.contains_exact (whitenT ref)) (coordinateBall_sound hp 3)) s₂
  have h₄ := Ball.contains_mul (Ball.contains_mul (Ball.contains_exact (whitenT ref)) (coordinateBall_sound hp 4)) s₂
  have h00 := Ball.contains_add h₀ h₁
  have h11 := Ball.contains_sub h₁ h₀
  have h22 := Ball.contains_mul (Ball.contains_exact (-2)) h₁
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    first
    | simpa [strainTensorBall,strainTensor,div_eq_mul_inv] using h00
    | simpa [strainTensorBall,strainTensor,div_eq_mul_inv] using h11
    | simpa [strainTensorBall,strainTensor,div_eq_mul_inv] using h22
    | simpa [strainTensorBall,strainTensor,div_eq_mul_inv] using h₂'
    | simpa [strainTensorBall,strainTensor,div_eq_mul_inv] using h₃
    | simpa [strainTensorBall,strainTensor,div_eq_mul_inv] using h₄

def shiftedTensorBall (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : MetricBalls :=
  fun i j => (Ball.exact (if i=j then 1 else 0)).add (strainTensorBall ref b w i j)

def strainMetricCheck (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : Bool :=
  let d := detBall (shiftedTensorBall ref b w)
  (w.sqrt₂.check (Ball.exact 2) && w.sqrt₆.check (Ball.exact 6)) &&
    ((d.positive && decide d.invertible) && cubeRootCheck w.determinantRoot d)

def metricBall (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : MetricBalls :=
  fun i j => w.determinantRoot.ball.inv.mul (shiftedTensorBall ref b w i j)

def inverseMetricBall (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : MetricBalls :=
  let J := shiftedTensorBall ref b w
  let r := w.determinantRoot.ball.mul (detBall J).inv
  fun i j => r.mul (cyclicAdjBall J i j)

theorem strainMetric_evaluate (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (ok : strainMetricCheck ref b w = true) (p : Point) (hp : b.Mem p) :
    (metricBall ref b w).Contains (reconstructedMetric ref p) ∧
    (inverseMetricBall ref b w).Contains (reconstructedMetric ref p)⁻¹ ∧
    (reconstructedMetric ref p).det=1 := by
  have h := Bool.and_eq_true_iff.mp ok
  have hs := Bool.and_eq_true_iff.mp h.1
  have hd := Bool.and_eq_true_iff.mp h.2
  have hx := Bool.and_eq_true_iff.mp hd.1
  let J : Mat := 1+strainTensor ref p
  let Jb := shiftedTensorBall ref b w
  have hJ : Jb.Contains J := by
    intro i j
    have h := Ball.contains_add (Ball.contains_exact (if i=j then (1 : ℚ) else 0))
      (strainTensorBall_sound ref b w hs.1 hs.2 p hp i j)
    by_cases hij : i=j <;> simpa [J,Jb,shiftedTensorBall,Matrix.one_apply,Matrix.add_apply,hij] using h
  have hdet := detBall_sound Jb J hJ
  have hdpos : 0<J.det := Ball.positive_sound hx.1 hdet
  let r := J.det^(1/3 : ℝ)
  have hr := cubeRoot_sound w.determinantRoot (detBall Jb) J.det hdpos.le hdet hd.2
  have hrpos : 0< r := Real.rpow_pos_of_pos hdpos _
  have rcube : r^3=J.det := by unfold r; rw [← Real.rpow_natCast,← Real.rpow_mul hdpos.le]; norm_num
  have hri := Ball.contains_inv (cubeRoot_invertible _ _ hd.2) hr
  have hdi := Ball.contains_inv (of_decide_eq_true hx.2) hdet
  have hC : reconstructedMetric ref p=r⁻¹ • J := by
    show (J.det ^ (-(1/3) : ℝ)) • J = r⁻¹ • J
    rw [Real.rpow_neg hdpos.le]
  have hCdet : (reconstructedMetric ref p).det=1 := by
    rw [hC,Matrix.det_smul,Fintype.card_fin,inv_pow,rcube,inv_mul_cancel₀ hdpos.ne']
  have hCinv : (reconstructedMetric ref p)⁻¹ = (r*J.det⁻¹) • cyclicAdj J := by
    apply Matrix.inv_eq_right_inv
    rw [hC,smul_mul_assoc,mul_smul_comm,cyclicAdj_right,smul_smul,smul_smul]
    have e : r⁻¹*(r*J.det⁻¹)*J.det=1 := by field_simp [hrpos.ne',hdpos.ne']
    have e' : r⁻¹*(r*J.det⁻¹*J.det)=1 := by rw [← mul_assoc]; exact e
    first | rw [e,one_smul] | rw [e',one_smul]
  refine ⟨?_,?_,hCdet⟩
  · intro i j
    rw [hC]
    exact Ball.contains_mul hri (hJ i j)
  · intro i j
    rw [hCinv]
    exact Ball.contains_mul (Ball.contains_mul hr hdi) (cyclicAdjBall_sound hJ i j)

end BccSharp.Coulomb.BravaisCover
