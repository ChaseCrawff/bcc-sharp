import BccSharp.Lattice.Geometry
import BccSharp.Analysis.IntervalChecks

set_option autoImplicit false

/-! Certificate arithmetic for the Lattice reduction, excluded strain
regions and ball geometry. Equality payloads must separately establish
ball criticality, curvature, and the classical defect comparison. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp

private def scale (c : ℚ) (b : Ball) : Ball := (Ball.exact c).mul b
private theorem scale_sound {c : ℚ} {b : Ball} {x : ℝ} (h : b.Contains x) :
    (scale c b).Contains ((c : ℝ)*x) := Ball.contains_mul (Ball.contains_exact _) h

private theorem upper_negative {b : Ball} {v : ℝ} (h : b.Contains v) (hs : b.hi < 0) : v < 0 := by
  have hu : v ≤ (b.hi : ℝ) := by
    simpa [Ball.hi] using ((SpecialFunctions.contains_iff_endpoints b _).mp h).2
  exact hu.trans_lt (by exact_mod_cast hs)

private def r12 (b : Rectangle) : Ball := (coordinateBall b 0).mul (coordinateBall b 1)
private def ir12 (b : Rectangle) : Ball := (r12 b).inv

private theorem ir12_sound {b : Rectangle} {p : Point} (hp : b.Mem p) (hi : (r12 b).invertible) :
    (ir12 b).Contains (p 0*p 1)⁻¹ :=
  Ball.contains_inv hi (Ball.contains_mul (coordinateBall_sound hp 0) (coordinateBall_sound hp 1))

def firstLength (p : Point) (m : IntVec) : ℝ :=
  (p 0*((m 0 : ℝ)+p 2*(m 1 : ℝ)+p 3*(m 2 : ℝ)))^2 +
  (p 1*((m 1 : ℝ)+p 4*(m 2 : ℝ)))^2 + ((p 0*p 1)⁻¹*(m 2 : ℝ))^2

def projectedLength (p : Point) (a d : ℤ) : ℝ :=
  (p 1*((a : ℝ)+p 4*(d : ℝ)))^2 + ((p 0*p 1)⁻¹*(d : ℝ))^2

theorem firstLength_eq (p : Point) (m : IntVec) :
    firstLength p m = sq ((chartBasis (coordLift p)).mulVec (castVec m)) := by
  unfold firstLength
  norm_num [sq,chartBasis,coordLift,castVec,Fin.sum_univ_three,Matrix.mulVec,dotProduct] <;> ring

theorem reduced_firstLength {p : Point} (hr : reduced p) (m : IntVec) (hm : m ≠ 0) :
    (p 0)^2 ≤ firstLength p m := by
  rw [firstLength_eq]
  exact hr.1 m hm

theorem reduced_projectedLength {p : Point} (hr : reduced p) (a d : ℤ) (hm : a ≠ 0 ∨ d ≠ 0) :
    (p 1)^2 ≤ projectedLength p a d := by
  have h := hr.2 a d hm
  change (p 1)^2 ≤ (p 1*((a : ℝ)+p 4*(d : ℝ)))^2 + ((d : ℝ)/(p 0*p 1))^2 at h
  have he : (p 1*((a : ℝ)+p 4*(d : ℝ)))^2 + ((d : ℝ)/(p 0*p 1))^2 = projectedLength p a d := by
    unfold projectedLength
    ring
  exact h.trans_eq he

theorem proofRoot_of_reduced_far (p : Point) (hr : reduced p)
    (hfar : (4/5 : ℝ) ≤ p 0) (h₂ : 0 < p 1)
    (hx : p 2 ∈ Set.Icc (0 : ℝ) (1/2)) (hy : p 3 ∈ Set.Icc (0 : ℝ) (1/2))
    (hz : p 4 ∈ Set.Icc (-1/2 : ℝ) (1/2)) : proofRoot p := by
  have h₁ : 0 < p 0 := (by norm_num : (0 : ℝ)<4/5).trans_le hfar
  let r₃ : ℝ := (p 0*p 1)⁻¹
  have h₃ : 0 < r₃ := inv_pos.mpr (mul_pos h₁ h₂)
  let s : ℝ := Real.sqrt 3/2
  have hs : 0 < s := by unfold s; positivity
  have hsq : s^2 = (3/4 : ℝ) := by unfold s; rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have hdet : p 0*p 1*r₃=1 := mul_inv_cancel₀ (mul_ne_zero h₁.ne' h₂.ne')
  have hf := reduced_firstLength hr (![0,1,0] : IntVec) (by decide)
  have hg := reduced_projectedLength hr 0 1 (Or.inr one_ne_zero)
  norm_num [firstLength] at hf
  norm_num [projectedLength] at hg
  have hx2 : (p 2)^2 ≤ (1/4 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1] : 0 ≤ 1/2+p 2)]
  have hz2 : (p 4)^2 ≤ (1/4 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (by linarith [hz.1] : 0 ≤ 1/2+p 4)]
  have h12 : s*p 0 ≤ p 1 := by
    apply (sq_le_sq₀ (mul_nonneg hs.le h₁.le) h₂.le).mp
    rw [mul_pow,hsq]
    nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg (p 0))]
  have h23 : s*p 1 ≤ r₃ := by
    apply (sq_le_sq₀ (mul_nonneg hs.le h₂.le) h₃.le).mp
    rw [mul_pow,hsq]
    unfold r₃
    rw [mul_inv_rev]
    nlinarith [mul_le_mul_of_nonneg_left hz2 (sq_nonneg (p 1))]
  have h13 : (3/4 : ℝ)*p 0 ≤ r₃ := by
    have h := (mul_le_mul_of_nonneg_left h12 hs.le).trans h23
    rw [← mul_assoc, ← pow_two,hsq] at h
    exact h
  have hpow : (3/4 : ℝ)*s*(p 0)^3 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul h12 h13 (by positivity) h₂.le) h₁.le
    rw [← hdet]
    convert h using 1 <;> ring
  have hmax : p 0 ≤ (231/200 : ℝ) := by
    by_contra! h
    have hslo : (866/1000 : ℝ) ≤ s := by
      apply (sq_le_sq₀ (by norm_num) hs.le).mp
      rw [hsq]
      norm_num
    have h3 : (231/200 : ℝ)^3 < (p 0)^3 := by
      have hp := mul_pos (sub_pos.mpr h) (show 0 < (p 0)^2+(p 0)*(231/200)+(231/200)^2 by positivity)
      linarith [show (p 0-231/200)*((p 0)^2+(p 0)*(231/200)+(231/200)^2) =
        (p 0)^3-(231/200)^3 by ring]
    have hj := mul_lt_mul_of_pos_left h3 (by positivity : 0 < (3/4 : ℝ)*s)
    have hk := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hslo (by norm_num : (0 : ℝ) ≤ 3/4))
      (by positivity : (0 : ℝ) ≤ (231/200 : ℝ)^3)
    linarith [hpow,hj,hk]
  have hlo : (2/5 : ℝ)*Real.sqrt 3 ≤ p 1 := by
    have h := (mul_le_mul_of_nonneg_left hfar hs.le).trans h12
    unfold s at h
    linarith
  have hhi : p 1 ≤ Real.sqrt (2/(Real.sqrt 3*(4/5))) := by
    have h := mul_le_mul_of_nonneg_left h23 (mul_pos h₁ h₂).le
    rw [hdet] at h
    have hd : (Real.sqrt 3)*(4/5 : ℝ)>0 := by positivity
    apply (sq_le_sq₀ h₂.le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    apply (le_div_iff₀ hd).mpr
    have hj := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfar hs.le) (sq_nonneg (p 1))
    unfold s at h hj
    linarith
  exact ⟨hfar,hmax,hlo,hhi,hx,hy,hz⟩

def projectedBall (b : Rectangle) (a d : ℤ) : Ball :=
  let v := (coordinateBall b 1).mul ((Ball.exact (a : ℚ)).add (scale (d : ℚ) (coordinateBall b 4)))
  let w := scale (d : ℚ) (ir12 b)
  (sqBall v).add (sqBall w)

theorem projectedBall_sound {b : Rectangle} {p : Point} (hp : b.Mem p) (hi : (r12 b).invertible)
    (a d : ℤ) : (projectedBall b a d).Contains (projectedLength p a d) := by
  have hv := Ball.contains_mul (coordinateBall_sound hp 1)
    (Ball.contains_add (Ball.contains_exact (a : ℚ)) (scale_sound (c := (d : ℚ)) (coordinateBall_sound hp 4)))
  have hw := scale_sound (c := (d : ℚ)) (ir12_sound hp hi)
  have h := Ball.contains_add (sqBall_sound hv) (sqBall_sound hw)
  have he : projectedLength p a d =
      (p 1*(((a : ℚ) : ℝ)+((d : ℚ) : ℝ)*p 4))^2 + (((d : ℚ) : ℝ)*(p 0*p 1)⁻¹)^2 := by
    unfold projectedLength
    push_cast
    ring
  rw [he]
  exact h

def firstBall (b : Rectangle) (m : IntVec) : Ball :=
  let w := (Ball.exact (m 0 : ℚ)).add
    ((scale (m 1 : ℚ) (coordinateBall b 2)).add (scale (m 2 : ℚ) (coordinateBall b 3)))
  (sqBall ((coordinateBall b 0).mul w)).add (projectedBall b (m 1) (m 2))

theorem firstBall_sound {b : Rectangle} {p : Point} (hp : b.Mem p) (hi : (r12 b).invertible)
    (m : IntVec) : (firstBall b m).Contains (firstLength p m) := by
  have hw := Ball.contains_add (Ball.contains_exact (m 0 : ℚ))
    (Ball.contains_add (scale_sound (c := (m 1 : ℚ)) (coordinateBall_sound hp 2))
      (scale_sound (c := (m 2 : ℚ)) (coordinateBall_sound hp 3)))
  have h := Ball.contains_add (sqBall_sound (Ball.contains_mul (coordinateBall_sound hp 0) hw))
    (projectedBall_sound hp hi (m 1) (m 2))
  convert h using 1
  · rfl
  · unfold firstLength projectedLength
    push_cast
    ring

inductive ReductionWitness where
  | full (m : IntVec)
  | projected (a d : ℤ)

def reductionCheck (w : ReductionWitness) (b : Rectangle) : Bool :=
  decide (r12 b).invertible &&
    match w with
    | .full m =>
      decide (m ≠ 0 ∧ ((firstBall b m).sub (sqBall (coordinateBall b 0))).hi < 0)
    | .projected a d =>
      decide ((a ≠ 0 ∨ d ≠ 0) ∧ ((projectedBall b a d).sub (sqBall (coordinateBall b 1))).hi < 0)

theorem reductionCheck_sound (w : ReductionWitness) (b : Rectangle) (hc : reductionCheck w b = true)
    (p : Point) (hp : b.Mem p) : ¬ reduced p := by
  intro hr
  have hs := Bool.and_eq_true_iff.mp hc
  have hi : (r12 b).invertible := of_decide_eq_true hs.1
  cases w with
  | full m =>
    have hm : m ≠ 0 ∧ ((firstBall b m).sub (sqBall (coordinateBall b 0))).hi < 0 := of_decide_eq_true hs.2
    have h := upper_negative (Ball.contains_sub (firstBall_sound hp hi m)
      (sqBall_sound (coordinateBall_sound hp 0))) hm.2
    exact (not_lt_of_ge (reduced_firstLength hr m hm.1)) (sub_neg.mp h)
  | projected a d =>
    have hm : (a ≠ 0 ∨ d ≠ 0) ∧ ((projectedBall b a d).sub (sqBall (coordinateBall b 1))).hi < 0 :=
      of_decide_eq_true hs.2
    have h := upper_negative (Ball.contains_sub (projectedBall_sound hp hi a d)
      (sqBall_sound (coordinateBall_sound hp 1))) hm.2
    exact (not_lt_of_ge (reduced_projectedLength hr a d hm.1)) (sub_neg.mp h)

def foldedOutsideCheck (b : Rectangle) : Bool :=
  decide (b.hi 0 < 0 ∨ b.hi 1 < 0 ∨ b.hi 2 < 0 ∨ b.hi 3 < 0 ∨
    (0 ≤ b.lo 0 ∧ 0 ≤ b.hi 1 ∧ 3*(b.hi 1)^2 < (b.lo 0)^2))

theorem foldedOutsideCheck_sound (b : Rectangle) (hc : foldedOutsideCheck b = true)
    (p : Point) (hp : b.Mem p) : ¬ folded p := by
  intro hf
  have hpos : 0 < Real.sqrt 3 := by positivity
  have hp1 : 0 ≤ p 1 := by
    by_contra! hn
    exact (not_lt_of_ge (hf.1.trans hf.2.1)) (mul_neg_of_pos_of_neg hpos hn)
  have h := of_decide_eq_true hc
  change b.hi 0 < 0 ∨ b.hi 1 < 0 ∨ b.hi 2 < 0 ∨ b.hi 3 < 0 ∨
    (0 ≤ b.lo 0 ∧ 0 ≤ b.hi 1 ∧ 3*(b.hi 1)^2 < (b.lo 0)^2) at h
  rcases h with h | h | h | h | ⟨hl,hu,hline⟩
  · exact (not_lt_of_ge (hf.1.trans (hp 0).2)) (by exact_mod_cast h)
  · exact (not_lt_of_ge (hp1.trans (hp 1).2)) (by exact_mod_cast h)
  · exact (not_lt_of_ge (hf.2.2.1.trans (hp 2).2)) (by exact_mod_cast h)
  · exact (not_lt_of_ge (hf.2.2.2.trans (hp 3).2)) (by exact_mod_cast h)
  · have hlo := pow_le_pow_left₀ (show (0 : ℝ) ≤ b.lo 0 by exact_mod_cast hl) (hp 0).1 2
    have hfold := pow_le_pow_left₀ hf.1 hf.2.1 2
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hfold
    have hhi := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp1 (hp 1).2 2) (by norm_num : (0 : ℝ) ≤ 3)
    have hfine : 3*(b.hi 1 : ℝ)^2 < (b.lo 0 : ℝ)^2 := by exact_mod_cast hline
    exact (not_lt_of_ge ((hlo.trans hfold).trans hhi)) hfine

def outsideBallCheck (e t : ℚ) (b : Rectangle) : Bool :=
  decide (e^2 < sqLower (b.lo 0) (b.hi 0)+sqLower (b.lo 1) (b.hi 1) ∨
    ∃ i : Fin 5, 2 ≤ i.val ∧ (b.hi i < -t ∨ t < b.lo i))

theorem outsideBallCheck_sound (e t : ℚ) (b : Rectangle) (hc : outsideBallCheck e t b = true)
    (p : Point) (hp : b.Mem p) : ¬ inProductBall e t p := by
  intro hb
  have h := of_decide_eq_true hc
  change e^2 < sqLower (b.lo 0) (b.hi 0)+sqLower (b.lo 1) (b.hi 1) ∨
    (∃ i : Fin 5, 2 ≤ i.val ∧ (b.hi i < -t ∨ t < b.lo i)) at h
  rcases h with h | ⟨i,hi,hlo | hhi⟩
  · have hsum := add_le_add (sqLower_sound (hp 0)) (sqLower_sound (hp 1))
    have hh : (e : ℝ)^2 <
        (sqLower (b.lo 0) (b.hi 0) : ℝ)+(sqLower (b.lo 1) (b.hi 1) : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (hsum.trans hb.1)) hh
  · exact (not_lt_of_ge (((abs_le.mp (hb.2 i hi)).1).trans (hp i).2)) (by exact_mod_cast hlo)
  · exact (not_lt_of_ge ((hp i).1.trans ((abs_le.mp (hb.2 i hi)).2))) (by exact_mod_cast hhi)

def insideBallCheck (e t : ℚ) (b : Rectangle) : Bool :=
  decide (sqUpper (b.lo 0) (b.hi 0)+sqUpper (b.lo 1) (b.hi 1) ≤ e^2 ∧
    ∀ i : Fin 5, 2 ≤ i.val → -t ≤ b.lo i ∧ b.hi i ≤ t)

theorem insideBallCheck_sound (e t : ℚ) (b : Rectangle) (hc : insideBallCheck e t b = true)
    (p : Point) (hp : b.Mem p) : inProductBall e t p := by
  have h : sqUpper (b.lo 0) (b.hi 0)+sqUpper (b.lo 1) (b.hi 1) ≤ e^2 ∧
    ∀ i : Fin 5, 2 ≤ i.val → -t ≤ b.lo i ∧ b.hi i ≤ t := of_decide_eq_true hc
  refine ⟨(add_le_add (sqUpper_sound (hp 0)) (sqUpper_sound (hp 1))).trans (by exact_mod_cast h.1),?_⟩
  intro i hi
  exact abs_le.mpr ⟨(by exact_mod_cast (h.2 i hi).1 : -(t : ℝ) ≤ b.lo i).trans (hp i).1,
    (hp i).2.trans (by exact_mod_cast (h.2 i hi).2)⟩

def strainOutsideCheck (ref : Reference) (b : Rectangle) : Bool :=
  foldedOutsideCheck b || outsideBallCheck (strainRadiusE ref) strainRadiusT b

theorem strainOutsideCheck_sound (ref : Reference) (b : Rectangle)
    (hc : strainOutsideCheck ref b = true) (p : Point) (hp : b.Mem p) : ¬ strainEligible ref p := by
  intro he
  rcases Bool.or_eq_true_iff.mp hc with hh | hh
  · exact foldedOutsideCheck_sound b hh p hp he.1
  · exact outsideBallCheck_sound _ _ b hh p hp he.2

end BccSharp.Coulomb.BravaisCover
