import BccSharp.Lattice.HessianTail
import BccSharp.Lattice.Curvature

set_option autoImplicit false

/-! Rational LDLᵀ fallback for completed Hessian intervals.
The row-radius correction applies to the signed, tail-inclusive matrix. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Intervals (Ball)

abbrev BallMatrix (n : ℕ) := Fin n → Fin n → Ball
abbrev RatMatrix (n : ℕ) := Fin n → Fin n → ℚ

def symmetricBall {n : ℕ} (B : BallMatrix n) (i j : Fin n) : Ball :=
  let m := ((B i j).mid+(B j i).mid)/2
  ⟨m,max (|(B i j).mid-m|+(B i j).rad) (|(B j i).mid-m|+(B j i).rad)⟩

theorem symmetricBall_swap {n : ℕ} (B : BallMatrix n) (i j : Fin n) :
    symmetricBall B i j=symmetricBall B j i := by
  unfold symmetricBall
  dsimp only
  rw [add_comm (B i j).mid (B j i).mid,max_comm]

theorem symmetricBall_sound {n : ℕ} {B : BallMatrix n} {i j : Fin n} {x : ℝ}
    (hx : (B i j).Contains x) : (symmetricBall B i j).Contains x := by
  apply Ball.covers_sound _ hx
  unfold Ball.Covers symmetricBall
  exact le_max_left _ _

def correctedMidpoint {n : ℕ} (B : BallMatrix n) : RatMatrix n :=
  fun i j => (symmetricBall B i j).mid-
    if i=j then ∑ k, (symmetricBall B i k).rad else 0

/-- Young's inequality subtracts one full interval-radius row sum from
each diagonal before the exact factor check. -/
theorem correctedMidpoint_lower {n : ℕ} (B : BallMatrix n) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, (B i j).Contains (M i j)) (v : Fin n → ℝ) :
    hessianQuadratic (fun i j => (correctedMidpoint B i j : ℝ)) v≤hessianQuadratic M v := by
  classical
  let m (i j : Fin n) : ℝ := (symmetricBall B i j).mid
  let r (i j : Fin n) : ℝ := (symmetricBall B i j).rad
  have sym (i j : Fin n) : r i j=r j i := by unfold r; rw [symmetricBall_swap B i j]
  have hb (i j : Fin n) : |M i j-m i j|≤ r i j := symmetricBall_sound (hM i j)
  have rn (i j : Fin n) : 0≤ r i j := (abs_nonneg _).trans (hb i j)
  have term (i j : Fin n) :
      m i j*v i*v j-r i j*((v i)^2+(v j)^2)/2≤M i j*v i*v j := by
    have hy : |v i*v j|≤((v i)^2+(v j)^2)/2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|v i|-|v j|),sq_abs (v i),sq_abs (v j)]
    have he : |(M i j-m i j)*(v i*v j)|≤ r i j*(((v i)^2+(v j)^2)/2) := by
      rw [abs_mul]
      exact mul_le_mul (hb i j) hy (abs_nonneg _) (rn i j)
    have h := (neg_le_neg he).trans (neg_abs_le ((M i j-m i j)*(v i*v j)))
    nlinarith
  have bound := Finset.sum_le_sum fun i (_ : i∈(Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun j (_ : j∈(Finset.univ : Finset (Fin n))) => term i j
  have s₁ : (∑ i,∑ j,r i j*(v i)^2)=∑ i,(∑ j,r i j)*(v i)^2 := by
    simp only [Finset.sum_mul]
  have s₂ : (∑ i,∑ j,r i j*(v j)^2)=∑ i,(∑ j,r i j)*(v i)^2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i,∑ j,r i j*(v i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [sym j i]
      _ = _ := s₁
  have sumCorrection : (∑ i,∑ j,r i j*((v i)^2+(v j)^2)/2)=
      ∑ i,(∑ j,r i j)*(v i)^2 := by
    have split : (∑ i,∑ j,r i j*((v i)^2+(v j)^2)/2) =
        ((∑ i,∑ j,r i j*(v i)^2)+(∑ i,∑ j,r i j*(v j)^2))/2 := by
      rw [← Finset.sum_add_distrib,Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib,Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [split,s₁,s₂]
    ring
  have expand : hessianQuadratic (fun i j => (correctedMidpoint B i j : ℝ)) v =
      (∑ i,∑ j,m i j*v i*v j)-(∑ i,(∑ j,r i j)*(v i)^2) := by
    have point (i j : Fin n) :
        (correctedMidpoint B i j : ℝ)*v i*v j =
          m i j*v i*v j-(if i=j then (∑ k,r i k)*(v i)^2 else 0) := by
      by_cases e : i=j
      · subst j
        simp [correctedMidpoint,m,r,Rat.cast_sum,pow_two] <;> ring
      · simp [correctedMidpoint,m,e]
    unfold hessianQuadratic
    simp only [point,Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [Finset.sum_ite_eq',Finset.sum_ite_eq]
  rw [expand]
  simp only [Finset.sum_sub_distrib,sumCorrection] at bound
  exact bound

structure LdlWitness (n : ℕ) where
  factor : RatMatrix n
  pivot : Fin n → ℚ

def ldlCheck {n : ℕ} (B : BallMatrix n) (w : LdlWitness n) : Bool :=
  decide ((∀ i, 0<w.pivot i ∧ w.factor i i=1) ∧
    (∀ i j, i<j → w.factor i j=0) ∧
    (∀ i j, correctedMidpoint B i j=∑ k,w.factor i k*w.pivot k*w.factor j k))

private theorem ldl_expansion {n : ℕ} (F : Fin n → Fin n → ℝ) (d v : Fin n → ℝ) :
    hessianQuadratic (fun i j => ∑ k, F i k*d k*F j k) v =
      ∑ k, d k*(∑ i, F i k*v i)^2 := by
  unfold hessianQuadratic
  simp_rw [Finset.sum_mul]
  calc
    (∑ i,∑ j,∑ k, F i k*d k*F j k*v i*v j)
        = ∑ i,∑ k,∑ j, F i k*d k*F j k*v i*v j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k,∑ i,∑ j, F i k*d k*F j k*v i*v j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem ldlCheck_sound {n : ℕ} (B : BallMatrix n) (w : LdlWitness n) (check : ldlCheck B w=true)
    (M : Fin n → Fin n → ℝ) (hM : ∀ i j, (B i j).Contains (M i j))
    (v : Fin n → ℝ) (hv : v≠0) : 0<hessianQuadratic M v := by
  classical
  have spec : (∀ i, 0<w.pivot i ∧ w.factor i i=1) ∧
      (∀ i j, i<j → w.factor i j=0) ∧
      (∀ i j, correctedMidpoint B i j=∑ k,w.factor i k*w.pivot k*w.factor j k) :=
    of_decide_eq_true check
  let F (i j : Fin n) : ℝ := w.factor i j
  let d (i : Fin n) : ℝ := w.pivot i
  have diag (i : Fin n) : F i i=1 := by
    show ((w.factor i i : ℚ) : ℝ)=1
    exact_mod_cast (spec.1 i).2
  have upper (i j : Fin n) (h : i<j) : F i j=0 := by
    show ((w.factor i j : ℚ) : ℝ)=0
    exact_mod_cast spec.2.1 i j h
  have positive (i : Fin n) : 0<d i := by
    show (0 : ℝ)<((w.pivot i : ℚ) : ℝ)
    exact_mod_cast (spec.1 i).1
  have e : (fun i j => (correctedMidpoint B i j : ℝ))=fun i j => ∑ k,F i k*d k*F j k := by
    funext i j
    have hr := congrArg (fun q : ℚ => (q : ℝ)) (spec.2.2 i j)
    simpa [F,d,Rat.cast_sum,Rat.cast_mul] using hr
  have existsNonzero : ∃ i, v i≠0 := by
    by_contra! h
    exact hv (funext h)
  let present : Finset (Fin n) := Finset.univ.filter (fun i => v i≠0)
  obtain ⟨i,hi⟩ := existsNonzero
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image present id ⟨i,by simp [present,hi]⟩
  have nonzero : v k≠0 := by simpa [present] using hk
  have col : (∑ i,F i k*v i)=v k := by
    rw [Finset.sum_eq_single k]
    · rw [diag,one_mul]
    · intro i _ ne
      rcases lt_or_gt_of_ne ne with h | h
      · rw [upper i k h,zero_mul]
      · have zero : v i=0 := by
          by_contra hf
          exact (not_le_of_gt h) (hmax i (by simp [present,hf]))
        rw [zero,mul_zero]
    · simp
  apply lt_of_lt_of_le _ (correctedMidpoint_lower B M hM v)
  rw [e,ldl_expansion]
  have hk' : 0<d k*(∑ i,F i k*v i)^2 := by rw [col]; exact mul_pos (positive _) (sq_pos_of_ne_zero nonzero)
  have single : d k*(∑ i,F i k*v i)^2≤∑ j,d j*(∑ i,F i j*v i)^2 :=
    Finset.single_le_sum (f := fun j => d j*(∑ i,F i j*v i)^2)
      (fun j _ => mul_nonneg (positive j).le (sq_nonneg _)) (Finset.mem_univ k)
  exact hk'.trans_le single

def tailHessian {n : ℕ} (part : BallMatrix n) (tau : RatMatrix n) : BallMatrix n :=
  fun i j => withSignedTail (part i j) (tau i j)

theorem ldl_with_signed_tail_sound {n : ℕ} (part : BallMatrix n) (tau : RatMatrix n)
    (w : LdlWitness n) (check : ldlCheck (tailHessian part tau) w=true)
    (P T : Fin n → Fin n → ℝ) (hp : ∀ i j, (part i j).Contains (P i j))
    (ht : ∀ i j, |T i j|≤(tau i j : ℝ)) (v : Fin n → ℝ) (hv : v≠0) :
    0<hessianQuadratic (fun i j => P i j+T i j) v :=
  ldlCheck_sound (tailHessian part tau) w check _ (fun i j => withSignedTail_sound (hp i j) (ht i j)) v hv

end BccSharp.Coulomb.BravaisCover
