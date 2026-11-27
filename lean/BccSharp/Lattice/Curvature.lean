import BccSharp.Lattice.GeometricLeaves
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-! Interval curvature and strict equality rules for the Lattice
local balls. The Hessian enclosures must be derived for the actual
Bravais objective, including the signed omitted Hessian terms. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Intervals (Ball)
open BccSharp

abbrev RationalHessian := Fin 5 → Fin 5 → Ball
abbrev RealHessian := Fin 5 → Fin 5 → ℝ

def absUpper (b : Ball) : ℚ := max |b.lo| |b.hi|

theorem absUpper_sound {b : Ball} {x : ℝ} (h : b.Contains x) : |x| ≤ (absUpper b : ℝ) := by
  have h' : (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ) := by
    simpa [Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints _ _).mp h
  unfold absUpper
  push_cast
  apply abs_le.mpr
  exact ⟨(neg_le_neg (le_max_left |(b.lo : ℝ)| |(b.hi : ℝ)|)).trans
      ((neg_abs_le _).trans h'.1),
    h'.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

def offDiagUpper {d : ℕ} (B : Fin d → Fin d → Ball) (i j : Fin d) : ℚ :=
  if i=j then 0 else max (absUpper (B i j)) (absUpper (B j i))

theorem offDiagUpper_symm {d : ℕ} (B : Fin d → Fin d → Ball) (i j : Fin d) :
    offDiagUpper B i j = offDiagUpper B j i := by simp [offDiagUpper,eq_comm,max_comm]

theorem offDiagUpper_nonnegative {d : ℕ} (B : Fin d → Fin d → Ball) (i j : Fin d) : 0 ≤ offDiagUpper B i j := by
  unfold offDiagUpper absUpper
  split_ifs <;> positivity

def curvatureCheck {d : ℕ} (lambda : ℚ) (B : Fin d → Fin d → Ball) : Bool :=
  decide (0 < lambda ∧ ∀ i, lambda+∑ j, offDiagUpper B i j ≤ (B i i).lo)

def hessianQuadratic {d : ℕ} (M : Fin d → Fin d → ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j*v i*v j

theorem curvatureCheck_sound {n : ℕ} (lambda : ℚ) (B : Fin n → Fin n → Ball)
    (hc : curvatureCheck lambda B = true) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, (B i j).Contains (M i j)) (v : Fin n → ℝ) :
    (lambda : ℝ)*(∑ i, (v i)^2) ≤ hessianQuadratic M v := by
  classical
  have row : ∀ i, lambda+∑ j, offDiagUpper B i j ≤ (B i i).lo :=
    (of_decide_eq_true hc : 0 < lambda ∧ ∀ i, _).2
  let A (i j : Fin n) : ℝ := (offDiagUpper B i j : ℝ)
  let d (i : Fin n) : ℝ := ((B i i).lo : ℝ)
  have asym (i j : Fin n) : A i j=A j i := by
    show (offDiagUpper B i j : ℝ) = (offDiagUpper B j i : ℝ)
    exact_mod_cast offDiagUpper_symm B i j
  have noff (i j : Fin n) : 0 ≤ A i j := by
    show (0 : ℝ) ≤ (offDiagUpper B i j : ℝ)
    exact_mod_cast offDiagUpper_nonnegative B i j
  have hrow (i : Fin n) : (lambda : ℝ)+∑ j, A i j ≤ d i := by
    show (lambda : ℝ)+∑ j, (offDiagUpper B i j : ℝ) ≤ ((B i i).lo : ℝ)
    exact_mod_cast row i
  have bound (i j : Fin n) :
      (if i=j then d i*(v i)^2 else 0)-A i j*((v i)^2+(v j)^2)/2 ≤ M i j*v i*v j := by
    by_cases hij : i=j
    · subst j
      have h : d i ≤ M i i := by
        simpa [d,Ball.lo] using ((SpecialFunctions.contains_iff_endpoints _ _).mp (hM i i)).1
      simpa [A,offDiagUpper,pow_two,mul_assoc] using mul_le_mul_of_nonneg_right h (sq_nonneg (v i))
    have hv : |M i j| ≤ A i j := by
      apply (absUpper_sound (hM i j)).trans
      simp only [A,offDiagUpper,if_neg hij,Rat.cast_max]
      exact le_max_left _ _
    have hxy : |v i*v j| ≤ ((v i)^2+(v j)^2)/2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|v i|-|v j|),sq_abs (v i),sq_abs (v j)]
    have hprod : |M i j*v i*v j| ≤ A i j * (((v i)^2+(v j)^2)/2) := by
      rw [mul_assoc,abs_mul]
      exact mul_le_mul hv hxy (abs_nonneg _) (noff i j)
    have hh := (neg_le_neg hprod).trans (neg_abs_le (M i j*v i*v j))
    simp only [if_neg hij,zero_sub]
    convert hh using 1 <;> ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => bound i j
  have s₁ : (∑ i, ∑ j, A i j*(v i)^2) = ∑ i, (∑ j, A i j)*(v i)^2 := by
    simp only [Finset.sum_mul]
  have s₂ : (∑ i, ∑ j, A i j*(v j)^2) = ∑ i, (∑ j, A i j)*(v i)^2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j, A i j*(v i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [asym j i]
      _ = _ := s₁
  have hsOff : (∑ i, ∑ j, A i j*((v i)^2+(v j)^2)/2) =
      ∑ i, (∑ j, A i j)*(v i)^2 := by
    have split : (∑ i, ∑ j, A i j*((v i)^2+(v j)^2)/2) =
        ((∑ i, ∑ j, A i j*(v i)^2)+(∑ i, ∑ j, A i j*(v j)^2))/2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [split,s₁,s₂]
    ring
  have hsDiag : (∑ i, ∑ j : Fin n, if i=j then d i*(v i)^2 else 0) = ∑ i, d i*(v i)^2 := by
    simp [Finset.sum_ite_eq', Finset.sum_ite_eq]
  simp only [Finset.sum_sub_distrib,hsOff,hsDiag] at hsum
  unfold hessianQuadratic
  apply le_trans _ hsum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi := mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (v i))
  linarith

theorem curvatureCheck_strict {n : ℕ} (lambda : ℚ) (B : Fin n → Fin n → Ball)
    (hc : curvatureCheck lambda B = true) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, (B i j).Contains (M i j)) (v : Fin n → ℝ) (hv : v≠0) :
    0 < hessianQuadratic M v := by
  have hl : (0 : ℝ) < lambda := by exact_mod_cast
    (of_decide_eq_true hc : 0 < lambda ∧ ∀ i, lambda+∑ j, offDiagUpper B i j ≤ (B i i).lo).1
  have hp : 0 < ∑ i, (v i)^2 := by
    have ex : ∃ i, v i≠0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i,hi⟩ := ex
    exact (sq_pos_of_ne_zero hi).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
  exact (mul_pos hl hp).trans_le (curvatureCheck_sound lambda B hc M hM v)

theorem centered_ray_strict (f g : ℝ → ℝ) (h0 : g 0 = 0)
    (cf : ContinuousOn f (Set.Icc 0 1)) (cg : ContinuousOn g (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ u > 0, HasDerivAt g u t) :
    f 0 < f 1 := by
  have incg : StrictMonoOn g (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) cg
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨u,hu,hd⟩ := hg t ht
    rwa [hd.deriv]
  have incf : StrictMonoOn f (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) cf
    intro t ht
    rw [interior_Icc] at ht
    rw [(hf t ht).deriv, ← h0]
    exact incg (by simp) (Set.Ioo_subset_Icc_self ht) ht.1
  exact incf (by simp) (by simp) zero_lt_one

/-- Strictness transfers even when the certified objective is a lower
bound for the actual capped-defect deficit. -/
theorem sharp_of_local_center (B : Mat) (p : Point) (objective : ℝ)
    (hbound : objective ≤ oneSiteDeficit B) (hzero : p=0 → 0 ≤ objective)
    (hstrict : p≠0 → 0 < objective)
    (hcenter : p=0 → rigidCopy (lattice B) bcc.points ∨ rigidCopy (lattice B) fcc.points) :
    Sharp B := by
  by_cases h : p=0
  · exact ⟨(hzero h).trans hbound, fun _ => hcenter h⟩
  · have hp := (hstrict h).trans_le hbound
    exact ⟨hp.le, fun he => (hp.ne' he).elim⟩

end BccSharp.Coulomb.BravaisCover
