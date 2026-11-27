import BccSharp.TwoSite.PrimitiveAnchor
import BccSharp.TwoSite.Star

set_option autoImplicit false

/-! Lattice-neighbour and matching argument for the star defect. The
strict outer cutoff is applied to the actual lifted neighbors. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

private theorem starTwice_injective : ∀ i j : Fin 14,
    (starTwice i 0 = starTwice j 0 ∧ starTwice i 1 = starTwice j 1 ∧
      starTwice i 2 = starTwice j 2) → i = j := by
  decide

theorem star_injective : Function.Injective star := by
  intro i j he
  have h (k : Fin 3) : starTwice i k = starTwice j k := by
    have hi := congrFun he k
    have hh : (starTwice i k : ℝ) = (starTwice j k : ℝ) :=
      (starTwice_eq i k).trans
        ((congrArg (fun t : ℝ => 2*t) hi).trans (starTwice_eq j k).symm)
    exact_mod_cast hh
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  exact starTwice_injective i j ⟨h₀, h₁, h₂⟩

theorem star_sq_bounds (j : Fin 14) : 0 < sq (star j) ∧ sq (star j) ≤ 1 := by
  simp only [sq, Fin.sum_univ_three]
  fin_cases j <;> norm_num [star]

theorem star_in_bcc (j : Fin 14) : star j ∈ bcc.points := by
  rw [← Constants.bcc_primitive_points]
  refine ⟨primitiveLabel j,?_⟩
  funext i
  fin_cases j <;> fin_cases i <;>
    norm_num [Constants.primitiveNormalized,Constants.Reference.naturalBasis,primitiveLabel,starTwice,star,
      Matrix.mulVec,dotProduct,castVec,Fin.sum_univ_three]

private theorem integralCatalogue (a b c : ℤ) (ha : -1 ≤ a ∧ a ≤ 1)
    (hb : -1 ≤ b ∧ b ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1) (h : a^2+b^2+c^2 < 2) :
    (a=0 ∧ b=0 ∧ c=0) ∨
      ∃ j : Fin 14, (starTwice j 0,starTwice j 1,starTwice j 2)=(2*a,2*b,2*c) := by
  rcases ha with ⟨ha₁,ha₂⟩
  rcases hb with ⟨hb₁,hb₂⟩
  rcases hc with ⟨hc₁,hc₂⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at h <;> decide

private theorem shiftedCatalogue (a b c : ℤ) (ha : -1 ≤ a ∧ a ≤ 0)
    (hb : -1 ≤ b ∧ b ≤ 0) (hc : -1 ≤ c ∧ c ≤ 0) :
    ∃ j : Fin 14, (starTwice j 0,starTwice j 1,starTwice j 2)=(2*a+1,2*b+1,2*c+1) := by
  rcases ha with ⟨ha₁,ha₂⟩
  rcases hb with ⟨hb₁,hb₂⟩
  rcases hc with ⟨hc₁,hc₂⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> decide

private theorem coordinate_sq_le (x : Vec) (i : Fin 3) : (x i)^2 ≤ sq x :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

private theorem integralAxisRange {a : ℤ} (h : (a : ℝ)^2 < 2) : -1 ≤ a ∧ a ≤ 1 := by
  have habs : |(a : ℝ)| < 2 := by
    by_contra! hn
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn 2
    rw [sq_abs] at hh
    linarith
  obtain ⟨h₁,h₂⟩ := abs_lt.mp habs
  have h₁' : (-2 : ℤ) < a := by exact_mod_cast h₁
  have h₂' : a < (2 : ℤ) := by exact_mod_cast h₂
  omega

private theorem shiftedAxisRange {a : ℤ} (h : ((a : ℝ)+1/2)^2 < 2) : -1 ≤ a ∧ a ≤ 0 := by
  have habs : |(a : ℝ)+1/2| < 3/2 := by
    by_contra! hn
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3/2) hn 2
    rw [sq_abs] at hh
    linarith
  obtain ⟨h₁,h₂⟩ := abs_lt.mp habs
  have h₁' : (-2 : ℤ) < a := by exact_mod_cast (show (-2 : ℝ) < a by linarith)
  have h₂' : a < (1 : ℤ) := by exact_mod_cast (show (a : ℝ) < 1 by linarith)
  omega

private theorem doubledCoordinates_eq {x : Vec} {j : Fin 14}
    (h : ((starTwice j 0 : ℝ),(starTwice j 1 : ℝ),(starTwice j 2 : ℝ)) =
      (2*x 0,2*x 1,2*x 2)) : star j = x := by
  have h₀ := congrArg Prod.fst h
  have h₁ := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) h
  have h₂ := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) h
  simp only [starTwice_eq] at h₀ h₁ h₂
  funext i
  rcases (by decide : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2) i with rfl | rfl | rfl <;> linarith

/-- Every nonzero conventional-coordinate BCC vector shorter than the
third shell occurs in the fourteen-label registry. -/
theorem bcc_short_is_star {x : Vec} (hx : x ∈ bcc.points) (hn : x≠0) (hr : sq x < 2) :
    ∃ j : Fin 14, star j=x := by
  change x ∈ lattice (1 : Mat) ∪ translate ((1 : Mat).mulVec (fun _ => 1/2)) (lattice (1 : Mat)) at hx
  rcases hx with ⟨n,h⟩ | ⟨u,⟨n,h⟩,eq⟩
  · change Matrix.mulVec 1 (castVec n) = x at h
    rw [Matrix.one_mulVec] at h
    subst x
    have h (i : Fin 3) : ((n i : ℤ) : ℝ)^2 < 2 := (coordinate_sq_le (castVec n) i).trans_lt hr
    have hsum : n 0^2+n 1^2+n 2^2 < 2 := by
      exact_mod_cast (show ((n 0 : ℝ)^2+(n 1 : ℝ)^2+(n 2 : ℝ)^2) < 2 by
        simpa [sq,castVec,Fin.sum_univ_three] using hr)
    rcases integralCatalogue (n 0) (n 1) (n 2) (integralAxisRange (h 0))
      (integralAxisRange (h 1)) (integralAxisRange (h 2)) hsum with hz | ⟨j,hj⟩
    · exact (hn (by funext i; fin_cases i <;> simp [castVec,hz.1,hz.2.1,hz.2.2])).elim
    · refine ⟨j,doubledCoordinates_eq ?_⟩
      have he := congrArg (fun z : ℤ × ℤ × ℤ => ((z.1 : ℝ),(z.2.1 : ℝ),(z.2.2 : ℝ))) hj
      simpa [castVec] using he
  · change Matrix.mulVec 1 (castVec n) = u at h
    rw [Matrix.one_mulVec] at h eq
    subst u
    subst x
    let y : Vec := castVec n+(fun _ => (1/2 : ℝ))
    have hh (i : Fin 3) : ((n i : ℝ)+1/2)^2 < 2 := (coordinate_sq_le y i).trans_lt hr
    obtain ⟨j,hj⟩ := shiftedCatalogue (n 0) (n 1) (n 2) (shiftedAxisRange (hh 0))
      (shiftedAxisRange (hh 1)) (shiftedAxisRange (hh 2))
    refine ⟨j,doubledCoordinates_eq ?_⟩
    have he := congrArg (fun z : ℤ × ℤ × ℤ => ((z.1 : ℝ),(z.2.1 : ℝ),(z.2.2 : ℝ))) hj
    simp only [Pi.add_apply,castVec]
    push_cast at he
    convert he using 1
    ring_nf

theorem star_norm_sum (M : Mat) : (∑ j, sq (M.mulVec (star j))) = 4*frobSq M := by
  have row (i : Fin 3) :
      (∑ j : Fin 14, (∑ k, M i k*star j k)^2) =
        ∑ k, ∑ l, M i k*M i l*(∑ j : Fin 14, star j k*star j l) := by
    calc
      _ = ∑ j : Fin 14, ∑ k, ∑ l, M i k*M i l*(star j k*star j l) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_two,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
  have h (i : Fin 3) :
      (∑ j : Fin 14, (M.mulVec (star j) i)^2) = 4*∑ k, (M i k)^2 := by
    change (∑ j : Fin 14, (∑ k, M i k*star j k)^2) = _
    rw [row i]
    simp_rw [star_second_moment, mul_ite, mul_zero]
    rw [Finset.mul_sum]
    simp [pow_two,mul_comm]
  unfold sq frobSq
  rw [Finset.sum_comm]
  simp_rw [h,Finset.mul_sum]

theorem sq_orthogonal {U : Mat} (hU : U.transpose*U=1) (x : Vec) : sq (U.mulVec x)=sq x := by
  rw [sq_mulVec_gram,gram,hU]
  simp [quad,sq,pow_two]

theorem cappedDefect_le_trial {Y : Set Vec} (U : Mat) (hU : proper U) (σ : Fin 14 ↪ ↥Y) :
    cappedDefect Y ≤ defectTrial U σ := by
  have lower : BddBelow (defectCandidates Y) := by
    refine ⟨0,?_⟩
    intro z hz
    rcases Set.mem_insert_iff.mp hz with hz | ⟨V,_,s,hz⟩
    · rw [hz]; norm_num
    · rw [hz]
      refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg
        (fun j _ => sq_nonnegative _))) (tsum_nonneg ?_)
      intro v
      split_ifs
      · exact le_rfl
      · exact le_max_left _ _
  exact csInf_le lower (Set.mem_insert_of_mem 1 ⟨U,hU,σ,rfl⟩)

theorem bcc_deformed_trial (B A U P : Mat) (hA : A.det≠0) (hU : proper U)
    (decompose : A=U*P) (hPoints : lattice B = A.mulVec '' bcc.points)
    (lower : ∀ x : Vec, (169/200 : ℝ)*sq x ≤ sq (A.mulVec x))
    (upper : ∀ x : Vec, x≠0 → sq (A.mulVec x) < (13/10 : ℝ)^2*sq x) :
    oneSiteDefect B ≤ 100*frobSq (P-1) := by
  let Y := liftedNeighbors (lattice B) 0
  have hInj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))
  have hStar (j : Fin 14) : A.mulVec (star j) ∈ Y := by
    have ne : star j ≠ 0 := fun h => (star_sq_bounds j).1.ne' ((sq_eq_zero_iff _).mpr h)
    refine ⟨?_,?_,(upper _ ne).trans_le ?_⟩
    · rw [zero_add,hPoints]
      exact ⟨star j,star_in_bcc j,rfl⟩
    · intro h
      apply ne (hInj (h.trans (Matrix.mulVec_zero A).symm))
    · simpa using (mul_le_mul_of_nonneg_left (star_sq_bounds j).2 (by positivity :
        (0 : ℝ) ≤ (13/10 : ℝ)^2))
  let σ : Fin 14 ↪ ↥Y := ⟨fun j => ⟨A.mulVec (star j),hStar j⟩,
    fun _ _ h => star_injective (hInj (congrArg Subtype.val h))⟩
  have hs (y : ↥Y) : y ∈ Set.range σ := by
    have hy : y.val ∈ lattice B := by simpa only [zero_add] using y.property.1
    rw [hPoints] at hy
    obtain ⟨x,hx,he⟩ := hy
    have hn : x≠0 := by
      intro hz
      have := y.property.2.1
      exact this (by simpa [hz] using he.symm)
    have hr : sq x < 2 := by
      have hh := lower x
      rw [he] at hh
      linarith [y.property.2.2]
    obtain ⟨j,hj⟩ := bcc_short_is_star hx hn hr
    exact ⟨j,Subtype.ext (by change A.mulVec (star j)=y.val; rwa [hj])⟩
  have hmat (j : Fin 14) :
      sq ((σ j : Vec)-U.mulVec (star j)) = sq ((P-1).mulVec (star j)) := by
    change sq (A.mulVec (star j)-U.mulVec (star j)) = _
    rw [decompose,← Matrix.mulVec_mulVec,← Matrix.mulVec_sub,sq_orthogonal hU.1]
    simp [Matrix.sub_mulVec]
  have hc : defectTrial U σ = 100*frobSq (P-1) := by
    unfold defectTrial
    simp only [hs,ite_true,tsum_zero,add_zero,hmat,star_norm_sum]
    ring
  rw [← hc]
  exact cappedDefect_le_trial U hU σ

end BccSharp.Coulomb
