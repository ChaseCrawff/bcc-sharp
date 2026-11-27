import BccSharp.Lattice.StrainOrigin

set_option autoImplicit false

/-! D18 for the actual FCC origin. The eighteen distinct physical
neighbors are inside the stronger 51/40 radius, so four unmatched weights
already reach the cap for every permitted labeling. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp

/-- Every squared-length sublevel of a full-rank lattice is finite. -/
theorem finite_lattice_sublevel (B : Mat) (hB : B.det≠0) (M : ℝ) (hM : 0≤M) :
    {x : Vec | x∈lattice B ∧ sq x≤M}.Finite := by
  obtain ⟨c,hc,coer⟩ := matrix_coercivity B hB
  let R := Real.sqrt (M/c)
  obtain ⟨N,hN⟩ := exists_nat_gt R
  let lift (z : Constants.Triple) : IntVec := ![z.1,z.2.1,z.2.2]
  let indices := Constants.cube (N : ℤ)
  apply (indices.finite_toSet.image (fun z => linearImage B (lift z))).subset
  intro x hx
  obtain ⟨⟨n,rfl⟩,len⟩ := hx
  have bound (i : Fin 3) : -(N : ℤ)≤n i ∧ n i≤N := by
    have hc₀ := coer (castVec n)
    have hpart : (n i : ℝ)^2≤ sq (castVec n) := by
      unfold sq
      exact Finset.single_le_sum (fun j _ => sq_nonneg (castVec n j)) (Finset.mem_univ i)
    have sqBound : (n i : ℝ)^2≤M/c :=
      (le_div_iff₀ hc).2 (by
        rw [mul_comm]
        exact ((mul_le_mul_of_nonneg_left hpart hc.le).trans hc₀).trans len)
    have hAbs : |(n i : ℝ)|≤R := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [sq_abs,Real.sq_sqrt (div_nonneg hM hc.le)]
      exact sqBound
    have hf : |n i|≤(N : ℤ) := by exact_mod_cast hAbs.trans hN.le
    exact abs_le.mp hf
  refine ⟨(n 0,n 1,n 2),?_,?_⟩
  · change (n 0,n 1,n 2) ∈ Constants.cube (N : ℤ)
    simpa [Constants.cube,Finset.mem_product,Finset.mem_Icc] using
      And.intro (bound 0) (And.intro (bound 1) (bound 2))
  · have e : lift (n 0,n 1,n 2)=n := by funext i; fin_cases i <;> rfl
    show linearImage B (lift (n 0,n 1,n 2))=linearImage B n
    rw [e]

private theorem finite_neighbors (B : Mat) (hB : B.det≠0) :
    (liftedNeighbors (lattice B) 0).Finite := by
  apply (finite_lattice_sublevel B hB ((13/10 : ℝ)^2) (by positivity)).subset
  intro x h
  exact ⟨by simpa only [zero_add] using h.1,h.2.2.le⟩

private theorem quarter_weight {x : Vec} (h : sq x≤(51/40 : ℝ)^2) : (1/4 : ℝ)≤annularWeight x := by
  have hroot : Real.sqrt (sq x) ≤ (51/40 : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rwa [Real.sq_sqrt (sq_nonnegative _)]
  unfold annularWeight
  exact (le_min (by norm_num) (by linarith)).trans (le_max_right _ _)

private theorem cappedDefect_eq_one_of_eighteen {Y : Set Vec} (hY : Y.Finite)
    (e : Fin 18 ↪ ↥Y) (near : ∀ i, sq (e i : Vec)≤(51/40 : ℝ)^2) :
    cappedDefect Y=1 := by
  classical
  letI : Fintype ↥Y := hY.fintype
  apply le_antisymm (cappedDefect_range Y).2
  apply le_csInf ⟨1,Set.mem_insert _ _⟩
  intro c hc
  rcases Set.mem_insert_iff.mp hc with rfl | ⟨U,_,σ,rfl⟩
  · exact le_rfl
  let T : Finset ↥Y := Finset.univ.map e
  let V : Finset ↥Y := Finset.univ.map σ
  let X := T \ V
  have ht : T.card=18 := by simp [T]
  have hv : V.card=14 := by simp [V]
  have hn : 4≤X.card := by
    have h : T.card≤X.card+V.card := Finset.card_le_card_sdiff_add_card
    omega
  let w (y : ↥Y) : ℝ := if y∈Set.range σ then 0 else annularWeight y.val
  have hw (y : ↥Y) : 0≤w y := by
    unfold w annularWeight
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  have hx (y : ↥Y) (hy : y∈X) : (1/4 : ℝ)≤w y := by
    have m := Finset.mem_sdiff.mp hy
    have outside : y∉Set.range σ := by
      rintro ⟨i,rfl⟩
      exact m.2 (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    have hwy : w y=annularWeight y.val := ite_eq_right outside
    rw [hwy]
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp m.1
    exact quarter_weight (near i)
  have sumBound : (1 : ℝ)≤ ∑ y∈X,w y := by
    have hsum : (∑ _y∈X,(1/4 : ℝ))≤ ∑ y∈X,w y := Finset.sum_le_sum hx
    have hc' : (4 : ℝ)≤X.card := by exact_mod_cast hn
    simp at hsum
    linarith
  have whole : (1 : ℝ)≤∑' y : ↥Y,w y := by
    rw [tsum_fintype]
    exact sumBound.trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X) (fun y _ _ => hw y))
  unfold defectTrial
  have n : 0≤25 * (∑ i, sq ((σ i : Vec)-U.mulVec (star i))) := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sq_nonnegative _))
  exact whole.trans (le_add_of_nonneg_left n)

private def fcc18 : Fin 18 → IntVec :=
  ![![1,1,0],![1,-1,0],![-1,1,0],![-1,-1,0],
    ![1,0,1],![1,0,-1],![-1,0,1],![-1,0,-1],
    ![0,1,1],![0,1,-1],![0,-1,1],![0,-1,-1],
    ![2,0,0],![-2,0,0],![0,2,0],![0,-2,0],![0,0,2],![0,0,-2]]

private theorem fcc18_inj : Function.Injective fcc18 := by
  have h : ∀ i j : Fin 18, (∀ k : Fin 3, fcc18 i k=fcc18 j k) → i=j := by decide
  exact fun _ _ e => h _ _ (congrFun e)

private theorem fcc18_even (i : Fin 18) :
    let z := fcc18 i
    z 0+z 1+z 2=2*((z 0+z 1+z 2)/2) := by
  fin_cases i <;> norm_num [fcc18]

private theorem fcc18_squares (i : Fin 18) :
    0<sq (castVec (fcc18 i)) ∧ sq (castVec (fcc18 i))≤4 := by
  fin_cases i <;> norm_num [sq,castVec,fcc18,Fin.sum_univ_three]

private def fccShortVector (i : Fin 18) : Vec := (Constants.fccLength/2) • castVec (fcc18 i)

private theorem fccShortVector_mem (i : Fin 18) : fccShortVector i∈fcc.points := by
  rw [← Constants.fcc_primitive_points]
  let z := fcc18 i
  let t := (z 0+z 1+z 2)/2
  let n : IntVec := fun j => t-z j
  have he : (z 0 : ℝ)+(z 1 : ℝ)+(z 2 : ℝ)=2*(t : ℝ) := by
    exact_mod_cast fcc18_even i
  refine ⟨n,?_⟩
  funext j
  fin_cases j <;>
    norm_num [fccShortVector,Constants.primitiveNormalized,Constants.Reference.naturalBasis,n,z,
      Matrix.smul_apply,smul_eq_mul,Pi.smul_apply,Matrix.mulVec,dotProduct,castVec,Fin.sum_univ_three] <;>
    push_cast <;> linear_combination (Constants.fccLength/2)*he.symm

private theorem referenceLength_lt : Constants.fccLength < (51/40 : ℝ) := by
  have hp : 0< Constants.fccLength := by unfold Constants.fccLength; positivity
  by_contra! h
  have hc := pow_le_pow_left₀ (by norm_num : 0≤(51/40 : ℝ)) h 3
  rw [referenceLength_cube] at hc
  norm_num at hc

theorem fcc_origin_defect_one (A : Mat) (hA : proper A) :
    oneSiteDefect (strainBasis .fcc A)=1 := by
  let P := strainBasis .fcc A
  let Y := liftedNeighbors (lattice P) 0
  have ht : 0< Constants.fccLength := by unfold Constants.fccLength; positivity
  have hball (i : Fin 18) :
      0<sq (A.mulVec (fccShortVector i)) ∧ sq (A.mulVec (fccShortVector i))≤(51/40 : ℝ)^2 := by
    rw [sq_orthogonal hA.1,fccShortVector,sq_smul]
    refine ⟨mul_pos (by positivity) (fcc18_squares i).1,?_⟩
    have hc := mul_le_mul_of_nonneg_left (fcc18_squares i).2
      (sq_nonneg (Constants.fccLength/2))
    have hq := pow_le_pow_left₀ ht.le referenceLength_lt.le 2
    nlinarith
  have hY (i : Fin 18) : A.mulVec (fccShortVector i)∈Y := by
    change 0+A.mulVec (fccShortVector i)∈lattice P ∧
      A.mulVec (fccShortVector i)≠0 ∧ sq (A.mulVec (fccShortVector i))<(13/10 : ℝ)^2
    refine ⟨?_,?_,(hball i).2.trans_lt (by norm_num)⟩
    · rw [zero_add, strain_origin_points]
      exact ⟨fccShortVector i,fccShortVector_mem i,rfl⟩
    · intro e
      exact (hball i).1.ne' ((sq_eq_zero_iff _).mpr e)
  let emb : Fin 18 ↪ ↥Y := ⟨fun i => ⟨A.mulVec (fccShortVector i),hY i⟩,by
    intro i j e
    have hU : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hA.2]; exact isUnit_one)
    have ee := Matrix.mulVec_injective_of_isUnit hU (congrArg Subtype.val e)
    apply fcc18_inj
    funext k
    have h := congrFun ee k
    change (Constants.fccLength/2)*(fcc18 i k : ℝ)=(Constants.fccLength/2)*(fcc18 j k : ℝ) at h
    exact_mod_cast mul_left_cancel₀ (show Constants.fccLength/2≠0 by positivity) h⟩
  have hP : P.det≠0 := by
    have h₁ : (cubicBasis .fcc).det≠0 := by
      intro e
      have h := cubicBasis_unitVolume .fcc
      simp [volumeOf,e] at h
    unfold P strainBasis
    rw [Matrix.det_smul,Fintype.card_fin,Matrix.det_mul,hA.2,one_mul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht.ne')) h₁
  exact cappedDefect_eq_one_of_eighteen (finite_neighbors P hP) emb (fun i => (hball i).2)

theorem strain_origin_deficit_zero (ref : Reference) (A : Mat) (h : proper A) :
    oneSiteDeficit (strainBasis ref A)=0 := by
  unfold oneSiteDeficit
  rw [strain_origin_energy ref A h]
  cases ref
  · simp [idealEnergy,bcc_origin_defect_zero A h]
  · rw [fcc_origin_defect_one A h]
    simp [idealEnergy,gap]

end BccSharp.Coulomb.BravaisCover
