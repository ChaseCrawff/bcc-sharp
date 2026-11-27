import BccSharp.Lattice.StarDefect
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false

/-! Polar-factor estimate in the exact Lattice normalization.
The only spectral input is mathlib's real symmetric matrix diagonalization. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb

private theorem frob_transpose (M : Mat) : frobSq M.transpose=frobSq M := by
  unfold frobSq
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

private theorem frob_left (U M : Mat) (hU : U.transpose*U=1) :
    frobSq (U*M)=frobSq M := by
  have eq (j : Fin 3) : (fun i : Fin 3 => (U*M) i j) = U.mulVec (fun i => M i j) := by
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold frobSq
  rw [Finset.sum_comm]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change sq (fun i : Fin 3 => M i j) = sq (fun i : Fin 3 => (U*M) i j)
  rw [eq, sq_orthogonal hU]

private theorem frob_right (U M : Mat) (hU : U.transpose*U=1) :
    frobSq (M*U.transpose)=frobSq M := by
  rw [← frob_transpose (M*U.transpose),Matrix.transpose_mul,Matrix.transpose_transpose,
    frob_left U M.transpose hU,frob_transpose]

private def diagConj (U : Mat) (d : Vec) : Mat :=
  U*Matrix.diagonal d*U.transpose

private theorem diagConj_mul (U : Mat) (d e : Vec) (hU : U.transpose*U=1) :
    diagConj U d*diagConj U e=diagConj U (fun i => d i*e i) := by
  unfold diagConj
  calc
    _ = U*Matrix.diagonal d*(U.transpose*U)*Matrix.diagonal e*U.transpose := by noncomm_ring
    _ = _ := by rw [hU,mul_one,mul_assoc U,Matrix.diagonal_mul_diagonal]

private theorem diagConj_one (U : Mat) (hU : U*U.transpose=1) :
    diagConj U (fun _ => 1)=1 := by
  simpa [diagConj] using hU

private theorem diagConj_sub (U : Mat) (u v : Vec) :
    diagConj U (fun i => u i-v i)=diagConj U u-diagConj U v := by
  have he : Matrix.diagonal (fun i => u i-v i) = Matrix.diagonal u-Matrix.diagonal v := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,hij]
  rw [diagConj,he,Matrix.mul_sub,Matrix.sub_mul] <;> rfl

private theorem frob_diagConj (U : Mat) (v : Vec) (hU : U.transpose*U=1) :
    frobSq (diagConj U v)=∑ i, (v i)^2 := by
  rw [diagConj,frob_right U _ hU,frob_left U _ hU]
  unfold frobSq
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.diagonal_apply,ite_pow,Finset.sum_ite_eq]

private theorem eigenvalue_from_diag (C U : Mat) (d : Vec)
    (hC : C=diagConj U d) (hU : U.transpose*U=1) (i : Fin 3) :
    ∃ x : Vec, sq x=1 ∧ quad C x=d i := by
  let e : Vec := Pi.single i 1
  let x : Vec := U.mulVec e
  have h₁ : sq e=1 := by simp [e,sq,Pi.single_apply,ite_pow,Finset.sum_ite_eq]
  have hx : sq x=1 := (sq_orthogonal hU e).trans h₁
  have he : (Matrix.diagonal d).mulVec e = d i • e := by
    funext j
    by_cases h : j=i
    · subst j; simp [e,Matrix.mulVec_diagonal,Pi.single_apply,Pi.smul_apply,smul_eq_mul]
    · simp [e,Matrix.mulVec_diagonal,Pi.single_apply,Pi.smul_apply,smul_eq_mul,h]
  have hCx : C.mulVec x = d i • x := by
    unfold x
    calc
      _ = U.mulVec ((Matrix.diagonal d).mulVec ((U.transpose*U).mulVec e)) := by
        rw [hC,diagConj]
        simp only [Matrix.mulVec_mulVec]
        congr 1 <;> noncomm_ring
      _ = _ := by rw [hU,Matrix.one_mulVec,he,Matrix.mulVec_smul]
  refine ⟨x,hx,?_⟩
  unfold quad
  rw [hCx]
  simp only [Pi.smul_apply,smul_eq_mul]
  have eq : ∑ j, x j*(d i*x j) = d i*sq x := by
    rw [sq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [eq,hx,mul_one]

private theorem sqrt_square_error {u m : ℝ} (hm : 0< m) (hu : m ≤ u) :
    (Real.sqrt u-1)^2 ≤ (u-1)^2/(1+Real.sqrt m)^2 := by
  have h0 : 0 < u := hm.trans_le hu
  have h₂ : 1+Real.sqrt m ≤ 1+Real.sqrt u := add_le_add_right (Real.sqrt_le_sqrt hu) 1
  have hprod : (Real.sqrt u-1)*(1+Real.sqrt u)=u-1 := by nlinarith [Real.sq_sqrt h0.le]
  apply (le_div_iff₀ (by positivity : 0 < (1+Real.sqrt m)^2)).mpr
  calc
    _ ≤ (Real.sqrt u-1)^2*(1+Real.sqrt u)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h₂ 2) (sq_nonneg _)
    _ = _ := by rw [← mul_pow,hprod]

theorem symmetric_squareRoot_error (C : Mat) (hC : C.transpose=C) (mu : ℝ) (hmu : 0< mu)
    (lower : ∀ x : Vec, mu*sq x ≤ quad C x) :
    ∃ P : Mat, P.transpose=P ∧ 0<P.det ∧ P*P=C ∧
      frobSq (P-1) ≤ frobSq (C-1)/(1+Real.sqrt mu)^2 := by
  have hH : C.IsHermitian := by
    change C.conjTranspose=C
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,hC]
  let V : Mat := hH.eigenvectorUnitary
  let d : Vec := hH.eigenvalues
  have hV : V.transpose*V=1 := by
    have eq := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.property
    simpa only [V,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using eq
  have hV' : V*V.transpose=1 := by
    have eq := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.property
    simpa only [V,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using eq
  have hd : C=diagConj V d := by
    have he := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at he
    exact he
  have hmin (i : Fin 3) : mu≤d i := by
    obtain ⟨x,hx,hq⟩ := eigenvalue_from_diag C V d hd hV i
    have h := lower x
    rwa [hx,hq,mul_one] at h
  let p : Vec := fun i => Real.sqrt (d i)
  let P := diagConj V p
  have dp (i : Fin 3) : 0<p i := Real.sqrt_pos.mpr (hmu.trans_le (hmin i))
  have hps : P.transpose=P := by
    simp [P,diagConj,Matrix.transpose_mul,Matrix.diagonal_transpose,mul_assoc]
  have hpdet : 0<P.det := by
    have e := congrArg Matrix.det hV'
    rw [Matrix.det_mul,Matrix.det_one] at e
    unfold P diagConj
    rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal]
    rw [show V.det*(∏ i, p i)*V.transpose.det=(V.det*V.transpose.det)*(∏ i, p i) by ring,e,one_mul]
    exact Finset.prod_pos fun i _ => dp i
  have hpp : P*P=C := by
    show diagConj V p*diagConj V p=C
    rw [diagConj_mul V p p hV,hd]
    congr 1
    funext i
    change Real.sqrt (d i)*Real.sqrt (d i)=d i
    rw [← pow_two,Real.sq_sqrt (hmu.trans_le (hmin i)).le]
  refine ⟨P,hps,hpdet,hpp,?_⟩
  show frobSq (diagConj V p-1) ≤ frobSq (C-1)/(1+Real.sqrt mu)^2
  rw [hd,← diagConj_one V hV',← diagConj_sub,← diagConj_sub,
    frob_diagConj V _ hV,frob_diagConj V _ hV,Finset.sum_div]
  exact Finset.sum_le_sum fun i _ => sqrt_square_error hmu (hmin i)

theorem oriented_polar_error (A : Mat) (ha : 0<A.det) (mu : ℝ) (hmu : 0< mu)
    (lower : ∀ x : Vec, mu*sq x ≤ sq (A.mulVec x)) :
    ∃ U P : Mat, proper U ∧ A=U*P ∧
      frobSq (P-1) ≤ frobSq (gram A-1)/(1+Real.sqrt mu)^2 := by
  let C := gram A
  have hc : C.transpose=C := by simp [C,gram,Matrix.transpose_mul]
  obtain ⟨P,hps,hpd,hpp,herr⟩ := symmetric_squareRoot_error C hc mu hmu (fun x => by
    simpa only [C,sq_mulVec_gram] using lower x)
  let U := A*P⁻¹
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hpd.ne'
  have hdec : A=U*P := by unfold U; rw [mul_assoc,Matrix.nonsing_inv_mul P hu,mul_one]
  have hortho : U.transpose*U=1 := by
    unfold U
    rw [Matrix.transpose_mul,Matrix.transpose_nonsing_inv,hps]
    calc
      _ = P⁻¹*C*P⁻¹ := by unfold C gram; noncomm_ring
      _ = (P⁻¹*P)*(P*P⁻¹) := by rw [← hpp]; noncomm_ring
      _ = _ := by rw [Matrix.nonsing_inv_mul P hu,Matrix.mul_nonsing_inv P hu,one_mul]
  have he := congrArg Matrix.det hdec
  rw [Matrix.det_mul] at he
  have hpos : 0<U.det := by
    by_contra! h
    have hn := mul_nonpos_of_nonpos_of_nonneg h hpd.le
    rw [← he] at hn
    exact (not_lt_of_ge hn) ha
  have hUd := congrArg Matrix.det hortho
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at hUd
  have hp : U.det=1 := by nlinarith
  exact ⟨U,P,⟨hortho,hp⟩,hdec,herr⟩

theorem bcc_deformed_defect_bound (B A : Mat) (ha : 0<A.det) (mu : ℝ) (hmu : (169/200 : ℝ)≤ mu)
    (points : lattice B=A.mulVec '' bcc.points)
    (lo : ∀ x : Vec, mu*sq x≤ sq (A.mulVec x))
    (hi : ∀ x : Vec, x≠0 → sq (A.mulVec x)<(13/10 : ℝ)^2*sq x) :
    oneSiteDefect B ≤ (100/(1+Real.sqrt mu)^2)*frobSq (gram A-1) := by
  obtain ⟨U,P,hu,hd,hp⟩ := oriented_polar_error A ha mu ((by norm_num : (0 : ℝ)<169/200).trans_le hmu) lo
  have h := bcc_deformed_trial B A U P ha.ne' hu hd points
    (fun x => (mul_le_mul_of_nonneg_right hmu (sq_nonnegative x)).trans (lo x)) hi
  exact h.trans ((mul_le_mul_of_nonneg_left hp (by norm_num)).trans_eq (by ring))

end BccSharp.Coulomb
