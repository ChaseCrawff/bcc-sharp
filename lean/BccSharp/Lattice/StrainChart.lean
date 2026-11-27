import BccSharp.Lattice.Energy

set_option autoImplicit false

/-! Exact geometry behind the SB and SF strain handoffs. The
integer matrices and dyadic whitening factors are the published data. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover

def handoffGamma : Reference → Fin 2 → Matrix (Fin 3) (Fin 3) ℤ
  | .bcc, _ => !![-1,0,0; -1,0,-1; 1,-1,1]
  | .fcc, j => if j=0 then !![0,-1,0; -1,0,-1; 0,0,1]
    else !![0,-1,0; -1,0,0; 0,0,-1]

theorem handoffGamma_unimodular (ref : Reference) (j : Fin 2) :
    |(handoffGamma ref j).det| = 1 := by
  cases ref <;> fin_cases j <;> norm_num [handoffGamma,Matrix.det_fin_three]

def cubicBasis : Reference → Mat
  | .bcc => Constants.fccLength • (!![1,0,1/2; 0,1,1/2; 0,0,1/2] : Mat)
  | .fcc => Constants.fccLength⁻¹ • (!![1,1,0; 1,0,1; 0,1,1] : Mat)

theorem cubicBasis_unitVolume (ref : Reference) : volumeOf (cubicBasis ref) = 1 := by
  have ht : Constants.fccLength^3 = 2 := by
    rw [Constants.fccLength, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  cases ref
  · rw [cubicBasis,volumeOf,Matrix.det_smul,Fintype.card_fin,ht,Matrix.det_fin_three]
    norm_num
  · rw [cubicBasis,volumeOf,Matrix.det_smul,Fintype.card_fin,inv_pow,ht,Matrix.det_fin_three]
    norm_num

def strainTensor (ref : Reference) (w : Point) : Mat :=
  let a := (whitenE ref : ℝ)*w 0/Real.sqrt 2
  let b := (whitenE ref : ℝ)*w 1/Real.sqrt 6
  let u := (whitenT ref : ℝ)*w 2/Real.sqrt 2
  let v := (whitenT ref : ℝ)*w 3/Real.sqrt 2
  let z := (whitenT ref : ℝ)*w 4/Real.sqrt 2
  !![a+b,u,v; u,b-a,z; v,z,-2*b]

def strainCoordinates (ref : Reference) (S : Mat) : Point :=
  ![(S 0 0-S 1 1)/(Real.sqrt 2*(whitenE ref : ℝ)),
    (S 0 0+S 1 1-2*S 2 2)/(Real.sqrt 6*(whitenE ref : ℝ)),
    Real.sqrt 2*S 0 1/(whitenT ref : ℝ),
    Real.sqrt 2*S 0 2/(whitenT ref : ℝ),
    Real.sqrt 2*S 1 2/(whitenT ref : ℝ)]

theorem strainTensor_reconstruct (ref : Reference) (S : Mat) (hSym : S.transpose=S)
    (hTrace : S 0 0+S 1 1+S 2 2=0) :
    strainTensor ref (strainCoordinates ref S) = S := by
  have he : (whitenE ref : ℝ) ≠ 0 := by cases ref <;> norm_num [whitenE]
  have ht : (whitenT ref : ℝ) ≠ 0 := by cases ref <;> norm_num [whitenT]
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h6 : Real.sqrt 6 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h2pow := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h6pow := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hSym' (i j : Fin 3) : S j i=S i j := congrFun (congrFun hSym i) j
  have hs01 := hSym' 0 1
  have hs02 := hSym' 0 2
  have hs12 := hSym' 1 2
  have e₂ : 1/(Real.sqrt 2*Real.sqrt 2) = (1/2 : ℝ) := by rw [← pow_two,h2pow]
  have e₆ : 1/(Real.sqrt 6*Real.sqrt 6) = (1/6 : ℝ) := by rw [← pow_two,h6pow]
  have ae (x : ℝ) : (whitenE ref : ℝ)*(x/(Real.sqrt 2*(whitenE ref : ℝ)))/Real.sqrt 2=x/2 := by
    calc
      _ = x*(1/(Real.sqrt 2*Real.sqrt 2)) := by field_simp [he,h2] <;> ring
      _ = _ := by rw [e₂]; ring
  have be (x : ℝ) : (whitenE ref : ℝ)*(x/(Real.sqrt 6*(whitenE ref : ℝ)))/Real.sqrt 6=x/6 := by
    calc
      _ = x*(1/(Real.sqrt 6*Real.sqrt 6)) := by field_simp [he,h6] <;> ring
      _ = _ := by rw [e₆]; ring
  have de (x : ℝ) : (whitenT ref : ℝ)*(Real.sqrt 2*x/(whitenT ref : ℝ))/Real.sqrt 2=x := by
    field_simp [ht,h2]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [strainTensor,strainCoordinates,ae,be,de] <;>
    linarith [hTrace,hs01,hs02,hs12]

def diagonalSum (C : Mat) : ℝ := C 0 0+C 1 1+C 2 2
def normalizedStrain (C : Mat) : Mat := (3/diagonalSum C : ℝ) • C-1

def reconstructedMetric (ref : Reference) (w : Point) : Mat :=
  let J := 1+strainTensor ref w
  (J.det ^ (-(1/3) : ℝ)) • J

theorem normalizedStrain_trace (C : Mat) (ht : diagonalSum C ≠ 0) :
    diagonalSum (normalizedStrain C) = 0 := by
  unfold normalizedStrain diagonalSum
  norm_num [Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply,smul_eq_mul]
  field_simp [show C 0 0+C 1 1+C 2 2 ≠ 0 from ht] <;> ring

theorem normalizedStrain_symm (C : Mat) (hC : C.transpose=C) :
    (normalizedStrain C).transpose=normalizedStrain C := by
  simp [normalizedStrain,Matrix.transpose_sub,Matrix.transpose_smul,hC]

theorem normalizedStrain_metric (ref : Reference) (C : Mat) (hSym : C.transpose=C)
    (hDet : C.det=1) (hTrace : 0 < diagonalSum C) :
    reconstructedMetric ref (strainCoordinates ref (normalizedStrain C)) = C := by
  have ht := normalizedStrain_trace C hTrace.ne'
  have hs := normalizedStrain_symm C hSym
  let u : ℝ := 3/diagonalSum C
  have hu : 0 < u := by unfold u; positivity
  have hS := strainTensor_reconstruct ref (normalizedStrain C) hs ht
  have hJ : 1+normalizedStrain C = u • C := by
    unfold normalizedStrain u
    abel
  have hJdet : (u • C).det = u^3 := by rw [Matrix.det_smul,Fintype.card_fin,hDet,mul_one]
  have hpow : (u^3) ^ (-(1/3) : ℝ) = u⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le,
      show ((3 : ℕ) : ℝ)*(-(1/3) : ℝ) = -1 by norm_num,Real.rpow_neg_one]
  unfold reconstructedMetric
  dsimp only
  rw [hS,hJ,hJdet,hpow,smul_smul,inv_mul_cancel₀ hu.ne',one_smul]

def toRealMatrix (G : Matrix (Fin 3) (Fin 3) ℤ) : Mat := G.map (Int.castRingHom ℝ)

def handoffMatrix (ref : Reference) (j : Fin 2) (p : Point) : Mat :=
  normalizedChart p * (toRealMatrix (handoffGamma ref j))⁻¹ * (cubicBasis ref)⁻¹

def handoffImage (ref : Reference) (j : Fin 2) (p : Point) : Point :=
  strainCoordinates ref (normalizedStrain (gram (handoffMatrix ref j p)))

private theorem volume_mul (A B : Mat) : volumeOf (A*B)=volumeOf A*volumeOf B := by
  rw [volumeOf,Matrix.det_mul,abs_mul]
  rfl

private theorem volume_inv_of_unit (A : Mat) (hA : volumeOf A=1) : volumeOf A⁻¹=1 := by
  have h : A.det≠0 := by
    intro hz
    unfold volumeOf at hA
    rw [hz,abs_zero] at hA
    exact zero_ne_one hA
  have e := congrArg volumeOf (Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h))
  rw [volume_mul,hA,one_mul] at e
  simpa [volumeOf] using e

theorem handoff_unitVolume (ref : Reference) (j : Fin 2) (p : Point)
    (h₁ : p 0≠0) (h₂ : p 1≠0) : volumeOf (handoffMatrix ref j p)=1 := by
  have hA : volumeOf (normalizedChart p)=1 := by simp [volumeOf,normalizedChart_det p h₁ h₂]
  have hG : volumeOf (toRealMatrix (handoffGamma ref j))=1 := by
    unfold volumeOf toRealMatrix
    have e : ((handoffGamma ref j).map (Int.castRingHom ℝ)).det =
        (((handoffGamma ref j).det : ℤ) : ℝ) :=
      ((Int.castRingHom ℝ).map_det (handoffGamma ref j)).symm
    rw [e]
    exact_mod_cast handoffGamma_unimodular ref j
  unfold handoffMatrix
  rw [volume_mul,volume_mul,hA,volume_inv_of_unit _ hG,volume_inv_of_unit _ (cubicBasis_unitVolume ref)]
  ring

private theorem gram_diagonal (A : Mat) (i : Fin 3) :
    gram A i i = sq (fun j => A j i) := by
  unfold gram sq
  simp [Matrix.mul_apply,pow_two]

theorem gram_trace_positive (A : Mat) (hA : A.det≠0) : 0 < diagonalSum (gram A) := by
  have hCol : (fun j : Fin 3 => A j 0) ≠ (0 : Vec) := by
    intro h
    have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
    have e : A.mulVec (Pi.single 0 1) = A.mulVec 0 := by
      rw [Matrix.mulVec_single_one,Matrix.mulVec_zero,Matrix.col_apply']
      exact h
    have hf := congrFun (Matrix.mulVec_injective_of_isUnit hu e) 0
    norm_num [Pi.single_apply] at hf
  have hPos : 0 < sq (fun j => A j 0) :=
    lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hCol))
  unfold diagonalSum
  rw [gram_diagonal A 0,gram_diagonal A 1,gram_diagonal A 2]
  linarith [sq_nonnegative (fun j => A j 1),sq_nonnegative (fun j => A j 2)]

/-- The geometric part of the strain-chart reduction. The actual index and metric are fixed by
the addressed box's chart and the integer basis change. -/
theorem handoff_sameGram (ref : Reference) (j : Fin 2) (p : Point)
    (h₁ : p 0≠0) (h₂ : p 1≠0) :
    reconstructedMetric ref (handoffImage ref j p) = gram (handoffMatrix ref j p) := by
  let A := handoffMatrix ref j p
  have hv : |A.det|=1 := handoff_unitVolume ref j p h₁ h₂
  have hA : A.det≠0 := by intro h; rw [h,abs_zero] at hv; exact zero_ne_one hv
  have hd : (gram A).det=1 := by
    rw [gram,Matrix.det_mul,Matrix.det_transpose,← pow_two,← sq_abs,hv,one_pow]
  exact normalizedStrain_metric ref (gram A) (by simp [gram,Matrix.transpose_mul]) hd (gram_trace_positive A hA)

end BccSharp.Coulomb.BravaisCover
