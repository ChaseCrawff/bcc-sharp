import BccSharp.Lattice.CubicFold

set_option autoImplicit false

/-! Physical value and rigid-copy proof at the closed chamber
origin. The exact BCC defect and the capped FCC bound use the actual
lifted lattice neighbors. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover

def idealPoints : Reference → Set Vec
  | .bcc => bcc.points
  | .fcc => fcc.points

def idealEnergy : Reference → ℝ
  | .bcc => energy bcc
  | .fcc => energy fcc

private def idealRebase : Reference → Matrix (Fin 3) (Fin 3) ℤ
  | .bcc => !![0,1,1;1,0,1;1,1,1]
  | .fcc => !![0,0,1;0,1,0;1,0,0]

private def idealRebaseInv : Reference → Matrix (Fin 3) (Fin 3) ℤ
  | .bcc => !![-1,0,1;0,-1,1;1,1,-1]
  | .fcc => !![0,0,1;0,1,0;1,0,0]

private theorem idealRebase_inverse (ref : Reference) :
    idealRebase ref*idealRebaseInv ref=1 ∧ idealRebaseInv ref*idealRebase ref=1 := by
  constructor <;> cases ref <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [idealRebase,idealRebaseInv,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_three]

def referenceKind : Reference → Constants.Reference
  | .bcc => .bcc
  | .fcc => .fcc

theorem referenceLength_cube : Constants.fccLength^3=2 := by
  rw [Constants.fccLength,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
  norm_num

private theorem referenceBasis_rebase (ref : Reference) :
    strainBasis ref 1= Constants.primitiveNormalized (referenceKind ref)*toRealMatrix (idealRebase ref) := by
  have ht : Constants.fccLength≠0 := by unfold Constants.fccLength; positivity
  have hScale : Constants.fccLength⁻¹* Constants.fccLength⁻¹= Constants.fccLength/2 := by
    field_simp [ht] <;> nlinarith [referenceLength_cube]
  unfold strainBasis
  rw [one_mul]
  cases ref
  · change Constants.fccLength⁻¹ • (Constants.fccLength • conventionalBcc)=_
    rw [smul_smul,inv_mul_cancel₀ ht,one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conventionalBcc,Constants.primitiveNormalized,referenceKind,Constants.Reference.naturalBasis,
        toRealMatrix,idealRebase,Matrix.map_apply,Matrix.mul_apply,Fin.sum_univ_three]
  · change Constants.fccLength⁻¹ • (Constants.fccLength⁻¹ • (!![1,1,0;1,0,1;0,1,1] : Mat))=_
    rw [smul_smul,hScale]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Constants.primitiveNormalized,referenceKind,Constants.Reference.naturalBasis,
        toRealMatrix,idealRebase,Matrix.map_apply,Matrix.mul_apply,Matrix.smul_apply,
        smul_eq_mul,Fin.sum_univ_three] <;> ring

theorem strain_reference_points (ref : Reference) : lattice (strainBasis ref 1)=idealPoints ref := by
  rw [referenceBasis_rebase, rebase_sameLattice _ _ _ (idealRebase_inverse ref).1]
  cases ref
  · exact Constants.bcc_primitive_points
  · exact Constants.fcc_primitive_points

theorem strain_reference_energy (ref : Reference) : oneSiteEnergy (strainBasis ref 1)=idealEnergy ref := by
  rw [referenceBasis_rebase, oneSiteEnergy_rebase _ _ _ (idealRebase_inverse ref).1
    (idealRebase_inverse ref).2]
  let r := referenceKind ref
  have hα : 0< seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  have h := Constants.reference_repeated_at_same_screen r seriesScreen hα
  rw [green_two_eq_energy _ (Constants.refTwo_valid r)] at h
  have he : Constants.primitiveWSBasis r=ac • Constants.primitiveNormalized r := Constants.wsBasis_eq r
  rw [he] at h
  change oneSiteEnergy (Constants.primitiveNormalized r)=idealEnergy ref
  unfold oneSiteEnergy
  exact h.symm.trans (by cases ref <;> rfl)

theorem lattice_left_mul (A B : Mat) : lattice (A*B)=A.mulVec '' lattice B := by
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨B.mulVec (castVec n),⟨n,rfl⟩,by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_,⟨n,rfl⟩,rfl⟩
    exact ⟨n,by rw [Matrix.mulVec_mulVec]⟩

theorem proper_regularSelf (α : ℝ) (A B : Mat) (hA : proper A) :
    ewaldRegularSelf α (A*B)=ewaldRegularSelf α B := by
  have hv : volumeOf (A*B)=volumeOf B := by simp [volumeOf,Matrix.det_mul,hA.2]
  have r (n : IntVec) : sq (linearImage (A*B) n)=sq (linearImage B n) := by
    unfold linearImage
    rw [← Matrix.mulVec_mulVec,sq_orthogonal hA.1]
  have d (n : IntVec) : sq (dualWave (A*B) n)=sq (dualWave B n) := by
    have e : A⁻¹=A.transpose := Matrix.inv_eq_left_inv hA.1
    unfold dualWave
    rw [Matrix.mul_inv_rev,e,Matrix.transpose_mul,Matrix.transpose_transpose,← Matrix.mulVec_mulVec,
      sq_smul,sq_orthogonal hA.1,sq_smul]
  have d' (n : IntVec) : reciprocalGreenTerm α (A*B) n=reciprocalGreenTerm α B n := by
    unfold reciprocalGreenTerm
    dsimp only
    rw [d]
  have r' (n : IntVec) : screened α (linearImage (A*B) n)=screened α (linearImage B n) := by
    unfold screened
    rw [r]
  unfold ewaldRegularSelf greenBackground
  simp_rw [hv,r',d']

theorem strain_origin_energy (ref : Reference) (A : Mat) (hA : proper A) :
    oneSiteEnergy (strainBasis ref A)=idealEnergy ref := by
  have he : strainBasis ref A=A*strainBasis ref 1 := by
    unfold strainBasis
    rw [one_mul,mul_smul_comm]
  rw [← strain_reference_energy ref,he]
  simp only [oneSite_energy_is_self]
  rw [← mul_smul_comm,proper_regularSelf _ A _ hA]

theorem strain_origin_points (ref : Reference) (A : Mat) :
    lattice (strainBasis ref A)=A.mulVec '' idealPoints ref := by
  have he : strainBasis ref A=A*strainBasis ref 1 := by
    unfold strainBasis
    rw [one_mul,mul_smul_comm]
  rw [he,lattice_left_mul,strain_reference_points]

theorem strain_origin_rigid (ref : Reference) (A : Mat) (hA : proper A) :
    rigidCopy (lattice (strainBasis ref A)) (idealPoints ref) := by
  refine ⟨0,A,hA,?_⟩
  rw [strain_origin_points]
  ext x
  simp [translate]

theorem reconstructedMetric_zero (ref : Reference) : reconstructedMetric ref 0=1 := by
  have e : strainTensor ref 0=0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [strainTensor]
  simp [reconstructedMetric,e]

theorem bcc_origin_defect_zero (A : Mat) (hA : proper A) :
    oneSiteDefect (strainBasis .bcc A)=0 := by
  have hc := bcc_deformed_trial (strainBasis .bcc A) A A 1
    (by rw [hA.2]; exact one_ne_zero) hA (by rw [mul_one])
    (strain_origin_points .bcc A)
    (fun x => by rw [sq_orthogonal hA.1]; nlinarith [sq_nonnegative x])
    (fun x hx => by
      have hn : 0<sq x := lt_of_le_of_ne (sq_nonnegative x)
        (Ne.symm (mt (sq_eq_zero_iff _).mp hx))
      rw [sq_orthogonal hA.1]
      nlinarith)
  have h₀ : 0≤oneSiteDefect (strainBasis .bcc A) := (cappedDefect_range _).1
  simp [frobSq] at hc
  exact le_antisymm hc h₀

theorem strain_origin_sharp (ref : Reference) (A : Mat) (hdet : A.det=1)
    (hgram : gram A=reconstructedMetric ref 0) : Sharp (strainBasis ref A) := by
  have hA : proper A := ⟨hgram.trans (reconstructedMetric_zero ref),hdet⟩
  have hE := strain_origin_energy ref A hA
  have hr := strain_origin_rigid ref A hA
  cases ref
  · exact ⟨by unfold oneSiteDeficit; rw [bcc_origin_defect_zero A hA,hE]; simp [idealEnergy],
      fun _ => Or.inl hr⟩
  · have hD : oneSiteDefect (strainBasis .fcc A)≤1 := (cappedDefect_range _).2
    have h := mul_le_mul_of_nonneg_left hD Constants.reference_gap_checked.2.le
    exact ⟨by unfold oneSiteDeficit; rw [hE]; unfold idealEnergy gap at *; linarith,
      fun _ => Or.inr hr⟩

end BccSharp.Coulomb.BravaisCover
