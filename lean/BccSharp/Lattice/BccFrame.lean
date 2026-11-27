import BccSharp.Lattice.StrainMetric

set_option autoImplicit false

/-! Exact BCC frame for the strain E2 leaves. Reducing parity in the
third coordinate proves the full lattice identity in both directions. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.BravaisCover

def conventionalBcc : Mat := !![1,0,1/2;0,1,1/2;0,0,1/2]

def bccFrameDirect (n : IntVec) : Vec :=
  ![(n 0 : ℝ)+(n 2 : ℝ)/2,(n 1 : ℝ)+(n 2 : ℝ)/2,(n 2 : ℝ)/2]

def bccFrameDual (n : IntVec) : Vec :=
  ![(n 0 : ℝ),(n 1 : ℝ),2*(n 2 : ℝ)-(n 0 : ℝ)-(n 1 : ℝ)]

theorem conventionalBcc_eq_direct (n : IntVec) :
    linearImage conventionalBcc n=bccFrameDirect n := by
  funext i
  fin_cases i <;> norm_num [conventionalBcc,bccFrameDirect,linearImage,Matrix.mulVec,dotProduct,
    castVec,Fin.sum_univ_three] <;> ring

theorem bccFrame_covers : lattice conventionalBcc=bcc.points := by
  ext x
  change x ∈ lattice conventionalBcc ↔
    x ∈ lattice (1 : Mat) ∪ translate ((1 : Mat).mulVec (fun _ => 1/2)) (lattice (1 : Mat))
  simp only [Matrix.one_mulVec]
  constructor
  · rintro ⟨n,rfl⟩
    change linearImage conventionalBcc n ∈ _
    rw [conventionalBcc_eq_direct]
    let k := n 2/2
    let m : IntVec := ![n 0+k,n 1+k,k]
    have h : n 2=2*k ∨ n 2=2*k+1 := by dsimp [k]; omega
    rcases h with e | o
    · left
      refine ⟨m,?_⟩
      have he : (n 2 : ℝ)=2*((k : ℤ) : ℝ) := by exact_mod_cast e
      funext i
      fin_cases i <;> norm_num [bccFrameDirect,castVec,m,he] <;> linarith
    · right
      refine ⟨castVec m,⟨m,Matrix.one_mulVec (castVec m)⟩,?_⟩
      have ho : (n 2 : ℝ)=2*((k : ℤ) : ℝ)+1 := by exact_mod_cast o
      funext i
      fin_cases i <;> norm_num [bccFrameDirect,castVec,m,Pi.add_apply,ho] <;> linarith
  · have build (n : IntVec) (r : ℤ) :
        linearImage conventionalBcc (![n 0-n 2,n 1-n 2,2*n 2+r] : IntVec)=
          castVec n+(fun _ => (r : ℝ)/2) := by
      rw [conventionalBcc_eq_direct]
      funext i
      fin_cases i <;> norm_num [bccFrameDirect,castVec,Pi.add_apply] <;> push_cast <;> ring
    rintro (⟨n,rfl⟩ | ⟨_,⟨n,rfl⟩,rfl⟩)
    · refine ⟨![n 0-n 2,n 1-n 2,2*n 2+0],(build n 0).trans ?_⟩
      funext i
      simp [Matrix.one_mulVec]
    · refine ⟨![n 0-n 2,n 1-n 2,2*n 2+1],(build n 1).trans ?_⟩
      funext i
      simp [Matrix.one_mulVec]

theorem bccCubic_det : (cubicBasis .bcc).det = 1 := by
  have h : Constants.fccLength^3 = 2 := by
    rw [Constants.fccLength, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [cubicBasis,Matrix.det_smul,Fintype.card_fin,h,Matrix.det_fin_three]
  norm_num

theorem bccCubic_short (n : IntVec) :
    linearImage (cubicBasis .bcc) n= Constants.fccLength • bccFrameDirect n := by
  change linearImage (Constants.fccLength • conventionalBcc) n=_
  rw [linearImage_scale,conventionalBcc_eq_direct]

theorem bccCubic_dual (n : IntVec) :
    cycleFrequency (cubicBasis .bcc) n= Constants.fccLength⁻¹ • bccFrameDual n := by
  have hd : (cubicBasis .bcc).det ≠ 0 := by rw [bccCubic_det]; exact one_ne_zero
  have hu : IsUnit (cubicBasis .bcc).transpose := by
    rw [Matrix.isUnit_iff_isUnit_det,Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hd
  apply Matrix.mulVec_injective_of_isUnit hu
  rw [cycleFrequency_transpose _ hd]
  have ht : Constants.fccLength ≠ 0 := by unfold Constants.fccLength; positivity
  funext i
  fin_cases i <;> norm_num [cubicBasis,bccFrameDual,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
    Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,castVec] <;> field_simp [ht] <;> ring

theorem bcc_strain_points (A : Mat) :
    lattice (Constants.fccLength⁻¹ • (A*cubicBasis .bcc))=A.mulVec '' bcc.points := by
  have ht : Constants.fccLength ≠ 0 := by unfold Constants.fccLength; positivity
  have he : Constants.fccLength⁻¹ • (A*cubicBasis .bcc)=A*conventionalBcc := by
    change Constants.fccLength⁻¹ • (A*(Constants.fccLength • conventionalBcc))=_
    rw [mul_smul_comm,smul_smul,inv_mul_cancel₀ ht,one_smul]
  rw [he,←bccFrame_covers]
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨conventionalBcc.mulVec (castVec n),⟨n,rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_,⟨n,rfl⟩,rfl⟩
    exact ⟨n,by rw [Matrix.mulVec_mulVec]⟩

theorem reconstructedMetric_symm (ref : Reference) (w : Point) :
    (reconstructedMetric ref w).transpose=reconstructedMetric ref w := by
  have hs : (strainTensor ref w).transpose=strainTensor ref w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [strainTensor,Matrix.transpose_apply]
  simp [reconstructedMetric,Matrix.transpose_smul,Matrix.transpose_add,hs]

/-- A concrete normalized basis for Lattice's BCC strain, with an oriented
deformation and the actual normalized physical neighbor set. -/
theorem bcc_strain_basis (w : Point) (hc : (reconstructedMetric .bcc w).det=1)
    (lo : ∀ x : Vec, (mu : ℝ)*sq x ≤ quad (reconstructedMetric .bcc w) x) :
    ∃ A : Mat, A.det=1 ∧ gram A=reconstructedMetric .bcc w := by
  let C := reconstructedMetric .bcc w
  obtain ⟨A,ha,hp,hS,_⟩ := symmetric_squareRoot_error C (reconstructedMetric_symm .bcc w)
    (mu : ℝ) (by norm_num [mu]) lo
  have e := congrArg Matrix.det hS
  rw [Matrix.det_mul,hc] at e
  refine ⟨A,by nlinarith,?_⟩
  rw [gram,ha,hS]

theorem strain_norms (ref : Reference) (A C : Mat) (hC : gram A=C) (n : IntVec) :
    sq (linearImage (A*cubicBasis ref) n)=quad C (linearImage (cubicBasis ref) n) ∧
    sq (cycleFrequency (A*cubicBasis ref) n)=quad C⁻¹ (cycleFrequency (cubicBasis ref) n) := by
  constructor
  · rw [linearImage,← Matrix.mulVec_mulVec,sq_mulVec_gram,hC]
    rfl
  · unfold cycleFrequency
    rw [Matrix.mul_inv_rev,Matrix.transpose_mul,← Matrix.mulVec_mulVec,sq_mulVec_gram]
    have e : gram (A⁻¹).transpose=C⁻¹ := by
      rw [gram,Matrix.transpose_transpose,Matrix.transpose_nonsing_inv,← Matrix.mul_inv_rev,← gram,hC]
    rw [e]

theorem bcc_strain_norms (A C : Mat) (hC : gram A=C) (n : IntVec) :
    sq (linearImage (A*cubicBasis .bcc) n)=quad C (linearImage (cubicBasis .bcc) n) ∧
    sq (cycleFrequency (A*cubicBasis .bcc) n)=quad C⁻¹ (cycleFrequency (cubicBasis .bcc) n) :=
  strain_norms .bcc A C hC n

end BccSharp.Coulomb.BravaisCover
