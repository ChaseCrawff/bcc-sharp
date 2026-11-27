import BccSharp.Lattice.HandoffBox

set_option autoImplicit false

/-! Cubic basis symmetries. The moves are right basis changes in
the same physical lattice, including the orientation adjustment. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover

inductive CubicMove
  | keep | swap01 | swap12 | flip1 | flip2 | invert

namespace CubicMove

def matrix : CubicMove → Mat
  | .keep => 1
  | .swap01 => !![0,1,0;1,0,0;0,0,1]
  | .swap12 => !![1,0,0;0,0,1;0,1,0]
  | .flip1 => !![1,0,0;0,-1,0;0,0,1]
  | .flip2 => !![1,0,0;0,1,0;0,0,-1]
  | .invert => -1

def permutation : CubicMove → Fin 3 → Fin 3
  | .swap01 => ![1,0,2]
  | .swap12 => ![0,2,1]
  | _ => id

def sign : CubicMove → Fin 3 → ℝ
  | .flip1 => ![1,-1,1]
  | .flip2 => ![1,1,-1]
  | .invert => fun _ => -1
  | _ => fun _ => 1

def act (m : CubicMove) (S : Mat) : Mat := m.matrix.transpose*S*m.matrix

theorem act_apply (m : CubicMove) (S : Mat) (i j : Fin 3) :
    m.act S i j=m.sign i*m.sign j*S (m.permutation i) (m.permutation j) := by
  cases m <;> fin_cases i <;> fin_cases j <;>
    norm_num [act,matrix,sign,permutation,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.one_apply,Fin.sum_univ_three] <;> ring

theorem diagonalSum_act (m : CubicMove) (S : Mat) : diagonalSum (m.act S)=diagonalSum S := by
  unfold diagonalSum
  simp only [act_apply]
  cases m <;> norm_num [sign,permutation] <;> ring

theorem diagonalSquares_act (m : CubicMove) (S : Mat) :
    (m.act S 0 0)^2+(m.act S 1 1)^2+(m.act S 2 2)^2=(S 0 0)^2+(S 1 1)^2+(S 2 2)^2 := by
  simp only [act_apply]
  cases m <;> norm_num [sign,permutation] <;> ring

theorem symmetric_act (m : CubicMove) (S : Mat) (h : S.transpose=S) :
    (m.act S).transpose=m.act S := by
  simp [act,Matrix.transpose_mul,h,mul_assoc]

theorem act_one (m : CubicMove) : m.act 1=1 := by
  ext i j
  rw [act_apply]
  cases m <;> fin_cases i <;> fin_cases j <;>
    norm_num [sign,permutation,Matrix.one_apply]

theorem act_eq_one {S : Mat} (m : CubicMove) (h : m.act S=1) : S=1 := by
  have e : m.act (m.act S)=S := by
    ext i j
    simp only [act_apply]
    cases m <;> fin_cases i <;> fin_cases j <;> norm_num [sign,permutation]
  rw [h,act_one] at e
  exact e.symm

theorem abs_det (m : CubicMove) : |m.matrix.det|=1 := by
  cases m <;> norm_num [matrix,Matrix.det_fin_three,Matrix.one_apply]

theorem normalizedStrain_act (m : CubicMove) (A : Mat) :
    normalizedStrain (gram (A*m.matrix))=m.act (normalizedStrain (gram A)) := by
  have hG : gram (A*m.matrix)=m.act (gram A) := by
    simp [gram,act,Matrix.transpose_mul,mul_assoc]
  rw [hG]
  unfold normalizedStrain
  rw [diagonalSum_act]
  ext i j
  have hI := congrFun (congrFun m.act_one i) j
  rw [act_apply] at hI
  simp only [act_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [mul_sub,← hI]
  ring

def integerIndex : Reference → CubicMove → Matrix (Fin 3) (Fin 3) ℤ
  | _, .keep => 1
  | _, .invert => -1
  | .bcc, .swap01 => !![0,1,0;1,0,0;0,0,1]
  | .bcc, .swap12 => !![1,-1,0;0,-1,0;0,2,1]
  | .bcc, .flip1 => !![1,0,0;0,-1,-1;0,0,1]
  | .bcc, .flip2 => !![1,0,1;0,1,1;0,0,-1]
  | .fcc, .swap01 => !![1,0,0;0,0,1;0,1,0]
  | .fcc, .swap12 => !![0,1,0;1,0,0;0,0,1]
  | .fcc, .flip1 => !![0,0,-1;1,1,1;-1,0,0]
  | .fcc, .flip2 => !![1,1,1;0,0,-1;0,-1,0]

theorem integerIndex_involution (ref : Reference) (m : CubicMove) :
    integerIndex ref m*integerIndex ref m=1 := by
  cases ref <;> cases m <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [integerIndex,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_three]

theorem rebase_cubic (ref : Reference) (m : CubicMove) :
    m.matrix*cubicBasis ref=cubicBasis ref*toRealMatrix (integerIndex ref m) := by
  cases ref <;> cases m <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrix,cubicBasis,toRealMatrix,integerIndex,Matrix.map_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_three] <;> ring

end CubicMove

def strainBasis (ref : Reference) (A : Mat) : Mat :=
  Constants.fccLength⁻¹ • (A*cubicBasis ref)

theorem strainBasis_move (ref : Reference) (m : CubicMove) (A : Mat) :
    strainBasis ref (A*m.matrix)=strainBasis ref A*toRealMatrix (CubicMove.integerIndex ref m) := by
  unfold strainBasis
  rw [mul_assoc,m.rebase_cubic ref,← mul_assoc,← smul_mul_assoc]

theorem strainBasis_move_lattice (ref : Reference) (m : CubicMove) (A : Mat) :
    lattice (strainBasis ref (A*m.matrix))=lattice (strainBasis ref A) := by
  rw [strainBasis_move]
  exact rebase_sameLattice _ _ _ (CubicMove.integerIndex_involution ref m)

theorem strainBasis_move_energy (ref : Reference) (m : CubicMove) (A : Mat) :
    oneSiteEnergy (strainBasis ref (A*m.matrix))=oneSiteEnergy (strainBasis ref A) := by
  rw [strainBasis_move]
  exact oneSiteEnergy_rebase _ _ _ (CubicMove.integerIndex_involution ref m)
    (CubicMove.integerIndex_involution ref m)

theorem strainBasis_move_deficit (ref : Reference) (m : CubicMove) (A : Mat) :
    oneSiteDeficit (strainBasis ref (A*m.matrix))=oneSiteDeficit (strainBasis ref A) := by
  unfold oneSiteDeficit oneSiteDefect
  rw [strainBasis_move_energy,strainBasis_move_lattice]

theorem strainBasis_move_sharp (ref : Reference) (m : CubicMove) (A : Mat) :
    Sharp (strainBasis ref (A*m.matrix)) ↔ Sharp (strainBasis ref A) := by
  unfold Sharp
  rw [strainBasis_move_deficit,strainBasis_move_lattice]

end BccSharp.Coulomb.BravaisCover
