import BccSharp.Lattice.LocalObjective

set_option autoImplicit false

/-! Finite cubic averaging for local first derivatives. Sign moves
with determinant minus one have the same conjugation as their proper
negatives. Exact physical ray differentiability is a separate input. -/

noncomputable section
open scoped Topology

namespace BccSharp.Coulomb.BravaisCover

private def diagonalPart (S : Mat) : Mat := Matrix.diagonal (fun i => S i i)

private theorem signAverage (S : Mat) :
    S+CubicMove.flip1.act S+CubicMove.flip2.act S+
      CubicMove.flip1.act (CubicMove.flip2.act S)=(4 : ℝ) • diagonalPart S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation,diagonalPart,
      Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] <;> ring

private theorem permutationAverage (S : Mat) :
    diagonalPart S+CubicMove.swap01.act (CubicMove.swap12.act (diagonalPart S))+
      CubicMove.swap12.act (CubicMove.swap01.act (diagonalPart S))=diagonalSum S • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation,diagonalPart,diagonalSum,
      Matrix.diagonal_apply,Matrix.one_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] <;> ring

theorem cubic_invariant_linear_zero (D : Mat →ₗ[ℝ] ℝ)
    (invariant : ∀ m : CubicMove, ∀ S : Mat, D (m.act S)=D S)
    (S : Mat) (traceZero : diagonalSum S=0) : D S=0 := by
  have shear := congrArg D (signAverage S)
  simp only [map_add,map_smul,smul_eq_mul,invariant] at shear
  have diag : D (diagonalPart S)=D S := by linarith
  have cyclic := congrArg D (permutationAverage S)
  simp only [map_add,map_smul,smul_eq_mul,invariant,traceZero,zero_mul] at cyclic
  linarith

theorem cubic_invariant_linear_zero_on_strain (D : Mat →ₗ[ℝ] ℝ)
    (invariant : ∀ m : CubicMove, ∀ S : Mat, S.transpose=S → diagonalSum S=0 → D (m.act S)=D S)
    (S : Mat) (symm : S.transpose=S) (traceZero : diagonalSum S=0) : D S=0 := by
  have sign := congrArg D (signAverage S)
  have e₁ := invariant .flip1 S symm traceZero
  have e₂ := invariant .flip2 S symm traceZero
  have e₃ := invariant .flip1 (CubicMove.flip2.act S) (CubicMove.flip2.symmetric_act S symm)
    ((CubicMove.flip2.diagonalSum_act S).trans traceZero)
  simp only [map_add,map_smul,smul_eq_mul,e₁,e₂,e₃] at sign
  let E := diagonalPart S
  have Es : E.transpose=E := by simp [E,diagonalPart]
  have Et : diagonalSum E=0 := by simpa [E,diagonalPart,diagonalSum] using traceZero
  have p₁ := invariant .swap01 (CubicMove.swap12.act E) (CubicMove.swap12.symmetric_act E Es)
    ((CubicMove.swap12.diagonalSum_act E).trans Et)
  have p₂ := invariant .swap12 (CubicMove.swap01.act E) (CubicMove.swap01.symmetric_act E Es)
    ((CubicMove.swap01.diagonalSum_act E).trans Et)
  have perm := congrArg D (permutationAverage E)
  have d : diagonalPart E=E := by simp [E,diagonalPart]
  rw [d] at perm
  have e₄ := invariant .swap01 E Es Et
  have e₅ := invariant .swap12 E Es Et
  simp only [map_add,map_smul,smul_eq_mul,p₁,p₂,e₄,e₅,Et,zero_mul] at perm
  linarith

/-- This takes actual ray derivative identifications. Equality of the
physical objective on cubic-equivalent rays forces its linear derivative
to vanish on the traceless strain space. -/
theorem cubic_ray_stationary (F : Mat → ℝ) (D : Mat →ₗ[ℝ] ℝ)
    (differentiate : ∀ S : Mat, HasDerivAt (fun t : ℝ => F (t • S)) (D S) 0)
    (invariant : ∀ m : CubicMove, ∀ S : Mat,
      (fun t : ℝ => F (t • S)) =ᶠ[𝓝 0] (fun t : ℝ => F (t • m.act S)))
    (S : Mat) (traceZero : diagonalSum S=0) : HasDerivAt (fun t : ℝ => F (t • S)) 0 0 := by
  have inv (m : CubicMove) (A : Mat) : D (m.act A)=D A :=
    ((differentiate (m.act A)).congr_of_eventuallyEq (invariant m A)).unique (differentiate A)
  have hd := differentiate S
  rwa [cubic_invariant_linear_zero D inv S traceZero] at hd

end BccSharp.Coulomb.BravaisCover
