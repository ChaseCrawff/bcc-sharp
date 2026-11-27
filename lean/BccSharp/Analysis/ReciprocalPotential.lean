module

public import BccSharp.Analysis.RealSpaceHessian

/-! Actual coordinate derivatives of each Gaussian-damped reciprocal Coulomb
Fourier mode, with the normalization used by the natural-unit Ewald matrix. -/
@[expose] public section
namespace BccSharp.ReciprocalPotential
open Real Ewald
open RealSpaceHessian (basis dot_basis line_zero)

noncomputable def amplitude (w : Vec) : ℝ := 8*π*exp (-beta*Ewald.sq w)/(4*π^2*Ewald.sq w)
noncomputable def phase (w x : Vec) : ℝ := 2*π*dot w x
noncomputable def potential (w x : Vec) : ℝ := amplitude w*cos (phase w x)
noncomputable def gradient (w x : Vec) (i : Fin 3) : ℝ := -amplitude w*sin (phase w x)*(2*π*w i)

theorem phase_hasDerivAt (w x v : Vec) (t : ℝ) :
    HasDerivAt (fun s => phase w (line x v s)) (2*π*dot w v) t := by
  convert ((((line_component_hasDerivAt x v t 0).const_mul (w 0)).add
    ((line_component_hasDerivAt x v t 1).const_mul (w 1))).add
    ((line_component_hasDerivAt x v t 2).const_mul (w 2))).const_mul (2*π) using 1
  · funext s; simp [phase,dot,Fin.sum_univ_three]
  · simp [dot,Fin.sum_univ_three]

theorem potential_hasDerivAt (w x : Vec) (i : Fin 3) :
    HasDerivAt (fun t => potential w (line x (basis i) t)) (gradient w x i) 0 := by
  convert ((phase_hasDerivAt w x (basis i) 0).cos).const_mul (amplitude w) using 1
  · rfl
  · simp only [gradient,line_zero,dot_basis]
    ring

theorem gradient_hasDerivAt (w x : Vec) (i j : Fin 3) :
    HasDerivAt (fun t => gradient w (line x (basis j) t) i)
      (-amplitude w*cos (phase w x)*(2*π*w i)*(2*π*w j)) 0 := by
  convert (((phase_hasDerivAt w x (basis j) 0).sin).const_mul (-amplitude w)).mul_const (2*π*w i) using 1
  · rfl
  · simp only [line_zero,dot_basis]
    ring

noncomputable def coordinatePartial (w x : Vec) (i : Fin 3) : ℝ :=
  deriv (fun t => potential w (line x (basis i) t)) 0
noncomputable def hessian (w x : Vec) (i j : Fin 3) : ℝ :=
  deriv (fun t => coordinatePartial w (line x (basis j) t) i) 0

theorem coordinatePartial_eq (w x : Vec) (i : Fin 3) : coordinatePartial w x i = gradient w x i :=
  (potential_hasDerivAt w x i).deriv

/-- The reciprocal kernel is the negative normalized Hessian coefficient
of the actual reciprocal Fourier mode. -/
theorem hessian_formula (w x : Vec) (i j : Fin 3) :
    hessian w x i j = -(8*π)*kernel w i j*cos (phase w x) := by
  simp_rw [hessian,coordinatePartial_eq]
  rw [(gradient_hasDerivAt w x i j).deriv]
  simp only [amplitude,kernel]
  field_simp
  ring

end BccSharp.ReciprocalPotential
