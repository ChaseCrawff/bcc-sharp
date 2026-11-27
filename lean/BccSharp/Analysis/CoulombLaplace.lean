module

public import BccSharp.Analysis.RealSpaceHessian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Gaussian integral representation of the screened Coulomb potential.
These identities prepare the Fourier-coefficient proof of the periodic
Coulomb Green function. -/
@[expose] public section
namespace BccSharp.CoulombLaplace
open Real Ewald Set MeasureTheory
open scoped BigOperators

/-- The actual erfc potential is an integral of Gaussians, at every nonzero
radius. This is the representation needed for Fourier integration. -/
theorem screened_integral {r : ℝ} (hr : 0 < r) :
    RadialPotential.screened r = (2/sqrt π)*∫ s in Ioi (2 : ℝ), exp (-s^2*r^2) := by
  have h := integral_comp_mul_right_Ioi (fun y : ℝ => exp (-y^2)) 2 hr
  simp only [smul_eq_mul] at h
  have he : (fun s : ℝ => exp (-(s*r)^2)) = fun s => exp (-s^2*r^2) := by
    funext s
    congr 1
    ring
  rw [he] at h
  rw [h]
  unfold RadialPotential.screened Gaussian.erfcIntegral
  ring

theorem potential_integral {x : Vec} (hx : 0 < Ewald.sq x) :
    RealSpaceHessian.potential x = (2/sqrt π)*∫ s in Ioi (2 : ℝ), exp (-s^2*Ewald.sq x) := by
  rw [RealSpaceHessian.potential,screened_integral (RealSpaceHessian.radius_pos hx),
    RealSpaceHessian.radius_square hx.le]

noncomputable def gaussianPhase (a : ℝ) (u x : Vec) : ℂ :=
  Complex.exp ((-a*Ewald.sq x : ℝ)-((2*π*dot u x : ℝ) : ℂ)*Complex.I)

theorem gaussian_integrable {a : ℝ} (ha : 0 < a) (u : Vec) : Integrable (gaussianPhase a u) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sum_add (b:=(a : ℂ)) (by simpa using ha)
    (fun i : Fin 3 => -2*π*Complex.I*(u i : ℂ))
  convert h using 1
  funext x
  simp only [gaussianPhase,Fin.sum_univ_three,Ewald.sq,dot,Complex.ofReal_add,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_ofNat]
  congr 1
  ring

/-- Exact three-dimensional Fourier integral of the Gaussian factor. The
complex power is retained here; it is positive real when a is positive. -/
theorem gaussian_fourier {a : ℝ} (ha : 0 < a) (u : Vec) :
    (∫ x : Vec, gaussianPhase a u x) =
      ((π : ℂ)/(a : ℂ))^(3/2 : ℂ)*Complex.exp (-((π^2*Ewald.sq u/a : ℝ) : ℂ)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sum_add (b:=(a : ℂ)) (by simpa using ha)
    (fun i : Fin 3 => -2*π*Complex.I*(u i : ℂ))
  have he : gaussianPhase a u = (fun x : Vec => Complex.exp
      (-(a : ℂ)*∑ i, (x i : ℂ)^2+∑ i, (-2*π*Complex.I*(u i : ℂ))*(x i : ℂ))) := by
    funext x
    simp only [gaussianPhase,Fin.sum_univ_three,Ewald.sq,dot,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_ofNat]
    congr 1
    ring
  rw [he,h]
  norm_num only [Fintype.card_fin]
  congr 1
  congr 1
  simp only [Fin.sum_univ_three,Ewald.sq,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_add,mul_pow,Complex.I_sq]
  ring

end BccSharp.CoulombLaplace
