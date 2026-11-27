module

public import BccSharp.Analysis.Erfc
public import BccSharp.Analysis.KernelDerivatives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Identification of the real-space Ewald coefficient with derivatives of
the actual screened Coulomb potential erfc(2r)/r. -/
@[expose] public section
namespace BccSharp.RadialPotential
open Real Ewald Filter
open scoped Topology

theorem erfc_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt Gaussian.erfcIntegral (-(2/sqrt π)*exp (-x^2)) x := by
  have hc : Continuous (fun t : ℝ => exp (-t^2)) := by fun_prop
  have hi := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd := (hi.const_mul (2/sqrt π)).const_sub 1
  have he : Gaussian.erfcIntegral =ᶠ[𝓝 x] (fun y => 1-2/sqrt π*(∫ t in (0 : ℝ)..y,exp (-t^2))) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact Erfc.split_integral hy.le
  convert hd.congr_of_eventuallyEq he using 1; ring

theorem erfc_two_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Gaussian.erfcIntegral (2*s))
      (-4*exp (-4*r^2)*(sqrt π)⁻¹) r := by
  convert (erfc_hasDerivAt (by positivity : 0 < 2*r)).comp r ((hasDerivAt_id r).const_mul 2) using 1
  · funext s; rfl
  · rw [show -(2*r)^2 = -4*r^2 by ring]
    ring

noncomputable def screened (r : ℝ) : ℝ := Gaussian.erfcIntegral (2*r)/r
noncomputable def first (r : ℝ) : ℝ :=
  -4*exp (-4*r^2)*(sqrt π)⁻¹*r⁻¹ - Gaussian.erfcIntegral (2*r)*r⁻¹^2
noncomputable def second (r : ℝ) : ℝ :=
  32*exp (-4*r^2)*(sqrt π)⁻¹ + 8*exp (-4*r^2)*(sqrt π)⁻¹*r⁻¹^2 +
    2*Gaussian.erfcIntegral (2*r)*r⁻¹^3

theorem screened_hasDerivAt {r : ℝ} (hr : 0 < r) : HasDerivAt screened (first r) r := by
  convert (erfc_two_hasDerivAt hr).div (hasDerivAt_id r) hr.ne' using 1
  · rfl
  · dsimp [first]
    field_simp

theorem first_hasDerivAt {r : ℝ} (hr : 0 < r) : HasDerivAt first (second r) r := by
  have he := (((hasDerivAt_id r).pow 2).const_mul (-4)).exp
  have hi := (hasDerivAt_id r).inv hr.ne'
  have hg := erfc_two_hasDerivAt hr
  convert ((he.const_mul (-4*(sqrt π)⁻¹)).mul hi).sub (hg.mul (hi.pow 2)) using 1
  · funext s; dsimp [first]; ring
  · dsimp [second]
    field_simp
    ring

/-- The algebraic coefficient used by the Ewald sum is the radial Hessian of
an actual twice differentiable screened Coulomb potential. -/
theorem radial_hessian_formula {r : ℝ} (hr : 0 < r) (t d : ℝ) :
    radialHessian r t d = second r*t + (first r/r)*(d-t) := by
  dsimp [radialHessian,first,second]
  field_simp
  ring

end BccSharp.RadialPotential
