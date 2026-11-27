module

public import BccSharp.Analysis.RadialPotential
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Coordinate Hessian of the actual screened Coulomb potential in three
variables, identified with every real-space coefficient of the Ewald series. -/
@[expose] public section
namespace BccSharp.RealSpaceHessian
open Real Ewald LatticeTails RadialPotential Filter
open scoped Topology

noncomputable def radius (w : Vec) : ℝ := sqrt (Ewald.sq w)
noncomputable def potential (w : Vec) : ℝ := screened (radius w)
noncomputable def gradient (w : Vec) (i : Fin 3) : ℝ := first (radius w)/radius w*w i

def basis (i : Fin 3) : Vec := fun j => if j=i then 1 else 0

theorem dot_basis (w : Vec) (i : Fin 3) : dot w (basis i) = w i := by
  simp [dot,basis]

theorem line_zero (w v : Vec) : line w v 0 = w := by funext k; simp [line]

theorem radius_pos {w : Vec} (h : 0 < Ewald.sq w) : 0 < radius w := Real.sqrt_pos.mpr h

theorem radius_square {w : Vec} (h : 0 ≤ Ewald.sq w) : radius w^2 = Ewald.sq w := Real.sq_sqrt h

theorem line_radius_hasDerivAt (w v : Vec) (t : ℝ) (h : 0 < Ewald.sq (line w v t)) :
    HasDerivAt (fun s => radius (line w v s)) (dot (line w v t) v / radius (line w v t)) t := by
  convert (line_sq_hasDerivAt w v t).sqrt h.ne' using 1
  · rfl
  · simp only [radius]
    field_simp

theorem line_potential_hasDerivAt (w v : Vec) (t : ℝ) (h : 0 < Ewald.sq (line w v t)) :
    HasDerivAt (fun s => potential (line w v s))
      (first (radius (line w v t))*dot (line w v t) v/radius (line w v t)) t := by
  convert (screened_hasDerivAt (radius_pos h)).comp t (line_radius_hasDerivAt w v t h) using 1
  · rfl
  · ring

theorem line_gradient_hasDerivAt (w v : Vec) (t : ℝ) (h : 0 < Ewald.sq (line w v t)) (i : Fin 3) :
    HasDerivAt (fun s => gradient (line w v s) i)
      ((second (radius (line w v t))*radius (line w v t)-first (radius (line w v t))) *
          dot (line w v t) v/radius (line w v t)^3 * line w v t i +
        first (radius (line w v t))/radius (line w v t)*v i) t := by
  have hr := line_radius_hasDerivAt w v t h
  have hf := (first_hasDerivAt (radius_pos h)).comp t hr
  convert (hf.div hr (radius_pos h).ne').mul (line_component_hasDerivAt w v t i) using 1
  · rfl
  · simp only [Function.comp_apply,Pi.div_apply]
    field_simp [(radius_pos h).ne']

/-- An actual first coordinate derivative, with no formal Hessian formula in its definition. -/
noncomputable def coordinatePartial (w : Vec) (i : Fin 3) : ℝ :=
  deriv (fun s => potential (line w (basis i) s)) 0

/-- The actual iterated coordinate derivative of the screened potential. -/
noncomputable def hessian (w : Vec) (i j : Fin 3) : ℝ :=
  deriv (fun t => coordinatePartial (line w (basis j) t) i) 0

theorem coordinatePartial_eq {w : Vec} (h : 0 < Ewald.sq w) (i : Fin 3) : coordinatePartial w i = gradient w i := by
  have hd := (line_potential_hasDerivAt w (basis i) 0 (by simpa only [line_zero] using h)).deriv
  simpa only [coordinatePartial,line_zero,dot_basis,gradient,mul_div_assoc,div_mul_eq_mul_div] using hd

theorem hessian_formula {w : Vec} (h : 0 < Ewald.sq w) (i j : Fin 3) :
    hessian w i j = radialHessian (radius w) (w i*w j/Ewald.sq w) (if i=j then 1 else 0) := by
  have he : (fun t => coordinatePartial (line w (basis j) t) i) =ᶠ[𝓝 0]
      (fun t => gradient (line w (basis j) t) i) := by
    have hc : Continuous (fun t : ℝ => Ewald.sq (line w (basis j) t)) := by
      unfold Ewald.sq line
      fun_prop
    have hc0 : ContinuousAt (fun t : ℝ => Ewald.sq (line w (basis j) t)) 0 := hc.continuousAt
    have hz : 0 < Ewald.sq (line w (basis j) 0) := by simpa only [line_zero] using h
    have hh := hc0.eventually (eventually_gt_nhds hz)
    filter_upwards [hh] with t ht
    exact coordinatePartial_eq ht i
  have hd := (line_gradient_hasDerivAt w (basis j) 0 (by simpa only [line_zero] using h) i).congr_of_eventuallyEq he
  rw [hessian,hd.deriv,radial_hessian_formula (radius_pos h)]
  simp only [line_zero,dot_basis,basis]
  rw [← radius_square h.le]
  field_simp [(radius_pos h).ne']
  ring

/-- The coefficient used in the real-space lattice sum is the actual Hessian
at the physical lattice vector z/2. -/
theorem phi_is_hessian {z : LatticeTails.Triple} (hz : z ≠ 0) (i j : Fin 3) :
    phi z i j = hessian ((1/2 : ℝ) • coord z) i j := by
  have hn : 0 < normSq z := lt_of_lt_of_le (by norm_num) (normSq_ge_one hz)
  have hw : 0 < Ewald.sq ((1/2 : ℝ) • coord z) := by rw [sq_smul,sq_coord]; positivity
  have hr : radius ((1/2 : ℝ) • coord z) = sqrt (normSq z)/2 := by
    unfold radius
    rw [sq_smul,sq_coord]
    have hsq := Real.sq_sqrt hn.le
    have hp := Real.sqrt_nonneg (Ewald.sq ((1/2 : ℝ) • coord z))
    have hs := radius_square hw.le
    dsimp [radius] at hs
    rw [sq_smul,sq_coord] at hs hp
    nlinarith [Real.sqrt_nonneg (normSq z)]
  rw [hessian_formula hw,hr,phi]
  congr 1
  simp only [Pi.smul_apply,smul_eq_mul,sq_smul,sq_coord]
  field_simp

end BccSharp.RealSpaceHessian
