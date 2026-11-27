module

public import BccSharp.Analysis.LatticeNeighborhood
public import BccSharp.Analysis.ReciprocalSeries

/-! The real-space periodic Hessian at noncolliding lattice differences.
Both coordinate derivatives are taken on the actual infinite potential. -/
@[expose] public section
namespace BccSharp.RealSpaceSeries
open Real Ewald LatticeTails LatticeNeighborhood Filter
open RealSpaceHessian (basis dot_basis line_zero radius)
open ReciprocalSeries (mask summable_mask)
open scoped Topology

noncomputable def potential (P : Triple → Prop) (x : Vec) : ℝ :=
  ∑' z, mask P (fun z => RealSpaceHessian.potential (shifted x z)) z
noncomputable def gradient (P : Triple → Prop) (x : Vec) (i : Fin 3) : ℝ :=
  ∑' z, mask P (fun z => RealSpaceHessian.gradient (shifted x z) i) z
noncomputable def hessian (P : Triple → Prop) (x : Vec) (i j : Fin 3) : ℝ :=
  deriv (fun t => deriv (fun s => potential P (line (line x (basis j) t) (basis i) s)) 0) 0

theorem shifted_line (x v : Vec) (t : ℝ) (z : Triple) :
    shifted (line x v t) z = line (shifted x z) v t := by
  funext k
  simp only [shifted,line,Pi.add_apply]
  ring

theorem square_pos {L z : Triple} (hz : L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) :
    0 < Ewald.sq (shifted x z) := by
  have hg := gap hz hx
  have hs := RealSpaceHessian.radius_square (sq_nonnegative (shifted x z))
  nlinarith

theorem mode_line_deriv (x : Vec) (z : Triple) (i : Fin 3) (t : ℝ)
    (hs : 0 < Ewald.sq (shifted (line x (basis i) t) z)) :
    HasDerivAt (fun s => RealSpaceHessian.potential (shifted (line x (basis i) s) z))
      (RealSpaceHessian.gradient (shifted (line x (basis i) t) z) i) t := by
  simp_rw [shifted_line] at hs ⊢
  convert RealSpaceHessian.line_potential_hasDerivAt (shifted x z) (basis i) t hs using 1
  simp only [RealSpaceHessian.gradient,dot_basis]
  ring

theorem gradient_line_deriv (x : Vec) (z : Triple) (i j : Fin 3) (t : ℝ)
    (hs : 0 < Ewald.sq (shifted (line x (basis j) t) z)) :
    HasDerivAt (fun s => RealSpaceHessian.gradient (shifted (line x (basis j) s) z) i)
      (RealSpaceHessian.hessian (shifted (line x (basis j) t) z) i j) t := by
  simp_rw [shifted_line] at hs ⊢
  convert RealSpaceHessian.line_gradient_hasDerivAt (shifted x z) (basis j) t hs i using 1
  rw [RealSpaceHessian.hessian_formula hs,RadialPotential.radial_hessian_formula (RealSpaceHessian.radius_pos hs)]
  simp only [dot_basis,basis]
  rw [← RealSpaceHessian.radius_square hs.le]
  field_simp [(RealSpaceHessian.radius_pos hs).ne']
  ring

theorem potential_summable {P : Triple → Prop} {L : Triple}
    (hP : ∀ z, P z → L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) :
    Summable (mask P (fun z => RealSpaceHessian.potential (shifted x z))) := by
  classical
  apply ((majorant_summable L).mul_left 8).of_norm_bounded
  intro z
  simp only [mask,Real.norm_eq_abs]
  split_ifs with hz
  · exact LatticeNeighborhood.potential_bound (hP z hz) hx
  · simp only [abs_zero]; exact mul_nonneg (by norm_num) (majorant_nonneg _ _)

theorem gradient_summable {P : Triple → Prop} {L : Triple}
    (hP : ∀ z, P z → L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) (i : Fin 3) :
    Summable (mask P (fun z => RealSpaceHessian.gradient (shifted x z) i)) := by
  classical
  apply ((majorant_summable L).mul_left 48).of_norm_bounded
  intro z
  simp only [mask,Real.norm_eq_abs]
  split_ifs with hz
  · exact LatticeNeighborhood.gradient_bound (hP z hz) hx i
  · simp only [abs_zero]; exact mul_nonneg (by norm_num) (majorant_nonneg _ _)

theorem potential_hasDerivAt {P : Triple → Prop} {L : Triple}
    (hP : ∀ z, P z → L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) (i : Fin 3) :
    HasDerivAt (fun t => potential P (line x (basis i) t)) (gradient P x i) 0 := by
  classical
  obtain ⟨r,hr,hline⟩ := line_neighborhood hx i
  have hd (z : Triple) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) r) :
      HasDerivAt (fun s => mask P (fun z => RealSpaceHessian.potential (shifted (line x (basis i) s) z)) z)
        (mask P (fun z => RealSpaceHessian.gradient (shifted (line x (basis i) t) z) i) z) t := by
    by_cases hz : P z
    · simpa only [mask,ite_eq_left hz] using mode_line_deriv x z i t (square_pos (hP z hz) (hline t ht))
    · simpa only [mask,ite_eq_right hz] using hasDerivAt_const t (0 : ℝ)
  have hb (z : Triple) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) r) :
      ‖mask P (fun z => RealSpaceHessian.gradient (shifted (line x (basis i) t) z) i) z‖ ≤
        48*majorant L z := by
    simp only [mask,Real.norm_eq_abs]
    split_ifs with hz
    · exact LatticeNeighborhood.gradient_bound (hP z hz) (hline t ht) i
    · simp only [abs_zero]; exact mul_nonneg (by norm_num) (majorant_nonneg _ _)
  have hz : (0 : ℝ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hp := potential_summable hP (hline 0 hz)
  have hh := hasDerivAt_tsum_of_isPreconnected ((majorant_summable L).mul_left 48)
    Metric.isOpen_ball (convex_ball (0 : ℝ) r).isPreconnected hd hb hz hp hz
  simpa only [potential,gradient,line_zero] using hh

theorem gradient_hasDerivAt {P : Triple → Prop} {L : Triple}
    (hP : ∀ z, P z → L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) (i j : Fin 3) :
    HasDerivAt (fun t => gradient P (line x (basis j) t) i)
      (∑' z, mask P (fun z => RealSpaceHessian.hessian (shifted x z) i j) z) 0 := by
  classical
  obtain ⟨r,hr,hline⟩ := line_neighborhood hx j
  have hd (z : Triple) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) r) :
      HasDerivAt (fun s => mask P (fun z => RealSpaceHessian.gradient (shifted (line x (basis j) s) z) i) z)
        (mask P (fun z => RealSpaceHessian.hessian (shifted (line x (basis j) t) z) i j) z) t := by
    by_cases hz : P z
    · simpa only [mask,ite_eq_left hz] using gradient_line_deriv x z i j t (square_pos (hP z hz) (hline t ht))
    · simpa only [mask,ite_eq_right hz] using hasDerivAt_const t (0 : ℝ)
  have hb (z : Triple) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) r) :
      ‖mask P (fun z => RealSpaceHessian.hessian (shifted (line x (basis j) t) z) i j) z‖ ≤
        800*majorant L z := by
    simp only [mask,Real.norm_eq_abs]
    split_ifs with hz
    · exact LatticeNeighborhood.hessian_bound (hP z hz) (hline t ht) i j
    · simp only [abs_zero]; exact mul_nonneg (by norm_num) (majorant_nonneg _ _)
  have hz : (0 : ℝ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hp := gradient_summable hP (hline 0 hz) i
  have hh := hasDerivAt_tsum_of_isPreconnected ((majorant_summable L).mul_left 800)
    Metric.isOpen_ball (convex_ball (0 : ℝ) r).isPreconnected hd hb hz hp hz
  simpa only [gradient,line_zero] using hh

/-- Actual second coordinate derivative of the infinite real-space potential. -/
theorem hessian_formula {P : Triple → Prop} {L : Triple}
    (hP : ∀ z, P z → L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) (i j : Fin 3) :
    hessian P x i j = ∑' z, mask P (fun z => RealSpaceHessian.hessian (shifted x z) i j) z := by
  obtain ⟨r,hr,hline⟩ := line_neighborhood hx j
  have he : (fun t => deriv (fun s => potential P (line (line x (basis j) t) (basis i) s)) 0) =ᶠ[𝓝 0]
      (fun t => gradient P (line x (basis j) t) i) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
    exact (potential_hasDerivAt hP (hline t ht) i).deriv
  exact ((gradient_hasDerivAt hP hx i j).congr_of_eventuallyEq he).deriv

/-- At a perfect lattice difference, the periodic real-space Hessian is exactly
its lattice sum of the already identified screened coefficients. -/
theorem hessian_at_lattice {P : Triple → Prop} {L : Triple}
    (hP : ∀ z, P z → L+z ≠ 0) (i j : Fin 3) :
    hessian P (center L) i j = ∑' z, mask P (fun z => phi (L+z) i j) z := by
  classical
  rw [hessian_formula hP (center_mem L)]
  apply tsum_congr
  intro z
  simp only [mask]
  split_ifs with hz
  · rw [RealSpaceHessian.phi_is_hessian (hP z hz)]
    congr 1
    funext k
    simp only [shifted,center,Pi.add_apply,Pi.smul_apply,smul_eq_mul,coord_add]
    ring
  · rfl

end BccSharp.RealSpaceSeries
