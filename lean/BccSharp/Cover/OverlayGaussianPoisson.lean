import BccSharp.TwoSite.ScreeningIndependence
import BccSharp.Analysis.CoulombFourier

set_option autoImplicit false

/-! Shifted Gaussian Poisson summation using the general period
cell Fourier coefficients. The heat variable is the positive square
root of the parameter. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BccSharp.Coulomb
open BccSharp

def heat (s : ℝ) (x : Vec) : ℝ := Real.exp (-Real.pi*s^2*sq x)

theorem heat_nonneg (s : ℝ) (x : Vec) : 0≤heat s x := (Real.exp_pos _).le

theorem heat_lattice_bound (s : ℝ) (hs : 0<s) (B : Mat) (hB : B.det≠0) (M : ℝ) :
    ∃ w : IntVec → ℝ, Summable w ∧ ∀ n x, sq x≤M → ‖heat s (x+linearImage B n)‖≤w n := by
  obtain ⟨d,hd,coerce⟩ := matrix_coercivity B hB
  let a := Real.pi*s^2
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨fun n => Real.exp (a*M)*Real.exp (-(a*d/2)*sq (castVec n)),
    (integerGaussian_summable (show 0<a*d/2 by positivity)).mul_left _,?_⟩
  intro n x hx
  have h := shifted_sq x (linearImage B n)
  have h' : d*sq (castVec n) ≤ sq (linearImage B n) := coerce _
  have e : -(a*sq (x+linearImage B n))≤a*M-(a*d/2)*sq (castVec n) := by
    have b : d*sq (castVec n)/2-M ≤ sq (x+linearImage B n) := by linarith only [h,h',hx]
    nlinarith only [mul_le_mul_of_nonneg_left b ha.le]
  show ‖heat s (x+linearImage B n)‖ ≤ Real.exp (a*M)*Real.exp (-(a*d/2)*sq (castVec n))
  rw [Real.norm_eq_abs,abs_of_nonneg (heat_nonneg _ _),← Real.exp_add]
  unfold heat
  apply Real.exp_le_exp.mpr
  have ea : -Real.pi*s^2*sq (x+linearImage B n) = -(a*sq (x+linearImage B n)) := by
    show -Real.pi*s^2*sq (x+linearImage B n) = -(Real.pi*s^2*sq (x+linearImage B n))
    ring
  rw [ea]
  linarith only [e]

theorem heat_lattice_summable (s : ℝ) (hs : 0<s) (B : Mat) (hB : B.det≠0) (x : Vec) :
    Summable (fun n : IntVec => heat s (x+linearImage B n)) := by
  obtain ⟨w,hw,h⟩ := heat_lattice_bound s hs B hB (sq x)
  exact hw.of_norm_bounded (fun n => h n x le_rfl)

private theorem heat_lattice_continuous (s : ℝ) (hs : 0<s) (B : Mat) (hB : B.det≠0) :
    Continuous (fun x : Vec => ∑' n : IntVec, heat s (x+linearImage B n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let U : Set Vec := {y | sq y<sq x+1}
  have hU : IsOpen U := by
    have hs : Continuous sq := by unfold sq; fun_prop
    exact isOpen_lt hs continuous_const
  obtain ⟨w,hw,h⟩ := heat_lattice_bound s hs B hB (sq x+1)
  have hc : ContinuousOn (fun y : Vec => ∑' n : IntVec, heat s (y+linearImage B n)) U := by
    refine continuousOn_tsum (fun n => ?_) hw (fun n y hy => h n y hy.le)
    unfold heat sq
    fun_prop
  exact hc.continuousAt (hU.mem_nhds (by dsimp [U]; linarith))

theorem cycle_det_ne_zero (B : Mat) (hB : B.det≠0) : ((B⁻¹).transpose).det≠0 := by
  rw [Matrix.det_transpose]
  intro h
  have one := congrArg Matrix.det (Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB))
  rw [Matrix.det_mul,Matrix.det_one,h,zero_mul] at one
  exact zero_ne_one one

theorem heat_cycle_summable (s : ℝ) (hs : 0<s) (B : Mat) (hB : B.det≠0) :
    Summable (fun n : IntVec => heat s (cycleFrequency B n)) := by
  simpa only [zero_add,linearImage,cycleFrequency] using
    heat_lattice_summable s hs (B⁻¹).transpose (cycle_det_ne_zero B hB) 0

private theorem sq_eq_ewaldSq (x : Vec) : sq x = Ewald.sq x := by
  simp [sq, Ewald.sq, Fin.sum_univ_three]

private theorem heat_eq_ewald (s : ℝ) (x : Vec) :
    heat s x = Real.exp (-(Real.pi*s^2)*Ewald.sq x) := by
  rw [heat, sq_eq_ewaldSq]
  congr 1
  ring

private theorem heat_wave_integrable (s : ℝ) (hs : 0<s) (u : Vec) :
    Integrable (fun x : Vec => (heat s x : ℂ)*CoulombLaplace.wave u x) := by
  have h := CoulombLaplace.gaussian_integrable (show 0<Real.pi*s^2 by positivity) u
  have e : CoulombLaplace.gaussianPhase (Real.pi*s^2) u =
      fun x : Vec => (heat s x : ℂ)*CoulombLaplace.wave u x := by
    funext x
    rw [CoulombLaplace.gaussianPhase_factor, heat_eq_ewald]
  rwa [e] at h

private theorem heat_fourier (s : ℝ) (hs : 0<s) (u : Vec) :
    (∫ x : Vec, (heat s x : ℂ)*CoulombLaplace.wave u x) =
      (((s^3)⁻¹*heat s⁻¹ u : ℝ) : ℂ) := by
  let r := Real.sqrt Real.pi
  have hr : 0< r := Real.sqrt_pos.mpr Real.pi_pos
  have rsq : r^2=Real.pi := Real.sq_sqrt Real.pi_pos.le
  have h := CoulombLaplace.gaussian_fourier_scalar (mul_pos hr hs) u
  have e : ((r*s)^2) = Real.pi*s^2 := by rw [mul_pow,rsq]
  rw [e] at h
  simp only [CoulombLaplace.gaussianPhase_factor] at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with x
    rw [heat_eq_ewald]
  · congr 1
    have p : r^3/(r*s)^3=(s^3)⁻¹ := by field_simp [hr.ne',hs.ne']
    change (s^3)⁻¹*heat s⁻¹ u = r^3/(r*s)^3*Real.exp (-Real.pi^2*Ewald.sq u/(Real.pi*s^2))
    rw [p,heat_eq_ewald]
    congr 2
    field_simp [hs.ne',Real.pi_pos.ne']

def heatThetaAt (B : Mat) (x : Vec) (s : ℝ) : ℝ := ∑' n : IntVec, heat s (x+linearImage B n)
def heatTheta (B : Mat) (f : Vec) (s : ℝ) : ℝ := heatThetaAt B (B.mulVec f) s

def heatDual (B : Mat) (f : Vec) (s : ℝ) : ℝ :=
  ∑' n : IntVec, heat s (cycleFrequency B n)*Real.cos (2*Real.pi*dot (castVec n) f)

theorem heat_poisson_at (B : Mat) (hB : B.det≠0) (s : ℝ) (hs : 0<s) (x : Vec) :
    heatThetaAt B x s = (volumeOf B*s^3)⁻¹ *
      ∑' n : IntVec, heat s⁻¹ (cycleFrequency B n)*Real.cos (dot (dualWave B n) x) := by
  let g (y : Vec) := (heat s y : ℂ)
  let a (n : IntVec) := heat s⁻¹ (cycleFrequency B n)
  let k := (volumeOf B*s^3)⁻¹
  let L := cellPeriodize B g
  let R (y : Vec) := (k : ℂ)*cellSeries B a y
  have ha : Summable a := heat_cycle_summable s⁻¹ (inv_pos.mpr hs) B hB
  have hv : 0<volumeOf B := abs_pos.mpr hB
  have hg : Integrable g := by
    simpa only [CoulombPeriodization.wave_zero, mul_one] using heat_wave_integrable s hs 0
  have hR := cellSeries_integrable B hB ha
  have hFourier (n : IntVec) : cellFourier B hB L n=cellFourier B hB R n := by
    simp only [L, R]
    rw [cellFourier_periodize B hB g n (heat_wave_integrable s hs _),
      cellFourier_const_mul,cellSeries_fourier B hB ha]
    change (∫ y : Vec, (heat s y : ℂ)*CoulombLaplace.wave (cycleFrequency B n) y) = _
    rw [heat_fourier s hs]
    have hvc : (volumeOf B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    simp only [k, a]
    push_cast
    field_simp
  have hLi : IntegrableOn L (periodCell B hB) := cellPeriodize_integrable B hB hg
  have hRi : IntegrableOn R (periodCell B hB) := hR.const_mul (k : ℂ)
  have pL : ∀ z : periodModule B, ∀ y, L (y+z.val) = L y :=
    fun z y => cellPeriodize_periodic B g z y
  have pR : ∀ z : periodModule B, ∀ y, R (y+z.val) = R y := by
    intro z y
    simp only [R, cellSeries_periodic B hB]
  have hAE := cellFourier_unique_periodic B hB hLi hRi pL pR hFourier
  have hLc : Continuous L := by
    have e : L = fun y => (heatThetaAt B y s : ℂ) := by
      funext y
      simp only [L]
      rw [cellPeriodize_eq_integer B hB,heatThetaAt,Complex.ofReal_tsum]
    rw [e]
    exact Complex.continuous_ofReal.comp (heat_lattice_continuous s hs B hB)
  have hRc : Continuous R := continuous_const.mul (cellSeries_continuous B ha)
  have e := congrArg Complex.re (congrFun (Measure.eq_of_ae_eq hAE hLc hRc) x)
  change (cellPeriodize B g x).re=((k : ℂ)*cellSeries B a x).re at e
  rw [cellPeriodize_eq_integer B hB,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at e
  change (∑' n : IntVec, (heat s (x+linearImage B n) : ℂ)).re = _ at e
  rw [← Complex.ofReal_tsum,Complex.ofReal_re] at e
  unfold cellSeries at e
  rw [Complex.re_tsum (cellSeries_summable B ha x)] at e
  simpa only [heatThetaAt,k,a,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,cellWave_real] using e

theorem heat_poisson (B : Mat) (hB : B.det≠0) (f : Vec) (s : ℝ) (hs : 0<s) :
    heatTheta B f s=(volumeOf B*s^3)⁻¹*heatDual B f s⁻¹ := by
  rw [heatTheta,heat_poisson_at B hB s hs,heatDual]
  congr 1
  apply tsum_congr
  intro n
  rw [dualWave_cycleFrequency,dot_left_smul,cycleFrequency_dot B hB]

end BccSharp.Coulomb
