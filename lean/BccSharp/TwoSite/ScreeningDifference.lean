import BccSharp.TwoSite.GeneralSummability
import BccSharp.TwoSite.PeriodFourier
import BccSharp.TwoSite.ScreenedTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

/-! Analytic lemmas for the *difference* of two screenings. At the
origin the interval of Gaussians supplies the removable value, so Fourier
uniqueness can be applied to globally continuous functions. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace BccSharp.Coulomb
open BccSharp

def screenedDifference (α β : ℝ) (x : Vec) : ℝ :=
  (2/Real.sqrt Real.pi) * ∫ s in α..β, Real.exp (-(s^2*sq x))

theorem screenedDifference_continuous (α β : ℝ) : Continuous (screenedDifference α β) := by
  have h : Continuous (Function.uncurry (fun (x : Vec) (s : ℝ) => Real.exp (-(s^2*sq x)))) := by
    unfold Function.uncurry sq
    fun_prop
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h α β)

theorem screenedDifference_zero (α β : ℝ) :
    screenedDifference α β 0 = (2/Real.sqrt Real.pi)*(β-α) := by
  simp [screenedDifference, sq]

theorem screenedDifference_eq_sub (α β : ℝ) (hab : α ≤ β) (x : Vec) (hx : x ≠ 0) :
    screenedDifference α β x = screened α x - screened β x := by
  have hs : 0 < sq x := lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff x).mp hx))
  let g (s : ℝ) := Real.exp (-(s^2*sq x))
  have hg : Integrable g := by
    simpa [g, mul_comm (sq x), neg_mul] using integrable_exp_neg_mul_sq hs
  have hd : Disjoint (Ioc α β) (Ioi β) := by
    refine Set.disjoint_left.mpr ?_
    intro s h₁ h₂
    exact (not_lt_of_ge h₁.2) h₂
  have hu : Ioc α β ∪ Ioi β = Ioi α := by
    ext s
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hab.trans_lt h
    · intro h
      exact (le_or_gt s β).elim (fun h' => Or.inl ⟨h,h'⟩) Or.inr
  have hi := setIntegral_union hd measurableSet_Ioi
    (hg.integrableOn (s := Ioc α β)) (hg.integrableOn (s := Ioi β))
  rw [hu] at hi
  rw [screenedDifference, intervalIntegral.integral_of_le hab, screened_gaussian_integral α x hs,
    screened_gaussian_integral β x hs]
  simp only [neg_mul]
  change (2/Real.sqrt Real.pi)*(∫ s in Ioc α β, g s) =
    (2/Real.sqrt Real.pi)*(∫ s in Ioi α, g s)-(2/Real.sqrt Real.pi)*(∫ s in Ioi β, g s)
  rw [hi]
  ring

theorem screenedDifference_bound (α β : ℝ) (ha : 0 < α) (hab : α ≤ β) (x : Vec) :
    ‖screenedDifference α β x‖ ≤
      (2/Real.sqrt Real.pi)*(β-α)*Real.exp (-(α^2*sq x)) := by
  unfold screenedDifference
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2/Real.sqrt Real.pi : ℝ))]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := α) (b := β) (C := Real.exp (-(α^2*sq x))) (f := fun s => Real.exp (-(s^2*sq x))) (by
        intro s hs
        rw [Set.uIoc_of_le hab] at hs
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ ha.le hs.1.le 2) (sq_nonnegative _)))
  simpa [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using he

theorem screenedDifference_lattice_bound (α β : ℝ) (ha : 0 < α) (hab : α ≤ β)
    (B : Mat) (hB : B.det ≠ 0) (M : ℝ) :
    ∃ w : IntVec → ℝ, Summable w ∧
      ∀ n x, sq x ≤ M → ‖screenedDifference α β (x+linearImage B n)‖ ≤ w n := by
  obtain ⟨c, hc, coerce⟩ := matrix_coercivity B hB
  let C := (2/Real.sqrt Real.pi)*(β-α)
  refine ⟨fun n => (C*Real.exp (α^2*M))*Real.exp (-(α^2*c/2)*sq (castVec n)),
    (integerGaussian_summable (show 0 < α^2*c/2 by positivity)).mul_left _, ?_⟩
  intro n x hx
  have hs := shifted_sq x (linearImage B n)
  have hco : c*sq (castVec n) ≤ sq (linearImage B n) := coerce _
  have ht : -(α^2*sq (x+linearImage B n)) ≤ α^2*M-(α^2*c/2)*sq (castVec n) := by
    have h := mul_le_mul_of_nonneg_left
      (show c*sq (castVec n)/2-M ≤ sq (x+linearImage B n) by linarith) (sq_nonneg α)
    linarith
  calc
    _ ≤ C*Real.exp (-(α^2*sq (x+linearImage B n))) := screenedDifference_bound α β ha hab _
    _ ≤ C*Real.exp (α^2*M-(α^2*c/2)*sq (castVec n)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht) (by dsimp [C]; positivity)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

theorem screenedDifference_lattice_summable (α β : ℝ) (ha : 0 < α) (hab : α ≤ β)
    (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    Summable (fun n : IntVec => screenedDifference α β (x+linearImage B n)) := by
  obtain ⟨w, hw, h⟩ := screenedDifference_lattice_bound α β ha hab B hB (sq x)
  exact hw.of_norm_bounded fun n => h n x le_rfl

theorem screenedDifference_lattice_continuous (α β : ℝ) (ha : 0 < α) (hab : α ≤ β)
    (B : Mat) (hB : B.det ≠ 0) :
    Continuous (fun x => ∑' n : IntVec, screenedDifference α β (x+linearImage B n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let U : Set Vec := {y | sq y < sq x+1}
  have hU : IsOpen U := by
    have hs : Continuous sq := by unfold sq; fun_prop
    exact isOpen_lt hs continuous_const
  obtain ⟨w, hw, h⟩ := screenedDifference_lattice_bound α β ha hab B hB (sq x+1)
  have hc : ContinuousOn (fun y => ∑' n : IntVec, screenedDifference α β (y+linearImage B n)) U := by
    apply continuousOn_tsum (fun n => ((screenedDifference_continuous α β).comp
      (continuous_id.add continuous_const)).continuousOn) hw
    intro n y hy
    exact h n y (le_of_lt hy)
  exact hc.continuousAt (hU.mem_nhds (by dsimp [U]; linarith))

theorem screenedDifference_phase_integrable (α β : ℝ) (ha : 0 < α) (hb : 0 < β) (hab : α ≤ β)
    (u : Vec) :
    Integrable (fun x => (screenedDifference α β x : ℂ)*CoulombLaplace.wave u x) := by
  apply ((screenedPhaseAt_integrable α ha u).sub (screenedPhaseAt_integrable β hb u)).congr
  filter_upwards [volume.ae_ne (0 : Vec)] with x hx
  simp [screenedPhaseAt, screenedDifference_eq_sub α β hab x hx, sub_mul]

theorem screenedDifference_phase_integral (α β : ℝ) (ha : 0 < α) (hb : 0 < β) (hab : α ≤ β)
    (u : Vec) :
    (∫ x : Vec, (screenedDifference α β x : ℂ)*CoulombLaplace.wave u x) =
      (∫ x : Vec, screenedPhaseAt α u x) - (∫ x : Vec, screenedPhaseAt β u x) := by
  rw [← integral_sub (screenedPhaseAt_integrable α ha u) (screenedPhaseAt_integrable β hb u)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : Vec)] with x hx
  simp [screenedPhaseAt, screenedDifference_eq_sub α β hab x hx, sub_mul]

end BccSharp.Coulomb
