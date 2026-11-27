import BccSharp.Lattice.StrictLeaves
import BccSharp.Analysis.RadialPotential

set_option autoImplicit false

/-! Scalar value/gradient/curvature enclosure used for the Lattice
mean-value and Taylor routes. The recurrence is proved by differentiating
the actual two kernels. All numerical inputs are rational witnesses. -/

noncomputable section
open scoped Topology

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

inductive KernelKind where
  | half | one
  deriving DecidableEq, Repr

def KernelKind.power : KernelKind → ℚ
  | .half => 1/2
  | .one => 1

def kernelValue (k : KernelKind) (t : ℝ) : ℝ := gKernel (k.power : ℝ) t
def kernelSlope (k : KernelKind) (t : ℝ) : ℝ :=
  -(Real.exp (-t)+(k.power : ℝ)*kernelValue k t)/t
def kernelCurvature (k : KernelKind) (t : ℝ) : ℝ :=
  (Real.exp (-t)-((k.power : ℝ)+1)*kernelSlope k t)/t

theorem kernelValue_hasDerivAt (k : KernelKind) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (kernelValue k) (kernelSlope k t) t := by
  cases k with
  | half =>
      have hr := Real.sqrt_pos.mpr ht
      have hh := Real.hasDerivAt_sqrt ht.ne'
      have hg := (RadialPotential.erfc_hasDerivAt hr).comp t hh
      have hd := (hg.const_mul (Real.sqrt Real.pi)).div hh hr.ne'
      have he : kernelValue .half =ᶠ[𝓝 t]
          (fun s => Real.sqrt Real.pi*Gaussian.erfcIntegral (Real.sqrt s)/Real.sqrt s) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        simpa [kernelValue,KernelKind.power] using halfKernel_formula hs
      convert hd.congr_of_eventuallyEq he using 1
      unfold kernelSlope
      simp only [kernelValue,KernelKind.power,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,
        Function.comp_apply]
      rw [halfKernel_formula ht,Real.sq_sqrt ht.le]
      field_simp [ht.ne',hr.ne',(Real.sqrt_pos.mpr Real.pi_pos).ne']
      ring
  | one =>
      have hd := ((hasDerivAt_id t).neg.exp).div (hasDerivAt_id t) ht.ne'
      have he : kernelValue .one =ᶠ[𝓝 t] (fun s => Real.exp (-s)/s) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        simpa [kernelValue,KernelKind.power] using gKernel_one hs
      convert hd.congr_of_eventuallyEq he using 1
      simp only [kernelSlope,kernelValue,KernelKind.power,Rat.cast_one,Pi.neg_apply,id_eq]
      rw [gKernel_one ht]
      field_simp [ht.ne']
      ring

theorem kernelSlope_hasDerivAt (k : KernelKind) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (kernelSlope k) (kernelCurvature k t) t := by
  have he := (hasDerivAt_id t).neg.exp
  have hh := (kernelValue_hasDerivAt k ht).const_mul (k.power : ℝ)
  convert ((he.add hh).neg.div (hasDerivAt_id t) ht.ne') using 1
  · funext s
    rfl
  · unfold kernelCurvature kernelSlope
    simp only [Pi.add_apply,Pi.neg_apply,id_eq]
    field_simp [ht.ne']
    ring

inductive KernelWitness where
  | half (atLower atUpper : ErfcSeriesProposal) (exponential : ExpBounds.Witness)
  | one (exponential : ExpBounds.Witness)

def KernelWitness.kind : KernelWitness → KernelKind
  | .half _ _ _ => .half
  | .one _ => .one

def KernelWitness.exponentialWitness : KernelWitness → ExpBounds.Witness
  | .half _ _ e | .one e => e

def KernelWitness.extraCheck (w : KernelWitness) (t : Ball) : Bool :=
  match w with
  | .one _ => true
  | .half wl wu _ =>
    (Constants.piRoot.check Constants.piInput && decide Constants.piInverseRoot.invertible) &&
      (wl.check t.lo Constants.piInverseRoot && wu.check t.hi Constants.piInverseRoot)

def KernelWitness.check (w : KernelWitness) (t : Ball) : Bool :=
  (t.positive && decide t.invertible) &&
    (w.exponentialWitness.check t.neg && w.extraCheck t)

structure KernelBall where
  value : Ball
  slope : Ball
  curvature : Ball

def KernelWitness.valueBall (w : KernelWitness) (t : Ball) : Ball :=
  match w with
  | .one e => e.result.mul t.inv
  | .half wl wu _ => ballOf (halfAt t.hi wu).lo (halfAt t.lo wl).hi

def KernelWitness.evaluate (w : KernelWitness) (t : Ball) : KernelBall :=
  let v := w.valueBall t
  let exp := w.exponentialWitness.result
  let u := ((exp.add ((Ball.exact w.kind.power).mul v)).neg).mul t.inv
  ⟨v,u,(exp.sub ((Ball.exact (w.kind.power+1)).mul u)).mul t.inv⟩

theorem kernelValue_enclosure (w : KernelWitness) {t : Ball} {x : ℝ} (hx : t.Contains x)
    (ok : w.check t = true) : (w.valueBall t).Contains (kernelValue w.kind x) := by
  have h := Bool.and_eq_true_iff.mp ok
  have hp := Bool.and_eq_true_iff.mp h.1
  have h0 := Ball.positive_sound hp.1 hx
  have hinv := Ball.contains_inv (of_decide_eq_true hp.2) hx
  have he := Bool.and_eq_true_iff.mp h.2
  have hex := ExpBounds.Witness.sound he.1 (Ball.contains_neg hx)
  cases w with
  | one e =>
    show (e.result.mul t.inv).Contains (kernelValue .one x)
    rw [show kernelValue (.one : KernelKind) x = Real.exp (-x)/x by
      simpa [kernelValue,KernelKind.power] using gKernel_one h0,div_eq_mul_inv]
    exact Ball.contains_mul hex hinv
  | half wl wu e =>
    have hb := Bool.and_eq_true_iff.mp he.2
    have hroot := Bool.and_eq_true_iff.mp hb.1
    have herfc := Bool.and_eq_true_iff.mp hb.2
    have hends : (t.lo : ℝ) ≤ x ∧ x ≤ (t.hi : ℝ) := by
      simpa [Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints t x).mp hx
    have hlo : (0 : ℝ) < t.lo := by exact_mod_cast (of_decide_eq_true hp.1 : 0 < t.lo)
    have hhi : (0 : ℝ) < t.hi := h0.trans_le hends.2
    have hl := halfAt_sound t.lo hlo wl hroot.1 (of_decide_eq_true hroot.2) herfc.1
    have hu := halfAt_sound t.hi hhi wu hroot.1 (of_decide_eq_true hroot.2) herfc.2
    have hl' : gKernel (1/2) (t.lo : ℝ) ≤ ((halfAt t.lo wl).hi : ℝ) := by
      simpa [Ball.hi] using ((SpecialFunctions.contains_iff_endpoints _ _).mp hl).2
    have hu' : ((halfAt t.hi wu).lo : ℝ) ≤ gKernel (1/2) (t.hi : ℝ) := by
      simpa [Ball.lo] using ((SpecialFunctions.contains_iff_endpoints _ _).mp hu).1
    have out := ballOf_sound ⟨hu'.trans (halfKernel_decreasing h0 hends.2),
      (halfKernel_decreasing hlo hends.1).trans hl'⟩
    simpa [KernelWitness.valueBall,KernelWitness.kind,kernelValue,KernelKind.power] using out

theorem KernelWitness.evaluate_sound (w : KernelWitness) {t : Ball} {x : ℝ} (hx : t.Contains x)
    (ok : w.check t = true) :
    ((w.evaluate t).value).Contains (kernelValue w.kind x) ∧
    ((w.evaluate t).slope).Contains (kernelSlope w.kind x) ∧
    ((w.evaluate t).curvature).Contains (kernelCurvature w.kind x) := by
  have h := Bool.and_eq_true_iff.mp ok
  have hinv := Ball.contains_inv (of_decide_eq_true (Bool.and_eq_true_iff.mp h.1).2) hx
  have he := ExpBounds.Witness.sound (Bool.and_eq_true_iff.mp h.2).1 (Ball.contains_neg hx)
  have hv := kernelValue_enclosure w hx ok
  have hs := Ball.contains_mul (Ball.contains_neg (Ball.contains_add he
    (Ball.contains_mul (Ball.contains_exact w.kind.power) hv))) hinv
  have hc := Ball.contains_mul (Ball.contains_sub he
    (Ball.contains_mul (Ball.contains_exact (w.kind.power+1)) hs)) hinv
  exact ⟨hv,by simpa [KernelWitness.evaluate,kernelSlope,div_eq_mul_inv] using hs,
    by simpa [KernelWitness.evaluate,kernelSlope,kernelCurvature,div_eq_mul_inv,Rat.cast_add] using hc⟩

end BccSharp.Coulomb.BravaisCover
