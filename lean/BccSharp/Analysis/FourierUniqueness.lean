module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! Uniqueness of integrable functions from their torus Fourier coefficients. -/
@[expose] public section
noncomputable section
namespace BccSharp.FourierUniqueness
open MeasureTheory Complex Set Submodule
open scoped ComplexConjugate ENNReal Topology

section Pairing
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] {μ : Measure X} {f : X → ℂ}

theorem mul_integrable (hf : Integrable f μ) (g : C(X,ℂ)) :
    Integrable (fun x => g x*f x) μ :=
  hf.bdd_mul g.continuous.aestronglyMeasurable (Filter.Eventually.of_forall g.norm_coe_le_norm)

def pairing (hf : Integrable f μ) : C(X,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ x,g x*f x ∂μ
      map_add' := by
        intro g h
        simp only [ContinuousMap.add_apply,add_mul]
        exact integral_add (mul_integrable hf g) (mul_integrable hf h)
      map_smul' := by
        intro c g
        simp only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc]
        exact integral_const_mul c _ }
    (∫ x,‖f x‖ ∂μ) (by
      intro g
      calc
        ‖∫ x,g x*f x ∂μ‖ ≤ ∫ x,‖g x*f x‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ x,‖g‖*‖f x‖ ∂μ := by
          apply integral_mono (mul_integrable hf g).norm (hf.norm.const_mul _)
          intro x
          exact (norm_mul (g x) (f x)).le.trans
            (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))
        _ = (∫ x,‖f x‖ ∂μ)*‖g‖ := by rw [integral_const_mul,mul_comm])

end Pairing

section TestUniqueness
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [HasOuterApproxClosed X] {μ : Measure X} [IsFiniteMeasure μ]

theorem real_ae_zero {f : X → ℝ} (hf : Integrable f μ)
    (h : ∀ g : BoundedContinuousFunction X ℝ,(∫ x,g x*f x ∂μ)=0) : f=ᵐ[μ] 0 := by
  let fp := fun x => max (f x) 0
  let fn := fun x => max (-f x) 0
  have hp : Integrable fp μ := hf.pos_part
  have hn : Integrable fn μ := hf.neg_part
  have hmp := hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmn := hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  let P := μ.withDensity (fun x => ENNReal.ofReal (fp x))
  let N := μ.withDensity (fun x => ENNReal.ofReal (fn x))
  have hp0 (x : X) : 0 ≤ fp x := le_max_right _ _
  have hn0 (x : X) : 0 ≤ fn x := le_max_right _ _
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hp.aestronglyMeasurable
      (Filter.Eventually.of_forall hp0)).mpr hp)
  let : IsFiniteMeasure N := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hn.aestronglyMeasurable
      (Filter.Eventually.of_forall hn0)).mpr hn)
  have he : P=N := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    change (∫ x,g x ∂μ.withDensity (fun x => ENNReal.ofReal (fp x)))=
      (∫ x,g x ∂μ.withDensity (fun x => ENNReal.ofReal (fn x)))
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmp (by simp),
      integral_withDensity_eq_integral_toReal_smul₀ hmn (by simp)]
    simp only [ENNReal.toReal_ofReal (hp0 _),ENNReal.toReal_ofReal (hn0 _),smul_eq_mul]
    apply sub_eq_zero.mp
    rw [← integral_sub (hp.mul_bdd g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall g.norm_coe_le_norm))
      (hn.mul_bdd g.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall g.norm_coe_le_norm))]
    convert h g using 1
    congr 1
    funext x
    rw [← sub_mul,show fp x-fn x=f x from max_zero_sub_max_neg_zero_eq_self _]
    ring
  have hae : (fun x => ENNReal.ofReal (fp x))=ᵐ[μ] (fun x => ENNReal.ofReal (fn x)) :=
    (withDensity_eq_iff_of_sigmaFinite hmp hmn).mp he
  filter_upwards [hae] with x hx
  have hx' : fp x=fn x := by
    simpa only [ENNReal.toReal_ofReal (hp0 x),ENNReal.toReal_ofReal (hn0 x)] using congrArg ENNReal.toReal hx
  have hd : fp x-fn x=f x := max_zero_sub_max_neg_zero_eq_self _
  simpa only [Pi.zero_apply,hx',sub_self] using hd.symm

end TestUniqueness

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

theorem continuous_tests {μ : Measure (UnitAddTorus d)} {f : UnitAddTorus d → ℂ} (hf : Integrable f μ)
    (h : ∀ n : d → ℤ,(∫ x,UnitAddTorus.mFourier n x*f x ∂μ)=0) (g : C(UnitAddTorus d,ℂ)) :
    (∫ x,g x*f x ∂μ)=0 := by
  have hd : Dense (span ℂ (range (UnitAddTorus.mFourier (d:=d))) : Set C(UnitAddTorus d,ℂ)) := by
    rw [dense_iff_closure_eq]
    change (span ℂ (range (UnitAddTorus.mFourier (d:=d)))).topologicalClosure.carrier=Set.univ
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    rfl
  have he : pairing hf=0 := ContinuousLinearMap.ext_on hd (by
    rintro _ ⟨n,rfl⟩
    change (∫ x,UnitAddTorus.mFourier n x*f x ∂μ)=0
    exact h n)
  exact congrArg (fun L : C(UnitAddTorus d,ℂ) →L[ℂ] ℂ => L g) he


theorem ae_zero {μ : Measure (UnitAddTorus d)} [IsFiniteMeasure μ] {f : UnitAddTorus d → ℂ}
    (hf : Integrable f μ) (h : ∀ n : d → ℤ,(∫ x,UnitAddTorus.mFourier n x*f x ∂μ)=0) :
    f=ᵐ[μ] 0 := by
  have hr : (fun x => (f x).re)=ᵐ[μ] 0 := by
    apply real_ae_zero hf.re
    intro g
    let G : C(UnitAddTorus d,ℂ) := ⟨fun x => (g x : ℂ),Complex.continuous_ofReal.comp g.continuous⟩
    have he : (∫ x,(G x*f x).re ∂μ)=0 :=
      (integral_re (mul_integrable hf G)).trans (congrArg Complex.re (continuous_tests hf h G))
    simpa only [G,ContinuousMap.coe_mk,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,RCLike.re_to_complex] using he
  have hi : (fun x => (f x).im)=ᵐ[μ] 0 := by
    apply real_ae_zero hf.im
    intro g
    let G : C(UnitAddTorus d,ℂ) := ⟨fun x => (g x : ℂ),Complex.continuous_ofReal.comp g.continuous⟩
    have he : (∫ x,(G x*f x).im ∂μ)=0 :=
      (integral_im (mul_integrable hf G)).trans (congrArg Complex.im (continuous_tests hf h G))
    simpa only [G,ContinuousMap.coe_mk,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,RCLike.im_to_complex] using he
  filter_upwards [hr,hi] with x hx hy
  exact Complex.ext hx hy

/-- Fourier coefficients determine every integrable torus function up to
almost-everywhere equality; no square-integrability premise is needed. -/
theorem ae_eq {μ : Measure (UnitAddTorus d)} [IsFiniteMeasure μ]
    {f g : UnitAddTorus d → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ n : d → ℤ,(∫ x,UnitAddTorus.mFourier n x*f x ∂μ)=
      (∫ x,UnitAddTorus.mFourier n x*g x ∂μ)) : f=ᵐ[μ] g := by
  have hz : (f-g)=ᵐ[μ] 0 := ae_zero (hf.sub hg) (by
    intro n
    simp only [Pi.sub_apply,mul_sub]
    rw [integral_sub (mul_integrable hf (UnitAddTorus.mFourier n))
      (mul_integrable hg (UnitAddTorus.mFourier n))]
    exact sub_eq_zero.mpr (h n))
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

theorem coefficients_ae_eq {f g : UnitAddTorus d → ℂ} (hf : Integrable f) (hg : Integrable g)
    (h : ∀ n : d → ℤ,UnitAddTorus.mFourierCoeff f n=UnitAddTorus.mFourierCoeff g n) :
    f=ᵐ[volume] g := ae_eq hf hg (fun n => by
      simpa only [UnitAddTorus.mFourierCoeff,neg_neg,smul_eq_mul] using h (-n))

end BccSharp.FourierUniqueness
