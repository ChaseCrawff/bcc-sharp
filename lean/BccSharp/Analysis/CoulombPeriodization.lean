module

public import BccSharp.Analysis.CoulombTransform
public import BccSharp.Analysis.PeriodLattice
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! Absolute integrability and Fourier unfolding for the screened Coulomb
sum on arbitrary finite-index bcc period lattices. -/
@[expose] public section
noncomputable section
namespace BccSharp.CoulombPeriodization
open Ewald TorusLattice PeriodLattice CoulombLaplace MeasureTheory
open scoped BigOperators Pointwise

variable (Γ : AddSubgroup Lattice) [Fintype (Torus Γ)]

instance : MeasurableVAdd (spatial Γ) Vec :=
  (inferInstance : MeasurableVAdd (spatial Γ).toAddSubgroup Vec)

instance : VAddInvariantMeasure (spatial Γ) Vec volume :=
  (inferInstance : VAddInvariantMeasure (spatial Γ).toAddSubgroup Vec volume)

def periodize (f : Vec → ℂ) (x : Vec) : ℂ := ∑' z : spatial Γ, f (z.val+x)

theorem translate_integrable {f : Vec → ℂ} (hf : Integrable f) (z : spatial Γ) :
    IntegrableOn (fun x : Vec => f (z.val+x)) (fundamental Γ) :=
  ((measurePreserving_add_left volume z.val).integrable_comp_of_integrable hf).integrableOn

theorem sum_lintegral {f : Vec → ℂ} (hf : Integrable f) :
    (∑' z : spatial Γ, ∫⁻ x in fundamental Γ, ‖f (z.val+x)‖ₑ) < ⊤ := by
  have h := (fundamental_domain Γ).lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
  change (∫⁻ x, ‖f x‖ₑ)=(∑' z : spatial Γ, ∫⁻ x in fundamental Γ, ‖f (z.val+x)‖ₑ) at h
  rw [← h]
  exact hf.hasFiniteIntegral

theorem periodize_integrable {f : Vec → ℂ} (hf : Integrable f) :
    IntegrableOn (periodize Γ f) (fundamental Γ) := by
  have hm (z : spatial Γ) := (translate_integrable Γ hf z).aestronglyMeasurable
  refine ⟨AEStronglyMeasurable.tsum hm,?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun z => (hm z).enorm)]
  exact sum_lintegral Γ hf

theorem periodize_integral {f : Vec → ℂ} (hf : Integrable f) :
    (∫ x in fundamental Γ, periodize Γ f x) = ∫ x : Vec, f x := by
  unfold periodize
  rw [integral_tsum (fun z => (translate_integrable Γ hf z).aestronglyMeasurable)
    (sum_lintegral Γ hf).ne]
  exact ((fundamental_domain Γ).integral_eq_tsum'' f hf).symm

theorem wave_add (u x y : Vec) : wave u (x+y)=wave u x*wave u y := by
  simp only [wave,← Complex.exp_add,dot,Fin.sum_univ_three,Pi.add_apply,
    Complex.ofReal_mul,Complex.ofReal_add]
  congr 1
  ring

omit [Fintype (Torus Γ)] in
theorem wave_period {u : Vec} (hu : Reciprocal Γ u) (z : spatial Γ) : wave u z.val=1 := by
  obtain ⟨w,hw,he⟩ := (mem_spatial Γ z.val).mp z.property
  obtain ⟨n,hn⟩ := hu w hw
  rw [← he,wave,hn]
  have he' : -((2*Real.pi*(n : ℝ) : ℝ) : ℂ)*Complex.I =
      ((-n : ℤ) : ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
  rw [he',Complex.exp_int_mul_two_pi_mul_I]

theorem screened_periodize_fourier {u : Vec} (hu : Reciprocal Γ u) :
    (∫ x in fundamental Γ, periodize Γ (fun y => (RealSpaceHessian.potential y : ℂ)) x*wave u x) =
      ∫ x : Vec, screenedPhase u x := by
  have he (x : Vec) : periodize Γ (screenedPhase u) x =
      periodize Γ (fun y => (RealSpaceHessian.potential y : ℂ)) x*wave u x := by
    simp only [periodize,screenedPhase,wave_add,wave_period Γ hu,one_mul,tsum_mul_right]
  rw [← funext he]
  exact periodize_integral Γ (screenedPhase_integrable u)

theorem fundamental_finite : volume (fundamental Γ) < ⊤ :=
  (ZSpan.fundamentalDomain_isBounded _).measure_lt_top

theorem wave_norm (u x : Vec) : ‖wave u x‖=1 := by
  simp [wave,Complex.norm_exp]

theorem wave_integrable (u : Vec) : IntegrableOn (wave u) (fundamental Γ) := by
  have : IsFiniteMeasure (volume.restrict (fundamental Γ)) :=
    isFiniteMeasure_restrict.mpr (fundamental_finite Γ).ne
  apply (integrable_const (1 : ℝ)).mono'
  · have h : Continuous (wave u) := by unfold wave dot; fun_prop
    exact h.aestronglyMeasurable
  · filter_upwards with x
    exact (wave_norm u x).le

theorem wave_zero (x : Vec) : wave 0 x=1 := by simp [wave,dot]

theorem wave_integral_zero : (∫ x in fundamental Γ, wave 0 x)=
    ((Fintype.card (Torus Γ) : ℝ)/2 : ℂ) := by
  simp only [wave_zero,integral_const]
  have he : (volume.restrict (fundamental Γ)).real Set.univ = volume.real (fundamental Γ) := by
    simp [measureReal_def]
  rw [he,fundamental_volume]
  simp [Complex.real_smul]

/-- Every nontrivial reciprocal character has zero integral on the torus. -/
theorem wave_integral {u : Vec} (hu : Reciprocal Γ u) (hu0 : u ≠ 0) :
    (∫ x in fundamental Γ, wave u x)=0 := by
  let y : Vec := (1/(2*Ewald.sq u)) • u
  have hy : dot u y=1/2 := by
    simp only [y,dot,Ewald.sq,Fin.sum_univ_three,Pi.smul_apply,smul_eq_mul]
    have hs := square_pos hu0
    unfold Ewald.sq at hs
    field_simp
  have hyw : wave u y = -1 := by
    rw [wave,hy]
    have he : -((2*Real.pi*(1/2 : ℝ) : ℝ) : ℂ)*Complex.I = -(Real.pi*Complex.I) := by
      push_cast
      ring
    rw [he,Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  have ht : IsAddFundamentalDomain (spatial Γ) (y +ᵥ fundamental Γ) volume :=
    (fundamental_domain Γ).vadd_of_comm y
  have hi := (fundamental_domain Γ).setIntegral_eq ht (f:=wave u) (fun z x => by
    change wave u (z.val+x)=wave u x
    rw [wave_add,wave_period Γ hu,one_mul])
  have himage : y +ᵥ fundamental Γ = (fun x : Vec => y+x) '' fundamental Γ := rfl
  rw [himage,(measurePreserving_add_left volume y).setIntegral_image_emb
    (measurableEmbedding_addLeft y) (wave u) (fundamental Γ)] at hi
  simp_rw [wave_add,hyw] at hi
  rw [integral_const_mul] at hi
  linear_combination (1/2 : ℂ)*hi

end BccSharp.CoulombPeriodization
