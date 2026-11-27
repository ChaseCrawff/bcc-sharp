import BccSharp.Cover.OverlayHeatSplit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import BccSharp.Analysis.CoulombFourier
import BccSharp.Analysis.RadialPotential

set_option autoImplicit false

/-! Scalar integrals used by the Overlay heat decomposition. All
limits and integrability are on the positive half-line. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp

private theorem inverse_at_zero_right : Tendsto (fun s : ℝ => s⁻¹) (𝓝[Set.Ioi 0] 0) atTop := by
  apply tendsto_atTop.2
  intro x
  let b := max (1:ℝ) x
  have hb : 0<b := zero_lt_one.trans_le (le_max_left _ _)
  have h : Iio b⁻¹ ∈ 𝓝[Set.Ioi 0] (0:ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (inv_pos.mpr hb))
  filter_upwards [h,self_mem_nhdsWithin] with s hs hs₀
  have hp : 0<s := hs₀
  have e : s*b<1 := (lt_div_iff₀ hb).mp (by simpa only [one_div,mem_Iio] using hs)
  exact (le_max_right _ _).trans (by
    rw [← one_div]
    apply (le_div_iff₀ hp).mpr
    linarith only [e,mul_comm s b])

private theorem integrable_positive_of_power_tail (f : ℝ→ℝ) (hf : Measurable f) (P C D : ℝ)
    (hP : P< -1) (hC : ∀ s∈Ioc (0:ℝ) 1, ‖f s‖≤C)
    (hD : ∀ s∈Ioi (1:ℝ), ‖f s‖≤D*s^P) : IntegrableOn f (Ioi 0) := by
  have h₀ : IntegrableOn f (Ioc (0:ℝ) 1) := by
    letI : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1)) := isFiniteMeasure_restrict.mpr (by simp)
    have k : IntegrableOn (fun _ : ℝ => C) (Ioc (0:ℝ) 1) := integrable_const _
    exact k.mono' hf.aestronglyMeasurable (by filter_upwards [ae_restrict_mem measurableSet_Ioc] using hC)
  have h₁ : IntegrableOn f (Ioi (1:ℝ)) := by
    apply ((integrableOn_Ioi_rpow_of_lt hP (c := 1) zero_lt_one).const_mul D).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] using hD
  have u : Ioc (0:ℝ) 1 ∪ Ioi 1=Ioi 0 := by
    ext s
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      exact (le_or_gt s 1).elim (fun hs => Or.inl ⟨h,hs⟩) Or.inr
  rw [← u]
  exact h₀.union h₁

private theorem integral_positiveFTC {f F : ℝ→ℝ} (integrable : IntegrableOn f (Ioi (0:ℝ)))
    (deriv : ∀ s>0, HasDerivAt F (f s) s) (nonneg : ∀ s>0, 0≤f s) {L R : ℝ}
    (atZero : Tendsto F (𝓝[Ioi 0] 0) (𝓝 L)) (atInfinity : Tendsto F atTop (𝓝 R)) :
    (∫ s in Ioi (0:ℝ), f s)=R-L := by
  have left : Tendsto (fun a : ℝ => ∫ s in Ioi a, f s) (𝓝[Ioi 0] 0) (𝓝 (∫ s in Ioi (0:ℝ), f s)) :=
    (integrable.continuousOn_Ici_primitive_Ioi 0 self_mem_Ici).mono Ioi_subset_Ici_self
  have equal : (fun a : ℝ => R-F a) =ᶠ[𝓝[Ioi 0] 0] (fun a => ∫ s in Ioi a, f s) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hapos : 0<a := ha
    symm
    exact integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun s hs => deriv s (hapos.trans_le hs)) (fun s hs => nonneg s (hapos.trans hs)) atInfinity
  have right := (tendsto_const_nhds.sub atZero).congr' equal
  exact tendsto_nhds_unique left right

def inversionHeat (A s : ℝ) : ℝ := 2*(s^3)⁻¹*Real.exp (-A/s^2)

private theorem powerExp_bound (x : ℝ) (h : 0≤x) : x^2*Real.exp (-x)≤4 := by
  have a : x/2≤Real.exp (x/2) := by linarith [Real.add_one_le_exp (x/2)]
  have b := pow_le_pow_left₀ (div_nonneg h (by norm_num)) a 2
  rw [pow_two (Real.exp (x/2)),← Real.exp_add,show x/2+x/2=x by ring] at b
  have e := mul_le_mul_of_nonneg_right b (Real.exp_pos (-x)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at e
  linarith only [show x^2*Real.exp (-x)=4*((x/2)^2*Real.exp (-x)) by ring,e]

theorem inversionHeat_integrable {A : ℝ} (hA : 0<A) : IntegrableOn (inversionHeat A) (Ioi 0) := by
  apply integrable_positive_of_power_tail _ (by unfold inversionHeat; fun_prop) (-3) (8/(A^2)) 2 (by norm_num)
  · intro s hs
    have sp : 0<s := hs.1
    have expo := powerExp_bound (A/s^2) (by positivity)
    rw [← neg_div] at expo
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold inversionHeat; positivity)]
    have e : inversionHeat A s= (2*s/A^2)*((A/s^2)^2*Real.exp (-A/s^2)) := by
      unfold inversionHeat
      field_simp [hA.ne',sp.ne'] <;> ring
    rw [e]
    calc
      _ ≤ (2*s/A^2)*4 := mul_le_mul_of_nonneg_left expo (by positivity)
      _ = 8*s/A^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith [hs.2]) (sq_nonneg A)
  · intro s hs
    have sp : 0<s := zero_lt_one.trans hs
    have exp : Real.exp (-A/s^2)≤1 := by
      simpa using Real.exp_le_exp.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA.le) (sq_nonneg s))
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold inversionHeat; positivity)]
    have hr : s^(-3 : ℝ)=(s^3)⁻¹ := by convert Real.rpow_neg_natCast s 3 using 1 <;> norm_num
    rw [hr,inversionHeat]
    exact (mul_le_mul_of_nonneg_left exp (by positivity : 0≤2*(s^3)⁻¹)).trans_eq (mul_one _)

private theorem inversionPrimitive_at_zero {A : ℝ} (hA : 0<A) :
    Tendsto (fun s : ℝ => Real.exp (-A/s^2)) (𝓝[Ioi 0] 0) (𝓝 0) := by
  have upper : Tendsto (fun s : ℝ => A/s^2) (𝓝[Ioi 0] 0) atTop := by
    apply tendsto_atTop.2
    intro x
    let D := max (1:ℝ) (x/A)
    have d : 0<D := zero_lt_one.trans_le (le_max_left _ _)
    have ev := (tendsto_atTop.1 inverse_at_zero_right) D
    filter_upwards [ev] with s hs
    have y : 1≤ s⁻¹ := (le_max_left _ _).trans hs
    have ey : s⁻¹≤(s⁻¹)^2 := by nlinarith only [mul_nonneg (zero_le_one.trans y) (sub_nonneg.mpr y)]
    have low : x/A≤(s⁻¹)^2 := (le_max_right _ _).trans (hs.trans ey)
    simpa [div_eq_mul_inv,inv_pow,mul_comm A] using (div_le_iff₀ hA).mp low
  simpa only [Function.comp_def,neg_div] using
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp upper)

theorem inversionHeat_full {A : ℝ} (hA : 0<A) : (∫ s in Ioi (0:ℝ), inversionHeat A s)=1/A := by
  let F (s : ℝ) := (1/A)*Real.exp (-A/s^2)
  have hd (s : ℝ) (hs : 0<s) : HasDerivAt F (inversionHeat A s) s := by
    convert (CoulombLaplace.scale_derivative (A := A) hs.ne').const_mul (1/A) using 1
    unfold inversionHeat
    field_simp [hA.ne',hs.ne'] <;> ring
  have hn (s : ℝ) (hs : 0<s) : 0≤ inversionHeat A s := by unfold inversionHeat; positivity
  have h0 : Tendsto F (𝓝[Ioi 0] 0) (𝓝 0) := by simpa [F] using (inversionPrimitive_at_zero hA).const_mul (1/A)
  have hi : Tendsto F atTop (𝓝 (1/A)) := by simpa [F] using (CoulombLaplace.scale_tendsto A).const_mul (1/A)
  simpa using integral_positiveFTC (inversionHeat_integrable hA) hd hn h0 hi

theorem inversionHeat_small {A : ℝ} (hA : 0<A) : (∫ s in Ioc (0:ℝ) 1, inversionHeat A s)=Real.exp (-A)/A := by
  let F (s : ℝ) := (1/A)*Real.exp (-A/s^2)
  have hd (s : ℝ) (hs : s∈Ici (1:ℝ)) : HasDerivAt F (inversionHeat A s) s := by
    have sp : 0<s := zero_lt_one.trans_le hs
    convert (CoulombLaplace.scale_derivative (A := A) sp.ne').const_mul (1/A) using 1
    unfold inversionHeat
    field_simp [hA.ne',sp.ne'] <;> ring
  have hn (s : ℝ) (hs : s∈Ioi (1:ℝ)) : 0≤ inversionHeat A s := by
    have sp : 0<s := zero_lt_one.trans hs
    unfold inversionHeat
    positivity
  have hi : Tendsto F atTop (𝓝 (1/A)) := by simpa [F] using (CoulombLaplace.scale_tendsto A).const_mul (1/A)
  have tail := integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hi
  have split := intervalIntegral.integral_Ioi_sub_Ioi (inversionHeat_integrable hA) (by norm_num : (0:ℝ)≤1)
  rw [inversionHeat_full hA,tail,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at split
  rw [← split]
  norm_num [F] <;> ring

def laplaceHeat (a b s : ℝ) : ℝ := 2*(s^2)⁻¹*Real.exp (-(Real.pi*(a^2*s^2+b^2/s^2)))

theorem laplaceHeat_integrable (a b : ℝ) (hb : 0<b) : IntegrableOn (laplaceHeat a b) (Ioi 0) := by
  let A := Real.pi*b^2
  have hA : 0<A := by dsimp [A]; positivity
  apply integrable_positive_of_power_tail _ (by unfold laplaceHeat; fun_prop) (-2) (2/A) 2 (by norm_num)
  · intro s hs
    have hp : 0<s := hs.1
    let x := A/s^2
    have hx : 0≤x := by unfold x; positivity
    have h : x*Real.exp (-x)≤1 := by
      have e : x≤Real.exp x := by linarith [Real.add_one_le_exp x]
      have a := mul_le_mul_of_nonneg_right e (Real.exp_pos (-x)).le
      rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at a
      exact a
    have exp : Real.exp (-(Real.pi*a^2*s^2))≤1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold laplaceHeat; positivity)]
    have e : laplaceHeat a b s=(2/A)*(x*Real.exp (-x))*Real.exp (-(Real.pi*a^2*s^2)) := by
      unfold laplaceHeat x A
      have e : Real.exp (-(Real.pi*(a^2*s^2+b^2/s^2)))=
          Real.exp (-(Real.pi*b^2/s^2))*Real.exp (-(Real.pi*a^2*s^2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      field_simp [Real.pi_pos.ne',hb.ne',hp.ne']
    rw [e]
    exact (mul_le_of_le_one_right (by positivity) exp).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h (by positivity : 0≤2/A))
  · intro s hs
    have hp : 0<s := zero_lt_one.trans hs
    have e : s^(-2 : ℝ)=(s^2)⁻¹ := by convert Real.rpow_neg_natCast s 2 using 1 <;> norm_num
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold laplaceHeat; positivity),e,laplaceHeat]
    exact mul_le_of_le_one_right (by positivity) (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity)))

private def gaussianPrimitive (x : ℝ) : ℝ := ∫ y in (0:ℝ)..x, Real.exp (-Real.pi*y^2)

private theorem gaussianPrimitive_deriv (x : ℝ) :
    HasDerivAt gaussianPrimitive (Real.exp (-Real.pi*x^2)) x := by
  have hc : Continuous (fun y : ℝ => Real.exp (-Real.pi*y^2)) := by fun_prop
  exact (hc.integral_hasStrictDerivAt 0 x).hasDerivAt

private theorem gaussianPrimitive_neg (x : ℝ) : gaussianPrimitive (-x)= -gaussianPrimitive x := by
  let F (y : ℝ) := gaussianPrimitive (-y)+gaussianPrimitive y
  have der (y : ℝ) : HasDerivAt F 0 y := by
    have a := ((gaussianPrimitive_deriv (-y)).comp y (hasDerivAt_neg' y)).fun_add (gaussianPrimitive_deriv y)
    simpa [F,Function.comp_def,neg_sq] using a
  have c : Continuous F := continuous_iff_continuousAt.mpr (fun y => (der y).continuousAt)
  have e (a b : ℝ) (h : a<b) : F a=F b := by
    obtain ⟨y,hy,h'⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) h c.continuousOn (fun y _ => der y)
    have z : F b-F a=0 := ((eq_div_iff (sub_ne_zero.mpr h.ne')).mp h').symm.trans (zero_mul _)
    exact (sub_eq_zero.mp z).symm
  have f : F x=F 0 := (lt_trichotomy x 0).elim (fun h => e x 0 h)
    (fun h => h.elim (fun hx => congrArg F hx) (fun hx => (e 0 x hx).symm))
  have z : F 0=0 := by simp [F,gaussianPrimitive]
  exact eq_neg_of_add_eq_zero_left (f.trans z)

private theorem gaussianPrimitive_top : Tendsto gaussianPrimitive atTop (𝓝 (1/2)) := by
  let Tail (y : ℝ) := ∫ x in Ioi y, Real.exp (-Real.pi*x^2)
  have b : Tendsto (fun y : ℝ => (1/(2*Real.pi))*y⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (1/(2*Real.pi))
  have t : Tendsto Tail atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun y => integral_nonneg (fun _ => (Real.exp_pos _).le))) _ b
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have h := Gaussian.tail Real.pi_pos hy
    have exp : Real.exp (-Real.pi*y^2)≤1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg Real.pi_pos.le (sq_nonneg y)]
    calc
      _ ≤ Real.exp (-Real.pi*y^2)/(2*Real.pi*y) := h
      _ ≤ 1/(2*Real.pi*y) := div_le_div_of_nonneg_right exp (by positivity)
      _ = _ := by ring
  have full : (∫ x in Ioi (0:ℝ), Real.exp (-Real.pi*x^2))=1/2 := by
    simpa [Real.pi_pos.ne'] using integral_gaussian_Ioi Real.pi
  have ev : (fun y : ℝ => 1/2-Tail y) =ᶠ[atTop] gaussianPrimitive := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    have e := intervalIntegral.integral_Ioi_sub_Ioi
      (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn hy
    simpa only [gaussianPrimitive,Tail,full] using e
  have const : Tendsto (fun _ : ℝ => (1/2:ℝ)) atTop (𝓝 (1/2)) := tendsto_const_nhds
  simpa only [sub_zero] using (const.sub t).congr' ev

private theorem gaussianPrimitive_bot : Tendsto gaussianPrimitive atBot (𝓝 (-(1/2))) := by
  have h := (gaussianPrimitive_top.comp (tendsto_neg_atBot_atTop : Tendsto (fun y : ℝ => -y) atBot atTop)).neg
  simpa only [Function.comp_def,gaussianPrimitive_neg,neg_neg] using h

private theorem laplaceArg_top (a b : ℝ) (ha : 0<a) (hb : 0≤b) :
    Tendsto (fun s : ℝ => a*s-b*s⁻¹) atTop atTop := by
  apply tendsto_atTop.2
  intro v
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((v+b)/a)] with s h₁ h₂
  have u : s⁻¹≤1 := by rw [← one_div]; exact (div_le_iff₀ (zero_lt_one.trans_le h₁)).mpr (by simpa)
  linarith only [mul_le_mul_of_nonneg_left u hb,(div_le_iff₀ ha).mp h₂,mul_comm a s]

private theorem laplaceArg_zero (a b : ℝ) (ha : 0≤a) (hb : 0<b) :
    Tendsto (fun s : ℝ => b*s⁻¹-a*s) (𝓝[Ioi 0] 0) atTop := by
  apply tendsto_atTop.2
  intro v
  have u := (tendsto_atTop.1 inverse_at_zero_right) ((v+a)/b)
  have v₁ : Iio (1:ℝ) ∈ 𝓝[Ioi (0:ℝ)] 0 := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [u,v₁] with s h hs
  have hs' : s≤1 := le_of_lt hs
  linarith only [mul_le_mul_of_nonneg_left hs' ha,(div_le_iff₀ hb).mp h,mul_comm b (s⁻¹)]

theorem laplaceHeat_integral {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    (∫ s in Ioi (0:ℝ), laplaceHeat a b s)=Real.exp (-2*Real.pi*a*b)/b := by
  let K := 2*Real.pi*a*b
  let minus (s : ℝ) := a*s-b*s⁻¹
  let plus (s : ℝ) := a*s+b*s⁻¹
  let F (s : ℝ) := Real.exp (-K)*gaussianPrimitive (minus s)-Real.exp K*gaussianPrimitive (plus s)
  have hd (s : ℝ) (hs : 0<s) : HasDerivAt F (b*laplaceHeat a b s) s := by
    have da := (hasDerivAt_id' s).const_mul a
    have db := (hasDerivAt_inv hs.ne').const_mul b
    have dm := (gaussianPrimitive_deriv (minus s)).comp s (da.fun_sub db)
    have dp := (gaussianPrimitive_deriv (plus s)).comp s (da.fun_add db)
    have e₁ : Real.exp (-K)*Real.exp (-Real.pi*(minus s)^2)=
        Real.exp (-(Real.pi*(a^2*s^2+b^2/s^2))) := by
      rw [← Real.exp_add]
      congr 1
      unfold K minus
      field_simp [hs.ne'] <;> ring
    have e₂ : Real.exp K*Real.exp (-Real.pi*(plus s)^2)=
        Real.exp (-(Real.pi*(a^2*s^2+b^2/s^2))) := by
      rw [← Real.exp_add]
      congr 1
      unfold K plus
      field_simp [hs.ne'] <;> ring
    refine ((dm.const_mul (Real.exp (-K))).fun_sub (dp.const_mul (Real.exp K))).congr_deriv ?_
    have e (u v X : ℝ) : u*(v*X)=u*v*X := by ring
    rw [e,e,e₁,e₂]
    unfold laplaceHeat
    ring
  have mn := laplaceArg_top a b ha hb.le
  have mx : Tendsto plus atTop atTop := by
    apply tendsto_atTop.2
    intro x
    filter_upwards [(tendsto_atTop.1 mn) x,eventually_gt_atTop (0:ℝ)] with s hx hs
    exact hx.trans (by dsimp [plus,minus]; linarith only [mul_nonneg hb.le (inv_nonneg.mpr hs.le)])
  have zm : Tendsto minus (𝓝[Ioi 0] 0) atBot := by
    simpa [minus,Function.comp_def,neg_sub] using (tendsto_neg_atTop_atBot.comp (laplaceArg_zero a b ha.le hb))
  have zp : Tendsto plus (𝓝[Ioi 0] 0) atTop := by
    apply tendsto_atTop.2
    intro x
    filter_upwards [(tendsto_atTop.1 (laplaceArg_zero a b ha.le hb)) x,self_mem_nhdsWithin] with s hx hs
    have hp : 0<s := hs
    exact hx.trans (by dsimp [plus]; linarith only [mul_nonneg ha.le hp.le])
  have l := ((gaussianPrimitive_bot.comp zm).const_mul (Real.exp (-K))).sub
    ((gaussianPrimitive_top.comp zp).const_mul (Real.exp K))
  have r := ((gaussianPrimitive_top.comp mn).const_mul (Real.exp (-K))).sub
    ((gaussianPrimitive_top.comp mx).const_mul (Real.exp K))
  have n (s : ℝ) (hs : 0<s) : 0≤b*laplaceHeat a b s := by unfold laplaceHeat; positivity
  have h := integral_positiveFTC ((laplaceHeat_integrable a b hb).const_mul b) hd n
    (show Tendsto F _ _ from l) (show Tendsto F _ _ from r)
  rw [integral_const_mul] at h
  apply (eq_div_iff hb.ne').mpr
  dsimp [K] at h
  rw [show -2*Real.pi*a*b= -(2*Real.pi*a*b) by ring]
  linarith only [h,mul_comm b (∫ s in Ioi (0:ℝ), laplaceHeat a b s)]

end BccSharp.Coulomb.CompactCover.OverlayPlanar
