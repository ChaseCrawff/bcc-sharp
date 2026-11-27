import BccSharp.Cover.OverlayZeroMode

set_option autoImplicit false

/-! Absolute sum of the integrated norms of the actual Overlay Fourier
layer terms. The phase-zero chart has exactly the same decay and is
used only as a nonnegative majorant for Tonelli and Fubini. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar

def layerOffset (p : Chart) (same : Bool) : Vec := if same then 0 else (chartPoint p).offset
def omitLayer (same : Bool) (m : Wave) (k : ℤ) : Prop := m=0 ∨ (same=true ∧ k=0)
instance (same : Bool) (m : Wave) (k : ℤ) : Decidable (omitLayer same m k) := by unfold omitLayer; infer_instance

def layerKernel (p : Chart) (same : Bool) (m : Wave) (k : ℤ) (s : ℝ) : ℝ :=
  if omitLayer same m k then 0 else
    (cReal p*Real.cos (2*Real.pi*layerPhase p (layerOffset p same) m k))*
      laplaceHeat (cReal p*|axialHeight (layerOffset p same) k|) (κReal p m) s

def layerMass (p : Chart) (same : Bool) (m : Wave) (k : ℤ) : ℝ :=
  if omitLayer same m k then 0 else
    (cReal p/κReal p m)*Real.exp (-tReal p m*|axialHeight (layerOffset p same) k|)

theorem waveKappa_pos (p : Chart) (hr : 0<p 0) (ht : 0<p 1) {m : Wave} (nz : m≠0) : 0<κReal p m := by
  let B := max (p 0) (secondColumn p)
  have e := waveRadius_le hr ht m (show p 0≤B from le_max_left _ _) (show secondColumn p≤B from le_max_right _ _)
  have j : 0<waveRadius m := by
    by_contra! h
    have aa : m.1.natAbs≤waveRadius m := le_max_left _ _
    have bb : m.2.natAbs≤waveRadius m := le_max_right _ _
    have a : m.1.natAbs=0 := by omega
    have b : m.2.natAbs=0 := by omega
    exact nz (Prod.ext (Int.natAbs_eq_zero.mp a) (Int.natAbs_eq_zero.mp b))
  by_contra! h
  exact (show (0:ℝ)<(waveRadius m : ℝ) by exact_mod_cast j).not_ge
    (e.trans (mul_nonpos_of_nonpos_of_nonneg h ((hr.le).trans (le_max_left _ _))))

private theorem layerHeight_ne (p : Chart) (h₀ : 0<p 7) (h₁ : p 7<1) (same : Bool) (m : Wave) (k : ℤ)
    (hk : ¬omitLayer same m k) : axialHeight (layerOffset p same) k≠0 := by
  cases same
  · intro he
    have e : (k : ℝ)+p 7=0 := he
    have upper : k<0 := by exact_mod_cast (show (k : ℝ)<0 by linarith only [e,h₀])
    have lower : (-1:ℤ)<k := by exact_mod_cast (show (-1:ℝ)<(k : ℝ) by linarith only [e,h₁])
    omega
  · have n : k≠0 := fun e => hk (Or.inr ⟨rfl,e⟩)
    simpa [axialHeight,layerOffset] using (show (k : ℝ)≠0 by exact_mod_cast n)

theorem layerMass_nonneg (p : Chart) (hc : 0<cReal p) (same : Bool) (m : Wave) (k : ℤ) :
    0≤layerMass p same m k := by
  unfold layerMass
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (div_nonneg hc.le (Real.sqrt_nonneg _)) (Real.exp_pos _).le

theorem layerKernel_integral (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1)
    (same : Bool) (m : Wave) (k : ℤ) : IntegrableOn (layerKernel p same m k) (Ioi 0) ∧
      (∫ s in Ioi (0:ℝ), layerKernel p same m k s)=
        layerMass p same m k*Real.cos (2*Real.pi*layerPhase p (layerOffset p same) m k) ∧
      (∫ s in Ioi (0:ℝ), ‖layerKernel p same m k s‖)≤layerMass p same m k := by
  by_cases hz : omitLayer same m k
  · have z : layerKernel p same m k=fun _ => 0 := funext fun _ => if_pos hz
    rw [z]
    simp [layerMass,hz]
  have mNZ : m≠0 := fun he => hz (Or.inl he)
  have kap := waveKappa_pos p hr ht mNZ
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  have apos := mul_pos hc (abs_pos.mpr (layerHeight_ne p h₀ h₁ same m k hz))
  obtain ⟨a,ha⟩ : ∃ a, a=cReal p*|axialHeight (layerOffset p same) k| := ⟨_,rfl⟩
  obtain ⟨C,hC⟩ : ∃ C, C=Real.cos (2*Real.pi*layerPhase p (layerOffset p same) m k) := ⟨_,rfl⟩
  rw [← ha] at apos
  have kernelPt (s : ℝ) : layerKernel p same m k s=(cReal p*C)*laplaceHeat a (κReal p m) s := by
    rw [ha,hC]
    exact if_neg hz
  have kernel : layerKernel p same m k=fun s => (cReal p*C)*laplaceHeat a (κReal p m) s := funext kernelPt
  have hk : IntegrableOn (laplaceHeat a (κReal p m)) (Ioi 0) := laplaceHeat_integrable a _ kap
  have he := laplaceHeat_integral apos kap
  have e : cReal p*(∫ s in Ioi (0:ℝ), laplaceHeat a (κReal p m) s)=layerMass p same m k := by
    rw [he,layerMass,if_neg hz,tReal,ha]
    rw [show -2*Real.pi*(cReal p*|axialHeight (layerOffset p same) k|)*κReal p m=
      -(2*Real.pi*cReal p*κReal p m)*|axialHeight (layerOffset p same) k| by ring]
    ring
  refine ⟨by rw [kernel]; exact hk.const_mul (cReal p*C),?_,?_⟩
  · simp only [kernelPt]
    rw [integral_const_mul,← e,← hC]
    ring
  · have cc : |C|≤1 := by rw [hC]; exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
    have ee : (∫ s in Ioi (0:ℝ), ‖layerKernel p same m k s‖)=
        (cReal p*|C|)*(∫ s in Ioi (0:ℝ), laplaceHeat a (κReal p m) s) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have sp : 0<s := hs
      have lp : 0≤laplaceHeat a (κReal p m) s := by unfold laplaceHeat; positivity
      show ‖layerKernel p same m k s‖=(cReal p*|C|)*laplaceHeat a (κReal p m) s
      rw [kernelPt,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg hc.le,abs_of_nonneg lp]
    rw [ee,← e]
    have nn : 0≤∫ s in Ioi (0:ℝ), laplaceHeat a (κReal p m) s := by rw [he]; positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cc hc.le) nn

def quietChart (p : Chart) : Chart := ![p 0,p 1,p 2,0,0,0,0,p 7]

private theorem waveValue_zero' (p : Chart) : waveValue p 0=0 := waveValue_zero p

private theorem layerMass_rows (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) (m : Wave) :
    Summable (layerMass p true m) ∧ Summable (layerMass p false m) ∧
    (∑' k : ℤ, layerMass p true m k)+(∑' k : ℤ, layerMass p false m k)=cReal p*waveValue (quietChart p) m := by
  by_cases m0 : m=0
  · subst m0
    have zp (same : Bool) (k : ℤ) : layerMass p same 0 k=0 := if_pos (Or.inl rfl)
    have zf (same : Bool) : layerMass p same 0=fun _ => 0 := funext (zp same)
    refine ⟨by rw [zf]; exact summable_zero,by rw [zf]; exact summable_zero,?_⟩
    simp only [zp,tsum_zero,add_zero,waveValue_zero',mul_zero]
  let η := min (p 7) (1-p 7)
  have he : 0<η := lt_min h₀ (sub_pos.mpr h₁)
  have lo : η≤p 7 := min_le_left _ _
  have hi : p 7≤1-η := by linarith [min_le_right (p 7) (1-p 7)]
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  have hk := waveKappa_pos p hr ht m0
  have t : 0<tReal p m := by unfold tReal; positivity
  let A (k : ℤ) := if k=0 then 0 else sameMode (tReal p m) 0 k
  let C := crossMode (tReal p m) 0 0 (p 7)
  obtain ⟨a,b,e⟩ := axialSeries_integer (tReal p m) 0 0 (p 7) η t he lo hi
  have aE (k : ℤ) : layerMass p true m k=cReal p/κReal p m*A k := by
    by_cases k0 : k=0 <;> simp [layerMass,omitLayer,m0,k0,A,layerOffset,axialHeight,sameMode,axialTerm]
  have bE (k : ℤ) : layerMass p false m k=cReal p/κReal p m*C k := by
    simp [layerMass,omitLayer,m0,C,layerOffset,chartPoint,axialHeight,crossMode,axialTerm]
  refine ⟨(a.mul_left (cReal p/κReal p m)).congr (fun k => (aE k).symm),
    (b.mul_left (cReal p/κReal p m)).congr (fun k => (bE k).symm),?_⟩
  simp_rw [aE,bE,tsum_mul_left,← mul_add]
  change cReal p/κReal p m*((∑' k, A k)+(∑' k, C k))=_
  rw [← e]
  have w : wReal (quietChart p) m=0 := by simp [wReal,quietChart]
  have u : uReal (quietChart p) m=0 := by simp [uReal,quietChart]
  rw [waveValue,w,u]
  change _=cReal p*(axialSeries (tReal p m) 0 0 (p 7)/κReal p m)
  ring

private def waveAxialIndex : (Σ _ : Wave, ℤ) ≃ Wave×ℤ where
  toFun z := (z.1,z.2)
  invFun z := ⟨z.1,z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

private theorem quietWave_summable (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) :
    Summable (fun m => cReal p*waveValue (quietChart p) m) := by
  let q := quietChart p
  let B := max (q 0) (secondColumn q)
  let step := 2*Real.pi*cReal q/B
  let η := min (p 7) (1-p 7)
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  have hB : 0<B := hr.trans_le (le_max_left _ _)
  have pos : 0<step := by dsimp [step]; change 0<2*Real.pi*cReal p/B; positivity
  have hη : 0<η := lt_min h₀ (sub_pos.mpr h₁)
  have lo : η≤q 7 := min_le_left _ _
  have hi : q 7≤1-η := by change p 7≤1-η; linarith [min_le_right (p 7) (1-p 7)]
  exact (radialTail_sound (p := q) (B := B) (τ := step) 0 hr ht
    (le_max_left _ _) (le_max_right _ _) pos le_rfl hη lo hi).1.mul_left (cReal p)

theorem layerMass_joint (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) (same : Bool) :
    Summable (fun z : Wave×ℤ => layerMass p same z.1 z.2) := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  have radial := quietWave_summable p hr ht h₀ h₁
  refine (summable_prod_of_nonneg (f := fun z : Wave×ℤ => layerMass p same z.1 z.2)
    (fun z => layerMass_nonneg p hc same z.1 z.2)).mpr ⟨?_,?_⟩
  · intro m
    have h := layerMass_rows p hr ht h₀ h₁ m
    cases same
    · exact h.2.1
    · exact h.1
  · refine Summable.of_nonneg_of_le (fun m => tsum_nonneg (fun k => layerMass_nonneg p hc same m k))
      (fun m => ?_) radial
    have e := (layerMass_rows p hr ht h₀ h₁ m).2.2
    have a : 0≤∑' k : ℤ, layerMass p true m k := tsum_nonneg (fun k => layerMass_nonneg p hc true m k)
    have b : 0≤∑' k : ℤ, layerMass p false m k := tsum_nonneg (fun k => layerMass_nonneg p hc false m k)
    cases same
    · show (∑' k : ℤ, layerMass p false m k)≤cReal p*waveValue (quietChart p) m
      linarith only [e,a,b]
    · show (∑' k : ℤ, layerMass p true m k)≤cReal p*waveValue (quietChart p) m
      linarith only [e,a,b]

private theorem layerKernel_point (p : Chart) (same : Bool) (m : Wave) (k : ℤ)
    (s : ℝ) (hs : 0<s) : layerKernel p same m k s=
      (2*cReal p*(s^2)⁻¹)*(if same=true ∧ k=0 then 0 else nonzeroWaveTerm p (layerOffset p same) s m k) := by
  by_cases skip : same=true ∧ k=0
  · simp [layerKernel,omitLayer,skip]
  by_cases hm : m=0
  · simp [layerKernel,omitLayer,skip,hm,nonzeroWaveTerm]
  have hsqrt : (κReal p m)^2=κSq p m := Real.sq_sqrt (by unfold κSq; positivity)
  let f := layerOffset p same
  have e : Real.exp (-(Real.pi*((cReal p*|axialHeight f k|)^2*s^2+(κReal p m)^2/s^2)))=
      planeDecay p s m*lineHeat (cReal p*s) (f 2) k := by
    rw [planeDecay,lineHeat,← Real.exp_add,hsqrt,mul_pow,sq_abs,axialHeight,inv_pow]
    congr 1
    ring
  simp only [layerKernel,omitLayer,hm,false_or,skip,if_false,nonzeroWaveTerm,laplaceHeat,spectralHeatTerm]
  rw [e]
  ring

private theorem layerKernel_sum_point (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s)
    (same : Bool) :
    (∑' z : Wave×ℤ, layerKernel p same z.1 z.2 s)=
      (2*cReal p*(s^2)⁻¹)*(∑' k : ℤ, ∑' m : Wave,
        if same=true ∧ k=0 then 0 else nonzeroWaveTerm p (layerOffset p same) s m k) := by
  let f : Wave×ℤ → ℝ := fun z =>
    if same=true ∧ z.2=0 then 0 else nonzeroWaveTerm p (layerOffset p same) s z.1 z.2
  have sf : Summable f := (spectralHeat_summable p (layerOffset p same) hr ht s hs).summable_of_eq_zero_or_self (fun z => by
    by_cases a : same=true ∧ z.2=0 <;> by_cases b : z.1=0 <;> simp [f,a,b,nonzeroWaveTerm])
  let index := Equiv.prodComm ℤ Wave
  have swap : Summable (fun c => f (index c)) := index.summable_iff.mpr sf
  simp_rw [layerKernel_point p same _ _ s hs]
  change (∑' z : Wave×ℤ, (2*cReal p*(s^2)⁻¹)*f z)=_
  rw [tsum_mul_left,← index.tsum_eq f,swap.tsum_prod] <;> rfl

def layerIntegrated (p : Chart) (same : Bool) (m : Wave) (k : ℤ) : ℝ :=
  layerMass p same m k*Real.cos (2*Real.pi*layerPhase p (layerOffset p same) m k)

private theorem layerIntegrated_bound (p : Chart) (hc : 0<cReal p) (same : Bool) (m : Wave) (k : ℤ) :
    |layerIntegrated p same m k|≤layerMass p same m k := by
  have nn := layerMass_nonneg p hc same m k
  rw [layerIntegrated,abs_mul,abs_of_nonneg nn]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_le.mpr
    ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) nn

private theorem integrated_outer_summable (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1)
    (same : Bool) : Summable (fun m : Wave => ∑' k : ℤ, layerIntegrated p same m k) := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  apply (quietWave_summable p hr ht h₀ h₁).of_norm_bounded
  intro m
  obtain ⟨s,c,e⟩ := layerMass_rows p hr ht h₀ h₁ m
  rw [Real.norm_eq_abs,← e]
  have sa : 0≤∑' k : ℤ, layerMass p true m k := tsum_nonneg (fun k => layerMass_nonneg p hc true m k)
  have ca : 0≤∑' k : ℤ, layerMass p false m k := tsum_nonneg (fun k => layerMass_nonneg p hc false m k)
  cases same
  · have b := (abs_sum_bound c (layerIntegrated_bound p hc false m)).2
    linarith only [b,sa]
  · have b := (abs_sum_bound s (layerIntegrated_bound p hc true m)).2
    linarith only [b,ca]

private theorem integrated_axial (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) (m : Wave) :
    (∑' k : ℤ, layerIntegrated p true m k)+(∑' k : ℤ, layerIntegrated p false m k)=cReal p*waveValue p m := by
  by_cases m0 : m=0
  · simp [layerIntegrated,layerMass,omitLayer,m0,waveValue_zero']
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  have hk := waveKappa_pos p hr ht m0
  have t : 0<tReal p m := by unfold tReal; positivity
  let η := min (p 7) (1-p 7)
  have he : 0<η := lt_min h₀ (sub_pos.mpr h₁)
  have lo : η≤p 7 := min_le_left _ _
  have hi : p 7≤1-η := by linarith [min_le_right (p 7) (1-p 7)]
  have e := (axialSeries_integer (tReal p m) (wReal p m) (uReal p m) (p 7) η t he lo hi).2.2
  have same (k : ℤ) : layerIntegrated p true m k=(cReal p/κReal p m)*
      (if k=0 then 0 else sameMode (tReal p m) (wReal p m) k) := by
    by_cases k0 : k=0 <;> simp [layerIntegrated,layerMass,omitLayer,m0,k0,layerOffset,layerPhase,axialHeight,sameMode,axialTerm,mul_assoc]
  have cross (k : ℤ) : layerIntegrated p false m k=(cReal p/κReal p m)*
      crossMode (tReal p m) (wReal p m) (uReal p m) (p 7) k := by
    simp [layerIntegrated,layerMass,omitLayer,m0,layerOffset,layerPhase,chartPoint,uReal,axialHeight,crossMode,axialTerm,mul_assoc]
  simp_rw [same,cross,tsum_mul_left,← mul_add,← e,waveValue]
  ring

theorem signedHeat_integral (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) :
    IntegrableOn (signedHeat p) (Ioi 0) ∧ (∫ s in Ioi (0:ℝ), signedHeat p s)=layerValue p := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  let f (same : Bool) (z : Wave×ℤ) := layerKernel p same z.1 z.2
  have both (same : Bool) := integrateSeries (S := Ioi (0:ℝ)) (f same)
    (fun z => (layerKernel_integral p hr ht h₀ h₁ same z.1 z.2).1)
    (Summable.of_nonneg_of_le (fun z => integral_nonneg (fun _ => norm_nonneg _))
      (fun z => (layerKernel_integral p hr ht h₀ h₁ same z.1 z.2).2.2)
      (layerMass_joint p hr ht h₀ h₁ same))
  have eq : signedHeat p =ᵐ[volume.restrict (Ioi (0:ℝ))] fun s =>
      (∑' z, f true z s)+(∑' z, f false z s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have a := layerKernel_sum_point p hr ht s hs true
    have b := layerKernel_sum_point p hr ht s hs false
    change signedHeat p s=(∑' z : Wave×ℤ, layerKernel p true z.1 z.2 s)+
      (∑' z : Wave×ℤ, layerKernel p false z.1 z.2 s)
    rw [a,b]
    simp only [signedHeat,layerOffset,Bool.true_eq, true_and,Bool.false_eq_true,false_and,if_false,if_true,sameSpectral]
    ring
  refine ⟨((both true).1.add (both false).1).congr eq.symm,?_⟩
  rw [integral_congr_ae eq,integral_add (both true).1 (both false).1,(both true).2,(both false).2]
  have term (same : Bool) (z : Wave×ℤ) : (∫ s in Ioi (0:ℝ), f same z s)=layerIntegrated p same z.1 z.2 :=
    (layerKernel_integral p hr ht h₀ h₁ same z.1 z.2).2.1
  have summable (same : Bool) : Summable (fun z : Wave×ℤ => layerIntegrated p same z.1 z.2) :=
    (layerMass_joint p hr ht h₀ h₁ same).of_norm_bounded (fun z => by
      rw [Real.norm_eq_abs]
      exact layerIntegrated_bound p hc same z.1 z.2)
  simp_rw [term,(summable true).tsum_prod,(summable false).tsum_prod]
  rw [← (integrated_outer_summable p hr ht h₀ h₁ true).tsum_add (integrated_outer_summable p hr ht h₀ h₁ false)]
  simp_rw [integrated_axial p hr ht h₀ h₁,tsum_mul_left,layerValue]

end BccSharp.Coulomb.CompactCover.OverlayPlanar
