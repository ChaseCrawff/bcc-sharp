import BccSharp.Cover.OverlayPlanarPoisson

set_option autoImplicit false

/-! Pointwise split of the determinant-one Series heat integrand.
The zero and signed parts below are derived by separating the actual
layer and reciprocal indices, with all sums at a fixed positive scale. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp

theorem chartBasis_det_one (p : Chart) (hr : 0<p 0) (ht : 0<p 1) : (chartBasis p).det=1 := by
  norm_num [chartBasis,Matrix.det_fin_three,mul_assoc]
  field_simp [hr.ne',ht.ne'] <;> ring

theorem chart_valid_seam (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) :
    (chartPoint p).Valid := by
  refine ⟨chartBasis_det_one p hr ht,fun n e => ?_⟩
  have a : p 7=(n 2 : ℝ) := congrFun e 2
  have b : (0:ℤ)<n 2 := by exact_mod_cast (a ▸ h₀)
  have d : n 2<1 := by exact_mod_cast (a ▸ h₁)
  omega

theorem sum_at_zero {ι : Type*} [Zero ι] [DecidableEq ι] (f : ι→ℝ) (h : Summable f) :
    Summable (fun n => if n=0 then 0 else f n) ∧
      (∑' n, f n)=f 0+∑' n, if n=0 then 0 else f n := by
  have hd : Summable (fun n => if n=0 then 0 else f n) := by
    apply h.summable_of_eq_zero_or_self
    intro n
    by_cases e : n=0 <;> simp [e]
  have hz : Summable (fun n : ι => if n=0 then f 0 else 0) := (hasSum_ite_eq 0 (f 0)).summable
  have e (n : ι) : f n=(if n=0 then f 0 else 0)+(if n=0 then 0 else f n) := by
    split_ifs with hn <;> simp_all
  refine ⟨hd,?_⟩
  calc
    _ = ∑' n : ι, ((if n=0 then f 0 else 0)+(if n=0 then 0 else f n)) := tsum_congr e
    _ = _ := by rw [hz.tsum_add hd]; simp

def axialHeight (f : Vec) (k : ℤ) : ℝ := (k : ℝ)+f 2
def layerX (p : Chart) (f : Vec) (k : ℤ) : ℝ := f 0+axialHeight f k*(p 3-p 2*p 4)
def layerY (p : Chart) (f : Vec) (k : ℤ) : ℝ := f 1+axialHeight f k*p 4

theorem chart_heat_term (p : Chart) (f : Vec) (s : ℝ) (m : Wave) (k : ℤ) :
    heat s ((chartBasis p).mulVec f+linearImage (chartBasis p) (planeIndex (m,k)))=
      lineHeat (cReal p*s) (f 2) k*planeHeat p s (layerX p f k) (layerY p f k) m := by
  simp only [heat,lineHeat,planeHeat,← Real.exp_add]
  congr 1
  simp [chartBasis,linearImage,castVec,planeIndex,planarNorm,layerX,layerY,axialHeight,cReal,
    sq,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

def chartLayer (p : Chart) (f : Vec) (s : ℝ) (k : ℤ) : ℝ :=
  lineHeat (cReal p*s) (f 2) k*planeTheta p s (layerX p f k) (layerY p f k)

theorem chart_heat_layers (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) (f : Vec) :
    heatTheta (chartBasis p) f s=∑' k : ℤ, chartLayer p f s k := by
  let idx := (Equiv.prodComm ℤ Wave).trans planeIndex
  let g (n : IntVec) := heat s ((chartBasis p).mulVec f+linearImage (chartBasis p) n)
  have hB : (chartBasis p).det≠0 := by rw [chartBasis_det_one p hr ht]; exact one_ne_zero
  have hg : Summable g := heat_lattice_summable s hs (chartBasis p) hB _
  have hp : Summable (fun c => g (idx c)) := idx.summable_iff.mpr hg
  change (∑' n : IntVec, g n)=_
  rw [← idx.tsum_eq g, hp.tsum_prod]
  apply tsum_congr
  intro k
  change (∑' m : Wave, g (planeIndex (m,k)))=chartLayer p f s k
  simp_rw [g,chart_heat_term,tsum_mul_left,chartLayer,planeTheta]

def planeDecay (p : Chart) (s : ℝ) (m : Wave) : ℝ := Real.exp (-Real.pi*(s⁻¹)^2*κSq p m)

theorem planeDecay_summable (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) :
    Summable (planeDecay p s) := by
  refine (planeDual_summable p hr.ne' ht.ne' s⁻¹ (inv_pos.mpr hs) 0 0).congr (fun m => ?_)
  simp [planeDecay,planeDualTerm]

def layerPhase (p : Chart) (f : Vec) (m : Wave) (k : ℤ) : ℝ :=
  (m.1 : ℝ)*f 0+(m.2 : ℝ)*f 1+axialHeight f k*wReal p m

theorem layerPhase_eq (p : Chart) (f : Vec) (m : Wave) (k : ℤ) :
    (m.1 : ℝ)*layerX p f k+(m.2 : ℝ)*layerY p f k=layerPhase p f m k := by
  unfold layerX layerY layerPhase wReal
  ring

def spectralHeatTerm (p : Chart) (f : Vec) (s : ℝ) (m : Wave) (k : ℤ) : ℝ :=
  planeDecay p s m*lineHeat (cReal p*s) (f 2) k*Real.cos (2*Real.pi*layerPhase p f m k)

theorem spectralHeatTerm_bound (p : Chart) (f : Vec) (s : ℝ) (m : Wave) (k : ℤ) :
    ‖spectralHeatTerm p f s m k‖≤planeDecay p s m*lineHeat (cReal p*s) (f 2) k := by
  have hpos : 0<planeDecay p s m*lineHeat (cReal p*s) (f 2) k :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  unfold spectralHeatTerm
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos hpos]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_le.mpr
    ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) hpos.le

theorem spectralHeat_summable (p : Chart) (f : Vec) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) :
    Summable (fun z : Wave × ℤ => spectralHeatTerm p f s z.1 z.2) := by
  have c : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  exact (productHeat_sum _ _ (planeDecay_summable p hr ht s hs)
    (lineHeat_summable (cReal p*s) (mul_pos c hs) (f 2))).1.of_norm_bounded
    (fun z => spectralHeatTerm_bound p f s z.1 z.2)

theorem chart_layer_poisson (p : Chart) (f : Vec) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) (k : ℤ) :
    chartLayer p f s k=cReal p*(s^2)⁻¹*(∑' m : Wave, spectralHeatTerm p f s m k) := by
  rw [chartLayer,plane_poisson p hr ht s hs,planeDual,← tsum_mul_left,← tsum_mul_left,← tsum_mul_left]
  apply tsum_congr
  intro m
  simp only [planeDualTerm,spectralHeatTerm,planeDecay,layerPhase_eq]
  ring

def nonzeroWaveTerm (p : Chart) (f : Vec) (s : ℝ) (m : Wave) (k : ℤ) : ℝ :=
  if m=0 then 0 else spectralHeatTerm p f s m k

theorem chart_layer_zero_split (p : Chart) (f : Vec) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) (k : ℤ) :
    chartLayer p f s k=cReal p*(s^2)⁻¹*
      (lineHeat (cReal p*s) (f 2) k+∑' m : Wave, nonzeroWaveTerm p f s m k) := by
  have h := (spectralHeat_summable p f hr ht s hs).comp_injective
    (show Function.Injective (fun m : Wave => (m,k)) from fun _ _ e => congrArg Prod.fst e)
  have hz : spectralHeatTerm p f s 0 k=lineHeat (cReal p*s) (f 2) k := by
    simp [spectralHeatTerm,planeDecay,κSq,layerPhase,wReal]
  rw [chart_layer_poisson p f hr ht s hs k, (sum_at_zero (fun m => spectralHeatTerm p f s m k) h).2, hz] <;> rfl

def sameSpectral (p : Chart) (s : ℝ) (m : Wave) (k : ℤ) : ℝ :=
  if k=0 then 0 else nonzeroWaveTerm p 0 s m k

def signedHeat (p : Chart) (s : ℝ) : ℝ :=
  2*cReal p*(s^2)⁻¹*((∑' k : ℤ, ∑' m : Wave, sameSpectral p s m k)+
    (∑' k : ℤ, ∑' m : Wave, nonzeroWaveTerm p (chartPoint p).offset s m k))

def planarRegularHeat (p : Chart) (s : ℝ) : ℝ :=
  2*(planeTheta p s 0 0-1-cReal p*(s^2)⁻¹)

def zeroHeat (p : Chart) (s : ℝ) : ℝ :=
  2*cReal p*(s^2)⁻¹*(lineTheta (cReal p*s) 0+lineTheta (cReal p*s) (p 7)-2/(cReal p*s))

def seriesHeatIntegrand (q : TwoSite) (s : ℝ) : ℝ :=
  2*(heatTheta q.basis 0 s+heatTheta q.basis q.offset s-1-2*(s^3)⁻¹)

theorem spectralHeat_reorder (p : Chart) (f : Vec) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s)
    (skip : ℤ → Bool) :
    (∑' k : ℤ, ∑' m : Wave, if skip k=true then 0 else nonzeroWaveTerm p f s m k)=
      ∑' m : Wave, ∑' k : ℤ, if skip k=true then 0 else nonzeroWaveTerm p f s m k := by
  let F (z : Wave × ℤ) := if skip z.2=true then 0 else nonzeroWaveTerm p f s z.1 z.2
  have h : Summable F := (spectralHeat_summable p f hr ht s hs).summable_of_eq_zero_or_self (fun z => by
    by_cases he : skip z.2=true <;> by_cases hm : z.1=0 <;> simp [F,nonzeroWaveTerm,he,hm])
  let e := Equiv.prodComm ℤ Wave
  have hswap : Summable (F ∘ e) := e.summable_iff.mpr h
  calc
    _ = ∑' z : ℤ × Wave, F (e z) := hswap.tsum_prod.symm
    _ = ∑' z : Wave × ℤ, F z := e.tsum_eq F
    _ = _ := h.tsum_prod

private theorem nonzero_row_summable (p : Chart) (f : Vec) (hr : 0<p 0) (ht : 0<p 1)
    (s : ℝ) (hs : 0<s) : Summable (fun k : ℤ => ∑' m : Wave, nonzeroWaveTerm p f s m k) := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  let θ := ∑' m : Wave, planeDecay p s m
  have seq := (lineHeat_summable (cReal p*s) (mul_pos hc hs) (f 2)).mul_left θ
  apply seq.of_norm_bounded
  intro k
  let a := lineHeat (cReal p*s) (f 2) k
  have hn : 0≤a := (Real.exp_pos _).le
  have hg := (planeDecay_summable p hr ht s hs).mul_left a
  have h (m : Wave) : |nonzeroWaveTerm p f s m k|≤a*planeDecay p s m := by
    by_cases e : m=0
    · simp only [nonzeroWaveTerm,e,if_true,abs_zero]
      exact mul_nonneg hn (Real.exp_pos _).le
    · have hb := spectralHeatTerm_bound p f s m k
      rw [Real.norm_eq_abs] at hb
      simp only [nonzeroWaveTerm,e,↓reduceIte]
      calc |spectralHeatTerm p f s m k| ≤ planeDecay p s m*lineHeat (cReal p*s) (f 2) k := hb
        _ = a*planeDecay p s m := mul_comm _ _
  have bound := (abs_sum_bound hg h).2
  rw [tsum_mul_left] at bound
  change ‖∑' m : Wave, nonzeroWaveTerm p f s m k‖≤θ*a
  rw [Real.norm_eq_abs,mul_comm θ]
  exact bound

private theorem zeroLayer (p : Chart) (s : ℝ) : chartLayer p 0 s 0=planeTheta p s 0 0 := by
  simp [chartLayer,lineHeat,layerX,layerY,axialHeight]

private theorem chartLayer_sum (p : Chart) (f : Vec) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) :
    (∑' k : ℤ, chartLayer p f s k)=cReal p*(s^2)⁻¹*(
      lineTheta (cReal p*s) (f 2)+∑' k : ℤ, ∑' m : Wave, nonzeroWaveTerm p f s m k) := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  have a := lineHeat_summable (cReal p*s) (mul_pos hc hs) (f 2)
  have b := nonzero_row_summable p f hr ht s hs
  simp_rw [chart_layer_zero_split p f hr ht s hs,tsum_mul_left,a.tsum_add b,lineTheta]

private theorem chartLayer_sum_summable (p : Chart) (f : Vec) (hr : 0<p 0) (ht : 0<p 1)
    (s : ℝ) (hs : 0<s) : Summable (chartLayer p f s) := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  have a := lineHeat_summable (cReal p*s) (mul_pos hc hs) (f 2)
  have b := nonzero_row_summable p f hr ht s hs
  exact ((a.add b).mul_left (cReal p*(s^2)⁻¹)).congr
    (fun k => (chart_layer_zero_split p f hr ht s hs k).symm)

private theorem chartLayer_samesum (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) :
    (∑' k : ℤ, chartLayer p 0 s k)=planeTheta p s 0 0+cReal p*(s^2)⁻¹*(
      lineTheta (cReal p*s) 0-1+∑' k : ℤ, ∑' m : Wave, sameSpectral p s m k) := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  obtain ⟨hA,sumA⟩ := sum_at_zero (lineHeat (cReal p*s) 0)
    (lineHeat_summable (cReal p*s) (mul_pos hc hs) 0)
  obtain ⟨hB,_⟩ := sum_at_zero (fun k : ℤ => ∑' m : Wave, nonzeroWaveTerm p 0 s m k)
    (nonzero_row_summable p 0 hr ht s hs)
  have hSplit := (sum_at_zero (chartLayer p 0 s) (chartLayer_sum_summable p 0 hr ht s hs)).2
  have row (k : ℤ) : (if k=0 then 0 else chartLayer p 0 s k)=cReal p*(s^2)⁻¹*
      ((if k=0 then 0 else lineHeat (cReal p*s) 0 k)+
        (if k=0 then 0 else ∑' m : Wave, nonzeroWaveTerm p 0 s m k)) := by
    by_cases h : k=0
    · simp [h]
    · simpa only [h,↓reduceIte,Pi.zero_apply] using chart_layer_zero_split p 0 hr ht s hs k
  have a : (∑' k : ℤ, if k=0 then 0 else lineHeat (cReal p*s) 0 k)=lineTheta (cReal p*s) 0-1 := by
    unfold lineTheta
    rw [sumA]
    have h : lineHeat (cReal p*s) 0 0=1 := by simp [lineHeat]
    rw [h]
    ring
  have b (k : ℤ) : (if k=0 then 0 else ∑' m : Wave, nonzeroWaveTerm p 0 s m k)=
      ∑' m : Wave, sameSpectral p s m k := by
    by_cases zk : k=0 <;> simp [sameSpectral,zk]
  rw [hSplit,zeroLayer,tsum_congr row,tsum_mul_left,hA.tsum_add hB,a,tsum_congr b]

theorem chart_heat_split (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) :
    seriesHeatIntegrand (chartPoint p) s=planarRegularHeat p s+zeroHeat p s+signedHeat p s := by
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  unfold seriesHeatIntegrand planarRegularHeat zeroHeat signedHeat
  rw [show (chartPoint p).basis=chartBasis p by rfl,
    chart_heat_layers p hr ht s hs 0,chart_heat_layers p hr ht s hs (chartPoint p).offset,
    chartLayer_samesum p hr ht s hs,chartLayer_sum p (chartPoint p).offset hr ht s hs]
  change 2*(planeTheta p s 0 0+cReal p*(s^2)⁻¹*(_)+cReal p*(s^2)⁻¹*(_)-1-2*(s^3)⁻¹)=_
  simp only [show (chartPoint p).offset 2=p 7 by rfl]
  field_simp [hc.ne',hs.ne'] <;> ring

end BccSharp.Coulomb.CompactCover.OverlayPlanar
