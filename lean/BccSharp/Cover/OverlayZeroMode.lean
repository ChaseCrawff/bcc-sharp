import BccSharp.Cover.OverlayEnergyHeat
import BccSharp.Cover.OverlayArea
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false

/-! Evaluation of the Overlay planar zero mode. Positive axial Fourier
weights justify integration of the transformed series. The n=0 term
of the natural Bernoulli and zeta series uses the field convention. -/

noncomputable section
open MeasureTheory Set Real

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar

def heightWeight (h : ℝ) (k : ℤ) : ℝ := 1+Real.cos (2*Real.pi*(k : ℝ)*h)

theorem heightWeight_nonneg (h : ℝ) (k : ℤ) : 0≤heightWeight h k := by
  unfold heightWeight
  linarith [Real.neg_one_le_cos (2*Real.pi*(k : ℝ)*h)]

private theorem bernoulli_cos_two (h : ℝ) (hh : h∈Icc (0:ℝ) 1) :
    HasSum (fun n : ℕ => (1/(n : ℝ)^2)*Real.cos (2*Real.pi*(n : ℝ)*h))
      (Real.pi^2*(h^2-h+1/6)) := by
  have series := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide) hh
  first
  | convert series using 1 <;> norm_num [Polynomial.bernoulli_two] <;> ring
  | convert series using 1 <;> norm_num [bernoulliFun,Polynomial.bernoulli_two] <;> ring
  | convert series using 1 <;> norm_num [bernoulliFun,Polynomial.bernoulli,Finset.sum_range_succ] <;> ring

theorem bernoulli_integer (h : ℝ) (hh : h∈Icc (0:ℝ) 1) :
    HasSum (fun k : ℤ => heightWeight h k/(k : ℝ)^2)
      (2*Real.pi^2*(h^2-h+1/3)) := by
  let f (k : ℤ) := heightWeight h k/(k : ℝ)^2
  let N := Real.pi^2*(h^2-h+1/3)
  have zeta : HasSum (fun n : ℕ => 1/(n : ℝ)^2) (Real.pi^2/6) := by
    simpa [one_div] using hasSum_zeta_two
  have hNat : HasSum (fun n : ℕ => f (n : ℤ)) N := by
    convert zeta.add (bernoulli_cos_two h hh) using 1
    · funext n
      simp only [f,heightWeight,Int.cast_natCast]
      ring
    · dsimp [N]
      ring
  have hzero : f 0=0 := by simp [f]
  have hp : Summable (fun n : ℕ => f ((n : ℤ)+1)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using hNat.summable.comp_injective
      (add_left_injective (1 : ℕ))
  have htail : HasSum (fun n : ℕ => f ((n : ℤ)+1)) N := by
    have shift := hNat.summable.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one,Nat.cast_zero,hzero,zero_add,Nat.cast_add,Nat.cast_one,hNat.tsum_eq] at shift
    rw [← shift]
    exact hp.hasSum
  have even (k : ℤ) : f (-k)=f k := by
    have e : 2*Real.pi*(-(k : ℝ))*h= -(2*Real.pi*(k : ℝ)*h) := by ring
    simp only [f,heightWeight,Int.cast_neg,neg_sq,e,Real.cos_neg]
  have hNeg : HasSum (fun n : ℕ => f (-((n : ℤ)+1))) N := by simpa only [even] using htail
  convert HasSum.of_nat_of_neg_add_one (f := f) hNat hNeg using 1
  dsimp [N]
  ring

def zeroHeatTerm (p : Chart) (k : ℤ) (s : ℝ) : ℝ :=
  if k=0 then 0 else heightWeight (p 7) k*inversionHeat (Real.pi*(k : ℝ)^2/(cReal p)^2) s

private theorem zeroHeat_point (p : Chart) (hc : 0<cReal p) (s : ℝ) (hs : 0<s) :
    zeroHeat p s=∑' k : ℤ, zeroHeatTerm p k s := by
  let a := cReal p*s
  have ha : 0<a := mul_pos hc hs
  let g (k : ℤ) := lineHeat a⁻¹ 0 k
  let d := lineDualTerm a⁻¹ (p 7)
  have hg : Summable g := lineHeat_summable a⁻¹ (inv_pos.mpr ha) 0
  have hd : Summable d := lineDual_summable a⁻¹ (inv_pos.mpr ha) (p 7)
  have e (k : ℤ) : g k+d k=heightWeight (p 7) k*g k := by dsimp [g,d,lineDualTerm,heightWeight]; ring
  have g0 : g 0+d 0=2 := by norm_num [g,d,lineHeat,lineDualTerm]
  have middle : lineDual a⁻¹ 0+lineDual a⁻¹ (p 7)=2+∑' k : ℤ, if k=0 then 0 else heightWeight (p 7) k*g k := by
    rw [lineDual_zero]
    change (∑' k, g k)+(∑' k, d k)=_
    rw [← hg.tsum_add hd,(sum_at_zero (fun k => g k+d k) (hg.add hd)).2,g0]
    simp_rw [e]
  have row (k : ℤ) : zeroHeatTerm p k s=2*(s^3)⁻¹*(if k=0 then 0 else heightWeight (p 7) k*g k) := by
    by_cases hk : k=0
    · simp [zeroHeatTerm,hk]
    · simp only [zeroHeatTerm,if_neg hk,inversionHeat,g,lineHeat,add_zero]
      have e' : -(Real.pi*(k : ℝ)^2/(cReal p)^2)/s^2= -Real.pi*(a⁻¹)^2*(k : ℝ)^2 := by
        dsimp [a]
        field_simp [hc.ne',hs.ne'] <;> ring
      rw [e']
      ring
  unfold zeroHeat
  change 2*cReal p*(s^2)⁻¹*(lineTheta a 0+lineTheta a (p 7)-2/a)=_
  rw [line_poisson a ha 0,line_poisson a ha (p 7),← mul_add,middle]
  simp_rw [row,tsum_mul_left]
  dsimp [a]
  field_simp [hc.ne',hs.ne'] <;> ring

theorem zeroHeat_integral (p : Chart) (hc : 0<cReal p) (hh : p 7∈Icc (0:ℝ) 1) :
    IntegrableOn (zeroHeat p) (Ioi 0) ∧ (∫ s in Ioi (0:ℝ), zeroHeat p s)=zeroMode p := by
  let A (k : ℤ) := Real.pi*(k : ℝ)^2/(cReal p)^2
  have pA (k : ℤ) (nz : k≠0) : 0<A k := by
    have kr : (k : ℝ)≠0 := by exact_mod_cast nz
    dsimp [A]
    positivity
  have h (k : ℤ) : IntegrableOn (zeroHeatTerm p k) (Ioi 0) := by
    by_cases nz : k=0
    · have z : zeroHeatTerm p k=fun _ => 0 := by funext s; simp [zeroHeatTerm,nz]
      rw [z]
      exact integrableOn_zero
    · have z : zeroHeatTerm p k=fun s => heightWeight (p 7) k*inversionHeat (A k) s := by
        funext s; simp only [zeroHeatTerm,if_neg nz,A]
      rw [z]
      exact (inversionHeat_integrable (pA k nz)).const_mul (heightWeight (p 7) k)
  have e (k : ℤ) : (∫ s in Ioi (0:ℝ), zeroHeatTerm p k s)=
      ((cReal p)^2/Real.pi)*(heightWeight (p 7) k/(k : ℝ)^2) := by
    by_cases nz : k=0
    · simp [zeroHeatTerm,nz]
    · simp only [zeroHeatTerm,if_neg nz,integral_const_mul]
      rw [inversionHeat_full (pA k nz)]
      have kr : (k : ℝ)≠0 := by exact_mod_cast nz
      dsimp [A]
      field_simp [Real.pi_pos.ne',kr,hc.ne'] <;> ring
  have absEq (k : ℤ) : (∫ s in Ioi (0:ℝ), ‖zeroHeatTerm p k s‖)=(∫ s in Ioi (0:ℝ), zeroHeatTerm p k s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have sp : 0<s := hs
    have nn : 0≤zeroHeatTerm p k s := by
      unfold zeroHeatTerm
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (heightWeight_nonneg _ _) (by unfold inversionHeat; positivity)
    show ‖zeroHeatTerm p k s‖=zeroHeatTerm p k s
    rw [Real.norm_eq_abs,abs_of_nonneg nn]
  have B := bernoulli_integer (p 7) hh
  have t := integrateSeries (zeroHeatTerm p) h (by simp only [absEq,e]; exact B.summable.mul_left _)
  have ident : zeroHeat p =ᵐ[volume.restrict (Ioi (0:ℝ))] (fun s => ∑' k : ℤ, zeroHeatTerm p k s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact zeroHeat_point p hc s hs
  refine ⟨t.1.congr ident.symm,?_⟩
  rw [integral_congr_ae ident,t.2]
  simp_rw [e,tsum_mul_left,B.tsum_eq]
  unfold zeroMode
  field_simp [Real.pi_pos.ne'] <;> ring

end BccSharp.Coulomb.CompactCover.OverlayPlanar
