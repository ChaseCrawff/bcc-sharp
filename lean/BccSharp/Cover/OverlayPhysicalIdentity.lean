import BccSharp.Cover.OverlayLayerIntegral

set_option autoImplicit false

/-! Assembly of the Overlay physical numerator. The seam chart has
positive diagonals and a nonintegral height. No reduction inequalities,
truncation data, or planar theta comparison enter the identity. -/

noncomputable section
open MeasureTheory Set

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coverage DirectRoute

def planarRegularized (p : Chart) : ℝ := ∫ s in Ioi (0:ℝ), planarRegularHeat p s

theorem chart_energy_planar (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) :
    IntegrableOn (planarRegularHeat p) (Ioi 0) ∧
    2*ac*energy (chartPoint p)=planarRegularized p+zeroMode p+layerValue p := by
  have hq := chart_valid_seam p hr ht h₀ h₁
  have cp : 0<cReal p := inv_pos.mpr (mul_pos hr ht)
  obtain ⟨ii,E⟩ := energy_eq_heat_integral (chartPoint p) hq
  obtain ⟨iz,Z⟩ := zeroHeat_integral p cp ⟨h₀.le,h₁.le⟩
  obtain ⟨is,L⟩ := signedHeat_integral p hr ht h₀ h₁
  have h : (seriesHeatIntegrand (chartPoint p)) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun s => planarRegularHeat p s+zeroHeat p s+signedHeat p s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact chart_heat_split p hr ht s hs
  have sub : (fun s => seriesHeatIntegrand (chartPoint p) s-zeroHeat p s-signedHeat p s)
      =ᵐ[volume.restrict (Ioi (0:ℝ))] planarRegularHeat p := by
    filter_upwards [h] with s hs
    rw [hs]
    ring
  have ip : IntegrableOn (planarRegularHeat p) (Ioi 0) := ((ii.sub iz).sub is).congr sub
  refine ⟨ip,?_⟩
  rw [E,integral_congr_ae h,integral_add (ip.fun_add iz) is,integral_add ip iz,Z,L] <;> rfl

theorem chart_green_planar (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (h₀ : 0<p 7) (h₁ : p 7<1) :
    2*ac*greenPerParticle seriesScreen (physicalBasis (chartPoint p)) (physicalTwoPositions (chartPoint p))=
      planarRegularized p+zeroMode p+layerValue p := by
  rw [green_two_eq_energy (chartPoint p) (chart_valid_seam p hr ht h₀ h₁)]
  exact (chart_energy_planar p hr ht h₀ h₁).2

theorem addressed_energy_planar {b : Cell} {p : Chart} (hp : b.Mem p) (cube : ℕ)
    (ok : layerCheck b cube=true) :
    2*ac*energy (chartPoint p)=planarRegularized (seamPoint b p)+zeroMode (seamPoint b p)+layerValue (seamPoint b p) := by
  let q := seamPoint b p
  let B := seamCell b
  have hm : B.Mem q := seamPoint_mem hp
  have c := (Bool.and_eq_true_iff.mp ok).1
  simp only [retainedCheck,Bool.and_eq_true] at c
  have h := diagonalsCheck_sound c.1.1
  have hη : 0<spacing B := of_decide_eq_true c.1.2
  have r : 0<q 0 := (show (0:ℝ)<(coord B 0).lo by exact_mod_cast h.1).trans_le (endpoints (coord_sound hm 0)).1
  have t : 0<q 1 := (show (0:ℝ)<(coord B 1).lo by exact_mod_cast h.2.1).trans_le (endpoints (coord_sound hm 1)).1
  have e := spacing_sound hm
  have η : (0:ℝ)<(spacing B : ℝ) := by exact_mod_cast hη
  have id := (chart_energy_planar q r t (η.trans_le e.1) (by linarith only [η,e.2])).2
  rw [seamPoint_energy b p] at id
  exact id

end BccSharp.Coulomb.CompactCover.OverlayPlanar
