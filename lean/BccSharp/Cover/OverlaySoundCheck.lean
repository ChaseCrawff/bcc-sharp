import BccSharp.Cover.OverlayMontgomery
import BccSharp.Cover.OverlaySharpPass

set_option autoImplicit false

/-! `SoundCheck`-shaped Overlay planar checks for the cover framework.

`overlayCheck` accepts a witness on route `.strictFCC` when the checker
passes at the cube radius 2, `numeratorCheck raw 2`, and its lower
endpoint clears the strict threshold `fccHUpper - 4`. Its soundness is
`energy_fcc_lt_of_numeratorCheck` (physical identity and Montgomery's
comparison). `overlaySharpCheck` is the same route with the sharpened one-call
check `sharpPass`; its soundness repeats that argument with
`sharpPass_sound` and a form of the physical identity that needs only the
seam and diagonal guards. Neither check uses `good`: the strict comparison
holds at every point of the closed box. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute

/-- The check at cube radius 2 in a form the kernel can reduce
(`Finset.toList` replaced by `wavesList`, the shared triangular check
discharged). Evaluating it per leaf still exceeds the memory budget:. -/
theorem numeratorCheck_two_eq (raw : Cell) :
    numeratorCheck raw 2=((decide (triangleBound 3<0) && areaCheck (seamCell raw) (triangleBound 3)) &&
      layerCheckL raw 2) := by
  simp only [numeratorCheck,show (2:ℕ)+1=3 from rfl,triangleCheck_three,layerCheck_eq,Bool.true_and]

def overlayCheck (w : WitnessRef) (b : Cell) : Bool :=
  decide (w.route=Route.strictFCC) && (numeratorCheck b 2 && decide (fccHUpper-4< numeratorLower b 2))

theorem overlayCheck_sound : SoundCheck overlayCheck := by
  intro w b ok p hp _
  obtain ⟨route,rest⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨check,strict⟩ := Bool.and_eq_true_iff.mp rest
  rw [of_decide_eq_true route]
  exact energy_fcc_lt_of_numeratorCheck hp 2 check scaleRoot_ok (of_decide_eq_true strict)

/-- The physical identity of `addressed_energy_planar`, from the seam and
diagonal guards alone. -/
theorem addressed_energy_planar_of_guards {b : Cell} {p : Chart} (hp : b.Mem p)
    (hd : diagonalsCheck (seamCell b)=true) (hη : 0< spacing (seamCell b)) :
    2*ac*energy (chartPoint p)=planarRegularized (seamPoint b p)+zeroMode (seamPoint b p)+
      layerValue (seamPoint b p) := by
  let q := seamPoint b p
  let B := seamCell b
  have hm : B.Mem q := seamPoint_mem hp
  have h := diagonalsCheck_sound hd
  have r : 0< q 0 := (show (0:ℝ)<(coord B 0).lo by exact_mod_cast h.1).trans_le (endpoints (coord_sound hm 0)).1
  have t : 0< q 1 := (show (0:ℝ)<(coord B 1).lo by exact_mod_cast h.2.1).trans_le (endpoints (coord_sound hm 1)).1
  have e := spacing_sound hm
  have η : (0:ℝ)<(spacing B : ℝ) := by exact_mod_cast hη
  have id := (chart_energy_planar q r t (η.trans_le e.1) (by linarith only [η,e.2])).2
  rw [seamPoint_energy b p] at id
  exact id

/-- A passing sharpened check is a strict FCC leaf at every point of the box. -/
theorem energy_fcc_lt_of_sharpPass {raw : Cell} (ok : sharpPass raw=true) {p : Chart} (hp : raw.Mem p) :
    energy fcc< energy (chartPoint p) := by
  have h1 := sharpPass_sound ok hp
  have layer : retainedCheckS raw 2=true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).2).1
  simp only [retainedCheckS,Bool.and_eq_true] at layer
  have hd := layer.1.1
  have hη : 0< spacing (seamCell raw) := of_decide_eq_true layer.1.2
  have h2 := addressed_energy_planar_of_guards hp hd hη
  let q := seamPoint raw p
  let B := seamCell raw
  have hm : B.Mem q := seamPoint_mem hp
  have h := diagonalsCheck_sound hd
  have r : 0< q 0 := (show (0:ℝ)<(coord B 0).lo by exact_mod_cast h.1).trans_le (endpoints (coord_sound hm 0)).1
  have t : 0< q 1 := (show (0:ℝ)<(coord B 1).lo by exact_mod_cast h.2.1).trans_le (endpoints (coord_sound hm 1)).1
  have h3 := planarRegularized_ge_triangle q r t
  have hac := ac_positive
  unfold triangularRelaxation at h1
  have h4 : 2*ac*energy fcc<2*ac*energy (chartPoint p) := by linarith
  exact lt_of_mul_lt_mul_left h4 (by positivity)

def overlaySharpCheck (w : WitnessRef) (b : Cell) : Bool :=
  decide (w.route=Route.strictFCC) && sharpPass b

theorem overlaySharpCheck_sound : SoundCheck overlaySharpCheck := by
  intro w b ok p hp _
  obtain ⟨route,pass⟩ := Bool.and_eq_true_iff.mp ok
  rw [of_decide_eq_true route]
  exact energy_fcc_lt_of_sharpPass pass hp

end BccSharp.Coulomb.CompactCover.OverlayPlanar
