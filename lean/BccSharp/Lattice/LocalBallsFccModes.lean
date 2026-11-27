import BccSharp.Lattice.LocalBallsFccData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! FCC differentiation witness: every mode of the cube has a fixed-point jet on
`analyticLocalBox`, checked slab by slab. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

abbrev ModesP_direct (i : ℕ) : Prop :=
  slabModes false (fquad (analyticData.index false)) radius ((i : ℤ) - (radius : ℤ)) = true

theorem analyticModes_direct_0 : ModesP_direct 0 := by decide +kernel

theorem analyticModes_direct_1 : ModesP_direct 1 := by decide +kernel

theorem analyticModes_direct_2 : ModesP_direct 2 := by decide +kernel

theorem analyticModes_direct_3 : ModesP_direct 3 := by decide +kernel

theorem analyticModes_direct_4 : ModesP_direct 4 := by decide +kernel

theorem analyticModes_direct_5 : ModesP_direct 5 := by decide +kernel

theorem analyticModes_direct_6 : ModesP_direct 6 := by decide +kernel

theorem analyticModes_direct_7 : ModesP_direct 7 := by decide +kernel

theorem analyticModes_direct_8 : ModesP_direct 8 := by decide +kernel

theorem analyticModes_direct_9 : ModesP_direct 9 := by decide +kernel

theorem analyticModes_direct_10 : ModesP_direct 10 := by decide +kernel

theorem analyticModes_direct : ∀ a ∈ side radius, slabModes false (fquad (analyticData.index false)) radius a = true := by
  apply forall_side
  intro i hi
  have hb : i < 11 := by
    have h := List.mem_range.mp hi
    simpa [radius] using h
  show ModesP_direct i
  match i, hb with
    | 0, _ => exact analyticModes_direct_0
    | 1, _ => exact analyticModes_direct_1
    | 2, _ => exact analyticModes_direct_2
    | 3, _ => exact analyticModes_direct_3
    | 4, _ => exact analyticModes_direct_4
    | 5, _ => exact analyticModes_direct_5
    | 6, _ => exact analyticModes_direct_6
    | 7, _ => exact analyticModes_direct_7
    | 8, _ => exact analyticModes_direct_8
    | 9, _ => exact analyticModes_direct_9
    | 10, _ => exact analyticModes_direct_10
    | k + 11, h => exact absurd h (by omega)

abbrev ModesP_dual (i : ℕ) : Prop :=
  slabModes true (fquad (analyticData.index true)) radius ((i : ℤ) - (radius : ℤ)) = true

theorem analyticModes_dual_0 : ModesP_dual 0 := by decide +kernel

theorem analyticModes_dual_1 : ModesP_dual 1 := by decide +kernel

theorem analyticModes_dual_2 : ModesP_dual 2 := by decide +kernel

theorem analyticModes_dual_3 : ModesP_dual 3 := by decide +kernel

theorem analyticModes_dual_4 : ModesP_dual 4 := by decide +kernel

theorem analyticModes_dual_5 : ModesP_dual 5 := by decide +kernel

theorem analyticModes_dual_6 : ModesP_dual 6 := by decide +kernel

theorem analyticModes_dual_7 : ModesP_dual 7 := by decide +kernel

theorem analyticModes_dual_8 : ModesP_dual 8 := by decide +kernel

theorem analyticModes_dual_9 : ModesP_dual 9 := by decide +kernel

theorem analyticModes_dual_10 : ModesP_dual 10 := by decide +kernel

theorem analyticModes_dual : ∀ a ∈ side radius, slabModes true (fquad (analyticData.index true)) radius a = true := by
  apply forall_side
  intro i hi
  have hb : i < 11 := by
    have h := List.mem_range.mp hi
    simpa [radius] using h
  show ModesP_dual i
  match i, hb with
    | 0, _ => exact analyticModes_dual_0
    | 1, _ => exact analyticModes_dual_1
    | 2, _ => exact analyticModes_dual_2
    | 3, _ => exact analyticModes_dual_3
    | 4, _ => exact analyticModes_dual_4
    | 5, _ => exact analyticModes_dual_5
    | 6, _ => exact analyticModes_dual_6
    | 7, _ => exact analyticModes_dual_7
    | 8, _ => exact analyticModes_dual_8
    | 9, _ => exact analyticModes_dual_9
    | 10, _ => exact analyticModes_dual_10
    | k + 11, h => exact absurd h (by omega)

theorem analyticModes : ∀ dual, ∀ a ∈ side analyticData.radius,
    slabModes dual (fquad (analyticData.index dual)) analyticData.radius a = true := by
  intro dual
  cases dual
  · exact analyticModes_direct
  · exact analyticModes_dual

end BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
