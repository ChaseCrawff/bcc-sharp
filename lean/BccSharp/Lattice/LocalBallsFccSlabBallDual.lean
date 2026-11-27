import BccSharp.Lattice.LocalBallsFccData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! FCC curvature: fixed-point Hessian sums of the dual family on box `ball`,
one slab per declaration. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

abbrev SlabP_ball_dual (i : ℕ) : Prop :=
  slabCheck true (cartArg .fcc true (cscale true) (pick cmet_ball_dual)) radius ((i : ℤ) - (radius : ℤ)) (pickSlab cslab_ball_dual ((i : ℤ) - (radius : ℤ)))

theorem slab_ball_dual_0 : SlabP_ball_dual 0 := by decide +kernel

theorem slab_ball_dual_1 : SlabP_ball_dual 1 := by decide +kernel

theorem slab_ball_dual_2 : SlabP_ball_dual 2 := by decide +kernel

theorem slab_ball_dual_3 : SlabP_ball_dual 3 := by decide +kernel

theorem slab_ball_dual_4 : SlabP_ball_dual 4 := by decide +kernel

theorem slab_ball_dual_5 : SlabP_ball_dual 5 := by decide +kernel

theorem slab_ball_dual_6 : SlabP_ball_dual 6 := by decide +kernel

theorem slab_ball_dual_7 : SlabP_ball_dual 7 := by decide +kernel

theorem slab_ball_dual_8 : SlabP_ball_dual 8 := by decide +kernel

theorem slab_ball_dual_9 : SlabP_ball_dual 9 := by decide +kernel

theorem slab_ball_dual_10 : SlabP_ball_dual 10 := by decide +kernel

theorem slabs_ball_dual : ∀ a ∈ side radius, slabCheck true (cartArg .fcc true (cscale true) (pick cmet_ball_dual)) radius a (pickSlab cslab_ball_dual a) = true := by
  apply forall_side
  intro i hi
  have hb : i < 11 := by
    have h := List.mem_range.mp hi
    simpa [radius] using h
  show SlabP_ball_dual i
  match i, hb with
    | 0, _ => exact slab_ball_dual_0
    | 1, _ => exact slab_ball_dual_1
    | 2, _ => exact slab_ball_dual_2
    | 3, _ => exact slab_ball_dual_3
    | 4, _ => exact slab_ball_dual_4
    | 5, _ => exact slab_ball_dual_5
    | 6, _ => exact slab_ball_dual_6
    | 7, _ => exact slab_ball_dual_7
    | 8, _ => exact slab_ball_dual_8
    | 9, _ => exact slab_ball_dual_9
    | 10, _ => exact slab_ball_dual_10
    | k + 11, h => exact absurd h (by omega)

end BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
