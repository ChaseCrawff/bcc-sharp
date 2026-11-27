import BccSharp.Lattice.LocalBallsFccData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! FCC curvature: fixed-point Hessian sums of the direct family on box `ball`,
one slab per declaration. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

abbrev SlabP_ball_direct (i : ℕ) : Prop :=
  slabCheck false (cartArg .fcc false (cscale false) (pick cmet_ball_direct)) radius ((i : ℤ) - (radius : ℤ)) (pickSlab cslab_ball_direct ((i : ℤ) - (radius : ℤ)))

theorem slab_ball_direct_0 : SlabP_ball_direct 0 := by decide +kernel

theorem slab_ball_direct_1 : SlabP_ball_direct 1 := by decide +kernel

theorem slab_ball_direct_2 : SlabP_ball_direct 2 := by decide +kernel

theorem slab_ball_direct_3 : SlabP_ball_direct 3 := by decide +kernel

theorem slab_ball_direct_4 : SlabP_ball_direct 4 := by decide +kernel

theorem slab_ball_direct_5 : SlabP_ball_direct 5 := by decide +kernel

theorem slab_ball_direct_6 : SlabP_ball_direct 6 := by decide +kernel

theorem slab_ball_direct_7 : SlabP_ball_direct 7 := by decide +kernel

theorem slab_ball_direct_8 : SlabP_ball_direct 8 := by decide +kernel

theorem slab_ball_direct_9 : SlabP_ball_direct 9 := by decide +kernel

theorem slab_ball_direct_10 : SlabP_ball_direct 10 := by decide +kernel

theorem slabs_ball_direct : ∀ a ∈ side radius, slabCheck false (cartArg .fcc false (cscale false) (pick cmet_ball_direct)) radius a (pickSlab cslab_ball_direct a) = true := by
  apply forall_side
  intro i hi
  have hb : i < 11 := by
    have h := List.mem_range.mp hi
    simpa [radius] using h
  show SlabP_ball_direct i
  match i, hb with
    | 0, _ => exact slab_ball_direct_0
    | 1, _ => exact slab_ball_direct_1
    | 2, _ => exact slab_ball_direct_2
    | 3, _ => exact slab_ball_direct_3
    | 4, _ => exact slab_ball_direct_4
    | 5, _ => exact slab_ball_direct_5
    | 6, _ => exact slab_ball_direct_6
    | 7, _ => exact slab_ball_direct_7
    | 8, _ => exact slab_ball_direct_8
    | 9, _ => exact slab_ball_direct_9
    | 10, _ => exact slab_ball_direct_10
    | k + 11, h => exact absurd h (by omega)

end BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
