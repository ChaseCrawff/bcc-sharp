import BccSharp.Lattice.LocalBallsBccData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! BCC curvature: fixed-point Hessian sums of the dual family on box `q11`,
one slab per declaration. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.BccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

abbrev SlabP_q11_dual (i : ℕ) : Prop :=
  slabCheck true (cartArg .bcc true (cscale true) (pick cmet_q11_dual)) radius ((i : ℤ) - (radius : ℤ)) (pickSlab cslab_q11_dual ((i : ℤ) - (radius : ℤ)))

theorem slab_q11_dual_0 : SlabP_q11_dual 0 := by decide +kernel

theorem slab_q11_dual_1 : SlabP_q11_dual 1 := by decide +kernel

theorem slab_q11_dual_2 : SlabP_q11_dual 2 := by decide +kernel

theorem slab_q11_dual_3 : SlabP_q11_dual 3 := by decide +kernel

theorem slab_q11_dual_4 : SlabP_q11_dual 4 := by decide +kernel

theorem slab_q11_dual_5 : SlabP_q11_dual 5 := by decide +kernel

theorem slab_q11_dual_6 : SlabP_q11_dual 6 := by decide +kernel

theorem slab_q11_dual_7 : SlabP_q11_dual 7 := by decide +kernel

theorem slab_q11_dual_8 : SlabP_q11_dual 8 := by decide +kernel

theorem slab_q11_dual_9 : SlabP_q11_dual 9 := by decide +kernel

theorem slab_q11_dual_10 : SlabP_q11_dual 10 := by decide +kernel

theorem slab_q11_dual_11 : SlabP_q11_dual 11 := by decide +kernel

theorem slab_q11_dual_12 : SlabP_q11_dual 12 := by decide +kernel

theorem slabs_q11_dual : ∀ a ∈ side radius, slabCheck true (cartArg .bcc true (cscale true) (pick cmet_q11_dual)) radius a (pickSlab cslab_q11_dual a) = true := by
  apply forall_side
  intro i hi
  have hb : i < 13 := by
    have h := List.mem_range.mp hi
    simpa [radius] using h
  show SlabP_q11_dual i
  match i, hb with
    | 0, _ => exact slab_q11_dual_0
    | 1, _ => exact slab_q11_dual_1
    | 2, _ => exact slab_q11_dual_2
    | 3, _ => exact slab_q11_dual_3
    | 4, _ => exact slab_q11_dual_4
    | 5, _ => exact slab_q11_dual_5
    | 6, _ => exact slab_q11_dual_6
    | 7, _ => exact slab_q11_dual_7
    | 8, _ => exact slab_q11_dual_8
    | 9, _ => exact slab_q11_dual_9
    | 10, _ => exact slab_q11_dual_10
    | 11, _ => exact slab_q11_dual_11
    | 12, _ => exact slab_q11_dual_12
    | k + 13, h => exact absurd h (by omega)

end BccSharp.Coulomb.BravaisCover.FixedLocal.BccBall
