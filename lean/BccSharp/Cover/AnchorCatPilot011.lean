import BccSharp.Cover.LayeredCatRoute

/-! # The anchor's capped defect is one on HalfShift boxes, in the kernel

For single HalfShift relative boxes whose anchor class has no BCC registration of
cost below one, `decide +kernel` checks `Layered.catalogueOk`, and
`catalogueOk_sound` gives `D(anchor) = 1` at every good point of the box.
Generated; the boxes are the Stage6 atoms of the
Corner jobs (geometry folder `cornerRule`) named in the comments. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.CatPilot011

noncomputable def box0 : Cell :=
  ⟨![(1807/2048 : ℚ), (785/1024 : ℚ), (31/64 : ℚ), (7/16 : ℚ), (-23/64 : ℚ), (0 : ℚ), (31/64 : ℚ), (-1/2 : ℚ)],
    ![(57/64 : ℚ), (99/128 : ℚ), (1/2 : ℚ), (29/64 : ℚ), (-45/128 : ℚ), (1/64 : ℚ), (1/2 : ℚ), (-31/64 : ℚ)]⟩
theorem cat0 : catalogueOk box0 ![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] = true := by decide +kernel

theorem anchor0 (p : Chart) (hp : box0.Mem p) (gp : good p) :
    defect (anchorOf (chartPoint p) (fun i => ((![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] : IntVec) i : ℝ) / 2)) = 1 :=
  catalogueOk_sound box0 ![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] cat0 p hp gp

noncomputable def box1 : Cell :=
  ⟨![(1807/2048 : ℚ), (785/1024 : ℚ), (31/64 : ℚ), (29/64 : ℚ), (-3/8 : ℚ), (0 : ℚ), (31/64 : ℚ), (-1/2 : ℚ)],
    ![(57/64 : ℚ), (99/128 : ℚ), (1/2 : ℚ), (15/32 : ℚ), (-47/128 : ℚ), (1/64 : ℚ), (1/2 : ℚ), (-31/64 : ℚ)]⟩
theorem cat1 : catalogueOk box1 ![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] = true := by decide +kernel

theorem anchor1 (p : Chart) (hp : box1.Mem p) (gp : good p) :
    defect (anchorOf (chartPoint p) (fun i => ((![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] : IntVec) i : ℝ) / 2)) = 1 :=
  catalogueOk_sound box1 ![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] cat1 p hp gp

noncomputable def box2 : Cell :=
  ⟨![(1807/2048 : ℚ), (785/1024 : ℚ), (31/64 : ℚ), (29/64 : ℚ), (-47/128 : ℚ), (0 : ℚ), (15/32 : ℚ), (-1/2 : ℚ)],
    ![(57/64 : ℚ), (99/128 : ℚ), (1/2 : ℚ), (15/32 : ℚ), (-23/64 : ℚ), (1/64 : ℚ), (31/64 : ℚ), (-31/64 : ℚ)]⟩
theorem cat2 : catalogueOk box2 ![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] = true := by decide +kernel

theorem anchor2 (p : Chart) (hp : box2.Mem p) (gp : good p) :
    defect (anchorOf (chartPoint p) (fun i => ((![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] : IntVec) i : ℝ) / 2)) = 1 :=
  catalogueOk_sound box2 ![(0 : ℤ), (-1 : ℤ), (-1 : ℤ)] cat2 p hp gp

end BccSharp.Coulomb.CompactCover.Layered.CatPilot011
