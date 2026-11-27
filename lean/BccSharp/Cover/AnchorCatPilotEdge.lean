import BccSharp.Cover.LayeredCatRoute

/-! # The anchor's capped defect is one on HalfShift boxes, in the kernel

For single HalfShift relative boxes whose anchor class has no BCC registration of
cost below one, `decide +kernel` checks `Layered.catalogueOk`, and
`catalogueOk_sound` gives `D(anchor) = 1` at every good point of the box.
Generated; the boxes are the Stage6 atoms of the
Corner jobs (geometry folder `cornerRule`) named in the comments.

The two boxes sit at the edges of the catalogue's work on the 12,719 HalfShift
relative items without a registration. On box 0 (Stage6 700747) 24 candidate
triples pass the determinant, class and pair tests, and only the frame bound
rejects them (least `frameLo` about 0.01202, against `1/100`). Box 1 (Stage6
790317) is one of the twelve boxes with the most candidate triples, 4,928, of
which 672 have determinant 8. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.CatPilotEdge

noncomputable def box0 : Cell :=
  ⟨![(439/512 : ℚ), (403/512 : ℚ), (13/32 : ℚ), (7/32 : ℚ), (5/32 : ℚ), (31/64 : ℚ), (-1/2 : ℚ), (31/64 : ℚ)],
    ![(895/1024 : ℚ), (205/256 : ℚ), (7/16 : ℚ), (1/4 : ℚ), (3/16 : ℚ), (1/2 : ℚ), (-31/64 : ℚ), (1/2 : ℚ)]⟩
theorem cat0 : catalogueOk box0 ![(-1 : ℤ), (-1 : ℤ), (-1 : ℤ)] = true := by decide +kernel

theorem anchor0 (p : Chart) (hp : box0.Mem p) (gp : good p) :
    defect (anchorOf (chartPoint p) (fun i => ((![(-1 : ℤ), (-1 : ℤ), (-1 : ℤ)] : IntVec) i : ℝ) / 2)) = 1 :=
  catalogueOk_sound box0 ![(-1 : ℤ), (-1 : ℤ), (-1 : ℤ)] cat0 p hp gp

noncomputable def box1 : Cell :=
  ⟨![(1773/2048 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (29/64 : ℚ), (21/64 : ℚ), (31/64 : ℚ), (-1/2 : ℚ), (31/64 : ℚ)],
    ![(895/1024 : ℚ), (403/512 : ℚ), (1/2 : ℚ), (15/32 : ℚ), (11/32 : ℚ), (1/2 : ℚ), (-15/32 : ℚ), (1/2 : ℚ)]⟩
theorem cat1 : catalogueOk box1 ![(-1 : ℤ), (-1 : ℤ), (-1 : ℤ)] = true := by decide +kernel

theorem anchor1 (p : Chart) (hp : box1.Mem p) (gp : good p) :
    defect (anchorOf (chartPoint p) (fun i => ((![(-1 : ℤ), (-1 : ℤ), (-1 : ℤ)] : IntVec) i : ℝ) / 2)) = 1 :=
  catalogueOk_sound box1 ![(-1 : ℤ), (-1 : ℤ), (-1 : ℤ)] cat1 p hp gp

end BccSharp.Coulomb.CompactCover.Layered.CatPilotEdge
