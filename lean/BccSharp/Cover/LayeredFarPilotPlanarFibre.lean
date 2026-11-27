import BccSharp.Cover.LayeredFarRoute

/-! # The relative defect bound on PlanarFibre layered boxes in the kernel

For single PlanarFibre layered boxes with a basin result (route local_basin, half
bits 111) whose registration cost bound `100 strain⁺ + 200 |R d|²⁺` exceeds
`1/2`, `decide +kernel` checks `Layered.farTransportOk` (the defect part of
`planarAnchorCertOkFar`), and `farTransportOk_sound` gives the relative defect bound
`D(p) ≤ D(anchor) + 200 |R d|²` on the whole box. The gain part of the PlanarAnchor
check (`splitOk`) fails on these boxes, so these are not request-level
results. Generated; the boxes are the PlanarFibre
restrictions of the JointDeficit roots (geometry folder `joint`) named in the comments. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.PilotFarPlanarFibre

noncomputable def box0 : Cell :=
  ⟨![(3529/4096 : ℚ), (205/256 : ℚ), (91/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (29/64 : ℚ), (15/32 : ℚ), (63/128 : ℚ)],
    ![(7075/8192 : ℚ), (1647/2048 : ℚ), (23/64 : ℚ), (1/64 : ℚ), (3/128 : ℚ), (15/32 : ℚ), (31/64 : ℚ), (1/2 : ℚ)]⟩
noncomputable def reg0 : JLeaf.RegData :=
  { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
    N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
    U := ![![(79771063759997/140737493859997 : ℚ), (81636805498416/140737493859997 : ℚ), (82334995916712/140737493859997 : ℚ)], ![(-115946068767144/140737493859997 : ℚ), (55856480802012/140737493859997 : ℚ), (56952654616373/140737493859997 : ℚ)], ![(358750659792/140737493859997 : ℚ), (-100112575226197/140737493859997 : ℚ), (98916054094044/140737493859997 : ℚ)]]
    f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
    wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item0 : farTransportOk reg0 box0 ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] = true := by decide +kernel

theorem transport0 (p : Chart) (hp : box0.Mem p) (gp : good p) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec ![(1 : ℤ), (1 : ℤ), (1 : ℤ)])) :=
  farTransportOk_sound reg0 box0 ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] item0 p hp gp

noncomputable def box1 : Cell :=
  ⟨![(3529/4096 : ℚ), (205/256 : ℚ), (91/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (15/32 : ℚ), (29/64 : ℚ), (63/128 : ℚ)],
    ![(7075/8192 : ℚ), (1647/2048 : ℚ), (23/64 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (31/64 : ℚ), (15/32 : ℚ), (1/2 : ℚ)]⟩
noncomputable def reg1 : JLeaf.RegData :=
  { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
    N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
    U := ![![(7977062057817/14073747834601 : ℚ), (8163561944276/14073747834601 : ℚ), (8233657475244/14073747834601 : ℚ)], ![(-57973432851212/70368739173005 : ℚ), (28038735363459/70368739173005 : ℚ), (5673340657716/14073747834601 : ℚ)], ![(3891568668/5412979936385 : ℚ), (-3845765504676/5412979936385 : ℚ), (761851017731/1082595987277 : ℚ)]]
    f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
    wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item1 : farTransportOk reg1 box1 ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] = true := by decide +kernel

theorem transport1 (p : Chart) (hp : box1.Mem p) (gp : good p) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec ![(1 : ℤ), (1 : ℤ), (1 : ℤ)])) :=
  farTransportOk_sound reg1 box1 ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] item1 p hp gp

noncomputable def box2 : Cell :=
  ⟨![(3529/4096 : ℚ), (205/256 : ℚ), (91/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (15/32 : ℚ), (29/64 : ℚ), (-1/2 : ℚ)],
    ![(7075/8192 : ℚ), (1647/2048 : ℚ), (23/64 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (61/128 : ℚ), (15/32 : ℚ), (-63/128 : ℚ)]⟩
noncomputable def reg2 : JLeaf.RegData :=
  { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
    N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
    U := ![![(7977062057817/14073747834601 : ℚ), (8163561944276/14073747834601 : ℚ), (8233657475244/14073747834601 : ℚ)], ![(-57973432851212/70368739173005 : ℚ), (28038735363459/70368739173005 : ℚ), (5673340657716/14073747834601 : ℚ)], ![(3891568668/5412979936385 : ℚ), (-3845765504676/5412979936385 : ℚ), (761851017731/1082595987277 : ℚ)]]
    f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
    wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item2 : farTransportOk reg2 box2 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem transport2 (p : Chart) (hp : box2.Mem p) (gp : good p) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) halfAll) +
      200 * sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec ![(1 : ℤ), (1 : ℤ), (0 : ℤ)])) :=
  farTransportOk_sound reg2 box2 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] item2 p hp gp

end BccSharp.Coulomb.CompactCover.Layered.PilotFarPlanarFibre
