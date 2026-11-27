import BccSharp.Cover.LayeredFarPilotPlanarFibre

/-! # Negative controls of the far-annulus transport check

`decide +kernel` proves `Layered.farTransportOk … = false` in two cases:

* `control0`: a HalfShift relative box (route local_basin, half bits 111) on which
  the interval bound `primalLo` does not certify that the registration's
  annular images clear `13/10` (least `primalLo` below `169/100`), so `annFarOk`
  fails (the untrusted test's `fail` class);
* `control1`: the first PlanarFibre pilot box and registration of
  `BccSharp.Cover.LayeredFarPilotPlanarFibre` with the wrap moved by one lattice step in the
  first coordinate, so that some odd annular images no longer clear `13/10`.

Generated. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.FarControls

-- HalfShift [700741, '3cffffbc931bc8207ac4', -1, 'local_basin'] hint 2.818030e-03 cost estimate 2.050659
noncomputable def box0 : Cell :=
  ⟨![(439/512 : ℚ), (205/256 : ℚ), (3/8 : ℚ), (5/32 : ℚ), (1/16 : ℚ), (15/32 : ℚ), (-1/2 : ℚ), (31/64 : ℚ)],
    ![(895/1024 : ℚ), (417/512 : ℚ), (13/32 : ℚ), (3/16 : ℚ), (3/32 : ℚ), (31/64 : ℚ), (-31/64 : ℚ), (1/2 : ℚ)]⟩
noncomputable def reg0 : JLeaf.RegData :=
  { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
    N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
    U := ![![(77671075232526/140737490095151 : ℚ), (77665185754747/140737490095151 : ℚ), (87990704691954/140737490095151 : ℚ)], ![(-117354016101771/140737490095151 : ℚ), (52751954152794/140737490095151 : ℚ), (57029004516382/140737490095151 : ℚ)], ![(-1509998440822/140737490095151 : ℚ), (-104844605836566/140737490095151 : ℚ), (93874222499931/140737490095151 : ℚ)]]
    f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
    wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem control0 : farTransportOk reg0 box0 ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] = false := by decide +kernel

theorem control1 :
    farTransportOk PilotFarPlanarFibre.reg0 PilotFarPlanarFibre.box0 ![(2 : ℤ), (1 : ℤ), (1 : ℤ)] = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.Layered.FarControls
