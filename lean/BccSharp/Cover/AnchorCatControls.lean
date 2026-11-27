import BccSharp.Cover.LayeredCatRoute
import BccSharp.Cover.LayeredFarPilotHalfShift
import BccSharp.Cover.LayeredFarPilotPlanarFibre

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-! # Negative controls of the catalogue check

`decide +kernel` proves `Layered.catalogueOk … = false` on two boxes whose
all-half anchor does have a BCC registration of cost below one, so a candidate
triple passes every test (determinant `8`, class, pair bands, frame bound):

* `control0`: the thinnest over-budget HalfShift relative box `PilotFarHalfShift.box0`
  (its literal registration passes `farTransportOk` there);
* `control1`: the thinnest over-budget PlanarFibre layered box `PilotFarPlanarFibre.box0`. -/

namespace BccSharp.Coulomb.CompactCover.Layered.CatControls
open BccSharp.Coulomb.CompactCover.Layered

theorem control0 : catalogueOk PilotFarHalfShift.box0 allHalfZ = false := by decide +kernel

theorem control1 : catalogueOk PilotFarPlanarFibre.box0 allHalfZ = false := by decide +kernel

end BccSharp.Coulomb.CompactCover.Layered.CatControls
