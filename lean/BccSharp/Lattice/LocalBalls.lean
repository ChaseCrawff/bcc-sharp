import BccSharp.Lattice.LocalBallsBcc
import BccSharp.Lattice.LocalBallsFcc
import BccSharp.Lattice.KzTransport

set_option autoImplicit false

/-! The Lattice local balls, closed. `localBalls` discharges the
`ballProof` premise of `latticeCase_from_checked_atlases` for both
references, so `LatticeCase` follows from the global grid forest and
strain atlas checks alone. No forest or atlas passing those checks is
known;. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage

theorem localBalls : ∀ ref, NonzeroLocalStrain ref
  | .bcc => FixedLocal.BccBall.nonzeroLocalStrain_bcc
  | .fcc => FixedLocal.FccBall.nonzeroLocalStrain_fcc

/-- `LatticeCase` from the addressed global forest and the two checked
strain atlases alone; the local-ball analytic input is proved. -/
theorem latticeCase_from_checked_covers (g : Grid 16) (gOK : g.check globalRoot=true)
    (forest : (Fin 2 → Fin 16) → (Fin 3 → Fin 16) → AddressedTree Payload)
    (checked : ∀ owner suffix, (forest owner suffix).check globalWithHandoffsCheck
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix))=true)
    (atlas : Reference → AtlasRows) (atlasOK : ∀ ref, (atlas ref).check ref=true) : LatticeCase :=
  KZ.latticeCase_from_checked_atlases g gOK forest checked atlas atlasOK localBalls

end BccSharp.Coulomb.BravaisCover
