import BccSharp.Lattice.Atlas.Atlases
import BccSharp.Lattice.Forest

set_option autoImplicit false

/-! `LatticeCase` (the lattice theorem) with no premises.

`StrainAtlas.latticeCase_from_tangent_forest_atlases` proves `LatticeCase` from
the premises of a checked global forest; its atlas premise is discharged by the
two checked strain atlases (`strainAtlases_closed`). The forest premises come
from the Lattice global forest of the tangent route (`TangentCover.Forest`,
`BccSharp.Lattice.Forest`: the `4^5` grid, `grid_check`, the forest and
`forest_checked`) and from the proved tangent tables (`Tables.tables` and
`Tables.tables_valid`, `BccSharp.Lattice.TangentTables`).

`LatticeCase` is the one-site statement the cover uses: nonnegativity of the
deficit at every determinant-1/2 one-site lattice, and zero deficit only at
rigid copies of BCC and FCC. The converse (BCC and FCC have zero deficit) is
proved separately (`bccValues`, `fccValues`). Build `BccSharp.Lattice.Forest` and the
atlas modules first. -/

namespace BccSharp.Coulomb.BravaisCover.StrainAtlas
open BccSharp.Coulomb.BravaisCover.TangentCover

/-- `LatticeCase` (the lattice theorem), proved from the checked global forest on the `4^5`
grid with the proved tangent tables and the two checked strain atlases. -/
theorem latticeCase_proved : LatticeCase :=
  latticeCase_from_tangent_forest_atlases (by decide) Forest.grid Forest.grid_check
    Tables.tables Tables.tables_valid Forest.forest Forest.forest_checked

end BccSharp.Coulomb.BravaisCover.StrainAtlas
