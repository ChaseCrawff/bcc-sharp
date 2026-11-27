import BccSharp.Cover.PlanarFibreTriLarge0
import BccSharp.Cover.PlanarFibreTriLarge1
import BccSharp.Cover.PlanarFibreTriLarge2
import BccSharp.Cover.PlanarFibreTriLarge3

set_option autoImplicit false
set_option maxRecDepth 65536

/-! Generated: position 3251 from its leaf theorems (`simp only` unfolds the splits
of `TriTree.ok`, rewrites each half-cell to its literal cell and each leaf check to `true`;
no leaf is evaluated again). -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

theorem item0 : tree0.ok box0 = true := by
  simp only [tree0, TriTree.ok, cell0_eq, cell1_eq, cell2_eq, cell3_eq, cell4_eq, cell5_eq, cell6_eq, cell7_eq, cell8_eq, cell9_eq, cell10_eq, cell11_eq, cell12_eq, cell13_eq, cell14_eq, cell15_eq, cell16_eq, cell17_eq, cell18_eq, cell19_eq, cell20_eq, cell21_eq, cell22_eq, cell23_eq, cell24_eq, cell25_eq, cell26_eq, cell27_eq, cell28_eq, cell29_eq, cell30_eq, cell31_eq, cell32_eq, cell33_eq, cell34_eq, cell35_eq, cell36_eq, cell37_eq, cell38_eq, cell39_eq, cell40_eq, cell41_eq,
    leaf0_ok, leaf1_ok, leaf2_ok, leaf3_ok, leaf4_ok, leaf5_ok, leaf6_ok, leaf7_ok, leaf8_ok, leaf9_ok, leaf10_ok, leaf11_ok, leaf12_ok, leaf13_ok, leaf14_ok, leaf15_ok, leaf16_ok, leaf17_ok, leaf18_ok, leaf19_ok, leaf20_ok, leaf21_ok, leaf22_ok, leaf23_ok, leaf24_ok, leaf25_ok, leaf26_ok, leaf27_ok, leaf28_ok, leaf29_ok, leaf30_ok, leaf31_ok, leaf32_ok, leaf33_ok, leaf34_ok, leaf35_ok, leaf36_ok, leaf37_ok, leaf38_ok, leaf39_ok, leaf40_ok, leaf41_ok, Bool.and_self]
theorem request0 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree0) (hbox : q.target.box = box0) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree0 hpay ht (by rw [hbox]; exact item0)

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
