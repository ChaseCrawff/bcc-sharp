import BccSharp.Cover.PlanarFibreTriLargeData

set_option autoImplicit false
set_option maxRecDepth 65536
set_option Elab.async false

/-! Generated: leaves 0–10 of `BccSharp.Cover.PlanarFibreTriLargeData`, one `decide +kernel`
evaluation of `boxOk` per leaf on its literal cell, and the equation identifying the
literal cell with the half-cell that `TriTree.ok` builds. `Elab.async false` checks
the theorems one at a time, so the kernel holds one leaf's terms at a time. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

theorem cell0_eq : (lowHalf (lowHalf (lowHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) = cell0 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf0_ok : boxOk cell0 pt0 = true := by decide +kernel
theorem cell1_eq : (highHalf (lowHalf (lowHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) = cell1 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf1_ok : boxOk cell1 pt1 = true := by decide +kernel
theorem cell2_eq : (lowHalf (lowHalf (highHalf (lowHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell2 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf2_ok : boxOk cell2 pt2 = true := by decide +kernel
theorem cell3_eq : (highHalf (lowHalf (highHalf (lowHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell3 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf3_ok : boxOk cell3 pt3 = true := by decide +kernel
theorem cell4_eq : (lowHalf (highHalf (highHalf (lowHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell4 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf4_ok : boxOk cell4 pt4 = true := by decide +kernel
theorem cell5_eq : (highHalf (highHalf (highHalf (lowHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell5 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf5_ok : boxOk cell5 pt5 = true := by decide +kernel
theorem cell6_eq : (lowHalf (lowHalf (lowHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell6 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf6_ok : boxOk cell6 pt6 = true := by decide +kernel
theorem cell7_eq : (highHalf (lowHalf (lowHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell7 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf7_ok : boxOk cell7 pt7 = true := by decide +kernel
theorem cell8_eq : (lowHalf (highHalf (lowHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell8 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf8_ok : boxOk cell8 pt8 = true := by decide +kernel
theorem cell9_eq : (highHalf (highHalf (lowHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell9 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf9_ok : boxOk cell9 pt9 = true := by decide +kernel
theorem cell10_eq : (lowHalf (lowHalf (highHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell10 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf10_ok : boxOk cell10 pt10 = true := by decide +kernel

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
