import BccSharp.Cover.PlanarFibreTriLargeData

set_option autoImplicit false
set_option maxRecDepth 65536
set_option Elab.async false

/-! Generated: leaves 11–21 of `BccSharp.Cover.PlanarFibreTriLargeData`, one `decide +kernel`
evaluation of `boxOk` per leaf on its literal cell, and the equation identifying the
literal cell with the half-cell that `TriTree.ok` builds. `Elab.async false` checks
the theorems one at a time, so the kernel holds one leaf's terms at a time. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

theorem cell11_eq : (highHalf (lowHalf (highHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell11 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf11_ok : boxOk cell11 pt11 = true := by decide +kernel
theorem cell12_eq : (lowHalf (highHalf (highHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell12 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf12_ok : boxOk cell12 pt12 = true := by decide +kernel
theorem cell13_eq : (highHalf (highHalf (highHalf (highHalf (lowHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell13 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf13_ok : boxOk cell13 pt13 = true := by decide +kernel
theorem cell14_eq : (lowHalf (lowHalf (lowHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) = cell14 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf14_ok : boxOk cell14 pt14 = true := by decide +kernel
theorem cell15_eq : (highHalf (lowHalf (lowHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) = cell15 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf15_ok : boxOk cell15 pt15 = true := by decide +kernel
theorem cell16_eq : (lowHalf (lowHalf (highHalf (lowHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell16 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf16_ok : boxOk cell16 pt16 = true := by decide +kernel
theorem cell17_eq : (highHalf (lowHalf (highHalf (lowHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) 7) = cell17 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf17_ok : boxOk cell17 pt17 = true := by decide +kernel
theorem cell18_eq : (highHalf (highHalf (lowHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) = cell18 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf18_ok : boxOk cell18 pt18 = true := by decide +kernel
theorem cell19_eq : (lowHalf (lowHalf (highHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) = cell19 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf19_ok : boxOk cell19 pt19 = true := by decide +kernel
theorem cell20_eq : (highHalf (lowHalf (highHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) = cell20 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf20_ok : boxOk cell20 pt20 = true := by decide +kernel
theorem cell21_eq : (lowHalf (highHalf (highHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) = cell21 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf21_ok : boxOk cell21 pt21 = true := by decide +kernel

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
