import BccSharp.Cover.PlanarFibreTriLargeData

set_option autoImplicit false
set_option maxRecDepth 65536
set_option Elab.async false

/-! Generated: leaves 22–32 of `BccSharp.Cover.PlanarFibreTriLargeData`, one `decide +kernel`
evaluation of `boxOk` per leaf on its literal cell, and the equation identifying the
literal cell with the half-cell that `TriTree.ok` builds. `Elab.async false` checks
the theorems one at a time, so the kernel holds one leaf's terms at a time. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

theorem cell22_eq : (highHalf (highHalf (highHalf (highHalf (lowHalf box0 5) 6) 0) 1) 2) = cell22 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf22_ok : boxOk cell22 pt22 = true := by decide +kernel
theorem cell23_eq : (lowHalf (lowHalf (lowHalf (highHalf box0 5) 6) 0) 1) = cell23 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf23_ok : boxOk cell23 pt23 = true := by decide +kernel
theorem cell24_eq : (lowHalf (highHalf (lowHalf (lowHalf (highHalf box0 5) 6) 0) 1) 2) = cell24 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf24_ok : boxOk cell24 pt24 = true := by decide +kernel
theorem cell25_eq : (highHalf (highHalf (lowHalf (lowHalf (highHalf box0 5) 6) 0) 1) 2) = cell25 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf25_ok : boxOk cell25 pt25 = true := by decide +kernel
theorem cell26_eq : (lowHalf (lowHalf (highHalf (lowHalf (highHalf box0 5) 6) 0) 1) 2) = cell26 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf26_ok : boxOk cell26 pt26 = true := by decide +kernel
theorem cell27_eq : (lowHalf (highHalf (lowHalf (highHalf (lowHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell27 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf27_ok : boxOk cell27 pt27 = true := by decide +kernel
theorem cell28_eq : (highHalf (highHalf (lowHalf (highHalf (lowHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell28 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf28_ok : boxOk cell28 pt28 = true := by decide +kernel
theorem cell29_eq : (lowHalf (highHalf (highHalf (lowHalf (highHalf box0 5) 6) 0) 1) 2) = cell29 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf29_ok : boxOk cell29 pt29 = true := by decide +kernel
theorem cell30_eq : (highHalf (highHalf (highHalf (lowHalf (highHalf box0 5) 6) 0) 1) 2) = cell30 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf30_ok : boxOk cell30 pt30 = true := by decide +kernel
theorem cell31_eq : (lowHalf (lowHalf (lowHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) = cell31 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf31_ok : boxOk cell31 pt31 = true := by decide +kernel
theorem cell32_eq : (highHalf (lowHalf (lowHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) = cell32 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf32_ok : boxOk cell32 pt32 = true := by decide +kernel

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
