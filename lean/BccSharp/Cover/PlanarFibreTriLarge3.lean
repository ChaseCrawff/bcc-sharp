import BccSharp.Cover.PlanarFibreTriLargeData

set_option autoImplicit false
set_option maxRecDepth 65536
set_option Elab.async false

/-! Generated: leaves 33–41 of `BccSharp.Cover.PlanarFibreTriLargeData`, one `decide +kernel`
evaluation of `boxOk` per leaf on its literal cell, and the equation identifying the
literal cell with the half-cell that `TriTree.ok` builds. `Elab.async false` checks
the theorems one at a time, so the kernel holds one leaf's terms at a time. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

theorem cell33_eq : (lowHalf (highHalf (lowHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) = cell33 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf33_ok : boxOk cell33 pt33 = true := by decide +kernel
theorem cell34_eq : (lowHalf (highHalf (highHalf (lowHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell34 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf34_ok : boxOk cell34 pt34 = true := by decide +kernel
theorem cell35_eq : (highHalf (highHalf (highHalf (lowHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell35 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf35_ok : boxOk cell35 pt35 = true := by decide +kernel
theorem cell36_eq : (lowHalf (lowHalf (highHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) = cell36 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf36_ok : boxOk cell36 pt36 = true := by decide +kernel
theorem cell37_eq : (lowHalf (highHalf (lowHalf (highHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell37 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf37_ok : boxOk cell37 pt37 = true := by decide +kernel
theorem cell38_eq : (highHalf (highHalf (lowHalf (highHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell38 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf38_ok : boxOk cell38 pt38 = true := by decide +kernel
theorem cell39_eq : (lowHalf (highHalf (highHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) = cell39 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf39_ok : boxOk cell39 pt39 = true := by decide +kernel
theorem cell40_eq : (lowHalf (highHalf (highHalf (highHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell40 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf40_ok : boxOk cell40 pt40 = true := by decide +kernel
theorem cell41_eq : (highHalf (highHalf (highHalf (highHalf (highHalf (highHalf box0 5) 6) 0) 1) 2) 7) = cell41 := cell_eq_of (by decide +kernel) (by decide +kernel)
theorem leaf41_ok : boxOk cell41 pt41 = true := by decide +kernel

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Large
