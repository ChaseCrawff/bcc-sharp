import BccSharp.Cover.Stage4Thin1
import BccSharp.Cover.Stage4Thin2

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Negative controls of `Stage4Stage5a.stage4stage5aCheck`

Each statement is a kernel evaluation (`decide +kernel`) of the check on a box and
certificate of `BccSharp.Cover.Stage4Thin1` or `BccSharp.Cover.Stage4Thin2` that the check must reject:

* the cubic atlas tile `2000004` (`r s` up to `1.0039`) with the far payment and the
  separation `sepOk` (`r s < 1`) instead of `sepCubicOk`;
* the thinnest Stage4 source `4014` with its wrap moved by `(1, 0, 0)`: the
  registration's wrap no longer matches the anchor (this control fails on several
  conjuncts at once, the wrap match, the cost and the gain, so it is not a sharp one);
* the same item on route `strictDeficit` with its optical payment (dispatch by route);
* the same item under the source `adaptiveRoute` (dispatch by exact source string).

`BccSharp.Cover.Stage4Stage5aOpen` adds three rejections of sources that the forecast leaves open. -/

namespace BccSharp.Coulomb.CompactCover.Stage4Stage5a.Controls
open BccSharp.Coulomb.CompactCover.Stage4Stage5a
open BccSharp.Coulomb.CompactCover.Layered

theorem cubic_needs_sepCubic : stage4stage5aCheck (fun _ => some (.optical
    (.far true false Thin1.s2000004Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, "stage4/atlas", 2000004⟩ Thin1.s2000004Box = false := by
  decide +kernel

theorem cubic_with_sepCubic : stage4stage5aCheck (fun _ => some (.optical
    (.far true true Thin1.s2000004Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, "stage4/atlas", 2000004⟩ Thin1.s2000004Box = true :=
  Thin1.s2000004_check

theorem wrap_moved_rejected : stage4stage5aCheck (fun _ => some (.optical
    (.opay (.planarAnchor Thin2.s4014Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)]))))
    ⟨.relativeOptical, "stage4/optical", 4014⟩ Thin2.s4014Box = false := by
  decide +kernel

theorem route_rejected : stage4stage5aCheck (fun _ => some (.optical
    (.opay (.planarAnchor Thin2.s4014Cert ![(0 : ℤ), (0 : ℤ), (0 : ℤ)]))))
    ⟨.strictDeficit, "stage4/optical", 4014⟩ Thin2.s4014Box = false := by
  decide +kernel

theorem source_rejected : stage4stage5aCheck (fun _ => some (.optical
    (.opay (.planarAnchor Thin2.s4014Cert ![(0 : ℤ), (0 : ℤ), (0 : ℤ)]))))
    ⟨.relativeOptical, "adaptive-source", 4014⟩ Thin2.s4014Box = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.Stage4Stage5a.Controls
