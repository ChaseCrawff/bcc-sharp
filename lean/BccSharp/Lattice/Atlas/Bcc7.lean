import BccSharp.Lattice.Atlas.Data

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Strain atlas `.bcc`, fragments 595 to 687 (599 tangent leaves). Each fragment
is a checked atlas tree on its box, a chain of cuts of the strain root. Generated. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.StrainAtlas
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.StrainAtlas

noncomputable def bccFrag595Tree : ATree :=
  .cut 0 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag595 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 1 (28823037615171175 / 1152921504606846976 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag595Tree _ (by decide +kernel)

noncomputable def bccFrag596Tree : ATree :=
  .cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))

theorem bccFrag596 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag596Tree _ (by decide +kernel)

noncomputable def bccFrag597Tree : ATree :=
  .cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag597 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag597Tree _ (by decide +kernel)

noncomputable def bccFrag598Tree : ATree :=
  .cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag598 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag598Tree _ (by decide +kernel)

noncomputable def bccFrag599Tree : ATree :=
  .cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag599 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag599Tree _ (by decide +kernel)

noncomputable def bccFrag600Tree : ATree :=
  .cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.cut 0 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem bccFrag600 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag600Tree _ (by decide +kernel)

noncomputable def bccFrag601Tree : ATree :=
  .cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem bccFrag601 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag601Tree _ (by decide +kernel)

noncomputable def bccFrag602Tree : ATree :=
  .cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag602 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag602Tree _ (by decide +kernel)

noncomputable def bccFrag603Tree : ATree :=
  .cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag603 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag603Tree _ (by decide +kernel)

noncomputable def bccFrag604Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))

theorem bccFrag604 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag604Tree _ (by decide +kernel)

noncomputable def bccFrag605Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag605 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag605Tree _ (by decide +kernel)

noncomputable def bccFrag606Tree : ATree :=
  .cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag606 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag606Tree _ (by decide +kernel)

noncomputable def bccFrag607Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag607 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag607Tree _ (by decide +kernel)

noncomputable def bccFrag608Tree : ATree :=
  .cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.cut 0 (28823037615171175 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 0 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag608 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag608Tree _ (by decide +kernel)

noncomputable def bccFrag609Tree : ATree :=
  .cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.cut 0 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag609 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag609Tree _ (by decide +kernel)

noncomputable def bccFrag610Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag610 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag610Tree _ (by decide +kernel)

noncomputable def bccFrag611Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag611 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag611Tree _ (by decide +kernel)

noncomputable def bccFrag612Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag612 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag612Tree _ (by decide +kernel)

noncomputable def bccFrag613Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag613 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag613Tree _ (by decide +kernel)

noncomputable def bccFrag614Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag614 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 0 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag614Tree _ (by decide +kernel)

noncomputable def bccFrag615Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag615 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 0 (17293822569102705 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag615Tree _ (by decide +kernel)

noncomputable def bccFrag616Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag616 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 0 (17293822569102705 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag616Tree _ (by decide +kernel)

noncomputable def bccFrag617Tree : ATree :=
  .cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag617 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag617Tree _ (by decide +kernel)

noncomputable def bccFrag618Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag618 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag618Tree _ (by decide +kernel)

noncomputable def bccFrag619Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag619 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag619Tree _ (by decide +kernel)

noncomputable def bccFrag620Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))

theorem bccFrag620 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag620Tree _ (by decide +kernel)

noncomputable def bccFrag621Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag621 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag621Tree _ (by decide +kernel)

noncomputable def bccFrag622Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag622 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag622Tree _ (by decide +kernel)

noncomputable def bccFrag623Tree : ATree :=
  .leaf .outside

theorem bccFrag623 : AtlasClosed .bcc
    (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag623Tree _ (by decide +kernel)

noncomputable def bccFrag624Tree : ATree :=
  .cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside))))

theorem bccFrag624 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag624Tree _ (by decide +kernel)

noncomputable def bccFrag625Tree : ATree :=
  .cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-28823037615171175 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf (.tangent false)))

theorem bccFrag625 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag625Tree _ (by decide +kernel)

noncomputable def bccFrag626Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))))

theorem bccFrag626 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag626Tree _ (by decide +kernel)

noncomputable def bccFrag627Tree : ATree :=
  .cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag627 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag627Tree _ (by decide +kernel)

noncomputable def bccFrag628Tree : ATree :=
  .cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf .outside))

theorem bccFrag628 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag628Tree _ (by decide +kernel)

noncomputable def bccFrag629Tree : ATree :=
  .cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf .outside) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))))

theorem bccFrag629 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag629Tree _ (by decide +kernel)

noncomputable def bccFrag630Tree : ATree :=
  .cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag630 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag630Tree _ (by decide +kernel)

noncomputable def bccFrag631Tree : ATree :=
  .cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag631 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag631Tree _ (by decide +kernel)

noncomputable def bccFrag632Tree : ATree :=
  .cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag632 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag632Tree _ (by decide +kernel)

noncomputable def bccFrag633Tree : ATree :=
  .cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf .outside) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))))

theorem bccFrag633 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag633Tree _ (by decide +kernel)

noncomputable def bccFrag634Tree : ATree :=
  .cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf .outside) (.leaf (.tangent false))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))))

theorem bccFrag634 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag634Tree _ (by decide +kernel)

noncomputable def bccFrag635Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag635 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag635Tree _ (by decide +kernel)

noncomputable def bccFrag636Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))))) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag636 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag636Tree _ (by decide +kernel)

noncomputable def bccFrag637Tree : ATree :=
  .leaf .outside

theorem bccFrag637 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag637Tree _ (by decide +kernel)

noncomputable def bccFrag638Tree : ATree :=
  .cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.cut 4 (-17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag638 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag638Tree _ (by decide +kernel)

noncomputable def bccFrag639Tree : ATree :=
  .cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside)) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag639 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag639Tree _ (by decide +kernel)

noncomputable def bccFrag640Tree : ATree :=
  .cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.leaf (.tangent false)))

theorem bccFrag640 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag640Tree _ (by decide +kernel)

noncomputable def bccFrag641Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag641 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag641Tree _ (by decide +kernel)

noncomputable def bccFrag642Tree : ATree :=
  .leaf .outside

theorem bccFrag642 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 0 (40352252661239645 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag642Tree _ (by decide +kernel)

noncomputable def bccFrag643Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.leaf (.tangent false))))

theorem bccFrag643 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag643Tree _ (by decide +kernel)

noncomputable def bccFrag644Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside)))

theorem bccFrag644 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag644Tree _ (by decide +kernel)

noncomputable def bccFrag645Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)))

theorem bccFrag645 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag645Tree _ (by decide +kernel)

noncomputable def bccFrag646Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside)))

theorem bccFrag646 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag646Tree _ (by decide +kernel)

noncomputable def bccFrag647Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)))

theorem bccFrag647 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag647Tree _ (by decide +kernel)

noncomputable def bccFrag648Tree : ATree :=
  .cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag648 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag648Tree _ (by decide +kernel)

noncomputable def bccFrag649Tree : ATree :=
  .cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag649 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag649Tree _ (by decide +kernel)

noncomputable def bccFrag650Tree : ATree :=
  .cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag650 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag650Tree _ (by decide +kernel)

noncomputable def bccFrag651Tree : ATree :=
  .cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag651 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag651Tree _ (by decide +kernel)

noncomputable def bccFrag652Tree : ATree :=
  .cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag652 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) false) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag652Tree _ (by decide +kernel)

noncomputable def bccFrag653Tree : ATree :=
  .leaf .outside

theorem bccFrag653 : AtlasClosed .bcc
    (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag653Tree _ (by decide +kernel)

noncomputable def bccFrag654Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag654 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag654Tree _ (by decide +kernel)

noncomputable def bccFrag655Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag655 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag655Tree _ (by decide +kernel)

noncomputable def bccFrag656Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag656 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag656Tree _ (by decide +kernel)

noncomputable def bccFrag657Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag657 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag657Tree _ (by decide +kernel)

noncomputable def bccFrag658Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf .outside) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside))) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf .outside) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf .outside) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem bccFrag658 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag658Tree _ (by decide +kernel)

noncomputable def bccFrag659Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag659 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag659Tree _ (by decide +kernel)

noncomputable def bccFrag660Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag660 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag660Tree _ (by decide +kernel)

noncomputable def bccFrag661Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag661 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag661Tree _ (by decide +kernel)

noncomputable def bccFrag662Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag662 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag662Tree _ (by decide +kernel)

noncomputable def bccFrag663Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.cut 1 (28823037615171175 / 1152921504606846976 : ℚ) (.leaf .outside) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))))) (.leaf (.tangent false))

theorem bccFrag663 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag663Tree _ (by decide +kernel)

noncomputable def bccFrag664Tree : ATree :=
  .cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag664 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag664Tree _ (by decide +kernel)

noncomputable def bccFrag665Tree : ATree :=
  .cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag665 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag665Tree _ (by decide +kernel)

noncomputable def bccFrag666Tree : ATree :=
  .cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag666 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag666Tree _ (by decide +kernel)

noncomputable def bccFrag667Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag667 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag667Tree _ (by decide +kernel)

noncomputable def bccFrag668Tree : ATree :=
  .leaf .outside

theorem bccFrag668 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag668Tree _ (by decide +kernel)

noncomputable def bccFrag669Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag669 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag669Tree _ (by decide +kernel)

noncomputable def bccFrag670Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag670 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag670Tree _ (by decide +kernel)

noncomputable def bccFrag671Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (40352252661239645 / 1152921504606846976 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.leaf (.tangent false))) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag671 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag671Tree _ (by decide +kernel)

noncomputable def bccFrag672Tree : ATree :=
  .leaf .outside

theorem bccFrag672 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag672Tree _ (by decide +kernel)

noncomputable def bccFrag673Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)

theorem bccFrag673 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag673Tree _ (by decide +kernel)

noncomputable def bccFrag674Tree : ATree :=
  .cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.leaf (.tangent false))

theorem bccFrag674 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag674Tree _ (by decide +kernel)

noncomputable def bccFrag675Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside))) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside))

theorem bccFrag675 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (17293822569102705 / 576460752303423488 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag675Tree _ (by decide +kernel)

noncomputable def bccFrag676Tree : ATree :=
  .cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))

theorem bccFrag676 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag676Tree _ (by decide +kernel)

noncomputable def bccFrag677Tree : ATree :=
  .cut 2 (5764607523034235 / 72057594037927936 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag677 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag677Tree _ (by decide +kernel)

noncomputable def bccFrag678Tree : ATree :=
  .cut 2 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 1 (17293822569102705 / 576460752303423488 : ℚ) (.leaf .outside) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag678 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (0 : ℚ) true) 1 (5764607523034235 / 288230376151711744 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag678Tree _ (by decide +kernel)

noncomputable def bccFrag679Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag679 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag679Tree _ (by decide +kernel)

noncomputable def bccFrag680Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag680 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag680Tree _ (by decide +kernel)

noncomputable def bccFrag681Tree : ATree :=
  .cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag681 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag681Tree _ (by decide +kernel)

noncomputable def bccFrag682Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag682 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag682Tree _ (by decide +kernel)

noncomputable def bccFrag683Tree : ATree :=
  .cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag683 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag683Tree _ (by decide +kernel)

noncomputable def bccFrag684Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag684 : AtlasClosed .bcc
    (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag684Tree _ (by decide +kernel)

noncomputable def bccFrag685Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag685 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 0 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag685Tree _ (by decide +kernel)

noncomputable def bccFrag686Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag686 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 0 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag686Tree _ (by decide +kernel)

noncomputable def bccFrag687Tree : ATree :=
  .cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))

theorem bccFrag687 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag687Tree _ (by decide +kernel)

end BccSharp.Coulomb.BravaisCover.StrainAtlas
