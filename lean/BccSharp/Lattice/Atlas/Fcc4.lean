import BccSharp.Lattice.Atlas.Data

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Strain atlas `.fcc`, fragments 335 to 415 (596 tangent leaves). Each fragment
is a checked atlas tree on its box, a chain of cuts of the strain root. Generated. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.StrainAtlas
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.StrainAtlas

noncomputable def fccFrag335Tree : ATree :=
  .cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag335 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) false) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (1170935903116329 / 72057594037927936 : ℚ) true) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (28823037615171175 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag335Tree _ (by decide +kernel)

noncomputable def fccFrag336Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag336 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) false) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (1170935903116329 / 72057594037927936 : ℚ) true) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag336Tree _ (by decide +kernel)

noncomputable def fccFrag337Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag337 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) false) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (1170935903116329 / 72057594037927936 : ℚ) true) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag337Tree _ (by decide +kernel)

noncomputable def fccFrag338Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag338 : AtlasClosed .fcc
    (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) false) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (1170935903116329 / 72057594037927936 : ℚ) true) 2 (17293822569102705 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag338Tree _ (by decide +kernel)

noncomputable def fccFrag339Tree : ATree :=
  .cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag339 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag339Tree _ (by decide +kernel)

noncomputable def fccFrag340Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag340 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag340Tree _ (by decide +kernel)

noncomputable def fccFrag341Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag341 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag341Tree _ (by decide +kernel)

noncomputable def fccFrag342Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag342 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag342Tree _ (by decide +kernel)

noncomputable def fccFrag343Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag343 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag343Tree _ (by decide +kernel)

noncomputable def fccFrag344Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag344 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag344Tree _ (by decide +kernel)

noncomputable def fccFrag345Tree : ATree :=
  .cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag345 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag345Tree _ (by decide +kernel)

noncomputable def fccFrag346Tree : ATree :=
  .cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag346 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag346Tree _ (by decide +kernel)

noncomputable def fccFrag347Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag347 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag347Tree _ (by decide +kernel)

noncomputable def fccFrag348Tree : ATree :=
  .cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag348 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag348Tree _ (by decide +kernel)

noncomputable def fccFrag349Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag349 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag349Tree _ (by decide +kernel)

noncomputable def fccFrag350Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag350 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) 1 (8196551321814303 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag350Tree _ (by decide +kernel)

noncomputable def fccFrag351Tree : ATree :=
  .cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.cut 1 (17564038546744935 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag351 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) 1 (8196551321814303 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag351Tree _ (by decide +kernel)

noncomputable def fccFrag352Tree : ATree :=
  .cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag352 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) 1 (8196551321814303 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag352Tree _ (by decide +kernel)

noncomputable def fccFrag353Tree : ATree :=
  .cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (3512807709348987 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (3512807709348987 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag353 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag353Tree _ (by decide +kernel)

noncomputable def fccFrag354Tree : ATree :=
  .cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag354 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag354Tree _ (by decide +kernel)

noncomputable def fccFrag355Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag355 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag355Tree _ (by decide +kernel)

noncomputable def fccFrag356Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag356 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag356Tree _ (by decide +kernel)

noncomputable def fccFrag357Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag357 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag357Tree _ (by decide +kernel)

noncomputable def fccFrag358Tree : ATree :=
  .cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag358 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag358Tree _ (by decide +kernel)

noncomputable def fccFrag359Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag359 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag359Tree _ (by decide +kernel)

noncomputable def fccFrag360Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag360 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag360Tree _ (by decide +kernel)

noncomputable def fccFrag361Tree : ATree :=
  .cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag361 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag361Tree _ (by decide +kernel)

noncomputable def fccFrag362Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag362 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag362Tree _ (by decide +kernel)

noncomputable def fccFrag363Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag363 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag363Tree _ (by decide +kernel)

noncomputable def fccFrag364Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag364 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) 1 (8196551321814303 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag364Tree _ (by decide +kernel)

noncomputable def fccFrag365Tree : ATree :=
  .cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.cut 1 (17564038546744935 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag365 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) 1 (8196551321814303 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag365Tree _ (by decide +kernel)

noncomputable def fccFrag366Tree : ATree :=
  .cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag366 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) false) 1 (8196551321814303 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag366Tree _ (by decide +kernel)

noncomputable def fccFrag367Tree : ATree :=
  .cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.cut 0 (3512807709348987 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag367 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (1170935903116329 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag367Tree _ (by decide +kernel)

noncomputable def fccFrag368Tree : ATree :=
  .cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag368 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag368Tree _ (by decide +kernel)

noncomputable def fccFrag369Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag369 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag369Tree _ (by decide +kernel)

noncomputable def fccFrag370Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag370 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag370Tree _ (by decide +kernel)

noncomputable def fccFrag371Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag371 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag371Tree _ (by decide +kernel)

noncomputable def fccFrag372Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag372 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag372Tree _ (by decide +kernel)

noncomputable def fccFrag373Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag373 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag373Tree _ (by decide +kernel)

noncomputable def fccFrag374Tree : ATree :=
  .cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag374 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag374Tree _ (by decide +kernel)

noncomputable def fccFrag375Tree : ATree :=
  .cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag375 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag375Tree _ (by decide +kernel)

noncomputable def fccFrag376Tree : ATree :=
  .cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag376 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (1170935903116329 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag376Tree _ (by decide +kernel)

noncomputable def fccFrag377Tree : ATree :=
  .cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag377 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag377Tree _ (by decide +kernel)

noncomputable def fccFrag378Tree : ATree :=
  .cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem fccFrag378 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag378Tree _ (by decide +kernel)

noncomputable def fccFrag379Tree : ATree :=
  .cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))

theorem fccFrag379 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag379Tree _ (by decide +kernel)

noncomputable def fccFrag380Tree : ATree :=
  .cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag380 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag380Tree _ (by decide +kernel)

noncomputable def fccFrag381Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag381 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag381Tree _ (by decide +kernel)

noncomputable def fccFrag382Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag382 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag382Tree _ (by decide +kernel)

noncomputable def fccFrag383Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag383 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag383Tree _ (by decide +kernel)

noncomputable def fccFrag384Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (1170935903116329 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (3512807709348987 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag384 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag384Tree _ (by decide +kernel)

noncomputable def fccFrag385Tree : ATree :=
  .cut 1 (3512807709348987 / 72057594037927936 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag385 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag385Tree _ (by decide +kernel)

noncomputable def fccFrag386Tree : ATree :=
  .cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem fccFrag386 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) true) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag386Tree _ (by decide +kernel)

noncomputable def fccFrag387Tree : ATree :=
  .cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 72057594037927936 : ℚ) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag387 : AtlasClosed .fcc
    (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag387Tree _ (by decide +kernel)

noncomputable def fccFrag388Tree : ATree :=
  .cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 72057594037927936 : ℚ) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (1170935903116329 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag388 : AtlasClosed .fcc
    (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (0 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag388Tree _ (by decide +kernel)

noncomputable def fccFrag389Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem fccFrag389 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag389Tree _ (by decide +kernel)

noncomputable def fccFrag390Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem fccFrag390 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag390Tree _ (by decide +kernel)

noncomputable def fccFrag391Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem fccFrag391 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag391Tree _ (by decide +kernel)

noncomputable def fccFrag392Tree : ATree :=
  .cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.leaf .outside)

theorem fccFrag392 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag392Tree _ (by decide +kernel)

noncomputable def fccFrag393Tree : ATree :=
  .cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.leaf .outside)

theorem fccFrag393 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag393Tree _ (by decide +kernel)

noncomputable def fccFrag394Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag394 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (8196551321814303 / 144115188075855872 : ℚ) false) 3 (17293822569102705 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag394Tree _ (by decide +kernel)

noncomputable def fccFrag395Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag395 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (8196551321814303 / 144115188075855872 : ℚ) false) 3 (17293822569102705 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag395Tree _ (by decide +kernel)

noncomputable def fccFrag396Tree : ATree :=
  .leaf .outside

theorem fccFrag396 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 0 (8196551321814303 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag396Tree _ (by decide +kernel)

noncomputable def fccFrag397Tree : ATree :=
  .cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.leaf .outside)

theorem fccFrag397 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag397Tree _ (by decide +kernel)

noncomputable def fccFrag398Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag398 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (3512807709348987 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag398Tree _ (by decide +kernel)

noncomputable def fccFrag399Tree : ATree :=
  .cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.leaf .outside)

theorem fccFrag399 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (17293822569102705 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag399Tree _ (by decide +kernel)

noncomputable def fccFrag400Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag400 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 2 (17293822569102705 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag400Tree _ (by decide +kernel)

noncomputable def fccFrag401Tree : ATree :=
  .cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)

theorem fccFrag401 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) 2 (17293822569102705 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag401Tree _ (by decide +kernel)

noncomputable def fccFrag402Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 1 (10538423128046961 / 288230376151711744 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag402 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 288230376151711744 : ℚ) true) 2 (17293822569102705 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag402Tree _ (by decide +kernel)

noncomputable def fccFrag403Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem fccFrag403 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag403Tree _ (by decide +kernel)

noncomputable def fccFrag404Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag404 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (17293822569102705 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag404Tree _ (by decide +kernel)

noncomputable def fccFrag405Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (10538423128046961 / 288230376151711744 : ℚ) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag405 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (5854679515581645 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag405Tree _ (by decide +kernel)

noncomputable def fccFrag406Tree : ATree :=
  .cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)

theorem fccFrag406 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (17293822569102705 / 288230376151711744 : ℚ) true) 1 (5854679515581645 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag406Tree _ (by decide +kernel)

noncomputable def fccFrag407Tree : ATree :=
  .cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag407 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (17293822569102705 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag407Tree _ (by decide +kernel)

noncomputable def fccFrag408Tree : ATree :=
  .cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag408 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (17293822569102705 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag408Tree _ (by decide +kernel)

noncomputable def fccFrag409Tree : ATree :=
  .cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag409 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (17293822569102705 / 288230376151711744 : ℚ) true) 3 (17293822569102705 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag409Tree _ (by decide +kernel)

noncomputable def fccFrag410Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag410 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag410Tree _ (by decide +kernel)

noncomputable def fccFrag411Tree : ATree :=
  .cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf .outside)) (.leaf .outside)

theorem fccFrag411 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag411Tree _ (by decide +kernel)

noncomputable def fccFrag412Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag412 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (28823037615171175 / 288230376151711744 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag412Tree _ (by decide +kernel)

noncomputable def fccFrag413Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag413 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (28823037615171175 / 288230376151711744 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (51881467707308115 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag413Tree _ (by decide +kernel)

noncomputable def fccFrag414Tree : ATree :=
  .cut 1 (5854679515581645 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag414 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (28823037615171175 / 288230376151711744 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (51881467707308115 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag414Tree _ (by decide +kernel)

noncomputable def fccFrag415Tree : ATree :=
  .cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag415 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 2 (28823037615171175 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag415Tree _ (by decide +kernel)

end BccSharp.Coulomb.BravaisCover.StrainAtlas
