import BccSharp.Lattice.Atlas.Data

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Strain atlas `.fcc`, fragments 416 to 433 (131 tangent leaves). Each fragment
is a checked atlas tree on its box, a chain of cuts of the strain root. Generated. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.StrainAtlas
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.StrainAtlas

noncomputable def fccFrag416Tree : ATree :=
  .cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag416 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (17293822569102705 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag416Tree _ (by decide +kernel)

noncomputable def fccFrag417Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag417 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (17293822569102705 / 144115188075855872 : ℚ) true) 2 (40352252661239645 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag417Tree _ (by decide +kernel)

noncomputable def fccFrag418Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag418 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (17293822569102705 / 144115188075855872 : ℚ) true) 2 (40352252661239645 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag418Tree _ (by decide +kernel)

noncomputable def fccFrag419Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.leaf .outside)) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 2 (28823037615171175 / 288230376151711744 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.leaf .outside))

theorem fccFrag419 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (17293822569102705 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag419Tree _ (by decide +kernel)

noncomputable def fccFrag420Tree : ATree :=
  .cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (40352252661239645 / 288230376151711744 : ℚ) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.leaf .outside)

theorem fccFrag420 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (17293822569102705 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag420Tree _ (by decide +kernel)

noncomputable def fccFrag421Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag421 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag421Tree _ (by decide +kernel)

noncomputable def fccFrag422Tree : ATree :=
  .cut 3 (51881467707308115 / 576460752303423488 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag422 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (28823037615171175 / 288230376151711744 : ℚ) false) 1 (5854679515581645 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag422Tree _ (by decide +kernel)

noncomputable def fccFrag423Tree : ATree :=
  .cut 3 (97998327891581995 / 1152921504606846976 : ℚ) (.cut 1 (12880294934279619 / 288230376151711744 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag423 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (28823037615171175 / 288230376151711744 : ℚ) false) 1 (5854679515581645 / 144115188075855872 : ℚ) true) 3 (51881467707308115 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag423Tree _ (by decide +kernel)

noncomputable def fccFrag424Tree : ATree :=
  .cut 3 (109527542937650465 / 1152921504606846976 : ℚ) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag424 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (28823037615171175 / 288230376151711744 : ℚ) false) 1 (5854679515581645 / 144115188075855872 : ℚ) true) 3 (51881467707308115 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag424Tree _ (by decide +kernel)

noncomputable def fccFrag425Tree : ATree :=
  .cut 3 (63410682753376585 / 576460752303423488 : ℚ) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))

theorem fccFrag425 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (3512807709348987 / 72057594037927936 : ℚ) true) 3 (28823037615171175 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag425Tree _ (by decide +kernel)

noncomputable def fccFrag426Tree : ATree :=
  .cut 2 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag426 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (17293822569102705 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag426Tree _ (by decide +kernel)

noncomputable def fccFrag427Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag427 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 2 (17293822569102705 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag427Tree _ (by decide +kernel)

noncomputable def fccFrag428Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag428 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag428Tree _ (by decide +kernel)

noncomputable def fccFrag429Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag429 : AtlasClosed .fcc
    (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag429Tree _ (by decide +kernel)

noncomputable def fccFrag430Tree : ATree :=
  .cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.leaf .outside)

theorem fccFrag430 : AtlasClosed .fcc
    (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag430Tree _ (by decide +kernel)

noncomputable def fccFrag431Tree : ATree :=
  .cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)

theorem fccFrag431 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) true) 3 (40352252661239645 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag431Tree _ (by decide +kernel)

noncomputable def fccFrag432Tree : ATree :=
  .cut 3 (86469112845513525 / 576460752303423488 : ℚ) (.cut 3 (167173618167992815 / 1152921504606846976 : ℚ) (.cut 1 (8196551321814303 / 144115188075855872 : ℚ) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (3512807709348987 / 72057594037927936 : ℚ) (.cut 4 (0 : ℚ) (.leaf (.tangent false)) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside))) (.cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem fccFrag432 : AtlasClosed .fcc
    (split (split (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (17293822569102705 / 144115188075855872 : ℚ) true) 3 (40352252661239645 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag432Tree _ (by decide +kernel)

noncomputable def fccFrag433Tree : ATree :=
  .cut 4 (0 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem fccFrag433 : AtlasClosed .fcc
    (split (split (split (split (split (strainRoot .fcc) 1 (1170935903116329 / 36028797018963968 : ℚ) true) 0 (1170935903116329 / 36028797018963968 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 1 (3512807709348987 / 72057594037927936 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .fcc fccFrag433Tree _ (by decide +kernel)

end BccSharp.Coulomb.BravaisCover.StrainAtlas
