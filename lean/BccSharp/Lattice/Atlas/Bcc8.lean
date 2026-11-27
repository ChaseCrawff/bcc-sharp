import BccSharp.Lattice.Atlas.Data

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Strain atlas `.bcc`, fragments 688 to 748 (427 tangent leaves). Each fragment
is a checked atlas tree on its box, a chain of cuts of the strain root. Generated. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.StrainAtlas
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.StrainAtlas

noncomputable def bccFrag688Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag688 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag688Tree _ (by decide +kernel)

noncomputable def bccFrag689Tree : ATree :=
  .cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem bccFrag689 : AtlasClosed .bcc
    (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag689Tree _ (by decide +kernel)

noncomputable def bccFrag690Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag690 : AtlasClosed .bcc
    (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag690Tree _ (by decide +kernel)

noncomputable def bccFrag691Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag691 : AtlasClosed .bcc
    (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag691Tree _ (by decide +kernel)

noncomputable def bccFrag692Tree : ATree :=
  .cut 2 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 0 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag692 : AtlasClosed .bcc
    (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (17293822569102705 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag692Tree _ (by decide +kernel)

noncomputable def bccFrag693Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag693 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag693Tree _ (by decide +kernel)

noncomputable def bccFrag694Tree : ATree :=
  .cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside))) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag694 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag694Tree _ (by decide +kernel)

noncomputable def bccFrag695Tree : ATree :=
  .cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag695 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag695Tree _ (by decide +kernel)

noncomputable def bccFrag696Tree : ATree :=
  .cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag696 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag696Tree _ (by decide +kernel)

noncomputable def bccFrag697Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag697 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag697Tree _ (by decide +kernel)

noncomputable def bccFrag698Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag698 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag698Tree _ (by decide +kernel)

noncomputable def bccFrag699Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag699 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag699Tree _ (by decide +kernel)

noncomputable def bccFrag700Tree : ATree :=
  .cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag700 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag700Tree _ (by decide +kernel)

noncomputable def bccFrag701Tree : ATree :=
  .cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf (.tangent false))

theorem bccFrag701 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag701Tree _ (by decide +kernel)

noncomputable def bccFrag702Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag702 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag702Tree _ (by decide +kernel)

noncomputable def bccFrag703Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag703 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag703Tree _ (by decide +kernel)

noncomputable def bccFrag704Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (-17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.leaf .outside)

theorem bccFrag704 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag704Tree _ (by decide +kernel)

noncomputable def bccFrag705Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.leaf .outside)

theorem bccFrag705 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag705Tree _ (by decide +kernel)

noncomputable def bccFrag706Tree : ATree :=
  .cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside))

theorem bccFrag706 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag706Tree _ (by decide +kernel)

noncomputable def bccFrag707Tree : ATree :=
  .cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag707 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag707Tree _ (by decide +kernel)

noncomputable def bccFrag708Tree : ATree :=
  .cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 1 (97998327891581995 / 2305843009213693952 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag708 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 0 (74939897799445055 / 1152921504606846976 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag708Tree _ (by decide +kernel)

noncomputable def bccFrag709Tree : ATree :=
  .cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 1 (97998327891581995 / 2305843009213693952 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (-5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag709 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) false) 4 (-5764607523034235 / 288230376151711744 : ℚ) true) 0 (74939897799445055 / 1152921504606846976 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag709Tree _ (by decide +kernel)

noncomputable def bccFrag710Tree : ATree :=
  .cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 0 (155644403121924345 / 2305843009213693952 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)))

theorem bccFrag710 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag710Tree _ (by decide +kernel)

noncomputable def bccFrag711Tree : ATree :=
  .cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag711 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag711Tree _ (by decide +kernel)

noncomputable def bccFrag712Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (17293822569102705 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag712 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag712Tree _ (by decide +kernel)

noncomputable def bccFrag713Tree : ATree :=
  .leaf .outside

theorem bccFrag713 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag713Tree _ (by decide +kernel)

noncomputable def bccFrag714Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)

theorem bccFrag714 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag714Tree _ (by decide +kernel)

noncomputable def bccFrag715Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)

theorem bccFrag715 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) 1 (28823037615171175 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag715Tree _ (by decide +kernel)

noncomputable def bccFrag716Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside))) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)))

theorem bccFrag716 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag716Tree _ (by decide +kernel)

noncomputable def bccFrag717Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (-5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside))) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)))

theorem bccFrag717 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 144115188075855872 : ℚ) true) 4 (-5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag717Tree _ (by decide +kernel)

noncomputable def bccFrag718Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag718 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag718Tree _ (by decide +kernel)

noncomputable def bccFrag719Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))))

theorem bccFrag719 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag719Tree _ (by decide +kernel)

noncomputable def bccFrag720Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (-17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag720 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag720Tree _ (by decide +kernel)

noncomputable def bccFrag721Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside))) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (-5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem bccFrag721 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (-5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag721Tree _ (by decide +kernel)

noncomputable def bccFrag722Tree : ATree :=
  .cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag722 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag722Tree _ (by decide +kernel)

noncomputable def bccFrag723Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag723 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag723Tree _ (by decide +kernel)

noncomputable def bccFrag724Tree : ATree :=
  .cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (63410682753376585 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag724 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (28823037615171175 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag724Tree _ (by decide +kernel)

noncomputable def bccFrag725Tree : ATree :=
  .cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag725 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag725Tree _ (by decide +kernel)

noncomputable def bccFrag726Tree : ATree :=
  .cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))

theorem bccFrag726 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag726Tree _ (by decide +kernel)

noncomputable def bccFrag727Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag727 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag727Tree _ (by decide +kernel)

noncomputable def bccFrag728Tree : ATree :=
  .cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (28823037615171175 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag728 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag728Tree _ (by decide +kernel)

noncomputable def bccFrag729Tree : ATree :=
  .cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))

theorem bccFrag729 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag729Tree _ (by decide +kernel)

noncomputable def bccFrag730Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag730 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag730Tree _ (by decide +kernel)

noncomputable def bccFrag731Tree : ATree :=
  .cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag731 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag731Tree _ (by decide +kernel)

noncomputable def bccFrag732Tree : ATree :=
  .cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 1 (97998327891581995 / 2305843009213693952 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 1 (97998327891581995 / 2305843009213693952 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))))

theorem bccFrag732 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag732Tree _ (by decide +kernel)

noncomputable def bccFrag733Tree : ATree :=
  .cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 1 (97998327891581995 / 2305843009213693952 : ℚ) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag733 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) false) 4 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag733Tree _ (by decide +kernel)

noncomputable def bccFrag734Tree : ATree :=
  .cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))

theorem bccFrag734 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) false) 3 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag734Tree _ (by decide +kernel)

noncomputable def bccFrag735Tree : ATree :=
  .cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag735 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) false) 2 (5764607523034235 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag735Tree _ (by decide +kernel)

noncomputable def bccFrag736Tree : ATree :=
  .cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 0 (155644403121924345 / 2305843009213693952 : ℚ) (.leaf (.tangent false)) (.leaf .outside))) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.cut 2 (5764607523034235 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.cut 4 (5764607523034235 / 288230376151711744 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))

theorem bccFrag736 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) false) 1 (51881467707308115 / 1152921504606846976 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag736Tree _ (by decide +kernel)

noncomputable def bccFrag737Tree : ATree :=
  .leaf .outside

theorem bccFrag737 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) false) 0 (40352252661239645 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag737Tree _ (by decide +kernel)

noncomputable def bccFrag738Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf .outside)

theorem bccFrag738 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) false) 3 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag738Tree _ (by decide +kernel)

noncomputable def bccFrag739Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 1 (51881467707308115 / 1152921504606846976 : ℚ) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 4 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf .outside)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside))

theorem bccFrag739 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) false) 4 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag739Tree _ (by decide +kernel)

noncomputable def bccFrag740Tree : ATree :=
  .cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 288230376151711744 : ℚ) (.cut 3 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside)) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside))) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside))

theorem bccFrag740 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) false) 2 (5764607523034235 / 144115188075855872 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag740Tree _ (by decide +kernel)

noncomputable def bccFrag741Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 1 (63410682753376585 / 1152921504606846976 : ℚ) (.cut 2 (5764607523034235 / 288230376151711744 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.leaf .outside)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.leaf (.tangent false)))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.leaf .outside)

theorem bccFrag741 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) false) 1 (28823037615171175 / 576460752303423488 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag741Tree _ (by decide +kernel)

noncomputable def bccFrag742Tree : ATree :=
  .cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)

theorem bccFrag742 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) false) 3 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag742Tree _ (by decide +kernel)

noncomputable def bccFrag743Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.cut 1 (28823037615171175 / 576460752303423488 : ℚ) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf (.tangent false))) (.cut 0 (74939897799445055 / 1152921504606846976 : ℚ) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside))) (.leaf .outside)) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.cut 3 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag743 : AtlasClosed .bcc
    (split (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) false) 4 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag743Tree _ (by decide +kernel)

noncomputable def bccFrag744Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 0 (40352252661239645 / 576460752303423488 : ℚ) (.leaf (.tangent false)) (.leaf .outside)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 4 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 144115188075855872 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.leaf (.tangent false)))

theorem bccFrag744 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) false) 4 (0 : ℚ) true) 0 (17293822569102705 / 288230376151711744 : ℚ) true) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag744Tree _ (by decide +kernel)

noncomputable def bccFrag745Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.cut 1 (40352252661239645 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.cut 1 (40352252661239645 / 576460752303423488 : ℚ) (.cut 3 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)))) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))))

theorem bccFrag745 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) false) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag745Tree _ (by decide +kernel)

noncomputable def bccFrag746Tree : ATree :=
  .cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))) (.cut 4 (-5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false)))

theorem bccFrag746 : AtlasClosed .bcc
    (split (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) false) 2 (5764607523034235 / 72057594037927936 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag746Tree _ (by decide +kernel)

noncomputable def bccFrag747Tree : ATree :=
  .leaf .outside

theorem bccFrag747 : AtlasClosed .bcc
    (split (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) false) 0 (17293822569102705 / 288230376151711744 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag747Tree _ (by decide +kernel)

noncomputable def bccFrag748Tree : ATree :=
  .cut 0 (17293822569102705 / 288230376151711744 : ℚ) (.cut 2 (5764607523034235 / 72057594037927936 : ℚ) (.cut 4 (5764607523034235 / 72057594037927936 : ℚ) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 1 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf .outside)) (.leaf (.tangent false))) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.cut 2 (5764607523034235 / 144115188075855872 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false)))) (.cut 1 (40352252661239645 / 576460752303423488 : ℚ) (.cut 2 (17293822569102705 / 144115188075855872 : ℚ) (.cut 3 (5764607523034235 / 72057594037927936 : ℚ) (.leaf (.tangent false)) (.leaf (.tangent false))) (.leaf (.tangent false))) (.leaf .outside))) (.leaf .outside)

theorem bccFrag748 : AtlasClosed .bcc
    (split (split (split (split (strainRoot .bcc) 1 (5764607523034235 / 144115188075855872 : ℚ) true) 0 (5764607523034235 / 144115188075855872 : ℚ) true) 1 (17293822569102705 / 288230376151711744 : ℚ) true) 4 (0 : ℚ) true) :=
  ATree.closed atlasData atlasData_valid .bcc bccFrag748Tree _ (by decide +kernel)

end BccSharp.Coulomb.BravaisCover.StrainAtlas
