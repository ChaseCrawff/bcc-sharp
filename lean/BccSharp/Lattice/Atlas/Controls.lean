import BccSharp.Lattice.Atlas.Data

set_option autoImplicit false
set_option maxRecDepth 100000


/-! Negative controls of the Lattice strain atlases: inputs the kernel must reject. Generated. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.StrainAtlas.Controls
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentCover
open BccSharp.Coulomb.BravaisCover.StrainAtlas

theorem control_center_fcc : tanCheck atlasData .fcc false
    ⟨![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 1024 : ℚ)], ![(1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ)]⟩ = false := by
  decide +kernel

theorem control_center_bcc_e1 : tanCheck atlasData .bcc false
    ⟨![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 1024 : ℚ)], ![(1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ)]⟩ = false := by
  decide +kernel

theorem control_center_bcc_e2 : tanCheck atlasData .bcc true
    ⟨![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 1024 : ℚ)], ![(1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ), (1 / 1024 : ℚ)]⟩ = false := by
  decide +kernel

theorem control_e2_on_fcc : tanCheck atlasData .fcc true
    ⟨![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-5764607523034235 / 36028797018963968 : ℚ)], ![(1170935903116329 / 36028797018963968 : ℚ), (1170935903116329 / 36028797018963968 : ℚ), (5764607523034235 / 72057594037927936 : ℚ), (5764607523034235 / 72057594037927936 : ℚ), (-17293822569102705 / 144115188075855872 : ℚ)]⟩ = false := by
  decide +kernel

theorem fccLeafPasses : tanCheck atlasData .fcc false
    ⟨![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-5764607523034235 / 36028797018963968 : ℚ)], ![(1170935903116329 / 36028797018963968 : ℚ), (1170935903116329 / 36028797018963968 : ℚ), (5764607523034235 / 72057594037927936 : ℚ), (5764607523034235 / 72057594037927936 : ℚ), (-17293822569102705 / 144115188075855872 : ℚ)]⟩ = true := by
  decide +kernel

theorem control_table_entry : ZTree.check .half (.leaf ((4827 : ℚ) / 4096) (2666612434582663130206750860) (1859862191365198444324238403)) = false := by
  decide +kernel

theorem tableEntryPasses : ZTree.check .half (.leaf ((4827 : ℚ) / 4096) (2666612434582663130206750860) (1859862191365198444324238404)) = true := by
  decide +kernel

theorem control_mirror : ZTree.mirror (.leaf (1 / 2) ⟨1 / 4, 1 / 8⟩)
    (.leaf (1 / 2) 0 9903520314283042199192993792) = false := by
  decide +kernel

theorem control_ball_leaf : ATree.check atlasData .bcc (.leaf .ball)
    ⟨![(1 / 100 : ℚ), (1 / 50 : ℚ), (1 / 100 : ℚ), (1 / 100 : ℚ), (-1 / 100 : ℚ)], ![(1 / 50 : ℚ), (3 / 100 : ℚ), (1 / 50 : ℚ), (1 / 50 : ℚ), (1 / 100 : ℚ)]⟩ = false := by
  decide +kernel

theorem control_outside_leaf : ATree.check atlasData .bcc (.leaf .outside)
    ⟨![(1 / 100 : ℚ), (1 / 50 : ℚ), (1 / 100 : ℚ), (1 / 100 : ℚ), (-1 / 100 : ℚ)], ![(1 / 50 : ℚ), (3 / 100 : ℚ), (1 / 50 : ℚ), (1 / 50 : ℚ), (1 / 100 : ℚ)]⟩ = false := by
  decide +kernel

theorem control_cands_pair : candsOK [⟨1, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨-1, 0, 0, 1, 0, 0, 0, 0, 0⟩] = false := by
  decide +kernel

theorem control_cands_zero : candsOK [⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩] = false := by
  decide +kernel

end BccSharp.Coulomb.BravaisCover.StrainAtlas.Controls
