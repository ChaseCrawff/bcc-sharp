import BccSharp.Cover.Stage5bOptical
import BccSharp.Cover.Stage5bPhase
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! # Stage5b optical tiles on the Lean deficit routes, part 1 (generated)

Generated.
Each tile is the shape group of the optical sweep refined along the recorded path
(`tileN_address`, kernel), in the standard frame. Each tile has:
* a whole-tile hint (`Stage5bOptical.wholeOk`: the registered cap and the Jensen check on the
  tile against `e_BCC⁺ + g⁺ · cap/S`), or an anchor tree (`Stage5bOptical.anchorTreeOk`: a
  uniform bisection of the tile's shape box by `opticalAxis`, and on every piece the anchor
  Jensen check against `e_BCC⁺ + g⁺ · cap/S + m`, the strain cap on the anchor cell, the far
  annulus on the piece and the layered gain with `k = anchorK m G`). Each piece is
  checked in its own declaration (`nodeN_P_ok`, kernel) and the tree is assembled with
  `anchorTreeOk_split`, whose box equations are kernel checks; or, for an `optical_lattice`
  tile, a relative certificate (`Layered.planarAnchorCertOk` or `planarAnchorCertOkFar` with wrap `0`,
  `tileN_cert`, kernel);
* the kernel check of the hint (`tileN_ok`);
* `0 < deficit` at every good point of the tile (`tileN_deficit`), or, for a relative tile,
  `OpticalEvidence` from `LatticeCase` (`tileN_optical`);
* the acceptance of the tile's witness by `stage5bOpticalCheck` on its route
  (`tileN_witness`), for every hint function giving the witness this hint;
* the coverage theorem (a good point, or no reduced point). -/

namespace BccSharp.Coulomb.CompactCover.Stage5bOptical.Leaves1

open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.Stage3Stage6
open BccSharp.Coulomb.CompactCover.Stage5bOptical
open BccSharp.Coulomb.CompactCover.Stage5bPhase

def group5 : Cell := ⟨![(439 / 512 : ℚ), (205 / 256 : ℚ), (11 / 32 : ℚ), (0 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (827 / 1024 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile5 : Cell := ⟨![(3529 / 4096 : ℚ), (1647 / 2048 : ℚ), (45 / 128 : ℚ), (0 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(1773 / 2048 : ℚ), (827 / 1024 : ℚ), (23 / 64 : ℚ), (1 / 128 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile5_address : sameCell (descendOptical group5 [false, false, false, true, true, true, false]) tile5 = true := by
  decide +kernel

def reg5_0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(130898585679384423 / 230584300941013499 : ℚ), (134049020971709986 / 230584300941013499 : ℚ), (134408110187290374 / 230584300941013499 : ℚ)], ![(-949051307626673646 / 1152921504705067495 : ℚ), (90193077852009831 / 230584300941013499 : ℚ), (474510093878971322 / 1152921504705067495 : ℚ)], ![(12985306385265478 / 1152921504705067495 : ℚ), (-164515010028152838 / 230584300941013499 : ℚ), (807731183448674979 / 1152921504705067495 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf5_0 : AnchorHint where
  reg := reg5_0
  cap := 12356638176825838039155560274
  margin := (134349472583417 / 4611686018427387904 : ℚ)
  depth := 0

def reg5_1 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(163623449827994354 / 288230376119237451 : ℚ), (167563800521374697 / 288230376119237451 : ℚ), (168007407988623674 / 288230376119237451 : ℚ)], ![(-237254842802701978 / 288230376119237451 : ℚ), (112284245056700954 / 288230376119237451 : ℚ), (119076184002297401 / 288230376119237451 : ℚ)], ![(3775705349742551 / 288230376119237451 : ℚ), (-205891648166497426 / 288230376119237451 : ℚ), (201670828287663482 / 288230376119237451 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf5_1 : AnchorHint where
  reg := reg5_1
  cap := 13533483404278148559755058522
  margin := (24352721292501 / 576460752303423488 : ℚ)
  depth := 0

def node5_0 : Cell := ⟨![(3529 / 4096 : ℚ), (1647 / 2048 : ℚ), (45 / 128 : ℚ), (0 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(1773 / 2048 : ℚ), (827 / 1024 : ℚ), (23 / 64 : ℚ), (1 / 128 : ℚ), (7 / 128 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem node5_0_ok : anchorTreeOk (.leaf leaf5_0) node5_0 = true := by
  decide +kernel

def node5_1 : Cell := ⟨![(3529 / 4096 : ℚ), (1647 / 2048 : ℚ), (45 / 128 : ℚ), (0 : ℚ), (7 / 128 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(1773 / 2048 : ℚ), (827 / 1024 : ℚ), (23 / 64 : ℚ), (1 / 128 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem node5_1_ok : anchorTreeOk (.leaf leaf5_1) node5_1 = true := by
  decide +kernel

theorem tile5_ok : anchorTreeOk (.split (.leaf leaf5_0) (.leaf leaf5_1)) tile5 = true :=
  anchorTreeOk_split (.leaf leaf5_0) (.leaf leaf5_1) tile5 node5_0 node5_1
    (by decide +kernel) (by decide +kernel) node5_0_ok node5_1_ok

def tree5 : AnchorTree := (.split (.leaf leaf5_0) (.leaf leaf5_1))

theorem tile5_tree : anchorTreeOk tree5 tile5 = true := tile5_ok

theorem tile5_deficit (p : Chart) (hp : tile5.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  anchorTreeOk_sound tree5 tile5 tile5_tree p hp gp

theorem tile5_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.anchor tree5)) : stage5bOpticalCheck hint w tile5 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile5_tree, Bool.true_and,
    decide_true]

def tile5Pt : Fin 8 → ℚ := ![(7075 / 8192 : ℚ), (6609 / 8192 : ℚ), (183 / 512 : ℚ), (1 / 256 : ℚ), (7 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem tile5_nonvacuous : ∃ p : Chart, tile5.Mem p ∧ good p := by
  have hall : ∀ i, tile5.lo i ≤ tile5Pt i ∧ tile5Pt i ≤ tile5.hi i := by
    decide +kernel
  refine ⟨fun i => (tile5Pt i : ℝ), fun i => ?_,
    good_of_check tile5Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group6 : Cell := ⟨![(439 / 512 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (-3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile6 : Cell := ⟨![(1773 / 2048 : ℚ), (1675 / 2048 : ℚ), (41 / 128 : ℚ), (1 / 128 : ℚ), (-3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (841 / 1024 : ℚ), (21 / 64 : ℚ), (1 / 64 : ℚ), (-1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile6_address : sameCell (descendOptical group6 [true, false, false, false, true, true, true]) tile6 = true := by
  decide +kernel

def reg6_0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(167538731051623158 / 288230376254396771 : ℚ), (165112481682482274 / 288230376254396771 : ℚ), (166569480355841201 / 288230376254396771 : ℚ)], ![(-234514252795495551 / 288230376254396771 : ℚ), (120774977645022794 / 288230376254396771 : ℚ), (116160319414014102 / 288230376254396771 : ℚ)], ![(-3254017383699626 / 288230376254396771 : ℚ), (-203046849183254577 / 288230376254396771 : ℚ), (204543731762599806 / 288230376254396771 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf6_0 : AnchorHint where
  reg := reg6_0
  cap := 5501561652263644920056881917
  margin := (112354991093195 / 9223372036854775808 : ℚ)
  depth := 0

theorem tile6_ok : anchorTreeOk (.leaf leaf6_0) tile6 = true := by
  decide +kernel

def tree6 : AnchorTree := (.leaf leaf6_0)

theorem tile6_tree : anchorTreeOk tree6 tile6 = true := tile6_ok

theorem tile6_deficit (p : Chart) (hp : tile6.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  anchorTreeOk_sound tree6 tile6 tile6_tree p hp gp

theorem tile6_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.anchor tree6)) : stage5bOpticalCheck hint w tile6 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile6_tree, Bool.true_and,
    decide_true]

def tile6Pt : Fin 8 → ℚ := ![(7109 / 8192 : ℚ), (6721 / 8192 : ℚ), (167 / 512 : ℚ), (3 / 256 : ℚ), (-5 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem tile6_nonvacuous : ∃ p : Chart, tile6.Mem p ∧ good p := by
  have hall : ∀ i, tile6.lo i ≤ tile6Pt i ∧ tile6Pt i ≤ tile6.hi i := by
    decide +kernel
  refine ⟨fun i => (tile6Pt i : ℝ), fun i => ?_,
    good_of_check tile6Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage5bOptical.Leaves1
