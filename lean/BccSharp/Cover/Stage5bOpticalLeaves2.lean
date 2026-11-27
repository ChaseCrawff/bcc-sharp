import BccSharp.Cover.Stage5bOptical
import BccSharp.Cover.Stage5bPhase
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! # Stage5b optical tiles on the Lean deficit routes, part 2 (generated)

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

namespace BccSharp.Coulomb.CompactCover.Stage5bOptical.Leaves2

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

def group7 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (0 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (431 / 512 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

def tile7 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (39 / 128 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

theorem tile7_address : sameCell (descendOptical group7 [false, true, true, true, false, false, true]) tile7 = true := by
  decide +kernel

def reg7_0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(338923733131142957 / 576460752124000957 : ℚ), (327239162423656860 / 576460752124000957 : ℚ), (332193065002992180 / 576460752124000957 : ℚ)], ![(-466301727218997540 / 576460752124000957 : ℚ), (237290226187608468 / 576460752124000957 : ℚ), (241998029925415085 / 576460752124000957 : ℚ)], ![(633286979395980 / 576460752124000957 : ℚ), (-410992552087584685 / 576460752124000957 : ℚ), (404217416516785668 / 576460752124000957 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf7_0 : AnchorHint where
  reg := reg7_0
  cap := 12152018775796736562533406679
  margin := (23412852790549 / 18446744073709551616 : ℚ)
  depth := 0

def reg7_1 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(677854103837619077 / 1152921503401909311 : ℚ), (654462423294848666 / 1152921503401909311 : ℚ), (664395020610518606 / 1152921503401909311 : ℚ)], ![(-932593307820657074 / 1152921503401909311 : ℚ), (472698332865995371 / 1152921503401909311 : ℚ), (485853888859966402 / 1152921503401909311 : ℚ)], ![(3395456544012646 / 1152921503401909311 : ℚ), (-823081536427140218 / 1152921503401909311 : ℚ), (807312361031413141 / 1152921503401909311 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf7_1 : AnchorHint where
  reg := reg7_1
  cap := 12732320002626804054598615801
  margin := (40780994384391 / 9223372036854775808 : ℚ)
  depth := 0

def reg7_2 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(67784204749715621 / 115292150353380159 : ℚ), (65249441416465582 / 115292150353380159 : ℚ), (66634014695156054 / 115292150353380159 : ℚ)], ![(-93260818429420342 / 115292150353380159 : ℚ), (237281381963896346 / 576460751766900795 : ℚ), (242002144097591047 / 576460751766900795 : ℚ)], ![(-35572879248974 / 115292150353380159 : ℚ), (-411785507238834953 / 576460751766900795 : ℚ), (403410042909162554 / 576460751766900795 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf7_2 : AnchorHint where
  reg := reg7_2
  cap := 12782752378752942972194539121
  margin := (6605411813379 / 2305843009213693952 : ℚ)
  depth := 0

def reg7_3 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(677851261242222121 / 1152921504530058267 : ℚ), (652477186086479342 / 1152921504530058267 : ℚ), (666347645660170178 / 1152921504530058267 : ℚ)], ![(-932599870901408302 / 1152921504530058267 : ℚ), (472678845920278999 / 1152921504530058267 : ℚ), (485860252564462078 / 1152921504530058267 : ℚ)], ![(1773142650344962 / 1152921504530058267 : ℚ), (-824667342547281982 / 1152921504530058267 : ℚ), (805697601900985289 / 1152921504530058267 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf7_3 : AnchorHint where
  reg := reg7_3
  cap := 13361709344990296668763057635
  margin := (93364512749755 / 18446744073709551616 : ℚ)
  depth := 0

def node7_0 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (39 / 128 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (5 / 16 : ℚ), (3 / 128 : ℚ), (1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

def node7_00 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (39 / 128 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (5 / 16 : ℚ), (3 / 128 : ℚ), (3 / 128 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

theorem node7_00_ok : anchorTreeOk (.leaf leaf7_0) node7_00 = true := by
  decide +kernel

def node7_01 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (39 / 128 : ℚ), (1 / 64 : ℚ), (3 / 128 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (5 / 16 : ℚ), (3 / 128 : ℚ), (1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

theorem node7_01_ok : anchorTreeOk (.leaf leaf7_1) node7_01 = true := by
  decide +kernel

theorem node7_0_ok : anchorTreeOk (.split (.leaf leaf7_0) (.leaf leaf7_1)) node7_0 = true :=
  anchorTreeOk_split (.leaf leaf7_0) (.leaf leaf7_1) node7_0 node7_00 node7_01
    (by decide +kernel) (by decide +kernel) node7_00_ok node7_01_ok

def node7_1 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (39 / 128 : ℚ), (3 / 128 : ℚ), (1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

def node7_10 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (39 / 128 : ℚ), (3 / 128 : ℚ), (1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (3 / 128 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

theorem node7_10_ok : anchorTreeOk (.leaf leaf7_2) node7_10 = true := by
  decide +kernel

def node7_11 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (39 / 128 : ℚ), (3 / 128 : ℚ), (3 / 128 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

theorem node7_11_ok : anchorTreeOk (.leaf leaf7_3) node7_11 = true := by
  decide +kernel

theorem node7_1_ok : anchorTreeOk (.split (.leaf leaf7_2) (.leaf leaf7_3)) node7_1 = true :=
  anchorTreeOk_split (.leaf leaf7_2) (.leaf leaf7_3) node7_1 node7_10 node7_11
    (by decide +kernel) (by decide +kernel) node7_10_ok node7_11_ok

theorem tile7_ok : anchorTreeOk (.split (.split (.leaf leaf7_0) (.leaf leaf7_1)) (.split (.leaf leaf7_2) (.leaf leaf7_3))) tile7 = true :=
  anchorTreeOk_split (.split (.leaf leaf7_0) (.leaf leaf7_1)) (.split (.leaf leaf7_2) (.leaf leaf7_3)) tile7 node7_0 node7_1
    (by decide +kernel) (by decide +kernel) node7_0_ok node7_1_ok

def tree7 : AnchorTree := (.split (.split (.leaf leaf7_0) (.leaf leaf7_1)) (.split (.leaf leaf7_2) (.leaf leaf7_3)))

theorem tile7_tree : anchorTreeOk tree7 tile7 = true := tile7_ok

theorem tile7_deficit (p : Chart) (hp : tile7.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  anchorTreeOk_sound tree7 tile7 tile7_tree p hp gp

theorem tile7_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.anchor tree7)) : stage5bOpticalCheck hint w tile7 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile7_tree, Bool.true_and,
    decide_true]

def tile7Pt : Fin 8 → ℚ := ![(3553447 / 4096000 : ℚ), (3399 / 4096 : ℚ), (79 / 256 : ℚ), (3 / 128 : ℚ), (3 / 128 : ℚ), (-65 / 128 : ℚ), (-1 / 2 : ℚ), (-65 / 128 : ℚ)]

theorem tile7_nonvacuous : ∃ p : Chart, tile7.Mem p ∧ good p := by
  have hall : ∀ i, tile7.lo i ≤ tile7Pt i ∧ tile7Pt i ≤ tile7.hi i := by
    decide +kernel
  refine ⟨fun i => (tile7Pt i : ℝ), fun i => ?_,
    good_of_check tile7Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group8 : Cell := ⟨![(439 / 512 : ℚ), (53 / 64 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-33 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (431 / 512 : ℚ), (9 / 32 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile8 : Cell := ⟨![(3563 / 4096 : ℚ), (855 / 1024 : ℚ), (1 / 4 : ℚ), (1 / 64 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-33 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (431 / 512 : ℚ), (17 / 64 : ℚ), (1 / 32 : ℚ), (-1 / 64 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile8_address : sameCell (descendOptical group8 [true, true, false, true, false, true]) tile8 = true := by
  decide +kernel

def reg8 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(351189457653140096 / 576460752625493573 : ℚ), (320307727160136573 / 576460752625493573 : ℚ), (326153221772147028 / 576460752625493573 : ℚ)], ![(-457100843999636133 / 576460752625493573 : ℚ), (251126406713393312 / 576460752625493573 : ℚ), (245563322960881464 / 576460752625493573 : ℚ)], ![(-5637602829583368 / 576460752625493573 : ℚ), (-408222350062165716 / 576460752625493573 : ℚ), (406976325677070557 / 576460752625493573 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 1]

def cert8 : PlanarAnchorCert := ⟨0, (1 / 1024 : ℚ), reg8⟩

theorem tile8_cert : planarAnchorCertOkFar cert8 tile8 0 = true := by
  decide +kernel

theorem tile8_ok : (planarAnchorCertOk cert8 tile8 0 || planarAnchorCertOkFar cert8 tile8 0) = true := by
  rw [tile8_cert, Bool.or_true]

theorem tile8_optical (latticeCase : LatticeCase) (p : Chart) (hp : tile8.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) :=
  planarAnchorCertOkFar_sound latticeCase cert8 tile8 0 tile8_cert p hp gp

theorem tile8_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .relativeOptical)
    (hh : hint w = some (.relative cert8)) : stage5bOpticalCheck hint w tile8 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile8_ok, Bool.true_and,
    decide_true]

def tile8Pt : Fin 8 → ℚ := ![(14269 / 16384 : ℚ), (6889 / 8192 : ℚ), (67 / 256 : ℚ), (3 / 128 : ℚ), (-3 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-1 / 2 : ℚ)]

theorem tile8_nonvacuous : ∃ p : Chart, tile8.Mem p ∧ good p := by
  have hall : ∀ i, tile8.lo i ≤ tile8Pt i ∧ tile8Pt i ≤ tile8.hi i := by
    decide +kernel
  refine ⟨fun i => (tile8Pt i : ℝ), fun i => ?_,
    good_of_check tile8Pt (-1) (-1) (1 / 2 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group9 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-33 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (431 / 512 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

def tile9 : Cell := ⟨![(886149 / 1024000 : ℚ), (53 / 64 : ℚ), (9 / 32 : ℚ), (0 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-33 / 64 : ℚ)],
    ![(1781149 / 2048000 : ℚ), (1703 / 2048 : ℚ), (19 / 64 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

theorem tile9_address : sameCell (descendOptical group9 [false, false, false, false, false]) tile9 = true := by
  decide +kernel

def reg9 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(343694970190721811 / 576460752512166151 : ℚ), (326271995965449654 / 576460752512166151 : ℚ), (328218450580117942 / 576460752512166151 : ℚ)], ![(-462792904792020738 / 576460752512166151 : ℚ), (243954463811593574 / 576460752512166151 : ℚ), (242107302755316291 / 576460752512166151 : ℚ)], ![(-1869204818993294 / 576460752512166151 : ℚ), (-407847769911780147 / 576460752512166151 : ℚ), (407386428146821266 / 576460752512166151 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 1]

def cert9 : PlanarAnchorCert := ⟨0, (1 / 1024 : ℚ), reg9⟩

theorem tile9_cert : planarAnchorCertOk cert9 tile9 0 = true := by
  decide +kernel

theorem tile9_ok : (planarAnchorCertOk cert9 tile9 0 || planarAnchorCertOkFar cert9 tile9 0) = true := by
  rw [tile9_cert, Bool.true_or]

theorem tile9_optical (latticeCase : LatticeCase) (p : Chart) (hp : tile9.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) :=
  planarAnchorCertOk_sound latticeCase cert9 tile9 0 tile9_cert p hp gp

theorem tile9_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .relativeOptical)
    (hh : hint w = some (.relative cert9)) : stage5bOpticalCheck hint w tile9 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile9_ok, Bool.true_and,
    decide_true]

def tile9Pt : Fin 8 → ℚ := ![(3553447 / 4096000 : ℚ), (3399 / 4096 : ℚ), (75 / 256 : ℚ), (1 / 128 : ℚ), (-1 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-65 / 128 : ℚ)]

theorem tile9_nonvacuous : ∃ p : Chart, tile9.Mem p ∧ good p := by
  have hall : ∀ i, tile9.lo i ≤ tile9Pt i ∧ tile9Pt i ≤ tile9.hi i := by
    decide +kernel
  refine ⟨fun i => (tile9Pt i : ℝ), fun i => ?_,
    good_of_check tile9Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group10 : Cell := ⟨![(439 / 512 : ℚ), (53 / 64 : ℚ), (9 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (431 / 512 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile10 : Cell := ⟨![(439 / 512 : ℚ), (53 / 64 : ℚ), (9 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(3529 / 4096 : ℚ), (1703 / 2048 : ℚ), (19 / 64 : ℚ), (3 / 64 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile10_address : sameCell (descendOptical group10 [false, false, false, false, true, false, false]) tile10 = true := by
  decide +kernel

def reg10 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(343615794646309141 / 576460752017666495 : ℚ), (322386916895198238 / 576460752017666495 : ℚ), (66423447697682070 / 115292150403533299 : ℚ)], ![(-462827440460088138 / 576460752017666495 : ℚ), (243871825177099066 / 576460752017666495 : ℚ), (48424907582246385 / 115292150403533299 : ℚ)], ![(-1018717694411202 / 115292150403533299 : ℚ), (-82194940797198111 / 115292150403533299 : ℚ), (80840793330317674 / 115292150403533299 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 1]

def cert10 : PlanarAnchorCert := ⟨0, (1 / 1024 : ℚ), reg10⟩

theorem tile10_cert : planarAnchorCertOk cert10 tile10 0 = true := by
  decide +kernel

theorem tile10_ok : (planarAnchorCertOk cert10 tile10 0 || planarAnchorCertOkFar cert10 tile10 0) = true := by
  rw [tile10_cert, Bool.true_or]

theorem tile10_optical (latticeCase : LatticeCase) (p : Chart) (hp : tile10.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) :=
  planarAnchorCertOk_sound latticeCase cert10 tile10 0 tile10_cert p hp gp

theorem tile10_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .relativeOptical)
    (hh : hint w = some (.relative cert10)) : stage5bOpticalCheck hint w tile10 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile10_ok, Bool.true_and,
    decide_true]

def tile10Pt : Fin 8 → ℚ := ![(7041 / 8192 : ℚ), (3399 / 4096 : ℚ), (37 / 128 : ℚ), (5 / 128 : ℚ), (-1 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem tile10_nonvacuous : ∃ p : Chart, tile10.Mem p ∧ good p := by
  have hall : ∀ i, tile10.lo i ≤ tile10Pt i ∧ tile10Pt i ≤ tile10.hi i := by
    decide +kernel
  refine ⟨fun i => (tile10Pt i : ℝ), fun i => ?_,
    good_of_check tile10Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage5bOptical.Leaves2
