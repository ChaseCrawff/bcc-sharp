import BccSharp.Cover.Stage5bOptical
import BccSharp.Cover.Stage5bPhase
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! # Stage5b optical tiles on the Lean deficit routes, part 0 (generated)

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

namespace BccSharp.Coulomb.CompactCover.Stage5bOptical.Leaves0

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

def group0 : Cell := ⟨![(443753 / 512000 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-63 / 128 : ℚ)],
    ![(111811 / 128000 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ)]⟩

def tile0 : Cell := ⟨![(443753 / 512000 : ℚ), (841 / 1024 : ℚ), (5 / 16 : ℚ), (1 / 64 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-63 / 128 : ℚ)],
    ![(111811 / 128000 : ℚ), (53 / 64 : ℚ), (21 / 64 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile0_address : sameCell (descendOptical group0 [false, true, false, true, true]) tile0 = true := by
  decide +kernel

def reg0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(336040711409672889 / 576460751945564921 : ℚ), (328234236511290072 / 576460751945564921 : ℚ), (334134590832463144 / 576460751945564921 : ℚ)], ![(-468371071337502056 / 576460751945564921 : ℚ), (238548052440898776 / 576460751945564921 : ℚ), (236707339861823673 / 576460751945564921 : ℚ)], ![(-3489748284279528 / 576460751945564921 : ℚ), (-409468083239891641 / 576460751945564921 : ℚ), (405747099802829976 / 576460751945564921 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def hint0 : DHint where
  reg := reg0
  cap := 25434338521224021823249080885

theorem tile0_ok : wholeOk hint0 tile0 = true := by
  decide +kernel

theorem tile0_deficit (p : Chart) (hp : tile0.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  wholeOk_sound hint0 tile0 tile0_ok p hp gp

theorem tile0_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.whole hint0)) : stage5bOpticalCheck hint w tile0 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile0_ok, Bool.true_and,
    decide_true]

def tile0Pt : Fin 8 → ℚ := ![(890997 / 1024000 : ℚ), (1689 / 2048 : ℚ), (41 / 128 : ℚ), (3 / 128 : ℚ), (-1 / 128 : ℚ), (-65 / 128 : ℚ), (-65 / 128 : ℚ), (-125 / 256 : ℚ)]

theorem tile0_nonvacuous : ∃ p : Chart, tile0.Mem p ∧ good p := by
  have hall : ∀ i, tile0.lo i ≤ tile0Pt i ∧ tile0Pt i ≤ tile0.hi i := by
    decide +kernel
  refine ⟨fun i => (tile0Pt i : ℝ), fun i => ?_,
    good_of_check tile0Pt (-1) (-1) (125 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group1 : Cell := ⟨![(379458944064943 / 436645906944000 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-65 / 128 : ℚ)],
    ![(111811 / 128000 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]⟩

def tile1 : Cell := ⟨![(379458944064943 / 436645906944000 : ℚ), (1689 / 2048 : ℚ), (23 / 64 : ℚ), (0 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-65 / 128 : ℚ)],
    ![(111811 / 128000 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 64 : ℚ), (-1 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]⟩

theorem tile1_address : sameCell (descendOptical group1 [true, true, true, false, false, true]) tile1 = true := by
  decide +kernel

def reg1 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(7631473211647935 / 13563782399752051 : ℚ), (134386846647512350 / 230584300795784867 : ℚ), (135196573273031142 / 230584300795784867 : ℚ)], ![(-56064148873046574 / 67818911998760255 : ℚ), (464302433920652181 / 1152921503978924335 : ℚ), (90613395083087986 / 230584300795784867 : ℚ)], ![(-481093893078118 / 67818911998760255 : ℚ), (-813729457741228158 / 1152921503978924335 : ℚ), (163340806231104177 / 230584300795784867 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def hint1 : DHint where
  reg := reg1
  cap := 26366248836198778934164990659

theorem tile1_ok : wholeOk hint1 tile1 = true := by
  decide +kernel

theorem tile1_deficit (p : Chart) (hp : tile1.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  wholeOk_sound hint1 tile1 tile1_ok p hp gp

theorem tile1_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.whole hint1)) : stage5bOpticalCheck hint w tile1 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile1_ok, Bool.true_and,
    decide_true]

def tile1Pt : Fin 8 → ℚ := ![(760879377668971 / 873291813888000 : ℚ), (3385 / 4096 : ℚ), (47 / 128 : ℚ), (1 / 128 : ℚ), (-3 / 128 : ℚ), (-65 / 128 : ℚ), (-65 / 128 : ℚ), (-129 / 256 : ℚ)]

theorem tile1_nonvacuous : ∃ p : Chart, tile1.Mem p ∧ good p := by
  have hall : ∀ i, tile1.lo i ≤ tile1Pt i ∧ tile1Pt i ≤ tile1.hi i := by
    decide +kernel
  refine ⟨fun i => (tile1Pt i : ℝ), fun i => ?_,
    good_of_check tile1Pt (-1) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group2 : Cell := ⟨![(439 / 512 : ℚ), (827 / 1024 : ℚ), (11 / 32 : ℚ), (0 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile2 : Cell := ⟨![(439 / 512 : ℚ), (827 / 1024 : ℚ), (45 / 128 : ℚ), (0 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(3529 / 4096 : ℚ), (1661 / 2048 : ℚ), (23 / 64 : ℚ), (1 / 128 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile2_address : sameCell (descendOptical group2 [false, false, false, false, false, true, false]) tile2 = true := by
  decide +kernel

def reg2_0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(654543801164678745 / 1152921504225030491 : ℚ), (670228464013892930 / 1152921504225030491 : ℚ), (672007599128892534 / 1152921504225030491 : ℚ)], ![(-949000712993536466 / 1152921504225030491 : ℚ), (450063424385539095 / 1152921504225030491 : ℚ), (475466671463551230 / 1152921504225030491 : ℚ)], ![(14073165925260870 / 1152921504225030491 : ℚ), (-823082447243559534 / 1152921504225030491 : ℚ), (807195903077375705 / 1152921504225030491 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf2_0 : AnchorHint where
  reg := reg2_0
  cap := 13524266621267542025777790603
  margin := (148495130622779 / 4611686018427387904 : ℚ)
  depth := 0

theorem tile2_ok : anchorTreeOk (.leaf leaf2_0) tile2 = true := by
  decide +kernel

def tree2 : AnchorTree := (.leaf leaf2_0)

theorem tile2_tree : anchorTreeOk tree2 tile2 = true := tile2_ok

theorem tile2_deficit (p : Chart) (hp : tile2.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  anchorTreeOk_sound tree2 tile2 tile2_tree p hp gp

theorem tile2_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.anchor tree2)) : stage5bOpticalCheck hint w tile2 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile2_tree, Bool.true_and,
    decide_true]

def tile2Pt : Fin 8 → ℚ := ![(7041 / 8192 : ℚ), (3315 / 4096 : ℚ), (91 / 256 : ℚ), (1 / 256 : ℚ), (7 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem tile2_nonvacuous : ∃ p : Chart, tile2.Mem p ∧ good p := by
  have hall : ∀ i, tile2.lo i ≤ tile2Pt i ∧ tile2Pt i ≤ tile2.hi i := by
    decide +kernel
  refine ⟨fun i => (tile2Pt i : ℝ), fun i => ?_,
    good_of_check tile2Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group3 : Cell := ⟨![(439 / 512 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (-3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile3 : Cell := ⟨![(439 / 512 : ℚ), (1675 / 2048 : ℚ), (43 / 128 : ℚ), (1 / 128 : ℚ), (-3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(3529 / 4096 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 64 : ℚ), (-1 / 32 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile3_address : sameCell (descendOptical group3 [false, true, false, false, true, true, true]) tile3 = true := by
  decide +kernel

def reg3_0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(26495212459749463 / 46116860209117777 : ℚ), (26573303206453968 / 46116860209117777 : ℚ), (26807239114797156 / 46116860209117777 : ℚ)], ![(-37742511939042816 / 46116860209117777 : ℚ), (19102840987339927 / 46116860209117777 : ℚ), (18367064389578612 / 46116860209117777 : ℚ)], ![(-520869265034748 / 46116860209117777 : ℚ), (-32491626897672876 / 46116860209117777 : ℚ), (32722892175027457 / 46116860209117777 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf3_0 : AnchorHint where
  reg := reg3_0
  cap := 5269965260429115213816546483
  margin := (99456064328589 / 4611686018427387904 : ℚ)
  depth := 0

theorem tile3_ok : anchorTreeOk (.leaf leaf3_0) tile3 = true := by
  decide +kernel

def tree3 : AnchorTree := (.leaf leaf3_0)

theorem tile3_tree : anchorTreeOk tree3 tile3 = true := tile3_ok

theorem tile3_deficit (p : Chart) (hp : tile3.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  anchorTreeOk_sound tree3 tile3 tile3_tree p hp gp

theorem tile3_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.anchor tree3)) : stage5bOpticalCheck hint w tile3 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile3_tree, Bool.true_and,
    decide_true]

def tile3Pt : Fin 8 → ℚ := ![(7041 / 8192 : ℚ), (3357 / 4096 : ℚ), (87 / 256 : ℚ), (3 / 256 : ℚ), (-5 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem tile3_nonvacuous : ∃ p : Chart, tile3.Mem p ∧ good p := by
  have hall : ∀ i, tile3.lo i ≤ tile3Pt i ∧ tile3Pt i ≤ tile3.hi i := by
    decide +kernel
  refine ⟨fun i => (tile3Pt i : ℝ), fun i => ?_,
    good_of_check tile3Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group4 : Cell := ⟨![(439 / 512 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (53 / 64 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

def tile4 : Cell := ⟨![(1773 / 2048 : ℚ), (1675 / 2048 : ℚ), (5 / 16 : ℚ), (3 / 64 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (841 / 1024 : ℚ), (21 / 64 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem tile4_address : sameCell (descendOptical group4 [true, false, false, true, true, false, true]) tile4 = true := by
  decide +kernel

def reg4_0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(336971373091449256 / 576460752575889005 : ℚ), (323806747289110092 / 576460752575889005 : ℚ), (67500069151748289 / 115292150515177801 : ℚ)], ![(-467667188668752408 / 576460752575889005 : ℚ), (239212693945206469 / 576460752575889005 : ℚ), (47485444910415588 / 115292150515177801 : ℚ)], ![(-1337065740929289 / 115292150515177801 : ℚ), (-82518719506760088 / 115292150515177801 : ℚ), (80505609472778344 / 115292150515177801 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf4_0 : AnchorHint where
  reg := reg4_0
  cap := 9644058847590069696593884374
  margin := (295247125926227 / 18446744073709551616 : ℚ)
  depth := 0

def reg4_1 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(134013119424697795 / 230584300977128421 : ℚ), (649576179197149204 / 1152921504885642105 : ℚ), (676971845351746472 / 1152921504885642105 : ℚ)], ![(-187623231761721404 / 230584300977128421 : ℚ), (95142472328445269 / 230584300977128421 : ℚ), (94416909076866892 / 230584300977128421 : ℚ)], ![(-2669565968469400 / 230584300977128421 : ℚ), (-825213022696674628 / 1152921504885642105 : ℚ), (805029998843577871 / 1152921504885642105 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

def leaf4_1 : AnchorHint where
  reg := reg4_1
  cap := 8443076293377851215916796863
  margin := (209170483867041 / 18446744073709551616 : ℚ)
  depth := 0

def node4_0 : Cell := ⟨![(1773 / 2048 : ℚ), (1675 / 2048 : ℚ), (5 / 16 : ℚ), (3 / 64 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (841 / 1024 : ℚ), (41 / 128 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem node4_0_ok : anchorTreeOk (.leaf leaf4_0) node4_0 = true := by
  decide +kernel

def node4_1 : Cell := ⟨![(1773 / 2048 : ℚ), (1675 / 2048 : ℚ), (41 / 128 : ℚ), (3 / 64 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (841 / 1024 : ℚ), (21 / 64 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem node4_1_ok : anchorTreeOk (.leaf leaf4_1) node4_1 = true := by
  decide +kernel

theorem tile4_ok : anchorTreeOk (.split (.leaf leaf4_0) (.leaf leaf4_1)) tile4 = true :=
  anchorTreeOk_split (.leaf leaf4_0) (.leaf leaf4_1) tile4 node4_0 node4_1
    (by decide +kernel) (by decide +kernel) node4_0_ok node4_1_ok

def tree4 : AnchorTree := (.split (.leaf leaf4_0) (.leaf leaf4_1))

theorem tile4_tree : anchorTreeOk tree4 tile4 = true := tile4_ok

theorem tile4_deficit (p : Chart) (hp : tile4.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  anchorTreeOk_sound tree4 tile4 tile4_tree p hp gp

theorem tile4_witness (hint : WitnessRef → Option OpticalHint) (w : WitnessRef)
    (hs : opticalSource w.source = true) (hr : w.route = .strictDeficit)
    (hh : hint w = some (.anchor tree4)) : stage5bOpticalCheck hint w tile4 = true := by
  simp only [stage5bOpticalCheck, hs, hh, opticalOk, hr, tile4_tree, Bool.true_and,
    decide_true]

def tile4Pt : Fin 8 → ℚ := ![(7109 / 8192 : ℚ), (6721 / 8192 : ℚ), (167 / 512 : ℚ), (7 / 128 : ℚ), (-1 / 128 : ℚ), (-65 / 128 : ℚ), (-65 / 128 : ℚ), (-127 / 256 : ℚ)]

theorem tile4_nonvacuous : ∃ p : Chart, tile4.Mem p ∧ good p := by
  have hall : ∀ i, tile4.lo i ≤ tile4Pt i ∧ tile4Pt i ≤ tile4.hi i := by
    decide +kernel
  refine ⟨fun i => (tile4Pt i : ℝ), fun i => ?_,
    good_of_check tile4Pt (-1) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage5bOptical.Leaves0
