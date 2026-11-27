import BccSharp.Cover.Stage5bPhase
import BccSharp.TwoSite.DefectCutoffBox
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! # The far defect bound on Stage5b optical tiles (generated)

Generated. The tiles are the thinnest tile of each
absolute Stage5b optical route (`whole_defect`, `screened_anchor`,
`taylor_anchor`) and the absolute-route tile with the largest registered cap.
On each, `JLeaf.Cutoff.defect_le_box_far` proves `defect ≤ regCost` at every
point of the tile, whatever the size of the cost (`_defect`): the group's
registration passes `registrationCheck` (`reg_check`, kernel), and every
annular image is at least `13/10` long on the tile (`_far`, kernel). That
`regCost` stays below the sweep's own defect bound is not checked here; `taylor_anchor` uses the
local-atlas majorant inside a Taylor bound instead.
The energy side of these routes is not proved here. -/

namespace BccSharp.Coulomb.CompactCover.Stage5bPhase.OpticalDefect
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Stage5bPhase
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Cutoff

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

theorem reg0_check : registrationCheck reg0.B reg0.N reg0.U reg0.f0 = true := by
  decide +kernel

theorem tile0_far : annFarOk reg0.N reg0.w tile0 = true := by
  decide +kernel

theorem tile0_defect (p : Chart) (hp : tile0.Mem p) :
    defect (chartPoint p) ≤ regCost reg0.N reg0.U reg0.w p :=
  defect_le_box_far reg0 tile0 reg0_check tile0_far p hp

def tile0Pt : Fin 8 → ℚ := ![(890997 / 1024000 : ℚ), (1689 / 2048 : ℚ), (41 / 128 : ℚ), (3 / 128 : ℚ), (-1 / 128 : ℚ), (-65 / 128 : ℚ), (-65 / 128 : ℚ), (-125 / 256 : ℚ)]

theorem tile0_nonvacuous : ∃ p : Chart, tile0.Mem p ∧ good p := by
  have hall : ∀ i, tile0.lo i ≤ tile0Pt i ∧ tile0Pt i ≤ tile0.hi i := by
    decide +kernel
  refine ⟨fun i => (tile0Pt i : ℝ), fun i => ?_,
    good_of_check tile0Pt (-1) (-1) (125 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group1 : Cell := ⟨![(439 / 512 : ℚ), (827 / 1024 : ℚ), (11 / 32 : ℚ), (0 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile1 : Cell := ⟨![(439 / 512 : ℚ), (827 / 1024 : ℚ), (45 / 128 : ℚ), (0 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(3529 / 4096 : ℚ), (1661 / 2048 : ℚ), (23 / 64 : ℚ), (1 / 128 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile1_address : sameCell (descendOptical group1 [false, false, false, false, false, true, false]) tile1 = true := by
  decide +kernel

def reg1 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(654543801164678745 / 1152921504225030491 : ℚ), (670228464013892930 / 1152921504225030491 : ℚ), (672007599128892534 / 1152921504225030491 : ℚ)], ![(-949000712993536466 / 1152921504225030491 : ℚ), (450063424385539095 / 1152921504225030491 : ℚ), (475466671463551230 / 1152921504225030491 : ℚ)], ![(14073165925260870 / 1152921504225030491 : ℚ), (-823082447243559534 / 1152921504225030491 : ℚ), (807195903077375705 / 1152921504225030491 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

theorem reg1_check : registrationCheck reg1.B reg1.N reg1.U reg1.f0 = true := by
  decide +kernel

theorem tile1_far : annFarOk reg1.N reg1.w tile1 = true := by
  decide +kernel

theorem tile1_defect (p : Chart) (hp : tile1.Mem p) :
    defect (chartPoint p) ≤ regCost reg1.N reg1.U reg1.w p :=
  defect_le_box_far reg1 tile1 reg1_check tile1_far p hp

def tile1Pt : Fin 8 → ℚ := ![(7041 / 8192 : ℚ), (3315 / 4096 : ℚ), (91 / 256 : ℚ), (1 / 256 : ℚ), (7 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem tile1_nonvacuous : ∃ p : Chart, tile1.Mem p ∧ good p := by
  have hall : ∀ i, tile1.lo i ≤ tile1Pt i ∧ tile1Pt i ≤ tile1.hi i := by
    decide +kernel
  refine ⟨fun i => (tile1Pt i : ℝ), fun i => ?_,
    good_of_check tile1Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group2 : Cell := ⟨![(439 / 512 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (-1 / 32 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (53 / 64 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

def tile2 : Cell := ⟨![(1773 / 2048 : ℚ), (1675 / 2048 : ℚ), (5 / 16 : ℚ), (3 / 64 : ℚ), (-1 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (841 / 1024 : ℚ), (21 / 64 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem tile2_address : sameCell (descendOptical group2 [true, false, false, true, true, false, true]) tile2 = true := by
  decide +kernel

def reg2 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(672005638901920393 / 1152921504833491929 : ℚ), (648596210463639164 / 1152921504833491929 : ℚ), (675987702080261236 / 1152921504833491929 : ℚ)], ![(-936727253469929636 / 1152921504833491929 : ℚ), (477069908743553039 / 1152921504833491929 : ℚ), (473470538772608032 / 1152921504833491929 : ℚ)], ![(-785839639178092 / 67818912049028937 : ℚ), (-48541184106923504 / 67818912049028937 : ℚ), (47355472049945567 / 67818912049028937 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

theorem reg2_check : registrationCheck reg2.B reg2.N reg2.U reg2.f0 = true := by
  decide +kernel

theorem tile2_far : annFarOk reg2.N reg2.w tile2 = true := by
  decide +kernel

theorem tile2_defect (p : Chart) (hp : tile2.Mem p) :
    defect (chartPoint p) ≤ regCost reg2.N reg2.U reg2.w p :=
  defect_le_box_far reg2 tile2 reg2_check tile2_far p hp

def tile2Pt : Fin 8 → ℚ := ![(7109 / 8192 : ℚ), (6721 / 8192 : ℚ), (167 / 512 : ℚ), (7 / 128 : ℚ), (-1 / 128 : ℚ), (-65 / 128 : ℚ), (-65 / 128 : ℚ), (-127 / 256 : ℚ)]

theorem tile2_nonvacuous : ∃ p : Chart, tile2.Mem p ∧ good p := by
  have hall : ∀ i, tile2.lo i ≤ tile2Pt i ∧ tile2Pt i ≤ tile2.hi i := by
    decide +kernel
  refine ⟨fun i => (tile2Pt i : ℝ), fun i => ?_,
    good_of_check tile2Pt (-1) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group3 : Cell := ⟨![(439 / 512 : ℚ), (53 / 64 : ℚ), (1 / 4 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (431 / 512 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

def tile3 : Cell := ⟨![(1773 / 2048 : ℚ), (855 / 1024 : ℚ), (1 / 4 : ℚ), (3 / 64 : ℚ), (3 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (431 / 512 : ℚ), (17 / 64 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)]⟩

theorem tile3_address : sameCell (descendOptical group3 [false, true, true, false, true, true]) tile3 = true := by
  decide +kernel

def reg3 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(351201450284008372 / 576460752825870045 : ℚ), (316085178642467371 / 576460752825870045 : ℚ), (66046862365910320 / 115292150565174009 : ℚ)], ![(-91424792751831281 / 115292150565174009 : ℚ), (48296546082992092 / 115292150565174009 : ℚ), (51002263564285784 / 115292150565174009 : ℚ)], ![(1490846771300296 / 576460752825870045 : ℚ), (-417232849021339472 / 576460752825870045 : ℚ), (79554139206457255 / 115292150565174009 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![0, 0, 0]

theorem reg3_check : registrationCheck reg3.B reg3.N reg3.U reg3.f0 = true := by
  decide +kernel

theorem tile3_far : annFarOk reg3.N reg3.w tile3 = true := by
  decide +kernel

theorem tile3_defect (p : Chart) (hp : tile3.Mem p) :
    defect (chartPoint p) ≤ regCost reg3.N reg3.U reg3.w p :=
  defect_le_box_far reg3 tile3 reg3_check tile3_far p hp

def tile3Pt : Fin 8 → ℚ := ![(3563 / 4096 : ℚ), (3441 / 4096 : ℚ), (67 / 256 : ℚ), (7 / 128 : ℚ), (7 / 128 : ℚ), (-65 / 128 : ℚ), (-1 / 2 : ℚ), (-65 / 128 : ℚ)]

theorem tile3_nonvacuous : ∃ p : Chart, tile3.Mem p ∧ good p := by
  have hall : ∀ i, tile3.lo i ≤ tile3Pt i ∧ tile3Pt i ≤ tile3.hi i := by
    decide +kernel
  refine ⟨fun i => (tile3Pt i : ℝ), fun i => ?_,
    good_of_check tile3Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage5bPhase.OpticalDefect
