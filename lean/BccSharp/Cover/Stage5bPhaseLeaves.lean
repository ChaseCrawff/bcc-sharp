import BccSharp.Cover.Stage5bPhase
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! # The thinnest Stage5b phase leaves (generated)

Generated. Each
leaf is the ranked Stage5a root refined along its recorded path (`_address`,
kernel), accepted by the fixed-point Jensen check with its recorded profile
(`_check`, kernel), and therefore above FCC at every `good` point
(`_strictFCC`). The recorded margin is in each docstring. -/

namespace BccSharp.Coulomb.CompactCover.Stage5bPhase.Leaves
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Stage5bPhase

def root0 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (3 / 16 : ℚ), (1 / 8 : ℚ), (29 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (7 / 32 : ℚ), (5 / 32 : ℚ), (15 / 32 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def leaf0 : Cell := ⟨![(1773 / 2048 : ℚ), (813 / 1024 : ℚ), (27 / 64 : ℚ), (3 / 16 : ℚ), (1 / 8 : ℚ), (29 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (13 / 64 : ℚ), (9 / 64 : ℚ), (15 / 32 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem leaf0_address : sameCell (descendStage5b root0 [true, true, true, false, true, false, false]) leaf0 = true := by
  decide +kernel

theorem leaf0_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 leaf0 leaf0 = true := by
  decide +kernel

theorem leaf0_strictFCC (p : Chart) (hp : leaf0.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf0_check p hp gp

def leaf0Pt : Fin 8 → ℚ := ![(7109 / 8192 : ℚ), (1633 / 2048 : ℚ), (55 / 128 : ℚ), (25 / 128 : ℚ), (17 / 128 : ℚ), (59 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem leaf0_nonvacuous : ∃ p : Chart, leaf0.Mem p ∧ good p := by
  have hall : ∀ i, leaf0.lo i ≤ leaf0Pt i ∧ leaf0Pt i ≤ leaf0.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf0Pt i : ℝ), fun i => ?_,
    good_of_check leaf0Pt (0) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def root1 : Cell := ⟨![(861 / 1024 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (15 / 32 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(439 / 512 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 64 : ℚ), (1 / 2 : ℚ), (-15 / 32 : ℚ), (-15 / 32 : ℚ)]⟩

def leaf1 : Cell := ⟨![(3461 / 4096 : ℚ), (841 / 1024 : ℚ), (23 / 64 : ℚ), (3 / 64 : ℚ), (0 : ℚ), (31 / 64 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(1739 / 2048 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 64 : ℚ), (63 / 128 : ℚ), (-15 / 32 : ℚ), (-31 / 64 : ℚ)]⟩

theorem leaf1_address : sameCell (descendStage5b root1 [false, true, true, false, true, true, true, false]) leaf1 = true := by
  decide +kernel

theorem leaf1_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (7 : ℚ) 3 leaf1 leaf1 = true := by
  decide +kernel

theorem leaf1_strictFCC (p : Chart) (hp : leaf1.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf1_check p hp gp

def leaf1Pt : Fin 8 → ℚ := ![(6939 / 8192 : ℚ), (1689 / 2048 : ℚ), (47 / 128 : ℚ), (7 / 128 : ℚ), (1 / 128 : ℚ), (125 / 256 : ℚ), (-61 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem leaf1_nonvacuous : ∃ p : Chart, leaf1.Mem p ∧ good p := by
  have hall : ∀ i, leaf1.lo i ≤ leaf1Pt i ∧ leaf1Pt i ≤ leaf1.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf1Pt i : ℝ), fun i => ?_,
    good_of_check leaf1Pt (0) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def root2 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 32 : ℚ), (13 / 32 : ℚ), (13 / 32 : ℚ), (31 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (3 / 32 : ℚ), (1 / 16 : ℚ), (27 / 64 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)]⟩

def leaf2 : Cell := ⟨![(1773 / 2048 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (5 / 64 : ℚ), (1 / 32 : ℚ), (13 / 32 : ℚ), (27 / 64 : ℚ), (31 / 64 : ℚ)],
    ![(3563 / 4096 : ℚ), (813 / 1024 : ℚ), (25 / 64 : ℚ), (3 / 32 : ℚ), (3 / 64 : ℚ), (27 / 64 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)]⟩

theorem leaf2_address : sameCell (descendStage5b root2 [true, false, true, false, false, false, true, false]) leaf2 = true := by
  decide +kernel

theorem leaf2_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (7 : ℚ) 3 leaf2 leaf2 = true := by
  decide +kernel

theorem leaf2_strictFCC (p : Chart) (hp : leaf2.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf2_check p hp gp

theorem leaf2_not_reduced (p : Chart) (hp : leaf2.Mem p) :
    ¬ reductionInequalities p :=
  Stage5bPhase.notReducedE2_sound leaf2 (by decide +kernel) p hp

def root3 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (0 : ℚ), (25 / 64 : ℚ), (13 / 32 : ℚ), (31 / 64 : ℚ)],
    ![(895 / 1024 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)]⟩

def leaf3 : Cell := ⟨![(3529 / 4096 : ℚ), (403 / 512 : ℚ), (27 / 64 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (25 / 64 : ℚ), (27 / 64 : ℚ), (31 / 64 : ℚ)],
    ![(1773 / 2048 : ℚ), (813 / 1024 : ℚ), (7 / 16 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (13 / 32 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)]⟩

theorem leaf3_address : sameCell (descendStage5b root3 [false, true, true, false, true, true, true, false]) leaf3 = true := by
  decide +kernel

theorem leaf3_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (7 : ℚ) 3 leaf3 leaf3 = true := by
  decide +kernel

theorem leaf3_strictFCC (p : Chart) (hp : leaf3.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf3_check p hp gp

def leaf3Pt : Fin 8 → ℚ := ![(7075 / 8192 : ℚ), (1619 / 2048 : ℚ), (55 / 128 : ℚ), (3 / 128 : ℚ), (1 / 128 : ℚ), (51 / 128 : ℚ), (55 / 128 : ℚ), (63 / 128 : ℚ)]

theorem leaf3_nonvacuous : ∃ p : Chart, leaf3.Mem p ∧ good p := by
  have hall : ∀ i, leaf3.lo i ≤ leaf3Pt i ∧ leaf3Pt i ≤ leaf3.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf3Pt i : ℝ), fun i => ?_,
    good_of_check leaf3Pt (0) (0) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def root4 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (1 / 16 : ℚ), (3 / 32 : ℚ), (15 / 32 : ℚ), (15 / 32 : ℚ), (-63 / 128 : ℚ)]⟩

def leaf4 : Cell := ⟨![(439 / 512 : ℚ), (813 / 1024 : ℚ), (25 / 64 : ℚ), (3 / 64 : ℚ), (1 / 16 : ℚ), (29 / 64 : ℚ), (7 / 16 : ℚ), (-1 / 2 : ℚ)],
    ![(3529 / 4096 : ℚ), (205 / 256 : ℚ), (13 / 32 : ℚ), (1 / 16 : ℚ), (3 / 32 : ℚ), (15 / 32 : ℚ), (29 / 64 : ℚ), (-63 / 128 : ℚ)]⟩

theorem leaf4_address : sameCell (descendStage5b root4 [false, false, true, false, true, false, true, true]) leaf4 = true := by
  decide +kernel

theorem leaf4_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 leaf4 leaf4 = true := by
  decide +kernel

theorem leaf4_strictFCC (p : Chart) (hp : leaf4.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf4_check p hp gp

def leaf4Pt : Fin 8 → ℚ := ![(7041 / 8192 : ℚ), (1633 / 2048 : ℚ), (51 / 128 : ℚ), (7 / 128 : ℚ), (5 / 64 : ℚ), (59 / 128 : ℚ), (57 / 128 : ℚ), (-127 / 256 : ℚ)]

theorem leaf4_nonvacuous : ∃ p : Chart, leaf4.Mem p ∧ good p := by
  have hall : ∀ i, leaf4.lo i ≤ leaf4Pt i ∧ leaf4Pt i ≤ leaf4.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf4Pt i : ℝ), fun i => ?_,
    good_of_check leaf4Pt (0) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def root5 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (-1 / 16 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (1 / 32 : ℚ), (-1 / 32 : ℚ), (15 / 32 : ℚ), (15 / 32 : ℚ), (-63 / 128 : ℚ)]⟩

def leaf5 : Cell := ⟨![(1773 / 2048 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (1 / 64 : ℚ), (-1 / 16 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (813 / 1024 : ℚ), (25 / 64 : ℚ), (1 / 32 : ℚ), (-1 / 32 : ℚ), (29 / 64 : ℚ), (29 / 64 : ℚ), (-63 / 128 : ℚ)]⟩

theorem leaf5_address : sameCell (descendStage5b root5 [true, false, false, false, false, false, false, true]) leaf5 = true := by
  decide +kernel

theorem leaf5_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 leaf5 leaf5 = true := by
  decide +kernel

theorem leaf5_strictFCC (p : Chart) (hp : leaf5.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf5_check p hp gp

theorem leaf5_not_reduced (p : Chart) (hp : leaf5.Mem p) :
    ¬ reductionInequalities p :=
  Stage5bPhase.notReducedE2_sound leaf5 (by decide +kernel) p hp

def root6 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (7 / 32 : ℚ), (1 / 8 : ℚ), (31 / 64 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(895 / 1024 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (1 / 4 : ℚ), (5 / 32 : ℚ), (1 / 2 : ℚ), (-15 / 32 : ℚ), (-31 / 64 : ℚ)]⟩

def leaf6 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (13 / 32 : ℚ), (7 / 32 : ℚ), (1 / 8 : ℚ), (31 / 64 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(3529 / 4096 : ℚ), (813 / 1024 : ℚ), (7 / 16 : ℚ), (1 / 4 : ℚ), (5 / 32 : ℚ), (1 / 2 : ℚ), (-15 / 32 : ℚ), (-31 / 64 : ℚ)]⟩

theorem leaf6_address : sameCell (descendStage5b root6 [false, true, false, false]) leaf6 = true := by
  decide +kernel

theorem leaf6_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 leaf6 leaf6 = true := by
  decide +kernel

theorem leaf6_strictFCC (p : Chart) (hp : leaf6.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf6_check p hp gp

def leaf6Pt : Fin 8 → ℚ := ![(7041 / 8192 : ℚ), (1619 / 2048 : ℚ), (27 / 64 : ℚ), (15 / 64 : ℚ), (9 / 64 : ℚ), (63 / 128 : ℚ), (-61 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem leaf6_nonvacuous : ∃ p : Chart, leaf6.Mem p ∧ good p := by
  have hall : ∀ i, leaf6.lo i ≤ leaf6Pt i ∧ leaf6Pt i ≤ leaf6.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf6Pt i : ℝ), fun i => ?_,
    good_of_check leaf6Pt (0) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def root7 : Cell := ⟨![(439 / 512 : ℚ), (403 / 512 : ℚ), (3 / 8 : ℚ), (0 : ℚ), (-1 / 32 : ℚ), (27 / 64 : ℚ), (13 / 32 : ℚ), (63 / 128 : ℚ)],
    ![(895 / 1024 : ℚ), (205 / 256 : ℚ), (7 / 16 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)]⟩

def leaf7 : Cell := ⟨![(3529 / 4096 : ℚ), (813 / 1024 : ℚ), (25 / 64 : ℚ), (0 : ℚ), (-1 / 32 : ℚ), (27 / 64 : ℚ), (27 / 64 : ℚ), (63 / 128 : ℚ)],
    ![(1773 / 2048 : ℚ), (205 / 256 : ℚ), (13 / 32 : ℚ), (1 / 64 : ℚ), (-1 / 64 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ), (1 / 2 : ℚ)]⟩

theorem leaf7_address : sameCell (descendStage5b root7 [false, false, true, true, true, true, false, false]) leaf7 = true := by
  decide +kernel

theorem leaf7_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 leaf7 leaf7 = true := by
  decide +kernel

theorem leaf7_strictFCC (p : Chart) (hp : leaf7.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf7_check p hp gp

def leaf7Pt : Fin 8 → ℚ := ![(7075 / 8192 : ℚ), (1633 / 2048 : ℚ), (51 / 128 : ℚ), (1 / 128 : ℚ), (-3 / 128 : ℚ), (55 / 128 : ℚ), (55 / 128 : ℚ), (127 / 256 : ℚ)]

theorem leaf7_nonvacuous : ∃ p : Chart, leaf7.Mem p ∧ good p := by
  have hall : ∀ i, leaf7.lo i ≤ leaf7Pt i ∧ leaf7Pt i ≤ leaf7.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf7Pt i : ℝ), fun i => ?_,
    good_of_check leaf7Pt (0) (0) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def root8 : Cell := ⟨![(443753 / 512000 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (-1 / 32 : ℚ), (15 / 32 : ℚ), (15 / 32 : ℚ), (-63 / 128 : ℚ)],
    ![(111811 / 128000 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ)]⟩

def leaf8 : Cell := ⟨![(443753 / 512000 : ℚ), (417 / 512 : ℚ), (23 / 64 : ℚ), (0 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (31 / 64 : ℚ), (-63 / 128 : ℚ)],
    ![(111811 / 128000 : ℚ), (841 / 1024 : ℚ), (3 / 8 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (63 / 128 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ)]⟩

theorem leaf8_address : sameCell (descendStage5b root8 [true, true, true, false, true, false, true, false]) leaf8 = true := by
  decide +kernel

theorem leaf8_check : Jensen.Fix.fLeafCheck (1 : ℚ) (6 : ℚ) 2 leaf8 leaf8 = true := by
  decide +kernel

theorem leaf8_strictFCC (p : Chart) (hp : leaf8.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ leaf8_check p hp gp

def leaf8Pt : Fin 8 → ℚ := ![(890997 / 1024000 : ℚ), (1675 / 2048 : ℚ), (47 / 128 : ℚ), (1 / 128 : ℚ), (-1 / 128 : ℚ), (125 / 256 : ℚ), (63 / 128 : ℚ), (-125 / 256 : ℚ)]

theorem leaf8_nonvacuous : ∃ p : Chart, leaf8.Mem p ∧ good p := by
  have hall : ∀ i, leaf8.lo i ≤ leaf8Pt i ∧ leaf8Pt i ≤ leaf8.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf8Pt i : ℝ), fun i => ?_,
    good_of_check leaf8Pt (0) (-1) (125 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group0 : Cell := ⟨![(439 / 512 : ℚ), (417 / 512 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (-1 / 16 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-65 / 128 : ℚ)],
    ![(895 / 1024 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (-1 / 32 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]⟩

def tile0 : Cell := ⟨![(439 / 512 : ℚ), (841 / 1024 : ℚ), (23 / 64 : ℚ), (3 / 64 : ℚ), (-1 / 16 : ℚ), (-33 / 64 : ℚ), (-33 / 64 : ℚ), (-65 / 128 : ℚ)],
    ![(1773 / 2048 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (-3 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]⟩

theorem tile0_address : sameCell (descendOptical group0 [true, false, true, true, true, false]) tile0 = true := by
  decide +kernel

theorem tile0_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 tile0 tile0 = true := by
  decide +kernel

theorem tile0_strictFCC (p : Chart) (hp : tile0.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ tile0_check p hp gp

def tile0Pt : Fin 8 → ℚ := ![(3529 / 4096 : ℚ), (1689 / 2048 : ℚ), (47 / 128 : ℚ), (7 / 128 : ℚ), (-7 / 128 : ℚ), (-65 / 128 : ℚ), (-65 / 128 : ℚ), (-129 / 256 : ℚ)]

theorem tile0_nonvacuous : ∃ p : Chart, tile0.Mem p ∧ good p := by
  have hall : ∀ i, tile0.lo i ≤ tile0Pt i ∧ tile0Pt i ≤ tile0.hi i := by
    decide +kernel
  refine ⟨fun i => (tile0Pt i : ℝ), fun i => ?_,
    good_of_check tile0Pt (-1) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def group1 : Cell := ⟨![(861 / 1024 : ℚ), (841 / 1024 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (0 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(54811 / 64000 : ℚ), (53 / 64 : ℚ), (11 / 32 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def tile1 : Cell := ⟨![(861 / 1024 : ℚ), (841 / 1024 : ℚ), (5 / 16 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (-33 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(432497 / 512000 : ℚ), (53 / 64 : ℚ), (21 / 64 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem tile1_address : sameCell (descendOptical group1 [false, false, true, false]) tile1 = true := by
  decide +kernel

theorem tile1_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 tile1 tile1 = true := by
  decide +kernel

theorem tile1_strictFCC (p : Chart) (hp : tile1.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ tile1_check p hp gp

def tile1Pt : Fin 8 → ℚ := ![(862997 / 1024000 : ℚ), (1689 / 2048 : ℚ), (41 / 128 : ℚ), (3 / 128 : ℚ), (1 / 128 : ℚ), (-65 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem tile1_nonvacuous : ∃ p : Chart, tile1.Mem p ∧ good p := by
  have hall : ∀ i, tile1.lo i ≤ tile1Pt i ∧ tile1Pt i ≤ tile1.hi i := by
    decide +kernel
  refine ⟨fun i => (tile1Pt i : ℝ), fun i => ?_,
    good_of_check tile1Pt (-1) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage5bPhase.Leaves
