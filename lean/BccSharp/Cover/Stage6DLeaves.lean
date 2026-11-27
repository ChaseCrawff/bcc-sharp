import BccSharp.Cover.Stage6Deficit
import BccSharp.Cover.Stage6FLeaves
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! # The thinnest Stage6 `D` entries, and entries on Stage5b fragments (generated)

Generated, the Stage5b
reconstruction of the held atoms after stage 5 (with the Stage5b replacement atoms) and
the Direct frontier. The entries are the thinnest `D` entry of each of the three owners with
the smallest recorded `D` margins, and the thinnest `D` and `F` entries on fragments of the
whole receipt (overall, and among boxes that pass the `e₂` test). Each `D` entry has:
* the address checks of its dyadic boxes (`_support_address`, `_target_address`);
* a registration (`dregN`: `B` from the owner's catalogue, `N = B⁻¹`, the half shift
  and wrap behind the cap, a rational rotation) and an integer cap `capN`
  (`defect ≤ capN/S` on the target box, `entryN_cap`, kernel);
* the Jensen check on the support box against `e_BCC⁺ + g⁺·capN/S` at the corners of
  the target box (`entryN_energy`, kernel);
* `0 < deficit` at every good point of the target box (`entryN_deficit`);
* the acceptance of every Stage6 `D` request with these boxes and profile, for every hint
  function giving it this registration and cap (`entryN_stage6`).

An `F` entry on a fragment has the box-built `F` check (`entryN_check`), so the hybrid `F`
check accepts it for every hint function (`entryN_stage6`). A fragment box is a Stage5b
replacement atom; its binding to the corpus is geometry for the data path. Replacement atoms are
numbered from 1 (fragment 0 is the dyadic seed). A margin is the owner's recorded margin
where it equals it, and otherwise a recomputation. -/

namespace BccSharp.Coulomb.CompactCover.Stage3Stage6.DLeaves
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.Stage3Stage6

def support0 : Cell := ⟨![(1773 / 2048 : ℚ), (1675 / 2048 : ℚ), (21 / 64 : ℚ), (7 / 128 : ℚ), (0 : ℚ), (63 / 128 : ℚ), (-61 / 128 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (1 / 128 : ℚ), (1 / 2 : ℚ), (-15 / 32 : ℚ), (-63 / 128 : ℚ)]⟩

def target0 : Cell := ⟨![(1773 / 2048 : ℚ), (1675 / 2048 : ℚ), (21 / 64 : ℚ), (7 / 128 : ℚ), (0 : ℚ), (63 / 128 : ℚ), (-61 / 128 : ℚ), (-1 / 2 : ℚ)],
    ![(3563 / 4096 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (1 / 128 : ℚ), (1 / 2 : ℚ), (-15 / 32 : ℚ), (-63 / 128 : ℚ)]⟩

def hull0 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]⟩

theorem entry0_support_address : FLeaves.seedOk hull0 "3ceeebc8318307bc48217bde58307bde" support0 = true := by
  decide +kernel

theorem entry0_target_address : FLeaves.seedOk hull0 "3ceeebc8318307bc48217bde58307bde" target0 = true := by
  decide +kernel

def dreg0 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(331220802925303044 / 576460752417168629 : ℚ), (325669087867515187 / 576460752417168629 : ℚ), (341378710517258856 / 576460752417168629 : ℚ)], ![(-471774744260526099 / 576460752417168629 : ℚ), (233323439069004804 / 576460752417168629 : ℚ), (235150510389188368 / 576460752417168629 : ℚ)], ![(-5326299353298352 / 576460752417168629 : ℚ), (-414495858924936984 / 576460752417168629 : ℚ), (400589331543721941 / 576460752417168629 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![1, 0, 0]

def cap0 : ℤ := 21637867231965114464018704886

theorem entry0_cap : capOk dreg0 target0 cap0 = true := by
  decide +kernel

theorem entry0_energy : Jensen.Fix.tLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support0 target0
    (dThreshold cap0) = true := by
  decide +kernel

theorem entry0_deficit (p : Chart) (hp : target0.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  deficit_pos_of_checks dreg0 cap0 (by decide) entry0_cap entry0_energy p hp gp

theorem entry0_stage6 (hint : Stage6Request → Option SupportHint)
    (dhint : Stage6Request → Option DHint) (q : Stage6Request)
    (hc : q.proposal.compare = .deficit) (hpr : q.proposal.profile = 0)
    (hs : q.proposal.source = support0) (ht : q.proposal.target = target0)
    (hd : dhint q = some ⟨dreg0, cap0⟩) : stage6FullCheck hint dhint q = true := by
  simp only [stage6FullCheck, stage6HybridCheck, hc, stage6DEval, hd, hpr, hs, ht, entry0_cap,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by decide, entry0_energy⟩

def target0Pt : Fin 8 → ℚ := ![(7109 / 8192 : ℚ), (3357 / 4096 : ℚ), (43 / 128 : ℚ), (15 / 256 : ℚ), (1 / 256 : ℚ), (127 / 256 : ℚ), (-121 / 256 : ℚ), (-127 / 256 : ℚ)]

theorem target0_nonvacuous : ∃ p : Chart, target0.Mem p ∧ good p := by
  have hall : ∀ i, target0.lo i ≤ target0Pt i ∧ target0Pt i ≤ target0.hi i := by
    decide +kernel
  refine ⟨fun i => (target0Pt i : ℝ), fun i => ?_,
    good_of_check target0Pt (0) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def support1 : Cell := ⟨![(439 / 512 : ℚ), (1675 / 2048 : ℚ), (21 / 64 : ℚ), (3 / 64 : ℚ), (5 / 128 : ℚ), (15 / 32 : ℚ), (-63 / 128 : ℚ), (63 / 128 : ℚ)],
    ![(1773 / 2048 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (3 / 64 : ℚ), (61 / 128 : ℚ), (-31 / 64 : ℚ), (1 / 2 : ℚ)]⟩

def target1 : Cell := ⟨![(3529 / 4096 : ℚ), (1675 / 2048 : ℚ), (21 / 64 : ℚ), (3 / 64 : ℚ), (5 / 128 : ℚ), (15 / 32 : ℚ), (-63 / 128 : ℚ), (63 / 128 : ℚ)],
    ![(1773 / 2048 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (3 / 64 : ℚ), (61 / 128 : ℚ), (-31 / 64 : ℚ), (1 / 2 : ℚ)]⟩

def hull1 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ)]⟩

theorem entry1_support_address : FLeaves.seedOk hull1 "3cffffbc8319b307cac48207adf593" support1 = true := by
  decide +kernel

theorem entry1_target_address : FLeaves.seedOk hull1 "3cffffbc8319b307cac48207adf5931" target1 = true := by
  decide +kernel

def dreg1 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(663467282565106941 / 1152921504083116901 : ℚ), (650916071058402796 / 1152921504083116901 : ℚ), (682163783838486552 / 1152921504083116901 : ℚ)], ![(-942888726811299244 / 1152921504083116901 : ℚ), (457938539783143677 / 1152921504083116901 : ℚ), (480084510488232456 / 1152921504083116901 : ℚ)], ![(91624866638472 / 1152921504083116901 : ℚ), (-834163387350734184 / 1152921504083116901 : ℚ), (795863951555609381 / 1152921504083116901 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![1, 0, 1]

def cap1 : ℤ := 22559997217984105514260902301

theorem entry1_cap : capOk dreg1 target1 cap1 = true := by
  decide +kernel

theorem entry1_energy : Jensen.Fix.tLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support1 target1
    (dThreshold cap1) = true := by
  decide +kernel

theorem entry1_deficit (p : Chart) (hp : target1.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  deficit_pos_of_checks dreg1 cap1 (by decide) entry1_cap entry1_energy p hp gp

theorem entry1_stage6 (hint : Stage6Request → Option SupportHint)
    (dhint : Stage6Request → Option DHint) (q : Stage6Request)
    (hc : q.proposal.compare = .deficit) (hpr : q.proposal.profile = 0)
    (hs : q.proposal.source = support1) (ht : q.proposal.target = target1)
    (hd : dhint q = some ⟨dreg1, cap1⟩) : stage6FullCheck hint dhint q = true := by
  simp only [stage6FullCheck, stage6HybridCheck, hc, stage6DEval, hd, hpr, hs, ht, entry1_cap,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by decide, entry1_energy⟩

def target1Pt : Fin 8 → ℚ := ![(7075 / 8192 : ℚ), (3357 / 4096 : ℚ), (43 / 128 : ℚ), (7 / 128 : ℚ), (11 / 256 : ℚ), (121 / 256 : ℚ), (-125 / 256 : ℚ), (127 / 256 : ℚ)]

theorem target1_nonvacuous : ∃ p : Chart, target1.Mem p ∧ good p := by
  have hall : ∀ i, target1.lo i ≤ target1Pt i ∧ target1Pt i ≤ target1.hi i := by
    decide +kernel
  refine ⟨fun i => (target1Pt i : ℝ), fun i => ?_,
    good_of_check target1Pt (0) (0) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def support2 : Cell := ⟨![(3495 / 4096 : ℚ), (1661 / 2048 : ℚ), (23 / 64 : ℚ), (0 : ℚ), (-1 / 128 : ℚ), (15 / 32 : ℚ), (29 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(439 / 512 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (1 / 128 : ℚ), (0 : ℚ), (61 / 128 : ℚ), (59 / 128 : ℚ), (-63 / 128 : ℚ)]⟩

def target2 : Cell := ⟨![(3495 / 4096 : ℚ), (1661 / 2048 : ℚ), (23 / 64 : ℚ), (0 : ℚ), (-1 / 128 : ℚ), (15 / 32 : ℚ), (29 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(439 / 512 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (1 / 128 : ℚ), (0 : ℚ), (61 / 128 : ℚ), (59 / 128 : ℚ), (-63 / 128 : ℚ)]⟩

def hull2 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (5 / 16 : ℚ), (0 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)]⟩

theorem entry2_support_address : FLeaves.seedOk hull2 "03bddeeeee319cb92659316ad59316ac" support2 = true := by
  decide +kernel

theorem entry2_target_address : FLeaves.seedOk hull2 "03bddeeeee319cb92659316ad59316ac" target2 = true := by
  decide +kernel

def dreg2 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(32238223460501088 / 57646075221547121 : ℚ), (168665747599277907 / 288230376107735605 : ℚ), (169251407677316924 / 288230376107735605 : ℚ)], ![(-47788528187480776 / 57646075221547121 : ℚ), (114436089074123076 / 288230376107735605 : ℚ), (113523326107390707 / 288230376107735605 : ℚ)], ![(-341493254511 / 128387695370929 : ℚ), (-90777932864512 / 128387695370929 : ℚ), (90789044547576 / 128387695370929 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![1, 1, 0]

def cap2 : ℤ := 65860898491979879630020207982

theorem entry2_cap : capOk dreg2 target2 cap2 = true := by
  decide +kernel

theorem entry2_energy : Jensen.Fix.tLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support2 target2
    (dThreshold cap2) = true := by
  decide +kernel

theorem entry2_deficit (p : Chart) (hp : target2.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  deficit_pos_of_checks dreg2 cap2 (by decide) entry2_cap entry2_energy p hp gp

theorem entry2_stage6 (hint : Stage6Request → Option SupportHint)
    (dhint : Stage6Request → Option DHint) (q : Stage6Request)
    (hc : q.proposal.compare = .deficit) (hpr : q.proposal.profile = 0)
    (hs : q.proposal.source = support2) (ht : q.proposal.target = target2)
    (hd : dhint q = some ⟨dreg2, cap2⟩) : stage6FullCheck hint dhint q = true := by
  simp only [stage6FullCheck, stage6HybridCheck, hc, stage6DEval, hd, hpr, hs, ht, entry2_cap,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by decide, entry2_energy⟩

def target2Pt : Fin 8 → ℚ := ![(7007 / 8192 : ℚ), (3329 / 4096 : ℚ), (47 / 128 : ℚ), (1 / 256 : ℚ), (-1 / 256 : ℚ), (121 / 256 : ℚ), (117 / 256 : ℚ), (-127 / 256 : ℚ)]

theorem target2_nonvacuous : ∃ p : Chart, target2.Mem p ∧ good p := by
  have hall : ∀ i, target2.lo i ≤ target2Pt i ∧ target2Pt i ≤ target2.hi i := by
    decide +kernel
  refine ⟨fun i => (target2Pt i : ℝ), fun i => ?_,
    good_of_check target2Pt (0) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def support3 : Cell := ⟨![(3549173 / 4096000 : ℚ), (1683899 / 2048000 : ℚ), (39 / 128 : ℚ), (3 / 128 : ℚ), (1 / 64 : ℚ), (31 / 64 : ℚ), (-31 / 64 : ℚ), (63 / 128 : ℚ)],
    ![(7098471 / 8192000 : ℚ), (1689 / 2048 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (5 / 256 : ℚ), (63 / 128 : ℚ), (-61 / 128 : ℚ), (1 / 2 : ℚ)]⟩

def target3 : Cell := ⟨![(3549173 / 4096000 : ℚ), (1683899 / 2048000 : ℚ), (39 / 128 : ℚ), (3 / 128 : ℚ), (1 / 64 : ℚ), (31 / 64 : ℚ), (-31 / 64 : ℚ), (63 / 128 : ℚ)],
    ![(7098471 / 8192000 : ℚ), (1689 / 2048 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (5 / 256 : ℚ), (63 / 128 : ℚ), (-61 / 128 : ℚ), (1 / 2 : ℚ)]⟩

def dreg3 : RegData where
  B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
  N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
  U := ![![(67978929054965400 / 115292150375649181 : ℚ), (65052541353392880 / 115292150375649181 : ℚ), (66628162260761731 / 115292150375649181 : ℚ)], ![(-465594534721174096 / 576460751878245905 : ℚ), (237978727936766703 / 576460751878245905 : ℚ), (48536523461576592 / 115292150375649181 : ℚ)], ![(-598169963741553 / 576460751878245905 : ℚ), (-412161734143598896 / 576460751878245905 : ℚ), (80605048367076456 / 115292150375649181 : ℚ)]]
  f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
  wrap := ![1, 0, 1]

def cap3 : ℤ := 15949068135482264087732033103

theorem entry3_cap : capOk dreg3 target3 cap3 = true := by
  decide +kernel

theorem entry3_energy : Jensen.Fix.tLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support3 target3
    (dThreshold cap3) = true := by
  decide +kernel

theorem entry3_deficit (p : Chart) (hp : target3.Mem p) (gp : good p) :
    0 < deficit (chartPoint p) :=
  deficit_pos_of_checks dreg3 cap3 (by decide) entry3_cap entry3_energy p hp gp

theorem entry3_stage6 (hint : Stage6Request → Option SupportHint)
    (dhint : Stage6Request → Option DHint) (q : Stage6Request)
    (hc : q.proposal.compare = .deficit) (hpr : q.proposal.profile = 0)
    (hs : q.proposal.source = support3) (ht : q.proposal.target = target3)
    (hd : dhint q = some ⟨dreg3, cap3⟩) : stage6FullCheck hint dhint q = true := by
  simp only [stage6FullCheck, stage6HybridCheck, hc, stage6DEval, hd, hpr, hs, ht, entry3_cap,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by decide, entry3_energy⟩

def target3Pt : Fin 8 → ℚ := ![(14196817 / 16384000 : ℚ), (3372899 / 4096000 : ℚ), (319 / 1024 : ℚ), (7 / 256 : ℚ), (9 / 512 : ℚ), (125 / 256 : ℚ), (-123 / 256 : ℚ), (127 / 256 : ℚ)]

theorem target3_nonvacuous : ∃ p : Chart, target3.Mem p ∧ good p := by
  have hall : ∀ i, target3.lo i ≤ target3Pt i ∧ target3Pt i ≤ target3.hi i := by
    decide +kernel
  refine ⟨fun i => (target3Pt i : ℝ), fun i => ?_,
    good_of_check target3Pt (0) (0) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def support4 : Cell := ⟨![(221811 / 256000 : ℚ), (1663363 / 2048000 : ℚ), (353869 / 1024000 : ℚ), (62381 / 1024000 : ℚ), (1 / 16 : ℚ), (127 / 256 : ℚ), (-1 / 2 : ℚ), (-127 / 256 : ℚ)],
    ![(7444843725 / 8589934592 : ℚ), (872261289 / 1073741824 : ℚ), (354381 / 1024000 : ℚ), (1 / 16 : ℚ), (9 / 128 : ℚ), (1 / 2 : ℚ), (-127 / 256 : ℚ), (-63 / 128 : ℚ)]⟩

def target4 : Cell := ⟨![(221811 / 256000 : ℚ), (1663363 / 2048000 : ℚ), (353869 / 1024000 : ℚ), (62381 / 1024000 : ℚ), (1 / 16 : ℚ), (127 / 256 : ℚ), (-1 / 2 : ℚ), (-127 / 256 : ℚ)],
    ![(7444843725 / 8589934592 : ℚ), (872261289 / 1073741824 : ℚ), (354381 / 1024000 : ℚ), (1 / 16 : ℚ), (9 / 128 : ℚ), (1 / 2 : ℚ), (-127 / 256 : ℚ), (-63 / 128 : ℚ)]⟩

theorem entry4_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support4 target4 = true := by
  decide +kernel

theorem entry4_stage6 (hint : Stage6Request → Option SupportHint)
    (dhint : Stage6Request → Option DHint) (q : Stage6Request)
    (hc : q.proposal.compare = .fcc) (hpr : q.proposal.profile = 0)
    (hs : q.proposal.source = support4) (ht : q.proposal.target = target4) :
    stage6FullCheck hint dhint q = true := by
  have h : stage6FCheck q = true := by
    simp only [stage6FCheck, hpr, hs, ht]
    exact entry4_check
  simp only [stage6FullCheck, stage6HybridCheck, hc, stage6FHybrid, h, Bool.or_true]

theorem target4_not_reduced (p : Chart) (hp : target4.Mem p) :
    ¬ reductionInequalities p :=
  Stage5bPhase.notReducedE2_sound target4 (by decide +kernel) p hp

def support5 : Cell := ⟨![(7377734861 / 8589934592 : ℚ), (872261289 / 1073741824 : ℚ), (90844953 / 268435456 : ℚ), (17 / 256 : ℚ), (9 / 128 : ℚ), (63 / 128 : ℚ), (63 / 128 : ℚ), (-127 / 256 : ℚ)],
    ![(7411289293 / 8589934592 : ℚ), (417 / 512 : ℚ), (91893529 / 268435456 : ℚ), (9 / 128 : ℚ), (5 / 64 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

def target5 : Cell := ⟨![(7377734861 / 8589934592 : ℚ), (872261289 / 1073741824 : ℚ), (90844953 / 268435456 : ℚ), (17 / 256 : ℚ), (9 / 128 : ℚ), (63 / 128 : ℚ), (63 / 128 : ℚ), (-127 / 256 : ℚ)],
    ![(7411289293 / 8589934592 : ℚ), (417 / 512 : ℚ), (91893529 / 268435456 : ℚ), (9 / 128 : ℚ), (5 / 64 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem entry5_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support5 target5 = true := by
  decide +kernel

theorem entry5_stage6 (hint : Stage6Request → Option SupportHint)
    (dhint : Stage6Request → Option DHint) (q : Stage6Request)
    (hc : q.proposal.compare = .fcc) (hpr : q.proposal.profile = 0)
    (hs : q.proposal.source = support5) (ht : q.proposal.target = target5) :
    stage6FullCheck hint dhint q = true := by
  have h : stage6FCheck q = true := by
    simp only [stage6FCheck, hpr, hs, ht]
    exact entry5_check
  simp only [stage6FullCheck, stage6HybridCheck, hc, stage6FHybrid, h, Bool.or_true]

def target5Pt : Fin 8 → ℚ := ![(7394512077 / 8589934592 : ℚ), (1746773673 / 2147483648 : ℚ), (91369241 / 268435456 : ℚ), (35 / 512 : ℚ), (19 / 256 : ℚ), (127 / 256 : ℚ), (127 / 256 : ℚ), (-253 / 512 : ℚ)]

theorem target5_nonvacuous : ∃ p : Chart, target5.Mem p ∧ good p := by
  have hall : ∀ i, target5.lo i ≤ target5Pt i ∧ target5Pt i ≤ target5.hi i := by
    decide +kernel
  refine ⟨fun i => (target5Pt i : ℝ), fun i => ?_,
    good_of_check target5Pt (0) (-1) (253 / 512 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage3Stage6.DLeaves
