import BccSharp.Cover.Stage3Stage6Compose
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! # The thinnest Stage6 F entries (generated)

Generated from the Direct frontier (owner hulls, reflected into the positive offset half).
Each entry's support box is a dyadic ancestor of its target box. Per entry:
the address checks (`_support_address`, `_target_address`, kernel: the boxes
are the owner hull restricted along the recorded seeds), the fixed-point
Jensen check on the support and the target with the recorded profile
(`_check`, kernel), the route theorem (`_strictFCC`), and the acceptance of any
Stage6 `F` request with these boxes and profile by `stage6Now` (`_stage6`). -/

namespace BccSharp.Coulomb.CompactCover.Stage3Stage6.FLeaves
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.Stage3Stage6

def seedOk (hull : Cell) (seed : String) (box : Cell) : Bool :=
  match decodeSeed seed with
  | some path => sameCell (restrict hull path) box
  | none => false

def hull0 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]⟩

def support0 : Cell := ⟨![(861 / 1024 : ℚ), (205 / 256 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (1 / 32 : ℚ), (7 / 16 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(439 / 512 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (3 / 32 : ℚ), (1 / 16 : ℚ), (29 / 64 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

def target0 : Cell := ⟨![(861 / 1024 : ℚ), (827 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (3 / 64 : ℚ), (7 / 16 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)],
    ![(1739 / 2048 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (3 / 32 : ℚ), (1 / 16 : ℚ), (29 / 64 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

theorem entry0_support_address : seedOk hull0 "3ceeebc830ac9216ace5" support0 = true := by
  decide +kernel

theorem entry0_target_address : seedOk hull0 "3ceeebc830ac9216ace5930" target0 = true := by
  decide +kernel

theorem entry0_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support0 target0 = true := by
  decide +kernel

theorem entry0_strictFCC (p : Chart) (hp : target0.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ entry0_check p hp gp

theorem entry0_stage6 (q : Stage6Request) (hc : q.proposal.compare = .fcc)
    (hpr : q.proposal.profile = 0) (hs : q.proposal.source = support0)
    (ht : q.proposal.target = target0) : stage6Now q = true := by
  simp only [stage6Now, stage6Check, hc, stage6FCheck, hpr, hs, ht]
  exact entry0_check

def target0Pt : Fin 8 → ℚ := ![(3461 / 4096 : ℚ), (1661 / 2048 : ℚ), (23 / 64 : ℚ), (5 / 64 : ℚ), (7 / 128 : ℚ), (57 / 128 : ℚ), (-63 / 128 : ℚ), (-63 / 128 : ℚ)]

theorem target0_nonvacuous : ∃ p : Chart, target0.Mem p ∧ good p := by
  have hall : ∀ i, target0.lo i ≤ target0Pt i ∧ target0Pt i ≤ target0.hi i := by
    decide +kernel
  refine ⟨fun i => (target0Pt i : ℝ), fun i => ?_,
    good_of_check target0Pt (0) (-1) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def hull1 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)]⟩

def support1 : Cell := ⟨![(439 / 512 : ℚ), (827 / 1024 : ℚ), (11 / 32 : ℚ), (5 / 64 : ℚ), (-1 / 32 : ℚ), (61 / 128 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(1773 / 2048 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (3 / 32 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (63 / 128 : ℚ), (-63 / 128 : ℚ)]⟩

def target1 : Cell := ⟨![(439 / 512 : ℚ), (827 / 1024 : ℚ), (11 / 32 : ℚ), (5 / 64 : ℚ), (-1 / 32 : ℚ), (61 / 128 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(1773 / 2048 : ℚ), (417 / 512 : ℚ), (3 / 8 : ℚ), (3 / 32 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (63 / 128 : ℚ), (-63 / 128 : ℚ)]⟩

theorem entry1_support_address : seedOk hull1 "133bddeeee9bd9206ad58307bce" support1 = true := by
  decide +kernel

theorem entry1_target_address : seedOk hull1 "133bddeeee9bd9206ad58307bce" target1 = true := by
  decide +kernel

theorem entry1_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support1 target1 = true := by
  decide +kernel

theorem entry1_strictFCC (p : Chart) (hp : target1.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ entry1_check p hp gp

theorem entry1_stage6 (q : Stage6Request) (hc : q.proposal.compare = .fcc)
    (hpr : q.proposal.profile = 0) (hs : q.proposal.source = support1)
    (ht : q.proposal.target = target1) : stage6Now q = true := by
  simp only [stage6Now, stage6Check, hc, stage6FCheck, hpr, hs, ht]
  exact entry1_check

def target1Pt : Fin 8 → ℚ := ![(3529 / 4096 : ℚ), (1661 / 2048 : ℚ), (23 / 64 : ℚ), (11 / 128 : ℚ), (-3 / 128 : ℚ), (123 / 256 : ℚ), (125 / 256 : ℚ), (-127 / 256 : ℚ)]

theorem target1_nonvacuous : ∃ p : Chart, target1.Mem p ∧ good p := by
  have hall : ∀ i, target1.lo i ≤ target1Pt i ∧ target1Pt i ≤ target1.hi i := by
    decide +kernel
  refine ⟨fun i => (target1Pt i : ℝ), fun i => ?_,
    good_of_check target1Pt (0) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def hull2 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (5 / 16 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ)]⟩

def support2 : Cell := ⟨![(3529 / 4096 : ℚ), (1675 / 2048 : ℚ), (19 / 64 : ℚ), (3 / 128 : ℚ), (7 / 128 : ℚ), (125 / 256 : ℚ), (-127 / 256 : ℚ), (63 / 128 : ℚ)],
    ![(1773 / 2048 : ℚ), (841 / 1024 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (63 / 128 : ℚ), (-63 / 128 : ℚ), (127 / 256 : ℚ)]⟩

def target2 : Cell := ⟨![(3529 / 4096 : ℚ), (1675 / 2048 : ℚ), (19 / 64 : ℚ), (3 / 128 : ℚ), (7 / 128 : ℚ), (125 / 256 : ℚ), (-127 / 256 : ℚ), (63 / 128 : ℚ)],
    ![(1773 / 2048 : ℚ), (841 / 1024 : ℚ), (5 / 16 : ℚ), (1 / 32 : ℚ), (1 / 16 : ℚ), (63 / 128 : ℚ), (-63 / 128 : ℚ), (127 / 256 : ℚ)]⟩

theorem entry2_support_address : seedOk hull2 "133bccfffffbc80936bc59207ac59317bde" support2 = true := by
  decide +kernel

theorem entry2_target_address : seedOk hull2 "133bccfffffbc80936bc59207ac59317bde" target2 = true := by
  decide +kernel

theorem entry2_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 support2 target2 = true := by
  decide +kernel

theorem entry2_strictFCC (p : Chart) (hp : target2.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  Jensen.Fix.fLeafCheck_route _ _ _ _ _ entry2_check p hp gp

theorem entry2_stage6 (q : Stage6Request) (hc : q.proposal.compare = .fcc)
    (hpr : q.proposal.profile = 0) (hs : q.proposal.source = support2)
    (ht : q.proposal.target = target2) : stage6Now q = true := by
  simp only [stage6Now, stage6Check, hc, stage6FCheck, hpr, hs, ht]
  exact entry2_check

def target2Pt : Fin 8 → ℚ := ![(14133 / 16384 : ℚ), (6721 / 8192 : ℚ), (159 / 512 : ℚ), (7 / 256 : ℚ), (15 / 256 : ℚ), (251 / 512 : ℚ), (-253 / 512 : ℚ), (253 / 512 : ℚ)]

theorem target2_nonvacuous : ∃ p : Chart, target2.Mem p ∧ good p := by
  have hall : ∀ i, target2.lo i ≤ target2Pt i ∧ target2Pt i ≤ target2.hi i := by
    decide +kernel
  refine ⟨fun i => (target2Pt i : ℝ), fun i => ?_,
    good_of_check target2Pt (0) (0) (253 / 512 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage3Stage6.FLeaves
