import BccSharp.Cover.LeafFixFarJLeaves
import BccSharp.Cover.LeafFixFarDLeaves

set_option autoImplicit false

open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.LeafFix

set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! Negative controls of the far-annulus leaf checks. Generated;
the kernel decides every statement. As in `BccSharp.Cover.LeafFixControls`, lowering the aggregate
constant `k` by `δ` subtracts `δ / (S · 2a_c)` from the support's minorant; each check accepts
the aggregate while `δ` leaves half of the least corner slack and rejects it once `δ` is twice
that slack. The far guard `annFarOk` rejects the named J leaf's box once the registration's
wrap moves by `+e₀`. On a J leaf with mixing weight `n < 4096` and corner costs above 1, the
check rejects both pure weights (`n = 4096`: `defect ≤ regCost` alone; `n = 0`: `defect ≤ 1`
alone), so the mixture is what closes it. -/

namespace BccSharp.Coulomb.CompactCover.LeafFix.FarControls

def lowerAgg (agg : Agg) (δ : ℤ) : Agg := ⟨{ agg.lin with k := agg.lin.k - δ }, agg.nls⟩

/-! #### J leaf `FarJLeaves.leaf_0` (`jointDeficit:666291-000736:3:fc50`): least corner slack 69847159281432336754553447895306884832241312197370239063935651073055907388850176, margin 8.441388e-12 -/

theorem j_far_half_accepted :
    jLeafFarOk FarJLeaves.screen FarJLeaves.support_0 FarJLeaves.leaf_0 (lowerAgg FarJLeaves.agg_0 1358312310386106487) FarJLeaves.reg_0 4096 = true := by
  decide +kernel
theorem j_far_double_rejected :
    jLeafFarOk FarJLeaves.screen FarJLeaves.support_0 FarJLeaves.leaf_0 (lowerAgg FarJLeaves.agg_0 5433249241544425951) FarJLeaves.reg_0 4096 = false := by
  decide +kernel
theorem far_moved_wrap_rejected :
    Cutoff.annFarOk FarJLeaves.reg_0.N (fun j => FarJLeaves.reg_0.w j + if j = 0 then (1 : ℚ) else 0) FarJLeaves.leaf_0 = false := by
  decide +kernel

/-! #### D leaf `FarDLeaves.leaf_6` (`cornerRule:704559-074880:337`): least corner slack 24958351960050721854763431144920920317361781214359238132037053398765074764856944864, margin 1.235495e-05 -/

theorem d_far_half_accepted :
    dLeafFarOk FarDLeaves.screen FarDLeaves.support_6 FarDLeaves.leaf_6 (lowerAgg FarDLeaves.agg_6 1988047431137679534226573) FarDLeaves.reg_6 43531584113809708839541005082 = true := by
  decide +kernel
theorem d_far_double_rejected :
    dLeafFarOk FarDLeaves.screen FarDLeaves.support_6 FarDLeaves.leaf_6 (lowerAgg FarDLeaves.agg_6 7952189724550718136906296) FarDLeaves.reg_6 43531584113809708839541005082 = false := by
  decide +kernel

/-! #### Mixed J leaf `FarJLeaves.leaf_7` (`continuationR1:705723-0000016:12:048257e8`): recorded weight 7, corner costs up to 1.075 -/

theorem j_mixed_regcost_alone_rejected :
    jLeafFarOk FarJLeaves.screen FarJLeaves.support_7 FarJLeaves.leaf_7 FarJLeaves.agg_7 FarJLeaves.reg_7 4096 = false := by
  decide +kernel
theorem j_mixed_one_alone_rejected :
    jLeafFarOk FarJLeaves.screen FarJLeaves.support_7 FarJLeaves.leaf_7 FarJLeaves.agg_7 FarJLeaves.reg_7 0 = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.LeafFix.FarControls
