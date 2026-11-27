import BccSharp.Cover.LeafFixRound6
import BccSharp.Cover.LeafFixDLeaves
import BccSharp.Cover.LeafFixCorner

set_option autoImplicit false

open BccSharp.Coulomb.CompactCover.LeafFix

set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! Negative controls of the fixed-point leaf checks. Generated;
the kernel decides every statement. Lowering the aggregate constant `k` by `δ` subtracts
`δ / (S · 2a_c)` from the support's minorant: a weaker minorant of the same energy. Each leaf
check accepts it while `δ` leaves half of the least corner slack and rejects it once `δ` is
twice that slack, so the checks compare at the margins they report. The support check
rejects an aggregate that differs from the witness sum by one unit (`2⁻⁹⁶`). -/

namespace BccSharp.Coulomb.CompactCover.LeafFix.Controls

def lowerAgg (agg : Agg) (δ : ℤ) : Agg := ⟨{ agg.lin with k := agg.lin.k - δ }, agg.nls⟩

/-! #### J leaf `Round6.leaf_0`: least corner slack 707856834935666753031517956331252173715525301509749145081657065143145804070912, margin 8.554813e-14 -/

theorem j_half_accepted :
    jLeafOk Round6.screen Round6.support_0 Round6.leaf_0 (lowerAgg Round6.agg_0 13765637182322145) Round6.reg_0 4096 = true := by
  decide +kernel
theorem j_double_rejected :
    jLeafOk Round6.screen Round6.support_0 Round6.leaf_0 (lowerAgg Round6.agg_0 55062548729288582) Round6.reg_0 4096 = false := by
  decide +kernel
theorem support_off_by_one_rejected :
    supportOk Round6.screen Round6.support_0 Round6.wits_0 (lowerAgg Round6.agg_0 1) = false := by
  decide +kernel

/-! #### D leaf `DLeaves.leaf_3`: least corner slack 833725449779304021396871961795446574510855090318792133863253590462519616350832, margin 4.127130e-10 -/

theorem d_half_accepted :
    dLeafOk DLeaves.screen DLeaves.support_3 DLeaves.leaf_3 (lowerAgg DLeaves.agg_3 66410063507433740296) DLeaves.reg_3 3360494244213911566807725 = true := by
  decide +kernel
theorem d_double_rejected :
    dLeafOk DLeaves.screen DLeaves.support_3 DLeaves.leaf_3 (lowerAgg DLeaves.agg_3 265640254029734961188) DLeaves.reg_3 3360494244213911566807725 = false := by
  decide +kernel

/-! #### F leaf `Corner.leaf_0`: least corner slack 130681234498512495351217772655165728463475947043, margin 5.125283e-12 -/

theorem f_half_accepted :
    fLeafOk Corner.screen Corner.support_0 Corner.leaf_0 (lowerAgg Corner.agg_0 824714535535167070) = true := by
  decide +kernel
theorem f_double_rejected :
    fLeafOk Corner.screen Corner.support_0 Corner.leaf_0 (lowerAgg Corner.agg_0 3298858142140668282) = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.LeafFix.Controls
