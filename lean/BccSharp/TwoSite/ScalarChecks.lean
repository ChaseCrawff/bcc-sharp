import BccSharp.TwoSite.Interface

set_option autoImplicit false

/-! Final arithmetic gates. Their arguments are proposals. The soundness
lemmas consume proved memberships and comparisons tied to the same q. -/

noncomputable section
namespace BccSharp.Coulomb

structure StrictBounds where
  anchorEnergyLower : ℚ
  opticalGainLower : ℚ
  fccUpper : ℚ
  bccUpper : ℚ
  gapUpper : ℚ
  defectUpper : ℚ
  deriving Repr

def StrictBounds.fccCheck (b : StrictBounds) : Bool :=
  decide (b.anchorEnergyLower + b.opticalGainLower > b.fccUpper)

def StrictBounds.deficitCheck (b : StrictBounds) : Bool :=
  decide (0 ≤ b.gapUpper ∧ 0 ≤ b.defectUpper ∧
    b.anchorEnergyLower + b.opticalGainLower - b.bccUpper - b.gapUpper * b.defectUpper > 0)

theorem StrictBounds.fccSound (b : StrictBounds) (q anchor : TwoSite)
    (hCheck : b.fccCheck = true)
    (hAnchor : (b.anchorEnergyLower : ℝ) ≤ energy anchor)
    (hGain : (b.opticalGainLower : ℝ) ≤ energy q - energy anchor)
    (hFcc : energy fcc ≤ (b.fccUpper : ℝ)) : LeafProof q := by
  have hRat : b.fccUpper < b.anchorEnergyLower + b.opticalGainLower := of_decide_eq_true hCheck
  have hReal : (b.fccUpper : ℝ) < (b.anchorEnergyLower : ℝ) + (b.opticalGainLower : ℝ) := by
    exact_mod_cast hRat
  exact .strictFCC (by linarith)

theorem StrictBounds.deficitSound (b : StrictBounds) (q anchor : TwoSite)
    (hCheck : b.deficitCheck = true)
    (hAnchor : (b.anchorEnergyLower : ℝ) ≤ energy anchor)
    (hGain : (b.opticalGainLower : ℝ) ≤ energy q - energy anchor)
    (hBcc : energy bcc ≤ (b.bccUpper : ℝ))
    (hGap : gap ≤ (b.gapUpper : ℝ)) (hDefect : defect q ≤ (b.defectUpper : ℝ))
    (hDefectNonneg : 0 ≤ defect q) : LeafProof q := by
  have hRat : 0 ≤ b.gapUpper ∧ 0 ≤ b.defectUpper ∧
      0 < b.anchorEnergyLower + b.opticalGainLower - b.bccUpper - b.gapUpper * b.defectUpper :=
    of_decide_eq_true hCheck
  have hGapNonneg : (0 : ℝ) ≤ (b.gapUpper : ℝ) := by exact_mod_cast hRat.1
  have hReal : (0 : ℝ) < (b.anchorEnergyLower : ℝ) + (b.opticalGainLower : ℝ) -
      (b.bccUpper : ℝ) - (b.gapUpper : ℝ) * (b.defectUpper : ℝ) := by
    exact_mod_cast hRat.2.2
  have hPenalty := le_trans (mul_le_mul_of_nonneg_right hGap hDefectNonneg)
    (mul_le_mul_of_nonneg_left hDefect hGapNonneg)
  exact .strictDeficit (by unfold deficit; linarith)

def anchorSlackCheck (slackLower netOpticalLower : ℚ) : Bool :=
  decide (0 < slackLower + netOpticalLower)

theorem anchorSlackSound (q anchor : TwoSite) (slackLower netOpticalLower : ℚ)
    (hCheck : anchorSlackCheck slackLower netOpticalLower = true)
    (hSlack : (slackLower : ℝ) ≤ deficit anchor)
    (hNet : (netOpticalLower : ℝ) ≤ deficit q - deficit anchor) : LeafProof q := by
  have hRat : 0 < slackLower + netOpticalLower := of_decide_eq_true hCheck
  have hReal : (0 : ℝ) < (slackLower : ℝ) + (netOpticalLower : ℝ) := by exact_mod_cast hRat
  exact .strictDeficit (by linarith)

def relativeCheck (uniformMargin curvature : ℚ) : Bool :=
  decide (0 ≤ uniformMargin ∧ 0 < curvature)

theorem relativeSound (q : TwoSite) (f₀ : Vec) (n : IntVec) (uniformMargin curvature : ℚ)
    (hCheck : relativeCheck uniformMargin curvature = true) (half : HalfClass f₀)
    (hAnchor : 0 ≤ deficit (⟨q.basis, f₀⟩ : TwoSite))
    (hGain : deficit (⟨q.basis, f₀⟩ : TwoSite) + (uniformMargin : ℝ) +
      (curvature : ℝ) * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤ deficit q)
    (hEquality : deficit (⟨q.basis, f₀⟩ : TwoSite) = 0 →
      sq (q.basis.mulVec (q.offset - f₀ - castVec n)) = 0 → IsBCC q ∨ IsFCC q) : LeafProof q := by
  have hRat : 0 ≤ uniformMargin ∧ 0 < curvature := of_decide_eq_true hCheck
  have hMargin : (0 : ℝ) ≤ (uniformMargin : ℝ) := by exact_mod_cast hRat.1
  have hCurv : (0 : ℝ) < (curvature : ℝ) := by exact_mod_cast hRat.2
  exact .optical f₀ n curvature half hCurv hAnchor (by linarith) hEquality

end BccSharp.Coulomb
