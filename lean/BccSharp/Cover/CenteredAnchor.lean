import BccSharp.Lattice.StrainAtlas

set_option autoImplicit false

/-! # A quantitative lower bound on the one-site deficit near BCC

The strain-atlas E2 tangent leaves (`StrainTangent.zLeafCheck .bcc true`) prove
`0 < oneSiteDeficit` on a box of whitened strain coordinates from the series
inequality `HbccUpper < a − Gs(s)` at every point of the box. This module keeps
a margin `m` in that inequality:

* `e2_deficit_lower`: for `det R = 1` and `0 ≤ m`, if
  `HbccUpper + gapFactorUpper·Q + m ≤ positiveSeries R` and the defect is at
  most `Q`, then `m / (2·scaleHi) ≤ oneSiteDeficit`;
* `zLeafCheckQ z b m`: `zLeafCheck .bcc true` with target `targetZ true + m`,
  and `0 ≤ m`;
* `zLeafCheckQ_sound`: on every strain point of `b` and every `A` with
  `det A = 1` and `gram A = reconstructedMetric .bcc w`,
  `m / 2⁶⁴ / (2·scaleHi) ≤ oneSiteDeficit (strainBasis .bcc A)`.

The aggregate `z` is any certified one; `StrainAtlas.AtlasData.agg` with
`AtlasData.agg_certified` gives one for every box. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.StrainTangent
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentE1

/-- The deficit with a margin in the series inequality of the E2 leaves. -/
theorem e2_deficit_lower (R : Mat) (hR : R.det = 1) (Q m : ℝ) (hm : 0 ≤ m)
    (upper : oneSiteDefect (Constants.fccLength⁻¹ • R) ≤ Q)
    (hc : (HbccUpper : ℝ) + (gapFactorUpper : ℝ) * Q + m ≤ positiveSeries R) :
    m / (2 * (scaleHi : ℝ)) ≤ oneSiteDeficit (Constants.fccLength⁻¹ • R) := by
  have hD : 0 ≤ oneSiteDefect (Constants.fccLength⁻¹ • R) := (cappedDefect_range _).1
  have hgp : 0 ≤ (gapFactorUpper : ℝ) :=
    (mul_nonneg (mul_pos two_pos bravaisScale_positive).le Constants.reference_gap_checked.2.le).trans
      gapFactorUpper_sound
  have hQ := mul_le_mul gapFactorUpper_sound upper hD hgp
  have hbs := bravaisScale_positive
  have h2 : (0 : ℝ) < 2 * bravaisScale := by positivity
  have hEnergy : (energy bcc + gap * oneSiteDefect (Constants.fccLength⁻¹ • R)) * (2 * bravaisScale) + m ≤
      positiveSeries R - 3 := by
    nlinarith [HbccUpper_sound, hQ, hc]
  have hE : oneSiteEnergy (Constants.fccLength⁻¹ • R) = (positiveSeries R - 3) / (2 * bravaisScale) :=
    oneSiteEnergy_from_normalized R hR
  have hdef : m / (2 * bravaisScale) ≤ oneSiteDeficit (Constants.fccLength⁻¹ • R) := by
    unfold oneSiteDeficit
    rw [hE]
    rw [div_le_iff₀ h2]
    have e : ((positiveSeries R - 3) / (2 * bravaisScale) - energy bcc -
        gap * oneSiteDefect (Constants.fccLength⁻¹ • R)) * (2 * bravaisScale) =
        positiveSeries R - 3 - (energy bcc + gap * oneSiteDefect (Constants.fccLength⁻¹ • R)) * (2 * bravaisScale) := by
      field_simp
      ring
    rw [e]
    linarith
  have hs : bravaisScale ≤ (scaleHi : ℝ) := bravaisScale_between.2
  have hmono : m / (2 * (scaleHi : ℝ)) ≤ m / (2 * bravaisScale) :=
    div_le_div_of_nonneg_left hm h2 (by linarith)
  linarith

/-- The E2 strain leaf check with a margin `m` (in units of `2⁻⁶⁴`). -/
def zLeafCheckQ (z : ZAgg) (b : Rectangle) (m : ℤ) : Bool :=
  let zb := zBox .bcc b
  let P := framePZ .bcc z
  let D := frameDZ .bcc z
  let γI := gammaZ true
  let bd := zBoxData (c1Z .bcc) (c2Z .bcc) γI P D zb
  let corr := corrZ (c1Z .bcc) (c2Z .bcc) γI P D zb bd
  ((decide (0 ≤ m) && lamOKZ bd.d bd.lam) && spectralCheck (cBallsZ bd) (automaticUpperPad (cBallsZ bd))) &&
    allCorners fun c => match cornerUpperZ (c1Z .bcc) (c2Z .bcc) γI.hi P D zb c with
      | some u => decide ((targetZ true + m + u + corr) * pw 32 < z.a)
      | none => false

theorem zLeafCheckQ_sound (z : ZAgg) (hz : Certified z.toAgg) (b : Rectangle) (m : ℤ)
    (ok : zLeafCheckQ z b m = true) (w : Point) (hw : b.Mem w) (A : Mat) (hA : A.det = 1)
    (hGram : gram A = reconstructedMetric .bcc w) :
    (m : ℝ) / 2 ^ 64 / (2 * (scaleHi : ℝ)) ≤ oneSiteDeficit (strainBasis .bcc A) := by
  unfold zLeafCheckQ at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨⟨⟨hm, hlam⟩, hspec⟩, hcorners⟩ := ok
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast of_decide_eq_true hm
  set zb := zBox .bcc b with hzb
  set γ := modeGamma true with hγ
  set p := sOf .bcc w with hpdef
  set bd := zBoxData (c1Z .bcc) (c2Z .bcc) (gammaZ true) (framePZ .bcc z) (frameDZ .bcc z) zb with hbd
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  have hpz : zb.Mem p := zBox_mem .bcc b w hw
  have hp : (zbRect zb).Mem p := zbRect_mem.mpr hpz
  let F := fun i => F2Z (c1Z .bcc) (c2Z .bcc) (gammaZ true) (framePZ .bcc z) (frameDZ .bcc z) bd i
  let M : Fin 5 → ℝ := fun i => ((max 0 (-(F i).lo) : ℤ) : ℝ) / (9 * 2 ^ 64)
  have hM (i : Fin 5) : 0 ≤ M i := by
    simp only [M]
    have : (0 : ℝ) ≤ ((max 0 (-(F i).lo) : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    positivity
  obtain ⟨c, hc⟩ := box_bound (zbRect zb) (Gs .bcc z.toAgg γ) (F1 .bcc z.toAgg γ) (F2 .bcc z.toAgg γ) M hM
    (fun i q hq => (lineDerivs .bcc z.toAgg γ i q
      (F2Z_mem .bcc z true zb hlam i q (zbRect_mem.mp hq)).1).1)
    (fun i q hq => (lineDerivs .bcc z.toAgg γ i q
      (F2Z_mem .bcc z true zb hlam i q (zbRect_mem.mp hq)).1).2)
    (fun i q hq => by
      have h := (F2Z_mem .bcc z true zb hlam i q (zbRect_mem.mp hq)).2.1
      have hmax : (-((max 0 (-(F i).lo) : ℤ) : ℝ)) ≤ ((F i).lo : ℝ) := by
        have := le_max_right (0 : ℤ) (-(F i).lo)
        have : (-(F i).lo : ℝ) ≤ ((max 0 (-(F i).lo) : ℤ) : ℝ) := by exact_mod_cast this
        linarith
      simp only [M]
      rw [neg_div', div_le_iff₀ (by positivity)]
      have : ((F i).lo : ℝ) / 2 ^ 64 ≤ 9 * F2 .bcc z.toAgg γ i q := h
      rw [div_le_iff₀ S] at this
      nlinarith)
    p hp
  have hcorner := allCorners_sound _ hcorners c
  cases hcu : cornerUpperZ (c1Z .bcc) (c2Z .bcc) (gammaZ true).hi (framePZ .bcc z) (frameDZ .bcc z) zb c with
  | none => simp [hcu] at hcorner
  | some u =>
    simp only [hcu] at hcorner
    have ht : (targetZ true + m + u + corrZ (c1Z .bcc) (c2Z .bcc) (gammaZ true) (framePZ .bcc z)
        (frameDZ .bcc z) zb bd) * 2 ^ 32 < z.a := by
      have := of_decide_eq_true hcorner
      rwa [pw_eq] at this
    have hG := cornerUpperZ_sound .bcc z true zb c u hcu
    rw [← zbRect_corner] at hG
    have hcorr : ∑ i, M i * (((zbRect zb).hi i : ℝ) - (zbRect zb).lo i) ^ 2 / 8 ≤
        ((corrZ (c1Z .bcc) (c2Z .bcc) (gammaZ true) (framePZ .bcc z) (frameDZ .bcc z) zb bd : ℤ) : ℝ) /
          2 ^ 64 := by
      have term (i : Fin 5) : M i * (((zbRect zb).hi i : ℝ) - (zbRect zb).lo i) ^ 2 / 8 ≤
          ((corrTermZ (F i) (zb.hi i - zb.lo i) : ℤ) : ℝ) / 2 ^ 64 := by
        have hpos : (0 : ℤ) < 72 * pw 128 := by rw [pw_eq]; norm_num
        have := div_le_div_of_nonneg_right (le_cdivN (max 0 (-(F i).lo) *
          ((zb.hi i - zb.lo i) * (zb.hi i - zb.lo i))) (72 * pw 128) hpos) S.le
        refine le_trans (le_of_eq ?_) this
        simp only [M, zbRect]
        push_cast
        rw [pw_cast]
        ring
      rw [Fin.sum_univ_five]
      simp only [corrZ]
      push_cast
      simp only [add_div]
      exact add_le_add (add_le_add (add_le_add (add_le_add (term 0) (term 1)) (term 2)) (term 3)) (term 4)
    have htR : ((targetZ true + m + u + corrZ (c1Z .bcc) (c2Z .bcc) (gammaZ true) (framePZ .bcc z)
        (frameDZ .bcc z) zb bd : ℤ) : ℝ) * 2 ^ 32 < (z.a : ℝ) := by exact_mod_cast ht
    have hga : (z.toAgg.a : ℝ) = (z.a : ℝ) / 2 ^ 96 := by simp [ZAgg.toAgg]
    have tg := targetZ_ge true
    have bound : (modeTarget true : ℝ) + (m : ℝ) / 2 ^ 64 < z.toAgg.a - Gs .bcc z.toAgg γ p := by
      rw [hga]
      have e96 : (z.a : ℝ) / 2 ^ 96 = (z.a : ℝ) / 2 ^ 32 / 2 ^ 64 := by rw [div_div]; norm_num
      have h32 : ((targetZ true + m + u + corrZ (c1Z .bcc) (c2Z .bcc) (gammaZ true) (framePZ .bcc z)
          (frameDZ .bcc z) zb bd : ℤ) : ℝ) < (z.a : ℝ) / 2 ^ 32 := by
        rw [lt_div_iff₀ (by positivity)]
        exact htR
      have h64 := div_lt_div_of_pos_right h32 S
      rw [e96]
      push_cast at h64
      rw [add_div, add_div, add_div] at h64
      linarith
    obtain ⟨dpos, hlamp⟩ := (by
      have hJ := boxJZ_mem zb p hpz
      have hdet := detZ_mem hJ (adjZ_mem hJ)
      exact lamZ_mem _ _ hlam (dS p) hdet : 0 < dS p ∧ bd.lam.Mem (dS p ^ (-(1/3 : ℝ))))
    have low := strain_lower .bcc z.toAgg hz γ w dpos A hA hGram
    rw [← hpdef] at low
    have hγ1 : (γ : ℝ) = gapFactorUpper * kappaUpper := by simp [hγ, modeGamma]
    have ht1 : (modeTarget true : ℝ) = HbccUpper := by simp [modeTarget]
    rw [ht1] at bound
    have hC : (cBallsZ bd).Contains (gram A) := by
      intro i j
      rw [hGram, metric_eq]
      have hJ := boxJZ_mem zb p hpz
      have hl : bd.lam.Mem (lamS p) := hlamp
      have hm := ZI.mem_mul hl (hJ i j)
      apply ballOf_sound
      push_cast
      rw [pwQ_cast]
      exact hm
    have hdet : (A * cubicBasis .bcc).det = 1 := by rw [Matrix.det_mul, hA, bccCubic_det, one_mul]
    have upper := defectPointwiseUpper_sound (Constants.fccLength⁻¹ • (A * cubicBasis .bcc)) A
      (by rw [hA]; norm_num) (bcc_strain_points A) (cBallsZ bd) hC _ hspec
    have e : (γ : ℝ) * frobSq (gram A - 1) = gapFactorUpper * (kappaUpper * frobSq (gram A - 1)) := by
      rw [hγ1]
      ring
    have hm64 : (0 : ℝ) ≤ (m : ℝ) / 2 ^ 64 := by positivity
    have key := e2_deficit_lower (A * cubicBasis .bcc) hdet ((kappaUpper : ℝ) * frobSq (gram A - 1))
      ((m : ℝ) / 2 ^ 64) hm64 upper (by linarith)
    exact key

end BccSharp.Coulomb.BravaisCover.StrainTangent
