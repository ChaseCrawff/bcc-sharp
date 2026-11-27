import BccSharp.Cover.JLeafTerms
import BccSharp.Cover.JLeafDefect

set_option autoImplicit false

/-! Leaf checker for a JointDeficit/Continuation J witness, and its soundness through
`jointCorner_sound_valid`. That rule is the common-corner rule
`jointCorner_sound` of BccSharp.Cover.CoverCorner with validity of the chart point in
place of `good`.

The support (a list of checked `LinTerm`s on a box `S` containing the leaf)
gives the separately concave energy minorant `T = (linSum − 4) / (2 a_c)`.
The registered cost `regCost` is separately convex under a row
condition and bounds the actual defect while it is at most 1/2. With mixing
weight 4096 the J comparison is `T − e⁺_BCC − g⁺ C > 0`, and the checker
verifies it at all 256 corners of the leaf with exact rational arithmetic.
`jleaf_sound` gives the strict deficit at every valid point of the leaf box.
`valid_of_box` shows that every point of a box is valid when its radial
coordinates are positive and its first offset coordinate stays strictly
between two consecutive integers. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.CompactCover.DirectRoute (cornerRat scaleInput scaleWitness endpoints)
open BccSharp.Coulomb.BravaisCover (cubeRootCheck cubeRoot_sound)

def boxIn (inner outer : Cell) : Bool :=
  decide (∀ i, outer.lo i ≤ inner.lo i ∧ inner.hi i ≤ outer.hi i)

theorem boxIn_sound {inner outer : Cell} (h : boxIn inner outer = true) {p : Chart}
    (hp : inner.Mem p) : outer.Mem p := by
  have hs : ∀ i, outer.lo i ≤ inner.lo i ∧ inner.hi i ≤ outer.hi i := of_decide_eq_true h
  intro i
  exact ⟨(by exact_mod_cast (hs i).1 : (outer.lo i : ℝ) ≤ inner.lo i).trans (hp i).1,
    (hp i).2.trans (by exact_mod_cast (hs i).2)⟩

/-- Registration proposal of a J witness: `B`, `N = B⁻¹`, rotation `U`,
half class `f₀` and integer wrap. -/
structure RegData where
  B : Fin 3 → Fin 3 → ℚ
  N : Fin 3 → Fin 3 → ℚ
  U : Fin 3 → Fin 3 → ℚ
  f0 : Fin 3 → ℚ
  wrap : IntVec

def RegData.w (r : RegData) : Fin 3 → ℚ := fun i => r.f0 i + (r.wrap i : ℚ)

/-! ### Division by the normalizing scale `2 a_c` -/

def divScale (X : ℚ) : ℚ :=
  if X ≤ 0 then X / (2 * scaleWitness.lower) else X / (2 * scaleWitness.upper)

theorem ac_bounds (hs : cubeRootCheck scaleWitness scaleInput = true) :
    (scaleWitness.lower : ℝ) ≤ ac ∧ ac ≤ (scaleWitness.upper : ℝ) := by
  have enclosed : scaleInput.Contains (8 * Real.pi / 3) := by
    have hm := Ball.contains_mul (Ball.contains_exact (8 / 3 : ℚ)) Constants.piInput_sound
    have e : ((8 / 3 : ℚ) : ℝ) * Real.pi = 8 * Real.pi / 3 := by push_cast; ring
    rw [e] at hm
    exact hm
  have h := cubeRoot_sound scaleWitness scaleInput (8 * Real.pi / 3) (by positivity) enclosed hs
  have b := endpoints h
  dsimp only [Constants.HighPrecision.RootProposal.ball, Ball.lo, Ball.hi] at b
  push_cast at b
  unfold ac
  constructor <;> linarith [b.1, b.2]

theorem divScale_le (X : ℚ) (hs : cubeRootCheck scaleWitness scaleInput = true)
    (hlo : 0 < scaleWitness.lower) : (divScale X : ℝ) ≤ (X : ℝ) / (2 * ac) := by
  obtain ⟨lo, hi⟩ := ac_bounds hs
  have lpos : (0 : ℝ) < scaleWitness.lower := by exact_mod_cast hlo
  have acpos : (0 : ℝ) < 2 * ac := by linarith
  unfold divScale
  split
  · rename_i hX
    have hXr : (X : ℝ) ≤ 0 := by exact_mod_cast hX
    push_cast
    rw [div_le_div_iff₀ (by linarith) acpos]
    nlinarith
  · rename_i hX
    have hXr : (0 : ℝ) ≤ X := by exact_mod_cast (le_of_lt (lt_of_not_ge hX))
    push_cast
    rw [div_le_div_iff₀ (by linarith) acpos]
    nlinarith

/-! ### The leaf check -/

theorem cornerRat_pos (b : Cell) (bits : Axis → Bool) (i : Axis) (lo : 0 < b.lo i)
    (ord : b.lo i ≤ b.hi i) : 0 < cornerRat b bits i := by
  unfold cornerRat
  split
  · exact lo.trans_le ord
  · exact lo

theorem corner_coord (b : Cell) (bits : Axis → Bool) (i : Axis) :
    corner b bits i = ((cornerRat b bits i : ℚ) : ℝ) := by
  rw [← cornerRat_cast b bits]

def cornerLower (b : Cell) (K : ℚ) (wt : Fin 19 → ℚ) (r : RegData) (bits : Axis → Bool) : ℚ :=
  divScale (aggValueQ K wt (cornerRat b bits) - 4) - Constants.bccBracket.hi -
    Constants.gapBracket.hi * regCostQ r.N r.U r.w (cornerRat b bits)

def LeafGood (b S : Cell) (K : ℚ) (wt : Fin 19 → ℚ) (r : RegData) : Prop :=
  boxIn b S = true ∧ 0 < b.lo 0 ∧ 0 < b.lo 1 ∧ (∀ i, b.lo i ≤ b.hi i) ∧
    cubeRootCheck scaleWitness scaleInput = true ∧ 0 < scaleWitness.lower ∧
    registrationCheck r.B r.N r.U r.f0 = true ∧ (∀ i, ∑ j, (r.U i j) ^ 2 = 1) ∧
    4 * (b.hi 0 * b.hi 1) ^ 2 ≤ 9 * ∑ j, (r.N 2 j) ^ 2 ∧
    (∀ bits : Axis → Bool, regCostQ r.N r.U r.w (cornerRat b bits) ≤ 1 / 2) ∧
    cornerCheck (cornerLower b K wt r) = true

instance (b S : Cell) (K : ℚ) (wt : Fin 19 → ℚ) (r : RegData) : Decidable (LeafGood b S K wt r) := by
  unfold LeafGood; infer_instance

def leafCheck (b S : Cell) (K : ℚ) (wt : Fin 19 → ℚ) (r : RegData) : Bool :=
  decide (LeafGood b S K wt r)

/-- `jointCorner_sound` of BccSharp.Cover.CoverCorner, with validity of the chart
point in place of `good`: the energy and defect bounds and the conclusion only
need a valid two-site representation, not a reduced one. -/
theorem jointCorner_sound_valid (b : Cell) (T C : Chart → ℝ) (weight : ℕ) (lower : CornerLower)
    (mix : weight ≤ 4096) (energyChord : ChordLower b T) (costChord : ChordUpper b C)
    (energyLower : ∀ p, b.Mem p → (chartPoint p).Valid → T p ≤ energy (chartPoint p))
    (defectUpper : ∀ p, b.Mem p → (chartPoint p).Valid → defect (chartPoint p) ≤ C p)
    (corners : ∀ bits, (lower bits : ℝ) ≤ jointFunction T C weight (corner b bits))
    (ok : cornerCheck lower = true) (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    0 < deficit (chartPoint p) := by
  have h := cornerCheck_sound b _ (jointChord b T C weight energyChord costChord) lower corners ok p hp
  have hT := energyLower p hp hv
  have hC := defectUpper p hp hv
  have hB : energy bcc ≤ (Constants.bccBracket.hi : ℝ) := (Constants.reference_bounds .bcc).2
  have hg := Constants.reference_gap_checked.1.2
  have nng := Constants.reference_gap_checked.2.le.trans hg
  let t : ℝ := (weight : ℝ) / 4096
  have t₀ : 0 ≤ t := by dsimp [t]; positivity
  have t₁ : t ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 4096)).mpr (by exact_mod_cast mix)
  have hd := defect_range (chartPoint p)
  have cap : defect (chartPoint p) ≤ mixedDefect weight (C p) := by
    have cap1 := mul_le_mul_of_nonneg_left hd.2 (sub_nonneg.mpr t₁)
    have cap2 := mul_le_mul_of_nonneg_left hC t₀
    show defect (chartPoint p) ≤ 1 - t + t * C p
    linarith only [cap1, cap2]
  have credit := mul_le_mul hg cap hd.1 nng
  unfold deficit jointFunction at *
  linarith only [h, hT, hB, credit]

/-- Soundness of one J leaf: strict deficit at every valid point of the closed
leaf box. -/
theorem jleaf_sound (S b : Cell) (lins : List LinTerm) (K : ℚ) (wt : Fin 19 → ℚ) (r : RegData)
    (valid : ∀ t ∈ lins, t.Valid S) (hs : structureOk lins = true)
    (hK : aggConst lins = K) (hw : ∀ j, aggWeight lins j = wt j)
    (hl : leafCheck b S K wt r = true) (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    0 < deficit (chartPoint p) := by
  have g : LeafGood b S K wt r := of_decide_eq_true hl
  obtain ⟨inside, lo0, lo1, ordered, cube, lower, reg, unit, cond, small, corners⟩ := g
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast lo0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast lo1
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  let T : Chart → ℝ := fun x => (linSum lins x - 4) / (2 * ac)
  let C : Chart → ℝ := regCost r.N r.U r.w
  -- Separate concavity of the energy minorant.
  have energyChord : ChordLower b T := by
    have base := linSum_chord lins b b0 b1 (fun t ht => (valid t ht).1)
    intro x hx i t t0 t1 e
    have h := base x hx i t t0 t1 e
    show (1 - t) * ((linSum lins (atLower b x i) - 4) / (2 * ac)) +
      t * ((linSum lins (atUpper b x i) - 4) / (2 * ac)) ≤ (linSum lins x - 4) / (2 * ac)
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have ipos : (0 : ℝ) ≤ (2 * ac)⁻¹ := inv_nonneg.mpr acpos.le
    nlinarith [mul_le_mul_of_nonneg_right h ipos]
  -- Separate convexity of the registered cost.
  have costChord : ChordUpper b C := regCost_chord r.N r.U r.w b b0 b1 unit cond
  -- Energy lower bound from the support.
  have energyLower : ∀ x, b.Mem x → (chartPoint x).Valid → T x ≤ energy (chartPoint x) := by
    intro x hx gx
    have h := support_sound S lins valid hs x (boxIn_sound inside hx) gx
    show (linSum lins x - 4) / (2 * ac) ≤ (h₂ (chartPoint x) - 4) / (2 * ac)
    exact div_le_div_of_nonneg_right (by linarith) acpos.le
  -- The cost is at most 1/2 on the box, so it bounds the defect.
  have costSmall : ∀ x, b.Mem x → C x ≤ 1 / 2 := by
    intro x hx
    obtain ⟨bits, hb⟩ := corner_le b (fun y => -C y) costChord x hx
    have cv : C (corner b bits) = (regCostQ r.N r.U r.w (cornerRat b bits) : ℝ) := by
      rw [← cornerRat_cast b bits]
      exact (regCostQ_cast r.N r.U r.w (cornerRat b bits)
        (cornerRat_pos b bits 0 lo0 (ordered 0)).ne'
        (cornerRat_pos b bits 1 lo1 (ordered 1)).ne').symm
    have hs := (Rat.cast_le (K := ℝ)).mpr (small bits)
    push_cast at hs
    have : C (corner b bits) ≤ 1 / 2 := by rw [cv]; exact hs
    have hb' : -C (corner b bits) ≤ -C x := hb
    linarith
  have defectUpper : ∀ x, b.Mem x → (chartPoint x).Valid → defect (chartPoint x) ≤ C x := by
    intro x hx gx
    exact defect_le_regCost r.B r.N r.U r.f0 r.wrap reg x gx (costSmall x hx)
  -- Corner values.
  have cornerVals : ∀ bits, (cornerLower b K wt r bits : ℝ) ≤
      jointFunction T C 4096 (corner b bits) := by
    intro bits
    have c0 : cornerRat b bits 0 ≠ 0 := (cornerRat_pos b bits 0 lo0 (ordered 0)).ne'
    have c1 : cornerRat b bits 1 ≠ 0 := (cornerRat_pos b bits 1 lo1 (ordered 1)).ne'
    have cr0 : (corner b bits) 0 ≠ 0 := by
      rw [corner_coord]; exact_mod_cast c0
    have cr1 : (corner b bits) 1 ≠ 0 := by
      rw [corner_coord]; exact_mod_cast c1
    have lin := linSum_feat lins (corner b bits) cr0 cr1
    have agg : linSum lins (corner b bits) = (aggValueQ K wt (cornerRat b bits) : ℝ) := by
      rw [lin, ← hK]
      unfold aggValueQ
      push_cast
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hw j, featGen_cast, cornerRat_cast]
    have cost : C (corner b bits) = (regCostQ r.N r.U r.w (cornerRat b bits) : ℝ) := by
      rw [← cornerRat_cast b bits]
      exact (regCostQ_cast r.N r.U r.w (cornerRat b bits) c0 c1).symm
    have div := divScale_le (aggValueQ K wt (cornerRat b bits) - 4) cube lower
    unfold jointFunction mixedDefect
    show (cornerLower b K wt r bits : ℝ) ≤ (linSum lins (corner b bits) - 4) / (2 * ac) -
      (Constants.bccBracket.hi : ℝ) - (Constants.gapBracket.hi : ℝ) *
        (1 - ((4096 : ℕ) : ℝ) / 4096 + ((4096 : ℕ) : ℝ) / 4096 * C (corner b bits))
    rw [agg, cost]
    unfold cornerLower
    push_cast at div ⊢
    norm_num
    linarith
  exact jointCorner_sound_valid b T C 4096 (cornerLower b K wt r) (by norm_num) energyChord costChord
    energyLower defectUpper cornerVals corners p hp hv

/-- The same leaf as a route result for the cover framework, on `good` points. -/
theorem jleaf_sound_good (S b : Cell) (lins : List LinTerm) (K : ℚ) (wt : Fin 19 → ℚ) (r : RegData)
    (valid : ∀ t ∈ lins, t.Valid S) (hs : structureOk lins = true)
    (hK : aggConst lins = K) (hw : ∀ j, aggWeight lins j = wt j)
    (hl : leafCheck b S K wt r = true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    Route.result .strictJoint p :=
  jleaf_sound S b lins K wt r valid hs hK hw hl p hp gp.1

/-- Every point of a closed box is a valid chart point when the box keeps both
radial coordinates positive and the first offset coordinate strictly between
the integers `k` and `k + 1`. A statement for the valid points of such a box
then holds at all of its points. -/
theorem valid_of_box (b : Cell) (k : ℤ) (l0 : (0 : ℚ) < b.lo 0) (l1 : (0 : ℚ) < b.lo 1)
    (l5 : (k : ℚ) < b.lo 5) (h5 : b.hi 5 < (k : ℚ) + 1) (p : Chart) (hp : b.Mem p) :
    (chartPoint p).Valid := by
  have m0 : ((b.lo 0 : ℚ) : ℝ) ≤ p 0 ∧ p 0 ≤ ((b.hi 0 : ℚ) : ℝ) := hp 0
  have m1 : ((b.lo 1 : ℚ) : ℝ) ≤ p 1 ∧ p 1 ≤ ((b.hi 1 : ℚ) : ℝ) := hp 1
  have m5 : ((b.lo 5 : ℚ) : ℝ) ≤ p 5 ∧ p 5 ≤ ((b.hi 5 : ℚ) : ℝ) := hp 5
  have c0 : (0 : ℝ) < ((b.lo 0 : ℚ) : ℝ) := by exact_mod_cast l0
  have c1 : (0 : ℝ) < ((b.lo 1 : ℚ) : ℝ) := by exact_mod_cast l1
  have c5 : ((k : ℚ) : ℝ) < ((b.lo 5 : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).mpr l5
  have d5 : ((b.hi 5 : ℚ) : ℝ) < (((k : ℚ) + 1 : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).mpr h5
  rw [Rat.cast_intCast] at c5
  push_cast at d5
  have r0 : (0 : ℝ) < p 0 := lt_of_lt_of_le c0 m0.1
  have r1 : (0 : ℝ) < p 1 := lt_of_lt_of_le c1 m1.1
  have r5 : (k : ℝ) < p 5 := lt_of_lt_of_le c5 m5.1
  have r5' : p 5 < (k : ℝ) + 1 := lt_of_le_of_lt m5.2 d5
  refine ⟨?_, ?_⟩
  · have e : (chartPoint p).basis.det = p 0 * p 1 * (p 0 * p 1)⁻¹ := by
      simp [chartPoint, chartBasis, Matrix.det_fin_three]
    rw [e]
    exact mul_inv_cancel₀ (mul_ne_zero r0.ne' r1.ne')
  · intro n hn
    have e5 : p 5 = ((n 0 : ℤ) : ℝ) := congrFun hn 0
    have a : k < n 0 := by
      have h : (k : ℝ) < ((n 0 : ℤ) : ℝ) := by rw [← e5]; exact r5
      exact_mod_cast h
    have c : n 0 < k + 1 := by
      have h : ((n 0 : ℤ) : ℝ) < (k : ℝ) + 1 := by rw [← e5]; exact r5'
      exact_mod_cast h
    omega

end BccSharp.Coulomb.CompactCover.JLeaf
