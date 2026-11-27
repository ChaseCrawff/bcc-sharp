import BccSharp.Cover.Stage2Fix

set_option autoImplicit false

/-! Soundness of the fixed-point Stage2 evaluator `BccSharp.Cover.Stage2Fix`.

* Scalars: `sqrtPiHi_ge`, `oneHighF_sound`, `halfHighF_sound` (the upper side
  of `Erfc.sqrt_remainder`, or `kernelValue_positive_bound` past `t = 24`),
  and `tangentF_sound`, the statement of `Stage2.tangent_sound`: a nonnegative
  penalty and `intercept - penalty·q ≤ kernelValue kind (π q)` for all `q > 0`,
  from `Stage2.globalTangent` at the anchor.
* Lines: `floorF_sound`, `evalLineF_sound` (the statement of
  `Stage2.evalLine_sound` for the rational line `LineF.toLine`), and
  `prepareF_sound`.
* Folds: `sumL` against list sums, the retained modes of the rational lines
  (`findLine_toLine`, `intercept_retained`, `moments_eq`: the integer moments
  are `Stage2.moments` of the retained modes and weights), and the integer
  corner fold: `fold_cast` (the integer corner value is `2^160 R₁²R₂² S` times
  `packedCorner`) and `foldZ_sound` (every corner value is at most the cap).
* The routes: `preparedLowerU` (the shape of `Stage2.preparedLower` for any
  corner bound), `bulkFix_sound`, `capacityF_sound`, `budgetF_sound` (the
  shape of `Stage2.budget_sound`), `checkedBudgetF_sound` and `phaseFix_sound`,
  with the conclusion of `Stage2.bulkCheck_sound` and `Stage2.phaseCheck_sound`;
  both routes go through `foldZ_sound` and `preparedLowerU`.
* Reference only: the exact rational corner maximum `cornerMax` with
  `packedCorner_le_cornerMax`, `preparedLowerF` and `baselineF`, which no
  route uses. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Stage2Fix
open BccSharp BccSharp.Coverage DirectRoute OverlayPlanar.Fix DirectFix Stage2 BravaisCover

/-! ### Upper bounds of the kernels -/

theorem sqrtPiHi_ge : Real.sqrt Real.pi ≤ (sqrtPiHi : ℝ) / Sz := by
  have p := Real.pi_lt_d20
  have h : Real.pi ≤ ((sqrtPiHi : ℝ) / Sz) ^ 2 := by
    refine p.le.trans ?_
    rw [div_pow, le_div_iff₀ (by norm_num [Sz])]
    norm_num [sqrtPiHi, Sz]
  exact Real.sqrt_le_iff.mpr ⟨div_nonneg (Nat.cast_nonneg _) Sz_pos.le, h⟩

theorem oneHigh_at (T : ℕ) (hT : 0 < T) :
    Real.exp (-((T : ℝ) / Sz)) / ((T : ℝ) / Sz) ≤ (oneHighF T : ℝ) / Sz := by
  have sp := Sz_pos
  have TR : (0 : ℝ) < T := by exact_mod_cast hT
  have T0 : (0 : ℤ) < (T : ℤ) := by exact_mod_cast hT
  have e := (expNegPt_mem T).2
  have c := le_cdiv ((expNegPt T).hi * Sz) (T : ℤ) T0
  calc Real.exp (-((T : ℝ) / Sz)) / ((T : ℝ) / Sz)
      ≤ ((expNegPt T).hi : ℝ) / Sz / ((T : ℝ) / Sz) :=
        div_le_div_of_nonneg_right e (div_pos TR sp).le
    _ = ((((expNegPt T).hi * Sz : ℤ) : ℝ) / ((T : ℤ) : ℝ)) / Sz := by push_cast; field_simp
    _ ≤ (oneHighF T : ℝ) / Sz := div_le_div_of_nonneg_right c sp.le

theorem oneHighF_sound (T : ℕ) (hT : 0 < T) {x : ℝ} (hx : (T : ℝ) / Sz ≤ x) :
    gKernel 1 x ≤ (oneHighF T : ℝ) / Sz := by
  have tpos : (0 : ℝ) < (T : ℝ) / Sz := div_pos (by exact_mod_cast hT) Sz_pos
  have mono := oneKernel_decreasing tpos hx
  rw [gKernel_one tpos] at mono
  exact mono.trans (oneHigh_at T hT)

/-- The real-number core: `G(1/2, t) ≤ √π/√t - 2 series + 4 t^96/96!`. -/
theorem half_series_upper {q : ℚ} (q0 : 0 < q) (q24 : q ≤ 24) :
    gKernel (1/2) (q : ℝ) ≤ Real.sqrt Real.pi / Real.sqrt (q : ℝ) - 2 * (Erfc.series q 96 : ℝ) +
      4 * (q : ℝ) ^ 96 / (Nat.factorial 96 : ℝ) := by
  have qr : (0 : ℝ) < q := by exact_mod_cast q0
  have guard : q / (96 + 1 : ℕ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by norm_num)]
    push_cast
    linarith
  have rem := Erfc.sqrt_remainder q0.le 96 guard
  have sp := Real.sqrt_pos.mpr Real.pi_pos
  have sq := Real.sqrt_pos.mpr qr
  have f0 : (0 : ℝ) < (Nat.factorial 96 : ℝ) := by positivity
  rw [halfKernel_formula qr]
  have upper := (abs_le.mp rem).2
  set E := Gaussian.erfcIntegral (Real.sqrt (q : ℝ))
  set s := Real.sqrt (q : ℝ)
  set P := Real.sqrt Real.pi
  set z := (Erfc.series q 96 : ℝ)
  have hE : E ≤ 1 - 2 * s / P * z + 4 * s * (q : ℝ) ^ 96 / (P * (Nat.factorial 96 : ℝ)) := by
    linarith
  calc P * E / s = P / s * E := by ring
    _ ≤ P / s * (1 - 2 * s / P * z + 4 * s * (q : ℝ) ^ 96 / (P * (Nat.factorial 96 : ℝ))) :=
        mul_le_mul_of_nonneg_left hE (div_nonneg sp.le sq.le)
    _ = P / s - 2 * z + 4 * (q : ℝ) ^ 96 / (Nat.factorial 96 : ℝ) := by field_simp

theorem halfHigh_at (T : ℕ) (hT : 0 < T) :
    gKernel (1/2) ((T : ℝ) / Sz) ≤ (halfHighF T : ℝ) / Sz := by
  have sp := Sz_pos
  have tpos : (0 : ℝ) < (T : ℝ) / Sz := div_pos (by exact_mod_cast hT) sp
  unfold halfHighF
  split_ifs with h
  · dsimp only
    set q : ℚ := (T : ℚ) / S with hq
    have qt : ((q : ℚ) : ℝ) = (T : ℝ) / Sz := by rw [hq]; push_cast; rw [S_eq]
    have q0 : 0 < q := by rw [hq]; exact div_pos (by exact_mod_cast hT) (by norm_num [S])
    have q24 : q ≤ 24 := by
      have h2 : ((T : ℕ) : ℝ) ≤ 24 * (Sz : ℝ) := by rw [← halfTMax_eq]; exact_mod_cast h.1
      have : ((q : ℚ) : ℝ) ≤ 24 := by rw [qt, div_le_iff₀ sp]; exact h2
      exact_mod_cast this
    have core := half_series_upper q0 q24
    rw [qt] at core
    set R := sqrtLo (T * S) with hR
    set acc : ℤ := (hornerN (T * T) erfPosC : ℤ) - ((T * hornerN (T * T) erfNegC : ℕ) : ℤ) with hacc
    have R0 : (0 : ℝ) < R := by exact_mod_cast h.2
    have RR := sqrtLo_sq (T * S)
    have Rs : (R : ℝ) ≤ Real.sqrt ((T : ℝ) / Sz) * Sz := by
      have e : Real.sqrt ((T : ℝ) / Sz) * Sz = Real.sqrt ((T : ℝ) * Sz) := by
        rw [show (T : ℝ) * Sz = (T : ℝ) / Sz * Sz ^ 2 by field_simp,
          Real.sqrt_mul' _ (by positivity), Real.sqrt_sq sp.le]
      have c : ((R * R : ℕ) : ℝ) ≤ ((T * S : ℕ) : ℝ) := by exact_mod_cast RR
      push_cast at c
      rw [S_eq] at c
      rw [e]
      calc (R : ℝ) = Real.sqrt ((R : ℝ) * R) := (Real.sqrt_mul_self R0.le).symm
        _ ≤ Real.sqrt ((T : ℝ) * Sz) := Real.sqrt_le_sqrt c
    have lead : Real.sqrt Real.pi / Real.sqrt ((T : ℝ) / Sz) ≤
        ((cdivN (sqrtPiHi * S) R : ℕ) : ℝ) / Sz := by
      have st := Real.sqrt_pos.mpr tpos
      have c := cdivN_ge (sqrtPiHi * S) R h.2
      calc Real.sqrt Real.pi / Real.sqrt ((T : ℝ) / Sz)
          ≤ ((sqrtPiHi : ℝ) / Sz) / Real.sqrt ((T : ℝ) / Sz) :=
            div_le_div_of_nonneg_right sqrtPiHi_ge st.le
        _ ≤ ((sqrtPiHi : ℝ) / Sz) / ((R : ℝ) / Sz) := by
            apply div_le_div_of_nonneg_left (div_nonneg (Nat.cast_nonneg _) sp.le) (div_pos R0 sp)
            rw [div_le_iff₀ sp]; exact Rs
        _ = ((sqrtPiHi * S : ℕ) : ℝ) / R / Sz := by push_cast; rw [S_eq]; field_simp
        _ ≤ ((cdivN (sqrtPiHi * S) R : ℕ) : ℝ) / Sz := div_le_div_of_nonneg_right c sp.le
    have accR : (acc : ℝ) = ((S ^ 95 * Nat.factorial 95 * erfL : ℕ) : ℝ) *
        (Erfc.series ((T : ℚ) / S) 96 : ℝ) := by
      rw [hacc, ← erfHorner_eq T]; push_cast; ring
    have DS : ((erfDS : ℤ) : ℝ) * Sz = ((S ^ 95 * Nat.factorial 95 * erfL : ℕ) : ℝ) := by
      rw [← S_eq]; push_cast; exact_mod_cast erfDS_eq
    have DS0 : (0 : ℤ) < erfDS := by norm_num [erfDS]
    have serB : ((acc / (erfDS : ℤ) : ℤ) : ℝ) / Sz ≤ (Erfc.series q 96 : ℝ) := by
      have c := fdiv_le acc (erfDS : ℤ) DS0
      have e : (acc : ℝ) / ((erfDS : ℤ) : ℝ) = (Erfc.series q 96 : ℝ) * Sz := by
        rw [accR, ← DS, hq]; field_simp
      rw [e] at c
      rw [div_le_iff₀ sp]; exact c
    have errB : 4 * ((T : ℝ) / Sz) ^ 96 / (Nat.factorial 96 : ℝ) ≤ (erfErr : ℝ) / Sz := by
      refine le_trans ?_ erfErr_ok
      have t24 : (T : ℝ) / Sz ≤ 24 := by rw [← qt]; exact_mod_cast q24
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ tpos.le t24 96) (by norm_num)
    push_cast
    rw [add_div, sub_div, mul_div_assoc]
    linarith
  · exact ((kernelValue_positive_bound .half tpos).2.trans (by
      simpa [kernelValue, KernelKind.power] using (oneHigh_at T hT))) |>.trans_eq' (by
        simp [kernelValue, KernelKind.power])

theorem halfHighF_sound (T : ℕ) (hT : 0 < T) {x : ℝ} (hx : (T : ℝ) / Sz ≤ x) :
    gKernel (1/2) x ≤ (halfHighF T : ℝ) / Sz := by
  have tpos : (0 : ℝ) < (T : ℝ) / Sz := div_pos (by exact_mod_cast hT) Sz_pos
  exact (halfKernel_decreasing tpos hx).trans (halfHigh_at T hT)

/-! ### Tangents -/

theorem anchorScale_eq : (anchorScale : ℝ) / Sz = 1 / (anchorGrid : ℝ) := by
  norm_num [anchorScale, Sz, anchorGrid]

theorem piLow_sound (X : ℕ) : (piLow X : ℝ) / Sz ≤ Real.pi * ((X : ℝ) / Sz) := by
  have sp := Sz_pos
  have tl := twoPi_bounds.1
  have tp : (0 : ℤ) ≤ twoPiLo := by norm_num [twoPiLo]
  have e : ((twoPiLo.toNat : ℕ) : ℝ) = (twoPiLo : ℝ) := by exact_mod_cast Int.toNat_of_nonneg tp
  have f := fdivN_le (twoPiLo.toNat * X) (2 * S)
  unfold piLow
  calc ((twoPiLo.toNat * X / (2 * S) : ℕ) : ℝ) / Sz
      ≤ ((twoPiLo.toNat * X : ℕ) : ℝ) / ((2 * S : ℕ) : ℝ) / Sz := div_le_div_of_nonneg_right f sp.le
    _ = ((twoPiLo : ℝ) / Sz) * ((X : ℝ) / Sz) / 2 := by push_cast; rw [e, S_eq]; field_simp
    _ ≤ (2 * Real.pi) * ((X : ℝ) / Sz) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_right tl (div_nonneg (Nat.cast_nonneg _) sp.le)
    _ = Real.pi * ((X : ℝ) / Sz) := by ring

theorem power_half : ((KernelKind.half.power : ℚ) : ℝ) = 1 / 2 := by norm_num [KernelKind.power]
theorem power_one : ((KernelKind.one.power : ℚ) : ℝ) = 1 := by norm_num [KernelKind.power]

theorem le_max_cdiv {x : ℝ} {n d : ℤ} (hd : 0 < d) (h : x ≤ (n : ℝ) / d) :
    x ≤ ((max 0 (cdivZ n d) : ℤ) : ℝ) := by
  have c := le_cdiv n d hd
  have m : ((cdivZ n d : ℤ) : ℝ) ≤ ((max 0 (cdivZ n d) : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
  linarith

theorem tangentF_sound (kind : KernelKind) (ticks : ℕ) (r : TangentF) (ok : tangentF kind ticks = some r) :
    0 ≤ r.penalty ∧ ∀ q : ℝ, 0 < q →
      (r.intercept : ℝ) / Sz - ((r.penalty : ℝ) / Sz) * q ≤ kernelValue kind (Real.pi * q) := by
  have sp := Sz_pos
  unfold tangentF at ok
  dsimp only at ok
  split_ifs at ok with h
  set X := ticks * anchorScale with hX
  set Thi := piTimes (X : ℤ) with hThi
  set Tlo := piLow X with hTlo
  have X0 : 0 < X := Nat.mul_pos h.1 (by norm_num [anchorScale])
  have XR : (0 : ℝ) < X := by exact_mod_cast X0
  have xpos : (0 : ℝ) < (X : ℝ) / Sz := div_pos XR sp
  set a := Real.pi * ((X : ℝ) / Sz) with ha
  have apos : 0 < a := mul_pos Real.pi_pos xpos
  have aHi : a ≤ (Thi : ℝ) / Sz := by
    have := piTimes_sound (Q := (X : ℤ)) xpos.le (by push_cast; exact le_rfl)
    simpa [hThi] using this
  have aLo : (Tlo : ℝ) / Sz ≤ a := piLow_sound X
  have eLo : ((expNegPt Thi).lo : ℝ) / Sz ≤ Real.exp (-a) :=
    (expNegPt_mem Thi).1.trans (Real.exp_le_exp.mpr (neg_le_neg aHi))
  have eHi : Real.exp (-a) ≤ ((expNegPt Tlo).hi : ℝ) / Sz :=
    (Real.exp_le_exp.mpr (neg_le_neg aLo)).trans (expNegPt_mem Tlo).2
  have slope : -Real.pi * kernelSlope kind a = (Real.exp (-a) + (kind.power : ℝ) * kernelValue kind a) /
      ((X : ℝ) / Sz) := by
    unfold kernelSlope; rw [ha]; field_simp
  have qx (q : ℝ) : Real.pi * q - a = Real.pi * (q - (X : ℝ) / Sz) := by rw [ha]; ring
  -- the tangent at the anchor, in the intercept-penalty form
  have tangent (q : ℝ) (hq : 0 < q) :
      kernelValue kind a + (-Real.pi * kernelSlope kind a) * ((X : ℝ) / Sz) -
        (-Real.pi * kernelSlope kind a) * q ≤ kernelValue kind (Real.pi * q) := by
    have t := globalTangent kind apos (mul_pos Real.pi_pos hq)
    rw [qx q] at t
    linarith
  -- intercept and penalty bounds give the claim
  have finish (I P : ℤ) (hI : (I : ℝ) / Sz ≤ kernelValue kind a + (-Real.pi * kernelSlope kind a) * ((X : ℝ) / Sz))
      (hP : -Real.pi * kernelSlope kind a ≤ (P : ℝ) / Sz) (q : ℝ) (hq : 0 < q) :
      (I : ℝ) / Sz - ((P : ℝ) / Sz) * q ≤ kernelValue kind (Real.pi * q) := by
    have pq := mul_le_mul_of_nonneg_right hP hq.le
    have t := tangent q hq
    linarith
  cases kind with
  | half =>
    have e := Option.some.inj ok
    have vLo := halfLowF_sound Thi apos aHi
    have vHi := halfHighF_sound Tlo h.2 aLo
    have kv : kernelValue .half a = gKernel (1/2) a := by norm_num [kernelValue, KernelKind.power]
    rw [power_half, kv] at slope
    rw [← e]
    refine ⟨le_max_left _ _, finish _ _ ?_ ?_⟩
    · rw [kv, slope]
      have xne : (X : ℝ) / Sz ≠ 0 := xpos.ne'
      rw [div_mul_cancel₀ _ xne]
      have f := fdiv_le (3 * halfLowF Thi) 2 (by norm_num)
      have h3 : ((3 * halfLowF Thi / 2 : ℤ) : ℝ) / Sz ≤ 3 / 2 * gKernel (1/2) a := by
        calc ((3 * halfLowF Thi / 2 : ℤ) : ℝ) / Sz ≤ (((3 * halfLowF Thi : ℤ) : ℝ) / ((2 : ℤ) : ℝ)) / Sz :=
              div_le_div_of_nonneg_right f sp.le
          _ = 3 / 2 * ((halfLowF Thi : ℝ) / Sz) := by push_cast; ring
          _ ≤ 3 / 2 * gKernel (1/2) a := mul_le_mul_of_nonneg_left vLo (by norm_num)
      push_cast
      rw [add_div]
      linarith
    · rw [slope]
      rw [le_div_iff₀ sp]
      apply le_max_cdiv (by exact_mod_cast (show 0 < 2 * X by omega))
      push_cast
      rw [le_div_iff₀ sp] at eHi vHi
      have key : 2 * (Real.exp (-a) * Sz) + gKernel (1/2) a * Sz ≤
          2 * ((expNegPt Tlo).hi : ℝ) + (halfHighF Tlo : ℝ) := by linarith
      calc (Real.exp (-a) + 1 / 2 * gKernel (1 / 2) a) / ((X : ℝ) / Sz) * Sz
          = (2 * (Real.exp (-a) * Sz) + gKernel (1/2) a * Sz) * Sz / (2 * X) := by field_simp
        _ ≤ (2 * ((expNegPt Tlo).hi : ℝ) + (halfHighF Tlo : ℝ)) * Sz / (2 * X) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right key sp.le
  | one =>
    have e := Option.some.inj ok
    have vLo := oneLowF_sound Thi apos aHi
    have vHi := oneHighF_sound Tlo h.2 aLo
    have kv : kernelValue .one a = gKernel 1 a := by norm_num [kernelValue, KernelKind.power]
    rw [power_one, kv] at slope
    rw [← e]
    refine ⟨le_max_left _ _, finish _ _ ?_ ?_⟩
    · rw [kv, slope]
      have xne : (X : ℝ) / Sz ≠ 0 := xpos.ne'
      rw [div_mul_cancel₀ _ xne]
      push_cast
      rw [add_div, mul_div_assoc]
      linarith
    · rw [slope]
      rw [le_div_iff₀ sp]
      apply le_max_cdiv (by exact_mod_cast X0)
      push_cast
      rw [le_div_iff₀ sp] at eHi vHi
      have key : Real.exp (-a) * Sz + gKernel 1 a * Sz ≤ ((expNegPt Tlo).hi : ℝ) + (oneHighF Tlo : ℝ) := by
        linarith
      calc (Real.exp (-a) + 1 * gKernel 1 a) / ((X : ℝ) / Sz) * Sz
          = (Real.exp (-a) * Sz + gKernel 1 a * Sz) * Sz / X := by field_simp
        _ ≤ (((expNegPt Tlo).hi : ℝ) + (oneHighF Tlo : ℝ)) * Sz / X := by
            apply div_le_div_of_nonneg_right _ XR.le
            exact mul_le_mul_of_nonneg_right key sp.le

/-! ### Lines -/

theorem cdivZ_nonneg {n d : ℤ} (hn : 0 ≤ n) (hd : 0 < d) : 0 ≤ cdivZ n d := by
  have c := le_cdiv n d hd
  have h : (0 : ℝ) ≤ (n : ℝ) / d := div_nonneg (by exact_mod_cast hn) (by exact_mod_cast hd.le)
  exact_mod_cast h.trans c

theorem floorF_sound (b : Cell) (m : Mode) (p : Chart) (hp : b.Mem p) :
    0 ≤ floorF b m ∧
      (m.family = .reciprocal → ((floorF b m : ℝ) / Sz) ≤ phaseFactor (chartPoint p) m.index) ∧
      (m.family ≠ .reciprocal → floorF b m = Sz) := by
  unfold floorF
  by_cases dual : m.family = .reciprocal
  · rw [ite_eq_left dual]
    obtain ⟨n0, nb⟩ := phaseLowF_sound hp m.index
    exact ⟨n0, fun _ => by unfold phaseFactor; exact nb, fun h => (h dual).elim⟩
  · rw [ite_eq_right dual]
    exact ⟨by norm_num [Sz], fun h => (dual h).elim, fun _ => rfl⟩

private theorem kernel_half (x : ℝ) : kernelValue .half x = gKernel (1/2) x := by
  norm_num [kernelValue, KernelKind.power]

private theorem kernel_one (x : ℝ) : kernelValue .one x = gKernel 1 x := by
  norm_num [kernelValue, KernelKind.power]

theorem multF_nonneg (b : Cell) (m : Mode) (p : Chart) (hp : b.Mem p) : 0 ≤ multF b m := by
  unfold multF
  split_ifs
  · norm_num [Sz]
  · exact mul_nonneg (by norm_num) (floorF_sound b m p hp).1

theorem evalLineF_eq (b : Cell) (src : AnchorRow) (l : LineF) (ok : evalLineF b src = some l) :
    src.mode.valid ∧ ∃ t, tangentF src.mode.kind src.ticks = some t ∧
      l = ⟨src.mode, multF b src.mode * t.intercept / Sz, cdivZ (multF b src.mode * t.penalty) Sz,
        floorF b src.mode⟩ := by
  unfold evalLineF at ok
  by_cases permitted : decide src.mode.valid = true
  · rw [ite_eq_left permitted] at ok
    cases kt : tangentF src.mode.kind src.ticks with
    | none => rw [kt] at ok; cases ok
    | some t =>
      rw [kt] at ok
      exact ⟨of_decide_eq_true permitted, t, rfl, (Option.some.inj ok).symm⟩
  · rw [ite_eq_right permitted] at ok; cases ok

theorem evalLineF_sound (b : Cell) (src : AnchorRow) (l : LineF) (ok : evalLineF b src = some l)
    (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) :
    l.mode = src.mode ∧ l.mode.valid ∧ 0 ≤ l.penalty ∧ 0 ≤ l.toLine.residual (chartPoint p) ∧
    ((l.intercept : ℝ) / Sz) - ((l.penalty : ℝ) / Sz) * l.mode.radial (squarePoint p) ≤
      l.mode.term (chartPoint p) - l.toLine.residual (chartPoint p) := by
  have sp := Sz_pos
  obtain ⟨valid, t, kt, rfl⟩ := evalLineF_eq b src l ok
  obtain ⟨tp, ts⟩ := tangentF_sound _ _ _ kt
  obtain ⟨fn, fb, fu⟩ := floorF_sound b src.mode p hp
  have m0 := multF_nonneg b src.mode p hp
  set fl := floorF b src.mode with hfl
  set mult := multF b src.mode with hmult
  have mR : (0 : ℝ) ≤ (mult : ℝ) / Sz := div_nonneg (by exact_mod_cast m0) sp.le
  have iB : ((mult * t.intercept / Sz : ℤ) : ℝ) / Sz ≤ ((mult : ℝ) / Sz) * ((t.intercept : ℝ) / Sz) := by
    have f := fdiv_le (mult * t.intercept) Sz Sz_posZ
    calc ((mult * t.intercept / Sz : ℤ) : ℝ) / Sz ≤ (((mult * t.intercept : ℤ) : ℝ) / Sz) / Sz :=
          div_le_div_of_nonneg_right f sp.le
      _ = ((mult : ℝ) / Sz) * ((t.intercept : ℝ) / Sz) := by push_cast; ring
  have pB : ((mult : ℝ) / Sz) * ((t.penalty : ℝ) / Sz) ≤ ((cdivZ (mult * t.penalty) Sz : ℤ) : ℝ) / Sz := by
    have c := le_cdiv (mult * t.penalty) Sz Sz_posZ
    calc ((mult : ℝ) / Sz) * ((t.penalty : ℝ) / Sz) = (((mult * t.penalty : ℤ) : ℝ) / Sz) / Sz := by
          push_cast; ring
      _ ≤ ((cdivZ (mult * t.penalty) Sz : ℤ) : ℝ) / Sz := div_le_div_of_nonneg_right c sp.le
  have line (rad : ℝ) (hrad : 0 < rad) :
      ((mult * t.intercept / Sz : ℤ) : ℝ) / Sz - (((cdivZ (mult * t.penalty) Sz : ℤ) : ℝ) / Sz) * rad ≤
        ((mult : ℝ) / Sz) * kernelValue src.mode.kind (Real.pi * rad) := by
    have tl := ts rad hrad
    have a1 : ((mult : ℝ) / Sz) * (((t.penalty : ℝ) / Sz) * rad) ≤
        (((cdivZ (mult * t.penalty) Sz : ℤ) : ℝ) / Sz) * rad := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right pB hrad.le
    have a2 := mul_le_mul_of_nonneg_left tl mR
    rw [mul_sub] at a2
    linarith
  refine ⟨rfl, valid, cdivZ_nonneg (mul_nonneg m0 tp) Sz_posZ, ?_⟩
  have flS : (((fl : ℚ) / S : ℚ) : ℝ) = (fl : ℝ) / Sz := by push_cast; rw [S_eq]
  have resEq : (LineF.toLine ⟨src.mode, mult * t.intercept / Sz, cdivZ (mult * t.penalty) Sz, fl⟩).residual
      (chartPoint p) = if src.mode.family = .reciprocal then
        2 * (phaseFactor (chartPoint p) src.mode.index - (fl : ℝ) / Sz) * seriesReciprocalTerm (chartPoint p) src.mode.index
      else 0 := by
    unfold Line.residual LineF.toLine
    split_ifs <;> simp [flS]
  simp only [resEq]
  cases family : src.mode.family with
  | cross =>
    have distance := cross_distance_positive hv src.mode.index
    have kind : src.mode.kind = .half := by simp [Mode.kind, family]
    have mOne : (mult : ℝ) / Sz = 1 := by
      rw [hmult]; unfold multF; rw [ite_eq_left family]; exact div_self sp.ne'
    have radial : src.mode.radial (squarePoint p) =
        quad (gram (chartBasis p)) (chartVector p true src.mode.index) := by
      simp only [Mode.radial, family]
      exact squaredRadial_eq p true _
    have term : src.mode.term (chartPoint p) =
        gKernel (1/2) (Real.pi * quad (gram (chartBasis p)) (chartVector p true src.mode.index)) := by
      simp only [Mode.term, family]
      rfl
    simp only [reduceCtorEq, ite_false]
    refine ⟨le_rfl, ?_⟩
    rw [sub_zero, radial, term]
    have h := line _ distance
    rw [kind, kernel_half, mOne, one_mul] at h
    exact h
  | period =>
    have lex : lexPositive src.mode.index := valid.2.resolve_left (by simp [family])
    have distance := period_distance_positive hv src.mode.index lex
    have kind : src.mode.kind = .half := by simp [Mode.kind, family]
    have one : fl = Sz := fu (by simp [family])
    have mTwo : (mult : ℝ) / Sz = 2 := by
      rw [hmult]; unfold multF; rw [ite_eq_right (by simp [family]), ← hfl, one]; push_cast; field_simp
    have radial : src.mode.radial (squarePoint p) =
        quad (gram (chartBasis p)) (chartVector p false src.mode.index) := by
      simp only [Mode.radial, family]
      exact squaredRadial_eq p false _
    have term : src.mode.term (chartPoint p) =
        2 * gKernel (1/2) (Real.pi * quad (gram (chartBasis p)) (chartVector p false src.mode.index)) := by
      simp only [Mode.term, family]
      rw [seriesDirectTerm, ite_eq_right (lex_ne lex)]
      rfl
    simp only [reduceCtorEq, ite_false]
    refine ⟨le_rfl, ?_⟩
    rw [sub_zero, radial, term]
    have h := line _ distance
    rw [kind, kernel_half, mTwo] at h
    exact h
  | reciprocal =>
    have lex : lexPositive src.mode.index := valid.2.resolve_left (by simp [family])
    have pos := reciprocalPositive hv (lex_ne lex)
    have kind : src.mode.kind = .one := by simp [Mode.kind, family]
    have base : seriesReciprocalTerm (chartPoint p) src.mode.index =
        gKernel 1 (Real.pi * quad (gram (chartPoint p).basis)⁻¹ (castVec src.mode.index)) := by
      rw [seriesReciprocalTerm, ite_eq_right (lex_ne lex)]
    have nonnegative : 0 ≤ seriesReciprocalTerm (chartPoint p) src.mode.index := by
      rw [base, gKernel_one (mul_pos Real.pi_pos pos)]; positivity
    have floor := fb family
    have mFl : (mult : ℝ) / Sz = 2 * ((fl : ℝ) / Sz) := by
      rw [hmult]; unfold multF; rw [ite_eq_right (by simp [family]), ← hfl]; push_cast; ring
    obtain ⟨h0, h1⟩ := radialLoPos b hd
    have d0 := h0.trans_le (hp 0).1
    have d1 := h1.trans_le (hp 1).1
    have radial : src.mode.radial (squarePoint p) =
        quad (gram (chartPoint p).basis)⁻¹ (castVec src.mode.index) := by
      simp only [Mode.radial, family]
      exact dualRadial_eq _ p d0.ne' d1.ne'
    have term : src.mode.term (chartPoint p) =
        2 * (phaseFactor (chartPoint p) src.mode.index * seriesReciprocalTerm (chartPoint p) src.mode.index) := by
      simp only [Mode.term, family]
      rw [pairedTerm_eq]
      rfl
    simp only [ite_true]
    refine ⟨mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr floor)) nonnegative, ?_⟩
    rw [radial, term]
    have h := line _ pos
    rw [kind, kernel_one, mFl, ← base] at h
    linarith

theorem prepareF_sound (b : Cell) (src : List AnchorRow) (out : List LineF) (h : prepareF b src = some out)
    (l : LineF) (hl : l ∈ out) : ∃ raw ∈ src, evalLineF b raw = some l := by
  induction src generalizing out with
  | nil =>
    have e : ([] : List LineF) = out := Option.some.inj h
    subst e
    simp at hl
  | cons a as ih =>
    cases hA : evalLineF b a with
    | none => simp [prepareF, hA] at h
    | some z =>
      cases hRest : prepareF b as with
      | none => simp [prepareF, hA, hRest] at h
      | some zs =>
        have e : z :: zs = out := by simpa [prepareF, hA, hRest] using h
        subst e
        rcases List.mem_cons.mp hl with rfl | later
        · exact ⟨a, by simp, hA⟩
        · obtain ⟨raw, hm, check⟩ := ih _ hRest later
          exact ⟨raw, List.mem_cons_of_mem _ hm, check⟩

theorem prepareF_modes (b : Cell) (src : List AnchorRow) (out : List LineF) (h : prepareF b src = some out) :
    out.map LineF.mode = src.map AnchorRow.mode := by
  induction src generalizing out with
  | nil =>
    have e : ([] : List LineF) = out := Option.some.inj h
    subst e
    rfl
  | cons a as ih =>
    cases hA : evalLineF b a with
    | none => simp [prepareF, hA] at h
    | some z =>
      cases hRest : prepareF b as with
      | none => simp [prepareF, hA, hRest] at h
      | some zs =>
        have e : z :: zs = out := by simpa [prepareF, hA, hRest] using h
        subst e
        obtain ⟨_, t, _, rfl⟩ := evalLineF_eq b a z hA
        simp [ih zs hRest]

/-! ### Folds -/

theorem sumL_cast (f : LineF → ℤ) (ys : List LineF) :
    ((sumL f ys : ℤ) : ℚ) / S = (ys.map fun l => ((f l : ℤ) : ℚ) / S).sum := by
  induction ys with
  | nil => simp [sumL]
  | cons a as ih =>
    simp only [sumL, List.map_cons, List.sum_cons]
    push_cast
    rw [add_div, ih]

theorem toLine_mode (ys : List LineF) : (ys.map LineF.toLine).map Line.mode = ys.map LineF.mode := by
  simp [LineF.toLine, Function.comp_def]

theorem findLine_toLine (ys : List LineF) (nd : (ys.map LineF.mode).Nodup) (l : LineF) (hl : l ∈ ys) :
    findLine (ys.map LineF.toLine) l.mode = some l.toLine := by
  induction ys with
  | nil => simp at hl
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at nd
    obtain ⟨fresh, rest⟩ := nd
    rcases List.mem_cons.mp hl with rfl | later
    · simp [findLine, LineF.toLine]
    · have ne : a.mode ≠ l.mode := fun e => fresh (e ▸ List.mem_map.mpr ⟨l, later, rfl⟩)
      have ne' : a.toLine.mode ≠ l.mode := ne
      simp only [List.map_cons, findLine, ne', ite_false]
      exact ih rest later

theorem retained_sum (ys : List LineF) (nd : (ys.map LineF.mode).Nodup) {M : Type*} [AddCommMonoid M]
    (G : Mode → M) : (∑ m ∈ retained (ys.map LineF.toLine), G m) = (ys.map fun l => G l.mode).sum := by
  unfold retained
  rw [toLine_mode, List.sum_toFinset _ nd, List.map_map]
  rfl

theorem retained_sum_lines (ys : List LineF) (nd : (ys.map LineF.mode).Nodup) {M : Type*} [AddCommMonoid M]
    (G : Mode → Option Line → M) :
    (∑ m ∈ retained (ys.map LineF.toLine), G m (findLine (ys.map LineF.toLine) m)) =
      (ys.map fun l => G l.mode (some l.toLine)).sum := by
  rw [retained_sum ys nd]
  congr 1
  apply List.map_congr_left
  intro l hl
  rw [findLine_toLine ys nd l hl]

theorem intercept_retained (ys : List LineF) (nd : (ys.map LineF.mode).Nodup) :
    (∑ m ∈ retained (ys.map LineF.toLine), intercept (ys.map LineF.toLine) m) =
      ((sumL LineF.intercept ys : ℤ) : ℚ) / S := by
  rw [sumL_cast]
  exact retained_sum_lines ys nd (fun _ o => o.elim 0 Line.intercept)

theorem moments_eq (ys : List LineF) (nd : (ys.map LineF.mode).Nodup) :
    moments (retained (ys.map LineF.toLine)) (weight (ys.map LineF.toLine)) = momentsQ ys := by
  set xs := ys.map LineF.toLine
  set s := retained xs
  have w (l : LineF) (hl : l ∈ ys) : weight xs l.mode = (l.penalty : ℚ) / S := by
    simp [weight, xs, findLine_toLine ys nd l hl, LineF.toLine]
  have total (P : Mode → Prop) [DecidablePred P] (g : Mode → ℚ) (gz : LineF → ℤ)
      (hg : ∀ l ∈ ys, (l.penalty : ℚ) / S * g l.mode = ((gz l : ℤ) : ℚ) / S) :
      (∑ m ∈ s.filter P, weight xs m * g m) =
        ((sumL (fun l => if P l.mode then gz l else 0) ys : ℤ) : ℚ) / S := by
    rw [Finset.sum_filter, retained_sum ys nd, sumL_cast]
    congr 1
    apply List.map_congr_left
    intro l hl
    split_ifs
    · rw [w l hl, hg l hl]
    · simp
  unfold moments momentsQ
  congr 1
  · funext j
    exact total (fun m => m.family ≠ .reciprocal) _ _ (fun l _ => by
      simp [intMoment, imageMoment]; ring)
  · funext j
    exact total (fun m => m.family = .reciprocal) _ _ (fun l _ => by
      simp [intMoment, imageMoment]; ring)
  · funext i
    exact total (fun m => m.family = .cross) _ _ (fun l _ => by push_cast; ring)
  · have h := total (fun m => m.family = .cross) (fun _ => 1) (fun l => l.penalty) (fun l _ => by ring)
    simp only [mul_one] at h
    exact h

theorem listMax_ge_init (init : ℚ) (l : List ℚ) : init ≤ listMax init l := by
  induction l generalizing init with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left init x).trans (ih _)

theorem listMax_ge (init : ℚ) (l : List ℚ) (x : ℚ) (hx : x ∈ l) : x ≤ listMax init l := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | later
    · exact (le_max_right init x).trans (listMax_ge_init _ _)
    · exact ih _ later

theorem mem_shapeList : ∀ σ : Fin 5 → Bool, σ ∈ shapeList := by decide
theorem mem_offsetList : ∀ f : Fin 3 → Bool, f ∈ offsetList := by decide

theorem sixDot_eq (v w : Metric6) : sixDot v w = dot6 v w := by
  simp [sixDot, dot6, Fin.sum_univ_succ, add_assoc]

theorem shift_eq6 (g : Moments) (f : Fin 3 → ℚ) : g.shift f = shift6 g f := by
  funext j
  fin_cases j <;> rfl

theorem packedCorner_le_cornerMax (b : Cell) (g : Moments) (σ : Fin 5 → Bool) (f : Fin 3 → Bool) :
    packedCorner b g σ f ≤ cornerMax b g := by
  have e : packedCorner b g σ f =
      dot6 (primalMetric (shapePart b σ)) (shift6 g (offsetPart b f)) +
        dot6 (dualMetric (shapePart b σ)) g.reciprocal := by
    simp only [packedCorner, sixDot_eq, shift_eq6]
  rw [e]
  have inShape : dot6 (primalMetric (shapePart b σ)) (shift6 g (offsetPart b f)) +
      dot6 (dualMetric (shapePart b σ)) g.reciprocal ≤ shapeMax b g σ :=
    listMax_ge _ _ _ (List.mem_map.mpr ⟨f, mem_offsetList f, rfl⟩)
  exact inShape.trans (listMax_ge _ _ _ (List.mem_map.mpr ⟨σ, mem_shapeList σ, rfl⟩))

/-! ### The tangent route -/

theorem preparedModeF (b : Cell) (inputs : List AnchorRow) (ys : List LineF)
    (evals : prepareF b inputs = some ys) (nd : (ys.map LineF.mode).Nodup) (p : Chart) (hp : b.Mem p)
    (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) (m : Mode)
    (hm : m ∈ retained (ys.map LineF.toLine)) :
    m.valid ∧ 0 ≤ weight (ys.map LineF.toLine) m ∧ 0 ≤ residualAt (ys.map LineF.toLine) (chartPoint p) m ∧
      (intercept (ys.map LineF.toLine) m : ℝ) - (weight (ys.map LineF.toLine) m : ℝ) * m.radial (squarePoint p) ≤
        m.term (chartPoint p) - residualAt (ys.map LineF.toLine) (chartPoint p) m := by
  have hm' : m ∈ ys.map LineF.mode := by
    have := List.mem_toFinset.mp hm
    rwa [toLine_mode] at this
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm'
  obtain ⟨raw, _, value⟩ := prepareF_sound b inputs ys evals l hl
  obtain ⟨_, validated, nn, residual, bound⟩ := evalLineF_sound b raw l value p hp hd hv
  have found := findLine_toLine ys nd l hl
  have sp := Sz_pos
  refine ⟨validated, ?_, ?_, ?_⟩
  · simp only [weight, found, Option.elim, LineF.toLine]
    exact div_nonneg (by exact_mod_cast nn) (by norm_num [S])
  · simpa [residualAt, found] using residual
  · simp only [intercept, weight, residualAt, found, Option.elim, LineF.toLine]
    push_cast
    rw [S_eq]
    exact bound

theorem preparedLowerF (b : Cell) (inputs : List AnchorRow) (ys : List LineF)
    (evals : prepareF b inputs = some ys) (nd : (ys.map LineF.mode).Nodup) (p : Chart) (hp : b.Mem p)
    (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) :
    ((((sumL LineF.intercept ys : ℤ) : ℚ) / S - cornerMax b (momentsQ ys) : ℚ) : ℝ) +
      (∑ m ∈ retained (ys.map LineF.toLine), residualAt (ys.map LineF.toLine) (chartPoint p) m) ≤
        h₂ (chartPoint p) := by
  let xs := ys.map LineF.toLine
  let s := retained xs
  let upper := cornerMax b (moments s (weight xs))
  have info := preparedModeF b inputs ys evals nd p hp hd hv
  have cost := corner_upper b hd s (weight xs) (fun m hm => (info m hm).2.1) upper
    (fun bits => by rw [← packedCorner_eq]; exact packedCorner_le_cornerMax _ _ _ _) p hp
  have summed := Finset.sum_le_sum (fun m hm => (info m hm).2.2.2)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at summed
  have full := physical_sum_le s (chartPoint p) hv (fun m hm => (info m hm).1)
  have ic := intercept_retained ys nd
  have mo := moments_eq ys nd
  have icR : (∑ m ∈ s, (intercept xs m : ℝ)) = ((((sumL LineF.intercept ys : ℤ) : ℚ) / S : ℚ) : ℝ) := by
    rw [← ic]; push_cast; rfl
  have upR : (upper : ℝ) = (cornerMax b (momentsQ ys) : ℝ) := by
    simp only [upper, s, xs, mo]
  push_cast at icR ⊢
  rw [← upR]
  have e1 : ∑ m ∈ s, ((intercept xs m : ℚ) : ℝ) = ((sumL LineF.intercept ys : ℤ) : ℝ) / (S : ℝ) := icR
  linarith only [cost, summed, full, e1]

theorem keys_nodup (r : Proposal) (h : (r.selected.map modeKey).Nodup) :
    (r.selected.map AnchorRow.mode).Nodup := by
  have e : r.selected.map modeKey = (r.selected.map AnchorRow.mode).map modeKeyM := by
    simp [modeKey, Function.comp_def]
  rw [e] at h
  exact List.Nodup.of_map modeKeyM h

theorem thr_lt_energy (v : ℚ) (strict : (thrZ : ℚ) / S < v) (q : TwoSite) (bound : (v : ℝ) ≤ h₂ q) :
    energy fcc < energy q := by
  have thr := thr_sound
  have strictR : (thrZ : ℝ) / Sz < (v : ℝ) := by
    have h : (((thrZ : ℚ) / S : ℚ) : ℝ) < (v : ℝ) := by exact_mod_cast strict
    push_cast at h
    rwa [S_eq] at h
  change energy fcc < (h₂ q - 4) / (2 * ac)
  apply (lt_div_iff₀ (mul_pos two_pos ac_positive : (0:ℝ) < 2 * ac)).2
  linarith

/-! ### The integer corner fold -/

/-- The integer corner value is `2^160 R₁²R₂² S` times the corner value, with the
grid integers `R = 2^20 r` of the radial coordinates (so `2^240 r₁²r₂² S`). -/
theorem fold_cast (R1 R2 X Y Z : ℤ) (F : Fin 3 → ℤ) (D Rr : Fin 6 → ℤ) (L : Fin 3 → ℤ) (M : ℤ)
    (h1 : R1 ≠ 0) (h2 : R2 ≠ 0) :
    (((gridK * gridK * dotZ (primalZ R1 R2 X Y Z) (shiftZ D L M F) + dotZ (dualZ R1 R2 X Y Z) Rr : ℤ)) : ℚ) =
      ((gridK * gridK * (gridK * gridK) * (gridK * gridK * (gridK * gridK)) * (R1 * R1 * (R2 * R2)) : ℤ) : ℚ) *
        (S : ℚ) *
        (dot6 (primalMetric ![((R1 : ℚ) / gridK) ^ 2, ((R2 : ℚ) / gridK) ^ 2, (X : ℚ) / gridK,
            (Y : ℚ) / gridK, (Z : ℚ) / gridK, 0, 0, 0])
          (shift6 ⟨fun j => (D j : ℚ) / S, fun j => (Rr j : ℚ) / S, fun i => (L i : ℚ) / S, (M : ℚ) / S⟩
            ![(F 0 : ℚ) / gridK, (F 1 : ℚ) / gridK, (F 2 : ℚ) / gridK]) +
         dot6 (dualMetric ![((R1 : ℚ) / gridK) ^ 2, ((R2 : ℚ) / gridK) ^ 2, (X : ℚ) / gridK,
            (Y : ℚ) / gridK, (Z : ℚ) / gridK, 0, 0, 0]) (fun j => (Rr j : ℚ) / S)) := by
  have hK : ((gridK : ℤ) : ℚ) ≠ 0 := by norm_num [gridK]
  have hS : ((S : ℕ) : ℚ) ≠ 0 := by norm_num [S]
  have r1 : ((R1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h1
  have r2 : ((R2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h2
  simp only [dotZ, dot6, primalZ, dualZ, shiftZ, shift6, primalMetric, dualMetric, Matrix.cons_val]
  push_cast
  field_simp
  ring

theorem gz_cast {c : ℚ} (h : (c * gridK).den = 1) : ((gz c : ℤ) : ℚ) = c * gridK := by
  unfold gz
  exact Rat.coe_int_num_of_den_eq_one h

theorem gridOK_sound {b : Cell} (h : gridOK b = true) (i : Axis) :
    (b.lo i * gridK).den = 1 ∧ (b.hi i * gridK).den = 1 := by
  have e := List.all_eq_true.mp h i (List.mem_finRange i)
  simpa using e

theorem primalMetric_congr5 {p q : Axis → ℚ} (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2)
    (h3 : p 3 = q 3) (h4 : p 4 = q 4) : primalMetric p = primalMetric q := by
  simp only [primalMetric, h0, h1, h2, h3, h4]

theorem dualMetric_congr5 {p q : Axis → ℚ} (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2)
    (h3 : p 3 = q 3) (h4 : p 4 = q 4) : dualMetric p = dualMetric q := by
  simp only [dualMetric, h0, h1, h2, h3, h4]

/-- The grid coordinates of a corner, as rationals. -/
theorem corner_grid {b : Cell} (g : gridOK b = true) (bit : Bool) (i : Axis) :
    (((if bit then gz (b.hi i) else gz (b.lo i) : ℤ) : ℚ) / gridK) = if bit then b.hi i else b.lo i := by
  have hK : ((gridK : ℤ) : ℚ) ≠ 0 := by norm_num [gridK]
  obtain ⟨l, h⟩ := gridOK_sound g i
  cases bit
  · simp only [Bool.false_eq_true, ite_false]; rw [gz_cast l]; field_simp
  · simp only [ite_true]; rw [gz_cast h]; field_simp

theorem foldZ_sound (b : Cell) (ys : List LineF) (C : ℤ) (ok : foldZ b ys C = true)
    (σ : Fin 5 → Bool) (f : Fin 3 → Bool) : packedCorner b (momentsQ ys) σ f ≤ (C : ℚ) / S := by
  obtain ⟨head, all⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨pos, grid⟩ := Bool.and_eq_true_iff.mp head
  obtain ⟨l0, l1, u0, u1⟩ := of_decide_eq_true pos
  have hK : ((gridK : ℤ) : ℚ) ≠ 0 := by norm_num [gridK]
  have Kpos : (0 : ℚ) < ((gridK : ℤ) : ℚ) := by norm_num [gridK]
  have Spos : (0 : ℚ) < ((S : ℕ) : ℚ) := by norm_num [S]
  have ct := List.all_eq_true.mp all σ (mem_shapeList σ)
  unfold cornerTest at ct
  have xf := List.all_eq_true.mp ct _ (List.mem_map.mpr ⟨f, mem_offsetList f, rfl⟩)
  have ineq := of_decide_eq_true xf
  -- the shape coordinates on the grid
  have sh (i : Fin 5) : ((shapeZ b σ i : ℤ) : ℚ) / gridK =
      if σ i then b.hi ⟨i.val, by omega⟩ else b.lo ⟨i.val, by omega⟩ := by
    unfold shapeZ; exact corner_grid grid (σ i) ⟨i.val, by omega⟩
  have of (i : Fin 3) : ((offsetZ b f i : ℤ) : ℚ) / gridK = offsetPart b f i := by
    unfold offsetZ offsetPart; exact corner_grid grid (f i) (offset i)
  have pos0 : (0 : ℚ) < ((shapeZ b σ 0 : ℤ) : ℚ) := by
    have e := sh 0
    have c : (0 : ℚ) < if σ 0 then b.hi 0 else b.lo 0 := by split_ifs <;> assumption
    have q : (0 : ℚ) < ((shapeZ b σ 0 : ℤ) : ℚ) / gridK := e ▸ c
    have m := mul_pos q Kpos
    rwa [div_mul_cancel₀ _ hK] at m
  have pos1 : (0 : ℚ) < ((shapeZ b σ 1 : ℤ) : ℚ) := by
    have e := sh 1
    have c : (0 : ℚ) < if σ 1 then b.hi 1 else b.lo 1 := by split_ifs <;> assumption
    have q : (0 : ℚ) < ((shapeZ b σ 1 : ℤ) : ℚ) / gridK := e ▸ c
    have m := mul_pos q Kpos
    rwa [div_mul_cancel₀ _ hK] at m
  have n0 : shapeZ b σ 0 ≠ 0 := by exact_mod_cast pos0.ne'
  have n1 : shapeZ b σ 1 ≠ 0 := by exact_mod_cast pos1.ne'
  have key := fold_cast (shapeZ b σ 0) (shapeZ b σ 1) (shapeZ b σ 2) (shapeZ b σ 3) (shapeZ b σ 4)
    (offsetZ b f) (directZ ys) (recipZ ys) (linearZ ys) (massZ ys) n0 n1
  -- the corner value in the form of `fold_cast`
  have shape : shapePart b σ 0 = (((shapeZ b σ 0 : ℤ) : ℚ) / gridK) ^ 2 ∧
      shapePart b σ 1 = (((shapeZ b σ 1 : ℤ) : ℚ) / gridK) ^ 2 ∧
      shapePart b σ 2 = ((shapeZ b σ 2 : ℤ) : ℚ) / gridK ∧
      shapePart b σ 3 = ((shapeZ b σ 3 : ℤ) : ℚ) / gridK ∧
      shapePart b σ 4 = ((shapeZ b σ 4 : ℤ) : ℚ) / gridK := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [shapePart, squaredCorner, cornerRat] <;>
      first
        | (rw [sh 0]; simp)
        | (rw [sh 1]; simp)
        | (rw [sh 2]; simp)
        | (rw [sh 3]; simp)
        | (rw [sh 4]; simp)
  obtain ⟨s0, s1, s2, s3, s4⟩ := shape
  have offs : offsetPart b f = ![((offsetZ b f 0 : ℤ) : ℚ) / gridK, ((offsetZ b f 1 : ℤ) : ℚ) / gridK,
      ((offsetZ b f 2 : ℤ) : ℚ) / gridK] := by
    funext i; fin_cases i <;> simp [of]
  have corner : packedCorner b (momentsQ ys) σ f =
      dot6 (primalMetric ![(((shapeZ b σ 0 : ℤ) : ℚ) / gridK) ^ 2, (((shapeZ b σ 1 : ℤ) : ℚ) / gridK) ^ 2,
          ((shapeZ b σ 2 : ℤ) : ℚ) / gridK, ((shapeZ b σ 3 : ℤ) : ℚ) / gridK,
          ((shapeZ b σ 4 : ℤ) : ℚ) / gridK, 0, 0, 0])
        (shift6 ⟨fun j => (directZ ys j : ℚ) / S, fun j => (recipZ ys j : ℚ) / S,
          fun i => (linearZ ys i : ℚ) / S, (massZ ys : ℚ) / S⟩
          ![((offsetZ b f 0 : ℤ) : ℚ) / gridK, ((offsetZ b f 1 : ℤ) : ℚ) / gridK,
            ((offsetZ b f 2 : ℤ) : ℚ) / gridK]) +
      dot6 (dualMetric ![(((shapeZ b σ 0 : ℤ) : ℚ) / gridK) ^ 2, (((shapeZ b σ 1 : ℤ) : ℚ) / gridK) ^ 2,
          ((shapeZ b σ 2 : ℤ) : ℚ) / gridK, ((shapeZ b σ 3 : ℤ) : ℚ) / gridK,
          ((shapeZ b σ 4 : ℤ) : ℚ) / gridK, 0, 0, 0]) (fun j => (recipZ ys j : ℚ) / S) := by
    simp only [packedCorner, sixDot_eq, shift_eq6]
    rw [primalMetric_congr5 (q := ![(((shapeZ b σ 0 : ℤ) : ℚ) / gridK) ^ 2, (((shapeZ b σ 1 : ℤ) : ℚ) / gridK) ^ 2,
          ((shapeZ b σ 2 : ℤ) : ℚ) / gridK, ((shapeZ b σ 3 : ℤ) : ℚ) / gridK,
          ((shapeZ b σ 4 : ℤ) : ℚ) / gridK, 0, 0, 0]) s0 s1 s2 s3 s4,
      dualMetric_congr5 (q := ![(((shapeZ b σ 0 : ℤ) : ℚ) / gridK) ^ 2, (((shapeZ b σ 1 : ℤ) : ℚ) / gridK) ^ 2,
          ((shapeZ b σ 2 : ℤ) : ℚ) / gridK, ((shapeZ b σ 3 : ℤ) : ℚ) / gridK,
          ((shapeZ b σ 4 : ℤ) : ℚ) / gridK, 0, 0, 0]) s0 s1 s2 s3 s4, offs]
    rfl
  rw [corner, le_div_iff₀ Spos]
  have cast := (Int.cast_le (R := ℚ)).mpr ineq
  rw [key] at cast
  push_cast at cast
  have K8 : (0 : ℚ) < ((gridK : ℤ) : ℚ) * gridK * (gridK * gridK) * (gridK * gridK * (gridK * gridK)) :=
    mul_pos (mul_pos (mul_pos Kpos Kpos) (mul_pos Kpos Kpos)) (mul_pos (mul_pos Kpos Kpos) (mul_pos Kpos Kpos))
  have big : (0 : ℚ) < ((gridK : ℤ) : ℚ) * gridK * (gridK * gridK) * (gridK * gridK * (gridK * gridK)) *
      (((shapeZ b σ 0 : ℤ) : ℚ) * (shapeZ b σ 0 : ℤ) * (((shapeZ b σ 1 : ℤ) : ℚ) * (shapeZ b σ 1 : ℤ))) :=
    mul_pos K8 (mul_pos (mul_pos pos0 pos0) (mul_pos pos1 pos1))
  nlinarith [cast, big]

/-- `preparedLowerF` with any corner bound `u` of the integer moments. -/
theorem preparedLowerU (b : Cell) (inputs : List AnchorRow) (ys : List LineF)
    (evals : prepareF b inputs = some ys) (nd : (ys.map LineF.mode).Nodup) (p : Chart) (hp : b.Mem p)
    (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) (u : ℚ)
    (hu : ∀ σ f, packedCorner b (momentsQ ys) σ f ≤ u) :
    ((((sumL LineF.intercept ys : ℤ) : ℚ) / S - u : ℚ) : ℝ) +
      (∑ m ∈ retained (ys.map LineF.toLine), residualAt (ys.map LineF.toLine) (chartPoint p) m) ≤
        h₂ (chartPoint p) := by
  let xs := ys.map LineF.toLine
  let s := retained xs
  have info := preparedModeF b inputs ys evals nd p hp hd hv
  have mo := moments_eq ys nd
  have cost := corner_upper b hd s (weight xs) (fun m hm => (info m hm).2.1) u
    (fun bits => by rw [← packedCorner_eq, mo]; exact hu _ _) p hp
  have summed := Finset.sum_le_sum (fun m hm => (info m hm).2.2.2)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at summed
  have full := physical_sum_le s (chartPoint p) hv (fun m hm => (info m hm).1)
  have ic := intercept_retained ys nd
  have icR : (∑ m ∈ s, (intercept xs m : ℝ)) = ((((sumL LineF.intercept ys : ℤ) : ℚ) / S : ℚ) : ℝ) := by
    rw [← ic]; push_cast; rfl
  push_cast at icR ⊢
  linarith only [cost, summed, full, icR]

/-- The plain tangent route: the conclusion of `Stage2.bulkCheck_sound`. -/
theorem bulkFix_sound (b : Cell) (r : Proposal) (p : Chart) (hp : b.Mem p)
    (hv : (chartPoint p).Valid) (ok : bulkFix b r = true) : energy fcc < energy (chartPoint p) := by
  unfold bulkFix at ok
  obtain ⟨data, work⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨_, keys⟩ := Bool.and_eq_true_iff.mp data
  obtain ⟨hd, compare⟩ := Bool.and_eq_true_iff.mp work
  have nd0 := keys_nodup r (of_decide_eq_true keys)
  cases evals : prepareF b r.selected with
  | none => simp [evals] at compare
  | some ys =>
    have fold : foldZ b ys (sumL LineF.intercept ys - thrZ - 1) = true := by simpa [evals] using compare
    have nd : (ys.map LineF.mode).Nodup := by rw [prepareF_modes b _ ys evals]; exact nd0
    have bound := preparedLowerU b r.selected ys evals nd p hp hd hv _ (foldZ_sound b ys _ fold)
    have nn := Finset.sum_nonneg (fun m hm => (preparedModeF b r.selected ys evals nd p hp hd hv m hm).2.2.1)
    have Spos : (0 : ℚ) < S := by norm_num [S]
    have e : ((sumL LineF.intercept ys : ℤ) : ℚ) / S - ((sumL LineF.intercept ys - thrZ - 1 : ℤ) : ℚ) / S =
        ((thrZ : ℚ) + 1) / S := by push_cast; field_simp; ring
    refine thr_lt_energy (((thrZ : ℚ) + 1) / S) (div_lt_div_of_pos_right (by linarith) Spos) _ ?_
    rw [← e]
    exact (le_add_of_nonneg_right nn).trans bound

/-! ### The phase-budget route -/

theorem waveUpperL_ge (b : Cell) (n : IntVec) (σ : Fin 5 → Bool) :
    dualCorner (shapePart b σ) n ≤ waveUpperL b n :=
  listMax_ge _ _ _ (List.mem_map.mpr ⟨σ, mem_shapeList σ, rfl⟩)

theorem waveUpperL_sound (b : Cell) (p : Chart) (n : IntVec) (hp : b.Mem p) (hd : diagonalsCheck b = true) :
    quad (gram (chartBasis p))⁻¹ (castVec n) ≤ (waveUpperL b n : ℝ) := by
  obtain ⟨h0, h1⟩ := radialLoPos b hd
  have p0 := h0.trans_le (hp 0).1
  have p1 := h1.trans_le (hp 1).1
  rw [← dualRadial_eq n p p0.ne' p1.ne']
  obtain ⟨bits, upper⟩ := corner_le (squareDiag b) (fun q => -dualRadial n q) (dualRadial_chord n b hd) _
    (squarePoint_mem hp hd)
  have eq : (⟨.reciprocal, n⟩ : Mode).atCorner b bits = dualCorner (shapePart b (selectShape bits)) n := by
    norm_num [Mode.atCorner, dualCorner, shapePart, selectShape, squaredCorner, cornerRat]
  have cmp := waveUpperL_ge b n (selectShape bits)
  have value := Mode.atCorner_eq b bits ⟨.reciprocal, n⟩
  rw [eq] at value
  have radial : Mode.radial ⟨.reciprocal, n⟩ (corner (squareDiag b) bits) =
      dualRadial n (corner (squareDiag b) bits) := rfl
  rw [radial] at value
  calc dualRadial n (squarePoint p) ≤ dualRadial n (corner (squareDiag b) bits) := neg_le_neg_iff.mp upper
    _ = (dualCorner (shapePart b (selectShape bits)) n : ℝ) := value.symm
    _ ≤ (waveUpperL b n : ℝ) := Rat.cast_le.mpr cmp

theorem capacityF_sound (b : Cell) (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b = true)
    (hv : (chartPoint p).Valid) (m : Mode) (valid : m.valid) (dual : m.family = .reciprocal) :
    (capacityF b m : ℝ) / Sz ≤ 2 * seriesReciprocalTerm (chartPoint p) m.index := by
  have sp := Sz_pos
  have npos : lexPositive m.index := valid.2.resolve_left (by simp [dual])
  have strict : 0 < quad (gram (chartBasis p))⁻¹ (castVec m.index) := reciprocalPositive hv (lex_ne npos)
  have up := waveUpperL_sound b p m.index hp hd
  have uQ (u : ℚ) : (u : ℝ) ≤ ((cdivZ (u.num * Sz) (u.den : ℤ) : ℤ) : ℝ) / Sz := by
    have c := le_cdiv (u.num * Sz) (u.den : ℤ) (by exact_mod_cast u.pos)
    rw [le_div_iff₀ sp]
    refine le_trans (le_of_eq ?_) c
    rw [Rat.cast_def]
    push_cast
    ring
  have T := piTimes_sound strict.le (up.trans (uQ _))
  have one := oneLowF_sound _ (mul_pos Real.pi_pos strict) T
  have term : seriesReciprocalTerm (chartPoint p) m.index =
      gKernel 1 (Real.pi * quad (gram (chartBasis p))⁻¹ (castVec m.index)) := by
    rw [seriesReciprocalTerm, ite_eq_right (lex_ne npos)]; rfl
  have G0 : 0 ≤ gKernel 1 (Real.pi * quad (gram (chartBasis p))⁻¹ (castVec m.index)) := by
    rw [gKernel_one (mul_pos Real.pi_pos strict)]; positivity
  unfold capacityF
  dsimp only
  rw [term]
  rcases le_total (2 * oneLowF (piTimes (cdivZ ((waveUpperL b m.index).num * Sz)
      ((waveUpperL b m.index).den : ℤ)))) 0 with h | h
  · rw [max_eq_left h]; simp only [Int.cast_zero, zero_div]; positivity
  · rw [max_eq_right h]; push_cast; rw [mul_div_assoc]; linarith

theorem budgetF_sound (b : Cell) (ys : List LineF) (budget : Array Allocation)
    (checked : budgetCheckF b (ys.map LineF.toLine) budget = true)
    (inputs : List AnchorRow) (evaluation : prepareF b inputs = some ys) (nd : (ys.map LineF.mode).Nodup)
    (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) :
    (budgetGain (ys.map LineF.toLine) budget : ℝ) ≤
      ∑ m ∈ retained (ys.map LineF.toLine), residualAt (ys.map LineF.toLine) (chartPoint p) m := by
  let xs := ys.map LineF.toLine
  let q := chartPoint p
  let s := retained xs
  let gap (m : Mode) := phaseFactor q m.index - (floorAt xs m : ℝ)
  have valid : ∀ i : Fin budget.size, budget[i].valid s := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1
  have caps : ∀ m ∈ s, capCheckF b budget m = true := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2
  have incidence (i : Fin budget.size) :
      (budget[i].amount : ℝ) * (3/2 - ∑ m ∈ budget[i].members, (floorAt xs m : ℝ)) ≤
        ∑ m ∈ s, if m ∈ budget[i].members then (budget[i].amount : ℝ) * gap m else 0 := by
    let a := budget[i]
    have lower := a.phaseFloor s (valid i) q
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_right lower (∑ m ∈ a.members, (floorAt xs m : ℝ)))
      (by exact_mod_cast (valid i).1 : (0:ℝ) ≤ a.amount)
    have incl : s.filter (fun m => m ∈ a.members) = a.members := by
      ext m
      exact ⟨fun e => (Finset.mem_filter.mp e).2, fun e => Finset.mem_filter.mpr ⟨(valid i).2.1 e, e⟩⟩
    rw [← Finset.sum_sub_distrib, Finset.mul_sum] at h
    rw [← Finset.sum_filter, incl]
    exact h
  have distribute : (∑ i : Fin budget.size, ∑ m ∈ s, if m ∈ budget[i].members then
      (budget[i].amount : ℝ) * gap m else 0) = ∑ m ∈ s, (spent budget m : ℝ) * gap m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    unfold spent
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have perMode (m : Mode) (hm : m ∈ s) : (spent budget m : ℝ) * gap m ≤ residualAt xs q m := by
    have info := preparedModeF b inputs ys evaluation nd p hp hd hv m hm
    by_cases used : spent budget m = 0
    · simpa [used] using info.2.2.1
    · have dual : m.family = .reciprocal := by
        by_contra no
        apply used
        unfold spent
        apply Finset.sum_eq_zero
        intro i _
        have nope : m ∉ budget[i].members := by
          intro h
          have e : m = wave budget[i].a ∨ m = wave budget[i].b ∨ m = wave budget[i].c := by
            simpa [Allocation.members] using h
          rcases e with rfl | rfl | rfl <;> exact no rfl
        exact ite_eq_right nope
      obtain ⟨line, found⟩ := existsLine xs m (List.mem_toFinset.mp hm)
      have modeEq := (findLine_sound xs m line found).2
      have formula : residualAt xs q m = 2 * gap m * seriesReciprocalTerm q m.index := by
        simp [residualAt, floorAt, found, Line.residual, modeEq, dual, gap]
      have pos := reciprocalPositive hv (lex_ne (info.1.2.resolve_left (by simp [dual])))
      have gpos : 0 < seriesReciprocalTerm q m.index := by
        have hn := lex_ne (info.1.2.resolve_left (by simp [dual]))
        rw [seriesReciprocalTerm, ite_eq_right hn, gKernel_one (mul_pos Real.pi_pos pos)]
        exact div_pos (Real.exp_pos _) (mul_pos Real.pi_pos pos)
      have nn : 0 ≤ gap m := by
        by_contra! e
        have hneg := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num : (0:ℝ) < 2) e) gpos
        exact (not_lt_of_ge (formula ▸ info.2.2.1)) hneg
      have paid : spent budget m ≤ (capacityF b m : ℚ) / S :=
        of_decide_eq_true (by simpa [capCheckF, used] using caps m hm)
      have paidR : (spent budget m : ℝ) ≤ (capacityF b m : ℝ) / Sz := by
        have h := Rat.cast_le (K := ℝ) |>.mpr paid
        push_cast at h
        rwa [S_eq] at h
      have upper := paidR.trans (capacityF_sound b p hp hd hv m info.1 dual)
      rw [formula]
      have credit := mul_le_mul_of_nonneg_right upper nn
      linarith only [credit]
  unfold budgetGain
  push_cast
  exact (Finset.sum_le_sum (fun i _ => incidence i)).trans (distribute ▸ Finset.sum_le_sum (fun m hm => perMode m hm))

theorem checkedBudgetF_sound (b : Cell) (ys : List LineF) (budget : Array Allocation) (value : ℚ)
    (ok : checkedBudgetF b (ys.map LineF.toLine) budget = some value) (inputs : List AnchorRow)
    (evaluation : prepareF b inputs = some ys) (nd : (ys.map LineF.mode).Nodup)
    (p : Chart) (hp : b.Mem p) (hd : diagonalsCheck b = true) (hv : (chartPoint p).Valid) :
    (value : ℝ) ≤ ∑ m ∈ retained (ys.map LineF.toLine), residualAt (ys.map LineF.toLine) (chartPoint p) m := by
  unfold checkedBudgetF at ok
  by_cases initial : budgetCheckF b (ys.map LineF.toLine) budget = true
  · rw [ite_eq_left initial] at ok
    rw [← Option.some.inj ok]
    exact budgetF_sound b ys budget initial inputs evaluation nd p hp hd hv
  · rw [ite_eq_right initial] at ok
    dsimp only at ok
    by_cases accepted : budgetCheckF b (ys.map LineF.toLine) (shrinkBudgetF b (ys.map LineF.toLine) budget) = true
    · rw [ite_eq_left accepted] at ok
      rw [← Option.some.inj ok]
      exact budgetF_sound b ys _ accepted inputs evaluation nd p hp hd hv
    · rw [ite_eq_right accepted] at ok
      cases ok

/-- The phase-budget route: the conclusion of `Stage2.phaseCheck_sound`. -/
theorem phaseFix_sound (b : Cell) (r : Proposal) (budget : Array Allocation) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) (ok : phaseFix b r budget = true) :
    energy fcc < energy (chartPoint p) := by
  unfold phaseFix at ok
  obtain ⟨data, work⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨_, keys⟩ := Bool.and_eq_true_iff.mp data
  obtain ⟨hd, compare⟩ := Bool.and_eq_true_iff.mp work
  have nd0 := keys_nodup r (of_decide_eq_true keys)
  cases evals : prepareF b r.selected with
  | none => simp [evals] at compare
  | some ys =>
    have nd : (ys.map LineF.mode).Nodup := by rw [prepareF_modes b _ ys evals]; exact nd0
    cases cap : checkedBudgetF b (ys.map LineF.toLine) budget with
    | none => simp [evals, cap] at compare
    | some gain =>
      have fold : foldZ b ys (sumL LineF.intercept ys - thrZ - 1 + ⌊gain * S⌋) = true := by
        simpa [evals, cap] using compare
      have base := preparedLowerU b r.selected ys evals nd p hp hd hv _ (foldZ_sound b ys _ fold)
      have g := checkedBudgetF_sound b ys budget gain cap r.selected evals nd p hp hd hv
      have fl := Int.floor_le (gain * S)
      have Spos : (0 : ℚ) < S := by norm_num [S]
      have e : ((sumL LineF.intercept ys : ℤ) : ℚ) / S -
          ((sumL LineF.intercept ys - thrZ - 1 + ⌊gain * S⌋ : ℤ) : ℚ) / S + gain =
            ((thrZ : ℚ) + 1 - ⌊gain * S⌋ + gain * S) / S := by push_cast; field_simp; ring
      refine thr_lt_energy (((sumL LineF.intercept ys : ℤ) : ℚ) / S -
          ((sumL LineF.intercept ys - thrZ - 1 + ⌊gain * S⌋ : ℤ) : ℚ) / S + gain) ?_ _ ?_
      · rw [e]; exact div_lt_div_of_pos_right (by linarith) Spos
      · rw [Rat.cast_add]
        linarith

end BccSharp.Coulomb.CompactCover.Stage2Fix
