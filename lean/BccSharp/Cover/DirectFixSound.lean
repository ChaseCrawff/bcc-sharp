import BccSharp.Cover.DirectFix
import BccSharp.Cover.OverlayFixSound

set_option autoImplicit false

/-! Soundness of the fixed-point direct evaluator `BccSharp.Cover.DirectFix`.

* The literal constants: the `erfc` Horner coefficients and denominator
  against their formulas (`erfPosC_eq`, `erfNegC_eq`, `erfDS_eq`, `erfL_dvd`,
  by `decide +kernel`), `erfHorner_eq` (the Horner value is
  `S^95 95! L · Erfc.series (T/S) 96`), `sqrtPiLo_le`, `erfErr_ok`, `acLo_le`
  and the threshold `thr_sound : 4 + 2 a_c e_FCC ≤ thrZ/S`.
* Scalars: `halfLowF_sound` (through `Erfc.sqrt_remainder` and
  `halfKernel_formula`), `oneLowF_sound` (through the Overlay `expNegPt_mem`),
  `piTimes_sound` and `phaseLowF_sound` (through `cosRange_mem`).
* The box: `realDistF_mem` and `recipDistF_mem` (the shapes of
  `DirectRoute.realDistance_sound` and `reciprocalDistance_sound`), the three
  families (`crossF_sound`, `periodF_sound`, `recipF_sound`), `valueF_sound`
  (against `finite_lower`) and `directFix_sound`, with the conclusion of
  `DirectRoute.check_sound`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.DirectFix
open BccSharp BccSharp.Coverage DirectRoute OverlayPlanar.Fix BravaisCover

/-! ### The `erfc` series constants -/

/-- `S^(95-k) (95!/k!) (L/(2k+1))`. -/
def erfCoef (k : ℕ) : ℕ := S ^ (95 - k) * (Nat.factorial 95 / Nat.factorial k) * (erfL / (2 * k + 1))

theorem erfPosC_eq : erfPosC = (List.range 48).reverse.map (fun i => erfCoef (2 * i)) := by
  decide +kernel
theorem erfNegC_eq : erfNegC = (List.range 48).reverse.map (fun i => erfCoef (2 * i + 1)) := by
  decide +kernel
theorem erfDS_eq : erfDS * S = S ^ 95 * Nat.factorial 95 * erfL := by decide +kernel
theorem erfL_mod : ∀ k < 96, erfL % (2 * k + 1) = 0 := by decide +kernel

theorem erfL_dvd (k : ℕ) (hk : k < 96) : 2 * k + 1 ∣ erfL := Nat.dvd_of_mod_eq_zero (erfL_mod k hk)

theorem neg_one_pow_even (i : ℕ) : ((-1 : ℝ)) ^ (2 * i) = 1 := by rw [pow_mul]; simp
theorem neg_one_pow_odd (i : ℕ) : ((-1 : ℝ)) ^ (2 * i + 1) = -1 := by rw [pow_succ, pow_mul]; simp

/-- The Horner value is `S^95 95! L` times `Erfc.series (T/S) 96`. -/
theorem erfHorner_eq (T : ℕ) :
    ((hornerN (T * T) erfPosC : ℕ) : ℝ) - ((T * hornerN (T * T) erfNegC : ℕ) : ℝ) =
      ((S ^ 95 * Nat.factorial 95 * erfL : ℕ) : ℝ) * (Erfc.series ((T : ℚ) / S) 96 : ℝ) := by
  have s0 : (S : ℝ) ≠ 0 := by norm_num [S]
  rw [hornerN_eq, hornerN_eq, erfPosC_eq, erfNegC_eq, hornerVal_range, hornerVal_range]
  unfold Erfc.series
  rw [show (96 : ℕ) = 2 * 48 from rfl, sum_range_two_mul]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 47 := by simp only [Finset.mem_range] at hi; omega
  unfold erfCoef
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity),
    Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity),
    Nat.cast_div (erfL_dvd (2 * i) (by omega)) (by positivity),
    Nat.cast_div (erfL_dvd (2 * i + 1) (by omega)) (by positivity)]
  push_cast
  rw [neg_pow, neg_pow ((T : ℝ) / (S : ℝ)) (2 * i + 1), neg_one_pow_even, neg_one_pow_odd,
    pow_sub₀ _ s0 (by omega), pow_sub₀ _ s0 (by omega), div_pow, div_pow]
  field_simp
  ring

theorem sqrtPiLo_le : (sqrtPiLo : ℝ) / Sz ≤ Real.sqrt Real.pi := by
  have p := Real.pi_gt_d20
  have h : ((sqrtPiLo : ℝ) / Sz) ^ 2 ≤ Real.pi := by
    refine le_trans ?_ p.le
    rw [div_pow, div_le_iff₀ (by norm_num [Sz])]
    norm_num [sqrtPiLo, Sz]
  exact (Real.le_sqrt (div_nonneg (Nat.cast_nonneg _) Sz_pos.le) Real.pi_pos.le).mpr h

theorem fact96 : Nat.factorial 96 =
    991677934870949689209571401541893801158183648651267795444376054838492222809091499987689476037000748982075094738965754305639874560000000000000000000000 := by decide

theorem erfErr_ok : (4 : ℝ) * 24 ^ 96 / (Nat.factorial 96 : ℝ) ≤ (erfErr : ℝ) / Sz := by
  rw [fact96, div_le_div_iff₀ (by positivity) Sz_pos]
  norm_num [erfErr, Sz]

/-! ### The half kernel -/

theorem half_nonneg {x : ℝ} (h : 0 < x) : 0 ≤ gKernel (1/2) x := by
  rw [halfKernel_formula h]
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Ewald.erfc_nonneg _)) (Real.sqrt_nonneg _)

theorem halfTMax_eq : (halfTMax : ℝ) = 24 * (Sz : ℝ) := by norm_num [halfTMax, Sz]

/-- The real-number core: `√π/√t - 2 series - 4 t^96/96! ≤ G(1/2, t)`. -/
theorem half_series_lower {q : ℚ} (q0 : 0 < q) (q24 : q ≤ 24) :
    Real.sqrt Real.pi / Real.sqrt (q : ℝ) - 2 * (Erfc.series q 96 : ℝ) -
      4 * (q : ℝ) ^ 96 / (Nat.factorial 96 : ℝ) ≤ gKernel (1/2) (q : ℝ) := by
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
  have lower := (abs_le.mp rem).1
  set E := Gaussian.erfcIntegral (Real.sqrt (q : ℝ))
  set s := Real.sqrt (q : ℝ)
  set P := Real.sqrt Real.pi
  set z := (Erfc.series q 96 : ℝ)
  have hE : 1 - 2 * s / P * z - 4 * s * (q : ℝ) ^ 96 / (P * (Nat.factorial 96 : ℝ)) ≤ E := by
    linarith
  calc P / s - 2 * z - 4 * (q : ℝ) ^ 96 / (Nat.factorial 96 : ℝ)
      = P / s * (1 - 2 * s / P * z - 4 * s * (q : ℝ) ^ 96 / (P * (Nat.factorial 96 : ℝ))) := by
        field_simp
    _ ≤ P / s * E := mul_le_mul_of_nonneg_left hE (div_nonneg sp.le sq.le)
    _ = P * E / s := by ring

theorem halfLowF_le_at (T : ℕ) (hT : 0 < T ∧ T ≤ halfTMax) :
    (halfLowF T : ℝ) / Sz ≤ gKernel (1/2) ((T : ℝ) / Sz) := by
  have sp := Sz_pos
  set q : ℚ := (T : ℚ) / S with hq
  have qt : ((q : ℚ) : ℝ) = (T : ℝ) / Sz := by rw [hq]; push_cast; rw [S_eq]
  have q0 : 0 < q := by rw [hq]; exact div_pos (by exact_mod_cast hT.1) (by norm_num [S])
  have q24 : q ≤ 24 := by
    have h : ((T : ℕ) : ℝ) ≤ 24 * (Sz : ℝ) := by rw [← halfTMax_eq]; exact_mod_cast hT.2
    have : ((q : ℚ) : ℝ) ≤ 24 := by rw [qt, div_le_iff₀ sp]; exact h
    exact_mod_cast this
  have core := half_series_lower q0 q24
  rw [qt] at core
  have G0 := half_nonneg (div_pos (by exact_mod_cast hT.1 : (0:ℝ) < T) sp)
  unfold halfLowF
  rw [ite_eq_left hT]
  dsimp only
  set R := sqrtHi (T * S) with hR
  set A : ℕ := sqrtPiLo * S / R with hA
  set acc : ℤ := (hornerN (T * T) erfPosC : ℤ) - ((T * hornerN (T * T) erfNegC : ℕ) : ℤ) with hacc
  set B : ℤ := cdivZ acc (erfDS : ℤ) with hB
  -- the leading term
  have tpos : (0 : ℝ) < (T : ℝ) / Sz := div_pos (by exact_mod_cast hT.1) sp
  have RR := le_sqrtHi_sq (T * S)
  have R0 : (0 : ℝ) < R := by
    have : 0 < T * S := Nat.mul_pos hT.1 S_pos
    have h1 : 0 < R * R := lt_of_lt_of_le this RR
    have : 0 < R := Nat.pos_of_mul_pos_left h1
    exact_mod_cast this
  have sR : Real.sqrt ((T : ℝ) / Sz) * Sz ≤ R := by
    have e : Real.sqrt ((T : ℝ) / Sz) * Sz = Real.sqrt ((T : ℝ) * Sz) := by
      rw [show (T : ℝ) * Sz = (T : ℝ) / Sz * Sz ^ 2 by field_simp,
        Real.sqrt_mul' _ (by positivity), Real.sqrt_sq sp.le]
    have c : ((T * S : ℕ) : ℝ) ≤ ((R * R : ℕ) : ℝ) := by exact_mod_cast RR
    push_cast at c
    rw [S_eq] at c
    rw [e]
    calc Real.sqrt ((T : ℝ) * Sz) ≤ Real.sqrt ((R : ℝ) * R) := Real.sqrt_le_sqrt c
      _ = R := Real.sqrt_mul_self R0.le
  have lead : (A : ℝ) / Sz ≤ Real.sqrt Real.pi / Real.sqrt ((T : ℝ) / Sz) := by
    have st := Real.sqrt_pos.mpr tpos
    have a1 : (A : ℝ) ≤ (sqrtPiLo : ℝ) * S / R := by
      rw [hA]; exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := sqrtPiLo * S) (n := R))
    calc (A : ℝ) / Sz ≤ (sqrtPiLo : ℝ) * S / R / Sz := div_le_div_of_nonneg_right a1 sp.le
      _ = ((sqrtPiLo : ℝ) / Sz) / ((R : ℝ) / Sz) := by rw [S_eq]; field_simp
      _ ≤ Real.sqrt Real.pi / ((R : ℝ) / Sz) :=
          div_le_div_of_nonneg_right sqrtPiLo_le (div_pos R0 sp).le
      _ ≤ Real.sqrt Real.pi / Real.sqrt ((T : ℝ) / Sz) := by
          apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) st
          rw [le_div_iff₀ sp]; exact sR
  -- the series term
  have accR : (acc : ℝ) = ((S ^ 95 * Nat.factorial 95 * erfL : ℕ) : ℝ) *
      (Erfc.series ((T : ℚ) / S) 96 : ℝ) := by
    rw [hacc, ← erfHorner_eq T]; push_cast; ring
  have DS : ((erfDS : ℤ) : ℝ) * Sz = ((S ^ 95 * Nat.factorial 95 * erfL : ℕ) : ℝ) := by
    rw [← S_eq]; push_cast; exact_mod_cast erfDS_eq
  have DS0 : (0 : ℤ) < erfDS := by norm_num [erfDS]
  have serB : (Erfc.series q 96 : ℝ) ≤ (B : ℝ) / Sz := by
    have c := le_cdiv acc (erfDS : ℤ) DS0
    rw [← hB] at c
    have e : (acc : ℝ) / ((erfDS : ℤ) : ℝ) = (Erfc.series q 96 : ℝ) * Sz := by
      rw [accR, ← DS, hq]; field_simp
    rw [e] at c
    rw [le_div_iff₀ sp]; exact c
  -- the truncation allowance
  have errB : 4 * ((T : ℝ) / Sz) ^ 96 / (Nat.factorial 96 : ℝ) ≤ (erfErr : ℝ) / Sz := by
    refine le_trans ?_ erfErr_ok
    have t24 : (T : ℝ) / Sz ≤ 24 := by rw [← qt]; exact_mod_cast q24
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ tpos.le t24 96) (by norm_num)
  have total : (((A : ℤ) - 2 * B - erfErr : ℤ) : ℝ) / Sz ≤ gKernel (1/2) ((T : ℝ) / Sz) := by
    push_cast
    rw [sub_div, sub_div, mul_div_assoc]
    linarith
  rcases le_total ((A : ℤ) - 2 * B - erfErr) 0 with h | h
  · rw [max_eq_left h]; simpa using G0
  · rw [max_eq_right h]; exact_mod_cast total

theorem halfLowF_sound (T : ℕ) {x : ℝ} (hx : 0 < x) (hT : x ≤ (T : ℝ) / Sz) :
    (halfLowF T : ℝ) / Sz ≤ gKernel (1/2) x := by
  by_cases h : 0 < T ∧ T ≤ halfTMax
  · exact (halfLowF_le_at T h).trans (halfKernel_decreasing hx hT)
  · have e : halfLowF T = 0 := by unfold halfLowF; rw [ite_eq_right h]
    rw [e]
    simpa using half_nonneg hx

/-! ### The reciprocal kernel and the phase -/

theorem oneLowF_sound (T : ℕ) {x : ℝ} (hx : 0 < x) (hT : x ≤ (T : ℝ) / Sz) :
    (oneLowF T : ℝ) / Sz ≤ gKernel 1 x := by
  have sp := Sz_pos
  have G0 : 0 ≤ gKernel 1 x := by rw [gKernel_one hx]; exact div_nonneg (Real.exp_pos _).le hx.le
  unfold oneLowF
  split_ifs with h
  · have tpos : (0 : ℝ) < (T : ℝ) / Sz := hx.trans_le hT
    have T0 : (0 : ℤ) < (T : ℤ) := by exact_mod_cast h
    have mono := oneKernel_decreasing hx hT
    rw [gKernel_one tpos] at mono
    refine le_trans ?_ mono
    have e := (expNegPt_mem T).1
    have f := fdiv_le ((expNegPt T).lo * Sz) (T : ℤ) T0
    have TR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast h
    calc (((expNegPt T).lo * Sz / (T : ℤ) : ℤ) : ℝ) / Sz
        ≤ ((((expNegPt T).lo * Sz : ℤ) : ℝ) / ((T : ℤ) : ℝ)) / Sz := div_le_div_of_nonneg_right f sp.le
      _ = ((expNegPt T).lo : ℝ) / Sz / ((T : ℝ) / Sz) := by push_cast; field_simp
      _ ≤ Real.exp (-((T : ℝ) / Sz)) / ((T : ℝ) / Sz) := div_le_div_of_nonneg_right e tpos.le
  · simpa using G0

theorem piTimes_sound {Q : ℤ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ (Q : ℝ) / Sz) :
    Real.pi * y ≤ (piTimes Q : ℝ) / Sz := by
  have sp := Sz_pos
  have Q0 : (0 : ℝ) ≤ Q := by
    have := hy0.trans hy
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd sp (not_lt.mpr h.2))
  have tp := twoPi_bounds.2
  have d0 : (0 : ℤ) < 2 * Sz := by norm_num [Sz]
  have c := le_cdiv (twoPiHi * Q) (2 * Sz) d0
  have tn : ((cdivZ (twoPiHi * Q) (2 * Sz) : ℤ) : ℝ) ≤ ((piTimes Q : ℕ) : ℝ) := by
    unfold piTimes; exact_mod_cast Int.self_le_toNat _
  calc Real.pi * y ≤ Real.pi * ((Q : ℝ) / Sz) := mul_le_mul_of_nonneg_left hy Real.pi_pos.le
    _ = (2 * Real.pi) * (Q : ℝ) / (2 * Sz) := by field_simp
    _ ≤ ((twoPiHi : ℝ) / Sz) * (Q : ℝ) / (2 * Sz) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right tp Q0
    _ = (((twoPiHi * Q : ℤ) : ℝ) / ((2 * Sz : ℤ) : ℝ)) / Sz := by push_cast; field_simp
    _ ≤ ((piTimes Q : ℕ) : ℝ) / Sz := div_le_div_of_nonneg_right (c.trans tn) sp.le

theorem turnsF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (n : IntVec) :
    (turnsF b n).Mem (dot (castVec n) (chartPoint p).offset) := by
  convert FI.add_mem (FI.smul_mem (n 0) (cx_mem hp 5))
    (FI.add_mem (FI.smul_mem (n 1) (cx_mem hp 6)) (FI.smul_mem (n 2) (cx_mem hp 7))) using 1
  · rfl
  · simp [dot, castVec, chartPoint, Fin.sum_univ_three]
    ring

theorem phaseLowF_sound {b : Cell} {p : Chart} (hp : b.Mem p) (n : IntVec) :
    0 ≤ phaseLowF b n ∧
      (phaseLowF b n : ℝ) / Sz ≤ 1 + Real.cos (2 * Real.pi * dot (castVec n) (chartPoint p).offset) := by
  have sp := Sz_pos
  have c := cosRange_mem (A := (turnsF b n).lo) (B := (turnsF b n).hi) (turnsF_mem hp n)
  have nn : (0 : ℝ) ≤ 1 + Real.cos (2 * Real.pi * dot (castVec n) (chartPoint p).offset) := by
    linarith [Real.neg_one_le_cos (2 * Real.pi * dot (castVec n) (chartPoint p).offset)]
  unfold phaseLowF
  dsimp only
  refine ⟨le_max_left _ _, ?_⟩
  rcases le_total (Sz + (cosRange (turnsF b n).lo (turnsF b n).hi).lo) 0 with h | h
  · rw [max_eq_left h]; simpa using nn
  · rw [max_eq_right h]
    push_cast
    rw [add_div, div_self sp.ne']
    linarith [c.1]

/-! ### Distances on the box -/

theorem guards_sound {b : Cell} (g : guardsF b = true) :
    0 < (cx b 0).lo ∧ 0 < (cx b 1).lo ∧ 0 < (FI.mulPos (cx b 0) (cx b 1)).lo := of_decide_eq_true g

theorem radial_pos {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true) :
    0 < p 0 ∧ 0 < p 1 := by
  obtain ⟨h0, h1, _⟩ := guards_sound g
  exact ⟨(div_pos (by exact_mod_cast h0) Sz_pos).trans_le (cx_mem hp 0).1,
    (div_pos (by exact_mod_cast h1) Sz_pos).trans_le (cx_mem hp 1).1⟩

theorem vecF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (cross : Bool) (n : IntVec) (i : Fin 3) :
    (vecF b cross n i).Mem (chartVector p cross n i) := by
  cases cross
  · simpa [vecF, chartVector, castVec] using FI.ofInt_mem (n i)
  · simpa [vecF, chartVector, castVec, offset_eq] using FI.add_mem (FI.ofInt_mem (n i)) (cx_mem hp (offset i))

theorem realDistF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true) (cross : Bool)
    (n : IntVec) : (realDistF b cross n).Mem (quad (gram (chartBasis p)) (chartVector p cross n)) := by
  have gs := guards_sound g
  have t i := vecF_mem hp cross n i
  have r := cx_mem hp 0
  have s := cx_mem hp 1
  have a := FI.mul_mem (cx_mem hp 2) (t 1)
  have c := FI.mul_mem (cx_mem hp 3) (t 2)
  have u := FI.mul_mem r (FI.add_mem (t 0) (FI.add_mem a c))
  have w := FI.mul_mem s (FI.add_mem (t 1) (FI.mul_mem (cx_mem hp 4) (t 2)))
  have z := FI.mul_mem (FI.invPos_mem gs.2.2 (FI.mulPos_mem r s)) (t 2)
  rw [← sq_mulVec_gram]
  convert FI.add_mem (FI.sq_mem u) (FI.add_mem (FI.sq_mem w) (FI.sq_mem z)) using 1
  · rfl
  · simp [sq, chartBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem recipDistF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true) (n : IntVec) :
    (recipDistF b n).Mem (quad (gram (chartBasis p))⁻¹ (castVec n)) := by
  have gs := guards_sound g
  have r := cx_mem hp 0
  have s := cx_mem hp 1
  have a := cx_mem hp 2
  have c := cx_mem hp 4
  have u := FI.smul_mem (n 0) (FI.invPos_mem gs.1 r)
  have v := FI.mul_mem (FI.sub_mem (FI.ofInt_mem (n 1)) (FI.smul_mem (n 0) a)) (FI.invPos_mem gs.2.1 s)
  have z := FI.add_mem (FI.sub_mem (FI.ofInt_mem (n 2)) (FI.smul_mem (n 1) c))
    (FI.smul_mem (n 0) (FI.sub_mem (FI.mul_mem a c) (cx_mem hp 3)))
  obtain ⟨rpos, spos⟩ := radial_pos hp g
  have chart : normalizedChart (takeShape p) = chartBasis p := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [dual_quad, ← chart, ← dualVector_eq (takeShape p) rpos.ne' spos.ne']
  convert FI.add_mem (FI.sq_mem u) (FI.add_mem (FI.sq_mem v)
    (FI.sq_mem (FI.mul_mem z (FI.mulPos_mem r s)))) using 1
  · rfl
  · simp [sq, dualVector, takeShape, Fin.sum_univ_three]
    ring

/-! ### The three families -/

theorem crossF_sound {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true)
    (hq : (chartPoint p).Valid) (n : IntVec) :
    (crossF b n : ℝ) / Sz ≤ seriesCrossTerm (chartPoint p) n := by
  have d := realDistF_mem hp g true n
  have pos := cross_distance_positive hq n
  exact halfLowF_sound _ (mul_pos Real.pi_pos pos) (piTimes_sound pos.le d.2)

theorem periodF_sound {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true)
    (hq : (chartPoint p).Valid) (n : IntVec) (hn : lexPositive n) :
    (periodF b n : ℝ) / Sz ≤ seriesDirectTerm (chartPoint p) n := by
  have d := realDistF_mem hp g false n
  have pos := period_distance_positive hq n hn
  rw [seriesDirectTerm, ite_eq_right (lex_ne hn)]
  exact halfLowF_sound _ (mul_pos Real.pi_pos pos) (piTimes_sound pos.le d.2)

theorem recipF_sound {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true)
    (hq : (chartPoint p).Valid) (n : IntVec) (hn : lexPositive n) :
    (recipF b n : ℝ) / Sz ≤ pairedTerm (chartPoint p) n := by
  have sp := Sz_pos
  rw [pairedTerm_eq]
  obtain ⟨φ0, φ⟩ := phaseLowF_sound hp n
  have d := recipDistF_mem hp g n
  have pos := reciprocalPositive hq (lex_ne hn)
  have pos' : 0 < quad (gram (chartBasis p))⁻¹ (castVec n) := pos
  have one := oneLowF_sound (piTimes (recipDistF b n).hi) (mul_pos Real.pi_pos pos') (piTimes_sound pos'.le d.2)
  have term : seriesReciprocalTerm (chartPoint p) n =
      gKernel 1 (Real.pi * quad (gram (chartBasis p))⁻¹ (castVec n)) := by
    rw [seriesReciprocalTerm, ite_eq_right (lex_ne hn)]; rfl
  have G0 : 0 ≤ gKernel 1 (Real.pi * quad (gram (chartBasis p))⁻¹ (castVec n)) := by
    rw [gKernel_one (mul_pos Real.pi_pos pos')]; positivity
  set O := max 0 (oneLowF (piTimes (recipDistF b n).hi)) with hO
  have O0 : (0 : ℤ) ≤ O := le_max_left _ _
  have Ole : (O : ℝ) / Sz ≤ gKernel 1 (Real.pi * quad (gram (chartBasis p))⁻¹ (castVec n)) := by
    rcases le_total (oneLowF (piTimes (recipDistF b n).hi)) 0 with h | h
    · rw [hO, max_eq_left h]; simpa using G0
    · rw [hO, max_eq_right h]; exact one
  have nn : (0 : ℝ) ≤ 1 + Real.cos (2 * Real.pi * dot (castVec n) (chartPoint p).offset) :=
    le_trans (div_nonneg (by exact_mod_cast φ0) sp.le) φ
  rw [term]
  unfold recipF
  rw [← hO]
  calc ((phaseLowF b n * O / Sz : ℤ) : ℝ) / Sz
      ≤ (((phaseLowF b n * O : ℤ) : ℝ) / Sz) / Sz := div_le_div_of_nonneg_right (fdiv_le _ _ Sz_posZ) sp.le
    _ = ((phaseLowF b n : ℝ) / Sz) * ((O : ℝ) / Sz) := by push_cast; field_simp
    _ ≤ _ := mul_le_mul φ Ole (div_nonneg (by exact_mod_cast O0) sp.le) nn

/-! ### The finite sum and the pass -/

theorem sumZ_sound (f : IntVec → ℤ) (v : IntVec → ℝ) (l : List IntVec) (nd : l.Nodup)
    (h : ∀ n ∈ l, (f n : ℝ) / Sz ≤ v n) : (sumZ f l : ℝ) / Sz ≤ ∑ n ∈ l.toFinset, v n := by
  induction l with
  | nil => simp [sumZ]
  | cons a ns ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp nd
    rw [sumZ, List.toFinset_cons, Finset.sum_insert (by simpa using fresh)]
    push_cast
    rw [add_div]
    exact add_le_add (h a (by simp)) (ih rest (fun n hn => h n (List.mem_cons_of_mem _ hn)))

theorem valueF_sound {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true)
    (hq : (chartPoint p).Valid) (radius : ℕ)
    (nd : (directIndices radius).Nodup ∧ (pairedIndices radius).Nodup) :
    (valueF b radius : ℝ) / Sz ≤ h₂ (chartPoint p) := by
  let q := chartPoint p
  let half := (pairedIndices radius).toFinset
  have pos (n : IntVec) (hn : n ∈ pairedIndices radius) : lexPositive n :=
    of_decide_eq_true (List.mem_filter.mp hn).2
  have pos' (n : IntVec) (hn : n ∈ half) : lexPositive n := pos n (List.mem_toFinset.mp hn)
  have hC := sumZ_sound (crossF b) (seriesCrossTerm q) _ nd.1 (fun n _ => crossF_sound hp g hq n)
  have hS := sumZ_sound (periodF b) (seriesDirectTerm q) _ nd.2
    (fun n hn => periodF_sound hp g hq n (pos n hn))
  have hR := sumZ_sound (recipF b) (pairedTerm q) _ nd.2
    (fun n hn => recipF_sound hp g hq n (pos n hn))
  have pS : 2 * ((sumZ (periodF b) (pairedIndices radius) : ℝ) / Sz) ≤
      ∑ n ∈ bothSigns half, seriesDirectTerm q n := by
    rw [← sum_pairs half pos' _ (even_direct q), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS (by norm_num)
  have rS : 2 * ((sumZ (recipF b) (pairedIndices radius) : ℝ) / Sz) ≤
      ∑ n ∈ bothSigns half, pairedTerm q n := by
    rw [← sum_pairs half pos' _ (even_pair q), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hR (by norm_num)
  have hFull := finite_lower q hq (bothSigns half) (directIndices radius).toFinset (bothSigns half)
  unfold valueF
  push_cast
  rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
  linarith

theorem radius_nodup_one : (directIndices 1).Nodup ∧ (pairedIndices 1).Nodup := by decide +kernel
theorem radius_nodup_two : (directIndices 2).Nodup ∧ (pairedIndices 2).Nodup := by decide +kernel

/-! ### The threshold -/

theorem acLo_pos : (0 : ℝ) < acLo := by norm_num [acLo]

theorem acLo_cube : (acLo : ℝ) ^ 3 ≤ 8 * Real.pi / 3 := by
  have p := Real.pi_gt_d20
  have h : (acLo : ℝ) ^ 3 ≤ 8 * 3.14159265358979323846 / 3 := by norm_num [acLo]
  linarith

theorem acLo_le : (acLo : ℝ) ≤ ac := by
  unfold ac
  have h0 : (0 : ℝ) ≤ (acLo : ℝ) ^ 3 := pow_nonneg acLo_pos.le 3
  calc (acLo : ℝ) = ((acLo : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul acLo_pos.le]; norm_num
    _ ≤ (8 * Real.pi / 3) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow h0 acLo_cube (by norm_num)

theorem thr_sound : 4 + 2 * ac * energy fcc ≤ (thrZ : ℝ) / Sz := by
  have fccHi : energy fcc ≤ (Constants.fccBracket.hi : ℝ) := (Constants.reference_bounds .fcc).2
  have negative : (Constants.fccBracket.hi : ℝ) ≤ 0 := by norm_num [Constants.fccBracket]
  have e1 := mul_le_mul_of_nonneg_left fccHi (mul_nonneg (by norm_num) ac_positive.le : (0:ℝ) ≤ 2 * ac)
  have e2 := mul_le_mul_of_nonpos_right
    (mul_le_mul_of_nonneg_left acLo_le (by norm_num : (0:ℝ) ≤ 2)) negative
  have e3 : 4 + 2 * (acLo : ℝ) * (Constants.fccBracket.hi : ℝ) ≤ (thrZ : ℝ) / Sz := by
    rw [le_div_iff₀ Sz_pos]
    norm_num [acLo, thrZ, Sz, Constants.fccBracket]
  linarith

/-- The pass: the conclusion of `DirectRoute.check_sound`. -/
theorem directFix_sound {b : Cell} (ok : directFix b = true) {p : Chart} (hp : b.Mem p)
    (hq : (chartPoint p).Valid) : energy fcc < energy (chartPoint p) := by
  obtain ⟨g, cmp⟩ := Bool.and_eq_true_iff.mp ok
  have key : ∃ radius, ((directIndices radius).Nodup ∧ (pairedIndices radius).Nodup) ∧
      thrZ < valueF b radius := by
    rcases Bool.or_eq_true_iff.mp cmp with h | h
    · exact ⟨1, radius_nodup_one, of_decide_eq_true h⟩
    · exact ⟨2, radius_nodup_two, of_decide_eq_true h⟩
  obtain ⟨radius, nd, lt⟩ := key
  have bound := valueF_sound hp g hq radius nd
  have ltR : (thrZ : ℝ) / Sz < (valueF b radius : ℝ) / Sz :=
    div_lt_div_of_pos_right (by exact_mod_cast lt) Sz_pos
  have thr := thr_sound
  change energy fcc < (h₂ (chartPoint p) - 4) / (2 * ac)
  apply (lt_div_iff₀ (mul_pos two_pos ac_positive : (0:ℝ) < 2 * ac)).2
  linarith

end BccSharp.Coulomb.CompactCover.DirectFix
