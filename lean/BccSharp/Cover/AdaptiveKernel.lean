import BccSharp.Cover.AdaptiveConst
import BccSharp.Cover.OverlayFixSound
import BccSharp.Cover.AdaptiveLogTangent

set_option autoImplicit false

/-! Fixed-point enclosures of the two Series kernels and their slopes at a dyadic anchor.

An anchor is a natural `A`; it stands for `T = A / RA` with `RA = 2^62`. All values
are integer intervals `FI` at the scale `S = 2^96` of `BccSharp.Cover.OverlayFix`.

* `halfG A` encloses `G(1/2, T) = gKernel (1/2) T`. It uses
  `G(1/2, T) = √(π/T) - 2 Σ_{k<2m} (-T)^k/(k!(2k+1)) ± 4 T^(2m)/(2m)!` (`Erfc.sqrt_remainder`
  with `halfKernel_formula`), with `2m ∈ {48, 64, 88, 112, 128}` terms by the size of `T`
  (`halfTerms`). The alternating sum is computed exactly, as two Horner values over `ℕ` in
  `A²` with the literal coefficients of `BccSharp.Cover.AdaptiveConst` over the common denominator
  `halfD`, and divided once.
* `oneG A` encloses `G(1, T) = e^{-T}/T` (`gKernel_one`).
* `halfW A` and `oneW A` enclose `W = (e^{-T} + a G(a, T))/T` (`a = 1/2`, `1`), the negated
  slope that `logTangent` uses.

`e^{-T}` is `expNegPt (A · 2^66)` of the Overlay evaluator, since `T · S = A · 2^34`. -/

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BravaisCover OverlayPlanar.Fix

/-! ### Checked constants -/

def posDen (i : ℕ) : ℕ := RA ^ (2 * i) * Nat.factorial (2 * i) * (4 * i + 1)
def negDen (i : ℕ) : ℕ := RA ^ (2 * i + 1) * Nat.factorial (2 * i + 1) * (4 * i + 3)

theorem posDen_dvd : ∀ i < 64, posDen i ∣ halfD := by decide +kernel
theorem negDen_dvd : ∀ i < 64, negDen i ∣ halfD := by decide +kernel
theorem halfPosC_eq : halfPosC = (List.range 64).reverse.map (fun i => halfD / posDen i) := by
  decide +kernel
theorem halfNegC_eq : halfNegC = (List.range 64).reverse.map (fun i => halfD / negDen i) := by
  decide +kernel
theorem RA_eq : RA = 2 ^ 62 := by decide +kernel

theorem RA_pos : (0:ℝ) < RA := by norm_num [RA]
theorem halfD_posN : 0 < halfD := by decide +kernel
theorem halfD_pos : (0:ℝ) < halfD := by exact_mod_cast halfD_posN

/-- `piLoN / S ≤ π ≤ piHiN / S`, from the Constants enclosure of `π`. -/
theorem piLo_check : ((piLoN : ℚ) / S) ≤ Constants.piInput.mid - Constants.piInput.rad := by decide +kernel
theorem piHi_check : Constants.piInput.mid + Constants.piInput.rad ≤ ((piHiN : ℚ) / S) := by decide +kernel

theorem pi_bounds : (piLoN : ℝ) / S ≤ Real.pi ∧ Real.pi ≤ (piHiN : ℝ) / S := by
  have h := Constants.piInput_sound
  unfold Intervals.Ball.Contains at h
  rw [abs_le] at h
  have lo : (((piLoN : ℚ) / S : ℚ) : ℝ) ≤ ((Constants.piInput.mid - Constants.piInput.rad : ℚ) : ℝ) :=
    Rat.cast_le.mpr piLo_check
  have hi : ((Constants.piInput.mid + Constants.piInput.rad : ℚ) : ℝ) ≤ (((piHiN : ℚ) / S : ℚ) : ℝ) :=
    Rat.cast_le.mpr piHi_check
  push_cast at lo hi
  constructor <;> linarith [h.1, h.2]

/-! ### Term counts -/

/-- Horner length per parity (`2m` series terms) for the anchor `A`. -/
def halfTerms (A : ℕ) : ℕ :=
  if A ≤ 2 * RA then 24 else if A ≤ 6 * RA then 32 else if A ≤ 12 * RA then 44
  else if A ≤ 20 * RA then 56 else 64

/-- `RA^(2m) (2m)!` for the five term counts. -/
def remDenOf (m : ℕ) : ℕ :=
  if m = 24 then remDen24 else if m = 32 then remDen32 else if m = 44 then remDen44
  else if m = 56 then remDen56 else remDen

theorem remDenOf_eq (A : ℕ) :
    remDenOf (halfTerms A) = RA ^ (2 * halfTerms A) * Nat.factorial (2 * halfTerms A) := by
  have h24 : remDen24 = RA ^ 48 * Nat.factorial 48 := by decide +kernel
  have h32 : remDen32 = RA ^ 64 * Nat.factorial 64 := by decide +kernel
  have h44 : remDen44 = RA ^ 88 * Nat.factorial 88 := by decide +kernel
  have h56 : remDen56 = RA ^ 112 * Nat.factorial 112 := by decide +kernel
  have h64 : remDen = RA ^ 128 * Nat.factorial 128 := by decide +kernel
  unfold halfTerms
  split_ifs <;> simp [remDenOf, h24, h32, h44, h56, h64]

theorem halfTerms_le (A : ℕ) : halfTerms A ≤ 64 := by
  unfold halfTerms; split_ifs <;> norm_num

theorem halfTerms_guard (A : ℕ) (h : 2 * A ≤ 129 * RA) : 2 * A ≤ (2 * halfTerms A + 1) * RA := by
  unfold halfTerms; split_ifs <;> omega

/-- The coefficient lists of `m ≤ 64` terms per parity: the last `m` entries. -/
def posList (m : ℕ) : List ℕ := halfPosC.drop (64 - m)
def negList (m : ℕ) : List ℕ := halfNegC.drop (64 - m)

theorem drop_range_map (f : ℕ → ℕ) : ∀ (n m : ℕ), m ≤ n →
    ((List.range n).reverse.map f).drop (n - m) = (List.range m).reverse.map f
  | n, m, h => by
    induction n with
    | zero =>
      have : m = 0 := by omega
      subst this; rfl
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le h with e | lt
      · subst e; simp
      · rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.map_cons, show n + 1 - m = (n - m) + 1 by omega, List.drop_succ_cons]
        exact ih (by omega)

theorem posList_eq {m : ℕ} (hm : m ≤ 64) :
    posList m = (List.range m).reverse.map (fun i => halfD / posDen i) := by
  unfold posList; rw [halfPosC_eq]; exact drop_range_map _ 64 m hm

theorem negList_eq {m : ℕ} (hm : m ≤ 64) :
    negList m = (List.range m).reverse.map (fun i => halfD / negDen i) := by
  unfold negList; rw [halfNegC_eq]; exact drop_range_map _ 64 m hm

/-! ### The half-kernel series -/

theorem posDen_pos (i : ℕ) : 0 < posDen i := by unfold posDen RA; positivity
theorem negDen_pos (i : ℕ) : 0 < negDen i := by unfold negDen RA; positivity

/-- The `2m`-term series of `Erfc.series` at `A / RA`, times `halfD`. -/
theorem halfSeries_eq {m : ℕ} (hm : m ≤ 64) (A : ℕ) :
    ((hornerN (A * A) (posList m) : ℕ) : ℝ) - ((A * hornerN (A * A) (negList m) : ℕ) : ℝ) =
      (halfD : ℝ) * ((Erfc.series ((A : ℚ) / RA) (2 * m) : ℚ) : ℝ) := by
  have r0 : (RA : ℝ) ≠ 0 := RA_pos.ne'
  rw [hornerN_eq, hornerN_eq, posList_eq hm, negList_eq hm, hornerVal_range, hornerVal_range]
  unfold Erfc.series
  rw [sum_range_two_mul]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < 64 := lt_of_lt_of_le (Finset.mem_range.mp hi) hm
  rw [Nat.cast_div (posDen_dvd i hi') (Nat.cast_ne_zero.mpr (posDen_pos i).ne'),
    Nat.cast_div (negDen_dvd i hi') (Nat.cast_ne_zero.mpr (negDen_pos i).ne')]
  unfold posDen negDen
  push_cast
  have m1 : ((-((A : ℝ) / RA))) ^ (2 * i) = ((A : ℝ) / RA) ^ (2 * i) := by
    rw [pow_mul, pow_mul, neg_sq]
  have m2 : ((-((A : ℝ) / RA))) ^ (2 * i + 1) = -((A : ℝ) / RA) ^ (2 * i + 1) := by
    rw [pow_succ, pow_succ, m1]; ring
  rw [m1, m2, div_pow, div_pow]
  have f1 : (0:ℝ) < Nat.factorial (2 * i) := by exact_mod_cast Nat.factorial_pos _
  have f2 : (0:ℝ) < Nat.factorial (2 * i + 1) := by exact_mod_cast Nat.factorial_pos _
  rw [show ((A : ℝ) * A) ^ i = (A : ℝ) ^ (2 * i) by rw [← pow_two, ← pow_mul]]
  field_simp
  ring

/-! ### Fixed-point kernel values -/

/-- `T · S = A · 2^34`. -/
def scaleUp : ℕ := 17179869184

theorem scaleUp_eq : (scaleUp : ℝ) * RA = S := by norm_num [scaleUp, RA, S]

theorem S_pos' : (0:ℝ) < S := by norm_num [S]

/-- `e^{-T} S`, enclosed. -/
def expT (A : ℕ) : FI := expNegPt (A * scaleUp)

theorem expT_mem (A : ℕ) : (expT A).Mem (Real.exp (-((A : ℝ) / RA))) := by
  have h := expNegPt_mem (A * scaleUp)
  have e : ((A * scaleUp : ℕ) : ℝ) / Sz = (A : ℝ) / RA := by
    rw [← S_eq, ← scaleUp_eq]
    push_cast
    rw [mul_comm (A : ℝ), mul_div_mul_left _ _ (by norm_num [scaleUp] : (scaleUp:ℝ) ≠ 0)]
  rw [e] at h
  exact h

/-- `G(1/2, A/RA)`, at scale `S`, with `m` Horner terms per parity. -/
def halfGm (m A : ℕ) : FI :=
  let Z : ℤ := ((hornerN (A * A) (posList m) : ℕ) : ℤ) - ((A * hornerN (A * A) (negList m) : ℕ) : ℤ)
  let serLo : ℤ := Z * Sz / (halfD : ℤ)
  let serHi : ℤ := cdivZ (Z * Sz) (halfD : ℤ)
  let sqLo : ℤ := ((sqrtLo (piLoN * RA * S / A) : ℕ) : ℤ)
  let sqHi : ℤ := ((sqrtHi (cdivN (piHiN * RA * S) A) : ℕ) : ℤ)
  let rem : ℤ := ((cdivN (4 * A ^ (2 * m) * S) (remDenOf m) : ℕ) : ℤ)
  ⟨sqLo - 2 * serHi - rem, sqHi - 2 * serLo + rem⟩

/-- `G(1/2, A/RA)`, at scale `S`. -/
def halfG (A : ℕ) : FI := halfGm (halfTerms A) A

/-- The guard of the anchor: `0 < T ≤ 64.5`. -/
def anchorGuard (A : ℕ) : Bool := decide (0 < A) && decide (2 * A ≤ 129 * RA)

theorem halfKernel_near {m A : ℕ} (hA : 0 < A) (guard : 2 * A ≤ (2 * m + 1) * RA) :
    |gKernel (1/2) ((A : ℝ) / RA) -
        (Real.sqrt (Real.pi / ((A : ℝ) / RA)) - 2 * ((Erfc.series ((A : ℚ) / RA) (2 * m) : ℚ) : ℝ))| ≤
      4 * ((A : ℝ) / RA) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
  set q : ℚ := (A : ℚ) / RA with hq
  have q0 : 0 ≤ q := by positivity
  have qR : ((q : ℚ) : ℝ) = (A : ℝ) / RA := by rw [hq]; push_cast; rfl
  have hguard : q / ((2 * m + 1 : ℕ) : ℚ) ≤ 1 / 2 := by
    rw [hq, div_div, div_le_iff₀ (by norm_num [RA]; positivity)]
    have : (2 * A : ℚ) ≤ (2 * m + 1) * RA := by exact_mod_cast guard
    push_cast
    linarith
  have rem := Erfc.sqrt_remainder q0 (2 * m) hguard
  rw [qR] at rem
  set t : ℝ := (A : ℝ) / RA with ht
  have tpos : 0 < t := by rw [ht]; exact div_pos (by exact_mod_cast hA) RA_pos
  set E := Gaussian.erfcIntegral (Real.sqrt t)
  set ser := ((Erfc.series q (2 * m) : ℚ) : ℝ)
  have a0 := Real.sqrt_pos.mpr Real.pi_pos
  have b0 := Real.sqrt_pos.mpr tpos
  have key : gKernel (1/2) t - (Real.sqrt (Real.pi / t) - 2 * ser) =
      (Real.sqrt Real.pi / Real.sqrt t) * (E - (1 - 2 * Real.sqrt t / Real.sqrt Real.pi * ser)) := by
    rw [halfKernel_formula tpos, Real.sqrt_div Real.pi_pos.le]
    field_simp
    ring
  rw [key, abs_mul, abs_of_pos (div_pos a0 b0)]
  calc Real.sqrt Real.pi / Real.sqrt t * |E - (1 - 2 * Real.sqrt t / Real.sqrt Real.pi * ser)|
      ≤ Real.sqrt Real.pi / Real.sqrt t *
          (4 * Real.sqrt t * t ^ (2 * m) / (Real.sqrt Real.pi * (Nat.factorial (2 * m) : ℝ))) :=
        mul_le_mul_of_nonneg_left rem (div_pos a0 b0).le
    _ = 4 * t ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
        field_simp

/-- Floor and ceiling of `Z S / D`, against `Z / D`. -/
theorem fdivS_le (Z : ℤ) {D : ℕ} (hD : 0 < D) :
    ((Z * Sz / (D : ℤ) : ℤ) : ℝ) / Sz ≤ (Z : ℝ) / D := by
  have f := fdiv_le (Z * Sz) (D : ℤ) (by exact_mod_cast hD)
  have sp := Sz_pos
  have Dp : (0:ℝ) < D := by exact_mod_cast hD
  rw [div_le_div_iff₀ sp Dp]
  have g := (le_div_iff₀ Dp).mp (f.trans (le_of_eq (by push_cast; rfl)))
  linarith

theorem le_cdivS (Z : ℤ) {D : ℕ} (hD : 0 < D) :
    (Z : ℝ) / D ≤ ((cdivZ (Z * Sz) (D : ℤ) : ℤ) : ℝ) / Sz := by
  have f := le_cdiv (Z * Sz) (D : ℤ) (by exact_mod_cast hD)
  have sp := Sz_pos
  have Dp : (0:ℝ) < D := by exact_mod_cast hD
  rw [div_le_div_iff₀ Dp sp]
  have g := (div_le_iff₀ Dp).mp ((le_of_eq (by push_cast; rfl)).trans f)
  linarith

theorem halfZ_eq {m : ℕ} (hm : m ≤ 64) (A : ℕ) :
    ((((hornerN (A * A) (posList m) : ℕ) : ℤ) - ((A * hornerN (A * A) (negList m) : ℕ) : ℤ) : ℤ) : ℝ) /
        halfD = ((Erfc.series ((A : ℚ) / RA) (2 * m) : ℚ) : ℝ) := by
  have h := halfSeries_eq hm A
  have e : ((((hornerN (A * A) (posList m) : ℕ) : ℤ) - ((A * hornerN (A * A) (negList m) : ℕ) : ℤ) : ℤ) : ℝ) =
      ((hornerN (A * A) (posList m) : ℕ) : ℝ) - ((A * hornerN (A * A) (negList m) : ℕ) : ℝ) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  rw [e, h]
  field_simp [halfD_pos.ne']

theorem sqrtLo_le {A : ℕ} (hA : 0 < A) :
    ((sqrtLo (piLoN * RA * S / A) : ℕ) : ℝ) / Sz ≤ Real.sqrt (Real.pi / ((A : ℝ) / RA)) := by
  set N := piLoN * RA * S / A
  set u : ℝ := ((sqrtLo N : ℕ) : ℝ) with hu
  have sp := Sz_pos
  have Ap : (0:ℝ) < A := by exact_mod_cast hA
  have r2 : u * u ≤ (N : ℝ) := by rw [hu]; exact_mod_cast sqrtLo_sq N
  have d : (N : ℝ) ≤ ((piLoN * RA * S : ℕ) : ℝ) / A := fdivN_le _ _
  have pl : (piLoN : ℝ) ≤ Real.pi * S := by
    have := pi_bounds.1
    rwa [div_le_iff₀ S_pos'] at this
  have bound : ((piLoN * RA * S : ℕ) : ℝ) / A ≤ Real.pi / ((A : ℝ) / RA) * (Sz : ℝ) ^ 2 := by
    rw [← S_eq]
    push_cast
    rw [div_le_iff₀ Ap]
    have e : Real.pi / ((A : ℝ) / RA) * (S : ℝ) ^ 2 * A = Real.pi * S * RA * S := by
      field_simp [RA_pos.ne']
    rw [e]
    have := mul_le_mul_of_nonneg_right pl (by positivity : (0:ℝ) ≤ (RA : ℝ) * S)
    nlinarith [this]
  have u0 : 0 ≤ u / Sz := div_nonneg (Nat.cast_nonneg _) sp.le
  rw [Real.le_sqrt u0 (div_nonneg Real.pi_pos.le (div_nonneg Ap.le RA_pos.le)), div_pow,
    div_le_iff₀ (pow_pos sp 2)]
  calc u ^ 2 = u * u := by ring
    _ ≤ _ := r2.trans (d.trans bound)

theorem le_sqrtHi {A : ℕ} (hA : 0 < A) :
    Real.sqrt (Real.pi / ((A : ℝ) / RA)) ≤ ((sqrtHi (cdivN (piHiN * RA * S) A) : ℕ) : ℝ) / Sz := by
  set M := cdivN (piHiN * RA * S) A
  set v : ℝ := ((sqrtHi M : ℕ) : ℝ) with hv
  have sp := Sz_pos
  have Ap : (0:ℝ) < A := by exact_mod_cast hA
  have r2 : (M : ℝ) ≤ v * v := by rw [hv]; exact_mod_cast le_sqrtHi_sq M
  have d : ((piHiN * RA * S : ℕ) : ℝ) / A ≤ (M : ℝ) := cdivN_ge _ _ hA
  have ph : Real.pi * S ≤ (piHiN : ℝ) := by
    have := pi_bounds.2
    rwa [le_div_iff₀ S_pos'] at this
  have bound : Real.pi / ((A : ℝ) / RA) * (Sz : ℝ) ^ 2 ≤ ((piHiN * RA * S : ℕ) : ℝ) / A := by
    rw [← S_eq]
    push_cast
    rw [le_div_iff₀ Ap]
    have e : Real.pi / ((A : ℝ) / RA) * (S : ℝ) ^ 2 * A = Real.pi * S * RA * S := by
      field_simp [RA_pos.ne']
    rw [e]
    have := mul_le_mul_of_nonneg_right ph (by positivity : (0:ℝ) ≤ (RA : ℝ) * S)
    nlinarith [this]
  have v0 : 0 ≤ v / Sz := div_nonneg (Nat.cast_nonneg _) sp.le
  rw [Real.sqrt_le_left v0, div_pow, le_div_iff₀ (pow_pos sp 2)]
  calc Real.pi / ((A : ℝ) / RA) * (Sz : ℝ) ^ 2 ≤ v * v := bound.trans (d.trans r2)
    _ = v ^ 2 := by ring

theorem rem_le (A : ℕ) :
    4 * ((A : ℝ) / RA) ^ (2 * halfTerms A) / (Nat.factorial (2 * halfTerms A) : ℝ) ≤
      ((cdivN (4 * A ^ (2 * halfTerms A) * S) (remDenOf (halfTerms A)) : ℕ) : ℝ) / Sz := by
  have rp : 0 < remDenOf (halfTerms A) := by
    rw [remDenOf_eq]; unfold RA; exact Nat.mul_pos (by positivity) (Nat.factorial_pos _)
  have d := cdivN_ge (4 * A ^ (2 * halfTerms A) * S) (remDenOf (halfTerms A)) rp
  have sp := Sz_pos
  rw [le_div_iff₀ sp, ← S_eq]
  refine le_trans (le_of_eq ?_) d
  rw [remDenOf_eq]
  push_cast
  field_simp [RA_pos.ne']
  rw [div_pow]
  field_simp [RA_pos.ne']

/-- **The half-kernel enclosure.** -/
theorem halfG_mem {A : ℕ} (hA : 0 < A) (guard : 2 * A ≤ 129 * RA) :
    (halfG A).Mem (gKernel (1/2) ((A : ℝ) / RA)) := by
  have near := halfKernel_near hA (halfTerms_guard A guard)
  rw [abs_le] at near
  have hm := halfTerms_le A
  set Z : ℤ := ((hornerN (A * A) (posList (halfTerms A)) : ℕ) : ℤ) -
    ((A * hornerN (A * A) (negList (halfTerms A)) : ℕ) : ℤ) with hZ
  have zEq : (Z : ℝ) / halfD = ((Erfc.series ((A : ℚ) / RA) (2 * halfTerms A) : ℚ) : ℝ) := halfZ_eq hm A
  have sLo := fdivS_le Z halfD_posN
  have sHi := le_cdivS Z halfD_posN
  rw [zEq] at sLo sHi
  have rLo := sqrtLo_le hA
  have rHi := le_sqrtHi hA
  have rem := rem_le A
  have sp := Sz_pos
  unfold halfG halfGm FI.Mem
  dsimp only
  rw [← hZ]
  constructor
  · have e : (((((sqrtLo (piLoN * RA * S / A) : ℕ) : ℤ) - 2 * cdivZ (Z * Sz) (halfD : ℤ) -
        ((cdivN (4 * A ^ (2 * halfTerms A) * S) (remDenOf (halfTerms A)) : ℕ) : ℤ) : ℤ) : ℝ) / Sz) =
        ((sqrtLo (piLoN * RA * S / A) : ℕ) : ℝ) / Sz - 2 * (((cdivZ (Z * Sz) (halfD : ℤ) : ℤ) : ℝ) / Sz) -
          ((cdivN (4 * A ^ (2 * halfTerms A) * S) (remDenOf (halfTerms A)) : ℕ) : ℝ) / Sz := by
      push_cast; ring
    rw [e]
    linarith [near.1]
  · have e : (((((sqrtHi (cdivN (piHiN * RA * S) A) : ℕ) : ℤ) - 2 * (Z * Sz / (halfD : ℤ)) +
        ((cdivN (4 * A ^ (2 * halfTerms A) * S) (remDenOf (halfTerms A)) : ℕ) : ℤ) : ℤ) : ℝ) / Sz) =
        ((sqrtHi (cdivN (piHiN * RA * S) A) : ℕ) : ℝ) / Sz - 2 * (((Z * Sz / (halfD : ℤ) : ℤ) : ℝ) / Sz) +
          ((cdivN (4 * A ^ (2 * halfTerms A) * S) (remDenOf (halfTerms A)) : ℕ) : ℝ) / Sz := by
      push_cast; ring
    rw [e]
    linarith [near.2]

/-! ### Scaling by `RA / A`, slopes and the reciprocal kernel -/

/-- `x ↦ x RA / A` on an enclosure. -/
def scaleDiv (a : FI) (A : ℕ) : FI := ⟨a.lo * RA / A, cdivZ (a.hi * RA) A⟩

theorem scaleDiv_mem {a : FI} {x : ℝ} (hx : a.Mem x) {A : ℕ} (hA : 0 < A) :
    (scaleDiv a A).Mem (x / ((A : ℝ) / RA)) := by
  have sp := Sz_pos
  have Ap : (0:ℝ) < A := by exact_mod_cast hA
  have Az : (0:ℤ) < A := by exact_mod_cast hA
  have e : x / ((A : ℝ) / RA) = x * RA / A := by field_simp
  rw [e]
  unfold scaleDiv FI.Mem
  constructor
  · have f := fdiv_le (a.lo * RA) (A : ℤ) Az
    have lo := hx.1
    rw [div_le_iff₀ sp] at lo ⊢
    push_cast at f ⊢
    calc ((a.lo * RA / A : ℤ) : ℝ) ≤ (a.lo : ℝ) * RA / A := f
      _ ≤ x * Sz * RA / A := by
          apply div_le_div_of_nonneg_right _ Ap.le
          exact mul_le_mul_of_nonneg_right lo RA_pos.le
      _ = x * RA / A * Sz := by ring
  · have f := le_cdiv (a.hi * RA) (A : ℤ) Az
    have hi := hx.2
    rw [le_div_iff₀ sp] at hi ⊢
    push_cast at f ⊢
    calc x * RA / A * Sz = x * Sz * RA / A := by ring
      _ ≤ (a.hi : ℝ) * RA / A := by
          apply div_le_div_of_nonneg_right _ Ap.le
          exact mul_le_mul_of_nonneg_right hi RA_pos.le
      _ ≤ _ := f

/-- `W(1/2, T) = (e^{-T} + G(1/2, T)/2)/T`. -/
def halfW (A : ℕ) : FI :=
  let E := expT A
  let G := halfG A
  scaleDiv ⟨E.lo + G.lo / 2, E.hi + cdivZ G.hi 2⟩ A

/-- `G(1, T) = e^{-T}/T`. -/
def oneG (A : ℕ) : FI := scaleDiv (expT A) A

/-- `W(1, T) = (e^{-T} + G(1, T))/T`. -/
def oneW (A : ℕ) : FI := scaleDiv ((expT A).add (oneG A)) A

theorem halfW_mem {A : ℕ} (hA : 0 < A) (guard : 2 * A ≤ 129 * RA) :
    (halfW A).Mem ((Real.exp (-((A : ℝ) / RA)) + gKernel (1/2) ((A : ℝ) / RA) / 2) / ((A : ℝ) / RA)) := by
  apply scaleDiv_mem _ hA
  exact FI.add_mem (expT_mem A) (half_mem (halfG_mem hA guard))

theorem oneG_mem {A : ℕ} (hA : 0 < A) : (oneG A).Mem (gKernel 1 ((A : ℝ) / RA)) := by
  have tpos : 0 < (A : ℝ) / RA := div_pos (by exact_mod_cast hA) RA_pos
  rw [gKernel_one tpos]
  exact scaleDiv_mem (expT_mem A) hA

theorem oneW_mem {A : ℕ} (hA : 0 < A) :
    (oneW A).Mem ((Real.exp (-((A : ℝ) / RA)) + gKernel 1 ((A : ℝ) / RA)) / ((A : ℝ) / RA)) :=
  scaleDiv_mem (FI.add_mem (expT_mem A) (oneG_mem hA)) hA

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
