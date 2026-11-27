import BccSharp.Cover.JensenFix
import BccSharp.Cover.OverlayFixSound

set_option autoImplicit false

/-! # Soundness of the fixed-point Jensen evaluator

`fLeafCheck_sound`: if `fLeafCheck s L N S b = true`, every valid point of the
leaf `b` has energy strictly above FCC. The chain is

* `qF_mem`, `rateF_mem`: interval enclosures of the squared lengths over a
  cell and of the rates;
* `gHalfF_mem`, `gOneF_mem`: the two kernels at a fixed-point anchor
  (`Erfc.sqrt_remainder` and an exact-integer invariant of `serRun`);
* `radial_sound`: the radial factor of a term, through `term_lower`;
* `secantData_sound`: the phase factor, through `phase_secant`;
* `mkTerm_sound`: each built term is `JTerm.Valid` on its support box;
* `buildSupport_structure`: distinct indices per kind, lex-positive halves;
* `fLeafCheck_sound`: `jensen_fcc_corners` at the 256 corners. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Jensen.Fix
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Screened (physicalS physicalS_cross physicalS_period
  physicalS_wave)
open BccSharp.Coulomb.CompactCover.DirectRoute (lexPositive cornerRat scaleInput scaleWitness
  offset)
open BccSharp.Coulomb.BravaisCover (KernelKind kernelValue kernelSlope cubeRootCheck)

/-! ### Constants and points -/

theorem piF_mem : piF.Mem Real.pi := by
  obtain ⟨h1, h2⟩ := twoPi_bounds
  have sp := Sz_pos
  have a := fdiv_le twoPiLo 2 (by norm_num)
  have b := le_cdiv twoPiHi 2 (by norm_num)
  push_cast at a b
  constructor
  · show ((twoPiLo / 2 : ℤ) : ℝ) / Sz ≤ Real.pi
    have c : ((twoPiLo / 2 : ℤ) : ℝ) / Sz ≤ (twoPiLo : ℝ) / 2 / Sz :=
      div_le_div_of_nonneg_right a sp.le
    have e : (twoPiLo : ℝ) / 2 / Sz = ((twoPiLo : ℝ) / Sz) / 2 := by ring
    linarith
  · show Real.pi ≤ ((cdivZ twoPiHi 2 : ℤ) : ℝ) / Sz
    have c : (twoPiHi : ℝ) / 2 / Sz ≤ ((cdivZ twoPiHi 2 : ℤ) : ℝ) / Sz :=
      div_le_div_of_nonneg_right b sp.le
    have e : (twoPiHi : ℝ) / 2 / Sz = ((twoPiHi : ℝ) / Sz) / 2 := by ring
    linarith

theorem ptF_mem (z : ℤ) : (ptF z).Mem ((z : ℝ) / Sz) := ⟨le_rfl, le_rfl⟩

theorem ratPt_mem (q : ℚ) : (ofRat q q).Mem (q : ℝ) := ofRat_mem ⟨le_rfl, le_rfl⟩

/-! ### Squared lengths over a cell -/

theorem vecF_mem (b : Cell) (n : IntVec) (shift : Bool) (i : Fin 3) {p : Chart} (hp : b.Mem p) :
    (vecF b n shift i).Mem (img (intVec n) shift p i) := by
  unfold vecF img intVec
  cases shift
  · simp only [Bool.false_eq_true, ite_false, add_zero]
    have h := FI.ofInt_mem (n i)
    push_cast
    exact h
  · simp only [ite_true]
    have h := FI.add_mem (FI.ofInt_mem (n i)) (cx_mem hp (offset i))
    push_cast
    exact h

theorem qGuard_parts {b : Cell} (g : qGuard b = true) :
    0 < (FI.sq (cx b 0)).lo ∧ 0 < (FI.sq (cx b 1)).lo ∧
      0 < (FI.mulPos (FI.sq (cx b 0)) (FI.sq (cx b 1))).lo := by
  unfold qGuard at g
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g
  exact ⟨g.1.1, g.1.2, g.2⟩

theorem primalF_mem (b : Cell) (n : IntVec) (shift : Bool) (g : qGuard b = true) {p : Chart}
    (hp : b.Mem p) : (primalF b n shift).Mem (primalQ (intVec n) shift p) := by
  obtain ⟨_, _, g3⟩ := qGuard_parts g
  have v0 := vecF_mem b n shift 0 hp
  have v1 := vecF_mem b n shift 1 hp
  have v2 := vecF_mem b n shift 2 hp
  have hA := FI.add_mem (FI.add_mem v0 (FI.mul_mem (cx_mem hp 2) v1)) (FI.mul_mem (cx_mem hp 3) v2)
  have hB := FI.add_mem v1 (FI.mul_mem (cx_mem hp 4) v2)
  have s2 := FI.sq_mem (cx_mem hp 0)
  have t2 := FI.sq_mem (cx_mem hp 1)
  have inv := FI.invPos_mem g3 (FI.mulPos_mem s2 t2)
  have total := FI.add_mem (FI.add_mem (FI.mulPos_mem s2 (FI.sq_mem hA)) (FI.mulPos_mem t2 (FI.sq_mem hB)))
    (FI.mulPos_mem (FI.sq_mem v2) inv)
  convert total using 1
  · rfl
  · simp only [primalQ, rowA, rowB, rowC, div_eq_mul_inv]

theorem dualF_mem (b : Cell) (m : IntVec) (g : qGuard b = true) {p : Chart} (hp : b.Mem p) :
    (dualF b m).Mem (dualQ m p) := by
  obtain ⟨g1, g2, _⟩ := qGuard_parts g
  have s2 := FI.sq_mem (cx_mem hp 0)
  have t2 := FI.sq_mem (cx_mem hp 1)
  have dB := FI.sub_mem (FI.ofInt_mem (m 1)) (FI.smul_mem (m 0) (cx_mem hp 2))
  have dC := FI.add_mem (FI.sub_mem (FI.ofInt_mem (m 2)) (FI.smul_mem (m 1) (cx_mem hp 4)))
    (FI.smul_mem (m 0) (FI.sub_mem (FI.mul_mem (cx_mem hp 2) (cx_mem hp 4)) (cx_mem hp 3)))
  have total := FI.add_mem (FI.add_mem (FI.mulPos_mem (FI.ofInt_mem (m 0 * m 0)) (FI.invPos_mem g1 s2))
    (FI.mulPos_mem (FI.sq_mem dB) (FI.invPos_mem g2 t2))) (FI.mulPos_mem (FI.mulPos_mem s2 t2) (FI.sq_mem dC))
  convert total using 1
  · rfl
  · simp only [dualQ, dualB, dualC, div_eq_mul_inv]
    push_cast
    ring

theorem qF_mem (b : Cell) (k : Kind) (n : IntVec) (g : qGuard b = true) {p : Chart}
    (hp : b.Mem p) : (qF b k n).Mem (termQ k n p) := by
  cases k
  · exact primalF_mem b n true g hp
  · exact primalF_mem b n false g hp
  · exact dualF_mem b n g hp

theorem rateF_mem (s : ℚ) (k : Kind) : (rateF s k).Mem (rate s k) := by
  cases k
  · have h := FI.mulPos_mem piF_mem (ratPt_mem (s * s))
    convert h using 1
    · rfl
    · simp only [rate]
      push_cast
      ring
  · have h := FI.mulPos_mem piF_mem (ratPt_mem (s * s))
    convert h using 1
    · rfl
    · simp only [rate]
      push_cast
      ring
  · have h := FI.mulPos_mem piF_mem (ratPt_mem (1 / (s * s)))
    convert h using 1
    · rfl
    · simp only [rate]
      push_cast
      ring

/-! ### The half kernel: the series invariant -/

/-- `qʲ/(j!(2j+1))`. -/
def sterm (q : ℝ) (j : ℕ) : ℝ := q ^ j / ((j.factorial : ℝ) * (2 * j + 1))

def evenSum (q : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if j % 2 = 0 then sterm q j else 0

def oddSum (q : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if j % 2 = 0 then 0 else sterm q j

def SerInv (Y : ℕ) (k : ℕ) (st : SerSt) : Prop :=
  let q : ℝ := (Y : ℝ) / S
  st.k = k ∧
    (st.tl : ℝ) ≤ T160 * (q ^ k / k.factorial) ∧ (T160 : ℝ) * (q ^ k / k.factorial) ≤ st.th ∧
    (st.pl : ℝ) ≤ T160 * evenSum q k ∧ (T160 : ℝ) * evenSum q k ≤ st.ph ∧
    (st.nl : ℝ) ≤ T160 * oddSum q k ∧ (T160 : ℝ) * oddSum q k ≤ st.nh

theorem evenSum_succ_even (q : ℝ) {k : ℕ} (h : k % 2 = 0) :
    evenSum q (k + 1) = evenSum q k + sterm q k := by
  simp [evenSum, Finset.sum_range_succ, h]

theorem evenSum_succ_odd (q : ℝ) {k : ℕ} (h : ¬ k % 2 = 0) :
    evenSum q (k + 1) = evenSum q k := by
  simp [evenSum, Finset.sum_range_succ, h]

theorem oddSum_succ_even (q : ℝ) {k : ℕ} (h : k % 2 = 0) :
    oddSum q (k + 1) = oddSum q k := by
  simp [oddSum, Finset.sum_range_succ, h]

theorem oddSum_succ_odd (q : ℝ) {k : ℕ} (h : ¬ k % 2 = 0) :
    oddSum q (k + 1) = oddSum q k + sterm q k := by
  simp [oddSum, Finset.sum_range_succ, h]

theorem S_posR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos

theorem serInv_start (Y : ℕ) : SerInv Y 0 serStart := by
  simp [SerInv, serStart, evenSum, oddSum]

theorem serInv_step (Y : ℕ) (k : ℕ) (st : SerSt) (h : SerInv Y k st) :
    SerInv Y (k + 1) (serStep Y st) := by
  obtain ⟨hk, tl, th, pl, ph, nl, nh⟩ := h
  set q : ℝ := (Y : ℝ) / S with hq
  have Sp := S_posR
  have kf : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have den : (0 : ℝ) < (S : ℝ) * (k + 1) := by positivity
  have fac : ((k + 1).factorial : ℝ) = (k.factorial : ℝ) * (k + 1) := by
    push_cast [Nat.factorial_succ]
    ring
  -- The next term, scaled.
  have Sne : (S : ℝ) ≠ 0 := Sp.ne'
  have kfne : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have k1ne : (k : ℝ) + 1 ≠ 0 := by positivity
  have nextEq : (T160 : ℝ) * (q ^ (k + 1) / (k + 1).factorial) =
      (T160 : ℝ) * (q ^ k / k.factorial) * Y / ((S : ℝ) * (k + 1)) := by
    rw [fac, pow_succ, hq]
    field_simp
  have Ynn : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
  have tl' : ((st.tl * Y / (S * (st.k + 1)) : ℕ) : ℝ) ≤ (T160 : ℝ) * (q ^ (k + 1) / (k + 1).factorial) := by
    rw [nextEq, hk]
    refine (Nat.cast_div_le).trans ?_
    push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right tl Ynn) den.le
  have th' : (T160 : ℝ) * (q ^ (k + 1) / (k + 1).factorial) ≤
      ((cdivN (st.th * Y) (S * (st.k + 1)) : ℕ) : ℝ) := by
    rw [nextEq, hk]
    have pos : 0 < S * (k + 1) := Nat.mul_pos S_pos (Nat.succ_pos k)
    refine le_trans ?_ (cdivN_ge _ _ pos)
    push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right th Ynn) den.le
  have d0 : (0 : ℝ) < 2 * k + 1 := by positivity
  have dpos : 0 < 2 * k + 1 := by omega
  have stermEq : sterm q k = (q ^ k / k.factorial) / (2 * k + 1) := by
    unfold sterm
    field_simp
  have lowT : ((st.tl / (2 * st.k + 1) : ℕ) : ℝ) ≤ T160 * sterm q k := by
    rw [hk, stermEq]
    refine (Nat.cast_div_le).trans ?_
    push_cast
    have := div_le_div_of_nonneg_right tl d0.le
    rw [mul_div_assoc] at this
    exact this
  have highT : (T160 : ℝ) * sterm q k ≤ ((cdivN st.th (2 * st.k + 1) : ℕ) : ℝ) := by
    rw [hk, stermEq]
    refine le_trans ?_ (cdivN_ge _ _ dpos)
    push_cast
    have := div_le_div_of_nonneg_right th d0.le
    rw [mul_div_assoc] at this
    exact this
  unfold serStep
  by_cases ev : st.k % 2 = 0
  · simp only [ev, ↓reduceIte]
    have ev' : k % 2 = 0 := hk ▸ ev
    refine ⟨by simp [hk], tl', th', ?_, ?_, ?_, ?_⟩
    · rw [evenSum_succ_even q ev']
      push_cast
      rw [mul_add]
      exact add_le_add pl lowT
    · rw [evenSum_succ_even q ev']
      push_cast
      rw [mul_add]
      exact add_le_add ph highT
    · rw [oddSum_succ_even q ev']
      exact nl
    · rw [oddSum_succ_even q ev']
      exact nh
  · simp only [ev, ↓reduceIte]
    have od' : ¬ k % 2 = 0 := hk ▸ ev
    refine ⟨by simp [hk], tl', th', ?_, ?_, ?_, ?_⟩
    · rw [evenSum_succ_odd q od']
      exact pl
    · rw [evenSum_succ_odd q od']
      exact ph
    · rw [oddSum_succ_odd q od']
      push_cast
      rw [mul_add]
      exact add_le_add nl lowT
    · rw [oddSum_succ_odd q od']
      push_cast
      rw [mul_add]
      exact add_le_add nh highT

theorem serRun_inv (Y n : ℕ) : SerInv Y n (serRun Y n) := by
  induction n with
  | zero => exact serInv_start Y
  | succ n ih => exact serInv_step Y n _ ih

theorem series_split (q : ℚ) (n : ℕ) :
    ((Erfc.series q n : ℚ) : ℝ) = evenSum (q : ℝ) n - oddSum (q : ℝ) n := by
  induction n with
  | zero => simp [Erfc.series, evenSum, oddSum]
  | succ n ih =>
    rw [Erfc.series, Finset.sum_range_succ, ← Erfc.series] at *
    push_cast
    rw [ih]
    simp only [evenSum, oddSum, Finset.sum_range_succ]
    by_cases ev : n % 2 = 0
    · simp only [ev, ↓reduceIte, add_zero]
      have e : (-(q : ℝ)) ^ n = (q : ℝ) ^ n := by
        rw [neg_pow, (Nat.even_iff.mpr ev).neg_one_pow, one_mul]
      rw [e]
      unfold sterm
      ring
    · simp only [ev, ↓reduceIte, add_zero]
      have e : (-(q : ℝ)) ^ n = -(q : ℝ) ^ n := by
        rw [neg_pow, (Nat.odd_iff.mpr (by omega)).neg_one_pow]
        ring
      rw [e]
      unfold sterm
      ring

/-! ### The half kernel: the enclosure -/

theorem Sz_eqS : ((S : ℕ) : ℝ) = (Sz : ℝ) := S_eq

theorem nTerms_guard (Y : ℕ) : ((Y : ℚ) / S) / ((nTerms Y + 1 : ℕ) : ℚ) ≤ 1 / 2 := by
  have hS : (0 : ℚ) < S := by exact_mod_cast S_pos
  have h1 : Y < S * (Y / S + 1) := Nat.lt_mul_div_succ Y S_pos
  have h1' : (Y : ℚ) < (S : ℚ) * ((Y / S : ℕ) + 1) := by exact_mod_cast h1
  have m0 : (0 : ℚ) ≤ ((Y / S : ℕ) : ℚ) := Nat.cast_nonneg _
  have hn : ((nTerms Y + 1 : ℕ) : ℚ) = 3 * ((Y / S : ℕ) : ℚ) + 61 := by
    simp only [nTerms]
    push_cast
    ring
  rw [hn, div_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The fixed-point enclosure of `G(1/2, Y/S)`. -/
theorem gHalfF_mem (Y : ℕ) (hY : 0 < Y) :
    (gHalfF Y).Mem (gKernel (1 / 2) ((Y : ℝ) / Sz)) := by
  set n := nTerms Y with hn
  set st := serRun Y n with hst
  set q : ℚ := (Y : ℚ) / S with hq
  have Sp := S_posR
  have Szp := Sz_pos
  have qr : ((q : ℚ) : ℝ) = (Y : ℝ) / Sz := by
    rw [hq]
    push_cast
    rw [Sz_eqS]
  have qpos : (0 : ℝ) < (Y : ℝ) / Sz := div_pos (by exact_mod_cast hY) Szp
  have inv : SerInv Y n st := serRun_inv Y n
  obtain ⟨_, tl, th, pl, ph, nl, nh⟩ := inv
  -- the series and the remainder
  have hser := series_split q n
  rw [qr] at hser
  have qS : (Y : ℝ) / S = (Y : ℝ) / Sz := by rw [Sz_eqS]
  rw [qS] at tl th pl ph nl nh
  set ser : ℝ := ((Erfc.series q n : ℚ) : ℝ) with hserdef
  have Tdef : (T160 : ℝ) = (U64 : ℝ) * Sz := by norm_num [T160, U64, Sz]
  have Up : (0 : ℝ) < U64 := by norm_num [U64]
  have Tp : (0 : ℝ) < T160 := by norm_num [T160]
  have serLo : ((((st.pl : ℤ) - st.nh) / (U64 : ℤ) : ℤ) : ℝ) / Sz ≤ ser := by
    have a := fdiv_le ((st.pl : ℤ) - st.nh) U64 (by norm_num [U64])
    push_cast at a
    have b : ((st.pl : ℝ) - st.nh) / U64 / Sz = ((st.pl : ℝ) - st.nh) / T160 := by
      rw [Tdef, div_div]
    have c : ((st.pl : ℝ) - st.nh) / T160 ≤ ser := by
      rw [div_le_iff₀ Tp, hser, sub_mul, mul_comm (evenSum _ _), mul_comm (oddSum _ _)]
      linarith
    calc ((((st.pl : ℤ) - st.nh) / (U64 : ℤ) : ℤ) : ℝ) / Sz
        ≤ ((st.pl : ℝ) - st.nh) / U64 / Sz := div_le_div_of_nonneg_right a Szp.le
      _ ≤ ser := b ▸ c
  have serHi : ser ≤ ((cdivZ ((st.ph : ℤ) - st.nl) U64 : ℤ) : ℝ) / Sz := by
    have a := le_cdiv ((st.ph : ℤ) - st.nl) U64 (by norm_num [U64])
    push_cast at a
    have b : ((st.ph : ℝ) - st.nl) / U64 / Sz = ((st.ph : ℝ) - st.nl) / T160 := by
      rw [Tdef, div_div]
    have c : ser ≤ ((st.ph : ℝ) - st.nl) / T160 := by
      rw [le_div_iff₀ Tp, hser, sub_mul, mul_comm (evenSum _ _), mul_comm (oddSum _ _)]
      linarith
    calc ser ≤ ((st.ph : ℝ) - st.nl) / U64 / Sz := b ▸ c
      _ ≤ _ := div_le_div_of_nonneg_right a Szp.le
  have remHi : 4 * (((Y : ℝ) / Sz) ^ n / n.factorial) ≤
      ((cdivN (4 * st.th) U64 : ℕ) : ℝ) / Sz := by
    have a := cdivN_ge (4 * st.th) U64 (by norm_num [U64])
    push_cast at a
    have b : 4 * (st.th : ℝ) / U64 / Sz = 4 * (st.th : ℝ) / T160 := by
      rw [Tdef, div_div]
    have c : 4 * (((Y : ℝ) / Sz) ^ n / n.factorial) ≤ 4 * (st.th : ℝ) / T160 := by
      have th' : ((Y : ℝ) / Sz) ^ n / n.factorial ≤ (st.th : ℝ) / T160 := by
        rw [le_div_iff₀ Tp, mul_comm]
        exact th
      rw [mul_div_assoc]
      linarith
    calc 4 * (((Y : ℝ) / Sz) ^ n / n.factorial) ≤ 4 * (st.th : ℝ) / U64 / Sz := b ▸ c
      _ ≤ _ := div_le_div_of_nonneg_right a Szp.le
  -- the root
  have hroot := FI.sqrt_mem (FI.mulPos_mem piF_mem (FI.invPos_mem (by
    show (0 : ℤ) < (Y : ℤ)
    exact_mod_cast hY) (ptF_mem (Y : ℤ))))
  push_cast at hroot
  -- the remainder theorem
  have q0 : (0 : ℚ) ≤ q := by positivity
  have rem := Erfc.sqrt_remainder q0 n (nTerms_guard Y)
  rw [qr] at rem
  have form := BravaisCover.halfKernel_formula qpos
  have sq0 : 0 < Real.sqrt ((Y : ℝ) / Sz) := Real.sqrt_pos.mpr qpos
  have sp0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set E := Gaussian.erfcIntegral (Real.sqrt ((Y : ℝ) / Sz))
  have rootEq : Real.sqrt (Real.pi * ((Y : ℝ) / Sz)⁻¹) =
      Real.sqrt Real.pi / Real.sqrt ((Y : ℝ) / Sz) := by
    rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_inv]
    ring
  have key : |gKernel (1 / 2) ((Y : ℝ) / Sz) -
      (Real.sqrt Real.pi / Real.sqrt ((Y : ℝ) / Sz) - 2 * ser)| ≤
      4 * (((Y : ℝ) / Sz) ^ n / n.factorial) := by
    rw [form]
    have e : Real.sqrt Real.pi * E / Real.sqrt ((Y : ℝ) / Sz) -
        (Real.sqrt Real.pi / Real.sqrt ((Y : ℝ) / Sz) - 2 * ser) =
        Real.sqrt Real.pi / Real.sqrt ((Y : ℝ) / Sz) *
          (E - (1 - 2 * Real.sqrt ((Y : ℝ) / Sz) / Real.sqrt Real.pi * ser)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (div_pos sp0 sq0)]
    have fac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    calc Real.sqrt Real.pi / Real.sqrt ((Y : ℝ) / Sz) *
          |E - (1 - 2 * Real.sqrt ((Y : ℝ) / Sz) / Real.sqrt Real.pi * ser)|
        ≤ Real.sqrt Real.pi / Real.sqrt ((Y : ℝ) / Sz) *
          (4 * Real.sqrt ((Y : ℝ) / Sz) * ((Y : ℝ) / Sz) ^ n /
            (Real.sqrt Real.pi * (n.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left rem (div_pos sp0 sq0).le
      _ = 4 * (((Y : ℝ) / Sz) ^ n / n.factorial) := by
          field_simp
  rw [rootEq] at hroot
  obtain ⟨k1, k2⟩ := abs_le.mp key
  unfold gHalfF
  constructor
  · show (((FI.sqrt (FI.mulPos piF (FI.invPos (ptF Y)))).lo -
        2 * cdivZ ((st.ph : ℤ) - st.nl) U64 - (cdivN (4 * st.th) U64 : ℕ) : ℤ) : ℝ) / Sz ≤ _
    push_cast
    have r1 := hroot.1
    rw [sub_div, sub_div, mul_div_assoc]
    linarith
  · show _ ≤ (((FI.sqrt (FI.mulPos piF (FI.invPos (ptF Y)))).hi -
        2 * ((((st.pl : ℤ) - st.nh) / (U64 : ℤ) : ℤ)) + (cdivN (4 * st.th) U64 : ℕ) : ℤ) : ℝ) / Sz
    push_cast
    have r2 := hroot.2
    rw [add_div, sub_div, mul_div_assoc]
    linarith

/-! ### The one kernel and the kernel pair -/

theorem gOneF_mem (Y : ℕ) (hY : 0 < Y) : (gOneF Y).Mem (gKernel 1 ((Y : ℝ) / Sz)) := by
  have Szp := Sz_pos
  have qpos : (0 : ℝ) < (Y : ℝ) / Sz := div_pos (by exact_mod_cast hY) Szp
  rw [gKernel_one qpos, div_eq_mul_inv]
  have h := FI.mulPos_mem (expNegPt_mem Y)
    (FI.invPos_mem (show (0 : ℤ) < (ptF (Y : ℤ)).lo from (by show (0 : ℤ) < (Y : ℤ); exact_mod_cast hY)) (ptF_mem (Y : ℤ)))
  push_cast at h
  exact h

/-- The kernel of a term kind: `G(1/2, ·)` for direct modes, `G(1, ·)` for
reciprocal modes. -/
def kindK : Kind → KernelKind
  | .wave => .one
  | _ => .half

theorem kernelValue_half (x : ℝ) : kernelValue .half x = gKernel (1 / 2) x := by
  simp [kernelValue, KernelKind.power]

theorem kernelValue_one (x : ℝ) : kernelValue .one x = gKernel 1 x := by
  simp [kernelValue, KernelKind.power]

theorem kernelF_mem (k : Kind) (Y : ℕ) (hY : 0 < Y) :
    (kernelF k Y).1.Mem (kernelValue (kindK k) ((Y : ℝ) / Sz)) ∧
    (kernelF k Y).2.Mem (Real.exp (-((Y : ℝ) / Sz)) +
      ((kindK k).power : ℝ) * kernelValue (kindK k) ((Y : ℝ) / Sz)) := by
  have hE := expNegPt_mem Y
  cases k
  · have hG := gHalfF_mem Y hY
    rw [← kernelValue_half] at hG
    refine ⟨hG, ?_⟩
    have h2 := FI.add_mem hE (half_mem hG)
    have e : ((kindK .cross).power : ℝ) * kernelValue (kindK .cross) ((Y : ℝ) / Sz) =
        kernelValue .half ((Y : ℝ) / Sz) / 2 := by
      simp only [kindK, KernelKind.power]
      push_cast
      ring
    rw [e]
    exact h2
  · have hG := gHalfF_mem Y hY
    rw [← kernelValue_half] at hG
    refine ⟨hG, ?_⟩
    have h2 := FI.add_mem hE (half_mem hG)
    have e : ((kindK .period).power : ℝ) * kernelValue (kindK .period) ((Y : ℝ) / Sz) =
        kernelValue .half ((Y : ℝ) / Sz) / 2 := by
      simp only [kindK, KernelKind.power]
      push_cast
      ring
    rw [e]
    exact h2
  · have hG := gOneF_mem Y hY
    rw [← kernelValue_one] at hG
    refine ⟨hG, ?_⟩
    have h2 := FI.add_mem hE hG
    have e : ((kindK .wave).power : ℝ) * kernelValue (kindK .wave) ((Y : ℝ) / Sz) =
        kernelValue .one ((Y : ℝ) / Sz) := by
      simp only [kindK, KernelKind.power]
      push_cast
      ring
    rw [e]
    exact h2

/-! ### The radial factor -/

theorem rate_pos' {s : ℚ} (hs : 0 < s) (k : Kind) : 0 < rate s k := by
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  cases k <;> simp only [rate] <;> positivity

theorem radialOk_parts {s L : ℚ} {S : Cell} {d : Radial} (ok : radialOk s L S d = true) :
    qGuard S = true ∧ 0 < s ∧ 0 < d.Y ∧ 0 < d.G.lo ∧ 0 < d.V ∧ 0 ≤ d.sig := by
  unfold radialOk at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨g, s0⟩, y0⟩, _⟩, g0⟩, v0⟩, sg⟩ := ok
  exact ⟨g, s0, y0, g0, v0, sg⟩

/-- **The radial factor.** On the support box, `(V/S) e^{-σ(y - y₀)}` lies
below the kernel at `y = rate · q`. -/
theorem radial_sound (s L : ℚ) (S : Cell) (k : Kind) (n : IntVec)
    (ok : radialOk s L S (radialOf s S k n) = true) (p : Chart) (hp : S.Mem p)
    (hq : 0 < termQ k n p) :
    (((radialOf s S k n).V : ℝ) / Sz) *
        Real.exp (-(((radialOf s S k n).sig : ℝ) / Sz) *
          (rate s k * termQ k n p - ((radialOf s S k n).Y : ℝ) / Sz)) ≤
      kernelValue (kindK k) (rate s k * termQ k n p) := by
  obtain ⟨gS, hs, Y0, _, _, _⟩ := radialOk_parts ok
  have Szp := Sz_pos
  have YN : (((radialOf s S k n).Y.toNat : ℕ) : ℝ) = ((radialOf s S k n).Y : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg Y0.le
  have YNpos : 0 < (radialOf s S k n).Y.toNat := by omega
  have y0pos : (0 : ℝ) < ((radialOf s S k n).Y : ℝ) / Sz := div_pos (by exact_mod_cast Y0) Szp
  have ypos : 0 < rate s k * termQ k n p := mul_pos (rate_pos' hs k) hq
  -- the range of `y` over the support box
  have yr := FI.mulPos_mem (rateF_mem s k) (qF_mem S k n gS hp)
  have eYm : (radialOf s S k n).Ym = max 0 (max ((FI.mulPos (rateF s k) (qF S k n)).hi -
      (radialOf s S k n).Y) ((radialOf s S k n).Y - (FI.mulPos (rateF s k) (qF S k n)).lo)) := rfl
  have hYm : |rate s k * termQ k n p - ((radialOf s S k n).Y : ℝ) / Sz| ≤
      ((radialOf s S k n).Ym : ℝ) / Sz := by
    have m1 : (FI.mulPos (rateF s k) (qF S k n)).hi - (radialOf s S k n).Y ≤
        (radialOf s S k n).Ym := by
      rw [eYm]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have m2 : (radialOf s S k n).Y - (FI.mulPos (rateF s k) (qF S k n)).lo ≤
        (radialOf s S k n).Ym := by
      rw [eYm]
      exact (le_max_right _ _).trans (le_max_right _ _)
    have m1r : (((FI.mulPos (rateF s k) (qF S k n)).hi : ℤ) : ℝ) - (radialOf s S k n).Y ≤
        (radialOf s S k n).Ym := by exact_mod_cast m1
    have m2r : (((radialOf s S k n).Y : ℤ) : ℝ) - (FI.mulPos (rateF s k) (qF S k n)).lo ≤
        (radialOf s S k n).Ym := by exact_mod_cast m2
    have d1 := div_le_div_of_nonneg_right m1r Szp.le
    have d2 := div_le_div_of_nonneg_right m2r Szp.le
    rw [sub_div] at d1 d2
    obtain ⟨l1, l2⟩ := yr
    rw [abs_le]
    constructor <;> linarith
  -- the kernel at the anchor
  obtain ⟨hG, hnum⟩ := kernelF_mem k (radialOf s S k n).Y.toNat YNpos
  rw [YN] at hG hnum
  have eG : (radialOf s S k n).G = (kernelF k (radialOf s S k n).Y.toNat).1 := rfl
  have enum : (radialOf s S k n).num = (kernelF k (radialOf s S k n).Y.toNat).2 := rfl
  rw [← eG] at hG
  rw [← enum] at hnum
  -- the residual `G' + σ G`
  have iy := FI.invPos_mem (show 0 < (ptF (radialOf s S k n).Y).lo from Y0)
    (ptF_mem (radialOf s S k n).Y)
  have heps := FI.sub_mem (FI.mul_mem hG (ptF_mem (radialOf s S k n).sig)) (FI.mulPos_mem hnum iy)
  have eem : (radialOf s S k n).em = max 0 (max ((FI.mul (radialOf s S k n).G
      (ptF (radialOf s S k n).sig)).sub (FI.mulPos (radialOf s S k n).num
        (FI.invPos (ptF (radialOf s S k n).Y)))).hi
      (-((FI.mul (radialOf s S k n).G (ptF (radialOf s S k n).sig)).sub
        (FI.mulPos (radialOf s S k n).num (FI.invPos (ptF (radialOf s S k n).Y)))).lo)) := rfl
  have slopeEq : kernelSlope (kindK k) (((radialOf s S k n).Y : ℝ) / Sz) +
      (((radialOf s S k n).sig : ℝ) / Sz) *
        kernelValue (kindK k) (((radialOf s S k n).Y : ℝ) / Sz) =
      kernelValue (kindK k) (((radialOf s S k n).Y : ℝ) / Sz) *
          (((radialOf s S k n).sig : ℝ) / Sz) -
        (Real.exp (-(((radialOf s S k n).Y : ℝ) / Sz)) +
          ((kindK k).power : ℝ) * kernelValue (kindK k) (((radialOf s S k n).Y : ℝ) / Sz)) *
          (((radialOf s S k n).Y : ℝ) / Sz)⁻¹ := by
    simp only [kernelSlope]
    ring
  have hε : |kernelSlope (kindK k) (((radialOf s S k n).Y : ℝ) / Sz) +
      (((radialOf s S k n).sig : ℝ) / Sz) *
        kernelValue (kindK k) (((radialOf s S k n).Y : ℝ) / Sz)| ≤
      ((radialOf s S k n).em : ℝ) / Sz := by
    rw [slopeEq, abs_le]
    obtain ⟨e1, e2⟩ := heps
    have m1 : ((FI.mul (radialOf s S k n).G (ptF (radialOf s S k n).sig)).sub
        (FI.mulPos (radialOf s S k n).num (FI.invPos (ptF (radialOf s S k n).Y)))).hi ≤
          (radialOf s S k n).em := by
      rw [eem]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have m2 : -((FI.mul (radialOf s S k n).G (ptF (radialOf s S k n).sig)).sub
        (FI.mulPos (radialOf s S k n).num (FI.invPos (ptF (radialOf s S k n).Y)))).lo ≤
          (radialOf s S k n).em := by
      rw [eem]
      exact (le_max_right _ _).trans (le_max_right _ _)
    have m1r := div_le_div_of_nonneg_right (show (((FI.mul (radialOf s S k n).G
        (ptF (radialOf s S k n).sig)).sub (FI.mulPos (radialOf s S k n).num
          (FI.invPos (ptF (radialOf s S k n).Y)))).hi : ℝ) ≤ (radialOf s S k n).em by
      exact_mod_cast m1) Szp.le
    have m2r := div_le_div_of_nonneg_right (show (-(((FI.mul (radialOf s S k n).G
        (ptF (radialOf s S k n).sig)).sub (FI.mulPos (radialOf s S k n).num
          (FI.invPos (ptF (radialOf s S k n).Y)))).lo : ℝ)) ≤ (radialOf s S k n).em by
      exact_mod_cast m2) Szp.le
    rw [neg_div] at m2r
    constructor <;> linarith
  -- the weight
  have eV : (radialOf s S k n).V =
      (radialOf s S k n).G.lo - cdivZ ((radialOf s S k n).Ym * (radialOf s S k n).em) Sz := rfl
  have hV : ((radialOf s S k n).V : ℝ) / Sz ≤
      kernelValue (kindK k) (((radialOf s S k n).Y : ℝ) / Sz) -
        (((radialOf s S k n).Ym : ℝ) / Sz) * (((radialOf s S k n).em : ℝ) / Sz) := by
    have c := le_cdiv ((radialOf s S k n).Ym * (radialOf s S k n).em) Sz Sz_posZ
    have c' := div_le_div_of_nonneg_right c Szp.le
    push_cast at c'
    have e : (((radialOf s S k n).Ym : ℝ) / Sz) * (((radialOf s S k n).em : ℝ) / Sz) =
        ((radialOf s S k n).Ym : ℝ) * (radialOf s S k n).em / Sz / Sz := by ring
    rw [eV, e]
    push_cast
    rw [sub_div]
    linarith [hG.1]
  exact term_lower (kindK k) y0pos ypos hYm hε hV

/-! ### The phase factor -/

theorem mul_minmax (c lo hi : ℚ) {x : ℝ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    ((min (c * lo) (c * hi) : ℚ) : ℝ) ≤ (c : ℝ) * x ∧ (c : ℝ) * x ≤ ((max (c * lo) (c * hi) : ℚ) : ℝ) := by
  rcases le_total 0 c with hc | hc
  · have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    have a1 := mul_le_mul_of_nonneg_left h1 hc'
    have a2 := mul_le_mul_of_nonneg_left h2 hc'
    have b1 : ((min (c * lo) (c * hi) : ℚ) : ℝ) ≤ (c : ℝ) * lo := by
      exact_mod_cast (show min (c * lo) (c * hi) ≤ c * lo from min_le_left _ _)
    have b2 : (c : ℝ) * hi ≤ ((max (c * lo) (c * hi) : ℚ) : ℝ) := by
      exact_mod_cast (show c * hi ≤ max (c * lo) (c * hi) from le_max_right _ _)
    exact ⟨b1.trans a1, a2.trans b2⟩
  · have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast hc
    have a1 := mul_le_mul_of_nonpos_left h1 hc'
    have a2 := mul_le_mul_of_nonpos_left h2 hc'
    have b1 : ((min (c * lo) (c * hi) : ℚ) : ℝ) ≤ (c : ℝ) * hi := by
      exact_mod_cast (show min (c * lo) (c * hi) ≤ c * hi from min_le_right _ _)
    have b2 : (c : ℝ) * lo ≤ ((max (c * lo) (c * hi) : ℚ) : ℝ) := by
      exact_mod_cast (show c * lo ≤ max (c * lo) (c * hi) from le_max_left _ _)
    exact ⟨b1.trans a2, a1.trans b2⟩

theorem phase_range (S : Cell) (n : IntVec) {p : Chart} (hp : S.Mem p) :
    (phaseLoQ S n : ℝ) ≤ phaseT n p ∧ phaseT n p ≤ (phaseHiQ S n : ℝ) := by
  obtain ⟨a1, a2⟩ := mul_minmax (n 0 : ℚ) (S.lo 5) (S.hi 5) (hp 5).1 (hp 5).2
  obtain ⟨b1, b2⟩ := mul_minmax (n 1 : ℚ) (S.lo 6) (S.hi 6) (hp 6).1 (hp 6).2
  obtain ⟨c1, c2⟩ := mul_minmax (n 2 : ℚ) (S.lo 7) (S.hi 7) (hp 7).1 (hp 7).2
  have e : phaseT n p = ((n 0 : ℚ) : ℝ) * p 5 + ((n 1 : ℚ) : ℝ) * p 6 + ((n 2 : ℚ) : ℝ) * p 7 := by
    simp only [phaseT, Fin.sum_univ_three, offset]
    push_cast
    rfl
  rw [e]
  unfold phaseLoQ phaseHiQ
  push_cast at a1 a2 b1 b2 c1 c2 ⊢
  constructor <;> linarith

theorem onePlusCosLo_le (v : ℚ) :
    (onePlusCosLo v : ℝ) / Sz ≤ 1 + Real.cos (2 * Real.pi * v) := by
  have h := cosRange_mem (A := (ofRat v v).lo) (B := (ofRat v v).hi) (ratPt_mem v)
  have Szp := Sz_pos
  unfold onePlusCosLo
  push_cast
  rw [add_div, div_self Szp.ne']
  linarith [h.1]

theorem expUpQ_ge (z : ℚ) (h : 0 < expUpQ z) : Real.exp z ≤ (expUpQ z : ℝ) / Sz := by
  have f := ratPt_mem z
  have Szp := Sz_pos
  unfold expUpQ at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with h1 h2
  · have hx : (ofRat z z).hi.toNat ≤ S64 := by omega
    have e := (expPosPt_mem (ofRat z z).hi.toNat hx).2
    have cast : (((ofRat z z).hi.toNat : ℕ) : ℝ) = ((ofRat z z).hi : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h1
    rw [cast] at e
    have mono := Real.exp_le_exp.mpr f.2
    rw [le_div_iff₀ Szp]
    push_cast
    nlinarith [Real.exp_pos (z : ℝ)]
  · simp at h
  · have e := (expNegPt_mem (-(ofRat z z).hi).toNat).2
    have cast : (((-(ofRat z z).hi).toNat : ℕ) : ℝ) = -((ofRat z z).hi : ℝ) := by
      have h0 : 0 ≤ -(ofRat z z).hi := by omega
      have h3 := Int.toNat_of_nonneg h0
      have h4 : ((((-(ofRat z z).hi).toNat : ℕ) : ℤ) : ℝ) = ((-(ofRat z z).hi : ℤ) : ℝ) := by
        rw [h3]
      push_cast at h4
      exact h4
    rw [cast, neg_div, neg_neg] at e
    exact (Real.exp_le_exp.mpr f.2).trans e

theorem expLoZ_le (z : ℚ) : (expLoZ z : ℝ) / Sz ≤ Real.exp z := by
  have f := ratPt_mem z
  have Szp := Sz_pos
  unfold expLoZ
  dsimp only
  split_ifs with h1 h2
  · have hx : (ofRat z z).lo.toNat ≤ S64 := by omega
    have e := (expPosPt_mem (ofRat z z).lo.toNat hx).1
    have cast : (((ofRat z z).lo.toNat : ℕ) : ℝ) = ((ofRat z z).lo : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h1
    rw [cast] at e
    have mono := Real.exp_le_exp.mpr f.1
    rw [div_le_iff₀ Szp]
    push_cast
    nlinarith [Real.exp_pos ((ofRat z z).lo / Sz : ℝ)]
  · push_cast
    rw [zero_div]
    exact (Real.exp_pos _).le
  · have e := (expNegPt_mem (-(ofRat z z).lo).toNat).1
    have cast : (((-(ofRat z z).lo).toNat : ℕ) : ℝ) = -((ofRat z z).lo : ℝ) := by
      have h0 : 0 ≤ -(ofRat z z).lo := by omega
      have h3 := Int.toNat_of_nonneg h0
      have h4 : ((((-(ofRat z z).lo).toNat : ℕ) : ℤ) : ℝ) = ((-(ofRat z z).lo : ℤ) : ℝ) := by
        rw [h3]
      push_cast at h4
      exact h4
    rw [cast, neg_div, neg_neg] at e
    exact e.trans (Real.exp_le_exp.mpr f.1)

/-- One endpoint of a secant: `(p/S) e^{±βw/2} ≤ 1 + cos 2πv` when `p` is at
most `S·(1 + cos 2πv)/e` and `e` bounds the exponential above. -/
theorem secant_end (v : ℚ) (x : ℚ) (pz : ℤ) (hpz : 0 ≤ pz) (he : 0 < expUpQ x)
    (hm : pz ≤ onePlusCosLo v * Sz / expUpQ x) :
    ((pz : ℝ) / Sz) * Real.exp (x : ℝ) ≤ 1 + Real.cos (2 * Real.pi * v) := by
  have Szp := Sz_pos
  have pz0 : (0 : ℝ) ≤ (pz : ℝ) / Sz := div_nonneg (by exact_mod_cast hpz) Szp.le
  have eu := expUpQ_ge x he
  have d := fdiv_le (onePlusCosLo v * Sz) (expUpQ x) he
  have ePos : (0 : ℝ) < expUpQ x := by exact_mod_cast he
  have mr : (pz : ℝ) ≤ ((onePlusCosLo v * Sz : ℤ) : ℝ) / expUpQ x :=
    (by exact_mod_cast hm : (pz : ℝ) ≤ ((onePlusCosLo v * Sz / expUpQ x : ℤ) : ℝ)).trans d
  have step : (pz : ℝ) / Sz * ((expUpQ x : ℝ) / Sz) ≤ (onePlusCosLo v : ℝ) / Sz := by
    have m2 := mul_le_mul_of_nonneg_right mr ePos.le
    rw [div_mul_cancel₀ _ ePos.ne'] at m2
    push_cast at m2
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) Szp]
    nlinarith
  calc ((pz : ℝ) / Sz) * Real.exp (x : ℝ) ≤ (pz : ℝ) / Sz * ((expUpQ x : ℝ) / Sz) :=
        mul_le_mul_of_nonneg_left eu pz0
    _ ≤ (onePlusCosLo v : ℝ) / Sz := step
    _ ≤ _ := onePlusCosLo_le v

/-- **The phase factor.** A secant from `secantData` holds on the whole phase
interval. -/
theorem secantData_sound (l r β : ℚ) (pz : ℤ) (h : secantData l r = some (β, pz)) (hpz : 0 ≤ pz)
    {t : ℝ} (htl : (l : ℝ) ≤ t) (htr : t ≤ r) :
    ((pz : ℝ) / Sz) * Real.exp ((β : ℝ) * (t - (((l + r) / 2 : ℚ) : ℝ))) ≤
      1 + Real.cos (2 * Real.pi * t) := by
  unfold secantData at h
  split_ifs at h with hc
  have hb : secantSlope l r = β := (Prod.mk.inj (Option.some.inj h)).1
  have hw : secantWeight l r = pz := (Prod.mk.inj (Option.some.inj h)).2
  rw [← hb, ← hw]
  rw [← hw] at hpz
  unfold secantOk at hc
  obtain ⟨hk1, hk2, _, _, _, heA, heB⟩ := of_decide_eq_true hc
  have Szp := Sz_pos
  have pz0 : (0 : ℝ) ≤ (secantWeight l r : ℝ) / Sz := div_nonneg (by exact_mod_cast hpz) Szp.le
  have kl : ((⌊(l + r) / 2 + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2 < l := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hk1
    push_cast at h
    exact h
  have kr : (r : ℝ) < ((⌊(l + r) / 2 + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hk2
    push_cast at h
    exact h
  have endA := secant_end l (-(secantSlope l r * (r - l) / 2)) (secantWeight l r) hpz heA
    (min_le_left _ _)
  have endB := secant_end r (secantSlope l r * (r - l) / 2) (secantWeight l r) hpz heB
    (min_le_right _ _)
  have exA : (((-(secantSlope l r * (r - l) / 2)) : ℚ) : ℝ) =
      (secantSlope l r : ℝ) * ((l : ℝ) - (((l + r) / 2 : ℚ) : ℝ)) := by
    push_cast
    ring
  have exB : (((secantSlope l r * (r - l) / 2) : ℚ) : ℝ) =
      (secantSlope l r : ℝ) * ((r : ℝ) - (((l + r) / 2 : ℚ) : ℝ)) := by
    push_cast
    ring
  rw [exA] at endA
  rw [exB] at endB
  exact phase_secant _ kl kr pz0 endA endB htl htr

/-! ### Terms -/

theorem mkTerm_kind {s L : ℚ} {S : Cell} {k : Kind} {n : IntVec} {t : JTerm}
    (h : mkTerm s L S k n = some t) : t.kind = k ∧ t.index = n := by
  unfold mkTerm at h
  dsimp only at h
  split_ifs at h
  cases k
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h
    exact ⟨rfl, rfl⟩
  · simp only at h
    split at h
    · cases h
    · split_ifs at h
      cases h
      exact ⟨rfl, rfl⟩

theorem rhi_bounds (s : ℚ) (hs : 0 < s) (S : Cell) (k : Kind) (n : IntVec) :
    rate s k ≤ ((((radialOf s S k n).r.hi : ℚ) / Sz : ℚ) : ℝ) ∧
      (0 : ℚ) ≤ ((radialOf s S k n).r.hi : ℚ) / Sz := by
  have er : (radialOf s S k n).r = rateF s k := rfl
  have hr := (rateF_mem s k).2
  rw [← er] at hr
  have c : ((((radialOf s S k n).r.hi : ℚ) / Sz : ℚ) : ℝ) = ((radialOf s S k n).r.hi : ℝ) / Sz := by
    push_cast
    rfl
  rw [c]
  refine ⟨hr, ?_⟩
  have pos := (rate_pos' hs k).trans_le hr
  have Szq : (0 : ℚ) < Sz := by exact_mod_cast Sz_posZ
  have : (0 : ℝ) < ((radialOf s S k n).r.hi : ℝ) := by
    have := mul_pos pos Sz_pos
    rwa [div_mul_cancel₀ _ Sz_pos.ne'] at this
  have hq : (0 : ℚ) < (radialOf s S k n).r.hi := by exact_mod_cast this
  positivity

/-- **Each built term is valid** on its support box. Period and reciprocal
indices must be lex-positive. -/
theorem mkTerm_sound (s L : ℚ) (S : Cell) (k : Kind) (n : IntVec) (t : JTerm)
    (h : mkTerm s L S k n = some t) (lex : k ≠ .cross → lexPositive n) :
    0 ≤ t.rhi ∧ t.Valid s S := by
  have hk := mkTerm_kind h
  unfold mkTerm at h
  dsimp only at h
  split_ifs at h with hok
  obtain ⟨gS, hs, Y0, _, V0, sig0⟩ := radialOk_parts hok
  obtain ⟨rr, rhi0⟩ := rhi_bounds s hs S k n
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  have Szp := Sz_pos
  have Vp : (0 : ℝ) < ((radialOf s S k n).V : ℝ) / Sz := div_pos (by exact_mod_cast V0) Szp
  have sigp : (0 : ℚ) ≤ ((radialOf s S k n).sig : ℚ) / Sz := by
    have : (0 : ℚ) ≤ (radialOf s S k n).sig := by exact_mod_cast sig0
    have Szq : (0 : ℚ) < Sz := by exact_mod_cast Sz_posZ
    positivity
  cases k
  · cases h
    refine ⟨rhi0, ?_, sigp, rr, ?_⟩
    · have : (0 : ℚ) < (radialOf s S .cross n).V := by exact_mod_cast V0
      have Szq : (0 : ℚ) < Sz := by exact_mod_cast Sz_posZ
      positivity
    · intro p hp hv
      obtain ⟨phys, hq⟩ := physicalS_cross s n hv
      have rs := radial_sound s L S .cross n hok p hp hq
      rw [phys]
      simp only [JTerm.u, kindK, kernelValue_half, rate] at rs ⊢
      push_cast at rs ⊢
      have e : Real.pi * ((s : ℝ) ^ 2 * termQ .cross n p) = Real.pi * (s : ℝ) ^ 2 * termQ .cross n p := by
        ring
      rw [e]
      simp only [zero_mul, add_zero]
      have key := mul_le_mul_of_nonneg_left rs sr.le
      refine le_trans (le_of_eq ?_) key
      ring
  · cases h
    have lp := lex (by decide)
    refine ⟨rhi0, ?_, sigp, rr, ?_⟩
    · have : (0 : ℚ) < (radialOf s S .period n).V := by exact_mod_cast V0
      have Szq : (0 : ℚ) < Sz := by exact_mod_cast Sz_posZ
      positivity
    · intro p hp hv
      obtain ⟨phys, hq⟩ := physicalS_period s n lp hv
      have rs := radial_sound s L S .period n hok p hp hq
      rw [phys]
      simp only [JTerm.u, kindK, kernelValue_half, rate] at rs ⊢
      push_cast at rs ⊢
      have e : Real.pi * ((s : ℝ) ^ 2 * termQ .period n p) =
          Real.pi * (s : ℝ) ^ 2 * termQ .period n p := by
        ring
      rw [e]
      simp only [zero_mul, add_zero]
      have two : (0 : ℝ) ≤ 2 * (s : ℝ) := by positivity
      have key := mul_le_mul_of_nonneg_left rs two
      refine le_trans (le_of_eq ?_) key
      ring
  · have lp := lex (by decide)
    simp only at h
    split at h
    · cases h
    · rename_i β pz hsd
      split_ifs at h with hpz
      cases h
      refine ⟨rhi0, ?_, sigp, rr, ?_⟩
      · have v1 : (0 : ℚ) < (radialOf s S .wave n).V := by exact_mod_cast V0
        have p1 : (0 : ℚ) ≤ pz := by exact_mod_cast hpz
        have Szq : (0 : ℚ) < Sz := by exact_mod_cast Sz_posZ
        have ss : (0 : ℚ) ≤ 2 / (s * s) := by positivity
        exact mul_nonneg (mul_nonneg ss (div_nonneg p1 Szq.le)) (div_nonneg v1.le Szq.le)
      · intro p hp hv
        obtain ⟨phys, hq⟩ := physicalS_wave s n lp hv hs
        have rs := radial_sound s L S .wave n hok p hp hq
        obtain ⟨tl, tr⟩ := phase_range S n hp
        have ph := secantData_sound _ _ β pz hsd hpz tl tr
        rw [phys]
        simp only [JTerm.u, kindK, rate] at rs ⊢
        have y0 : 0 < Real.pi / (s : ℝ) ^ 2 * termQ .wave n p := by positivity
        rw [kernelValue_one, gKernel_one y0] at rs
        have ey : Real.pi * termQ .wave n p / (s : ℝ) ^ 2 = Real.pi / (s : ℝ) ^ 2 * termQ .wave n p := by
          ring
        rw [ey]
        push_cast at rs ph ⊢
        set E1 := Real.exp (-(((radialOf s S .wave n).sig : ℝ) / Sz) *
          (Real.pi / (s : ℝ) ^ 2 * termQ .wave n p - ((radialOf s S .wave n).Y : ℝ) / Sz))
        set E2 := Real.exp ((β : ℝ) * (phaseT n p - ((phaseLoQ S n : ℝ) + (phaseHiQ S n : ℝ)) / 2))
        have split : Real.exp (-(((radialOf s S .wave n).sig : ℝ) / Sz) *
            (Real.pi / (s : ℝ) ^ 2 * termQ .wave n p - ((radialOf s S .wave n).Y : ℝ) / Sz) +
            (β : ℝ) * (phaseT n p - ((phaseLoQ S n : ℝ) + (phaseHiQ S n : ℝ)) / 2)) = E1 * E2 := by
          rw [← Real.exp_add]
        rw [split]
        have pzr : (0 : ℝ) ≤ (pz : ℝ) / Sz := div_nonneg (by exact_mod_cast hpz) Szp.le
        have f1 : 0 ≤ ((pz : ℝ) / Sz) * E2 := mul_nonneg pzr (Real.exp_pos _).le
        have f2 : 0 ≤ ((radialOf s S .wave n).V : ℝ) / Sz * E1 := mul_nonneg Vp.le (Real.exp_pos _).le
        have prod := mul_le_mul ph rs f2 (by linarith [Real.neg_one_le_cos (2 * Real.pi * phaseT n p)])
        have c2 : (0 : ℝ) ≤ 2 / (s : ℝ) ^ 2 := by positivity
        have fin := mul_le_mul_of_nonneg_left prod c2
        calc 2 / ((s : ℝ) * s) * ((pz : ℝ) / Sz) * (((radialOf s S .wave n).V : ℝ) / Sz) * (E1 * E2)
            = 2 / (s : ℝ) ^ 2 * (((pz : ℝ) / Sz) * E2 * (((radialOf s S .wave n).V : ℝ) / Sz * E1)) := by
              ring
          _ ≤ _ := fin

/-! ### The support -/

theorem cubeRange_nodup (N : ℕ) : (cubeRange N).Nodup := by
  unfold cubeRange
  refine List.Nodup.map (fun a b h => ?_) List.nodup_range
  have h' : (a : ℤ) - N = (b : ℤ) - N := h
  omega

theorem cubeNodes_nodup (N : ℕ) : (cubeNodes N).Nodup := by
  unfold cubeNodes
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun b _ => ?_, ?_⟩
    · exact (cubeRange_nodup N).map (fun c c' h => by simpa using congrFun h 2)
    · refine (cubeRange_nodup N).imp (fun {b b'} hne => ?_)
      intro x hx hx'
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨c', _, h⟩ := List.mem_map.mp hx'
      exact hne (by simpa using (congrFun h 1).symm)
  · refine (cubeRange_nodup N).imp (fun {a a'} hne => ?_)
    intro x hx hx'
    obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    obtain ⟨b', _, hb'⟩ := List.mem_flatMap.mp hx'
    obtain ⟨c', _, h⟩ := List.mem_map.mp hb'
    exact hne (by simpa using (congrFun h 0).symm)

theorem halfNodes_nodup (N : ℕ) : (halfNodes N).Nodup := (cubeNodes_nodup N).filter _

theorem filterMap_index (l : List IntVec) (f : IntVec → Option JTerm)
    (hf : ∀ n t, f n = some t → t.index = n) :
    (l.filterMap f).map JTerm.index = l.filter (fun n => (f n).isSome) := by
  induction l with
  | nil => rfl
  | cons n rest ih =>
    cases hfn : f n with
    | none => simp [hfn, ih]
    | some t => simp [hfn, ih, hf n t hfn]

theorem filter_lin_kind (A : List JTerm) (k k' : Kind) (hA : ∀ t ∈ A, t.kind = k') :
    (A.map JTerm.lin).filter (fun t => decide (t.kind = k)) =
      if k' = k then A.map JTerm.lin else [] := by
  split_ifs with he
  · rw [List.filter_eq_self]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    simp [JTerm.lin, hA u hu, he]
  · rw [List.filter_eq_nil_iff]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    simp [JTerm.lin, hA u hu, he]

theorem lin_index (A : List JTerm) : (A.map JTerm.lin).map LinTerm.index = A.map JTerm.index := by
  simp [List.map_map, Function.comp_def, JTerm.lin]

theorem support_parts (s L : ℚ) (N : ℕ) (S : Cell) :
    (∀ t ∈ (cubeNodes N).filterMap (mkTerm s L S .cross), t.kind = .cross) ∧
    (∀ t ∈ (halfNodes N).filterMap (mkTerm s L S .period), t.kind = .period) ∧
    (∀ t ∈ (halfNodes N).filterMap (mkTerm s L S .wave), t.kind = .wave) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro t ht
    obtain ⟨n, _, hn⟩ := List.mem_filterMap.mp ht
    exact (mkTerm_kind hn).1

theorem kindIdx_support (s L : ℚ) (N : ℕ) (S : Cell) :
    kindIdx .cross ((buildSupport s L N S).map JTerm.lin) =
      (cubeNodes N).filter (fun n => (mkTerm s L S .cross n).isSome) ∧
    kindIdx .period ((buildSupport s L N S).map JTerm.lin) =
      (halfNodes N).filter (fun n => (mkTerm s L S .period n).isSome) ∧
    kindIdx .wave ((buildSupport s L N S).map JTerm.lin) =
      (halfNodes N).filter (fun n => (mkTerm s L S .wave n).isSome) := by
  obtain ⟨hA, hB, hC⟩ := support_parts s L N S
  have ix : ∀ (l : List IntVec) (k : Kind), ∀ n t, mkTerm s L S k n = some t → t.index = n :=
    fun _ k n t h => (mkTerm_kind h).2
  unfold kindIdx buildSupport
  simp only [List.map_append, List.filter_append, filter_lin_kind _ _ _ hA, filter_lin_kind _ _ _ hB,
    filter_lin_kind _ _ _ hC]
  have comp : (LinTerm.index ∘ JTerm.lin) = JTerm.index := by
    funext t
    rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> rw [comp, filterMap_index _ _ (ix [] _)]

theorem buildSupport_structure (s L : ℚ) (N : ℕ) (S : Cell) :
    structureOk ((buildSupport s L N S).map JTerm.lin) = true := by
  obtain ⟨hx, hp, hw⟩ := kindIdx_support s L N S
  unfold structureOk
  rw [hx, hp, hw]
  refine decide_eq_true ⟨List.filter_sublist.nodup (cubeNodes_nodup N),
    List.filter_sublist.nodup (halfNodes_nodup N), List.filter_sublist.nodup (halfNodes_nodup N),
    ?_, ?_⟩
  · intro n hn
    have h := (List.mem_filter.mp ((List.mem_filter.mp hn).1)).2
    exact of_decide_eq_true h
  · intro n hn
    have h := (List.mem_filter.mp ((List.mem_filter.mp hn).1)).2
    exact of_decide_eq_true h

theorem buildSupport_valid (s L : ℚ) (N : ℕ) (S : Cell) :
    ∀ t ∈ buildSupport s L N S, 0 ≤ t.rhi ∧ t.Valid s S := by
  intro t ht
  unfold buildSupport at ht
  rcases List.mem_append.mp ht with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · obtain ⟨n, _, hn⟩ := List.mem_filterMap.mp h1
      exact mkTerm_sound s L S .cross n t hn (fun h => absurd rfl h)
    · obtain ⟨n, hmem, hn⟩ := List.mem_filterMap.mp h2
      exact mkTerm_sound s L S .period n t hn
        (fun _ => of_decide_eq_true (List.mem_filter.mp hmem).2)
  · obtain ⟨n, hmem, hn⟩ := List.mem_filterMap.mp h3
    exact mkTerm_sound s L S .wave n t hn
      (fun _ => of_decide_eq_true (List.mem_filter.mp hmem).2)

/-! ### The leaf -/

theorem aggConst_lin (ts : List JTerm) : aggConst (ts.map JTerm.lin) = 0 := by
  simp [aggConst, List.map_map, Function.comp_def, JTerm.lin]

theorem cornerValue_eq (ts : List JTerm) (c : Fin 8 → ℚ) :
    cornerValue (aggOf ts) c = centerConst ts +
      aggValueQ (aggConst (ts.map JTerm.lin)) (fun j => aggWeight (ts.map JTerm.lin) j) c := by
  rw [aggConst_lin]
  unfold cornerValue aggOf aggValueQ
  simp only [zero_add]
  congr 1

theorem bools_all {f : Bool → Bool} (h : bools.all f = true) (x : Bool) : f x = true := by
  cases x <;> simp_all [bools]

theorem vec8_eta (bits : Axis → Bool) :
    (![bits 0, bits 1, bits 2, bits 3, bits 4, bits 5, bits 6, bits 7] : Axis → Bool) = bits := by
  funext i
  fin_cases i <;> rfl

/-- **Soundness of the F leaf check**: every valid point of the leaf has
energy strictly above FCC. -/
theorem fLeafCheck_sound (s L : ℚ) (N : ℕ) (S b : Cell) (ok : fLeafCheck s L N S b = true)
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) := by
  unfold fLeafCheck fLeafCheckAgg at ok
  obtain ⟨guards, corners⟩ := Bool.and_eq_true_iff.mp ok
  unfold leafGuards at guards
  simp only [Bool.and_eq_true, decide_eq_true_eq] at guards
  obtain ⟨⟨hs, hM⟩, ⟨⟨⟨⟨⟨inside, lo0⟩, lo1⟩, ord⟩, hsc⟩, hlo⟩⟩ := guards
  set ts := buildSupport s L N S
  have hval := buildSupport_valid s L N S
  have hMts : 0 < mass ts := hM
  have cornerOk : ∀ bits : Axis → Bool, fCornerOk s (aggOf ts) (cornerRat b bits) = true := by
    intro bits
    have h := bools_all (bools_all (bools_all (bools_all (bools_all (bools_all (bools_all
      (bools_all corners (bits 0)) (bits 1)) (bits 2)) (bits 3)) (bits 4)) (bits 5)) (bits 6)) (bits 7)
    unfold cornerOf at h
    rw [vec8_eta] at h
    exact h
  refine Jensen.jensen_fcc_corners s hs S b ts (fun t ht => (hval t ht).2) (fun t ht => (hval t ht).1)
    (buildSupport_structure s L N S) hMts inside lo0 lo1 ord
    (fun bits => ((expLoZ (cornerValue (aggOf ts) (cornerRat b bits) / (aggOf ts).M) : ℚ) / Sz))
    ?_ hsc hlo ?_ p hp hv
  · intro bits
    have e := expLoZ_le (cornerValue (aggOf ts) (cornerRat b bits) / (aggOf ts).M)
    have hm : (aggOf ts).M = mass ts := rfl
    have hc : (((cornerValue (aggOf ts) (cornerRat b bits) / (aggOf ts).M : ℚ)) : ℝ) =
        (((centerConst ts + aggValueQ (aggConst (ts.map JTerm.lin))
          (fun j => aggWeight (ts.map JTerm.lin) j) (cornerRat b bits) : ℚ)) : ℝ) / (mass ts : ℝ) := by
      rw [cornerValue_eq, hm]
      push_cast
      ring
    rw [hc] at e
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    exact e
  · intro bits
    have h := cornerOk bits
    unfold fCornerOk at h
    exact of_decide_eq_true h

/-- The F leaf check as a route result on `good` points. -/
theorem fLeafCheck_route (s L : ℚ) (N : ℕ) (S b : Cell) (ok : fLeafCheck s L N S b = true)
    (p : Chart) (hp : b.Mem p) (gp : good p) : Route.result .strictFCC p :=
  fLeafCheck_sound s L N S b ok p hp gp.1

end BccSharp.Coulomb.CompactCover.Jensen.Fix
