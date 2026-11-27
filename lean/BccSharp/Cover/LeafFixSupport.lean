import BccSharp.Cover.LeafFix
import BccSharp.Cover.OverlayFixSound

set_option autoImplicit false

/-! # Soundness of the fixed-point supports (`BccSharp.Cover.LeafFix`)

* Rounding: `fmulQ_le`, `le_cmulQ`, `qF_mem`, `negF_mem`, `cdivZ_le`.
* The literal constants, each checked once: `piF_mem` (against the Machin
  enclosure `Constants.piInput`), `sqrtPiF_mem`, `acF_mem` (against the cube-root
  witness of `2 a_c`), `bcc_le`, `fcc_le`, `gap_le` (against the Constants brackets).
* Point exponentials and cosines: `expUpZ_ge`, `expLoZ_le`, `expUpQ_ge`,
  `expLoQ_le`, `cosLoQ_le`, from the Overlay lemmas `expPosPt_mem`,
  `expNegPt_mem`, `cosRange_mem`.
* The erfc series: `serLoop_spec` (the interval term recurrence encloses the
  terms and the even and odd partial sums), `series_split`, and `halfF_mem`
  (`G(1/2, a²)` through `Erfc.sqrt_remainder` and `halfKernel_formula`).
* The three witness families: `directZ_valid`, `waveZ_valid`, `perspZ_valid`,
  each stating `ZValid`: the term lies below its screened series summand at
  every valid point of the support box.
* The support: `support_facts`, the energy lower bound and the separate
  concavity of the minorant `(K + Σ W_j feat_j − Σ c y eʸ − 2s − 2/s²)/(2 a_c)`
  built from the literal aggregate. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.LeafFix
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Screened
open BccSharp.Coulomb.CompactCover.DirectRoute (lexPositive lex_ne endpoints scaleWitness
  scaleInput)
open BccSharp.Coulomb.BravaisCover (KernelKind kernelValue kernelSlope halfKernel_formula
  cubeRootCheck)
open BccSharp.Coulomb.CompactCover.Stage2 (globalTangent)

/-! ### Rounding -/

theorem fmulQ_le (z : ℤ) (q : ℚ) : (fmulQ z q : ℝ) ≤ (z : ℝ) * q := by
  unfold fmulQ
  have h := fdiv_le (z * q.num) (q.den : ℤ) (by exact_mod_cast q.pos)
  have e : (z : ℝ) * (q : ℝ) = ((z * q.num : ℤ) : ℝ) / ((q.den : ℤ) : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    ring
  rw [e]
  exact h

theorem le_cmulQ (z : ℤ) (q : ℚ) : (z : ℝ) * q ≤ (cmulQ z q : ℝ) := by
  unfold cmulQ
  have h := le_cdiv (z * q.num) (q.den : ℤ) (by exact_mod_cast q.pos)
  have e : (z : ℝ) * (q : ℝ) = ((z * q.num : ℤ) : ℝ) / ((q.den : ℤ) : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    ring
  rw [e]
  exact h

theorem qF_mem (q : ℚ) : (qF q).Mem (q : ℝ) := ofRat_mem ⟨le_rfl, le_rfl⟩

theorem negF_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (negF a).Mem (-x) := by
  unfold negF FI.Mem at *
  push_cast
  rw [neg_div, neg_div]
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem halfFI_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (halfFI a).Mem (x / 2) := half_mem hx

theorem cdivZ_le {n m d : ℤ} (hd : 0 < d) (h : n ≤ m * d) : cdivZ n d ≤ m := by
  unfold cdivZ
  have : -m ≤ (-n) / d := by
    rw [Int.le_ediv_iff_mul_le hd]
    linarith
  linarith

theorem Sz_eq : (Sz : ℝ) = 2 ^ 96 := by norm_num [Sz]

/-! ### The literal constants -/

theorem piF_mem : piF.Mem Real.pi := by
  have h := endpoints Constants.piInput_sound
  have l : ((piF.lo : ℚ) / (Sz : ℚ)) ≤ Constants.piInput.lo := by decide +kernel
  have u : Constants.piInput.hi ≤ ((piF.hi : ℚ) / (Sz : ℚ)) := by decide +kernel
  have l' := (Rat.cast_le (K := ℝ)).mpr l
  have u' := (Rat.cast_le (K := ℝ)).mpr u
  push_cast at l' u'
  exact ⟨l'.trans h.1, h.2.trans u'⟩

theorem piF_hi_pos : (0 : ℝ) < (piF.hi : ℝ) := by
  have h := piF_mem.2
  have sp := Sz_pos
  have : (0 : ℝ) < (piF.hi : ℝ) / Sz := Real.pi_pos.trans_le h
  exact (div_pos_iff_of_pos_right sp).mp this

theorem sqrtPiF_mem : sqrtPiF.Mem (Real.sqrt Real.pi) := by
  have hp := piF_mem
  have sp := Sz_pos
  have l2 : sqrtPiF.lo * sqrtPiF.lo ≤ piF.lo * Sz := by decide +kernel
  have h2 : piF.hi * Sz ≤ sqrtPiF.hi * sqrtPiF.hi := by decide +kernel
  have l0 : (0 : ℤ) ≤ sqrtPiF.lo := by decide +kernel
  have h0 : (0 : ℤ) ≤ sqrtPiF.hi := by decide +kernel
  have l0r : (0 : ℝ) ≤ sqrtPiF.lo := by exact_mod_cast l0
  have h0r : (0 : ℝ) ≤ sqrtPiF.hi := by exact_mod_cast h0
  have l2r : ((sqrtPiF.lo : ℝ) / Sz) ^ 2 ≤ (piF.lo : ℝ) / Sz := by
    rw [div_pow, div_le_div_iff₀ (by positivity) sp]
    have : (sqrtPiF.lo : ℝ) * sqrtPiF.lo ≤ (piF.lo : ℝ) * Sz := by exact_mod_cast l2
    nlinarith
  have h2r : (piF.hi : ℝ) / Sz ≤ ((sqrtPiF.hi : ℝ) / Sz) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ sp (by positivity)]
    have : (piF.hi : ℝ) * Sz ≤ (sqrtPiF.hi : ℝ) * sqrtPiF.hi := by exact_mod_cast h2
    nlinarith
  constructor
  · exact (Real.le_sqrt (div_nonneg l0r sp.le) Real.pi_pos.le).mpr (l2r.trans hp.1)
  · exact (Real.sqrt_le_left (div_nonneg h0r sp.le)).mpr (hp.2.trans h2r)

theorem acF_mem : acF.Mem (2 * ac) := by
  have cube : cubeRootCheck scaleWitness scaleInput = true := by decide +kernel
  obtain ⟨lo, hi⟩ := ac_bounds cube
  have l : ((acF.lo : ℚ) / (Sz : ℚ)) ≤ 2 * scaleWitness.lower := by decide +kernel
  have u : 2 * scaleWitness.upper ≤ ((acF.hi : ℚ) / (Sz : ℚ)) := by decide +kernel
  have l' := (Rat.cast_le (K := ℝ)).mpr l
  have u' := (Rat.cast_le (K := ℝ)).mpr u
  push_cast at l' u'
  exact ⟨by linarith, by linarith⟩

theorem acF_lo_pos : (0 : ℤ) < acF.lo := by decide +kernel

theorem bcc_le : energy bcc ≤ (bccHiZ : ℝ) / Sz := by
  have h : energy bcc ≤ (Constants.bccBracket.hi : ℝ) := (Constants.reference_bounds .bcc).2
  have c : Constants.bccBracket.hi ≤ ((bccHiZ : ℚ) / (Sz : ℚ)) := by decide +kernel
  have c' := (Rat.cast_le (K := ℝ)).mpr c
  push_cast at c'
  linarith

theorem fcc_le : energy fcc ≤ (fccHiZ : ℝ) / Sz := by
  have h : energy fcc ≤ (Constants.fccBracket.hi : ℝ) := (Constants.reference_bounds .fcc).2
  have c : Constants.fccBracket.hi ≤ ((fccHiZ : ℚ) / (Sz : ℚ)) := by decide +kernel
  have c' := (Rat.cast_le (K := ℝ)).mpr c
  push_cast at c'
  linarith

theorem gap_le : gap ≤ (gapHiZ : ℝ) / Sz := by
  have h : gap ≤ (Constants.gapBracket.hi : ℝ) := Constants.reference_gap_checked.1.2
  have c : Constants.gapBracket.hi ≤ ((gapHiZ : ℚ) / (Sz : ℚ)) := by decide +kernel
  have c' := (Rat.cast_le (K := ℝ)).mpr c
  push_cast at c'
  linarith

theorem gap_pos : 0 < gap := Constants.reference_gap_checked.2

/-! ### Exponentials and cosines at points -/

theorem expUpZ_ge {x : ℤ} (hx : x ≤ (S64 : ℤ)) :
    Real.exp ((x : ℝ) / Sz) ≤ (expUpZ x : ℝ) / Sz := by
  have sp := Sz_pos
  unfold expUpZ
  split_ifs with h
  · have hn : x.toNat ≤ S64 := Int.toNat_le.mpr hx
    have e : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h
    have m := (expPosPt_mem x.toNat hn).2
    rw [e] at m
    rw [le_div_iff₀ sp]
    push_cast
    exact m
  · have e : (((-x).toNat : ℕ) : ℝ) = -(x : ℝ) := by
      have : (((-x).toNat : ℕ) : ℤ) = -x := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have m := (expNegPt_mem (-x).toNat).2
    rw [e, neg_div, neg_neg] at m
    exact m

theorem expLoZ_le {x : ℤ} (hx : x ≤ (S64 : ℤ)) :
    (expLoZ x : ℝ) / Sz ≤ Real.exp ((x : ℝ) / Sz) := by
  have sp := Sz_pos
  unfold expLoZ
  split_ifs with h
  · have hn : x.toNat ≤ S64 := Int.toNat_le.mpr hx
    have e : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h
    have m := (expPosPt_mem x.toNat hn).1
    rw [e] at m
    rw [div_le_iff₀ sp]
    push_cast
    exact m
  · have e : (((-x).toNat : ℕ) : ℝ) = -(x : ℝ) := by
      have : (((-x).toNat : ℕ) : ℤ) = -x := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have m := (expNegPt_mem (-x).toNat).1
    rw [e, neg_div, neg_neg] at m
    exact m

theorem qF_hi_le {r : ℚ} (hr : r ≤ 64) : (qF r).hi ≤ (S64 : ℤ) := by
  unfold qF ofRat
  dsimp only
  apply cdivZ_le (by exact_mod_cast r.pos)
  have h1 : r.num ≤ 64 * (r.den : ℤ) := by
    have e : (r.num : ℚ) = r * r.den := (Rat.mul_den_eq_num r).symm
    have d0 : (0 : ℚ) ≤ r.den := by positivity
    have : (r.num : ℚ) ≤ 64 * r.den := by rw [e]; nlinarith
    exact_mod_cast this
  have hS : (S64 : ℤ) = 64 * Sz := by norm_num [S64, Sz]
  rw [hS]
  nlinarith [Sz_posZ]

theorem qF_lo_le {r : ℚ} (hr : r ≤ 64) : (qF r).lo ≤ (S64 : ℤ) := by
  have h := (qF_mem r).1
  have sp := Sz_pos
  have hr' : (r : ℝ) ≤ 64 := by exact_mod_cast hr
  have : ((qF r).lo : ℝ) ≤ 64 * Sz := by
    rw [div_le_iff₀ sp] at h
    nlinarith
  have hS : ((S64 : ℤ) : ℝ) = 64 * Sz := by norm_num [S64, Sz]
  exact_mod_cast (show ((qF r).lo : ℝ) ≤ ((S64 : ℤ) : ℝ) by rw [hS]; exact this)

theorem expUpQ_ge {r : ℚ} (hr : r ≤ 64) : Real.exp (r : ℝ) ≤ (expUpQ r : ℝ) / Sz :=
  (Real.exp_le_exp.mpr (qF_mem r).2).trans (expUpZ_ge (qF_hi_le hr))

theorem expLoQ_le {r : ℚ} (hr : r ≤ 64) : (expLoQ r : ℝ) / Sz ≤ Real.exp (r : ℝ) :=
  (expLoZ_le (qF_lo_le hr)).trans (Real.exp_le_exp.mpr (qF_mem r).1)

theorem cosLoQ_le (v : ℚ) : (cosLoQ v : ℝ) / Sz ≤ Real.cos (2 * Real.pi * v) :=
  (cosRange_mem (A := (qF v).lo) (B := (qF v).hi) (qF_mem v)).1

/-! ### The erfc series -/

/-- The term `q^k/k!`. -/
def tauR (q : ℝ) (k : ℕ) : ℝ := q ^ k / (k.factorial : ℝ)

/-- The even and the odd part of `Ser(q, N) = Σ_{k<N} (−q)^k/(k!(2k+1))`. -/
def evenSum (q : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, if j % 2 = 0 then tauR q j / (2 * j + 1) else 0

def oddSum (q : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, if j % 2 = 0 then 0 else tauR q j / (2 * j + 1)

theorem serScale_eq : (serScale : ℝ) = (Sz : ℝ) * 2 ^ 64 := by norm_num [serScale, Sz]

/-- The interval recurrence of `serLoop` encloses `2^160 q^N/N!` and the even and
odd partial sums of `2^160 Ser(q, N)`, for `q = y/S`. -/
theorem serLoop_spec (y N : ℕ) :
    ((serLoop y N).1 : ℝ) ≤ serScale * tauR ((y : ℝ) / Sz) N ∧
    (serScale : ℝ) * tauR ((y : ℝ) / Sz) N ≤ (serLoop y N).2.1 ∧
    ((serLoop y N).2.2.1 : ℝ) ≤ serScale * evenSum ((y : ℝ) / Sz) N ∧
    (serScale : ℝ) * evenSum ((y : ℝ) / Sz) N ≤ (serLoop y N).2.2.2.1 ∧
    ((serLoop y N).2.2.2.2.1 : ℝ) ≤ serScale * oddSum ((y : ℝ) / Sz) N ∧
    (serScale : ℝ) * oddSum ((y : ℝ) / Sz) N ≤ (serLoop y N).2.2.2.2.2 := by
  induction N with
  | zero =>
    simp [serLoop, tauR, evenSum, oddSum]
  | succ N ih =>
    set q : ℝ := (y : ℝ) / Sz with hq
    obtain ⟨t1, t2, e1, e2, o1, o2⟩ := ih
    have hstep : serLoop y (N + 1) = serStep y N (serLoop y N) := rfl
    rw [hstep]
    set st := serLoop y N with hst
    have sp := Sz_pos
    have q0 : 0 ≤ q := by positivity
    have tauS : tauR q (N + 1) = tauR q N * q / (N + 1) := by
      unfold tauR
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have mR : ((S * (N + 1) : ℕ) : ℝ) = Sz * (N + 1) := by push_cast; rw [S_eq]
    have yfac : (0 : ℝ) ≤ (y : ℝ) / (Sz * (N + 1)) := by positivity
    have qfac : q / (N + 1) = (y : ℝ) / (Sz * (N + 1)) := by
      rw [hq]
      field_simp
    have lo' : (((st.1 * y / (S * (N + 1)) : ℕ) : ℝ)) ≤ serScale * tauR q (N + 1) := by
      refine (fdivN_le _ _).trans ?_
      rw [mR, tauS]
      push_cast
      have h := mul_le_mul_of_nonneg_right t1 yfac
      calc (st.1 : ℝ) * y / (Sz * (N + 1)) = (st.1 : ℝ) * ((y : ℝ) / (Sz * (N + 1))) := by ring
        _ ≤ serScale * tauR q N * ((y : ℝ) / (Sz * (N + 1))) := h
        _ = serScale * (tauR q N * q / (N + 1)) := by rw [← qfac]; ring
    have hi' : (serScale : ℝ) * tauR q (N + 1) ≤ ((cdivN (st.2.1 * y) (S * (N + 1)) : ℕ) : ℝ) := by
      refine le_trans ?_ (cdivN_ge _ _ (Nat.mul_pos S_pos (Nat.succ_pos N)))
      rw [mR, tauS]
      push_cast
      have h := mul_le_mul_of_nonneg_right t2 yfac
      calc serScale * (tauR q N * q / (N + 1)) = serScale * tauR q N * ((y : ℝ) / (Sz * (N + 1))) := by
            rw [← qfac]; ring
        _ ≤ (st.2.1 : ℝ) * ((y : ℝ) / (Sz * (N + 1))) := h
        _ = (st.2.1 : ℝ) * y / (Sz * (N + 1)) := by ring
    have d0 : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
    have dR : (((2 * N + 1 : ℕ)) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    have sLo : (((st.1 / (2 * N + 1) : ℕ)) : ℝ) ≤ serScale * (tauR q N / (2 * N + 1)) := by
      refine (fdivN_le _ _).trans ?_
      rw [dR, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right t1 d0.le
    have sHi : (serScale : ℝ) * (tauR q N / (2 * N + 1)) ≤ ((cdivN st.2.1 (2 * N + 1) : ℕ) : ℝ) := by
      refine le_trans ?_ (cdivN_ge _ _ (by omega))
      rw [dR, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right t2 d0.le
    have evS : evenSum q (N + 1) =
        evenSum q N + (if N % 2 = 0 then tauR q N / (2 * N + 1) else 0) := by
      unfold evenSum
      rw [Finset.sum_range_succ]
    have odS : oddSum q (N + 1) =
        oddSum q N + (if N % 2 = 0 then 0 else tauR q N / (2 * N + 1)) := by
      unfold oddSum
      rw [Finset.sum_range_succ]
    unfold serStep
    dsimp only
    by_cases hN : N % 2 = 0
    · rw [ite_eq_left hN]
      rw [ite_eq_left hN] at evS odS
      rw [evS, odS]
      push_cast
      refine ⟨lo', hi', ?_, ?_, ?_, ?_⟩
      · rw [mul_add]; linarith [e1, sLo]
      · rw [mul_add]; linarith [e2, sHi]
      · linarith [o1]
      · linarith [o2]
    · rw [ite_eq_right hN]
      rw [ite_eq_right hN] at evS odS
      rw [evS, odS]
      push_cast
      refine ⟨lo', hi', ?_, ?_, ?_, ?_⟩
      · linarith [e1]
      · linarith [e2]
      · rw [mul_add]; linarith [o1, sLo]
      · rw [mul_add]; linarith [o2, sHi]

/-- The series of `Erfc.series` is the even part minus the odd part. -/
theorem series_split (q : ℚ) (N : ℕ) :
    ((Erfc.series q N : ℚ) : ℝ) = evenSum (q : ℝ) N - oddSum (q : ℝ) N := by
  induction N with
  | zero => simp [Erfc.series, evenSum, oddSum]
  | succ N ih =>
    have step : Erfc.series q (N + 1) =
        Erfc.series q N + (-q) ^ N / ((N.factorial : ℚ) * ((2 * N + 1 : ℕ) : ℚ)) := by
      unfold Erfc.series
      rw [Finset.sum_range_succ]
    rw [step]
    push_cast
    rw [ih]
    unfold evenSum oddSum
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    unfold tauR
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · rw [ite_eq_left h, ite_eq_left h]
      have ev : Even N := Nat.even_iff.mpr h
      rw [ev.neg_pow, ← div_div]
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have od : Odd N := Nat.odd_iff.mpr h
      rw [od.neg_pow, neg_div, ← div_div]
      ring

theorem gKernel_half_nonneg (t : ℝ) : 0 ≤ gKernel (1/2) t := ScreenedSeries.gKernel_nonneg _ _

theorem two64_pos : (0 : ℤ) < two64 := by norm_num [two64]
theorem two64_eq : ((two64 : ℤ) : ℝ) = 2 ^ 64 := by norm_num [two64]
theorem two112_eq : ((two112 : ℤ) : ℝ) = 2 ^ 112 := by norm_num [two112]
theorem serScale_pos : (0 : ℝ) < serScale := by norm_num [serScale]

/-- From bounds at the series scale `2^160 = 2^64 S` to an interval at scale `S`. -/
theorem fi_of_scaled {L U : ℤ} {x : ℝ} (hL : (L : ℝ) ≤ serScale * x) (hU : (serScale : ℝ) * x ≤ U) :
    (⟨L / two64, cdivZ U two64⟩ : FI).Mem x := by
  have sp := Sz_pos
  have PS := serScale_eq
  constructor
  · refine (div_le_div_of_nonneg_right (fdiv_le L two64 two64_pos) sp.le).trans ?_
    rw [two64_eq, div_div, div_le_iff₀ (by positivity)]
    rw [PS] at hL
    linarith
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv U two64 two64_pos) sp.le)
    rw [two64_eq, div_div, le_div_iff₀ (by positivity)]
    rw [PS] at hU
    linarith

/-- **The half kernel at `a²`.** For `a = A/2^48`, `halfF A N` encloses
`G(1/2, a²)`, under the series guard `a²/(N + 1) ≤ 1/2`. -/
theorem halfF_mem (A N : ℕ) (hA : 0 < A) (hg : 2 * (A * A) ≤ S * (N + 1)) :
    (halfF A N).Mem (gKernel (1/2) (((A : ℝ) / 2 ^ 48) ^ 2)) := by
  have sp := Sz_pos
  set a : ℝ := (A : ℝ) / 2 ^ 48 with ha
  have a0 : 0 < a := by positivity
  set qr : ℝ := ((A * A : ℕ) : ℝ) / Sz with hqr
  have qa : qr = a ^ 2 := by rw [hqr, ha, Sz_eq]; push_cast; ring
  set qQ : ℚ := ((A * A : ℕ) : ℚ) / (Sz : ℚ) with hqQ
  have qR : ((qQ : ℚ) : ℝ) = qr := by rw [hqQ, hqr]; push_cast; ring
  have sqa : Real.sqrt ((qQ : ℚ) : ℝ) = a := by rw [qR, qa, Real.sqrt_sq a0.le]
  have SzQ : (0 : ℚ) < (Sz : ℚ) := by norm_num [Sz]
  have hq0 : 0 ≤ qQ := div_nonneg (by positivity) SzQ.le
  have guard : qQ / ((N + 1 : ℕ) : ℚ) ≤ 1 / 2 := by
    have h1 : ((2 * (A * A) : ℕ) : ℚ) ≤ ((S * (N + 1) : ℕ) : ℚ) := by exact_mod_cast hg
    have hSz : ((S : ℕ) : ℚ) = (Sz : ℚ) := by norm_num [S, Sz]
    push_cast at h1
    rw [hSz] at h1
    rw [hqQ, div_div, div_le_iff₀ (by positivity)]
    push_cast
    linarith
  have rem := Erfc.sqrt_remainder hq0 N guard
  rw [sqa, qR] at rem
  have form := halfKernel_formula (pow_pos a0 2)
  rw [Real.sqrt_sq a0.le] at form
  set G := gKernel (1/2) (a ^ 2) with hG
  set E := Gaussian.erfcIntegral a with hE
  set Ser : ℝ := ((Erfc.series qQ N : ℚ) : ℝ) with hSer
  have pi0 := Real.sqrt_pos.mpr Real.pi_pos
  -- |G − (√π/a − 2 Ser)| ≤ 4 q^N/N!
  have key : |G - (Real.sqrt Real.pi / a - 2 * Ser)| ≤ 4 * tauR qr N := by
    have e : G - (Real.sqrt Real.pi / a - 2 * Ser) =
        Real.sqrt Real.pi / a * (E - (1 - 2 * a / Real.sqrt Real.pi * Ser)) := by
      rw [form]
      field_simp
    rw [e, abs_mul, abs_of_pos (div_pos pi0 a0)]
    calc Real.sqrt Real.pi / a * |E - (1 - 2 * a / Real.sqrt Real.pi * Ser)|
        ≤ Real.sqrt Real.pi / a * (4 * a * qr ^ N / (Real.sqrt Real.pi * (N.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left rem (div_pos pi0 a0).le
      _ = 4 * tauR qr N := by
          unfold tauR
          field_simp
  have ab := abs_le.mp key
  -- the series enclosure
  obtain ⟨_, t2, e1, e2, o1, o2⟩ := serLoop_spec (A * A) N
  rw [← hqr] at t2 e1 e2 o1 o2
  have split := series_split qQ N
  rw [qR, ← hSer] at split
  set st := serLoop (A * A) N with hst
  have P0 := serScale_pos
  have PS := serScale_eq
  -- the root `√π/a`, scaled
  have Apos : (0 : ℝ) < A := by exact_mod_cast hA
  have AZ : (0 : ℤ) < (A : ℤ) := by exact_mod_cast hA
  have sq := sqrtPiF_mem
  have rootE : (serScale : ℝ) * (Real.sqrt Real.pi / a) = Real.sqrt Real.pi * Sz * 2 ^ 112 / A := by
    rw [PS, ha, Sz_eq]
    field_simp
  have rootLo : (((sqrtPiF.lo * two112) / (A : ℤ) : ℤ) : ℝ) ≤ serScale * (Real.sqrt Real.pi / a) := by
    refine (fdiv_le _ _ AZ).trans ?_
    rw [rootE]
    have h1 := sq.1
    rw [div_le_iff₀ sp] at h1
    push_cast
    rw [two112_eq]
    apply div_le_div_of_nonneg_right _ Apos.le
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ 112)
    linarith
  have rootHi : (serScale : ℝ) * (Real.sqrt Real.pi / a) ≤
      ((cdivZ (sqrtPiF.hi * two112) (A : ℤ) : ℤ) : ℝ) := by
    refine le_trans ?_ (le_cdiv _ _ AZ)
    rw [rootE]
    have h1 := sq.2
    rw [le_div_iff₀ sp] at h1
    push_cast
    rw [two112_eq]
    apply div_le_div_of_nonneg_right _ Apos.le
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ 112)
    linarith
  -- multiply the error bound by the scale
  have lowG : (serScale : ℝ) * (Real.sqrt Real.pi / a) - 2 * (serScale * Ser) -
      4 * (serScale * tauR qr N) ≤ serScale * G := by
    have h : Real.sqrt Real.pi / a - 2 * Ser - 4 * tauR qr N ≤ G := by linarith [ab.1]
    have := mul_le_mul_of_nonneg_left h P0.le
    linarith
  have highG : (serScale : ℝ) * G ≤ (serScale : ℝ) * (Real.sqrt Real.pi / a) -
      2 * (serScale * Ser) + 4 * (serScale * tauR qr N) := by
    have h : G ≤ Real.sqrt Real.pi / a - 2 * Ser + 4 * tauR qr N := by linarith [ab.2]
    have := mul_le_mul_of_nonneg_left h P0.le
    linarith
  have serEq : (serScale : ℝ) * Ser = serScale * evenSum qr N - serScale * oddSum qr N := by
    rw [split]; ring
  apply fi_of_scaled
  · push_cast
    linarith
  · push_cast
    linarith

/-! ### Terms and their meaning -/

/-- The perspective penalty `y eʸ` at `y = π Q*/s²`. -/
def nlVal (s : ℚ) (m : IntVec) (p : Chart) : ℝ :=
  Real.pi * dualQ m p / (s : ℝ) ^ 2 * Real.exp (Real.pi * dualQ m p / (s : ℝ) ^ 2)

/-- The affine part of an integer term, with coefficients `c/S`, `a/S`, `b/S`. -/
def ZTerm.lin (t : ZTerm) : LinTerm :=
  ⟨t.kind, t.index, (t.c : ℚ) / (Sz : ℚ), (t.a : ℚ) / (Sz : ℚ), (t.b : ℚ) / (Sz : ℚ)⟩

/-- The value of a term: its affine part minus `(nl/S)` times the penalty. -/
def ZTerm.eval (s : ℚ) (t : ZTerm) (p : Chart) : ℝ :=
  t.lin.eval p - (t.nl : ℝ) / Sz * nlVal s t.index p

/-- A term is valid on a box at screening `s` when its slope is nonpositive,
its penalty coefficient nonnegative, and it lies below its screened series
summand at every valid point of the box. -/
def ZValid (s : ℚ) (box : Cell) (t : ZTerm) : Prop :=
  t.a ≤ 0 ∧ 0 ≤ t.nl ∧
    ∀ p, box.Mem p → (chartPoint p).Valid → t.eval s p ≤ physicalS s t.kind t.index p

theorem ZTerm.eval_eq (s : ℚ) (t : ZTerm) (p : Chart) :
    t.eval s p = (t.c : ℝ) / Sz + (t.a : ℝ) / Sz * termQ t.kind t.index p +
      (t.b : ℝ) / Sz * phaseT t.index p - (t.nl : ℝ) / Sz * nlVal s t.index p := by
  unfold ZTerm.eval ZTerm.lin LinTerm.eval
  push_cast
  ring

/-! ### Direct tangents -/

theorem directZ_valid (s : ℚ) (w : DWit) (ok : directOk s w = true) (box : Cell) :
    ZValid s box (directZ s w) := by
  simp only [directOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at ok
  obtain ⟨⟨⟨⟨spos, Apos⟩, guard⟩, _⟩, lexOk⟩ := ok
  have sp := Sz_pos
  have sr : (0 : ℝ) < s := by exact_mod_cast spos
  set a : ℝ := (w.A : ℝ) / 2 ^ 48 with ha
  have a0 : 0 < a := by positivity
  have a2 : a ^ 2 = ((w.A * w.A : ℕ) : ℝ) / Sz := by rw [ha, Sz_eq]; push_cast; ring
  set G := gKernel (1/2) (a ^ 2) with hG
  set E := Real.exp (-(a ^ 2)) with hE
  have hGm := halfF_mem w.A w.N Apos guard
  rw [← ha, ← hG] at hGm
  have hEm : (expNegPt (w.A * w.A)).Mem E := by
    have h := expNegPt_mem (w.A * w.A)
    rw [hE, a2]
    exact h
  have G0 : 0 ≤ G := gKernel_half_nonneg _
  have E0 : 0 < E := Real.exp_pos _
  set g := halfF w.A w.N with hg
  set e := expNegPt (w.A * w.A) with he
  have g1 := hGm.1
  have g2 := hGm.2
  have e1 := hEm.1
  have e2 := hEm.2
  rw [div_le_iff₀ sp] at g1 e1
  rw [le_div_iff₀ sp] at g2 e2
  -- the intercept `I = (3/2) G + E`
  have iLo : ((3 * g.lo / 2 + e.lo : ℤ) : ℝ) ≤ Sz * (3 / 2 * G + E) := by
    have h1 := fdiv_le (3 * g.lo) 2 (by norm_num)
    push_cast at h1 ⊢
    linarith
  -- the penalty `P = π (E + G/2)/a²`
  set Pt : ℝ := Real.pi * (E + G / 2) / a ^ 2 with hPt
  have Ppos : 0 < Pt := by positivity
  have yZ : (0 : ℤ) < ((w.A * w.A : ℕ) : ℤ) := by positivity
  set X : ℤ := e.hi + cdivZ g.hi 2 with hX
  have xh : Sz * (E + G / 2) ≤ (X : ℝ) := by
    have h1 := le_cdiv g.hi 2 (by norm_num)
    rw [hX]
    push_cast at h1 ⊢
    linarith
  have pih := piF_mem.2
  rw [le_div_iff₀ sp] at pih
  have prod : Real.pi * Sz * (Sz * (E + G / 2)) ≤ (piF.hi : ℝ) * (X : ℝ) :=
    mul_le_mul pih xh (by positivity) (le_of_lt piF_hi_pos)
  have yR : (((w.A * w.A : ℕ) : ℤ) : ℝ) = a ^ 2 * Sz := by rw [a2]; push_cast; field_simp
  have pHi : Sz * Pt ≤ ((cdivZ (piF.hi * X) ((w.A * w.A : ℕ) : ℤ) : ℤ) : ℝ) := by
    refine le_trans ?_ (le_cdiv _ _ yZ)
    rw [yR]
    push_cast
    rw [le_div_iff₀ (by positivity), hPt]
    have e' : Sz * (Real.pi * (E + G / 2) / a ^ 2) * (a ^ 2 * Sz) =
        Real.pi * Sz * (Sz * (E + G / 2)) := by field_simp
    rw [e']
    exact prod
  set PH : ℤ := cdivZ (piF.hi * X) ((w.A * w.A : ℕ) : ℤ) with hPH
  have PH0 : (0 : ℝ) ≤ (PH : ℝ) := le_trans (by positivity) pHi
  -- the term
  set m : ℤ := w.mult with hm
  have m0 : (0 : ℤ) < m := by rw [hm]; unfold DWit.mult; split <;> norm_num
  have m0r : (0 : ℝ) < m := by exact_mod_cast m0
  have num0 : (0 : ℤ) < s.num := Rat.num_pos.mpr spos
  have num0r : (0 : ℝ) < s.num := by exact_mod_cast num0
  have den0 : (0 : ℤ) < (s.den : ℤ) := by exact_mod_cast s.pos
  have den0r : (0 : ℝ) < (s.den : ℝ) := by exact_mod_cast s.pos
  have sNum : (s : ℝ) = (s.num : ℝ) / (s.den : ℝ) := by rw [Rat.cast_def]
  have cDef : (directZ s w).c = m * s.num * (3 * g.lo / 2 + e.lo) / (s.den : ℤ) := rfl
  have aDef : (directZ s w).a = -cdivZ (m * s.num ^ 3 * PH) ((s.den : ℤ) ^ 3) := rfl
  have constLe : ((directZ s w).c : ℝ) / Sz ≤ (m : ℝ) * s * (3 / 2 * G + E) := by
    rw [cDef, div_le_iff₀ sp]
    refine (fdiv_le _ _ den0).trans ?_
    rw [div_le_iff₀ (by exact_mod_cast den0)]
    have h := mul_le_mul_of_nonneg_left iLo (mul_nonneg m0r.le num0r.le)
    have e5 : (m : ℝ) * s * (3 / 2 * G + E) * Sz * (s.den : ℝ) =
        (m : ℝ) * s.num * (Sz * (3 / 2 * G + E)) := by
      rw [sNum]
      field_simp
    push_cast at h ⊢
    rw [e5]
    linarith
  have slopeLe : ((directZ s w).a : ℝ) / Sz ≤ -((m : ℝ) * (s : ℝ) ^ 3 * Pt) := by
    rw [aDef]
    have h := le_cdiv (m * s.num ^ 3 * PH) ((s.den : ℤ) ^ 3) (by positivity)
    push_cast at h ⊢
    have s3 : (m : ℝ) * (s : ℝ) ^ 3 * Pt * Sz ≤
        (m : ℝ) * (s.num : ℝ) ^ 3 * (PH : ℝ) / (s.den : ℝ) ^ 3 := by
      rw [sNum, div_pow, le_div_iff₀ (by positivity)]
      have h2 := mul_le_mul_of_nonneg_left pHi (mul_nonneg m0r.le (pow_pos num0r 3).le)
      have e : (m : ℝ) * ((s.num : ℝ) ^ 3 / (s.den : ℝ) ^ 3) * Pt * Sz * (s.den : ℝ) ^ 3 =
          (m : ℝ) * (s.num : ℝ) ^ 3 * (Sz * Pt) := by
        field_simp
      rw [e]
      exact h2
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ sp]
    linarith
  have slopeNeg : (directZ s w).a ≤ 0 := by
    rw [aDef]
    have h := le_cdiv (m * s.num ^ 3 * PH) ((s.den : ℤ) ^ 3) (by positivity)
    have : (0 : ℝ) ≤ ((cdivZ (m * s.num ^ 3 * PH) ((s.den : ℤ) ^ 3) : ℤ) : ℝ) := by
      refine le_trans ?_ h
      push_cast
      have : (0 : ℝ) ≤ (m : ℝ) * (s.num : ℝ) ^ 3 * (PH : ℝ) :=
        mul_nonneg (mul_nonneg m0r.le (pow_pos num0r 3).le) PH0
      positivity
    have : (0 : ℤ) ≤ cdivZ (m * s.num ^ 3 * PH) ((s.den : ℤ) ^ 3) := by exact_mod_cast this
    linarith
  refine ⟨slopeNeg, le_rfl, ?_⟩
  intro p _ hv
  -- the tangent of the convex half kernel at `a²`
  have tangent (Q : ℝ) (hQ : 0 < Q) :
      3 / 2 * G + E - Pt * ((s : ℝ) ^ 2 * Q) ≤ gKernel (1/2) (Real.pi * ((s : ℝ) ^ 2 * Q)) := by
    have x0 : 0 < Real.pi * ((s : ℝ) ^ 2 * Q) := by positivity
    have tan := globalTangent KernelKind.half (pow_pos a0 2) x0
    have kv : kernelValue KernelKind.half (a ^ 2) = G := by
      simp [kernelValue, KernelKind.power, hG]
    have kq : kernelValue KernelKind.half (Real.pi * ((s : ℝ) ^ 2 * Q)) =
        gKernel (1/2) (Real.pi * ((s : ℝ) ^ 2 * Q)) := by
      simp [kernelValue, KernelKind.power]
    have ks : kernelSlope KernelKind.half (a ^ 2) = -(E + 1 / 2 * G) / a ^ 2 := by
      simp [kernelSlope, kernelValue, KernelKind.power, hG, hE]
    rw [kv, kq, ks] at tan
    have lin : G + -(E + 1 / 2 * G) / a ^ 2 * (Real.pi * ((s : ℝ) ^ 2 * Q) - a ^ 2) =
        3 / 2 * G + E - Pt * ((s : ℝ) ^ 2 * Q) := by
      rw [hPt]
      field_simp
      ring
    rw [lin] at tan
    exact tan
  rw [ZTerm.eval_eq]
  have bZero : (directZ s w).b = 0 := rfl
  have nlZero : (directZ s w).nl = 0 := rfl
  rw [bZero, nlZero]
  simp only [Int.cast_zero, zero_div, zero_mul, add_zero, sub_zero]
  have kindEq : (directZ s w).kind = w.kind := rfl
  have idxEq : (directZ s w).index = w.index := rfl
  rw [kindEq, idxEq]
  cases hc : w.cross
  · have kind : w.kind = .period := by simp [DWit.kind, hc]
    have mult : (m : ℝ) = 2 := by rw [hm]; simp [DWit.mult, hc]
    have lex : lexPositive w.index := by simpa [hc] using lexOk
    obtain ⟨phys, qpos⟩ := physicalS_period s w.index lex hv
    rw [kind, phys]
    have t := tangent _ qpos
    have sl := mul_le_mul_of_nonneg_right slopeLe qpos.le
    rw [mult] at constLe sl
    have hmul := mul_le_mul_of_nonneg_left t (by positivity : (0 : ℝ) ≤ 2 * s)
    have e3 : -(2 * (s : ℝ) ^ 3 * Pt) * termQ Kind.period w.index p =
        -(2 * s * (Pt * ((s : ℝ) ^ 2 * termQ Kind.period w.index p))) := by ring
    rw [e3] at sl
    have e4 : 2 * (s : ℝ) * (3 / 2 * G + E - Pt * ((s : ℝ) ^ 2 * termQ Kind.period w.index p)) =
        2 * s * (3 / 2 * G + E) - 2 * s * (Pt * ((s : ℝ) ^ 2 * termQ Kind.period w.index p)) := by ring
    rw [e4] at hmul
    linarith
  · have kind : w.kind = .cross := by simp [DWit.kind, hc]
    have mult : (m : ℝ) = 1 := by rw [hm]; simp [DWit.mult, hc]
    obtain ⟨phys, qpos⟩ := physicalS_cross s w.index hv
    rw [kind, phys]
    have t := tangent _ qpos
    have sl := mul_le_mul_of_nonneg_right slopeLe qpos.le
    rw [mult] at constLe sl
    have hmul := mul_le_mul_of_nonneg_left t sr.le
    have e3 : -(1 * (s : ℝ) ^ 3 * Pt) * termQ Kind.cross w.index p =
        -((s : ℝ) * (Pt * ((s : ℝ) ^ 2 * termQ Kind.cross w.index p))) := by ring
    rw [e3] at sl
    have e4 : (s : ℝ) * (3 / 2 * G + E - Pt * ((s : ℝ) ^ 2 * termQ Kind.cross w.index p)) =
        s * (3 / 2 * G + E) - s * (Pt * ((s : ℝ) ^ 2 * termQ Kind.cross w.index p)) := by ring
    rw [e4] at hmul
    linarith

/-! ### Wave tangents -/

theorem fmulQ_mono_lo {a : FI} {x : ℝ} (hx : a.Mem x) {q : ℚ} (hq : 0 ≤ q) :
    (fmulQ a.lo q : ℝ) ≤ Sz * x * q := by
  have sp := Sz_pos
  have h := hx.1
  rw [div_le_iff₀ sp] at h
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have := mul_le_mul_of_nonneg_right h hq'
  linarith [fmulQ_le a.lo q]

theorem cmulQ_mono_hi {a : FI} {x : ℝ} (hx : a.Mem x) {q : ℚ} (hq : 0 ≤ q) :
    Sz * x * q ≤ (cmulQ a.hi q : ℝ) := by
  have sp := Sz_pos
  have h := hx.2
  rw [le_div_iff₀ sp] at h
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have := mul_le_mul_of_nonneg_right h hq'
  linarith [le_cmulQ a.hi q]

theorem cdivZ_nonneg {n d : ℤ} (hn : 0 ≤ n) (hd : 0 < d) : 0 ≤ cdivZ n d := by
  have h := le_cdiv n d hd
  have : (0 : ℝ) ≤ (n : ℝ) / d := div_nonneg (by exact_mod_cast hn) (by exact_mod_cast hd.le)
  exact_mod_cast this.trans h

theorem waveZ_valid (s : ℚ) (w : WWit) (box : Cell) (ok : waveOk s w box = true) :
    ZValid s box (waveZ s w box) := by
  simp only [waveOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨spos, xpos⟩, lex⟩, kL⟩, kR⟩, argOk⟩, eLok⟩, eRok⟩, pL⟩, pR⟩ := ok
  have sp := Sz_pos
  have sr : (0 : ℝ) < s := by exact_mod_cast spos
  have s2 : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have xb : (0 : ℝ) < w.xbar := by exact_mod_cast xpos
  -- the anchor coefficient `H = 2 e^{−x̄ + ℓ(t̄)}/(x̄ s²)`
  set Hr : ℝ := 2 / ((w.xbar : ℝ) * (s : ℝ) ^ 2) * Real.exp ((w.arg box : ℚ) : ℝ) with hHr
  have Hpos : 0 < Hr := by positivity
  have facR : ((w.fac s : ℚ) : ℝ) = 2 / ((w.xbar : ℝ) * (s : ℝ) ^ 2) := by
    unfold WWit.fac
    push_cast
    ring
  have fac0 : 0 ≤ w.fac s := by
    unfold WWit.fac
    have : 0 < w.xbar * (s * s) := by positivity
    positivity
  have hH : (w.hF s box).Mem Hr := by
    have lo := expLoQ_le argOk
    have hi := expUpQ_ge argOk
    rw [div_le_iff₀ sp] at lo
    rw [le_div_iff₀ sp] at hi
    have fac0r : (0 : ℝ) ≤ ((w.fac s : ℚ) : ℝ) := by exact_mod_cast fac0
    constructor
    · show (fmulQ (expLoQ (w.arg box)) (w.fac s) : ℝ) / Sz ≤ Hr
      rw [div_le_iff₀ sp]
      refine (fmulQ_le _ _).trans ?_
      have := mul_le_mul_of_nonneg_right lo fac0r
      rw [hHr, ← facR]
      linarith
    · show Hr ≤ (cmulQ (expUpQ (w.arg box)) (w.fac s) : ℝ) / Sz
      rw [le_div_iff₀ sp]
      refine le_trans ?_ (le_cmulQ _ _)
      have := mul_le_mul_of_nonneg_right hi fac0r
      rw [hHr, ← facR]
      linarith
  have Hhi0 : (0 : ℝ) ≤ ((w.hF s box).hi : ℝ) := by
    have h := hH.2
    rw [le_div_iff₀ sp] at h
    nlinarith
  -- the `Q*` coefficient
  set r : ℚ := (1 + 1 / w.xbar) / (s * s) with hr
  have r0 : 0 ≤ r := by rw [hr]; positivity
  have rR : ((r : ℚ) : ℝ) = (1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 := by rw [hr]; push_cast; ring
  have cqLe : ((w.cq s box : ℤ) : ℝ) / Sz ≤ Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) := by
    unfold WWit.cq
    rw [← hr]
    have c1 := le_cdiv ((w.hF s box).hi * piF.hi) Sz Sz_posZ
    have c2 := le_cmulQ (cdivZ ((w.hF s box).hi * piF.hi) Sz) r
    have hh := hH.2
    rw [le_div_iff₀ sp] at hh
    have pih := piF_mem.2
    rw [le_div_iff₀ sp] at pih
    have prod : (Hr * Sz) * (Real.pi * Sz) ≤ ((w.hF s box).hi : ℝ) * (piF.hi : ℝ) :=
      mul_le_mul hh pih (by positivity) Hhi0
    have r0r : (0 : ℝ) ≤ ((r : ℚ) : ℝ) := by exact_mod_cast r0
    push_cast at c1
    have step : Hr * Real.pi * Sz ≤ ((cdivZ ((w.hF s box).hi * piF.hi) Sz : ℤ) : ℝ) := by
      refine le_trans ?_ c1
      rw [le_div_iff₀ sp]
      nlinarith
    have step2 := mul_le_mul_of_nonneg_right step r0r
    rw [div_le_iff₀ sp]
    push_cast
    rw [rR] at step2 c2
    have e : Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) * Sz =
        -(Hr * Real.pi * Sz * ((1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2)) := by ring
    rw [e]
    linarith
  -- the constant and phase coefficients at both window ends
  set ct : ℤ := w.ct s box with hct
  have atLe (u : ℚ) : ((w.atZ s box u : ℤ) : ℝ) + (ct : ℝ) * u ≤
      Sz * Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * ((u : ℝ) - (w.tbar : ℝ))) := by
    have gR : ((w.gAt u : ℚ) : ℝ) = 2 + (w.xbar : ℝ) + (w.b : ℝ) * ((u : ℝ) - (w.tbar : ℝ)) := by
      unfold WWit.gAt
      push_cast
      ring
    set Pz : ℤ := (if 0 ≤ w.gAt u then fmulQ (w.hF s box).lo (w.gAt u)
      else fmulQ (w.hF s box).hi (w.gAt u)) with hPz
    have prodLe : (Pz : ℝ) ≤ Sz * Hr * ((w.gAt u : ℚ) : ℝ) := by
      rw [hPz]
      split_ifs with hg
      · exact fmulQ_mono_lo hH hg
      · have hg' : ((w.gAt u : ℚ) : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hg))
        have h := hH.2
        rw [le_div_iff₀ sp] at h
        have := mul_le_mul_of_nonpos_right h hg'
        linarith [fmulQ_le (w.hF s box).hi (w.gAt u)]
    have ctLe := le_cmulQ ct u
    have atEq : w.atZ s box u = Pz - cmulQ ct u := rfl
    rw [atEq, ← gR]
    push_cast
    linarith
  have kap (u : ℚ) (hu : u = w.L box ∨ u = w.R box) :
      ((w.kappa s box : ℤ) : ℝ) ≤ ((w.atZ s box u : ℤ) : ℝ) := by
    have h1 : w.kappa s box ≤ w.atZ s box u := by
      unfold WWit.kappa
      rcases hu with rfl | rfl
      · exact min_le_left _ _
      · exact min_le_right _ _
    exact_mod_cast h1
  refine ⟨?_, le_rfl, ?_⟩
  · -- the `Q*` coefficient is nonpositive
    have h : ((w.cq s box : ℤ) : ℝ) / Sz ≤ 0 := by
      refine cqLe.trans ?_
      have : 0 ≤ Hr * ((1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) := by positivity
      have e : Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) =
          -(Hr * ((1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi)) := by ring
      rw [e]
      linarith
    have : ((w.cq s box : ℤ) : ℝ) ≤ 0 := by
      have := (div_le_iff₀ sp).mp h
      linarith
    exact_mod_cast this
  intro p hp hv
  obtain ⟨phys, qpos⟩ := physicalS_wave s w.index lex hv spos
  obtain ⟨tL, tR⟩ := window_sound box w.index hp
  obtain ⟨q, hq⟩ : ∃ q, q = termQ .wave w.index p := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = phaseT w.index p := ⟨_, rfl⟩
  rw [← hq] at phys qpos
  rw [← ht] at phys tL tR
  obtain ⟨y, hy⟩ : ∃ y, y = Real.pi * q / (s : ℝ) ^ 2 := ⟨_, rfl⟩
  rw [← hy] at phys
  have ypos : 0 < y := by rw [hy]; positivity
  have tL' : (w.L box : ℝ) ≤ t := by simpa [WWit.L] using tL
  have tR' : t ≤ (w.R box : ℝ) := by simpa [WWit.R] using tR
  -- the exponential-affine phase bound on the window
  have ellEq (u : ℚ) : ((w.ell box u : ℚ) : ℝ) = (w.a : ℝ) + (w.b : ℝ) * ((u : ℝ) - (w.c box : ℝ)) := by
    simp [WWit.ell]
  have endL : Real.exp ((w.a : ℝ) + (w.b : ℝ) * ((w.L box : ℝ) - (w.c box : ℝ))) ≤
      1 + Real.cos (2 * Real.pi * (w.L box : ℝ)) := by
    rw [← ellEq]
    have h1 := expUpQ_ge eLok
    have h2 := cosLoQ_le (w.L box)
    have h3 : ((expUpQ (w.ell box (w.L box)) : ℤ) : ℝ) ≤ ((Sz + cosLoQ (w.L box) : ℤ) : ℝ) := by
      exact_mod_cast pL
    push_cast at h3
    have h4 : ((expUpQ (w.ell box (w.L box)) : ℤ) : ℝ) / Sz ≤ 1 + (cosLoQ (w.L box) : ℝ) / Sz := by
      rw [div_le_iff₀ sp, add_mul, div_mul_cancel₀ _ sp.ne']
      linarith
    linarith
  have endR : Real.exp ((w.a : ℝ) + (w.b : ℝ) * ((w.R box : ℝ) - (w.c box : ℝ))) ≤
      1 + Real.cos (2 * Real.pi * (w.R box : ℝ)) := by
    rw [← ellEq]
    have h1 := expUpQ_ge eRok
    have h2 := cosLoQ_le (w.R box)
    have h3 : ((expUpQ (w.ell box (w.R box)) : ℤ) : ℝ) ≤ ((Sz + cosLoQ (w.R box) : ℤ) : ℝ) := by
      exact_mod_cast pR
    push_cast at h3
    have h4 : ((expUpQ (w.ell box (w.R box)) : ℤ) : ℝ) / Sz ≤ 1 + (cosLoQ (w.R box) : ℝ) / Sz := by
      rw [div_le_iff₀ sp, add_mul, div_mul_cancel₀ _ sp.ne']
      linarith
    linarith
  have kLr : ((w.k box : ℤ) : ℝ) - 1 / 2 < (w.L box : ℝ) := by
    have h : ((((w.k box : ℤ) : ℚ) - 1 / 2 : ℚ) : ℝ) < ((w.L box : ℚ) : ℝ) := Rat.cast_lt.mpr kL
    push_cast at h
    exact h
  have kRr : (w.R box : ℝ) < ((w.k box : ℤ) : ℝ) + 1 / 2 := by
    have h : ((w.R box : ℚ) : ℝ) < ((((w.k box : ℤ) : ℚ) + 1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr kR
    push_cast at h
    exact h
  have phase := phase_secant (w.k box) (w.L box) (w.R box) w.a w.b (w.c box) t kLr kRr tL' tR'
    endL endR
  -- joint tangent of `G₁` with the phase factor at `y = π q/s²`
  have tang := g1_tangent (w.xbar : ℝ) y
    ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c box : ℝ)))
    ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c box : ℝ))) xb ypos
  have g1nn : 0 ≤ Real.exp (-y) / y := by positivity
  have lower1 : 2 / (s : ℝ) ^ 2 *
      (Real.exp (-y + ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c box : ℝ)))) / y) ≤
      physicalS s .wave w.index p := by
    rw [phys, Real.exp_add]
    have m := mul_le_mul_of_nonneg_right phase g1nn
    have e : Real.exp (-y) * Real.exp ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c box : ℝ))) / y =
        Real.exp ((w.a : ℝ) + (w.b : ℝ) * (t - (w.c box : ℝ))) * (Real.exp (-y) / y) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left m (by positivity)
  have argR : ((w.arg box : ℚ) : ℝ) = -(w.xbar : ℝ) +
      ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c box : ℝ))) := by
    simp [WWit.arg, WWit.ell]
  have plane : Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * (t - (w.tbar : ℝ))) +
      Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) * q ≤
      physicalS s .wave w.index p := by
    have e : Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * (t - (w.tbar : ℝ))) +
        Hr * (-(1 + 1 / (w.xbar : ℝ)) / (s : ℝ) ^ 2 * Real.pi) * q =
        2 / (s : ℝ) ^ 2 * (Real.exp (-(w.xbar : ℝ) +
          ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c box : ℝ)))) / (w.xbar : ℝ) *
          (1 + (-1 - 1 / (w.xbar : ℝ)) * (y - (w.xbar : ℝ)) +
            (((w.a : ℝ) + (w.b : ℝ) * (t - (w.c box : ℝ))) -
              ((w.a : ℝ) + (w.b : ℝ) * ((w.tbar : ℝ) - (w.c box : ℝ)))))) := by
      rw [hHr, argR, hy]
      field_simp
      ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left tang (by positivity)).trans lower1
  have mid0 : ((w.kappa s box : ℤ) : ℝ) + (ct : ℝ) * t ≤
      Sz * Hr * (2 + (w.xbar : ℝ) - (w.b : ℝ) * (w.tbar : ℝ)) + Sz * Hr * (w.b : ℝ) * t := by
    apply affine_between (w.L box) (w.R box) t _ _ _ _ tL' tR'
    · have h1 := atLe (w.L box)
      have h2 := kap (w.L box) (Or.inl rfl)
      have e : Sz * Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * ((w.L box : ℝ) - (w.tbar : ℝ))) =
          Sz * Hr * (2 + (w.xbar : ℝ) - (w.b : ℝ) * (w.tbar : ℝ)) + Sz * Hr * (w.b : ℝ) * (w.L box : ℝ) := by
        ring
      linarith
    · have h1 := atLe (w.R box)
      have h2 := kap (w.R box) (Or.inr rfl)
      have e : Sz * Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * ((w.R box : ℝ) - (w.tbar : ℝ))) =
          Sz * Hr * (2 + (w.xbar : ℝ) - (w.b : ℝ) * (w.tbar : ℝ)) + Sz * Hr * (w.b : ℝ) * (w.R box : ℝ) := by
        ring
      linarith
  have mid : ((w.kappa s box : ℤ) : ℝ) / Sz + ((ct : ℝ) / Sz) * t ≤
      (Hr * (2 + (w.xbar : ℝ) - (w.b : ℝ) * (w.tbar : ℝ))) + (Hr * (w.b : ℝ)) * t := by
    have e : ((w.kappa s box : ℤ) : ℝ) / Sz + ((ct : ℝ) / Sz) * t =
        (((w.kappa s box : ℤ) : ℝ) + (ct : ℝ) * t) / Sz := by
      field_simp
    rw [e, div_le_iff₀ sp]
    linarith
  have cqq := mul_le_mul_of_nonneg_right cqLe qpos.le
  rw [ZTerm.eval_eq]
  show ((w.kappa s box : ℤ) : ℝ) / Sz + ((w.cq s box : ℤ) : ℝ) / Sz * termQ .wave w.index p +
    ((w.ct s box : ℤ) : ℝ) / Sz * phaseT w.index p - ((0 : ℤ) : ℝ) / Sz * nlVal s w.index p ≤
      physicalS s .wave w.index p
  rw [← hq, ← ht, ← hct]
  simp only [Int.cast_zero, zero_div, zero_mul, sub_zero]
  have e2 : Hr * (2 + (w.xbar : ℝ) + (w.b : ℝ) * (t - (w.tbar : ℝ))) =
      Hr * (2 + (w.xbar : ℝ) - (w.b : ℝ) * (w.tbar : ℝ)) + Hr * (w.b : ℝ) * t := by ring
  rw [e2] at plane
  linarith [plane, mid, cqq]

/-! ### Perspective terms -/

theorem perspZ_valid (s : ℚ) (w : PWit) (box : Cell) (ok : perspOk s w box = true) :
    ZValid s box (perspZ s w box) := by
  simp only [perspOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨spos, lex⟩, dpos⟩, dhalf⟩, sinPos⟩ := ok
  have sp := Sz_pos
  have sr : (0 : ℝ) < s := by exact_mod_cast spos
  have s2 : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have dpr : (0 : ℝ) < w.d box := by exact_mod_cast dpos
  -- `sin πd ≥ sinLo/S > 0`
  set sl : ℝ := (w.sinLo box : ℝ) / Sz with hsl
  have sl0 : 0 < sl := by
    rw [hsl]
    exact div_pos (by exact_mod_cast sinPos) sp
  have slLe : sl ≤ Real.sin (Real.pi * (w.d box : ℝ)) := by
    have h := cosLoQ_le (1 / 4 - w.d box / 2)
    have e : Real.cos (2 * Real.pi * (((1 / 4 - w.d box / 2 : ℚ)) : ℝ)) =
        Real.sin (Real.pi * (w.d box : ℝ)) := by
      push_cast
      rw [show 2 * Real.pi * (1 / 4 - (w.d box : ℝ) / 2) = Real.pi / 2 - Real.pi * (w.d box : ℝ) by ring]
      exact Real.cos_pi_div_two_sub _
    rw [e] at h
    exact h
  set κ : ℝ := 4 * sl ^ 2 / (w.d box : ℝ) ^ 2 with hκ
  have κpos : 0 < κ := by positivity
  have κd : κ * (w.d box : ℝ) ^ 2 ≤ 4 * Real.sin (Real.pi * (w.d box : ℝ)) ^ 2 := by
    rw [hκ, div_mul_cancel₀ _ (by positivity)]
    have := pow_le_pow_left₀ sl0.le slLe 2
    linarith
  -- the penalty coefficient: `nl/S ≥ u² s²/κ`
  set u : ℝ := (w.U : ℝ) / Sz with hu
  have nlZ0 : 0 ≤ w.nlZ s box := by
    unfold PWit.nlZ
    apply cdivZ_nonneg
    · have c0 : 0 ≤ (w.coef s box).num := Rat.num_nonneg.mpr (by unfold PWit.coef; positivity)
      have : 0 ≤ w.U * w.U := mul_self_nonneg _
      have : (0 : ℤ) ≤ Sz := Sz_posZ.le
      positivity
    · have : (0 : ℤ) < w.sinLo box := sinPos
      have : (0 : ℤ) < ((w.coef s box).den : ℤ) := by exact_mod_cast (w.coef s box).pos
      positivity
  have nlLe : u ^ 2 * (s : ℝ) ^ 2 / κ ≤ (w.nlZ s box : ℝ) / Sz := by
    have h := le_cdiv (w.U * w.U * (w.coef s box).num * Sz)
      (4 * w.sinLo box * w.sinLo box * ((w.coef s box).den : ℤ)) (by
        have : (0 : ℤ) < w.sinLo box := sinPos
        have : (0 : ℤ) < ((w.coef s box).den : ℤ) := by exact_mod_cast (w.coef s box).pos
        positivity)
    have coefR : ((w.coef s box : ℚ) : ℝ) = (s : ℝ) ^ 2 * (w.d box : ℝ) ^ 2 := by
      unfold PWit.coef
      push_cast
      ring
    have cd : ((w.coef s box : ℚ) : ℝ) = ((w.coef s box).num : ℝ) / ((w.coef s box).den : ℝ) :=
      Rat.cast_def _
    have den0 : (0 : ℝ) < ((w.coef s box).den : ℝ) := by exact_mod_cast (w.coef s box).pos
    have sl0' : (0 : ℝ) < (w.sinLo box : ℝ) := by exact_mod_cast sinPos
    have hnd : ((w.coef s box).num : ℝ) = (s : ℝ) ^ 2 * (w.d box : ℝ) ^ 2 * ((w.coef s box).den : ℝ) := by
      rw [← coefR, cd]
      field_simp
    unfold PWit.nlZ
    rw [le_div_iff₀ sp]
    refine le_trans (le_of_eq ?_) h
    push_cast
    rw [hnd, hu, hκ, hsl]
    field_simp
  refine ⟨le_rfl, nlZ0, ?_⟩
  intro p hp hv
  obtain ⟨phys, qpos⟩ := physicalS_wave s w.index lex hv spos
  obtain ⟨tL, tR⟩ := window_sound box w.index hp
  obtain ⟨q, hq⟩ : ∃ q, q = termQ .wave w.index p := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = phaseT w.index p := ⟨_, rfl⟩
  rw [← hq] at phys qpos
  rw [← ht] at phys tL tR
  obtain ⟨y, hy⟩ : ∃ y, y = Real.pi * q / (s : ℝ) ^ 2 := ⟨_, rfl⟩
  rw [← hy] at phys
  have ypos : 0 < y := by rw [hy]; positivity
  -- the distance to the extinction
  have zbound : |t - (w.z0 box : ℝ)| ≤ (w.d box : ℝ) := by
    have dL : |(w.L box : ℝ) - (w.z0 box : ℝ)| ≤ (w.d box : ℝ) := by
      have := le_max_left |w.L box - w.z0 box| |w.R box - w.z0 box|
      exact_mod_cast this
    have dR : |(w.R box : ℝ) - (w.z0 box : ℝ)| ≤ (w.d box : ℝ) := by
      have := le_max_right |w.L box - w.z0 box| |w.R box - w.z0 box|
      exact_mod_cast this
    have tL' : (w.L box : ℝ) ≤ t := by simpa [PWit.L] using tL
    have tR' : t ≤ (w.R box : ℝ) := by simpa [PWit.R] using tR
    rw [abs_le] at dL dR ⊢
    constructor <;> linarith [dL.1, dL.2, dR.1, dR.2]
  have zeq : t = (t - (w.z0 box : ℝ)) + ((w.k box : ℤ) : ℝ) + 1 / 2 := by
    simp only [PWit.z0]
    push_cast
    ring
  have pl := persp_lower (w.k box) (t - (w.z0 box : ℝ)) (w.d box) κ (u * (s : ℝ) ^ 2) y dpr
    (by have h := (Rat.cast_le (K := ℝ)).mpr dhalf; push_cast at h; exact h)
    zbound κpos κd ypos
  rw [← zeq] at pl
  -- divide by `s²`
  obtain ⟨A, hA⟩ : ∃ A, A = (1 + Real.cos (2 * Real.pi * t)) * (Real.exp (-y) / y) := ⟨_, rfl⟩
  rw [← hA] at pl phys
  have key : 2 * u * (t - (w.z0 box : ℝ)) - u ^ 2 * (s : ℝ) ^ 2 / κ * (y * Real.exp y) ≤
      2 / (s : ℝ) ^ 2 * A := by
    have e0 : 2 / (s : ℝ) ^ 2 * A = 2 * A / (s : ℝ) ^ 2 := by ring
    rw [e0, le_div_iff₀ s2]
    have e : (2 * u * (t - (w.z0 box : ℝ)) - u ^ 2 * (s : ℝ) ^ 2 / κ * (y * Real.exp y)) * (s : ℝ) ^ 2 =
        2 * (u * (s : ℝ) ^ 2) * (t - (w.z0 box : ℝ)) - (u * (s : ℝ) ^ 2) ^ 2 * (y * Real.exp y / κ) := by
      field_simp
    rw [e]
    linarith [pl]
  have nlv : nlVal s w.index p = y * Real.exp y := by
    unfold nlVal
    rw [hy, hq]
    rfl
  have yey : 0 ≤ y * Real.exp y := by positivity
  have pen := mul_le_mul_of_nonneg_right nlLe yey
  rw [ZTerm.eval_eq]
  show ((-(w.U * (2 * w.k box + 1)) : ℤ) : ℝ) / Sz + ((0 : ℤ) : ℝ) / Sz * termQ .wave w.index p +
    ((2 * w.U : ℤ) : ℝ) / Sz * phaseT w.index p - ((w.nlZ s box : ℤ) : ℝ) / Sz * nlVal s w.index p ≤
      physicalS s .wave w.index p
  rw [← hq, ← ht, nlv, phys]
  have lin : ((-(w.U * (2 * w.k box + 1)) : ℤ) : ℝ) / Sz + ((0 : ℤ) : ℝ) / Sz * q +
      ((2 * w.U : ℤ) : ℝ) / Sz * t = 2 * u * (t - (w.z0 box : ℝ)) := by
    rw [hu]
    simp only [PWit.z0]
    push_cast
    ring
  rw [lin]
  linarith [key, pen]

theorem witZ_valid (s : ℚ) (box : Cell) (x : Wit) (ok : witOk s box x = true) :
    ZValid s box (witZ s box x) := by
  cases x with
  | direct w => exact directZ_valid s w ok box
  | wave w => exact waveZ_valid s w box ok
  | persp w => exact perspZ_valid s w box ok

/-! ### Distinct indices -/

theorem lexLt_trans {a b c : IntVec} (h1 : lexLt a b) (h2 : lexLt b c) : lexLt a c := by
  unfold lexLt at *
  omega

theorem lexLt_irrefl (a : IntVec) : ¬ lexLt a a := by
  unfold lexLt
  omega

theorem sortedLex_pairwise : ∀ l : List IntVec, sortedLex l = true → l.Pairwise lexLt
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: l, h => by
    simp only [sortedLex, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := sortedLex_pairwise (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact lexLt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem sortedLex_nodup {l : List IntVec} (h : sortedLex l = true) : l.Nodup :=
  (sortedLex_pairwise l h).imp (fun {a _} hab heq => by subst heq; exact lexLt_irrefl a hab)

/-! ### Sums of terms -/

private theorem zsum_by_kind (l : List ZTerm) (g : ZTerm → ℝ) :
    (l.map g).sum = ((l.filter (fun t => decide (t.kind = .cross))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .period))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .wave))).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hk : a.kind <;> simp [hk, ih] <;> ring

private theorem zfilter_kind_sum (l : List ZTerm) (k : Kind) (G : Kind → IntVec → ℝ) :
    ((l.filter (fun t => decide (t.kind = k))).map (fun t => G t.kind t.index)).sum =
      ((kindIdxZ k l).map (fun n => G k n)).sum := by
  induction l with
  | nil => simp [kindIdxZ]
  | cons a l ih =>
    by_cases hk : a.kind = k
    · simp [hk, kindIdxZ] at ih ⊢
      rw [ih]
    · simp [hk, kindIdxZ] at ih ⊢
      exact ih

/-- **Screened energy bound for integer terms.** For terms valid on a box, with
strictly increasing indices per kind and lex-positive period and wave indices,
`(Σ terms − 2s − 2/s²)/(2 a_c)` is at most the energy at every valid point of
the box (`ScreenedSeries.energy_finite_lower_lex`). -/
theorem zsum_le_energy (s : ℚ) (hs : 0 < s) (box : Cell) (zs : List ZTerm)
    (valid : ∀ t ∈ zs, ZValid s box t) (hst : structOk zs = true) (p : Chart) (hp : box.Mem p)
    (hv : (chartPoint p).Valid) :
    ((zs.map fun t => t.eval s p).sum - (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2)) / (2 * ac) ≤
      energy (chartPoint p) := by
  simp only [structOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hst
  obtain ⟨⟨⟨⟨ncr, nper⟩, nwav⟩, lexP⟩, lexW⟩ := hst
  have ncross := sortedLex_nodup ncr
  have nperiod := sortedLex_nodup nper
  have nwave := sortedLex_nodup nwav
  set q := chartPoint p with hq
  have step1 : (zs.map fun t => t.eval s p).sum ≤
      (zs.map (fun t => physicalS s t.kind t.index p)).sum := by
    apply List.sum_le_sum
    intro t ht
    exact (valid t ht).2.2 p hp hv
  have fc := zfilter_kind_sum zs .cross (fun k n => physicalS s k n p)
  have fp := zfilter_kind_sum zs .period (fun k n => physicalS s k n p)
  have fw := zfilter_kind_sum zs .wave (fun k n => physicalS s k n p)
  rw [zsum_by_kind zs (fun t => physicalS s t.kind t.index p), fc, fp, fw] at step1
  set X := (kindIdxZ .cross zs).toFinset
  set P := (kindIdxZ .period zs).toFinset
  set W := (kindIdxZ .wave zs).toFinset
  have cross : ((kindIdxZ .cross zs).map (fun n => physicalS s .cross n p)).sum =
      (s : ℝ) * ∑ n ∈ X,
        gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 * quad (gram q.basis) (castVec n + q.offset)) := by
    rw [Finset.mul_sum, List.sum_toFinset _ ncross]
    rfl
  have period : ((kindIdxZ .period zs).map (fun n => physicalS s .period n p)).sum =
      2 * (s : ℝ) * ∑ n ∈ P,
        gKernel (1/2) (Real.pi * (s : ℝ) ^ 2 * quad (gram q.basis) (castVec n)) := by
    rw [Finset.mul_sum, List.sum_toFinset _ nperiod]
    rfl
  have wave : ((kindIdxZ .wave zs).map (fun n => physicalS s .wave n p)).sum =
      2 / (s : ℝ) ^ 2 * ∑ n ∈ W, (1 + Real.cos (2 * Real.pi * dot (castVec n) q.offset)) *
        gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n) / (s : ℝ) ^ 2) := by
    rw [Finset.mul_sum, List.sum_toFinset _ nwave]
    rfl
  rw [cross, period, wave] at step1
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  have fl := ScreenedSeries.energy_finite_lower_lex q hv (s : ℝ) sr X P W
    (fun n hn => lexP n (List.mem_toFinset.mp hn)) (fun n hn => lexW n (List.mem_toFinset.mp hn))
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  refine le_trans ?_ fl
  exact div_le_div_of_nonneg_right (by linarith) acpos.le

/-! ### The aggregate -/

/-- The value of an aggregated affine form at a point. -/
def Lin19.val (l : Lin19) (p : Chart) : ℝ :=
  (l.k : ℝ) / Sz + ∑ j : Fin 19, ((l.W j : ℝ) / Sz) * featGen p j

theorem push_val (l : Lin19) (t : ZTerm) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    (l.push t).val p = l.val p + t.lin.eval p := by
  have hq := termQ_feat t.kind t.index p h0 h1
  have ht := phaseT_feat t.index p
  unfold Lin19.val LinTerm.eval ZTerm.lin
  simp only
  rw [hq, ht]
  cases hk : t.kind <;>
    simp [Lin19.push, hk, Lin19.W, qForm, tForm, mom, Fin.sum_univ_succ] <;> ring

theorem zero_val (p : Chart) : Lin19.zero.val p = 0 := by
  simp [Lin19.val, Lin19.zero, Lin19.W, Fin.sum_univ_succ]

theorem foldl_val (zs : List ZTerm) (l : Lin19) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    (zs.foldl Lin19.push l).val p = l.val p + (zs.map fun t => t.lin.eval p).sum := by
  induction zs generalizing l with
  | nil => simp
  | cons t zs ih =>
    rw [List.foldl_cons, ih, push_val l t p h0 h1]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem linOf_val (zs : List ZTerm) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    (linOf zs).val p = (zs.map fun t => t.lin.eval p).sum := by
  unfold linOf
  rw [foldl_val zs Lin19.zero p h0 h1, zero_val, zero_add]

/-- The penalty sum of a penalty list. -/
def aggNLR (s : ℚ) (nls : List (IntVec × ℤ)) (p : Chart) : ℝ :=
  (nls.map fun e => (e.2 : ℝ) / Sz * nlVal s e.1 p).sum

theorem nlsOf_sum (s : ℚ) (zs : List ZTerm) (p : Chart) :
    aggNLR s (nlsOf zs) p = (zs.map fun t => (t.nl : ℝ) / Sz * nlVal s t.index p).sum := by
  unfold aggNLR
  induction zs with
  | nil => simp [nlsOf]
  | cons t zs ih =>
    unfold nlsOf at ih ⊢
    rw [List.filterMap_cons]
    by_cases h : t.nl = 0
    · simp [h, ih]
    · simp [h, ih]

theorem eval_sum (s : ℚ) (zs : List ZTerm) (p : Chart) :
    (zs.map fun t => t.eval s p).sum = (zs.map fun t => t.lin.eval p).sum -
      (zs.map fun t => (t.nl : ℝ) / Sz * nlVal s t.index p).sum := by
  induction zs with
  | nil => simp
  | cons t zs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    unfold ZTerm.eval
    ring

/-- The energy minorant of a support certificate. -/
def minorant (s : ℚ) (agg : Agg) (p : Chart) : ℝ :=
  (agg.lin.val p - aggNLR s agg.nls p - (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2)) / (2 * ac)

/-! ### Separate convexity of the penalty -/

theorem mul_exp_chord {y1 y2 t : ℝ} (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    ((1 - t) * y1 + t * y2) * Real.exp ((1 - t) * y1 + t * y2) ≤
      (1 - t) * (y1 * Real.exp y1) + t * (y2 * Real.exp y2) := by
  rcases lt_trichotomy y1 y2 with lt | eq | gt
  · have w : 0 < y2 - y1 := sub_pos.mpr lt
    have hy1 : y1 ≤ (1 - t) * y1 + t * y2 := by nlinarith
    have hy2 : (1 - t) * y1 + t * y2 ≤ y2 := by nlinarith
    have sec := secant_mul_exp y1 y2 ((1 - t) * y1 + t * y2) h1 hy1 hy2
    have e1 : y2 - ((1 - t) * y1 + t * y2) = (1 - t) * (y2 - y1) := by ring
    have e2 : (1 - t) * y1 + t * y2 - y1 = t * (y2 - y1) := by ring
    rw [e1, e2] at sec
    have : ((1 - t) * y1 + t * y2) * Real.exp ((1 - t) * y1 + t * y2) * (y2 - y1) ≤
        ((1 - t) * (y1 * Real.exp y1) + t * (y2 * Real.exp y2)) * (y2 - y1) := by linarith
    exact le_of_mul_le_mul_right this w
  · subst eq
    have e : (1 - t) * y1 + t * y1 = y1 := by ring
    rw [e]
    linarith
  · have w : 0 < y1 - y2 := sub_pos.mpr gt
    have hy1 : y2 ≤ (1 - t) * y1 + t * y2 := by nlinarith
    have hy2 : (1 - t) * y1 + t * y2 ≤ y1 := by nlinarith
    have sec := secant_mul_exp y2 y1 ((1 - t) * y1 + t * y2) h2 hy1 hy2
    have e1 : y1 - ((1 - t) * y1 + t * y2) = t * (y1 - y2) := by ring
    have e2 : (1 - t) * y1 + t * y2 - y2 = (1 - t) * (y1 - y2) := by ring
    rw [e1, e2] at sec
    have : ((1 - t) * y1 + t * y2) * Real.exp ((1 - t) * y1 + t * y2) * (y1 - y2) ≤
        ((1 - t) * (y1 * Real.exp y1) + t * (y2 * Real.exp y2)) * (y1 - y2) := by linarith
    exact le_of_mul_le_mul_right this w

theorem mul_exp_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x * Real.exp x ≤ y * Real.exp y :=
  mul_le_mul hxy (Real.exp_le_exp.mpr hxy) (Real.exp_pos _).le (hx.trans hxy)

theorem dualQ_nonneg (m : IntVec) (p : Chart) : 0 ≤ dualQ m p := by
  unfold dualQ
  have a : 0 ≤ (m 0 : ℝ) ^ 2 / (p 0) ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have b : 0 ≤ (dualB m p) ^ 2 / (p 1) ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have c : 0 ≤ (p 0) ^ 2 * (p 1) ^ 2 * (dualC m p) ^ 2 := by positivity
  linarith

/-- The penalty `y eʸ`, `y = π Q*/s²`, is separately convex on a box with
positive radial coordinates. -/
theorem nlVal_chord (s : ℚ) (m : IntVec) (b : Cell) (h0 : (0 : ℝ) < b.lo 0) (h1 : (0 : ℝ) < b.lo 1) :
    ChordUpper b (nlVal s m) := by
  have dq := dualQ_chord m b h0 h1
  intro p hp i t t0 t1 e
  have hd := dq p hp i t t0 t1 e
  simp only at hd
  set κ : ℝ := Real.pi / (s : ℝ) ^ 2 with hκ
  have κ0 : 0 ≤ κ := by positivity
  have nv (x : Chart) : nlVal s m x = κ * dualQ m x * Real.exp (κ * dualQ m x) := by
    unfold nlVal
    rw [hκ]
    ring_nf
  show (1 - t) * (-nlVal s m (atLower b p i)) + t * (-nlVal s m (atUpper b p i)) ≤ -nlVal s m p
  rw [nv, nv, nv]
  set yL := κ * dualQ m (atLower b p i)
  set yU := κ * dualQ m (atUpper b p i)
  have yL0 : 0 ≤ yL := mul_nonneg κ0 (dualQ_nonneg _ _)
  have yU0 : 0 ≤ yU := mul_nonneg κ0 (dualQ_nonneg _ _)
  have yp0 : 0 ≤ κ * dualQ m p := mul_nonneg κ0 (dualQ_nonneg _ _)
  have hy : κ * dualQ m p ≤ (1 - t) * yL + t * yU := by
    have := mul_le_mul_of_nonneg_left (show dualQ m p ≤ (1 - t) * dualQ m (atLower b p i) +
      t * dualQ m (atUpper b p i) by linarith) κ0
    simp only [yL, yU]
    linarith
  have mono := mul_exp_mono yp0 hy
  have conv := mul_exp_chord yL0 yU0 t0 t1
  linarith

/-! ### Chords on a box -/

theorem atLower_mem {b : Cell} {p : Chart} (hp : b.Mem p) (i : Axis) : b.Mem (atLower b p i) := by
  intro j
  by_cases eq : j = i
  · subst eq
    have e : atLower b p j j = b.lo j := Function.update_self _ _ _
    rw [e]
    exact ⟨le_rfl, (hp j).1.trans (hp j).2⟩
  · have e : atLower b p i j = p j := Function.update_of_ne eq _ _
    rw [e]
    exact hp j

theorem atUpper_mem {b : Cell} {p : Chart} (hp : b.Mem p) (i : Axis) : b.Mem (atUpper b p i) := by
  intro j
  by_cases eq : j = i
  · subst eq
    have e : atUpper b p j j = b.hi j := Function.update_self _ _ _
    rw [e]
    exact ⟨(hp j).1.trans (hp j).2, le_rfl⟩
  · have e : atUpper b p i j = p j := Function.update_of_ne eq _ _
    rw [e]
    exact hp j

theorem chordLower_congr_on {b : Cell} {F G : Chart → ℝ} (h : ∀ p, b.Mem p → F p = G p)
    (hG : ChordLower b G) : ChordLower b F := by
  intro p hp i t t0 t1 e
  have := hG p hp i t t0 t1 e
  rw [h p hp, h _ (atLower_mem hp i), h _ (atUpper_mem hp i)]
  exact this

theorem zsum_chord (s : ℚ) (zs : List ZTerm) (b : Cell) (h0 : (0 : ℝ) < b.lo 0) (h1 : (0 : ℝ) < b.lo 1)
    (hz : ∀ t ∈ zs, t.a ≤ 0 ∧ 0 ≤ t.nl) :
    ChordLower b (fun p => (zs.map fun t => t.eval s p).sum) := by
  induction zs with
  | nil => exact chordLower_congr (fun p => by simp) (chordLower_const b 0)
  | cons t rest ih =>
    obtain ⟨ta, tn⟩ := hz t List.mem_cons_self
    have slope : t.lin.slope ≤ 0 := by
      show (t.a : ℚ) / (Sz : ℚ) ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ta) (by norm_num [Sz])
    have hl := linTerm_chord t.lin b h0 h1 slope
    have hn := chordLower_negSmul (c := -((t.nl : ℝ) / Sz))
      (by have : (0 : ℝ) ≤ (t.nl : ℝ) / Sz := div_nonneg (by exact_mod_cast tn) Sz_pos.le; linarith)
      (nlVal_chord s t.index b h0 h1)
    have hr := ih (fun u hu => hz u (List.mem_cons_of_mem _ hu))
    refine chordLower_congr (fun p => ?_) (chordLower_add (chordLower_add hl hn) hr)
    simp only [List.map_cons, List.sum_cons]
    unfold ZTerm.eval
    ring

/-! ### Support facts -/

/-- What a checked support certificate provides: the minorant lies below the
energy at every valid point of the support box, and it is separately concave on
every box with positive radial coordinates. -/
structure SupportFacts (s : ℚ) (box : Cell) (agg : Agg) : Prop where
  pos : 0 < s
  lower : ∀ p, box.Mem p → (chartPoint p).Valid → minorant s agg p ≤ energy (chartPoint p)
  chord : ∀ b : Cell, (0 : ℝ) < b.lo 0 → (0 : ℝ) < b.lo 1 → ChordLower b (minorant s agg)

theorem minorant_eq (s : ℚ) (zs : List ZTerm) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    minorant s ⟨linOf zs, nlsOf zs⟩ p =
      ((zs.map fun t => t.eval s p).sum - (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2)) / (2 * ac) := by
  unfold minorant
  simp only
  rw [linOf_val zs p h0 h1, nlsOf_sum, eval_sum]

/-- **Soundness of the support check.** -/
theorem support_facts {s : ℚ} {box : Cell} {wits : List Wit} {agg : Agg}
    (h : supportOk s box wits agg = true) : SupportFacts s box agg := by
  unfold supportOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨spos, hw⟩, hst⟩, hlin⟩, hnls⟩ := h
  set zs := wits.map (witZ s box) with hzs
  have valid : ∀ t ∈ zs, ZValid s box t := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    exact witZ_valid s box x (hw x hx)
  have aggEq : agg = ⟨linOf zs, nlsOf zs⟩ := by
    cases agg
    simp only at hlin hnls
    rw [hlin, hnls]
  rw [aggEq]
  refine ⟨spos, ?_, ?_⟩
  · intro p hp hv
    obtain ⟨h0, h1⟩ := valid_diag hv
    rw [minorant_eq s zs p h0 h1]
    exact zsum_le_energy s spos box zs valid hst p hp hv
  · intro b h0 h1
    have hz : ∀ t ∈ zs, t.a ≤ 0 ∧ 0 ≤ t.nl := fun t ht => ⟨(valid t ht).1, (valid t ht).2.1⟩
    have base := zsum_chord s zs b h0 h1 hz
    have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
    have chordT : ChordLower b (fun p => ((zs.map fun t => t.eval s p).sum -
        (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2)) / (2 * ac)) := by
      have c1 := chordLower_add base (chordLower_const b (-(2 * (s : ℝ) + 2 / (s : ℝ) ^ 2)))
      have c2 := chordLower_smul (inv_nonneg.mpr acpos.le) c1
      exact chordLower_congr (fun p => by ring) c2
    refine chordLower_congr_on (fun p hp => ?_) chordT
    have p0 : 0 < p 0 := h0.trans_le (hp 0).1
    have p1 : 0 < p 1 := h1.trans_le (hp 1).1
    exact minorant_eq s zs p p0.ne' p1.ne'

end BccSharp.Coulomb.CompactCover.LeafFix
