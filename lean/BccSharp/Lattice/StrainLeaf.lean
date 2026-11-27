import BccSharp.Lattice.StrainTangent

set_option autoImplicit false

/-! Fixed-point arithmetic for the strain leaf check.

A rational operation costs the kernel three to four times an integer one, and
the rational leaf check of `BccSharp.Lattice.StrainTangent` took 1.5 to 3 s per leaf against 0.45 to
0.64 s for this one, so the leaf check is evaluated on integers: exact integer matrices with
power-of-two scales at the corners, and integer intervals at scale `2^64` with outward rounding
(`ZI`) for the second-derivative bounds. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.StrainTangent
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentE1

/-! ## Powers of two and rounded division

Integer and rational powers unfold in the kernel as repeated multiplication, so the powers of
two that this check introduces are natural-number powers (evaluated with GMP) cast to `ℤ` or
`ℚ`, and its divisions by powers of two are shifts. -/

/-- `2^k` as an integer, computed in `ℕ`. -/
def pw (k : ℕ) : ℤ := ((2 ^ k : ℕ) : ℤ)
/-- `2^k` as a rational, computed in `ℕ`. -/
def pwQ (k : ℕ) : ℚ := ((2 ^ k : ℕ) : ℚ)

@[simp] theorem pw_cast (k : ℕ) : ((pw k : ℤ) : ℝ) = 2 ^ k := by simp [pw]
@[simp] theorem pwQ_cast (k : ℕ) : ((pwQ k : ℚ) : ℝ) = 2 ^ k := by simp [pwQ]
theorem pw_eq (k : ℕ) : pw k = 2 ^ k := by simp [pw]
theorem pwQ_eq (k : ℕ) : pwQ k = 2 ^ k := by simp [pwQ]

/-- `⌊x / 2^e⌋`. -/
def fdivZ (x : ℤ) (e : ℕ) : ℤ := x >>> e
/-- `⌈x / 2^e⌉`. -/
def cdivZ (x : ℤ) (e : ℕ) : ℤ := -((-x) >>> e)

theorem fdivZ_eq (x : ℤ) (e : ℕ) : fdivZ x e = x / 2 ^ e := by
  rw [fdivZ, Int.shiftRight_eq_div_pow]
  push_cast
  rfl

theorem fdivZ_le (x : ℤ) (e : ℕ) : ((fdivZ x e : ℤ) : ℝ) ≤ (x : ℝ) / 2 ^ e := by
  rw [fdivZ_eq]
  have hp : (0 : ℤ) < 2 ^ e := by positivity
  have h := Int.ediv_mul_le x hp.ne'
  have hp' : (0 : ℝ) < 2 ^ e := by positivity
  rw [le_div_iff₀ hp']
  have : ((x / 2 ^ e * 2 ^ e : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
  push_cast at this
  exact this

theorem le_cdivZ (x : ℤ) (e : ℕ) : (x : ℝ) / 2 ^ e ≤ ((cdivZ x e : ℤ) : ℝ) := by
  have h := fdivZ_le (-x) e
  have e' : cdivZ x e = -fdivZ (-x) e := rfl
  rw [e']
  push_cast at h ⊢
  have : -((x : ℝ) / 2 ^ e) = (-(x : ℝ)) / 2 ^ e := by ring
  linarith

/-! ## Integer intervals at scale `2^64` -/

/-- The interval `[lo, hi] / 2^64`. -/
structure ZI where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace ZI

def Mem (a : ZI) (x : ℝ) : Prop := (a.lo : ℝ) / 2 ^ 64 ≤ x ∧ x ≤ (a.hi : ℝ) / 2 ^ 64

/-- The point `k / 2^64`. -/
def exact (k : ℤ) : ZI := ⟨k, k⟩
def add (a b : ZI) : ZI := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : ZI) : ZI := ⟨a.lo - b.hi, a.hi - b.lo⟩
def mul (a b : ZI) : ZI :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨fdivZ (min (min p1 p2) (min p3 p4)) 64, cdivZ (max (max p1 p2) (max p3 p4)) 64⟩
/-- `c x` for an integer `c`. -/
def smul (c : ℤ) (a : ZI) : ZI := ⟨min (c * a.lo) (c * a.hi), max (c * a.lo) (c * a.hi)⟩
/-- `(c / 2^e) x`, rounded outward. -/
def qmul (c : ℤ) (e : ℕ) (a : ZI) : ZI :=
  ⟨fdivZ (min (c * a.lo) (c * a.hi)) e, cdivZ (max (c * a.lo) (c * a.hi)) e⟩
def sq (a : ZI) : ZI :=
  if 0 ≤ a.lo then ⟨fdivZ (a.lo * a.lo) 64, cdivZ (a.hi * a.hi) 64⟩
  else if a.hi ≤ 0 then ⟨fdivZ (a.hi * a.hi) 64, cdivZ (a.lo * a.lo) 64⟩
  else ⟨0, cdivZ (max (a.lo * a.lo) (a.hi * a.hi)) 64⟩
/-- `x⁻¹` on an interval with positive lower end. -/
def inv (a : ZI) : ZI := ⟨pw 128 / a.hi, -((-pw 128) / a.lo)⟩

theorem mem_exact (k : ℤ) : (exact k).Mem ((k : ℝ) / 2 ^ 64) := ⟨le_rfl, le_rfl⟩

theorem mem_add {a b : ZI} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.add b).Mem (x + y) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  constructor <;> simp only [add] <;> push_cast <;> rw [add_div] <;> linarith

theorem mem_sub {a b : ZI} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.sub b).Mem (x - y) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  constructor <;> simp only [sub] <;> push_cast <;> rw [sub_div] <;> linarith

/-- `m / 2^64 / 2^64` from integers. -/
theorem cast_div2 (m : ℤ) : (m : ℝ) / 2 ^ 64 / 2 ^ 64 = (m : ℝ) / 2 ^ 128 := by
  rw [div_div]
  norm_num

theorem mem_mul {a b : ZI} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.mul b).Mem (x * y) := by
  have h := QI.mul_bounds_real ha hb
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  have e (u v : ℤ) : (u : ℝ) / 2 ^ 64 * ((v : ℝ) / 2 ^ 64) = ((u * v : ℤ) : ℝ) / 2 ^ 128 := by
    push_cast
    ring
  rw [e, e, e, e] at h
  set p1 := a.lo * b.lo
  set p2 := a.lo * b.hi
  set p3 := a.hi * b.lo
  set p4 := a.hi * b.hi
  have T : (0 : ℝ) < 2 ^ 128 := by positivity
  have cl (u v : ℤ) (huv : u ≤ v) : (u : ℝ) / 2 ^ 128 ≤ (v : ℝ) / 2 ^ 128 :=
    div_le_div_of_nonneg_right (by exact_mod_cast huv) T.le
  constructor
  · simp only [mul]
    set m := min (min p1 p2) (min p3 p4)
    have hm : ((fdivZ m 64 : ℤ) : ℝ) / 2 ^ 64 ≤ (m : ℝ) / 2 ^ 128 := by
      rw [← cast_div2]
      exact div_le_div_of_nonneg_right (fdivZ_le m 64) S.le
    refine hm.trans (le_trans ?_ h.1)
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact cl _ _ ((min_le_left _ _).trans (min_le_left _ _))
    · exact cl _ _ ((min_le_left _ _).trans (min_le_right _ _))
    · exact cl _ _ ((min_le_right _ _).trans (min_le_left _ _))
    · exact cl _ _ ((min_le_right _ _).trans (min_le_right _ _))
  · simp only [mul]
    set m := max (max p1 p2) (max p3 p4)
    have hm : (m : ℝ) / 2 ^ 128 ≤ ((cdivZ m 64 : ℤ) : ℝ) / 2 ^ 64 := by
      rw [← cast_div2]
      exact div_le_div_of_nonneg_right (le_cdivZ m 64) S.le
    refine le_trans (le_trans h.2 ?_) hm
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact cl _ _ ((le_max_left _ _).trans (le_max_left _ _))
    · exact cl _ _ ((le_max_right _ _).trans (le_max_left _ _))
    · exact cl _ _ ((le_max_left _ _).trans (le_max_right _ _))
    · exact cl _ _ ((le_max_right _ _).trans (le_max_right _ _))

theorem mem_smul (c : ℤ) {a : ZI} {x : ℝ} (ha : a.Mem x) : (a.smul c).Mem ((c : ℝ) * x) := by
  obtain ⟨h1, h2⟩ := ha
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  have cl (u v : ℤ) (huv : u ≤ v) : (u : ℝ) / 2 ^ 64 ≤ (v : ℝ) / 2 ^ 64 :=
    div_le_div_of_nonneg_right (by exact_mod_cast huv) S.le
  have e (u : ℤ) : ((c * u : ℤ) : ℝ) / 2 ^ 64 = (c : ℝ) * ((u : ℝ) / 2 ^ 64) := by
    push_cast
    ring
  constructor <;> simp only [smul]
  · rcases le_total 0 (c : ℝ) with hc | hc
    · refine (cl _ _ (min_le_left _ _)).trans ?_
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 hc
    · refine (cl _ _ (min_le_right _ _)).trans ?_
      rw [e]
      exact mul_le_mul_of_nonpos_left h2 hc
  · rcases le_total 0 (c : ℝ) with hc | hc
    · refine le_trans ?_ (cl _ _ (le_max_right _ _))
      rw [e]
      exact mul_le_mul_of_nonneg_left h2 hc
    · refine le_trans ?_ (cl _ _ (le_max_left _ _))
      rw [e]
      exact mul_le_mul_of_nonpos_left h1 hc

theorem mem_qmul (c : ℤ) (e : ℕ) {a : ZI} {x : ℝ} (ha : a.Mem x) :
    (a.qmul c e).Mem ((c : ℝ) / 2 ^ e * x) := by
  have h := mem_smul c ha
  have S : (0 : ℝ) < 2 ^ e := by positivity
  obtain ⟨h1, h2⟩ := h
  simp only [smul] at h1 h2
  constructor
  · simp only [qmul]
    have := fdivZ_le (min (c * a.lo) (c * a.hi)) e
    have h1' : ((min (c * a.lo) (c * a.hi) : ℤ) : ℝ) / 2 ^ 64 / 2 ^ e ≤ (c : ℝ) * x / 2 ^ e :=
      div_le_div_of_nonneg_right h1 S.le
    calc (((fdivZ (min (c * a.lo) (c * a.hi)) e : ℤ) : ℝ)) / 2 ^ 64
        ≤ ((min (c * a.lo) (c * a.hi) : ℤ) : ℝ) / 2 ^ e / 2 ^ 64 :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = ((min (c * a.lo) (c * a.hi) : ℤ) : ℝ) / 2 ^ 64 / 2 ^ e := by ring
      _ ≤ (c : ℝ) * x / 2 ^ e := h1'
      _ = (c : ℝ) / 2 ^ e * x := by ring
  · simp only [qmul]
    have := le_cdivZ (max (c * a.lo) (c * a.hi)) e
    have h2' : (c : ℝ) * x / 2 ^ e ≤ ((max (c * a.lo) (c * a.hi) : ℤ) : ℝ) / 2 ^ 64 / 2 ^ e :=
      div_le_div_of_nonneg_right h2 S.le
    calc (c : ℝ) / 2 ^ e * x = (c : ℝ) * x / 2 ^ e := by ring
      _ ≤ ((max (c * a.lo) (c * a.hi) : ℤ) : ℝ) / 2 ^ 64 / 2 ^ e := h2'
      _ = ((max (c * a.lo) (c * a.hi) : ℤ) : ℝ) / 2 ^ e / 2 ^ 64 := by ring
      _ ≤ (((cdivZ (max (c * a.lo) (c * a.hi)) e : ℤ) : ℝ)) / 2 ^ 64 :=
          div_le_div_of_nonneg_right this (by positivity)

theorem mem_sq {a : ZI} {x : ℝ} (ha : a.Mem x) : a.sq.Mem (x * x) := by
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  obtain ⟨h1, h2⟩ := ha
  have e (u v : ℤ) : ((u * v : ℤ) : ℝ) / 2 ^ 64 / 2 ^ 64 = (u : ℝ) / 2 ^ 64 * ((v : ℝ) / 2 ^ 64) := by
    push_cast
    ring
  have lo (u : ℤ) : ((fdivZ u 64 : ℤ) : ℝ) / 2 ^ 64 ≤ (u : ℝ) / 2 ^ 64 / 2 ^ 64 :=
    div_le_div_of_nonneg_right (fdivZ_le u 64) S.le
  have hi (u : ℤ) : (u : ℝ) / 2 ^ 64 / 2 ^ 64 ≤ ((cdivZ u 64 : ℤ) : ℝ) / 2 ^ 64 :=
    div_le_div_of_nonneg_right (le_cdivZ u 64) S.le
  set l := (a.lo : ℝ) / 2 ^ 64
  set u := (a.hi : ℝ) / 2 ^ 64
  unfold sq
  split_ifs with hl hu
  · have hl' : 0 ≤ l := by
      have : (0 : ℝ) ≤ a.lo := by exact_mod_cast hl
      positivity
    refine ⟨(lo _).trans ?_, le_trans ?_ (hi _)⟩ <;> rw [e]
    · exact mul_le_mul h1 h1 hl' (hl'.trans h1)
    · exact mul_le_mul h2 h2 (hl'.trans h1) (hl'.trans (h1.trans h2))
  · have hu' : u ≤ 0 := by
      have : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hu
      exact div_nonpos_of_nonpos_of_nonneg this S.le
    have hx : x ≤ 0 := h2.trans hu'
    refine ⟨(lo _).trans ?_, le_trans ?_ (hi _)⟩ <;> rw [e]
    · exact mul_le_mul_of_nonpos_of_nonpos' h2 h2 hu' hx
    · exact mul_le_mul_of_nonpos_of_nonpos' h1 h1 hx (h1.trans hx)
  · constructor
    · simp only [Int.cast_zero, zero_div]
      exact mul_self_nonneg x
    · refine le_trans ?_ (hi _)
      rcases le_total 0 x with hx | hx
      · have h3 : (a.hi : ℤ) * a.hi ≤ max (a.lo * a.lo) (a.hi * a.hi) := le_max_right _ _
        have h4 : ((a.hi * a.hi : ℤ) : ℝ) / 2 ^ 64 / 2 ^ 64 ≤
            ((max (a.lo * a.lo) (a.hi * a.hi) : ℤ) : ℝ) / 2 ^ 64 / 2 ^ 64 := by
          apply div_le_div_of_nonneg_right _ S.le
          apply div_le_div_of_nonneg_right _ S.le
          exact_mod_cast h3
        refine le_trans ?_ h4
        rw [e]
        exact mul_le_mul h2 h2 hx (hx.trans h2)
      · have h3 : (a.lo : ℤ) * a.lo ≤ max (a.lo * a.lo) (a.hi * a.hi) := le_max_left _ _
        have h4 : ((a.lo * a.lo : ℤ) : ℝ) / 2 ^ 64 / 2 ^ 64 ≤
            ((max (a.lo * a.lo) (a.hi * a.hi) : ℤ) : ℝ) / 2 ^ 64 / 2 ^ 64 := by
          apply div_le_div_of_nonneg_right _ S.le
          apply div_le_div_of_nonneg_right _ S.le
          exact_mod_cast h3
        refine le_trans ?_ h4
        rw [e]
        exact mul_le_mul_of_nonpos_of_nonpos' h1 h1 hx (h1.trans hx)

theorem mem_inv {a : ZI} {x : ℝ} (hpos : 0 < a.lo) (ha : a.Mem x) : a.inv.Mem x⁻¹ := by
  rw [show inv a = ⟨2 ^ 128 / a.hi, -((-(2 ^ 128 : ℤ)) / a.lo)⟩ by simp [inv, pw_eq]]
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  obtain ⟨h1, h2⟩ := ha
  have hl : (0 : ℝ) < (a.lo : ℝ) / 2 ^ 64 := by
    have : (0 : ℝ) < a.lo := by exact_mod_cast hpos
    positivity
  have hx : 0 < x := hl.trans_le h1
  have hh : (0 : ℝ) < (a.hi : ℝ) := by
    have := hl.trans_le (h1.trans h2)
    have : (0 : ℝ) < (a.hi : ℝ) / 2 ^ 64 := this
    exact (div_pos_iff_of_pos_right S).mp this
  have hhZ : (0 : ℤ) < a.hi := by exact_mod_cast hh
  constructor
  · simp only
    have hq := Int.ediv_mul_le (2 ^ 128 : ℤ) hhZ.ne'
    have hq' : (((2 ^ 128 : ℤ) / a.hi : ℤ) : ℝ) * a.hi ≤ 2 ^ 128 := by exact_mod_cast hq
    have : (((2 ^ 128 : ℤ) / a.hi : ℤ) : ℝ) / 2 ^ 64 ≤ ((a.hi : ℝ) / 2 ^ 64)⁻¹ := by
      rw [inv_div, div_le_div_iff₀ S hh]
      nlinarith
    exact this.trans (inv_anti₀ hx h2)
  · simp only
    have hq := Int.ediv_mul_le (-(2 ^ 128 : ℤ)) hpos.ne'
    have hq' : (((-(2 ^ 128 : ℤ)) / a.lo : ℤ) : ℝ) * a.lo ≤ -(2 ^ 128) := by exact_mod_cast hq
    have hlo : (0 : ℝ) < (a.lo : ℝ) := by exact_mod_cast hpos
    have : ((a.lo : ℝ) / 2 ^ 64)⁻¹ ≤ (((-((-(2 ^ 128 : ℤ)) / a.lo) : ℤ) : ℝ)) / 2 ^ 64 := by
      rw [inv_div, div_le_div_iff₀ hlo S]
      push_cast
      nlinarith
    exact (inv_anti₀ hl h1).trans this

end ZI


theorem ZI.mem_congr {a : ZI} {x y : ℝ} (h : a.Mem x) (e : x = y) : a.Mem y := e ▸ h

theorem ZI.mem_one : (ZI.exact (pw 64)).Mem 1 :=
  ZI.mem_congr (ZI.mem_exact (pw 64)) (by rw [pw_cast]; norm_num)

/-- `⌈x / n⌉` for a positive integer `n`. -/
def cdivN (x n : ℤ) : ℤ := -((-x) / n)

theorem le_cdivN (x n : ℤ) (hn : 0 < n) : (x : ℝ) / n ≤ ((cdivN x n : ℤ) : ℝ) := by
  have h := Int.ediv_mul_le (-x) hn.ne'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h' : (((-x) / n : ℤ) : ℝ) * n ≤ -(x : ℝ) := by exact_mod_cast h
  unfold cdivN
  push_cast
  rw [div_le_iff₀ hn']
  nlinarith

/-! ## Integer interval matrices -/

abbrev ZM := Matrix (Fin 3) (Fin 3) ZI

def ZM.Mem (A : ZM) (X : Mat) : Prop := ∀ i j, (A i j).Mem (X i j)

/-- An integer matrix at scale `2^e`, as a real matrix. -/
def castZ (C : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) : Mat := fun i j => (C i j : ℝ) / 2 ^ e

/-- The `s`-box ends at scale `2^64`, rounded outward. -/
def sLoZ (ref : Reference) (b : Rectangle) (i : Fin 5) : ℤ :=
  ⌊min (sLo ref i * b.lo i) (sHi ref i * b.lo i) * pwQ 64⌋
def sHiZ (ref : Reference) (b : Rectangle) (i : Fin 5) : ℤ :=
  ⌈max (sLo ref i * b.hi i) (sHi ref i * b.hi i) * pwQ 64⌉

structure ZBox where
  lo : Fin 5 → ℤ
  hi : Fin 5 → ℤ

def ZBox.Mem (z : ZBox) (q : Fin 5 → ℝ) : Prop :=
  ∀ i, (z.lo i : ℝ) / 2 ^ 64 ≤ q i ∧ q i ≤ (z.hi i : ℝ) / 2 ^ 64

/-- The `s`-box of a `w`-box, as vector literals (each end is evaluated once). -/
def zBox (ref : Reference) (b : Rectangle) : ZBox :=
  ⟨![sLoZ ref b 0, sLoZ ref b 1, sLoZ ref b 2, sLoZ ref b 3, sLoZ ref b 4],
    ![sHiZ ref b 0, sHiZ ref b 1, sHiZ ref b 2, sHiZ ref b 3, sHiZ ref b 4]⟩

theorem zBox_ends (ref : Reference) (b : Rectangle) (i : Fin 5) :
    (zBox ref b).lo i = sLoZ ref b i ∧ (zBox ref b).hi i = sHiZ ref b i := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

theorem zBox_mem (ref : Reference) (b : Rectangle) (w : Point) (hw : b.Mem w) :
    (zBox ref b).Mem (sOf ref w) := by
  intro i
  rw [(zBox_ends ref b i).1, (zBox_ends ref b i).2, sLoZ, sHiZ, pwQ_eq]
  obtain ⟨h0, hl, hh⟩ := sScale_bounds ref i
  have h0' : (0 : ℝ) ≤ sLo ref i := by exact_mod_cast h0
  have hc : 0 ≤ sScale ref i := h0'.trans hl
  obtain ⟨w1, w2⟩ := hw i
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  have lower : ((min (sLo ref i * b.lo i) (sHi ref i * b.lo i) : ℚ) : ℝ) ≤ sScale ref i * b.lo i := by
    push_cast
    rcases le_total 0 (b.lo i : ℝ) with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hh h)
  have upper : sScale ref i * b.hi i ≤ ((max (sLo ref i * b.hi i) (sHi ref i * b.hi i) : ℚ) : ℝ) := by
    push_cast
    rcases le_total 0 (b.hi i : ℝ) with h | h
    · exact (mul_le_mul_of_nonneg_right hh h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hl h).trans (le_max_left _ _)
  have fl (q : ℚ) : ((⌊q * 2 ^ 64⌋ : ℤ) : ℝ) / 2 ^ 64 ≤ (q : ℝ) := by
    rw [div_le_iff₀ S]
    have := Int.floor_le (q * 2 ^ 64)
    have : ((⌊q * 2 ^ 64⌋ : ℤ) : ℝ) ≤ ((q * 2 ^ 64 : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this
    exact this
  have ce (q : ℚ) : (q : ℝ) ≤ ((⌈q * 2 ^ 64⌉ : ℤ) : ℝ) / 2 ^ 64 := by
    rw [le_div_iff₀ S]
    have := Int.le_ceil (q * 2 ^ 64)
    have : ((q * 2 ^ 64 : ℚ) : ℝ) ≤ ((⌈q * 2 ^ 64⌉ : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at this
    exact this
  constructor
  · refine (fl _).trans (lower.trans ?_)
    exact mul_le_mul_of_nonneg_left w1 hc
  · refine le_trans ?_ ((upper).trans (ce _))
    exact mul_le_mul_of_nonneg_left w2 hc

def zIv (zb : ZBox) (i : Fin 5) : ZI := ⟨zb.lo i, zb.hi i⟩

def boxJZ (zb : ZBox) : ZM :=
  let s0 := zIv zb 0
  let s1 := zIv zb 1
  let s2 := zIv zb 2
  let s3 := zIv zb 3
  let s4 := zIv zb 4
  !![((ZI.exact (pw 64)).add s0).add s1, s2, s3;
     s2, ((ZI.exact (pw 64)).add s1).sub s0, s4;
     s3, s4, (ZI.exact (pw 64)).sub (s1.smul 2)]

theorem boxJZ_mem (zb : ZBox) (q : Fin 5 → ℝ) (hq : zb.Mem q) : ZM.Mem (boxJZ zb) (sJ q) := by
  have hs (i : Fin 5) : (zIv zb i).Mem (q i) := hq i
  have e00 := ZI.mem_add (ZI.mem_add ZI.mem_one (hs 0)) (hs 1)
  have e11 := ZI.mem_sub (ZI.mem_add ZI.mem_one (hs 1)) (hs 0)
  have e22 := ZI.mem_congr (ZI.mem_sub ZI.mem_one (ZI.mem_smul 2 (hs 1))) (by push_cast; ring :
    (1 : ℝ) - ((2 : ℤ) : ℝ) * q 1 = 1 - 2 * q 1)
  intro i j
  fin_cases i <;> fin_cases j
  · exact e00
  · exact hs 2
  · exact hs 3
  · exact hs 2
  · exact e11
  · exact hs 4
  · exact hs 3
  · exact hs 4
  · exact e22

def adjZ (X : ZM) : ZM :=
  !![((X 1 1).mul (X 2 2)).sub ((X 1 2).mul (X 2 1)), ((X 0 2).mul (X 2 1)).sub ((X 0 1).mul (X 2 2)),
      ((X 0 1).mul (X 1 2)).sub ((X 0 2).mul (X 1 1));
     ((X 1 2).mul (X 2 0)).sub ((X 1 0).mul (X 2 2)), ((X 0 0).mul (X 2 2)).sub ((X 0 2).mul (X 2 0)),
      ((X 0 2).mul (X 1 0)).sub ((X 0 0).mul (X 1 2));
     ((X 1 0).mul (X 2 1)).sub ((X 1 1).mul (X 2 0)), ((X 0 1).mul (X 2 0)).sub ((X 0 0).mul (X 2 1)),
      ((X 0 0).mul (X 1 1)).sub ((X 0 1).mul (X 1 0))]

theorem adjZ_mem {X : ZM} {Y : Mat} (h : ZM.Mem X Y) : ZM.Mem (adjZ X) (adj3 Y) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    exact ZI.mem_sub (ZI.mem_mul (h _ _) (h _ _)) (ZI.mem_mul (h _ _) (h _ _))

def detZ (X A : ZM) : ZI :=
  (((X 0 0).mul (A 0 0)).add ((X 0 1).mul (A 1 0))).add ((X 0 2).mul (A 2 0))

theorem detZ_mem {X A : ZM} {Y : Mat} (hX : ZM.Mem X Y) (hA : ZM.Mem A (adj3 Y)) :
    (detZ X A).Mem (det3 Y) :=
  ZI.mem_add (ZI.mem_add (ZI.mem_mul (hX 0 0) (hA 0 0)) (ZI.mem_mul (hX 0 1) (hA 1 0)))
    (ZI.mem_mul (hX 0 2) (hA 2 0))

def rowZ (C : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) (X : ZM) (i : Fin 3) : ZI :=
  (((X i 0).qmul (C i 0) e).add ((X i 1).qmul (C i 1) e)).add ((X i 2).qmul (C i 2) e)

/-- `Σ_ij (C_ij / 2^e) X_ij`. -/
def dotZ (C : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) (X : ZM) : ZI :=
  ((rowZ C e X 0).add (rowZ C e X 1)).add (rowZ C e X 2)

theorem dotZ_mem (C : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) {X : ZM} {Y : Mat} (h : ZM.Mem X Y) :
    (dotZ C e X).Mem (dot3 (castZ C e) Y) := by
  have row (i : Fin 3) : (rowZ C e X i).Mem (∑ j, castZ C e i j * Y i j) := by
    rw [Fin.sum_univ_three]
    exact ZI.mem_add (ZI.mem_add (ZI.mem_qmul _ _ (h i 0)) (ZI.mem_qmul _ _ (h i 1)))
      (ZI.mem_qmul _ _ (h i 2))
  unfold dot3
  rw [Fin.sum_univ_three]
  exact ZI.mem_add (ZI.mem_add (row 0) (row 1)) (row 2)

def rowSqZ (X : ZM) (i : Fin 3) : ZI := (((X i 0).sq).add ((X i 1).sq)).add ((X i 2).sq)

def dotSqZ (X : ZM) : ZI := ((rowSqZ X 0).add (rowSqZ X 1)).add (rowSqZ X 2)

theorem dotSqZ_mem {X : ZM} {Y : Mat} (h : ZM.Mem X Y) : (dotSqZ X).Mem (dot3 Y Y) := by
  have row (i : Fin 3) : (rowSqZ X i).Mem (∑ j, Y i j * Y i j) := by
    rw [Fin.sum_univ_three]
    exact ZI.mem_add (ZI.mem_add (ZI.mem_sq (h i 0)) (ZI.mem_sq (h i 1))) (ZI.mem_sq (h i 2))
  unfold dot3
  rw [Fin.sum_univ_three]
  exact ZI.mem_add (ZI.mem_add (row 0) (row 1)) (row 2)

/-! ## Direction data on integer intervals -/

def d1Z (i : Fin 5) (A : ZM) : ZI :=
  if i = 0 then (A 0 0).sub (A 1 1)
  else if i = 1 then ((A 0 0).add (A 1 1)).sub ((A 2 2).smul 2)
  else if i = 2 then (A 0 1).add (A 1 0)
  else if i = 3 then (A 0 2).add (A 2 0)
  else (A 1 2).add (A 2 1)

theorem d1Z_mem (i : Fin 5) {A : ZM} {Y : Mat} (h : ZM.Mem A Y) :
    (d1Z i A).Mem (trm Y (castM (Ecoord i))) := by
  fin_cases i
  · exact ZI.mem_congr (ZI.mem_sub (h 0 0) (h 1 1))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three]; ring)
  · exact ZI.mem_congr (ZI.mem_sub (ZI.mem_add (h 0 0) (h 1 1)) (ZI.mem_smul 2 (h 2 2)))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three]; ring)
  · exact ZI.mem_congr (ZI.mem_add (h 0 1) (h 1 0))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three])
  · exact ZI.mem_congr (ZI.mem_add (h 0 2) (h 2 0))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three])
  · exact ZI.mem_congr (ZI.mem_add (h 1 2) (h 2 1))
      (by simp [trm, Ecoord, castM, Fin.sum_univ_three])

def d2Z (i : Fin 5) (J : ZM) : ZI :=
  if i = 0 then (J 2 2).smul (-2)
  else if i = 1 then (((J 0 0).smul (-4)).add ((J 1 1).smul (-4))).add ((J 2 2).smul 2)
  else if i = 2 then (J 2 2).smul (-2)
  else if i = 3 then (J 1 1).smul (-2)
  else (J 0 0).smul (-2)

theorem d2Z_mem (i : Fin 5) {J : ZM} {Y : Mat} (h : ZM.Mem J Y) :
    (d2Z i J).Mem (2 * trm (adj3 (castM (Ecoord i))) Y) := by
  fin_cases i
  · exact ZI.mem_congr (ZI.mem_smul (-2) (h 2 2))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])
  · exact ZI.mem_congr (ZI.mem_add (ZI.mem_add (ZI.mem_smul (-4) (h 0 0)) (ZI.mem_smul (-4) (h 1 1)))
      (ZI.mem_smul 2 (h 2 2))) (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three]; ring)
  · exact ZI.mem_congr (ZI.mem_smul (-2) (h 2 2))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])
  · exact ZI.mem_congr (ZI.mem_smul (-2) (h 1 1))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])
  · exact ZI.mem_congr (ZI.mem_smul (-2) (h 0 0))
      (by simp [trm, adj3, Ecoord, castM, Fin.sum_univ_three])

/-- `⟨P, E_i⟩` for an integer matrix. -/
def dirEZ (i : Fin 5) (P : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  if i = 0 then P 0 0 - P 1 1 else if i = 1 then P 0 0 + P 1 1 - 2 * P 2 2
  else if i = 2 then P 0 1 + P 1 0 else if i = 3 then P 0 2 + P 2 0 else P 1 2 + P 2 1

/-- `⟨D, adj E_i⟩` for an integer matrix. -/
def adjEZ (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  if i = 0 then -D 2 2 else if i = 1 then -2 * D 0 0 - 2 * D 1 1 + D 2 2
  else if i = 2 then -D 2 2 else if i = 3 then -D 1 1 else -D 0 0

def frobEZ (i : Fin 5) : ℤ := if i = 1 then 6 else 2

/-- `⟨D, dadj(Y, E_i)⟩ = ⟨W_i D, Y⟩` for an integer matrix. -/
def WmatZ (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  if i = 0 then !![-D 2 2, 0, D 0 2; 0, D 2 2, -D 1 2; D 2 0, -D 2 1, -D 0 0 + D 1 1]
  else if i = 1 then
    !![-2 * D 1 1 + D 2 2, 2 * D 0 1, -D 0 2; 2 * D 1 0, -2 * D 0 0 + D 2 2, -D 1 2;
      -D 2 0, -D 2 1, D 0 0 + D 1 1]
  else if i = 2 then !![0, -D 2 2, D 1 2; -D 2 2, 0, D 0 2; D 2 1, D 2 0, -D 0 1 - D 1 0]
  else if i = 3 then !![0, D 2 1, -D 1 1; D 1 2, -D 0 2 - D 2 0, D 1 0; -D 1 1, D 0 1, 0]
  else !![-D 1 2 - D 2 1, D 0 2, D 0 1; D 2 0, 0, -D 0 0; D 1 0, -D 0 0, 0]

theorem dirEZ_eq (i : Fin 5) (P : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) :
    dot3 (castZ P e) (castM (Ecoord i)) = (dirEZ i P : ℝ) / 2 ^ e := by
  fin_cases i <;> simp [dot3, dirEZ, Ecoord, castM, castZ, Fin.sum_univ_three] <;> ring

theorem adjEZ_eq (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) :
    dot3 (castZ D e) (adj3 (castM (Ecoord i))) = (adjEZ i D : ℝ) / 2 ^ e := by
  fin_cases i <;> simp [dot3, adjEZ, adj3, Ecoord, castM, castZ, Fin.sum_univ_three] <;> ring

theorem frobEZ_eq (i : Fin 5) : dot3 (castM (Ecoord i)) (castM (Ecoord i)) = (frobEZ i : ℝ) := by
  fin_cases i <;> simp [dot3, frobEZ, Ecoord, castM, Fin.sum_univ_three] <;> norm_num

theorem WmatZ_eq (i : Fin 5) (D : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) (Y : Mat) :
    dot3 (castZ D e) (dadj3 Y (castM (Ecoord i))) = dot3 (castZ (WmatZ i D) e) Y := by
  fin_cases i <;> simp [dot3, dadj3, WmatZ, Ecoord, castM, castZ, Fin.sum_univ_three] <;> ring


/-! ## Integer aggregates and frames -/

/-- An aggregate at scale `2^96`. -/
structure ZAgg where
  a : ℤ
  p00 : ℤ
  p01 : ℤ
  p02 : ℤ
  p11 : ℤ
  p12 : ℤ
  p22 : ℤ
  d00 : ℤ
  d01 : ℤ
  d02 : ℤ
  d11 : ℤ
  d12 : ℤ
  d22 : ℤ
  deriving DecidableEq, Repr

def ZAgg.toAgg (z : ZAgg) : Aggregate :=
  ⟨z.a / 2 ^ 96, z.p00 / 2 ^ 96, z.p01 / 2 ^ 96, z.p02 / 2 ^ 96, z.p11 / 2 ^ 96, z.p12 / 2 ^ 96,
    z.p22 / 2 ^ 96, z.d00 / 2 ^ 96, z.d01 / 2 ^ 96, z.d02 / 2 ^ 96, z.d11 / 2 ^ 96, z.d12 / 2 ^ 96,
    z.d22 / 2 ^ 96⟩

def mul3Z (A B : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 0 2 * B 2 0, A 0 0 * B 0 1 + A 0 1 * B 1 1 + A 0 2 * B 2 1,
      A 0 0 * B 0 2 + A 0 1 * B 1 2 + A 0 2 * B 2 2;
     A 1 0 * B 0 0 + A 1 1 * B 1 0 + A 1 2 * B 2 0, A 1 0 * B 0 1 + A 1 1 * B 1 1 + A 1 2 * B 2 1,
      A 1 0 * B 0 2 + A 1 1 * B 1 2 + A 1 2 * B 2 2;
     A 2 0 * B 0 0 + A 2 1 * B 1 0 + A 2 2 * B 2 0, A 2 0 * B 0 1 + A 2 1 * B 1 1 + A 2 2 * B 2 1,
      A 2 0 * B 0 2 + A 2 1 * B 1 2 + A 2 2 * B 2 2]

def tr3Z (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![A 0 0, A 1 0, A 2 0; A 0 1, A 1 1, A 2 1; A 0 2, A 1 2, A 2 2]

/-- Twice the cubic frames (integer matrices). -/
def dirFrame2 : Reference → Matrix (Fin 3) (Fin 3) ℤ
  | .bcc => !![2, 0, 1; 0, 2, 1; 0, 0, 1]
  | .fcc => !![2, 2, 0; 2, 0, 2; 0, 2, 2]

def dualFrame2 : Reference → Matrix (Fin 3) (Fin 3) ℤ
  | .bcc => !![2, 0, 0; 0, 2, 0; -2, -2, 4]
  | .fcc => !![1, 1, -1; 1, -1, 1; -1, 1, 1]

def PmatZ (z : ZAgg) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![z.p00, z.p01, z.p02; z.p01, z.p11, z.p12; z.p02, z.p12, z.p22]
def DmatZ (z : ZAgg) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![z.d00, z.d01, z.d02; z.d01, z.d11, z.d12; z.d02, z.d12, z.d22]

/-- `P'` at scale `2^98`. -/
def framePZ (ref : Reference) (z : ZAgg) : Matrix (Fin 3) (Fin 3) ℤ :=
  mul3Z (mul3Z (dirFrame2 ref) (PmatZ z)) (tr3Z (dirFrame2 ref))
/-- `D'` at scale `2^98`. -/
def frameDZ (ref : Reference) (z : ZAgg) : Matrix (Fin 3) (Fin 3) ℤ :=
  mul3Z (mul3Z (dualFrame2 ref) (DmatZ z)) (tr3Z (dualFrame2 ref))

theorem framePZ_cast (ref : Reference) (z : ZAgg) :
    castM (Pframe ref z.toAgg) = castZ (framePZ ref z) 98 := by
  rw [Pframe_eq]
  ext i j
  cases ref <;> fin_cases i <;> fin_cases j <;>
    simp [castM, castZ, framePZ, mul3Z, tr3Z, dirFrame2, dirFrame, PmatZ, Pmat, ZAgg.toAgg,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem frameDZ_cast (ref : Reference) (z : ZAgg) :
    castM (Dframe ref z.toAgg) = castZ (frameDZ ref z) 98 := by
  rw [Dframe_eq]
  ext i j
  cases ref <;> fin_cases i <;> fin_cases j <;>
    simp [castM, castZ, frameDZ, mul3Z, tr3Z, dualFrame2, dualFrame, DmatZ, Dmat, ZAgg.toAgg,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-! ## Constants at scale `2^64` -/

def c4invLo : ℤ := 11620720580245083920
def c4invHi : ℤ := 11620720580245083922

def c1Z : Reference → ZI
  | .bcc => ⟨29282380947994691627, 29282380947994691628⟩
  | .fcc => ⟨c4invLo, c4invHi⟩

def c2Z : Reference → ZI
  | .bcc => ⟨c4invLo, c4invHi⟩
  | .fcc => ⟨29282380947994691627, 29282380947994691628⟩

theorem cZ_mem (ref : Reference) : (c1Z ref).Mem (c1R ref) ∧ (c2Z ref).Mem (c2R ref) := by
  obtain ⟨lo, hi⟩ := fccLength_sq_bounds
  have hpos : 0 < Constants.fccLength ^ 2 := by unfold Constants.fccLength; positivity
  have lo' : ((29282380947994691627 : ℤ) : ℝ) / 2 ^ 64 ≤ Constants.fccLength ^ 2 := by
    refine le_trans (le_of_eq ?_) lo
    norm_num [cbrt4Lo]
  have hi' : Constants.fccLength ^ 2 ≤ ((29282380947994691628 : ℤ) : ℝ) / 2 ^ 64 := by
    refine hi.trans (le_of_eq ?_)
    norm_num [cbrt4Hi]
  have ilo : ((c4invLo : ℤ) : ℝ) / 2 ^ 64 ≤ (Constants.fccLength ^ 2)⁻¹ := by
    refine le_trans ?_ (inv_anti₀ hpos hi')
    norm_num [c4invLo]
  have ihi : (Constants.fccLength ^ 2)⁻¹ ≤ ((c4invHi : ℤ) : ℝ) / 2 ^ 64 := by
    refine (inv_anti₀ (by norm_num) lo').trans ?_
    norm_num [c4invHi]
  have e1 : c1R .fcc = (Constants.fccLength ^ 2)⁻¹ := by simp [c1R, framePow, inv_pow]
  have e2 : c2R .fcc = Constants.fccLength ^ 2 := by simp [c2R, framePow, inv_pow]
  cases ref
  · exact ⟨⟨lo', hi'⟩, by simpa [c2Z, c2R, framePow, ZI.Mem] using And.intro ilo ihi⟩
  · rw [e1, e2]
    exact ⟨⟨ilo, ihi⟩, ⟨lo', hi'⟩⟩

/-- `γ` of each mode, as an interval at scale `2^64`. -/
def gammaZ (e2 : Bool) : ZI := if e2 then ⟨87140687507897918, 87140687507897919⟩ else ⟨0, 0⟩

theorem gammaZ_mem (e2 : Bool) : (gammaZ e2).Mem (modeGamma e2 : ℝ) := by
  cases e2
  · simp [gammaZ, modeGamma, ZI.Mem]
  · simp only [gammaZ, modeGamma, ZI.Mem, ite_true]
    constructor <;> norm_num [gapFactorUpper, kappaUpper, scaleHi, Constants.gapBracket, Constants.fccBracket,
      Constants.bccBracket, Constants.Interval.sub]

/-- The target of each mode, rounded up at scale `2^64`. -/
def targetZ (e2 : Bool) : ℤ := if e2 then 2057522107530222059 else 2060831158889259753

theorem targetZ_ge (e2 : Bool) : (modeTarget e2 : ℝ) ≤ (targetZ e2 : ℝ) / 2 ^ 64 := by
  cases e2
  · simp only [modeTarget, targetZ, Bool.false_eq_true, ite_false]
    norm_num [HfccUpper, Constants.fccBracket]
  · simp only [modeTarget, targetZ, ite_true]
    norm_num [HbccUpper, scaleLo, Constants.bccBracket]

/-! ## Box data and the second-derivative enclosure -/

structure ZBoxData where
  J : ZM
  A : ZM
  d : ZI
  lam : ZI
  dinv : ZI
  AI : ZI
  BI : ZI

/-- A proposed `⌊(2^256 / D)^(1/3)⌋`. -/
def lamOfZ (D : ℤ) : ℤ := (icbrt ((2 ^ 256 : ℕ) / D.toNat) : ℤ)

def zBoxData (c1 c2 γ : ZI) (P D : Matrix (Fin 3) (Fin 3) ℤ) (zb : ZBox) : ZBoxData :=
  let J := boxJZ zb
  let A := adjZ J
  let d := detZ J A
  ⟨J, A, d, ⟨lamOfZ d.hi, lamOfZ d.lo + 1⟩, d.inv,
    (c1.mul (dotZ P 98 J)).sub (γ.smul 6),
    (c2.mul (dotZ D 98 A)).add (γ.mul (dotSqZ J))⟩

def lamOKZ (d L : ZI) : Bool :=
  decide (0 < d.lo ∧ 0 ≤ L.lo ∧ L.lo ^ 3 * d.hi ≤ pw 256 ∧ pw 256 ≤ L.hi ^ 3 * d.lo)

theorem lamZ_mem (d L : ZI) (ok : lamOKZ d L = true) (x : ℝ) (hx : d.Mem x) :
    0 < x ∧ L.Mem (x ^ (-(1/3 : ℝ))) := by
  obtain ⟨hdl, hlo, hl, hu⟩ := of_decide_eq_true ok
  rw [pw_eq] at hl hu
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  have hdl' : (0 : ℝ) < (d.lo : ℝ) / 2 ^ 64 := by
    have : (0 : ℝ) < d.lo := by exact_mod_cast hdl
    positivity
  have hxpos : 0 < x := hdl'.trans_le hx.1
  refine ⟨hxpos, ?_⟩
  set y := x ^ (-(1/3 : ℝ)) with hy
  have ypos : 0 < y := Real.rpow_pos_of_pos hxpos _
  have cube : y ^ 3 * x = 1 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
    rw [Real.rpow_neg_one, inv_mul_cancel₀ hxpos.ne']
  have hlo' : (0 : ℝ) ≤ L.lo := by exact_mod_cast hlo
  have hl' : (L.lo : ℝ) ^ 3 * d.hi ≤ 2 ^ 256 := by exact_mod_cast hl
  have hu' : (2 : ℝ) ^ 256 ≤ (L.hi : ℝ) ^ 3 * d.lo := by exact_mod_cast hu
  have key (a b : ℝ) : (a / 2 ^ 64) ^ 3 * (b / 2 ^ 64) = a ^ 3 * b / 2 ^ 256 := by ring
  constructor
  · apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) ypos.le
    have h1 : ((L.lo : ℝ) / 2 ^ 64) ^ 3 * x ≤ 1 := by
      have : ((L.lo : ℝ) / 2 ^ 64) ^ 3 * x ≤ ((L.lo : ℝ) / 2 ^ 64) ^ 3 * ((d.hi : ℝ) / 2 ^ 64) :=
        mul_le_mul_of_nonneg_left hx.2 (by positivity)
      refine this.trans ?_
      rw [key, div_le_one (by positivity)]
      exact hl'
    nlinarith
  · have hhi : (0 : ℝ) ≤ L.hi := by
      by_contra hneg
      push Not at hneg
      have hdlo : (0 : ℝ) < d.lo := by exact_mod_cast hdl
      have : (L.hi : ℝ) ^ 3 < 0 := by
        have h3 : (L.hi : ℝ) ^ 3 = -((-(L.hi : ℝ)) ^ 3) := by ring
        rw [h3]
        have : 0 < (-(L.hi : ℝ)) ^ 3 := pow_pos (by linarith) 3
        linarith
      nlinarith
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
    have h1 : 1 ≤ ((L.hi : ℝ) / 2 ^ 64) ^ 3 * x := by
      have : ((L.hi : ℝ) / 2 ^ 64) ^ 3 * ((d.lo : ℝ) / 2 ^ 64) ≤ ((L.hi : ℝ) / 2 ^ 64) ^ 3 * x :=
        mul_le_mul_of_nonneg_left hx.1 (by positivity)
      refine le_trans ?_ this
      rw [key, one_le_div (by positivity)]
      exact hu'
    nlinarith

/-- An enclosure of `9 ∂²G/∂s_i²` on the box. -/
def F2Z (c1 c2 γ : ZI) (P D : Matrix (Fin 3) (Fin 3) ℤ) (bd : ZBoxData) (i : Fin 5) : ZI :=
  let ρ := (d1Z i bd.A).mul bd.dinv
  let σ := (d2Z i bd.J).mul bd.dinv
  let A1 := c1.qmul (dirEZ i P) 98
  let B1 := (c2.mul (dotZ (WmatZ i D) 98 bd.J)).add ((γ.smul 2).mul (d1Z i bd.J))
  let B2 := (c2.qmul (2 * adjEZ i D) 98).add (γ.smul (2 * frobEZ i))
  let ρ2 := ρ.sq
  let t1 := (ρ2.smul 4).sub (σ.smul 3)
  let t2 := (ρ2.smul 10).sub (σ.smul 6)
  let in1 := (t1.mul bd.AI).sub ((ρ.mul A1).smul 6)
  let in2 := ((t2.mul bd.BI).sub ((ρ.mul B1).smul 12)).add (B2.smul 9)
  (bd.lam.mul in1).add (bd.lam.sq.mul in2)

theorem F2_nine (ref : Reference) (g : Aggregate) (γ : ℝ) (i : Fin 5) (q : Fin 5 → ℝ) (hd : 0 < dS q) :
    9 * F2 ref g γ i q =
      lamS q * ((4 * ((d1P i q * (dS q)⁻¹) * (d1P i q * (dS q)⁻¹)) - 3 * (d2P i q * (dS q)⁻¹)) *
          AP ref g γ q - 6 * ((d1P i q * (dS q)⁻¹) * A1P ref g i)) +
        (lamS q * lamS q) * ((10 * ((d1P i q * (dS q)⁻¹) * (d1P i q * (dS q)⁻¹)) -
          6 * (d2P i q * (dS q)⁻¹)) * BP ref g γ q - 12 * ((d1P i q * (dS q)⁻¹) * B1P ref g γ i q) +
          9 * B2P ref g γ i) := by
  rw [F2_formula ref g γ i q hd]
  ring

theorem F2Z_mem (ref : Reference) (z : ZAgg) (e2 : Bool) (zb : ZBox)
    (lamok : lamOKZ (zBoxData (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb).d
      (zBoxData (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb).lam = true)
    (i : Fin 5) (q : Fin 5 → ℝ) (hq : zb.Mem q) :
    0 < dS q ∧ (F2Z (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z)
      (zBoxData (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb) i).Mem
      (9 * F2 ref z.toAgg (modeGamma e2 : ℝ) i q) := by
  set bd := zBoxData (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb with hbd
  have hJ : ZM.Mem bd.J (sJ q) := boxJZ_mem zb q hq
  have hA : ZM.Mem bd.A (adj3 (sJ q)) := adjZ_mem hJ
  have hdet : bd.d.Mem (det3 (sJ q)) := detZ_mem hJ hA
  obtain ⟨dpos, hlam0⟩ := lamZ_mem _ _ lamok (dS q) hdet
  have hlam : bd.lam.Mem (lamS q) := hlam0
  have dlo : 0 < bd.d.lo := (of_decide_eq_true lamok).1
  refine ⟨dpos, ?_⟩
  have hdinv : bd.dinv.Mem (dS q)⁻¹ := ZI.mem_inv dlo hdet
  obtain ⟨c1m, c2m⟩ := cZ_mem ref
  have gm := gammaZ_mem e2
  have hP := framePZ_cast ref z
  have hD := frameDZ_cast ref z
  have hd1 : (d1Z i bd.A).Mem (d1P i q) := d1Z_mem i hA
  have hd2 : (d2Z i bd.J).Mem (d2P i q) := d2Z_mem i hJ
  have hρ := ZI.mem_mul hd1 hdinv
  have hσ := ZI.mem_mul hd2 hdinv
  have hAI : bd.AI.Mem (AP ref z.toAgg (modeGamma e2) q) :=
    ZI.mem_congr (ZI.mem_sub (ZI.mem_mul c1m (dotZ_mem _ _ hJ)) (ZI.mem_smul 6 gm))
      (by unfold AP; rw [hP]; push_cast; ring)
  have hBI : bd.BI.Mem (BP ref z.toAgg (modeGamma e2) q) :=
    ZI.mem_congr (ZI.mem_add (ZI.mem_mul c2m (dotZ_mem _ _ hA)) (ZI.mem_mul gm (dotSqZ_mem hJ)))
      (by unfold BP; rw [hD])
  have hA1 : ((c1Z ref).qmul (dirEZ i (framePZ ref z)) 98).Mem (A1P ref z.toAgg i) :=
    ZI.mem_congr (ZI.mem_qmul _ _ c1m) (by unfold A1P; rw [hP, dirEZ_eq]; ring)
  have hB1 : (((c2Z ref).mul (dotZ (WmatZ i (frameDZ ref z)) 98 bd.J)).add
      (((gammaZ e2).smul 2).mul (d1Z i bd.J))).Mem (B1P ref z.toAgg (modeGamma e2) i q) :=
    ZI.mem_congr (ZI.mem_add (ZI.mem_mul c2m (dotZ_mem _ _ hJ))
      (ZI.mem_mul (ZI.mem_smul 2 gm) (d1Z_mem i hJ)))
      (by unfold B1P; rw [hD, WmatZ_eq, dotE_trm]; push_cast; ring)
  have hB2 : (((c2Z ref).qmul (2 * adjEZ i (frameDZ ref z)) 98).add
      ((gammaZ e2).smul (2 * frobEZ i))).Mem (B2P ref z.toAgg (modeGamma e2) i) :=
    ZI.mem_congr (ZI.mem_add (ZI.mem_qmul _ _ c2m) (ZI.mem_smul _ gm))
      (by unfold B2P; rw [hD, adjEZ_eq, frobEZ_eq]; push_cast; ring)
  have ht1 := ZI.mem_sub (ZI.mem_smul 4 (ZI.mem_sq hρ)) (ZI.mem_smul 3 hσ)
  have ht2 := ZI.mem_sub (ZI.mem_smul 10 (ZI.mem_sq hρ)) (ZI.mem_smul 6 hσ)
  have hin1 := ZI.mem_sub (ZI.mem_mul ht1 hAI) (ZI.mem_smul 6 (ZI.mem_mul hρ hA1))
  have hin2 := ZI.mem_add (ZI.mem_sub (ZI.mem_mul ht2 hBI) (ZI.mem_smul 12 (ZI.mem_mul hρ hB1)))
    (ZI.mem_smul 9 hB2)
  rw [F2_nine ref z.toAgg (modeGamma e2) i q dpos]
  unfold F2Z
  simp only
  refine ZI.mem_congr (ZI.mem_add (ZI.mem_mul hlam hin1) (ZI.mem_mul (ZI.mem_sq hlam) hin2)) ?_
  push_cast
  ring


/-! ## Exact corners -/

def cornerZ (zb : ZBox) (c : Fin 5 → Bool) : Fin 5 → ℤ :=
  ![if c 0 then zb.hi 0 else zb.lo 0, if c 1 then zb.hi 1 else zb.lo 1, if c 2 then zb.hi 2 else zb.lo 2,
    if c 3 then zb.hi 3 else zb.lo 3, if c 4 then zb.hi 4 else zb.lo 4]

def sJZ (s : Fin 5 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![pw 64 + s 0 + s 1, s 2, s 3; s 2, pw 64 + s 1 - s 0, s 4; s 3, s 4, pw 64 - 2 * s 1]

theorem castZ_sJZ (s : Fin 5 → ℤ) : castZ (sJZ s) 64 = sJ (fun i => (s i : ℝ) / 2 ^ 64) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [castZ, sJZ, sJ, pw_cast] <;> field_simp

/-- `Σ_ij A_ij X_ij` for integer matrices. -/
def dotZQ (A X : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  A 0 0 * X 0 0 + A 0 1 * X 0 1 + A 0 2 * X 0 2 + (A 1 0 * X 1 0 + A 1 1 * X 1 1 + A 1 2 * X 1 2) +
    (A 2 0 * X 2 0 + A 2 1 * X 2 1 + A 2 2 * X 2 2)

theorem cast_dotZQ (A X : Matrix (Fin 3) (Fin 3) ℤ) (e f : ℕ) :
    (dotZQ A X : ℝ) / 2 ^ (e + f) = dot3 (castZ A e) (castZ X f) := by
  simp only [dotZQ, dot3, castZ, Fin.sum_univ_three, pow_add]
  push_cast
  ring

theorem castZ_adj3 (X : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) : castZ (adj3 X) (e + e) = adj3 (castZ X e) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [castZ, adj3, pow_add] <;> ring

theorem castZ_det (X : Matrix (Fin 3) (Fin 3) ℤ) (e : ℕ) :
    ((det3 X : ℤ) : ℝ) / 2 ^ (e + e + e) = det3 (castZ X e) := by
  simp [det3, adj3, castZ, pow_add]
  ring

/-- `x c t ≤` the matching product of ends, for `0 ≤ l ≤ x ≤ L`, `0 ≤ k ≤ c ≤ K`, `t ≤ a`. -/
theorem prod_upper {x c t l L k K a : ℝ} (hl : 0 ≤ l) (hx : l ≤ x ∧ x ≤ L) (hk : 0 ≤ k)
    (hc : k ≤ c ∧ c ≤ K) (ht : t ≤ a) :
    x * c * t ≤ (if 0 ≤ a then L * K * a else l * k * a) := by
  have x0 : 0 ≤ x := hl.trans hx.1
  have c0 : 0 ≤ c := hk.trans hc.1
  have xc : 0 ≤ x * c := mul_nonneg x0 c0
  have step : x * c * t ≤ x * c * a := mul_le_mul_of_nonneg_left ht xc
  split_ifs with ha
  · refine step.trans (mul_le_mul_of_nonneg_right ?_ ha)
    exact mul_le_mul hx.2 hc.2 c0 (x0.trans hx.2)
  · refine step.trans (mul_le_mul_of_nonpos_right ?_ (le_of_lt (not_le.mp ha)))
    exact mul_le_mul hx.1 hc.1 hk x0

/-- `L K a` or `l k a`, by the sign of `a`. -/
def prodUpZ (a L K l k : ℤ) : ℤ := if 0 ≤ a then L * K * a else l * k * a

theorem prodUpZ_cast (a L K l k : ℤ) (e : ℕ) :
    (if 0 ≤ (a : ℝ) / 2 ^ e then (L : ℝ) / 2 ^ e * ((K : ℝ) / 2 ^ e) * ((a : ℝ) / 2 ^ e)
      else (l : ℝ) / 2 ^ e * ((k : ℝ) / 2 ^ e) * ((a : ℝ) / 2 ^ e)) =
      (prodUpZ a L K l k : ℝ) / 2 ^ (e + e + e) := by
  have S : (0 : ℝ) < 2 ^ e := by positivity
  have e1 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ e ↔ 0 ≤ a := by
    rw [div_nonneg_iff]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact_mod_cast h
      · exact absurd h (not_le.mpr S)
    · intro h
      exact Or.inl ⟨by exact_mod_cast h, S.le⟩
  unfold prodUpZ
  by_cases ha : 0 ≤ a
  · rw [ite_eq_left (e1.mpr ha), ite_eq_left ha, pow_add, pow_add]
    push_cast
    field_simp
  · rw [ite_eq_right (mt e1.mp ha), ite_eq_right ha, pow_add, pow_add]
    push_cast
    field_simp

/-- An upper bound of `G` at the corner `c`, at scale `2^64`. -/
def cornerUpperZ (c1 c2 : ZI) (γhi : ℤ) (P D : Matrix (Fin 3) (Fin 3) ℤ) (zb : ZBox) (c : Fin 5 → Bool) :
    Option ℤ :=
  let J := sJZ (cornerZ zb c)
  let A := adj3 J
  let d := J 0 0 * A 0 0 + J 0 1 * A 1 0 + J 0 2 * A 2 0
  let m : ℤ := (icbrt ((2 ^ 384 : ℕ) / d.toNat) : ℤ)
  if decide (0 < d ∧ m ^ 3 * d ≤ pw 384 ∧ pw 384 ≤ (m + 1) ^ 3 * d ∧ 0 ≤ γhi ∧ 0 ≤ c1.lo ∧ 0 ≤ c2.lo) then
    let α := cdivZ (dotZQ P J) 98
    let β := cdivZ (dotZQ D A) 162
    let f := cdivZ (dotZQ J J) 64
    let T1 := cdivZ (prodUpZ α (m + 1) c1.hi m c1.lo) 128
    let T2 := cdivZ (prodUpZ β ((m + 1) ^ 2) c2.hi (m ^ 2) c2.lo) 192
    let Q := cdivZ ((m + 1) ^ 2 * f) 128 - 6 * m + 3 * pw 64
    some (T1 + T2 + cdivZ (γhi * max Q 0) 64)
  else none

set_option exponentiation.threshold 400 in
theorem cornerUpperZ_sound (ref : Reference) (z : ZAgg) (e2 : Bool) (zb : ZBox) (c : Fin 5 → Bool) (u : ℤ)
    (h : cornerUpperZ (c1Z ref) (c2Z ref) (gammaZ e2).hi (framePZ ref z) (frameDZ ref z) zb c = some u) :
    Gs ref z.toAgg (modeGamma e2 : ℝ) (fun i => (cornerZ zb c i : ℝ) / 2 ^ 64) ≤ (u : ℝ) / 2 ^ 64 := by
  unfold cornerUpperZ at h
  simp only at h
  split_ifs at h with hok
  obtain ⟨hd0, hm1, hm2, hγ0, hc10, hc20⟩ := of_decide_eq_true hok
  rw [pw_eq] at hm1 hm2
  have hu := Option.some.inj h
  set J := sJZ (cornerZ zb c) with hJdef
  set q : Fin 5 → ℝ := fun i => (cornerZ zb c i : ℝ) / 2 ^ 64 with hq
  set d := J 0 0 * adj3 J 0 0 + J 0 1 * adj3 J 1 0 + J 0 2 * adj3 J 2 0 with hd
  set m : ℤ := (icbrt ((2 ^ 384 : ℕ) / d.toNat) : ℤ) with hm
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  have hsJ : sJ q = castZ J 64 := (castZ_sJZ _).symm
  have hdet3 : det3 J = d := rfl
  have hdS : dS q = (d : ℝ) / 2 ^ 192 := by
    unfold dS
    rw [hsJ, ← castZ_det, hdet3]
  have m0 : (0 : ℤ) ≤ m := by rw [hm]; exact Int.natCast_nonneg _
  have dpos : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdSpos : 0 < dS q := by rw [hdS]; positivity
  -- the bracket of `λ`
  set lam := lamS q with hlam
  have lpos : 0 < lam := lamS_pos q hdSpos
  have cube : lam ^ 3 * dS q = 1 := cube_lamS q hdSpos
  have hm1' : (m : ℝ) ^ 3 * d ≤ 2 ^ 384 := by exact_mod_cast hm1
  have hm2' : (2 : ℝ) ^ 384 ≤ ((m : ℝ) + 1) ^ 3 * d := by exact_mod_cast hm2
  have keyc (a : ℝ) : (a / 2 ^ 64) ^ 3 * ((d : ℝ) / 2 ^ 192) = a ^ 3 * d / 2 ^ 384 := by
    rw [div_pow, div_mul_div_comm]
    congr 1
    rw [← pow_mul, ← pow_add]
  have llo : (m : ℝ) / 2 ^ 64 ≤ lam := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) lpos.le
    have : ((m : ℝ) / 2 ^ 64) ^ 3 * dS q ≤ lam ^ 3 * dS q := by
      rw [cube, hdS, keyc, div_le_one (by positivity)]
      exact hm1'
    exact le_of_mul_le_mul_right this hdSpos
  have lhi : lam ≤ ((m : ℝ) + 1) / 2 ^ 64 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
    have : lam ^ 3 * dS q ≤ (((m : ℝ) + 1) / 2 ^ 64) ^ 3 * dS q := by
      rw [cube, hdS, keyc, one_le_div (by positivity)]
      exact hm2'
    exact le_of_mul_le_mul_right this hdSpos
  have m0' : (0 : ℝ) ≤ (m : ℝ) / 2 ^ 64 := by
    have : (0 : ℝ) ≤ m := by exact_mod_cast m0
    positivity
  -- the three contractions
  obtain ⟨c1m, c2m⟩ := cZ_mem ref
  have gm := gammaZ_mem e2
  have hP := framePZ_cast ref z
  have hD := frameDZ_cast ref z
  have hα : dot3 (castM (Pframe ref z.toAgg)) (sJ q) ≤
      ((cdivZ (dotZQ (framePZ ref z) J) 98 : ℤ) : ℝ) / 2 ^ 64 := by
    rw [hP, hsJ, ← cast_dotZQ]
    have := div_le_div_of_nonneg_right (le_cdivZ (dotZQ (framePZ ref z) J) 98) S.le
    calc (dotZQ (framePZ ref z) J : ℝ) / 2 ^ (98 + 64) = (dotZQ (framePZ ref z) J : ℝ) / 2 ^ 98 / 2 ^ 64 := by
          rw [pow_add, div_div]
      _ ≤ _ := this
  have hβ : dot3 (castM (Dframe ref z.toAgg)) (adj3 (sJ q)) ≤
      ((cdivZ (dotZQ (frameDZ ref z) (adj3 J)) 162 : ℤ) : ℝ) / 2 ^ 64 := by
    rw [hD, hsJ, ← castZ_adj3, ← cast_dotZQ]
    have := div_le_div_of_nonneg_right (le_cdivZ (dotZQ (frameDZ ref z) (adj3 J)) 162) S.le
    calc (dotZQ (frameDZ ref z) (adj3 J) : ℝ) / 2 ^ (98 + (64 + 64)) =
          (dotZQ (frameDZ ref z) (adj3 J) : ℝ) / 2 ^ 162 / 2 ^ 64 := by
          rw [div_div]
          norm_num
      _ ≤ _ := this
  have hf : dot3 (sJ q) (sJ q) ≤ ((cdivZ (dotZQ J J) 64 : ℤ) : ℝ) / 2 ^ 64 := by
    rw [hsJ, ← cast_dotZQ]
    have := div_le_div_of_nonneg_right (le_cdivZ (dotZQ J J) 64) S.le
    calc (dotZQ J J : ℝ) / 2 ^ (64 + 64) = (dotZQ J J : ℝ) / 2 ^ 64 / 2 ^ 64 := by rw [pow_add, div_div]
      _ ≤ _ := this
  have hf0 : 0 ≤ dot3 (sJ q) (sJ q) := by
    unfold dot3
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  -- term bounds
  set α := cdivZ (dotZQ (framePZ ref z) J) 98
  set β := cdivZ (dotZQ (frameDZ ref z) (adj3 J)) 162
  set f := cdivZ (dotZQ J J) 64
  have c1lo : (0 : ℝ) ≤ ((c1Z ref).lo : ℝ) / 2 ^ 64 := by
    have : (0 : ℝ) ≤ (c1Z ref).lo := by exact_mod_cast hc10
    positivity
  have c2lo : (0 : ℝ) ≤ ((c2Z ref).lo : ℝ) / 2 ^ 64 := by
    have : (0 : ℝ) ≤ (c2Z ref).lo := by exact_mod_cast hc20
    positivity
  have T1 : lam * c1R ref * dot3 (castM (Pframe ref z.toAgg)) (sJ q) ≤
      ((cdivZ (prodUpZ α (m + 1) (c1Z ref).hi m (c1Z ref).lo) 128 : ℤ) : ℝ) / 2 ^ 64 := by
    have p := prod_upper m0' ⟨llo, lhi⟩ c1lo c1m hα
    have e : ((m : ℝ) + 1) / 2 ^ 64 = ((m + 1 : ℤ) : ℝ) / 2 ^ 64 := by push_cast; ring
    rw [e, prodUpZ_cast] at p
    refine p.trans ?_
    have := div_le_div_of_nonneg_right (le_cdivZ (prodUpZ α (m + 1) (c1Z ref).hi m (c1Z ref).lo) 128) S.le
    refine le_trans (le_of_eq ?_) this
    rw [div_div]
    norm_num
  have l2 : ((m : ℝ) / 2 ^ 64) ^ 2 ≤ lam ^ 2 ∧ lam ^ 2 ≤ (((m : ℝ) + 1) / 2 ^ 64) ^ 2 :=
    ⟨pow_le_pow_left₀ m0' llo 2, pow_le_pow_left₀ lpos.le lhi 2⟩
  have T2 : lam ^ 2 * c2R ref * dot3 (castM (Dframe ref z.toAgg)) (adj3 (sJ q)) ≤
      ((cdivZ (prodUpZ β ((m + 1) ^ 2) (c2Z ref).hi (m ^ 2) (c2Z ref).lo) 192 : ℤ) : ℝ) / 2 ^ 64 := by
    have l2' : (((m ^ 2 : ℤ) : ℝ) / 2 ^ 128) ≤ lam ^ 2 ∧ lam ^ 2 ≤ ((((m + 1) ^ 2 : ℤ) : ℝ) / 2 ^ 128) := by
      constructor
      · refine le_trans (le_of_eq ?_) l2.1
        push_cast
        ring
      · refine l2.2.trans (le_of_eq ?_)
        push_cast
        ring
    have m20 : (0 : ℝ) ≤ ((m ^ 2 : ℤ) : ℝ) / 2 ^ 128 := by positivity
    have c2m' : (((c2Z ref).lo : ℝ) * 2 ^ 64 / 2 ^ 128) ≤ c2R ref ∧
        c2R ref ≤ (((c2Z ref).hi : ℝ) * 2 ^ 64 / 2 ^ 128) := by
      constructor
      · refine le_trans (le_of_eq ?_) c2m.1
        field_simp
      · refine c2m.2.trans (le_of_eq ?_)
        field_simp
    have β' : dot3 (castM (Dframe ref z.toAgg)) (adj3 (sJ q)) ≤ ((β * 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 := by
      refine hβ.trans (le_of_eq ?_)
      push_cast
      field_simp
      ring
    have c2lo' : (0 : ℝ) ≤ ((c2Z ref).lo : ℝ) * 2 ^ 64 / 2 ^ 128 := by
      have : (0 : ℝ) ≤ (c2Z ref).lo := by exact_mod_cast hc20
      positivity
    have p := prod_upper m20 l2' c2lo' c2m' β'
    have e1 : ((c2Z ref).lo : ℝ) * 2 ^ 64 / 2 ^ 128 = (((c2Z ref).lo * 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 := by
      push_cast; ring
    have e2 : ((c2Z ref).hi : ℝ) * 2 ^ 64 / 2 ^ 128 = (((c2Z ref).hi * 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 := by
      push_cast; ring
    rw [e1, e2, prodUpZ_cast] at p
    refine p.trans ?_
    have := div_le_div_of_nonneg_right
      (le_cdivZ (prodUpZ β ((m + 1) ^ 2) (c2Z ref).hi (m ^ 2) (c2Z ref).lo) 192) S.le
    refine le_trans (le_of_eq ?_) this
    have hsign : prodUpZ (β * 2 ^ 64) ((m + 1) ^ 2) ((c2Z ref).hi * 2 ^ 64) (m ^ 2) ((c2Z ref).lo * 2 ^ 64) =
        prodUpZ β ((m + 1) ^ 2) (c2Z ref).hi (m ^ 2) (c2Z ref).lo * 2 ^ 128 := by
      unfold prodUpZ
      have : (0 ≤ β * 2 ^ 64) ↔ 0 ≤ β := by
        constructor
        · intro h
          by_contra hn
          have : β * 2 ^ 64 < 0 := mul_neg_of_neg_of_pos (not_le.mp hn) (by positivity)
          linarith
        · intro h
          exact mul_nonneg h (by positivity)
      by_cases hb : 0 ≤ β
      · rw [ite_eq_left (this.mpr hb), ite_eq_left hb]
        ring
      · rw [ite_eq_right (mt this.mp hb), ite_eq_right hb]
        ring
    rw [hsign]
    push_cast
    field_simp
    ring
  -- the γ term
  set Qz := cdivZ ((m + 1) ^ 2 * f) 128 - 6 * m + 3 * pw 64
  have hQ0 : 0 ≤ lam ^ 2 * dot3 (sJ q) (sJ q) - 6 * lam + 3 := by
    have := frob_metric q
    rw [← this]
    unfold frobSq
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hQ : lam ^ 2 * dot3 (sJ q) (sJ q) - 6 * lam + 3 ≤ (Qz : ℝ) / 2 ^ 64 := by
    have f0 : (0 : ℝ) ≤ (f : ℝ) / 2 ^ 64 := hf0.trans hf
    have a1 : lam ^ 2 * dot3 (sJ q) (sJ q) ≤ (((m : ℝ) + 1) / 2 ^ 64) ^ 2 * ((f : ℝ) / 2 ^ 64) :=
      mul_le_mul l2.2 hf hf0 (by positivity)
    have a2 : (((m : ℝ) + 1) / 2 ^ 64) ^ 2 * ((f : ℝ) / 2 ^ 64) ≤
        ((cdivZ ((m + 1) ^ 2 * f) 128 : ℤ) : ℝ) / 2 ^ 64 := by
      refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (le_cdivZ _ 128) S.le)
      push_cast
      ring
    have a3 : -6 * lam ≤ -6 * ((m : ℝ) / 2 ^ 64) := by linarith
    have e : ((Qz : ℤ) : ℝ) / 2 ^ 64 =
        ((cdivZ ((m + 1) ^ 2 * f) 128 : ℤ) : ℝ) / 2 ^ 64 - 6 * ((m : ℝ) / 2 ^ 64) + 3 := by
      simp only [Qz]
      push_cast
      rw [pw_cast]
      ring
    rw [e]
    linarith
  have γ0 : (0 : ℝ) ≤ (modeGamma e2 : ℝ) := by
    cases e2 <;> simp [modeGamma]
    norm_num [gapFactorUpper, kappaUpper, scaleHi, Constants.gapBracket, Constants.fccBracket, Constants.bccBracket,
      Constants.Interval.sub]
  have T3 : (modeGamma e2 : ℝ) * (lam ^ 2 * dot3 (sJ q) (sJ q) - 6 * lam + 3) ≤
      ((cdivZ ((gammaZ e2).hi * max Qz 0) 64 : ℤ) : ℝ) / 2 ^ 64 := by
    have g1 : (modeGamma e2 : ℝ) * (lam ^ 2 * dot3 (sJ q) (sJ q) - 6 * lam + 3) ≤
        (modeGamma e2 : ℝ) * ((max Qz 0 : ℤ) : ℝ) / 2 ^ 64 := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ γ0
      refine hQ.trans (div_le_div_of_nonneg_right ?_ S.le)
      exact_mod_cast le_max_left _ _
    have g2 : (modeGamma e2 : ℝ) * ((max Qz 0 : ℤ) : ℝ) / 2 ^ 64 ≤
        (((gammaZ e2).hi : ℝ) / 2 ^ 64) * ((max Qz 0 : ℤ) : ℝ) / 2 ^ 64 := by
      apply div_le_div_of_nonneg_right _ S.le
      exact mul_le_mul_of_nonneg_right gm.2 (by exact_mod_cast le_max_right _ _)
    refine g1.trans (g2.trans (le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (le_cdivZ _ 64) S.le)))
    push_cast
    ring
  -- assemble
  rw [Gs_split, ← hu]
  push_cast
  have split : lamS q * AP ref z.toAgg (modeGamma e2) q + lamS q ^ 2 * BP ref z.toAgg (modeGamma e2) q +
      3 * (modeGamma e2 : ℝ) =
      lam * c1R ref * dot3 (castM (Pframe ref z.toAgg)) (sJ q) +
        lam ^ 2 * c2R ref * dot3 (castM (Dframe ref z.toAgg)) (adj3 (sJ q)) +
        (modeGamma e2 : ℝ) * (lam ^ 2 * dot3 (sJ q) (sJ q) - 6 * lam + 3) := by
    unfold AP BP
    ring
  rw [split]
  have := add_le_add (add_le_add T1 T2) T3
  refine this.trans (le_of_eq ?_)
  rw [add_div, add_div]

/-! ## The correction and the leaf check -/

def corrTermZ (F : ZI) (w : ℤ) : ℤ := cdivN (max 0 (-F.lo) * (w * w)) (72 * pw 128)

def corrZ (c1 c2 γ : ZI) (P D : Matrix (Fin 3) (Fin 3) ℤ) (zb : ZBox) (bd : ZBoxData) : ℤ :=
  corrTermZ (F2Z c1 c2 γ P D bd 0) (zb.hi 0 - zb.lo 0) + corrTermZ (F2Z c1 c2 γ P D bd 1) (zb.hi 1 - zb.lo 1) +
    corrTermZ (F2Z c1 c2 γ P D bd 2) (zb.hi 2 - zb.lo 2) + corrTermZ (F2Z c1 c2 γ P D bd 3) (zb.hi 3 - zb.lo 3) +
    corrTermZ (F2Z c1 c2 γ P D bd 4) (zb.hi 4 - zb.lo 4)

/-- Balls containing `λ J` on the box (the spectral guard). -/
def cBallsZ (bd : ZBoxData) : MetricBalls := fun i j =>
  let c := bd.lam.mul (bd.J i j)
  ballOf ((c.lo : ℚ) / pwQ 64) ((c.hi : ℚ) / pwQ 64)

/-- The strain leaf check on integers. -/
def zLeafCheck (ref : Reference) (e2 : Bool) (z : ZAgg) (b : Rectangle) : Bool :=
  let zb := zBox ref b
  let P := framePZ ref z
  let D := frameDZ ref z
  let γI := gammaZ e2
  let bd := zBoxData (c1Z ref) (c2Z ref) γI P D zb
  let corr := corrZ (c1Z ref) (c2Z ref) γI P D zb bd
  (lamOKZ bd.d bd.lam &&
      (!e2 || (decide (ref = .bcc) && spectralCheck (cBallsZ bd) (automaticUpperPad (cBallsZ bd))))) &&
    allCorners fun c => match cornerUpperZ (c1Z ref) (c2Z ref) γI.hi P D zb c with
      | some u => decide ((targetZ e2 + u + corr) * pw 32 < z.a)
      | none => false

/-- The `s`-box as a rational rectangle. -/
def zbRect (zb : ZBox) : Rectangle := ⟨fun i => (zb.lo i : ℚ) / 2 ^ 64, fun i => (zb.hi i : ℚ) / 2 ^ 64⟩

theorem zbRect_mem {zb : ZBox} {q : Fin 5 → ℝ} : (zbRect zb).Mem q ↔ zb.Mem q := by
  unfold Box.Mem ZBox.Mem zbRect
  simp only
  push_cast
  rfl

theorem zbRect_corner (zb : ZBox) (c : Fin 5 → Bool) :
    TangentE1.corner (zbRect zb) c = fun i => (cornerZ zb c i : ℝ) / 2 ^ 64 := by
  funext i
  fin_cases i <;> simp [TangentE1.corner, zbRect, cornerZ] <;> split_ifs <;> rfl

theorem zLeafCheck_sound (ref : Reference) (e2 : Bool) (z : ZAgg) (hz : Certified z.toAgg)
    (b : Rectangle) (ok : zLeafCheck ref e2 z b = true) (w : Point) (hw : b.Mem w) :
    strainSharp ref w := by
  unfold zLeafCheck at ok
  simp only at ok
  obtain ⟨⟨hlam, hmode⟩, hcorners⟩ := Bool.and_eq_true_iff.mp ok |>.imp_left Bool.and_eq_true_iff.mp
  set zb := zBox ref b with hzb
  set γ := modeGamma e2 with hγ
  set p := sOf ref w with hpdef
  set bd := zBoxData (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb with hbd
  have S : (0 : ℝ) < 2 ^ 64 := by positivity
  have hpz : zb.Mem p := zBox_mem ref b w hw
  have hp : (zbRect zb).Mem p := zbRect_mem.mpr hpz
  let F := fun i => F2Z (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) bd i
  let M : Fin 5 → ℝ := fun i => ((max 0 (-(F i).lo) : ℤ) : ℝ) / (9 * 2 ^ 64)
  have hM (i : Fin 5) : 0 ≤ M i := by
    simp only [M]
    have : (0 : ℝ) ≤ ((max 0 (-(F i).lo) : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    positivity
  obtain ⟨c, hc⟩ := box_bound (zbRect zb) (Gs ref z.toAgg γ) (F1 ref z.toAgg γ) (F2 ref z.toAgg γ) M hM
    (fun i q hq => (lineDerivs ref z.toAgg γ i q
      (F2Z_mem ref z e2 zb hlam i q (zbRect_mem.mp hq)).1).1)
    (fun i q hq => (lineDerivs ref z.toAgg γ i q
      (F2Z_mem ref z e2 zb hlam i q (zbRect_mem.mp hq)).1).2)
    (fun i q hq => by
      have h := (F2Z_mem ref z e2 zb hlam i q (zbRect_mem.mp hq)).2.1
      have hmax : (-((max 0 (-(F i).lo) : ℤ) : ℝ)) ≤ ((F i).lo : ℝ) := by
        have := le_max_right (0 : ℤ) (-(F i).lo)
        have : (-(F i).lo : ℝ) ≤ ((max 0 (-(F i).lo) : ℤ) : ℝ) := by exact_mod_cast this
        linarith
      simp only [M]
      rw [neg_div', div_le_iff₀ (by positivity)]
      have : ((F i).lo : ℝ) / 2 ^ 64 ≤ 9 * F2 ref z.toAgg γ i q := h
      rw [div_le_iff₀ S] at this
      nlinarith)
    p hp
  have hcorner := allCorners_sound _ hcorners c
  cases hcu : cornerUpperZ (c1Z ref) (c2Z ref) (gammaZ e2).hi (framePZ ref z) (frameDZ ref z) zb c with
  | none => simp [hcu] at hcorner
  | some u =>
    simp only [hcu] at hcorner
    have ht : (targetZ e2 + u + corrZ (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb bd) *
        2 ^ 32 < z.a := by
      have := of_decide_eq_true hcorner
      rwa [pw_eq] at this
    have hG := cornerUpperZ_sound ref z e2 zb c u hcu
    rw [← zbRect_corner] at hG
    have hcorr : ∑ i, M i * (((zbRect zb).hi i : ℝ) - (zbRect zb).lo i) ^ 2 / 8 ≤
        ((corrZ (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb bd : ℤ) : ℝ) / 2 ^ 64 := by
      have term (i : Fin 5) : M i * (((zbRect zb).hi i : ℝ) - (zbRect zb).lo i) ^ 2 / 8 ≤
          ((corrTermZ (F i) (zb.hi i - zb.lo i) : ℤ) : ℝ) / 2 ^ 64 := by
        have hpos : (0 : ℤ) < 72 * pw 128 := by rw [pw_eq]; norm_num
        have := div_le_div_of_nonneg_right (le_cdivN (max 0 (-(F i).lo) * ((zb.hi i - zb.lo i) * (zb.hi i - zb.lo i)))
          (72 * pw 128) hpos) S.le
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
    have htR : ((targetZ e2 + u + corrZ (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb bd : ℤ)
        : ℝ) * 2 ^ 32 < (z.a : ℝ) := by exact_mod_cast ht
    have hga : (z.toAgg.a : ℝ) = (z.a : ℝ) / 2 ^ 96 := by simp [ZAgg.toAgg]
    have tg := targetZ_ge e2
    have bound : (modeTarget e2 : ℝ) < z.toAgg.a - Gs ref z.toAgg γ p := by
      rw [hga]
      have e96 : (z.a : ℝ) / 2 ^ 96 = (z.a : ℝ) / 2 ^ 32 / 2 ^ 64 := by rw [div_div]; norm_num
      have h32 : ((targetZ e2 + u + corrZ (c1Z ref) (c2Z ref) (gammaZ e2) (framePZ ref z) (frameDZ ref z) zb bd : ℤ)
          : ℝ) < (z.a : ℝ) / 2 ^ 32 := by
        rw [lt_div_iff₀ (by positivity)]
        exact htR
      have h64 := div_lt_div_of_pos_right h32 S
      rw [e96]
      push_cast at h64
      rw [add_div, add_div] at h64
      linarith
    intro A hA hGram
    obtain ⟨dpos, hlamp⟩ := (by
      have hJ := boxJZ_mem zb p hpz
      have hdet := detZ_mem hJ (adjZ_mem hJ)
      exact lamZ_mem _ _ hlam (dS p) hdet : 0 < dS p ∧ bd.lam.Mem (dS p ^ (-(1/3 : ℝ))))
    have low := strain_lower ref z.toAgg hz γ w dpos A hA hGram
    rw [← hpdef] at low
    have hvol : volumeOf (A * cubicBasis ref) = 1 := by
      unfold volumeOf
      rw [Matrix.det_mul, hA, one_mul]
      exact cubicBasis_unitVolume ref
    cases e2 with
    | false =>
      have hγ0 : (γ : ℝ) * frobSq (gram A - 1) = 0 := by simp [hγ, modeGamma]
      have ht0 : (modeTarget false : ℝ) = HfccUpper := by simp [modeTarget]
      rw [ht0] at bound
      exact unitVolume_above_fcc_of_series (A * cubicBasis ref) hvol (by linarith)
    | true =>
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hmode
      obtain ⟨href, hspec⟩ := hmode
      have href' : ref = .bcc := of_decide_eq_true href
      subst href'
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
      apply strict_e2_from_same_point (A * cubicBasis .bcc) hdet ((kappaUpper : ℝ) * frobSq (gram A - 1)) upper
      have e : (γ : ℝ) * frobSq (gram A - 1) = gapFactorUpper * (kappaUpper * frobSq (gram A - 1)) := by
        rw [hγ1]
        ring
      linarith

end BccSharp.Coulomb.BravaisCover.StrainTangent
