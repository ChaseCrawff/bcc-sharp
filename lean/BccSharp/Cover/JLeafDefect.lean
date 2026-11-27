import BccSharp.Cover.JLeafCore

set_option autoImplicit false

/-! Registered upper bound for the actual capped defect in the small-cost
regime.

For a rational index-two BCC registration `(B, f₀)` with `N = B⁻¹`, a rational
proper rotation `U` and an integer wrap `n`, put `A = R N` and
`h = R (f - f₀ - n)` for the chart basis `R`. When
`regCost = 100‖A - U‖²_F + 200|h|² ≤ 1/2`, the fourteen star images
`A s + χ(s) h` are lifted neighbours, they are pairwise distinct, and every
other lifted vector has length at least `13/10`. The unmatched annular sum
therefore vanishes and the trial cost equals `regCost`, so the actual
`defect` is at most `regCost`.

`registrationCheck` is exact rational arithmetic on the proposal. It checks
`N B = B N = 1`, `Uᵀ U = 1`, `det U = 1`, that the columns of `2B` and the
vector `2 B f₀` are integral with one parity per vector (so `B ℤ³` and
`B (ℤ³ + f₀)` lie in the BCC point set), that `f₀ ∉ ℤ³`, and that every star
vector lies in `B ℤ³` or `B (ℤ³ + f₀)`, with eight odd labels whose star
vectors sum to zero. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp
open BccSharp.Coulomb.CompactCover.DirectRoute (offset)

/-! ### Euclidean length on `Vec` -/

/-- Euclidean length, `√(sq v)`. -/
def nrm (v : Vec) : ℝ := Real.sqrt (sq v)

theorem nrm_nonneg (v : Vec) : 0 ≤ nrm v := Real.sqrt_nonneg _

theorem nrm_sq (v : Vec) : nrm v ^ 2 = sq v := Real.sq_sqrt (sq_nonnegative v)

private theorem sq_three (v : Vec) : sq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [sq, Fin.sum_univ_three]

theorem dot_le_nrm (u v : Vec) : (∑ i, u i * v i) ≤ nrm u * nrm v := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) u v
  have h2 : (∑ i, u i * v i) ^ 2 ≤ (nrm u * nrm v) ^ 2 := by
    rw [mul_pow, nrm_sq, nrm_sq]
    simpa [sq] using cs
  have hn : 0 ≤ nrm u * nrm v := mul_nonneg (nrm_nonneg u) (nrm_nonneg v)
  by_contra hc
  push Not at hc
  nlinarith

theorem nrm_add_le (u v : Vec) : nrm (u + v) ≤ nrm u + nrm v := by
  have hsum : sq (u + v) = sq u + 2 * (∑ i, u i * v i) + sq v := by
    simp only [sq_three, Pi.add_apply, Fin.sum_univ_three]
    ring
  have d := dot_le_nrm u v
  rw [nrm, Real.sqrt_le_left (add_nonneg (nrm_nonneg u) (nrm_nonneg v)), hsum]
  nlinarith [nrm_sq u, nrm_sq v]

theorem nrm_neg (v : Vec) : nrm (-v) = nrm v := by
  unfold nrm
  congr 1
  simp [sq_three]

/-- Reverse triangle inequality. -/
theorem nrm_sub_le (u v : Vec) : nrm u - nrm v ≤ nrm (u + v) := by
  have h := nrm_add_le (u + v) (-v)
  rw [nrm_neg, show u + v + -v = u by abel] at h
  linarith

theorem frobSq_nonneg (M : Mat) : 0 ≤ frobSq M :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (M i j)))

theorem nrm_mulVec_le (M : Mat) (v : Vec) :
    nrm (M.mulVec v) ≤ Real.sqrt (frobSq M) * nrm v := by
  unfold nrm
  rw [← Real.sqrt_mul (frobSq_nonneg M)]
  exact Real.sqrt_le_sqrt (mulVec_sq_le_frob M v)

/-- Orthogonal matrices preserve `sq`. -/
theorem sq_orth (U : Mat) (hU : U.transpose * U = 1) (v : Vec) :
    sq (U.mulVec v) = sq v := by
  have e : ∀ i j : Fin 3, U 0 i * U 0 j + U 1 i * U 1 j + U 2 i * U 2 j =
      if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun hU i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_three] using h
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp only [Fin.isValue, ite_true, Fin.reduceEq, ite_false] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  simp only [sq_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  linear_combination (v 0 * v 0) * e00 + (v 0 * v 1) * e01 + (v 0 * v 2) * e02 +
    (v 1 * v 0) * e10 + (v 1 * v 1) * e11 + (v 1 * v 2) * e12 +
    (v 2 * v 0) * e20 + (v 2 * v 1) * e21 + (v 2 * v 2) * e22

/-- `|A e| ≥ (1 - ‖A - U‖_F) |e|` for orthogonal `U`. -/
theorem nrm_mulVec_lower (A U : Mat) (hU : U.transpose * U = 1) (v : Vec) :
    (1 - Real.sqrt (frobSq (A - U))) * nrm v ≤ nrm (A.mulVec v) := by
  have split : A.mulVec v = U.mulVec v + (A - U).mulVec v := by
    rw [Matrix.sub_mulVec]
    abel
  have hu : nrm (U.mulVec v) = nrm v := by unfold nrm; rw [sq_orth U hU v]
  have hr := nrm_sub_le (U.mulVec v) ((A - U).mulVec v)
  have hm := nrm_mulVec_le (A - U) v
  rw [← split, hu] at hr
  nlinarith

theorem nrm_mulVec_upper (A U : Mat) (hU : U.transpose * U = 1) (v : Vec) :
    nrm (A.mulVec v) ≤ (1 + Real.sqrt (frobSq (A - U))) * nrm v := by
  have split : A.mulVec v = U.mulVec v + (A - U).mulVec v := by
    rw [Matrix.sub_mulVec]
    abel
  have hu : nrm (U.mulVec v) = nrm v := by unfold nrm; rw [sq_orth U hU v]
  have ht := nrm_add_le (U.mulVec v) ((A - U).mulVec v)
  have hm := nrm_mulVec_le (A - U) v
  rw [← split, hu] at ht
  nlinarith

/-! ### Star identities -/

theorem star_moment (M : Mat) : ∑ j, sq (M.mulVec (star j)) = 4 * frobSq M := by
  have hsq : ∀ v : Vec, sq (M.mulVec v) = ∑ i, ∑ k, ∑ l, M i k * M i l * (v k * v l) := by
    intro v
    unfold sq
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec, dotProduct]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc ∑ j, sq (M.mulVec (star j))
      = ∑ j, ∑ i, ∑ k, ∑ l, M i k * M i l * (star j k * star j l) := by simp_rw [hsq]
    _ = ∑ i, ∑ k, ∑ l, M i k * M i l * ∑ j, (star j k * star j l) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ k, ∑ l, M i k * M i l * (if k = l then 4 else 0) := by
        simp_rw [star_second_moment]
    _ = 4 * frobSq M := by
        unfold frobSq
        simp [Fin.sum_univ_three]
        ring

/-- The matched trial cost of a registration: eight odd labels whose star
vectors balance. -/
theorem star_cost (M : Mat) (h : Vec) (c : Fin 14 → ℝ) (hc : ∀ j, c j * c j = c j)
    (bal : ∀ i, ∑ j, c j * star j i = 0) (cnt : ∑ j, c j = 8) :
    ∑ j, sq (M.mulVec (star j) + c j • h) = 4 * frobSq M + 8 * sq h := by
  have expand : ∀ j, sq (M.mulVec (star j) + c j • h) =
      sq (M.mulVec (star j)) + 2 * (∑ i, h i * (c j * (M.mulVec (star j)) i)) + c j * sq h := by
    intro j
    have hcj := hc j
    simp only [sq_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    linear_combination (h 0 ^ 2 + h 1 ^ 2 + h 2 ^ 2) * hcj
  have cross : ∑ j, (∑ i, h i * (c j * (M.mulVec (star j)) i)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have inner : ∑ j, h i * (c j * (M.mulVec (star j)) i) =
        h i * ∑ k, M i k * ∑ j, c j * star j k := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [inner]
    simp [bal]
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, star_moment, ← Finset.mul_sum, cross,
    ← Finset.sum_mul, cnt]
  ring

theorem star_sq_bounds (j : Fin 14) : 3 / 4 ≤ sq (star j) ∧ sq (star j) ≤ 1 := by
  fin_cases j <;> norm_num [sq_three, star]

private theorem star_gap_int :
    ∀ i j : Fin 14, i ≠ j →
      3 ≤ (starTwice i 0 - starTwice j 0) ^ 2 + (starTwice i 1 - starTwice j 1) ^ 2 +
        (starTwice i 2 - starTwice j 2) ^ 2 := by
  decide

theorem star_gap (i j : Fin 14) (hij : i ≠ j) : 3 / 4 ≤ sq (star i - star j) := by
  have h := star_gap_int i j hij
  have hr : (3 : ℝ) ≤ ((starTwice i 0 - starTwice j 0 : ℤ) : ℝ) ^ 2 +
      ((starTwice i 1 - starTwice j 1 : ℤ) : ℝ) ^ 2 + ((starTwice i 2 - starTwice j 2 : ℤ) : ℝ) ^ 2 := by
    exact_mod_cast h
  push_cast at hr
  simp only [starTwice_eq] at hr
  rw [sq_three]
  simp only [Pi.sub_apply]
  nlinarith

/-! ### Integer points of `2 · BCC` -/

/-- An integer vector whose coordinates have one parity: `z / 2` is a BCC
point. -/
def BCCInt (z : IntVec) : Prop := (z 0 - z 1) % 2 = 0 ∧ (z 1 - z 2) % 2 = 0

instance (z : IntVec) : Decidable (BCCInt z) := by unfold BCCInt; infer_instance

private theorem bcc_small :
    ∀ a b c : ℤ, -2 ≤ a → a ≤ 2 → -2 ≤ b → b ≤ 2 → -2 ≤ c → c ≤ 2 →
      (a - b) % 2 = 0 → (b - c) % 2 = 0 → a ^ 2 + b ^ 2 + c ^ 2 < 8 →
      (a = 0 ∧ b = 0 ∧ c = 0) ∨
        ∃ j : Fin 14, starTwice j 0 = a ∧ starTwice j 1 = b ∧ starTwice j 2 = c := by
  intro a b c ha1 ha2 hb1 hb2 hc1 hc2
  interval_cases a <;> interval_cases b <;> interval_cases c <;> decide

/-- A nonzero point of `2 · BCC` that is not twice a star vector has squared
length at least `8`. -/
theorem bcc_norm (z : IntVec) (hz : BCCInt z) (h0 : z ≠ 0) (hs : ∀ j, z ≠ starTwice j) :
    8 ≤ z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  by_contra hlt
  push Not at hlt
  have bnd : ∀ i : Fin 3, -2 ≤ z i ∧ z i ≤ 2 := by
    intro i
    have hi : z i ^ 2 < 8 := by
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2)]
    constructor
    · by_contra h
      push Not at h
      have : z i ≤ -3 := by omega
      nlinarith
    · by_contra h
      push Not at h
      have : 3 ≤ z i := by omega
      nlinarith
  rcases bcc_small (z 0) (z 1) (z 2) (bnd 0).1 (bnd 0).2 (bnd 1).1 (bnd 1).2 (bnd 2).1 (bnd 2).2
    hz.1 hz.2 hlt with ⟨a, b, c⟩ | ⟨j, a, b, c⟩
  · apply h0
    funext i
    fin_cases i <;> simp [a, b, c]
  · apply hs j
    funext i
    fin_cases i <;> simp [a, b, c]

theorem bccInt_add {a b : IntVec} (ha : BCCInt a) (hb : BCCInt b) : BCCInt (a + b) := by
  unfold BCCInt at *
  simp only [Pi.add_apply]
  omega

theorem bccInt_smul (k : ℤ) {a : IntVec} (ha : BCCInt a) : BCCInt (fun i => k * a i) := by
  unfold BCCInt at *
  have d0 : (2 : ℤ) ∣ a 0 - a 1 := Int.dvd_of_emod_eq_zero ha.1
  have d1 : (2 : ℤ) ∣ a 1 - a 2 := Int.dvd_of_emod_eq_zero ha.2
  constructor
  · apply Int.emod_eq_zero_of_dvd
    have : k * a 0 - k * a 1 = k * (a 0 - a 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left d0 k
  · apply Int.emod_eq_zero_of_dvd
    have : k * a 1 - k * a 2 = k * (a 1 - a 2) := by ring
    rw [this]
    exact Dvd.dvd.mul_left d1 k

/-! ### Rational data and the registration check -/

def isIntQ (x : ℚ) : Bool := x.den == 1

theorem isIntQ_cast {x : ℚ} (h : isIntQ x = true) : ((x.num : ℚ)) = x :=
  (Rat.den_eq_one_iff x).mp (by simpa [isIntQ] using h)

theorem isIntQ_int (k : ℤ) : isIntQ (k : ℚ) = true := by
  simp [isIntQ]

def starQ (j : Fin 14) (i : Fin 3) : ℚ := (starTwice j i : ℚ) / 2

theorem starQ_cast (j : Fin 14) (i : Fin 3) : ((starQ j i : ℚ) : ℝ) = star j i := by
  rw [starQ]
  push_cast
  rw [starTwice_eq]
  ring

/-- `N s_j` for the star vector `s_j`. -/
def labelCoord (N : Fin 3 → Fin 3 → ℚ) (j : Fin 14) (i : Fin 3) : ℚ :=
  ∑ k, N i k * starQ j k

/-- Odd labels: `N s_j` is not integral. -/
def labelOdd (N : Fin 3 → Fin 3 → ℚ) (j : Fin 14) : Bool :=
  !(isIntQ (labelCoord N j 0) && isIntQ (labelCoord N j 1) && isIntQ (labelCoord N j 2))

def labelShift (N : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (j : Fin 14) (i : Fin 3) : ℚ :=
  labelCoord N j i - (if labelOdd N j then f0 i else 0)

/-- The integer vector `k_j` with `s_j = B (k_j + χ_j f₀)`. -/
def labelInt (N : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (j : Fin 14) : IntVec :=
  fun i => (labelShift N f0 j i).num

def twiceB (B : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) : ℤ := (2 * B i j).num

def twiceBf (B : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (i : Fin 3) : ℤ :=
  (2 * ∑ k, B i k * f0 k).num

def det3Q (U : Fin 3 → Fin 3 → ℚ) : ℚ :=
  U 0 0 * U 1 1 * U 2 2 - U 0 0 * U 1 2 * U 2 1 - U 0 1 * U 1 0 * U 2 2 +
    U 0 1 * U 1 2 * U 2 0 + U 0 2 * U 1 0 * U 2 1 - U 0 2 * U 1 1 * U 2 0

/-- Exact rational check of a registration proposal. -/
def registrationCheck (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) : Bool :=
  decide (
    (∀ i j : Fin 3, ∑ k, N i k * B k j = if i = j then 1 else 0) ∧
    (∀ i j : Fin 3, ∑ k, B i k * N k j = if i = j then 1 else 0) ∧
    (∀ i j : Fin 3, ∑ k, U k i * U k j = if i = j then 1 else 0) ∧
    det3Q U = 1 ∧
    (∀ i j : Fin 3, isIntQ (2 * B i j) = true) ∧
    (∀ j : Fin 3, BCCInt (fun i => twiceB B i j)) ∧
    (∀ i : Fin 3, isIntQ (2 * ∑ k, B i k * f0 k) = true) ∧
    BCCInt (twiceBf B f0) ∧
    (∃ i : Fin 3, isIntQ (f0 i) = false) ∧
    (∀ (j : Fin 14) (i : Fin 3), isIntQ (labelShift N f0 j i) = true) ∧
    (∑ j : Fin 14, (if labelOdd N j then (1 : ℤ) else 0)) = 8 ∧
    (∀ i : Fin 3, ∑ j : Fin 14, (if labelOdd N j then starTwice j i else 0) = 0))

/-! ### Fixture data -/

def B0 : Fin 3 → Fin 3 → ℚ := ![![1/2, -1/2, 0], ![1/2, 1/2, -1], ![1/2, 1/2, 1]]
def N0 : Fin 3 → Fin 3 → ℚ := ![![1, 1/2, 1/2], ![-1, 1/2, 1/2], ![0, -1/2, 1/2]]
def f00 : Fin 3 → ℚ := ![-1/2, -1/2, -1/2]

def U0 : Fin 3 → Fin 3 → ℚ :=
  ![![81219450610428/140737497135737, 81270656829527/140737497135737,
      81274376534484/140737497135737],
    ![-114936695235183/140737497135737, 57434329788636/140737497135737,
      57427318848928/140737497135737],
    ![-5566550864/140737497135737, -99515934403788/140737497135737,
      99516942621777/140737497135737]]

def U1 : Fin 3 → Fin 3 → ℚ :=
  ![![162438883715601/281474961629219, 162533854019582/281474961629219,
      162556172995494/281474961629219],
    ![-229873362496642/281474961629219, 114868644419889/281474961629219,
      114854628847926/281474961629219],
    ![-17201371686/281474961629219, -199037923147446/281474961629219,
      199027784184607/281474961629219]]

theorem fixture_registration_ok :
    registrationCheck B0 N0 U0 f00 = true ∧ registrationCheck B0 N0 U1 f00 = true := by
  constructor <;> decide +kernel

/-! ### Real matrices from the rational data -/

def ofQ (P : Fin 3 → Fin 3 → ℚ) : Mat := Matrix.of fun i j => (P i j : ℝ)

theorem ofQ_mulVec (P : Fin 3 → Fin 3 → ℚ) (v : Vec) (i : Fin 3) :
    (ofQ P).mulVec v i = ∑ k, (P i k : ℝ) * v k := by
  simp [ofQ, Matrix.mulVec, dotProduct]

theorem ofQ_mul_eq_one (P Q : Fin 3 → Fin 3 → ℚ)
    (h : ∀ i j : Fin 3, ∑ k, P i k * Q k j = if i = j then 1 else 0) : ofQ P * ofQ Q = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hc : ((∑ k, P i k * Q k j : ℚ) : ℝ) = if i = j then 1 else 0 := by
    rw [h i j]
    split_ifs <;> simp
  push_cast at hc
  simpa [ofQ] using hc

theorem ofQ_orth (U : Fin 3 → Fin 3 → ℚ)
    (h : ∀ i j : Fin 3, ∑ k, U k i * U k j = if i = j then 1 else 0) :
    (ofQ U).transpose * ofQ U = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hc : ((∑ k, U k i * U k j : ℚ) : ℝ) = if i = j then 1 else 0 := by
    rw [h i j]
    split_ifs <;> simp
  push_cast at hc
  simpa [ofQ, Matrix.transpose_apply] using hc

theorem nrm_zero : nrm 0 = 0 := by
  simp [nrm, sq_three]

theorem castVec_sub' (a b : IntVec) : castVec (a - b) = castVec a - castVec b := by
  funext i
  simp [castVec]

theorem ofQ_det (U : Fin 3 → Fin 3 → ℚ) (h : det3Q U = 1) : (ofQ U).det = 1 := by
  rw [Matrix.det_fin_three]
  have hc : ((det3Q U : ℚ) : ℝ) = 1 := by rw [h]; norm_num
  unfold det3Q at hc
  push_cast at hc
  simpa [ofQ] using hc

theorem f0_not_int (f0 : Fin 3 → ℚ) (h : ∃ i : Fin 3, isIntQ (f0 i) = false) (m : IntVec) :
    (fun i => (f0 i : ℝ)) ≠ castVec m := by
  intro e
  obtain ⟨i, hi⟩ := h
  have hr : ((f0 i : ℚ) : ℝ) = ((m i : ℚ) : ℝ) := by
    have := congrFun e i
    simpa [castVec] using this
  have hq : f0 i = (m i : ℚ) := by exact_mod_cast hr
  rw [hq] at hi
  simp [isIntQ_int] at hi

theorem twiceB_cast (B : Fin 3 → Fin 3 → ℚ) (h : ∀ i j : Fin 3, isIntQ (2 * B i j) = true)
    (i j : Fin 3) : ((twiceB B i j : ℤ) : ℝ) = 2 * (B i j : ℝ) := by
  have e := isIntQ_cast (h i j)
  have hr : (((twiceB B i j : ℤ) : ℚ) : ℝ) = ((2 * B i j : ℚ) : ℝ) := by
    unfold twiceB
    rw [e]
  push_cast at hr
  exact hr

theorem twiceBf_cast (B : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ)
    (h : ∀ i : Fin 3, isIntQ (2 * ∑ k, B i k * f0 k) = true) (i : Fin 3) :
    ((twiceBf B f0 i : ℤ) : ℝ) = 2 * ∑ k, (B i k : ℝ) * (f0 k : ℝ) := by
  have e := isIntQ_cast (h i)
  have hr : (((twiceBf B f0 i : ℤ) : ℚ) : ℝ) = ((2 * ∑ k, B i k * f0 k : ℚ) : ℝ) := by
    unfold twiceBf
    rw [e]
  push_cast at hr
  exact hr

/-- `N s_j = k_j + χ_j f₀`. -/
theorem N_star (N : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ)
    (hshift : ∀ (j : Fin 14) (i : Fin 3), isIntQ (labelShift N f0 j i) = true) (j : Fin 14) :
    (ofQ N).mulVec (star j) =
      castVec (labelInt N f0 j) + (if labelOdd N j then (fun i => (f0 i : ℝ)) else 0) := by
  funext i
  rw [ofQ_mulVec]
  have h1 : ((labelInt N f0 j i : ℤ) : ℝ) = ((labelShift N f0 j i : ℚ) : ℝ) := by
    have e := isIntQ_cast (hshift j i)
    unfold labelInt
    exact_mod_cast e
  have h2 : ((labelCoord N j i : ℚ) : ℝ) = ∑ k, (N i k : ℝ) * star j k := by
    unfold labelCoord
    push_cast
    simp only [starQ_cast]
  have h3 : labelCoord N j i = labelShift N f0 j i + (if labelOdd N j then f0 i else 0) := by
    unfold labelShift
    ring
  rw [← h2, h3]
  cases labelOdd N j <;> simp [castVec, h1]

/-- Integer combinations of the columns of `2B`, plus an optional `2 B f₀`. -/
def zVec (B : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (k : IntVec) (odd : Bool) : IntVec :=
  fun i => (∑ l, twiceB B i l * k l) + (if odd then twiceBf B f0 i else 0)

theorem zVec_bcc (B : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (k : IntVec) (odd : Bool)
    (hcol : ∀ j : Fin 3, BCCInt (fun i => twiceB B i j)) (hzf : BCCInt (twiceBf B f0)) :
    BCCInt (zVec B f0 k odd) := by
  have c0 := bccInt_smul (k 0) (hcol 0)
  have c1 := bccInt_smul (k 1) (hcol 1)
  have c2 := bccInt_smul (k 2) (hcol 2)
  have sum := bccInt_add (bccInt_add c0 c1) c2
  have e : zVec B f0 k odd = ((fun i => k 0 * twiceB B i 0) + (fun i => k 1 * twiceB B i 1) +
      (fun i => k 2 * twiceB B i 2)) + (if odd then twiceBf B f0 else 0) := by
    funext i
    simp only [zVec, Fin.sum_univ_three, Pi.add_apply]
    cases odd <;> simp <;> ring
  rw [e]
  cases odd
  · simpa using sum
  · simpa using bccInt_add sum hzf

theorem zVec_cast (B : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (k : IntVec) (odd : Bool)
    (h2B : ∀ i j : Fin 3, isIntQ (2 * B i j) = true)
    (h2Bf : ∀ i : Fin 3, isIntQ (2 * ∑ k, B i k * f0 k) = true) :
    (ofQ B).mulVec (castVec k + (if odd then (fun i => (f0 i : ℝ)) else 0)) =
      fun i => ((zVec B f0 k odd i : ℤ) : ℝ) / 2 := by
  funext i
  rw [ofQ_mulVec]
  simp only [zVec]
  push_cast
  simp only [twiceB_cast B h2B]
  cases odd
  · simp [castVec, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    ring
  · simp only [ite_true, twiceBf_cast B f0 h2Bf, Pi.add_apply, castVec]
    rw [add_div, Finset.sum_div]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro l _
      ring
    · rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem half_sq (z : IntVec) : sq (fun i => ((z i : ℤ) : ℝ) / 2) =
    ((z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 : ℤ) : ℝ) / 4 := by
  rw [sq_three]
  push_cast
  ring

theorem half_eq_star (z : IntVec) (j : Fin 14) (h : z = starTwice j) :
    (fun i => ((z i : ℤ) : ℝ) / 2) = star j := by
  funext i
  rw [h, starTwice_eq]
  ring

/-! ### The registered cost in matrix form -/

private theorem chart_mul_entry (N : Fin 3 → Fin 3 → ℚ) (p : Chart) (i j : Fin 3) :
    (chartBasis p * ofQ N) i j = strainEntry N p i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> simp [strainEntry, chartBasis, ofQ] <;> ring

theorem regCost_eq (N U : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (p : Chart) :
    regCost N U w p = 100 * frobSq (chartBasis p * ofQ N - ofQ U) +
      200 * sq ((chartBasis p).mulVec ((chartPoint p).offset - fun i => (w i : ℝ))) := by
  unfold regCost
  congr 2
  · unfold strainCost frobSq
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.sub_apply, chart_mul_entry]
    simp [ofQ]
  · have e0 := DirectRoute.offset_eq p 0
    have e1 := DirectRoute.offset_eq p 1
    have e2 := DirectRoute.offset_eq p 2
    rw [sq_three]
    simp only [primalQ, rowA, rowB, rowC, img, ite_true, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Pi.sub_apply, e0, e1, e2]
    simp [chartBasis]
    ring

/-! ### Main theorem -/

theorem defect_le_regCost (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (n : IntVec)
    (ok : registrationCheck B N U f0 = true) (p : Chart) (hv : (chartPoint p).Valid)
    (small : regCost N U (fun i => f0 i + (n i : ℚ)) p ≤ 1 / 2) :
    defect (chartPoint p) ≤ regCost N U (fun i => f0 i + (n i : ℚ)) p := by
  unfold registrationCheck at ok
  obtain ⟨hNB, hBN, hUU, hdet, h2B, hcol, h2Bf, hzf, hf0, hshift, hcnt, hbal⟩ :=
    of_decide_eq_true ok
  -- Real data.
  set R : Mat := chartBasis p with hR
  set f : Vec := (chartPoint p).offset with hf
  set f0r : Vec := fun i => (f0 i : ℝ) with hf0r
  set Br := ofQ B with hBr
  set Nr := ofQ N with hNr
  set Ur := ofQ U with hUr
  set A : Mat := R * Nr with hA
  set h : Vec := R.mulVec (f - fun i => ((f0 i + (n i : ℚ) : ℚ) : ℝ)) with hh
  have NB : Nr * Br = 1 := ofQ_mul_eq_one N B hNB
  have UU : Ur.transpose * Ur = 1 := ofQ_orth U hUU
  have properU : proper Ur := ⟨UU, ofQ_det U hdet⟩
  have hwr : (fun i => ((f0 i + (n i : ℚ) : ℚ) : ℝ)) = f0r + castVec n := by
    funext i
    simp [hf0r, castVec]
  have basisR : (chartPoint p).basis = R := rfl
  -- The cost and its two parts.
  have cost := regCost_eq N U (fun i => f0 i + (n i : ℚ)) p
  set X := frobSq (A - Ur) with hX
  set Y := sq h with hY
  have hX0 : 0 ≤ X := frobSq_nonneg _
  have hY0 : 0 ≤ Y := sq_nonnegative _
  have hXY : 100 * X + 200 * Y ≤ 1 / 2 := by
    rw [cost] at small
    exact small
  set x := Real.sqrt X with hx
  set y := Real.sqrt Y with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = X := Real.sq_sqrt hX0
  have hy2 : y ^ 2 = Y := Real.sq_sqrt hY0
  have hxb : x ≤ 3 / 40 := by
    rw [hx, Real.sqrt_le_left (by norm_num)]
    linarith only [hXY, hY0]
  have hyb : y ≤ 1 / 20 := by
    rw [hy, Real.sqrt_le_left (by norm_num)]
    linarith only [hXY, hX0]
  have hny : nrm h = y := rfl
  set s2 := Real.sqrt 2 with hs2d
  have hs2 : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs20 : 0 ≤ s2 := Real.sqrt_nonneg _
  have hs2b : 707 / 500 ≤ s2 := by
    rw [hs2d, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have csq : (s2 * x + y) ^ 2 ≤ 1 / 80 := by
    have a : (x - 2 * s2 * y) ^ 2 = x ^ 2 - 4 * s2 * x * y + 4 * s2 ^ 2 * y ^ 2 := by ring
    have b : (s2 * x + y) ^ 2 = s2 ^ 2 * x ^ 2 + 2 * s2 * x * y + y ^ 2 := by ring
    rw [hs2] at a b
    linarith only [a, b, sq_nonneg (x - 2 * s2 * y), hx2, hy2, hXY]
  have key : s2 * x + y ≤ 1119 / 10000 := by
    nlinarith only [csq, mul_nonneg hs20 hx0, hy0]
  have far : 13 / 10 < (1 - x) * s2 - y := by
    linarith only [key, hs2b]
  -- Length bounds for images.
  have lowerA : ∀ v : Vec, (1 - x) * nrm v ≤ nrm (A.mulVec v) := nrm_mulVec_lower A Ur UU
  have upperA : ∀ v : Vec, nrm (A.mulVec v) ≤ (1 + x) * nrm v := nrm_mulVec_upper A Ur UU
  have AB : ∀ v : Vec, A.mulVec (Br.mulVec v) = R.mulVec v := by
    intro v
    rw [hA, Matrix.mulVec_mulVec, Matrix.mul_assoc, NB, Matrix.mul_one]
  have NBv : ∀ v : Vec, Nr.mulVec (Br.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, NB, Matrix.one_mulVec]
  have notInt : ∀ m : IntVec, f0r ≠ castVec m := f0_not_int f0 hf0
  -- Star data.
  have Ns : ∀ j : Fin 14, Nr.mulVec (star j) =
      castVec (labelInt N f0 j) + (if labelOdd N j then f0r else 0) :=
    N_star N f0 hshift
  have parity : ∀ (j : Fin 14) (κ : IntVec) (c : Bool),
      Nr.mulVec (star j) = castVec κ + (if c then f0r else 0) → labelOdd N j = c := by
    intro j κ c e
    rw [Ns j] at e
    cases hj : labelOdd N j <;> cases c
    · rfl
    · rw [hj] at e
      exfalso
      apply notInt (labelInt N f0 j - κ)
      have e' : castVec (labelInt N f0 j) = castVec κ + f0r := by simpa using e
      funext i
      have := congrFun e' i
      simp only [Pi.add_apply, Pi.sub_apply, castVec, Int.cast_sub] at this ⊢
      linarith only [this]
    · rw [hj] at e
      exfalso
      apply notInt (κ - labelInt N f0 j)
      have e' : castVec (labelInt N f0 j) + f0r = castVec κ := by simpa using e
      funext i
      have := congrFun e' i
      simp only [Pi.add_apply, Pi.sub_apply, castVec, Int.cast_sub] at this ⊢
      linarith only [this]
    · rfl
  -- The fourteen matched images.
  set σv : Fin 14 → Vec := fun j => A.mulVec (star j) + (if labelOdd N j then h else 0) with hσv
  have chiNorm : ∀ b : Bool, nrm (if b then h else 0) ≤ y := by
    intro b
    cases b
    · simp only [Bool.false_eq_true, ite_false, nrm_zero]
      exact hy0
    · simp only [ite_true]
      exact le_of_eq hny
  have starNrm : ∀ j : Fin 14, Real.sqrt (3 / 4) ≤ nrm (star j) ∧ nrm (star j) ≤ 1 := by
    intro j
    obtain ⟨lo, hi⟩ := star_sq_bounds j
    exact ⟨Real.sqrt_le_sqrt lo, by rw [nrm, Real.sqrt_le_left (by norm_num)]; linarith only [hi]⟩
  have r34 : 866 / 1000 ≤ Real.sqrt (3 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have σsmall : ∀ j : Fin 14, sq (σv j) < (13 / 10) ^ 2 := by
    intro j
    have t := nrm_add_le (A.mulVec (star j)) (if labelOdd N j then h else 0)
    have u := upperA (star j)
    have c := chiNorm (labelOdd N j)
    have s := (starNrm j).2
    have m : (1 + x) * nrm (star j) ≤ (1 + x) * 1 :=
      mul_le_mul_of_nonneg_left s (by linarith only [hx0])
    have bound : nrm (σv j) ≤ 9 / 8 := by
      show nrm (A.mulVec (star j) + (if labelOdd N j then h else 0)) ≤ 9 / 8
      linarith only [t, u, c, m, hxb, hyb]
    rw [← nrm_sq]
    nlinarith only [bound, nrm_nonneg (σv j)]
  have σne : ∀ j : Fin 14, σv j ≠ 0 := by
    intro j e
    have t := nrm_sub_le (A.mulVec (star j)) (if labelOdd N j then h else 0)
    have l := lowerA (star j)
    have c := chiNorm (labelOdd N j)
    have s := (starNrm j).1
    have z : nrm (A.mulVec (star j) + (if labelOdd N j then h else 0)) = 0 := by
      have : A.mulVec (star j) + (if labelOdd N j then h else 0) = 0 := e
      rw [this, nrm_zero]
    have m : (1 - x) * (866 / 1000) ≤ (1 - x) * nrm (star j) :=
      mul_le_mul_of_nonneg_left (r34.trans s) (by linarith only [hxb])
    linarith only [t, l, c, z, m, hxb, hyb]
  have σinj : ∀ i j : Fin 14, σv i = σv j → i = j := by
    intro i j e
    by_contra hij
    have gap := star_gap i j hij
    have e' : A.mulVec (star i) + (if labelOdd N i then h else 0) =
        A.mulVec (star j) + (if labelOdd N j then h else 0) := e
    have d : A.mulVec (star i - star j) =
        (if labelOdd N j then h else 0) - (if labelOdd N i then h else 0) := by
      rw [Matrix.mulVec_sub, sub_eq_sub_iff_add_eq_add, e', add_comm]
    have l := lowerA (star i - star j)
    have ndist : Real.sqrt (3 / 4) ≤ nrm (star i - star j) := Real.sqrt_le_sqrt gap
    have rhs : nrm ((if labelOdd N j then h else 0) - (if labelOdd N i then h else 0)) ≤ y := by
      cases labelOdd N i <;> cases labelOdd N j
      · simp only [Bool.false_eq_true, ite_false, sub_zero, nrm_zero]
        exact hy0
      · simp only [Bool.false_eq_true, ite_false, ite_true, sub_zero]
        exact le_of_eq hny
      · simp only [Bool.false_eq_true, ite_false, ite_true, zero_sub, nrm_neg]
        exact le_of_eq hny
      · simp only [ite_true, sub_self, nrm_zero]
        exact hy0
    rw [d] at l
    have m : (1 - x) * (866 / 1000) ≤ (1 - x) * nrm (star i - star j) :=
      mul_le_mul_of_nonneg_left (r34.trans ndist) (by linarith only [hxb])
    linarith only [l, m, rhs, hxb, hyb]
  have σalt : ∀ j : Fin 14, σv j =
      R.mulVec (castVec (labelInt N f0 j) - (if labelOdd N j then castVec n else 0)) +
        (if labelOdd N j then R.mulVec f else 0) := by
    intro j
    show A.mulVec (star j) + (if labelOdd N j then h else 0) = _
    have hs : star j = Br.mulVec (Nr.mulVec (star j)) := by
      rw [Matrix.mulVec_mulVec, ofQ_mul_eq_one B N hBN, Matrix.one_mulVec]
    rw [hs, AB, Ns j, hh, hwr]
    cases labelOdd N j
    · simp
    · simp only [ite_true, Matrix.mulVec_add, Matrix.mulVec_sub]
      abel
  have σmem : ∀ j : Fin 14, σv j ∈ (chartPoint p).points := by
    intro j
    rw [σalt j]
    cases labelOdd N j
    · left
      simp only [Bool.false_eq_true, ite_false, sub_zero, add_zero]
      exact ⟨labelInt N f0 j, rfl⟩
    · right
      simp only [ite_true]
      refine ⟨R.mulVec (castVec (labelInt N f0 j - n)), ⟨labelInt N f0 j - n, rfl⟩, ?_⟩
      rw [castVec_sub']
      rfl
  have σnb : ∀ j : Fin 14, σv j ∈ neighbors (chartPoint p) := by
    intro j
    refine ⟨by simpa using σmem j, σne j, σsmall j⟩
  let σ : Fin 14 ↪ ↥(neighbors (chartPoint p)) :=
    ⟨fun j => ⟨σv j, σnb j⟩, fun i j e => σinj i j (congrArg Subtype.val e)⟩
  -- Every lifted neighbour is matched.
  have farImage : ∀ (e : Vec) (z : IntVec), BCCInt z → z ≠ 0 → (∀ j, z ≠ starTwice j) →
      e = (fun i => ((z i : ℤ) : ℝ) / 2) → (1 - x) * s2 ≤ nrm (A.mulVec e) := by
    intro e z hz z0 zs he
    have n8 := bcc_norm z hz z0 zs
    have se : 2 ≤ sq e := by
      rw [he, half_sq]
      have : (8 : ℝ) ≤ ((z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 : ℤ) : ℝ) := by exact_mod_cast n8
      linarith only [this]
    have ne : s2 ≤ nrm e := Real.sqrt_le_sqrt se
    have l := lowerA e
    have m : (1 - x) * s2 ≤ (1 - x) * nrm e :=
      mul_le_mul_of_nonneg_left ne (by linarith only [hxb])
    linarith only [l, m]
  have matched : ∀ v ∈ neighbors (chartPoint p), ∃ j, σv j = v := by
    intro v hvn
    obtain ⟨hpt, hv0, hvs⟩ := hvn
    rw [zero_add] at hpt
    have big : ∀ t : ℝ, 13 / 10 < t → t ≤ nrm v → False := by
      intro t ht tv
      have lt : (13 / 10 : ℝ) < nrm v := lt_of_lt_of_le ht tv
      have sqv : (13 / 10 : ℝ) ^ 2 < nrm v ^ 2 :=
        pow_lt_pow_left₀ lt (by norm_num) (by norm_num)
      rw [nrm_sq] at sqv
      exact absurd hvs (not_lt.mpr sqv.le)
    rcases hpt with hl | ht
    · -- `v = R k`
      obtain ⟨k, hk⟩ := hl
      have hk' : R.mulVec (castVec k) = v := hk
      set e := Br.mulVec (castVec k + (if false then f0r else 0)) with he
      have ze := zVec_cast B f0 k false h2B h2Bf
      have Ae : A.mulVec e = v := by
        rw [he, AB]
        simpa using hk'
      have Ne : Nr.mulVec e = castVec k + (if false then f0r else 0) := NBv _
      by_cases hs : ∃ j, zVec B f0 k false = starTwice j
      · obtain ⟨j, hj⟩ := hs
        have es : e = star j := by
          rw [he, ze]
          exact half_eq_star _ j hj
        have odd := parity j k false (by rw [← es]; exact Ne)
        refine ⟨j, ?_⟩
        show A.mulVec (star j) + (if labelOdd N j then h else 0) = v
        rw [odd, ← es, Ae]
        simp
      · push Not at hs
        have z0 : zVec B f0 k false ≠ 0 := by
          intro z0
          apply hv0
          rw [← Ae, he, ze, z0]
          have : (fun i : Fin 3 => (((0 : IntVec) i : ℤ) : ℝ) / 2) = 0 := by
            funext i
            simp
          rw [this, Matrix.mulVec_zero]
        have fi := farImage e (zVec B f0 k false) (zVec_bcc B f0 k false hcol hzf) z0 hs
          (by rw [he, ze])
        rw [Ae] at fi
        exact (big _ (by linarith only [far, hy0]) fi).elim
    · -- `v = R k + R f`
      obtain ⟨yv, ⟨k, hk⟩, hyv⟩ := ht
      have hk' : R.mulVec (castVec k) = yv := hk
      set κ : IntVec := k + n with hκ
      set e := Br.mulVec (castVec κ + (if true then f0r else 0)) with he
      have ze := zVec_cast B f0 κ true h2B h2Bf
      have Ae : A.mulVec e + h = v := by
        rw [he, AB, hyv, ← hk', hh, hwr, hκ, castVec_add, basisR]
        simp only [ite_true, Matrix.mulVec_add, Matrix.mulVec_sub]
        abel
      have Ne : Nr.mulVec e = castVec κ + (if true then f0r else 0) := NBv _
      by_cases hs : ∃ j, zVec B f0 κ true = starTwice j
      · obtain ⟨j, hj⟩ := hs
        have es : e = star j := by
          rw [he, ze]
          exact half_eq_star _ j hj
        have odd := parity j κ true (by rw [← es]; exact Ne)
        refine ⟨j, ?_⟩
        show A.mulVec (star j) + (if labelOdd N j then h else 0) = v
        rw [odd, ← es]
        simpa using Ae
      · push Not at hs
        have z0 : zVec B f0 κ true ≠ 0 := by
          intro z0
          have e0 : e = 0 := by
            rw [he, ze, z0]
            funext i
            simp
          have hz : castVec κ + f0r = 0 := by
            have h1 := Ne
            rw [e0, Matrix.mulVec_zero] at h1
            simpa using h1.symm
          apply notInt (-κ)
          rw [castVec_neg]
          funext i
          have := congrFun hz i
          simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at this ⊢
          linarith only [this]
        have fi := farImage e (zVec B f0 κ true) (zVec_bcc B f0 κ true hcol hzf) z0 hs
          (by rw [he, ze])
        have t := nrm_sub_le (A.mulVec e) h
        rw [Ae, hny] at t
        exact (big ((1 - x) * s2 - y) far (by linarith only [t, fi])).elim
  -- The trial cost.
  have trial : defectTrial Ur σ = 100 * X + 200 * Y := by
    unfold defectTrial
    have zeroTail : (∑' v : ↥(neighbors (chartPoint p)),
        if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val) = 0 := by
      have hz : (fun v : ↥(neighbors (chartPoint p)) =>
          if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val) = fun _ => 0 := by
        funext v
        have hm : v ∈ Set.range σ := by
          obtain ⟨j, hj⟩ := matched v.val v.property
          exact ⟨j, Subtype.ext hj⟩
        simp [hm]
      rw [hz, tsum_zero]
    rw [zeroTail, add_zero]
    let c : Fin 14 → ℝ := fun j => if labelOdd N j then 1 else 0
    have hcc : ∀ j, c j * c j = c j := by
      intro j
      simp only [c]
      split_ifs <;> norm_num
    have bal : ∀ i, ∑ j, c j * star j i = 0 := by
      intro i
      have hb := hbal i
      have hr : ((∑ j : Fin 14, (if labelOdd N j then starTwice j i else 0) : ℤ) : ℝ) = 0 := by
        rw [hb]
        simp
      push_cast at hr
      have e : ∀ j, c j * star j i =
          (1 / 2) * (if labelOdd N j then (starTwice j i : ℝ) else 0) := by
        intro j
        simp only [c]
        split_ifs
        · rw [starTwice_eq]
          ring
        · ring
      rw [Finset.sum_congr rfl (fun j _ => e j), ← Finset.mul_sum, hr, mul_zero]
    have cnt : ∑ j, c j = 8 := by
      have hr : ((∑ j : Fin 14, (if labelOdd N j then (1 : ℤ) else 0) : ℤ) : ℝ) = 8 := by
        rw [hcnt]
        norm_num
      push_cast at hr
      simpa [c] using hr
    have terms : ∀ j, (σ j : Vec) - Ur.mulVec (star j) = (A - Ur).mulVec (star j) + c j • h := by
      intro j
      show A.mulVec (star j) + (if labelOdd N j then h else 0) - Ur.mulVec (star j) =
        (A - Ur).mulVec (star j) + c j • h
      simp only [c, Matrix.sub_mulVec]
      cases labelOdd N j
      · simp
      · simp
        abel
    simp_rw [terms]
    rw [star_cost (A - Ur) h c hcc bal cnt]
    ring
  -- Conclusion.
  have bdd : BddBelow (defectCandidates (neighbors (chartPoint p))) := by
    refine ⟨0, fun c hc => ?_⟩
    rcases Set.mem_insert_iff.mp hc with rfl | ⟨U', _, σ', rfl⟩
    · norm_num
    · apply add_nonneg
      · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => sq_nonnegative _))
      · apply tsum_nonneg
        intro v
        split_ifs
        · exact le_rfl
        · exact le_max_left _ _
  have mem : defectTrial Ur σ ∈ defectCandidates (neighbors (chartPoint p)) :=
    Set.mem_insert_of_mem _ ⟨Ur, properU, σ, rfl⟩
  have le := csInf_le bdd mem
  rw [cost]
  unfold defect cappedDefect
  rw [trial] at le
  exact le

end BccSharp.Coulomb.CompactCover.JLeaf
