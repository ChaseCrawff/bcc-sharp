import BccSharp.TwoSite.DefectAnnulus

set_option autoImplicit false

/-! # The registered defect bound up to the Stage5b cutoff

This module shows
that the annular images are lifted neighbours only above the cutoff
`d♯ = (600/11)(√2 − 13/10)² ≈ 0.7115`, so below it the actual defect is at most
the registered cost. The existing `defect_le_regCost` uses the operator bound
`|A e| ≥ (1 − ‖A − U‖_F)|e|` and stops at `40(√2 − 13/10)² ≈ 0.522`. The cutoff
needs the sharper determinant-one bound (1): with `s = σ_min(A)`,
`‖A − U‖²_F ≥ (1 − s)² + 2(1/√s − 1)² ≥ (3/2)(1 − s)²`.

We prove (1) only for the twelve annular vectors, which is all that is needed,
and without singular values. The annular vectors are `±u_k` and `±v_k` for the
three orthogonal frames `(u_k, v_k, w_k)` with `|u_k|² = |v_k|² = 2`,
`|w_k|² = 1` (`frameU`, `frameV`, `frameW`; `ann_frame`). For such a frame and any matrix
`M`, `‖M‖²_F = |M u|²/2 + |M v|²/2 + |M w|²` (`frame_frob`), and
`[M u, M v, M w]` has determinant `± 2 det M` (`frame_tripleProd`). With
`a = |A u|/√2`, `b = |A v|/√2`, `c = |A w|`, Hadamard's inequality
(`tripleProd_sq_le`) and `det A = 1` give `a b c ≥ 1`. For orthogonal `U`,
`|(A − U) u| ≥ ||A u| − √2|` (`dist_orth`), so
`‖A − U‖²_F ≥ (a − 1)² + (b − 1)² + (c − 1)²`, and `scalar_lower` gives
`3(1 − a)² ≤ 2‖A − U‖²_F` when `a ≤ 1`. This is (1) at `e = u`
(`frame_lower`).

`annular_far` is the lower length (2) at `t = √2`: if
`100‖A − U‖²_F + 200|h|² ≤ d♯`, every annular image `A e_j + χ h` is at least
`13/10` long. The deficit `g = √2 − |A e_j|` satisfies `75 g² ≤ 100‖A − U‖²_F`,
and Cauchy–Schwarz gives `(g + |h|)² ≤ (11/600)(75 g² + 200|h|²) ≤
(√2 − 13/10)²`.

* `annPhi_eq_zero`: below the cutoff the annular penalty vanishes.
* `defect_le_regCost_cutoff`: `defect ≤ q` for `q ≤ d♯`, from
  `defect_le_annulus`. Besides `registrationCheck` it needs `det N = 1`
  (`det3Q N = 1`), which Stage5b's catalogue guarantees (`det B = 1`), and a valid
  chart point (`det R = 1`).
* `cutoffOk c` is an exact rational test of `0 ≤ c ≤ d♯`; `dSharpQ = 711531/10⁶`
  and `dSharpZ / 2⁹⁶` pass it (`cutoffOk_dSharpQ`, `cutoffOk_dSharpZ`). -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf.Cutoff
open BccSharp

/-- The Stage5b cutoff `d♯ = (600/11)(√2 − 13/10)²`. -/
def dSharp : ℝ := 600 / 11 * (Real.sqrt 2 - 13 / 10) ^ 2

/-! ### Hadamard's inequality -/

/-- The triple product `a · (b × c)`. -/
def tripleProd (a b c : Vec) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) + a 1 * (b 2 * c 0 - b 0 * c 2) +
    a 2 * (b 0 * c 1 - b 1 * c 0)

/-- Hadamard's inequality for three vectors, squared. -/
theorem tripleProd_sq_le (a b c : Vec) : tripleProd a b c ^ 2 ≤ sq a * sq b * sq c := by
  have lagB : (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) * (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) =
      ((b 1 * c 2 - b 2 * c 1) ^ 2 + (b 2 * c 0 - b 0 * c 2) ^ 2 + (b 0 * c 1 - b 1 * c 0) ^ 2) +
        (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) ^ 2 := by
    ring
  have lagA : ∀ w0 w1 w2 : ℝ, (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) =
      (a 0 * w0 + a 1 * w1 + a 2 * w2) ^ 2 + (a 0 * w1 - a 1 * w0) ^ 2 +
        (a 0 * w2 - a 2 * w0) ^ 2 + (a 1 * w2 - a 2 * w1) ^ 2 := by
    intro w0 w1 w2
    ring
  obtain ⟨w0, hw0⟩ : ∃ w0, b 1 * c 2 - b 2 * c 1 = w0 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w1, b 2 * c 0 - b 0 * c 2 = w1 := ⟨_, rfl⟩
  obtain ⟨w2, hw2⟩ : ∃ w2, b 0 * c 1 - b 1 * c 0 = w2 := ⟨_, rfl⟩
  rw [hw0, hw1, hw2] at lagB
  have htp : tripleProd a b c = a 0 * w0 + a 1 * w1 + a 2 * w2 := by
    rw [← hw0, ← hw1, ← hw2]
    rfl
  have hw : w0 ^ 2 + w1 ^ 2 + w2 ^ 2 ≤ sq b * sq c := by
    rw [sq_eq_three b, sq_eq_three c, lagB]
    nlinarith [sq_nonneg (b 0 * c 0 + b 1 * c 1 + b 2 * c 2)]
  have cs : tripleProd a b c ^ 2 ≤ sq a * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := by
    rw [htp, sq_eq_three a, lagA w0 w1 w2]
    nlinarith [sq_nonneg (a 0 * w1 - a 1 * w0), sq_nonneg (a 0 * w2 - a 2 * w0),
      sq_nonneg (a 1 * w2 - a 2 * w1)]
  calc tripleProd a b c ^ 2 ≤ sq a * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := cs
    _ ≤ sq a * (sq b * sq c) := mul_le_mul_of_nonneg_left hw (sq_nonnegative a)
    _ = sq a * sq b * sq c := by ring

/-! ### Three orthogonal frames through the annular vectors -/

/-- `u_k`: `(1, 1, 0)`, `(1, 0, 1)`, `(0, 1, 1)`. -/
def frameUZ : Fin 3 → IntVec := ![![1, 1, 0], ![1, 0, 1], ![0, 1, 1]]
/-- `v_k`: `(1, −1, 0)`, `(1, 0, −1)`, `(0, 1, −1)`. -/
def frameVZ : Fin 3 → IntVec := ![![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
/-- `w_k`: `(0, 0, 1)`, `(0, 1, 0)`, `(1, 0, 0)`. -/
def frameWZ : Fin 3 → IntVec := ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]

def frameU (k : Fin 3) : Vec := castVec (frameUZ k)
def frameV (k : Fin 3) : Vec := castVec (frameVZ k)
def frameW (k : Fin 3) : Vec := castVec (frameWZ k)

theorem frame_sq (k : Fin 3) :
    sq (frameU k) = 2 ∧ sq (frameV k) = 2 ∧ sq (frameW k) = 1 := by
  fin_cases k <;>
    norm_num [sq_eq_three, frameU, frameV, frameW, frameUZ, frameVZ, frameWZ, castVec]

/-- The Frobenius norm in an orthogonal frame. -/
theorem frame_frob (k : Fin 3) (M : Mat) :
    frobSq M = sq (M.mulVec (frameU k)) / 2 + sq (M.mulVec (frameV k)) / 2 +
      sq (M.mulVec (frameW k)) := by
  fin_cases k <;>
    simp [frobSq, sq_eq_three, frameU, frameV, frameW, frameUZ, frameVZ, frameWZ, castVec,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- The frame has determinant `±2`. -/
theorem frame_tripleProd (k : Fin 3) (M : Mat) :
    tripleProd (M.mulVec (frameU k)) (M.mulVec (frameV k)) (M.mulVec (frameW k)) ^ 2 =
      4 * M.det ^ 2 := by
  fin_cases k <;>
    simp [tripleProd, frameU, frameV, frameW, frameUZ, frameVZ, frameWZ, castVec,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three] <;>
    ring

/-- `(|M u| − |u|)² ≤ |(M − U) u|²` for orthogonal `U`. -/
theorem dist_orth (M U : Mat) (hU : U.transpose * U = 1) (u : Vec) :
    (nrm (M.mulVec u) - nrm u) ^ 2 ≤ sq ((M - U).mulVec u) := by
  have hu : nrm (U.mulVec u) = nrm u := by unfold nrm; rw [sq_orth U hU u]
  have e : (M - U).mulVec u = M.mulVec u + -U.mulVec u := by
    rw [Matrix.sub_mulVec]
    abel
  have e' : -(M - U).mulVec u = U.mulVec u + -M.mulVec u := by
    rw [Matrix.sub_mulVec]
    abel
  have t1 := nrm_sub_le (M.mulVec u) (-U.mulVec u)
  have t2 := nrm_sub_le (U.mulVec u) (-M.mulVec u)
  rw [nrm_neg, ← e, hu] at t1
  rw [nrm_neg, ← e', nrm_neg, hu] at t2
  rw [← nrm_sq]
  exact sq_le_sq' (by linarith) t1

/-! ### The determinant-one bound (1) -/

/-- The scalar step of (1): `a b c ≥ 1` and `a ≤ 1` give
`(b − 1)² + (c − 1)² ≥ (1 − a)²/2`. -/
theorem scalar_lower (a b c X : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (prod : 1 ≤ a * b * c) (hX : (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 ≤ X) (h1 : a ≤ 1) :
    3 * (1 - a) ^ 2 ≤ 2 * X := by
  have apos : 0 < a := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · rw [← h] at prod
      norm_num at prod
  have sum2 : 4 ≤ a * (b + c) ^ 2 := by
    have e : a * (b + c) ^ 2 = a * (b - c) ^ 2 + 4 * (a * b * c) := by ring
    rw [e]
    nlinarith [mul_nonneg ha (sq_nonneg (b - c))]
  have cub : a * (3 - a) ^ 2 ≤ 4 := by
    have e : 4 - a * (3 - a) ^ 2 = (1 - a) ^ 2 * (4 - a) := by ring
    nlinarith [mul_nonneg (sq_nonneg (1 - a)) (by linarith : (0 : ℝ) ≤ 4 - a)]
  have sqge : (3 - a) ^ 2 ≤ (b + c) ^ 2 := by
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left hlt apos
    linarith
  have lin : 3 - a ≤ b + c := by
    by_contra hl
    push Not at hl
    have p1 : 0 < (3 - a) - (b + c) := by linarith
    have p2 : 0 < (3 - a) + (b + c) := by linarith
    nlinarith [mul_pos p1 p2]
  have quad : (1 - a) ^ 2 ≤ ((b - 1) + (c - 1)) ^ 2 := by
    have h0 : 0 ≤ 1 - a := by linarith
    have h1' : 0 ≤ ((b - 1) + (c - 1)) - (1 - a) := by linarith
    nlinarith [mul_nonneg h0 h1', sq_nonneg (((b - 1) + (c - 1)) - (1 - a))]
  nlinarith [sq_nonneg ((b - 1) - (c - 1))]

/-- **(1) on a frame.** For `det A = 1` and orthogonal `U`, the frame vectors
`u_k`, `v_k` (length `√2`) satisfy `3(√2 − |A u|)² ≤ 4‖A − U‖²_F` when
`|A u| < √2`. -/
theorem frame_lower (A U : Mat) (hU : U.transpose * U = 1) (hdet : A.det = 1) (k : Fin 3) :
    (nrm (A.mulVec (frameU k)) < Real.sqrt 2 →
      3 * (Real.sqrt 2 - nrm (A.mulVec (frameU k))) ^ 2 ≤ 4 * frobSq (A - U)) ∧
    (nrm (A.mulVec (frameV k)) < Real.sqrt 2 →
      3 * (Real.sqrt 2 - nrm (A.mulVec (frameV k))) ^ 2 ≤ 4 * frobSq (A - U)) := by
  obtain ⟨su, sv, sw⟩ := frame_sq k
  have hr2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have r2ne : Real.sqrt 2 ≠ 0 := hr2pos.ne'
  have nu : nrm (frameU k) = Real.sqrt 2 := by rw [nrm, su]
  have nv : nrm (frameV k) = Real.sqrt 2 := by rw [nrm, sv]
  have nw : nrm (frameW k) = 1 := by rw [nrm, sw, Real.sqrt_one]
  have du := dist_orth A U hU (frameU k)
  have dv := dist_orth A U hU (frameV k)
  have dw := dist_orth A U hU (frameW k)
  rw [nu] at du
  rw [nv] at dv
  rw [nw] at dw
  have fro := frame_frob k (A - U)
  have had2 := tripleProd_sq_le (A.mulVec (frameU k)) (A.mulVec (frameV k)) (A.mulVec (frameW k))
  rw [frame_tripleProd k A, hdet, ← nrm_sq, ← nrm_sq, ← nrm_sq] at had2
  have a0 := nrm_nonneg (A.mulVec (frameU k))
  have b0 := nrm_nonneg (A.mulVec (frameV k))
  have c0 := nrm_nonneg (A.mulVec (frameW k))
  -- abstract the three lengths and the Frobenius norm
  obtain ⟨a, ha⟩ : ∃ a, nrm (A.mulVec (frameU k)) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, nrm (A.mulVec (frameV k)) = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, nrm (A.mulVec (frameW k)) = c := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, frobSq (A - U) = X := ⟨_, rfl⟩
  rw [ha] at du a0 had2 ⊢
  rw [hb] at dv b0 had2 ⊢
  rw [hc] at dw c0 had2
  rw [hX] at fro ⊢
  -- `X ≥ (a − √2)²/2 + (b − √2)²/2 + (c − 1)²`
  have hXabc : (a - Real.sqrt 2) ^ 2 / 2 + (b - Real.sqrt 2) ^ 2 / 2 + (c - 1) ^ 2 ≤ X := by
    rw [fro]
    linarith
  -- Hadamard: `a b c ≥ 2`
  have abc : 2 ≤ a * b * c := by
    have h4 : (2 : ℝ) ^ 2 ≤ (a * b * c) ^ 2 := by nlinarith
    have hp : 0 ≤ a * b * c := mul_nonneg (mul_nonneg a0 b0) c0
    nlinarith
  -- normalized lengths
  have key : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → 2 ≤ s * t * c →
      (s - Real.sqrt 2) ^ 2 / 2 + (t - Real.sqrt 2) ^ 2 / 2 + (c - 1) ^ 2 ≤ X →
      s < Real.sqrt 2 → 3 * (Real.sqrt 2 - s) ^ 2 ≤ 4 * X := by
    intro s t s0 t0 hst hX' hs
    have e1 : (s / Real.sqrt 2 - 1) ^ 2 = (s - Real.sqrt 2) ^ 2 / 2 := by
      rw [div_sub_one r2ne, div_pow, hr2sq]
    have e2 : (t / Real.sqrt 2 - 1) ^ 2 = (t - Real.sqrt 2) ^ 2 / 2 := by
      rw [div_sub_one r2ne, div_pow, hr2sq]
    have e3 : (1 - s / Real.sqrt 2) ^ 2 = (Real.sqrt 2 - s) ^ 2 / 2 := by
      rw [one_sub_div r2ne, div_pow, hr2sq]
    have e4 : s / Real.sqrt 2 * (t / Real.sqrt 2) * c = s * t * c / 2 := by
      rw [div_mul_div_comm, ← pow_two, hr2sq]
      ring
    have sc := scalar_lower (s / Real.sqrt 2) (t / Real.sqrt 2) c X
      (div_nonneg s0 hr2pos.le) (div_nonneg t0 hr2pos.le) c0
      (by rw [e4]; linarith)
      (by rw [e1, e2]; exact hX')
      (by rw [div_le_one hr2pos]; exact hs.le)
    rw [e3] at sc
    linarith
  refine ⟨fun hs => key a b a0 b0 abc hXabc hs, fun hs => ?_⟩
  have abc' : 2 ≤ b * a * c := by
    rw [mul_comm b a]
    exact abc
  have hX' : (b - Real.sqrt 2) ^ 2 / 2 + (a - Real.sqrt 2) ^ 2 / 2 + (c - 1) ^ 2 ≤ X := by
    linarith
  exact key b a b0 a0 abc' hX' hs

/-- Each annular vector is twice `±u_k` or `±v_k`. -/
private theorem ann_frame_int : ∀ j : Fin 12, ∃ k : Fin 3, ∃ neg : Bool, ∃ isV : Bool,
    ∀ i : Fin 3, annTwice j i =
      2 * (if neg then -1 else 1) * (if isV then frameVZ k i else frameUZ k i) := by
  decide

theorem ann_frame (A : Mat) (j : Fin 12) :
    ∃ k : Fin 3, nrm (A.mulVec (ann j)) = nrm (A.mulVec (frameU k)) ∨
      nrm (A.mulVec (ann j)) = nrm (A.mulVec (frameV k)) := by
  obtain ⟨k, neg, isV, h⟩ := ann_frame_int j
  have hv : ann j = (if neg then -1 else 1 : ℝ) • (if isV then frameV k else frameU k) := by
    funext i
    have hi := h i
    unfold ann
    rw [hi]
    cases neg <;> cases isV <;> simp [frameU, frameV, castVec] <;> ring
  refine ⟨k, ?_⟩
  rw [hv]
  cases neg <;> cases isV <;> simp [Matrix.mulVec_neg, nrm_neg]

/-! ### The lower length (2) at the annular shell -/

/-- **Stage5b (2) at `t = √2`.** If `det A = 1`, `U` is orthogonal and
`100‖A − U‖²_F + 200|h|² ≤ d♯`, every annular image `A e_j + χ h` has length at
least `13/10`. -/
theorem annular_far (A U : Mat) (hU : U.transpose * U = 1) (hdet : A.det = 1) (hv : Vec)
    (hq : 100 * frobSq (A - U) + 200 * sq hv ≤ dSharp) (j : Fin 12) (χ : Bool) :
    13 / 10 ≤ nrm (A.mulVec (ann j) + (if χ then hv else 0)) := by
  have hr2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr2b : 13 / 10 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hX0 : 0 ≤ frobSq (A - U) := frobSq_nonneg _
  have hy0 : 0 ≤ nrm hv := nrm_nonneg _
  have hy2 : nrm hv ^ 2 = sq hv := nrm_sq hv
  have key : nrm (A.mulVec (ann j)) < Real.sqrt 2 →
      3 * (Real.sqrt 2 - nrm (A.mulVec (ann j))) ^ 2 ≤ 4 * frobSq (A - U) := by
    obtain ⟨k, hk⟩ := ann_frame A j
    have fl := frame_lower A U hU hdet k
    rcases hk with hk | hk
    · rw [hk]
      exact fl.1
    · rw [hk]
      exact fl.2
  have tri : nrm (A.mulVec (ann j)) - nrm hv ≤
      nrm (A.mulVec (ann j) + (if χ then hv else 0)) := by
    cases χ
    · simp only [Bool.false_eq_true, ite_false, add_zero]
      linarith
    · simp only [ite_true]
      exact nrm_sub_le _ _
  have hq' : 100 * frobSq (A - U) + 200 * nrm hv ^ 2 ≤
      600 / 11 * (Real.sqrt 2 - 13 / 10) ^ 2 := by
    rw [hy2]
    exact hq
  -- abstract
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, nrm (A.mulVec (ann j)) = ℓ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, nrm hv = y := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, frobSq (A - U) = X := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, Real.sqrt 2 = r := ⟨_, rfl⟩
  rw [hℓ] at key tri
  rw [hy] at tri hy0 hq'
  rw [hX] at key hX0 hq'
  rw [hr] at key hq' hr2sq hr2b
  suffices 13 / 10 ≤ ℓ - y by linarith
  have Dpos : 0 < r - 13 / 10 := by linarith
  by_cases hl : r ≤ ℓ
  · have yD : y ^ 2 ≤ (r - 13 / 10) ^ 2 := by nlinarith
    have yle : y ≤ r - 13 / 10 := by nlinarith
    linarith
  · push Not at hl
    have k3 := key hl
    have h75 : 75 * (r - ℓ) ^ 2 + 200 * y ^ 2 ≤ 600 / 11 * (r - 13 / 10) ^ 2 := by nlinarith
    have hgy : ((r - ℓ) + y) ^ 2 ≤ (r - 13 / 10) ^ 2 := by
      nlinarith [sq_nonneg (15 * (r - ℓ) - 40 * y)]
    have gle : (r - ℓ) + y ≤ r - 13 / 10 := by nlinarith
    linarith

theorem annularWeight_eq_zero {v : Vec} (h : 13 / 10 ≤ nrm v) : annularWeight v = 0 := by
  unfold annularWeight
  have h1 : 13 - 10 * Real.sqrt (sq v) ≤ 0 := by
    unfold nrm at h
    linarith
  exact max_eq_left ((min_le_right _ _).trans h1)

/-! ### The cutoff theorem -/

/-- Below the cutoff the annular penalty vanishes. -/
theorem annPhi_eq_zero (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (n : IntVec)
    (ok : registrationCheck B N U f0 = true) (hN : det3Q N = 1) (p : Chart)
    (hv : (chartPoint p).Valid)
    (hq : regCost N U (fun i => f0 i + (n i : ℚ)) p ≤ dSharp) :
    annPhi N (fun i => f0 i + (n i : ℚ)) p = 0 := by
  unfold registrationCheck at ok
  obtain ⟨-, -, hUU, -⟩ := of_decide_eq_true ok
  have UU : (ofQ U).transpose * ofQ U = 1 := ofQ_orth U hUU
  have detA : (chartBasis p * ofQ N).det = 1 := by
    rw [Matrix.det_mul, ofQ_det N hN, mul_one]
    exact hv.1
  rw [regCost_eq] at hq
  apply Finset.sum_eq_zero
  intro j _
  apply annularWeight_eq_zero
  rw [annImage_eq]
  exact annular_far (chartBasis p * ofQ N) (ofQ U) UU detA _ hq j (annOdd N j)

/-- **The registered defect bound up to the Stage5b cutoff.** For a registration
passing `registrationCheck` with `det N = 1`, an integer wrap `n` and a valid
chart point whose registered cost is at most `d♯`, the actual capped defect is at
most the registered cost. -/
theorem defect_le_regCost_cutoff (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (n : IntVec)
    (ok : registrationCheck B N U f0 = true) (hN : det3Q N = 1) (p : Chart)
    (hv : (chartPoint p).Valid)
    (hq : regCost N U (fun i => f0 i + (n i : ℚ)) p ≤ dSharp) :
    defect (chartPoint p) ≤ regCost N U (fun i => f0 i + (n i : ℚ)) p := by
  have h := defect_le_annulus B N U f0 n ok p
  rw [annPhi_eq_zero B N U f0 n ok hN p hv hq, add_zero] at h
  exact h

/-! ### Rational tests of `c ≤ d♯` -/

/-- An exact test of `0 ≤ c ≤ d♯`: `0 ≤ c` and, with `u = 11c/600`,
`u ≤ 369/100` and `(369/100 − u)² ≥ 1352/100`. The last two say
`369/100 − u ≥ (26/10)√2`, that is `u ≤ (√2 − 13/10)²`; so for `c ≥ 0` they hold
exactly when `c ≤ d♯`. -/
def cutoffOk (c : ℚ) : Bool :=
  decide (0 ≤ c) && decide (11 * c / 600 ≤ 369 / 100) &&
    decide (1352 / 100 ≤ (369 / 100 - 11 * c / 600) ^ 2)

theorem cutoffOk_sound {c : ℚ} (h : cutoffOk c = true) : (c : ℝ) ≤ dSharp := by
  simp only [cutoffOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, h1⟩, h2⟩ := h
  have h1r : 11 * (c : ℝ) / 600 ≤ 369 / 100 := by
    have hq : ((11 * c / 600 : ℚ) : ℝ) ≤ ((369 / 100 : ℚ) : ℝ) := Rat.cast_le.mpr h1
    push_cast at hq
    linarith
  have h2r : (1352 / 100 : ℝ) ≤ (369 / 100 - 11 * (c : ℝ) / 600) ^ 2 := by
    have hq : ((1352 / 100 : ℚ) : ℝ) ≤ (((369 / 100 - 11 * c / 600) ^ 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr h2
    push_cast at hq
    linarith
  have hr2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have step : 26 / 10 * Real.sqrt 2 ≤ 369 / 100 - 11 * (c : ℝ) / 600 := by
    by_contra hc
    push Not at hc
    have p1 : 0 < 26 / 10 * Real.sqrt 2 - (369 / 100 - 11 * (c : ℝ) / 600) := by linarith
    have r2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have p2 : 0 < 26 / 10 * Real.sqrt 2 + (369 / 100 - 11 * (c : ℝ) / 600) := by linarith
    nlinarith [mul_pos p1 p2]
  have hu : 11 * (c : ℝ) / 600 ≤ (Real.sqrt 2 - 13 / 10) ^ 2 := by nlinarith
  unfold dSharp
  linarith

/-- A rational just below `d♯ ≈ 0.7115311544`. -/
def dSharpQ : ℚ := 711531 / 1000000

theorem cutoffOk_dSharpQ : cutoffOk dSharpQ = true := by decide +kernel

theorem dSharpQ_le : (dSharpQ : ℝ) ≤ dSharp := cutoffOk_sound cutoffOk_dSharpQ

/-- `⌊2⁹⁶ d♯⌋`, for checkers at the fixed-point scale `2⁹⁶`. -/
def dSharpZ : ℤ := 56373305931680625969332615839

theorem cutoffOk_dSharpZ : cutoffOk ((dSharpZ : ℚ) / 2 ^ 96) = true := by decide +kernel

theorem dSharpZ_le : ((((dSharpZ : ℚ) / 2 ^ 96 : ℚ)) : ℝ) ≤ dSharp :=
  cutoffOk_sound cutoffOk_dSharpZ

end BccSharp.Coulomb.CompactCover.JLeaf.Cutoff
