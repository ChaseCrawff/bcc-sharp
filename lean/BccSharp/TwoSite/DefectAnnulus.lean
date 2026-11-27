import BccSharp.Cover.JLeafDefect

set_option autoImplicit false

/-! # The registered defect bound with annulus penalties

`defect_le_regCost` (`BccSharp.Cover.JLeafDefect`) bounds the actual capped defect
by the registered cost `q = 100‖A − U‖²_F + 200|h|²` (`A = R N`,
`h = R (f − f₀ − n)`) when `q ≤ 1/2`: then every lifted neighbour is one of
the fourteen matched star images. This module also admits the next reference shell. Below `q = 1` the only lifted
neighbours other than the star images are images of the twelve reference
vectors of length `√2`, the annular vectors `(±1, ±1, 0)` and their
permutations. Their annular weights add up to `Φ`, and the actual defect is at
most `min 1 (q + Φ)`.

* `annPhi N w p` is the sum of the twelve annular weights
  `annularWeight (A e_j + χ_j h)`. The parity `χ_j` of `e_j` is read from the
  rational vector `N e_j` (`annOdd`). The image is
  `annImage N w j p = R (annVec N w j + χ_j f)` with the rational
  `annVec = N e_j − χ_j w` (`annImage_eq`).
* `defect_le_annulus`: `defect ≤ q + Φ` at every chart point (validity is not
  used), for every registration that passes `registrationCheck` and every
  integer wrap. If
  `q ≥ 1` this is the cap `defect ≤ 1`. If `q < 1`, then `x = ‖A − U‖_F < 1/10`
  and `|h| < 71/1000`. The fourteen star images are then pairwise distinct
  lifted neighbours, as in `defect_le_regCost`. A point `z/2` of the BCC
  lattice that is neither `0`, nor a star vector, nor an annular vector has
  `|z|² ≥ 11` (`bcc_norm11`), so its image has length at least
  `(1 − x)√(11/4) − |h| > 13/10`. Every unmatched lifted neighbour is
  therefore an annular image, and the unmatched sum in the trial cost is at
  most `Φ`.
* `defect_le_annulus_min`: `defect ≤ min 1 (q + Φ)`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf.Cutoff
open BccSharp
open BccSharp.Coulomb.CompactCover.DirectRoute (offset)

/-! ### The twelve annular reference vectors -/

/-- Twice the twelve reference vectors of squared length `2` in the
conventional BCC lattice: `(±2, ±2, 0)` and its coordinate permutations. -/
def annTwice : Fin 12 → IntVec :=
  ![![2, 2, 0], ![2, -2, 0], ![-2, 2, 0], ![-2, -2, 0],
    ![2, 0, 2], ![2, 0, -2], ![-2, 0, 2], ![-2, 0, -2],
    ![0, 2, 2], ![0, 2, -2], ![0, -2, 2], ![0, -2, -2]]

/-- The annular reference vector `e_j`. -/
def ann (j : Fin 12) : Vec := fun i => (annTwice j i : ℝ) / 2

/-- The annular reference vector `e_j` with rational coordinates. -/
def annQ (j : Fin 12) (i : Fin 3) : ℚ := (annTwice j i : ℚ) / 2

theorem annQ_cast (j : Fin 12) (i : Fin 3) : ((annQ j i : ℚ) : ℝ) = ann j i := by
  simp [annQ, ann]

theorem sq_eq_three (v : Vec) : sq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [sq, Fin.sum_univ_three]

private theorem bcc_small11 :
    ∀ a b c : ℤ, -3 ≤ a → a ≤ 3 → -3 ≤ b → b ≤ 3 → -3 ≤ c → c ≤ 3 →
      (a - b) % 2 = 0 → (b - c) % 2 = 0 → a ^ 2 + b ^ 2 + c ^ 2 < 11 →
      (a = 0 ∧ b = 0 ∧ c = 0) ∨
        (∃ j : Fin 14, starTwice j 0 = a ∧ starTwice j 1 = b ∧ starTwice j 2 = c) ∨
        (∃ j : Fin 12, annTwice j 0 = a ∧ annTwice j 1 = b ∧ annTwice j 2 = c) := by
  intro a b c ha1 ha2 hb1 hb2 hc1 hc2
  interval_cases a <;> interval_cases b <;> interval_cases c <;> decide

/-- A nonzero point of `2 · BCC` that is neither twice a star vector nor twice
an annular vector has squared length at least `11`. -/
theorem bcc_norm11 (z : IntVec) (hz : BCCInt z) (h0 : z ≠ 0) (hs : ∀ j, z ≠ starTwice j)
    (ha : ∀ j, z ≠ annTwice j) : 11 ≤ z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  by_contra hlt
  push Not at hlt
  have bnd : ∀ i : Fin 3, -3 ≤ z i ∧ z i ≤ 3 := by
    intro i
    have hi : z i ^ 2 < 11 := by
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2)]
    constructor
    · by_contra h
      push Not at h
      have : z i ≤ -4 := by omega
      nlinarith
    · by_contra h
      push Not at h
      have : 4 ≤ z i := by omega
      nlinarith
  rcases bcc_small11 (z 0) (z 1) (z 2) (bnd 0).1 (bnd 0).2 (bnd 1).1 (bnd 1).2 (bnd 2).1
    (bnd 2).2 hz.1 hz.2 hlt with ⟨a, b, c⟩ | ⟨j, a, b, c⟩ | ⟨j, a, b, c⟩
  · apply h0
    funext i
    fin_cases i <;> simp [a, b, c]
  · apply hs j
    funext i
    fin_cases i <;> simp [a, b, c]
  · apply ha j
    funext i
    fin_cases i <;> simp [a, b, c]

theorem half_eq_ann (z : IntVec) (j : Fin 12) (h : z = annTwice j) :
    (fun i => ((z i : ℤ) : ℝ) / 2) = ann j := by
  funext i
  rw [h]
  rfl

/-! ### Annular labels of a registration -/

/-- `N e_j` for the annular vector `e_j`. -/
def annCoord (N : Fin 3 → Fin 3 → ℚ) (j : Fin 12) (i : Fin 3) : ℚ :=
  ∑ k, N i k * annQ j k

/-- Odd annular labels: `N e_j` is not integral. -/
def annOdd (N : Fin 3 → Fin 3 → ℚ) (j : Fin 12) : Bool :=
  !(isIntQ (annCoord N j 0) && isIntQ (annCoord N j 1) && isIntQ (annCoord N j 2))

/-- The rational part `N e_j − χ_j w` of the chart preimage `annVec + χ_j f`
of the annular image. -/
def annVec (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (j : Fin 12) (i : Fin 3) : ℚ :=
  annCoord N j i - (if annOdd N j then w i else 0)

/-- The annular image `R (annVec + χ_j f) = A e_j + χ_j h` (`annImage_eq`). -/
def annImage (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (j : Fin 12) (p : Chart) : Vec :=
  (chartBasis p).mulVec (fun i => img (annVec N w j) (annOdd N j) p i)

/-- The annular penalty `Φ`: the sum of the twelve annular weights. -/
def annPhi (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (p : Chart) : ℝ :=
  ∑ j : Fin 12, annularWeight (annImage N w j p)

theorem annularWeight_nonneg (v : Vec) : 0 ≤ annularWeight v := le_max_left _ _

theorem annPhi_nonneg (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (p : Chart) :
    0 ≤ annPhi N w p :=
  Finset.sum_nonneg (fun _ _ => annularWeight_nonneg _)

theorem annCoord_cast (N : Fin 3 → Fin 3 → ℚ) (j : Fin 12) :
    (ofQ N).mulVec (ann j) = fun i => ((annCoord N j i : ℚ) : ℝ) := by
  funext i
  rw [ofQ_mulVec]
  unfold annCoord
  push_cast
  simp only [annQ_cast]

theorem annImage_eq (N : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (j : Fin 12) (p : Chart) :
    annImage N w j p = (chartBasis p * ofQ N).mulVec (ann j) +
      (if annOdd N j then
        (chartBasis p).mulVec ((chartPoint p).offset - fun i => (w i : ℝ)) else 0) := by
  have e1 : (fun i => img (annVec N w j) (annOdd N j) p i) =
      (ofQ N).mulVec (ann j) +
        (if annOdd N j then (chartPoint p).offset - (fun i => (w i : ℝ)) else 0) := by
    funext i
    rw [annCoord_cast]
    have eo := DirectRoute.offset_eq p i
    simp only [img, annVec]
    cases annOdd N j
    · simp
    · simp [eo]
      ring
  rw [annImage, e1, Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
  cases annOdd N j
  · simp
  · simp

/-- The parity of an annular vector that lies in `B ℤ³` or in `B (ℤ³ + f₀)`. -/
theorem annOdd_eq (N : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ)
    (hf0 : ∃ i : Fin 3, isIntQ (f0 i) = false) (j : Fin 12) (κ : IntVec) (c : Bool)
    (e : (ofQ N).mulVec (ann j) = castVec κ + (if c then (fun i => (f0 i : ℝ)) else 0)) :
    annOdd N j = c := by
  rw [annCoord_cast] at e
  have hq : ∀ i, annCoord N j i = (κ i : ℚ) + (if c then f0 i else 0) := by
    intro i
    have hi := congrFun e i
    cases c
    · simp only [castVec, Bool.false_eq_true, ite_false, Pi.add_apply, Pi.zero_apply,
        add_zero] at hi
      simp only [Bool.false_eq_true, ite_false, add_zero]
      exact_mod_cast hi
    · simp only [castVec, ite_true, Pi.add_apply] at hi
      simp only [ite_true]
      exact_mod_cast hi
  cases c
  · have h' : ∀ i, annCoord N j i = (κ i : ℚ) := by
      intro i
      simpa using hq i
    simp [annOdd, h', isIntQ_int]
  · by_contra hne
    have hall : (isIntQ (annCoord N j 0) && isIntQ (annCoord N j 1) &&
        isIntQ (annCoord N j 2)) = true := by
      cases hb : (isIntQ (annCoord N j 0) && isIntQ (annCoord N j 1) && isIntQ (annCoord N j 2))
      · exfalso
        apply hne
        simp [annOdd, hb]
      · rfl
    simp only [Bool.and_eq_true] at hall
    obtain ⟨⟨i0, i1⟩, i2⟩ := hall
    have hint : ∀ i : Fin 3, isIntQ (annCoord N j i) = true := by
      intro i
      fin_cases i
      · exact i0
      · exact i1
      · exact i2
    obtain ⟨i, hi⟩ := hf0
    have e1 := isIntQ_cast (hint i)
    have hfi : f0 i = (((annCoord N j i).num - κ i : ℤ) : ℚ) := by
      have hqi := hq i
      simp only [ite_true] at hqi
      push_cast
      rw [e1]
      linarith
    rw [hfi, isIntQ_int] at hi
    exact absurd hi (by decide)

/-! ### Main theorem -/

/-- **The registered defect bound with annulus penalties.** For a registration
passing `registrationCheck`, an integer wrap `n` and any chart point, the
actual capped defect is at most the registered cost plus the annular penalty
`Φ` of the twelve annular images. -/
theorem defect_le_annulus (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (n : IntVec)
    (ok : registrationCheck B N U f0 = true) (p : Chart) :
    defect (chartPoint p) ≤ regCost N U (fun i => f0 i + (n i : ℚ)) p +
      annPhi N (fun i => f0 i + (n i : ℚ)) p := by
  have phi0 := annPhi_nonneg N (fun i => f0 i + (n i : ℚ)) p
  by_cases bigq : 1 ≤ regCost N U (fun i => f0 i + (n i : ℚ)) p
  · have := (defect_range (chartPoint p)).2
    linarith
  push Not at bigq
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
  have hXY : 100 * X + 200 * Y < 1 := by
    rw [cost] at bigq
    exact bigq
  set x := Real.sqrt X with hx
  set y := Real.sqrt Y with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hxb : x ≤ 1 / 10 := by
    rw [hx, Real.sqrt_le_left (by norm_num)]
    linarith only [hXY, hY0]
  have hyb : y ≤ 71 / 1000 := by
    rw [hy, Real.sqrt_le_left (by norm_num)]
    linarith only [hXY, hX0]
  have hny : nrm h = y := rfl
  set s11 := Real.sqrt (11 / 4) with hs11d
  have hs11b : 1658 / 1000 ≤ s11 := by
    rw [hs11d, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have far : 13 / 10 < (1 - x) * s11 - y := by
    have m : (1 - x) * (1658 / 1000) ≤ (1 - x) * s11 :=
      mul_le_mul_of_nonneg_left hs11b (by linarith only [hxb])
    linarith only [m, hxb, hyb]
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
  set σv : Fin 14 → Vec := fun j => A.mulVec (star j) + (if labelOdd N j then h else 0)
    with hσv
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
    have bound : nrm (σv j) ≤ 6 / 5 := by
      show nrm (A.mulVec (star j) + (if labelOdd N j then h else 0)) ≤ 6 / 5
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
  -- Points of `2 · BCC` outside the star and the annulus.
  have farImage : ∀ (e : Vec) (z : IntVec), BCCInt z → z ≠ 0 → (∀ j, z ≠ starTwice j) →
      (∀ j, z ≠ annTwice j) → e = (fun i => ((z i : ℤ) : ℝ) / 2) →
      (1 - x) * s11 ≤ nrm (A.mulVec e) := by
    intro e z hz z0 zs za he
    have n11 := bcc_norm11 z hz z0 zs za
    have se : 11 / 4 ≤ sq e := by
      rw [he, half_sq]
      have : (11 : ℝ) ≤ ((z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 : ℤ) : ℝ) := by exact_mod_cast n11
      linarith only [this]
    have ne : s11 ≤ nrm e := Real.sqrt_le_sqrt se
    have l := lowerA e
    have m : (1 - x) * s11 ≤ (1 - x) * nrm e :=
      mul_le_mul_of_nonneg_left ne (by linarith only [hxb])
    linarith only [l, m]
  -- Every lifted neighbour is a star image or an annular image.
  have matched : ∀ v ∈ neighbors (chartPoint p),
      (∃ j, σv j = v) ∨ ∃ j, annImage N (fun i => f0 i + (n i : ℚ)) j p = v := by
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
        left
        refine ⟨j, ?_⟩
        show A.mulVec (star j) + (if labelOdd N j then h else 0) = v
        rw [odd, ← es, Ae]
        simp
      · push Not at hs
        by_cases ha : ∃ j, zVec B f0 k false = annTwice j
        · obtain ⟨j, hj⟩ := ha
          have ea : e = ann j := by
            rw [he, ze]
            exact half_eq_ann _ j hj
          have odd := annOdd_eq N f0 hf0 j k false (by rw [← ea]; exact Ne)
          right
          refine ⟨j, ?_⟩
          rw [annImage_eq, odd, ← ea]
          simp only [Bool.false_eq_true, ite_false, add_zero]
          exact Ae
        · push Not at ha
          have z0 : zVec B f0 k false ≠ 0 := by
            intro z0
            apply hv0
            rw [← Ae, he, ze, z0]
            have : (fun i : Fin 3 => (((0 : IntVec) i : ℤ) : ℝ) / 2) = 0 := by
              funext i
              simp
            rw [this, Matrix.mulVec_zero]
          have fi := farImage e (zVec B f0 k false) (zVec_bcc B f0 k false hcol hzf) z0 hs ha
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
        left
        refine ⟨j, ?_⟩
        show A.mulVec (star j) + (if labelOdd N j then h else 0) = v
        rw [odd, ← es]
        simpa using Ae
      · push Not at hs
        by_cases ha : ∃ j, zVec B f0 κ true = annTwice j
        · obtain ⟨j, hj⟩ := ha
          have ea : e = ann j := by
            rw [he, ze]
            exact half_eq_ann _ j hj
          have odd := annOdd_eq N f0 hf0 j κ true (by rw [← ea]; exact Ne)
          right
          refine ⟨j, ?_⟩
          rw [annImage_eq, odd, ← ea]
          simp only [ite_true]
          exact Ae
        · push Not at ha
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
          have fi := farImage e (zVec B f0 κ true) (zVec_bcc B f0 κ true hcol hzf) z0 hs ha
            (by rw [he, ze])
          have t := nrm_sub_le (A.mulVec e) h
          rw [Ae, hny] at t
          exact (big ((1 - x) * s11 - y) far (by linarith only [t, fi])).elim
  -- The trial cost.
  have trialEq : defectTrial Ur σ = 100 * X + 200 * Y +
      ∑' v : ↥(neighbors (chartPoint p)),
        (if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val) := by
    unfold defectTrial
    congr 1
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
  -- The unmatched sum is at most the annular penalty.
  set W : Fin 12 → ℝ := fun j => annularWeight (annImage N (fun i => f0 i + (n i : ℚ)) j p)
    with hW
  have W0 : ∀ j, 0 ≤ W j := fun j => annularWeight_nonneg _
  have tailLe : (∑' v : ↥(neighbors (chartPoint p)),
      (if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val)) ≤ ∑ j : Fin 12, W j := by
    apply Real.tsum_le_of_sum_le
    · intro v
      by_cases hvr : v ∈ Set.range σ
      · simp [hvr]
      · simp [hvr, annularWeight_nonneg]
    · intro s
      have dom : ∀ v : ↥(neighbors (chartPoint p)),
          (if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val) ≤
            ∑ j : Fin 12,
              (if v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p then W j else 0) := by
        intro v
        have nn : ∀ j : Fin 12, 0 ≤
            (if v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p then W j else 0) := by
          intro j
          split_ifs
          · exact W0 j
          · exact le_rfl
        split_ifs with hσ
        · exact Finset.sum_nonneg (fun j _ => nn j)
        · rcases matched v.val v.property with ⟨j, hj⟩ | ⟨j, hj⟩
          · exact absurd ⟨j, Subtype.ext hj⟩ hσ
          · have hterm : (if v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p then W j
                else 0) = annularWeight v.val := by
              split_ifs with hc
              · show annularWeight (annImage N (fun i => f0 i + (n i : ℚ)) j p) =
                  annularWeight v.val
                rw [hj]
              · exact absurd hj.symm hc
            rw [← hterm]
            exact Finset.single_le_sum (fun j' _ => nn j') (Finset.mem_univ j)
      have atMostOne : ∀ j : Fin 12, ∑ v ∈ s,
          (if v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p then W j else 0) ≤ W j := by
        intro j
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hc : (s.filter (fun v : ↥(neighbors (chartPoint p)) =>
            v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          exact Subtype.ext (ha.2.trans hb.2.symm)
        have hcr : ((s.filter (fun v : ↥(neighbors (chartPoint p)) =>
            v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p)).card : ℝ) ≤ 1 := by
          exact_mod_cast hc
        nlinarith [W0 j]
      calc ∑ v ∈ s, (if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val)
          ≤ ∑ v ∈ s, ∑ j : Fin 12,
              (if v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p then W j else 0) :=
            Finset.sum_le_sum (fun v _ => dom v)
        _ = ∑ j : Fin 12, ∑ v ∈ s,
              (if v.val = annImage N (fun i => f0 i + (n i : ℚ)) j p then W j else 0) :=
            Finset.sum_comm
        _ ≤ ∑ j : Fin 12, W j := Finset.sum_le_sum (fun j _ => atMostOne j)
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
  have phiEq : annPhi N (fun i => f0 i + (n i : ℚ)) p = ∑ j : Fin 12, W j := rfl
  rw [cost, phiEq]
  unfold defect cappedDefect
  rw [trialEq] at le
  linarith

/-- `defect ≤ min 1 (q + Φ)`. -/
theorem defect_le_annulus_min (B N U : Fin 3 → Fin 3 → ℚ) (f0 : Fin 3 → ℚ) (n : IntVec)
    (ok : registrationCheck B N U f0 = true) (p : Chart) :
    defect (chartPoint p) ≤ min 1 (regCost N U (fun i => f0 i + (n i : ℚ)) p +
      annPhi N (fun i => f0 i + (n i : ℚ)) p) :=
  le_min (defect_range (chartPoint p)).2 (defect_le_annulus B N U f0 n ok p)

end BccSharp.Coulomb.CompactCover.JLeaf.Cutoff
