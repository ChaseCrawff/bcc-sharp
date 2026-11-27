import BccSharp.TwoSite.GlobalRegister
import BccSharp.TwoSite.GlobalAttain
import BccSharp.Cover.JLeafDefect

set_option autoImplicit false

/-! # The relative defect bound about a half-translation anchor

For a valid two-site configuration `q` with basis `R`, a half class `f₀` and an
integer wrap `n`, put `a = anchorOf q f₀` (a Bravais lattice) and
`h = R (f − f₀ − n)`. Then

  `D(q) ≤ D(a) + 200 |h|²` whenever `D(a) + 200 |h|² ≤ 1/2`

(`defect_transport`). The proof takes an optimal defect trial at the anchor
(`cappedDefect_attained`); `GlobalInputs.Trial.core` registers it: a basis
`A` with `lattice (A · bccPrimitive) = lattice R ∪ (R f₁ + lattice R)` and raw
cost `4‖A − O‖² + 8|R(f₀ − f₁)|²`. The cost bound and the period separation
force `f₁ = f₀`. Every star image `A sⱼ` then lies in the even coset `lattice R`
or the odd coset `R f₀ + lattice R`; the odd labels are exactly those of a
nonzero coset character (`labelParity`), eight of them, balanced. Moving the
odd images by `h` gives a trial at `q` of raw cost `4‖A − O‖² + 8|h|²`
(`registered_cost`), and under the cost bound it matches every lifted
neighbour of `q` (as in `JLeaf.defect_le_regCost`), so no annular weight
enters. Neither the Stage5b catalogue nor the registration theorem's uniqueness is used.

The hypotheses are the period separation of `q` and the coset separation of
the anchor, `|R(m + f₀)| > 1/2` for every integer `m`. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb
open BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.CompactCover.JLeaf (nrm nrm_nonneg nrm_sq nrm_add_le nrm_sub_le nrm_neg
  nrm_zero nrm_mulVec_lower nrm_mulVec_upper frobSq_nonneg star_sq_bounds star_gap bcc_norm BCCInt half_sq
  half_eq_star)

/-! ### The BCC lattice in twice-integer coordinates -/

def bccTwice (z : IntVec) : IntVec := ![-z 0 + z 1 + z 2, z 0 - z 1 + z 2, z 0 + z 1 - z 2]

theorem bccTwice_bcc (z : IntVec) : BCCInt (bccTwice z) := by
  unfold BCCInt bccTwice
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  omega

theorem bccPrimitive_mulVec (z : IntVec) :
    bccPrimitive.mulVec (castVec z) = fun i => ((bccTwice z i : ℤ) : ℝ) / 2 := by
  funext i
  fin_cases i <;>
    simp [bccPrimitive, Constants.Reference.naturalBasis, Matrix.mulVec, dotProduct, castVec,
      Fin.sum_univ_three, bccTwice] <;> ring

/-- A point `A e` of `lattice (A · bccPrimitive)` is zero, a star image, or
has `|e|² ≥ 2`. -/
theorem bcc_point_cases (z : IntVec) :
    bccPrimitive.mulVec (castVec z) = 0 ∨ (∃ j, bccPrimitive.mulVec (castVec z) = star j) ∨
      2 ≤ sq (bccPrimitive.mulVec (castVec z)) := by
  rw [bccPrimitive_mulVec]
  by_cases h0 : bccTwice z = 0
  · left
    funext i
    simp [h0]
  by_cases hs : ∃ j, bccTwice z = starTwice j
  · obtain ⟨j, hj⟩ := hs
    exact Or.inr (Or.inl ⟨j, half_eq_star _ j hj⟩)
  push Not at hs
  right; right
  have n8 := bcc_norm (bccTwice z) (bccTwice_bcc z) h0 hs
  rw [half_sq]
  have : (8 : ℝ) ≤ ((bccTwice z 0 ^ 2 + bccTwice z 1 ^ 2 + bccTwice z 2 ^ 2 : ℤ) : ℝ) := by exact_mod_cast n8
  linarith

/-! ### The coset parity of a registered basis -/

section Parity
variable (R A : Mat) (f₀ : Vec)

/-- The parity of a point of `lattice R ∪ (R f₀ + lattice R)`. -/
def oddC (v : Vec) : Prop := v ∉ lattice R

theorem lattice_add {u v : Vec} (hu : u ∈ lattice R) (hv : v ∈ lattice R) : u + v ∈ lattice R := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact ⟨a + b, by
    show R.mulVec (castVec (a + b)) = R.mulVec (castVec a) + R.mulVec (castVec b)
    rw [castVec_add, Matrix.mulVec_add]⟩

theorem lattice_sub {u v : Vec} (hu : u ∈ lattice R) (hv : v ∈ lattice R) : u - v ∈ lattice R := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact ⟨a - b, by
    show R.mulVec (castVec (a - b)) = R.mulVec (castVec a) - R.mulVec (castVec b)
    rw [castVec_sub', Matrix.mulVec_sub]⟩

theorem lattice_smul (k : ℤ) {u : Vec} (hu : u ∈ lattice R) : (k : ℝ) • u ∈ lattice R := by
  obtain ⟨a, rfl⟩ := hu
  refine ⟨k • a, ?_⟩
  show R.mulVec (castVec (k • a)) = (k : ℝ) • R.mulVec (castVec a)
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [castVec]

theorem lattice_zero : (0 : Vec) ∈ lattice R := ⟨0, by
  show R.mulVec (castVec 0) = 0
  rw [castVec_zero, Matrix.mulVec_zero]⟩

end Parity

/-- Every star image lies in a coset; the odd labels are those of a coset
character, eight of them and balanced. -/
theorem registered_parity (R A : Mat) (f₀ : Vec) (half : HalfClass f₀)
    (hinj : Function.Injective R.mulVec)
    (hlat : lattice (A * bccPrimitive) = lattice R ∪ translate (R.mulVec f₀) (lattice R)) :
    ∃ ε : Fin 14 → ℝ, (∀ j, ε j = 0 ∨ ε j = 1) ∧ (∑ j, ε j = 8) ∧
      (∀ k : Fin 3, ∑ j, ε j * star j k = 0) ∧
      ∀ j, (ε j = 0 → A.mulVec (star j) ∈ lattice R) ∧
        (ε j = 1 → A.mulVec (star j) ∈ translate (R.mulVec f₀) (lattice R)) := by
  set M := A * bccPrimitive with hM
  set t := R.mulVec f₀ with ht
  obtain ⟨m₀, hm₀⟩ := half.1
  -- `2t ∈ lattice R`, `t ∉ lattice R`
  have h2t : t + t ∈ lattice R := ⟨m₀, by
    show R.mulVec (castVec m₀) = t + t
    rw [← hm₀, two_smul, Matrix.mulVec_add]⟩
  have htn : t ∉ lattice R := by
    rintro ⟨n, hn⟩
    exact half.2 n (hinj hn).symm
  -- the columns of `M` and their cosets
  have hstar (j : Fin 14) : A.mulVec (star j) = M.mulVec (castVec (primitiveLabel j)) := by
    rw [hM, ← Matrix.mulVec_mulVec, bccPrimitive_label]
  have inM (z : IntVec) : M.mulVec (castVec z) ∈ lattice R ∪ translate t (lattice R) := by
    rw [← hlat]; exact ⟨z, rfl⟩
  -- coset coordinates of the three basis columns
  have colCoset (k : Fin 3) : ∃ (a : IntVec) (e : ℤ), (e = 0 ∨ e = 1) ∧
      M.mulVec (castVec (fun i => if i = k then (1 : ℤ) else 0)) = R.mulVec (castVec a) + (e : ℝ) • t := by
    rcases inM (fun i => if i = k then (1 : ℤ) else 0) with ⟨a, ha⟩ | ⟨y, ⟨a, rfl⟩, hy⟩
    · exact ⟨a, 0, Or.inl rfl, by rw [← ha]; simp⟩
    · exact ⟨a, 1, Or.inr rfl, by rw [hy]; simp⟩
  choose a e he hcol using colCoset
  -- every lattice point of `M`
  have point (z : IntVec) : M.mulVec (castVec z) =
      R.mulVec (castVec (z 0 • a 0 + z 1 • a 1 + z 2 • a 2)) + ((z 0 * e 0 + z 1 * e 1 + z 2 * e 2 : ℤ) : ℝ) • t := by
    have hz : castVec z = (z 0 : ℝ) • castVec (fun i => if i = (0 : Fin 3) then (1 : ℤ) else 0) +
        (z 1 : ℝ) • castVec (fun i => if i = (1 : Fin 3) then (1 : ℤ) else 0) +
        (z 2 : ℝ) • castVec (fun i => if i = (2 : Fin 3) then (1 : ℤ) else 0) := by
      funext i
      fin_cases i <;> simp [castVec]
    rw [hz, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hcol 0, hcol 1, hcol 2]
    have ca : castVec (z 0 • a 0 + z 1 • a 1 + z 2 • a 2) =
        (z 0 : ℝ) • castVec (a 0) + (z 1 : ℝ) • castVec (a 1) + (z 2 : ℝ) • castVec (a 2) := by
      funext i; simp [castVec]
    rw [ca, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul]
    push_cast
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- a point is even iff its coset count is even
  have evenOdd (b : IntVec) (N : ℤ) :
      (N % 2 = 0 → R.mulVec (castVec b) + (N : ℝ) • t ∈ lattice R) ∧
      (N % 2 = 1 → R.mulVec (castVec b) + (N : ℝ) • t ∈ translate t (lattice R) ∧
        R.mulVec (castVec b) + (N : ℝ) • t ∉ lattice R) := by
    have hN : N = 2 * (N / 2) + N % 2 := by omega
    have hNr : (N : ℝ) = 2 * ((N / 2 : ℤ) : ℝ) + ((N % 2 : ℤ) : ℝ) := by exact_mod_cast hN
    have key : (N : ℝ) • t = ((N / 2 : ℤ) : ℝ) • (t + t) + ((N % 2 : ℤ) : ℝ) • t := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hNr]
      ring
    have l1 : R.mulVec (castVec b) + ((N / 2 : ℤ) : ℝ) • (t + t) ∈ lattice R :=
      lattice_add R ⟨b, rfl⟩ (lattice_smul R _ h2t)
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · rw [key, h0]
      simpa [← add_assoc] using l1
    · rw [key, h1]
      have e : R.mulVec (castVec b) + (((N / 2 : ℤ) : ℝ) • (t + t) + ((1 : ℤ) : ℝ) • t) =
          (R.mulVec (castVec b) + ((N / 2 : ℤ) : ℝ) • (t + t)) + t := by simp; abel
      rw [e]
      refine ⟨⟨_, l1, rfl⟩, fun hin => htn ?_⟩
      have := lattice_sub R hin l1
      rwa [add_sub_cancel_left] at this
  -- the character
  set cB : Fin 3 → Bool := fun k => decide (e k = 1) with hcB
  have hcB1 (k : Fin 3) : (if cB k then (1 : ℤ) else 0) = e k := by
    rcases he k with h | h <;> simp [hcB, h]
  have hsum (j : Fin 14) : (∑ i : Fin 3, (if cB i then primitiveLabel j i else 0)) =
      primitiveLabel j 0 * e 0 + primitiveLabel j 1 * e 1 + primitiveLabel j 2 * e 2 := by
    rw [Fin.sum_univ_three]
    have g (i : Fin 3) : (if cB i then primitiveLabel j i else 0) = primitiveLabel j i * e i := by
      rw [← hcB1 i]; split_ifs <;> simp
    rw [g 0, g 1, g 2]
  -- a nonzero character
  have hne : ∃ k, cB k = true := by
    by_contra! hall
    have e0 (k : Fin 3) : e k = 0 := by
      have hk := hall k
      simp only [hcB, ne_eq, decide_eq_true_eq] at hk
      rcases he k with h | h
      · exact h
      · exact absurd h hk
    -- then every point of `M` is even, but `t` is a point of `M`
    have tin : t ∈ lattice M := by
      rw [hlat]
      exact Or.inr ⟨0, lattice_zero R, by rw [zero_add]⟩
    obtain ⟨z, hz⟩ := tin
    have hz' := point z
    rw [e0 0, e0 1, e0 2] at hz'
    simp only [mul_zero, add_zero, Int.cast_zero, zero_smul] at hz'
    exact htn ⟨_, (hz.symm.trans hz').symm⟩
  -- the parities of the labels
  let ε : Fin 14 → ℝ := fun j => if labelParity cB j then 1 else 0
  refine ⟨ε, fun j => by by_cases h : labelParity cB j <;> simp [ε, h], ?_, ?_, ?_⟩
  · rw [Finset.sum_boole, labelParity_count cB hne]; norm_num
  · intro k
    have h := labelParity_balance cB k
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : labelParity cB j <;> simp [ε, hj]
  · intro j
    have hp := point (primitiveLabel j)
    set N := primitiveLabel j 0 * e 0 + primitiveLabel j 1 * e 1 + primitiveLabel j 2 * e 2 with hNdef
    have lp : labelParity cB j = decide (N % 2 = 1) := by
      unfold labelParity; rw [hsum j]
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · have hpar : labelParity cB j = false := by
        by_contra hc; simp only [Bool.not_eq_false] at hc; simp [ε, hc] at h0
      rw [lp] at hpar
      have heven : N % 2 = 0 := by
        have := Int.emod_two_eq_zero_or_one N
        simp only [decide_eq_false_iff_not] at hpar
        omega
      rw [hstar j, hp]
      exact (evenOdd _ N).1 heven
    · have hpar : labelParity cB j = true := by
        by_contra hc; simp only [Bool.not_eq_true] at hc; simp [ε, hc] at h1
      rw [lp] at hpar
      have hodd : N % 2 = 1 := by simpa using hpar
      rw [hstar j, hp]
      exact ((evenOdd _ N).2 hodd).1

/-! ### The transported trial -/

theorem defect_transport (q : TwoSite) (hq : q.Valid)
    (hsep₁ : ∀ n : IntVec, n ≠ 0 → (5 / 8 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n)))
    (f₀ : Vec) (half : HalfClass f₀)
    (asep : ∀ n : IntVec, (1 / 2 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec n + f₀)))
    (n : IntVec)
    (small : defect (anchorOf q f₀) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) ≤ 1 / 2) :
    defect q ≤ defect (anchorOf q f₀) + 200 * sq (q.basis.mulVec (q.offset - f₀ - castVec n)) := by
  set R := q.basis with hR
  set a := anchorOf q f₀ with haDef
  have ha : a.Valid := anchor_valid q hq f₀ half
  have hsepA : separated a := ⟨hsep₁, asep⟩
  have hinj : Function.Injective R.mulVec := basis_injective q hq
  set D := defect a with hDdef
  set h : Vec := R.mulVec (q.offset - f₀ - castVec n) with hh
  have hb0 : 0 ≤ sq h := sq_nonnegative h
  have hD1 : cappedDefect (neighbors a) < 1 := by
    show defect a < 1
    linarith
  -- an optimal trial at the anchor
  obtain ⟨O, hO, σ, hσ⟩ := cappedDefect_attained (twoSite_neighbors_finite a ha) hD1
  have htail : 0 ≤ ∑' v : ↥(neighbors a), if v ∈ Set.range σ then (0 : ℝ) else annularWeight v.val := by
    apply tsum_nonneg
    intro v
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  have htrial : 25 * ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) ≤ D := by
    have e : defectTrial O σ = D := hσ
    unfold defectTrial at e
    linarith
  have hDhalf : D ≤ 1 / 2 := by linarith only [small, hb0]
  have hsmall : ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) < 1 / 25 := by
    linarith only [htrial, hDhalf]
  have hmem : ∀ j, (σ j : Vec) ∈ a.points := by
    intro j
    have := (σ j).property.1
    simpa only [zero_add] using this
  let T : Trial a := ⟨O, hO, fun j => (σ j : Vec), hmem, hsmall⟩
  obtain ⟨A, f₁, _hdetA, half₁, hlat, hcost⟩ := T.core ha hsepA
  -- the registered half class is the anchor's
  have hcost' : 100 * frobSq (A - O) + 200 * sq (R.mulVec (f₀ - f₁)) ≤ D := by
    have e : 25 * ∑ j, sq (T.err j) ≤ D := htrial
    rw [hcost] at e
    have e2 : sq (a.basis.mulVec (a.offset - f₁)) = sq (R.mulVec (f₀ - f₁)) := rfl
    rw [e2] at e
    linarith only [e]
  have hf : f₁ = f₀ := by
    obtain ⟨m, hm⟩ := half.1
    obtain ⟨m', hm'⟩ := half₁.1
    by_cases hz : m - m' = 0
    · have : (2 : ℝ) • f₀ = (2 : ℝ) • f₁ := by rw [hm, hm', sub_eq_zero.mp hz]
      exact (smul_right_injective Vec (two_ne_zero) this).symm
    · have hs := hsep₁ _ hz
      have e : R.mulVec (castVec (m - m')) = (2 : ℝ) • R.mulVec (f₀ - f₁) := by
        rw [castVec_sub', ← hm, ← hm', ← smul_sub, Matrix.mulVec_smul]
      rw [e, sq_smul] at hs
      have hf0 := frobSq_nonneg (A - O)
      nlinarith
  rw [hf] at hlat
  have hlatR : lattice (A * bccPrimitive) = lattice R ∪ translate (R.mulVec f₀) (lattice R) := hlat
  -- the parity of the star images
  obtain ⟨ε, h01, hcount, hbal, hcos⟩ := registered_parity R A f₀ half hinj hlatR
  -- the transported vectors
  set y : Fin 14 → Vec := fun j => A.mulVec (star j) + ε j • h with hy
  set X := frobSq (A - O) with hX
  set Y := sq h with hY
  have hX0 : 0 ≤ X := frobSq_nonneg _
  have hXY : 100 * X + 200 * Y ≤ 1 / 2 := by
    have : 200 * sq (R.mulVec (f₀ - f₀)) = 0 := by simp [sq]
    have hc := hcost'
    rw [hf] at hc
    linarith
  set x := Real.sqrt X with hx
  set yy := Real.sqrt Y with hyy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ yy := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = X := Real.sq_sqrt hX0
  have hy2 : yy ^ 2 = Y := Real.sq_sqrt hb0
  have hxb : x ≤ 3 / 40 := by
    rw [hx, Real.sqrt_le_left (by norm_num)]
    linarith
  have hyb : yy ≤ 1 / 20 := by
    rw [hyy, Real.sqrt_le_left (by norm_num)]
    linarith
  have hny : nrm h = yy := rfl
  set s2 := Real.sqrt 2 with hs2d
  have hs2 : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs20 : 0 ≤ s2 := Real.sqrt_nonneg _
  have hs2b : 707 / 500 ≤ s2 := by
    rw [hs2d, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have csq : (s2 * x + yy) ^ 2 ≤ 1 / 80 := by
    have e1 : (x - 2 * s2 * yy) ^ 2 = x ^ 2 - 4 * s2 * x * yy + 4 * s2 ^ 2 * yy ^ 2 := by ring
    have e2 : (s2 * x + yy) ^ 2 = s2 ^ 2 * x ^ 2 + 2 * s2 * x * yy + yy ^ 2 := by ring
    rw [hs2] at e1 e2
    nlinarith [sq_nonneg (x - 2 * s2 * yy), hx2, hy2, hXY]
  have key : s2 * x + yy ≤ 1119 / 10000 := by
    nlinarith [csq, mul_nonneg hs20 hx0, hy0]
  have far : 13 / 10 < (1 - x) * s2 - yy := by linarith
  have UU : O.transpose * O = 1 := hO.1
  have lowerA : ∀ v : Vec, (1 - x) * nrm v ≤ nrm (A.mulVec v) := nrm_mulVec_lower A O UU
  have upperA : ∀ v : Vec, nrm (A.mulVec v) ≤ (1 + x) * nrm v := nrm_mulVec_upper A O UU
  have chiNorm : ∀ j, nrm (ε j • h) ≤ yy := by
    intro j
    rcases h01 j with e | e <;> rw [e]
    · rw [zero_smul, nrm_zero]; exact hy0
    · rw [one_smul]; exact le_of_eq hny
  have starNrm : ∀ j : Fin 14, Real.sqrt (3 / 4) ≤ nrm (star j) ∧ nrm (star j) ≤ 1 := by
    intro j
    obtain ⟨lo, hi⟩ := JLeaf.star_sq_bounds j
    exact ⟨Real.sqrt_le_sqrt lo, by rw [nrm, Real.sqrt_le_left (by norm_num)]; linarith⟩
  have r34 : 866 / 1000 ≤ Real.sqrt (3 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  -- the images are lifted neighbours of `q`
  have ySmall : ∀ j, sq (y j) < (13 / 10) ^ 2 := by
    intro j
    have t := nrm_add_le (A.mulVec (star j)) (ε j • h)
    have u := upperA (star j)
    have c := chiNorm j
    have s := (starNrm j).2
    have m : (1 + x) * nrm (star j) ≤ (1 + x) * 1 := mul_le_mul_of_nonneg_left s (by linarith only [hx0])
    have bound : nrm (y j) ≤ 9 / 8 := by
      show nrm (A.mulVec (star j) + ε j • h) ≤ 9 / 8
      linarith only [t, u, c, m, hxb, hyb]
    rw [← nrm_sq]
    nlinarith only [bound, nrm_nonneg (y j)]
  have yNe : ∀ j, y j ≠ 0 := by
    intro j e0
    have t := nrm_sub_le (A.mulVec (star j)) (ε j • h)
    have l := lowerA (star j)
    have c := chiNorm j
    have s := (starNrm j).1
    have z : nrm (A.mulVec (star j) + ε j • h) = 0 := by
      have : A.mulVec (star j) + ε j • h = 0 := e0
      rw [this, nrm_zero]
    have m : (1 - x) * (866 / 1000) ≤ (1 - x) * nrm (star j) :=
      mul_le_mul_of_nonneg_left (r34.trans s) (by linarith only [hxb])
    linarith only [t, l, c, z, m, hxb, hyb]
  have yInj : ∀ i j, y i = y j → i = j := by
    intro i j e
    by_contra hij
    have gap := star_gap i j hij
    have e' : A.mulVec (star i) + ε i • h = A.mulVec (star j) + ε j • h := e
    have d : A.mulVec (star i - star j) = ε j • h - ε i • h := by
      rw [Matrix.mulVec_sub, sub_eq_sub_iff_add_eq_add, e', add_comm]
    have l := lowerA (star i - star j)
    have ndist : Real.sqrt (3 / 4) ≤ nrm (star i - star j) := Real.sqrt_le_sqrt gap
    have rhs : nrm (ε j • h - ε i • h) ≤ yy := by
      rcases h01 i with ei | ei <;> rcases h01 j with ej | ej <;> rw [ei, ej]
      · simp only [zero_smul, sub_self, nrm_zero]; exact hy0
      · simp only [one_smul, zero_smul, sub_zero]; exact le_of_eq hny
      · simp only [one_smul, zero_smul, zero_sub, nrm_neg]; exact le_of_eq hny
      · simp only [sub_self, nrm_zero]; exact hy0
    rw [d] at l
    have m : (1 - x) * (866 / 1000) ≤ (1 - x) * nrm (star i - star j) :=
      mul_le_mul_of_nonneg_left (r34.trans ndist) (by linarith only [hxb])
    linarith only [l, m, rhs, hxb, hyb]
  have yMem : ∀ j, y j ∈ q.points := by
    intro j
    rcases h01 j with e | e
    · have hl := (hcos j).1 e
      show A.mulVec (star j) + ε j • h ∈ q.points
      rw [e, zero_smul, add_zero]
      exact Or.inl hl
    · obtain ⟨w, ⟨ℓ, rfl⟩, hw⟩ := (hcos j).2 e
      show A.mulVec (star j) + ε j • h ∈ q.points
      rw [e, one_smul, hw, hh]
      right
      refine ⟨R.mulVec (castVec (ℓ - n)), ⟨ℓ - n, rfl⟩, ?_⟩
      rw [castVec_sub', Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_sub]
      abel
  have yNb : ∀ j, y j ∈ neighbors q := fun j => ⟨by simpa using yMem j, yNe j, ySmall j⟩
  let σ' : Fin 14 ↪ ↥(neighbors q) := ⟨fun j => ⟨y j, yNb j⟩, fun i j e => yInj i j (congrArg Subtype.val e)⟩
  -- every lifted neighbour of `q` is matched
  have farImage : ∀ z : IntVec, bccPrimitive.mulVec (castVec z) ≠ 0 →
      (∀ j, bccPrimitive.mulVec (castVec z) ≠ star j) →
      (1 - x) * s2 ≤ nrm (A.mulVec (bccPrimitive.mulVec (castVec z))) := by
    intro z hz0 hzs
    rcases bcc_point_cases z with h0 | ⟨j, hj⟩ | h2
    · exact absurd h0 hz0
    · exact absurd hj (hzs j)
    · have ne : s2 ≤ nrm (bccPrimitive.mulVec (castVec z)) := Real.sqrt_le_sqrt h2
      have l := lowerA (bccPrimitive.mulVec (castVec z))
      have m : (1 - x) * s2 ≤ (1 - x) * nrm (bccPrimitive.mulVec (castVec z)) :=
        mul_le_mul_of_nonneg_left ne (by linarith only [hxb])
      linarith only [l, m]
  have inLattice : ∀ w : Vec, w ∈ lattice R ∪ translate (R.mulVec f₀) (lattice R) →
      ∃ z : IntVec, w = A.mulVec (bccPrimitive.mulVec (castVec z)) := by
    intro w hw
    rw [← hlatR] at hw
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, by rw [← hz, Matrix.mulVec_mulVec]⟩
  have matched : ∀ v ∈ neighbors q, ∃ j, y j = v := by
    intro v hvn
    obtain ⟨hpt, hv0, hvs⟩ := hvn
    rw [zero_add] at hpt
    have big : ∀ t : ℝ, 13 / 10 < t → t ≤ nrm v → False := by
      intro t ht tv
      have lt : (13 / 10 : ℝ) < nrm v := lt_of_lt_of_le ht tv
      have sqv : (13 / 10 : ℝ) ^ 2 < nrm v ^ 2 := pow_lt_pow_left₀ lt (by norm_num) (by norm_num)
      rw [nrm_sq] at sqv
      exact absurd hvs (not_lt.mpr sqv.le)
    rcases hpt with hl | ht
    · -- an even point
      obtain ⟨z, hz⟩ := inLattice v (Or.inl hl)
      rcases bcc_point_cases z with h0 | ⟨j, hj⟩ | _
      · exact absurd (by rw [hz, h0, Matrix.mulVec_zero]) hv0
      · rw [hj] at hz
        refine ⟨j, ?_⟩
        rcases h01 j with e | e
        · show A.mulVec (star j) + ε j • h = v
          rw [e, zero_smul, add_zero, hz]
        · -- an odd image cannot be even
          exfalso
          obtain ⟨w, hw, hwe⟩ := (hcos j).2 e
          have hin : A.mulVec (star j) ∈ lattice R := by rw [← hz]; exact hl
          rw [hwe] at hin
          have := lattice_sub R hin hw
          rw [add_sub_cancel_left] at this
          have htn : R.mulVec f₀ ∉ lattice R := by
            rintro ⟨k, hk⟩; exact half.2 k (hinj hk).symm
          exact htn this
      · have hz0 : bccPrimitive.mulVec (castVec z) ≠ 0 := by
          intro e0; apply hv0; rw [hz, e0, Matrix.mulVec_zero]
        by_cases hs : ∃ j, bccPrimitive.mulVec (castVec z) = star j
        · obtain ⟨j, hj⟩ := hs
          rw [hj] at hz
          refine ⟨j, ?_⟩
          rcases h01 j with e | e
          · show A.mulVec (star j) + ε j • h = v
            rw [e, zero_smul, add_zero, hz]
          · exfalso
            obtain ⟨w, hw, hwe⟩ := (hcos j).2 e
            have hin : A.mulVec (star j) ∈ lattice R := by rw [← hz]; exact hl
            rw [hwe] at hin
            have := lattice_sub R hin hw
            rw [add_sub_cancel_left] at this
            have htn : R.mulVec f₀ ∉ lattice R := by
              rintro ⟨k, hk⟩; exact half.2 k (hinj hk).symm
            exact htn this
        · push Not at hs
          have fi := farImage z hz0 hs
          rw [← hz] at fi
          exact (big _ (by linarith) fi).elim
    · -- an odd point: `v − h` is an odd point of the anchor lattice
      obtain ⟨u, ⟨ℓ, rfl⟩, hu⟩ := ht
      have hvh : v - h ∈ translate (R.mulVec f₀) (lattice R) := by
        refine ⟨R.mulVec (castVec (ℓ + n)), ⟨ℓ + n, rfl⟩, ?_⟩
        rw [hu, hh, castVec_add, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub]
        abel
      obtain ⟨z, hz⟩ := inLattice (v - h) (Or.inr hvh)
      have htn : R.mulVec f₀ ∉ lattice R := by
        rintro ⟨k, hk⟩; exact half.2 k (hinj hk).symm
      have notEven : v - h ∉ lattice R := by
        intro hin
        obtain ⟨w, hw, hwe⟩ := hvh
        rw [hwe] at hin
        have := lattice_sub R hin hw
        rw [add_sub_cancel_left] at this
        exact htn this
      have hz0 : bccPrimitive.mulVec (castVec z) ≠ 0 := by
        intro e0
        apply notEven
        rw [hz, e0, Matrix.mulVec_zero]
        exact lattice_zero R
      by_cases hs : ∃ j, bccPrimitive.mulVec (castVec z) = star j
      · obtain ⟨j, hj⟩ := hs
        rw [hj] at hz
        refine ⟨j, ?_⟩
        rcases h01 j with e | e
        · exfalso
          exact notEven (by rw [hz]; exact (hcos j).1 e)
        · show A.mulVec (star j) + ε j • h = v
          rw [e, one_smul, ← hz]
          abel
      · push Not at hs
        have fi := farImage z hz0 hs
        rw [← hz] at fi
        have t := nrm_add_le v (-h)
        rw [nrm_neg, ← sub_eq_add_neg, hny] at t
        exact (big ((1 - x) * s2 - yy) far (by linarith only [t, fi])).elim
  -- the trial cost
  have zeroTail : (∑' v : ↥(neighbors q), if v ∈ Set.range σ' then (0 : ℝ) else annularWeight v.val) = 0 := by
    have hz : (fun v : ↥(neighbors q) => if v ∈ Set.range σ' then (0 : ℝ) else annularWeight v.val) =
        fun _ => 0 := by
      funext v
      have hm : v ∈ Set.range σ' := by
        obtain ⟨j, hj⟩ := matched v.val v.property
        exact ⟨j, Subtype.ext hj⟩
      simp [hm]
    rw [hz, tsum_zero]
  have trialCost : defectTrial O σ' = 100 * X + 200 * Y := by
    unfold defectTrial
    rw [zeroTail, add_zero]
    have terms : ∀ j, (σ' j : Vec) - O.mulVec (star j) = (A - O).mulVec (star j) + ε j • h := by
      intro j
      show A.mulVec (star j) + ε j • h - O.mulVec (star j) = _
      rw [Matrix.sub_mulVec]
      abel
    simp_rw [terms]
    rw [registered_cost (A - O) h ε h01 hcount hbal]
    ring
  have bdd : BddBelow (defectCandidates (neighbors q)) := by
    refine ⟨0, fun c hc => ?_⟩
    rcases Set.mem_insert_iff.mp hc with rfl | ⟨U', _, τ, rfl⟩
    · norm_num
    · apply add_nonneg
      · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => sq_nonnegative _))
      · apply tsum_nonneg
        intro v
        split_ifs
        · exact le_rfl
        · exact le_max_left _ _
  have memC : defectTrial O σ' ∈ defectCandidates (neighbors q) :=
    Set.mem_insert_of_mem _ ⟨O, hO, σ', rfl⟩
  have le := csInf_le bdd memC
  show cappedDefect (neighbors q) ≤ D + 200 * Y
  rw [trialCost] at le
  have : 100 * X ≤ D := by
    have hc := hcost'
    rw [hf] at hc
    have : 200 * sq (R.mulVec (f₀ - f₀)) = 0 := by simp [sq]
    linarith
  unfold cappedDefect
  linarith

end BccSharp.Coulomb.CompactCover.Layered
