import BccSharp.TwoSite.GlobalDet

set_option autoImplicit false

/-! The registration of a nonsaturated two-site BCC defect, under the
two strict separations. A trial of raw cost below one pairs opposite
star labels with equal parity, fixes a nonzero half shift, registers all
fourteen labels exactly through a basis of the corrected Bravais lattice and
has exactly eight odd labels. The star second moment then gives the
registered cost formula. This discharges the `register` field of
`GlobalAnalyticInputs`. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.KZ

/-! ### Star labels -/

/-- The label of the opposite star vector. -/
def negLabel : Fin 14 → Fin 14 := ![7,6,5,4,3,2,1,0,9,8,11,10,13,12]

theorem star_negLabel (j : Fin 14) : star (negLabel j) = -star j := by
  funext i
  fin_cases j <;> fin_cases i <;> norm_num [negLabel, star]

theorem negLabel_negLabel : ∀ j : Fin 14, negLabel (negLabel j) = j := by decide

theorem negLabel_ne : ∀ j : Fin 14, negLabel j ≠ j := by decide

def negEquiv : Fin 14 ≃ Fin 14 :=
  ⟨negLabel, negLabel, negLabel_negLabel, negLabel_negLabel⟩

/-- The odd labels for the coset character with support `c`, in the
primitive BCC coordinates of the star. -/
def labelParity (c : Fin 3 → Bool) (j : Fin 14) : Bool :=
  decide ((∑ i : Fin 3, (if c i then primitiveLabel j i else 0)) % 2 = 1)

theorem labelParity_count : ∀ c : Fin 3 → Bool, (∃ i, c i = true) →
    (Finset.univ.filter (fun j => labelParity c j = true)).card = 8 := by
  decide

theorem labelParity_balance_int : ∀ c : Fin 3 → Bool, ∀ i : Fin 3,
    (∑ j : Fin 14, if labelParity c j then starTwice j i else 0) = 0 := by
  decide

theorem labelParity_balance (c : Fin 3 → Bool) (i : Fin 3) :
    (∑ j : Fin 14, if labelParity c j then star j i else 0) = 0 := by
  have hInt := labelParity_balance_int c i
  have hReal : (∑ j : Fin 14, if labelParity c j then (starTwice j i : ℝ) else 0) = 0 := by
    exact_mod_cast hInt
  have hHalf : ∀ j : Fin 14, (if labelParity c j then star j i else 0) =
      (1/2 : ℝ) * (if labelParity c j then (starTwice j i : ℝ) else 0) := by
    intro j
    split_ifs
    · rw [starTwice_eq]
      ring
    · ring
  rw [Finset.sum_congr rfl (fun j _ => hHalf j), ← Finset.mul_sum, hReal, mul_zero]

/-- Primitive coordinates of the three basis labels `6, 5, 3`. -/
def baseLabel : Fin 3 → Fin 14 := ![6,5,3]

theorem primitiveLabel_base : ∀ i k : Fin 3,
    primitiveLabel (baseLabel i) k = if i = k then 1 else 0 := by
  decide

/-! ### Vector identities -/

theorem sq_add_smul (u h : Vec) (t : ℝ) : sq (u + t • h) = sq u + 2 * t * dot u h + t^2 * sq h := by
  simp only [sq, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem sq_sub_smul (u h : Vec) (t : ℝ) : sq (u - t • h) = sq u - 2 * t * dot u h + t^2 * sq h := by
  simp only [sq, dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem dot_add_left' (a b h : Vec) : dot (a + b) h = dot a h + dot b h := by
  simp only [dot, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem dot_smul_left' (t : ℝ) (a h : Vec) : dot (t • a) h = t * dot a h := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem dot_self' (h : Vec) : dot h h = sq h := by
  simp only [dot, sq, Fin.sum_univ_three]
  ring

private theorem sum4_sq_le (w x y z : ℝ) : (w + x + y + z)^2 ≤ 4 * (w^2 + x^2 + y^2 + z^2) := by
  nlinarith [sq_nonneg (w - x), sq_nonneg (w - y), sq_nonneg (w - z), sq_nonneg (x - y),
    sq_nonneg (x - z), sq_nonneg (y - z)]

theorem sq_sum4_le (a b c d : Vec) : sq (a + b + c + d) ≤ 4 * (sq a + sq b + sq c + sq d) := by
  simp only [sq, Pi.add_apply, Fin.sum_univ_three]
  linarith [sum4_sq_le (a 0) (b 0) (c 0) (d 0), sum4_sq_le (a 1) (b 1) (c 1) (d 1),
    sum4_sq_le (a 2) (b 2) (c 2) (d 2)]

theorem sq_smul_le (t : ℝ) (ht : t^2 ≤ 1) (v : Vec) : sq (t • v) ≤ sq v := by
  rw [sq_smul]
  exact mul_le_of_le_one_left (sq_nonnegative v) ht

theorem sq_sub_lower (x h : Vec) : (2/3) * sq x - 2 * sq h ≤ sq (x - h) := by
  simp only [sq, Pi.sub_apply, Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 - 3 * h 0), sq_nonneg (x 1 - 3 * h 1), sq_nonneg (x 2 - 3 * h 2)]

theorem castVec_sub' (a b : IntVec) : castVec (a - b) = castVec a - castVec b := by
  funext i
  simp [castVec]

theorem sum_pair_le (F : Fin 14 → ℝ) (hF : ∀ j, 0 ≤ F j) (j : Fin 14) :
    F j + F (negLabel j) ≤ ∑ k, F k := by
  rw [← Finset.sum_pair (negLabel_ne j).symm]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hF k)

theorem sum_three_le (F : Fin 14 → ℝ) (hF : ∀ j, 0 ≤ F j) : F 6 + F 5 + F 3 ≤ ∑ k, F k := by
  have e : ∑ k ∈ ({6, 5, 3} : Finset (Fin 14)), F k = F 6 + F 5 + F 3 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [← e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hF k)

theorem sum_four_le (F : Fin 14 → ℝ) (hF : ∀ j, 0 ≤ F j) (j : Fin 14)
    (hj : j ≠ 6 ∧ j ≠ 5 ∧ j ≠ 3) : F j + F 6 + F 5 + F 3 ≤ ∑ k, F k := by
  have hmem : j ∉ ({6, 5, 3} : Finset (Fin 14)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact hj
  have e : ∑ k ∈ insert j ({6, 5, 3} : Finset (Fin 14)), F k = F j + F 6 + F 5 + F 3 := by
    rw [Finset.sum_insert hmem, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  rw [← e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hF k)

/-! ### Two-site points -/

theorem points_cases (q : TwoSite) {x : Vec} (hx : x ∈ q.points) :
    (∃ a : IntVec, x = q.basis.mulVec (castVec a)) ∨
      (∃ a : IntVec, x = q.basis.mulVec (castVec a + q.offset)) := by
  rcases hx with ⟨a, ha⟩ | ⟨_, ⟨a, rfl⟩, hx⟩
  · exact Or.inl ⟨a, ha.symm⟩
  · refine Or.inr ⟨a, ?_⟩
    rw [hx, Matrix.mulVec_add]

theorem basis_injective (q : TwoSite) (hq : q.Valid) : Function.Injective q.basis.mulVec := by
  have hu : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hq.1]; exact isUnit_one)
  exact Matrix.mulVec_injective_of_isUnit hu

theorem coset_ne (q : TwoSite) (hq : q.Valid) (a b : IntVec) :
    q.basis.mulVec (castVec a) ≠ q.basis.mulVec (castVec b + q.offset) := by
  intro h
  have e := basis_injective q hq h
  apply hq.2 (a - b)
  rw [castVec_sub', e]
  abel

/-- A lattice vector of squared length at most `(5/8)²` is zero. -/
theorem period_zero (q : TwoSite) (hsep : separated q) (a : IntVec)
    (h : sq (q.basis.mulVec (castVec a)) ≤ (5/8)^2) : a = 0 := by
  by_contra ha
  exact absurd (hsep.1 a ha) (not_lt.mpr h)

/-! ### A trial of raw cost below one -/

structure Trial (c : TwoSite) where
  O : Mat
  hO : proper O
  y : Fin 14 → Vec
  mem : ∀ j, y j ∈ c.points
  small : ∑ j, sq (y j - O.mulVec (star j)) < 1/25

namespace Trial

variable {c : TwoSite} (T : Trial c)

def err (j : Fin 14) : Vec := T.y j - T.O.mulVec (star j)

theorem err_small : ∑ j, sq (T.err j) < 1/25 := T.small

theorem pair_sum_eq (j : Fin 14) : T.y j + T.y (negLabel j) = T.err j + T.err (negLabel j) := by
  unfold err
  rw [star_negLabel, Matrix.mulVec_neg]
  abel

theorem pair_sum_small (j : Fin 14) : sq (T.y j + T.y (negLabel j)) < 2/25 := by
  rw [pair_sum_eq]
  have h1 := sq_add_le (T.err j) (T.err (negLabel j))
  have h2 := sum_pair_le (fun k => sq (T.err k)) (fun k => sq_nonnegative _) j
  have h3 := T.err_small
  linarith

def isOdd (j : Fin 14) : Prop := T.y j ∉ lattice c.basis

theorem even_cases (j : Fin 14) (h : ¬ T.isOdd j) :
    ∃ a : IntVec, T.y j = c.basis.mulVec (castVec a) := by
  have hm : T.y j ∈ lattice c.basis := not_not.mp h
  obtain ⟨a, ha⟩ := hm
  exact ⟨a, ha.symm⟩

theorem odd_cases (j : Fin 14) (h : T.isOdd j) :
    ∃ a : IntVec, T.y j = c.basis.mulVec (castVec a + c.offset) := by
  rcases points_cases c (T.mem j) with ⟨a, ha⟩ | hb
  · exact absurd ⟨a, ha.symm⟩ h
  · exact hb

theorem mixed_false (hsep : separated c) (j : Fin 14) (a b : IntVec)
    (ha : T.y j = c.basis.mulVec (castVec a + c.offset))
    (hb : T.y (negLabel j) = c.basis.mulVec (castVec b)) : False := by
  have hs := T.pair_sum_small j
  have he : T.y j + T.y (negLabel j) = c.basis.mulVec (castVec (a + b) + c.offset) := by
    rw [ha, hb, ← Matrix.mulVec_add, castVec_add]
    congr 1
    abel
  rw [he] at hs
  have := hsep.2 (a + b)
  linarith

theorem isOdd_negLabel (hsep : separated c) (j : Fin 14) :
    T.isOdd (negLabel j) ↔ T.isOdd j := by
  constructor
  · intro hn
    by_contra hj
    obtain ⟨a, ha⟩ := T.odd_cases (negLabel j) hn
    obtain ⟨b, hb⟩ := T.even_cases j hj
    have hb' : T.y (negLabel (negLabel j)) = c.basis.mulVec (castVec b) := by
      rw [negLabel_negLabel]
      exact hb
    exact T.mixed_false hsep (negLabel j) a b ha hb'
  · intro hj
    by_contra hn
    obtain ⟨a, ha⟩ := T.odd_cases j hj
    obtain ⟨b, hb⟩ := T.even_cases (negLabel j) hn
    exact T.mixed_false hsep j a b ha hb

theorem even_pair_zero (hsep : separated c) (j : Fin 14) (h : ¬ T.isOdd j) :
    T.y j + T.y (negLabel j) = 0 := by
  obtain ⟨a, ha⟩ := T.even_cases j h
  obtain ⟨b, hb⟩ := T.even_cases (negLabel j) (fun hn => h ((T.isOdd_negLabel hsep j).mp hn))
  have he : T.y j + T.y (negLabel j) = c.basis.mulVec (castVec (a + b)) := by
    rw [ha, hb, ← Matrix.mulVec_add, castVec_add]
  have hs := T.pair_sum_small j
  rw [he] at hs ⊢
  have hz := period_zero c hsep (a + b) (by linarith)
  rw [hz, castVec_zero, Matrix.mulVec_zero]

theorem odd_pair_coords (hsep : separated c) (j : Fin 14) (h : T.isOdd j) :
    ∃ l : IntVec, T.y j + T.y (negLabel j) = c.basis.mulVec (castVec l + (2:ℝ) • c.offset) := by
  obtain ⟨a, ha⟩ := T.odd_cases j h
  obtain ⟨b, hb⟩ := T.odd_cases (negLabel j) ((T.isOdd_negLabel hsep j).mpr h)
  refine ⟨a + b, ?_⟩
  rw [ha, hb, ← Matrix.mulVec_add, castVec_add, two_smul]
  congr 1
  abel

theorem odd_pair_common (hsep : separated c) (j k : Fin 14) (l m : IntVec)
    (hl : T.y j + T.y (negLabel j) = c.basis.mulVec (castVec l + (2:ℝ) • c.offset))
    (hm : T.y k + T.y (negLabel k) = c.basis.mulVec (castVec m + (2:ℝ) • c.offset)) : l = m := by
  have hd : c.basis.mulVec (castVec (l - m)) =
      (T.y j + T.y (negLabel j)) - (T.y k + T.y (negLabel k)) := by
    rw [hl, hm, ← Matrix.mulVec_sub, castVec_sub']
    congr 1
    abel
  have h1 := T.pair_sum_small j
  have h2 := T.pair_sum_small k
  have h3 := sq_sub_le (T.y j + T.y (negLabel j)) (T.y k + T.y (negLabel k))
  rw [← hd] at h3
  have hz := period_zero c hsep (l - m) (by linarith)
  exact sub_eq_zero.mp hz

end Trial

/-! ### The registered cost formula -/

theorem registered_cost (D : Mat) (h : Vec) (ε : Fin 14 → ℝ) (h01 : ∀ j, ε j = 0 ∨ ε j = 1)
    (hcount : ∑ j, ε j = 8) (hbal : ∀ k : Fin 3, ∑ j, ε j * star j k = 0) :
    ∑ j, sq (D.mulVec (star j) + ε j • h) = 4 * frobSq D + 8 * sq h := by
  have hsq : ∀ j, ε j ^ 2 = ε j := by
    intro j
    rcases h01 j with e | e <;> rw [e] <;> norm_num
  have e : ∀ j, sq (D.mulVec (star j) + ε j • h) =
      sq (D.mulVec (star j)) + 2 * (ε j * dot (D.mulVec (star j)) h) + ε j * sq h := by
    intro j
    rw [sq_add_smul, hsq]
    ring
  have hcross : ∑ j, ε j * dot (D.mulVec (star j)) h = 0 := by
    have e2 : ∀ j, ε j * dot (D.mulVec (star j)) h =
        (ε j * star j 0) * (D 0 0 * h 0 + D 1 0 * h 1 + D 2 0 * h 2) +
        (ε j * star j 1) * (D 0 1 * h 0 + D 1 1 * h 1 + D 2 1 * h 2) +
        (ε j * star j 2) * (D 0 2 * h 0 + D 1 2 * h 1 + D 2 2 * h 2) := by
      intro j
      simp only [dot, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    rw [Finset.sum_congr rfl (fun j _ => e2 j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hbal 0, hbal 1, hbal 2]
    ring
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    star_norm_sum, ← Finset.mul_sum, hcross, ← Finset.sum_mul, hcount]
  ring

theorem primitiveLabel_six : primitiveLabel 6 = ![1,0,0] := by decide
theorem primitiveLabel_five : primitiveLabel 5 = ![0,1,0] := by decide
theorem primitiveLabel_three : primitiveLabel 3 = ![0,0,1] := by decide

/-- Bound for an error combination with coefficients in `[-1,1]`. -/
theorem sq_comb_le (a b c d : Vec) (s t u : ℝ) (hs : s^2 ≤ 1) (ht : t^2 ≤ 1) (hu : u^2 ≤ 1) :
    sq (a - (s • b + t • c + u • d)) ≤ 4 * (sq a + sq b + sq c + sq d) := by
  have e : a - (s • b + t • c + u • d) = a + (-s) • b + (-t) • c + (-u) • d := by
    simp only [neg_smul]
    abel
  rw [e]
  have h1 := sq_sum4_le a ((-s) • b) ((-t) • c) ((-u) • d)
  have h2 := sq_smul_le (-s) (by rw [neg_sq]; exact hs) b
  have h3 := sq_smul_le (-t) (by rw [neg_sq]; exact ht) c
  have h4 := sq_smul_le (-u) (by rw [neg_sq]; exact hu) d
  linarith

theorem primitiveLabel_sq_le (j : Fin 14) (i : Fin 3) : ((primitiveLabel j i : ℤ) : ℝ)^2 ≤ 1 := by
  have h := primitiveLabel_range j i
  have h1 : ((primitiveLabel j i : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h.2
  have h2 : (-1 : ℝ) ≤ ((primitiveLabel j i : ℤ) : ℝ) := by exact_mod_cast h.1
  nlinarith

namespace Trial

variable {c : TwoSite} (T : Trial c)

/-- Indicator of the odd labels, as a real number and as an integer. -/
def eps (j : Fin 14) : ℝ := if T.isOdd j then 1 else 0
def epsZ (j : Fin 14) : ℤ := if T.isOdd j then 1 else 0

theorem eps01 (j : Fin 14) : T.eps j = 0 ∨ T.eps j = 1 := by
  unfold eps
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem eps_nonneg (j : Fin 14) : 0 ≤ T.eps j := by
  unfold eps
  split_ifs <;> norm_num

theorem eps_sq (j : Fin 14) : T.eps j ^ 2 = T.eps j := by
  unfold eps
  split_ifs <;> norm_num

theorem eps_eq_cast (j : Fin 14) : T.eps j = (T.epsZ j : ℝ) := by
  unfold eps epsZ
  split_ifs <;> simp

theorem eps_neg (hsep : separated c) (j : Fin 14) : T.eps (negLabel j) = T.eps j := by
  unfold eps
  by_cases hj : T.isOdd j
  · rw [ite_eq_left ((T.isOdd_negLabel hsep j).mpr hj), ite_eq_left hj]
  · rw [ite_eq_right (fun h => hj ((T.isOdd_negLabel hsep j).mp h)), ite_eq_right hj]

/-- The existence part of Steps 1–5 for one trial: the registered basis,
the half shift and the exact cost formula. the registration theorem's uniqueness statements are
not needed for `Registration` and are not formalized. -/
theorem core (hc : c.Valid) (hsep : separated c) :
    ∃ (A : Mat) (f₀ : Vec), A.det = 1 ∧ HalfClass f₀ ∧
      lattice (A * bccPrimitive) =
        lattice c.basis ∪ translate (c.basis.mulVec f₀) (lattice c.basis) ∧
      ∑ j, sq (T.err j) = 4 * frobSq (A - T.O) + 8 * sq (c.basis.mulVec (c.offset - f₀)) := by
  have hR : c.basis.det = 1 := hc.1
  have hsmall := T.err_small
  -- an odd label exists
  have hodd : ∃ j₀, T.isOdd j₀ := by
    by_contra! hnone
    have hmem : ∀ j, T.y j ∈ lattice c.basis := fun j => not_not.mp (hnone j)
    have h3 := sum_three_le (fun k => sq (T.err k)) (fun k => sq_nonnegative _)
    have hdet := det_columns_near T.O T.hO (T.y 6) (T.y 5) (T.y 3) (by
      show sq (T.err 6) + sq (T.err 5) + sq (T.err 3) < 1/25
      linarith)
    exact columns_integral_false c.basis hR _ _ _ (hmem 6) (hmem 5) (hmem 3) hdet.1 hdet.2
  obtain ⟨j₀, hj₀⟩ := hodd
  obtain ⟨l, hl⟩ := T.odd_pair_coords hsep j₀ hj₀
  have hpair : ∀ j, T.isOdd j →
      T.y j + T.y (negLabel j) = c.basis.mulVec (castVec l + (2:ℝ) • c.offset) := by
    intro j hj
    obtain ⟨m, hm⟩ := T.odd_pair_coords hsep j hj
    rw [hm, T.odd_pair_common hsep j₀ j l m hl hm]
  -- the half shift and the displacement
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Vec, f₀ = (-(1/2 : ℝ)) • castVec l := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : Vec, h = c.basis.mulVec (c.offset - f₀) := ⟨_, rfl⟩
  have h2h : c.basis.mulVec (castVec l + (2:ℝ) • c.offset) = (2:ℝ) • h := by
    rw [hhdef, ← Matrix.mulVec_smul]
    congr 1
    rw [hf₀]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  -- corrected labels in coordinates
  have hcoord : ∀ j, ∃ z : IntVec,
      T.y j - T.eps j • h = c.basis.mulVec (castVec z + (T.epsZ j : ℝ) • f₀) := by
    intro j
    by_cases hj : T.isOdd j
    · obtain ⟨a, ha⟩ := T.odd_cases j hj
      refine ⟨a, ?_⟩
      have e1 : T.eps j = 1 := by simp [eps, hj]
      have e2 : T.epsZ j = 1 := by simp [epsZ, hj]
      rw [e1, e2, one_smul, Int.cast_one, one_smul, ha, hhdef, ← Matrix.mulVec_sub]
      congr 1
      abel
    · obtain ⟨a, ha⟩ := T.even_cases j hj
      refine ⟨a, ?_⟩
      have e1 : T.eps j = 0 := by simp [eps, hj]
      have e2 : T.epsZ j = 0 := by simp [epsZ, hj]
      rw [e1, e2, zero_smul, sub_zero, Int.cast_zero, zero_smul, add_zero, ha]
  -- the corrected error sum
  have hεneg := T.eps_neg hsep
  have hdotsum : ∑ j, T.eps j * dot (T.err j) h = (∑ j, T.eps j) * sq h := by
    have hre : ∑ j, T.eps j * dot (T.err j) h = ∑ j, T.eps j * dot (T.err (negLabel j)) h := by
      rw [← Equiv.sum_comp negEquiv (fun j => T.eps j * dot (T.err j) h)]
      apply Finset.sum_congr rfl
      intro j _
      show T.eps (negLabel j) * dot (T.err (negLabel j)) h = T.eps j * dot (T.err (negLabel j)) h
      rw [hεneg]
    have hpt : ∀ j, T.eps j * (dot (T.err j) h + dot (T.err (negLabel j)) h) =
        T.eps j * (2 * sq h) := by
      intro j
      by_cases hj : T.isOdd j
      · rw [← dot_add_left', ← T.pair_sum_eq j, hpair j hj, h2h, dot_smul_left', dot_self']
      · have e1 : T.eps j = 0 := by simp [eps, hj]
        rw [e1, zero_mul, zero_mul]
    have hsum : ∑ j, T.eps j * dot (T.err j) h + ∑ j, T.eps j * dot (T.err (negLabel j)) h =
        2 * ((∑ j, T.eps j) * sq h) := by
      rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_add, hpt j]
      ring
    linarith
  have hI1 : ∑ j, sq (T.err j - T.eps j • h) = ∑ j, sq (T.err j) - (∑ j, T.eps j) * sq h := by
    have e : ∀ j, sq (T.err j - T.eps j • h) =
        sq (T.err j) - 2 * (T.eps j * dot (T.err j) h) + T.eps j * sq h := by
      intro j
      rw [sq_sub_smul, T.eps_sq j]
      ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, hdotsum]
    ring
  have hk2 : 2 ≤ ∑ j, T.eps j := by
    have hp := sum_pair_le T.eps T.eps_nonneg j₀
    have e1 : T.eps j₀ = 1 := by simp [eps, hj₀]
    have e2 : T.eps (negLabel j₀) = 1 := by rw [hεneg]; exact e1
    linarith
  have hsqh := sq_nonnegative h
  have he0 : ∑ j, sq (T.err j - T.eps j • h) < 1/25 - 2 * sq h := by
    rw [hI1]
    nlinarith
  have he0nn : ∀ j, 0 ≤ sq (T.err j - T.eps j • h) := fun j => sq_nonnegative _
  have hy0 : ∀ j, T.y j - T.eps j • h - T.O.mulVec (star j) = T.err j - T.eps j • h := by
    intro j
    unfold err
    abel
  -- the determinant of the three corrected basis labels
  obtain ⟨M, hMdef⟩ : ∃ M : Mat,
      M = columns (T.y 6 - T.eps 6 • h) (T.y 5 - T.eps 5 • h) (T.y 3 - T.eps 3 • h) := ⟨_, rfl⟩
  have hdetM : 0 < M.det ∧ M.det < 1 := by
    rw [hMdef]
    apply det_columns_near T.O T.hO
    rw [hy0, hy0, hy0]
    have h3 := sum_three_le (fun k => sq (T.err k - T.eps k • h)) he0nn
    linarith
  -- the half shift is a nonzero half period
  have h2f₀ : (2:ℝ) • f₀ = castVec (-l) := by
    rw [hf₀, smul_smul, castVec_neg]
    norm_num
  have hf₀nint : ∀ n : IntVec, f₀ ≠ castVec n := by
    intro n hn
    have hmem : ∀ j, T.y j - T.eps j • h ∈ lattice c.basis := by
      intro j
      obtain ⟨z, hz⟩ := hcoord j
      refine ⟨z + T.epsZ j • n, ?_⟩
      show c.basis.mulVec (castVec (z + T.epsZ j • n)) = T.y j - T.eps j • h
      rw [hz, hn]
      congr 1
      funext i
      simp [castVec]
    rw [hMdef] at hdetM
    exact columns_integral_false c.basis hR _ _ _ (hmem 6) (hmem 5) (hmem 3) hdetM.1 hdetM.2
  have half : HalfClass f₀ := ⟨⟨-l, h2f₀⟩, hf₀nint⟩
  -- the corrected Bravais lattice and its basis
  have hc' : (⟨c.basis, f₀⟩ : TwoSite).Valid := ⟨hR, hf₀nint⟩
  obtain ⟨model⟩ := primitive_anchor_exists ⟨c.basis, f₀⟩ hc' half
  have hPmem : ∀ j, T.y j - T.eps j • h ∈ lattice model.basis := by
    intro j
    rw [model.points]
    obtain ⟨z, hz⟩ := hcoord j
    rw [hz]
    by_cases hj : T.isOdd j
    · have e2 : (T.epsZ j : ℝ) = 1 := by simp [epsZ, hj]
      rw [e2, one_smul, Matrix.mulVec_add]
      exact Or.inr ⟨c.basis.mulVec (castVec z), ⟨z, rfl⟩, rfl⟩
    · have e2 : (T.epsZ j : ℝ) = 0 := by simp [epsZ, hj]
      rw [e2, zero_smul, add_zero]
      exact Or.inl ⟨z, rfl⟩
  have hbasis : M.det = 1/2 ∧ lattice M = lattice model.basis := by
    rw [hMdef]
    rw [hMdef] at hdetM
    exact columns_half_basis model.basis model.volume _ _ _ (hPmem 6) (hPmem 5)
      (hPmem 3) hdetM.1 hdetM.2
  -- every label is registered exactly, with the parity relation
  have hMv : ∀ v : IntVec, M.mulVec (castVec v) =
      (v 0 : ℝ) • (T.y 6 - T.eps 6 • h) + (v 1 : ℝ) • (T.y 5 - T.eps 5 • h) +
        (v 2 : ℝ) • (T.y 3 - T.eps 3 • h) := by
    intro v
    rw [hMdef, columns_mulVec]
    rfl
  have hreg : ∀ j, T.y j - T.eps j • h = M.mulVec (castVec (primitiveLabel j)) ∧
      (T.epsZ j - (primitiveLabel j 0 * T.epsZ 6 + primitiveLabel j 1 * T.epsZ 5 +
        primitiveLabel j 2 * T.epsZ 3)) % 2 = 0 := by
    intro j
    by_cases hb : j = 6 ∨ j = 5 ∨ j = 3
    · rcases hb with rfl | rfl | rfl
      · refine ⟨?_, ?_⟩
        · rw [hMv, primitiveLabel_six]
          simp
        · rw [primitiveLabel_six]
          simp
      · refine ⟨?_, ?_⟩
        · rw [hMv, primitiveLabel_five]
          simp
        · rw [primitiveLabel_five]
          simp
      · refine ⟨?_, ?_⟩
        · rw [hMv, primitiveLabel_three]
          simp
        · rw [primitiveLabel_three]
          simp
    have hj : j ≠ 6 ∧ j ≠ 5 ∧ j ≠ 3 := by
      simpa only [not_or] using hb
    obtain ⟨zj, hzj⟩ := hcoord j
    obtain ⟨z6, hz6⟩ := hcoord 6
    obtain ⟨z5, hz5⟩ := hcoord 5
    obtain ⟨z3, hz3⟩ := hcoord 3
    obtain ⟨Z, hZ⟩ : ∃ Z : IntVec, Z = zj - (primitiveLabel j 0 • z6 + primitiveLabel j 1 • z5 +
        primitiveLabel j 2 • z3) := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, m = T.epsZ j - (primitiveLabel j 0 * T.epsZ 6 +
        primitiveLabel j 1 * T.epsZ 5 + primitiveLabel j 2 * T.epsZ 3) := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : Vec,
        d = T.y j - T.eps j • h - M.mulVec (castVec (primitiveLabel j)) := ⟨_, rfl⟩
    -- the coordinates of the difference
    have hdc : d = c.basis.mulVec (castVec Z + (m : ℝ) • f₀) := by
      rw [hd, hMv, hzj, hz6, hz5, hz3, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
        ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_add, ← Matrix.mulVec_sub]
      congr 1
      funext i
      rw [hZ, hm]
      simp only [castVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Int.cast_add, Int.cast_sub, Int.cast_mul]
      ring
    -- the difference is small
    have hsj : star j = (primitiveLabel j 0 : ℝ) • star 6 + (primitiveLabel j 1 : ℝ) • star 5 +
        (primitiveLabel j 2 : ℝ) • star 3 := by
      rw [← bccPrimitive_label j, bccPrimitive_columns, columns_mulVec]
      rfl
    have hde : d = (T.err j - T.eps j • h) - ((primitiveLabel j 0 : ℝ) • (T.err 6 - T.eps 6 • h) +
        (primitiveLabel j 1 : ℝ) • (T.err 5 - T.eps 5 • h) +
        (primitiveLabel j 2 : ℝ) • (T.err 3 - T.eps 3 • h)) := by
      rw [hd, hMv]
      unfold err
      rw [hsj, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_smul]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hdsq : sq d < 4/25 - 8 * sq h := by
      rw [hde]
      have h1 := sq_comb_le (T.err j - T.eps j • h) (T.err 6 - T.eps 6 • h)
        (T.err 5 - T.eps 5 • h) (T.err 3 - T.eps 3 • h) _ _ _
        (primitiveLabel_sq_le j 0) (primitiveLabel_sq_le j 1) (primitiveLabel_sq_le j 2)
      have h2 := sum_four_le (fun k => sq (T.err k - T.eps k • h)) he0nn j hj
      linarith
    -- parity of the coefficient
    rcases Int.emod_two_eq_zero_or_one m with hm0 | hm1
    · have hm2 : m = 2 * (m / 2) := by omega
      have hcv : castVec Z + (m : ℝ) • f₀ = castVec (Z - (m / 2) • l) := by
        rw [hf₀]
        funext i
        have hm2' : (m : ℝ) = 2 * ((m / 2 : ℤ) : ℝ) := by exact_mod_cast hm2
        simp only [castVec, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
          Int.cast_sub, Int.cast_mul]
        rw [hm2']
        ring
      have hdz : d = c.basis.mulVec (castVec (Z - (m / 2) • l)) := by rw [hdc, hcv]
      have hz : Z - (m / 2) • l = 0 := by
        apply period_zero c hsep
        rw [← hdz]
        nlinarith
      have hd0 : d = 0 := by rw [hdz, hz, castVec_zero, Matrix.mulVec_zero]
      refine ⟨?_, ?_⟩
      · rw [hd] at hd0
        exact sub_eq_zero.mp hd0
      · rw [← hm]
        exact hm0
    · exfalso
      have hm2 : m = 2 * (m / 2) + 1 := by omega
      have hcv : castVec Z + (m : ℝ) • f₀ =
          (castVec (Z - (m / 2) • l) + c.offset) - (c.offset - f₀) := by
        rw [hf₀]
        funext i
        have hm2' : (m : ℝ) = 2 * ((m / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast hm2
        simp only [castVec, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
          Int.cast_sub, Int.cast_mul]
        rw [hm2']
        ring
      have hdz : d = c.basis.mulVec (castVec (Z - (m / 2) • l) + c.offset) - h := by
        rw [hdc, hcv, Matrix.mulVec_sub, hhdef]
      have hlow := sq_sub_lower (c.basis.mulVec (castVec (Z - (m / 2) • l) + c.offset)) h
      have hsep2 := hsep.2 (Z - (m / 2) • l)
      rw [← hdz] at hlow
      nlinarith
  -- parity of every label
  obtain ⟨cB, hcB⟩ : ∃ cB : Fin 3 → Bool, cB = fun i => decide (T.isOdd (baseLabel i)) :=
    ⟨_, rfl⟩
  have hpar : ∀ j, T.isOdd j ↔ labelParity cB j = true := by
    intro j
    have hm := (hreg j).2
    have hterm : ∀ (i : Fin 3) (k : Fin 14), baseLabel i = k →
        (if cB i then primitiveLabel j i else 0) = primitiveLabel j i * T.epsZ k := by
      intro i k hk
      subst hk
      by_cases hi : T.isOdd (baseLabel i)
      · simp [hcB, hi, epsZ]
      · simp [hcB, hi, epsZ]
    have hsum : (∑ i : Fin 3, (if cB i then primitiveLabel j i else 0)) =
        primitiveLabel j 0 * T.epsZ 6 + primitiveLabel j 1 * T.epsZ 5 +
          primitiveLabel j 2 * T.epsZ 3 := by
      rw [Fin.sum_univ_three, hterm 0 6 rfl, hterm 1 5 rfl, hterm 2 3 rfl]
    unfold labelParity
    rw [decide_eq_true_iff, hsum]
    by_cases hj : T.isOdd j
    · have e : T.epsZ j = 1 := by simp [epsZ, hj]
      rw [e] at hm
      exact ⟨fun _ => by omega, fun _ => hj⟩
    · have e : T.epsZ j = 0 := by simp [epsZ, hj]
      rw [e] at hm
      exact ⟨fun h' => absurd h' hj, fun _ => by omega⟩
  have hcBne : ∃ i, cB i = true := by
    by_contra! hall
    have hp := (hpar j₀).mp hj₀
    unfold labelParity at hp
    have hz : (∑ i : Fin 3, (if cB i then primitiveLabel j₀ i else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [hall i]
    rw [hz] at hp
    simp at hp
  have hcount : ∑ j, T.eps j = 8 := by
    have e : ∀ j, T.eps j = if labelParity cB j = true then (1:ℝ) else 0 := by
      intro j
      unfold eps
      by_cases hj : T.isOdd j
      · rw [ite_eq_left hj, ite_eq_left ((hpar j).mp hj)]
      · rw [ite_eq_right hj, ite_eq_right (fun h' => hj ((hpar j).mpr h'))]
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_boole, labelParity_count cB hcBne]
    norm_num
  have hbal : ∀ k : Fin 3, ∑ j, T.eps j * star j k = 0 := by
    intro k
    have e : ∀ j, T.eps j * star j k = if labelParity cB j then star j k else 0 := by
      intro j
      unfold eps
      by_cases hj : T.isOdd j
      · rw [ite_eq_left hj, ite_eq_left ((hpar j).mp hj), one_mul]
      · rw [ite_eq_right hj, ite_eq_right (fun h' => hj ((hpar j).mpr h')), zero_mul]
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    exact labelParity_balance cB k
  -- the registered linear map and the cost
  have hBpu : IsUnit bccPrimitive.det := by
    rw [bccPrimitive_det]
    norm_num
  obtain ⟨A, hAdef⟩ : ∃ A : Mat, A = M * bccPrimitive⁻¹ := ⟨_, rfl⟩
  have hAB : A * bccPrimitive = M := by
    rw [hAdef, mul_assoc, Matrix.nonsing_inv_mul _ hBpu, mul_one]
  have hdetA : A.det = 1 := by
    have e := congrArg Matrix.det hAB
    rw [Matrix.det_mul, bccPrimitive_det, hbasis.1] at e
    linarith
  have hAs : ∀ j, A.mulVec (star j) = T.y j - T.eps j • h := by
    intro j
    rw [← bccPrimitive_label j, Matrix.mulVec_mulVec, hAB]
    exact ((hreg j).1).symm
  have herr : ∀ j, T.err j = (A - T.O).mulVec (star j) + T.eps j • h := by
    intro j
    rw [Matrix.sub_mulVec, hAs j]
    unfold err
    abel
  have hcost : ∑ j, sq (T.err j) = 4 * frobSq (A - T.O) + 8 * sq h := by
    rw [Finset.sum_congr rfl (fun j _ => congrArg sq (herr j))]
    exact registered_cost (A - T.O) h T.eps T.eps01 hcount hbal
  refine ⟨A, f₀, hdetA, half, ?_, ?_⟩
  · rw [hAB, hbasis.2, model.points]
    rfl
  · rw [hcost, hhdef]

end Trial

/-- Registration: every reduced representative with actual
defect below one has a registered index-two BCC basis, its nonzero half
class, an integer wrap and a proper rotation whose strain and displacement
cost is bounded by the defect. -/
theorem register_proof (q : TwoSite) (p : Chart) (rep : ReducedRepresentative q p)
    (hD : defect q < 1) : Registration q := by
  have hc : (chartPoint p).Valid := rep.valid
  have hsep : separated (chartPoint p) := rep.separation
  have hDc : cappedDefect (neighbors (chartPoint p)) < 1 := by
    show defect (chartPoint p) < 1
    rw [rep.sameDefect]
    exact hD
  obtain ⟨O, hO, σ, hσ⟩ :=
    cappedDefect_attained (twoSite_neighbors_finite (chartPoint p) hc) hDc
  have hmem : ∀ j, (σ j : Vec) ∈ (chartPoint p).points := by
    intro j
    have h := (σ j).property.1
    simpa only [zero_add] using h
  have htail : 0 ≤ ∑' v : ↥(neighbors (chartPoint p)),
      if v ∈ Set.range σ then 0 else annularWeight v.val := by
    apply tsum_nonneg
    intro v
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  have htrial : 25 * ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) ≤ defect (chartPoint p) := by
    show _ ≤ cappedDefect (neighbors (chartPoint p))
    rw [← hσ]
    unfold defectTrial
    linarith
  have hsame := rep.sameDefect
  have hsmall : ∑ j, sq ((σ j : Vec) - O.mulVec (star j)) < 1/25 := by
    linarith
  let T : Trial (chartPoint p) := ⟨O, hO, fun j => (σ j : Vec), hmem, hsmall⟩
  obtain ⟨A, f₀, hdetA, half, hlat, hcost⟩ := T.core hc hsep
  have hAu : IsUnit A.det := by
    rw [hdetA]
    exact isUnit_one
  have hRu : IsUnit (chartPoint p).basis.det := by
    rw [hc.1]
    exact isUnit_one
  have hBdet : (A⁻¹ * (chartPoint p).basis).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdetA, hc.1]
    simp
  refine ⟨p, rep, A⁻¹ * (chartPoint p).basis, f₀, 0, O, ⟨hBdet, half, ?_, ?_⟩, hO, ?_⟩
  · rintro ⟨n, hn⟩
    have hBu : IsUnit (A⁻¹ * (chartPoint p).basis).det := by
      rw [hBdet]
      exact isUnit_one
    have e := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hBu) hn
    exact half.2 n e.symm
  · rw [lattice_left_mul, ← Matrix.mulVec_mulVec, translate_image, ← Set.image_union, ← hlat,
      lattice_left_mul, Set.image_image]
    have hid : (fun x => A⁻¹.mulVec (A.mulVec x)) = id := by
      funext x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]
      rfl
    rw [hid, Set.image_id, bccPrimitive_lattice]
  · have hRB : chartBasis p * (A⁻¹ * (chartPoint p).basis)⁻¹ = A := by
      change (chartPoint p).basis * (A⁻¹ * (chartPoint p).basis)⁻¹ = A
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hAu, ← mul_assoc,
        Matrix.mul_nonsing_inv _ hRu, one_mul]
    have htrial' : 25 * ∑ j, sq (T.err j) ≤ defect (chartPoint p) := htrial
    rw [hRB, castVec_zero, sub_zero, ← hsame]
    change 100 * frobSq (A - T.O) + 200 * sq ((chartPoint p).basis.mulVec
      ((chartPoint p).offset - f₀)) ≤ defect (chartPoint p)
    rw [hcost] at htrial'
    linarith

end BccSharp.Coulomb.GlobalInputs
