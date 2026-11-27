module

public import BccSharp.Analysis.LatticeTails

/-! Gaussian lattice tails with a quadratic weight. These preserve the full
cube exponent, which is needed when bounding derivatives or the regular Ewald
matrix after division by the squared distance to Gamma. -/

@[expose] public section
namespace BccSharp.LatticeTails

private theorem hasSum_product {α β : Type*} {f : α → ℝ} {g : β → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    HasSum (fun z : α × β => f z.1 * g z.2) (a * b) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

theorem hasSum_integer_secondMoment :
    HasSum (fun z : ℤ => (z.natAbs : ℝ) ^ 2 * (1 / 2 : ℝ) ^ z.natAbs) 12 := by
  have hn : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) 6 := by
    convert hasSum_sq_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num) using 1
    norm_num
  have hs : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n + 1)) 6 := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) 1).mpr
    simpa using hn
  have h1 : HasSum (fun n : ℕ => ((n : ℤ).natAbs : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n : ℤ).natAbs) 6 := by
    simpa using hn
  have h2 : HasSum (fun n : ℕ => ((-(↑n + 1) : ℤ).natAbs : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ (-(↑n + 1) : ℤ).natAbs) 6 := by
    simpa only [Int.natAbs_neg, ← Int.natCast_succ, Int.natAbs_natCast] using hs
  convert HasSum.of_nat_of_neg_add_one
    (f := fun z : ℤ => (z.natAbs : ℝ) ^ 2 * (1 / 2 : ℝ) ^ z.natAbs) h1 h2 using 1
  norm_num

/-- The complete three-dimensional quadratic moment is exactly 324. -/
theorem hasSum_weighted_square : HasSum (fun z : Triple => normSq z * weight z) 324 := by
  let g := fun z : ℤ => (1 / 2 : ℝ) ^ z.natAbs
  let m := fun z : ℤ => (z.natAbs : ℝ) ^ 2 * (1 / 2 : ℝ) ^ z.natAbs
  have hg : HasSum g 3 := hasSum_integer_geometric
  have hm : HasSum m 12 := hasSum_integer_secondMoment
  have hg0 : ∀ z, 0 ≤ g z := fun z => by dsimp [g]; positivity
  have hm0 : ∀ z, 0 ≤ m z := fun z => by dsimp [m]; positivity
  have hgg := hasSum_product hg hg hg0 hg0
  have hmg := hasSum_product hm hg hm0 hg0
  have hgm := hasSum_product hg hm hg0 hm0
  have h1 := hasSum_product hm hgg hm0 (fun z => mul_nonneg (hg0 z.1) (hg0 z.2))
  have h2 := hasSum_product hg hmg hg0 (fun z => mul_nonneg (hm0 z.1) (hg0 z.2))
  have h3 := hasSum_product hg hgm hg0 (fun z => mul_nonneg (hg0 z.1) (hm0 z.2))
  convert (h1.add h2).add h3 using 1
  · funext z
    rw [normSq_eq_square]
    simp only [square, weight, length, pow_add, Nat.cast_add, Nat.cast_pow]
    dsimp [g, m]
    ring
  · norm_num

noncomputable def weighted (A B : ℝ) (z : Triple) : ℝ := (A + B * normSq z) * weight z

theorem weighted_hasSum (A B : ℝ) : HasSum (weighted A B) (27 * A + 324 * B) := by
  have hw : HasSum weight 27 := by rw [← tsum_weight]; exact weight_summable.hasSum
  convert (hw.mul_left A).add (hasSum_weighted_square.mul_left B) using 1
  · funext z
    dsimp [weighted]
    ring
  · ring

theorem normSq_nonneg (z : Triple) : 0 ≤ normSq z := by rw [normSq_eq_square]; positivity

theorem weighted_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (z : Triple) :
    0 ≤ weighted A B z :=
  mul_nonneg (add_nonneg hA (mul_nonneg hB (normSq_nonneg z))) (weight_nonneg z)

theorem summable_of_weighted_gaussian_bound {f : Triple → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ z, |f z| ≤ (A + B * normSq z) * Real.exp (-normSq z)) : Summable f := by
  apply (weighted_hasSum A B).summable.of_norm_bounded
  intro z
  exact (hf z).trans (mul_le_mul_of_nonneg_left (gaussian_le_weight z)
    (add_nonneg hA (mul_nonneg hB (normSq_nonneg z))))

/-- A complete cube remainder for any function dominated by
`(A + B |z|²) exp(-|z|²)`, with explicit nonnegative constants. -/
theorem weighted_cube_error {f : Triple → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ z, |f z| ≤ (A + B * normSq z) * Real.exp (-normSq z)) (R : ℕ) :
    |(∑' z, f z) - ∑ z ∈ cube R, f z| ≤
      (1 / 2 : ℝ) ^ (R * (R + 1)) * (27 * A + 324 * B) := by
  let c : ℝ := (1 / 2 : ℝ) ^ (R * (R + 1))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs := summable_of_weighted_gaussian_bound hA hB hf
  have hw := ((weighted_hasSum A B).summable.mul_left c).subtype (fun z => z ∉ cube R)
  have hb (z : {z // z ∉ cube R}) : ‖f z.val‖ ≤ c * weighted A B z.val := by
    calc
      _ ≤ (A + B * normSq z.val) * Real.exp (-normSq z.val) := hf z.val
      _ ≤ (A + B * normSq z.val) * (c * weight z.val) :=
        mul_le_mul_of_nonneg_left (gaussian_outside R z.property)
          (add_nonneg hA (mul_nonneg hB (normSq_nonneg z.val)))
      _ = _ := by dsimp [weighted]; ring
  have hn := Summable.of_nonneg_of_le (fun z => norm_nonneg (f z.val)) hb hw
  have he := hs.sum_add_tsum_subtype_compl (cube R)
  have ht : (∑' z, f z) - ∑ z ∈ cube R, f z = ∑' z : {z // z ∉ cube R}, f z := by linarith
  rw [ht, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' z : {z // z ∉ cube R}, ‖f z.val‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' z : {z // z ∉ cube R}, c * weighted A B z.val := hn.tsum_le_tsum hb hw
    _ ≤ ∑' z : Triple, c * weighted A B z := by
      exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun z _ => mul_nonneg hc (weighted_nonneg hA hB z)) (fun _ => le_rfl) hw
        ((weighted_hasSum A B).summable.mul_left c)
    _ = _ := by rw [tsum_mul_left, (weighted_hasSum A B).tsum_eq]

end BccSharp.LatticeTails
