module

public import BccSharp.Analysis.EwaldRegular
public import BccSharp.Analysis.Interpolation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quadratic bounds for the regularized Ewald summands, with constants kept
explicit. The norm and dot product here are the actual three-dimensional ones. -/

@[expose] public section
namespace BccSharp.Ewald

open Real LatticeTails

noncomputable def dot (v w : Vec) : ℝ := ∑ k, v k * w k

theorem dot_sq_le (v w : Vec) : dot v w ^ 2 ≤ Ewald.sq v * Ewald.sq w := by
  simp only [dot, Fin.sum_univ_three, Ewald.sq]
  nlinarith [sq_nonneg (v 0 * w 1 - v 1 * w 0),
    sq_nonneg (v 0 * w 2 - v 2 * w 0), sq_nonneg (v 1 * w 2 - v 2 * w 1)]

theorem shifted_square_upper (u : Vec) (z : Triple) :
    Ewald.sq (fun i => coord z i + u i) ≤ 2 * normSq z + 2 * Ewald.sq u := by
  rw [← sq_coord]
  dsimp [Ewald.sq]
  nlinarith [sq_nonneg (coord z 0 - u 0), sq_nonneg (coord z 1 - u 1),
    sq_nonneg (coord z 2 - u 2)]

theorem shifted_square_lower (u : Vec) (z : Triple) :
    normSq z ≤ 5 * Ewald.sq (fun i => coord z i + u i) + 5 / 4 * Ewald.sq u := by
  rw [← sq_coord]
  dsimp [Ewald.sq]
  nlinarith [sq_nonneg (2 * coord z 0 + 5 / 2 * u 0),
    sq_nonneg (2 * coord z 1 + 5 / 2 * u 1), sq_nonneg (2 * coord z 2 + 5 / 2 * u 2)]

theorem reciprocal_normSq_ge_two {z : Triple} (hz : reciprocal z) (hz0 : z ≠ 0) :
    2 ≤ normSq z := by
  have hsq (k : ℤ) : k ^ 2 % 2 = k % 2 := by
    rw [pow_two, Int.mul_emod k k 2]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
  have hn : (1 : ℤ) ≤ z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 := by
    have h := normSq_ge_one hz0
    dsimp [normSq] at h
    exact_mod_cast h
  have hp : (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2) % 2 = 0 := by
    have h1 := hsq z.1
    have h2 := hsq z.2.1
    have h3 := hsq z.2.2
    dsimp [reciprocal] at hz
    omega
  have hh : (2 : ℤ) ≤ z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 := by omega
  dsimp [normSq]
  exact_mod_cast hh

theorem reciprocal_shift_sq_lower {z : Triple} (hz : reciprocal z) (hz0 : z ≠ 0)
    {u : Vec} (hu : Ewald.sq u ≤ 1) :
    1 / 8 ≤ Ewald.sq (fun k => coord z k + u k) := by
  linarith [reciprocal_normSq_ge_two hz hz0, shifted_square_lower u z]

theorem beta_le_three : beta ≤ 3 := by
  unfold beta
  nlinarith [Real.pi_lt_d4, Real.pi_gt_three]

/-- The normalized cosine deficit is bounded uniformly even at zero. -/
theorem cosc_bounds (x : ℝ) : 0 ≤ DividedExp.cosc x ∧ DividedExp.cosc x ≤ 1 / 2 := by
  by_cases hx : x = 0
  · subst x; norm_num
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hi := DividedExp.cosc_identity x
  have hc : 1 - cos x ≤ x ^ 2 / 2 := by
    have hcos := cos_two_mul (x / 2)
    have hsin := (sin_sq_le_sq (x := x / 2))
    have hsum := sin_sq_add_cos_sq (x / 2)
    have he : 2 * (x / 2) = x := by ring
    rw [he] at hcos
    nlinarith
  constructor
  · have h0 : 0 ≤ x ^ 2 * DividedExp.cosc x := by rw [hi]; linarith [cos_le_one x]
    exact nonneg_of_mul_nonneg_right h0 hx2
  · nlinarith

noncomputable def realScaled (x : ℝ) (v : Vec) (z : Triple) (i j : Fin 3) : ℝ :=
  if bcc z ∧ z ≠ 0 then (Real.pi * dot v (coord z)) ^ 2 *
    DividedExp.cosc (Real.pi * x * dot v (coord z)) * phi z i j else 0

theorem realScaled_identity (x : ℝ) (v : Vec) (z : Triple) (i j : Fin 3) :
    x ^ 2 * realScaled x v z i j = realTerm (x • v) z i j := by
  unfold realScaled realTerm
  split_ifs
  · have he : Real.pi * (∑ k, (x • v) k * coord z k) = Real.pi * x * dot v (coord z) := by
      simp [dot, Fin.sum_univ_three, smul_eq_mul]
      ring
    rw [he]
    have hi := DividedExp.cosc_identity (Real.pi * x * dot v (coord z))
    calc
      _ = ((Real.pi * x * dot v (coord z)) ^ 2 *
          DividedExp.cosc (Real.pi * x * dot v (coord z))) * phi z i j := by ring
      _ = _ := by rw [hi]
  · ring

theorem realScaled_bound (x : ℝ) (v : Vec) (z : Triple) (i j : Fin 3) :
    |realScaled x v z i j| ≤ 1024 * Ewald.sq v * normSq z * exp (-normSq z) := by
  have hv := sq_nonnegative v
  have hn := normSq_nonneg z
  unfold realScaled
  split_ifs with hz
  · have hc := cosc_bounds (Real.pi * x * dot v (coord z))
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hc.1]
    calc
      _ ≤ (Real.pi * dot v (coord z)) ^ 2 * (1 / 2) * (128 * exp (-normSq z)) := by
        gcongr
        · exact hc.2
        · exact phi_bound hz.2 i j
      _ = 64 * Real.pi ^ 2 * dot v (coord z) ^ 2 * exp (-normSq z) := by ring
      _ ≤ 64 * 16 * (Ewald.sq v * normSq z) * exp (-normSq z) := by
        gcongr
        · nlinarith [Real.pi_lt_four, Real.pi_pos]
        · simpa using dot_sq_le v (coord z)
      _ = _ := by ring
  · simp only [abs_zero]; positivity

theorem realScaled_summable (x : ℝ) (v : Vec) (i j : Fin 3) :
    Summable (fun z => realScaled x v z i j) := by
  have hv := sq_nonnegative v
  apply summable_of_weighted_gaussian_bound (A := 0) (B := 1024 * Ewald.sq v)
    (by norm_num) (by positivity)
  intro z
  simpa only [zero_add, mul_assoc] using realScaled_bound x v z i j

end BccSharp.Ewald
