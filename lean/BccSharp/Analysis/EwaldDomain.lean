module

public import BccSharp.Analysis.Ewald

/-! Convergence on the entire real parameter space, and cube remainders on the
full closed irreducible wedge. The point theorem's coordinate bound is not
silently reused outside its range. -/

@[expose] public section
namespace BccSharp.Ewald

open Real LatticeTails

/-- The elementary translated-square inequality, with the dependence on the
translation retained explicitly. -/
theorem shifted_square_all (u : Vec) (z : Triple) :
    normSq z - 2 * Ewald.sq u ≤ 2 * Ewald.sq (fun i => coord z i + u i) := by
  rw [← sq_coord]
  dsimp [Ewald.sq]
  nlinarith [sq_nonneg (coord z 0 + 2 * u 0), sq_nonneg (coord z 1 + 2 * u 1),
    sq_nonneg (coord z 2 + 2 * u 2)]

theorem shifted_kernel_bound_all (u : Vec) (z : Triple) (i j : Fin 3) :
    |kernel (fun k => coord z k + u k) i j| ≤
      exp (2 * Ewald.sq u) * exp (-normSq z) := by
  apply (kernel_bound _ _ _).trans
  rw [← exp_add]
  apply exp_le_exp.mpr
  nlinarith [shifted_square_all u z,
    mul_nonneg (sub_nonneg.mpr beta_ge_two) (sq_nonnegative (fun k => coord z k + u k))]

theorem reciprocalTerm_bound_all (u : Vec) (z : Triple) (i j : Fin 3) :
    |reciprocalTerm u z i j| ≤ 32 * (exp (2 * Ewald.sq u) + 1) * exp (-normSq z) := by
  unfold reciprocalTerm
  split_ifs
  · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 8 * Real.pi)]
    calc
      _ ≤ (8 * Real.pi) * (|kernel (fun k => coord z k + u k) i j| +
          |kernel (coord z) i j|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
      _ ≤ 32 * (exp (2 * Ewald.sq u) * exp (-normSq z) + exp (-normSq z)) := by
        gcongr
        · nlinarith [Real.pi_lt_four]
        · exact shifted_kernel_bound_all u z i j
        · exact zero_kernel_bound z i j
      _ = _ := by ring
  · simp only [abs_zero]; positivity

noncomputable def majorant (u : Vec) : ℝ := 256 + 32 * (exp (2 * Ewald.sq u) + 1)

theorem majorant_nonneg (u : Vec) : 0 ≤ majorant u := by unfold majorant; positivity

theorem summand_bound_all (u : Vec) (z : Triple) (i j : Fin 3) :
    |summand u z i j| ≤ majorant u * exp (-normSq z) := by
  calc
    _ ≤ |realTerm u z i j| + |reciprocalTerm u z i j| := abs_add_le _ _
    _ ≤ 256 * exp (-normSq z) + 32 * (exp (2 * Ewald.sq u) + 1) * exp (-normSq z) :=
      add_le_add (realTerm_bound u z i j) (reciprocalTerm_bound_all u z i j)
    _ = _ := by unfold majorant; ring

/-- The actual Ewald series is absolutely convergent at every real argument;
the zero-kernel convention still does not assert a physical Bloch value there. -/
theorem summable_all (u : Vec) (i j : Fin 3) : Summable (fun z => summand u z i j) :=
  summable_of_gaussian_bound (majorant_nonneg u) (fun z => summand_bound_all u z i j)

theorem absolutely_summable_all (u : Vec) (i j : Fin 3) :
    Summable (fun z => |summand u z i j|) := by
  apply summable_of_gaussian_bound (majorant_nonneg u)
  intro z
  simpa only [abs_abs] using summand_bound_all u z i j

theorem reciprocalSummand_summable_all (u : Vec) (i j : Fin 3) :
    Summable (fun z => reciprocalSummand u z i j) := by
  apply summable_of_gaussian_bound (exp_pos (2 * Ewald.sq u)).le
  intro z
  unfold reciprocalSummand
  split_ifs
  · exact shifted_kernel_bound_all u z i j
  · simp only [abs_zero]; positivity

theorem series_formula_all (u : Vec) (i j : Fin 3) :
    matrix u i j = (∑' z, realTerm u z i j) + 8 * Real.pi *
      ((∑' z, reciprocalSummand u z i j) - ∑' z, reciprocalSummand 0 z i j) := by
  have hr := summable_of_gaussian_bound (by norm_num : (0 : ℝ) ≤ 256)
    (fun z => realTerm_bound u z i j)
  have hu := reciprocalSummand_summable_all u i j
  have hz := reciprocalSummand_summable_all 0 i j
  have ht : (fun z => reciprocalTerm u z i j) =
      fun z => (8 * Real.pi) * (reciprocalSummand u z i j - reciprocalSummand 0 z i j) := by
    funext z
    simp only [reciprocalTerm, reciprocalSummand, Pi.zero_apply, add_zero]
    split_ifs <;> simp
  unfold matrix summand
  rw [hr.tsum_add (by rw [ht]; exact (hu.sub hz).mul_left _), ht,
    tsum_mul_left, hu.tsum_sub hz]

theorem finiteMatrix_error_all (R : ℕ) (u : Vec) (i j : Fin 3) :
    |matrix u i j - finiteMatrix R u i j| ≤
      majorant u * (1 / 2 : ℝ) ^ (R * (R + 1)) * 27 :=
  cube_error (majorant_nonneg u) (fun z => summand_bound_all u z i j) R

theorem majorant_le_of_sq_le_one {u : Vec} (hu : Ewald.sq u ≤ 1) : majorant u ≤ 576 := by
  have he2 : exp (2 : ℝ) ≤ 9 := by
    have hh := pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_three.le 2
    convert hh using 1 <;> norm_num [← exp_nat_mul]
  have he : exp (2 * Ewald.sq u) ≤ exp 2 := exp_le_exp.mpr (by linarith)
  unfold majorant
  linarith

theorem finiteMatrix_error_unitBall (R : ℕ) (u : Vec) (hu : Ewald.sq u ≤ 1)
    (i j : Fin 3) : |matrix u i j - finiteMatrix R u i j| ≤
      576 * (1 / 2 : ℝ) ^ (R * (R + 1)) * 27 := by
  apply (finiteMatrix_error_all R u i j).trans
  gcongr
  exact majorant_le_of_sq_le_one hu

/-- The full closed wedge, including its boundary faces. -/
def InWedge (u : Vec) : Prop := 0 ≤ u 2 ∧ u 2 ≤ u 1 ∧ u 1 ≤ u 0 ∧ u 0 + u 1 ≤ 1

theorem wedge_sq_le_one {u : Vec} (hu : InWedge u) : Ewald.sq u ≤ 1 := by
  rcases hu with ⟨hz, hzy, hyx, hxy⟩
  have hy : 0 ≤ u 1 := hz.trans hzy
  have hx : 0 ≤ u 0 := hy.trans hyx
  have hy2 : u 1 ^ 2 ≤ u 0 * u 1 := by nlinarith [mul_nonneg hy (sub_nonneg.mpr hyx)]
  have hz2 : u 2 ^ 2 ≤ u 1 ^ 2 := by nlinarith
  have hsum : (u 0 + u 1) ^ 2 ≤ 1 := by nlinarith
  dsimp [Ewald.sq]
  nlinarith

theorem finiteMatrix_error_wedge (R : ℕ) (u : Vec) (hu : InWedge u)
    (i j : Fin 3) : |matrix u i j - finiteMatrix R u i j| ≤
      576 * (1 / 2 : ℝ) ^ (R * (R + 1)) * 27 :=
  finiteMatrix_error_unitBall R u (wedge_sq_le_one hu) i j

end BccSharp.Ewald
