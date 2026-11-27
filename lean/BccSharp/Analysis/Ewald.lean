module

public import BccSharp.Analysis.Gaussian
public import BccSharp.Analysis.LatticeTails
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr

/-! The Ewald series in the certifier's natural units (η = 2). These are actual
infinite sums of real functions, with erfc defined by its Gaussian integral.
The reciprocal kernel is assigned zero at the origin, as in the omitted h=0
self term; conclusions about the physical dynamical matrix exclude reciprocal
lattice points. No equivalence to the Bloch Hessian is asserted here. -/

@[expose] public section
namespace BccSharp.Ewald

open Real
open LatticeTails

abbrev Vec := Fin 3 → ℝ

noncomputable def coord (z : Triple) : Vec := ![(z.1 : ℝ), (z.2.1 : ℝ), (z.2.2 : ℝ)]
noncomputable def sq (w : Vec) : ℝ := w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2

@[simp] theorem sq_coord (z : Triple) : sq (coord z) = normSq z := by
  simp [sq, coord, normSq]

theorem sq_nonnegative (w : Vec) : 0 ≤ sq w := by
  unfold sq; positivity

theorem component_sq_le (w : Vec) (i : Fin 3) : w i ^ 2 ≤ sq w := by
  fin_cases i <;> dsimp [sq] <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]

theorem abs_component_product (w : Vec) (i j : Fin 3) : |w i * w j| ≤ sq w := by
  apply abs_le.mpr
  constructor <;> nlinarith [component_sq_le w i, component_sq_le w j,
    sq_nonneg (w i - w j), sq_nonneg (w i + w j)]

theorem abs_ratio (w : Vec) (i j : Fin 3) : |w i * w j / sq w| ≤ 1 := by
  by_cases hs : sq w = 0
  · simp [hs]
  · have hp := lt_of_le_of_ne (sq_nonnegative w) (Ne.symm hs)
    rw [abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (by simpa using abs_component_product w i j)

noncomputable def beta : ℝ := Real.pi ^ 2 / 4

noncomputable def kernel (w : Vec) (i j : Fin 3) : ℝ :=
  (w i * w j / sq w) * exp (-beta * sq w)

theorem beta_ge_two : 2 ≤ beta := by
  unfold beta
  nlinarith [Real.pi_gt_three]

theorem kernel_bound (w : Vec) (i j : Fin 3) :
    |kernel w i j| ≤ exp (-beta * sq w) := by
  rw [kernel, abs_mul, abs_of_pos (exp_pos _)]
  exact (mul_le_mul_of_nonneg_right (abs_ratio w i j) (exp_pos _).le).trans_eq (one_mul _)

theorem shifted_square (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2) (z : Triple) :
    normSq z - 3 / 2 ≤ 2 * sq (fun i => coord z i + u i) := by
  have h (i : Fin 3) : (coord z i) ^ 2 - 1 / 2 ≤ 2 * (coord z i + u i) ^ 2 := by
    have hi := abs_le.mp (hu i)
    have hu2 : (u i) ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [sq_nonneg (coord z i + 2 * u i)]
  rw [← sq_coord]
  dsimp [sq]
  linarith [h 0, h 1, h 2]

theorem shifted_kernel_bound (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2)
    (z : Triple) (i j : Fin 3) :
    |kernel (fun k => coord z k + u k) i j| ≤ 9 * exp (-normSq z) := by
  have hs := sq_nonnegative (fun k => coord z k + u k)
  have he : -beta * sq (fun k => coord z k + u k) ≤ 2 - normSq z := by
    nlinarith [shifted_square u hu z, mul_nonneg (sub_nonneg.mpr beta_ge_two) hs]
  have he2 : exp (2 : ℝ) ≤ 9 := by
    have hh := pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_three.le 2
    convert hh using 1 <;> norm_num [← exp_nat_mul]
  calc
    _ ≤ exp (-beta * sq (fun k => coord z k + u k)) := kernel_bound _ _ _
    _ ≤ exp (2 - normSq z) := exp_le_exp.mpr he
    _ = exp 2 * exp (-normSq z) := by rw [sub_eq_add_neg, exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right he2 (exp_pos _).le

theorem zero_kernel_bound (z : Triple) (i j : Fin 3) :
    |kernel (coord z) i j| ≤ exp (-normSq z) := by
  apply (kernel_bound _ _ _).trans
  apply exp_le_exp.mpr
  rw [sq_coord]
  have hn : 0 ≤ normSq z := by simpa using sq_nonnegative (coord z)
  nlinarith [mul_le_mul_of_nonneg_right beta_ge_two hn]

theorem erfc_nonneg (x : ℝ) : 0 ≤ Gaussian.erfcIntegral x := by
  unfold Gaussian.erfcIntegral
  exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun _ => (exp_pos _).le)

/-- Algebraically expanded radial Hessian of erfc(2r)/r. Here t = LᵢLⱼ/r²
and d is the Kronecker delta. The expanded form avoids repeated interval error. -/
noncomputable def radialHessian (r t d : ℝ) : ℝ :=
  Gaussian.erfcIntegral (2 * r) * r⁻¹ ^ 3 * (3 * t - d) +
    exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ *
      ((12 * r⁻¹ ^ 2 + 32) * t - 4 * d * r⁻¹ ^ 2)

theorem radialHessian_bound {r t d : ℝ} (hr : 1 / 2 ≤ r) (ht : |t| ≤ 1)
    (hd : |d| ≤ 1) : |radialHessian r t d| ≤ 128 * exp (-(4 * r ^ 2)) := by
  have hr0 : 0 < r := by linarith
  have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hi2 : r⁻¹ ≤ 2 := by
    simpa using (one_div_le hr0 (by norm_num : (0 : ℝ) < 2)).mpr hr
  have hp : 0 < sqrt Real.pi := sqrt_pos.mpr pi_pos
  have hp1 : 1 ≤ sqrt Real.pi := by
    nlinarith [sq_sqrt pi_pos.le, Real.pi_gt_three]
  have hpi : 0 ≤ (sqrt Real.pi)⁻¹ := inv_nonneg.mpr hp.le
  have hpi1 : (sqrt Real.pi)⁻¹ ≤ 1 := by
    simpa using (one_div_le hp (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hp1)
  have he := (exp_pos (-(4 * r ^ 2))).le
  have hc : Gaussian.erfcIntegral (2 * r) ≤
      exp (-(4 * r ^ 2)) * r⁻¹ * (sqrt Real.pi)⁻¹ / 2 := by
    have h := Gaussian.erfc_upper (by positivity : 0 < 2 * r)
    have heq : -(2 * r) ^ 2 = -(4 * r ^ 2) := by ring
    rw [heq] at h
    convert h using 1; ring
  have hab : |3 * t - d| ≤ 4 := by
    calc
      _ ≤ |3 * t| + |d| := abs_sub _ _
      _ ≤ 3 * 1 + 1 := by rw [abs_mul]; norm_num; linarith
      _ = _ := by norm_num
  have hab' : |(12 * r⁻¹ ^ 2 + 32) * t - 4 * d * r⁻¹ ^ 2| ≤
      (12 * r⁻¹ ^ 2 + 32) * 1 + 4 * 1 * r⁻¹ ^ 2 := by
    calc
      _ ≤ |(12 * r⁻¹ ^ 2 + 32) * t| + |4 * d * r⁻¹ ^ 2| := abs_sub _ _
      _ = (12 * r⁻¹ ^ 2 + 32) * |t| + 4 * |d| * r⁻¹ ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 12 * r⁻¹ ^ 2 + 32),
          abs_of_nonneg (by positivity : 0 ≤ r⁻¹ ^ 2)]
        norm_num
      _ ≤ _ := by gcongr
  calc
    _ ≤ |Gaussian.erfcIntegral (2 * r) * r⁻¹ ^ 3 * (3 * t - d)| +
        |exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ *
          ((12 * r⁻¹ ^ 2 + 32) * t - 4 * d * r⁻¹ ^ 2)| := abs_add_le _ _
    _ = Gaussian.erfcIntegral (2 * r) * r⁻¹ ^ 3 * |3 * t - d| +
        exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ *
          |(12 * r⁻¹ ^ 2 + 32) * t - 4 * d * r⁻¹ ^ 2| := by
      simp only [abs_mul, abs_of_nonneg (erfc_nonneg _), abs_of_nonneg hi,
        abs_of_nonneg hpi, abs_of_nonneg he, abs_pow]
    _ ≤ (exp (-(4 * r ^ 2)) * r⁻¹ * (sqrt Real.pi)⁻¹ / 2) * r⁻¹ ^ 3 * 4 +
        exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ *
          ((12 * r⁻¹ ^ 2 + 32) * 1 + 4 * 1 * r⁻¹ ^ 2) := by
      gcongr
    _ = exp (-(4 * r ^ 2)) * (sqrt Real.pi)⁻¹ * (2 * r⁻¹ ^ 4 + 16 * r⁻¹ ^ 2 + 32) := by ring
    _ ≤ exp (-(4 * r ^ 2)) * 1 * (2 * 2 ^ 4 + 16 * 2 ^ 2 + 32) := by gcongr
    _ = _ := by ring

theorem normSq_ge_one {z : Triple} (hz : z ≠ 0) : 1 ≤ normSq z := by
  have hs : square z ≠ 0 := by
    intro h
    have h₁ : z.1.natAbs = 0 := by dsimp [square] at h; nlinarith
    have h₂ : z.2.1.natAbs = 0 := by dsimp [square] at h; nlinarith
    have h₃ : z.2.2.natAbs = 0 := by dsimp [square] at h; nlinarith
    apply hz
    apply Prod.ext
    · exact Int.natAbs_eq_zero.mp h₁
    · exact Prod.ext (Int.natAbs_eq_zero.mp h₂) (Int.natAbs_eq_zero.mp h₃)
  rw [normSq_eq_square]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs

noncomputable def phi (z : Triple) (i j : Fin 3) : ℝ :=
  radialHessian (sqrt (normSq z) / 2)
    (coord z i * coord z j / normSq z) (if i = j then 1 else 0)

theorem phi_bound {z : Triple} (hz : z ≠ 0) (i j : Fin 3) :
    |phi z i j| ≤ 128 * exp (-normSq z) := by
  have hn : 0 ≤ normSq z := by simpa using sq_nonnegative (coord z)
  have hr : 1 / 2 ≤ sqrt (normSq z) / 2 := by
    nlinarith [normSq_ge_one hz, sq_sqrt hn, sqrt_nonneg (normSq z)]
  have h := radialHessian_bound hr (by simpa using abs_ratio (coord z) i j)
    (show |(if i = j then 1 else 0 : ℝ)| ≤ 1 by split_ifs <;> norm_num)
  have he : 4 * (sqrt (normSq z) / 2) ^ 2 = normSq z := by nlinarith [sq_sqrt hn]
  simpa only [phi, he] using h

noncomputable def realTerm (u : Vec) (z : Triple) (i j : Fin 3) : ℝ :=
  if bcc z ∧ z ≠ 0 then
    (1 - cos (Real.pi * ∑ k, u k * coord z k)) * phi z i j else 0

noncomputable def reciprocalTerm (u : Vec) (z : Triple) (i j : Fin 3) : ℝ :=
  if reciprocal z then 8 * Real.pi *
    (kernel (fun k => coord z k + u k) i j - kernel (coord z) i j) else 0

theorem realTerm_bound (u : Vec) (z : Triple) (i j : Fin 3) :
    |realTerm u z i j| ≤ 256 * exp (-normSq z) := by
  unfold realTerm
  split_ifs with hz
  · have hc (x : ℝ) : |1 - cos x| ≤ 2 := by
      apply abs_le.mpr
      constructor <;> linarith [cos_le_one x, neg_one_le_cos x]
    rw [abs_mul]
    calc
      _ ≤ 2 * (128 * exp (-normSq z)) :=
        mul_le_mul (hc _) (phi_bound hz.2 i j) (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  · simp only [abs_zero]; positivity

theorem reciprocalTerm_bound (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2)
    (z : Triple) (i j : Fin 3) :
    |reciprocalTerm u z i j| ≤ 320 * exp (-normSq z) := by
  unfold reciprocalTerm
  split_ifs
  · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 8 * Real.pi)]
    calc
      _ ≤ (8 * Real.pi) * (|kernel (fun k => coord z k + u k) i j| +
          |kernel (coord z) i j|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
      _ ≤ 32 * (9 * exp (-normSq z) + exp (-normSq z)) := by
        gcongr
        · nlinarith [Real.pi_lt_four]
        · exact shifted_kernel_bound u hu z i j
        · exact zero_kernel_bound z i j
      _ = _ := by ring
  · simp only [abs_zero]; positivity

noncomputable def summand (u : Vec) (z : Triple) (i j : Fin 3) : ℝ :=
  realTerm u z i j + reciprocalTerm u z i j

/-- The complete Ewald series, with both full parity lattices and the 8π
normalization. The η=2 Gaussian factor in real space is exp(-|z|²), since L=z/2. -/
noncomputable def matrix (u : Vec) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑' z : Triple, summand u z i j

noncomputable def finiteMatrix (R : ℕ) (u : Vec) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ z ∈ cube R, summand u z i j

theorem summand_bound (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2)
    (z : Triple) (i j : Fin 3) : |summand u z i j| ≤ 576 * exp (-normSq z) := by
  calc
    _ ≤ |realTerm u z i j| + |reciprocalTerm u z i j| := abs_add_le _ _
    _ ≤ 256 * exp (-normSq z) + 320 * exp (-normSq z) :=
      add_le_add (realTerm_bound u z i j) (reciprocalTerm_bound u hu z i j)
    _ = _ := by ring

theorem summable (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2) (i j : Fin 3) :
    Summable (fun z => summand u z i j) :=
  summable_of_gaussian_bound (by norm_num) (fun z => summand_bound u hu z i j)

theorem absolutely_summable (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2) (i j : Fin 3) :
    Summable (fun z => |summand u z i j|) := by
  apply summable_of_gaussian_bound (by norm_num : (0 : ℝ) ≤ 576)
  intro z
  simpa only [abs_abs] using summand_bound u hu z i j

/-- Uniform entrywise truncation theorem for the actual Ewald series. -/
theorem finiteMatrix_error (R : ℕ) (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2)
    (i j : Fin 3) : |matrix u i j - finiteMatrix R u i j| ≤
      576 * (1 / 2 : ℝ) ^ (R * (R + 1)) * 27 :=
  cube_error (by norm_num) (fun z => summand_bound u hu z i j) R

noncomputable def pointN : Vec := ![1 / 2, 1 / 2, 0]

theorem pointN_bound (i : Fin 3) : |pointN i| ≤ 1 / 2 := by
  fin_cases i <;> norm_num [pointN]

/-- A concrete exact rational remainder at N, without any membership premise. -/
theorem pointN_error (i j : Fin 3) :
    |matrix pointN i j - finiteMatrix 5 pointN i j| ≤ (243 : ℝ) / 16777216 := by
  convert finiteMatrix_error 5 pointN pointN_bound i j using 1; norm_num

/-- The conventional reciprocal sums, including h=0 in the shifted sum and
with the zero self term defined to be zero in the unshifted sum. -/
noncomputable def reciprocalSummand (u : Vec) (z : Triple) (i j : Fin 3) : ℝ :=
  if reciprocal z then kernel (fun k => coord z k + u k) i j else 0

theorem reciprocalSummand_summable (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2)
    (i j : Fin 3) : Summable (fun z => reciprocalSummand u z i j) := by
  apply summable_of_gaussian_bound (by norm_num : (0 : ℝ) ≤ 9)
  intro z
  unfold reciprocalSummand
  split_ifs
  · exact shifted_kernel_bound u hu z i j
  · simp only [abs_zero]; positivity

/-- Identification with the usual three absolutely convergent Ewald sums.
In particular the matrix is not defined through a conditionally cancelling
pair of divergent sums or through a numerical enclosure. -/
theorem series_formula (u : Vec) (hu : ∀ i, |u i| ≤ 1 / 2) (i j : Fin 3) :
    matrix u i j = (∑' z, realTerm u z i j) + 8 * Real.pi *
      ((∑' z, reciprocalSummand u z i j) - ∑' z, reciprocalSummand 0 z i j) := by
  have hr := summable_of_gaussian_bound (by norm_num : (0 : ℝ) ≤ 256)
    (fun z => realTerm_bound u z i j)
  have hu' := reciprocalSummand_summable u hu i j
  have hzero : ∀ i : Fin 3, |(0 : Vec) i| ≤ 1 / 2 := by intro i; norm_num
  have hzero' := reciprocalSummand_summable 0 hzero i j
  have ht : (fun z => reciprocalTerm u z i j) =
      fun z => (8 * Real.pi) * (reciprocalSummand u z i j - reciprocalSummand 0 z i j) := by
    funext z
    simp only [reciprocalTerm, reciprocalSummand, Pi.zero_apply, add_zero]
    split_ifs <;> simp
  unfold matrix summand
  rw [hr.tsum_add (by rw [ht]; exact (hu'.sub hzero').mul_left _), ht,
    tsum_mul_left, hu'.tsum_sub hzero']

/-- Exact equality between the cube sum and the explicitly filtered finite
lattices. This is the enumeration interface used by a finite verifier. -/
theorem finite_formula (R : ℕ) (u : Vec) (i j : Fin 3) :
    finiteMatrix R u i j =
      (∑ z ∈ bccCube R, (1 - cos (Real.pi * ∑ k, u k * coord z k)) * phi z i j) +
      8 * Real.pi * ∑ z ∈ reciprocalCube R,
        (kernel (fun k => coord z k + u k) i j - kernel (coord z) i j) := by
  simp only [finiteMatrix, summand, Finset.sum_add_distrib, bccCube,
    reciprocalCube, Finset.sum_filter, realTerm, reciprocalTerm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

theorem kernel_symmetric (w : Vec) (i j : Fin 3) : kernel w i j = kernel w j i := by
  simp only [kernel, mul_comm (w i) (w j)]

theorem phi_symmetric (z : Triple) (i j : Fin 3) : phi z i j = phi z j i := by
  simp only [phi, mul_comm (coord z i) (coord z j), eq_comm]

theorem summand_symmetric (u : Vec) (z : Triple) (i j : Fin 3) :
    summand u z i j = summand u z j i := by
  simp only [summand, realTerm, reciprocalTerm, phi_symmetric z i j, kernel_symmetric _ i j]

theorem matrix_symmetric (u : Vec) (i j : Fin 3) : matrix u i j = matrix u j i := by
  unfold matrix
  exact tsum_congr fun z => summand_symmetric u z i j

theorem finiteMatrix_symmetric (R : ℕ) (u : Vec) (i j : Fin 3) :
    finiteMatrix R u i j = finiteMatrix R u j i := by
  unfold finiteMatrix
  exact Finset.sum_congr rfl fun z _ => summand_symmetric u z i j

end BccSharp.Ewald
