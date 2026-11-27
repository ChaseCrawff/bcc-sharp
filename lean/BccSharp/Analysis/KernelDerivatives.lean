module

public import BccSharp.Analysis.RegularBounds

/-! Directional derivatives of the actual reciprocal Ewald kernel. The
formulas are proved by ordinary one-dimensional differentiation along lines. -/

@[expose] public section
namespace BccSharp.Ewald

open Real LatticeTails

noncomputable def radialKernel (s : ℝ) : ℝ := exp (-beta * s) / s
noncomputable def radialKernelD (s : ℝ) : ℝ := -exp (-beta * s) * (beta * s⁻¹ + s⁻¹ ^ 2)
noncomputable def radialKernelD2 (s : ℝ) : ℝ :=
  exp (-beta * s) * (beta ^ 2 * s⁻¹ + 2 * beta * s⁻¹ ^ 2 + 2 * s⁻¹ ^ 3)

theorem radialKernel_hasDerivAt {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt radialKernel (radialKernelD s) s := by
  convert (((hasDerivAt_id s).const_mul (-beta)).exp).div (hasDerivAt_id s) hs using 1
  · funext y; simp [radialKernel]
  · dsimp [radialKernelD]
    field_simp
    ring

theorem radialKernelD_hasDerivAt {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt radialKernelD (radialKernelD2 s) s := by
  have he := ((hasDerivAt_id s).const_mul (-beta)).exp
  have hi := (hasDerivAt_id s).inv hs
  convert he.neg.mul ((hi.const_mul beta).add (hi.pow 2)) using 1
  · funext y; simp [radialKernelD]
  · dsimp [radialKernelD2]
    field_simp
    ring

noncomputable def line (w v : Vec) (t : ℝ) : Vec := fun k => w k + t * v k

noncomputable def productD (w v : Vec) (i j : Fin 3) : ℝ := v i * w j + w i * v j

noncomputable def kernelD (w v : Vec) (i j : Fin 3) : ℝ :=
  productD w v i j * radialKernel (Ewald.sq w) +
    (w i * w j) * radialKernelD (Ewald.sq w) * (2 * dot w v)

noncomputable def kernelD2 (w v : Vec) (i j : Fin 3) : ℝ :=
  (2 * v i * v j) * radialKernel (Ewald.sq w) +
    2 * productD w v i j * radialKernelD (Ewald.sq w) * (2 * dot w v) +
    (w i * w j) * radialKernelD2 (Ewald.sq w) * (2 * dot w v) ^ 2 +
    (w i * w j) * radialKernelD (Ewald.sq w) * (2 * Ewald.sq v)

theorem line_component_hasDerivAt (w v : Vec) (t : ℝ) (k : Fin 3) :
    HasDerivAt (fun y => line w v y k) (v k) t := by
  convert (hasDerivAt_const t (w k)).add ((hasDerivAt_id t).mul_const (v k)) using 1
  · rfl
  · simp

theorem line_sq_hasDerivAt (w v : Vec) (t : ℝ) :
    HasDerivAt (fun y => Ewald.sq (line w v y)) (2 * dot (line w v t) v) t := by
  convert (((line_component_hasDerivAt w v t 0).pow 2).add
    ((line_component_hasDerivAt w v t 1).pow 2)).add ((line_component_hasDerivAt w v t 2).pow 2) using 1
  · rfl
  · simp only [dot, Fin.sum_univ_three, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring

theorem line_dot_hasDerivAt (w v : Vec) (t : ℝ) :
    HasDerivAt (fun y => dot (line w v y) v) (Ewald.sq v) t := by
  convert (((line_component_hasDerivAt w v t 0).mul_const (v 0)).add
    ((line_component_hasDerivAt w v t 1).mul_const (v 1))).add
    ((line_component_hasDerivAt w v t 2).mul_const (v 2)) using 1
  · funext y; simp [dot, Fin.sum_univ_three]
  · dsimp [Ewald.sq]; ring

theorem line_product_hasDerivAt (w v : Vec) (t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun y => line w v y i * line w v y j) (productD (line w v t) v i j) t := by
  convert (line_component_hasDerivAt w v t i).mul (line_component_hasDerivAt w v t j) using 1
  rfl

theorem line_productD_hasDerivAt (w v : Vec) (t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun y => productD (line w v y) v i j) (2 * v i * v j) t := by
  convert ((line_component_hasDerivAt w v t j).const_mul (v i)).add
    ((line_component_hasDerivAt w v t i).mul_const (v j)) using 1
  · rfl
  · ring

theorem kernel_hasDerivAt (w v : Vec) (t : ℝ) (i j : Fin 3)
    (hs : Ewald.sq (line w v t) ≠ 0) :
    HasDerivAt (fun y => kernel (line w v y) i j) (kernelD (line w v t) v i j) t := by
  have hg := (radialKernel_hasDerivAt hs).comp t (line_sq_hasDerivAt w v t)
  convert (line_product_hasDerivAt w v t i j).mul hg using 1
  · funext y; dsimp [kernel, radialKernel]; ring
  · dsimp [kernelD]; ring

theorem kernelD_hasDerivAt (w v : Vec) (t : ℝ) (i j : Fin 3)
    (hs : Ewald.sq (line w v t) ≠ 0) :
    HasDerivAt (fun y => kernelD (line w v y) v i j) (kernelD2 (line w v t) v i j) t := by
  have hg := (radialKernel_hasDerivAt hs).comp t (line_sq_hasDerivAt w v t)
  have hg1 := (radialKernelD_hasDerivAt hs).comp t (line_sq_hasDerivAt w v t)
  have hp := line_product_hasDerivAt w v t i j
  have hp1 := line_productD_hasDerivAt w v t i j
  have hs1 := (line_dot_hasDerivAt w v t).const_mul 2
  convert (hp1.mul hg).add ((hp.mul hg1).mul hs1) using 1
  · funext y; rfl
  · dsimp [kernelD2]; ring


theorem productD_sq_le (w v : Vec) (i j : Fin 3) :
    productD w v i j ^ 2 ≤ 4 * Ewald.sq w * Ewald.sq v := by
  have hv := sq_nonnegative v
  have hw := sq_nonnegative w
  have h1 : (v i * w j) ^ 2 ≤ Ewald.sq v * Ewald.sq w := by
    rw [mul_pow]
    exact mul_le_mul (component_sq_le v i) (component_sq_le w j) (sq_nonneg _) hv
  have h2 : (w i * v j) ^ 2 ≤ Ewald.sq v * Ewald.sq w := by
    rw [mul_comm, mul_pow]
    exact mul_le_mul (component_sq_le v j) (component_sq_le w i) (sq_nonneg _) hv
  dsimp [productD]
  nlinarith [sq_nonneg (v i * w j - w i * v j)]

theorem productD_dot_bound (w v : Vec) (i j : Fin 3) :
    |productD w v i j * (2 * dot w v)| ≤ 4 * Ewald.sq w * Ewald.sq v := by
  have h1 := productD_sq_le w v i j
  have h2 := dot_sq_le w v
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (productD w v i j + 2 * dot w v),
    sq_nonneg (productD w v i j - 2 * dot w v)]

/-- A directional Hessian bound expressed only in the two squared norms. -/
theorem kernelD2_bound (w v : Vec) (i j : Fin 3) (hs : 0 < Ewald.sq w) :
    |kernelD2 w v i j| ≤ Ewald.sq v * exp (-beta * Ewald.sq w) *
      (20 / Ewald.sq w + 18 * beta + 4 * beta ^ 2 * Ewald.sq w) := by
  let s := Ewald.sq w
  let V := Ewald.sq v
  let E := exp (-beta * s)
  let a := beta * s⁻¹ + s⁻¹ ^ 2
  let b := beta ^ 2 * s⁻¹ + 2 * beta * s⁻¹ ^ 2 + 2 * s⁻¹ ^ 3
  have hs0 : 0 < s := hs
  have hV : 0 ≤ V := sq_nonnegative v
  have hE : 0 ≤ E := (exp_pos _).le
  have hβ : 0 ≤ beta := by linarith [beta_ge_two]
  have hi : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0.le
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hg : radialKernel s = E * s⁻¹ := by dsimp [radialKernel, E]; ring
  have hg1 : radialKernelD s = -E * a := rfl
  have hg2 : radialKernelD2 s = E * b := rfl
  have hp : |w i * w j| ≤ s := abs_component_product w i j
  have hvp : |v i * v j| ≤ V := abs_component_product v i j
  have hpd : |productD w v i j * (2 * dot w v)| ≤ 4 * s * V := productD_dot_bound w v i j
  have hsd : (2 * dot w v) ^ 2 ≤ 4 * s * V := by nlinarith [dot_sq_le w v]
  have ht1 : |(2 * v i * v j) * radialKernel s| ≤ 2 * V * E * s⁻¹ := by
    rw [hg]
    calc
      _ = 2 * |v i * v j| * E * s⁻¹ := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hE hi)]
        rw [show 2 * v i * v j = 2 * (v i * v j) by ring, abs_mul]
        norm_num
        ring
      _ ≤ _ := by gcongr
  have ht2 : |2 * productD w v i j * radialKernelD s * (2 * dot w v)| ≤
      8 * s * V * E * a := by
    rw [hg1]
    calc
      _ = 2 * |productD w v i j * (2 * dot w v)| * E * a := by
        rw [show 2 * productD w v i j * (-E * a) * (2 * dot w v) =
          -(2 * (productD w v i j * (2 * dot w v)) * E * a) by ring]
        simp only [abs_neg, abs_mul, abs_of_nonneg hE, abs_of_nonneg ha]
        norm_num
      _ ≤ 2 * (4 * s * V) * E * a := by gcongr
      _ = _ := by ring
  have ht3 : |(w i * w j) * radialKernelD2 s * (2 * dot w v) ^ 2| ≤
      s * E * b * (4 * s * V) := by
    rw [hg2]
    calc
      _ = |w i * w j| * E * b * (2 * dot w v) ^ 2 := by
        rw [abs_mul, abs_mul (w i * w j) (E * b), abs_mul E b,
          abs_of_nonneg hE, abs_of_nonneg hb, abs_of_nonneg (sq_nonneg (2 * dot w v))]
        ring
      _ ≤ _ := by gcongr
  have ht4 : |(w i * w j) * radialKernelD s * (2 * V)| ≤ s * E * a * (2 * V) := by
    rw [hg1]
    calc
      _ = |w i * w j| * E * a * (2 * V) := by
        rw [abs_mul, abs_mul (w i * w j) (-E * a), abs_mul (-E) a,
          abs_neg, abs_of_nonneg hE, abs_of_nonneg ha,
          abs_of_nonneg (show 0 ≤ 2 * V by positivity)]
        ring
      _ ≤ _ := by gcongr
  have hsum : |kernelD2 w v i j| ≤
      2 * V * E * s⁻¹ + 8 * s * V * E * a + s * E * b * (4 * s * V) + s * E * a * (2 * V) := by
    unfold kernelD2
    calc
      _ ≤ |(2 * v i * v j) * radialKernel (Ewald.sq w) +
          2 * productD w v i j * radialKernelD (Ewald.sq w) * (2 * dot w v) +
          (w i * w j) * radialKernelD2 (Ewald.sq w) * (2 * dot w v) ^ 2| +
          |(w i * w j) * radialKernelD (Ewald.sq w) * (2 * Ewald.sq v)| := abs_add_le _ _
      _ ≤ (|(2 * v i * v j) * radialKernel (Ewald.sq w) +
          2 * productD w v i j * radialKernelD (Ewald.sq w) * (2 * dot w v)| +
          |(w i * w j) * radialKernelD2 (Ewald.sq w) * (2 * dot w v) ^ 2|) +
          |(w i * w j) * radialKernelD (Ewald.sq w) * (2 * Ewald.sq v)| := by
        gcongr; exact abs_add_le _ _
      _ ≤ ((|(2 * v i * v j) * radialKernel (Ewald.sq w)| +
          |2 * productD w v i j * radialKernelD (Ewald.sq w) * (2 * dot w v)|) +
          |(w i * w j) * radialKernelD2 (Ewald.sq w) * (2 * dot w v) ^ 2|) +
          |(w i * w j) * radialKernelD (Ewald.sq w) * (2 * Ewald.sq v)| := by
        gcongr; exact abs_add_le _ _
      _ ≤ _ := add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4
  apply hsum.trans_eq
  change _ = V * E * (20 / s + 18 * beta + 4 * beta ^ 2 * s)
  dsimp [a, b]
  field_simp
  ring


theorem shifted_gaussian_bound {u : Vec} (hu : Ewald.sq u ≤ 1) (z : Triple) :
    exp (-beta * Ewald.sq (fun k => coord z k + u k)) ≤ 9 * exp (-normSq z) := by
  have he : -beta * Ewald.sq (fun k => coord z k + u k) ≤ 2 - normSq z := by
    nlinarith [shifted_square_all u z,
      mul_nonneg (sub_nonneg.mpr beta_ge_two) (sq_nonnegative (fun k => coord z k + u k))]
  have he2 : exp (2 : ℝ) ≤ 9 := by
    have hh := pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_three.le 2
    convert hh using 1 <;> norm_num [← exp_nat_mul]
  calc
    _ ≤ exp (2 - normSq z) := exp_le_exp.mpr he
    _ = exp 2 * exp (-normSq z) := by rw [sub_eq_add_neg, exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right he2 (exp_pos _).le

/-- Uniform in the whole unit ball, including all line segments used to reach
Gamma. The h=0 reciprocal term is excluded explicitly. -/
theorem kernelD2_shifted_bound {u : Vec} (hu : Ewald.sq u ≤ 1)
    {z : Triple} (hz : reciprocal z) (hz0 : z ≠ 0) (v : Vec) (i j : Fin 3) :
    |kernelD2 (fun k => coord z k + u k) v i j| ≤
      Ewald.sq v * (2574 + 648 * normSq z) * exp (-normSq z) := by
  let w : Vec := fun k => coord z k + u k
  have hs : 1 / 8 ≤ Ewald.sq w := reciprocal_shift_sq_lower hz hz0 hu
  have hs0 : 0 < Ewald.sq w := by linarith
  have hs' : Ewald.sq w ≤ 2 * normSq z + 2 := by linarith [shifted_square_upper u z]
  have hb0 : 0 ≤ beta := by linarith [beta_ge_two]
  have hb2 : beta ^ 2 ≤ 9 := by nlinarith [beta_le_three]
  have hi : 20 / Ewald.sq w ≤ 160 := (div_le_iff₀ hs0).mpr (by linarith)
  have hpoly : 20 / Ewald.sq w + 18 * beta + 4 * beta ^ 2 * Ewald.sq w ≤
      286 + 72 * normSq z := by
    have hh := mul_le_mul_of_nonneg_right hb2 hs0.le
    nlinarith [beta_le_three]
  have hv := sq_nonnegative v
  have hn := normSq_nonneg z
  calc
    _ ≤ Ewald.sq v * exp (-beta * Ewald.sq w) *
        (20 / Ewald.sq w + 18 * beta + 4 * beta ^ 2 * Ewald.sq w) := kernelD2_bound w v i j hs0
    _ ≤ Ewald.sq v * (9 * exp (-normSq z)) * (286 + 72 * normSq z) := by
      gcongr
      exact shifted_gaussian_bound hu z
    _ = _ := by ring

@[simp] theorem sq_smul (x : ℝ) (v : Vec) : Ewald.sq (x • v) = x ^ 2 * Ewald.sq v := by
  simp only [Ewald.sq, Pi.smul_apply, smul_eq_mul]
  ring

theorem segment_sq_le {x t : ℝ} {v : Vec} (_hx : 0 ≤ x) (ht : t ∈ Set.Icc (-x) x)
    (hu : Ewald.sq (x • v) ≤ 1) : Ewald.sq (t • v) ≤ 1 := by
  have hsq : t ^ 2 ≤ x ^ 2 := by nlinarith [ht.1, ht.2]
  rw [sq_smul] at hu ⊢
  exact (mul_le_mul_of_nonneg_right hsq (sq_nonnegative v)).trans hu

/-- The paired reciprocal difference is quadratic in the radial parameter.
This estimate comes from the proved second derivative and the midpoint case
of the scalar interpolation theorem. -/
theorem kernel_pair_bound {x : ℝ} (hx : 0 ≤ x) (v : Vec)
    (hu : Ewald.sq (x • v) ≤ 1) {z : Triple} (hz : reciprocal z) (hz0 : z ≠ 0)
    (i j : Fin 3) :
    |kernel (fun k => coord z k + x * v k) i j +
      kernel (fun k => coord z k - x * v k) i j - 2 * kernel (coord z) i j| ≤
      x ^ 2 * (Ewald.sq v * (2574 + 648 * normSq z) * exp (-normSq z)) := by
  let M := Ewald.sq v * (2574 + 648 * normSq z) * exp (-normSq z)
  have hM : 0 ≤ M := by
    have hv := sq_nonnegative v
    have hn := normSq_nonneg z
    dsimp [M]
    positivity
  have hs (t : ℝ) (ht : t ∈ Set.Icc (-x) x) : Ewald.sq (line (coord z) v t) ≠ 0 := by
    have hh := reciprocal_shift_sq_lower hz hz0 (segment_sq_le hx ht hu)
    change 1 / 8 ≤ Ewald.sq (line (coord z) v t) at hh
    linarith
  have hf : ContinuousOn (fun t => kernel (line (coord z) v t) i j) (Set.Icc (-x) x) := by
    intro t ht
    exact (kernel_hasDerivAt (coord z) v t i j (hs t ht)).continuousAt.continuousWithinAt
  have h := Interpolation.linear_error (a := -x) (b := x) (t := 1 / 2) (M := M)
    (f := fun t => kernel (line (coord z) v t) i j)
    (f' := fun t => kernelD (line (coord z) v t) v i j)
    (f'' := fun t => kernelD2 (line (coord z) v t) v i j)
    (by linarith) hM (by norm_num) (by norm_num) hf
    (fun t ht => kernel_hasDerivAt (coord z) v t i j (hs t ⟨ht.1.le, ht.2.le⟩))
    (fun t ht => kernelD_hasDerivAt (coord z) v t i j (hs t ⟨ht.1.le, ht.2.le⟩))
    (fun t ht => kernelD2_shifted_bound (segment_sq_le hx ⟨ht.1.le, ht.2.le⟩ hu) hz hz0 v i j)
  have hmid : (1 - (1 / 2 : ℝ)) * -x + 1 / 2 * x = 0 := by ring
  rw [hmid] at h
  have h0 : line (coord z) v 0 = coord z := by funext k; simp [line]
  have hn : line (coord z) v (-x) = fun k => coord z k - x * v k := by funext k; simp [line, sub_eq_add_neg]
  rw [h0, hn] at h
  change |kernel (coord z) i j - ((1 - 1 / 2) * kernel (fun k => coord z k - x * v k) i j +
    1 / 2 * kernel (fun k => coord z k + x * v k) i j)| ≤ _ at h
  rw [abs_le] at h ⊢
  constructor <;> nlinarith

end BccSharp.Ewald
