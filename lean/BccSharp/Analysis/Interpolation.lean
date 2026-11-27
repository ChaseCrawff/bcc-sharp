module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The scalar interpolation estimate. The derivative
hypotheses are ordinary real derivatives, including continuity at the endpoints. -/

@[expose] public section

namespace BccSharp.Interpolation

open Set

private theorem quadratic_convex {a b M : ℝ} {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Ioo a b, -M ≤ f'' x) :
    ConvexOn ℝ (Icc a b) (fun x => M / 2 * x ^ 2 + f x) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    ((continuousOn_const.mul (continuousOn_id.pow 2)).add hf)
    (f' := fun x => M * x + f' x) (f'' := fun x => M + f'' x)
  · intro x hx
    rw [interior_Icc] at hx
    convert ((((hasDerivAt_id x).pow 2).const_mul (M / 2)).add (hf' x hx)).hasDerivWithinAt using 1
    simp only [id_eq, Nat.cast_ofNat]
    ring
  · intro x hx
    rw [interior_Icc] at hx
    convert (((hasDerivAt_id x).const_mul M).add (hf'' x hx)).hasDerivWithinAt using 1
    · funext y
      rfl
    · ring
  · intro x hx
    rw [interior_Icc] at hx
    linarith [hM x hx]

/-- Sharp `1/8` error bound for linear interpolation on an interval, including
both endpoints. The position is expressed by its convex weight `t`. -/
theorem linear_error {a b M t : ℝ} {f f' f'' : ℝ → ℝ} (hab : a ≤ b)
    (hM : 0 ≤ M) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Ioo a b, |f'' x| ≤ M) :
    |f ((1 - t) * a + t * b) - ((1 - t) * f a + t * f b)| ≤ (b - a) ^ 2 * M / 8 := by
  have hplus := quadratic_convex hf hf' hf'' (fun x hx => (abs_le.mp (hbound x hx)).1)
  have hminus := quadratic_convex (M := M) hf.neg
    (fun x hx => (hf' x hx).neg) (fun x hx => (hf'' x hx).neg)
    (fun x hx => by linarith [(abs_le.mp (hbound x hx)).2])
  have h₁ := hplus.2 (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩) (sub_nonneg.mpr ht') ht (by ring : 1 - t + t = 1)
  have h₂ := hminus.2 (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩) (sub_nonneg.mpr ht') ht (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, Pi.neg_apply] at h₁ h₂
  have hid : (1 - t) * (M / 2 * a ^ 2) + t * (M / 2 * b ^ 2) -
      M / 2 * ((1 - t) * a + t * b) ^ 2 = M * (b - a) ^ 2 / 2 * (t * (1 - t)) := by ring
  have htmax : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hh := mul_le_mul_of_nonneg_left htmax
    (show 0 ≤ M * (b - a) ^ 2 / 2 from by positivity)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The error bound is attained by a quadratic at the midpoint; the constant
cannot be made smaller for the stated class of functions. -/
theorem quadratic_midpoint_error (a b M : ℝ) (hM : 0 ≤ M) :
    |M / 2 * ((a + b) / 2) ^ 2 - (M / 2 * a ^ 2 + M / 2 * b ^ 2) / 2| =
      (b - a) ^ 2 * M / 8 := by
  have hid : M / 2 * ((a + b) / 2) ^ 2 - (M / 2 * a ^ 2 + M / 2 * b ^ 2) / 2 =
      -((b - a) ^ 2 * M / 8) := by ring
  rw [hid, abs_neg, abs_of_nonneg (by positivity)]

def lerp (t a b : ℝ) : ℝ := (1 - t) * a + t * b

theorem lerp_error {t a b c d e : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (ha : |a - c| ≤ e) (hb : |b - d| ≤ e) :
    |lerp t a b - lerp t c d| ≤ e := by
  have h₁ := (abs_le.mp ha).1
  have h₂ := (abs_le.mp ha).2
  have h₃ := (abs_le.mp hb).1
  have h₄ := (abs_le.mp hb).2
  have hlo := add_le_add (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ht'))
    (mul_le_mul_of_nonneg_left h₃ ht)
  have hhi := add_le_add (mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr ht'))
    (mul_le_mul_of_nonneg_left h₄ ht)
  unfold lerp
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

def trilinear (f : ℝ → ℝ → ℝ → ℝ) (a b c d e g tx ty tz : ℝ) : ℝ :=
  lerp tx (lerp ty (lerp tz (f a c e) (f a c g)) (lerp tz (f a d e) (f a d g)))
    (lerp ty (lerp tz (f b c e) (f b c g)) (lerp tz (f b d e) (f b d g)))

/-- Tensorization of the one-dimensional estimate. `hx`, `hy`, `hz` are the
slice estimates furnished by `linear_error`; no mixed partials are required. -/
theorem trilinear_error (f : ℝ → ℝ → ℝ → ℝ) (a b c d e g tx ty tz ex ey ez : ℝ)
    (htx : tx ∈ Icc (0 : ℝ) 1) (hty : ty ∈ Icc (0 : ℝ) 1)
    (hx : |f (lerp tx a b) (lerp ty c d) (lerp tz e g) -
      lerp tx (f a (lerp ty c d) (lerp tz e g)) (f b (lerp ty c d) (lerp tz e g))| ≤ ex)
    (hy : ∀ x ∈ ({a, b} : Set ℝ), |f x (lerp ty c d) (lerp tz e g) -
      lerp ty (f x c (lerp tz e g)) (f x d (lerp tz e g))| ≤ ey)
    (hz : ∀ x ∈ ({a, b} : Set ℝ), ∀ y ∈ ({c, d} : Set ℝ),
      |f x y (lerp tz e g) - lerp tz (f x y e) (f x y g)| ≤ ez) :
    |f (lerp tx a b) (lerp ty c d) (lerp tz e g) -
      trilinear f a b c d e g tx ty tz| ≤ ex + ey + ez := by
  have ha : a ∈ ({a, b} : Set ℝ) := by simp
  have hb : b ∈ ({a, b} : Set ℝ) := by simp
  have hc : c ∈ ({c, d} : Set ℝ) := by simp
  have hd : d ∈ ({c, d} : Set ℝ) := by simp
  have hxy := lerp_error htx.1 htx.2 (hy a ha) (hy b hb)
  have hxyz := lerp_error htx.1 htx.2
    (lerp_error hty.1 hty.2 (hz a ha c hc) (hz a ha d hd))
    (lerp_error hty.1 hty.2 (hz b hb c hc) (hz b hb d hd))
  calc
    _ ≤ |f (lerp tx a b) (lerp ty c d) (lerp tz e g) -
        lerp tx (f a (lerp ty c d) (lerp tz e g)) (f b (lerp ty c d) (lerp tz e g))| +
        |lerp tx (f a (lerp ty c d) (lerp tz e g)) (f b (lerp ty c d) (lerp tz e g)) -
          trilinear f a b c d e g tx ty tz| := abs_sub_le _ _ _
    _ ≤ ex + (ey + ez) := add_le_add hx
      ((abs_sub_le _ (lerp tx (lerp ty (f a c (lerp tz e g)) (f a d (lerp tz e g)))
        (lerp ty (f b c (lerp tz e g)) (f b d (lerp tz e g)))) _).trans
          (add_le_add hxy hxyz))
    _ = _ := by ring

end BccSharp.Interpolation
