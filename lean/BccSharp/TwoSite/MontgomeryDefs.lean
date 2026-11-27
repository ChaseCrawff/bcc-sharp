import Mathlib

/-!
# Montgomery's minimal theta functions: shared definitions and interfaces

H. L. Montgomery, *Minimal theta functions*, Glasgow Math. J. 30 (1988) 75–85.

* `theta1 t β` is the paper's (7) for real `β`.
* `theta2 α x y` is the paper's (4): the theta function of the form
  `f(m,n) = |m + n(x+iy)|² / (2y)` of discriminant `-1`, in the paper's
  normalisation `Σ e^{-2παf}`.
* `Qser t β` is the paper's `Q(t; β) = -∂_β θ(t; β) / sin 2πβ` from Lemma 1,
  written as a Chebyshev series that is continuous in `β`.

The `Prop`s below are the interfaces between the modules that prove the paper's
lemmas. `Theorem1` is the inequality of the paper's Theorem 1.
-/

set_option autoImplicit false

namespace BccSharp.Coulomb.Montgomery

open Real

/-- Montgomery (7) for real `β`: `θ(t; β) = Σ_k e^{-π k² t} cos(2π k β)`. -/
noncomputable def theta1 (t β : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-π * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * β)

/-- Montgomery (4): `θ(α; x, y) = Σ_{m,n} e^{-πα((m+nx)² + (ny)²)/y}`. -/
noncomputable def theta2 (α x y : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, Real.exp (-π * α * (((p.1 : ℝ) + p.2 * x) ^ 2 + ((p.2 : ℝ) * y) ^ 2) / y)

/-- The hexagonal comparison `θ_h(α) = θ(α; 1/2, √3/2)`. -/
noncomputable def thetaHex (α : ℝ) : ℝ := theta2 α (1 / 2) (Real.sqrt 3 / 2)

/-- Montgomery's `Q(t; β)` as the series `4π Σ_{k ≥ 0} (k+1) e^{-π (k+1)² t} U_k(cos 2πβ)`,
which equals `-∂_β θ(t; β) / sin 2πβ` wherever the sine is nonzero. -/
noncomputable def Qser (t β : ℝ) : ℝ :=
  4 * π * ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * t) *
    (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos (2 * π * β))

/-- `∂_β θ(t; β) = -sin(2πβ) · Q(t; β)`. -/
def Theta1Deriv : Prop :=
  ∀ t : ℝ, 0 < t → ∀ β : ℝ, HasDerivAt (theta1 t) (-(Real.sin (2 * π * β) * Qser t β)) β

/-- Montgomery, Lemma 1, monotone part (non-strict): `Q(t; ·)` decreases on `[0, 1/2]`. -/
def Lemma1 : Prop :=
  ∀ t : ℝ, 0 < t → AntitoneOn (Qser t) (Set.Icc 0 (1 / 2))

/-- Montgomery, Lemma 2 for `0 < t < 1`, at the endpoints `β = 0` and `β = 1/2`
(proved as `smallT_bounds`). -/
def SmallT : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 →
    Qser t 0 ≤ (t * Real.sqrt t)⁻¹ ∧ (t * Real.sqrt t)⁻¹ * Real.exp (-π / (4 * t)) ≤ Qser t (1 / 2)

/-- Montgomery (2): `θ(1/α) = α θ(α)`. -/
def Duality : Prop :=
  ∀ α : ℝ, 0 < α → ∀ x y : ℝ, 0 < y → theta2 α⁻¹ x y = α * theta2 α x y

/-- Montgomery (13): Poisson summation in `m` in (4). -/
def Unfold13 : Prop :=
  ∀ α : ℝ, 0 < α → ∀ x y : ℝ, 0 < y →
    theta2 α x y = Real.sqrt (y / α) *
      ∑' n : ℤ, Real.exp (-π * α * y * (n : ℝ) ^ 2) * theta1 (y / α) (n * x)

/-- Montgomery, Lemma 4 (non-strict): `θ(α; ·, y)` decreases on `[0, 1/2]` when `y ≥ 1/2`. -/
def XMonotone : Prop :=
  ∀ α : ℝ, 0 < α → ∀ y : ℝ, 1 / 2 ≤ y →
    AntitoneOn (fun x => theta2 α x y) (Set.Icc 0 (1 / 2))

/-- Montgomery, Lemma 7 on the line `x = 1/2`: `θ(α; 1/2, ·)` increases on `[√3/2, ∞)`. -/
def YMonotoneHalf : Prop :=
  ∀ α : ℝ, 0 < α → MonotoneOn (fun y => theta2 α (1 / 2) y) (Set.Ici (Real.sqrt 3 / 2))

/-- Montgomery, Theorem 1 (the inequality): `θ_h(α) ≤ θ(α; x, y)` for every form. -/
def Theorem1 : Prop :=
  ∀ α : ℝ, 0 < α → ∀ x y : ℝ, 0 < y → thetaHex α ≤ theta2 α x y

/-- Gaussian summability over `ℤ`. -/
theorem summable_exp_neg_mul_int_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) := by
  have hτ : 0 < (((c / π : ℝ) : ℂ) * Complex.I).im := by
    simpa using div_pos hc Real.pi_pos
  refine ((summable_jacobiTheta₂_term_iff (0 : ℂ) _).mpr hτ).norm.congr fun k => ?_
  rw [norm_jacobiTheta₂_term]
  congr 1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero, Complex.zero_im]
  field_simp
  ring

end BccSharp.Coulomb.Montgomery
