import BccSharp.TwoSite.Bravais

set_option autoImplicit false

/-! Finite BCC star identities for the registration theorem and Stage5b. The proof of
registration of a nonsaturated minimizing injection remains separate. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb

def starTwice (label : Fin 14) (i : Fin 3) : ℤ :=
  if label.val < 8 then
    if label.val / (2 ^ i.val) % 2 = 0 then -1 else 1
  else if i.val = (label.val - 8) / 2 then
    if label.val % 2 = 0 then -2 else 2
  else 0

theorem starTwice_eq (label : Fin 14) (i : Fin 3) :
    (starTwice label i : ℝ) = 2 * star label i := by
  fin_cases label <;> fin_cases i <;> norm_num [starTwice, star]

/-- Convert the conventional star to the primitive Constants BCC basis. Its
inverse is the matrix with zero diagonal and all off-diagonal entries one. -/
def primitiveLabel (label : Fin 14) (i : Fin 3) : ℤ :=
  ((∑ j, starTwice label j) - starTwice label i) / 2

def isOddLabel (χ : Fin 7) (label : Fin 14) : Bool :=
  decide ((∑ i : Fin 3, (((χ.val + 1) / (2 ^ i.val) % 2 : Nat) : ℤ) * primitiveLabel label i) % 2 = 1)

theorem star_has_eight_odd (χ : Fin 7) :
    (Finset.univ.filter (fun label => isOddLabel χ label = true)).card = 8 := by
  fin_cases χ <;> decide

theorem star_second_moment (i j : Fin 3) :
    (∑ label : Fin 14, star label i * star label j) = if i = j then 4 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ, star]

theorem odd_star_balance_int :
    ∀ (χ : Fin 7) (i : Fin 3),
      (∑ label : Fin 14, if isOddLabel χ label then starTwice label i else 0) = 0 := by
  decide

theorem odd_star_balance (χ : Fin 7) (i : Fin 3) :
    (∑ label : Fin 14, if isOddLabel χ label then star label i else 0) = 0 := by
  have hInt := odd_star_balance_int χ i
  have hReal : (∑ label : Fin 14,
      if isOddLabel χ label then (starTwice label i : ℝ) else 0) = 0 := by
    exact_mod_cast hInt
  have hHalf : ∀ label : Fin 14, (if isOddLabel χ label then star label i else 0) =
      (1 / 2 : ℝ) * (if isOddLabel χ label then (starTwice label i : ℝ) else 0) := by
    intro label
    split_ifs
    · rw [starTwice_eq]
      ring
    · ring
  rw [Finset.sum_congr rfl (fun label _ => hHalf label), ← Finset.mul_sum, hReal, mul_zero]

/-- The two numerical coefficients used in the registered lower cost.
Annular weights enter with a nonnegative sign. -/
theorem registered_cost_bound (S H annular actual : ℝ)
    (hModel : actual = 25 * (4 * S + 8 * H) + annular) (hAnn : 0 ≤ annular) :
    100 * S + 200 * H ≤ actual := by
  linarith

end BccSharp.Coulomb
