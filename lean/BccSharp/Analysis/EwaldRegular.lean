module

public import BccSharp.Analysis.EwaldPeriodicity
public import BccSharp.Analysis.DividedExp
public import BccSharp.Analysis.WeightedTails

/-! The exact regular/plasmon decomposition and symmetric pairing of reciprocal
terms. These are identities for the actual absolutely convergent Ewald series. -/

@[expose] public section
namespace BccSharp.Ewald

open Real LatticeTails

noncomputable def plasmon (u : Vec) (i j : Fin 3) : ℝ := 8 * Real.pi * kernel u i j

noncomputable def regularSummand (u : Vec) (z : Triple) (i j : Fin 3) : ℝ :=
  if z = 0 then 0 else summand u z i j

noncomputable def regular (u : Vec) (i j : Fin 3) : ℝ := ∑' z : Triple, regularSummand u z i j

@[simp] theorem coord_zero : coord 0 = 0 := by funext i; fin_cases i <;> simp [coord]
@[simp] theorem kernel_zero (i j : Fin 3) : kernel 0 i j = 0 := by simp [kernel, Ewald.sq]

theorem summand_zero (u : Vec) (i j : Fin 3) : summand u 0 i j = plasmon u i j := by
  simp [summand, realTerm, reciprocalTerm, reciprocal, plasmon]

theorem regularSummand_bound (u : Vec) (z : Triple) (i j : Fin 3) :
    |regularSummand u z i j| ≤ majorant u * exp (-normSq z) := by
  unfold regularSummand
  split_ifs
  · simp only [abs_zero]; exact mul_nonneg (majorant_nonneg u) (exp_pos _).le
  · exact summand_bound_all u z i j

theorem regular_summable (u : Vec) (i j : Fin 3) : Summable (fun z => regularSummand u z i j) :=
  summable_of_gaussian_bound (majorant_nonneg u) (fun z => regularSummand_bound u z i j)

/-- The exact h=0 plasmon term is separated from the remaining full series. -/
theorem regular_decomposition (u : Vec) (i j : Fin 3) :
    matrix u i j = plasmon u i j + regular u i j := by
  have h := (summable_all u i j).tsum_eq_add_tsum_ite 0
  simpa only [matrix, regular, regularSummand, summand_zero] using h

@[simp] theorem regular_at_zero (i j : Fin 3) : regular 0 i j = 0 := by
  simp [regular, regularSummand, summand, realTerm, reciprocalTerm]

@[simp] theorem coord_neg (z : Triple) (i : Fin 3) : coord (-z) i = -coord z i := by
  fin_cases i <;> simp [coord]

@[simp] theorem normSq_neg (z : Triple) : normSq (-z) = normSq z := by simp [normSq]

@[simp] theorem bcc_neg_iff (z : Triple) : bcc (-z) ↔ bcc z := by
  dsimp [bcc]
  omega

@[simp] theorem reciprocal_neg_iff (z : Triple) : reciprocal (-z) ↔ reciprocal z := by
  dsimp [reciprocal]
  omega

@[simp] theorem kernel_neg (w : Vec) (i j : Fin 3) : kernel (-w) i j = kernel w i j := by
  simp [kernel, Ewald.sq]

@[simp] theorem phi_neg (z : Triple) (i j : Fin 3) : phi (-z) i j = phi z i j := by
  simp [phi]

theorem realTerm_neg_index (u : Vec) (z : Triple) (i j : Fin 3) :
    realTerm u (-z) i j = realTerm u z i j := by
  unfold realTerm
  simp only [bcc_neg_iff, neg_ne_zero, phi_neg, coord_neg]
  have he : Real.pi * (∑ k, u k * -coord z k) = -(Real.pi * ∑ k, u k * coord z k) := by
    simp [Finset.sum_neg_distrib]
  rw [he, cos_neg]

theorem realTerm_even (u : Vec) (z : Triple) (i j : Fin 3) :
    realTerm (-u) z i j = realTerm u z i j := by
  unfold realTerm
  have he : Real.pi * (∑ k, (-u) k * coord z k) = -(Real.pi * ∑ k, u k * coord z k) := by
    simp [Finset.sum_neg_distrib]
  rw [he, cos_neg]

theorem kernel_neg_shift (u : Vec) (z : Triple) (i j : Fin 3) :
    kernel (fun k => coord (-z) k + u k) i j = kernel (fun k => coord z k - u k) i j := by
  have he : (fun k => coord (-z) k + u k) = -(fun k => coord z k - u k) := by
    funext k
    simp only [coord_neg, Pi.neg_apply]
    ring
  rw [he, kernel_neg]

theorem reciprocalTerm_even_index (u : Vec) (z : Triple) (i j : Fin 3) :
    reciprocalTerm (-u) z i j = reciprocalTerm u (-z) i j := by
  simp only [reciprocalTerm, reciprocal_neg_iff, kernel_neg_shift, Pi.neg_apply, sub_eq_add_neg]
  have he : coord (-z) = -coord z := by funext k; exact coord_neg z k
  rw [he, kernel_neg]

theorem regularSummand_even_index (u : Vec) (z : Triple) (i j : Fin 3) :
    regularSummand (-u) z i j = regularSummand u (-z) i j := by
  simp only [regularSummand, neg_eq_zero, summand, realTerm_even, realTerm_neg_index,
    reciprocalTerm_even_index]

theorem regular_even (u : Vec) (i j : Fin 3) : regular (-u) i j = regular u i j := by
  unfold regular
  simp_rw [regularSummand_even_index]
  exact (Equiv.neg Triple).tsum_eq (fun z => regularSummand u z i j)

noncomputable def pairedRegularSummand (u : Vec) (z : Triple) (i j : Fin 3) : ℝ :=
  realTerm u z i j + if reciprocal z ∧ z ≠ 0 then 4 * Real.pi *
    (kernel (fun k => coord z k + u k) i j + kernel (fun k => coord z k - u k) i j -
      2 * kernel (coord z) i j) else 0

theorem pairedRegularSummand_eq (u : Vec) (z : Triple) (i j : Fin 3) :
    pairedRegularSummand u z i j = (regularSummand u z i j + regularSummand u (-z) i j) / 2 := by
  by_cases hz : z = 0
  · subst z
    simp [pairedRegularSummand, regularSummand, realTerm]
  · have he : coord (-z) = -coord z := by funext k; exact coord_neg z k
    have hk : kernel (coord (-z)) i j = kernel (coord z) i j := by rw [he, kernel_neg]
    have hkx : kernel (fun k => -coord z k + u k) i j =
        kernel (fun k => coord z k - u k) i j := by simpa using kernel_neg_shift u z i j
    have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    by_cases hr : reciprocal z <;>
      simp [pairedRegularSummand, regularSummand, hz, hnz, summand,
        realTerm_neg_index, reciprocalTerm, hr, hkx, hk]
    ring

/-- Pairing h and -h removes the odd reciprocal terms exactly. -/
theorem regular_paired_formula (u : Vec) (i j : Fin 3) :
    regular u i j = ∑' z, pairedRegularSummand u z i j := by
  have hs := regular_summable u i j
  have hn : Summable (fun z : Triple => regularSummand u (-z) i j) :=
    hs.comp_injective (neg_injective : Function.Injective (fun z : Triple => -z))
  simp_rw [pairedRegularSummand_eq, div_eq_mul_inv]
  have he : (∑' z : Triple, regularSummand u (-z) i j) = ∑' z, regularSummand u z i j :=
    (Equiv.neg Triple).tsum_eq (fun z => regularSummand u z i j)
  rw [tsum_mul_right, hs.tsum_add hn, he]
  unfold regular
  ring

end BccSharp.Ewald
