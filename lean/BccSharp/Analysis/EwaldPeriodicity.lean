module

public import BccSharp.Analysis.EwaldDomain

/-! Exact reciprocal-lattice periodicity of the actual Ewald series. All
reindexing is on complete integer triples, with the parity restrictions proved. -/

@[expose] public section
namespace BccSharp.Ewald

open Real LatticeTails

@[simp] theorem coord_add (z h : Triple) (i : Fin 3) :
    coord (z + h) i = coord z i + coord h i := by
  fin_cases i <;> simp [coord]

theorem reciprocal_add_iff {h : Triple} (hh : reciprocal h) (z : Triple) :
    reciprocal (z + h) ↔ reciprocal z := by
  dsimp [reciprocal] at *
  omega

theorem reciprocal_bcc_dot_even {h z : Triple} (hh : reciprocal h) (hz : bcc z) :
    2 ∣ h.1 * z.1 + h.2.1 * z.2.1 + h.2.2 * z.2.2 := by
  have he : (h.1 * z.1 + h.2.1 * z.2.1 + h.2.2 * z.2.2) % 2 =
      ((h.1 + h.2.1 + h.2.2) * z.2.2) % 2 := by
    have h1 : (h.1 * z.1) % 2 = (h.1 * z.2.2) % 2 := by
      rw [Int.mul_emod h.1 z.1 2, Int.mul_emod h.1 z.2.2 2, hz.1, hz.2]
    have h2 : (h.2.1 * z.2.1) % 2 = (h.2.1 * z.2.2) % 2 := by
      rw [Int.mul_emod h.2.1 z.2.1 2, Int.mul_emod h.2.1 z.2.2 2, hz.2]
    rw [add_mul, add_mul]
    omega
  apply Int.dvd_of_emod_eq_zero
  rw [he, Int.mul_emod, hh]
  norm_num

theorem realTerm_periodic (u : Vec) {h : Triple} (hh : reciprocal h)
    (z : Triple) (i j : Fin 3) : realTerm (u + coord h) z i j = realTerm u z i j := by
  unfold realTerm
  split_ifs with hz
  · obtain ⟨m, hm⟩ := reciprocal_bcc_dot_even hh hz.1
    have hd : (∑ k, (u + coord h) k * coord z k) =
        (∑ k, u k * coord z k) + (h.1 * z.1 + h.2.1 * z.2.1 + h.2.2 * z.2.2 : ℤ) := by
      simp [Fin.sum_univ_three, coord]
      ring
    have he : Real.pi * (∑ k, (u + coord h) k * coord z k) =
        Real.pi * (∑ k, u k * coord z k) + (m : ℝ) * (2 * Real.pi) := by
      rw [hd, hm]
      push_cast
      ring
    rw [he, cos_add_int_mul_two_pi]
  · rfl

theorem reciprocalSummand_shift (u : Vec) {h : Triple} (hh : reciprocal h)
    (z : Triple) (i j : Fin 3) :
    reciprocalSummand (u + coord h) z i j = reciprocalSummand u (z + h) i j := by
  simp only [reciprocalSummand, reciprocal_add_iff hh]
  split_ifs
  · congr 1
    funext k
    simp only [Pi.add_apply, coord_add]
    ring
  · rfl

/-- Reciprocal-lattice periodicity, without a bounded-coordinate hypothesis. -/
theorem matrix_periodic (u : Vec) {h : Triple} (hh : reciprocal h) :
    matrix (u + coord h) = matrix u := by
  funext i j
  rw [series_formula_all, series_formula_all]
  have hr : (∑' z, realTerm (u + coord h) z i j) = ∑' z, realTerm u z i j :=
    tsum_congr fun z => realTerm_periodic u hh z i j
  have hs : (∑' z, reciprocalSummand (u + coord h) z i j) =
      ∑' z, reciprocalSummand u z i j := by
    simp_rw [reciprocalSummand_shift u hh]
    exact (Equiv.addRight h).tsum_eq (fun z => reciprocalSummand u z i j)
  rw [hr, hs]

end BccSharp.Ewald
