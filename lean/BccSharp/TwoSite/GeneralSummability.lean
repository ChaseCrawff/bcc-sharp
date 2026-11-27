import BccSharp.TwoSite.EwaldCellRepetition
import BccSharp.Analysis.GaussianSummability
import BccSharp.Analysis.Ewald

set_option autoImplicit false

/-! Absolute convergence for the screened Ewald terms at every
invertible period basis and every positive screening. No uniform shape
estimate is needed for the finite-index invariance theorem. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb
open BccSharp

private def tripleVector : LatticeTails.Triple ≃ IntVec where
  toFun z := ![z.1, z.2.1, z.2.2]
  invFun n := (n 0, n 1, n 2)
  left_inv z := by rcases z with ⟨a, b, c⟩; rfl
  right_inv n := by funext i; fin_cases i <;> rfl

private theorem frob_nonnegative (B : Mat) : 0 ≤ frobSq B := by
  unfold frobSq
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (B i j)))

theorem mulVec_sq_le_frob (B : Mat) (x : Vec) : sq (B.mulVec x) ≤ frobSq B * sq x := by
  unfold sq frobSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa [Matrix.mulVec, dotProduct] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) (fun j => B i j) x)

theorem matrix_coercivity (B : Mat) (hB : B.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Vec, c*sq x ≤ sq (B.mulVec x) := by
  let C := frobSq B⁻¹ + 1
  have hC : 0 < C := by unfold C; linarith [frob_nonnegative B⁻¹]
  refine ⟨1/C, one_div_pos.mpr hC, fun x => ?_⟩
  have h := mulVec_sq_le_frob B⁻¹ (B.mulVec x)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec] at h
  rw [show 1/C*sq x = sq x/C by ring]
  apply (div_le_iff₀ hC).mpr
  unfold C
  nlinarith [sq_nonnegative (B.mulVec x)]

theorem shifted_sq (x y : Vec) : sq y/2 - sq x ≤ sq (x+y) := by
  have point (i : Fin 3) : (y i)^2/2-(x i)^2 ≤ (x i+y i)^2 := by
    nlinarith [sq_nonneg (x i+y i/2)]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => point i)
  simpa [sq,Finset.sum_sub_distrib,Finset.sum_div] using h

private theorem triple_norm_eq (z : LatticeTails.Triple) :
    sq (castVec (tripleVector z)) = LatticeTails.normSq z := by
  simp [sq,castVec,tripleVector,LatticeTails.normSq,Fin.sum_univ_three]

theorem integerGaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : IntVec => Real.exp (-a*sq (castVec n))) := by
  apply tripleVector.summable_iff.mp
  simpa only [Function.comp_def, triple_norm_eq] using LatticeTails.scaled_gaussian_summable ha

private theorem above_cube {R : ℕ} {z : LatticeTails.Triple} (h : z ∉ LatticeTails.cube R) :
    (R : ℝ) ≤ LatticeTails.normSq z := by
  have h' := LatticeTails.outside_square R h
  rw [LatticeTails.normSq_eq_square]
  have hR : R ≤ R*(R+1) := by nlinarith
  have hsmall : R ≤ LatticeTails.length z+R*(R+1) := by omega
  exact_mod_cast hsmall.trans h'

private theorem term_of_outside_dominance (f : LatticeTails.Triple → ℝ) (C a : ℝ)
    (hC : 0 ≤ C) (ha : 0 < a) (R : ℕ)
    (bound : ∀ z ∉ LatticeTails.cube R, |f z| ≤ C*Real.exp (-a*LatticeTails.normSq z)) :
    Summable f := by
  apply summable_of_finset_compl (LatticeTails.cube R)
  have h := ((LatticeTails.scaled_gaussian_summable ha).mul_left C).subtype
    (fun z => z ∉ LatticeTails.cube R)
  apply h.of_norm_bounded
  intro z
  rw [Real.norm_eq_abs]
  exact bound z.val z.property

theorem screened_lattice_summable (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    Summable (fun n : IntVec => screened α (x+linearImage B n)) := by
  obtain ⟨c, hc, coerce⟩ := matrix_coercivity B hB
  obtain ⟨R, hR⟩ := exists_nat_gt (2*(sq x+1)/c)
  apply tripleVector.summable_iff.mp
  apply term_of_outside_dominance
    (C := Real.exp (α^2*sq x)/(α*Real.sqrt Real.pi)) (a := α^2*c/2)
    (hC := by positivity) (ha := by positivity) (R := R)
  intro z hz
  let n := tripleVector z
  let y := linearImage B n
  let r := Real.sqrt (sq (x+y))
  have hco : c*LatticeTails.normSq z ≤ sq y := by
    simpa [y,n,linearImage,triple_norm_eq] using coerce (castVec n)
  have hx := shifted_sq x y
  have hbig : 1 ≤ sq (x+y) := by
    have hmin := (div_lt_iff₀ hc).mp (hR.trans_le (above_cube hz))
    linarith
  have rpos : 0 < r := Real.sqrt_pos.mpr (zero_lt_one.trans_le hbig)
  have hr2 : r^2 = sq (x+y) := Real.sq_sqrt (sq_nonnegative _)
  have hden : α*Real.sqrt Real.pi ≤ α*Real.sqrt Real.pi*sq (x+y) :=
    le_mul_of_one_le_right (by positivity) hbig
  change |screened α (x+y)| ≤ _
  change |Gaussian.erfcIntegral (α*r)/r| ≤ _
  rw [abs_of_nonneg (div_nonneg (Ewald.erfc_nonneg _) rpos.le)]
  calc
    _ ≤ (Real.exp (-(α*r)^2)/(α*r*Real.sqrt Real.pi))/r :=
      div_le_div_of_nonneg_right (Gaussian.erfc_upper (mul_pos ha rpos)) rpos.le
    _ = Real.exp (-α^2*sq (x+y))/(α*Real.sqrt Real.pi*sq (x+y)) := by
      rw [mul_pow, hr2, div_div]
      rw [show (α*r*Real.sqrt Real.pi)*r = α*Real.sqrt Real.pi*r^2 by ring, hr2, neg_mul]
    _ ≤ Real.exp (-α^2*sq (x+y))/(α*Real.sqrt Real.pi) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
    _ ≤ _ := by
      have u : -α^2*sq (x+y) ≤ α^2*sq x-(α^2*c/2)*LatticeTails.normSq z := by
        have h := mul_le_mul_of_nonneg_left (show c*LatticeTails.normSq z/2 ≤ sq (x+y)+sq x by linarith)
          (sq_nonneg α)
        linarith
      rw [show Real.exp (α^2*sq x)/(α*Real.sqrt Real.pi)*
        Real.exp (-(α^2*c/2)*LatticeTails.normSq z) =
        Real.exp (α^2*sq x-(α^2*c/2)*LatticeTails.normSq z)/(α*Real.sqrt Real.pi) by
          rw [sub_eq_add_neg,Real.exp_add]; ring]
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr u) (by positivity)

theorem reciprocal_lattice_summable (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) :
    Summable (reciprocalGreenTerm α B) := by
  let M := (B⁻¹).transpose
  have hM : M.det ≠ 0 := by
    dsimp [M]
    rw [Matrix.det_transpose]
    intro hz
    have h := congrArg Matrix.det (Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB))
    rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨d, hd, coerce⟩ := matrix_coercivity M hM
  let c := (2*Real.pi)^2*d
  have hc : 0 < c := by unfold c; positivity
  obtain ⟨R,hR⟩ := exists_nat_gt (1/c)
  apply tripleVector.summable_iff.mp
  apply term_of_outside_dominance
    (C := 1) (a := c/(4*α^2)) (hC := by norm_num) (ha := by positivity) (R := R)
  intro z hz
  let n := tripleVector z
  have hsq : c*LatticeTails.normSq z ≤ sq (dualWave B n) := by
    rw [dualWave,sq_smul]
    unfold c
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by
      simpa [n,triple_norm_eq] using coerce (castVec n)) (sq_nonneg _)
  have hq : 1 ≤ sq (dualWave B n) := (le_of_lt ((div_lt_iff₀ hc).mp (hR.trans_le (above_cube hz)))).trans
    ((mul_comm (LatticeTails.normSq z) c).le.trans hsq)
  have hn : n ≠ 0 := by
    intro h
    rw [h,dualWave_zero] at hq
    norm_num [sq] at hq
  unfold Function.comp reciprocalGreenTerm
  change |(if n=0 then 0 else Real.exp (-(sq (dualWave B n)/(4*α^2)))/sq (dualWave B n))| ≤ _
  rw [if_neg hn,abs_of_nonneg (div_nonneg (Real.exp_pos _).le (sq_nonnegative _)),one_mul]
  refine (div_le_self (Real.exp_pos _).le hq).trans (Real.exp_le_exp.mpr ?_)
  have he := div_le_div_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 4*α^2)
  rw [show c*LatticeTails.normSq z/(4*α^2) =
    (c/(4*α^2))*LatticeTails.normSq z by ring] at he
  linarith

theorem greenPerParticle_repetition {ι κ : Type} [Fintype ι] [Fintype κ] {B C : Mat}
    (rep : PeriodRepetition B C κ) (hB : B.det ≠ 0) (hC : C.det ≠ 0)
    (α : ℝ) (ha : 0 < α) (s : ι → Vec) (hm : 0 < Fintype.card κ) (hn : 0 < Fintype.card ι) :
    greenPerParticle α C (repeatedSites rep s) = greenPerParticle α B s := by
  apply screened_per_particle_repetition rep hB hC α s hm hn
  · intro i j
    exact (periodIndices B hB).summable_iff.mp (screened_lattice_summable α ha B hB (s i-s j))
  · exact reciprocal_lattice_summable α ha B hB
  · exact reciprocal_lattice_summable α ha C hC

end BccSharp.Coulomb
