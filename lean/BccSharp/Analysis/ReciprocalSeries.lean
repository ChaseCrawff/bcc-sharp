module

public import BccSharp.Analysis.ReciprocalPotential
public import BccSharp.Analysis.GaussianSummability
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! Termwise differentiation of the complete Gaussian-damped reciprocal
potential, including arbitrary sublattices of a scaled integer lattice. -/
@[expose] public section
namespace BccSharp.ReciprocalSeries
open Real Ewald LatticeTails ReciprocalPotential
open RealSpaceHessian (basis dot_basis line_zero)

noncomputable def frequency (m : ℝ) (z : Triple) : Vec := (1/m) • coord z

theorem frequency_square (m : ℝ) (z : Triple) :
    Ewald.sq (frequency m z) = normSq z / m^2 := by
  simp only [frequency,sq_smul,sq_coord]
  ring

theorem frequency_zero (m : ℝ) : frequency m 0 = 0 := by
  ext i
  fin_cases i <;> simp [frequency,coord]

theorem frequency_gap {m : ℝ} (_hm : 0 < m) {z : Triple} (hz : z ≠ 0) :
    1/m^2 ≤ Ewald.sq (frequency m z) := by
  rw [frequency_square]
  exact div_le_div_of_nonneg_right (normSq_ge_one hz) (sq_nonneg m)

theorem amplitude_bound {m : ℝ} (hm : 0 < m) (z : Triple) :
    |amplitude (frequency m z)| ≤ (2*m^2/π)*exp (-beta*Ewald.sq (frequency m z)) := by
  by_cases hz : z = 0
  · subst z
    simp [frequency_zero,amplitude,Ewald.sq]
    positivity
  have hg := frequency_gap hm hz
  have hm2 : 0 < m^2 := sq_pos_of_pos hm
  have hs : 0 < Ewald.sq (frequency m z) := lt_of_lt_of_le (by positivity) hg
  have hp : (0 : ℝ) < 4*π^2*Ewald.sq (frequency m z) := by positivity
  rw [amplitude,abs_of_nonneg (by positivity),div_le_iff₀ hp]
  have hg' := (div_le_iff₀ hm2).mp hg
  have he := exp_pos (-beta*Ewald.sq (frequency m z))
  field_simp
  nlinarith

theorem component_ratio_bound {m : ℝ} (hm : 0 < m) {z : Triple} (hz : z ≠ 0) (i : Fin 3) :
    |frequency m z i| / Ewald.sq (frequency m z) ≤ 1+m^2 := by
  have hg := frequency_gap hm hz
  have hs : 0 < Ewald.sq (frequency m z) := lt_of_lt_of_le (by positivity) hg
  have hc := component_sq_le (frequency m z) i
  have ha : |frequency m z i| ≤ 1+Ewald.sq (frequency m z) := by
    nlinarith [sq_abs (frequency m z i),sq_nonneg (|frequency m z i|-1)]
  apply (div_le_iff₀ hs).2
  have hg' := (div_le_iff₀ (sq_pos_of_pos hm)).mp hg
  nlinarith

theorem gradient_bound {m : ℝ} (hm : 0 < m) (z : Triple) (x : Vec) (i : Fin 3) :
    |gradient (frequency m z) x i| ≤ 4*(1+m^2)*exp (-beta*Ewald.sq (frequency m z)) := by
  by_cases hz : z = 0
  · subst z
    simp [gradient,frequency_zero,amplitude,Ewald.sq]
    positivity
  have hs : 0 < Ewald.sq (frequency m z) := lt_of_lt_of_le (by positivity) (frequency_gap hm hz)
  have heq : gradient (frequency m z) x i =
      -4*exp (-beta*Ewald.sq (frequency m z))*
        (frequency m z i/Ewald.sq (frequency m z))*sin (phase (frequency m z) x) := by
    unfold gradient amplitude
    field_simp
    ring
  rw [heq,abs_mul,abs_mul,abs_mul,abs_div,abs_of_pos hs,abs_of_pos (exp_pos _)]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc
    _ ≤ 4*exp (-beta*Ewald.sq (frequency m z))*(1+m^2)*1 := by
      gcongr
      · exact component_ratio_bound hm hz i
      · exact abs_sin_le_one _
    _ = _ := by ring

theorem hessian_bound (w x : Vec) (i j : Fin 3) :
    |ReciprocalPotential.hessian w x i j| ≤ 8*π*exp (-beta*Ewald.sq w) := by
  rw [hessian_formula,abs_mul,abs_mul,abs_neg,abs_of_pos (by positivity : (0 : ℝ) < 8*π)]
  calc
    _ ≤ (8*π)*exp (-beta*Ewald.sq w)*1 := by
      gcongr
      · exact kernel_bound w i j
      · exact abs_cos_le_one _
    _ = _ := mul_one _

theorem gaussian_summable {m : ℝ} (hm : 0 < m) :
    Summable (fun z : Triple => exp (-beta*Ewald.sq (frequency m z))) := by
  have hb : 0 < beta := lt_of_lt_of_le (by norm_num) beta_ge_two
  convert scaled_gaussian_summable (div_pos hb (sq_pos_of_pos hm)) using 1
  funext z
  rw [frequency_square]
  congr 1
  ring

noncomputable def mask (P : Triple → Prop) (f : Triple → ℝ) (z : Triple) : ℝ :=
  by
    classical
    exact if P z then f z else 0

theorem summable_mask {P : Triple → Prop} {f g : Triple → ℝ}
    (hg : Summable g) (hf : ∀ z, |f z| ≤ g z) : Summable (mask P f) := by
  classical
  apply hg.of_norm_bounded
  intro z
  simp only [mask,Real.norm_eq_abs]
  split_ifs
  · exact hf z
  · simpa using (abs_nonneg (f z)).trans (hf z)

noncomputable def potential (m : ℝ) (P : Triple → Prop) (x : Vec) : ℝ :=
  ∑' z, mask P (fun z => ReciprocalPotential.potential (frequency m z) x) z
noncomputable def gradient (m : ℝ) (P : Triple → Prop) (x : Vec) (i : Fin 3) : ℝ :=
  ∑' z, mask P (fun z => ReciprocalPotential.gradient (frequency m z) x i) z
noncomputable def hessian (m : ℝ) (P : Triple → Prop) (x : Vec) (i j : Fin 3) : ℝ :=
  deriv (fun t => deriv (fun s => potential m P (line (line x (basis j) t) (basis i) s)) 0) 0

theorem mask_bound {P : Triple → Prop} {f : Triple → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ z, |f z| ≤ C) (z : Triple) : |mask P f z| ≤ C := by
  classical
  simp only [mask]
  split_ifs
  · exact hf z
  · simpa using hC

theorem potential_mode_bound {m : ℝ} (hm : 0 < m) (z : Triple) (x : Vec) :
    |ReciprocalPotential.potential (frequency m z) x| ≤
      (2*m^2/π)*exp (-beta*Ewald.sq (frequency m z)) := by
  rw [ReciprocalPotential.potential,abs_mul]
  calc
    _ ≤ |amplitude (frequency m z)| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
    _ ≤ _ := by simpa using amplitude_bound hm z

theorem potential_summable {m : ℝ} (hm : 0 < m) (P : Triple → Prop) (x : Vec) :
    Summable (mask P (fun z => ReciprocalPotential.potential (frequency m z) x)) :=
  summable_mask ((gaussian_summable hm).mul_left (2*m^2/π)) (fun z => potential_mode_bound hm z x)

theorem gradient_summable {m : ℝ} (hm : 0 < m) (P : Triple → Prop) (x : Vec) (i : Fin 3) :
    Summable (mask P (fun z => ReciprocalPotential.gradient (frequency m z) x i)) :=
  summable_mask ((gaussian_summable hm).mul_left (4*(1+m^2))) (fun z => gradient_bound hm z x i)

theorem mode_line_deriv (w x : Vec) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => ReciprocalPotential.potential w (line x (basis i) s))
      (ReciprocalPotential.gradient w (line x (basis i) t) i) t := by
  convert ((phase_hasDerivAt w x (basis i) t).cos).const_mul (amplitude w) using 1
  · rfl
  · simp only [ReciprocalPotential.gradient,dot_basis]
    ring

theorem gradient_line_deriv (w x : Vec) (i j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => ReciprocalPotential.gradient w (line x (basis j) s) i)
      (ReciprocalPotential.hessian w (line x (basis j) t) i j) t := by
  convert (((phase_hasDerivAt w x (basis j) t).sin).const_mul (-amplitude w)).mul_const (2*π*w i) using 1
  · rfl
  · rw [hessian_formula]
    simp only [dot_basis,amplitude,kernel]
    field_simp
    ring

theorem potential_hasDerivAt {m : ℝ} (hm : 0 < m) (P : Triple → Prop) (x : Vec) (i : Fin 3) :
    HasDerivAt (fun t => potential m P (line x (basis i) t)) (gradient m P x i) 0 := by
  classical
  have hd (z : Triple) (t : ℝ) :
      HasDerivAt (fun s => mask P (fun z => ReciprocalPotential.potential (frequency m z) (line x (basis i) s)) z)
        (mask P (fun z => ReciprocalPotential.gradient (frequency m z) (line x (basis i) t) i) z) t := by
    by_cases hz : P z
    · simpa only [mask,ite_eq_left hz] using mode_line_deriv (frequency m z) x i t
    · simpa only [mask,ite_eq_right hz] using hasDerivAt_const t (0 : ℝ)
  have hb (z : Triple) (t : ℝ) :
      ‖mask P (fun z => ReciprocalPotential.gradient (frequency m z) (line x (basis i) t) i) z‖ ≤
        4*(1+m^2)*exp (-beta*Ewald.sq (frequency m z)) := by
    simp only [mask,Real.norm_eq_abs]
    split_ifs
    · exact gradient_bound hm z _ i
    · simp only [abs_zero]; positivity
  have hp := potential_summable hm P (line x (basis i) 0)
  have hd := hasDerivAt_tsum ((gaussian_summable hm).mul_left (4*(1+m^2))) hd hb hp 0
  simpa only [potential,gradient,line_zero] using hd

theorem gradient_hasDerivAt {m : ℝ} (hm : 0 < m) (P : Triple → Prop) (x : Vec) (i j : Fin 3) :
    HasDerivAt (fun t => gradient m P (line x (basis j) t) i)
      (∑' z, mask P (fun z => ReciprocalPotential.hessian (frequency m z) x i j) z) 0 := by
  classical
  have hd (z : Triple) (t : ℝ) :
      HasDerivAt (fun s => mask P (fun z => ReciprocalPotential.gradient (frequency m z) (line x (basis j) s) i) z)
        (mask P (fun z => ReciprocalPotential.hessian (frequency m z) (line x (basis j) t) i j) z) t := by
    by_cases hz : P z
    · simpa only [mask,ite_eq_left hz] using gradient_line_deriv (frequency m z) x i j t
    · simpa only [mask,ite_eq_right hz] using hasDerivAt_const t (0 : ℝ)
  have hb (z : Triple) (t : ℝ) :
      ‖mask P (fun z => ReciprocalPotential.hessian (frequency m z) (line x (basis j) t) i j) z‖ ≤
        (8*π)*exp (-beta*Ewald.sq (frequency m z)) := by
    simp only [mask,Real.norm_eq_abs]
    split_ifs
    · exact hessian_bound _ _ i j
    · simp only [abs_zero]; positivity
  have hp := gradient_summable hm P (line x (basis j) 0) i
  have hh := hasDerivAt_tsum ((gaussian_summable hm).mul_left (8*π)) hd hb hp 0
  simpa only [gradient,line_zero] using hh

/-- Both coordinate differentiations are applied to the actual infinite
potential. No derivative interchange is left as a premise. -/
theorem hessian_formula {m : ℝ} (hm : 0 < m) (P : Triple → Prop) (x : Vec) (i j : Fin 3) :
    hessian m P x i j =
      ∑' z, mask P (fun z => -(8*π)*kernel (frequency m z) i j*cos (phase (frequency m z) x)) z := by
  have he : (fun t => deriv (fun s => potential m P (line (line x (basis j) t) (basis i) s)) 0) =
      (fun t => gradient m P (line x (basis j) t) i) := by
    funext t
    exact (potential_hasDerivAt hm P _ i).deriv
  rw [hessian,he]
  simpa only [ReciprocalPotential.hessian_formula] using (gradient_hasDerivAt hm P x i j).deriv

end BccSharp.ReciprocalSeries
