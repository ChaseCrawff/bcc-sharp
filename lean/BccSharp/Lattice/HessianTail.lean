import BccSharp.Lattice.KernelJet

set_option autoImplicit false

/-! Analytic and scalar arithmetic parts of the Lattice signed Hessian
tail. Bounds on the actual metric, its inverse, and their chart derivatives
are separate inputs to the per-index shell step. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Intervals (Ball)

theorem kernelValue_positive_bound (k : KernelKind) {t : ℝ} (ht : 0 < t) :
    0 ≤ kernelValue k t ∧ kernelValue k t ≤ Real.exp (-t)/t := by
  cases k with
  | one =>
      have he : kernelValue .one t = Real.exp (-t)/t := by
        simpa [kernelValue,KernelKind.power] using gKernel_one ht
      rw [he]
      exact ⟨by positivity,le_rfl⟩
  | half =>
      have he : kernelValue .half t = Real.sqrt Real.pi*Gaussian.erfcIntegral (Real.sqrt t)/Real.sqrt t := by
        simpa [kernelValue,KernelKind.power] using halfKernel_formula ht
      rw [he]
      refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Ewald.erfc_nonneg _)) (Real.sqrt_nonneg _),?_⟩
      have hr := Real.sqrt_pos.mpr ht
      have hπ := Real.sqrt_pos.mpr Real.pi_pos
      calc
        _ ≤ Real.sqrt Real.pi*(Real.exp (-(Real.sqrt t)^2)/(Real.sqrt t*Real.sqrt Real.pi))/Real.sqrt t :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Gaussian.erfc_upper hr) hπ.le) hr.le
        _ = _ := by
          rw [Real.sq_sqrt ht.le]
          have he : Real.sqrt Real.pi*(Real.exp (-t)/(Real.sqrt t*Real.sqrt Real.pi))/Real.sqrt t =
              Real.exp (-t)/(Real.sqrt t)^2 := by field_simp [hr.ne',hπ.ne'] <;> ring
          rw [he,Real.sq_sqrt ht.le]

theorem kernelDerivative_bounds (k : KernelKind) {t : ℝ} (ht : 1 ≤ t) :
    |kernelSlope k t| ≤ 2*Real.exp (-t)/t ∧
    |kernelCurvature k t| ≤ 5*Real.exp (-t)/t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hk : (0 : ℝ) ≤ k.power ∧ (k.power : ℝ) ≤ 1 := by cases k <;> norm_num [KernelKind.power]
  have hg := kernelValue_positive_bound k ht0
  have hg' : kernelValue k t ≤ Real.exp (-t) := hg.2.trans (div_le_self (Real.exp_pos _).le ht)
  have hv : (k.power : ℝ)*kernelValue k t ≤ Real.exp (-t) :=
    (mul_le_of_le_one_left hg.1 hk.2).trans hg'
  have hn : kernelSlope k t ≤ 0 := by
    unfold kernelSlope
    apply div_nonpos_of_nonpos_of_nonneg _ ht0.le
    have hh := mul_nonneg hk.1 hg.1
    linarith [Real.exp_pos (-t)]
  have hs : -kernelSlope k t ≤ 2*Real.exp (-t)/t := by
    unfold kernelSlope
    rw [← neg_div,neg_neg]
    exact div_le_div_of_nonneg_right (by linarith) ht0.le
  refine ⟨by simpa [abs_of_nonpos hn] using hs,?_⟩
  have hp : 0 ≤ kernelCurvature k t := by
    unfold kernelCurvature
    exact div_nonneg (sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (by linarith [hk.1]) hn).trans
      (Real.exp_pos _).le)) ht0.le
  rw [abs_of_nonneg hp, kernelCurvature]
  apply div_le_div_of_nonneg_right _ ht0.le
  have hh := hs.trans (div_le_self (by positivity) ht)
  have hmul := mul_le_mul (show (k.power : ℝ)+1 ≤ 2 by linarith [hk.2]) hh
    (neg_nonneg.mpr hn) (by norm_num : (0 : ℝ)≤2)
  linarith

theorem kernelHessian_entry_bound (k : KernelKind) {t u v w : ℝ} (ht : 1 ≤ t) :
    |Real.pi^2*kernelCurvature k t*u*v+Real.pi*kernelSlope k t*w| ≤
      5*Real.exp (-t)/t*(Real.pi^2 * |u| * |v| + Real.pi * |w|) := by
  have h := kernelDerivative_bounds k ht
  have ht' : 0 < t := zero_lt_one.trans_le ht
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h.2 (sq_nonneg Real.pi)) (abs_nonneg u))
    (abs_nonneg v)
  have hs : |kernelSlope k t| ≤ 5*Real.exp (-t)/t := h.1.trans
    (div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-t)]) ht'.le)
  have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs Real.pi_pos.le) (abs_nonneg w)
  have hsum := add_le_add h₁ h₂
  calc
    _ ≤ |Real.pi^2*kernelCurvature k t*u*v| + |Real.pi*kernelSlope k t*w| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (sq_nonneg Real.pi)]
      convert hsum using 1 <;> ring

def gaussianShell (a c₂ c₄ : ℝ) (n : ℕ) : ℝ :=
  (c₂*(n : ℝ)^2+c₄*(n : ℝ)^4)*Real.exp (-a*(n : ℝ)^2)

def gaussianRatio (a : ℝ) (N : ℕ) : ℝ :=
  (((N : ℝ)+1)/(N : ℝ))^4*Real.exp (-a*(2*(N : ℝ)+1))

theorem gaussianShell_step (a c₂ c₄ : ℝ) (ha : 0 ≤ a) (hc₂ : 0 ≤ c₂) (hc₄ : 0 ≤ c₄)
    (N n : ℕ) (hN : 0 < N) (hn : N ≤ n) :
    gaussianShell a c₂ c₄ (n+1) ≤ gaussianRatio a N * gaussianShell a c₂ c₄ n := by
  have Npos : (0 : ℝ)<N := by exact_mod_cast hN
  have nn : (0 : ℝ)≤n := Nat.cast_nonneg _
  have hn' : (N : ℝ)≤n := by exact_mod_cast hn
  let r : ℝ := (((N : ℝ)+1)/(N : ℝ))
  have hr : 1 ≤ r := (le_div_iff₀ Npos).mpr (by linarith)
  have hx : (n : ℝ)+1 ≤ r*(n : ℝ) := by
    unfold r
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ Npos).mpr
    linarith [show ((n : ℝ)+1)*N-((N : ℝ)+1)*n=(N : ℝ)-n by ring]
  have r2 : r^2 ≤ r^4 := by
    have h := mul_le_mul_of_nonneg_right (one_le_pow₀ hr : 1≤ r^2) (sq_nonneg r)
    linarith [show r^2*r^2=r^4 by ring]
  have h2 : ((n : ℝ)+1)^2 ≤ r^4*(n : ℝ)^2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(n : ℝ)+1) hx 2
    rw [mul_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right r2 (sq_nonneg _))
  have h4 : ((n : ℝ)+1)^4 ≤ r^4*(n : ℝ)^4 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(n : ℝ)+1) hx 4
  have hp : c₂*((n : ℝ)+1)^2+c₄*((n : ℝ)+1)^4 ≤ r^4*(c₂*(n : ℝ)^2+c₄*(n : ℝ)^4) := by
    linarith [mul_le_mul_of_nonneg_left h2 hc₂,mul_le_mul_of_nonneg_left h4 hc₄]
  have hExp : Real.exp (-a*((n : ℝ)+1)^2) ≤ Real.exp (-a*(n : ℝ)^2)*Real.exp (-a*(2*(N : ℝ)+1)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hn' ha]
  have h := mul_le_mul hp hExp (Real.exp_pos _).le (by positivity :
    0 ≤ r^4*(c₂*(n : ℝ)^2+c₄*(n : ℝ)^4))
  unfold gaussianShell gaussianRatio
  push_cast
  change (c₂*((n : ℝ)+1)^2+c₄*((n : ℝ)+1)^4)*Real.exp (-a*((n : ℝ)+1)^2) ≤ _
  convert h using 1 <;> unfold r <;> ring

theorem gaussianShell_tail (a c₂ c₄ ρ : ℝ) (ha : 0 ≤ a) (hc₂ : 0 ≤ c₂) (hc₄ : 0 ≤ c₄)
    (N : ℕ) (hN : 0 < N) (hρ : gaussianRatio a N ≤ ρ) (hr : ρ < 1) :
    Summable (fun k => gaussianShell a c₂ c₄ (N+1+k)) ∧
    (∑' k, gaussianShell a c₂ c₄ (N+1+k)) ≤ gaussianShell a c₂ c₄ N*ρ/(1-ρ) := by
  have hr0 : 0 ≤ ρ := (show 0 ≤ gaussianRatio a N by unfold gaussianRatio; positivity).trans hρ
  have nn (n : ℕ) : 0 ≤ gaussianShell a c₂ c₄ n := by unfold gaussianShell; positivity
  have step (n : ℕ) (hn : N≤n) : gaussianShell a c₂ c₄ (n+1) ≤ ρ*gaussianShell a c₂ c₄ n :=
    (gaussianShell_step a c₂ c₄ ha hc₂ hc₄ N n hN hn).trans
      (mul_le_mul_of_nonneg_right hρ (nn n))
  have geom (k : ℕ) : gaussianShell a c₂ c₄ (N+k) ≤ gaussianShell a c₂ c₄ N*ρ^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ ρ*gaussianShell a c₂ c₄ (N+k) := step _ (by omega)
        _ ≤ ρ*(gaussianShell a c₂ c₄ N*ρ^k) := mul_le_mul_of_nonneg_left ih hr0
        _ = _ := by rw [pow_succ]; ring
  have h (k : ℕ) : gaussianShell a c₂ c₄ (N+1+k) ≤ (gaussianShell a c₂ c₄ N*ρ)*ρ^k := by
    have e := geom (k+1)
    rw [show N+(k+1)=N+1+k by omega,pow_succ] at e
    convert e using 1 <;> ring
  have hμ := summable_geometric_of_lt_one hr0 hr
  have H := hμ.mul_left (gaussianShell a c₂ c₄ N*ρ)
  have hs := Summable.of_nonneg_of_le (fun k => nn (N+1+k)) h H
  refine ⟨hs,(hs.tsum_le_tsum h H).trans_eq ?_⟩
  rw [tsum_mul_left,tsum_geometric_of_lt_one hr0 hr,div_eq_mul_inv]

structure RemainderWitness where
  ratioExp : ExpBounds.Witness
  edgeExp : ExpBounds.Witness

def ratioArgument (a : ℚ) (N : ℕ) : Ball :=
  Ball.exact (-a*(2*(N : ℚ)+1))

def edgeArgument (a : ℚ) (N : ℕ) : Ball :=
  Ball.exact (-a*(N : ℚ)^2)

def ratioUpper (w : RemainderWitness) (N : ℕ) : ℚ :=
  (((N : ℚ)+1)/(N : ℚ))^4*w.ratioExp.result.hi

def edgeUpper (w : RemainderWitness) (c₂ c₄ : ℚ) (N : ℕ) : ℚ :=
  (c₂*(N : ℚ)^2+c₄*(N : ℚ)^4)*w.edgeExp.result.hi

def remainderCheck (w : RemainderWitness) (a c₂ c₄ : ℚ) (N : ℕ) : Bool :=
  decide (0 ≤ a ∧ 0 ≤ c₂ ∧ 0 ≤ c₄ ∧ 0 < N ∧ ratioUpper w N < 1) &&
    (w.ratioExp.check (ratioArgument a N) && w.edgeExp.check (edgeArgument a N))

def remainderUpper (w : RemainderWitness) (c₂ c₄ : ℚ) (N : ℕ) : ℚ :=
  edgeUpper w c₂ c₄ N*ratioUpper w N/(1-ratioUpper w N)

theorem remainderUpper_sound (w : RemainderWitness) (a c₂ c₄ : ℚ) (N : ℕ)
    (ok : remainderCheck w a c₂ c₄ N = true) :
    Summable (fun k => gaussianShell (a : ℝ) (c₂ : ℝ) (c₄ : ℝ) (N+1+k)) ∧
    (∑' k, gaussianShell (a : ℝ) (c₂ : ℝ) (c₄ : ℝ) (N+1+k)) ≤ (remainderUpper w c₂ c₄ N : ℝ) := by
  have h := Bool.and_eq_true_iff.mp ok
  have hex := Bool.and_eq_true_iff.mp h.2
  have hc : 0 ≤ a ∧ 0 ≤ c₂ ∧ 0 ≤ c₄ ∧ 0 < N ∧ ratioUpper w N < 1 := of_decide_eq_true h.1
  have ha : (0 : ℝ)≤a := by exact_mod_cast hc.1
  have h₂ : (0 : ℝ)≤ c₂ := by exact_mod_cast hc.2.1
  have h₄ : (0 : ℝ)≤ c₄ := by exact_mod_cast hc.2.2.1
  have hq : (ratioUpper w N : ℝ)<1 := by exact_mod_cast hc.2.2.2.2
  have hR := ExpBounds.Witness.sound hex.1 (Ball.contains_exact (-a*(2*(N : ℚ)+1)))
  have hE := ExpBounds.Witness.sound hex.2 (Ball.contains_exact (-a*(N : ℚ)^2))
  have hp : gaussianRatio (a : ℝ) N ≤ (ratioUpper w N : ℝ) := by
    have ll := ((SpecialFunctions.contains_iff_endpoints _ _).mp hR).2
    unfold gaussianRatio ratioUpper Ball.hi
    push_cast at ll ⊢
    exact mul_le_mul_of_nonneg_left ll (by positivity)
  have he : gaussianShell (a : ℝ) (c₂ : ℝ) (c₄ : ℝ) N ≤ (edgeUpper w c₂ c₄ N : ℝ) := by
    have ll := ((SpecialFunctions.contains_iff_endpoints _ _).mp hE).2
    unfold gaussianShell edgeUpper Ball.hi
    push_cast at ll ⊢
    exact mul_le_mul_of_nonneg_left ll (by positivity)
  have hTail := gaussianShell_tail (a : ℝ) (c₂ : ℝ) (c₄ : ℝ) (ratioUpper w N : ℝ) ha h₂ h₄
    N hc.2.2.2.1 hp hq
  have hlo : (0 : ℝ) ≤ ratioUpper w N := (show 0 ≤ gaussianRatio (a : ℝ) N by
    unfold gaussianRatio; positivity).trans hp
  refine ⟨hTail.1,hTail.2.trans ?_⟩
  unfold remainderUpper
  push_cast
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hlo) (sub_nonneg.mpr hq.le)

def withSignedTail (part : Ball) (tau : ℚ) : Ball :=
  part.add ⟨0,tau⟩

theorem withSignedTail_sound {part : Ball} {tau : ℚ} {x omitted : ℝ}
    (hx : part.Contains x) (ho : |omitted| ≤ (tau : ℝ)) :
    (withSignedTail part tau).Contains (x+omitted) := by
  have h : (⟨0,tau⟩ : Ball).Contains omitted := by
    simpa [Ball.Contains] using ho
  exact Ball.contains_add hx h

end BccSharp.Coulomb.BravaisCover
