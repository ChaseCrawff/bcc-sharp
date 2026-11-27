import BccSharp.Lattice.KernelJet
import BccSharp.Lattice.MeanValue
import BccSharp.Lattice.StrainMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

/-! First-order rational jets. Each interval derivative is bound
to the derivative of its value along the actual centered segment. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

structure FirstJet where
  value : Ball
  gradient : Fin 5 → Ball

def FirstJet.Agrees (b : Rectangle) (j : FirstJet) (f : Point → ℝ) : Prop :=
  (∀ x, b.Mem x → j.value.Contains (f x)) ∧
  ∀ p, b.Mem p → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ g : Point,
    (∀ i, (j.gradient i).Contains (g i)) ∧
    HasDerivWithinAt (fun s => f (segment b p s))
      (∑ i, g i*(p i-boxCenter b i)) (Set.Icc 0 1) t

namespace FirstJet

/-- `Ball.contains_exact` states containment of the cast `(q : ℝ)`; this form
accepts any real number equal to that cast. -/
theorem contains_exact_of_eq {q : ℚ} {x : ℝ} (h : (q : ℝ) = x) : (Ball.exact q).Contains x :=
  h ▸ Ball.contains_exact q

def constant (v : Ball) : FirstJet := ⟨v, fun _ => Ball.exact 0⟩

def coordinate (b : Rectangle) (i : Fin 5) : FirstJet :=
  ⟨coordinateBall b i, fun j => Ball.exact (if j=i then 1 else 0)⟩

def add (a b : FirstJet) : FirstJet :=
  ⟨a.value.add b.value,fun i => (a.gradient i).add (b.gradient i)⟩

def sub (a b : FirstJet) : FirstJet :=
  ⟨a.value.sub b.value,fun i => (a.gradient i).sub (b.gradient i)⟩

def mul (a b : FirstJet) : FirstJet :=
  ⟨a.value.mul b.value,
    fun i => ((a.gradient i).mul b.value).add (a.value.mul (b.gradient i))⟩

def square (a : FirstJet) : FirstJet :=
  ⟨sqBall a.value,fun i => ((Ball.exact 2).mul a.value).mul (a.gradient i)⟩

def chain (j : FirstJet) (v slope : Ball) : FirstJet :=
  ⟨v,fun i => slope.mul (j.gradient i)⟩

def inverse (j : FirstJet) : FirstJet :=
  let v := j.value.inv
  j.chain v (sqBall v).neg

def cubeRoot (j : FirstJet) (r : RootProposal) : FirstJet :=
  j.chain r.ball (((Ball.exact (1/3)).mul r.ball).mul j.value.inv)

def kernel (j : FirstJet) (w : KernelWitness) : FirstJet :=
  let k := w.evaluate j.value
  j.chain k.value k.slope

def round (j : FirstJet) : FirstJet :=
  ⟨Constants.round j.value, fun i => Constants.round (j.gradient i)⟩

theorem agrees_congr {b : Rectangle} {j : FirstJet} {f g : Point → ℝ}
    (h : j.Agrees b f) (eq : ∀ p, b.Mem p → f p = g p) : j.Agrees b g := by
  refine ⟨fun p hp => eq p hp ▸ h.1 p hp,?_⟩
  intro p hp t ht
  obtain ⟨d,hd,hderiv⟩ := h.2 p hp t ht
  exact ⟨d,hd,hderiv.congr_of_mem (fun s hs => (eq _ (segment_mem hp hs)).symm) ht⟩

theorem constant_sound (b : Rectangle) (v : Ball) (x : ℝ) (h : v.Contains x) :
    (constant v).Agrees b (fun _ => x) := by
  refine ⟨fun _ _ => h,?_⟩
  intro p _ t _
  refine ⟨fun _ => 0,fun _ => contains_exact_of_eq Rat.cast_zero,?_⟩
  simpa using (hasDerivAt_const t x).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)

theorem coordinate_sound (b : Rectangle) (i : Fin 5) :
    (coordinate b i).Agrees b (fun x => x i) := by
  classical
  refine ⟨fun x hx => coordinateBall_sound hx i,?_⟩
  intro p _ t _
  refine ⟨fun j => if j=i then 1 else 0, ?_, ?_⟩
  · intro j
    by_cases h : j=i <;> simpa [coordinate,h] using Ball.contains_exact (if j=i then 1 else 0)
  · have d : (∑ j : Fin 5, (if j=i then (1 : ℝ) else 0)*(p j-boxCenter b j)) =
        p i-boxCenter b i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ h; simp [h]
      · simp
    rw [d]
    have h : HasDerivAt (fun s : ℝ => (1-s)*boxCenter b i+s*p i) (p i-boxCenter b i) t := by
      have h₀ := (((hasDerivAt_id' t).const_sub (1 : ℝ)).mul_const (boxCenter b i)).fun_add
        ((hasDerivAt_id' t).mul_const (p i))
      convert h₀ using 1
      ring
    exact h.hasDerivWithinAt

theorem add_sound {b : Rectangle} {a c : FirstJet} {f g : Point → ℝ}
    (ha : a.Agrees b f) (hc : c.Agrees b g) :
    (a.add c).Agrees b (fun p => f p+g p) := by
  refine ⟨fun p hp => Ball.contains_add (ha.1 p hp) (hc.1 p hp),?_⟩
  intro p hp t ht
  obtain ⟨u,hu,hdu⟩ := ha.2 p hp t ht
  obtain ⟨v,hv,hdv⟩ := hc.2 p hp t ht
  refine ⟨fun i => u i+v i,fun i => Ball.contains_add (hu i) (hv i),?_⟩
  simpa only [add_mul,Finset.sum_add_distrib] using hdu.fun_add hdv

theorem sub_sound {b : Rectangle} {a c : FirstJet} {f g : Point → ℝ}
    (ha : a.Agrees b f) (hc : c.Agrees b g) :
    (a.sub c).Agrees b (fun p => f p-g p) := by
  refine ⟨fun p hp => Ball.contains_sub (ha.1 p hp) (hc.1 p hp),?_⟩
  intro p hp t ht
  obtain ⟨u,hu,hdu⟩ := ha.2 p hp t ht
  obtain ⟨v,hv,hdv⟩ := hc.2 p hp t ht
  refine ⟨fun i => u i-v i,fun i => Ball.contains_sub (hu i) (hv i),?_⟩
  simpa only [sub_mul,Finset.sum_sub_distrib] using hdu.fun_sub hdv

theorem mul_sound {b : Rectangle} {a c : FirstJet} {f g : Point → ℝ}
    (ha : a.Agrees b f) (hc : c.Agrees b g) :
    (a.mul c).Agrees b (fun p => f p*g p) := by
  refine ⟨fun p hp => Ball.contains_mul (ha.1 p hp) (hc.1 p hp),?_⟩
  intro p hp t ht
  obtain ⟨u,hu,hdu⟩ := ha.2 p hp t ht
  obtain ⟨v,hv,hdv⟩ := hc.2 p hp t ht
  let x := segment b p t
  have hx := segment_mem hp ht
  refine ⟨fun i => u i*g x+f x*v i,fun i => Ball.contains_add
    (Ball.contains_mul (hu i) (hc.1 x hx)) (Ball.contains_mul (ha.1 x hx) (hv i)),?_⟩
  have e : (∑ i, (u i*g x+f x*v i)*(p i-boxCenter b i)) =
      (∑ i, u i*(p i-boxCenter b i))*g x + f x*(∑ i, v i*(p i-boxCenter b i)) := by
    rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e]
  exact hdu.fun_mul hdv

theorem chain_sound {b : Rectangle} {a : FirstJet} {f : Point → ℝ}
    (ha : a.Agrees b f) (v slope : Ball) (F F' : ℝ → ℝ)
    (h : ∀ x, b.Mem x → v.Contains (F (f x)) ∧ slope.Contains (F' (f x)) ∧
      HasDerivAt F (F' (f x)) (f x)) :
    (a.chain v slope).Agrees b (fun x => F (f x)) := by
  refine ⟨fun x hx => (h x hx).1,?_⟩
  intro p hp t ht
  obtain ⟨u,hu,hd⟩ := ha.2 p hp t ht
  let x := segment b p t
  have hh := (h x (segment_mem hp ht)).2
  refine ⟨fun i => F' (f x)*u i,fun i => Ball.contains_mul hh.1 (hu i),?_⟩
  have e : (∑ i, F' (f x)*u i*(p i-boxCenter b i)) =
      F' (f x)*(∑ i, u i*(p i-boxCenter b i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e]
  exact hh.2.comp_hasDerivWithinAt t hd

theorem square_sound {b : Rectangle} {a : FirstJet} {f : Point → ℝ} (h : a.Agrees b f) :
    a.square.Agrees b (fun p => (f p)^2) := by
  apply chain_sound h (sqBall a.value) ((Ball.exact 2).mul a.value) (fun x => x^2) (fun x => 2*x)
  intro x hx
  exact ⟨sqBall_sound (h.1 x hx),
    Ball.contains_mul (contains_exact_of_eq (by norm_num)) (h.1 x hx),
    by simpa using hasDerivAt_pow 2 (f x)⟩

theorem inverse_sound {b : Rectangle} {a : FirstJet} {f : Point → ℝ} (h : a.Agrees b f)
    (hn : a.value.invertible) : a.inverse.Agrees b (fun p => (f p)⁻¹) := by
  apply chain_sound h a.value.inv (sqBall a.value.inv).neg (fun x => x⁻¹) (fun x => -((x⁻¹)^2))
  intro p hp
  have hv := h.1 p hp
  have hi := Ball.contains_inv hn hv
  have hx : f p ≠ 0 := by
    intro e
    have hz : |(a.value.mid : ℝ)| ≤ (a.value.rad : ℝ) := by
      simpa [e,Ball.Contains] using hv
    exact (not_le_of_gt hn) (by exact_mod_cast hz)
  refine ⟨hi,Ball.contains_neg (sqBall_sound hi),?_⟩
  have e := hasDerivAt_inv hx
  rw [← inv_pow] at e
  exact e

theorem cubeRoot_sound {b : Rectangle} {a : FirstJet} {f : Point → ℝ} (h : a.Agrees b f)
    (r : RootProposal) (hp : a.value.positive=true) (hi : a.value.invertible)
    (ok : cubeRootCheck r a.value = true) :
    (a.cubeRoot r).Agrees b (fun x => (f x)^(1/3 : ℝ)) := by
  apply chain_sound h r.ball (((Ball.exact (1/3)).mul r.ball).mul a.value.inv)
    (fun x => x^(1/3 : ℝ)) (fun x => (1/3)*x^(1/3 : ℝ)*x⁻¹)
  intro x hx
  have hv := h.1 x hx
  have hpos := Ball.positive_sound hp hv
  have hr := BccSharp.Coulomb.BravaisCover.cubeRoot_sound r a.value (f x) hpos.le hv ok
  refine ⟨hr,Ball.contains_mul (Ball.contains_mul (contains_exact_of_eq (by norm_num)) hr)
    (Ball.contains_inv hi hv),?_⟩
  -- d/dy y^(1/3) = (1/3) y^(1/3-1) = (1/3) y^(1/3) y⁻¹ for y = f x > 0.
  have e := Real.hasDerivAt_rpow_const (x := f x) (p := (1/3 : ℝ)) (Or.inl hpos.ne')
  convert e using 1
  rw [Real.rpow_sub hpos,Real.rpow_one]
  ring

theorem kernel_sound {b : Rectangle} {a : FirstJet} {f : Point → ℝ} (h : a.Agrees b f)
    (w : KernelWitness) (ok : w.check a.value = true) :
    (a.kernel w).Agrees b (fun p => kernelValue w.kind (f p)) := by
  let k := w.evaluate a.value
  apply chain_sound h k.value k.slope (kernelValue w.kind) (kernelSlope w.kind)
  intro p hp
  have hv := h.1 p hp
  have hh := w.evaluate_sound hv ok
  have hpos := Ball.positive_sound (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1 hv
  exact ⟨hh.1,hh.2.1,kernelValue_hasDerivAt _ hpos⟩

theorem round_sound {b : Rectangle} {a : FirstJet} {f : Point → ℝ} (h : a.Agrees b f) :
    a.round.Agrees b f := by
  refine ⟨fun p hp => Constants.round_sound (h.1 p hp),?_⟩
  intro p hp t ht
  obtain ⟨g,hg,hd⟩ := h.2 p hp t ht
  exact ⟨g,fun i => Constants.round_sound (hg i),hd⟩

def sum {ι : Type} (s : Finset ι) (J : ι → FirstJet) : FirstJet :=
  ⟨Constants.sumBalls s (fun i => (J i).value),fun k => Constants.sumBalls s (fun i => (J i).gradient k)⟩

theorem sum_sound {ι : Type} (s : Finset ι) {J : ι → FirstJet} {f : ι → Point → ℝ}
    {b : Rectangle} (h : ∀ i ∈ s, (J i).Agrees b (f i)) :
    (sum s J).Agrees b (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [sum,Constants.sumBalls,constant,Ball.exact] using constant_sound b (Ball.exact 0) 0
      (contains_exact_of_eq Rat.cast_zero)
  | @insert i s hi ih =>
    have h₁ := h i (Finset.mem_insert_self i s)
    have h₂ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    simpa [sum,Constants.sumBalls,add,Ball.add,Finset.sum_insert hi] using add_sound h₁ h₂

theorem centeredLower_sound {b : Rectangle} {j : FirstJet} {f : Point → ℝ}
    (h : j.Agrees b f) (center : Ball) (hc : center.Contains (f (boxCenter b)))
    (p : Point) (hp : b.Mem p) : (meanValueLower b center j.gradient : ℝ) ≤ f p := by
  let F (t : ℝ) := f (segment b p t)
  have hcont : ContinuousOn F (Set.Icc 0 1) := by
    intro t ht
    obtain ⟨g,_,dg⟩ := h.2 p hp t ht
    exact dg.continuousWithinAt
  have interior (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      Set.Icc (0 : ℝ) 1 ∈ nhds t :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  have hdiff (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt F (deriv F t) t := by
    obtain ⟨g,_,dg⟩ := h.2 p hp t (Set.Ioo_subset_Icc_self ht)
    exact (dg.hasDerivAt (interior t ht)).differentiableAt.hasDerivAt
  obtain ⟨t,ht,hs⟩ := exists_hasDerivAt_eq_slope F (deriv F)
    (by norm_num : (0 : ℝ)<1) hcont hdiff
  obtain ⟨g,hg,dg⟩ := h.2 p hp t (Set.Ioo_subset_Icc_self ht)
  have slope : deriv F t=∑ i, g i*(p i-boxCenter b i) :=
    (dg.hasDerivAt (interior t ht)).deriv
  rw [slope] at hs
  have cost (i : Fin 5) : -((coordinateBall b i).rad : ℝ)*(absUpper (j.gradient i) : ℝ)
      ≤ g i*(p i-boxCenter b i) := by
    have h₁ := absUpper_sound (hg i)
    have h₂ : |p i-boxCenter b i| ≤ ((coordinateBall b i).rad : ℝ) := coordinateBall_sound hp i
    have he := neg_abs_le (g i*(p i-boxCenter b i))
    rw [abs_mul] at he
    have e := (neg_le_neg (mul_le_mul h₁ h₂ (abs_nonneg _) ((abs_nonneg _).trans h₁))).trans he
    linarith
  have hn := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => cost i)
  have h₀ : segment b p 0=boxCenter b := by funext i; simp [segment]
  have h₁ : segment b p 1=p := by funext i; simp [segment]
  simp only [F,h₀,h₁,sub_zero,div_one] at hs
  simp_rw [neg_mul,Finset.sum_neg_distrib] at hn
  have hl : (center.lo : ℝ) ≤ f (boxCenter b) := by
    simpa [Ball.lo] using ((SpecialFunctions.contains_iff_endpoints center _).mp hc).1
  unfold meanValueLower gradientLoss
  push_cast
  linarith

end FirstJet
end BccSharp.Coulomb.BravaisCover
