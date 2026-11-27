import BccSharp.Lattice.LocalSeries
import BccSharp.Lattice.StrainFirstJet

set_option autoImplicit false

/-! Second-order interval algebra. The real fields are explicit
formulas. The derivative proofs are for the compositions with open rays,
including the slope of the first derivative at each live point. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

structure StrainJet (α : Type) where
  value : α
  gradient : Fin 5 → α
  hessian : Fin 5 → Fin 5 → α

namespace StrainJet

variable {α β : Type}

def constant (zero a : α) : StrainJet α := ⟨a, fun _ => zero, fun _ _ => zero⟩

def coordinate (zero one a : α) (i : Fin 5) : StrainJet α :=
  ⟨a, fun j => if j=i then one else zero, fun _ _ => zero⟩

def entrywise (f : α → β) (a : StrainJet α) : StrainJet β :=
  ⟨f a.value, fun i => f (a.gradient i), fun i j => f (a.hessian i j)⟩

def combine (add : α → α → α) (a b : StrainJet α) : StrainJet α :=
  ⟨add a.value b.value, fun i => add (a.gradient i) (b.gradient i),
    fun i j => add (a.hessian i j) (b.hessian i j)⟩

def product (add mul : α → α → α) (a b : StrainJet α) : StrainJet α :=
  ⟨mul a.value b.value,
    fun i => add (mul (a.gradient i) b.value) (mul a.value (b.gradient i)),
    fun i j => add (add (mul (a.hessian i j) b.value) (mul a.value (b.hessian i j)))
      (add (mul (a.gradient i) (b.gradient j)) (mul (a.gradient j) (b.gradient i)))⟩

def chain (add mul : α → α → α) (a : StrainJet α) (value slope curvature : α) : StrainJet α :=
  ⟨value, fun i => mul slope (a.gradient i),
    fun i j => add (mul (mul curvature (a.gradient i)) (a.gradient j))
      (mul slope (a.hessian i j))⟩

abbrev RealField := Point → StrainJet ℝ

def directional (a : StrainJet ℝ) (v : Point) : ℝ := ∑ i, a.gradient i * v i

def Rel (b : StrainJet Ball) (a : StrainJet ℝ) : Prop :=
  b.value.Contains a.value ∧ (∀ i, (b.gradient i).Contains (a.gradient i)) ∧
    ∀ i j, (b.hessian i j).Contains (a.hessian i j)

def Encloses (b : Rectangle) (B : StrainJet Ball) (f : RealField) : Prop :=
  ∀ p, b.Mem p → Rel B (f p)

def RayDerivatives (b : Rectangle) (f : RealField) : Prop :=
  ∀ (v : Point) (t : ℝ), b.Mem (t • v) →
    HasDerivAt (fun s : ℝ => (f (s • v)).value) ((f (t • v)).directional v) t ∧
    HasDerivAt (fun s : ℝ => (f (s • v)).directional v) (hessianQuadratic (f (t • v)).hessian v) t

theorem constant_derivatives (b : Rectangle) (r : ℝ) :
    RayDerivatives b (fun _ => constant 0 r) := by
  intro v t _
  simpa [constant, directional, hessianQuadratic] using
    And.intro (hasDerivAt_const t r) (hasDerivAt_const t (0 : ℝ))

theorem coordinate_derivatives (b : Rectangle) (i : Fin 5) :
    RayDerivatives b (fun p => coordinate 0 1 (p i) i) := by
  have h (p v : Point) : (coordinate 0 1 (p i) i).directional v = v i := by
    classical
    simp [directional, coordinate, ite_mul]
  have hv (s : ℝ) (v : Point) : (coordinate 0 1 ((s • v) i) i).value = s * v i := by
    simp [coordinate, Pi.smul_apply, smul_eq_mul]
  have hh (p v : Point) : hessianQuadratic (coordinate 0 1 (p i) i).hessian v = 0 := by
    simp [coordinate, hessianQuadratic]
  intro v t _
  simp only [h, hv, hh]
  exact ⟨by simpa using (hasDerivAt_id t).mul_const (v i), hasDerivAt_const t (v i)⟩

theorem add_rel {a b : StrainJet ℝ} {A B : StrainJet Ball} (ha : Rel A a) (hb : Rel B b) :
    Rel (combine Ball.add A B) (combine (·+·) a b) :=
  ⟨Ball.contains_add ha.1 hb.1, fun i => Ball.contains_add (ha.2.1 i) (hb.2.1 i),
    fun i j => Ball.contains_add (ha.2.2 i j) (hb.2.2 i j)⟩

theorem neg_rel {a : StrainJet ℝ} {A : StrainJet Ball} (h : Rel A a) :
    Rel (entrywise Ball.neg A) (entrywise Neg.neg a) :=
  ⟨Ball.contains_neg h.1, fun i => Ball.contains_neg (h.2.1 i),
    fun i j => Ball.contains_neg (h.2.2 i j)⟩

theorem product_rel {a b : StrainJet ℝ} {A B : StrainJet Ball} (ha : Rel A a) (hb : Rel B b) :
    Rel (product Ball.add Ball.mul A B) (product (·+·) (·*·) a b) :=
  ⟨Ball.contains_mul ha.1 hb.1,
    fun i => Ball.contains_add (Ball.contains_mul (ha.2.1 i) hb.1) (Ball.contains_mul ha.1 (hb.2.1 i)),
    fun i j => Ball.contains_add
      (Ball.contains_add (Ball.contains_mul (ha.2.2 i j) hb.1) (Ball.contains_mul ha.1 (hb.2.2 i j)))
      (Ball.contains_add (Ball.contains_mul (ha.2.1 i) (hb.2.1 j))
        (Ball.contains_mul (ha.2.1 j) (hb.2.1 i)))⟩

theorem chain_rel {a : StrainJet ℝ} {A : StrainJet Ball} {V S C : Ball} {v s c : ℝ}
    (ha : Rel A a) (hv : V.Contains v) (hs : S.Contains s) (hc : C.Contains c) :
    Rel (chain Ball.add Ball.mul A V S C) (chain (·+·) (·*·) a v s c) :=
  ⟨hv, fun i => Ball.contains_mul hs (ha.2.1 i), fun i j =>
    Ball.contains_add (Ball.contains_mul (Ball.contains_mul hc (ha.2.1 i)) (ha.2.1 j))
      (Ball.contains_mul hs (ha.2.2 i j))⟩

theorem add_derivatives {b : Rectangle} {f g : RealField}
    (hf : RayDerivatives b f) (hg : RayDerivatives b g) :
    RayDerivatives b (fun p => combine (·+·) (f p) (g p)) := by
  intro v t h
  obtain ⟨f', f''⟩ := hf v t h
  obtain ⟨g', g''⟩ := hg v t h
  have D (a d : StrainJet ℝ) : (combine (·+·) a d).directional v =
      a.directional v + d.directional v := by
    simp [directional, combine, add_mul, Finset.sum_add_distrib]
  have H (a d : StrainJet ℝ) : hessianQuadratic (combine (·+·) a d).hessian v =
      hessianQuadratic a.hessian v + hessianQuadratic d.hessian v := by
    simp [hessianQuadratic, combine, add_mul, Finset.sum_add_distrib]
  have V (a d : StrainJet ℝ) : (combine (·+·) a d).value = a.value + d.value := rfl
  simp only [D, H, V]
  exact ⟨f'.fun_add g', f''.fun_add g''⟩

theorem neg_derivatives {b : Rectangle} {f : RealField} (hf : RayDerivatives b f) :
    RayDerivatives b (fun p => entrywise Neg.neg (f p)) := by
  intro v t h
  obtain ⟨f', f''⟩ := hf v t h
  have D (a : StrainJet ℝ) : (entrywise Neg.neg a).directional v = -a.directional v := by
    simp [directional, entrywise, Finset.sum_neg_distrib]
  have H (a : StrainJet ℝ) : hessianQuadratic (entrywise Neg.neg a).hessian v =
      -hessianQuadratic a.hessian v := by
    simp [hessianQuadratic, entrywise, Finset.sum_neg_distrib]
  have V (a : StrainJet ℝ) : (entrywise Neg.neg a).value = -a.value := rfl
  simp only [D, H, V]
  exact ⟨f'.fun_neg, f''.fun_neg⟩

theorem product_directional (a b : StrainJet ℝ) (v : Point) :
    (product (·+·) (·*·) a b).directional v = a.directional v * b.value +
      a.value * b.directional v := by
  simp only [directional, product, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem product_hessian (a b : StrainJet ℝ) (v : Point) :
    hessianQuadratic (product (·+·) (·*·) a b).hessian v =
      hessianQuadratic a.hessian v * b.value + a.value * hessianQuadratic b.hessian v +
      (a.directional v * b.directional v + a.directional v * b.directional v) := by
  have cross (x y : Point) : (∑ i, ∑ j, x i*y j*v i*v j) = (∑ i, x i*v i)*(∑ j, y j*v j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have cross' : (∑ i, ∑ j, a.gradient j*b.gradient i*v i*v j) =
      a.directional v * b.directional v := by
    simp only [directional]
    rw [mul_comm, ← cross]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [hessianQuadratic, product, add_mul, Finset.sum_add_distrib]
  rw [cross', cross]
  simp only [directional, Finset.sum_mul, Finset.mul_sum]
  congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem product_derivatives {b : Rectangle} {f g : RealField}
    (hf : RayDerivatives b f) (hg : RayDerivatives b g) :
    RayDerivatives b (fun p => product (·+·) (·*·) (f p) (g p)) := by
  intro v t h
  obtain ⟨f', f''⟩ := hf v t h
  obtain ⟨g', g''⟩ := hg v t h
  have V (a d : StrainJet ℝ) : (product (·+·) (·*·) a d).value = a.value * d.value := rfl
  refine ⟨by simp only [V, product_directional]; exact f'.fun_mul g', ?_⟩
  rw [product_hessian]
  convert (f''.mul g').add (f'.mul g'') using 1
  · ext s; exact product_directional _ _ _
  · ring

theorem chain_directional (a : StrainJet ℝ) (x y z : ℝ) (v : Point) :
    (chain (·+·) (·*·) a x y z).directional v = y*a.directional v := by
  simp [directional, chain, Finset.mul_sum, mul_assoc]

theorem chain_hessian (a : StrainJet ℝ) (x y z : ℝ) (v : Point) :
    hessianQuadratic (chain (·+·) (·*·) a x y z).hessian v =
      z*(a.directional v)^2 + y*hessianQuadratic a.hessian v := by
  simp only [hessianQuadratic, chain, directional, pow_two, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem chain_derivatives {b : Rectangle} {f : RealField} (hf : RayDerivatives b f)
    (F F' F'' : ℝ → ℝ) (h : ∀ p, b.Mem p → HasDerivAt F (F' (f p).value) (f p).value ∧
      HasDerivAt F' (F'' (f p).value) (f p).value) :
    RayDerivatives b (fun p => chain (·+·) (·*·) (f p) (F (f p).value) (F' (f p).value) (F'' (f p).value)) := by
  intro v t ht
  obtain ⟨a, da⟩ := hf v t ht
  obtain ⟨d, dd⟩ := h _ ht
  have V (a : StrainJet ℝ) (x y z : ℝ) : (chain (·+·) (·*·) a x y z).value = x := rfl
  refine ⟨by simp only [V, chain_directional]; exact d.comp t a, ?_⟩
  rw [chain_hessian]
  convert (dd.comp t a).mul da using 1
  · ext s; exact chain_directional _ _ _ _ _
  · simp only [Function.comp_apply]; ring

def inverse (add mul : α → α → α) (neg inv : α → α) (two : α) (a : StrainJet α) : StrainJet α :=
  let y := inv a.value
  let y₂ := mul y y
  chain add mul a y (neg y₂) (mul two (mul y₂ y))

def cubeRoot (add mul : α → α → α) (inv root : α → α) (oneThird negTwoNinth : α)
    (a : StrainJet α) : StrainJet α :=
  let r := root a.value
  let y := inv a.value
  chain add mul a r (mul (mul oneThird r) y) (mul (mul negTwoNinth r) (mul y y))

abbrev realInverse := inverse (α := ℝ) (·+·) (·*·) Neg.neg Inv.inv 2
abbrev realRoot := cubeRoot (α := ℝ) (·+·) (·*·) Inv.inv (fun x => x^(1/3 : ℝ)) (1/3) (-2/9)

theorem inverse_scalar {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun s : ℝ => s⁻¹) (-(x⁻¹*x⁻¹)) x ∧
    HasDerivAt (fun s : ℝ => -(s⁻¹*s⁻¹)) (2*((x⁻¹*x⁻¹)*x⁻¹)) x := by
  have h : HasDerivAt (fun s : ℝ => s⁻¹) (-(x⁻¹*x⁻¹)) x := by
    convert hasDerivAt_inv hx using 1
    rw [pow_two, mul_inv]
  refine ⟨h, ?_⟩
  convert (h.mul h).neg using 1 <;> ring

theorem cubeRoot_scalar {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => s^(1/3 : ℝ)) ((1/3)*x^(1/3 : ℝ)*x⁻¹) x ∧
    HasDerivAt (fun s : ℝ => (1/3)*s^(1/3 : ℝ)*s⁻¹) ((-2/9)*x^(1/3 : ℝ)*(x⁻¹*x⁻¹)) x := by
  have h := Real.hasDerivAt_rpow_const (p := (1/3 : ℝ)) (Or.inl hx.ne')
  rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv] at h
  have r : HasDerivAt (fun s : ℝ => s^(1/3 : ℝ)) ((1/3)*x^(1/3 : ℝ)*x⁻¹) x := by
    simpa [mul_assoc, div_eq_mul_inv] using h
  refine ⟨r, ?_⟩
  convert (r.const_mul (1/3)).mul (inverse_scalar hx.ne').1 using 1 <;> ring

theorem inverse_derivatives {b : Rectangle} {f : RealField} (hf : RayDerivatives b f)
    (h : ∀ p, b.Mem p → (f p).value ≠ 0) : RayDerivatives b (fun p => realInverse (f p)) :=
  chain_derivatives hf (fun s => s⁻¹) (fun s => -(s⁻¹*s⁻¹)) (fun s => 2*((s⁻¹*s⁻¹)*s⁻¹))
    (fun p hp => inverse_scalar (h p hp))

theorem root_derivatives {b : Rectangle} {f : RealField} (hf : RayDerivatives b f)
    (h : ∀ p, b.Mem p → 0 < (f p).value) : RayDerivatives b (fun p => realRoot (f p)) :=
  chain_derivatives hf (fun s => s^(1/3 : ℝ)) (fun s => (1/3)*s^(1/3 : ℝ)*s⁻¹)
    (fun s => (-2/9)*s^(1/3 : ℝ)*(s⁻¹*s⁻¹)) (fun p hp => cubeRoot_scalar (h p hp))

def intervalInverse := inverse (α := Ball) Ball.add Ball.mul Ball.neg Ball.inv (Ball.exact 2)

def intervalRoot (r : RootProposal) :=
  cubeRoot (α := Ball) Ball.add Ball.mul Ball.inv (fun _ => r.ball) (Ball.exact (1/3)) (Ball.exact (-2/9))

theorem inverse_rel {a : StrainJet ℝ} {A : StrainJet Ball} (ha : Rel A a)
    (ok : A.value.invertible) : Rel (intervalInverse A) (realInverse a) := by
  have h := Ball.contains_inv ok ha.1
  exact chain_rel ha h (Ball.contains_neg (Ball.contains_mul h h))
    (Ball.contains_mul (Ball.contains_exact 2) (Ball.contains_mul (Ball.contains_mul h h) h))

theorem root_rel {a : StrainJet ℝ} {A : StrainJet Ball} (ha : Rel A a) (r : RootProposal)
    (pos : A.value.positive=true) (inv : A.value.invertible)
    (ok : cubeRootCheck r A.value=true) : Rel (intervalRoot r A) (realRoot a) := by
  have h := Ball.contains_inv inv ha.1
  have hr := cubeRoot_sound r A.value a.value (Ball.positive_sound pos ha.1).le ha.1 ok
  have c₁ : (Ball.exact (1/3)).Contains (1/3 : ℝ) := by
    have e := Ball.contains_exact (1/3 : ℚ)
    rwa [show ((1/3 : ℚ) : ℝ) = 1/3 by norm_num] at e
  have c₂ : (Ball.exact (-2/9)).Contains (-2/9 : ℝ) := by
    have e := Ball.contains_exact (-2/9 : ℚ)
    rwa [show ((-2/9 : ℚ) : ℝ) = -2/9 by norm_num] at e
  exact chain_rel ha hr (Ball.contains_mul (Ball.contains_mul c₁ hr) h)
    (Ball.contains_mul (Ball.contains_mul c₂ hr) (Ball.contains_mul h h))

def realKernel (k : KernelKind) (a : StrainJet ℝ) : StrainJet ℝ :=
  chain (·+·) (·*·) a (kernelValue k a.value) (kernelSlope k a.value) (kernelCurvature k a.value)

def intervalKernel (w : KernelWitness) (a : StrainJet Ball) : StrainJet Ball :=
  let k := w.evaluate a.value
  chain Ball.add Ball.mul a k.value k.slope k.curvature

theorem kernel_derivatives {b : Rectangle} {f : RealField} (hf : RayDerivatives b f)
    (k : KernelKind) (h : ∀ p, b.Mem p → 0 < (f p).value) :
    RayDerivatives b (fun p => realKernel k (f p)) :=
  chain_derivatives hf (kernelValue k) (kernelSlope k) (kernelCurvature k)
    (fun p hp => ⟨kernelValue_hasDerivAt k (h p hp), kernelSlope_hasDerivAt k (h p hp)⟩)

theorem kernel_rel {a : StrainJet ℝ} {A : StrainJet Ball} (ha : Rel A a) (w : KernelWitness)
    (ok : w.check A.value=true) : Rel (intervalKernel w A) (realKernel w.kind a) := by
  have k := w.evaluate_sound ha.1 ok
  exact chain_rel ha k.1 k.2.1 k.2.2

end StrainJet

end BccSharp.Coulomb.BravaisCover
