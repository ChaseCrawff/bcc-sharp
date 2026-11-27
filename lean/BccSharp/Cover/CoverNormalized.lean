import BccSharp.Cover.CoverReductionLeaves

set_option autoImplicit false

/-! Exact normalized reduction upper bounds. Both dimensional ratios
are evaluated on the source rectangle. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Coverage BravaisCover

private def productLo (m : ℤ) (b : Rectangle) (i : Fin 5) : ℚ := min (m*b.lo i) (m*b.hi i)
private def productHi (m : ℤ) (b : Rectangle) (i : Fin 5) : ℚ := max (m*b.lo i) (m*b.hi i)

private theorem productRange (m : ℤ) {b : Rectangle} {p : Point} (hp : b.Mem p) (i : Fin 5) :
    (productLo m b i : ℝ) ≤ (m : ℝ)*p i ∧ (m : ℝ)*p i ≤ (productHi m b i : ℝ) := by
  unfold productLo productHi
  push_cast
  by_cases s : (0 : ℝ)≤(m : ℝ)
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hp i).1 s),
      (mul_le_mul_of_nonneg_left (hp i).2 s).trans (le_max_right _ _)⟩
  · have s' := le_of_not_ge s
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left (hp i).2 s'),
      (mul_le_mul_of_nonpos_left (hp i).1 s').trans (le_max_left _ _)⟩

private def normA (b : Rectangle) (m : IntVec) : ℚ :=
  sqUpper ((m 0 : ℚ)+productLo (m 1) b 2+productLo (m 2) b 3)
    ((m 0 : ℚ)+productHi (m 1) b 2+productHi (m 2) b 3)

private def normB (b : Rectangle) (a d : ℤ) : ℚ :=
  sqUpper ((a : ℚ)+productLo d b 4) ((a : ℚ)+productHi d b 4)

private theorem normA_sound {b : Rectangle} {p : Point} (hp : b.Mem p) (m : IntVec) :
    ((m 0 : ℝ)+(m 1 : ℝ)*p 2+(m 2 : ℝ)*p 3)^2 ≤ (normA b m : ℝ) := by
  have l := productRange (m 1) hp 2
  have r := productRange (m 2) hp 3
  apply sqUpper_sound
  push_cast
  exact ⟨by linarith only [l.1,r.1],by linarith only [l.2,r.2]⟩

private theorem normB_sound {b : Rectangle} {p : Point} (hp : b.Mem p) (a d : ℤ) :
    ((a : ℝ)+(d : ℝ)*p 4)^2 ≤ (normB b a d : ℝ) := by
  have h := productRange d hp 4
  apply sqUpper_sound
  push_cast
  exact ⟨by linarith only [h.1],by linarith only [h.2]⟩

private theorem endpoint_max (l u h A C : ℝ) (lpos : 0<l) (lu : l≤u) (uh : u≤h) (cpos : 0≤C) :
    A*u+C/u ≤ max (A*l+C/l) (A*h+C/h) := by
  have upos := lpos.trans_le lu
  have hpos := upos.trans_le uh
  have product : 0<l*h := mul_pos lpos hpos
  have chord : 1/u ≤ (l+h-u)/(l*h) := by
    apply (div_le_div_iff₀ upos product).2
    nlinarith only [mul_nonneg (sub_nonneg.mpr lu) (sub_nonneg.mpr uh)]
  have bound := mul_le_mul_of_nonneg_left chord cpos
  let k := A-C/(l*h)
  let c := C*(l+h)/(l*h)
  have line : A*u+C/u ≤ k*u+c := by
    calc
      _ = A*u+C*(1/u) := by ring
      _ ≤ A*u+C*((l+h-u)/(l*h)) := add_le_add le_rfl bound
      _ = k*u+c := by dsimp [k,c]; ring
  have left : k*l+c=A*l+C/l := by dsimp [k,c]; field_simp [lpos.ne',hpos.ne'] <;> ring
  have right : k*h+c=A*h+C/h := by dsimp [k,c]; field_simp [lpos.ne',hpos.ne'] <;> ring
  by_cases hk : 0≤k
  · rw [← right]
    exact line.trans ((add_le_add (mul_le_mul_of_nonneg_left uh hk) le_rfl).trans (le_max_right _ _))
  · rw [← left]
    exact line.trans ((add_le_add (mul_le_mul_of_nonpos_left lu (le_of_not_ge hk)) le_rfl).trans (le_max_left _ _))

def normalizedUpper (b : Rectangle) : ReductionWitness → ℚ
  | .projected a d => normB b a d+(d : ℚ)^2/((b.lo 0)^2*(b.lo 1)^4)
  | .full m =>
    let eval (x : ℚ) := normA b m+(x/b.lo 0)^2*normB b (m 1) (m 2)+
      (m 2 : ℚ)^2/((b.lo 0)^4*x^2)
    max (eval (b.lo 1)) (eval (b.hi 1))

structure NormalizedProposal where
  shape : Rectangle
  witness : ReductionWitness
  upper : ℚ

/-- The witness is not the zero vector: a nonzero projected pair `(a,d)` or a
nonzero full integer vector `m`. -/
def normalizedWitnessNonzero : ReductionWitness → Prop
  | .projected a d => a≠0 ∨ d≠0
  | .full m => m≠0

instance (w : ReductionWitness) : Decidable (normalizedWitnessNonzero w) :=
  match w with
  | .projected a d => inferInstanceAs (Decidable (a≠0 ∨ d≠0))
  | .full m => inferInstanceAs (Decidable (m≠0))

def NormalizedProposal.check (w : NormalizedProposal) (b : Cell) : Bool :=
  decide ((∀ i, (shapeBox b).lo i = w.shape.lo i ∧ (shapeBox b).hi i = w.shape.hi i) ∧
    0<w.shape.lo 0 ∧ 0<w.shape.lo 1 ∧ w.upper=normalizedUpper w.shape w.witness ∧ w.upper<1 ∧
    normalizedWitnessNonzero w.witness)

theorem NormalizedProposal.sound (w : NormalizedProposal) (b : Cell) (ok : w.check b=true)
    (p : Chart) (hp : b.Mem p) : Route.result .invalidReduction p := by
  obtain ⟨ends,lo0,lo1,eq,upper,nonzero⟩ := of_decide_eq_true (show decide _ = true from ok)
  let q := takeShape p
  have hq : w.shape.Mem q := fun i => by simpa only [← (ends i).1,← (ends i).2] using takeShape_mem hp i
  have l₀ : (0:ℝ)<w.shape.lo 0 := by exact_mod_cast lo0
  have l₁ : (0:ℝ)<w.shape.lo 1 := by exact_mod_cast lo1
  have r₀ := l₀.trans_le (hq 0).1
  have r₁ := l₁.trans_le (hq 1).1
  have H₂ := pow_le_pow_left₀ l₀.le (hq 0).1 2
  have H₄ := pow_le_pow_left₀ l₀.le (hq 0).1 4
  have U : (normalizedUpper w.shape w.witness : ℝ)<1 := by rw [←eq]; exact_mod_cast upper
  intro h
  have reducedQ := takeShape_reduced p h
  cases route : w.witness with
  | projected a d =>
    rw [route] at U nonzero
    simp only [normalizedUpper] at U
    push_cast at U
    have ge := reduced_projectedLength reducedQ a d nonzero
    have quotient : 1 ≤ projectedLength q a d/(q 1)^2 :=
      (le_div_iff₀ (by positivity)).2 (by simpa using ge)
    have formula : projectedLength q a d/(q 1)^2 =
        ((a : ℝ)+(d : ℝ)*q 4)^2+(d : ℝ)^2/((q 0)^2*(q 1)^4) := by
      unfold projectedLength
      field_simp [r₀.ne',r₁.ne'] <;> ring
    have denom := mul_le_mul H₂ (pow_le_pow_left₀ l₁.le (hq 1).1 4) (by positivity) (by positivity)
    have bound := div_le_div_of_nonneg_left (sq_nonneg (d : ℝ)) (by positivity) denom
    rw [formula] at quotient
    linarith only [quotient,normB_sound hq a d,bound,U]
  | full m =>
    rw [route] at U nonzero
    simp only [normalizedUpper] at U
    push_cast at U
    have ge := reduced_firstLength reducedQ m nonzero
    have quotient : 1 ≤ firstLength q m/(q 0)^2 :=
      (le_div_iff₀ (by positivity)).2 (by simpa using ge)
    let a := (normA w.shape m : ℝ)
    let b₂ := (normB w.shape (m 1) (m 2) : ℝ)
    let A := b₂/(w.shape.lo 0 : ℝ)^2
    let C := (m 2 : ℝ)^2/(w.shape.lo 0 : ℝ)^4
    let u := (q 1)^2
    have formula : firstLength q m/(q 0)^2 =
        ((m 0 : ℝ)+(m 1 : ℝ)*q 2+(m 2 : ℝ)*q 3)^2+
        u*(((m 1 : ℝ)+(m 2 : ℝ)*q 4)^2/(q 0)^2)+((m 2 : ℝ)^2/(q 0)^4)/u := by
      unfold firstLength u
      field_simp [r₀.ne',r₁.ne'] <;> ring
    have divB : ((m 1 : ℝ)+(m 2 : ℝ)*q 4)^2/(q 0)^2≤A := by
      exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) H₂).trans
        (div_le_div_of_nonneg_right (normB_sound hq (m 1) (m 2)) (by positivity))
    have divC : ((m 2 : ℝ)^2/(q 0)^4)/u≤C/u :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) H₄) (by positivity)
    have bound : firstLength q m/(q 0)^2 ≤ a+(A*u+C/u) := by
      rw [formula,mul_comm A u,←add_assoc]
      exact add_le_add (add_le_add (normA_sound hq m) (mul_le_mul_of_nonneg_left divB (by positivity))) divC
    have ends := endpoint_max ((w.shape.lo 1 : ℝ)^2) u ((w.shape.hi 1 : ℝ)^2) A C
      (by positivity) (pow_le_pow_left₀ l₁.le (hq 1).1 2) (pow_le_pow_left₀ r₁.le (hq 1).2 2) (by positivity)
    have convertAt (x : ℝ) (hx : 0<x) : a+(A*x^2+C/x^2) =
        a+(x/(w.shape.lo 0 : ℝ))^2*b₂+(m 2 : ℝ)^2/((w.shape.lo 0 : ℝ)^4*x^2) := by
      dsimp [A,C]
      field_simp [l₀.ne',hx.ne'] <;> ring
    have hi₁ := r₁.trans_le (hq 1).2
    have contradiction := quotient.trans (bound.trans (add_le_add le_rfl ends))
    rw [add_max,convertAt _ l₁,convertAt _ hi₁] at contradiction
    exact (not_lt_of_ge contradiction) U

/-- Deterministic Adaptive geometry search. Projected representatives come
first, then lexicographically positive full representatives. -/
def normalizedStencil : List ReductionWitness :=
  let v : List ℤ := [-1,0,1]
  let projected := v.flatMap fun a => v.filterMap fun d =>
    if 0<a ∨ (a=0 ∧ 0<d) then some (.projected a d) else none
  let full := v.flatMap fun a => v.flatMap fun b => v.filterMap fun d =>
    if 0<a ∨ (a=0 ∧ (0<b ∨ (b=0 ∧ 0<d))) then some (.full ![a,b,d]) else none
  projected++full

def normalizedStencilCheck (b : Cell) : Bool :=
  normalizedStencil.any fun w => (⟨shapeBox b,w,normalizedUpper (shapeBox b) w⟩ : NormalizedProposal).check b

theorem normalizedStencilCheck_sound (b : Cell) (h : normalizedStencilCheck b=true)
    (p : Chart) (hp : b.Mem p) : Route.result .invalidReduction p := by
  obtain ⟨w,_,ok⟩ := List.any_eq_true.mp h
  exact (⟨shapeBox b,w,normalizedUpper (shapeBox b) w⟩ : NormalizedProposal).sound b ok p hp

end BccSharp.Coulomb.CompactCover
