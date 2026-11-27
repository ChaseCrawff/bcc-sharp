import BccSharp.Cover.CoverExactRealGeometry
import BccSharp.Cover.Stage2Tangents

set_option autoImplicit false

/-! Common-corner upper bound for the actual sum of weighted primal
and reciprocal squared distances. The threshold is applied after a single
joint maximum over the closed box. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Stage2
open BccSharp.Coverage BravaisCover DirectRoute

def dualB (m : IntVec) (p : Chart) : ℝ := (m 1 : ℝ)-p 2*(m 0 : ℝ)
def dualC (m : IntVec) (p : Chart) : ℝ :=
  (m 2 : ℝ)-p 4*(m 1 : ℝ)+(p 2*p 4-p 3)*(m 0 : ℝ)

def dualRadial (m : IntVec) (p : Chart) : ℝ :=
  (m 0 : ℝ)^2/(p 0)+(dualB m p)^2/(p 1)+p 0*p 1*(dualC m p)^2

theorem dualRadial_eq (m : IntVec) (p : Chart) (r0 : p 0≠0) (r1 : p 1≠0) :
    dualRadial m (squarePoint p)=quad (gram (chartBasis p))⁻¹ (castVec m) := by
  have basis : normalizedChart (takeShape p)=chartBasis p := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [dual_quad,←basis,←dualVector_eq (takeShape p) r0 r1]
  norm_num [dualRadial,dualB,dualC,squarePoint,dualVector,takeShape,sq,Fin.sum_univ_three] <;>
    field_simp [r0,r1] <;> ring

private theorem dual_affine (b : Cell) (m : IntVec) (p : Chart) (i : Axis) (t : ℝ)
    (e : p i=(1-t)*(b.lo i : ℝ)+t*(b.hi i : ℝ)) :
    dualB m p=(1-t)*dualB m (atLower b p i)+t*dualB m (atUpper b p i) ∧
    dualC m p=(1-t)*dualC m (atLower b p i)+t*dualC m (atUpper b p i) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :=
    (by decide : ∀ a : Axis, a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7) i
  all_goals
    simp only [dualB,dualC,atLower,atUpper,Function.update_apply,Fin.reduceEq,↓reduceIte] <;>
    refine ⟨?_,?_⟩ <;> (try rw [e]) <;> ring

theorem dualRadial_chord (m : IntVec) (b : Cell) (h : diagonalsCheck b=true) :
    ChordUpper (squareDiag b) (dualRadial m) := by
  let d := squareDiag b
  intro p hp i t low high e
  have radial := radialLoPos b h
  have h0 : (0:ℝ)<d.lo 0 := by
    change (0:ℝ)<(((b.lo 0)^2 : ℚ) : ℝ)
    push_cast
    exact pow_pos radial.1 2
  have h1 : (0:ℝ)<d.lo 1 := by
    change (0:ℝ)<(((b.lo 1)^2 : ℚ) : ℝ)
    push_cast
    exact pow_pos radial.2 2
  have p0 := h0.trans_le (hp 0).1
  have p1 := h1.trans_le (hp 1).1
  have u0 := p0.trans_le (hp 0).2
  have u1 := p1.trans_le (hp 1).2
  change (1-t)*(-dualRadial m (atLower d p i))+t*(-dualRadial m (atUpper d p i))≤-dualRadial m p
  by_cases eq0 : i=0
  · subst i
    have hc := radial_form (d.lo 0) (d.hi 0) (p 1*(dualC m p)^2) ((m 0 : ℝ)^2)
      ((dualB m p)^2/(p 1)) t h0 u0 (sq_nonneg _) low high
    have formula (a : ℝ) : dualRadial m (Function.update p 0 a)=
        (p 1*(dualC m p)^2)*a+(m 0 : ℝ)^2*a⁻¹+(dualB m p)^2/(p 1) := by
      norm_num [dualRadial,dualB,dualC,Function.update,div_eq_mul_inv] <;> ring
    have self : Function.update p 0 (p 0)=p := by ext j; by_cases hj : j=0 <;> simp_all
    have f := formula (p 0)
    rw [self] at f
    rw [←e] at hc
    rw [f]
    simp only [atLower,atUpper,formula]
    linarith only [hc]
  by_cases eq1 : i=1
  · subst i
    have hc := radial_form (d.lo 1) (d.hi 1) (p 0*(dualC m p)^2) ((dualB m p)^2)
      ((m 0 : ℝ)^2/(p 0)) t h1 u1 (sq_nonneg _) low high
    have formula (a : ℝ) : dualRadial m (Function.update p 1 a)=
        (p 0*(dualC m p)^2)*a+(dualB m p)^2*a⁻¹+(m 0 : ℝ)^2/(p 0) := by
      norm_num [dualRadial,dualB,dualC,Function.update,div_eq_mul_inv] <;> ring
    have self : Function.update p 1 (p 1)=p := by ext j; by_cases hj : j=1 <;> simp_all
    have f := formula (p 1)
    rw [self] at f
    rw [←e] at hc
    rw [f]
    simp only [atLower,atUpper,formula]
    linarith only [hc]
  obtain ⟨hb,hc⟩ := dual_affine d m p i t e
  have a := div_le_div_of_nonneg_right
    (affineSq_chord (dualB m (atLower d p i)) (dualB m (atUpper d p i)) t low high) p1.le
  have a' := mul_le_mul_of_nonneg_left
    (affineSq_chord (dualC m (atLower d p i)) (dualC m (atUpper d p i)) t low high) (mul_nonneg p0.le p1.le)
  rw [←hb] at a
  rw [←hc] at a'
  have L0 : atLower d p i 0=p 0 := Function.update_of_ne (Ne.symm eq0) _ _
  have L1 : atLower d p i 1=p 1 := Function.update_of_ne (Ne.symm eq1) _ _
  have U0 : atUpper d p i 0=p 0 := Function.update_of_ne (Ne.symm eq0) _ _
  have U1 : atUpper d p i 1=p 1 := Function.update_of_ne (Ne.symm eq1) _ _
  unfold dualRadial
  simp only [L0,L1,U0,U1]
  simp only [div_eq_mul_inv] at a ⊢
  linear_combination a+a'

inductive Family where
  | cross | period | reciprocal
  deriving DecidableEq, Repr

structure Mode where
  family : Family
  index : IntVec
  deriving DecidableEq

def Mode.radial (m : Mode) : Chart → ℝ :=
  match m.family with
  | .cross => squaredRadial true m.index
  | .period => squaredRadial false m.index
  | .reciprocal => dualRadial m.index

theorem Mode.chord (b : Cell) (hd : diagonalsCheck b=true) (m : Mode) :
    ChordUpper (squareDiag b) m.radial := by
  cases m with
  | mk fam m =>
    cases fam
    · exact squaredRadial_chord true m b hd
    · exact squaredRadial_chord false m b hd
    · exact dualRadial_chord m b hd

def squaredCorner (b : Cell) (bits : Axis → Bool) (i : Axis) : ℚ :=
  if i.val<2 then (cornerRat b bits i)^2 else cornerRat b bits i

theorem squaredCorner_cast (b : Cell) (bits : Axis → Bool) (i : Axis) :
    (squaredCorner b bits i : ℝ)=corner (squareDiag b) bits i := by
  show (((if i.val < 2 then (if bits i then b.hi i else b.lo i)^2
        else (if bits i then b.hi i else b.lo i) : ℚ)) : ℝ) =
    if bits i then (((if i.val < 2 then (b.hi i)^2 else b.hi i : ℚ)) : ℝ)
      else (((if i.val < 2 then (b.lo i)^2 else b.lo i : ℚ)) : ℝ)
  split_ifs <;> push_cast <;> rfl

def dualCorner (p : Axis → ℚ) (m : IntVec) : ℚ :=
  (m 0 : ℚ)^2/(p 0)+((m 1 : ℚ)-p 2*(m 0 : ℚ))^2/(p 1)+
    p 0*p 1*((m 2 : ℚ)-p 4*(m 1 : ℚ)+(p 2*p 4-p 3)*(m 0 : ℚ))^2

def Mode.atCorner (b : Cell) (bits : Axis → Bool) (m : Mode) : ℚ :=
  match m.family with
  | .cross => cornerDistance b bits true m.index
  | .period => cornerDistance b bits false m.index
  | .reciprocal => dualCorner (squaredCorner b bits) m.index

theorem Mode.atCorner_eq (b : Cell) (bits : Axis → Bool) (m : Mode) :
    (m.atCorner b bits : ℝ)=m.radial (corner (squareDiag b) bits) := by
  cases m with
  | mk fam m =>
    cases fam
    · exact cornerDistance_eq b bits true m
    · exact cornerDistance_eq b bits false m
    · unfold Mode.atCorner Mode.radial dualCorner dualRadial dualB dualC
      push_cast
      simp only [squaredCorner_cast]

theorem sum_chord (b : Cell) (hd : diagonalsCheck b=true) (s : Finset Mode) (w : Mode → ℚ)
    (nn : ∀ m∈s,0≤w m) : ChordUpper (squareDiag b) (fun p => ∑ m ∈ s,(w m : ℝ)*m.radial p) := by
  intro p hp i t lo hi e
  simp only [←Finset.sum_neg_distrib,←mul_neg,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m hm
  have h := mul_le_mul_of_nonneg_left (m.chord b hd p hp i t lo hi e)
    (by exact_mod_cast nn m hm : (0:ℝ)≤w m)
  linear_combination h

theorem corner_upper (b : Cell) (hd : diagonalsCheck b=true) (s : Finset Mode) (w : Mode → ℚ)
    (nn : ∀ m∈s,0≤w m) (u : ℚ) (h : ∀ bits, (∑ m ∈ s,w m*m.atCorner b bits)≤u)
    (p : Chart) (hp : b.Mem p) : (∑ m ∈ s,(w m : ℝ)*m.radial (squarePoint p))≤(u : ℝ) := by
  let f (p : Chart) := ∑ m ∈ s,(w m : ℝ)*m.radial p
  obtain ⟨bits,maximal⟩ := corner_le (squareDiag b) (fun p => -f p) (sum_chord b hd s w nn) _ (squarePoint_mem hp hd)
  have hR : ((∑ m ∈ s,w m*m.atCorner b bits : ℚ) : ℝ)≤u := by exact_mod_cast h bits
  push_cast at hR
  simp_rw [Mode.atCorner_eq] at hR
  exact (neg_le_neg_iff.mp maximal).trans hR

abbrev Metric6 := Fin 6 → ℚ

def sixDot (v w : Metric6) : ℚ := ∑ j, v j*w j
def metricPair (j : Fin 6) : Fin 3 × Fin 3 := ![(0,0),(1,1),(2,2),(0,1),(0,2),(1,2)] j
def imageMoment (f : Fin 3 → ℚ) (j : Fin 6) : ℚ := f (metricPair j).1*f (metricPair j).2

/-- Fold off-diagonals into the metric rows. -/
def primalMetric (p : Axis → ℚ) : Metric6 :=
  let s := p 0
  let t := p 1
  let x := p 2
  let y := p 3
  let z := p 4
  ![s,s*x^2+t,s*y^2+t*z^2+(s*t)⁻¹,2*s*x,2*s*y,2*(s*x*y+t*z)]

def dualMetric (p : Axis → ℚ) : Metric6 :=
  let s := p 0
  let t := p 1
  let x := p 2
  let z := p 4
  let h := x*z-p 3
  ![s⁻¹+x^2*t⁻¹+h^2*(s*t),t⁻¹+z^2*(s*t),s*t,
    2*(-x*t⁻¹-h*z*(s*t)),2*h*(s*t),-2*z*(s*t)]

def shapePart (b : Cell) (shape : Fin 5 → Bool) : Axis → ℚ :=
  squaredCorner b (fun i => if h : i.val<5 then shape ⟨i.val,h⟩ else false)

def offsetPart (b : Cell) (bits : Fin 3 → Bool) : Fin 3 → ℚ :=
  fun i => if bits i then b.hi (offset i) else b.lo (offset i)

def selectShape (bits : Axis → Bool) : Fin 5 → Bool := fun i => bits ⟨i.val,by omega⟩
def selectOffsets (bits : Axis → Bool) : Fin 3 → Bool := fun i => bits (offset i)

/-- On the five shape axes the selected shape bits give the full corner. -/
private theorem shapePart_select (b : Cell) (bits : Axis → Bool) (j : Axis) (hj : j.val < 5) :
    shapePart b (selectShape bits) j=squaredCorner b bits j := by
  simp [shapePart,squaredCorner,cornerRat,selectShape,hj]

private theorem primalMetric_congr {p q : Axis → ℚ} (h : ∀ j : Axis, j.val < 5 → p j=q j) :
    primalMetric p=primalMetric q := by
  simp only [primalMetric,h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),
    h 4 (by decide)]

private theorem dualMetric_congr {p q : Axis → ℚ} (h : ∀ j : Axis, j.val < 5 → p j=q j) :
    dualMetric p=dualMetric q := by
  simp only [dualMetric,h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),
    h 4 (by decide)]

private theorem offsetPart_select (b : Cell) (bits : Axis → Bool) (i : Fin 3) :
    offsetPart b (selectOffsets bits) i=cornerRat b bits (offset i) := rfl

private theorem metric_primal (b : Cell) (bits : Axis → Bool) (m : Mode) (hd : m.family≠.reciprocal) :
    m.atCorner b bits = sixDot (primalMetric (shapePart b (selectShape bits)))
      (imageMoment (fun i => (m.index i : ℚ)+if m.family=.cross then offsetPart b (selectOffsets bits) i else 0)) := by
  rw [primalMetric_congr (shapePart_select b bits)]
  cases m with
  | mk family n =>
    cases family <;> (try contradiction) <;>
      norm_num [Mode.atCorner,primalMetric,offsetPart_select,squaredCorner,cornerDistance,
        sixDot,imageMoment,metricPair,Fin.sum_univ_succ,div_eq_mul_inv] <;> ring

private theorem metric_dual (b : Cell) (bits : Axis → Bool) (m : Mode) (hr : m.family=.reciprocal) :
    m.atCorner b bits = sixDot (dualMetric (shapePart b (selectShape bits)))
      (imageMoment (fun i => (m.index i : ℚ))) := by
  rw [dualMetric_congr (shapePart_select b bits)]
  cases m with
  | mk family n =>
    cases family <;> try contradiction
    norm_num [Mode.atCorner,dualMetric,squaredCorner,dualCorner,
      sixDot,imageMoment,metricPair,Fin.sum_univ_succ,div_eq_mul_inv] <;> ring

structure Moments where
  direct : Metric6
  reciprocal : Metric6
  crossLinear : Fin 3 → ℚ
  crossMass : ℚ

private def directSet (s : Finset Mode) := s.filter (fun m => m.family≠.reciprocal)
private def crossSet (s : Finset Mode) := s.filter (fun m => m.family=.cross)
private def reciprocalSet (s : Finset Mode) := s.filter (fun m => m.family=.reciprocal)

def moments (s : Finset Mode) (w : Mode → ℚ) : Moments :=
  ⟨fun j => ∑ m ∈ directSet s,w m*imageMoment (fun k => (m.index k : ℚ)) j,
    fun j => ∑ m ∈ reciprocalSet s,w m*imageMoment (fun k => (m.index k : ℚ)) j,
    fun j => ∑ m ∈ crossSet s,w m*(m.index j : ℚ),
    ∑ m ∈ crossSet s,w m⟩

def Moments.shift (m : Moments) (f : Fin 3 → ℚ) : Metric6 := fun j =>
  let i := (metricPair j).1
  let k := (metricPair j).2
  m.direct j+m.crossLinear i*f k+m.crossLinear k*f i+m.crossMass*f i*f k

private theorem shift_eq (s : Finset Mode) (w : Mode → ℚ) (f : Fin 3 → ℚ) (j : Fin 6) :
    (moments s w).shift f j = ∑ m ∈ directSet s,w m*
      imageMoment (fun k => (m.index k : ℚ)+if m.family=.cross then f k else 0) j := by
  have incl : crossSet s ⊆ directSet s := by
    intro m hm
    have h := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨h.1,by rw [h.2]; decide⟩
  have restrict (g : Mode → ℚ) : (∑ m ∈ crossSet s,g m)=
      ∑ m ∈ directSet s,if m.family=.cross then g m else 0 := by
    rw [←Finset.sum_filter]
    congr 1
    ext m
    constructor
    · intro hm
      exact Finset.mem_filter.mpr ⟨incl hm,(Finset.mem_filter.mp hm).2⟩
    · intro hm
      have h := Finset.mem_filter.mp hm
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h.1).1,h.2⟩
  unfold Moments.shift moments imageMoment
  simp only
  simp_rw [Finset.sum_mul,restrict,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.family=.cross <;> simp [hm] <;> ring

def packedCorner (b : Cell) (terms : Moments) (shape : Fin 5 → Bool) (f : Fin 3 → Bool) : ℚ :=
  let p := shapePart b shape
  sixDot (primalMetric p) (terms.shift (offsetPart b f))+sixDot (dualMetric p) terms.reciprocal

private theorem dot_fold (s : Finset Mode) (row : Metric6) (w : Mode → ℚ) (v : Mode → Metric6) :
    sixDot row (fun j => ∑ m ∈ s,w m*v m j) = ∑ m ∈ s,w m*sixDot row (v m) := by
  unfold sixDot
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem packedCorner_eq (b : Cell) (s : Finset Mode) (w : Mode → ℚ) (bits : Axis → Bool) :
    packedCorner b (moments s w) (selectShape bits) (selectOffsets bits)=∑ m ∈ s,w m*m.atCorner b bits := by
  let f := offsetPart b (selectOffsets bits)
  have shifted : (moments s w).shift f = fun j => ∑ m ∈ directSet s,w m*
      imageMoment (fun k => (m.index k : ℚ)+if m.family=.cross then f k else 0) j :=
    funext (shift_eq s w f)
  unfold packedCorner
  change sixDot _ ((moments s w).shift f)+_=_
  rw [shifted,dot_fold]
  change _+sixDot _ (fun j => ∑ m ∈ reciprocalSet s,w m*imageMoment (fun i => (m.index i : ℚ)) j)=_
  rw [dot_fold]
  have direct : (∑ m ∈ directSet s,w m*sixDot (primalMetric (shapePart b (selectShape bits)))
      (imageMoment (fun i => (m.index i : ℚ)+if m.family=.cross then offsetPart b (selectOffsets bits) i else 0))) =
        ∑ m ∈ directSet s,w m*m.atCorner b bits := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [metric_primal b bits m (Finset.mem_filter.mp hm).2]
  rw [direct]
  have reciprocal : (∑ m ∈ reciprocalSet s,w m*sixDot (dualMetric (shapePart b (selectShape bits)))
      (imageMoment (fun i => (m.index i : ℚ))))=∑ m∈reciprocalSet s,w m*m.atCorner b bits := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [metric_dual b bits m (Finset.mem_filter.mp hm).2]
  rw [reciprocal,directSet,reciprocalSet,Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases e : m.family=.reciprocal <;> simp [e]

end BccSharp.Coulomb.CompactCover.Stage2
