import BccSharp.Cover.CoverDirectOperands
import BccSharp.Cover.CoverCorner

set_option autoImplicit false

/-! Exact whole-box maxima for the Direct exact-real sidecar.
The existing closed-corner argument is applied after squaring the two
positive radial coordinates. The expression is separately convex there. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.DirectRoute
open BccSharp.Coverage BravaisCover
open BccSharp.Intervals (Ball)

def squareDiag (b : Cell) : Cell :=
  ⟨fun i => if i.val<2 then (b.lo i)^2 else b.lo i,
    fun i => if i.val<2 then (b.hi i)^2 else b.hi i⟩

def squarePoint (p : Chart) : Chart := fun i => if i.val<2 then (p i)^2 else p i

theorem radialLoPos (b : Cell) (h : diagonalsCheck b=true) :
    (0:ℝ)<b.lo 0 ∧ (0:ℝ)<b.lo 1 := by
  obtain ⟨h0,h1,_⟩ := diagonalsCheck_sound h
  have e (i : Axis) : (coord b i).lo=b.lo i := by unfold coord ballOf Ball.lo; ring
  rw [e] at h0 h1
  exact ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩

theorem squarePoint_mem {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) :
    (squareDiag b).Mem (squarePoint p) := by
  intro i
  by_cases j : i.val<2
  · have h : (0:ℝ)<b.lo i := by
      have ij : i.val=0 ∨ i.val=1 := by omega
      rcases ij with j0 | j1
      · have he : i=0 := Fin.ext j0
        simpa [he] using (radialLoPos b hd).1
      · have he : i=1 := Fin.ext j1
        simpa [he] using (radialLoPos b hd).2
    have h₁ := pow_le_pow_left₀ h.le (hp i).1 2
    have h₂ := pow_le_pow_left₀ (h.le.trans (hp i).1) (hp i).2 2
    have elo : (squareDiag b).lo i=(b.lo i)^2 := ite_eq_left j
    have ehi : (squareDiag b).hi i=(b.hi i)^2 := ite_eq_left j
    have ep : squarePoint p i=(p i)^2 := ite_eq_left j
    rw [elo,ehi,ep]
    push_cast
    exact ⟨h₁,h₂⟩
  · have elo : (squareDiag b).lo i=b.lo i := ite_eq_right j
    have ehi : (squareDiag b).hi i=b.hi i := ite_eq_right j
    have ep : squarePoint p i=p i := ite_eq_right j
    rw [elo,ehi,ep]
    exact hp i

def chartImage (s : Bool) (n : IntVec) (p : Chart) (i : Fin 3) : ℝ :=
  (n i : ℝ)+(if s then p (offset i) else 0)

def formA (s : Bool) (n : IntVec) (p : Chart) : ℝ :=
  chartImage s n p 0+p 2*chartImage s n p 1+p 3*chartImage s n p 2

def formB (s : Bool) (n : IntVec) (p : Chart) : ℝ :=
  chartImage s n p 1+p 4*chartImage s n p 2

def formC (s : Bool) (n : IntVec) (p : Chart) : ℝ := chartImage s n p 2

def squaredRadial (s : Bool) (n : IntVec) (p : Chart) : ℝ :=
  p 0*(formA s n p)^2+p 1*(formB s n p)^2+(formC s n p)^2/((p 0)*(p 1))

theorem squaredRadial_eq (p : Chart) (s : Bool) (n : IntVec) :
    squaredRadial s n (squarePoint p)=quad (gram (chartBasis p)) (chartVector p s n) := by
  rw [←sq_mulVec_gram]
  cases s <;>
    norm_num [squaredRadial,squarePoint,formA,formB,formC,chartImage,chartVector,offset,
      castVec,chartPoint,sq,chartBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_three] <;>
    simp only [div_eq_mul_inv,mul_inv_rev,mul_pow,inv_pow] <;> ring

theorem affineSq_chord (x y t : ℝ) (lo : 0≤t) (hi : t≤1) :
    ((1-t)*x+t*y)^2 ≤ (1-t)*x^2+t*y^2 := by
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hi) lo) (sq_nonneg (x-y))
  nlinarith only [h]

private theorem inv_chord (x y t : ℝ) (xpos : 0<x) (ypos : 0<y) (lo : 0≤t) (hi : t≤1) :
    ((1-t)*x+t*y)⁻¹ ≤ (1-t)*x⁻¹+t*y⁻¹ := by
  let z := (1-t)*x+t*y
  have hz : 0<z := by
    dsimp [z]
    rcases eq_or_lt_of_le lo with eq | pos
    · simpa [←eq] using xpos
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hi) xpos.le) (mul_pos pos ypos)
  have identity : (1-t)*x⁻¹+t*y⁻¹-z⁻¹ = ((1-t)*t*(x-y)^2)/(x*y*z) := by
    field_simp [xpos.ne',ypos.ne',hz.ne'] <;> dsimp [z] <;> ring
  have nn : 0≤((1-t)*t*(x-y)^2)/(x*y*z) :=
    div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hi) lo) (sq_nonneg _)) (by positivity)
  exact sub_nonneg.mp (identity.symm ▸ nn)

private theorem offset_zero : offset 0=5 := rfl
private theorem offset_one : offset 1=6 := rfl
private theorem offset_two : offset 2=7 := rfl

private theorem affine_forms (b : Cell) (s : Bool) (n : IntVec) (p : Chart) (i : Axis)
    (i0 : i≠0) (i1 : i≠1) (t : ℝ) (e : p i=(1-t)*(b.lo i : ℝ)+t*(b.hi i : ℝ)) :
    formA s n p=(1-t)*formA s n (atLower b p i)+t*formA s n (atUpper b p i) ∧
    formB s n p=(1-t)*formB s n (atLower b p i)+t*formB s n (atUpper b p i) ∧
    formC s n p=(1-t)*formC s n (atLower b p i)+t*formC s n (atUpper b p i) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :=
    (by decide : ∀ a : Axis, a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7) i
  · exact absurd rfl i0
  · exact absurd rfl i1
  all_goals
    cases s <;>
    simp only [formA,formB,formC,chartImage,offset_zero,offset_one,offset_two,atLower,atUpper,
      Function.update_apply,Fin.reduceEq,↓reduceIte,Bool.false_eq_true] <;>
    refine ⟨?_,?_,?_⟩ <;> (try rw [e]) <;> ring

theorem radial_form (x y A B C t : ℝ) (hx : 0<x) (hy : 0<y)
    (hB : 0≤B) (lo : 0≤t) (hi : t≤1) :
    A*((1-t)*x+t*y)+B*((1-t)*x+t*y)⁻¹+C ≤
      (1-t)*(A*x+B*x⁻¹+C)+t*(A*y+B*y⁻¹+C) := by
  have h := mul_le_mul_of_nonneg_left (inv_chord x y t hx hy lo hi) hB
  linear_combination h

theorem squaredRadial_chord (s : Bool) (n : IntVec) (b : Cell) (h : diagonalsCheck b=true) :
    ChordUpper (squareDiag b) (squaredRadial s n) := by
  intro p hp i t low high e
  have radial := radialLoPos b h
  have h0 : (0:ℝ)<(squareDiag b).lo 0 := by
    change (0:ℝ)<(((b.lo 0)^2 : ℚ) : ℝ)
    push_cast
    exact pow_pos radial.1 2
  have h1 : (0:ℝ)<(squareDiag b).lo 1 := by
    change (0:ℝ)<(((b.lo 1)^2 : ℚ) : ℝ)
    push_cast
    exact pow_pos radial.2 2
  have p0 := h0.trans_le (hp 0).1
  have p1 := h1.trans_le (hp 1).1
  have u0 := p0.trans_le (hp 0).2
  have u1 := p1.trans_le (hp 1).2
  change (1-t)*(-squaredRadial s n (atLower (squareDiag b) p i))+
    t*(-squaredRadial s n (atUpper (squareDiag b) p i))≤-squaredRadial s n p
  by_cases eq0 : i=0
  · subst eq0
    have calc0 := radial_form ((squareDiag b).lo 0) ((squareDiag b).hi 0) ((formA s n p)^2)
      ((formC s n p)^2/(p 1)) (p 1*(formB s n p)^2) t h0 u0 (div_nonneg (sq_nonneg _) p1.le) low high
    have hplain (a : ℝ) : squaredRadial s n (Function.update p 0 a) =
        (formA s n p)^2*a+((formC s n p)^2/(p 1))*a⁻¹+p 1*(formB s n p)^2 := by
      simp only [squaredRadial,formA,formB,formC,chartImage,offset_zero,offset_one,offset_two,
        Function.update_apply,Fin.reduceEq,↓reduceIte]
      ring
    have hpplain := hplain (p 0)
    rw [Function.update_eq_self] at hpplain
    rw [←e] at calc0
    rw [hpplain]
    simp only [atLower,atUpper,hplain]
    linarith only [calc0]
  by_cases eq1 : i=1
  · subst eq1
    have calc1 := radial_form ((squareDiag b).lo 1) ((squareDiag b).hi 1) ((formB s n p)^2)
      ((formC s n p)^2/(p 0)) (p 0*(formA s n p)^2) t h1 u1 (div_nonneg (sq_nonneg _) p0.le) low high
    have hplain (a : ℝ) : squaredRadial s n (Function.update p 1 a) =
        (formB s n p)^2*a+((formC s n p)^2/(p 0))*a⁻¹+p 0*(formA s n p)^2 := by
      simp only [squaredRadial,formA,formB,formC,chartImage,offset_zero,offset_one,offset_two,
        Function.update_apply,Fin.reduceEq,↓reduceIte]
      ring
    have hpplain := hplain (p 1)
    rw [Function.update_eq_self] at hpplain
    rw [←e] at calc1
    rw [hpplain]
    simp only [atLower,atUpper,hplain]
    linarith only [calc1]
  obtain ⟨ha,hb,hc⟩ := affine_forms (squareDiag b) s n p i eq0 eq1 t e
  have a := mul_le_mul_of_nonneg_left (affineSq_chord (formA s n (atLower (squareDiag b) p i))
    (formA s n (atUpper (squareDiag b) p i)) t low high) p0.le
  have a' := mul_le_mul_of_nonneg_left (affineSq_chord (formB s n (atLower (squareDiag b) p i))
    (formB s n (atUpper (squareDiag b) p i)) t low high) p1.le
  have a'' := div_le_div_of_nonneg_right (affineSq_chord (formC s n (atLower (squareDiag b) p i))
    (formC s n (atUpper (squareDiag b) p i)) t low high) (mul_nonneg p0.le p1.le)
  rw [←ha] at a
  rw [←hb] at a'
  rw [←hc] at a''
  have L0 : atLower (squareDiag b) p i 0=p 0 := Function.update_of_ne (Ne.symm eq0) _ _
  have L1 : atLower (squareDiag b) p i 1=p 1 := Function.update_of_ne (Ne.symm eq1) _ _
  have U0 : atUpper (squareDiag b) p i 0=p 0 := Function.update_of_ne (Ne.symm eq0) _ _
  have U1 : atUpper (squareDiag b) p i 1=p 1 := Function.update_of_ne (Ne.symm eq1) _ _
  unfold squaredRadial
  simp only [L0,L1,U0,U1]
  simp only [div_eq_mul_inv] at a'' ⊢
  linear_combination a+a'+a''

def cornerRat (b : Cell) (bits : Axis → Bool) : Axis → ℚ := fun i => if bits i then b.hi i else b.lo i

def cornerDistance (b : Cell) (bits : Axis → Bool) (s : Bool) (n : IntVec) : ℚ :=
  let p := cornerRat b bits
  let v (i : Fin 3) := (n i : ℚ)+(if s then p (offset i) else 0)
  (p 0)^2*(v 0+p 2*v 1+p 3*v 2)^2+(p 1)^2*(v 1+p 4*v 2)^2+(v 2)^2/((p 0)^2*(p 1)^2)

theorem cornerDistance_eq (b : Cell) (bits : Axis → Bool) (s : Bool) (n : IntVec) :
    (cornerDistance b bits s n : ℝ)=squaredRadial s n (corner (squareDiag b) bits) := by
  have diagonal (i : Axis) : (corner (squareDiag b) bits) i =
      if i.val<2 then ((cornerRat b bits i : ℚ) : ℝ)^2 else (cornerRat b bits i : ℚ) := by
    show (if bits i then (((if i.val<2 then (b.hi i)^2 else b.hi i : ℚ)) : ℝ)
        else (((if i.val<2 then (b.lo i)^2 else b.lo i : ℚ)) : ℝ)) =
      if i.val<2 then (((if bits i then b.hi i else b.lo i : ℚ)) : ℝ)^2
        else (((if bits i then b.hi i else b.lo i : ℚ)) : ℝ)
    split_ifs <;> push_cast <;> rfl
  unfold cornerDistance squaredRadial formA formB formC chartImage
  push_cast
  simp only [diagonal,offset]
  cases s <;> norm_num

def exactUpperCheck (b : Cell) (s : Bool) (n : IntVec) (u : ℚ) : Bool :=
  decide (0<u ∧ (∀ bits : Axis → Bool, cornerDistance b bits s n≤u) ∧
    ∃ bits : Axis → Bool, cornerDistance b bits s n=u)

theorem exactUpperCheck_sound (b : Cell) (s : Bool) (n : IntVec) (u : ℚ)
    (ok : exactUpperCheck b s n u=true) (hd : diagonalsCheck b=true) (p : Chart) (hp : b.Mem p) :
    quad (gram (chartBasis p)) (chartVector p s n)≤(u : ℝ) := by
  have numeric : 0<u ∧ (∀ bits : Axis → Bool, cornerDistance b bits s n≤u) ∧
      ∃ bits : Axis → Bool, cornerDistance b bits s n=u := of_decide_eq_true ok
  have h := squaredRadial_chord s n b hd
  obtain ⟨bits,bound⟩ := corner_le (squareDiag b) (fun q => -squaredRadial s n q) h
    (squarePoint p) (squarePoint_mem hp hd)
  rw [←cornerDistance_eq, squaredRadial_eq] at bound
  exact (neg_le_neg_iff.mp bound).trans (by exact_mod_cast numeric.2.1 bits)

end BccSharp.Coulomb.CompactCover.DirectRoute
