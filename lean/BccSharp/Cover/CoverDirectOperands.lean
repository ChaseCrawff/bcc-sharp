import BccSharp.Lattice.StrictLeaves
import BccSharp.Cover.CoverReductionLeaves
import BccSharp.Analysis.TrigBounds

set_option autoImplicit false

/-! Exact boxes for Direct's direct positive Ewald bound. The rational
products use the four endpoint products, including when a factor changes
sign. The reciprocal phase is reduced in turns before bounding cosine. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.DirectRoute
open BccSharp BccSharp.Coverage BravaisCover
open BccSharp.Intervals (Ball)

theorem endpoints {b : Ball} {x : ℝ} (h : b.Contains x) :
    (b.lo : ℝ)≤x ∧ x≤(b.hi : ℝ) := by
  simpa [Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints b x).mp h

def coord (b : Cell) (i : Axis) : Ball := ballOf (b.lo i) (b.hi i)
theorem coord_sound {b : Cell} {p : Chart} (h : b.Mem p) (i : Axis) : (coord b i).Contains (p i) :=
  ballOf_sound (h i)

private theorem scalarRange (c a x b : ℝ) (ha : a≤x) (hb : x≤b) :
    min (c*a) (c*b)≤ c*x ∧ c*x≤ max (c*a) (c*b) := by
  by_cases hc : 0≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ha hc),
      (mul_le_mul_of_nonneg_left hb hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hb (le_of_not_ge hc)),
      (mul_le_mul_of_nonpos_left ha (le_of_not_ge hc)).trans (le_max_left _ _)⟩

def intervalMul (a b : Ball) : Ball :=
  ballOf (min (min (a.lo*b.lo) (a.hi*b.lo)) (min (a.lo*b.hi) (a.hi*b.hi)))
    (max (max (a.lo*b.lo) (a.hi*b.lo)) (max (a.lo*b.hi) (a.hi*b.hi)))

theorem intervalMul_sound {a b : Ball} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (intervalMul a b).Contains (x*y) := by
  obtain ⟨xl,xu⟩ := endpoints hx
  obtain ⟨yl,yu⟩ := endpoints hy
  have l := scalarRange (b.lo : ℝ) (a.lo : ℝ) x (a.hi : ℝ) xl xu
  have u := scalarRange (b.hi : ℝ) (a.lo : ℝ) x (a.hi : ℝ) xl xu
  have middle := scalarRange x (b.lo : ℝ) y (b.hi : ℝ) yl yu
  unfold intervalMul
  apply ballOf_sound
  push_cast
  rw [mul_comm (a.lo : ℝ) (b.lo : ℝ),mul_comm (a.hi : ℝ) (b.lo : ℝ),
    mul_comm (a.lo : ℝ) (b.hi : ℝ),mul_comm (a.hi : ℝ) (b.hi : ℝ)]
  have B := mul_comm (b.lo : ℝ) x
  have T := mul_comm (b.hi : ℝ) x
  rw [B] at l
  rw [T] at u
  exact ⟨(min_le_min l.1 u.1).trans middle.1,middle.2.trans (max_le_max l.2 u.2)⟩

def positiveInv (b : Ball) : Ball := ballOf b.hi⁻¹ b.lo⁻¹

theorem positiveInv_sound {b : Ball} {x : ℝ} (hl : (0:ℚ)<b.lo) (hx : b.Contains x) :
    (positiveInv b).Contains x⁻¹ := by
  have e := endpoints hx
  have lo : (0:ℝ)<b.lo := by exact_mod_cast hl
  apply ballOf_sound
  push_cast
  exact ⟨inv_anti₀ (lo.trans_le e.1) e.2,inv_anti₀ lo e.1⟩

private def scaled (z : ℤ) (b : Ball) := (Ball.exact (z : ℚ)).mul b

private theorem scaled_sound {z : ℤ} {b : Ball} {x : ℝ} (h : b.Contains x) :
    (scaled z b).Contains ((z : ℝ)*x) := by
  simpa [scaled] using Ball.contains_mul (Ball.contains_exact (z : ℚ)) h

def offset (i : Fin 3) : Axis := ⟨i.val+5,by omega⟩

theorem offset_eq (p : Chart) (i : Fin 3) : (chartPoint p).offset i=p (offset i) := by
  fin_cases i <;> rfl

def inputVector (b : Cell) (cross : Bool) (n : IntVec) (i : Fin 3) : Ball :=
  let v := Ball.exact (n i : ℚ)
  if cross then v.add (coord b (offset i)) else v

def chartVector (p : Chart) (cross : Bool) (n : IntVec) : Vec :=
  if cross then castVec n+(chartPoint p).offset else castVec n

private theorem inputVector_sound {b : Cell} {p : Chart} (hp : b.Mem p)
    (cross : Bool) (n : IntVec) (i : Fin 3) : (inputVector b cross n i).Contains (chartVector p cross n i) := by
  cases cross
  · simpa [inputVector,chartVector,castVec] using Ball.contains_exact (n i : ℚ)
  · simpa [inputVector,chartVector,castVec,offset_eq] using
      Ball.contains_add (Ball.contains_exact (n i : ℚ)) (coord_sound hp (offset i))

def diagonalsCheck (b : Cell) : Bool :=
  decide (0 < (coord b 0).lo ∧ 0 < (coord b 1).lo ∧ 0 < (intervalMul (coord b 0) (coord b 1)).lo)

theorem diagonalsCheck_sound {b : Cell} (h : diagonalsCheck b=true) :
    0 < (coord b 0).lo ∧ 0 < (coord b 1).lo ∧ 0 < (intervalMul (coord b 0) (coord b 1)).lo :=
  of_decide_eq_true h

def realDistance (b : Cell) (cross : Bool) (n : IntVec) : Ball :=
  let v := inputVector b cross n
  let r := coord b 0
  let s := coord b 1
  let u := intervalMul r ((v 0).add ((intervalMul (coord b 2) (v 1)).add (intervalMul (coord b 3) (v 2))))
  let w := intervalMul s ((v 1).add (intervalMul (coord b 4) (v 2)))
  let z := intervalMul (positiveInv (intervalMul r s)) (v 2)
  (sqBall u).add ((sqBall w).add (sqBall z))

theorem realDistance_sound {b : Cell} {p : Chart} (hp : b.Mem p) (h : diagonalsCheck b=true)
    (cross : Bool) (n : IntVec) :
    (realDistance b cross n).Contains (quad (gram (chartBasis p)) (chartVector p cross n)) := by
  have t i := inputVector_sound hp cross n i
  have r := coord_sound hp 0
  have s := coord_sound hp 1
  have a := intervalMul_sound (coord_sound hp 2) (t 1)
  have c := intervalMul_sound (coord_sound hp 3) (t 2)
  have u := intervalMul_sound r (Ball.contains_add (t 0) (Ball.contains_add a c))
  have w := intervalMul_sound s (Ball.contains_add (t 1) (intervalMul_sound (coord_sound hp 4) (t 2)))
  have z := intervalMul_sound (positiveInv_sound (diagonalsCheck_sound h).2.2 (intervalMul_sound r s)) (t 2)
  rw [← sq_mulVec_gram]
  convert Ball.contains_add (sqBall_sound u) (Ball.contains_add (sqBall_sound w) (sqBall_sound z)) using 1
  · rfl
  · simp [sq,chartBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
    ring

def reciprocalDistance (b : Cell) (n : IntVec) : Ball :=
  let r := coord b 0
  let s := coord b 1
  let a := coord b 2
  let c := coord b 4
  let u := scaled (n 0) (positiveInv r)
  let v := intervalMul ((Ball.exact (n 1 : ℚ)).sub (scaled (n 0) a)) (positiveInv s)
  let z := ((Ball.exact (n 2 : ℚ)).sub (scaled (n 1) c)).add
    (scaled (n 0) ((intervalMul a c).sub (coord b 3)))
  (sqBall u).add ((sqBall v).add (sqBall (intervalMul z (intervalMul r s))))

theorem dual_quad (B : Mat) (n : IntVec) :
    quad (gram B)⁻¹ (castVec n)=sq (cycleFrequency B n) := by
  rw [cycleFrequency,sq_mulVec_gram]
  simp only [gram,Matrix.transpose_transpose,Matrix.mul_inv_rev,Matrix.transpose_nonsing_inv]

theorem reciprocalDistance_sound {b : Cell} {p : Chart} (hp : b.Mem p) (h : diagonalsCheck b=true)
    (n : IntVec) : (reciprocalDistance b n).Contains (quad (gram (chartBasis p))⁻¹ (castVec n)) := by
  obtain ⟨hr,hs,_⟩ := diagonalsCheck_sound h
  have r := coord_sound hp 0
  have s := coord_sound hp 1
  have a := coord_sound hp 2
  have c := coord_sound hp 4
  have u := scaled_sound (z := n 0) (positiveInv_sound hr r)
  have v := intervalMul_sound (Ball.contains_sub (Ball.contains_exact (n 1 : ℚ)) (scaled_sound (z := n 0) a))
    (positiveInv_sound hs s)
  have z := Ball.contains_add
    (Ball.contains_sub (Ball.contains_exact (n 2 : ℚ)) (scaled_sound (z := n 1) c))
    (scaled_sound (z := n 0) (Ball.contains_sub (intervalMul_sound a c) (coord_sound hp 3)))
  have rpos := Ball.positive_sound (decide_eq_true hr) r
  have spos := Ball.positive_sound (decide_eq_true hs) s
  have chart : normalizedChart (takeShape p)=chartBasis p := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [dual_quad,←chart,← dualVector_eq (takeShape p) rpos.ne' spos.ne']
  convert Ball.contains_add (sqBall_sound u) (Ball.contains_add (sqBall_sound v)
    (sqBall_sound (intervalMul_sound z (intervalMul_sound r s)))) using 1
  · rfl
  · simp [sq,dualVector,takeShape,Fin.sum_univ_three]
    ring

def phaseTurns (b : Cell) (n : IntVec) : Ball :=
  (scaled (n 0) (coord b 5)).add ((scaled (n 1) (coord b 6)).add (scaled (n 2) (coord b 7)))

theorem phaseTurns_sound {b : Cell} {p : Chart} (hp : b.Mem p) (n : IntVec) :
    (phaseTurns b n).Contains (dot (castVec n) (chartPoint p).offset) := by
  convert Ball.contains_add (scaled_sound (z := n 0) (coord_sound hp 5))
    (Ball.contains_add (scaled_sound (z := n 1) (coord_sound hp 6)) (scaled_sound (z := n 2) (coord_sound hp 7))) using 1
  · rfl
  · simp [dot,castVec,chartPoint,Fin.sum_univ_three]
    ring

def phaseShift (u : Ball) : ℤ := ⌊u.mid+1/2⌋
def phaseDistance (u : Ball) : ℚ := |u.mid-(phaseShift u : ℚ)|+u.rad
def phaseArgument (u : Ball) : Ball := (Ball.exact (2*phaseDistance u)).mul Constants.piInput

def phaseLower (u : Ball) : Option ℚ :=
  if 1/2≤phaseDistance u then some 0
  else
    let a := phaseArgument u
    if |a.mid|/(65:ℚ)≤1/2 then some (max 0 (1+(TrigBounds.cosBall a 64).lo)) else none

/-- `phaseLower` with its `let` inlined, so that `rw` can reach both conditions. -/
private theorem phaseLower_eq (u : Ball) : phaseLower u=if 1/2≤phaseDistance u then some 0 else
    if |(phaseArgument u).mid|/(65:ℚ)≤1/2 then
      some (max 0 (1+(TrigBounds.cosBall (phaseArgument u) 64).lo)) else none := rfl

theorem phaseLower_sound {u : Ball} {x : ℝ} (hx : u.Contains x) (l : ℚ) (ok : phaseLower u=some l) :
    (l : ℝ)≤1+Real.cos (2*Real.pi*x) := by
  have trivialLower : (0:ℝ)≤1+Real.cos (2*Real.pi*x) := by linarith [Real.neg_one_le_cos (2*Real.pi*x)]
  by_cases wide : 1/2≤phaseDistance u
  · have zero : l=0 := by
      rw [phaseLower_eq,ite_eq_left wide] at ok
      exact (Option.some.inj ok).symm
    simpa [zero] using trivialLower
  · by_cases small : |(phaseArgument u).mid|/(65:ℚ)≤1/2
    · have ub : |x-(phaseShift u : ℝ)|≤(phaseDistance u : ℝ) := by
        have hx' : |x-(u.mid : ℝ)|≤(u.rad : ℝ) := hx
        have tri := abs_sub_le x (u.mid : ℝ) (phaseShift u : ℝ)
        have e : ((phaseDistance u : ℚ) : ℝ)=|(u.mid : ℝ)-(phaseShift u : ℝ)|+(u.rad : ℝ) := by
          simp [phaseDistance]
        rw [e]
        linarith
      have hr : (phaseDistance u : ℝ)<1/2 := by
        have h : ((phaseDistance u : ℚ) : ℝ)<((1/2 : ℚ) : ℝ) := Rat.cast_lt.mpr (lt_of_not_ge wide)
        rwa [show ((1/2 : ℚ) : ℝ)=1/2 by norm_num] at h
      have arg2 : 2*Real.pi*(phaseDistance u : ℝ)≤Real.pi := by
        calc
          _ ≤ 2*Real.pi*(1/2:ℝ) := mul_le_mul_of_nonneg_left hr.le (by positivity)
          _ = _ := by ring
      have absArg : |2*Real.pi*(x-(phaseShift u : ℝ))|=2*Real.pi*|x-(phaseShift u : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0≤2*Real.pi)]
      have mono : Real.cos (2*Real.pi*(phaseDistance u : ℝ))≤Real.cos |2*Real.pi*(x-(phaseShift u : ℝ))| := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) arg2
        rw [absArg]
        exact mul_le_mul_of_nonneg_left ub (by positivity)
      have per : Real.cos |2*Real.pi*(x-(phaseShift u : ℝ))|=Real.cos (2*Real.pi*x) := by
        rw [Real.cos_abs,show 2*Real.pi*(x-(phaseShift u : ℝ))=2*Real.pi*x-(phaseShift u : ℝ)*(2*Real.pi) by ring]
        exact Real.cos_sub_int_mul_two_pi _ _
      have arg : (phaseArgument u).Contains (2*Real.pi*(phaseDistance u : ℝ)) := by
        convert Ball.contains_mul (Ball.contains_exact (2*phaseDistance u)) Constants.piInput_sound using 1
        · rfl
        · push_cast; ring
      have point := TrigBounds.cos_contains arg (n := 64) (by decide) (by simpa using small)
      have bound := (endpoints point).1.trans (mono.trans_eq per)
      have eq : l=max 0 (1+(TrigBounds.cosBall (phaseArgument u) 64).lo) := by
        rw [phaseLower_eq,ite_eq_right wide,ite_eq_left small] at ok
        exact (Option.some.inj ok).symm
      rw [eq]
      push_cast
      exact max_le trivialLower (by linarith)
    · rw [phaseLower_eq,ite_eq_right wide,ite_eq_right small] at ok
      cases ok

theorem phaseLower_nonnegative {u : Ball} {l : ℚ} (ok : phaseLower u=some l) : 0≤l := by
  rw [phaseLower_eq] at ok
  split at ok
  · cases ok; exact le_rfl
  · split at ok
    · cases ok; exact le_max_left _ _
    · simp at ok

end BccSharp.Coulomb.CompactCover.DirectRoute
