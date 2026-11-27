import BccSharp.Lattice.LocalDifferentiation
import BccSharp.Analysis.FixedPoint
import BccSharp.Analysis.RoundedPolynomial

set_option autoImplicit false

/-! Fixed-point evaluation of the Lattice local-ball mode jets. The exact
index jets of `BccSharp.Lattice.LocalMetricJet` are converted once to integer
balls; every mode is then an integer quadratic form in those balls,
followed by an outward kernel enclosure. Near modes use the Constants erfc and
exponential witnesses on dyadic arguments; far modes use a crude
exponential bound. Every operation is proved to enclose the actual real
jet of `localModeJet`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.FixedLocal
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open Constants.HighPrecision
open StrainJet

abbrev FBall := FixedPoint.Ball
abbrev FJet := StrainJet FBall

/-! ## Integer balls and jets -/

def fsmul (c : ℤ) (b : FBall) : FBall := ⟨c * b.mid, |c| * b.rad⟩

theorem fsmul_contains {c : ℤ} {b : FBall} {x : ℝ} (h : b.Contains x) :
    (fsmul c b).Contains ((c : ℝ) * x) := by
  unfold FixedPoint.Ball.Contains FixedPoint.Ball.rational Intervals.Ball.Contains at *
  simp only [fsmul]
  push_cast at h ⊢
  have e : (c : ℝ) * x - (c : ℝ) * (b.mid : ℝ) / (FixedPoint.scale : ℝ) =
      (c : ℝ) * (x - (b.mid : ℝ) / (FixedPoint.scale : ℝ)) := by ring
  have f : |(c : ℝ)| * (b.rad : ℝ) / (FixedPoint.scale : ℝ) =
      |(c : ℝ)| * ((b.rad : ℝ) / (FixedPoint.scale : ℝ)) := by ring
  rw [e, abs_mul, f]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

def FRel (B : FJet) (a : StrainJet ℝ) : Prop :=
  B.value.Contains a.value ∧ (∀ i, (B.gradient i).Contains (a.gradient i)) ∧
    ∀ i j, (B.hessian i j).Contains (a.hessian i j)

def fixedOf (B : StrainJet Ball) : FJet := entrywise FixedPoint.Ball.fromBall B

theorem fixedOf_rel {B : StrainJet Ball} {a : StrainJet ℝ} (h : Rel B a) : FRel (fixedOf B) a :=
  ⟨FixedPoint.Ball.fromBall_contains h.1, fun i => FixedPoint.Ball.fromBall_contains (h.2.1 i),
    fun i j => FixedPoint.Ball.fromBall_contains (h.2.2 i j)⟩

def fzeroJet : FJet := constant FixedPoint.Ball.zero FixedPoint.Ball.zero

theorem fzeroJet_rel : FRel fzeroJet (constant 0 0) :=
  ⟨FixedPoint.Ball.zero_contains, fun _ => FixedPoint.Ball.zero_contains,
    fun _ _ => FixedPoint.Ball.zero_contains⟩

def fadd (A B : FJet) : FJet := combine FixedPoint.Ball.add A B

theorem fadd_rel {A B : FJet} {a b : StrainJet ℝ} (ha : FRel A a) (hb : FRel B b) :
    FRel (fadd A B) (combine (·+·) a b) :=
  ⟨FixedPoint.Ball.add_contains ha.1 hb.1,
    fun i => FixedPoint.Ball.add_contains (ha.2.1 i) (hb.2.1 i),
    fun i j => FixedPoint.Ball.add_contains (ha.2.2 i j) (hb.2.2 i j)⟩

def fchain (A : FJet) (V S C : FBall) : FJet :=
  chain FixedPoint.Ball.add FixedPoint.Ball.mul A V S C

theorem fchain_rel {A : FJet} {a : StrainJet ℝ} {V S C : FBall} {v s c : ℝ}
    (ha : FRel A a) (hv : V.Contains v) (hs : S.Contains s) (hc : C.Contains c) :
    FRel (fchain A V S C) (chain (·+·) (·*·) a v s c) :=
  ⟨hv, fun i => FixedPoint.Ball.mul_contains hs (ha.2.1 i), fun i j =>
    FixedPoint.Ball.add_contains
      (FixedPoint.Ball.mul_contains (FixedPoint.Ball.mul_contains hc (ha.2.1 i)) (ha.2.1 j))
      (FixedPoint.Ball.mul_contains hs (ha.2.2 i j))⟩

/-! ## Mode arguments as integer quadratic forms -/

def quadBall (B : Fin 3 → Fin 3 → FBall) (n : IntVec) : FBall :=
  let t (k l : Fin 3) := fsmul (n k * n l) (B k l)
  let r (k : Fin 3) := ((t k 0).add (t k 1)).add (t k 2)
  ((r 0).add (r 1)).add (r 2)

theorem quadBall_contains (B : Fin 3 → Fin 3 → FBall) (X : Fin 3 → Fin 3 → ℝ)
    (h : ∀ k l, (B k l).Contains (X k l)) (n : IntVec) :
    (quadBall B n).Contains (hessianQuadratic X (castVec n)) := by
  have term (k l : Fin 3) :
      (fsmul (n k * n l) (B k l)).Contains (X k l * castVec n k * castVec n l) := by
    have e : X k l * castVec n k * castVec n l = ((n k * n l : ℤ) : ℝ) * X k l := by
      simp only [castVec]; push_cast; ring
    rw [e]
    exact fsmul_contains (h k l)
  have row (k : Fin 3) :
      (((fsmul (n k * n 0) (B k 0)).add (fsmul (n k * n 1) (B k 1))).add
        (fsmul (n k * n 2) (B k 2))).Contains
      (X k 0 * castVec n k * castVec n 0 + X k 1 * castVec n k * castVec n 1 +
        X k 2 * castVec n k * castVec n 2) :=
    FixedPoint.Ball.add_contains (FixedPoint.Ball.add_contains (term k 0) (term k 1)) (term k 2)
  simp only [hessianQuadratic, Fin.sum_univ_three]
  exact FixedPoint.Ball.add_contains (FixedPoint.Ball.add_contains (row 0) (row 1)) (row 2)

def fquad (I : Fin 3 → Fin 3 → FJet) (n : IntVec) : FJet :=
  ⟨quadBall (fun k l => (I k l).value) n, fun i => quadBall (fun k l => (I k l).gradient i) n,
    fun i j => quadBall (fun k l => (I k l).hessian i j) n⟩

theorem fquad_rel (ref : Reference) (dual : Bool) (p : Point) (I : Fin 3 → Fin 3 → FJet)
    (hI : ∀ k l, FRel (I k l) (indexJet ref dual p k l)) (n : IntVec) :
    FRel (fquad I n) (localArgumentJet ref dual n p) := by
  obtain ⟨v, g, h⟩ := indexJet_expansion ref dual n p
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · rw [v]; exact quadBall_contains _ _ (fun k l => (hI k l).1) n
  · rw [g i]; exact quadBall_contains _ _ (fun k l => (hI k l).2.1 i) n
  · rw [h i j]; exact quadBall_contains _ _ (fun k l => (hI k l).2.2 i j) n

/-! ## Rounded kernel evaluation -/

def rb : Ball → Ball := RoundedPolynomial.roundBall

theorem rb_contains {b : Ball} {x : ℝ} (h : b.Contains x) : (rb b).Contains x :=
  RoundedPolynomial.round_contains h

def dyadicFloor (k : ℕ) (q : ℚ) : ℚ := (⌊q*2^k⌋ : ℤ)/2^k
def dyadicCeil (k : ℕ) (q : ℚ) : ℚ := (⌈q*2^k⌉ : ℤ)/2^k

theorem dyadicFloor_le (k : ℕ) (q : ℚ) : dyadicFloor k q ≤ q := by
  unfold dyadicFloor
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem le_dyadicCeil (k : ℕ) (q : ℚ) : q ≤ dyadicCeil k q := by
  unfold dyadicCeil
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

def roundOut (b : Ball) : Ball := ballOf (dyadicFloor 64 b.lo) (dyadicCeil 64 b.hi)

theorem roundOut_contains {b : Ball} {x : ℝ} (h : b.Contains x) : (roundOut b).Contains x := by
  have e := (SpecialFunctions.contains_iff_endpoints b x).mp h
  apply ballOf_sound
  constructor
  · have f : (dyadicFloor 64 b.lo : ℝ) ≤ (b.lo : ℝ) := by exact_mod_cast dyadicFloor_le 64 b.lo
    exact f.trans (by simpa [Ball.lo] using e.1)
  · have f : (b.hi : ℝ) ≤ (dyadicCeil 64 b.hi : ℝ) := by exact_mod_cast le_dyadicCeil 64 b.hi
    exact (by simpa [Ball.hi] using e.2 : x ≤ (b.hi : ℝ)).trans f

def shortRoot (power : ℕ) (xlo xhi hi : ℚ) (steps : ℕ) : RootProposal :=
  ⟨(Constants.bisect power xlo steps (0, hi)).1, (Constants.bisect power xhi steps (0, hi)).2⟩

def expPointShort (x : ℚ) : ExpBounds.PointWitness :=
  let t := x/256
  let s := rb (RoundedPolynomial.expBound t 24)
  let sq₁ := rb (s.mul s)
  let sq₂ := rb (sq₁.mul sq₁)
  let sq₃ := rb (sq₂.mul sq₂)
  let sq₄ := rb (sq₃.mul sq₃)
  let sq₅ := rb (sq₄.mul sq₄)
  let sq₆ := rb (sq₅.mul sq₅)
  let sq₇ := rb (sq₆.mul sq₆)
  let sq₈ := rb (sq₇.mul sq₇)
  ⟨24, s, [sq₁,sq₂,sq₃,sq₄,sq₅,sq₆,sq₇,sq₈]⟩

def expShort (a : Ball) : ExpBounds.Witness :=
  let l := expPointShort (a.mid-a.rad)
  let u := expPointShort (a.mid+a.rad)
  let lo := l.bound.mid - l.bound.rad
  let hi := u.bound.mid + u.bound.rad
  ⟨l, u, ⟨(lo+hi)/2, (hi-lo)/2⟩⟩

/-- Integer bisection: the largest `s ≤ hi` reached with `s*s ≤ N`. A proposal only;
`RootProposal.check` verifies the resulting bracket. -/
def natSqrtLoop (N : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f+1, lo, hi =>
    if hi ≤ lo + 1 then lo else
      let m := (lo + hi) / 2
      if m*m ≤ N then natSqrtLoop N f m hi else natSqrtLoop N f lo m

/-- Square-root bracket of a nonnegative rational at resolution `2^-64`. -/
def rootOf (q : ℚ) : RootProposal :=
  let N : ℕ := (q.num * 2^128 / (q.den : ℤ)).toNat
  let s := natSqrtLoop N 80 0 (2^70)
  ⟨(s : ℚ)/2^64, ((s+1 : ℕ) : ℚ)/2^64⟩

def erfcAt (q : ℚ) : ErfcSeriesProposal :=
  let s := rootOf q
  let n := 2*(⌈q⌉.toNat) + 48
  ⟨s, n, dyadicCeil 128 (4 * (s.ball.mid+s.ball.rad) *
    (Constants.piInverseRoot.mid+ Constants.piInverseRoot.rad) * q^n / (n.factorial : ℚ))⟩

def proposeKernel (kind : KernelKind) (t : Ball) : KernelWitness :=
  match kind with
  | .one => .one (expShort t.neg)
  | .half => .half (erfcAt t.lo) (erfcAt t.hi) (expShort t.neg)

def fastHalfAt (q : ℚ) (w : ErfcSeriesProposal) : Ball :=
  rb (Constants.piInverseRoot.inv.mul (rb ((Constants.fastResult w q Constants.piInverseRoot).mul w.root.ball.inv)))

theorem fastHalfAt_sound (t : ℚ) (ht : 0 < (t : ℝ)) (w : ErfcSeriesProposal)
    (rootOK : Constants.piRoot.check Constants.piInput = true) (invOK : Constants.piInverseRoot.invertible)
    (ok : w.check t Constants.piInverseRoot = true) :
    (fastHalfAt t w).Contains (gKernel (1/2) (t : ℝ)) := by
  have hs := Constants.piInverseRoot_sound rootOK
  have hs' := Ball.contains_inv invOK hs
  have he := ErfcSeriesProposal.sound w t Constants.piInverseRoot hs ok
  rw [← Constants.fastResult_eq] at he
  have hr := RootProposal.inverse_sound w.root (Ball.exact t) t ht.le (Ball.contains_exact t)
    (Bool.and_eq_true_iff.mp ok).1
  have h := rb_contains (Ball.contains_mul hs' (rb_contains (Ball.contains_mul he hr)))
  rw [halfKernel_formula ht]
  simpa [fastHalfAt, div_eq_mul_inv, mul_assoc] using h

def fastValueBall (w : KernelWitness) (t : Ball) : Ball :=
  match w with
  | .one e => rb (e.result.mul t.inv)
  | .half wl wu _ => ballOf (fastHalfAt t.hi wu).lo (fastHalfAt t.lo wl).hi

theorem fastValue_sound (w : KernelWitness) {t : Ball} {x : ℝ} (hx : t.Contains x)
    (ok : w.check t = true) : (fastValueBall w t).Contains (kernelValue w.kind x) := by
  have h := Bool.and_eq_true_iff.mp ok
  have hp := Bool.and_eq_true_iff.mp h.1
  have h0 := Ball.positive_sound hp.1 hx
  have hinv := Ball.contains_inv (of_decide_eq_true hp.2) hx
  have he := Bool.and_eq_true_iff.mp h.2
  have hex := ExpBounds.Witness.sound he.1 (Ball.contains_neg hx)
  cases w with
  | one e =>
    show (rb (e.result.mul t.inv)).Contains (kernelValue .one x)
    rw [show kernelValue (.one : KernelKind) x = Real.exp (-x)/x by
      simpa [kernelValue,KernelKind.power] using gKernel_one h0,div_eq_mul_inv]
    exact rb_contains (Ball.contains_mul hex hinv)
  | half wl wu e =>
    have hb := Bool.and_eq_true_iff.mp he.2
    have hroot := Bool.and_eq_true_iff.mp hb.1
    have herfc := Bool.and_eq_true_iff.mp hb.2
    have hends : (t.lo : ℝ) ≤ x ∧ x ≤ (t.hi : ℝ) := by
      simpa [Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints t x).mp hx
    have hlo : (0 : ℝ) < t.lo := by exact_mod_cast (of_decide_eq_true hp.1 : 0 < t.lo)
    have hhi : (0 : ℝ) < t.hi := h0.trans_le hends.2
    have hl := fastHalfAt_sound t.lo hlo wl hroot.1 (of_decide_eq_true hroot.2) herfc.1
    have hu := fastHalfAt_sound t.hi hhi wu hroot.1 (of_decide_eq_true hroot.2) herfc.2
    have hl' : gKernel (1/2) (t.lo : ℝ) ≤ ((fastHalfAt t.lo wl).hi : ℝ) := by
      simpa [Ball.hi] using ((SpecialFunctions.contains_iff_endpoints _ _).mp hl).2
    have hu' : ((fastHalfAt t.hi wu).lo : ℝ) ≤ gKernel (1/2) (t.hi : ℝ) := by
      simpa [Ball.lo] using ((SpecialFunctions.contains_iff_endpoints _ _).mp hu).1
    have out := ballOf_sound ⟨hu'.trans (halfKernel_decreasing h0 hends.2),
      (halfKernel_decreasing hlo hends.1).trans hl'⟩
    simpa [fastValueBall,KernelWitness.kind,kernelValue,KernelKind.power] using out

def fastEvaluate (w : KernelWitness) (t : Ball) : KernelBall :=
  let v := fastValueBall w t
  let exp := w.exponentialWitness.result
  let u := rb (((exp.add ((Ball.exact w.kind.power).mul v)).neg).mul t.inv)
  ⟨v,u,rb ((exp.sub ((Ball.exact (w.kind.power+1)).mul u)).mul t.inv)⟩

theorem fastEvaluate_sound (w : KernelWitness) {t : Ball} {x : ℝ} (hx : t.Contains x)
    (ok : w.check t = true) :
    ((fastEvaluate w t).value).Contains (kernelValue w.kind x) ∧
    ((fastEvaluate w t).slope).Contains (kernelSlope w.kind x) ∧
    ((fastEvaluate w t).curvature).Contains (kernelCurvature w.kind x) := by
  have h := Bool.and_eq_true_iff.mp ok
  have hinv := Ball.contains_inv (of_decide_eq_true (Bool.and_eq_true_iff.mp h.1).2) hx
  have he := ExpBounds.Witness.sound (Bool.and_eq_true_iff.mp h.2).1 (Ball.contains_neg hx)
  have hv := fastValue_sound w hx ok
  have hs := rb_contains (Ball.contains_mul (Ball.contains_neg (Ball.contains_add he
    (Ball.contains_mul (Ball.contains_exact w.kind.power) hv))) hinv)
  have hc := rb_contains (Ball.contains_mul (Ball.contains_sub he
    (Ball.contains_mul (Ball.contains_exact (w.kind.power+1)) hs)) hinv)
  exact ⟨hv,by simpa [fastEvaluate,kernelSlope,div_eq_mul_inv] using hs,
    by simpa [fastEvaluate,kernelSlope,kernelCurvature,div_eq_mul_inv,Rat.cast_add] using hc⟩

/-- Crude far-mode radius: `(1+t/64)^64 ≤ exp t`. -/
def crudeRadius (t : ℚ) : ℚ := ((1+t/64)^64*t)⁻¹

theorem crudeRadius_sound {t x : ℝ} (ht : 1 ≤ t) (h : t ≤ x) :
    Real.exp (-x)/x ≤ ((1+t/64)^64*t)⁻¹ := by
  have ht' := zero_lt_one.trans_le ht
  have v : 1+t/64 ≤ Real.exp (t/64) := by simpa only [add_comm] using Real.add_one_le_exp (t/64)
  have H := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+t/64) v 64
  rw [← Real.exp_nat_mul (t/64) 64] at H
  have E : (64 : ℝ)*(t/64)=t := by ring
  have H' : (1+t/64)^64 ≤ Real.exp t := by simpa [E] using H
  have T : 0 < (1+t/64)^64*t := by positivity
  have V : (1+t/64)^64*t ≤ Real.exp x*x :=
    mul_le_mul (H'.trans (Real.exp_le_exp.mpr h)) h ht'.le (Real.exp_pos _).le
  rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv]
  simpa only [one_div] using one_div_le_one_div_of_le T V

def crudeKernel (t : ℚ) : FBall × FBall × FBall :=
  let r := crudeRadius t
  (FixedPoint.Ball.fromBall (ballOf 0 r), FixedPoint.Ball.fromBall ⟨0, 2*r⟩,
    FixedPoint.Ball.fromBall ⟨0, 5*r⟩)

theorem crudeKernel_sound (k : KernelKind) {t : ℚ} {x : ℝ} (ht : 1 ≤ t) (hx : (t : ℝ) ≤ x) :
    (crudeKernel t).1.Contains (kernelValue k x) ∧ (crudeKernel t).2.1.Contains (kernelSlope k x) ∧
      (crudeKernel t).2.2.Contains (kernelCurvature k x) := by
  have lim : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have R : Real.exp (-x)/x ≤ (crudeRadius t : ℝ) := by
    simpa [crudeRadius] using crudeRadius_sound lim hx
  have V := kernelValue_positive_bound k (zero_lt_one.trans_le (lim.trans hx))
  have D := kernelDerivative_bounds k (lim.trans hx)
  have S : |kernelSlope k x| ≤ 2*(Real.exp (-x)/x) := by rw [← mul_div_assoc]; exact D.1
  have K : |kernelCurvature k x| ≤ 5*(Real.exp (-x)/x) := by rw [← mul_div_assoc]; exact D.2
  refine ⟨FixedPoint.Ball.fromBall_contains (ballOf_sound ⟨by simpa using V.1, V.2.trans R⟩),
    FixedPoint.Ball.fromBall_contains ?_, FixedPoint.Ball.fromBall_contains ?_⟩
  · simpa [Ball.Contains] using S.trans (mul_le_mul_of_nonneg_left R (by norm_num : (0 : ℝ) ≤ 2))
  · simpa [Ball.Contains] using K.trans (mul_le_mul_of_nonneg_left R (by norm_num : (0 : ℝ) ≤ 5))

def nearKernel (kind : KernelKind) (t : FBall) : Option (FBall × FBall × FBall) :=
  let tr := roundOut t.rational
  let w := proposeKernel kind tr
  if w.kind = kind ∧ w.check tr = true then
    let k := fastEvaluate w tr
    some (FixedPoint.Ball.fromBall k.value, FixedPoint.Ball.fromBall k.slope,
      FixedPoint.Ball.fromBall k.curvature)
  else none

theorem nearKernel_sound {kind : KernelKind} {t : FBall} {x : ℝ} {V S C : FBall}
    (h : nearKernel kind t = some (V, S, C)) (hx : t.Contains x) :
    V.Contains (kernelValue kind x) ∧ S.Contains (kernelSlope kind x) ∧
      C.Contains (kernelCurvature kind x) := by
  unfold nearKernel at h
  dsimp only at h
  split_ifs at h with ok
  have e := Option.some.inj h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  have hx' := roundOut_contains (b := t.rational) hx
  have k := fastEvaluate_sound (proposeKernel kind (roundOut t.rational)) hx' ok.2
  rw [ok.1] at k
  exact ⟨FixedPoint.Ball.fromBall_contains k.1, FixedPoint.Ball.fromBall_contains k.2.1,
    FixedPoint.Ball.fromBall_contains k.2.2⟩

/-- `(1+t/256)^256 ≤ exp t`. -/
theorem crude256_sound {t x : ℝ} (ht : 1 ≤ t) (h : t ≤ x) :
    Real.exp (-x)/x ≤ ((1+t/256)^256*t)⁻¹ := by
  have ht' := zero_lt_one.trans_le ht
  have v : 1+t/256 ≤ Real.exp (t/256) := by simpa only [add_comm] using Real.add_one_le_exp (t/256)
  have H := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+t/256) v 256
  rw [← Real.exp_nat_mul (t/256) 256] at H
  have E : (256 : ℝ)*(t/256)=t := by ring
  have H' : (1+t/256)^256 ≤ Real.exp t := by simpa [E] using H
  have T : 0 < (1+t/256)^256*t := by positivity
  have V : (1+t/256)^256*t ≤ Real.exp x*x :=
    mul_le_mul (H'.trans (Real.exp_le_exp.mpr h)) h ht'.le (Real.exp_pos _).le
  rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv]
  simpa only [one_div] using one_div_le_one_div_of_le T V

/-- `⌈2^7348/((2^28+τ)^256 τ)⌉`, the far-mode radius in units of `2^-160`
for the argument bound `τ/2^20`. Natural-number arithmetic only. -/
def crudeFixed (tau : ℕ) : ℕ :=
  let den := (2^28 + tau)^256 * tau
  (2^7348 + den - 1) / den

theorem fixedScale_eq : FixedPoint.scale = 2^160 := by norm_num [FixedPoint.scale]

theorem crudeFixed_sound {tau : ℕ} (htau : 20*2^20 ≤ tau) {x : ℝ} (hx : (tau : ℝ)/2^20 ≤ x) :
    Real.exp (-x)/x ≤ (crudeFixed tau : ℝ)/2^160 := by
  have hpos : 0 < tau := by omega
  set den : ℕ := (2^28 + tau)^256 * tau with hden
  have dpos : 0 < den := by positivity
  have ceil : 2^7348 ≤ crudeFixed tau * den := by
    have h := Nat.lt_div_mul_add (a := 2^7348 + den - 1) dpos
    unfold crudeFixed
    simp only [← hden]
    set P := (2^7348 + den - 1) / den * den with hP
    omega
  have t1 : (1 : ℝ) ≤ (tau : ℝ)/2^20 := by
    rw [le_div_iff₀ (by positivity)]
    have : ((20*2^20 : ℕ) : ℝ) ≤ (tau : ℝ) := by exact_mod_cast htau
    push_cast at this
    linarith
  have base := crude256_sound t1 hx
  have ident : (1+((tau : ℝ)/2^20)/256)^256*((tau : ℝ)/2^20) = (den : ℝ)/2^7188 := by
    have e : 1+((tau : ℝ)/2^20)/256 = ((2:ℝ)^28+tau)/2^28 := by field_simp; ring
    rw [e, div_pow, div_mul_div_comm, ← pow_mul, ← pow_add, hden]
    push_cast
    norm_num
  rw [ident, inv_div] at base
  refine base.trans ?_
  rw [div_le_div_iff₀ (by exact_mod_cast dpos) (by positivity)]
  have c : ((2^7348 : ℕ) : ℝ) ≤ (crudeFixed tau : ℝ) * (den : ℝ) := by exact_mod_cast ceil
  push_cast at c
  calc (2:ℝ)^7188 * 2^160 = 2^7348 := by rw [← pow_add]
    _ ≤ _ := c

def farLimitFixed : ℤ := 20*2^160

def kernelBalls (dual : Bool) (t : FBall) : Option (FBall × FBall × FBall) :=
  let lo := t.mid - t.rad
  if farLimitFixed ≤ lo then
    let r : ℤ := crudeFixed (lo / 2^140).toNat
    some (⟨0, r⟩, ⟨0, 2*r⟩, ⟨0, 5*r⟩)
  else nearKernel (localKernelKind dual) t

theorem fixedScale_real : ((FixedPoint.scale : ℤ) : ℝ) = (2:ℝ)^160 := by
  rw [fixedScale_eq]; norm_num

theorem fixed_zero_contains {r : ℤ} {x : ℝ} (h : |x| ≤ (r : ℝ)/2^160) :
    (⟨0, r⟩ : FBall).Contains x := by
  have hs : ((FixedPoint.scale : ℤ) : ℚ) = 2^160 := by rw [fixedScale_eq]; norm_num
  unfold FixedPoint.Ball.Contains FixedPoint.Ball.rational Intervals.Ball.Contains
  rw [hs]
  simp only [Int.cast_zero, zero_div, Rat.cast_zero, sub_zero, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_pow, Rat.cast_ofNat]
  exact h

theorem kernelBalls_sound {dual : Bool} {t : FBall} {x : ℝ} {V S C : FBall}
    (h : kernelBalls dual t = some (V, S, C)) (hx : t.Contains x) :
    V.Contains (kernelValue (localKernelKind dual) x) ∧
      S.Contains (kernelSlope (localKernelKind dual) x) ∧
      C.Contains (kernelCurvature (localKernelKind dual) x) := by
  unfold kernelBalls at h
  dsimp only at h
  split_ifs at h with far
  · have e := Option.some.inj h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    have hlo : (((t.mid - t.rad : ℤ) : ℝ))/2^160 ≤ x := by
      have c := (SpecialFunctions.contains_iff_endpoints t.rational x).mp hx
      have c1 := c.1
      simp only [FixedPoint.Ball.rational, Rat.cast_div, Rat.cast_intCast] at c1
      rw [fixedScale_real] at c1
      rw [Int.cast_sub, sub_div]
      exact c1
    set lo : ℤ := t.mid - t.rad with hlo_def
    have q0 : 0 ≤ lo / 2^140 := by
      apply Int.ediv_nonneg _ (by norm_num)
      have : (0 : ℤ) ≤ farLimitFixed := by norm_num [farLimitFixed]
      linarith
    set tau : ℕ := (lo / 2^140).toNat with htau_def
    have htau : (tau : ℤ) = lo / 2^140 := Int.toNat_of_nonneg q0
    have mul_le : (tau : ℤ) * 2^140 ≤ lo := by rw [htau]; exact Int.ediv_mul_le lo (by norm_num)
    have big : 20*2^20 ≤ tau := by
      have h1 : 20*2^160 ≤ lo := far
      have h2 : (20*2^20 : ℤ) ≤ lo / 2^140 := by
        rw [Int.le_ediv_iff_mul_le (by norm_num)]
        norm_num at h1 ⊢
        try exact h1
      omega
    have targ : (tau : ℝ)/2^20 ≤ x := by
      have m : ((tau : ℤ) : ℝ) * 2^140 ≤ (lo : ℝ) := by exact_mod_cast mul_le
      have e : (tau : ℝ)/2^20 = ((tau : ℤ) : ℝ) * 2^140 / 2^160 := by
        rw [Int.cast_natCast, mul_div_assoc, show ((2:ℝ)^140/2^160) = 1/2^20 by norm_num]
        ring
      rw [e]
      exact (div_le_div_of_nonneg_right m (by positivity)).trans hlo
    have R := crudeFixed_sound big targ
    have pos : (1 : ℝ) ≤ x := by
      have : (1 : ℝ) ≤ (tau : ℝ)/2^20 := by
        rw [le_div_iff₀ (by positivity)]
        have : ((20*2^20 : ℕ) : ℝ) ≤ (tau : ℝ) := by exact_mod_cast big
        push_cast at this
        linarith
      linarith
    have Vb := kernelValue_positive_bound (localKernelKind dual) (zero_lt_one.trans_le pos)
    have D := kernelDerivative_bounds (localKernelKind dual) pos
    have castR : ((crudeFixed tau : ℤ) : ℝ) = (crudeFixed tau : ℝ) := by push_cast; rfl
    refine ⟨fixed_zero_contains ?_, fixed_zero_contains ?_, fixed_zero_contains ?_⟩
    · rw [castR, abs_of_nonneg Vb.1]
      exact Vb.2.trans R
    · push_cast
      calc |kernelSlope (localKernelKind dual) x| ≤ 2*(Real.exp (-x)/x) := by
            rw [← mul_div_assoc]; exact D.1
        _ ≤ 2*((crudeFixed tau : ℝ)/2^160) := by linarith
        _ = _ := by ring
    · push_cast
      calc |kernelCurvature (localKernelKind dual) x| ≤ 5*(Real.exp (-x)/x) := by
            rw [← mul_div_assoc]; exact D.2
        _ ≤ 5*((crudeFixed tau : ℝ)/2^160) := by linarith
        _ = _ := by ring
  · exact nearKernel_sound h hx

/-! ## Modes and their finite sum -/

/-- One mode's fixed-point jet from a proposed argument jet `arg n`. -/
def fmode (dual : Bool) (arg : IntVec → FJet) (n : IntVec) : Option FJet :=
  if n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 then some fzeroJet else
  let A := arg n
  match kernelBalls dual A.value with
  | some (V, S, C) => some (fchain A V S C)
  | none => none

theorem intVec_eq_zero {n : IntVec} (h : n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0) : n = 0 := by
  funext i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem fmode_rel (ref : Reference) (dual : Bool) (p : Point) (arg : IntVec → FJet)
    (harg : ∀ n, n ≠ 0 → FRel (arg n) (localArgumentJet ref dual n p)) (n : IntVec) (B : FJet)
    (h : fmode dual arg n = some B) : FRel B (localModeJet ref dual n p) := by
  unfold fmode at h
  by_cases hz : n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0
  · rw [if_pos hz] at h
    rw [← Option.some.inj h, localModeJet, if_pos (intVec_eq_zero hz)]
    exact fzeroJet_rel
  · rw [if_neg hz] at h
    have nz : n ≠ 0 := by
      intro e
      apply hz
      simp [e]
    dsimp only at h
    have A := harg n nz
    cases hk : kernelBalls dual (arg n).value with
    | none => rw [hk] at h; simp at h
    | some k =>
      obtain ⟨V, S, C⟩ := k
      rw [hk] at h
      rw [← Option.some.inj h, localModeJet, if_neg nz]
      have K := kernelBalls_sound hk A.1
      exact fchain_rel A K.1 K.2.1 K.2.2

def ffold (dual : Bool) (arg : IntVec → FJet) : List IntVec → FJet → Option FJet
  | [], s => some s
  | n :: ns, s => match fmode dual arg n with
    | none => none
    | some J => ffold dual arg ns (fadd s J)

theorem ffold_some (dual : Bool) (arg : IntVec → FJet) :
    ∀ (l : List IntVec) (s S : FJet), ffold dual arg l s = some S →
      ∀ n ∈ l, ∃ B, fmode dual arg n = some B := by
  intro l
  induction l with
  | nil => intro s S _ n hn; simp at hn
  | cons m ms ih =>
    intro s S h n hn
    simp only [ffold] at h
    cases hm : fmode dual arg m with
    | none => rw [hm] at h; simp at h
    | some J =>
      rw [hm] at h
      rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨J, hm⟩
      · exact ih _ _ h n hn

theorem ffold_rel (ref : Reference) (dual : Bool) (p : Point) (arg : IntVec → FJet)
    (harg : ∀ n, n ≠ 0 → FRel (arg n) (localArgumentJet ref dual n p)) :
    ∀ (l : List IntVec) (s : FJet) (a : StrainJet ℝ) (S : FJet), FRel s a → ffold dual arg l s = some S →
      FRel S (l.foldl (fun acc n => combine (·+·) acc (localModeJet ref dual n p)) a) := by
  intro l
  induction l with
  | nil => intro s a S hs h; simp only [ffold, Option.some.injEq] at h; subst h; exact hs
  | cons m ms ih =>
    intro s a S hs h
    simp only [ffold] at h
    cases hm : fmode dual arg m with
    | none => rw [hm] at h; simp at h
    | some J =>
      rw [hm] at h
      exact ih _ _ _ (fadd_rel hs (fmode_rel ref dual p arg harg m J hm)) h

theorem foldl_combine_hessian (f : IntVec → StrainJet ℝ) (i j : Fin 5) :
    ∀ (l : List IntVec) (a : StrainJet ℝ),
      (l.foldl (fun acc n => combine (·+·) acc (f n)) a).hessian i j =
        a.hessian i j + (l.map (fun n => (f n).hessian i j)).sum := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons m ms ih => intro a; rw [List.foldl_cons, ih]; simp [combine, add_assoc]

/-! ## Cartesian mode arguments

`localArgumentJet` is `π·vᵀ C v` with `v = localVector ref dual n`. Writing
`v = μ·q` with an integer vector `q` turns each argument jet into one scalar
ball times an integer quadratic form in the Cartesian metric jets, which
are close to the identity, so the nine terms do not cancel. -/

/-- Integer coordinates `q` with `localVector ref dual n = qfactor ref dual • q`. -/
def qvec : Reference → Bool → IntVec → IntVec
  | .bcc, false, n => ![2*n 0 + n 2, 2*n 1 + n 2, n 2]
  | .bcc, true, n => ![n 0, n 1, 2*n 2 - n 0 - n 1]
  | .fcc, false, n => ![n 0 + n 1, n 0 + n 2, n 1 + n 2]
  | .fcc, true, n => ![n 0 + n 1 - n 2, n 0 - n 1 + n 2, -(n 0) + n 1 + n 2]

def qfactor : Reference → Bool → ℝ
  | .bcc, false => Constants.fccLength / 2
  | .bcc, true => Constants.fccLength⁻¹
  | .fcc, false => Constants.fccLength⁻¹
  | .fcc, true => Constants.fccLength / 2

private theorem fccVector_eq' (dual : Bool) (n : IntVec) :
    localVector .fcc dual n = (if dual then Constants.fccLength else Constants.fccLength⁻¹) •
      (fun i => (fccFrameQ dual n i : ℝ)) := by
  cases dual
  · ext i
    fin_cases i <;> norm_num [localVector, cubicBasis, linearImage, Matrix.mulVec, dotProduct,
      fccFrameQ, castVec, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;>
      push_cast <;> ring
  · have hd : (cubicBasis .fcc).det ≠ 0 := by
      have h := cubicBasis_unitVolume .fcc
      change |(cubicBasis .fcc).det|=1 at h
      intro hd; simpa [hd] using h
    have hu : IsUnit (cubicBasis .fcc).transpose := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact isUnit_iff_ne_zero.mpr hd
    apply Matrix.mulVec_injective_of_isUnit hu
    change (cubicBasis .fcc).transpose.mulVec (cycleFrequency (cubicBasis .fcc) n) = _
    rw [cycleFrequency_transpose _ hd]
    have ht : Constants.fccLength ≠ 0 := by unfold Constants.fccLength; positivity
    ext i
    fin_cases i <;> norm_num [cubicBasis, fccFrameQ, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.smul_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, castVec] <;>
      push_cast <;> field_simp [ht] <;> ring

theorem localVector_qvec (ref : Reference) (dual : Bool) (n : IntVec) (i : Fin 3) :
    localVector ref dual n i = qfactor ref dual * (qvec ref dual n i : ℝ) := by
  cases ref <;> cases dual
  · have e := congrFun (bccCubic_short n) i
    show linearImage (cubicBasis .bcc) n i = _
    rw [e]
    fin_cases i <;> simp [bccFrameDirect, qvec, qfactor, Pi.smul_apply, smul_eq_mul] <;> ring
  · have e := congrFun (bccCubic_dual n) i
    show cycleFrequency (cubicBasis .bcc) n i = _
    rw [e]
    fin_cases i <;> simp [bccFrameDual, qvec, qfactor, Pi.smul_apply, smul_eq_mul]
  · have e := congrFun (fccVector_eq' false n) i
    rw [e]
    fin_cases i <;> simp [fccFrameQ, qvec, qfactor, Pi.smul_apply, smul_eq_mul]
  · have e := congrFun (fccVector_eq' true n) i
    rw [e]
    fin_cases i <;> simp [fccFrameQ, qvec, qfactor, Pi.smul_apply, smul_eq_mul] <;> ring

/-- `localArgumentJet` in Cartesian form. -/
theorem localArgumentJet_cart (ref : Reference) (dual : Bool) (n : IntVec) (p : Point) :
    (localArgumentJet ref dual n p).value =
      Real.pi * hessianQuadratic (fun i j => (localMetricJet ref dual p i j).value) (localVector ref dual n) ∧
    (∀ k, (localArgumentJet ref dual n p).gradient k =
      Real.pi * hessianQuadratic (fun i j => (localMetricJet ref dual p i j).gradient k)
        (localVector ref dual n)) ∧
    (∀ k l, (localArgumentJet ref dual n p).hessian k l =
      Real.pi * hessianQuadratic (fun i j => (localMetricJet ref dual p i j).hessian k l)
        (localVector ref dual n)) := by
  have e : localArgumentJet ref dual n p = product (·+·) (·*·) (constant 0 Real.pi)
      ⟨∑ i, ∑ j, (product (·+·) (·*·) (product (·+·) (·*·) (localMetricJet ref dual p i j)
          (constant 0 (localVector ref dual n i))) (constant 0 (localVector ref dual n j))).value,
        fun k => ∑ i, ∑ j, (product (·+·) (·*·) (product (·+·) (·*·) (localMetricJet ref dual p i j)
          (constant 0 (localVector ref dual n i))) (constant 0 (localVector ref dual n j))).gradient k,
        fun k l => ∑ i, ∑ j, (product (·+·) (·*·) (product (·+·) (·*·) (localMetricJet ref dual p i j)
          (constant 0 (localVector ref dual n i))) (constant 0 (localVector ref dual n j))).hessian k l⟩ :=
    rfl
  rw [e]
  refine ⟨?_, fun k => ?_, fun k l => ?_⟩ <;>
    simp [StrainJet.product, StrainJet.constant, hessianQuadratic]

def qscaleBall : Reference → Bool → RootProposal → Ball
  | .bcc, false, r => (Constants.piInput.mul (r.ball.mul r.ball)).mul (Ball.exact (1/4))
  | .bcc, true, r => Constants.piInput.mul (r.ball.mul r.ball).inv
  | .fcc, false, r => Constants.piInput.mul (r.ball.mul r.ball).inv
  | .fcc, true, r => (Constants.piInput.mul (r.ball.mul r.ball)).mul (Ball.exact (1/4))

theorem qscaleBall_sound (ref : Reference) (dual : Bool) (r : RootProposal)
    (hr : cubeRootCheck r (Ball.exact 2) = true) (hinv : (r.ball.mul r.ball).invertible) :
    (qscaleBall ref dual r).Contains (Real.pi * qfactor ref dual ^ 2) := by
  have h : r.ball.Contains Constants.fccLength :=
    cubeRoot_sound r (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) hr
  have sq' := Ball.contains_mul h h
  have quarter : Real.pi * (Constants.fccLength / 2) ^ 2 =
      Real.pi * (Constants.fccLength * Constants.fccLength) * ((1/4 : ℚ) : ℝ) := by push_cast; ring
  have inverse : Real.pi * Constants.fccLength⁻¹ ^ 2 = Real.pi * (Constants.fccLength * Constants.fccLength)⁻¹ := by
    rw [inv_pow, pow_two]
  cases ref <;> cases dual
  · show (qscaleBall .bcc false r).Contains (Real.pi * (Constants.fccLength / 2) ^ 2)
    rw [quarter]
    exact Ball.contains_mul (Ball.contains_mul Constants.piInput_sound sq') (Ball.contains_exact (1/4 : ℚ))
  · show (qscaleBall .bcc true r).Contains (Real.pi * Constants.fccLength⁻¹ ^ 2)
    rw [inverse]
    exact Ball.contains_mul Constants.piInput_sound (Ball.contains_inv hinv sq')
  · show (qscaleBall .fcc false r).Contains (Real.pi * Constants.fccLength⁻¹ ^ 2)
    rw [inverse]
    exact Ball.contains_mul Constants.piInput_sound (Ball.contains_inv hinv sq')
  · show (qscaleBall .fcc true r).Contains (Real.pi * (Constants.fccLength / 2) ^ 2)
    rw [quarter]
    exact Ball.contains_mul (Ball.contains_mul Constants.piInput_sound sq') (Ball.contains_exact (1/4 : ℚ))

/-- The Cartesian argument jet of mode `n` from Cartesian metric jets `M`. -/
def cartArg (ref : Reference) (dual : Bool) (c : FBall) (M : Fin 3 → Fin 3 → FJet) (n : IntVec) : FJet :=
  entrywise (c.mul ·) (fquad M (qvec ref dual n))

theorem cartArg_rel (ref : Reference) (dual : Bool) (p : Point) (c : FBall)
    (hc : c.Contains (Real.pi * qfactor ref dual ^ 2)) (M : Fin 3 → Fin 3 → FJet)
    (hM : ∀ i j, FRel (M i j) (localMetricJet ref dual p i j)) (n : IntVec) :
    FRel (cartArg ref dual c M n) (localArgumentJet ref dual n p) := by
  obtain ⟨ev, eg, eh⟩ := localArgumentJet_cart ref dual n p
  have conv (X : Fin 3 → Fin 3 → ℝ) : Real.pi * hessianQuadratic X (localVector ref dual n) =
      (Real.pi * qfactor ref dual ^ 2) * hessianQuadratic X (castVec (qvec ref dual n)) := by
    simp only [hessianQuadratic, localVector_qvec, castVec, Fin.sum_univ_three]
    ring
  refine ⟨?_, fun k => ?_, fun k l => ?_⟩
  · rw [ev, conv]
    exact FixedPoint.Ball.mul_contains hc (quadBall_contains _ _ (fun i j => (hM i j).1) _)
  · rw [eg k, conv]
    exact FixedPoint.Ball.mul_contains hc (quadBall_contains _ _ (fun i j => (hM i j).2.1 k) _)
  · rw [eh k l, conv]
    exact FixedPoint.Ball.mul_contains hc (quadBall_contains _ _ (fun i j => (hM i j).2.2 k l) _)

/-! ## The index cube as an explicit list -/

def side (r : ℕ) : List ℤ := (List.range (2*r+1)).map (fun i : ℕ => (i : ℤ) - (r : ℤ))

def cubeList (r : ℕ) : List IntVec :=
  (side r).flatMap (fun a => (side r).flatMap (fun b => (side r).map (fun c => ![a,b,c])))

/-- The modes with first index `a`; `cubeList r` is the concatenation of these slabs. -/
def slabList (r : ℕ) (a : ℤ) : List IntVec :=
  (side r).flatMap (fun b => (side r).map (fun c => ![a,b,c]))

theorem cubeList_slabs (r : ℕ) : cubeList r = (side r).flatMap (slabList r) := rfl

theorem mem_side (r : ℕ) (x : ℤ) : x ∈ side r ↔ -(r : ℤ) ≤ x ∧ x ≤ r := by
  simp only [side, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    omega
  · intro h
    exact ⟨(x + r).toNat, List.mem_range.mpr (by omega), by omega⟩

theorem side_nodup (r : ℕ) : (side r).Nodup := by
  unfold side
  refine List.Nodup.map ?_ List.nodup_range
  intro i j h
  have h' : (i : ℤ) - r = (j : ℤ) - r := h
  omega

theorem side_toFinset (r : ℕ) : (side r).toFinset = Finset.Icc (-(r : ℤ)) r := by
  ext x
  simp [mem_side]

theorem sum_Icc_side {M : Type} [AddCommMonoid M] (r : ℕ) (g : ℤ → M) :
    ∑ x ∈ Finset.Icc (-(r : ℤ)) r, g x = ((side r).map g).sum := by
  rw [← side_toFinset, List.sum_toFinset _ (side_nodup r)]

theorem localCube_sum (r : ℕ) {M : Type} [AddCommMonoid M] (f : IntVec → M) :
    ∑ n ∈ localCube r, f n = ((cubeList r).map f).sum := by
  rw [localCube, Finset.sum_map, LatticeTails.cube, Finset.sum_product]
  simp only [Finset.sum_product]
  rw [sum_Icc_side]
  simp only [cubeList, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply]
  rw [sum_Icc_side]
  simp only [List.map_flatten, List.sum_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply]
  rw [sum_Icc_side]
  simp only [List.map_map]
  rfl

theorem mem_cubeList (r : ℕ) (n : IntVec) : n ∈ cubeList r ↔ n ∈ localCube r := by
  rw [mem_localCube]
  simp only [cubeList, List.mem_flatMap, List.mem_map, mem_side]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    simp only [cubeRadius, max_le_iff]
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
  · intro h
    simp only [cubeRadius, max_le_iff] at h
    refine ⟨n 0, by omega, n 1, by omega, n 2, by omega, ?_⟩
    funext i
    fin_cases i <;> rfl

/-! ## Witness choices for the local boxes -/

/-- Chart witness with short dyadic roots. The determinant-root bracket is
recomputed from the exact determinant ball of the box. -/
def shortChart (ref : Reference) (b : Rectangle) : StrainMetricWitness :=
  let s₂ := shortRoot 2 2 2 2 64
  let s₆ := shortRoot 2 6 6 3 64
  let d := detBall (shiftedTensorBall ref b ⟨s₂,s₆,⟨0,0⟩⟩)
  ⟨s₂,s₆,shortRoot 3 (d.lo) (d.hi) (dyadicCeil 8 (1+max |d.lo| |d.hi|)) 80⟩

/-- Cube root of two with 80 bisection steps. -/
def lengthRoot : RootProposal := shortRoot 3 2 2 2 80

end BccSharp.Coulomb.BravaisCover.FixedLocal
