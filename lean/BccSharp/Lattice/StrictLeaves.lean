import BccSharp.Lattice.Energy
import BccSharp.TwoSite.ReferencePacket

set_option autoImplicit false

/-! Strict Lattice one-site leaf evaluator. It uses genuine monotone
kernels and checked enclosures on a closed chart cell. This endpoint
evaluator supplies one E1 route. The mean-value and centered
Taylor routes need their derivative enclosures. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

theorem halfKernel_formula {t : ℝ} (ht : 0 < t) :
    gKernel (1/2) t = Real.sqrt Real.pi*Gaussian.erfcIntegral (Real.sqrt t)/Real.sqrt t := by
  have hs := Real.sqrt_pos.mpr ht
  let g (u : ℝ) := Real.exp (-u^2)
  have h := integral_comp_mul_right_Ioi (E := ℝ) g 1 hs
  simp only [one_mul,smul_eq_mul] at h
  rw [gKernel_half]
  change 2*(∫ y in Set.Ioi (1 : ℝ), Real.exp (-t*y^2)) = _
  have he : (fun y : ℝ => Real.exp (-t*y^2)) = fun y => g (y*Real.sqrt t) := by
    funext y
    unfold g
    rw [mul_pow,Real.sq_sqrt ht.le]
    congr 1
    ring
  simp_rw [he]
  rw [h]
  unfold Gaussian.erfcIntegral g
  field_simp [hs.ne',(Real.sqrt_pos.mpr Real.pi_pos).ne']

theorem halfKernel_decreasing {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    gKernel (1/2) t ≤ gKernel (1/2) s := by
  rw [gKernel_half,gKernel_half]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h (t : ℝ) (h : 0 < t) : IntegrableOn (fun x : ℝ => Real.exp (-t*x^2)) (Set.Ioi 1) :=
    (integrable_exp_neg_mul_sq h).integrableOn
  exact setIntegral_mono_on (h t (hs.trans_le hst)) (h s hs) measurableSet_Ioi
    (fun x _ => Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hst (sq_nonneg x)]))

theorem oneKernel_decreasing {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    gKernel 1 t ≤ gKernel 1 s := by
  rw [gKernel_one (hs.trans_le hst),gKernel_one hs]
  exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hs hst).trans
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hst)) hs.le)

private def latticeScale (c : ℚ) (a : Ball) : Ball := (Ball.exact c).mul a
private theorem latticeScale_sound {c : ℚ} {a : Ball} {x : ℝ} (hx : a.Contains x) :
    (latticeScale c a).Contains ((c : ℝ)*x) := Ball.contains_mul (Ball.contains_exact _) hx

def chartInversesCheck (b : Rectangle) : Bool :=
  decide (0 < b.lo 0 ∧ 0 < b.lo 1 ∧ (coordinateBall b 0).invertible ∧
    (coordinateBall b 1).invertible ∧
    ((coordinateBall b 0).mul (coordinateBall b 1)).invertible)

theorem chartInverses_sound {b : Rectangle} (ok : chartInversesCheck b = true) :
    0 < b.lo 0 ∧ 0 < b.lo 1 ∧ (coordinateBall b 0).invertible ∧
      (coordinateBall b 1).invertible ∧ ((coordinateBall b 0).mul (coordinateBall b 1)).invertible :=
  of_decide_eq_true ok

private theorem chartPos {b : Rectangle} {p : Point} (hb : chartInversesCheck b = true)
    (hp : b.Mem p) : 0 < p 0 ∧ 0 < p 1 := by
  have h := chartInverses_sound hb
  exact ⟨(by exact_mod_cast h.1 : (0 : ℝ) < b.lo 0).trans_le (hp 0).1,
    (by exact_mod_cast h.2.1 : (0 : ℝ) < b.lo 1).trans_le (hp 1).1⟩

def dualVector (p : Point) (n : IntVec) : Vec :=
  ![(p 0)⁻¹*(n 0 : ℝ), (p 1)⁻¹*((n 1 : ℝ)-p 2*(n 0 : ℝ)),
    (p 0*p 1)*((n 2 : ℝ)-p 3*(n 0 : ℝ)+p 4*(p 2*(n 0 : ℝ)-(n 1 : ℝ)))]

theorem dualVector_eq (p : Point) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (n : IntVec) :
    dualVector p n = cycleFrequency (normalizedChart p) n := by
  have hd : (normalizedChart p).det ≠ 0 := by rw [normalizedChart_det p h0 h1]; exact one_ne_zero
  have hU : IsUnit (normalizedChart p).transpose := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hd
  apply Matrix.mulVec_injective_of_isUnit hU
  rw [cycleFrequency_transpose _ hd]
  funext i
  fin_cases i <;> norm_num [normalizedChart,coordLift,chartBasis,dualVector,castVec,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three] <;> field_simp [h0,h1] <;> ring

def dualLengthBall (b : Rectangle) (n : IntVec) : Ball :=
  let r := coordinateBall b 0
  let s := coordinateBall b 1
  let u := latticeScale (n 0 : ℚ) r.inv
  let v := s.inv.mul ((Ball.exact (n 1 : ℚ)).sub (latticeScale (n 0 : ℚ) (coordinateBall b 2)))
  let w := (r.mul s).mul (((Ball.exact (n 2 : ℚ)).sub (latticeScale (n 0 : ℚ) (coordinateBall b 3))).add
    ((coordinateBall b 4).mul ((latticeScale (n 0 : ℚ) (coordinateBall b 2)).sub (Ball.exact (n 1 : ℚ)))))
  (sqBall u).add ((sqBall v).add (sqBall w))

theorem dualLengthBall_sound {b : Rectangle} {p : Point} (hb : chartInversesCheck b = true)
    (hp : b.Mem p) (n : IntVec) : (dualLengthBall b n).Contains (sq (dualVector p n)) := by
  have hi := chartInverses_sound hb
  have r := coordinateBall_sound hp 0
  have s := coordinateBall_sound hp 1
  have x := latticeScale_sound (c := (n 0 : ℚ)) (coordinateBall_sound hp 2)
  have y := latticeScale_sound (c := (n 0 : ℚ)) (coordinateBall_sound hp 3)
  have u := latticeScale_sound (c := (n 0 : ℚ)) (Ball.contains_inv hi.2.2.1 r)
  have v := Ball.contains_mul (Ball.contains_inv hi.2.2.2.1 s)
    (Ball.contains_sub (Ball.contains_exact (n 1 : ℚ)) x)
  have w := Ball.contains_mul (Ball.contains_mul r s)
    (Ball.contains_add (Ball.contains_sub (Ball.contains_exact (n 2 : ℚ)) y)
      (Ball.contains_mul (coordinateBall_sound hp 4) (Ball.contains_sub x (Ball.contains_exact (n 1 : ℚ)))))
  have h := Ball.contains_add (sqBall_sound u) (Ball.contains_add (sqBall_sound v) (sqBall_sound w))
  convert h using 1
  · rfl
  · norm_num [sq,dualVector,Fin.sum_univ_three]
    ring

inductive HalfLower where
  | omit
  | check (witness : ErfcSeriesProposal)

inductive OneLower where
  | omit
  | check (witness : ExpBounds.Witness)

def halfAt (t : ℚ) (w : ErfcSeriesProposal) : Ball :=
  Constants.piInverseRoot.inv.mul ((w.result t Constants.piInverseRoot).mul w.root.ball.inv)

theorem halfAt_sound (t : ℚ) (ht : 0 < (t : ℝ)) (w : ErfcSeriesProposal)
    (rootOK : Constants.piRoot.check Constants.piInput = true) (invOK : Constants.piInverseRoot.invertible)
    (ok : w.check t Constants.piInverseRoot = true) : (halfAt t w).Contains (gKernel (1/2) (t : ℝ)) := by
  have hs := Constants.piInverseRoot_sound rootOK
  have hs' := Ball.contains_inv invOK hs
  have he := ErfcSeriesProposal.sound w t Constants.piInverseRoot hs ok
  have hr := RootProposal.inverse_sound w.root (Ball.exact t) t ht.le (Ball.contains_exact t)
    (Bool.and_eq_true_iff.mp ok).1
  have h := Ball.contains_mul hs' (Ball.contains_mul he hr)
  rw [halfKernel_formula ht]
  simpa [halfAt, div_eq_mul_inv, mul_assoc] using h

def halfLower (q : Ball) : HalfLower → Option ℚ
  | .omit => some 0
  | .check w =>
    let t := (Constants.piInput.mul q).hi
    if decide (0 < t ∧ Constants.piInverseRoot.invertible) &&
        (Constants.piRoot.check Constants.piInput && w.check t Constants.piInverseRoot)
    then some (max 0 (halfAt t w).lo) else none

def oneLower (q : Ball) : OneLower → Option ℚ
  | .omit => some 0
  | .check w =>
    let t := (Constants.piInput.mul q).hi
    if decide (0 < t) && w.check (Ball.exact (-t)) then
      some (max 0 (w.result.lo/t)) else none

theorem halfLower_sound {q : Ball} {x : ℝ} (hx : q.Contains x) (hx0 : 0 < x)
    (w : HalfLower) (l : ℚ) (ok : halfLower q w = some l) :
    (l : ℝ) ≤ gKernel (1/2) (Real.pi*x) := by
  have hpx := mul_pos Real.pi_pos hx0
  have hn : 0 ≤ gKernel (1/2) (Real.pi*x) := by
    rw [halfKernel_formula hpx]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Ewald.erfc_nonneg _)) (Real.sqrt_nonneg _)
  cases w with
  | «omit» =>
    have hl : l=0 := (Option.some.inj ok).symm
    simpa [hl] using hn
  | check w =>
    let t := (Constants.piInput.mul q).hi
    have htx : Real.pi*x ≤ (t : ℝ) := by
      simpa [t,Ball.hi] using ((SpecialFunctions.contains_iff_endpoints _ _).mp
        (Ball.contains_mul Constants.piInput_sound hx)).2
    simp only [halfLower] at ok
    split_ifs at ok with ht
    have hs := Bool.and_eq_true_iff.mp ht
    have h := Bool.and_eq_true_iff.mp hs.2
    have hi : 0 < t ∧ Constants.piInverseRoot.invertible := of_decide_eq_true hs.1
    have hv := halfAt_sound t (hpx.trans_le htx) w h.1 hi.2 h.2
    have hv' : ((halfAt t w).lo : ℝ) ≤ gKernel (1/2) (Real.pi*x) := by
      have hh := ((SpecialFunctions.contains_iff_endpoints _ _).mp hv).1
      exact (by simpa [Ball.lo] using hh : ((halfAt t w).lo : ℝ) ≤ gKernel (1/2) (t : ℝ)).trans
        (halfKernel_decreasing hpx htx)
    rw [← Option.some.inj ok]
    exact_mod_cast (max_le hn hv')

theorem oneLower_sound {q : Ball} {x : ℝ} (hx : q.Contains x) (hx0 : 0 < x)
    (w : OneLower) (l : ℚ) (ok : oneLower q w = some l) :
    (l : ℝ) ≤ gKernel 1 (Real.pi*x) := by
  have hpx := mul_pos Real.pi_pos hx0
  have hn : 0 ≤ gKernel 1 (Real.pi*x) := by rw [gKernel_one hpx]; positivity
  cases w with
  | «omit» =>
    have hl : l=0 := (Option.some.inj ok).symm
    simpa [hl] using hn
  | check w =>
    let t := (Constants.piInput.mul q).hi
    have htx : Real.pi*x ≤ (t : ℝ) := by
      simpa [t,Ball.hi] using ((SpecialFunctions.contains_iff_endpoints _ _).mp
        (Ball.contains_mul Constants.piInput_sound hx)).2
    simp only [oneLower] at ok
    split_ifs at ok with ht
    have ht' := (Bool.and_eq_true_iff.mp ht).2
    have he := ExpBounds.Witness.sound ht' (Ball.contains_exact (-t))
    have hl : (w.result.lo : ℝ) ≤ Real.exp (-(t : ℝ)) := by
      simpa [Ball.lo] using ((SpecialFunctions.contains_iff_endpoints _ _).mp he).1
    have he' := (div_le_div_of_nonneg_right hl (hpx.trans_le htx).le).trans_eq
      (gKernel_one (hpx.trans_le htx)).symm
    have hb := he'.trans (oneKernel_decreasing hpx htx)
    rw [← Option.some.inj ok]
    exact_mod_cast (max_le hn hb)

/-- Each retained integer index must occur only once. Skipping a kernel
term gives zero; a failed requested enclosure rejects the whole witness. -/
structure SeriesTerm where
  index : IntVec
  direct : HalfLower
  dual : OneLower

def evaluateTerm (b : Rectangle) (w : SeriesTerm) : Option ℚ := do
  if w.index = 0 then none else
    let a ← halfLower (firstBall b w.index) w.direct
    let d ← oneLower (dualLengthBall b w.index) w.dual
    pure (a+d)

def evaluateTermList (eval : SeriesTerm → Option ℚ) : List SeriesTerm → Option ℚ
  | [] => some 0
  | w :: later => do
    let a ← eval w
    let d ← evaluateTermList eval later
    pure (a+d)

def evaluateSeries (b : Rectangle) (terms : List SeriesTerm) : Option ℚ :=
  evaluateTermList (evaluateTerm b) terms

def strictSeriesCheck (b : Rectangle) (terms : List SeriesTerm) : Bool :=
  (chartInversesCheck b && decide ((terms.map SeriesTerm.index).Nodup)) &&
    match evaluateSeries b terms with
    | some v => decide (HfccUpper < v)
    | none => false

private theorem evaluateTerm_sound (b : Rectangle) (p : Point) (hb : chartInversesCheck b = true)
    (hp : b.Mem p) (w : SeriesTerm) (v : ℚ) (ok : evaluateTerm b w = some v) :
    (v : ℝ) ≤ shortKernel (normalizedChart p) w.index+dualKernel (normalizedChart p) w.index := by
  have h := chartPos hb hp
  let R := normalizedChart p
  have hd : R.det ≠ 0 := by rw [normalizedChart_det p h.1.ne' h.2.ne']; exact one_ne_zero
  unfold evaluateTerm at ok
  split_ifs at ok with hn
  cases e : halfLower (firstBall b w.index) w.direct with
  | none => simp [e] at ok
  | some a =>
    cases f : oneLower (dualLengthBall b w.index) w.dual with
    | none => simp [e,f] at ok
    | some d =>
      have hsum : v=a+d := by simpa [e,f,eq_comm] using ok
      have hf := firstBall_sound hp (chartInverses_sound hb).2.2.2.2 w.index
      have hi : linearImage R w.index ≠ 0 := by
        intro hz
        apply hn
        apply (periodIndices R hd).injective
        apply Subtype.ext
        change linearImage R w.index=linearImage R 0
        rw [hz, linearImage, castVec_zero, Matrix.mulVec_zero]
      have hpos (x : Vec) (hx : x ≠ 0) : 0 < sq x :=
        lt_of_le_of_ne (sq_nonnegative _) (Ne.symm (mt (sq_eq_zero_iff _).mp hx))
      have hf' : (firstBall b w.index).Contains (sq (linearImage R w.index)) := by
        simpa [firstLength_eq,R,normalizedChart,linearImage] using hf
      have hc : cycleFrequency R w.index ≠ 0 := fun z =>
        hn (cycleFrequency_injective R hd (z.trans (cycleFrequency_zero R).symm))
      have hd' := dualLengthBall_sound hb hp w.index
      rw [dualVector_eq p h.1.ne' h.2.ne'] at hd'
      rw [hsum,Rat.cast_add,shortKernel_eq _ hd _ hn,dualKernel_eq _ hd _ hn]
      exact add_le_add (halfLower_sound hf' (hpos _ hi) _ _ e) (oneLower_sound hd' (hpos _ hc) _ _ f)

theorem evaluateTermList_sound (eval : SeriesTerm → Option ℚ) (value : IntVec → ℝ)
    (correct : ∀ t u, eval t=some u → (u : ℝ)≤value t.index)
    (terms : List SeriesTerm) (nd : (terms.map SeriesTerm.index).Nodup)
    (v : ℚ) (ev : evaluateTermList eval terms = some v) :
    (v : ℝ) ≤ ∑ n ∈ (terms.map SeriesTerm.index).toFinset,value n := by
  classical
  induction terms generalizing v with
  | nil =>
    have e : v=0 := (Option.some.inj ev).symm
    simp [e]
  | cons t ts ih =>
    have ht := List.nodup_cons.mp nd
    cases e : eval t with
    | none => simp [evaluateTermList,e] at ev
    | some u =>
      cases f : evaluateTermList eval ts with
      | none => simp [evaluateTermList,e,f] at ev
      | some w =>
        have he : v=u+w := by simpa [evaluateTermList,e,f,eq_comm] using ev
        rw [he,Rat.cast_add,List.map_cons,List.toFinset_cons,Finset.sum_insert]
        · exact add_le_add (correct t u e) (ih ht.2 w f)
        · simpa using ht.1

theorem strictSeriesCheck_sound (b : Rectangle) (terms : List SeriesTerm) (ok : strictSeriesCheck b terms = true)
    (p : Point) (hp : b.Mem p) : Sharp (primitiveChart p) := by
  classical
  have h := Bool.and_eq_true_iff.mp ok
  have h0 := Bool.and_eq_true_iff.mp h.1
  have nd : (terms.map SeriesTerm.index).Nodup := of_decide_eq_true h0.2
  obtain ⟨v,ev,hv⟩ : ∃ v, evaluateSeries b terms = some v ∧ HfccUpper < v := by
    cases e : evaluateSeries b terms with
    | none => simp [e] at h
    | some v => exact ⟨v,rfl,of_decide_eq_true (by simpa [e] using h.2)⟩
  have bounds := evaluateTermList_sound (evaluateTerm b)
    (fun n => shortKernel (normalizedChart p) n+dualKernel (normalizedChart p) n)
    (evaluateTerm_sound b p h0.1 hp) terms nd v ev
  have hp0 := chartPos h0.1 hp
  have hd : (normalizedChart p).det ≠ 0 := by rw [normalizedChart_det p hp0.1.ne' hp0.2.ne']; exact one_ne_zero
  apply chart_above_fcc_of_series p hp0.1.ne' hp0.2.ne'
  exact (by exact_mod_cast hv : (HfccUpper : ℝ) < (v : ℝ)).trans_le
    (bounds.trans (positiveSeries_finite_lower _ hd _))

def automaticErfc (t : ℚ) : ErfcSeriesProposal :=
  let root := Constants.rootPair 2 t t 16
  let order := if t ≤ 4 then 128 else 256
  ⟨root,order,4*(root.ball.mid+root.ball.rad)*(Constants.piInverseRoot.mid+ Constants.piInverseRoot.rad) *
    t^order/(order.factorial : ℚ)⟩

def automaticKernelTerm (n : IntVec) (shortQ dualQ : Ball) : SeriesTerm :=
  let r := (Constants.piInput.mul shortQ).hi
  let t := (Constants.piInput.mul dualQ).hi
  ⟨n, if 0 < r ∧ r ≤ 64 then .check (automaticErfc r) else .omit,
    if 0 < t ∧ t ≤ 128 then .check (Constants.expProposal (Ball.exact (-t))) else .omit⟩

def cubeIndices (radius : ℕ) : List IntVec :=
  let side := (List.range (2*radius+1)).map (fun i => (i : ℤ)-(radius : ℤ))
  side.flatMap (fun i => side.flatMap (fun j => side.filterMap (fun k =>
    if (i,j,k) = (0,0,0) then none else some ![i,j,k])))

def automaticSeries (b : Rectangle) (radius : ℕ) : List SeriesTerm :=
  (cubeIndices radius).map (fun n => automaticKernelTerm n (firstBall b n) (dualLengthBall b n))

def strictRadiusCheck (b : Rectangle) (radius : ℕ) : Bool :=
  decide (0 < radius ∧ radius ≤ 6) && strictSeriesCheck b (automaticSeries b radius)

theorem strictRadiusCheck_sound (b : Rectangle) (radius : ℕ) (ok : strictRadiusCheck b radius = true)
    (p : Point) (hp : b.Mem p) : Sharp (primitiveChart p) :=
  strictSeriesCheck_sound b _ (Bool.and_eq_true_iff.mp ok).2 p hp

end BccSharp.Coulomb.BravaisCover
