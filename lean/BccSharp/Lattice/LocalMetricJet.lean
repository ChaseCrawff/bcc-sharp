import BccSharp.Lattice.SecondJet

set_option autoImplicit false

/-! Normalization by the actual determinant, including the inverse
metric and the signed defect penalty. The same algebraic expression is
used for the real derivatives and their rational enclosure. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision
open StrainJet

private structure JetArithmetic (α : Type) where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α

private def tensorFormula {α : Type} (o : JetArithmetic α) (a b x y z : α) (twiceNegative : α) : Fin 3 → Fin 3 → α :=
  ![![o.add a b,x,y],![x,o.sub b a,z],![y,z,o.mul twiceNegative b]]

private def detFormula {α : Type} (o : JetArithmetic α) (M : Fin 3 → Fin 3 → α) : α :=
  let a := o.mul (M 0 0) (o.sub (o.mul (M 1 1) (M 2 2)) (o.mul (M 1 2) (M 2 1)))
  let b := o.mul (M 0 1) (o.sub (o.mul (M 1 0) (M 2 2)) (o.mul (M 1 2) (M 2 0)))
  let c := o.mul (M 0 2) (o.sub (o.mul (M 1 0) (M 2 1)) (o.mul (M 1 1) (M 2 0)))
  o.add (o.sub a b) c

private def adjFormula {α : Type} (o : JetArithmetic α) (M : Fin 3 → Fin 3 → α) (i j : Fin 3) : α :=
  o.sub (o.mul (M (j+1) (i+1)) (M (j+2) (i+2))) (o.mul (M (j+1) (i+2)) (M (j+2) (i+1)))

private def strainFormula {α : Type} (o : JetArithmetic α) (rat : ℚ → α) (coord : Fin 5 → α)
    (is₂ is₆ : α) (ref : Reference) (i j : Fin 3) : α :=
  let c (k : Fin 5) (f : ℚ) (s : α) := o.mul (o.mul (rat f) (coord k)) s
  let S := tensorFormula o (c 0 (whitenE ref) is₂) (c 1 (whitenE ref) is₆)
    (c 2 (whitenT ref) is₂) (c 3 (whitenT ref) is₂) (c 4 (whitenT ref) is₂) (rat (-2))
  o.add (rat (if i=j then 1 else 0)) (S i j)

private def realArith : JetArithmetic (StrainJet ℝ) where
  add := combine (·+·)
  sub a b := combine (·+·) a (entrywise Neg.neg b)
  mul := product (·+·) (·*·)

private def ballArith : JetArithmetic (StrainJet Ball) where
  add := combine Ball.add
  sub := combine Ball.sub
  mul := product Ball.add Ball.mul

private theorem sub_rel {a b : StrainJet ℝ} {A B : StrainJet Ball} (ha : Rel A a) (hb : Rel B b) :
    Rel (ballArith.sub A B) (realArith.sub a b) :=
  ⟨by simpa only [ballArith, realArith, combine, entrywise, sub_eq_add_neg] using Ball.contains_sub ha.1 hb.1,
   fun i => by simpa only [ballArith, realArith, combine, entrywise, sub_eq_add_neg] using
      Ball.contains_sub (ha.2.1 i) (hb.2.1 i),
   fun i j => by simpa only [ballArith, realArith, combine, entrywise, sub_eq_add_neg] using
      Ball.contains_sub (ha.2.2 i j) (hb.2.2 i j)⟩

private theorem contains_exact_zero : (Ball.exact 0).Contains (0 : ℝ) := by
  simp [Ball.Contains, Ball.exact]

private theorem contains_exact_one : (Ball.exact 1).Contains (1 : ℝ) := by
  simp [Ball.Contains, Ball.exact]

private theorem contains_exact_ite (c : Prop) [Decidable c] :
    (Ball.exact (if c then 1 else 0)).Contains (if c then (1 : ℝ) else 0) := by
  split_ifs
  · exact contains_exact_one
  · exact contains_exact_zero

private theorem const_rel {r : ℝ} {B : Ball} (h : B.Contains r) :
    Rel (constant (Ball.exact 0) B) (constant 0 r) :=
  ⟨h,fun _ => contains_exact_zero,fun _ _ => contains_exact_zero⟩

private theorem coord_rel (b : Rectangle) (p : Point) (hp : b.Mem p) (i : Fin 5) :
    Rel (coordinate (Ball.exact 0) (Ball.exact 1) (coordinateBall b i) i) (coordinate 0 1 (p i) i) := by
  refine ⟨coordinateBall_sound hp i, ?_, fun _ _ => contains_exact_zero⟩
  intro j
  by_cases h : j=i
  · simp only [coordinate, h, if_true]; exact contains_exact_one
  · simp only [coordinate, h, if_false]; exact contains_exact_zero

private def shiftedReal (ref : Reference) (p : Point) :=
  strainFormula realArith (fun q => constant 0 (q : ℝ)) (fun i => coordinate 0 1 (p i) i)
    (constant 0 (Real.sqrt 2)⁻¹) (constant 0 (Real.sqrt 6)⁻¹) ref

private def shiftedInterval (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) :=
  strainFormula ballArith (fun q => constant (Ball.exact 0) (Ball.exact q))
    (fun i => coordinate (Ball.exact 0) (Ball.exact 1) (coordinateBall b i) i)
    (constant (Ball.exact 0) w.sqrt₂.ball.inv) (constant (Ball.exact 0) w.sqrt₆.ball.inv) ref

private theorem shiftedReal_value (ref : Reference) (p : Point) (i j : Fin 3) :
    (shiftedReal ref p i j).value = (1+strainTensor ref p) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [shiftedReal, strainFormula, tensorFormula, strainTensor, realArith,
      combine, product, constant, coordinate, entrywise, Matrix.add_apply, Matrix.one_apply, div_eq_mul_inv] <;> ring

private theorem shiftedInterval_value (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) (i j : Fin 3) :
    (shiftedInterval ref b w i j).value = shiftedTensorBall ref b w i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem tensor_rel {A B X Y Z T : StrainJet Ball} {a b x y z t : StrainJet ℝ}
    (hA : Rel A a) (hB : Rel B b) (hX : Rel X x) (hY : Rel Y y) (hZ : Rel Z z) (hT : Rel T t)
    (i j : Fin 3) :
    Rel (tensorFormula ballArith A B X Y Z T i j) (tensorFormula realArith a b x y z t i j) := by
  fin_cases i <;> fin_cases j
  · exact add_rel hA hB
  · exact hX
  · exact hY
  · exact hX
  · exact sub_rel hB hA
  · exact hZ
  · exact hY
  · exact hZ
  · exact product_rel hT hB

private theorem tensor_derivatives {b : Rectangle} {A B X Y Z T : RealField}
    (hA : RayDerivatives b A) (hB : RayDerivatives b B) (hX : RayDerivatives b X)
    (hY : RayDerivatives b Y) (hZ : RayDerivatives b Z) (hT : RayDerivatives b T) (i j : Fin 3) :
    RayDerivatives b (fun p => tensorFormula realArith (A p) (B p) (X p) (Y p) (Z p) (T p) i j) := by
  fin_cases i <;> fin_cases j
  · exact add_derivatives hA hB
  · exact hX
  · exact hY
  · exact hX
  · exact add_derivatives hB (neg_derivatives hA)
  · exact hZ
  · exact hY
  · exact hZ
  · exact product_derivatives hT hB

private theorem shifted_rel (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (h₂ : w.sqrt₂.check (Ball.exact 2)=true) (h₆ : w.sqrt₆.check (Ball.exact 6)=true)
    (p : Point) (hp : b.Mem p) (i j : Fin 3) : Rel (shiftedInterval ref b w i j) (shiftedReal ref p i j) := by
  have s₂ := const_rel (RootProposal.inverse_sound w.sqrt₂ (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) h₂)
  have s₆ := const_rel (RootProposal.inverse_sound w.sqrt₆ (Ball.exact 6) 6 (by norm_num) (Ball.contains_exact 6) h₆)
  have c₂ k f := product_rel (product_rel (const_rel (Ball.contains_exact f)) (coord_rel b p hp k)) s₂
  have c₆ k f := product_rel (product_rel (const_rel (Ball.contains_exact f)) (coord_rel b p hp k)) s₆
  exact add_rel (const_rel (Ball.contains_exact (if i=j then 1 else 0)))
    (tensor_rel (c₂ 0 (whitenE ref)) (c₆ 1 (whitenE ref)) (c₂ 2 (whitenT ref)) (c₂ 3 (whitenT ref))
      (c₂ 4 (whitenT ref)) (const_rel (Ball.contains_exact (-2))) i j)

private theorem shifted_derivatives (ref : Reference) (b : Rectangle) (i j : Fin 3) :
    RayDerivatives b (fun p => shiftedReal ref p i j) := by
  have c k (r : ℚ) (s : ℝ) := product_derivatives
    (product_derivatives (constant_derivatives b (r : ℝ)) (coordinate_derivatives b k))
    (constant_derivatives b s)
  exact add_derivatives (constant_derivatives b (((if i=j then 1 else 0 : ℚ)) : ℝ))
    (tensor_derivatives (c 0 (whitenE ref) (Real.sqrt 2)⁻¹) (c 1 (whitenE ref) (Real.sqrt 6)⁻¹)
      (c 2 (whitenT ref) (Real.sqrt 2)⁻¹) (c 3 (whitenT ref) (Real.sqrt 2)⁻¹)
      (c 4 (whitenT ref) (Real.sqrt 2)⁻¹) (constant_derivatives b ((-2 : ℚ) : ℝ)) i j)

private theorem det_rel {A : Fin 3 → Fin 3 → StrainJet Ball} {M : Fin 3 → Fin 3 → StrainJet ℝ}
    (h : ∀ i j, Rel (A i j) (M i j)) : Rel (detFormula ballArith A) (detFormula realArith M) :=
  add_rel (sub_rel (product_rel (h 0 0) (sub_rel (product_rel (h 1 1) (h 2 2)) (product_rel (h 1 2) (h 2 1))))
    (product_rel (h 0 1) (sub_rel (product_rel (h 1 0) (h 2 2)) (product_rel (h 1 2) (h 2 0)))))
    (product_rel (h 0 2) (sub_rel (product_rel (h 1 0) (h 2 1)) (product_rel (h 1 1) (h 2 0))))

private theorem det_derivatives {b : Rectangle} {M : Fin 3 → Fin 3 → Point → StrainJet ℝ}
    (h : ∀ i j, RayDerivatives b (M i j)) : RayDerivatives b (fun p => detFormula realArith (fun i j => M i j p)) := by
  have d (c i j k l x y u v : Fin 3) := product_derivatives (h 0 c)
    (add_derivatives (product_derivatives (h i j) (h k l)) (neg_derivatives (product_derivatives (h x y) (h u v))))
  exact add_derivatives (add_derivatives (d 0 1 1 2 2 1 2 2 1) (neg_derivatives (d 1 1 0 2 2 1 2 2 0)))
    (d 2 1 0 2 1 1 1 2 0)

def localMetricJet (ref : Reference) (dual : Bool) (p : Point) (i j : Fin 3) : StrainJet ℝ :=
  let J := shiftedReal ref p
  let d := detFormula realArith J
  let r := realRoot d
  if dual then realArith.mul (realArith.mul r (realInverse d)) (adjFormula realArith J i j)
  else realArith.mul (realInverse r) (J i j)

def localMetricJetBall (ref : Reference) (dual : Bool) (b : Rectangle) (w : StrainMetricWitness)
    (i j : Fin 3) : StrainJet Ball :=
  let J := shiftedInterval ref b w
  let d := detFormula ballArith J
  let r := intervalRoot w.determinantRoot d
  if dual then ballArith.mul (ballArith.mul r (intervalInverse d)) (adjFormula ballArith J i j)
  else ballArith.mul (intervalInverse r) (J i j)

theorem localMetricJets_sound (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (ok : strainMetricCheck ref b w=true) (dual : Bool) (i j : Fin 3) :
    Encloses b (localMetricJetBall ref dual b w i j) (fun p => localMetricJet ref dual p i j) ∧
    RayDerivatives b (fun p => localMetricJet ref dual p i j) ∧
    ∀ p, b.Mem p → (localMetricJet ref dual p i j).value =
      (if dual then (reconstructedMetric ref p)⁻¹ else reconstructedMetric ref p) i j := by
  obtain ⟨hs,hd⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨h₂,h₆⟩ := Bool.and_eq_true_iff.mp hs
  obtain ⟨hp,hr⟩ := Bool.and_eq_true_iff.mp hd
  obtain ⟨dp,di⟩ := Bool.and_eq_true_iff.mp hp
  let Db := detFormula ballArith (shiftedInterval ref b w)
  let D (p : Point) := detFormula realArith (shiftedReal ref p)
  have evalBall : Db.value=detBall (shiftedTensorBall ref b w) := by
    simp only [Db, detFormula, ballArith, combine, product, shiftedInterval_value, detBall]
  have evalReal (p : Point) : (D p).value=(1+strainTensor ref p).det := by
    simp only [D, detFormula, realArith, combine, product, entrywise, shiftedReal_value, Matrix.det_fin_three]
    ring
  have dpos : Db.value.positive=true := by rw [evalBall]; exact dp
  have dinv : Db.value.invertible := by rw [evalBall]; exact of_decide_eq_true di
  have rootOK : cubeRootCheck w.determinantRoot Db.value=true := by rw [evalBall]; exact hr
  have RootInv : (intervalRoot w.determinantRoot Db).value.invertible := cubeRoot_invertible _ _ rootOK
  have bound (p : Point) (hm : b.Mem p) : Rel Db (D p) := det_rel (shifted_rel ref b w h₂ h₆ p hm)
  have P (p : Point) (hm : b.Mem p) : 0<(D p).value := Ball.positive_sound dpos (bound p hm).1
  refine ⟨?_, ?_, ?_⟩
  · intro p hm
    have hJ := shifted_rel ref b w h₂ h₆ p hm
    have hD := bound p hm
    have hR := root_rel hD w.determinantRoot dpos dinv rootOK
    cases dual
    · exact product_rel (inverse_rel hR RootInv) (hJ i j)
    · exact product_rel (product_rel hR (inverse_rel hD dinv))
        (sub_rel (product_rel (hJ _ _) (hJ _ _)) (product_rel (hJ _ _) (hJ _ _)))
  · have hJ := shifted_derivatives ref b
    have hD : RayDerivatives b D := det_derivatives hJ
    have hR := root_derivatives hD P
    cases dual
    · exact product_derivatives (inverse_derivatives hR (fun p hm => (Real.rpow_pos_of_pos (P p hm) _).ne')) (hJ i j)
    · exact product_derivatives (product_derivatives hR (inverse_derivatives hD (fun p hm => (P p hm).ne')))
        (add_derivatives (product_derivatives (hJ _ _) (hJ _ _))
          (neg_derivatives (product_derivatives (hJ _ _) (hJ _ _))))
  · intro p hm
    let J : Mat := 1+strainTensor ref p
    let r : ℝ := J.det^(1/3 : ℝ)
    have detPos : 0 < J.det := by rw [← evalReal p]; exact P p hm
    have rp : 0 < r := Real.rpow_pos_of_pos detPos _
    have e : reconstructedMetric ref p = r⁻¹ • J := by
      show (J.det ^ (-(1/3) : ℝ)) • J = r⁻¹ • J
      rw [Real.rpow_neg detPos.le]
    have inv : (reconstructedMetric ref p)⁻¹ = (r*J.det⁻¹) • cyclicAdj J := by
      apply Matrix.inv_eq_right_inv
      rw [e,smul_mul_assoc,mul_smul_comm,cyclicAdj_right,smul_smul,smul_smul]
      have s : r⁻¹*(r*J.det⁻¹*J.det)=1 := by field_simp [rp.ne',detPos.ne']
      first | rw [s, one_smul] | rw [mul_assoc, s, one_smul]
    cases dual
    · simp only [localMetricJet, Bool.false_eq_true, if_false, realArith, product, realInverse, inverse, chain]
      change ((D p).value^(1/3 : ℝ))⁻¹*(shiftedReal ref p i j).value = _
      rw [evalReal, shiftedReal_value, e]
      rfl
    · simp only [localMetricJet, if_true, realArith, product, realInverse, inverse, realRoot, cubeRoot, chain,
        adjFormula, combine, entrywise, shiftedReal_value]
      change ((D p).value^(1/3 : ℝ) * (D p).value⁻¹) * (J (j+1) (i+1) * J (j+2) (i+2) +
        -(J (j+1) (i+2) * J (j+2) (i+1))) = _
      rw [evalReal, inv]
      simp only [cyclicAdj, r, J, Matrix.smul_apply, smul_eq_mul, sub_eq_add_neg]

private def realSum {ι : Type} (s : Finset ι) (J : ι → StrainJet ℝ) : StrainJet ℝ :=
  ⟨∑ i ∈ s, (J i).value, fun j => ∑ i ∈ s, (J i).gradient j, fun j k => ∑ i ∈ s, (J i).hessian j k⟩

private def ballSum {ι : Type} (s : Finset ι) (J : ι → StrainJet Ball) : StrainJet Ball :=
  ⟨Constants.sumBalls s (fun i => (J i).value), fun j => Constants.sumBalls s (fun i => (J i).gradient j),
    fun j k => Constants.sumBalls s (fun i => (J i).hessian j k)⟩

private theorem sum_rel {ι : Type} (s : Finset ι) {R : ι → StrainJet ℝ} {B : ι → StrainJet Ball}
    (h : ∀ i ∈ s, Rel (B i) (R i)) : Rel (ballSum s B) (realSum s R) :=
  ⟨Constants.sumBalls_sound _ _ _ (fun i hi => (h i hi).1),
    fun j => Constants.sumBalls_sound _ _ _ (fun i hi => (h i hi).2.1 j),
    fun j k => Constants.sumBalls_sound _ _ _ (fun i hi => (h i hi).2.2 j k)⟩

private theorem sum_derivatives {ι : Type} (s : Finset ι) {b : Rectangle} {F : ι → RealField}
    (h : ∀ i ∈ s, RayDerivatives b (F i)) : RayDerivatives b (fun p => realSum s (fun i => F i p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [realSum, constant] using constant_derivatives b 0
  | @insert i s hi ih =>
    simpa only [realSum, Finset.sum_insert hi, combine] using
      add_derivatives (h i (Finset.mem_insert_self _ _)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def localVector (ref : Reference) (dual : Bool) (n : IntVec) : Vec :=
  if dual then cycleFrequency (cubicBasis ref) n else linearImage (cubicBasis ref) n

def localArgument (ref : Reference) (dual : Bool) (n : IntVec) (p : Point) : ℝ :=
  Real.pi*quad (if dual then (reconstructedMetric ref p)⁻¹ else reconstructedMetric ref p)
    (localVector ref dual n)

def localArgumentJet (ref : Reference) (dual : Bool) (n : IntVec) (p : Point) : StrainJet ℝ :=
  let u := localVector ref dual n
  realArith.mul (constant 0 Real.pi) (realSum Finset.univ fun i => realSum Finset.univ fun j =>
    realArith.mul (realArith.mul (localMetricJet ref dual p i j) (constant 0 (u i))) (constant 0 (u j)))

def localArgumentJetBall (ref : Reference) (dual : Bool) (u : Fin 3 → Ball)
    (b : Rectangle) (w : StrainMetricWitness) : StrainJet Ball :=
  ballArith.mul (constant (Ball.exact 0) Constants.piInput)
    (ballSum Finset.univ fun i => ballSum Finset.univ fun j =>
      ballArith.mul (ballArith.mul (localMetricJetBall ref dual b w i j) (constant (Ball.exact 0) (u i)))
        (constant (Ball.exact 0) (u j)))

theorem localArgumentJet_derivatives (ref : Reference) (dual : Bool) (n : IntVec) (b : Rectangle)
    (w : StrainMetricWitness) (ok : strainMetricCheck ref b w=true) :
    RayDerivatives b (localArgumentJet ref dual n) ∧
    ∀ p, b.Mem p → (localArgumentJet ref dual n p).value = localArgument ref dual n p := by
  have h := localMetricJets_sound ref b w ok dual
  constructor
  · apply product_derivatives (constant_derivatives b Real.pi)
    exact sum_derivatives _ (fun i _ => sum_derivatives _ (fun j _ =>
      product_derivatives (product_derivatives (h i j).2.1 (constant_derivatives _ _)) (constant_derivatives _ _)))
  · intro p hp
    rw [localArgument, ← hessianQuadratic_eq_quad]
    simp only [localArgumentJet, realArith, product, constant, realSum, hessianQuadratic, (h _ _).2.2 p hp]

theorem localArgumentJet_rel (ref : Reference) (dual : Bool) (n : IntVec) (b : Rectangle)
    (w : StrainMetricWitness) (ok : strainMetricCheck ref b w=true)
    (u : Fin 3 → Ball) (hu : ∀ i, (u i).Contains (localVector ref dual n i)) :
    Encloses b (localArgumentJetBall ref dual u b w) (localArgumentJet ref dual n) := by
  intro p hp
  apply product_rel (const_rel Constants.piInput_sound)
  exact sum_rel _ (fun i _ => sum_rel _ (fun j _ => product_rel
    (product_rel ((localMetricJets_sound ref b w ok dual i j).1 p hp) (const_rel (hu i))) (const_rel (hu j))))

def localPenaltyJet (ref : Reference) (p : Point) : StrainJet ℝ :=
  let d (i j : Fin 3) := realArith.sub (localMetricJet ref false p i j) (constant 0 (if i=j then 1 else 0))
  realArith.mul (constant 0 (localPenalty ref : ℝ))
    (realSum Finset.univ fun i => realSum Finset.univ fun j => realArith.mul (d i j) (d i j))

def localPenaltyJetBall (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : StrainJet Ball :=
  let d (i j : Fin 3) := ballArith.sub (localMetricJetBall ref false b w i j)
    (constant (Ball.exact 0) (Ball.exact (if i=j then 1 else 0)))
  ballArith.mul (constant (Ball.exact 0) (Ball.exact (localPenalty ref)))
    (ballSum Finset.univ fun i => ballSum Finset.univ fun j => ballArith.mul (d i j) (d i j))

theorem localPenaltyJet_sound (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (ok : strainMetricCheck ref b w=true) :
    Encloses b (localPenaltyJetBall ref b w) (localPenaltyJet ref) ∧
    RayDerivatives b (localPenaltyJet ref) ∧ ∀ p, b.Mem p →
      (localPenaltyJet ref p).value = (localPenalty ref : ℝ)*frobSq (reconstructedMetric ref p-1) := by
  have h := localMetricJets_sound ref b w ok false
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    apply product_rel (const_rel (Ball.contains_exact (localPenalty ref)))
    refine sum_rel _ (fun i _ => sum_rel _ (fun j _ => ?_))
    have s := sub_rel ((h i j).1 p hp) (const_rel (contains_exact_ite (i=j)))
    exact product_rel s s
  · apply product_derivatives (constant_derivatives _ _)
    refine sum_derivatives _ (fun i _ => sum_derivatives _ (fun j _ => ?_))
    have s := add_derivatives (h i j).2.1 (neg_derivatives (constant_derivatives b (if i=j then 1 else 0)))
    exact product_derivatives s s
  · intro p hp
    simp only [localPenaltyJet, realArith, realSum, product, constant, combine, entrywise,
      (h _ _).2.2 p hp, Bool.false_eq_true, if_false, frobSq, Matrix.sub_apply, Matrix.one_apply, pow_two, sub_eq_add_neg]

def fccFrameQ (dual : Bool) (n : IntVec) : Fin 3 → ℚ :=
  let a := (n 0 : ℚ)
  let b := (n 1 : ℚ)
  let c := (n 2 : ℚ)
  if dual then ![(a+b-c)/2,(a-b+c)/2,(-a+b+c)/2] else ![a+b,a+c,b+c]

def localVectorBall (ref : Reference) (dual : Bool) (r : RootProposal) (n : IntVec) : Fin 3 → Ball :=
  match ref, dual with
  | .bcc, false => directVectorBall r n
  | .bcc, true => reciprocalVectorBall r n
  | .fcc, false => fun i => r.ball.inv.mul (Ball.exact (fccFrameQ false n i))
  | .fcc, true => fun i => r.ball.mul (Ball.exact (fccFrameQ true n i))

private theorem fccVector_eq (dual : Bool) (n : IntVec) :
    localVector .fcc dual n = (if dual then Constants.fccLength else Constants.fccLength⁻¹) •
      (fun i => (fccFrameQ dual n i : ℝ)) := by
  cases dual
  · ext i
    fin_cases i <;> norm_num [localVector, cubicBasis, linearImage, Matrix.mulVec, dotProduct,
      fccFrameQ, castVec, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;> push_cast <;> ring
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

theorem localVectorBall_sound (ref : Reference) (dual : Bool) (r : RootProposal)
    (hr : cubeRootCheck r (Ball.exact 2)=true) (n : IntVec) (i : Fin 3) :
    (localVectorBall ref dual r n i).Contains (localVector ref dual n i) := by
  cases ref
  · cases dual
    · exact directVectorBall_sound r hr n i
    · exact reciprocalVectorBall_sound r hr n i
  · have h := cubeRoot_sound r (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) hr
    have hi := Ball.contains_inv (cubeRoot_invertible _ _ hr) h
    rw [fccVector_eq]
    cases dual
    · exact Ball.contains_mul hi (Ball.contains_exact _)
    · exact Ball.contains_mul h (Ball.contains_exact _)

/-- Large finite modes retain a checked interval. This avoids evaluating
the alternating erfc expansion far outside its small-argument regime. -/
def largeKernelRadius (t : ℚ) : ℚ := ((1+t/32)^32*t)⁻¹

theorem largeKernelRadius_sound {t x : ℝ} (ht : 1 ≤ t) (h : t ≤ x) :
    Real.exp (-x)/x ≤ ((1+t/32)^32*t)⁻¹ := by
  have ht' := zero_lt_one.trans_le ht
  have v : 1+t/32 ≤ Real.exp (t/32) := by simpa only [add_comm] using Real.add_one_le_exp (t/32)
  have H := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+t/32) v 32
  rw [← Real.exp_nat_mul (t/32) 32] at H
  have E : (32 : ℝ)*(t/32)=t := by ring
  have H' : (1+t/32)^32 ≤ Real.exp t := by simpa [E] using H
  have T : 0 < (1+t/32)^32*t := by positivity
  have V : (1+t/32)^32*t ≤ Real.exp x*x :=
    mul_le_mul (H'.trans (Real.exp_le_exp.mpr h)) h ht'.le (Real.exp_pos _).le
  rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv]
  simpa only [one_div] using one_div_le_one_div_of_le T V

def largeKernelBalls (t : Ball) : KernelBall :=
  let r := largeKernelRadius t.lo
  ⟨ballOf 0 r, ⟨0,2*r⟩, ⟨0,5*r⟩⟩

theorem largeKernelBalls_sound (k : KernelKind) {t : Ball} {x : ℝ} (hx : t.Contains x)
    (ok : 1 ≤ t.lo) : (largeKernelBalls t).value.Contains (kernelValue k x) ∧
      (largeKernelBalls t).slope.Contains (kernelSlope k x) ∧
      (largeKernelBalls t).curvature.Contains (kernelCurvature k x) := by
  have bound : (t.lo : ℝ) ≤ x := by
    simpa [Ball.lo] using ((SpecialFunctions.contains_iff_endpoints t x).mp hx).1
  have lim : (1 : ℝ) ≤ t.lo := by exact_mod_cast ok
  have h := largeKernelRadius_sound lim bound
  have R : Real.exp (-x)/x ≤ (largeKernelRadius t.lo : ℝ) := by
    simpa [largeKernelRadius] using h
  have V := kernelValue_positive_bound k (zero_lt_one.trans_le (lim.trans bound))
  have D := kernelDerivative_bounds k (lim.trans bound)
  have S : |kernelSlope k x| ≤ 2*(Real.exp (-x)/x) := by rw [← mul_div_assoc]; exact D.1
  have K : |kernelCurvature k x| ≤ 5*(Real.exp (-x)/x) := by rw [← mul_div_assoc]; exact D.2
  refine ⟨ballOf_sound ⟨by simpa using V.1, V.2.trans R⟩, ?_, ?_⟩
  · simpa [largeKernelBalls, Ball.Contains] using
      S.trans (mul_le_mul_of_nonneg_left R (by norm_num : (0 : ℝ) ≤ 2))
  · simpa [largeKernelBalls, Ball.Contains] using
      K.trans (mul_le_mul_of_nonneg_left R (by norm_num : (0 : ℝ) ≤ 5))

def localKernelKind (dual : Bool) : KernelKind := if dual then .one else .half

def localModeJet (ref : Reference) (dual : Bool) (n : IntVec) (p : Point) : StrainJet ℝ :=
  if n=0 then constant 0 0 else realKernel (localKernelKind dual) (localArgumentJet ref dual n p)

def localModeJetBall (ref : Reference) (dual : Bool) (b : Rectangle) (w : StrainMetricWitness)
    (r : RootProposal) (propose : Ball → KernelWitness) (n : IntVec) : Option (StrainJet Ball) :=
  if n=0 then some (constant (Ball.exact 0) (Ball.exact 0)) else
  let a := localArgumentJetBall ref dual (localVectorBall ref dual r n) b w
  if 64 ≤ a.value.lo then
    let k := largeKernelBalls a.value
    some (chain Ball.add Ball.mul a k.value k.slope k.curvature)
  else
    let k := propose a.value
    if k.kind = localKernelKind dual ∧ k.check a.value = true then some (intervalKernel k a) else none

theorem localModeJetBall_sound (ref : Reference) (dual : Bool) (b : Rectangle) (w : StrainMetricWitness)
    (r : RootProposal) (propose : Ball → KernelWitness) (n : IntVec) (B : StrainJet Ball)
    (hw : strainMetricCheck ref b w=true) (hr : cubeRootCheck r (Ball.exact 2)=true)
    (ok : localModeJetBall ref dual b w r propose n=some B) : Encloses b B (localModeJet ref dual n) := by
  intro p hp
  unfold localModeJetBall at ok
  by_cases hn : n=0
  · rw [if_pos hn] at ok
    rw [← Option.some.inj ok, localModeJet, if_pos hn]
    exact const_rel contains_exact_zero
  rw [if_neg hn] at ok
  dsimp only at ok
  have ha := localArgumentJet_rel ref dual n b w hw _ (localVectorBall_sound ref dual r hr n) p hp
  split_ifs at ok with high checked
  · rw [← Option.some.inj ok, localModeJet, if_neg hn]
    have he := largeKernelBalls_sound (localKernelKind dual) ha.1 (by linarith only [high])
    exact chain_rel ha he.1 he.2.1 he.2.2
  · rw [← Option.some.inj ok, localModeJet, if_neg hn]
    have he := kernel_rel ha _ checked.2
    rwa [checked.1] at he

theorem localModeJet_derivatives (ref : Reference) (dual : Bool) (b : Rectangle) (w : StrainMetricWitness)
    (n : IntVec) (hw : strainMetricCheck ref b w=true)
    (pos : n≠0 → ∀ p, b.Mem p → 0 < localArgument ref dual n p) :
    RayDerivatives b (localModeJet ref dual n) := by
  by_cases hn : n=0
  · have e : localModeJet ref dual n = fun _ => constant 0 0 := by
      funext p; simp only [localModeJet, if_pos hn]
    rw [e]
    exact constant_derivatives b 0
  have h := localArgumentJet_derivatives ref dual n b w hw
  have e : localModeJet ref dual n = fun p => realKernel (localKernelKind dual) (localArgumentJet ref dual n p) := by
    funext p; simp only [localModeJet, if_neg hn]
  rw [e]
  exact kernel_derivatives h.1 (localKernelKind dual) (fun p hp => (h.2 p hp).symm ▸ pos hn p hp)

def finiteLocalHessian (ref : Reference) (modes : Finset IntVec) (p : Point) : RealHessian :=
  fun i j => (∑ n ∈ modes, (localModeJet ref false n p).hessian i j) +
    (∑ n ∈ modes, (localModeJet ref true n p).hessian i j) - (localPenaltyJet ref p).hessian i j

def finiteLocalHessianBall (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (modes : Finset IntVec) (direct dual : IntVec → StrainJet Ball) : RationalHessian :=
  fun i j => ((Constants.sumBalls modes fun n => (direct n).hessian i j).add
    (Constants.sumBalls modes fun n => (dual n).hessian i j)).sub ((localPenaltyJetBall ref b w).hessian i j)

theorem finiteLocalHessianBall_sound (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (hw : strainMetricCheck ref b w=true) (r : RootProposal) (hr : cubeRootCheck r (Ball.exact 2)=true)
    (modes : Finset IntVec) (proposal : Bool → IntVec → Ball → KernelWitness)
    (direct dual : IntVec → StrainJet Ball)
    (d : ∀ n ∈ modes, localModeJetBall ref false b w r (proposal false n) n=some (direct n))
    (e : ∀ n ∈ modes, localModeJetBall ref true b w r (proposal true n) n=some (dual n)) :
    ∀ p, b.Mem p → ∀ i j, (finiteLocalHessianBall ref b w modes direct dual i j).Contains
      (finiteLocalHessian ref modes p i j) := by
  intro p hp i j
  have dr := Constants.sumBalls_sound modes (fun n => (direct n).hessian i j) _ (fun n hn =>
    (localModeJetBall_sound ref false b w r _ n _ hw hr (d n hn) p hp).2.2 i j)
  have du := Constants.sumBalls_sound modes (fun n => (dual n).hessian i j) _ (fun n hn =>
    (localModeJetBall_sound ref true b w r _ n _ hw hr (e n hn) p hp).2.2 i j)
  exact Ball.contains_sub (Ball.contains_add dr du) (((localPenaltyJet_sound ref b w hw).1 p hp).2.2 i j)

def indexUnit (k : Fin 3) : IntVec := fun j => if j=k then 1 else 0

def indexJet (ref : Reference) (dual : Bool) (p : Point) (k l : Fin 3) : StrainJet ℝ :=
  let u := localVector ref dual (indexUnit k)
  let v := localVector ref dual (indexUnit l)
  realArith.mul (constant 0 Real.pi) (realSum Finset.univ fun i => realSum Finset.univ fun j =>
    realArith.mul (realArith.mul (localMetricJet ref dual p i j) (constant 0 (u i))) (constant 0 (v j)))

def indexJetBall (ref : Reference) (dual : Bool) (b : Rectangle) (w : StrainMetricWitness)
    (r : RootProposal) (k l : Fin 3) : StrainJet Ball :=
  let u := localVectorBall ref dual r (indexUnit k)
  let v := localVectorBall ref dual r (indexUnit l)
  ballArith.mul (constant (Ball.exact 0) Constants.piInput) (ballSum Finset.univ fun i => ballSum Finset.univ fun j =>
    ballArith.mul (ballArith.mul (localMetricJetBall ref dual b w i j) (constant (Ball.exact 0) (u i)))
      (constant (Ball.exact 0) (v j)))

theorem indexJetBall_sound (ref : Reference) (dual : Bool) (b : Rectangle) (w : StrainMetricWitness)
    (r : RootProposal) (hw : strainMetricCheck ref b w=true) (hr : cubeRootCheck r (Ball.exact 2)=true)
    (p : Point) (hp : b.Mem p) (k l : Fin 3) : Rel (indexJetBall ref dual b w r k l) (indexJet ref dual p k l) := by
  apply product_rel (const_rel Constants.piInput_sound)
  exact sum_rel _ (fun i _ => sum_rel _ (fun j _ => product_rel (product_rel
    ((localMetricJets_sound ref b w hw dual i j).1 p hp)
    (const_rel (localVectorBall_sound ref dual r hr (indexUnit k) i)))
    (const_rel (localVectorBall_sound ref dual r hr (indexUnit l) j))))

private theorem localVector_linear (ref : Reference) (dual : Bool) (n : IntVec) (i : Fin 3) :
    localVector ref dual n i = ∑ k, localVector ref dual (indexUnit k) i * castVec n k := by
  let B := if dual then ((cubicBasis ref)⁻¹).transpose else cubicBasis ref
  have e (u : IntVec) : localVector ref dual u = B.mulVec (castVec u) := by
    cases dual <;> rfl
  have unit (k : Fin 3) : B.mulVec (castVec (indexUnit k)) i = B i k := by
    simp [Matrix.mulVec, dotProduct, castVec, indexUnit, mul_ite]
  simp only [e, unit]
  rfl

private theorem transformedQuad (ref : Reference) (dual : Bool) (n : IntVec) (F : Mat) :
    (∑ i, ∑ j, F i j * localVector ref dual n i * localVector ref dual n j) =
    hessianQuadratic (fun k l => ∑ i, ∑ j,
      F i j * localVector ref dual (indexUnit k) i * localVector ref dual (indexUnit l) j) (castVec n) := by
  simp only [hessianQuadratic, Fin.sum_univ_three, localVector_linear ref dual n]
  ring

private theorem hessianQuadratic_const_mul (c : ℝ) (G : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) :
    c * hessianQuadratic G v = hessianQuadratic (fun k l => c * G k l) v := by
  unfold hessianQuadratic
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem indexJet_expansion (ref : Reference) (dual : Bool) (n : IntVec) (p : Point) :
    ((localArgumentJet ref dual n p).value =
      hessianQuadratic (fun k l => (indexJet ref dual p k l).value) (castVec n)) ∧
    (∀ i, (localArgumentJet ref dual n p).gradient i =
      hessianQuadratic (fun k l => (indexJet ref dual p k l).gradient i) (castVec n)) ∧
    (∀ i j, (localArgumentJet ref dual n p).hessian i j =
      hessianQuadratic (fun k l => (indexJet ref dual p k l).hessian i j) (castVec n)) := by
  have algebra (F : Mat) := transformedQuad ref dual n F
  refine ⟨?_, ?_, ?_⟩
  · simp only [localArgumentJet,indexJet,realArith,realSum,product,constant]
    rw [algebra (fun a c => (localMetricJet ref dual p a c).value), hessianQuadratic_const_mul]
  · intro i
    simp only [localArgumentJet,indexJet,realArith,realSum,product,constant,zero_mul,mul_zero,zero_add,add_zero]
    rw [algebra (fun a c => (localMetricJet ref dual p a c).gradient i), hessianQuadratic_const_mul]
  · intro i j
    simp only [localArgumentJet,indexJet,realArith,realSum,product,constant,zero_mul,mul_zero,zero_add,add_zero]
    rw [algebra (fun a c => (localMetricJet ref dual p a c).hessian i j), hessianQuadratic_const_mul]

end BccSharp.Coulomb.BravaisCover
