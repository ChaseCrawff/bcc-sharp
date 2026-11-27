import BccSharp.Lattice.FirstJet
import BccSharp.Lattice.StrainE2

set_option autoImplicit false

/-! Differentiation of the Lattice strain metric, its cofactor
inverse, the two quadratic arguments, and the Frobenius penalty. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

abbrev StrainJetMatrix := Fin 3 → Fin 3 → FirstJet

private def rational (q : ℚ) : FirstJet := FirstJet.constant (Ball.exact q)

private theorem rational_sound (b : Rectangle) (q : ℚ) :
    (rational q).Agrees b (fun _ => (q : ℝ)) :=
  FirstJet.constant_sound b _ _ (Ball.contains_exact q)

private def tensorJet (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : StrainJetMatrix :=
  let c (i : Fin 5) (factor : ℚ) (root : RootProposal) :=
    ((rational factor).mul (FirstJet.coordinate b i)).mul (FirstJet.constant root.ball.inv)
  let a := c 0 (whitenE ref) w.sqrt₂
  let d := c 1 (whitenE ref) w.sqrt₆
  let u := c 2 (whitenT ref) w.sqrt₂
  let v := c 3 (whitenT ref) w.sqrt₂
  let z := c 4 (whitenT ref) w.sqrt₂
  ![![a.add d,u,v],![u,d.sub a,z],![v,z,(rational (-2)).mul d]]

private theorem tensorJet_sound (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (h₂ : w.sqrt₂.check (Ball.exact 2)=true) (h₆ : w.sqrt₆.check (Ball.exact 6)=true)
    (i j : Fin 3) : ((tensorJet ref b w) i j).Agrees b (fun p => strainTensor ref p i j) := by
  have h2 := RootProposal.inverse_sound w.sqrt₂ (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) h₂
  have h6 := RootProposal.inverse_sound w.sqrt₆ (Ball.exact 6) 6 (by norm_num) (Ball.contains_exact 6) h₆
  have hs₂ := FirstJet.constant_sound b _ _ h2
  have hs₆ := FirstJet.constant_sound b _ _ h6
  have a := FirstJet.mul_sound (FirstJet.mul_sound (rational_sound b (whitenE ref))
    (FirstJet.coordinate_sound b 0)) hs₂
  have d := FirstJet.mul_sound (FirstJet.mul_sound (rational_sound b (whitenE ref))
    (FirstJet.coordinate_sound b 1)) hs₆
  have u := FirstJet.mul_sound (FirstJet.mul_sound (rational_sound b (whitenT ref))
    (FirstJet.coordinate_sound b 2)) hs₂
  have v := FirstJet.mul_sound (FirstJet.mul_sound (rational_sound b (whitenT ref))
    (FirstJet.coordinate_sound b 3)) hs₂
  have z := FirstJet.mul_sound (FirstJet.mul_sound (rational_sound b (whitenT ref))
    (FirstJet.coordinate_sound b 4)) hs₂
  have h00 := FirstJet.add_sound a d
  have h11 := FirstJet.sub_sound d a
  have h22 := FirstJet.mul_sound (rational_sound b (-2)) d
  fin_cases i <;> fin_cases j
  all_goals
    first
    | simpa [tensorJet,strainTensor,div_eq_mul_inv] using h00
    | simpa [tensorJet,strainTensor,div_eq_mul_inv] using h11
    | simpa [tensorJet,strainTensor,div_eq_mul_inv] using h22
    | simpa [tensorJet,strainTensor,div_eq_mul_inv] using u
    | simpa [tensorJet,strainTensor,div_eq_mul_inv] using v
    | simpa [tensorJet,strainTensor,div_eq_mul_inv] using z

private def shiftedJet (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : StrainJetMatrix :=
  fun i j => (rational (if i=j then 1 else 0)).add (tensorJet ref b w i j)

private theorem shiftedJet_sound (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (h₂ : w.sqrt₂.check (Ball.exact 2)=true) (h₆ : w.sqrt₆.check (Ball.exact 6)=true)
    (i j : Fin 3) : (shiftedJet ref b w i j).Agrees b (fun p => (1+strainTensor ref p) i j) := by
  have h := FirstJet.add_sound (rational_sound b (if i=j then 1 else 0))
    (tensorJet_sound ref b w h₂ h₆ i j)
  by_cases hh : i=j <;> simpa [shiftedJet,Matrix.one_apply,Matrix.add_apply,hh] using h

private theorem shiftedJet_value (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (i j : Fin 3) : (shiftedJet ref b w i j).value=shiftedTensorBall ref b w i j := by
  fin_cases i <;> fin_cases j <;> rfl

private def detJet (M : StrainJetMatrix) : FirstJet :=
  let a := (M 0 0).mul (((M 1 1).mul (M 2 2)).sub ((M 1 2).mul (M 2 1)))
  let b := (M 0 1).mul (((M 1 0).mul (M 2 2)).sub ((M 1 2).mul (M 2 0)))
  let c := (M 0 2).mul (((M 1 0).mul (M 2 1)).sub ((M 1 1).mul (M 2 0)))
  (a.sub b).add c

private theorem detJet_sound {b : Rectangle} {M : StrainJetMatrix} {F : Point → Mat}
    (h : ∀ i j, (M i j).Agrees b (fun p => F p i j)) :
    (detJet M).Agrees b (fun p => (F p).det) := by
  have a := FirstJet.mul_sound (h 0 0) (FirstJet.sub_sound
    (FirstJet.mul_sound (h 1 1) (h 2 2)) (FirstJet.mul_sound (h 1 2) (h 2 1)))
  have d := FirstJet.mul_sound (h 0 1) (FirstJet.sub_sound
    (FirstJet.mul_sound (h 1 0) (h 2 2)) (FirstJet.mul_sound (h 1 2) (h 2 0)))
  have c := FirstJet.mul_sound (h 0 2) (FirstJet.sub_sound
    (FirstJet.mul_sound (h 1 0) (h 2 1)) (FirstJet.mul_sound (h 1 1) (h 2 0)))
  convert FirstJet.add_sound (FirstJet.sub_sound a d) c using 1
  all_goals first
    | rfl
    | (funext p; rw [Matrix.det_fin_three]; ring)

private def adjJet (M : StrainJetMatrix) (i j : Fin 3) : FirstJet :=
  ((M (j+1) (i+1)).mul (M (j+2) (i+2))).sub ((M (j+1) (i+2)).mul (M (j+2) (i+1)))

private theorem adjJet_sound {b : Rectangle} {M : StrainJetMatrix} {F : Point → Mat}
    (h : ∀ i j, (M i j).Agrees b (fun p => F p i j)) (i j : Fin 3) :
    (adjJet M i j).Agrees b (fun p => cyclicAdj (F p) i j) :=
  FirstJet.sub_sound (FirstJet.mul_sound (h _ _) (h _ _)) (FirstJet.mul_sound (h _ _) (h _ _))

structure StrainFirstJets where
  metric : StrainJetMatrix
  reciprocal : StrainJetMatrix

def strainFirstJets (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) : StrainFirstJets :=
  let J := shiftedJet ref b w
  let d := detJet J
  let r := d.cubeRoot w.determinantRoot
  ⟨fun i j => r.inverse.mul (J i j), fun i j => (r.mul d.inverse).mul (adjJet J i j)⟩

private theorem strainFirstJet_detValue (ref : Reference) (b : Rectangle) (w : StrainMetricWitness) :
    (detJet (shiftedJet ref b w)).value=detBall (shiftedTensorBall ref b w) := by
  change _ = _
  simp only [detJet,FirstJet.mul,FirstJet.sub,FirstJet.add,detBall,shiftedJet_value]

theorem strainFirstJets_sound (ref : Reference) (b : Rectangle) (w : StrainMetricWitness)
    (ok : strainMetricCheck ref b w=true) :
    (∀ i j, ((strainFirstJets ref b w).metric i j).Agrees b
      (fun p => reconstructedMetric ref p i j)) ∧
    (∀ i j, ((strainFirstJets ref b w).reciprocal i j).Agrees b
      (fun p => (reconstructedMetric ref p)⁻¹ i j)) := by
  have hs := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1
  have hd := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).2
  have hi := Bool.and_eq_true_iff.mp hd.1
  let J (p : Point) : Mat := 1+strainTensor ref p
  let Jb := shiftedJet ref b w
  let d := detJet Jb
  let r := d.cubeRoot w.determinantRoot
  have hv : d.value=detBall (shiftedTensorBall ref b w) := strainFirstJet_detValue ref b w
  have hJ : ∀ i j, (Jb i j).Agrees b (fun p => J p i j) := shiftedJet_sound ref b w hs.1 hs.2
  have hD := detJet_sound hJ
  have hdp : d.value.positive=true := by rw [hv]; exact hi.1
  have hdi : d.value.invertible := by rw [hv]; exact of_decide_eq_true hi.2
  have hdc : cubeRootCheck w.determinantRoot d.value=true := by rw [hv]; exact hd.2
  have hR := FirstJet.cubeRoot_sound hD w.determinantRoot hdp hdi hdc
  have hRi : r.value.invertible := cubeRoot_invertible w.determinantRoot d.value hdc
  have hp (p : Point) (h : b.Mem p) : 0 < (J p).det := Ball.positive_sound hdp (hD.1 p h)
  have hc (p : Point) (h : b.Mem p) :
      reconstructedMetric ref p=((J p).det^(1/3 : ℝ))⁻¹ • J p := by
    show ((J p).det ^ (-(1/3) : ℝ)) • J p = ((J p).det^(1/3 : ℝ))⁻¹ • J p
    rw [Real.rpow_neg (hp p h).le]
  have hI (p : Point) (h : b.Mem p) :
      (reconstructedMetric ref p)⁻¹ =
        (((J p).det^(1/3 : ℝ))*(J p).det⁻¹) • cyclicAdj (J p) := by
    let a := (J p).det^(1/3 : ℝ)
    have ha : 0<a := Real.rpow_pos_of_pos (hp p h) _
    apply Matrix.inv_eq_right_inv
    rw [hc p h,smul_mul_assoc,mul_smul_comm,cyclicAdj_right,smul_smul,smul_smul]
    have e : a⁻¹*(a*(J p).det⁻¹)*(J p).det=1 := by
      field_simp [ha.ne',(hp p h).ne']
    have e' : a⁻¹*(a*(J p).det⁻¹*(J p).det)=1 := by rw [← mul_assoc]; exact e
    first | rw [e,one_smul] | rw [e',one_smul]
  constructor
  · intro i j
    have h := FirstJet.mul_sound (FirstJet.inverse_sound hR hRi) (hJ i j)
    apply FirstJet.agrees_congr h
    intro p hp
    rw [hc p hp]
    rfl
  · intro i j
    have h := FirstJet.mul_sound (FirstJet.mul_sound hR (FirstJet.inverse_sound hD hdi))
      (adjJet_sound hJ i j)
    apply FirstJet.agrees_congr h
    intro p hp
    rw [hI p hp]
    rfl

def strainFrobJet (J : StrainJetMatrix) : FirstJet :=
  FirstJet.sum Finset.univ fun i =>
    FirstJet.sum Finset.univ fun j => ((J i j).sub (rational (if i=j then 1 else 0))).square

theorem strainFrobJet_sound {b : Rectangle} {J : StrainJetMatrix} {F : Point → Mat}
    (h : ∀ i j, (J i j).Agrees b (fun p => F p i j)) :
    (strainFrobJet J).Agrees b (fun p => frobSq (F p-1)) := by
  unfold strainFrobJet frobSq
  apply FirstJet.sum_sound
  intro i _
  apply FirstJet.sum_sound
  intro j _
  have e := FirstJet.square_sound
    (FirstJet.sub_sound (h i j) (rational_sound b (if i=j then 1 else 0)))
  by_cases hh : i=j <;> simpa [Matrix.sub_apply,Matrix.one_apply,hh] using e

def strainQuadJet (J : StrainJetMatrix) (u : Fin 3 → Ball) : FirstJet :=
  FirstJet.sum Finset.univ fun i => FirstJet.sum Finset.univ fun j =>
    ((J i j).mul (FirstJet.constant (u i))).mul (FirstJet.constant (u j))

theorem strainQuadJet_sound {b : Rectangle} {J : StrainJetMatrix} {F : Point → Mat}
    (h : ∀ i j, (J i j).Agrees b (fun p => F p i j))
    (u : Fin 3 → Ball) (x : Vec) (hx : ∀ i, (u i).Contains (x i)) :
    (strainQuadJet J u).Agrees b (fun p => quad (F p) x) := by
  unfold strainQuadJet
  simp only [← hessianQuadratic_eq_quad,hessianQuadratic]
  exact FirstJet.sum_sound _ (fun i _ => FirstJet.sum_sound _ (fun j _ =>
    FirstJet.mul_sound (FirstJet.mul_sound (h i j) (FirstJet.constant_sound b _ _ (hx i)))
      (FirstJet.constant_sound b _ _ (hx j))))

end BccSharp.Coulomb.BravaisCover
