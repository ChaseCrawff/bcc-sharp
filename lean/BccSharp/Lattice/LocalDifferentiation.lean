import BccSharp.Lattice.LocalHessian
import BccSharp.Lattice.Stationarity

set_option autoImplicit false

/-! Uniform differentiation of the two actual strain series.
The near coefficients, positive exponent guard, and quadratic growth
constants are extracted from the same interval jet arithmetic used for
the curvature leaves. -/

noncomputable section
open scoped BigOperators Topology

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open StrainJet

private theorem abs_directional (v u : Point) (G : Point) (z : ℝ) (hz : 0≤z)
    (h : ∀ i, |u i|≤G i*z) : |∑ i, u i*v i| ≤ (∑ i, G i*|v i|)*z := by
  calc
    _ ≤ ∑ i, |u i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (G i*|v i|)*z := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_right_comm (G i)]
      exact mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem abs_hessian (v : Point) (F G : RealHessian) (z : ℝ)
    (h : ∀ i j, |F i j|≤G i j*z) :
    |hessianQuadratic F v| ≤ (∑ i, ∑ j, G i j*|v i| *|v j|)*z := by
  unfold hessianQuadratic
  calc
    _ ≤ ∑ i, |∑ j, F i j*v i*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, G i j*|v i| *|v j| *z := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
      simp only [abs_mul]
      convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h i j) (abs_nonneg (v i)))
        (abs_nonneg (v j)) using 1
      ring
    _ = _ := by simp only [Finset.sum_mul]

def analyticLocalBox : Rectangle := ⟨fun _ => -2*beta, fun _ => 2*beta⟩

theorem analyticLocalBox_ray (v : Point) (h : inProductBall beta beta v) (t : ℝ)
    (ht : t ∈ Set.Ioo (-2 : ℝ) 2) : analyticLocalBox.Mem (t • v) := by
  intro i
  have B : (0 : ℚ) ≤ beta := by norm_num [beta]
  have C : |v i| ≤ (beta : ℝ) := by
    by_cases hlt : i.val < 2
    · exact productBall_abs_le B h i hlt
    · exact h.2 i (by omega)
  have d : |t*v i| ≤ 2*(beta : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨ht.1.le,ht.2.le⟩) C (abs_nonneg _) (by norm_num)
  simpa [analyticLocalBox, Pi.smul_apply, smul_eq_mul] using abs_le.mp d

private theorem mode_near_bounds (ref : Reference) (dual : Bool) (n : IntVec) (v : Point)
    (b : Rectangle) (p : Point) (hp : b.Mem p) (w : LocalHessianWitness)
    (hw : strainMetricCheck ref b w.chart=true) (hr : cubeRootCheck w.length (Ball.exact 2)=true)
    (B : StrainJet Ball) (ok : w.mode ref b dual n=some B) :
    let U := (absUpper B.value : ℝ) + (∑ i, (absUpper (B.gradient i) : ℝ)*|v i|) +
      (∑ i, ∑ j, (absUpper (B.hessian i j) : ℝ)*|v i| *|v j|)
    |(localModeJet ref dual n p).value| ≤ U ∧ |(localModeJet ref dual n p).directional v| ≤ U ∧
      |hessianQuadratic (localModeJet ref dual n p).hessian v| ≤ U := by
  let F := localModeJet ref dual n p
  have hf := localModeJetBall_sound ref dual b w.chart w.length (w.propose dual n) n B hw hr ok p hp
  have nn (a : Ball) : (0 : ℝ)≤absUpper a := by
    exact_mod_cast (abs_nonneg a.lo).trans (le_max_left |a.lo| |a.hi|)
  have G := abs_directional v F.gradient (fun i => (absUpper (B.gradient i) : ℝ)) 1 (by norm_num)
    (fun i => by simpa only [mul_one] using absUpper_sound (hf.2.1 i))
  have H := abs_hessian v F.hessian (fun i j => (absUpper (B.hessian i j) : ℝ)) 1
    (fun i j => by simpa only [mul_one] using absUpper_sound (hf.2.2 i j))
  simp only [mul_one] at G H
  have g : 0 ≤ ∑ i, (absUpper (B.gradient i) : ℝ)*|v i| :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (nn _) (abs_nonneg _))
  have h : 0 ≤ ∑ i, ∑ j, (absUpper (B.hessian i j) : ℝ)*|v i| *|v j| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (nn _) (abs_nonneg _)) (abs_nonneg _)))
  have e := absUpper_sound hf.1
  change _ ∧ _ ∧ _
  exact ⟨by linarith, by dsimp [directional]; dsimp [F,directional] at G; linarith [nn B.value],
    by dsimp [F] at H; linarith [nn B.value]⟩

private theorem contraction_exchange (H : IntVec → RealHessian) (v : Point)
    (h : ∀ i j, Summable (fun n => H n i j)) :
    (∑' n, hessianQuadratic (H n) v)=hessianQuadratic (fun i j => ∑' n, H n i j) v := by
  have hs (i j : Fin 5) := ((h i j).mul_right (v i)).mul_right (v j)
  unfold hessianQuadratic
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [tsum_mul_right]

private theorem vector_exchange (G : IntVec → Point) (v : Point)
    (h : ∀ i, Summable (fun n => G n i)) :
    (∑' n, ∑ i, G n i*v i) = ∑ i, (∑' n, G n i)*v i := by
  rw [Summable.tsum_finsetSum (fun i _ => (h i).mul_right (v i))]
  simp only [tsum_mul_right]

theorem localFamily_differentiation (ref : Reference) (dual : Bool) (b : Rectangle)
    (w : LocalHessianWitness) (ok : w.check ref b=true) (v : Point) (e : ℝ) (he : 0<e)
    (inside : ∀ t ∈ Set.Ioo (-e) e, b.Mem (t • v)) :
    ∀ t ∈ Set.Ioo (-e) e,
      Summable (fun n => (localModeJet ref dual n (t • v)).directional v) ∧
      HasDerivAt (fun s => ∑' n, (localModeJet ref dual n (s • v)).value)
        (∑' n, (localModeJet ref dual n (t • v)).directional v) t ∧
      HasDerivAt (fun s => ∑' n, (localModeJet ref dual n (s • v)).directional v)
        (hessianQuadratic (fun i j => ∑' n, (localModeJet ref dual n (t • v)).hessian i j) v) t := by
  obtain ⟨geom,rest⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨chart,root⟩ := Bool.and_eq_true_iff.mp geom
  obtain ⟨modes,families⟩ := Bool.and_eq_true_iff.mp rest
  have m : w.modeCheck ref b dual=true := by
    cases dual
    · exact (Bool.and_eq_true_iff.mp modes).1
    · exact (Bool.and_eq_true_iff.mp modes).2
  have f : w.familyCheck ref b dual=true := by
    cases dual
    · exact (Bool.and_eq_true_iff.mp families).1
    · exact (Bool.and_eq_true_iff.mp families).2
  obtain ⟨ex, tail⟩ := Bool.and_eq_true_iff.mp f
  let J := indexJetBall ref dual b w.chart w.length
  let a : ℝ := w.exponentLower dual
  have ha : 0<a := by
    show (0 : ℝ) < ((w.exponentLower dual : ℚ) : ℝ)
    exact_mod_cast (of_decide_eq_true (Bool.and_eq_true_iff.mp ex).1 : 0<w.exponentLower dual)
  let G (i : Fin 5) : ℝ := coefficient₁ J i
  let H (i j : Fin 5) : ℝ := coefficient₂ J i j
  have gn (i : Fin 5) : 0≤G i := by
    dsimp [G,coefficient₁]; push_cast
    apply Finset.sum_nonneg; intro k _
    apply Finset.sum_nonneg; intro l _
    unfold absUpper; positivity
  have hn (i j : Fin 5) : 0≤H i j := by
    dsimp [H,coefficient₂]; push_cast
    apply Finset.sum_nonneg; intro k _
    apply Finset.sum_nonneg; intro l _
    unfold absUpper; positivity
  let K₁ : ℝ := ∑ i, G i*|v i|
  let K₂ : ℝ := ∑ i, ∑ j, H i j*|v i| *|v j|
  have n₁ : 0≤K₁ := Finset.sum_nonneg (fun i _ => mul_nonneg (gn i) (abs_nonneg _))
  have n₂ : 0≤K₂ := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hn i j) (abs_nonneg _)) (abs_nonneg _)))
  let q (n : IntVec) (t : ℝ) := localArgumentJet ref dual n (t • v)
  let V (n : IntVec) (t : ℝ) := (q n t).value
  let D (n : IntVec) (t : ℝ) := (q n t).directional v
  let E (n : IntVec) (t : ℝ) := hessianQuadratic (q n t).hessian v
  let B (n : IntVec) := (w.mode ref b dual n).getD (constant (Ball.exact 0) (Ball.exact 0))
  let U (n : IntVec) : ℝ := (absUpper (B n).value : ℝ) + (∑ i, (absUpper ((B n).gradient i) : ℝ)*|v i|) +
    (∑ i, ∑ j, (absUpper ((B n).hessian i j) : ℝ)*|v i| *|v j|)
  have low (n : IntVec) (t : ℝ) (ht : t ∈ Set.Ioo (-e) e) : a*sq (castVec n) ≤ V n t :=
    exponentCheck_sound ref dual b w.chart w.length chart root _ _ ex _ (inside t ht) n
  have val (n : IntVec) (t : ℝ) : rayKernel (localKernelKind dual) V n t = (localModeJet ref dual n (t • v)).value := by
    by_cases hz : n=0 <;> simp [rayKernel, localModeJet, hz, constant, V, q, realKernel, chain]
  have first (n : IntVec) (t : ℝ) : rayKernelFirst (localKernelKind dual) V D n t =
      (localModeJet ref dual n (t • v)).directional v := by
    by_cases hz : n=0
    · simp [rayKernelFirst, localModeJet, hz, constant, directional]
    · simp only [rayKernelFirst, localModeJet, if_neg hz, realKernel, chain_directional, V, D, q]
  have second (n : IntVec) (t : ℝ) : rayKernelSecond (localKernelKind dual) V D E n t =
      hessianQuadratic (localModeJet ref dual n (t • v)).hessian v := by
    by_cases hz : n=0
    · simp [rayKernelSecond, localModeJet, hz, constant, hessianQuadratic]
    · simp only [rayKernelSecond, localModeJet, if_neg hz, realKernel, chain_hessian, V, D, E, q]
  have jets (n : IntVec) (t : ℝ) (nz : n≠0) (ht : t ∈ Set.Ioo (-e) e) :
      0<V n t ∧ HasDerivAt (V n) (D n t) t ∧ HasDerivAt (D n) (E n t) t := by
    have p : 0<sq (castVec n) := by
      apply lt_of_le_of_ne (sq_nonnegative _)
      intro h0
      have h := (sq_eq_zero_iff _).mp h0.symm
      apply nz
      funext i
      show n i = 0
      have hc : ((n i : ℤ) : ℝ) = 0 := congrFun h i
      exact_mod_cast hc
    exact ⟨(mul_pos ha p).trans_le (low n t ht),
      (localArgumentJet_derivatives ref dual n b w.chart chart).1 v t (inside t ht)⟩
  have remote (n : IntVec) (out : n∉localCube checkedLocalRadius) (nz : n≠0) (t : ℝ) (ht : t ∈ Set.Ioo (-e) e) :
      1≤V n t ∧ a*sq (castVec n)≤V n t ∧ |D n t|≤K₁*sq (castVec n) ∧ |E n t|≤K₂*sq (castVec n) := by
    have h0 : 1≤a*(checkedLocalRadius+1 : ℝ)^2 := by
      show (1 : ℝ) ≤ ((w.exponentLower dual : ℚ) : ℝ)*(checkedLocalRadius+1 : ℝ)^2
      exact_mod_cast (of_decide_eq_true (Bool.and_eq_true_iff.mp tail).1 : 1≤w.exponentLower dual*(checkedLocalRadius+1 : ℚ)^2)
    have hN : checkedLocalRadius+1≤ cubeRadius n := by
      have h := (mem_localCube n checkedLocalRadius).not.mp out
      omega
    have hs : (checkedLocalRadius+1 : ℝ)^2≤ sq (castVec n) :=
      (pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(checkedLocalRadius+1 : ℝ))
        (by exact_mod_cast hN) 2).trans (cubeRadius_sq_le n)
    obtain ⟨g,d⟩ := derivativeCoefficients_sound ref dual b w.chart w.length chart root _ (inside t ht) n
    refine ⟨h0.trans ((mul_le_mul_of_nonneg_left hs ha.le).trans (low n t ht)),low n t ht,?_⟩
    exact ⟨(abs_directional v (q n t).gradient G _ (sq_nonneg _) g).trans
        (mul_le_mul_of_nonneg_left (cubeRadius_sq_le n) n₁),
      (abs_hessian v (q n t).hessian H _ d).trans (mul_le_mul_of_nonneg_left (cubeRadius_sq_le n) n₂)⟩
  have near (n : IntVec) (hin : n∈localCube checkedLocalRadius) : 0≤U n ∧
      ∀ t ∈ Set.Ioo (-e) e, |rayKernel (localKernelKind dual) V n t|≤U n ∧
        |rayKernelFirst (localKernelKind dual) V D n t|≤U n ∧ |rayKernelSecond (localKernelKind dual) V D E n t|≤U n := by
    have accepted : w.mode ref b dual n=some (B n) := option_getD_sound
      ((of_decide_eq_true m : ∀ n : ↥(localCube checkedLocalRadius), _) ⟨n,hin⟩) _
    have bound (t : ℝ) (ht : t ∈ Set.Ioo (-e) e) :=
      mode_near_bounds ref dual n v b (t • v) (inside t ht) w chart root (B n) accepted
    refine ⟨(abs_nonneg _).trans (bound 0 ⟨neg_lt_zero.mpr he,he⟩).1, fun t ht => ?_⟩
    rw [val,first,second]
    exact bound t ht
  intro t ht
  have hh := rayKernel_tsum_derivatives (localKernelKind dual) V D E _ U e a K₁ K₂ he ha n₁ n₂ jets remote near t ht
  simp_rw [val,first,second] at hh
  have hx := contraction_exchange (fun n => (localModeJet ref dual n (t • v)).hessian) v
    (fun i j => (localFamilyTail_sound ref dual b w.chart w.length chart root _ _ _ ex tail _ (inside t ht) i j).1)
  rw [hx] at hh
  exact hh

def signedRaySlope (ref : Reference) (v : Point) (t : ℝ) : ℝ :=
  (∑' n, (localModeJet ref false n (t • v)).directional v) +
  (∑' n, (localModeJet ref true n (t • v)).directional v) - (localPenaltyJet ref (t • v)).directional v

theorem localSignedObjective_differentiation (ref : Reference) (b : Rectangle)
    (w : LocalHessianWitness) (ok : w.check ref b=true) (v : Point) (e : ℝ) (he : 0<e)
    (inside : ∀ t ∈ Set.Ioo (-e) e, b.Mem (t • v)) :
    ∀ t ∈ Set.Ioo (-e) e,
      HasDerivAt (fun s : ℝ => localSignedObjective ref (s • v)) (signedRaySlope ref v t) t ∧
      HasDerivAt (signedRaySlope ref v) (hessianQuadratic (localSignedHessian ref (t • v)) v) t := by
  intro t ht
  have chart := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1
  have mode (dual : Bool) := (localFamily_differentiation ref dual b w ok v e he inside t ht).2
  have p := localPenaltyJet_sound ref b w.chart chart
  obtain ⟨s,ds⟩ := p.2.1 v t (inside t ht)
  have same (y : ℝ) (hy : y ∈ Set.Ioo (-e) e) :
      ((∑' n, (localModeJet ref false n (y • v)).value) + (∑' n, (localModeJet ref true n (y • v)).value) -
        strainFullSeries ref 0) - (localPenaltyJet ref (y • v)).value = localSignedObjective ref (y • v) := by
    rw [p.2.2 _ (inside y hy), localSignedObjective]
    have modeValue (dual : Bool) (n : IntVec) : (localModeJet ref dual n (y • v)).value =
        if n=0 then 0 else kernelValue (localKernelKind dual) (localArgument ref dual n (y • v)) := by
      have eq := (localArgumentJet_derivatives ref dual n b w.chart chart).2 _ (inside y hy)
      by_cases hn : n=0 <;> simp [localModeJet, hn, constant, realKernel, chain, eq]
    simp_rw [modeValue]
    norm_num [strainFullSeries, localArgument, localVector, localKernelKind, kernelValue, KernelKind.power]
  constructor
  · have h := (((mode false).1.add (mode true).1).sub_const (strainFullSeries ref 0)).sub s
    exact h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) (fun y hy => (same y hy).symm))
  · have h := ((mode false).2.fun_add (mode true).2).fun_sub ds
    refine h.congr_deriv ?_
    simp only [hessianQuadratic, localSignedHessian, sub_mul, add_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]

private theorem analyticLocalBox_small_ray (v : Point) :
    ∃ e : ℝ, 0<e ∧ ∀ t ∈ Set.Ioo (-e) e, analyticLocalBox.Mem (t • v) := by
  let C := 1+∑ i, |v i|
  have hC : 0<C := by dsimp [C]; linarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => abs_nonneg (v i))]
  have hb : (0 : ℝ)<beta := by norm_num [beta]
  let e := 2*(beta : ℝ)/C
  have he : 0<e := by dsimp [e]; positivity
  refine ⟨e,he,fun t ht i => ?_⟩
  have h : |v i| ≤ C := by
    dsimp [C]
    linarith [Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)]
  have bound : |t*v i| ≤ 2*(beta : ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ e*C := mul_le_mul (abs_le.mpr ⟨ht.1.le,ht.2.le⟩) h (abs_nonneg _) he.le
      _ = _ := by dsimp [e]; field_simp [hC.ne']
  simpa [analyticLocalBox, Pi.smul_apply, smul_eq_mul] using abs_le.mp bound

def localSignedGradient (ref : Reference) (p : Point) (i : Fin 5) : ℝ :=
  (∑' n, (localModeJet ref false n p).gradient i) + (∑' n, (localModeJet ref true n p).gradient i) -
    (localPenaltyJet ref p).gradient i

theorem localSignedObjective_origin_derivative (ref : Reference) (w : LocalHessianWitness)
    (ok : w.check ref analyticLocalBox=true) (v : Point) :
    HasDerivAt (fun t : ℝ => localSignedObjective ref (t • v)) (∑ i, localSignedGradient ref 0 i*v i) 0 := by
  obtain ⟨e,he,heBox⟩ := analyticLocalBox_small_ray v
  have exactD := (localSignedObjective_differentiation ref analyticLocalBox w ok v e he heBox 0
    ⟨neg_lt_zero.mpr he,he⟩).1
  have gs (dual : Bool) (i : Fin 5) : Summable (fun n => (localModeJet ref dual n 0).gradient i) := by
    let u : Point := fun j => if j=i then 1 else 0
    obtain ⟨d,hd,inBox⟩ := analyticLocalBox_small_ray u
    have s := (localFamily_differentiation ref dual analyticLocalBox w ok u d hd inBox 0 ⟨neg_lt_zero.mpr hd,hd⟩).1
    simpa [zero_smul, directional, u, mul_ite] using s
  unfold signedRaySlope directional at exactD
  simp only [zero_smul] at exactD
  rw [vector_exchange _ v (gs false),vector_exchange _ v (gs true)] at exactD
  simpa only [localSignedGradient, sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib] using exactD

def tensorDerivative (ref : Reference) : Mat →ₗ[ℝ] ℝ where
  toFun S := ∑ i, localSignedGradient ref 0 i * strainCoordinates ref S i
  map_add' S T := by
    classical
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    fin_cases i <;> simp [strainCoordinates, Matrix.add_apply, div_eq_mul_inv] <;> ring
  map_smul' r S := by
    classical
    simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    fin_cases i <;> simp [strainCoordinates, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring

def analyticMetricPositiveCheck (ref : Reference) (w : LocalHessianWitness) : Bool :=
  curvatureCheck (9/10) (metricBall ref analyticLocalBox w.chart)

private theorem analyticLocal_frame (ref : Reference) (w : LocalHessianWitness)
    (ok : w.check ref analyticLocalBox=true) (positive : analyticMetricPositiveCheck ref w=true)
    (p : Point) (hp : analyticLocalBox.Mem p) : ∃ A : Mat, |A.det|=1 ∧ gram A=reconstructedMetric ref p := by
  have chart := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1
  let C := reconstructedMetric ref p
  have enc := strainMetric_evaluate ref analyticLocalBox w.chart chart p hp
  have lo (v : Vec) : (9/10 : ℝ)*sq v ≤ quad C v := by
    have h := curvatureCheck_sound (9/10) _ positive C enc.1 v
    simpa only [hessianQuadratic_eq_quad, sq, Rat.cast_div, Rat.cast_ofNat] using h
  obtain ⟨A,symm,_,sqA,_⟩ := symmetric_squareRoot_error C (reconstructedMetric_symm ref p)
    (9/10 : ℝ) (by norm_num) lo
  refine ⟨A,?_ ,?_⟩
  · have hd := congrArg Matrix.det sqA
    rw [Matrix.det_mul,enc.2.2] at hd
    have hp : |A.det|^2=1 := by rw [sq_abs,pow_two,hd]
    nlinarith only [hp,abs_nonneg A.det]
  · rw [gram,symm,sqA]

private theorem cubic_act_add (m : CubicMove) (X Y : Mat) : m.act (X+Y)=m.act X+m.act Y := by
  simp [CubicMove.act,Matrix.mul_add,Matrix.add_mul]

private theorem cubic_act_scale (m : CubicMove) (r : ℝ) (S : Mat) : m.act (r • S)=r • m.act S := by
  simp [CubicMove.act,mul_smul_comm,smul_mul_assoc]

private theorem cubic_act_det (m : CubicMove) (S : Mat) : (m.act S).det=S.det := by
  have h := congrArg (fun x : ℝ => x^2) m.abs_det
  simp only [sq_abs,one_pow] at h
  simp only [CubicMove.act,Matrix.det_mul,Matrix.det_transpose]
  calc
    _ = m.matrix.det^2*S.det := by ring
    _ = _ := by rw [h,one_mul]

private theorem cubic_act_frob (m : CubicMove) (S : Mat) : frobSq (m.act S)=frobSq S := by
  cases m <;> norm_num [frobSq,Fin.sum_univ_three,CubicMove.act_apply,CubicMove.sign,CubicMove.permutation] <;> ring

private theorem cubic_metric (ref : Reference) (m : CubicMove) (S : Mat)
    (symm : S.transpose=S) (tr : diagonalSum S=0) :
    reconstructedMetric ref (strainCoordinates ref (m.act S)) = m.act (reconstructedMetric ref (strainCoordinates ref S)) := by
  unfold reconstructedMetric
  have e : 1+m.act S=m.act (1+S) := by rw [cubic_act_add,m.act_one]
  rw [strainTensor_reconstruct ref S symm tr, strainTensor_reconstruct ref _ (m.symmetric_act S symm)
    ((m.diagonalSum_act S).trans tr), e]
  dsimp only
  rw [cubic_act_det, cubic_act_scale]

private theorem cubicRay_value_eq (ref : Reference) (w : LocalHessianWitness)
    (ok : w.check ref analyticLocalBox=true) (positive : analyticMetricPositiveCheck ref w=true)
    (m : CubicMove) (S : Mat) (symm : S.transpose=S) (tr : diagonalSum S=0)
    (inside : analyticLocalBox.Mem (strainCoordinates ref S)) :
    localSignedObjective ref (strainCoordinates ref (m.act S)) = localSignedObjective ref (strainCoordinates ref S) := by
  obtain ⟨A,hA,hG⟩ := analyticLocal_frame ref w ok positive _ inside
  have vol : |(A*m.matrix).det|=1 := by rw [Matrix.det_mul,abs_mul,hA,m.abs_det,one_mul]
  have gramMove : gram (A*m.matrix)=reconstructedMetric ref (strainCoordinates ref (m.act S)) := by
    rw [cubic_metric ref m S symm tr,← hG]
    simp [gram,CubicMove.act,Matrix.transpose_mul,mul_assoc]
  have e₁ := strainFullSeries_energy_of_absDet ref _ (A*m.matrix) vol gramMove
  have e₂ := strainFullSeries_energy_of_absDet ref _ A hA hG
  rw [strainBasis_move_energy] at e₁
  have ec : strainFullSeries ref (strainCoordinates ref (m.act S))=strainFullSeries ref (strainCoordinates ref S) := by
    linarith only [e₁,e₂]
  have ep : reconstructedMetric ref (strainCoordinates ref (m.act S))-1 =
      m.act (reconstructedMetric ref (strainCoordinates ref S)-1) := by
    rw [cubic_metric ref m S symm tr]
    have orth : m.matrix.transpose*m.matrix=1 := by
      simpa only [CubicMove.act, Matrix.mul_one] using m.act_one
    simp [CubicMove.act, Matrix.mul_sub, Matrix.sub_mul, orth]
  rw [localSignedObjective,localSignedObjective,ec,ep,cubic_act_frob]

private theorem strainCoordinates_smul (ref : Reference) (t : ℝ) (S : Mat) :
    strainCoordinates ref (t • S)=t • strainCoordinates ref S := by
  ext i
  fin_cases i <;> simp [strainCoordinates, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring

private theorem strainCoordinates_tensor (ref : Reference) (v : Point) :
    strainCoordinates ref (strainTensor ref v)=v := by
  have e : (whitenE ref : ℝ)≠0 := by cases ref <;> norm_num [whitenE]
  have t : (whitenT ref : ℝ)≠0 := by cases ref <;> norm_num [whitenT]
  have s₂ := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have s₆ := Real.sq_sqrt (by norm_num : (0 : ℝ)≤6)
  have z₂ := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ)<2)).ne'
  have z₆ := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ)<6)).ne'
  ext i
  fin_cases i <;> simp [strainCoordinates,strainTensor] <;> field_simp [e,t,z₂,z₆] <;>
    (try rw [s₂]) <;> (try rw [s₆]) <;> ring

theorem localSignedObjective_stationary (ref : Reference) (w : LocalHessianWitness)
    (ok : w.check ref analyticLocalBox=true) (positive : analyticMetricPositiveCheck ref w=true) (v : Point) :
    HasDerivAt (fun t : ℝ => localSignedObjective ref (t • v)) 0 0 := by
  let F (S : Mat) := localSignedObjective ref (strainCoordinates ref S)
  have diff (S : Mat) : HasDerivAt (fun t : ℝ => F (t • S)) (tensorDerivative ref S) 0 := by
    simp_rw [F,strainCoordinates_smul]
    exact localSignedObjective_origin_derivative ref w ok (strainCoordinates ref S)
  have inv (m : CubicMove) (S : Mat) (symm : S.transpose=S) (tr : diagonalSum S=0) :
      tensorDerivative ref (m.act S)=tensorDerivative ref S := by
    obtain ⟨e,he,small⟩ := analyticLocalBox_small_ray (strainCoordinates ref S)
    have eq : (fun t : ℝ => F (t • S)) =ᶠ[𝓝 0] (fun t : ℝ => F (t • m.act S)) := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr he) he] with t ht
      have symmT : (t • S).transpose=t • S := by simp [Matrix.transpose_smul,symm]
      have traceT : diagonalSum (t • S)=0 := by
        simpa [diagonalSum,Matrix.smul_apply,smul_eq_mul,mul_add] using congrArg (fun x : ℝ => t*x) tr
      have h := cubicRay_value_eq ref w ok positive m (t • S) symmT traceT
        (by rw [strainCoordinates_smul]; exact small t ht)
      simpa [F,cubic_act_scale] using h.symm
    exact ((diff (m.act S)).congr_of_eventuallyEq eq).unique (diff S)
  let S := strainTensor ref v
  have symm : S.transpose=S := by ext i j; fin_cases i <;> fin_cases j <;> simp [S,strainTensor,Matrix.transpose_apply]
  have tr : diagonalSum S=0 := by simp [S,strainTensor,diagonalSum]; ring
  have h := diff S
  rw [cubic_invariant_linear_zero_on_strain _ inv S symm tr] at h
  simpa only [F,strainCoordinates_smul,S,strainCoordinates_tensor] using h

theorem computedNonzeroLocalStrain (ref : Reference) (rayWitness : LocalHessianWitness)
    (rayOK : rayWitness.check ref analyticLocalBox=true)
    (positive : analyticMetricPositiveCheck ref rayWitness=true)
    (spectral : ref=.bcc → localBccSpectralCheck=true)
    (g : Grid 5) (gOK : g.check ballRoot=true)
    (forest : (Fin 2 → Fin 5) → (Fin 3 → Fin 5) → AddressedTree LocalCurvatureRow)
    (checked : ∀ owner suffix, (forest owner suffix).check (localCurvatureCheck ref)
      (gridAddress (.localBall ref) (Fin.append owner suffix)) (g.box (Fin.append owner suffix))=true) :
    NonzeroLocalStrain ref := by
  intro v fold ball nz A hA hG
  have D := localSignedObjective_differentiation ref analyticLocalBox rayWitness rayOK v 2 (by norm_num)
    (analyticLocalBox_ray v ball)
  have D0 := localSignedObjective_stationary ref rayWitness rayOK positive v
  have zero : signedRaySlope ref v 0=0 := (D 0 (by norm_num)).1.unique D0
  apply local_strict_of_signed_ray ref v fold ball nz A hA hG spectral (localSignedHessian ref) (signedRaySlope ref v) zero
  · exact fun t ht => (D t (localRayInterval_mem ht)).1.continuousAt.continuousWithinAt
  · exact fun t ht => (D t (localRayInterval_mem ht)).2.continuousAt.continuousWithinAt
  · exact fun t ht => (D t (localRayInterval_mem (Set.Ioo_subset_Icc_self ht))).1
  · exact fun t ht => (D t (localRayInterval_mem (Set.Ioo_subset_Icc_self ht))).2
  · exact fun p fold ball => computedLocalGrid_curvature ref g gOK forest checked p fold ball

end BccSharp.Coulomb.BravaisCover
