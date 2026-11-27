import BccSharp.Lattice.FixedLocal

set_option autoImplicit false

/-! Local-ball closure from fixed-point mode jets. The index jets are
literal integer balls checked against the exact `indexJetBall`; the
exponent, tail, differentiation and stationarity arguments of
`BccSharp.Lattice.LocalDifferentiation` are restated for any such enclosure
and an arbitrary cube radius. The curvature check sums the fixed-point
mode Hessians over the cube, adds the Gaussian tails and checks an exact
rational LDLᵀ factor. `nonzeroLocalStrain_of_checks` then gives
`NonzeroLocalStrain`. -/

noncomputable section
open scoped BigOperators Topology

namespace BccSharp.Coulomb.BravaisCover.FixedLocal
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open Constants.HighPrecision
open StrainJet

/-! ## Rational views and coverage -/

def ratJet (F : FJet) : StrainJet Ball := entrywise FixedPoint.Ball.rational F

theorem ratJet_rel {F : FJet} {a : StrainJet ℝ} (h : FRel F a) : Rel (ratJet F) a := h

def jetCovered (B : StrainJet Ball) (F : FJet) : Bool :=
  (decide (B.value.Covers F.value.rational) &&
    decide (∀ i, (B.gradient i).Covers (F.gradient i).rational)) &&
    decide (∀ i j, (B.hessian i j).Covers (F.hessian i j).rational)

theorem jetCovered_rel {B : StrainJet Ball} {F : FJet} {a : StrainJet ℝ}
    (h : jetCovered B F = true) (hB : Rel B a) : FRel F a := by
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
  have c1 : B.value.Covers F.value.rational := of_decide_eq_true h1
  have c2 : ∀ i, (B.gradient i).Covers (F.gradient i).rational := of_decide_eq_true h2
  have c3 : ∀ i j, (B.hessian i j).Covers (F.hessian i j).rational := of_decide_eq_true h3
  exact ⟨Ball.covers_sound c1 hB.1, fun i => Ball.covers_sound (c2 i) (hB.2.1 i),
    fun i j => Ball.covers_sound (c3 i j) (hB.2.2 i j)⟩

def IndexEnclosure (ref : Reference) (dual : Bool) (b : Rectangle)
    (J : Fin 3 → Fin 3 → StrainJet Ball) : Prop :=
  ∀ p, b.Mem p → ∀ k l, Rel (J k l) (indexJet ref dual p k l)

/-! ## Exponent, derivative coefficients and tails for an arbitrary enclosure -/

private theorem rat_cast_ite' (c : Prop) [Decidable c] (x y : ℚ) :
    (((if c then x else y : ℚ)) : ℝ) = if c then (x : ℝ) else (y : ℝ) := by
  split_ifs <;> rfl

theorem exponentCheck_sound' (ref : Reference) (dual : Bool) (b : Rectangle)
    (J : Fin 3 → Fin 3 → StrainJet Ball) (hJ : IndexEnclosure ref dual b J) (a : ℚ)
    (f : LdlWitness 3) (ok : exponentCheck J a f=true) (p : Point) (hp : b.Mem p) :
    ∀ n : IntVec, (a : ℝ)*sq (castVec n) ≤ (localArgumentJet ref dual n p).value := by
  intro n
  let M : Mat := fun k l => (indexJet ref dual p k l).value-(if k=l then (a : ℝ) else 0)
  have bd (i j : Fin 3) : (shiftedIndexMetric J a i j).Contains (M i j) := by
    unfold M shiftedIndexMetric
    simpa only [rat_cast_ite', Rat.cast_zero] using Ball.contains_sub
      (hJ p hp i j).1 (Ball.contains_exact (if i=j then a else 0))
  by_cases hn : castVec n=0
  · rw [(indexJet_expansion ref dual n p).1, hn]; simp [sq,hessianQuadratic]
  have h := ldlCheck_sound (shiftedIndexMetric J a) f (Bool.and_eq_true_iff.mp ok).2 M bd (castVec n) hn
  rw [(indexJet_expansion ref dual n p).1]
  have expand : hessianQuadratic M (castVec n) =
      hessianQuadratic (fun i j => (indexJet ref dual p i j).value) (castVec n) -
        (a : ℝ)*sq (castVec n) := by
    simp only [hessianQuadratic, M, sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp [Finset.mul_sum, sq, pow_two, ite_mul, mul_assoc]
  rw [expand] at h
  linarith

private theorem absQuad_bound' (B : Fin 3 → Fin 3 → Ball) (F : Mat)
    (entry : ∀ i j, (B i j).Contains (F i j)) (n : IntVec) :
    |hessianQuadratic F (castVec n)| ≤ (∑ i, ∑ j, (absUpper (B i j) : ℝ))*(cubeRadius n : ℝ)^2 := by
  unfold hessianQuadratic
  calc
    _ ≤ ∑ i, |∑ j, F i j*castVec n i*castVec n j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (absUpper (B i j) : ℝ)*(cubeRadius n : ℝ)^2 := by
      refine Finset.sum_le_sum (fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_)
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul, pow_two, mul_assoc]
      exact mul_le_mul (absUpper_sound (entry i j))
        (mul_le_mul (cubeRadius_coord n i) (cubeRadius_coord n j) (abs_nonneg _) (Nat.cast_nonneg _))
        (by positivity) ((abs_nonneg _).trans (absUpper_sound (entry i j)))
    _ = _ := by simp [Finset.sum_mul]

theorem derivativeCoefficients_sound' (ref : Reference) (dual : Bool) (b : Rectangle)
    (J : Fin 3 → Fin 3 → StrainJet Ball) (hJ : IndexEnclosure ref dual b J)
    (p : Point) (hp : b.Mem p) (n : IntVec) :
    (∀ i, |(localArgumentJet ref dual n p).gradient i| ≤
      (coefficient₁ J i : ℝ)*(cubeRadius n : ℝ)^2) ∧
    (∀ i j, |(localArgumentJet ref dual n p).hessian i j| ≤
      (coefficient₂ J i j : ℝ)*(cubeRadius n : ℝ)^2) := by
  obtain ⟨_,g,h⟩ := indexJet_expansion ref dual n p
  constructor
  · intro i; rw [g]; unfold coefficient₁; push_cast
    exact absQuad_bound' _ _ (fun k l => (hJ p hp k l).2.1 i) n
  · intro i j; rw [h]; unfold coefficient₂; push_cast
    exact absQuad_bound' _ _ (fun k l => (hJ p hp k l).2.2 i j) n

private theorem absUpper_nonneg' (b : Ball) : 0 ≤ absUpper b :=
  (abs_nonneg b.lo).trans (le_max_left _ _)

private theorem pairCoefficient_nonneg' (J : Fin 3 → Fin 3 → StrainJet Ball) (i j : Fin 5) :
    0 ≤ pairCoefficient J i j := by
  apply (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
    (fun l _ => absUpper_nonneg' ((J k l).gradient i)))).trans
  exact le_max_left _ _

private theorem coefficient₂_nonneg' (J : Fin 3 → Fin 3 → StrainJet Ball) (i j : Fin 5) :
    0 ≤ coefficient₂ J i j :=
  Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => absUpper_nonneg' ((J k l).hessian i j)))

def familyTailCheck (R : ℕ) (J : Fin 3 → Fin 3 → StrainJet Ball) (a : ℚ)
    (w : Fin 5 → Fin 5 → LocalTailWitness) : Bool :=
  decide (1 ≤ a*(R+1 : ℚ)^2) && decide (∀ i j,
    localTailCheck (w i j) R a (shellTailC₂ a (coefficient₂ J i j))
      (shellTailC₄ a (pairCoefficient J i j))=true)

def familyTailUpper (R : ℕ) (J : Fin 3 → Fin 3 → StrainJet Ball) (a : ℚ)
    (w : Fin 5 → Fin 5 → LocalTailWitness) (i j : Fin 5) : ℚ :=
  localTailUpper (w i j) R (shellTailC₂ a (coefficient₂ J i j))
    (shellTailC₄ a (pairCoefficient J i j))

theorem familyTail_sound (R : ℕ) (ref : Reference) (dual : Bool) (b : Rectangle)
    (J : Fin 3 → Fin 3 → StrainJet Ball) (hJ : IndexEnclosure ref dual b J) (a : ℚ)
    (f : LdlWitness 3) (tail : Fin 5 → Fin 5 → LocalTailWitness)
    (ex : exponentCheck J a f=true) (ok : familyTailCheck R J a tail=true)
    (p : Point) (hp : b.Mem p) (i j : Fin 5) :
    Summable (fun n => (localModeJet ref dual n p).hessian i j) ∧
    |∑' n : {n // n ∉ localCube R}, (localModeJet ref dual n.val p).hessian i j| ≤
      (familyTailUpper R J a tail i j : ℝ) := by
  have ap : 0<a := of_decide_eq_true (Bool.and_eq_true_iff.mp ex).1
  have a' : (0 : ℝ)<a := by exact_mod_cast ap
  obtain ⟨rOK, tOK⟩ := Bool.and_eq_true_iff.mp ok
  have hN : (1 : ℝ) ≤ (a : ℝ)*(R+1 : ℝ)^2 := by
    exact_mod_cast (of_decide_eq_true rOK : 1 ≤ a*(R+1 : ℚ)^2)
  have t := localTailUpper_sound (tail i j) R a (shellTailC₂ a (coefficient₂ J i j))
    (shellTailC₄ a (pairCoefficient J i j)) ((of_decide_eq_true tOK : ∀ i j, _) i j)
  have nn₁ : (0 : ℝ)≤pairCoefficient J i j := by exact_mod_cast pairCoefficient_nonneg' J i j
  have nn₂ : (0 : ℝ)≤ coefficient₂ J i j := by exact_mod_cast coefficient₂_nonneg' J i j
  have gaussian := shellTail_gaussian R (fun n => (localModeJet ref dual n p).hessian i j)
    (a : ℝ) (pairCoefficient J i j) (coefficient₂ J i j) a' nn₁ nn₂
  have mode : ∀ k n, n ∈ localShell (R+1+k) →
      |(localModeJet ref dual n p).hessian i j| ≤
        shellEnvelope (a : ℝ) (pairCoefficient J i j) (coefficient₂ J i j) (R+1+k) := by
    intro k n hn
    let N := R+1+k
    have pos : 0<N := by dsimp [N]; omega
    have size : cubeRadius n=N := (mem_localShell n pos).mp hn
    have nz : n≠0 := by intro eq; simp [eq,cubeRadius] at size; omega
    let A := localArgumentJet ref dual n p
    have low : (a : ℝ)*(N : ℝ)^2 ≤ A.value := by
      rw [← size]
      exact (mul_le_mul_of_nonneg_left (cubeRadius_sq_le n) a'.le).trans
        (exponentCheck_sound' ref dual b J hJ a f ex p hp n)
    have big : 1≤A.value := hN.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(R+1 : ℝ))
        (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; dsimp only [N]; push_cast; linarith) 2)
          a'.le).trans low)
    obtain ⟨G,H⟩ := derivativeCoefficients_sound' ref dual b J hJ p hp n
    have g (k : Fin 5) (hh : coefficient₁ J k ≤ pairCoefficient J i j) :
        |A.gradient k| ≤ (pairCoefficient J i j : ℝ)*(N : ℝ)^2 := by
      rw [← size]
      exact (G k).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (sq_nonneg _))
    simp only [localModeJet,if_neg nz,StrainJet.realKernel,StrainJet.chain]
    exact modeHessian_shell_bound (localKernelKind dual) a' pos big low
      (g i (le_max_left _ _)) (g j (le_max_right _ _)) (by simpa only [size] using H i j) nn₁ nn₂
  have t' : Summable (fun k => gaussianShell (a : ℝ) (130*(coefficient₂ J i j : ℝ)/a)
      (130*(pairCoefficient J i j : ℝ)^2/a) (R+1+k)) := by
    simpa [shellTailC₂,shellTailC₄] using t.1
  obtain ⟨ss, bound⟩ := gaussian mode t'
  exact ⟨ss,bound.trans (by simpa [familyTailUpper,shellTailC₂,shellTailC₄] using t.2)⟩

/-! ## The local witness -/

structure LocalData where
  chart : StrainMetricWitness
  length : RootProposal
  radius : ℕ
  index : Bool → Fin 3 → Fin 3 → FJet
  exponent : Bool → ℚ
  exponentFactor : Bool → LdlWitness 3
  tail : Bool → Fin 5 → Fin 5 → LocalTailWitness

namespace LocalData

def indexRat (w : LocalData) (dual : Bool) : Fin 3 → Fin 3 → StrainJet Ball :=
  fun k l => ratJet (w.index dual k l)

def familyCheck (w : LocalData) (dual : Bool) : Bool :=
  exponentCheck (w.indexRat dual) (w.exponent dual) (w.exponentFactor dual) &&
    familyTailCheck w.radius (w.indexRat dual) (w.exponent dual) (w.tail dual)

/-- The finite checks shared by the differentiation and curvature boxes. -/
structure Base (w : LocalData) (ref : Reference) (b : Rectangle) : Prop where
  chart : strainMetricCheck ref b w.chart = true
  length : cubeRootCheck w.length (Ball.exact 2) = true
  covered : ∀ dual k l, jetCovered (indexJetBall ref dual b w.chart w.length k l) (w.index dual k l) = true
  family : ∀ dual, w.familyCheck dual = true

theorem Base.fixedIndex {w : LocalData} {ref : Reference} {b : Rectangle} (base : w.Base ref b)
    (dual : Bool) (p : Point) (hp : b.Mem p) : ∀ k l, FRel (w.index dual k l) (indexJet ref dual p k l) :=
  fun k l => jetCovered_rel (base.covered dual k l)
    (indexJetBall_sound ref dual b w.chart w.length base.chart base.length p hp k l)

theorem Base.index {w : LocalData} {ref : Reference} {b : Rectangle} (base : w.Base ref b)
    (dual : Bool) : IndexEnclosure ref dual b (w.indexRat dual) :=
  fun p hp k l => ratJet_rel (base.fixedIndex dual p hp k l)

/-- Every mode of the cube has a fixed-point jet. -/
def ModesDefined (w : LocalData) (dual : Bool) : Prop :=
  ∀ n ∈ localCube w.radius, ∃ B, fmode dual (fquad (w.index dual)) n = some B

end LocalData

def slabModes (dual : Bool) (arg : IntVec → FJet) (r : ℕ) (a : ℤ) : Bool :=
  (ffold dual arg (slabList r a) fzeroJet).isSome

theorem modes_of_slabs (dual : Bool) (arg : IntVec → FJet) (r : ℕ)
    (h : ∀ a ∈ side r, slabModes dual arg r a = true) (n : IntVec) (hn : n ∈ localCube r) :
    ∃ B, fmode dual arg n = some B := by
  rw [← mem_cubeList, cubeList_slabs, List.mem_flatMap] at hn
  obtain ⟨a, ha, hn⟩ := hn
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp (h a ha)
  exact ffold_some dual arg _ _ _ hS n hn

theorem forall_side {r : ℕ} {Q : ℤ → Prop} (h : ∀ i ∈ List.range (2*r+1), Q ((i : ℤ) - r)) :
    ∀ a ∈ side r, Q a := by
  intro a ha
  simp only [side, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact h i hi

/-! ## Differentiation along rays -/

private theorem abs_directional' (v u : Point) (G : Point) (z : ℝ) (hz : 0≤z)
    (h : ∀ i, |u i|≤G i*z) : |∑ i, u i*v i| ≤ (∑ i, G i*|v i|)*z := by
  calc
    _ ≤ ∑ i, |u i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (G i*|v i|)*z := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_right_comm (G i)]
      exact mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem abs_hessian' (v : Point) (F G : RealHessian) (z : ℝ)
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

theorem fixed_near_bounds (ref : Reference) (dual : Bool) (n : IntVec) (v : Point) (p : Point)
    (B : FJet) (hB : FRel B (localModeJet ref dual n p)) :
    let U := (absUpper B.value.rational : ℝ) + (∑ i, (absUpper (B.gradient i).rational : ℝ)*|v i|) +
      (∑ i, ∑ j, (absUpper (B.hessian i j).rational : ℝ)*|v i| *|v j|)
    |(localModeJet ref dual n p).value| ≤ U ∧ |(localModeJet ref dual n p).directional v| ≤ U ∧
      |hessianQuadratic (localModeJet ref dual n p).hessian v| ≤ U := by
  let F := localModeJet ref dual n p
  have hf1 : B.value.rational.Contains F.value := hB.1
  have hf2 : ∀ i, (B.gradient i).rational.Contains (F.gradient i) := hB.2.1
  have hf3 : ∀ i j, (B.hessian i j).rational.Contains (F.hessian i j) := hB.2.2
  have nn (a : Ball) : (0 : ℝ)≤absUpper a := by
    exact_mod_cast (abs_nonneg a.lo).trans (le_max_left |a.lo| |a.hi|)
  have G := abs_directional' v F.gradient (fun i => (absUpper (B.gradient i).rational : ℝ)) 1
    (by norm_num) (fun i => by simpa only [mul_one] using absUpper_sound (hf2 i))
  have H := abs_hessian' v F.hessian (fun i j => (absUpper (B.hessian i j).rational : ℝ)) 1
    (fun i j => by simpa only [mul_one] using absUpper_sound (hf3 i j))
  simp only [mul_one] at G H
  have g : 0 ≤ ∑ i, (absUpper (B.gradient i).rational : ℝ)*|v i| :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (nn _) (abs_nonneg _))
  have h : 0 ≤ ∑ i, ∑ j, (absUpper (B.hessian i j).rational : ℝ)*|v i| *|v j| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (nn _) (abs_nonneg _)) (abs_nonneg _)))
  have e := absUpper_sound hf1
  change _ ∧ _ ∧ _
  exact ⟨by linarith, by dsimp [directional]; dsimp [F,directional] at G; linarith [nn B.value.rational],
    by dsimp [F] at H; linarith [nn B.value.rational]⟩

private theorem contraction_exchange' (H : IntVec → RealHessian) (v : Point)
    (h : ∀ i j, Summable (fun n => H n i j)) :
    (∑' n, hessianQuadratic (H n) v)=hessianQuadratic (fun i j => ∑' n, H n i j) v := by
  have hs (i j : Fin 5) := ((h i j).mul_right (v i)).mul_right (v j)
  unfold hessianQuadratic
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [tsum_mul_right]

private theorem vector_exchange' (G : IntVec → Point) (v : Point)
    (h : ∀ i, Summable (fun n => G n i)) :
    (∑' n, ∑ i, G n i*v i) = ∑ i, (∑' n, G n i)*v i := by
  rw [Summable.tsum_finsetSum (fun i _ => (h i).mul_right (v i))]
  simp only [tsum_mul_right]

theorem family_differentiation (ref : Reference) (dual : Bool) (b : Rectangle)
    (w : LocalData) (base : w.Base ref b) (modesOK : w.ModesDefined dual)
    (v : Point) (e : ℝ) (he : 0<e) (inside : ∀ t ∈ Set.Ioo (-e) e, b.Mem (t • v)) :
    ∀ t ∈ Set.Ioo (-e) e,
      Summable (fun n => (localModeJet ref dual n (t • v)).directional v) ∧
      HasDerivAt (fun s => ∑' n, (localModeJet ref dual n (s • v)).value)
        (∑' n, (localModeJet ref dual n (t • v)).directional v) t ∧
      HasDerivAt (fun s => ∑' n, (localModeJet ref dual n (s • v)).directional v)
        (hessianQuadratic (fun i j => ∑' n, (localModeJet ref dual n (t • v)).hessian i j) v) t := by
  have chart := base.chart
  have hJ := base.index dual
  obtain ⟨ex, tail⟩ := Bool.and_eq_true_iff.mp (base.family dual)
  let J := w.indexRat dual
  let a : ℝ := w.exponent dual
  have ha : 0<a := by
    show (0 : ℝ) < ((w.exponent dual : ℚ) : ℝ)
    exact_mod_cast (of_decide_eq_true (Bool.and_eq_true_iff.mp ex).1 : 0<w.exponent dual)
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
  let B (n : IntVec) := (fmode dual (fquad (w.index dual)) n).getD fzeroJet
  let U (n : IntVec) : ℝ := (absUpper (B n).value.rational : ℝ) +
    (∑ i, (absUpper ((B n).gradient i).rational : ℝ)*|v i|) +
    (∑ i, ∑ j, (absUpper ((B n).hessian i j).rational : ℝ)*|v i| *|v j|)
  have low (n : IntVec) (t : ℝ) (ht : t ∈ Set.Ioo (-e) e) : a*sq (castVec n) ≤ V n t :=
    exponentCheck_sound' ref dual b J hJ _ _ ex _ (inside t ht) n
  have val (n : IntVec) (t : ℝ) :
      rayKernel (localKernelKind dual) V n t = (localModeJet ref dual n (t • v)).value := by
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
  have remote (n : IntVec) (out : n∉localCube w.radius) (nz : n≠0) (t : ℝ) (ht : t ∈ Set.Ioo (-e) e) :
      1≤V n t ∧ a*sq (castVec n)≤V n t ∧ |D n t|≤K₁*sq (castVec n) ∧ |E n t|≤K₂*sq (castVec n) := by
    have h0 : 1≤a*(w.radius+1 : ℝ)^2 := by
      show (1 : ℝ) ≤ ((w.exponent dual : ℚ) : ℝ)*(w.radius+1 : ℝ)^2
      exact_mod_cast (of_decide_eq_true (Bool.and_eq_true_iff.mp tail).1 :
        1≤w.exponent dual*(w.radius+1 : ℚ)^2)
    have hN : w.radius+1≤ cubeRadius n := by
      have h := (mem_localCube n w.radius).not.mp out
      omega
    have hs : (w.radius+1 : ℝ)^2≤ sq (castVec n) :=
      (pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(w.radius+1 : ℝ))
        (by exact_mod_cast hN) 2).trans (cubeRadius_sq_le n)
    obtain ⟨g,d⟩ := derivativeCoefficients_sound' ref dual b J hJ _ (inside t ht) n
    refine ⟨h0.trans ((mul_le_mul_of_nonneg_left hs ha.le).trans (low n t ht)),low n t ht,?_⟩
    exact ⟨(abs_directional' v (q n t).gradient G _ (sq_nonneg _) g).trans
        (mul_le_mul_of_nonneg_left (cubeRadius_sq_le n) n₁),
      (abs_hessian' v (q n t).hessian H _ d).trans (mul_le_mul_of_nonneg_left (cubeRadius_sq_le n) n₂)⟩
  have near (n : IntVec) (hin : n∈localCube w.radius) : 0≤U n ∧
      ∀ t ∈ Set.Ioo (-e) e, |rayKernel (localKernelKind dual) V n t|≤U n ∧
        |rayKernelFirst (localKernelKind dual) V D n t|≤U n ∧
        |rayKernelSecond (localKernelKind dual) V D E n t|≤U n := by
    obtain ⟨Bn, hBn⟩ := modesOK n hin
    have hB : B n = Bn := by simp [B, hBn]
    have bound (t : ℝ) (ht : t ∈ Set.Ioo (-e) e) := by
      have r := fmode_rel ref dual (t • v) (fquad (w.index dual))
        (fun m _ => fquad_rel ref dual (t • v) (w.index dual) (base.fixedIndex dual (t • v) (inside t ht)) m)
        n Bn hBn
      rw [← hB] at r
      exact fixed_near_bounds ref dual n v (t • v) (B n) r
    refine ⟨(abs_nonneg _).trans (bound 0 ⟨neg_lt_zero.mpr he,he⟩).1, fun t ht => ?_⟩
    rw [val,first,second]
    exact bound t ht
  intro t ht
  have hh := rayKernel_tsum_derivatives (localKernelKind dual) V D E _ U e a K₁ K₂ he ha n₁ n₂
    jets remote near t ht
  simp_rw [val,first,second] at hh
  have hx := contraction_exchange' (fun n => (localModeJet ref dual n (t • v)).hessian) v
    (fun i j => (familyTail_sound w.radius ref dual b J hJ _ _ _ ex tail _ (inside t ht) i j).1)
  rw [hx] at hh
  exact hh

theorem signed_differentiation (ref : Reference) (b : Rectangle)
    (w : LocalData) (base : w.Base ref b) (modesOK : ∀ dual, w.ModesDefined dual)
    (v : Point) (e : ℝ) (he : 0<e) (inside : ∀ t ∈ Set.Ioo (-e) e, b.Mem (t • v)) :
    ∀ t ∈ Set.Ioo (-e) e,
      HasDerivAt (fun s : ℝ => localSignedObjective ref (s • v)) (signedRaySlope ref v t) t ∧
      HasDerivAt (signedRaySlope ref v) (hessianQuadratic (localSignedHessian ref (t • v)) v) t := by
  intro t ht
  have chart := base.chart
  have mode (dual : Bool) :=
    (family_differentiation ref dual b w base (modesOK dual) v e he inside t ht).2
  have p := localPenaltyJet_sound ref b w.chart chart
  obtain ⟨s,ds⟩ := p.2.1 v t (inside t ht)
  have same (y : ℝ) (hy : y ∈ Set.Ioo (-e) e) :
      ((∑' n, (localModeJet ref false n (y • v)).value) +
        (∑' n, (localModeJet ref true n (y • v)).value) -
        strainFullSeries ref 0) - (localPenaltyJet ref (y • v)).value =
        localSignedObjective ref (y • v) := by
    rw [p.2.2 _ (inside y hy), localSignedObjective]
    have modeValue (dual : Bool) (n : IntVec) : (localModeJet ref dual n (y • v)).value =
        if n=0 then 0 else kernelValue (localKernelKind dual) (localArgument ref dual n (y • v)) := by
      have eq := (localArgumentJet_derivatives ref dual n b w.chart chart).2 _ (inside y hy)
      by_cases hn : n=0 <;> simp [localModeJet, hn, constant, realKernel, chain, eq]
    simp_rw [modeValue]
    norm_num [strainFullSeries, localArgument, localVector, localKernelKind, kernelValue,
      KernelKind.power]
  constructor
  · have h := (((mode false).1.add (mode true).1).sub_const (strainFullSeries ref 0)).sub s
    exact h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
      (fun y hy => (same y hy).symm))
  · have h := ((mode false).2.fun_add (mode true).2).fun_sub ds
    refine h.congr_deriv ?_
    simp only [hessianQuadratic, localSignedHessian, sub_mul, add_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-! ## First-order stationarity at the reference -/

private theorem analyticLocalBox_small_ray' (v : Point) :
    ∃ e : ℝ, 0<e ∧ ∀ t ∈ Set.Ioo (-e) e, analyticLocalBox.Mem (t • v) := by
  let C := 1+∑ i, |v i|
  have hC : 0<C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => abs_nonneg (v i))]
  have hb : (0 : ℝ)<beta := by norm_num [beta]
  let e := 2*(beta : ℝ)/C
  have he : 0<e := by dsimp [e]; positivity
  refine ⟨e,he,fun t ht i => ?_⟩
  have h : |v i| ≤ C := by
    dsimp [C]
    have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) => abs_nonneg (v j))
      (Finset.mem_univ i)
    linarith
  have bound : |t*v i| ≤ 2*(beta : ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ e*C := mul_le_mul (abs_le.mpr ⟨ht.1.le,ht.2.le⟩) h (abs_nonneg _) he.le
      _ = _ := by dsimp [e]; field_simp [hC.ne']
  simpa [analyticLocalBox, Pi.smul_apply, smul_eq_mul] using abs_le.mp bound

theorem origin_derivative (ref : Reference) (w : LocalData) (base : w.Base ref analyticLocalBox)
    (modesOK : ∀ dual, w.ModesDefined dual) (v : Point) :
    HasDerivAt (fun t : ℝ => localSignedObjective ref (t • v))
      (∑ i, localSignedGradient ref 0 i*v i) 0 := by
  obtain ⟨e,he,heBox⟩ := analyticLocalBox_small_ray' v
  have exactD := (signed_differentiation ref analyticLocalBox w base modesOK v e he heBox 0
    ⟨neg_lt_zero.mpr he,he⟩).1
  have gs (dual : Bool) (i : Fin 5) :
      Summable (fun n => (localModeJet ref dual n 0).gradient i) := by
    let u : Point := fun j => if j=i then 1 else 0
    obtain ⟨d,hd,inBox⟩ := analyticLocalBox_small_ray' u
    have s := (family_differentiation ref dual analyticLocalBox w base (modesOK dual) u d hd inBox 0
      ⟨neg_lt_zero.mpr hd,hd⟩).1
    simpa [zero_smul, directional, u, mul_ite] using s
  unfold signedRaySlope directional at exactD
  simp only [zero_smul] at exactD
  rw [vector_exchange' _ v (gs false),vector_exchange' _ v (gs true)] at exactD
  simpa only [localSignedGradient, sub_mul, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] using exactD

def metricPositiveCheck (ref : Reference) (chart : StrainMetricWitness) : Bool :=
  curvatureCheck (9/10) (metricBall ref analyticLocalBox chart)

private theorem local_frame (ref : Reference) (chart : StrainMetricWitness)
    (hc : strainMetricCheck ref analyticLocalBox chart=true)
    (positive : metricPositiveCheck ref chart=true)
    (p : Point) (hp : analyticLocalBox.Mem p) :
    ∃ A : Mat, |A.det|=1 ∧ gram A=reconstructedMetric ref p := by
  let C := reconstructedMetric ref p
  have enc := strainMetric_evaluate ref analyticLocalBox chart hc p hp
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

private theorem cubic_act_add' (m : CubicMove) (X Y : Mat) : m.act (X+Y)=m.act X+m.act Y := by
  simp [CubicMove.act,Matrix.mul_add,Matrix.add_mul]

private theorem cubic_act_scale' (m : CubicMove) (r : ℝ) (S : Mat) : m.act (r • S)=r • m.act S := by
  simp [CubicMove.act,mul_smul_comm,smul_mul_assoc]

private theorem cubic_act_det' (m : CubicMove) (S : Mat) : (m.act S).det=S.det := by
  have h := congrArg (fun x : ℝ => x^2) m.abs_det
  simp only [sq_abs,one_pow] at h
  simp only [CubicMove.act,Matrix.det_mul,Matrix.det_transpose]
  calc
    _ = m.matrix.det^2*S.det := by ring
    _ = _ := by rw [h,one_mul]

private theorem cubic_act_frob' (m : CubicMove) (S : Mat) : frobSq (m.act S)=frobSq S := by
  cases m <;> norm_num [frobSq,Fin.sum_univ_three,CubicMove.act_apply,CubicMove.sign,
    CubicMove.permutation] <;> ring

private theorem cubic_metric' (ref : Reference) (m : CubicMove) (S : Mat)
    (symm : S.transpose=S) (tr : diagonalSum S=0) :
    reconstructedMetric ref (strainCoordinates ref (m.act S)) =
      m.act (reconstructedMetric ref (strainCoordinates ref S)) := by
  unfold reconstructedMetric
  have e : 1+m.act S=m.act (1+S) := by rw [cubic_act_add',m.act_one]
  rw [strainTensor_reconstruct ref S symm tr, strainTensor_reconstruct ref _ (m.symmetric_act S symm)
    ((m.diagonalSum_act S).trans tr), e]
  dsimp only
  rw [cubic_act_det', cubic_act_scale']

private theorem cubicRay_value_eq' (ref : Reference) (chart : StrainMetricWitness)
    (hc : strainMetricCheck ref analyticLocalBox chart=true)
    (positive : metricPositiveCheck ref chart=true)
    (m : CubicMove) (S : Mat) (symm : S.transpose=S) (tr : diagonalSum S=0)
    (inside : analyticLocalBox.Mem (strainCoordinates ref S)) :
    localSignedObjective ref (strainCoordinates ref (m.act S)) =
      localSignedObjective ref (strainCoordinates ref S) := by
  obtain ⟨A,hA,hG⟩ := local_frame ref chart hc positive _ inside
  have vol : |(A*m.matrix).det|=1 := by rw [Matrix.det_mul,abs_mul,hA,m.abs_det,one_mul]
  have gramMove : gram (A*m.matrix)=reconstructedMetric ref (strainCoordinates ref (m.act S)) := by
    rw [cubic_metric' ref m S symm tr,← hG]
    simp [gram,CubicMove.act,Matrix.transpose_mul,mul_assoc]
  have e₁ := strainFullSeries_energy_of_absDet ref _ (A*m.matrix) vol gramMove
  have e₂ := strainFullSeries_energy_of_absDet ref _ A hA hG
  rw [strainBasis_move_energy] at e₁
  have ec : strainFullSeries ref (strainCoordinates ref (m.act S)) =
      strainFullSeries ref (strainCoordinates ref S) := by
    linarith only [e₁,e₂]
  have ep : reconstructedMetric ref (strainCoordinates ref (m.act S))-1 =
      m.act (reconstructedMetric ref (strainCoordinates ref S)-1) := by
    rw [cubic_metric' ref m S symm tr]
    have orth : m.matrix.transpose*m.matrix=1 := by
      simpa only [CubicMove.act, Matrix.mul_one] using m.act_one
    simp [CubicMove.act, Matrix.mul_sub, Matrix.sub_mul, orth]
  rw [localSignedObjective,localSignedObjective,ec,ep,cubic_act_frob']

private theorem strainCoordinates_smul' (ref : Reference) (t : ℝ) (S : Mat) :
    strainCoordinates ref (t • S)=t • strainCoordinates ref S := by
  ext i
  fin_cases i <;> simp [strainCoordinates, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv] <;> ring

private theorem strainCoordinates_tensor' (ref : Reference) (v : Point) :
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

theorem stationary (ref : Reference) (w : LocalData) (base : w.Base ref analyticLocalBox)
    (modesOK : ∀ dual, w.ModesDefined dual) (positive : metricPositiveCheck ref w.chart=true)
    (v : Point) : HasDerivAt (fun t : ℝ => localSignedObjective ref (t • v)) 0 0 := by
  let F (S : Mat) := localSignedObjective ref (strainCoordinates ref S)
  have diff (S : Mat) : HasDerivAt (fun t : ℝ => F (t • S)) (tensorDerivative ref S) 0 := by
    simp_rw [F,strainCoordinates_smul']
    exact origin_derivative ref w base modesOK (strainCoordinates ref S)
  have inv (m : CubicMove) (S : Mat) (symm : S.transpose=S) (tr : diagonalSum S=0) :
      tensorDerivative ref (m.act S)=tensorDerivative ref S := by
    obtain ⟨e,he,small⟩ := analyticLocalBox_small_ray' (strainCoordinates ref S)
    have eq : (fun t : ℝ => F (t • S)) =ᶠ[𝓝 0] (fun t : ℝ => F (t • m.act S)) := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr he) he] with t ht
      have symmT : (t • S).transpose=t • S := by simp [Matrix.transpose_smul,symm]
      have traceT : diagonalSum (t • S)=0 := by
        simpa [diagonalSum,Matrix.smul_apply,smul_eq_mul,mul_add] using
          congrArg (fun x : ℝ => t*x) tr
      have h := cubicRay_value_eq' ref w.chart base.chart positive m (t • S) symmT traceT
        (by rw [strainCoordinates_smul']; exact small t ht)
      simpa [F,cubic_act_scale'] using h.symm
    exact ((diff (m.act S)).congr_of_eventuallyEq eq).unique (diff S)
  let S := strainTensor ref v
  have symm : S.transpose=S := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [S,strainTensor,Matrix.transpose_apply]
  have tr : diagonalSum S=0 := by simp [S,strainTensor,diagonalSum]; ring
  have h := diff S
  rw [cubic_invariant_linear_zero_on_strain _ inv S symm tr] at h
  simpa only [F,strainCoordinates_smul',S,strainCoordinates_tensor'] using h

/-! ## Curvature from family enclosures -/

namespace LocalData

def tailRadius (w : LocalData) (i j : Fin 5) : ℚ :=
  familyTailUpper w.radius (w.indexRat false) (w.exponent false) (w.tail false) i j +
    familyTailUpper w.radius (w.indexRat true) (w.exponent true) (w.tail true) i j

end LocalData

/-- The fixed-point Hessian sum of one slab is covered by the proposal `P`. -/
def slabCheck (dual : Bool) (arg : IntVec → FJet) (r : ℕ) (a : ℤ)
    (P : Fin 5 → Fin 5 → FBall) : Bool :=
  match ffold dual arg (slabList r a) fzeroJet with
  | some J => decide (∀ i j, (J.hessian i j).rational.Covers (P i j).rational)
  | none => false

theorem slabCheck_sound (ref : Reference) (dual : Bool) (p : Point) (arg : IntVec → FJet)
    (harg : ∀ n, n ≠ 0 → FRel (arg n) (localArgumentJet ref dual n p)) (r : ℕ) (a : ℤ)
    (P : Fin 5 → Fin 5 → FBall) (h : slabCheck dual arg r a P = true) (i j : Fin 5) :
    (P i j).Contains (((slabList r a).map (fun n => (localModeJet ref dual n p).hessian i j)).sum) := by
  unfold slabCheck at h
  cases hS : ffold dual arg (slabList r a) fzeroJet with
  | none => rw [hS] at h; simp at h
  | some J =>
    rw [hS] at h
    dsimp only at h
    have cov : ∀ i j, (J.hessian i j).rational.Covers (P i j).rational := of_decide_eq_true h
    have rel := ffold_rel ref dual p arg harg (slabList r a) fzeroJet (constant 0 0) J fzeroJet_rel hS
    have e := foldl_combine_hessian (fun n => localModeJet ref dual n p) i j (slabList r a)
      (constant 0 0)
    have c := rel.2.2 i j
    rw [e] at c
    have c' : (J.hessian i j).Contains
        (((slabList r a).map (fun n => (localModeJet ref dual n p).hessian i j)).sum) := by
      simpa [constant] using c
    exact Ball.covers_sound (cov i j) c'

def sideSum (r : ℕ) (P : ℤ → Fin 5 → Fin 5 → FBall) (i j : Fin 5) : FBall :=
  (side r).foldr (fun a acc => (P a i j).add acc) FixedPoint.Ball.zero

theorem listSum_contains (l : List ℤ) (P : ℤ → FBall) (X : ℤ → ℝ)
    (h : ∀ a ∈ l, (P a).Contains (X a)) :
    (l.foldr (fun a acc => (P a).add acc) FixedPoint.Ball.zero).Contains ((l.map X).sum) := by
  induction l with
  | nil => simpa using FixedPoint.Ball.zero_contains
  | cons a t ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact FixedPoint.Ball.add_contains (h a (List.mem_cons_self ..))
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem cube_slab_sum (r : ℕ) (f : IntVec → ℝ) :
    ∑ n ∈ localCube r, f n = ((side r).map (fun a => ((slabList r a).map f).sum)).sum := by
  rw [localCube_sum, cubeList_slabs]
  simp only [List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
  rfl

/-- An enclosure of one family's finite cube sum of mode Hessians on a box. -/
def FamilyHessian (ref : Reference) (dual : Bool) (r : ℕ) (b : Rectangle)
    (H : Fin 5 → Fin 5 → FBall) : Prop :=
  ∀ p, b.Mem p → ∀ i j, (H i j).Contains (∑ n ∈ localCube r, (localModeJet ref dual n p).hessian i j)

theorem FamilyHessian.mono {ref : Reference} {dual : Bool} {r : ℕ} {b b' : Rectangle}
    {H : Fin 5 → Fin 5 → FBall} (h : FamilyHessian ref dual r b H) (sub : ∀ p, b'.Mem p → b.Mem p) :
    FamilyHessian ref dual r b' H :=
  fun p hp => h p (sub p hp)

theorem familyHessian_of_slabs (ref : Reference) (dual : Bool) (r : ℕ) (b : Rectangle)
    (arg : IntVec → FJet)
    (harg : ∀ p, b.Mem p → ∀ n, n ≠ 0 → FRel (arg n) (localArgumentJet ref dual n p))
    (P : ℤ → Fin 5 → Fin 5 → FBall) (hP : ∀ a ∈ side r, slabCheck dual arg r a (P a) = true) :
    FamilyHessian ref dual r b (sideSum r P) := by
  intro p hp i j
  rw [cube_slab_sum]
  exact listSum_contains (side r) (fun a => P a i j) _
    (fun a ha => slabCheck_sound ref dual p arg (harg p hp) r a (P a) (hP a ha) i j)

/-- Family enclosure through Cartesian metric jets checked on the box `b`. -/
theorem cartFamily (ref : Reference) (dual : Bool) (b : Rectangle) (chart : StrainMetricWitness)
    (hc : strainMetricCheck ref b chart = true) (M : Fin 3 → Fin 3 → FJet)
    (cov : ∀ i j, jetCovered (localMetricJetBall ref dual b chart i j) (M i j) = true)
    (root : RootProposal) (hr : cubeRootCheck root (Ball.exact 2) = true)
    (hinv : (root.ball.mul root.ball).invertible) (r : ℕ) (P : ℤ → Fin 5 → Fin 5 → FBall)
    (hP : ∀ a ∈ side r,
      slabCheck dual (cartArg ref dual (FixedPoint.Ball.fromBall (qscaleBall ref dual root)) M) r a (P a) = true) :
    FamilyHessian ref dual r b (sideSum r P) := by
  apply familyHessian_of_slabs ref dual r b _ _ P hP
  intro p hp n _
  apply cartArg_rel ref dual p _ (FixedPoint.Ball.fromBall_contains (qscaleBall_sound ref dual root hr hinv))
  intro i j
  exact jetCovered_rel (cov i j) ((localMetricJets_sound ref b chart hc dual i j).1 p hp)

/-- Both families' tails beyond the cube on a box. -/
def TailControl (ref : Reference) (r : ℕ) (b : Rectangle) (tail : Fin 5 → Fin 5 → ℚ) : Prop :=
  ∀ p, b.Mem p → ∀ i j,
    Summable (fun n => (localModeJet ref false n p).hessian i j) ∧
    Summable (fun n => (localModeJet ref true n p).hessian i j) ∧
    |(∑' n : {n // n ∉ localCube r}, (localModeJet ref false n.val p).hessian i j) +
      (∑' n : {n // n ∉ localCube r}, (localModeJet ref true n.val p).hessian i j)| ≤ (tail i j : ℝ)

theorem TailControl.mono {ref : Reference} {r : ℕ} {b b' : Rectangle} {tail : Fin 5 → Fin 5 → ℚ}
    (h : TailControl ref r b tail) (sub : ∀ p, b'.Mem p → b.Mem p) : TailControl ref r b' tail :=
  fun p hp => h p (sub p hp)

theorem LocalData.tailControl (w : LocalData) {ref : Reference} {b : Rectangle} (base : w.Base ref b) :
    TailControl ref w.radius b w.tailRadius := by
  intro p hp i j
  have tl (dual : Bool) := by
    obtain ⟨ex, tail⟩ := Bool.and_eq_true_iff.mp (base.family dual)
    exact familyTail_sound w.radius ref dual b (w.indexRat dual) (base.index dual) (w.exponent dual)
      (w.exponentFactor dual) (w.tail dual) ex tail p hp i j
  refine ⟨(tl false).1, (tl true).1, ?_⟩
  unfold LocalData.tailRadius
  push_cast
  exact (abs_add_le _ _).trans (add_le_add (tl false).2 (tl true).2)

def penaltyCheck (ref : Reference) (b : Rectangle) (chart : StrainMetricWitness)
    (penalty : Fin 5 → Fin 5 → FBall) : Bool :=
  decide (∀ i j, ((localPenaltyJetBall ref b chart).hessian i j).Covers (penalty i j).rational)

def PenaltyEnclosure (ref : Reference) (b : Rectangle) (penalty : Fin 5 → Fin 5 → FBall) : Prop :=
  ∀ p, b.Mem p → ∀ i j, (penalty i j).Contains ((localPenaltyJet ref p).hessian i j)

theorem PenaltyEnclosure.mono {ref : Reference} {b b' : Rectangle} {penalty : Fin 5 → Fin 5 → FBall}
    (h : PenaltyEnclosure ref b penalty) (sub : ∀ p, b'.Mem p → b.Mem p) :
    PenaltyEnclosure ref b' penalty :=
  fun p hp => h p (sub p hp)

theorem penaltyEnclosure_of_check (ref : Reference) (b : Rectangle) (chart : StrainMetricWitness)
    (hc : strainMetricCheck ref b chart = true) (penalty : Fin 5 → Fin 5 → FBall)
    (pen : penaltyCheck ref b chart penalty = true) : PenaltyEnclosure ref b penalty :=
  fun p hp i j => Ball.covers_sound ((of_decide_eq_true pen : ∀ i j, _) i j)
    (((localPenaltyJet_sound ref b chart hc).1 p hp).2.2 i j)

def curvatureMatrixOf (D U penalty : Fin 5 → Fin 5 → FBall) (tail : Fin 5 → Fin 5 → ℚ) :
    RationalHessian :=
  tailHessian (fun i j => ((D i j).rational.add (U i j).rational).sub (penalty i j).rational) tail

def curvatureOf (D U penalty : Fin 5 → Fin 5 → FBall) (tail : Fin 5 → Fin 5 → ℚ) : Bool :=
  ldlCheck (curvatureMatrixOf D U penalty tail) (rationalLdlProposal (curvatureMatrixOf D U penalty tail))

theorem curvature_of_families (ref : Reference) (b : Rectangle) (r : ℕ)
    (D U : Fin 5 → Fin 5 → FBall) (hD : FamilyHessian ref false r b D)
    (hU : FamilyHessian ref true r b U) (penalty : Fin 5 → Fin 5 → FBall)
    (hpen : PenaltyEnclosure ref b penalty) (tail : Fin 5 → Fin 5 → ℚ) (htail : TailControl ref r b tail)
    (ok : curvatureOf D U penalty tail = true) (p : Point) (hp : b.Mem p) :
    ∀ v : Point, v ≠ 0 → 0 < hessianQuadratic (localSignedHessian ref p) v := by
  intro v hv
  apply ldlCheck_sound (curvatureMatrixOf D U penalty tail) _ ok (localSignedHessian ref p) _ v hv
  intro i j
  obtain ⟨s0, s1, tb⟩ := htail p hp i j
  let Et (dual : Bool) : ℝ := ∑' n : {n // n ∉ localCube r}, (localModeJet ref dual n.val p).hessian i j
  have split0 := s0.sum_add_tsum_subtype_compl (localCube r)
  have split1 := s1.sum_add_tsum_subtype_compl (localCube r)
  have eq : localSignedHessian ref p i j =
      finiteLocalHessian ref (localCube r) p i j + (Et false + Et true) := by
    unfold localSignedHessian finiteLocalHessian
    rw [← split0, ← split1]
    dsimp [Et]
    ring
  have part : (((D i j).rational.add (U i j).rational).sub (penalty i j).rational).Contains
      (finiteLocalHessian ref (localCube r) p i j) :=
    Ball.contains_sub (Ball.contains_add (hD p hp i j) (hU p hp i j)) (hpen p hp i j)
  rw [eq]
  exact withSignedTail_sound part tb

/-! ## Assembly -/

theorem split_sub (b : Rectangle) (axis : Fin 5) (cut : ℚ) (upper : Bool)
    (hcut : b.lo axis ≤ cut ∧ cut ≤ b.hi axis) (p : Point) (h : (split b axis cut upper).Mem p) :
    b.Mem p := by
  intro i
  have hi := h i
  by_cases e : i = axis
  · subst e
    have c1 : (b.lo i : ℝ) ≤ cut := by exact_mod_cast hcut.1
    have c2 : (cut : ℝ) ≤ b.hi i := by exact_mod_cast hcut.2
    cases upper
    · simp [split] at hi
      exact ⟨hi.1, hi.2.trans c2⟩
    · simp [split] at hi
      exact ⟨c1.trans hi.1, hi.2⟩
  · simpa [split, e] using hi

theorem ballRoot_sub_analytic (p : Point) (hp : ballRoot.Mem p) : analyticLocalBox.Mem p := by
  have hb : (0 : ℝ) ≤ (beta : ℝ) := by norm_num [beta]
  intro i
  have h := hp i
  simp only [ballRoot, strainBox, analyticLocalBox] at h ⊢
  fin_cases i <;> simp at h ⊢ <;> constructor <;> push_cast at h ⊢ <;> linarith [h.1, h.2]

theorem nonzeroLocalStrain_of_checks (ref : Reference)
    (wD : LocalData) (baseD : wD.Base ref analyticLocalBox)
    (modesD : ∀ dual, ∀ a ∈ side wD.radius, slabModes dual (fquad (wD.index dual)) wD.radius a = true)
    (positive : metricPositiveCheck ref wD.chart = true)
    (spectral : ref = .bcc → localBccSpectralCheck = true)
    (curvature : ∀ p, ballRoot.Mem p → ∀ v : Point, v ≠ 0 →
      0 < hessianQuadratic (localSignedHessian ref p) v) :
    NonzeroLocalStrain ref := by
  have modesOK : ∀ dual, wD.ModesDefined dual :=
    fun dual => modes_of_slabs dual (fquad (wD.index dual)) wD.radius (modesD dual)
  intro v fold ball nz A hA hG
  have D := signed_differentiation ref analyticLocalBox wD baseD modesOK v 2 (by norm_num)
    (analyticLocalBox_ray v ball)
  have D0 := stationary ref wD baseD modesOK positive v
  have zero : signedRaySlope ref v 0=0 := (D 0 (by norm_num)).1.unique D0
  apply local_strict_of_signed_ray ref v fold ball nz A hA hG spectral (localSignedHessian ref)
    (signedRaySlope ref v) zero
  · exact fun t ht => (D t (localRayInterval_mem ht)).1.continuousAt.continuousWithinAt
  · exact fun t ht => (D t (localRayInterval_mem ht)).2.continuousAt.continuousWithinAt
  · exact fun t ht => (D t (localRayInterval_mem (Set.Ioo_subset_Icc_self ht))).1
  · exact fun t ht => (D t (localRayInterval_mem (Set.Ioo_subset_Icc_self ht))).2
  · exact fun p fold ball => curvature p (ballRoot_contains p fold ball)

end BccSharp.Coulomb.BravaisCover.FixedLocal
