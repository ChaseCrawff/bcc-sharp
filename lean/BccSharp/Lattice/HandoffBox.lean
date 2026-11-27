import BccSharp.Lattice.StrainE2

set_option autoImplicit false

/-! SB/SF image enclosure for the fixed representatives. It checks
membership in the invariant strain region before any cubic symmetry fold. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

def handoffGammaInverseZ : Reference → Fin 2 → Matrix (Fin 3) (Fin 3) ℤ
  | .bcc, _ => !![-1,0,0;0,-1,-1;1,-1,0]
  | .fcc, j => if j=0 then !![0,-1,-1;-1,0,0;0,0,1]
    else !![0,-1,0;-1,0,0;0,0,-1]

theorem handoffGammaInverse_eq (ref : Reference) (j : Fin 2) :
    (toRealMatrix (handoffGamma ref j))⁻¹ =
      toRealMatrix (handoffGammaInverseZ ref j) := by
  apply Matrix.inv_eq_right_inv
  ext r c
  cases ref <;> fin_cases j <;> fin_cases r <;> fin_cases c <;>
    norm_num [handoffGamma,toRealMatrix,handoffGammaInverseZ,Matrix.map_apply,Matrix.mul_apply,
      Fin.sum_univ_three,Matrix.one_apply]

private theorem gammaInverse_left (ref : Reference) (j : Fin 2) :
    toRealMatrix (handoffGammaInverseZ ref j)*toRealMatrix (handoffGamma ref j)=1 := by
  ext r c
  cases ref <;> fin_cases j <;> fin_cases r <;> fin_cases c <;>
    norm_num [handoffGamma,toRealMatrix,handoffGammaInverseZ,Matrix.map_apply,Matrix.mul_apply,
      Fin.sum_univ_three,Matrix.one_apply]

private theorem castIndex_mul (G : Matrix (Fin 3) (Fin 3) ℤ) (n : IntVec) :
    castVec (G.mulVec n)=(toRealMatrix G).mulVec (castVec n) := by
  funext i
  simp [toRealMatrix,Matrix.mulVec,dotProduct,Matrix.map_apply,castVec]

theorem handoffBasis_eq (ref : Reference) (j : Fin 2) (p : Point) :
    handoffMatrix ref j p*cubicBasis ref=
      normalizedChart p*toRealMatrix (handoffGammaInverseZ ref j) := by
  have hu : IsUnit (cubicBasis ref).det := isUnit_iff_ne_zero.mpr (by
    intro e
    have h := cubicBasis_unitVolume ref
    simp [volumeOf,e] at h)
  rw [handoffMatrix,mul_assoc,Matrix.nonsing_inv_mul _ hu,mul_one,handoffGammaInverse_eq]

theorem handoff_sameLattice (ref : Reference) (j : Fin 2) (p : Point) :
    lattice (Constants.fccLength⁻¹ • (handoffMatrix ref j p*cubicBasis ref)) =
      lattice (primitiveChart p) := by
  rw [handoffBasis_eq,← smul_mul_assoc]
  change lattice (primitiveChart p*toRealMatrix (handoffGammaInverseZ ref j))=_
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    refine ⟨(handoffGammaInverseZ ref j).mulVec n,?_⟩
    dsimp only
    rw [castIndex_mul,Matrix.mulVec_mulVec]
  · rintro ⟨n,rfl⟩
    refine ⟨(handoffGamma ref j).mulVec n,?_⟩
    dsimp only
    rw [castIndex_mul,Matrix.mulVec_mulVec,mul_assoc,gammaInverse_left,mul_one]

theorem handoff_sameDefect (ref : Reference) (j : Fin 2) (p : Point) :
    oneSiteDefect (Constants.fccLength⁻¹ • (handoffMatrix ref j p*cubicBasis ref)) =
      oneSiteDefect (primitiveChart p) := by
  unfold oneSiteDefect
  rw [handoff_sameLattice]

private theorem gammaInverse_indices (ref : Reference) (j : Fin 2) :
    handoffGammaInverseZ ref j*handoffGamma ref j=1 ∧
      handoffGamma ref j*handoffGammaInverseZ ref j=1 := by
  constructor <;> ext r c <;> cases ref <;> fin_cases j <;> fin_cases r <;> fin_cases c <;>
    norm_num [handoffGamma,handoffGammaInverseZ,Matrix.mul_apply,Fin.sum_univ_three,Matrix.one_apply]

private def rebaseIndices (G H : Matrix (Fin 3) (Fin 3) ℤ) (h₁ : H*G=1) (h₂ : G*H=1) :
    IntVec ≃ IntVec where
  toFun := G.mulVec
  invFun := H.mulVec
  left_inv n := by rw [Matrix.mulVec_mulVec,h₁,Matrix.one_mulVec]
  right_inv n := by rw [Matrix.mulVec_mulVec,h₂,Matrix.one_mulVec]

private theorem rebaseIndex_zero (G H : Matrix (Fin 3) (Fin 3) ℤ) (h₁ : H*G=1) (h₂ : G*H=1)
    (n : IntVec) : rebaseIndices G H h₁ h₂ n=0 ↔ n=0 := by
  have e : rebaseIndices G H h₁ h₂ 0=0 := Matrix.mulVec_zero G
  constructor
  · intro h
    exact (rebaseIndices G H h₁ h₂).injective (h.trans e.symm)
  · rintro rfl
    exact e

private theorem realProduct_one (G H : Matrix (Fin 3) (Fin 3) ℤ) (h : G*H=1) :
    toRealMatrix G*toRealMatrix H=1 := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp [toRealMatrix,Matrix.map_apply,Matrix.mul_apply,Matrix.one_apply] at e ⊢
  by_cases h : i=j <;> simpa [h] using (congrArg (fun z : ℤ => (z : ℝ)) e)

theorem rebase_sameLattice (B : Mat) (H G : Matrix (Fin 3) (Fin 3) ℤ) (hg : H*G=1) :
    lattice (B*toRealMatrix H)=lattice B := by
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    refine ⟨H.mulVec n,?_⟩
    dsimp only
    rw [castIndex_mul,Matrix.mulVec_mulVec]
  · rintro ⟨n,rfl⟩
    refine ⟨G.mulVec n,?_⟩
    dsimp only
    rw [castIndex_mul,Matrix.mulVec_mulVec,mul_assoc,realProduct_one H G hg,mul_one]

theorem regularSelf_rebase (α : ℝ) (B : Mat) (H G : Matrix (Fin 3) (Fin 3) ℤ)
    (hg : H*G=1) (gh : G*H=1) :
    ewaldRegularSelf α (B*toRealMatrix H)=ewaldRegularSelf α B := by
  let C := B*toRealMatrix H
  let direct := rebaseIndices H G gh hg
  have h₁ : H.transpose*G.transpose=1 := by rw [← Matrix.transpose_mul,gh,Matrix.transpose_one]
  have h₂ : G.transpose*H.transpose=1 := by rw [← Matrix.transpose_mul,hg,Matrix.transpose_one]
  let dual := rebaseIndices G.transpose H.transpose h₁ h₂
  have hDirect (n : IntVec) : linearImage C n=linearImage B (direct n) := by
    unfold C linearImage
    change (B*toRealMatrix H).mulVec (castVec n)=B.mulVec (castVec (H.mulVec n))
    rw [castIndex_mul,Matrix.mulVec_mulVec]
  have hDual (n : IntVec) : dualWave C n=dualWave B (dual n) := by
    have invH : (toRealMatrix H)⁻¹=toRealMatrix G :=
      Matrix.inv_eq_right_inv (realProduct_one H G hg)
    unfold C dualWave
    rw [Matrix.mul_inv_rev,invH,Matrix.transpose_mul,← Matrix.mulVec_mulVec]
    change _ = (2*Real.pi) • (B⁻¹).transpose.mulVec (castVec (G.transpose.mulVec n))
    rw [castIndex_mul]
    rfl
  have hZn : H.det*G.det=1 := by
    rw [← Matrix.det_mul,hg,Matrix.det_one]
  have hZ : H.det=1 ∨ H.det=-1 := Int.eq_one_or_neg_one_of_mul_eq_one hZn
  have hH : |(toRealMatrix H).det|=1 := by
    have hcast : (toRealMatrix H).det=((H.det : ℤ) : ℝ) := ((Int.castRingHom ℝ).map_det H).symm
    rw [hcast]
    rcases hZ with e | e <;> rw [e] <;> norm_num
  have hvol : volumeOf C=volumeOf B := by
    unfold C volumeOf
    rw [Matrix.det_mul,abs_mul,hH,mul_one]
  have hReal (n : IntVec) :
      (if n=0 then 0 else screened α (linearImage C n)) =
        if direct n=0 then 0 else screened α (linearImage B (direct n)) := by
    have hz : direct n=0 ↔ n=0 := rebaseIndex_zero H G gh hg n
    by_cases hn : n=0
    · rw [ite_eq_left hn,ite_eq_left (hz.mpr hn)]
    · rw [ite_eq_right hn,ite_eq_right (fun h => hn (hz.mp h)),hDirect]
  have hReciprocal (n : IntVec) :
      reciprocalGreenTerm α C n=reciprocalGreenTerm α B (dual n) := by
    unfold reciprocalGreenTerm
    dsimp only
    have hz : dual n=0 ↔ n=0 := rebaseIndex_zero G.transpose H.transpose h₁ h₂ n
    by_cases hn : n=0
    · rw [ite_eq_left hn,ite_eq_left (hz.mpr hn)]
    · rw [ite_eq_right hn,ite_eq_right (fun h => hn (hz.mp h)),hDual]
  have hDirectSum : (∑' n : IntVec, if direct n=0 then 0 else screened α (linearImage B (direct n))) =
      ∑' n : IntVec, if n=0 then 0 else screened α (linearImage B n) :=
    direct.tsum_eq (fun m : IntVec => if m=0 then 0 else screened α (linearImage B m))
  have hDualSum : (∑' n : IntVec, reciprocalGreenTerm α B (dual n)) =
      ∑' n : IntVec, reciprocalGreenTerm α B n :=
    dual.tsum_eq (reciprocalGreenTerm α B)
  change ewaldRegularSelf α C = _
  unfold ewaldRegularSelf greenBackground
  rw [hvol]
  simp_rw [hReal,hReciprocal]
  rw [hDirectSum,hDualSum]

theorem oneSiteEnergy_rebase (B : Mat) (H G : Matrix (Fin 3) (Fin 3) ℤ)
    (hg : H*G=1) (gh : G*H=1) : oneSiteEnergy (B*toRealMatrix H)=oneSiteEnergy B := by
  simp only [oneSite_energy_is_self]
  rw [← smul_mul_assoc,regularSelf_rebase _ _ H G hg gh]

theorem handoff_sameEnergy (ref : Reference) (j : Fin 2) (p : Point) :
    oneSiteEnergy (Constants.fccLength⁻¹ • (handoffMatrix ref j p*cubicBasis ref)) =
      oneSiteEnergy (primitiveChart p) := by
  rw [handoffBasis_eq,← smul_mul_assoc]
  change oneSiteEnergy (primitiveChart p*toRealMatrix (handoffGammaInverseZ ref j))=_
  have g := gammaInverse_indices ref j
  exact oneSiteEnergy_rebase _ _ _ g.1 g.2

theorem handoff_transferSharp (ref : Reference) (j : Fin 2) (p : Point)
    (h : Sharp (Constants.fccLength⁻¹ • (handoffMatrix ref j p*cubicBasis ref))) :
    Sharp (primitiveChart p) := by
  unfold Sharp oneSiteDeficit at h ⊢
  simpa only [handoff_sameEnergy, handoff_sameDefect, handoff_sameLattice] using h

def cubicInverseQ : Reference → Matrix (Fin 3) (Fin 3) ℚ
  | .bcc => !![1,0,-1;0,1,-1;0,0,2]
  | .fcc => !![1/2,1/2,-1/2;1/2,-1/2,1/2;-1/2,1/2,1/2]

theorem cubicInverse_eq (ref : Reference) :
    (cubicBasis ref)⁻¹ = (match ref with | .bcc => Constants.fccLength⁻¹ | .fcc => Constants.fccLength) •
      (show Mat from fun i j => (cubicInverseQ ref i j : ℝ)) := by
  have ht : Constants.fccLength≠0 := by unfold Constants.fccLength; positivity
  apply Matrix.inv_eq_right_inv
  cases ref
  · change (Constants.fccLength • (!![1,0,1/2; 0,1,1/2; 0,0,1/2] : Mat)) *
        (Constants.fccLength⁻¹ • (show Mat from fun i j => (cubicInverseQ .bcc i j : ℝ))) = 1
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ ht,one_smul]
    ext r c
    rw [Matrix.mul_apply,Fin.sum_univ_three]
    fin_cases r <;> fin_cases c <;> norm_num [cubicInverseQ,Matrix.one_apply]
  · change (Constants.fccLength⁻¹ • (!![1,1,0; 1,0,1; 0,1,1] : Mat)) *
        (Constants.fccLength • (show Mat from fun i j => (cubicInverseQ .fcc i j : ℝ))) = 1
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,inv_mul_cancel₀ ht,one_smul]
    ext r c
    rw [Matrix.mul_apply,Fin.sum_univ_three]
    fin_cases r <;> fin_cases c <;> norm_num [cubicInverseQ,Matrix.one_apply]

private def chartBasisBall (b : Rectangle) : MetricBalls :=
  let c := coordinateBall b
  ![![c 0,(c 0).mul (c 2),(c 0).mul (c 3)],
    ![Ball.exact 0,c 1,(c 1).mul (c 4)], ![Ball.exact 0,Ball.exact 0,((c 0).mul (c 1)).inv]]

private theorem chartBasisBall_sound (b : Rectangle) (ok : chartInversesCheck b=true)
    (p : Point) (hp : b.Mem p) : (chartBasisBall b).Contains (normalizedChart p) := by
  have c := coordinateBall_sound hp
  have h₁ := Ball.contains_mul (c 0) (c 2)
  have h₂ := Ball.contains_mul (c 0) (c 3)
  have h₃ := Ball.contains_mul (c 1) (c 4)
  have h₄ := Ball.contains_inv (chartInverses_sound ok).2.2.2.2
    (Ball.contains_mul (c 0) (c 1))
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    first
    | simpa [chartBasisBall,normalizedChart,chartBasis,coordLift] using c 0
    | simpa [chartBasisBall,normalizedChart,chartBasis,coordLift] using c 1
    | simpa [chartBasisBall,normalizedChart,chartBasis,coordLift] using h₁
    | simpa [chartBasisBall,normalizedChart,chartBasis,coordLift] using h₂
    | simpa [chartBasisBall,normalizedChart,chartBasis,coordLift] using h₃
    | simpa [chartBasisBall,normalizedChart,chartBasis,coordLift] using h₄
    | simpa [chartBasisBall,normalizedChart,chartBasis,coordLift] using Ball.contains_exact 0

private def matMulBall (B C : MetricBalls) : MetricBalls :=
  fun i j => Constants.sumBalls Finset.univ (fun k => (B i k).mul (C k j))

private theorem matMulBall_sound {B C : MetricBalls} {M N : Mat}
    (hB : B.Contains M) (hC : C.Contains N) : (matMulBall B C).Contains (M*N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Constants.sumBalls_sound _ _ _ (fun k _ => Ball.contains_mul (hB i k) (hC k j))

private def gammaInverseBall (ref : Reference) (j : Fin 2) : MetricBalls :=
  fun i k => Ball.exact (handoffGammaInverseZ ref j i k : ℚ)

private theorem gammaInverseBall_sound (ref : Reference) (j : Fin 2) :
    (gammaInverseBall ref j).Contains (toRealMatrix (handoffGamma ref j))⁻¹ := by
  rw [handoffGammaInverse_eq]
  intro i k
  simpa [gammaInverseBall,toRealMatrix,Matrix.map_apply] using
    (Ball.contains_exact (handoffGammaInverseZ ref j i k : ℚ))

private def cubicInverseBall (ref : Reference) (w : RootProposal) : MetricBalls :=
  let s := match ref with | .bcc => w.ball.inv | .fcc => w.ball
  fun i j => s.mul (Ball.exact (cubicInverseQ ref i j))

private theorem cubicInverseBall_sound (ref : Reference) (w : RootProposal)
    (ok : cubeRootCheck w (Ball.exact 2)=true) :
    (cubicInverseBall ref w).Contains (cubicBasis ref)⁻¹ := by
  have hw : w.ball.Contains Constants.fccLength :=
    cubeRoot_sound w (Ball.exact 2) 2 (by norm_num) (Ball.contains_exact 2) ok
  have hs := Ball.contains_inv (cubeRoot_invertible w _ ok) hw
  rw [cubicInverse_eq]
  intro i j
  cases ref
  · exact Ball.contains_mul hs (Ball.contains_exact _)
  · exact Ball.contains_mul hw (Ball.contains_exact _)

private def handoffGramBall (ref : Reference) (j : Fin 2) (b : Rectangle) (w : RootProposal) :
    MetricBalls :=
  let A := matMulBall (matMulBall (chartBasisBall b) (gammaInverseBall ref j)) (cubicInverseBall ref w)
  matMulBall (fun i k => A k i) A

private theorem handoffGramBall_sound (ref : Reference) (j : Fin 2) (b : Rectangle)
    (w : RootProposal) (hB : chartInversesCheck b=true) (hW : cubeRootCheck w (Ball.exact 2)=true)
    (p : Point) (hp : b.Mem p) :
    (handoffGramBall ref j b w).Contains (gram (handoffMatrix ref j p)) := by
  have hA := matMulBall_sound
    (matMulBall_sound (chartBasisBall_sound b hB p hp) (gammaInverseBall_sound ref j))
    (cubicInverseBall_sound ref w hW)
  exact matMulBall_sound (fun i k => hA k i) hA

private def traceBall (G : MetricBalls) : Ball := ((G 0 0).add (G 1 1)).add (G 2 2)

private def handoffStrainBall (G : MetricBalls) : MetricBalls :=
  let s := (Ball.exact 3).mul (traceBall G).inv
  fun i j => (s.mul (G i j)).sub (Ball.exact (if i=j then 1 else 0))

private theorem handoffStrainBall_sound {G : MetricBalls} {C : Mat}
    (h : G.Contains C) (ht : (traceBall G).invertible) :
    (handoffStrainBall G).Contains (normalizedStrain C) := by
  have tr : (traceBall G).Contains (diagonalSum C) :=
    Ball.contains_add (Ball.contains_add (h 0 0) (h 1 1)) (h 2 2)
  have s := Ball.contains_mul (Ball.contains_exact 3) (Ball.contains_inv ht tr)
  intro i j
  have e := Ball.contains_sub (Ball.contains_mul s (h i j)) (Ball.contains_exact (if i=j then 1 else 0))
  by_cases ij : i=j <;> simpa [handoffStrainBall,normalizedStrain,Matrix.sub_apply,Matrix.one_apply,
    Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,ij] using e

structure HandoffRoots where
  cubic : RootProposal
  sqrt₂ : RootProposal
  sqrt₆ : RootProposal

private def handoffCoordinateBall (ref : Reference) (S : MetricBalls) (roots : HandoffRoots) :
    Fin 5 → Ball :=
  let e (r : RootProposal) := (Ball.exact (whitenE ref)).inv.mul r.ball.inv
  let t := (Ball.exact (whitenT ref)).inv.mul roots.sqrt₂.ball
  ![((S 0 0).sub (S 1 1)).mul (e roots.sqrt₂),
    (((S 0 0).add (S 1 1)).sub ((Ball.exact 2).mul (S 2 2))).mul (e roots.sqrt₆),
    t.mul (S 0 1),t.mul (S 0 2),t.mul (S 1 2)]

private theorem handoffCoordinateBall_sound (ref : Reference) (G : MetricBalls) (S : Mat)
    (roots : HandoffRoots) (hS : G.Contains S)
    (h2 : roots.sqrt₂.check (Ball.exact 2)=true) (h6 : roots.sqrt₆.check (Ball.exact 6)=true)
    (i : Fin 5) : (handoffCoordinateBall ref G roots i).Contains (strainCoordinates ref S i) := by
  have e : (Ball.exact (whitenE ref)).invertible := by
    cases ref <;> norm_num [Ball.invertible,Ball.exact,whitenE]
  have t : (Ball.exact (whitenT ref)).invertible := by
    cases ref <;> norm_num [Ball.invertible,Ball.exact,whitenT]
  have ei := Ball.contains_inv e (Ball.contains_exact (whitenE ref))
  have ti := Ball.contains_inv t (Ball.contains_exact (whitenT ref))
  have s2 := RootProposal.sound roots.sqrt₂ _ 2 (by norm_num) (Ball.contains_exact 2) h2
  have s2i := RootProposal.inverse_sound roots.sqrt₂ _ 2 (by norm_num) (Ball.contains_exact 2) h2
  have s6i := RootProposal.inverse_sound roots.sqrt₆ _ 6 (by norm_num) (Ball.contains_exact 6) h6
  have ns2 : Real.sqrt 2≠0 := by positivity
  have ns6 : Real.sqrt 6≠0 := by positivity
  have ne : (whitenE ref : ℝ)≠0 := by cases ref <;> norm_num [whitenE]
  have nt : (whitenT ref : ℝ)≠0 := by cases ref <;> norm_num [whitenT]
  have r₀ := Ball.contains_mul (Ball.contains_sub (hS 0 0) (hS 1 1)) (Ball.contains_mul ei s2i)
  have r₁ := Ball.contains_mul (Ball.contains_sub (Ball.contains_add (hS 0 0) (hS 1 1))
    (Ball.contains_mul (Ball.contains_exact 2) (hS 2 2))) (Ball.contains_mul ei s6i)
  have r₂ := Ball.contains_mul (Ball.contains_mul ti s2) (hS 0 1)
  have r₃ := Ball.contains_mul (Ball.contains_mul ti s2) (hS 0 2)
  have r₄ := Ball.contains_mul (Ball.contains_mul ti s2) (hS 1 2)
  fin_cases i
  · convert r₀ using 1 <;> simp [handoffCoordinateBall,strainCoordinates]
    field_simp [ns2,ne]
  · convert r₁ using 1 <;> simp [handoffCoordinateBall,strainCoordinates]
    field_simp [ns6,ne]
  · convert r₂ using 1 <;> simp [handoffCoordinateBall,strainCoordinates]
    field_simp [nt]
  · convert r₃ using 1 <;> simp [handoffCoordinateBall,strainCoordinates]
    field_simp [nt]
  · convert r₄ using 1 <;> simp [handoffCoordinateBall,strainCoordinates]
    field_simp [nt]

def handoffRegionCheck (ref : Reference) (j : Fin 2) (b : Rectangle) (roots : HandoffRoots) : Bool :=
  let G := handoffGramBall ref j b roots.cubic
  let w := handoffCoordinateBall ref (handoffStrainBall G) roots
  ((chartInversesCheck b && cubeRootCheck roots.cubic (Ball.exact 2)) &&
    (roots.sqrt₂.check (Ball.exact 2) && roots.sqrt₆.check (Ball.exact 6))) &&
  (decide (traceBall G).invertible &&
    insideBallCheck (strainRadiusE ref) strainRadiusT ⟨fun i => (w i).lo,fun i => (w i).hi⟩)

theorem handoffRegionCheck_sound (ref : Reference) (j : Fin 2) (b : Rectangle) (roots : HandoffRoots)
    (ok : handoffRegionCheck ref j b roots=true) (p : Point) (hp : b.Mem p) :
    inProductBall (strainRadiusE ref) strainRadiusT (handoffImage ref j p) := by
  have h := Bool.and_eq_true_iff.mp ok
  have h₀ := Bool.and_eq_true_iff.mp h.1
  have hc := Bool.and_eq_true_iff.mp h₀.1
  have hs := Bool.and_eq_true_iff.mp h₀.2
  have ht := Bool.and_eq_true_iff.mp h.2
  have hG := handoffGramBall_sound ref j b roots.cubic hc.1 hc.2 p hp
  have hS := handoffStrainBall_sound hG (of_decide_eq_true ht.1)
  apply insideBallCheck_sound (strainRadiusE ref) strainRadiusT _ ht.2
  intro i
  have hi := handoffCoordinateBall_sound ref _ _ roots hS hs.1 hs.2 i
  simpa [handoffImage,Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints _ _).mp hi

private def automaticHandoffRoots : HandoffRoots :=
  ⟨Constants.rootPair 3 2 2 2,Constants.rootPair 2 2 2 2,Constants.rootPair 2 6 6 3⟩

def handoffAnyRegionCheck (ref : Reference) (b : Rectangle) : Bool :=
  handoffRegionCheck ref 0 b automaticHandoffRoots ||
    handoffRegionCheck ref 1 b automaticHandoffRoots

theorem handoffAnyRegionCheck_sound (ref : Reference) (b : Rectangle)
    (ok : handoffAnyRegionCheck ref b=true) :
    ∃ j : Fin 2, ∀ p, b.Mem p → inProductBall (strainRadiusE ref) strainRadiusT (handoffImage ref j p) := by
  rcases Bool.or_eq_true_iff.mp ok with h | h
  · exact ⟨0,handoffRegionCheck_sound ref 0 b automaticHandoffRoots h⟩
  · exact ⟨1,handoffRegionCheck_sound ref 1 b automaticHandoffRoots h⟩

theorem handoffAnyRegion_chartInverses (ref : Reference) (b : Rectangle)
    (ok : handoffAnyRegionCheck ref b=true) : chartInversesCheck b=true := by
  rcases Bool.or_eq_true_iff.mp ok with h | h
  · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1
  · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1

end BccSharp.Coulomb.BravaisCover
