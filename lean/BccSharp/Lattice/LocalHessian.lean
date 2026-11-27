import BccSharp.Lattice.LocalShell

set_option autoImplicit false

/-! Addressed checker for the signed Hessian of the exact local
series. The rectangle in each check is the rectangle decoded from its
address. All entry balls are computed inside the checker. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open StrainJet
open Constants.HighPrecision

def localSignedHessian (ref : Reference) (p : Point) : RealHessian :=
  fun i j => (∑' n, (localModeJet ref false n p).hessian i j) +
    (∑' n, (localModeJet ref true n p).hessian i j) - (localPenaltyJet ref p).hessian i j

structure LocalHessianWitness where
  chart : StrainMetricWitness
  length : RootProposal
  exponentLower : Bool → ℚ
  exponentFactor : Bool → LdlWitness 3
  tail : Bool → Fin 5 → Fin 5 → LocalTailWitness
  propose : Bool → IntVec → Ball → KernelWitness

def LocalHessianWitness.mode (w : LocalHessianWitness) (ref : Reference) (b : Rectangle)
    (dual : Bool) (n : IntVec) : Option (StrainJet Ball) :=
  localModeJetBall ref dual b w.chart w.length (w.propose dual n) n

def LocalHessianWitness.finitePart (w : LocalHessianWitness) (ref : Reference) (b : Rectangle) : RationalHessian :=
  let get (dual : Bool) (n : IntVec) := (w.mode ref b dual n).getD (constant (Ball.exact 0) (Ball.exact 0))
  finiteLocalHessianBall ref b w.chart (localCube checkedLocalRadius) (get false) (get true)

def LocalHessianWitness.tailRadius (w : LocalHessianWitness) (ref : Reference) (b : Rectangle)
    (dual : Bool) : RatMatrix 5 :=
  localFamilyTailUpper (indexJetBall ref dual b w.chart w.length) (w.exponentLower dual) (w.tail dual)

def LocalHessianWitness.matrix (w : LocalHessianWitness) (ref : Reference) (b : Rectangle) : RationalHessian :=
  tailHessian (w.finitePart ref b) (fun i j => w.tailRadius ref b false i j + w.tailRadius ref b true i j)

def LocalHessianWitness.familyCheck (w : LocalHessianWitness) (ref : Reference) (b : Rectangle) (dual : Bool) : Bool :=
  let J := indexJetBall ref dual b w.chart w.length
  exponentCheck J (w.exponentLower dual) (w.exponentFactor dual) &&
    localFamilyTailCheck J (w.exponentLower dual) (w.tail dual)

def LocalHessianWitness.modeCheck (w : LocalHessianWitness) (ref : Reference) (b : Rectangle) (dual : Bool) : Bool :=
  decide (∀ n : ↥(localCube checkedLocalRadius), (w.mode ref b dual n.val).isSome = true)

def LocalHessianWitness.check (w : LocalHessianWitness) (ref : Reference) (b : Rectangle) : Bool :=
  (strainMetricCheck ref b w.chart && cubeRootCheck w.length (Ball.exact 2)) &&
    ((w.modeCheck ref b false && w.modeCheck ref b true) && (w.familyCheck ref b false && w.familyCheck ref b true))

theorem option_getD_sound {α : Type} {o : Option α} (h : o.isSome=true) (x : α) :
    o=some (o.getD x) := by cases o <;> simp_all

theorem LocalHessianWitness.sound (w : LocalHessianWitness) (ref : Reference) (b : Rectangle)
    (ok : w.check ref b=true) (p : Point) (hp : b.Mem p) :
    ∀ i j, (w.matrix ref b i j).Contains (localSignedHessian ref p i j) := by
  obtain ⟨geom,rest⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨chart,scale⟩ := Bool.and_eq_true_iff.mp geom
  obtain ⟨modes,family⟩ := Bool.and_eq_true_iff.mp rest
  have fin (dual : Bool) (n : IntVec) (hn : n ∈ localCube checkedLocalRadius) :
      w.mode ref b dual n = some ((w.mode ref b dual n).getD (constant (Ball.exact 0) (Ball.exact 0))) := by
    have m : w.modeCheck ref b dual=true := by
      cases dual
      · exact (Bool.and_eq_true_iff.mp modes).1
      · exact (Bool.and_eq_true_iff.mp modes).2
    exact option_getD_sound ((of_decide_eq_true m : ∀ n : ↥(localCube checkedLocalRadius), _) ⟨n,hn⟩) _
  have part := finiteLocalHessianBall_sound ref b w.chart chart w.length scale (localCube checkedLocalRadius)
    w.propose _ _ (fin false) (fin true) p hp
  have tail (dual : Bool) (i j : Fin 5) := by
    have f : w.familyCheck ref b dual=true := by
      cases dual
      · exact (Bool.and_eq_true_iff.mp family).1
      · exact (Bool.and_eq_true_iff.mp family).2
    obtain ⟨ex,t⟩ := Bool.and_eq_true_iff.mp f
    exact localFamilyTail_sound ref dual b w.chart w.length chart scale (w.exponentLower dual)
      (w.exponentFactor dual) (w.tail dual) ex t p hp i j
  intro i j
  let E (dual : Bool) : ℝ := ∑' n : {n // n ∉ localCube checkedLocalRadius},
    (localModeJet ref dual n.val p).hessian i j
  have eh : |E false+E true| ≤ ((w.tailRadius ref b false i j+w.tailRadius ref b true i j : ℚ) : ℝ) := by
    push_cast
    exact (abs_add_le _ _).trans (add_le_add (tail false i j).2 (tail true i j).2)
  have split (dual : Bool) := (tail dual i j).1.sum_add_tsum_subtype_compl (localCube checkedLocalRadius)
  have eq : localSignedHessian ref p i j = finiteLocalHessian ref (localCube checkedLocalRadius) p i j+E false+E true := by
    unfold localSignedHessian finiteLocalHessian
    rw [← split false, ← split true]
    dsimp [E]
    ring
  rw [eq, add_assoc]
  exact withSignedTail_sound (part i j) eh

/-- Rational elimination proposes the factor. `ldlCheck` recomputes the
matrix product and rejects singular or negative pivots. -/
def rationalLdlProposal {n : ℕ} (B : BallMatrix n) : LdlWitness n :=
  let A := correctedMidpoint B
  let step (h : LdlWitness n) (k : Fin n) : LdlWitness n :=
    let residual (i : Fin n) := A i k - ∑ j, h.factor i j*h.pivot j*h.factor k j
    let d := residual k
    ⟨fun i j => if j=k then (if i<k then 0 else if i=k then 1 else residual i/d) else h.factor i j,
      fun j => if j=k then d else h.pivot j⟩
  (List.finRange n).foldl step ⟨fun _ _ => 0,fun _ => 0⟩

def pickExponent (J : Fin 3 → Fin 3 → StrainJet Ball) : ℚ :=
  ([2,3/2,1,3/4,1/2,1/4,1/8,1/16] : List ℚ).find? (fun a =>
    exponentCheck J a (rationalLdlProposal (shiftedIndexMetric J a))) |>.getD 0

def automaticLocalTail (a : ℚ) : LocalTailWitness :=
  let r := checkedLocalRadius
  ⟨0,fun k => Constants.expProposal (edgeArgument a (r+1+k)),
    ⟨Constants.expProposal (ratioArgument a r),Constants.expProposal (edgeArgument a r)⟩⟩

def automaticLocalHessian (ref : Reference) (b : Rectangle) : LocalHessianWitness :=
  let chart := automaticStrainMetricFor ref b
  let length := Constants.rootPair 3 2 2 2
  let J := fun dual => indexJetBall ref dual b chart length
  let a := fun dual => pickExponent (J dual)
  ⟨chart,length,a,fun dual => rationalLdlProposal (shiftedIndexMetric (J dual) (a dual)),
    fun dual _ _ => automaticLocalTail (a dual),
    fun dual _ t => if dual then .one (Constants.expProposal t.neg)
      else .half (automaticErfc t.lo) (automaticErfc t.hi) (Constants.expProposal t.neg)⟩

inductive LocalCurvatureRow where
  | excluded
  | diagonal (arithmetic : LocalHessianWitness) (lambda : ℚ)
  | factor (arithmetic : LocalHessianWitness) (factor : LdlWitness 5)
  | automatic

def localCurvatureCheck (ref : Reference) (a : Address) (route : Route) (w : LocalCurvatureRow) (b : Rectangle) : Bool :=
  decide (a.family = .localBall ref) &&
    match route,w with
    | .outsideStrain,.excluded => foldedOutsideCheck b || outsideBallCheck beta beta b
    | .curvature,.diagonal ar margin => ar.check ref b && curvatureCheck margin (ar.matrix ref b)
    | .curvature,.factor ar F => ar.check ref b && ldlCheck (ar.matrix ref b) F
    | .curvature,.automatic =>
      let ar := automaticLocalHessian ref b
      let B := ar.matrix ref b
      ar.check ref b && ldlCheck B (rationalLdlProposal B)
    | _,_ => false

theorem localCurvatureCheck_sound (ref : Reference) : AddressedSound (localCurvatureCheck ref)
    (fun p => folded p ∧ inProductBall beta beta p)
    (fun p => ∀ v : Point, v≠0 → 0<hessianQuadratic (localSignedHessian ref p) v) := by
  intro a route row b ok p hp live
  have h := (Bool.and_eq_true_iff.mp ok).2
  split at h
  · rcases Bool.or_eq_true_iff.mp h with out | out
    · exact (foldedOutsideCheck_sound b out p hp live.1).elim
    · exact (outsideBallCheck_sound beta beta b out p hp live.2).elim
  next ar margin =>
    obtain ⟨hw,hd⟩ := Bool.and_eq_true_iff.mp h
    exact curvatureCheck_strict margin _ hd _ (ar.sound ref b hw p hp)
  next ar F =>
    obtain ⟨hw,hd⟩ := Bool.and_eq_true_iff.mp h
    exact ldlCheck_sound _ F hd _ (ar.sound ref b hw p hp)
  next =>
    obtain ⟨hw,hd⟩ := Bool.and_eq_true_iff.mp h
    exact ldlCheck_sound _ _ hd _ ((automaticLocalHessian ref b).sound ref b hw p hp)
  next => contradiction

theorem computedLocalGrid_curvature (ref : Reference) (g : Grid 5) (gOK : g.check ballRoot=true)
    (forest : (Fin 2 → Fin 5) → (Fin 3 → Fin 5) → AddressedTree LocalCurvatureRow)
    (checked : ∀ owner suffix, (forest owner suffix).check (localCurvatureCheck ref)
      (gridAddress (.localBall ref) (Fin.append owner suffix)) (g.box (Fin.append owner suffix))=true)
    (p : Point) (fold : folded p) (ball : inProductBall beta beta p) :
    ∀ v : Point, v≠0 → 0<hessianQuadratic (localSignedHessian ref p) v :=
  addressed_grid_sound g (by decide) ballRoot gOK (.localBall ref) (localCurvatureCheck ref)
    (localCurvatureCheck_sound ref) forest checked p (ballRoot_contains p fold ball) ⟨fold,ball⟩

end BccSharp.Coulomb.BravaisCover
