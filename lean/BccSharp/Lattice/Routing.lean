import BccSharp.Lattice.Curvature
import BccSharp.Lattice.CenteredStrain
import BccSharp.Lattice.FccStrain
import BccSharp.Lattice.FccDefect
import BccSharp.Lattice.LdlCurvature
import BccSharp.TwoSite.PrimitiveAnchor

set_option autoImplicit false

/-! Type-directed combination of the addressed Lattice checkers. The
concrete global checker accepts reduction and strict positive-series
leaves. Strain geometry is checked separately from the analytic closure. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage

inductive Payload where
  | reduction (evidence : ReductionWitness)
  | strictSeries (terms : List SeriesTerm)
  | seriesRadius (radius : ℕ)
  | shortEscape
  | strainHandoff
  | excluded
  | inBall
  | intervalHessian (lambda : ℚ) (matrix : RationalHessian)
  | intervalHessianLdl (part : RationalHessian) (tail : RatMatrix 5) (witness : LdlWitness 5)
  | awaitingArithmetic

def globalCheck (a : Address) (route : Route) (w : Payload) (b : Rectangle) : Bool :=
  match a.family, route, w with
  | .global, .reducedFailure, .reduction h => reductionCheck h b
  | .global, .aboveFCC, .strictSeries term => strictSeriesCheck b term
  | .global, .shortVector, .strictSeries term => strictSeriesCheck b term
  | .global, .aboveFCC, .seriesRadius radius => strictRadiusCheck b radius
  | .global, .shortVector, .seriesRadius radius => strictRadiusCheck b radius
  | .global, .shortVector, .shortEscape => shortBoxCheck b
  | _, _, _ => false

theorem globalCheck_sound : AddressedSound globalCheck reduced (fun p => Sharp (primitiveChart p)) := by
  intro a route w b ok p inBox live
  unfold globalCheck at ok
  split at ok
  · exact (reductionCheck_sound _ b ok p inBox live).elim
  · exact strictSeriesCheck_sound b _ ok p inBox
  · exact strictSeriesCheck_sound b _ ok p inBox
  · exact strictRadiusCheck_sound b _ ok p inBox
  · exact strictRadiusCheck_sound b _ ok p inBox
  · exact shortBoxCheck_sound b ok p inBox
  · contradiction

def strainGeometryCheck (ref : Reference) (a : Address) (route : Route) (w : Payload) (b : Rectangle) : Bool :=
  decide (a.family = .strain ref) &&
    match route,w with
    | .outsideStrain,.excluded => strainOutsideCheck ref b
    | .ball,.inBall => insideBallCheck beta beta b
    | _,_ => false

theorem strainGeometryCheck_sound (ref : Reference) :
    AddressedSound (strainGeometryCheck ref) (strainEligible ref) (inProductBall beta beta) := by
  intro a route w b ok p inBox live
  have h := (Bool.and_eq_true_iff.mp ok).2
  split at h
  · exact (strainOutsideCheck_sound ref b h p inBox live).elim
  · exact insideBallCheck_sound beta beta b h p inBox
  · contradiction

def bccStrainCheck (a : Address) (route : Route) (w : Payload) (b : Rectangle) : Bool :=
  match route,w with
  | .strictDefect,.seriesRadius radius =>
      decide (a.family = .strain .bcc) &&
        (strainE2RadiusCheck b radius || centeredBccStrainCheck .strictDefect b radius)
  | .aboveFCC,.seriesRadius radius =>
      decide (a.family = .strain .bcc) &&
        (bccStrainE1RadiusCheck b radius || centeredBccStrainCheck .aboveFCC b radius)
  | _,_ => strainGeometryCheck .bcc a route w b

theorem bccStrainCheck_sound :
    AddressedSound bccStrainCheck (strainEligible .bcc)
      (fun p => inProductBall beta beta p ∨ BccStrainSharp p) := by
  intro a route w b ok p inBox live
  unfold bccStrainCheck at ok
  split at ok
  next radius =>
    rcases Bool.or_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).2 with endpoint | centered
    · exact Or.inr (strainE2RadiusCheck_sound b radius endpoint p inBox).2
    · exact Or.inr (centeredBccStrainCheck_sound .strictDefect b radius centered p inBox)
  next radius =>
    rcases Bool.or_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).2 with endpoint | centered
    · exact Or.inr (bccStrainE1RadiusCheck_sound b radius endpoint p inBox)
    · exact Or.inr (centeredBccStrainCheck_sound .aboveFCC b radius centered p inBox)
  next => exact Or.inl (strainGeometryCheck_sound .bcc a route w b ok p inBox live)

/-- Full check of the supplied BCC spine and its addressed fragments.
The local ball still needs a separate equality proof. -/
theorem bcc_strain_spine_proofs (fragments : List (RootRow Payload)) (spine : AddressedTree Address)
    (checked : spine.check (fragmentCheck bccStrainCheck fragments)
      ⟨.strain .bcc,[0],[]⟩ (strainRoot .bcc) = true)
    (p : Point) (live : strainEligible .bcc p) :
    inProductBall beta beta p ∨ BccStrainSharp p :=
  spine_sound bccStrainCheck_sound fragments spine _ _ checked p (strainRoot_contains .bcc p live) live

def fccStrainCheck (a : Address) (route : Route) (w : Payload) (b : Rectangle) : Bool :=
  match route,w with
  | .aboveFCC,.seriesRadius radius =>
      decide (a.family = .strain .fcc) && fccStrainRadiusCheck b radius
  | _,_ => strainGeometryCheck .fcc a route w b

theorem fccStrainCheck_sound :
    AddressedSound fccStrainCheck (strainEligible .fcc)
      (fun p => inProductBall beta beta p ∨ FccStrainSharp p) := by
  intro a route w b ok p inBox live
  unfold fccStrainCheck at ok
  split at ok
  next radius => exact Or.inr (fccStrainRadiusCheck_sound b radius (Bool.and_eq_true_iff.mp ok).2 p inBox)
  next => exact Or.inl (strainGeometryCheck_sound .fcc a route w b ok p inBox live)

def foldedAtlasCheck : Reference → Address → Route → Payload → Rectangle → Bool
  | .bcc => bccStrainCheck
  | .fcc => fccStrainCheck

def strainSharp (ref : Reference) (w : Point) : Prop :=
  ∀ A : Mat, A.det=1 → gram A=reconstructedMetric ref w → Sharp (strainBasis ref A)

theorem foldedAtlasCheck_sound (ref : Reference) :
    AddressedSound (foldedAtlasCheck ref) (strainEligible ref)
      (fun p => inProductBall beta beta p ∨ strainSharp ref p) := by
  cases ref
  · exact bccStrainCheck_sound
  · exact fccStrainCheck_sound

structure AtlasRows where
  fragments : List (RootRow Payload)
  spine : AddressedTree Address

def AtlasRows.check (atlas : AtlasRows) (ref : Reference) : Bool :=
  atlas.spine.check (fragmentCheck (foldedAtlasCheck ref) atlas.fragments)
    ⟨.strain ref,[0],[]⟩ (strainRoot ref)

/-- The analytic obligation for nonzero local-ball strains. It requires
strict actual deficit, including at the faces of the closed chamber. -/
def NonzeroLocalStrain (ref : Reference) : Prop :=
  ∀ w, folded w → inProductBall beta beta w → w≠0 →
    ∀ A : Mat, A.det=1 → gram A=reconstructedMetric ref w →
    0<oneSiteDeficit (strainBasis ref A)

theorem AtlasRows.sound (atlas : AtlasRows) (ref : Reference) (checked : atlas.check ref=true)
    (hLocal : NonzeroLocalStrain ref) (w : Point) (live : strainEligible ref w) :
    strainSharp ref w := by
  have closed := spine_sound (foldedAtlasCheck_sound ref) atlas.fragments atlas.spine _ _ checked
    w (strainRoot_contains ref w live) live
  rcases closed with ball | sharp
  · intro A hA gramEq
    by_cases zero : w=0
    · rw [zero,reconstructedMetric_zero] at gramEq
      have properA : proper A := ⟨gramEq,hA⟩
      have rigid := strain_origin_rigid ref A properA
      have equality := strain_origin_deficit_zero ref A properA
      refine ⟨equality.ge,fun _ => ?_⟩
      cases ref
      · exact Or.inl rigid
      · exact Or.inr rigid
    · have strict := hLocal w live.1 ball zero A hA gramEq
      exact ⟨strict.le,fun e => (strict.ne' e).elim⟩
  · exact sharp

theorem handoff_fold_to_atlas (ref : Reference) (b : Rectangle) (ok : handoffAnyRegionCheck ref b=true)
    (p : Point) (hp : b.Mem p) (atlas : AtlasRows) (checked : atlas.check ref=true)
    (hLocal : NonzeroLocalStrain ref) : Sharp (primitiveChart p) := by
  obtain ⟨j,into⟩ := handoffAnyRegionCheck_sound ref b ok
  have hc := chartInverses_sound (handoffAnyRegion_chartInverses ref b ok)
  have h₀ : 0<p 0 := (by exact_mod_cast hc.1 : (0 : ℝ)<b.lo 0).trans_le (hp 0).1
  have h₁ : 0<p 1 := (by exact_mod_cast hc.2.1 : (0 : ℝ)<b.lo 1).trans_le (hp 1).1
  let A := handoffMatrix ref j p
  have ha : |A.det|=1 := handoff_unitVolume ref j p h₀.ne' h₁.ne'
  obtain ⟨B,hDet,hFold,hRegion,hGram,hL,hD⟩ := fold_strain_frame ref A ha
    (strainRadiusE ref) strainRadiusT (into p hp)
  have sharp := atlas.sound ref checked hLocal (framePoint ref B) ⟨hFold,hRegion⟩ B hDet hGram
  apply handoff_transferSharp ref j p
  change Sharp (strainBasis ref A)
  unfold Sharp at sharp ⊢
  simpa only [hL,hD] using sharp

def globalWithHandoffsCheck (a : Address) (r : Route) (w : Payload) (b : Rectangle) : Bool :=
  match a.family,r,w with
  | .global,.bccStrain,.strainHandoff => handoffAnyRegionCheck .bcc b
  | .global,.fccStrain,.strainHandoff => handoffAnyRegionCheck .fcc b
  | _,_,_ => globalCheck a r w b

theorem globalWithHandoffsCheck_sound (atlas : Reference → AtlasRows)
    (checked : ∀ ref, (atlas ref).check ref=true) (ballProof : ∀ ref, NonzeroLocalStrain ref) :
    AddressedSound globalWithHandoffsCheck reduced (fun p => Sharp (primitiveChart p)) := by
  intro a r w b ok p hp live
  unfold globalWithHandoffsCheck at ok
  split at ok
  · exact handoff_fold_to_atlas .bcc b ok p hp (atlas .bcc) (checked .bcc) (ballProof .bcc)
  · exact handoff_fold_to_atlas .fcc b ok p hp (atlas .fcc) (checked .fcc) (ballProof .fcc)
  · exact globalCheck_sound a _ _ b ok p hp live

theorem reduced_chart_with_handoffs (g : Grid 16) (ok : g.check globalRoot=true)
    (forest : (Fin 2 → Fin 16) → (Fin 3 → Fin 16) → AddressedTree Payload)
    (checked : ∀ owner suffix, (forest owner suffix).check globalWithHandoffsCheck
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix))=true)
    (atlas : Reference → AtlasRows) (checkedAtlas : ∀ ref, (atlas ref).check ref=true)
    (ballProof : ∀ ref, NonzeroLocalStrain ref)
    (p : Point) (live : reduced p) (h₀ : 0<p 0) (h₁ : 0<p 1)
    (hx : p 2 ∈ Set.Icc (0 : ℝ) (1/2)) (hy : p 3 ∈ Set.Icc (0 : ℝ) (1/2))
    (hz : p 4 ∈ Set.Icc (-1/2 : ℝ) (1/2)) : Sharp (primitiveChart p) := by
  rcases chart_escape_or_root p live h₀ h₁ hx hy hz with strict | root
  · exact strict
  · exact addressed_grid_sound g (by decide) globalRoot ok .global globalWithHandoffsCheck
      (globalWithHandoffsCheck_sound atlas checkedAtlas ballProof)
      forest checked p (globalRoot_contains p root) live

def curvatureGeometryCheck (ref : Reference) (a : Address) (route : Route) (w : Payload) (b : Rectangle) : Bool :=
  decide (a.family = .localBall ref) &&
    match route,w with
    | .outsideStrain,.excluded => foldedOutsideCheck b || outsideBallCheck beta beta b
    | .curvature,.intervalHessian lambda matrix => curvatureCheck lambda matrix
    | .curvature,.intervalHessianLdl part tail factor => ldlCheck (tailHessian part tail) factor
    | _,_ => false

theorem curvatureGeometryCheck_sound (ref : Reference) (M : Point → RealHessian)
    (actual : ∀ a lambda matrix b,
      curvatureGeometryCheck ref a .curvature (.intervalHessian lambda matrix) b = true →
      ∀ p, b.Mem p → ∀ i j, (matrix i j).Contains (M p i j))
    (actualLdl : ∀ a part tail factor b,
      curvatureGeometryCheck ref a .curvature (.intervalHessianLdl part tail factor) b = true →
      ∀ p, b.Mem p → ∀ i j, (tailHessian part tail i j).Contains (M p i j)) :
    AddressedSound (curvatureGeometryCheck ref)
      (fun p => folded p ∧ inProductBall beta beta p)
      (fun p => ∀ v : Point, v ≠ 0 → 0 < hessianQuadratic (M p) v) := by
  intro a route w b ok p inBox live
  have h := (Bool.and_eq_true_iff.mp ok).2
  split at h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact (foldedOutsideCheck_sound b h p inBox live.1).elim
    · exact (outsideBallCheck_sound beta beta b h p inBox live.2).elim
  next lambda matrix =>
    exact fun v hv => curvatureCheck_strict lambda matrix h _ (actual a lambda matrix b ok p inBox) v hv
  next part tail factor =>
    exact fun v hv => ldlCheck_sound (tailHessian part tail) factor h _
      (actualLdl a part tail factor b ok p inBox) v hv
  next => contradiction

theorem local_grid_curvature (ref : Reference) (M : Point → RealHessian)
    (actual : ∀ a lambda matrix b,
      curvatureGeometryCheck ref a .curvature (.intervalHessian lambda matrix) b=true →
      ∀ p, b.Mem p → ∀ i j, (matrix i j).Contains (M p i j))
    (actualLdl : ∀ a part tail factor b,
      curvatureGeometryCheck ref a .curvature (.intervalHessianLdl part tail factor) b=true →
      ∀ p, b.Mem p → ∀ i j, (tailHessian part tail i j).Contains (M p i j))
    (g : Grid 5) (gOK : g.check ballRoot=true)
    (forest : (Fin 2 → Fin 5) → (Fin 3 → Fin 5) → AddressedTree Payload)
    (checked : ∀ owner suffix, (forest owner suffix).check (curvatureGeometryCheck ref)
      (gridAddress (.localBall ref) (Fin.append owner suffix)) (g.box (Fin.append owner suffix))=true)
    (p : Point) (fold : folded p) (ball : inProductBall beta beta p) :
    ∀ v : Point, v≠0 → 0<hessianQuadratic (M p) v :=
  addressed_grid_sound g (by decide) ballRoot gOK (.localBall ref) (curvatureGeometryCheck ref)
    (curvatureGeometryCheck_sound ref M actual actualLdl) forest checked p
    (ballRoot_contains p fold ball) ⟨fold,ball⟩

theorem global_grid_proofs (g : Grid 16) (ok : g.check globalRoot = true)
    (forest : (Fin 2 → Fin 16) → (Fin 3 → Fin 16) → AddressedTree Payload)
    (checked : ∀ owner suffix, (forest owner suffix).check globalCheck
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix)) = true)
    (p : Point) (root : proofRoot p) (live : reduced p) : Sharp (primitiveChart p) :=
  addressed_grid_sound g (by decide) globalRoot ok .global globalCheck globalCheck_sound
    forest checked p (globalRoot_contains p root) live

/-- The short branch precedes the addressed grid for an already reduced
chart. The global grid premise still requires every leaf to close. -/
theorem reduced_chart_proofs (g : Grid 16) (ok : g.check globalRoot = true)
    (forest : (Fin 2 → Fin 16) → (Fin 3 → Fin 16) → AddressedTree Payload)
    (checked : ∀ owner suffix, (forest owner suffix).check globalCheck
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix)) = true)
    (p : Point) (live : reduced p) (h₀ : 0<p 0) (h₁ : 0<p 1)
    (hx : p 2 ∈ Set.Icc (0 : ℝ) (1/2)) (hy : p 3 ∈ Set.Icc (0 : ℝ) (1/2))
    (hz : p 4 ∈ Set.Icc (-1/2 : ℝ) (1/2)) : Sharp (primitiveChart p) := by
  rcases chart_escape_or_root p live h₀ h₁ hx hy hz with sharp | root
  · exact sharp
  · exact global_grid_proofs g ok forest checked p root live

theorem optical_leaf_of_lattice (hLattice : LatticeCase) (q : TwoSite) (hq : q.Valid)
    (f₀ : Vec) (wrap : IntVec) (half : HalfClass f₀) (uniformMargin curvature : ℚ)
    (hCheck : relativeCheck uniformMargin curvature = true)
    (gain : deficit (anchorOf q f₀)+(uniformMargin : ℝ)+
      (curvature : ℝ)*sq (q.basis.mulVec (q.offset-f₀-castVec wrap)) ≤ deficit q) :
    LeafProof q := by
  have hB : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hq.1]; exact isUnit_one)
  exact optical_from_Bravais (bravais_comparison_from_lattice hLattice) q hq
    (Matrix.mulVec_injective_of_isUnit hB) f₀ wrap half uniformMargin curvature hCheck gain

end BccSharp.Coulomb.BravaisCover
