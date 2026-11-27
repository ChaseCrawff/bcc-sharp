import BccSharp.TwoSite.Reduction
import BccSharp.TwoSite.ReferenceKernels
import BccSharp.TwoSite.ReferencePoints
import BccSharp.TwoSite.PrimitiveAnchor
import BccSharp.TwoSite.Star

set_option autoImplicit false

/-! Dependencies and final chart assembly. Filling the named fields
requires replaying the matching geometry and analytic certificate families. -/

noncomputable section
namespace BccSharp.Coulomb
namespace CompactCover

abbrev Region := Set Chart
abbrev chartRoot : Region := {p | root.Mem p}
def cellUnion (cells : List AddressedCell) : Region := {p | Held cells p}

inductive Phase where
  | directRoute | stage2 | stage3a | stage3b | stage3c | stage3d | stage3e | stage3f | stage3g | stage3h
  | stage3 | stage4 | stage5a | stage5b | stage6 | corner_halfShift | jointDeficit_planarFibre | continuation_r1 | planarAnchor
  deriving DecidableEq, Repr

def prefixOrder : List Phase :=
  [.directRoute, .stage2, .stage3a, .stage3b, .stage3c, .stage3d, .stage3e, .stage3f, .stage3g, .stage3h,
   .stage3, .stage4, .stage5a, .stage5b, .stage6, .corner_halfShift, .jointDeficit_planarFibre, .continuation_r1]

/-- Lattice supplies the exact anchor classification for Stage5b and PlanarAnchor.
The supplied gain still has to be proved on the addressed source cell. -/
theorem relativeOptical_route_of_lattice (latticeCase : LatticeCase) (p : Chart)
    (valid : (chartPoint p).Valid) (f₀ : Vec) (n : IntVec) (half : HalfClass f₀)
    (margin curvature : ℚ) (ok : relativeCheck margin curvature = true)
    (gain : deficit (anchorOf (chartPoint p) f₀)+(margin : ℝ)+
      (curvature : ℝ)*sq ((chartPoint p).basis.mulVec ((chartPoint p).offset-f₀-castVec n)) ≤
        deficit (chartPoint p)) : Route.result .relativeOptical p := by
  let q := chartPoint p
  have h := bravais_comparison_from_lattice latticeCase (anchorOf q f₀) (anchor_valid q valid f₀ half) half
  have a : 0 ≤ margin ∧ 0 < curvature := of_decide_eq_true ok
  have am : (0 : ℝ) ≤ margin := by exact_mod_cast a.1
  have acurv : (0 : ℝ) < curvature := by exact_mod_cast a.2
  have hu : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [valid.1]; exact isUnit_one)
  change OpticalEvidence q
  refine ⟨f₀,n,(curvature : ℝ),half,acurv,h.1,by linarith,?_⟩
  intro hzero hdisp
  have points := zero_displacement_same_points q f₀ n (Matrix.mulVec_injective_of_isUnit hu) hdisp
  simpa only [IsBCC,IsFCC,points] using h.2 hzero

structure CoverLink where
  phase : Phase
  before : Region
  after : Region
  sound : Handoff before after

def Chain : Region → List CoverLink → Region → Prop
  | start, [], stop => start = stop
  | start, link :: later, stop => start = link.before ∧ Chain link.after later stop

theorem Chain.sound (start : Region) (links : List CoverLink) (stop : Region)
    (h : Chain start links stop) : Handoff start stop := by
  induction links generalizing start with
  | nil =>
      change start = stop at h
      subst stop
      exact fun p hMem _ => Or.inr hMem
  | cons link later ih =>
      change start = link.before ∧ Chain link.after later stop at h
      rw [h.1]
      exact Handoff.trans link.sound (ih link.after h.2)

/-- First Continuation round's full complement is the entrance to the short PlanarAnchor
route. This ties the abstract region chain to the exact addressed list. -/
structure ShortRoute where
  links : List CoverLink
  order : links.map CoverLink.phase = prefixOrder
  planarAnchorInput : List AddressedCell
  prefixChain : Chain chartRoot links (cellUnion planarAnchorInput)
  planarAnchorJobs : List RootTrace
  planarAnchorCheck : WitnessRef → Cell → Bool
  planarAnchorCheckSound : SoundCheck planarAnchorCheck
  closed : runStage planarAnchorCheck planarAnchorInput planarAnchorJobs = some []

theorem ShortRoute.onChart (cert : ShortRoute) (p : Chart) (hRoot : inRoot p)
    (valid : good p) : LeafProof (chartPoint p) := by
  have h := Chain.sound chartRoot cert.links (cellUnion cert.planarAnchorInput) cert.prefixChain
  rcases h p ((inRoot_iff p).mp hRoot) valid with w | openCell
  · exact w
  · exact chain_zero_holds cert.planarAnchorCheckSound [cert.planarAnchorJobs] cert.planarAnchorInput
      (by simp [runChain, cert.closed]) p valid openCell

end CompactCover

/-- Analytic transport of the reduced point-set equality cases. The actual
orientation, basis and wrapping facts are recorded by the representative. -/
def ReducedEqualityTransport : Prop :=
  ∀ q p, ReducedRepresentative q p →
    (IsBCC (chartPoint p) ∨ IsFCC (chartPoint p)) → IsBCC q ∨ IsFCC q

theorem rigidCopy_trans {A B C : Set Vec} (hAB : rigidCopy A B) (hBC : rigidCopy B C) :
    rigidCopy A C := by
  obtain ⟨v,U,hU,hA⟩ := hAB
  obtain ⟨w,V,hV,hB⟩ := hBC
  refine ⟨v+U.mulVec w, U*V, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc U.transpose U V, hU.1, one_mul, hV.1]
  · rw [Matrix.det_mul, hU.2, hV.2, mul_one]
  rw [hA,hB]
  ext x
  constructor
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
    rcases hy with ⟨_,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨(U*V).mulVec z,⟨z,hz,rfl⟩,?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨U.mulVec (V.mulVec z+w),⟨V.mulVec z+w,⟨V.mulVec z,⟨z,hz,rfl⟩,rfl⟩,rfl⟩,?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel

theorem reduced_equality_transport : ReducedEqualityTransport := by
  intro q p rep h
  exact h.elim (fun hB => Or.inl (rigidCopy_trans rep.samePoints hB))
    (fun hF => Or.inr (rigidCopy_trans rep.samePoints hF))

theorem compact_nonpositive_from_short (cover : CompactCover.ShortRoute)
    (gapPositive : 0 < gap)
    (q : TwoSite) (p : Chart) (rep : ReducedRepresentative q p) (h : deficit q ≤ 0) :
    deficit q = 0 ∧ (IsBCC q ∨ IsFCC q) := by
  have hEq : deficit (chartPoint p) = deficit q := by
    simp only [deficit, rep.sameEnergy, rep.sameDefect]
  have witness := cover.onChart p rep.root ⟨rep.valid, rep.reduced, rep.separation⟩
  obtain ⟨hz, kind⟩ := leaf_of_nonpositive (chartPoint p) gapPositive
    (defect_range (chartPoint p)).2 (by simpa only [hEq] using h) witness
  exact ⟨hEq ▸ hz, reduced_equality_transport q p rep kind⟩

/-- Remaining analytic inputs after the exact closure and Constants proofs. -/
structure GlobalAnalyticInputs : Prop where
  compact : ∀ q, q.Valid → energy q ≤ energy fcc → ∃ p, ReducedRepresentative q p
  bccValues : ∀ q, q.Valid → IsBCC q → energy q = energy bcc ∧ defect q = 0
  fccValues : ∀ q, q.Valid → IsFCC q → energy q = energy fcc ∧ defect q = 1
  fccSaturated : defect fcc = 1
  register : ∀ q p, ReducedRepresentative q p → defect q < 1 → Registration q

theorem assemble_from_short (anal : GlobalAnalyticInputs) (cover : CompactCover.ShortRoute) : Statement := by
  have gapPositive := Constants.reference_gap_checked.2
  apply assemble
  refine ⟨gapPositive, fun q _ => defect_range q, anal.compact, ?_, anal.bccValues,
    anal.fccValues, Constants.refTwo_valid .fcc, anal.fccSaturated, anal.register⟩
  intro q p rep
  by_cases h : deficit q ≤ 0
  · obtain ⟨hz, cls⟩ := compact_nonpositive_from_short cover gapPositive q p rep h
    exact .classifiedNonnegative (le_of_eq hz.symm) (fun _ => cls)
  · exact .strictDeficit (lt_of_not_ge h)

end BccSharp.Coulomb
