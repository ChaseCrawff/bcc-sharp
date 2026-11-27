import BccSharp.Cover.LayeredRoute

set_option autoImplicit false

/-! # HalfShift relative requests through the PlanarAnchor certificate check

A HalfShift half-transport request with a basin result has the same route result as
a PlanarAnchor relative request, `OpticalEvidence (chartPoint p)` at every good point
of its target box, and all HalfShift anchors are half-height anchors. So the same
certificate check applies: `halfShiftCheck` accepts a request
`.halfShift` / `.optical (.transport _) .basin half _` when its table entry passes
`Layered.planarAnchorCertOk` on the target box with wrap `half.wrap`. The check uses
the all-half anchor `(−1/2, −1/2, −1/2)` whatever the proposal's half bits; the
route result does not depend on the anchor, so this is sound for every
request, and it is useful for the requests with half bits `111`. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets

/-- The HalfShift relative checker, from a table of certificates indexed by requests. -/
def halfShiftCheck (table : Request → Option PlanarAnchorCert) : Checker := fun q =>
  match q.packet, q.proposal.payload with
  | .halfShift, .optical (.transport _) .basin half _ =>
    match table q with
    | some c => planarAnchorCertOk c q.target.box half.wrap
    | none => false
  | _, _ => false

theorem halfShiftCheck_sound (latticeCase : LatticeCase) (table : Request → Option PlanarAnchorCert) :
    CheckerSound (halfShiftCheck table) := by
  intro q _ _ _ h p hp gp
  unfold halfShiftCheck at h
  rcases q with ⟨packet, root, path, ⟨ancestor, payload⟩⟩
  cases packet <;> try (simp at h)
  cases payload with
  | optical method result half hint =>
    cases method with
    | layered => simp at h
    | transport s =>
      cases result <;> try (simp at h)
      cases hc : table ⟨.halfShift, root, path, ⟨ancestor, .optical (.transport s) .basin half hint⟩⟩ with
      | none => rw [hc] at h; simp at h
      | some c =>
        rw [hc] at h
        have ev := planarAnchorCertOk_sound latticeCase c _ half.wrap h p hp gp
        show (Proposal.route (.optical (.transport s) .basin half hint)).result p
        simp only [Proposal.route, Route.result]
        exact ev
  | _ => simp at h

end BccSharp.Coulomb.CompactCover.Layered
