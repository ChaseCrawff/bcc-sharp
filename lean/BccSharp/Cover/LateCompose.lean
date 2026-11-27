import BccSharp.Cover.CoverLatePackets

set_option autoImplicit false

/-! # Composing late corpus checkers

`Corpus.run` takes one `LatePackets.Checker`. Each family evaluator (the
fixed-point J/F/D leaves of Corner, JointDeficit and Continuation, the optical comparisons of
HalfShift, PlanarFibre and PlanarAnchor, the triangular fibers of PlanarFibre and the centered PlanarAnchor
comparisons) is a checker that accepts only its own kind of request and is
sound on its own. `eitherCheck` accepts a request when either checker accepts it,
and `CheckerSound` is closed under it, so the late checker is the disjunction
of the family checkers. A family whose evaluator is not written yet
contributes `noCheck`, which accepts nothing.

Each family checker states its own premises: the optical ones assume
`LatticeCase`, which `Forest.latticeCase_of_atlases` reduces to the two Lattice
strain-atlas checks. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover
namespace LatePackets

/-- Accept a request when either checker accepts it. -/
def eitherCheck (a b : Checker) : Checker := fun q => a q || b q

theorem eitherCheck_sound {a b : Checker} (ha : CheckerSound a) (hb : CheckerSound b) :
    CheckerSound (eitherCheck a b) := by
  intro q pre prof scope h p hp gp
  cases e : a q with
  | true => exact ha q pre prof scope e p hp gp
  | false =>
    have hb' : b q = true := by simpa [eitherCheck, e] using h
    exact hb q pre prof scope hb' p hp gp

/-- The checker that accepts nothing. -/
def noCheck : Checker := fun _ => false

theorem noCheck_sound : CheckerSound noCheck := by
  intro q _ _ _ h
  exact absurd h (by simp [noCheck])

/-- Accept a request when some checker of the list accepts it. -/
def anyCheck : List Checker → Checker
  | [] => noCheck
  | c :: cs => eitherCheck c (anyCheck cs)

theorem anyCheck_sound : ∀ cs : List Checker, (∀ c ∈ cs, CheckerSound c) → CheckerSound (anyCheck cs)
  | [], _ => noCheck_sound
  | c :: cs, h =>
    eitherCheck_sound (h c (List.mem_cons_self ..))
      (anyCheck_sound cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- Restrict a checker to the requests a Boolean filter selects. -/
def onlyIf (select : Request → Bool) (c : Checker) : Checker := fun q => select q && c q

theorem onlyIf_sound (select : Request → Bool) {c : Checker} (hc : CheckerSound c) :
    CheckerSound (onlyIf select c) := by
  intro q pre prof scope h p hp gp
  exact hc q pre prof scope (Bool.and_eq_true_iff.mp h).2 p hp gp

/-! ### The late families

The late corpus requests fall into these families, by packet and payload
constructor. Every request that `Request.profileCheck` accepts belongs to
exactly one of them. -/

inductive Family where
  /-- Corner corners, JointDeficit and Continuation round-one corners and joints. -/
  | leaf
  /-- HalfShift half-translation transport. -/
  | transport
  /-- PlanarFibre and PlanarAnchor layered half-height comparisons. -/
  | layered
  /-- PlanarFibre triangular fibers. -/
  | triangular
  /-- PlanarAnchor centered comparisons. -/
  | centered
  /-- Rejected by `Request.profileCheck`. -/
  | other
  deriving DecidableEq, Repr

def Request.family (q : Request) : Family :=
  match q.packet, q.proposal.payload with
  | .cornerRule, .corner _ _ _ | .jointDeficit, .corner _ _ _ | .continuationR1, .corner _ _ _
  | .jointDeficit, .joint _ _ _ | .continuationR1, .joint _ _ _ => .leaf
  | .halfShift, .optical (.transport _) _ _ _ => .transport
  | .planarFibreOther, .optical .layered _ _ _ | .planarFibreSaturated, .optical .layered _ _ _
  | .planarAnchor, .optical .layered _ _ _ => .layered
  | .planarFibreOther, .triangular _ _ | .planarFibreSaturated, .triangular _ _ => .triangular
  | .planarAnchor, .centered _ _ _ _ => .centered
  | _, _ => .other

/-- The late checker from one checker per family. Each family checker is
consulted only on its own requests. -/
def familyCheck (leaf transport layered triangular centered : Checker) : Checker := fun q =>
  match q.family with
  | .leaf => leaf q
  | .transport => transport q
  | .layered => layered q
  | .triangular => triangular q
  | .centered => centered q
  | .other => false

theorem familyCheck_sound {leaf transport layered triangular centered : Checker}
    (h₁ : CheckerSound leaf) (h₂ : CheckerSound transport) (h₃ : CheckerSound layered)
    (h₄ : CheckerSound triangular) (h₅ : CheckerSound centered) :
    CheckerSound (familyCheck leaf transport layered triangular centered) := by
  intro q pre prof scope h p hp gp
  unfold familyCheck at h
  cases hf : q.family with
  | leaf => rw [hf] at h; exact h₁ q pre prof scope h p hp gp
  | transport => rw [hf] at h; exact h₂ q pre prof scope h p hp gp
  | layered => rw [hf] at h; exact h₃ q pre prof scope h p hp gp
  | triangular => rw [hf] at h; exact h₄ q pre prof scope h p hp gp
  | centered => rw [hf] at h; exact h₅ q pre prof scope h p hp gp
  | other => rw [hf] at h; exact absurd h (by simp)

/-- Every request accepted by `profileCheck` has a family other than `other`. -/
theorem family_ne_other (q : Request) (h : q.profileCheck = true) : q.family ≠ .other := by
  rcases q with ⟨packet, root, path, ⟨ancestor, payload⟩⟩
  unfold Request.profileCheck at h
  unfold Request.family
  cases packet <;> cases payload with
  | corner compare steps hint => simp_all
  | joint steps par hint => simp_all
  | optical method result half hint =>
    cases method with
    | transport s => cases s <;> simp_all
    | layered => simp_all
  | triangular radius hint => simp_all
  | centered method wrap hint slack => simp_all

end LatePackets
end BccSharp.Coulomb.CompactCover
