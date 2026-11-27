import BccSharp.Cover.AnchorCatalogue
import BccSharp.Cover.LayeredHalfShift

set_option autoImplicit false

/-! # HalfShift relative requests whose anchor has no registration (catalogue route)

For a HalfShift relative request (half bits `111`) whose all-half anchor has no BCC
registration of cost below one on the box, `catalogueOk box (−1, −1, −1)`
certifies `D(anchor) = 1` at every good point (`catalogueOk_sound`,
`BccSharp.Cover.AnchorCatalogue`). Then `D(p) ≤ 1 = D(anchor)`, so the defect term of
the relative comparison needs no penalty, and the gain check of `planarAnchorCertOk`
can run with `λ = 2 a_c⁺ k` in place of `2 a_c⁺ (200 gap⁺ + k)`:

  `deficit(p) − deficit(anchor) = E(p) − E(anchor) − gap (D(p) − 1) ≥ k |R d|²`.

`planarAnchorCertOkCat c box n` is that check; it reads only `c.depth` and `c.k` (the
certificate's registration is not used). `halfShiftCheckCat` is the request-level
checker, with the certificates and request shapes of `halfShiftCheck`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-- The all-half class `2 f₀ = (−1, −1, −1)`. -/
def allHalfZ : IntVec := ![-1, -1, -1]

theorem allHalfZ_half : (fun i => ((allHalfZ i : ℤ) : ℝ) / 2) = halfAll := by
  funext i
  fin_cases i <;> simp [allHalfZ, halfAll]

/-- The gain scale with no defect penalty. -/
def lamCat (k : ℚ) : ℚ := 2 * DirectRoute.scaleWitness.upper * k

/-- The PlanarAnchor certificate check for an anchor without registration: the gain
check with penalty `0`, and the catalogue check of the all-half class. -/
def planarAnchorCertOkCat (c : PlanarAnchorCert) (box : Cell) (n : IntVec) : Bool :=
  (decide (0 < c.k) && splitOk (anchorW n) (lamCat c.k) c.depth (shiftCell box (seamShiftW n))) &&
    catalogueOk box allHalfZ

/-- The route result of one certificate accepted by `planarAnchorCertOkCat`. -/
theorem planarAnchorCertOkCat_sound (latticeCase : LatticeCase) (c : PlanarAnchorCert) (box : Cell) (n : IntVec)
    (ok : planarAnchorCertOkCat c box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) := by
  simp only [planarAnchorCertOkCat, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨hk, hsplit⟩, hcat⟩ := ok
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨an, han⟩ : ∃ an, an = anchorW n := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb, ← han] at hsplit
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  -- the gain
  have gain := splitOk_gain c.depth hsplit hp'
  have hE : energy (chartPoint p') = energy (chartPoint p) := by
    rw [hp'def, chartPoint_shift, energy_wrap]
  have hA := anchor_chart_wrap p n
  rw [← hp'def, ← han] at hA
  have hEa : energy (chartPoint (anchorChart p' (an.k₁ / 2) (an.k₂ / 2))) =
      energy (anchorOf (chartPoint p) halfAll) := by rw [hA, energy_wrap]
  have hG := gram_eq p n
  rw [← hp'def, ← han] at hG
  obtain ⟨bq, hbq⟩ : ∃ x, x =
      sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) :=
    ⟨_, rfl⟩
  rw [← hbq] at hG
  rw [hE, hEa, hG] at gain
  -- the scale and the gap
  obtain ⟨_, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gapB := Constants.reference_gap_checked
  have gap0 : 0 < gap := gapB.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  -- the anchor's defect is one
  have hD1 : defect (anchorOf (chartPoint p) halfAll) = 1 := by
    have h := catalogueOk_sound box allHalfZ hcat p hp gp
    rw [allHalfZ_half] at h
    exact h
  have hDp : defect (chartPoint p) ≤ 1 := (defect_range (chartPoint p)).2
  -- combine
  have hk0 : (0 : ℝ) < c.k := by exact_mod_cast hk
  have hlam : (2 * ac) * (c.k : ℝ) ≤ (lamCat c.k : ℝ) := by
    unfold lamCat
    push_cast
    have h3 : (2 * ac) * (c.k : ℝ) ≤ (2 * (DirectRoute.scaleWitness.upper : ℝ)) * c.k :=
      mul_le_mul_of_nonneg_right (by linarith) hk0.le
    linarith
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (c.k : ℝ) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((c.k : ℝ) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  have deficitGain : deficit (anchorOf (chartPoint p) halfAll) + ((0 : ℚ) : ℝ) +
      ((c.k : ℚ) : ℝ) * bq ≤ deficit (chartPoint p) := by
    unfold deficit
    rw [hD1]
    have h1 := mul_le_mul_of_nonneg_left hDp gap0.le
    push_cast
    linarith
  have rel : relativeCheck 0 c.k = true := by
    unfold relativeCheck
    exact decide_eq_true ⟨le_rfl, hk⟩
  exact relativeOptical_route_of_lattice latticeCase p gp.1 halfAll n halfAll_half 0 c.k rel (by
    rw [hbq] at deficitGain; exact deficitGain)

/-- The HalfShift relative checker with `planarAnchorCertOkCat`. -/
def halfShiftCheckCat (table : Request → Option PlanarAnchorCert) : Checker := fun q =>
  match q.packet, q.proposal.payload with
  | .halfShift, .optical (.transport _) .basin half _ =>
    match table q with
    | some c => planarAnchorCertOkCat c q.target.box half.wrap
    | none => false
  | _, _ => false

theorem halfShiftCheckCat_sound (latticeCase : LatticeCase) (table : Request → Option PlanarAnchorCert) :
    CheckerSound (halfShiftCheckCat table) := by
  intro q _ _ _ h p hp gp
  unfold halfShiftCheckCat at h
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
        have ev := planarAnchorCertOkCat_sound latticeCase c _ half.wrap h p hp gp
        show (Proposal.route (.optical (.transport s) .basin half hint)).result p
        simp only [Proposal.route, Route.result]
        exact ev
  | _ => simp at h

/-- A HalfShift request with a basin result is accepted by `halfShiftCheckCat` when its
table entry passes `planarAnchorCertOkCat` on the request's target box and half wrap. -/
theorem halfShiftCheckCat_accept (table : Request → Option PlanarAnchorCert) (q : Request) (s : ℕ)
    (half : HalfWitness) (hint : ℚ) (c : PlanarAnchorCert) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (ht : table q = some c) (ok : planarAnchorCertOkCat c q.target.box half.wrap = true) :
    halfShiftCheckCat table q = true := by
  unfold halfShiftCheckCat
  rw [hq, hpay]
  simp only [ht, ok]

/-- A certificate for `planarAnchorCertOkCat`: its registration field is not read. -/
def catCert (depth : ℕ) (k : ℚ) : PlanarAnchorCert where
  depth := depth
  k := k
  reg := { B := 1, N := 1, U := 1, f0 := ![-1 / 2, -1 / 2, -1 / 2], wrap := 0 }

end BccSharp.Coulomb.CompactCover.Layered
