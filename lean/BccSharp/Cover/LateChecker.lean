import BccSharp.Cover.LateCompose
import BccSharp.Cover.LayeredHalfShift
import BccSharp.Cover.LayeredFarRoute
import BccSharp.Cover.LayeredCatRoute
import BccSharp.Cover.PlanarFibreTri
import BccSharp.Cover.CenteredRoute
import BccSharp.Cover.LeafFixFar
import BccSharp.Cover.OverlayCorpusPrefix

set_option autoImplicit false

/-! # The late corpus checker

`lateChecker t` is the checker that `Corpus.run` runs on the late rows of the
corpus (Corner, HalfShift, JointDeficit, PlanarFibre, Continuation round one and PlanarAnchor). It dispatches by
`Request.family`:

* `.leaf` (Corner corners, JointDeficit and Continuation round-one corners and joints):
  `LeafFix.lateCheckFar t.leaf`, the fixed-point J, F and D leaves with the
  far-annulus defect bound for J and D leaves whose registered cost exceeds
  1/2 (every old `LeafCert` enters through `FarCert.ofLeafCert`,
  `lateChecker_ofLeafCert`);
* `.transport` (HalfShift requests with a basin result): the PlanarAnchor certificate check
  `Layered.halfShiftCheck t.halfShift` (registered cost at most 1/2), its far form
  `Layered.halfShiftCheckFar t.halfShiftFar` (transport past cost 1/2) and its catalogue form `Layered.halfShiftCheckCat t.halfShiftCat`
  (anchors without a registration of their class, `D(anchor) = 1`);
* `.layered`: the PlanarAnchor relative comparisons `Layered.planarAnchorCheck t.planarAnchor` and
  their far form `Layered.planarAnchorCheckFar t.planarAnchorFar`, and the PlanarFibre layered
  comparisons `Layered.planarFibreCheckFar t.planarFibreFar`;
* `.triangular` (PlanarFibre): `PlanarFibreTri.planarFibreTriCheck t.tri`;
* `.centered` (PlanarAnchor): `Layered.centeredCheck t.atlas t.centered`: a lower
  bound on the anchor's deficit from E2 strain leaves on the atlas `t.atlas`,
  plus the layered gain bound `k |R d|²` with `k < 0`.

Within a family a request is accepted when any of the family's checks accepts
it (`eitherCheck`); each check reads its own table and rejects requests without
an entry there.

`lateChecker_sound` proves `CheckerSound (lateChecker t)` from `LatticeCase`,
which the optical routes need. The centered route needs the atlas to be valid;
`LateTables` carries that proof (`atlasValid`), so whoever builds the corpus
tables passes `StrainAtlas.atlasData` with `atlasData_valid` (the final assembly
takes the tables `t` as a parameter). `LatticeCase` is proved as
`StrainAtlas.latticeCase_proved`; it stays a hypothesis
here. `assemble_from_late_tables` feeds it to `assemble_from_overlay_corpus`: the
statement follows once the late corpus run `corp.run (lateChecker t) stage6`
returns `some []`. That run needs a certificate for every late request, so it is
not yet available. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.LatePackets

/-- The certificate tables of the written late evaluators. -/
structure LateTables where
  /-- Fixed-point J, F and D leaf certificates (Corner, JointDeficit, Continuation round one),
  with the far J/D checks. -/
  leaf : Request → Option LeafFix.FarCert
  /-- HalfShift relative certificates (checked by the PlanarAnchor certificate check). -/
  halfShift : Request → Option Layered.PlanarAnchorCert
  /-- PlanarAnchor relative certificates. -/
  planarAnchor : Request → Option Layered.PlanarAnchorCert
  /-- The strain atlas of the centered anchor leaves (`StrainAtlas.atlasData` for
  the corpus tables). -/
  atlas : BravaisCover.StrainAtlas.AtlasData
  /-- The atlas is valid (`StrainAtlas.atlasData_valid` for `StrainAtlas.atlasData`). -/
  atlasValid : atlas.Valid
  /-- PlanarAnchor centered certificates. -/
  centered : Request → Option Layered.CenteredCert
  /-- HalfShift relative certificates for the far transport check. -/
  halfShiftFar : Request → Option Layered.PlanarAnchorCert
  /-- HalfShift relative certificates for the catalogue check. -/
  halfShiftCat : Request → Option Layered.PlanarAnchorCert
  /-- PlanarAnchor relative certificates for the far transport check. -/
  planarAnchorFar : Request → Option Layered.PlanarAnchorCert
  /-- PlanarFibre layered certificates for the far transport check. -/
  planarFibreFar : Request → Option Layered.PlanarAnchorCert
  /-- PlanarFibre triangular trees. -/
  tri : Request → Option PlanarFibreTri.TriTree

/-- The checks of the transport family (HalfShift). -/
def transportCheck (t : LateTables) : Checker :=
  eitherCheck (Layered.halfShiftCheck t.halfShift) (eitherCheck (Layered.halfShiftCheckFar t.halfShiftFar) (Layered.halfShiftCheckCat t.halfShiftCat))

/-- The checks of the layered family (PlanarAnchor and PlanarFibre). -/
def layeredCheck (t : LateTables) : Checker :=
  eitherCheck (Layered.planarAnchorCheck t.planarAnchor) (eitherCheck (Layered.planarAnchorCheckFar t.planarAnchorFar) (Layered.planarFibreCheckFar t.planarFibreFar))

/-- The late checker. -/
def lateChecker (t : LateTables) : Checker :=
  familyCheck (LeafFix.lateCheckFar t.leaf) (transportCheck t) (layeredCheck t) (PlanarFibreTri.planarFibreTriCheck t.tri)
    (Layered.centeredCheck t.atlas t.centered)

theorem lateChecker_sound (latticeCase : LatticeCase) (t : LateTables) : CheckerSound (lateChecker t) :=
  familyCheck_sound (LeafFix.lateCheckFar_sound t.leaf)
    (eitherCheck_sound (Layered.halfShiftCheck_sound latticeCase t.halfShift)
      (eitherCheck_sound (Layered.halfShiftCheckFar_sound latticeCase t.halfShiftFar) (Layered.halfShiftCheckCat_sound latticeCase t.halfShiftCat)))
    (eitherCheck_sound (Layered.planarAnchorCheck_sound latticeCase t.planarAnchor)
      (eitherCheck_sound (Layered.planarAnchorCheckFar_sound latticeCase t.planarAnchorFar) (Layered.planarFibreCheckFar_sound latticeCase t.planarFibreFar)))
    (PlanarFibreTri.planarFibreTriCheck_sound t.tri) (Layered.centeredCheck_sound t.atlas t.atlasValid t.centered)

/-- Old leaf certificates keep working: with a `LeafCert` table mapped by
`FarCert.ofLeafCert`, the late checker is the one built on `LeafFix.lateCheck`.
(`LateTables.leaf` now holds `FarCert`s, so table builders map old
certificates this way.) -/
theorem lateChecker_ofLeafCert (leaf : Request → Option LeafFix.LeafCert)
    (halfShift planarAnchor : Request → Option Layered.PlanarAnchorCert) (atlas : BravaisCover.StrainAtlas.AtlasData)
    (atlasValid : atlas.Valid) (centered : Request → Option Layered.CenteredCert)
    (halfShiftFar halfShiftCat planarAnchorFar planarFibreFar : Request → Option Layered.PlanarAnchorCert)
    (tri : Request → Option PlanarFibreTri.TriTree) :
    lateChecker ⟨fun q => (leaf q).map LeafFix.FarCert.ofLeafCert, halfShift, planarAnchor, atlas, atlasValid, centered,
        halfShiftFar, halfShiftCat, planarAnchorFar, planarFibreFar, tri⟩ =
      familyCheck (LeafFix.lateCheck leaf)
        (eitherCheck (Layered.halfShiftCheck halfShift) (eitherCheck (Layered.halfShiftCheckFar halfShiftFar) (Layered.halfShiftCheckCat halfShiftCat)))
        (eitherCheck (Layered.planarAnchorCheck planarAnchor) (eitherCheck (Layered.planarAnchorCheckFar planarAnchorFar) (Layered.planarFibreCheckFar planarFibreFar)))
        (PlanarFibreTri.planarFibreTriCheck tri) (Layered.centeredCheck atlas centered) := by
  simp only [lateChecker, transportCheck, layeredCheck, LeafFix.lateCheckFar_ofLeafCert]

/-! ### Request-level corollaries -/

/-- A request of the transport family (HalfShift) that one of the family's checks accepts
(`transportCheck`) is accepted by the late checker. -/
theorem lateChecker_of_transport (t : LateTables) {q : Request} (hf : q.family = .transport)
    (h : transportCheck t q = true) : lateChecker t q = true := by
  unfold lateChecker familyCheck
  rw [hf]
  exact h

/-- A request of the layered family (PlanarAnchor and PlanarFibre) that one of the family's checks accepts
(`layeredCheck`) is accepted by the late checker. -/
theorem lateChecker_of_layered (t : LateTables) {q : Request} (hf : q.family = .layered)
    (h : layeredCheck t q = true) : lateChecker t q = true := by
  unfold lateChecker familyCheck
  rw [hf]
  exact h

/-- A PlanarAnchor centered request is accepted when its table entry passes
`centeredCertOk` on the atlas, the request's target box and its wrap. -/
theorem lateChecker_centered (t : LateTables) (q : Request) (method : CenteredMethod) (wrap : IntVec)
    (hint slack : ℚ) (c : Layered.CenteredCert) (hq : q.packet = .planarAnchor)
    (hpay : q.proposal.payload = .centered method wrap hint slack)
    (ht : t.centered q = some c) (ok : Layered.centeredCertOk t.atlas c q.target.box wrap = true) :
    lateChecker t q = true := by
  have hf : q.family = .centered := by simp only [Request.family, hq, hpay]
  have hk : Layered.centeredCheck t.atlas t.centered q = true := by
    unfold Layered.centeredCheck
    rw [hq, hpay]
    simp only [ht, ok]
  unfold lateChecker familyCheck
  rw [hf]
  exact hk

/-- A PlanarAnchor relative request is accepted when its table entry passes
`planarAnchorCertOk` on the request's target box and half wrap. -/
theorem lateChecker_planarAnchor (t : LateTables) (q : Request) (half : HalfWitness) (hint : ℚ)
    (c : Layered.PlanarAnchorCert) (hq : q.packet = .planarAnchor)
    (hpay : q.proposal.payload = .optical .layered .basin half hint)
    (ht : t.planarAnchor q = some c) (ok : Layered.planarAnchorCertOk c q.target.box half.wrap = true) :
    lateChecker t q = true := by
  have hf : q.family = .layered := by simp only [Request.family, hq, hpay]
  have hk : Layered.planarAnchorCheck t.planarAnchor q = true := by
    unfold Layered.planarAnchorCheck
    rw [hq, hpay]
    simp only [ht, ok]
  exact lateChecker_of_layered t hf (by simp [layeredCheck, eitherCheck, hk])

/-- A PlanarAnchor relative request is accepted when its far-table entry passes
`planarAnchorCertOkFar`. -/
theorem lateChecker_planarAnchorFar (t : LateTables) (q : Request) (half : HalfWitness) (hint : ℚ)
    (c : Layered.PlanarAnchorCert) (hq : q.packet = .planarAnchor)
    (hpay : q.proposal.payload = .optical .layered .basin half hint)
    (ht : t.planarAnchorFar q = some c) (ok : Layered.planarAnchorCertOkFar c q.target.box half.wrap = true) :
    lateChecker t q = true := by
  have hf : q.family = .layered := by simp only [Request.family, hq, hpay]
  have hk : Layered.planarAnchorCheckFar t.planarAnchorFar q = true := by
    unfold Layered.planarAnchorCheckFar
    rw [hq, hpay]
    simp only [ht, ok]
  exact lateChecker_of_layered t hf (by simp [layeredCheck, eitherCheck, hk])

/-- A PlanarFibre layered request with a basin result is accepted when its far-table
entry passes `planarAnchorCertOkFar`. -/
theorem lateChecker_planarFibreFar (t : LateTables) (q : Request) (half : HalfWitness) (hint : ℚ)
    (c : Layered.PlanarAnchorCert) (hq : q.packet = .planarFibreOther ∨ q.packet = .planarFibreSaturated)
    (hpay : q.proposal.payload = .optical .layered .basin half hint)
    (ht : t.planarFibreFar q = some c) (ok : Layered.planarAnchorCertOkFar c q.target.box half.wrap = true) :
    lateChecker t q = true := by
  have hf : q.family = .layered := by
    rcases hq with hq | hq <;> simp only [Request.family, hq, hpay]
  have hk : Layered.planarFibreCheckFar t.planarFibreFar q = true := by
    unfold Layered.planarFibreCheckFar
    rcases hq with hq | hq <;> rw [hq, hpay] <;> simp only [ht, ok]
  exact lateChecker_of_layered t hf (by simp [layeredCheck, eitherCheck, hk])

/-- A HalfShift request with a basin result is accepted when its table entry passes
`planarAnchorCertOk` on the request's target box and half wrap. -/
theorem lateChecker_halfShift (t : LateTables) (q : Request) (s : ℕ) (half : HalfWitness) (hint : ℚ)
    (c : Layered.PlanarAnchorCert) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (ht : t.halfShift q = some c) (ok : Layered.planarAnchorCertOk c q.target.box half.wrap = true) :
    lateChecker t q = true := by
  have hf : q.family = .transport := by simp only [Request.family, hq, hpay]
  have hk : Layered.halfShiftCheck t.halfShift q = true := by
    unfold Layered.halfShiftCheck
    rw [hq, hpay]
    simp only [ht, ok]
  exact lateChecker_of_transport t hf (by simp [transportCheck, eitherCheck, hk])

/-- A HalfShift request with a basin result is accepted when its far-table entry
passes `planarAnchorCertOkFar`. -/
theorem lateChecker_halfShiftFar (t : LateTables) (q : Request) (s : ℕ) (half : HalfWitness) (hint : ℚ)
    (c : Layered.PlanarAnchorCert) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (ht : t.halfShiftFar q = some c) (ok : Layered.planarAnchorCertOkFar c q.target.box half.wrap = true) :
    lateChecker t q = true := by
  have hf : q.family = .transport := by simp only [Request.family, hq, hpay]
  have hk : Layered.halfShiftCheckFar t.halfShiftFar q = true := by
    unfold Layered.halfShiftCheckFar
    rw [hq, hpay]
    simp only [ht, ok]
  exact lateChecker_of_transport t hf (by simp [transportCheck, eitherCheck, hk])

/-- A HalfShift request with a basin result is accepted when its catalogue-table
entry passes `planarAnchorCertOkCat`. -/
theorem lateChecker_halfShiftCat (t : LateTables) (q : Request) (s : ℕ) (half : HalfWitness) (hint : ℚ)
    (c : Layered.PlanarAnchorCert) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (ht : t.halfShiftCat q = some c) (ok : Layered.planarAnchorCertOkCat c q.target.box half.wrap = true) :
    lateChecker t q = true := by
  have hf : q.family = .transport := by simp only [Request.family, hq, hpay]
  have hk : Layered.halfShiftCheckCat t.halfShiftCat q = true := by
    unfold Layered.halfShiftCheckCat
    rw [hq, hpay]
    simp only [ht, ok]
  exact lateChecker_of_transport t hf (by simp [transportCheck, eitherCheck, hk])

/-- A PlanarFibre triangular request is accepted when its table entry is a tree that
passes on the request's target box. -/
theorem lateChecker_planarFibre (t : LateTables) (q : Request) (radius hint : ℚ)
    (tr : PlanarFibreTri.TriTree) (hq : q.packet = .planarFibreOther ∨ q.packet = .planarFibreSaturated)
    (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t.tri q = some tr) (ok : tr.ok q.target.box = true) :
    lateChecker t q = true := by
  have hf : q.family = .triangular := by
    rcases hq with hq | hq <;> simp only [Request.family, hq, hpay]
  unfold lateChecker familyCheck
  rw [hf]
  exact PlanarFibreTri.planarFibreTriCheck_of t.tri q radius hint tr hpay ht ok

end BccSharp.Coulomb.CompactCover.LatePackets

namespace BccSharp.Coulomb
open CompactCover CompactCover.LatePackets CompactCover.EarlyReplay CompactCover.OverlayCorpus

/-- `assemble_from_overlay_corpus` with the late checker. -/
theorem assemble_from_late_tables (latticeCase : LatticeCase) (t : LateTables)
    (geometric : WitnessRef → Option NormalizedProposal)
    (direct : WitnessRef → Option Cell) (sidecar : WitnessRef → Option DirectSidecarProposal)
    (bulk : WitnessRef → Option Stage2Payload) {later : WitnessRef → Cell → Bool}
    (laterSound : SoundCheck later) {early : Stage6Checker} (sEarly : Stage6CheckerSound early)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom)
    (rStage5b : pre.run (corpusCheck geometric direct sidecar bulk later) = some stage5b)
    (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage6 : runRows (runStage6 early) stage5b rows = some stage6)
    (closed : corp.run (lateChecker t) stage6 = some []) :
    Statement :=
  assemble_from_overlay_corpus geometric direct sidecar bulk laterSound sEarly (lateChecker_sound latticeCase t)
    pre stage5b stage6 rStage5b rows corp rStage6 closed

end BccSharp.Coulomb
