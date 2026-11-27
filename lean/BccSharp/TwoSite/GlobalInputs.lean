import BccSharp.TwoSite.GlobalRegister
import BccSharp.Cover.CoverAssembly
import BccSharp.Cover.CoverEarlyHandoff

set_option autoImplicit false

/-! `GlobalAnalyticInputs` without premises. Every final the two-site theorem assembly
theorem that took the analytic inputs as a premise now needs only its cover
certificate data. The cover premises are unchanged. So is `LatticeCase`, which
the cover's relative optical witnesses use for their half-period anchors: both
the anchor inequality `0 ≤ deficit` and its equality classification. -/

noncomputable section

namespace BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.EarlyReplay

/-- All analytic premises of the two-site theorem assembly, proved. -/
theorem globalAnalyticInputs : GlobalAnalyticInputs where
  compact := compact_proof
  bccValues := bccValues_proof
  fccValues := fccValues_proof
  fccSaturated := fccSaturated_proof
  register := register_proof

/-- the two-site theorem from the short-route cover certificate alone. -/
theorem assemble_from_short_cover (cover : ShortRoute) : Statement :=
  assemble_from_short globalAnalyticInputs cover

/-- The two-site theorem from the checked corpus alone. -/
theorem assemble_from_checked_cover_cover
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early)
    (sLate : CheckerSound late)
    (stage5b stage6 : List Atom) (rows : List (Row Stage6Trace)) (corp : Corpus)
    (upstream : Handoff positiveHalf {p | Slots stage5b p})
    (rStage6 : runRows (runStage6 early) stage5b rows=some stage6) (closed : corp.run late stage6=some []) :
    Statement :=
  assemble_from_checked_cover globalAnalyticInputs sEarly sLate stage5b stage6 rows corp upstream rStage6
    closed

/-- the two-site theorem from the full corpus with its checked prefix alone. -/
theorem assemble_from_cover_corpus_cover
    {prefixCheck : WitnessRef → Cell → Bool} (prefixSound : SoundCheck prefixCheck)
    {early : Stage6Checker} {late : Checker} (sEarly : Stage6CheckerSound early)
    (sLate : CheckerSound late)
    (pre : CorpusPrefix) (stage5b stage6 : List Atom) (rStage5b : pre.run prefixCheck=some stage5b)
    (rows : List (Row Stage6Trace)) (corp : Corpus)
    (rStage6 : runRows (runStage6 early) stage5b rows=some stage6) (closed : corp.run late stage6=some []) :
    Statement :=
  assemble_from_cover_corpus globalAnalyticInputs prefixSound sEarly sLate pre stage5b stage6 rStage5b rows
    corp rStage6 closed

end BccSharp.Coulomb.GlobalInputs
