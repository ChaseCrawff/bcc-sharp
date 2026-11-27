import BccSharp.TwoSite.Interface
import BccSharp.TwoSite.MontgomeryDefs
import BccSharp.TwoSite.JacobiTriple
import BccSharp.TwoSite.MontgomeryBasic
import BccSharp.TwoSite.MontgomerySmallT
import BccSharp.TwoSite.MontgomeryX
import BccSharp.TwoSite.MontgomeryY
import BccSharp.TwoSite.Montgomery
import BccSharp.TwoSite.Physical
import BccSharp.TwoSite.Reference
import BccSharp.Cover.Round7Geometry
import BccSharp.TwoSite.ScalarChecks
import BccSharp.TwoSite.Bravais
import BccSharp.TwoSite.PeriodRepetition
import BccSharp.TwoSite.ReciprocalRepetition
import BccSharp.TwoSite.PhysicalScale
import BccSharp.TwoSite.RepetitionVolume
import BccSharp.TwoSite.EwaldCellRepetition
import BccSharp.TwoSite.Star
import BccSharp.Analysis.Coverage
import BccSharp.TwoSite.BravaisCover
import BccSharp.Lattice.Addressed
import BccSharp.TwoSite.Coverage
import BccSharp.TwoSite.GoodPoint
import BccSharp.TwoSite.Reduction
import BccSharp.Analysis.FourierUniqueness
import BccSharp.Analysis.Gaussian
import BccSharp.Analysis.Interpolation
import BccSharp.Analysis.Intervals
import BccSharp.Analysis.IntervalChecks
import BccSharp.Analysis.FixedPoint
import BccSharp.Analysis.LatticeTails
import BccSharp.Analysis.Ewald
import BccSharp.Analysis.EwaldDomain
import BccSharp.Analysis.EwaldPeriodicity
import BccSharp.Analysis.SpecialFunctions
import BccSharp.Lattice.Geometry
import BccSharp.Lattice.GeometricLeaves
import BccSharp.Lattice.Curvature
import BccSharp.Analysis.Erfc
import BccSharp.Analysis.DividedExp
import BccSharp.Analysis.DividedReal
import BccSharp.Analysis.TrigBounds
import BccSharp.Analysis.RoundedPolynomial
import BccSharp.Analysis.ExpBounds
import BccSharp.Analysis.ErfcBounds
import BccSharp.TwoSite.ReferenceKernels
import BccSharp.TwoSite.Pi
import BccSharp.Analysis.WeightedTails
import BccSharp.Analysis.EwaldRegular
import BccSharp.Analysis.GaussianSummability
import BccSharp.TwoSite.GeneralSummability
import BccSharp.TwoSite.SeriesModes
import BccSharp.TwoSite.ExpectedStatement
import BccSharp.TwoSite.ReferenceTails
import BccSharp.TwoSite.ReferencePacket
import BccSharp.TwoSite.ReferenceCert
import BccSharp.TwoSite.ReferencePhysical
import BccSharp.Analysis.RegularBounds
import BccSharp.Analysis.KernelDerivatives
import BccSharp.Analysis.RadialPotential
import BccSharp.Analysis.RealSpaceHessian
import BccSharp.Analysis.CoulombLaplace
import BccSharp.Analysis.CoulombIntegrability
import BccSharp.Analysis.CoulombFourier
import BccSharp.Analysis.CoulombTransform
import BccSharp.TwoSite.ScreenedTransform
import BccSharp.Analysis.ReciprocalPotential
import BccSharp.Analysis.ReciprocalSeries
import BccSharp.Analysis.ScreenedBounds
import BccSharp.Analysis.LatticeNeighborhood
import BccSharp.Analysis.RealSpaceSeries
import BccSharp.Analysis.PeriodicPotential
import BccSharp.Analysis.TorusLattice
import BccSharp.Analysis.PeriodLattice
import BccSharp.Analysis.CoulombPeriodization
import BccSharp.TwoSite.PeriodFourier
import BccSharp.TwoSite.ScreeningDifference
import BccSharp.TwoSite.ScreeningIndependence
import BccSharp.Cover.OverlayGaussianPoisson
import BccSharp.TwoSite.RegularLimit
import BccSharp.TwoSite.ReferencePoints
import BccSharp.Lattice.Energy
import BccSharp.Lattice.MeanValue
import BccSharp.Lattice.StrainChart
import BccSharp.Lattice.StrictLeaves
import BccSharp.Lattice.Escape
import BccSharp.Lattice.KernelJet
import BccSharp.Lattice.HessianTail
import BccSharp.Lattice.LdlCurvature
import BccSharp.Cover.AdaptiveLogTangent
import BccSharp.TwoSite.PrimitiveAnchor
import BccSharp.TwoSite.Assembly
import BccSharp.Cover.CoverLatePackets
import BccSharp.Cover.CoverClips
import BccSharp.Cover.CoverCorner
import BccSharp.Cover.CoverReflection
import BccSharp.Cover.CoverAssembly
import BccSharp.Cover.CoverEarlyTransport
import BccSharp.Cover.CoverEarlyReplay
import BccSharp.Cover.CoverEarlyMirror
import BccSharp.Cover.CoverPacketDecode
import BccSharp.Cover.CoverReductionLeaves
import BccSharp.Cover.CoverDirectOperands
import BccSharp.Cover.CoverExactRealGeometry
import BccSharp.Cover.CoverNormalized
import BccSharp.Cover.CoverEarlyHandoff
import BccSharp.Lattice.StarDefect
import BccSharp.Lattice.Polar
import BccSharp.Lattice.E2Core
import BccSharp.Cover.CoverOpticalSurplus
import BccSharp.Lattice.StrainMetric
import BccSharp.Cover.CoverDirectSeries
import BccSharp.Cover.CoverExactReal
import BccSharp.Cover.CoverDirectMoment
import BccSharp.Lattice.BccFrame
import BccSharp.Lattice.FirstJet
import BccSharp.Lattice.StrainE2
import BccSharp.Lattice.HandoffBox
import BccSharp.Lattice.CubicMoves
import BccSharp.Lattice.CubicFold
import BccSharp.Lattice.StrainFirstJet
import BccSharp.Lattice.CenteredStrain
import BccSharp.Lattice.StrainOrigin
import BccSharp.Lattice.FccDefect
import BccSharp.Lattice.FccStrain
import BccSharp.Lattice.Routing
import BccSharp.Lattice.LocalObjective
import BccSharp.Lattice.LocalSeries
import BccSharp.Lattice.SecondJet
import BccSharp.Lattice.LocalMetricJet
import BccSharp.Lattice.LocalShell
import BccSharp.Lattice.LocalHessian
import BccSharp.Lattice.ShortestVector
import BccSharp.Lattice.KzProjection
import BccSharp.Lattice.KzChoices
import BccSharp.Lattice.KzBasis
import BccSharp.Lattice.KzChart
import BccSharp.Lattice.KzTransport
import BccSharp.Lattice.Stationarity
import BccSharp.Lattice.LocalDifferentiation
import BccSharp.Lattice.FixedLocal
import BccSharp.Lattice.FixedLocalBall
import BccSharp.Lattice.LocalBallsBccData
import BccSharp.Lattice.LocalBallsBccAnalytic
import BccSharp.Lattice.LocalBallsBccMetric
import BccSharp.Lattice.LocalBallsBccModes
import BccSharp.Lattice.LocalBallsBccSlabBallDirect
import BccSharp.Lattice.LocalBallsBccSlabQ00Dual
import BccSharp.Lattice.LocalBallsBccSlabQ01Dual
import BccSharp.Lattice.LocalBallsBccSlabQ10Dual
import BccSharp.Lattice.LocalBallsBccSlabQ11Dual
import BccSharp.Lattice.LocalBallsBcc
import BccSharp.Lattice.LocalBallsFccData
import BccSharp.Lattice.LocalBallsFccAnalytic
import BccSharp.Lattice.LocalBallsFccMetric
import BccSharp.Lattice.LocalBallsFccModes
import BccSharp.Lattice.LocalBallsFccSlabBallDirect
import BccSharp.Lattice.LocalBallsFccSlabBallDual
import BccSharp.Lattice.LocalBallsFcc
import BccSharp.Lattice.LocalBalls
import BccSharp.TwoSite.GlobalValues
import BccSharp.TwoSite.GlobalCompact
import BccSharp.TwoSite.GlobalAttain
import BccSharp.TwoSite.GlobalDet
import BccSharp.TwoSite.GlobalRegister
import BccSharp.TwoSite.GlobalInputs
import BccSharp.TwoSite.DefectInvariance
import BccSharp.Cover.AdaptiveGap
import BccSharp.Cover.Stage2Tangents
import BccSharp.Lattice.TangentE1
import BccSharp.Lattice.TangentCover
import BccSharp.Lattice.StrainTangent
import BccSharp.Lattice.StrainLeaf
import BccSharp.Lattice.StrainAtlas
import BccSharp.Lattice.Atlas.TableHalf0
import BccSharp.Lattice.Atlas.TableHalf1
import BccSharp.Lattice.Atlas.TableHalf2
import BccSharp.Lattice.Atlas.TableHalf3
import BccSharp.Lattice.Atlas.TableHalf4
import BccSharp.Lattice.Atlas.TableOne0
import BccSharp.Lattice.Atlas.TableOne1
import BccSharp.Lattice.Atlas.TableOne2
import BccSharp.Lattice.Atlas.TableOne3
import BccSharp.Lattice.Atlas.TableOne4
import BccSharp.Lattice.TangentE1SampleRoot10
import BccSharp.Lattice.TangentTableHalf0
import BccSharp.Lattice.TangentTableHalf1
import BccSharp.Lattice.TangentTableHalf2
import BccSharp.Lattice.TangentTableHalf3
import BccSharp.Lattice.TangentTableHalf4
import BccSharp.Lattice.TangentTableHalf5
import BccSharp.Lattice.TangentTableHalf6
import BccSharp.Lattice.TangentTableHalf7
import BccSharp.Lattice.TangentTableHalf8
import BccSharp.Lattice.TangentTableOne0
import BccSharp.Lattice.TangentTableOne1
import BccSharp.Lattice.TangentTableOne2
import BccSharp.Lattice.TangentTableOne3
import BccSharp.Lattice.TangentTableOne4
import BccSharp.Lattice.TangentTableOne5
import BccSharp.Lattice.TangentTableOne6
import BccSharp.Lattice.TangentTableOne7
import BccSharp.Lattice.TangentTableOne8
import BccSharp.Lattice.TangentTables
import BccSharp.Lattice.Atlas.TableMirror
import BccSharp.Lattice.Atlas.Data
import BccSharp.Lattice.Atlas.Bcc0
import BccSharp.Lattice.Atlas.Bcc1
import BccSharp.Lattice.Atlas.Bcc2
import BccSharp.Lattice.Atlas.Bcc3
import BccSharp.Lattice.Atlas.Bcc4
import BccSharp.Lattice.Atlas.Bcc5
import BccSharp.Lattice.Atlas.Bcc6
import BccSharp.Lattice.Atlas.Bcc7
import BccSharp.Lattice.Atlas.Bcc8
import BccSharp.Lattice.Atlas.Controls
import BccSharp.Lattice.Atlas.Fcc0
import BccSharp.Lattice.Atlas.Fcc1
import BccSharp.Lattice.Atlas.Fcc2
import BccSharp.Lattice.Atlas.Fcc3
import BccSharp.Lattice.Atlas.Fcc4
import BccSharp.Lattice.Atlas.Fcc5
import BccSharp.Lattice.Atlas.Atlases
import BccSharp.Lattice.ForestBase
import BccSharp.Lattice.ForestControls
import BccSharp.Lattice.ForestG00
import BccSharp.Lattice.ForestG01
import BccSharp.Lattice.ForestG02
import BccSharp.Lattice.Forest
import BccSharp.Lattice.Atlas.LatticeCase
import BccSharp.Cover.OverlayAxial
import BccSharp.Cover.OverlayPlanarOperands
import BccSharp.Cover.OverlayPlanarAxialCheck
import BccSharp.Cover.OverlayPlanarPoisson
import BccSharp.Cover.OverlayHeatSplit
import BccSharp.Cover.OverlayRadial
import BccSharp.Cover.OverlayLayerCheck
import BccSharp.Cover.OverlayArea
import BccSharp.Cover.OverlayKernelCheck
import BccSharp.Cover.OverlayScalarHeat
import BccSharp.Cover.OverlayEnergyHeat
import BccSharp.Cover.OverlaySharpLayer
import BccSharp.Cover.OverlaySharpPass
import BccSharp.Cover.OverlayFixConst
import BccSharp.Cover.DirectFixConst
import BccSharp.Cover.OverlayFix
import BccSharp.Cover.OverlayZeroMode
import BccSharp.Cover.OverlayLayerIntegral
import BccSharp.Cover.OverlayPhysicalIdentity
import BccSharp.Cover.OverlayMontgomery
import BccSharp.Cover.OverlaySoundCheck
import BccSharp.Cover.OverlayFixSound
import BccSharp.Cover.OverlayDecodeBase
import BccSharp.Cover.OverlayPilotLeaves
import BccSharp.Cover.AdaptiveConst
import BccSharp.Cover.AdaptiveKernel
import BccSharp.Cover.CenteredAnchor
import BccSharp.Cover.Stage2Geometry
import BccSharp.Cover.AdaptiveCorner
import BccSharp.Cover.Stage2Bulk
import BccSharp.Cover.AdaptiveSupport
import BccSharp.Cover.AdaptiveGain
import BccSharp.Cover.JLeafKernels
import BccSharp.Cover.JLeafCore
import BccSharp.Cover.JLeafChord
import BccSharp.Cover.JLeafDefect
import BccSharp.TwoSite.DefectAnnulus
import BccSharp.TwoSite.DefectCutoff
import BccSharp.Cover.JLeafPhase
import BccSharp.Cover.JLeafTerms
import BccSharp.Cover.JLeafCheck
import BccSharp.TwoSite.DefectCutoffBox
import BccSharp.Cover.JLeafF
import BccSharp.Cover.FLeafSample
import BccSharp.Cover.Stage2Phase
import BccSharp.Cover.CoverEarlyDecode
import BccSharp.Cover.DirectFix
import BccSharp.Cover.DirectFixSound
import BccSharp.Cover.DirectSidecarFix
import BccSharp.Cover.OverlayCorpusGlue
import BccSharp.Cover.OverlayCorpusPrefix
import BccSharp.Cover.OverlayCorpusTrace
import BccSharp.Cover.DataPath
import BccSharp.Cover.DataPathPacker
import BccSharp.Cover.Stage2Fix
import BccSharp.Cover.Stage2FixSound
import BccSharp.Cover.Stage2Table
import BccSharp.Cover.PlanarFibreGWeights
import BccSharp.Cover.PlanarFibreJet
import BccSharp.Cover.PlanarFibreJetSound
import BccSharp.Cover.PlanarFibrePlanar
import BccSharp.Cover.PlanarFibreTaylor
import BccSharp.Cover.LateCompose
import BccSharp.Cover.PlanarFibreTri
import BccSharp.Cover.PlanarFibreTriCell
import BccSharp.Cover.PlanarFibreTriLargeData
import BccSharp.Cover.PlanarFibreTriLarge0
import BccSharp.Cover.PlanarFibreTriLarge1
import BccSharp.Cover.PlanarFibreTriLarge2
import BccSharp.Cover.PlanarFibreTriLarge3
import BccSharp.Cover.PlanarFibreTriLarge
import BccSharp.Cover.PlanarFibreTriPilot
import BccSharp.Cover.PlanarFibreTriRelax
import BccSharp.Cover.PlanarFibreTriSample
import BccSharp.Cover.LayeredDefect
import BccSharp.Cover.LayeredDefectCutoff
import BccSharp.Cover.LayeredScalar
import BccSharp.Cover.LayeredGain
import BccSharp.Cover.LayeredFix
import BccSharp.Cover.LayeredFixSound
import BccSharp.Cover.LayeredRoute
import BccSharp.Cover.AnchorCatalogue
import BccSharp.Cover.AdaptiveLayeredSign
import BccSharp.Cover.CenteredRoute
import BccSharp.Cover.LayeredHalfShift
import BccSharp.Cover.LayeredCatRoute
import BccSharp.Cover.AnchorCatPilot011
import BccSharp.Cover.AnchorCatPilot111
import BccSharp.Cover.AnchorCatPilotEdge
import BccSharp.Cover.LayeredFarRoute
import BccSharp.Cover.AdaptiveFarQ
import BccSharp.Cover.AdaptiveOptical
import BccSharp.Cover.LayeredFarPilotHalfShift
import BccSharp.Cover.LayeredFarPilotPlanarFibre
import BccSharp.Cover.AnchorCatControls
import BccSharp.Cover.LayeredFarControls
import BccSharp.Cover.PrefixDirectItems
import BccSharp.Cover.PrefixFixGlue
import BccSharp.Cover.PrefixStage2TangentTable
import BccSharp.Cover.PrefixStage2PhaseItems
import BccSharp.Cover.PrefixStage2TangentItems
import BccSharp.Cover.PrefixSidecarItems
import BccSharp.Cover.ReplayCompose
import BccSharp.Cover.DataPathLater
import BccSharp.Cover.DataPathLaterChecks
import BccSharp.Cover.DataPathLaterMirror
import BccSharp.Cover.DataPathLaterRun
import BccSharp.Cover.DataPathLaterOr
import BccSharp.Cover.Round7Leaves
import BccSharp.Cover.Round7Fixture
import BccSharp.TwoSite.ScreenedSeries
import BccSharp.Cover.AdaptiveScreened
import BccSharp.Cover.JLeafScreenedTerms
import BccSharp.Cover.JLeafScreenedCheck
import BccSharp.Cover.JensenCore
import BccSharp.Cover.JensenFix
import BccSharp.Cover.JensenFixSound
import BccSharp.Cover.Stage5bPhase
import BccSharp.Cover.Stage3Stage6Compose
import BccSharp.Cover.Stage3Stage6Hybrid
import BccSharp.Cover.Stage3
import BccSharp.Cover.Stage5bOpticalDefect
import BccSharp.Cover.Stage5bPhaseLeaves
import BccSharp.Cover.Stage6FLeaves
import BccSharp.Cover.Stage3Leaves
import BccSharp.Cover.Stage5bStage6HybridThin
import BccSharp.Cover.LeafFix
import BccSharp.Cover.LeafFixPack
import BccSharp.Cover.LeafFixSupport
import BccSharp.Cover.LeafFixSound
import BccSharp.Cover.LeafFixDLeaves
import BccSharp.Cover.LeafFixFLeaves
import BccSharp.Cover.LeafFixFar
import BccSharp.Cover.AdaptiveDeficit
import BccSharp.Cover.AdaptiveCheck
import BccSharp.Cover.AdaptiveThinItems
import BccSharp.Cover.AdaptiveThinK
import BccSharp.Cover.AdaptiveThinQ
import BccSharp.Cover.AdaptiveThinV
import BccSharp.Cover.AdaptiveThinX
import BccSharp.Cover.Stage4Stage5a
import BccSharp.Cover.Stage4Stage5aOpen
import BccSharp.Cover.Stage4Thin1
import BccSharp.Cover.Stage4Thin2
import BccSharp.Cover.Stage4Controls
import BccSharp.Cover.Stage5aAnchored
import BccSharp.Cover.Stage5aThin1
import BccSharp.Cover.Stage6Deficit
import BccSharp.Cover.Stage5bOptical
import BccSharp.Cover.Stage5bOpticalLeaves0
import BccSharp.Cover.Stage5bOpticalLeaves1
import BccSharp.Cover.Stage5bOpticalLeaves2
import BccSharp.Cover.Stage6DLeaves
import BccSharp.Cover.LateChecker
import BccSharp.Cover.LayeredHalfShiftPilot
import BccSharp.Cover.LayeredPilot
import BccSharp.Cover.LayeredControls
import BccSharp.Cover.LeafFixFarDLeaves
import BccSharp.Cover.LeafFixFarJLeaves
import BccSharp.Cover.LeafFixFarControls
import BccSharp.Cover.LeafFixJLeaves
import BccSharp.Cover.LeafFixCorner
import BccSharp.Cover.LeafFixCornerEnv
import BccSharp.Cover.LeafFixCornerPacked
import BccSharp.Cover.LeafFixCornerSample
import BccSharp.Cover.LeafFixRound5
import BccSharp.Cover.LeafFixRound6
import BccSharp.Cover.LeafFixControls
import BccSharp.Cover.Round6ScreenedLeaf
import BccSharp.Cover.Round6ScreenedFixture
import BccSharp.TwoSite.ScreenedModes
import BccSharp.TwoSite.Spec
import BccSharp.TwoSite.StatementFull
import BccSharp.FinalAssembly

/-! Axiom audit of the scope of the package. Generated by `tools/make_audit.py`; do not edit.
Run from the Lake package directory after the build: `lake env lean <this file>`. -/

open Lean Elab Command

def scopeModules : Array Name := #[
  `BccSharp.TwoSite.Interface, `BccSharp.TwoSite.MontgomeryDefs, `BccSharp.TwoSite.JacobiTriple, `BccSharp.TwoSite.MontgomeryBasic,
  `BccSharp.TwoSite.MontgomerySmallT, `BccSharp.TwoSite.MontgomeryX, `BccSharp.TwoSite.MontgomeryY, `BccSharp.TwoSite.Montgomery,
  `BccSharp.TwoSite.Physical, `BccSharp.TwoSite.Reference, `BccSharp.Cover.Round7Geometry, `BccSharp.TwoSite.ScalarChecks,
  `BccSharp.TwoSite.Bravais, `BccSharp.TwoSite.PeriodRepetition, `BccSharp.TwoSite.ReciprocalRepetition, `BccSharp.TwoSite.PhysicalScale,
  `BccSharp.TwoSite.RepetitionVolume, `BccSharp.TwoSite.EwaldCellRepetition, `BccSharp.TwoSite.Star, `BccSharp.Analysis.Coverage,
  `BccSharp.TwoSite.BravaisCover, `BccSharp.Lattice.Addressed, `BccSharp.TwoSite.Coverage, `BccSharp.TwoSite.GoodPoint,
  `BccSharp.TwoSite.Reduction, `BccSharp.Analysis.FourierUniqueness, `BccSharp.Analysis.Gaussian, `BccSharp.Analysis.Interpolation,
  `BccSharp.Analysis.Intervals, `BccSharp.Analysis.IntervalChecks, `BccSharp.Analysis.FixedPoint, `BccSharp.Analysis.LatticeTails,
  `BccSharp.Analysis.Ewald, `BccSharp.Analysis.EwaldDomain, `BccSharp.Analysis.EwaldPeriodicity, `BccSharp.Analysis.SpecialFunctions,
  `BccSharp.Lattice.Geometry, `BccSharp.Lattice.GeometricLeaves, `BccSharp.Lattice.Curvature, `BccSharp.Analysis.Erfc,
  `BccSharp.Analysis.DividedExp, `BccSharp.Analysis.DividedReal, `BccSharp.Analysis.TrigBounds, `BccSharp.Analysis.RoundedPolynomial,
  `BccSharp.Analysis.ExpBounds, `BccSharp.Analysis.ErfcBounds, `BccSharp.TwoSite.ReferenceKernels, `BccSharp.TwoSite.Pi,
  `BccSharp.Analysis.WeightedTails, `BccSharp.Analysis.EwaldRegular, `BccSharp.Analysis.GaussianSummability, `BccSharp.TwoSite.GeneralSummability,
  `BccSharp.TwoSite.SeriesModes, `BccSharp.TwoSite.ExpectedStatement, `BccSharp.TwoSite.ReferenceTails, `BccSharp.TwoSite.ReferencePacket,
  `BccSharp.TwoSite.ReferenceCert, `BccSharp.TwoSite.ReferencePhysical, `BccSharp.Analysis.RegularBounds, `BccSharp.Analysis.KernelDerivatives,
  `BccSharp.Analysis.RadialPotential, `BccSharp.Analysis.RealSpaceHessian, `BccSharp.Analysis.CoulombLaplace, `BccSharp.Analysis.CoulombIntegrability,
  `BccSharp.Analysis.CoulombFourier, `BccSharp.Analysis.CoulombTransform, `BccSharp.TwoSite.ScreenedTransform, `BccSharp.Analysis.ReciprocalPotential,
  `BccSharp.Analysis.ReciprocalSeries, `BccSharp.Analysis.ScreenedBounds, `BccSharp.Analysis.LatticeNeighborhood, `BccSharp.Analysis.RealSpaceSeries,
  `BccSharp.Analysis.PeriodicPotential, `BccSharp.Analysis.TorusLattice, `BccSharp.Analysis.PeriodLattice, `BccSharp.Analysis.CoulombPeriodization,
  `BccSharp.TwoSite.PeriodFourier, `BccSharp.TwoSite.ScreeningDifference, `BccSharp.TwoSite.ScreeningIndependence, `BccSharp.Cover.OverlayGaussianPoisson,
  `BccSharp.TwoSite.RegularLimit, `BccSharp.TwoSite.ReferencePoints, `BccSharp.Lattice.Energy, `BccSharp.Lattice.MeanValue,
  `BccSharp.Lattice.StrainChart, `BccSharp.Lattice.StrictLeaves, `BccSharp.Lattice.Escape, `BccSharp.Lattice.KernelJet,
  `BccSharp.Lattice.HessianTail, `BccSharp.Lattice.LdlCurvature, `BccSharp.Cover.AdaptiveLogTangent, `BccSharp.TwoSite.PrimitiveAnchor,
  `BccSharp.TwoSite.Assembly, `BccSharp.Cover.CoverLatePackets, `BccSharp.Cover.CoverClips, `BccSharp.Cover.CoverCorner,
  `BccSharp.Cover.CoverReflection, `BccSharp.Cover.CoverAssembly, `BccSharp.Cover.CoverEarlyTransport, `BccSharp.Cover.CoverEarlyReplay,
  `BccSharp.Cover.CoverEarlyMirror, `BccSharp.Cover.CoverPacketDecode, `BccSharp.Cover.CoverReductionLeaves, `BccSharp.Cover.CoverDirectOperands,
  `BccSharp.Cover.CoverExactRealGeometry, `BccSharp.Cover.CoverNormalized, `BccSharp.Cover.CoverEarlyHandoff, `BccSharp.Lattice.StarDefect,
  `BccSharp.Lattice.Polar, `BccSharp.Lattice.E2Core, `BccSharp.Cover.CoverOpticalSurplus, `BccSharp.Lattice.StrainMetric,
  `BccSharp.Cover.CoverDirectSeries, `BccSharp.Cover.CoverExactReal, `BccSharp.Cover.CoverDirectMoment, `BccSharp.Lattice.BccFrame,
  `BccSharp.Lattice.FirstJet, `BccSharp.Lattice.StrainE2, `BccSharp.Lattice.HandoffBox, `BccSharp.Lattice.CubicMoves,
  `BccSharp.Lattice.CubicFold, `BccSharp.Lattice.StrainFirstJet, `BccSharp.Lattice.CenteredStrain, `BccSharp.Lattice.StrainOrigin,
  `BccSharp.Lattice.FccDefect, `BccSharp.Lattice.FccStrain, `BccSharp.Lattice.Routing, `BccSharp.Lattice.LocalObjective,
  `BccSharp.Lattice.LocalSeries, `BccSharp.Lattice.SecondJet, `BccSharp.Lattice.LocalMetricJet, `BccSharp.Lattice.LocalShell,
  `BccSharp.Lattice.LocalHessian, `BccSharp.Lattice.ShortestVector, `BccSharp.Lattice.KzProjection, `BccSharp.Lattice.KzChoices,
  `BccSharp.Lattice.KzBasis, `BccSharp.Lattice.KzChart, `BccSharp.Lattice.KzTransport, `BccSharp.Lattice.Stationarity,
  `BccSharp.Lattice.LocalDifferentiation, `BccSharp.Lattice.FixedLocal, `BccSharp.Lattice.FixedLocalBall, `BccSharp.Lattice.LocalBallsBccData,
  `BccSharp.Lattice.LocalBallsBccAnalytic, `BccSharp.Lattice.LocalBallsBccMetric, `BccSharp.Lattice.LocalBallsBccModes, `BccSharp.Lattice.LocalBallsBccSlabBallDirect,
  `BccSharp.Lattice.LocalBallsBccSlabQ00Dual, `BccSharp.Lattice.LocalBallsBccSlabQ01Dual, `BccSharp.Lattice.LocalBallsBccSlabQ10Dual, `BccSharp.Lattice.LocalBallsBccSlabQ11Dual,
  `BccSharp.Lattice.LocalBallsBcc, `BccSharp.Lattice.LocalBallsFccData, `BccSharp.Lattice.LocalBallsFccAnalytic, `BccSharp.Lattice.LocalBallsFccMetric,
  `BccSharp.Lattice.LocalBallsFccModes, `BccSharp.Lattice.LocalBallsFccSlabBallDirect, `BccSharp.Lattice.LocalBallsFccSlabBallDual, `BccSharp.Lattice.LocalBallsFcc,
  `BccSharp.Lattice.LocalBalls, `BccSharp.TwoSite.GlobalValues, `BccSharp.TwoSite.GlobalCompact, `BccSharp.TwoSite.GlobalAttain,
  `BccSharp.TwoSite.GlobalDet, `BccSharp.TwoSite.GlobalRegister, `BccSharp.TwoSite.GlobalInputs, `BccSharp.TwoSite.DefectInvariance,
  `BccSharp.Cover.AdaptiveGap, `BccSharp.Cover.Stage2Tangents, `BccSharp.Lattice.TangentE1, `BccSharp.Lattice.TangentCover,
  `BccSharp.Lattice.StrainTangent, `BccSharp.Lattice.StrainLeaf, `BccSharp.Lattice.StrainAtlas, `BccSharp.Lattice.Atlas.TableHalf0,
  `BccSharp.Lattice.Atlas.TableHalf1, `BccSharp.Lattice.Atlas.TableHalf2, `BccSharp.Lattice.Atlas.TableHalf3, `BccSharp.Lattice.Atlas.TableHalf4,
  `BccSharp.Lattice.Atlas.TableOne0, `BccSharp.Lattice.Atlas.TableOne1, `BccSharp.Lattice.Atlas.TableOne2, `BccSharp.Lattice.Atlas.TableOne3,
  `BccSharp.Lattice.Atlas.TableOne4, `BccSharp.Lattice.TangentE1SampleRoot10, `BccSharp.Lattice.TangentTableHalf0, `BccSharp.Lattice.TangentTableHalf1,
  `BccSharp.Lattice.TangentTableHalf2, `BccSharp.Lattice.TangentTableHalf3, `BccSharp.Lattice.TangentTableHalf4, `BccSharp.Lattice.TangentTableHalf5,
  `BccSharp.Lattice.TangentTableHalf6, `BccSharp.Lattice.TangentTableHalf7, `BccSharp.Lattice.TangentTableHalf8, `BccSharp.Lattice.TangentTableOne0,
  `BccSharp.Lattice.TangentTableOne1, `BccSharp.Lattice.TangentTableOne2, `BccSharp.Lattice.TangentTableOne3, `BccSharp.Lattice.TangentTableOne4,
  `BccSharp.Lattice.TangentTableOne5, `BccSharp.Lattice.TangentTableOne6, `BccSharp.Lattice.TangentTableOne7, `BccSharp.Lattice.TangentTableOne8,
  `BccSharp.Lattice.TangentTables, `BccSharp.Lattice.Atlas.TableMirror, `BccSharp.Lattice.Atlas.Data, `BccSharp.Lattice.Atlas.Bcc0,
  `BccSharp.Lattice.Atlas.Bcc1, `BccSharp.Lattice.Atlas.Bcc2, `BccSharp.Lattice.Atlas.Bcc3, `BccSharp.Lattice.Atlas.Bcc4,
  `BccSharp.Lattice.Atlas.Bcc5, `BccSharp.Lattice.Atlas.Bcc6, `BccSharp.Lattice.Atlas.Bcc7, `BccSharp.Lattice.Atlas.Bcc8,
  `BccSharp.Lattice.Atlas.Controls, `BccSharp.Lattice.Atlas.Fcc0, `BccSharp.Lattice.Atlas.Fcc1, `BccSharp.Lattice.Atlas.Fcc2,
  `BccSharp.Lattice.Atlas.Fcc3, `BccSharp.Lattice.Atlas.Fcc4, `BccSharp.Lattice.Atlas.Fcc5, `BccSharp.Lattice.Atlas.Atlases,
  `BccSharp.Lattice.ForestBase, `BccSharp.Lattice.ForestControls, `BccSharp.Lattice.ForestG00, `BccSharp.Lattice.ForestG01,
  `BccSharp.Lattice.ForestG02, `BccSharp.Lattice.Forest, `BccSharp.Lattice.Atlas.LatticeCase, `BccSharp.Cover.OverlayAxial,
  `BccSharp.Cover.OverlayPlanarOperands, `BccSharp.Cover.OverlayPlanarAxialCheck, `BccSharp.Cover.OverlayPlanarPoisson, `BccSharp.Cover.OverlayHeatSplit,
  `BccSharp.Cover.OverlayRadial, `BccSharp.Cover.OverlayLayerCheck, `BccSharp.Cover.OverlayArea, `BccSharp.Cover.OverlayKernelCheck,
  `BccSharp.Cover.OverlayScalarHeat, `BccSharp.Cover.OverlayEnergyHeat, `BccSharp.Cover.OverlaySharpLayer, `BccSharp.Cover.OverlaySharpPass,
  `BccSharp.Cover.OverlayFixConst, `BccSharp.Cover.DirectFixConst, `BccSharp.Cover.OverlayFix, `BccSharp.Cover.OverlayZeroMode,
  `BccSharp.Cover.OverlayLayerIntegral, `BccSharp.Cover.OverlayPhysicalIdentity, `BccSharp.Cover.OverlayMontgomery, `BccSharp.Cover.OverlaySoundCheck,
  `BccSharp.Cover.OverlayFixSound, `BccSharp.Cover.OverlayDecodeBase, `BccSharp.Cover.OverlayPilotLeaves, `BccSharp.Cover.AdaptiveConst,
  `BccSharp.Cover.AdaptiveKernel, `BccSharp.Cover.CenteredAnchor, `BccSharp.Cover.Stage2Geometry, `BccSharp.Cover.AdaptiveCorner,
  `BccSharp.Cover.Stage2Bulk, `BccSharp.Cover.AdaptiveSupport, `BccSharp.Cover.AdaptiveGain, `BccSharp.Cover.JLeafKernels,
  `BccSharp.Cover.JLeafCore, `BccSharp.Cover.JLeafChord, `BccSharp.Cover.JLeafDefect, `BccSharp.TwoSite.DefectAnnulus,
  `BccSharp.TwoSite.DefectCutoff, `BccSharp.Cover.JLeafPhase, `BccSharp.Cover.JLeafTerms, `BccSharp.Cover.JLeafCheck,
  `BccSharp.TwoSite.DefectCutoffBox, `BccSharp.Cover.JLeafF, `BccSharp.Cover.FLeafSample, `BccSharp.Cover.Stage2Phase,
  `BccSharp.Cover.CoverEarlyDecode, `BccSharp.Cover.DirectFix, `BccSharp.Cover.DirectFixSound, `BccSharp.Cover.DirectSidecarFix,
  `BccSharp.Cover.OverlayCorpusGlue, `BccSharp.Cover.OverlayCorpusPrefix, `BccSharp.Cover.OverlayCorpusTrace, `BccSharp.Cover.DataPath,
  `BccSharp.Cover.DataPathPacker, `BccSharp.Cover.Stage2Fix, `BccSharp.Cover.Stage2FixSound, `BccSharp.Cover.Stage2Table,
  `BccSharp.Cover.PlanarFibreGWeights, `BccSharp.Cover.PlanarFibreJet, `BccSharp.Cover.PlanarFibreJetSound, `BccSharp.Cover.PlanarFibrePlanar,
  `BccSharp.Cover.PlanarFibreTaylor, `BccSharp.Cover.LateCompose, `BccSharp.Cover.PlanarFibreTri, `BccSharp.Cover.PlanarFibreTriCell,
  `BccSharp.Cover.PlanarFibreTriLargeData, `BccSharp.Cover.PlanarFibreTriLarge0, `BccSharp.Cover.PlanarFibreTriLarge1, `BccSharp.Cover.PlanarFibreTriLarge2,
  `BccSharp.Cover.PlanarFibreTriLarge3, `BccSharp.Cover.PlanarFibreTriLarge, `BccSharp.Cover.PlanarFibreTriPilot, `BccSharp.Cover.PlanarFibreTriRelax,
  `BccSharp.Cover.PlanarFibreTriSample, `BccSharp.Cover.LayeredDefect, `BccSharp.Cover.LayeredDefectCutoff, `BccSharp.Cover.LayeredScalar,
  `BccSharp.Cover.LayeredGain, `BccSharp.Cover.LayeredFix, `BccSharp.Cover.LayeredFixSound, `BccSharp.Cover.LayeredRoute,
  `BccSharp.Cover.AnchorCatalogue, `BccSharp.Cover.AdaptiveLayeredSign, `BccSharp.Cover.CenteredRoute, `BccSharp.Cover.LayeredHalfShift,
  `BccSharp.Cover.LayeredCatRoute, `BccSharp.Cover.AnchorCatPilot011, `BccSharp.Cover.AnchorCatPilot111, `BccSharp.Cover.AnchorCatPilotEdge,
  `BccSharp.Cover.LayeredFarRoute, `BccSharp.Cover.AdaptiveFarQ, `BccSharp.Cover.AdaptiveOptical, `BccSharp.Cover.LayeredFarPilotHalfShift,
  `BccSharp.Cover.LayeredFarPilotPlanarFibre, `BccSharp.Cover.AnchorCatControls, `BccSharp.Cover.LayeredFarControls, `BccSharp.Cover.PrefixDirectItems,
  `BccSharp.Cover.PrefixFixGlue, `BccSharp.Cover.PrefixStage2TangentTable, `BccSharp.Cover.PrefixStage2PhaseItems, `BccSharp.Cover.PrefixStage2TangentItems,
  `BccSharp.Cover.PrefixSidecarItems, `BccSharp.Cover.ReplayCompose, `BccSharp.Cover.DataPathLater, `BccSharp.Cover.DataPathLaterChecks,
  `BccSharp.Cover.DataPathLaterMirror, `BccSharp.Cover.DataPathLaterRun, `BccSharp.Cover.DataPathLaterOr, `BccSharp.Cover.Round7Leaves,
  `BccSharp.Cover.Round7Fixture, `BccSharp.TwoSite.ScreenedSeries, `BccSharp.Cover.AdaptiveScreened, `BccSharp.Cover.JLeafScreenedTerms,
  `BccSharp.Cover.JLeafScreenedCheck, `BccSharp.Cover.JensenCore, `BccSharp.Cover.JensenFix, `BccSharp.Cover.JensenFixSound,
  `BccSharp.Cover.Stage5bPhase, `BccSharp.Cover.Stage3Stage6Compose, `BccSharp.Cover.Stage3Stage6Hybrid, `BccSharp.Cover.Stage3,
  `BccSharp.Cover.Stage5bOpticalDefect, `BccSharp.Cover.Stage5bPhaseLeaves, `BccSharp.Cover.Stage6FLeaves, `BccSharp.Cover.Stage3Leaves,
  `BccSharp.Cover.Stage5bStage6HybridThin, `BccSharp.Cover.LeafFix, `BccSharp.Cover.LeafFixPack, `BccSharp.Cover.LeafFixSupport,
  `BccSharp.Cover.LeafFixSound, `BccSharp.Cover.LeafFixDLeaves, `BccSharp.Cover.LeafFixFLeaves, `BccSharp.Cover.LeafFixFar,
  `BccSharp.Cover.AdaptiveDeficit, `BccSharp.Cover.AdaptiveCheck, `BccSharp.Cover.AdaptiveThinItems, `BccSharp.Cover.AdaptiveThinK,
  `BccSharp.Cover.AdaptiveThinQ, `BccSharp.Cover.AdaptiveThinV, `BccSharp.Cover.AdaptiveThinX, `BccSharp.Cover.Stage4Stage5a,
  `BccSharp.Cover.Stage4Stage5aOpen, `BccSharp.Cover.Stage4Thin1, `BccSharp.Cover.Stage4Thin2, `BccSharp.Cover.Stage4Controls,
  `BccSharp.Cover.Stage5aAnchored, `BccSharp.Cover.Stage5aThin1, `BccSharp.Cover.Stage6Deficit, `BccSharp.Cover.Stage5bOptical,
  `BccSharp.Cover.Stage5bOpticalLeaves0, `BccSharp.Cover.Stage5bOpticalLeaves1, `BccSharp.Cover.Stage5bOpticalLeaves2, `BccSharp.Cover.Stage6DLeaves,
  `BccSharp.Cover.LateChecker, `BccSharp.Cover.LayeredHalfShiftPilot, `BccSharp.Cover.LayeredPilot, `BccSharp.Cover.LayeredControls,
  `BccSharp.Cover.LeafFixFarDLeaves, `BccSharp.Cover.LeafFixFarJLeaves, `BccSharp.Cover.LeafFixFarControls, `BccSharp.Cover.LeafFixJLeaves,
  `BccSharp.Cover.LeafFixCorner, `BccSharp.Cover.LeafFixCornerEnv, `BccSharp.Cover.LeafFixCornerPacked, `BccSharp.Cover.LeafFixCornerSample,
  `BccSharp.Cover.LeafFixRound5, `BccSharp.Cover.LeafFixRound6, `BccSharp.Cover.LeafFixControls, `BccSharp.Cover.Round6ScreenedLeaf,
  `BccSharp.Cover.Round6ScreenedFixture, `BccSharp.TwoSite.ScreenedModes, `BccSharp.TwoSite.Spec, `BccSharp.TwoSite.StatementFull,
  `BccSharp.FinalAssembly
]

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#audit_scope" : command => do
  let env ← getEnv
  let mut scope : NameSet := {}
  for m in scopeModules do scope := scope.insert m
  let loaded := scopeModules.filter fun m => env.header.moduleNames.contains m
  logInfo m!"scope modules listed: {scopeModules.size}; present in the environment: {loaded.size}"
  let mut checked : Nat := 0
  let mut internal : Nat := 0
  let mut theorems : Nat := 0
  let mut declared : Array Name := #[]
  let mut bad : Array (Name × Array Name) := #[]
  let mut n0 : Nat := 0
  let mut sets : Array (List Name × Nat) := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless scope.contains modName do continue
    if let .axiomInfo _ := info then declared := declared.push name
    if let .thmInfo _ := info then theorems := theorems + 1
    if name.isInternal then internal := internal + 1
    let axs ← liftCoreM <| Lean.collectAxioms name
    checked := checked + 1
    let key := (axs.qsort (fun a b => a.toString < b.toString)).toList
    if key.isEmpty then n0 := n0 + 1
    match sets.findIdx? (fun p => p.1 == key) with
    | some i => sets := sets.modify i (fun p => (p.1, p.2 + 1))
    | none => sets := sets.push (key, 1)
    let extra := axs.filter (fun a => !allowedAxioms.contains a)
    unless extra.isEmpty do bad := bad.push (name, extra)
  logInfo m!"axioms declared in modules of the scope: {declared.size} {declared}"
  logInfo m!"constants checked: {checked} (theorems {theorems}, internal names {internal}); using an axiom outside propext, Classical.choice, Quot.sound: {bad.size}"
  for (k, n) in sets do
    logInfo m!"axiom set {k}: {n} constants"
  for (n, a) in bad do
    logInfo m!"OFFENDER {n}: {a}"

#audit_scope

set_option pp.fullNames true

-- statements of the headline theorems
#check @BccSharp.Coulomb.Full.ewald_energy
#check @BccSharp.Coulomb.BravaisCover.oneSiteEnergy_from_normalized
#check @BccSharp.Coulomb.DefectInvariance.energy_of_points_eq
#check @BccSharp.Coulomb.Full.energy_of_rigidImage
#check @BccSharp.Coulomb.Full.defect_of_rigidImage
#check @BccSharp.Coulomb.DefectInvariance.siteDefect_of_mem
#check @BccSharp.Coulomb.SpecBridge.spec_physical
#check @BccSharp.Coulomb.Constants.reference_bounds
#check @BccSharp.Coulomb.Constants.reference_gap_checked
#check @BccSharp.Coulomb.Full.gap_value
#check @BccSharp.Coulomb.BravaisCover.StrainAtlas.latticeCase_proved
#check @BccSharp.Coulomb.GlobalInputs.bccValues_proof
#check @BccSharp.Coulomb.GlobalInputs.fccValues_proof
#check @BccSharp.Coulomb.GlobalInputs.compact_proof
#check @BccSharp.Coulomb.GlobalInputs.register_proof
#check @BccSharp.Coulomb.Full.register_frame
#check @BccSharp.Coulomb.GlobalInputs.globalAnalyticInputs
#check @BccSharp.Coulomb.CompactCover.JLeaf.Cutoff.defect_le_regCost_cutoff
#check @BccSharp.Coulomb.CompactCover.JLeaf.Cutoff.defect_le_annulus
#check @BccSharp.Coulomb.CompactCover.Layered.defect_transport
#check @BccSharp.Coulomb.CompactCover.Layered.defect_transport_cutoff
#check @BccSharp.Coulomb.Montgomery.theorem1
#check @BccSharp.Coulomb.CompactCover.OverlayCorpus.corpusCheckFix_sound
#check @BccSharp.Coulomb.CompactCover.AdaptiveSupport.adaptiveFull_sound
#check @BccSharp.Coulomb.CompactCover.LatePackets.lateChecker_sound
#check @BccSharp.Coulomb.Full.StatementFull.physical
#check @BccSharp.Coulomb.FinalAssembly.statementFull_of_replay
#check @BccSharp.Coulomb.FinalAssembly.statementFull_of_runs
#check @BccSharp.Coulomb.FinalAssembly.statementFull_of_replay_merged
#check @BccSharp.Coulomb.FinalAssembly.statementFull_of_runs_merged

-- definitions named in the scope table (existence check)
#check @BccSharp.Coulomb.TwoSite.Valid
#check @BccSharp.Coulomb.energy
#check @BccSharp.Coulomb.h₂
#check @BccSharp.Coulomb.gKernel
#check @BccSharp.Coulomb.gap
#check @BccSharp.Coulomb.defect
#check @BccSharp.Coulomb.cappedDefect
#check @BccSharp.Coulomb.defectTrial
#check @BccSharp.Coulomb.deficit
#check @BccSharp.Coulomb.Statement
#check @BccSharp.Coulomb.Full.StatementFull
#check @BccSharp.Coulomb.LatticeCase
#check @BccSharp.Coulomb.oneSiteEnergy
#check @BccSharp.Coulomb.oneSiteDefect
#check @BccSharp.Coulomb.oneSiteDeficit
#check @BccSharp.Coulomb.GlobalAnalyticInputs
#check @BccSharp.Coulomb.Registration
#check @TwoSiteSpec.specDefect
#check @TwoSiteSpec.specSiteDefect
#check @TwoSiteSpec.TwoCosetConfig
#check @TwoSiteSpec.TwoTranslates
#check @TwoSiteSpec.RigidImage
#check @TwoSiteSpec.RegisteredBound
#check @TwoSiteSpec.bccUnit
#check @TwoSiteSpec.fccUnit
#check @BccSharp.Coulomb.Constants.bccBracket
#check @BccSharp.Coulomb.Constants.fccBracket
#check @BccSharp.Coulomb.Constants.gapBracket

-- axioms of each theorem of the scope table
#print axioms BccSharp.Coulomb.periodicGreen_fourier_on_cell
#print axioms BccSharp.Coulomb.periodicGreen_regular_limit
#print axioms BccSharp.Coulomb.periodicGreen_screening_independent
#print axioms BccSharp.Coulomb.ewaldRegularSelf_screening_independent
#print axioms BccSharp.Coulomb.Full.greenPerParticle_screening
#print axioms BccSharp.Coulomb.Full.ewald_energy
#print axioms BccSharp.Coulomb.green_two_eq_energy
#print axioms BccSharp.Coulomb.ScreenedSeries.h₂_screened
#print axioms BccSharp.Coulomb.BravaisCover.oneSiteEnergy_from_normalized
#print axioms BccSharp.Coulomb.greenPerParticle_repetition
#print axioms BccSharp.Coulomb.DefectInvariance.energy_of_points_eq
#print axioms BccSharp.Coulomb.DefectInvariance.energy_of_isometric
#print axioms BccSharp.Coulomb.Full.energy_of_rigidImage
#print axioms BccSharp.Coulomb.greenPerParticle_scale
#print axioms BccSharp.Coulomb.Full.density_energy
#print axioms BccSharp.Coulomb.SpecBridge.specDefect_one
#print axioms BccSharp.Coulomb.DefectInvariance.cappedDefect_orthogonal_image
#print axioms BccSharp.Coulomb.DefectInvariance.defect_of_isometric
#print axioms BccSharp.Coulomb.Full.defect_of_rigidImage
#print axioms BccSharp.Coulomb.DefectInvariance.defect_rebase
#print axioms BccSharp.Coulomb.DefectInvariance.defect_wrap
#print axioms BccSharp.Coulomb.DefectInvariance.defect_swap
#print axioms BccSharp.Coulomb.DefectInvariance.siteDefect_second_site
#print axioms BccSharp.Coulomb.DefectInvariance.siteDefect_of_mem
#print axioms BccSharp.Coulomb.SpecBridge.spec_physical
#print axioms BccSharp.Coulomb.DefectInvariance.repetition_siteDefect
#print axioms BccSharp.Coulomb.SpecBridge.spec_dilated
#print axioms BccSharp.Coulomb.DefectInvariance.defect_eq_min
#print axioms BccSharp.Coulomb.SpecBridge.twoCoset_of_valid
#print axioms BccSharp.Coulomb.SpecBridge.valid_of_twoCoset
#print axioms BccSharp.Coulomb.SpecBridge.spec_translates
#print axioms BccSharp.Coulomb.SpecBridge.isBCC_iff_physical
#print axioms BccSharp.Coulomb.SpecBridge.isFCC_iff_physical
#print axioms BccSharp.Coulomb.Constants.bcc_primitive_enclosed
#print axioms BccSharp.Coulomb.Constants.fcc_primitive_enclosed
#print axioms BccSharp.Coulomb.Constants.reference_bounds
#print axioms BccSharp.Coulomb.Constants.reference_gap_checked
#print axioms BccSharp.Coulomb.Full.gap_value
#print axioms BccSharp.Coulomb.BravaisCover.StrainAtlas.latticeCase_proved
#print axioms BccSharp.Coulomb.BravaisCover.localBalls
#print axioms BccSharp.Coulomb.BravaisCover.TangentCover.Tables.tables_valid
#print axioms BccSharp.Coulomb.BravaisCover.TangentCover.Forest.grid_check
#print axioms BccSharp.Coulomb.BravaisCover.TangentCover.Forest.forest_checked
#print axioms BccSharp.Coulomb.BravaisCover.StrainAtlas.bccClosed
#print axioms BccSharp.Coulomb.BravaisCover.StrainAtlas.fccClosed
#print axioms BccSharp.Coulomb.BravaisCover.StrainAtlas.strainAtlases_sharp
#print axioms BccSharp.Coulomb.BravaisCover.StrainAtlas.latticeCase_from_tangent_forest_atlases
#print axioms BccSharp.Coulomb.primitive_anchor_exists
#print axioms BccSharp.Coulomb.GlobalInputs.bccValues_proof
#print axioms BccSharp.Coulomb.GlobalInputs.fccValues_proof
#print axioms BccSharp.Coulomb.GlobalInputs.fccSaturated_proof
#print axioms BccSharp.Coulomb.GlobalInputs.compact_proof
#print axioms BccSharp.Coulomb.GlobalInputs.separated_of_energy
#print axioms BccSharp.Coulomb.GlobalInputs.register_proof
#print axioms BccSharp.Coulomb.Full.register_frame
#print axioms BccSharp.Coulomb.GlobalInputs.globalAnalyticInputs
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.defect_le_regCost
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.Cutoff.defect_le_regCost_cutoff
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.Cutoff.defect_le_annulus
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.Cutoff.defect_le_box_cutoff
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.Cutoff.defect_le_box_far
#print axioms BccSharp.Coulomb.CompactCover.Layered.defect_transport
#print axioms BccSharp.Coulomb.CompactCover.Layered.defect_transport_cutoff
#print axioms BccSharp.Coulomb.CompactCover.Layered.defect_transport_annulus
#print axioms BccSharp.Coulomb.Montgomery.theorem1
#print axioms BccSharp.Coulomb.Montgomery.jacobi_triple_product
#print axioms BccSharp.Coulomb.CompactCover.OverlayPlanar.chart_energy_planar
#print axioms BccSharp.Coulomb.CompactCover.OverlayPlanar.planarRegularized_ge_triangle
#print axioms BccSharp.Coulomb.CompactCover.DirectFix.directFix_sound
#print axioms BccSharp.Coulomb.CompactCover.EarlyReplay.initialWitnessCheckFix_sound
#print axioms BccSharp.Coulomb.CompactCover.EarlyReplay.checkWithDirectSidecarFix_sound
#print axioms BccSharp.Coulomb.CompactCover.EarlyReplay.checkWithStage2Fix_sound
#print axioms BccSharp.Coulomb.CompactCover.EarlyReplay.checkWithStage2FixT_sound
#print axioms BccSharp.Coulomb.CompactCover.OverlayPlanar.energy_fcc_lt_of_numeratorCheck
#print axioms BccSharp.Coulomb.CompactCover.OverlayPlanar.overlayCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.OverlayPlanar.overlaySharpCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix.overlayFixCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix.checkWithOverlay_sound
#print axioms BccSharp.Coulomb.CompactCover.OverlayCorpus.corpusCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.OverlayCorpus.corpusCheckFix_sound
#print axioms BccSharp.Coulomb.CompactCover.AdaptiveSupport.adaptiveCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.AdaptiveSupport.adaptiveFull_sound
#print axioms BccSharp.Coulomb.CompactCover.AdaptiveOptical.gapSatOk_sound
#print axioms BccSharp.Coulomb.CompactCover.Jensen.Fix.fLeafCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage5bPhase.stage5bPhaseCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage3Stage6.stage3Check_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage3Stage6.stage5bHybridCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage5bOptical.stage5bOpticalCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage4Stage5a.stage4stage5aCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage4Stage5a.stage5aCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage3Stage6.stage6Check_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage3Stage6.stage6DEval_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage3Stage6.stage6FullCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Stage3Stage6.stage6HybridCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.jleaf_sound
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.fleaf_sound
#print axioms BccSharp.Coulomb.CompactCover.JLeaf.Screened.jleaf_sound_screened
#print axioms BccSharp.Coulomb.CompactCover.LeafFix.jleafFix_sound
#print axioms BccSharp.Coulomb.CompactCover.LeafFix.dleafFix_sound
#print axioms BccSharp.Coulomb.CompactCover.LeafFix.fleafFix_sound
#print axioms BccSharp.Coulomb.CompactCover.LeafFix.certCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.LeafFix.lateCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.LeafFix.lateCheckFar_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.planarAnchorCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.halfShiftCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.farTransportOk_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.planarAnchorCertOkFar_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.planarAnchorCheckFar_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.halfShiftCheckFar_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.planarFibreCheckFar_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.catalogueOk_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.halfShiftCheckCat_sound
#print axioms BccSharp.Coulomb.CompactCover.Layered.centeredCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.PlanarFibreTri.planarFibreTriCheck_sound
#print axioms BccSharp.Coulomb.CompactCover.LatePackets.lateChecker_sound
#print axioms BccSharp.Coulomb.BravaisCover.TangentE1.leafCheck_sound
#print axioms BccSharp.Coulomb.BravaisCover.StrainTangent.zLeafCheck_sound
#print axioms BccSharp.Coulomb.assemble
#print axioms BccSharp.Coulomb.GlobalInputs.assemble_from_cover_corpus_cover
#print axioms BccSharp.Coulomb.Full.statementFull_of_statement
#print axioms BccSharp.Coulomb.Full.statementFull_iff
#print axioms BccSharp.Coulomb.Full.StatementFull.physical
#print axioms BccSharp.Coulomb.FinalAssembly.later_sound
#print axioms BccSharp.Coulomb.FinalAssembly.prefix_sound
#print axioms BccSharp.Coulomb.FinalAssembly.late_sound
#print axioms BccSharp.Coulomb.FinalAssembly.mergedPending_sound
#print axioms BccSharp.Coulomb.FinalAssembly.statementFull_of_replay
#print axioms BccSharp.Coulomb.FinalAssembly.statementFull_of_runs
#print axioms BccSharp.Coulomb.FinalAssembly.statementFull_of_replay_merged
#print axioms BccSharp.Coulomb.FinalAssembly.statementFull_of_runs_merged
