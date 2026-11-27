import BccSharp.Lattice.LocalBallsFccData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! FCC differentiation witness on `analyticLocalBox`: chart, root, index-jet
coverage, exponent and tail checks, the metric positivity check. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

theorem lengthOK : cubeRootCheck lengthRoot (Ball.exact 2) = true := by decide +kernel

theorem analyticChart : strainMetricCheck .fcc analyticLocalBox analyticData.chart = true := by decide +kernel

theorem analyticCover_direct_00 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 0 0) (analyticData.index false 0 0) = true := by decide +kernel

theorem analyticCover_direct_01 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 0 1) (analyticData.index false 0 1) = true := by decide +kernel

theorem analyticCover_direct_02 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 0 2) (analyticData.index false 0 2) = true := by decide +kernel

theorem analyticCover_direct_10 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 1 0) (analyticData.index false 1 0) = true := by decide +kernel

theorem analyticCover_direct_11 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 1 1) (analyticData.index false 1 1) = true := by decide +kernel

theorem analyticCover_direct_12 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 1 2) (analyticData.index false 1 2) = true := by decide +kernel

theorem analyticCover_direct_20 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 2 0) (analyticData.index false 2 0) = true := by decide +kernel

theorem analyticCover_direct_21 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 2 1) (analyticData.index false 2 1) = true := by decide +kernel

theorem analyticCover_direct_22 : jetCovered (indexJetBall .fcc false analyticLocalBox analyticData.chart analyticData.length 2 2) (analyticData.index false 2 2) = true := by decide +kernel

theorem analyticFamily_direct : analyticData.familyCheck false = true := by decide +kernel

theorem analyticCover_dual_00 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 0 0) (analyticData.index true 0 0) = true := by decide +kernel

theorem analyticCover_dual_01 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 0 1) (analyticData.index true 0 1) = true := by decide +kernel

theorem analyticCover_dual_02 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 0 2) (analyticData.index true 0 2) = true := by decide +kernel

theorem analyticCover_dual_10 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 1 0) (analyticData.index true 1 0) = true := by decide +kernel

theorem analyticCover_dual_11 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 1 1) (analyticData.index true 1 1) = true := by decide +kernel

theorem analyticCover_dual_12 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 1 2) (analyticData.index true 1 2) = true := by decide +kernel

theorem analyticCover_dual_20 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 2 0) (analyticData.index true 2 0) = true := by decide +kernel

theorem analyticCover_dual_21 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 2 1) (analyticData.index true 2 1) = true := by decide +kernel

theorem analyticCover_dual_22 : jetCovered (indexJetBall .fcc true analyticLocalBox analyticData.chart analyticData.length 2 2) (analyticData.index true 2 2) = true := by decide +kernel

theorem analyticFamily_dual : analyticData.familyCheck true = true := by decide +kernel

theorem analyticBase : analyticData.Base .fcc analyticLocalBox where
  chart := analyticChart
  length := lengthOK
  covered := by
    intro d k l
    cases d <;> fin_cases k <;> fin_cases l
    exacts [analyticCover_direct_00, analyticCover_direct_01, analyticCover_direct_02, analyticCover_direct_10, analyticCover_direct_11, analyticCover_direct_12, analyticCover_direct_20, analyticCover_direct_21, analyticCover_direct_22, analyticCover_dual_00, analyticCover_dual_01, analyticCover_dual_02, analyticCover_dual_10, analyticCover_dual_11, analyticCover_dual_12, analyticCover_dual_20, analyticCover_dual_21, analyticCover_dual_22]
  family := by
    intro d
    cases d
    exacts [analyticFamily_direct, analyticFamily_dual]

theorem positiveOK : metricPositiveCheck .fcc analyticData.chart = true := by decide +kernel

end BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
