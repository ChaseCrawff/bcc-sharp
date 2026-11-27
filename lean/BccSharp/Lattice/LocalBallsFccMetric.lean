import BccSharp.Lattice.LocalBallsFccData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! FCC curvature inputs: charts and Cartesian metric-jet coverage on the curvature
boxes, the root-square invertibility and the penalty Hessian coverage. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

theorem rootSquareOK : (lengthRoot.ball.mul lengthRoot.ball).invertible := by decide +kernel

theorem chart_ball : strainMetricCheck .fcc (ballRoot) (shortChart .fcc (ballRoot)) = true := by decide +kernel

theorem metricCover_ball_direct_00 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 0 0) (pick cmet_ball_direct 0 0) = true := by decide +kernel

theorem metricCover_ball_direct_01 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 0 1) (pick cmet_ball_direct 0 1) = true := by decide +kernel

theorem metricCover_ball_direct_02 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 0 2) (pick cmet_ball_direct 0 2) = true := by decide +kernel

theorem metricCover_ball_direct_10 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 1 0) (pick cmet_ball_direct 1 0) = true := by decide +kernel

theorem metricCover_ball_direct_11 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 1 1) (pick cmet_ball_direct 1 1) = true := by decide +kernel

theorem metricCover_ball_direct_12 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 1 2) (pick cmet_ball_direct 1 2) = true := by decide +kernel

theorem metricCover_ball_direct_20 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 2 0) (pick cmet_ball_direct 2 0) = true := by decide +kernel

theorem metricCover_ball_direct_21 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 2 1) (pick cmet_ball_direct 2 1) = true := by decide +kernel

theorem metricCover_ball_direct_22 : jetCovered (localMetricJetBall .fcc false (ballRoot) (shortChart .fcc (ballRoot)) 2 2) (pick cmet_ball_direct 2 2) = true := by decide +kernel

theorem metricCover_ball_direct : ∀ i j, jetCovered (localMetricJetBall .fcc false (ballRoot)
    (shortChart .fcc (ballRoot)) i j) (pick cmet_ball_direct i j) = true := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [metricCover_ball_direct_00, metricCover_ball_direct_01, metricCover_ball_direct_02, metricCover_ball_direct_10, metricCover_ball_direct_11, metricCover_ball_direct_12, metricCover_ball_direct_20, metricCover_ball_direct_21, metricCover_ball_direct_22]

theorem metricCover_ball_dual_00 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 0 0) (pick cmet_ball_dual 0 0) = true := by decide +kernel

theorem metricCover_ball_dual_01 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 0 1) (pick cmet_ball_dual 0 1) = true := by decide +kernel

theorem metricCover_ball_dual_02 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 0 2) (pick cmet_ball_dual 0 2) = true := by decide +kernel

theorem metricCover_ball_dual_10 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 1 0) (pick cmet_ball_dual 1 0) = true := by decide +kernel

theorem metricCover_ball_dual_11 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 1 1) (pick cmet_ball_dual 1 1) = true := by decide +kernel

theorem metricCover_ball_dual_12 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 1 2) (pick cmet_ball_dual 1 2) = true := by decide +kernel

theorem metricCover_ball_dual_20 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 2 0) (pick cmet_ball_dual 2 0) = true := by decide +kernel

theorem metricCover_ball_dual_21 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 2 1) (pick cmet_ball_dual 2 1) = true := by decide +kernel

theorem metricCover_ball_dual_22 : jetCovered (localMetricJetBall .fcc true (ballRoot) (shortChart .fcc (ballRoot)) 2 2) (pick cmet_ball_dual 2 2) = true := by decide +kernel

theorem metricCover_ball_dual : ∀ i j, jetCovered (localMetricJetBall .fcc true (ballRoot)
    (shortChart .fcc (ballRoot)) i j) (pick cmet_ball_dual i j) = true := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [metricCover_ball_dual_00, metricCover_ball_dual_01, metricCover_ball_dual_02, metricCover_ball_dual_10, metricCover_ball_dual_11, metricCover_ball_dual_12, metricCover_ball_dual_20, metricCover_ball_dual_21, metricCover_ball_dual_22]

theorem penaltyOK : penaltyCheck .fcc ballRoot (shortChart .fcc ballRoot) penalty = true := by decide +kernel

end BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
