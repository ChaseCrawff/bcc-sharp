import BccSharp.Lattice.LocalBallsBccData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! BCC curvature inputs: charts and Cartesian metric-jet coverage on the curvature
boxes, the root-square invertibility and the penalty Hessian coverage. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.BccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

theorem rootSquareOK : (lengthRoot.ball.mul lengthRoot.ball).invertible := by decide +kernel

theorem chart_ball : strainMetricCheck .bcc (ballRoot) (shortChart .bcc (ballRoot)) = true := by decide +kernel

theorem metricCover_ball_direct_00 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 0 0) (pick cmet_ball_direct 0 0) = true := by decide +kernel

theorem metricCover_ball_direct_01 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 0 1) (pick cmet_ball_direct 0 1) = true := by decide +kernel

theorem metricCover_ball_direct_02 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 0 2) (pick cmet_ball_direct 0 2) = true := by decide +kernel

theorem metricCover_ball_direct_10 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 1 0) (pick cmet_ball_direct 1 0) = true := by decide +kernel

theorem metricCover_ball_direct_11 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 1 1) (pick cmet_ball_direct 1 1) = true := by decide +kernel

theorem metricCover_ball_direct_12 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 1 2) (pick cmet_ball_direct 1 2) = true := by decide +kernel

theorem metricCover_ball_direct_20 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 2 0) (pick cmet_ball_direct 2 0) = true := by decide +kernel

theorem metricCover_ball_direct_21 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 2 1) (pick cmet_ball_direct 2 1) = true := by decide +kernel

theorem metricCover_ball_direct_22 : jetCovered (localMetricJetBall .bcc false (ballRoot) (shortChart .bcc (ballRoot)) 2 2) (pick cmet_ball_direct 2 2) = true := by decide +kernel

theorem metricCover_ball_direct : ∀ i j, jetCovered (localMetricJetBall .bcc false (ballRoot)
    (shortChart .bcc (ballRoot)) i j) (pick cmet_ball_direct i j) = true := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [metricCover_ball_direct_00, metricCover_ball_direct_01, metricCover_ball_direct_02, metricCover_ball_direct_10, metricCover_ball_direct_11, metricCover_ball_direct_12, metricCover_ball_direct_20, metricCover_ball_direct_21, metricCover_ball_direct_22]

theorem chart_q00 : strainMetricCheck .bcc (qbox false false) (shortChart .bcc (qbox false false)) = true := by decide +kernel

theorem metricCover_q00_dual_00 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 0 0) (pick cmet_q00_dual 0 0) = true := by decide +kernel

theorem metricCover_q00_dual_01 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 0 1) (pick cmet_q00_dual 0 1) = true := by decide +kernel

theorem metricCover_q00_dual_02 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 0 2) (pick cmet_q00_dual 0 2) = true := by decide +kernel

theorem metricCover_q00_dual_10 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 1 0) (pick cmet_q00_dual 1 0) = true := by decide +kernel

theorem metricCover_q00_dual_11 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 1 1) (pick cmet_q00_dual 1 1) = true := by decide +kernel

theorem metricCover_q00_dual_12 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 1 2) (pick cmet_q00_dual 1 2) = true := by decide +kernel

theorem metricCover_q00_dual_20 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 2 0) (pick cmet_q00_dual 2 0) = true := by decide +kernel

theorem metricCover_q00_dual_21 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 2 1) (pick cmet_q00_dual 2 1) = true := by decide +kernel

theorem metricCover_q00_dual_22 : jetCovered (localMetricJetBall .bcc true (qbox false false) (shortChart .bcc (qbox false false)) 2 2) (pick cmet_q00_dual 2 2) = true := by decide +kernel

theorem metricCover_q00_dual : ∀ i j, jetCovered (localMetricJetBall .bcc true (qbox false false)
    (shortChart .bcc (qbox false false)) i j) (pick cmet_q00_dual i j) = true := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [metricCover_q00_dual_00, metricCover_q00_dual_01, metricCover_q00_dual_02, metricCover_q00_dual_10, metricCover_q00_dual_11, metricCover_q00_dual_12, metricCover_q00_dual_20, metricCover_q00_dual_21, metricCover_q00_dual_22]

theorem chart_q01 : strainMetricCheck .bcc (qbox false true) (shortChart .bcc (qbox false true)) = true := by decide +kernel

theorem metricCover_q01_dual_00 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 0 0) (pick cmet_q01_dual 0 0) = true := by decide +kernel

theorem metricCover_q01_dual_01 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 0 1) (pick cmet_q01_dual 0 1) = true := by decide +kernel

theorem metricCover_q01_dual_02 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 0 2) (pick cmet_q01_dual 0 2) = true := by decide +kernel

theorem metricCover_q01_dual_10 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 1 0) (pick cmet_q01_dual 1 0) = true := by decide +kernel

theorem metricCover_q01_dual_11 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 1 1) (pick cmet_q01_dual 1 1) = true := by decide +kernel

theorem metricCover_q01_dual_12 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 1 2) (pick cmet_q01_dual 1 2) = true := by decide +kernel

theorem metricCover_q01_dual_20 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 2 0) (pick cmet_q01_dual 2 0) = true := by decide +kernel

theorem metricCover_q01_dual_21 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 2 1) (pick cmet_q01_dual 2 1) = true := by decide +kernel

theorem metricCover_q01_dual_22 : jetCovered (localMetricJetBall .bcc true (qbox false true) (shortChart .bcc (qbox false true)) 2 2) (pick cmet_q01_dual 2 2) = true := by decide +kernel

theorem metricCover_q01_dual : ∀ i j, jetCovered (localMetricJetBall .bcc true (qbox false true)
    (shortChart .bcc (qbox false true)) i j) (pick cmet_q01_dual i j) = true := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [metricCover_q01_dual_00, metricCover_q01_dual_01, metricCover_q01_dual_02, metricCover_q01_dual_10, metricCover_q01_dual_11, metricCover_q01_dual_12, metricCover_q01_dual_20, metricCover_q01_dual_21, metricCover_q01_dual_22]

theorem chart_q10 : strainMetricCheck .bcc (qbox true false) (shortChart .bcc (qbox true false)) = true := by decide +kernel

theorem metricCover_q10_dual_00 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 0 0) (pick cmet_q10_dual 0 0) = true := by decide +kernel

theorem metricCover_q10_dual_01 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 0 1) (pick cmet_q10_dual 0 1) = true := by decide +kernel

theorem metricCover_q10_dual_02 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 0 2) (pick cmet_q10_dual 0 2) = true := by decide +kernel

theorem metricCover_q10_dual_10 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 1 0) (pick cmet_q10_dual 1 0) = true := by decide +kernel

theorem metricCover_q10_dual_11 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 1 1) (pick cmet_q10_dual 1 1) = true := by decide +kernel

theorem metricCover_q10_dual_12 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 1 2) (pick cmet_q10_dual 1 2) = true := by decide +kernel

theorem metricCover_q10_dual_20 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 2 0) (pick cmet_q10_dual 2 0) = true := by decide +kernel

theorem metricCover_q10_dual_21 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 2 1) (pick cmet_q10_dual 2 1) = true := by decide +kernel

theorem metricCover_q10_dual_22 : jetCovered (localMetricJetBall .bcc true (qbox true false) (shortChart .bcc (qbox true false)) 2 2) (pick cmet_q10_dual 2 2) = true := by decide +kernel

theorem metricCover_q10_dual : ∀ i j, jetCovered (localMetricJetBall .bcc true (qbox true false)
    (shortChart .bcc (qbox true false)) i j) (pick cmet_q10_dual i j) = true := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [metricCover_q10_dual_00, metricCover_q10_dual_01, metricCover_q10_dual_02, metricCover_q10_dual_10, metricCover_q10_dual_11, metricCover_q10_dual_12, metricCover_q10_dual_20, metricCover_q10_dual_21, metricCover_q10_dual_22]

theorem chart_q11 : strainMetricCheck .bcc (qbox true true) (shortChart .bcc (qbox true true)) = true := by decide +kernel

theorem metricCover_q11_dual_00 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 0 0) (pick cmet_q11_dual 0 0) = true := by decide +kernel

theorem metricCover_q11_dual_01 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 0 1) (pick cmet_q11_dual 0 1) = true := by decide +kernel

theorem metricCover_q11_dual_02 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 0 2) (pick cmet_q11_dual 0 2) = true := by decide +kernel

theorem metricCover_q11_dual_10 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 1 0) (pick cmet_q11_dual 1 0) = true := by decide +kernel

theorem metricCover_q11_dual_11 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 1 1) (pick cmet_q11_dual 1 1) = true := by decide +kernel

theorem metricCover_q11_dual_12 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 1 2) (pick cmet_q11_dual 1 2) = true := by decide +kernel

theorem metricCover_q11_dual_20 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 2 0) (pick cmet_q11_dual 2 0) = true := by decide +kernel

theorem metricCover_q11_dual_21 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 2 1) (pick cmet_q11_dual 2 1) = true := by decide +kernel

theorem metricCover_q11_dual_22 : jetCovered (localMetricJetBall .bcc true (qbox true true) (shortChart .bcc (qbox true true)) 2 2) (pick cmet_q11_dual 2 2) = true := by decide +kernel

theorem metricCover_q11_dual : ∀ i j, jetCovered (localMetricJetBall .bcc true (qbox true true)
    (shortChart .bcc (qbox true true)) i j) (pick cmet_q11_dual i j) = true := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [metricCover_q11_dual_00, metricCover_q11_dual_01, metricCover_q11_dual_02, metricCover_q11_dual_10, metricCover_q11_dual_11, metricCover_q11_dual_12, metricCover_q11_dual_20, metricCover_q11_dual_21, metricCover_q11_dual_22]

theorem penaltyOK : penaltyCheck .bcc ballRoot (shortChart .bcc ballRoot) penalty = true := by decide +kernel

end BccSharp.Coulomb.BravaisCover.FixedLocal.BccBall
