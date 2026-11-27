import BccSharp.Lattice.LocalBallsFccAnalytic
import BccSharp.Lattice.LocalBallsFccModes
import BccSharp.Lattice.LocalBallsFccMetric
import BccSharp.Lattice.LocalBallsFccSlabBallDirect
import BccSharp.Lattice.LocalBallsFccSlabBallDual

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! FCC local ball: `NonzeroLocalStrain .fcc` from the checked witness on
`analyticLocalBox` and the curvature enclosures on the ball box. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

theorem family_ball_direct : FamilyHessian .fcc false radius (ballRoot)
    (sideSum radius (pickSlab cslab_ball_direct)) :=
  cartFamily .fcc false (ballRoot) (shortChart .fcc (ballRoot)) chart_ball (pick cmet_ball_direct)
    metricCover_ball_direct lengthRoot lengthOK rootSquareOK radius (pickSlab cslab_ball_direct) slabs_ball_direct

theorem family_ball_dual : FamilyHessian .fcc true radius (ballRoot)
    (sideSum radius (pickSlab cslab_ball_dual)) :=
  cartFamily .fcc true (ballRoot) (shortChart .fcc (ballRoot)) chart_ball (pick cmet_ball_dual)
    metricCover_ball_dual lengthRoot lengthOK rootSquareOK radius (pickSlab cslab_ball_dual) slabs_ball_dual

theorem penaltyEnclosure : PenaltyEnclosure .fcc ballRoot penalty :=
  penaltyEnclosure_of_check .fcc ballRoot (shortChart .fcc ballRoot) chart_ball penalty penaltyOK

theorem tailOnBall : TailControl .fcc radius ballRoot analyticData.tailRadius :=
  (analyticData.tailControl analyticBase).mono ballRoot_sub_analytic

theorem curvatureLdl : curvatureOf (sideSum radius (pickSlab cslab_ball_direct))
    (sideSum radius (pickSlab cslab_ball_dual)) penalty analyticData.tailRadius = true := by decide +kernel

theorem curvature : ∀ p, ballRoot.Mem p → ∀ v : Point, v ≠ 0 →
    0 < hessianQuadratic (localSignedHessian .fcc p) v :=
  curvature_of_families .fcc ballRoot radius _ _ family_ball_direct family_ball_dual penalty penaltyEnclosure
    analyticData.tailRadius tailOnBall curvatureLdl

theorem nonzeroLocalStrain_fcc : NonzeroLocalStrain .fcc :=
  nonzeroLocalStrain_of_checks .fcc analyticData analyticBase analyticModes positiveOK (fun h => by cases h) curvature

end BccSharp.Coulomb.BravaisCover.FixedLocal.FccBall
