import BccSharp.Lattice.LocalBallsBccAnalytic
import BccSharp.Lattice.LocalBallsBccModes
import BccSharp.Lattice.LocalBallsBccMetric
import BccSharp.Lattice.LocalBallsBccSlabBallDirect
import BccSharp.Lattice.LocalBallsBccSlabQ00Dual
import BccSharp.Lattice.LocalBallsBccSlabQ01Dual
import BccSharp.Lattice.LocalBallsBccSlabQ10Dual
import BccSharp.Lattice.LocalBallsBccSlabQ11Dual

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

/-! BCC local ball: `NonzeroLocalStrain .bcc` from the checked witness on
`analyticLocalBox` and the curvature enclosures on the ball box. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.FixedLocal.BccBall
open BccSharp
open BccSharp.Intervals (Ball)
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.FixedLocal
open Constants.HighPrecision

theorem family_ball_direct : FamilyHessian .bcc false radius (ballRoot)
    (sideSum radius (pickSlab cslab_ball_direct)) :=
  cartFamily .bcc false (ballRoot) (shortChart .bcc (ballRoot)) chart_ball (pick cmet_ball_direct)
    metricCover_ball_direct lengthRoot lengthOK rootSquareOK radius (pickSlab cslab_ball_direct) slabs_ball_direct

theorem family_q00_dual : FamilyHessian .bcc true radius (qbox false false)
    (sideSum radius (pickSlab cslab_q00_dual)) :=
  cartFamily .bcc true (qbox false false) (shortChart .bcc (qbox false false)) chart_q00 (pick cmet_q00_dual)
    metricCover_q00_dual lengthRoot lengthOK rootSquareOK radius (pickSlab cslab_q00_dual) slabs_q00_dual

theorem family_q01_dual : FamilyHessian .bcc true radius (qbox false true)
    (sideSum radius (pickSlab cslab_q01_dual)) :=
  cartFamily .bcc true (qbox false true) (shortChart .bcc (qbox false true)) chart_q01 (pick cmet_q01_dual)
    metricCover_q01_dual lengthRoot lengthOK rootSquareOK radius (pickSlab cslab_q01_dual) slabs_q01_dual

theorem family_q10_dual : FamilyHessian .bcc true radius (qbox true false)
    (sideSum radius (pickSlab cslab_q10_dual)) :=
  cartFamily .bcc true (qbox true false) (shortChart .bcc (qbox true false)) chart_q10 (pick cmet_q10_dual)
    metricCover_q10_dual lengthRoot lengthOK rootSquareOK radius (pickSlab cslab_q10_dual) slabs_q10_dual

theorem family_q11_dual : FamilyHessian .bcc true radius (qbox true true)
    (sideSum radius (pickSlab cslab_q11_dual)) :=
  cartFamily .bcc true (qbox true true) (shortChart .bcc (qbox true true)) chart_q11 (pick cmet_q11_dual)
    metricCover_q11_dual lengthRoot lengthOK rootSquareOK radius (pickSlab cslab_q11_dual) slabs_q11_dual

theorem penaltyEnclosure : PenaltyEnclosure .bcc ballRoot penalty :=
  penaltyEnclosure_of_check .bcc ballRoot (shortChart .bcc ballRoot) chart_ball penalty penaltyOK

theorem tailOnBall : TailControl .bcc radius ballRoot analyticData.tailRadius :=
  (analyticData.tailControl analyticBase).mono ballRoot_sub_analytic

theorem curvatureLdl_q00 : curvatureOf (sideSum radius (pickSlab cslab_ball_direct))
    (sideSum radius (pickSlab cslab_q00_dual)) penalty analyticData.tailRadius = true := by decide +kernel

theorem curvatureLdl_q01 : curvatureOf (sideSum radius (pickSlab cslab_ball_direct))
    (sideSum radius (pickSlab cslab_q01_dual)) penalty analyticData.tailRadius = true := by decide +kernel

theorem curvatureLdl_q10 : curvatureOf (sideSum radius (pickSlab cslab_ball_direct))
    (sideSum radius (pickSlab cslab_q10_dual)) penalty analyticData.tailRadius = true := by decide +kernel

theorem curvatureLdl_q11 : curvatureOf (sideSum radius (pickSlab cslab_ball_direct))
    (sideSum radius (pickSlab cslab_q11_dual)) penalty analyticData.tailRadius = true := by decide +kernel

theorem qbox_sub (u0 u1 : Bool) (p : Point) (hp : (qbox u0 u1).Mem p) : ballRoot.Mem p := by
  have b0 : (0 : ℚ) ≤ beta/2 ∧ beta/2 ≤ beta := by norm_num [beta]
  exact split_sub ballRoot 0 (beta/2) u0 (by simpa [ballRoot, strainBox] using b0) p
    (split_sub _ 1 (beta/2) u1 (by simpa [split, ballRoot, strainBox] using b0) p hp)

/-- The reciprocal slab sums of the sub-box `qbox u0 u1`. -/
def dualSlab : Bool → Bool → List (Fin 5 → Fin 5 → FBall)
  | false, false => cslab_q00_dual
  | false, true => cslab_q01_dual
  | true, false => cslab_q10_dual
  | true, true => cslab_q11_dual

theorem curvature_on_qbox (u0 u1 : Bool) (p : Point) (h : (qbox u0 u1).Mem p)
    (ldl : curvatureOf (sideSum radius (pickSlab cslab_ball_direct))
      (sideSum radius (pickSlab (dualSlab u0 u1))) penalty analyticData.tailRadius = true)
    (hU : FamilyHessian .bcc true radius (qbox u0 u1) (sideSum radius (pickSlab (dualSlab u0 u1)))) :
    ∀ v : Point, v ≠ 0 → 0 < hessianQuadratic (localSignedHessian .bcc p) v :=
  curvature_of_families .bcc (qbox u0 u1) radius _ _ (family_ball_direct.mono (qbox_sub u0 u1)) hU penalty
    (penaltyEnclosure.mono (qbox_sub u0 u1)) analyticData.tailRadius (tailOnBall.mono (qbox_sub u0 u1)) ldl p h

theorem curvature : ∀ p, ballRoot.Mem p → ∀ v : Point, v ≠ 0 →
    0 < hessianQuadratic (localSignedHessian .bcc p) v := by
  intro p hp
  rcases split_covers ballRoot 0 (beta/2) p hp with h0 | h0 <;>
    rcases split_covers _ 1 (beta/2) p h0 with h1 | h1
  · exact curvature_on_qbox false false p h1 curvatureLdl_q00 family_q00_dual
  · exact curvature_on_qbox false true p h1 curvatureLdl_q01 family_q01_dual
  · exact curvature_on_qbox true false p h1 curvatureLdl_q10 family_q10_dual
  · exact curvature_on_qbox true true p h1 curvatureLdl_q11 family_q11_dual

theorem nonzeroLocalStrain_bcc : NonzeroLocalStrain .bcc :=
  nonzeroLocalStrain_of_checks .bcc analyticData analyticBase analyticModes positiveOK (fun _ => spectralOK) curvature

end BccSharp.Coulomb.BravaisCover.FixedLocal.BccBall
