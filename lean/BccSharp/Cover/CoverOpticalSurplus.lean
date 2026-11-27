import BccSharp.Cover.CoverAssembly
import BccSharp.Lattice.LdlCurvature
import BccSharp.Lattice.E2Core

set_option autoImplicit false

/-! Common signed-matrix check for the relative optical branch.
An LDL pivot checks the shifted interval matrix. The rational displacement
coefficient is independently subtracted against the actual period metric. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Intervals (Ball)
open LatePackets
open BravaisCover (BallMatrix LdlWitness ldlCheck ldlCheck_sound hessianQuadratic hessianQuadratic_eq_quad)

def surplusMatrix (E G : BallMatrix 3) (cost k : ℚ) : BallMatrix 3 :=
  fun i j => (E i j).sub ((Ball.exact (Constants.gapBracket.hi*cost+k)).mul (G i j))

def opticalSurplusCheck (E G : BallMatrix 3) (cost margin k : ℚ) (factor : LdlWitness 3) : Bool :=
  (decide (0≤ cost) && relativeCheck margin k) && ldlCheck (surplusMatrix E G cost k) factor

theorem opticalSurplus_sound (E G : BallMatrix 3) (A B : Mat) (cost margin k : ℚ) (factor : LdlWitness 3)
    (arith : opticalSurplusCheck E G cost margin k factor=true)
    (eA : ∀ i j, (E i j).Contains (A i j)) (eB : ∀ i j, (G i j).Contains ((gram B) i j))
    (d : Vec) : ((Constants.gapBracket.hi : ℝ)*(cost : ℝ)+(k : ℝ))*sq (B.mulVec d) ≤ quad A d := by
  let c : ℝ := (Constants.gapBracket.hi : ℝ)*(cost : ℝ)+(k : ℝ)
  let R : Mat := fun i j => A i j-c*(gram B) i j
  have enc (i j : Fin 3) : (surplusMatrix E G cost k i j).Contains (R i j) := by
    unfold surplusMatrix R c
    simpa only [Rat.cast_add,Rat.cast_mul] using Ball.contains_sub (eA i j)
      (Ball.contains_mul (Ball.contains_exact (Constants.gapBracket.hi*cost+k)) (eB i j))
  have expanded : hessianQuadratic R d=quad A d-c*sq (B.mulVec d) := by
    rw [sq_mulVec_gram,← hessianQuadratic_eq_quad,← hessianQuadratic_eq_quad]
    simp only [hessianQuadratic,R,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  by_cases hd : d=0
  · subst d
    simp [quad,sq]
  · have positive := ldlCheck_sound _ factor (Bool.and_eq_true_iff.mp arith).2 R enc d hd
    rw [expanded] at positive
    linarith only [positive]

/-- Separately checked Ewald and defect bounds give relative optical
strictness off the registered anchor, including zero uniform margin. -/
theorem relativeOptical_of_signed_matrix (latticeCase : LatticeCase) (p : Chart) (gp : good p)
    (half : HalfWitness) (nonzero : ∃ i, half.bits i=true)
    (E G : BallMatrix 3) (A : Mat) (cost margin k : ℚ) (factor : LdlWitness 3)
    (arith : opticalSurplusCheck E G cost margin k factor=true)
    (hE : ∀ i j, (E i j).Contains (A i j))
    (hG : ∀ i j, (G i j).Contains ((gram (chartPoint p).basis) i j))
    (energyGain : energy (anchorOf (chartPoint p) half.anchor)+(margin : ℝ)+
       quad A ((chartPoint p).offset-half.anchor-castVec half.wrap) ≤ energy (chartPoint p))
    (costIncrease : defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) half.anchor)+(cost : ℝ)*
       sq ((chartPoint p).basis.mulVec ((chartPoint p).offset-half.anchor-castVec half.wrap))) :
    Route.result .relativeOptical p := by
  have flags := (Bool.and_eq_true_iff.mp arith).1
  obtain ⟨pc,rel⟩ := Bool.and_eq_true_iff.mp flags
  have hn : 0≤ cost := of_decide_eq_true pc
  have hC : (0 : ℝ)≤ cost := by exact_mod_cast hn
  let q := chartPoint p
  let a := anchorOf q half.anchor
  let d := q.offset-half.anchor-castVec half.wrap
  have pos := Constants.reference_gap_checked
  have cap := mul_le_mul_of_nonneg_left costIncrease pos.2.le
  have curvature := opticalSurplus_sound E G A q.basis cost margin k factor arith hE hG d
  have spend := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right pos.1.2 hC)
    (sq_nonnegative (q.basis.mulVec d))
  apply relativeOptical_route_of_lattice latticeCase p gp.1 half.anchor half.wrap (half.anchor_sound nonzero) margin k rel
  change deficit a+(margin : ℝ)+(k : ℝ)*sq (q.basis.mulVec d)≤deficit q
  change energy a+(margin : ℝ)+quad A d≤energy q at energyGain
  change gap*defect q≤gap*(defect a+(cost : ℝ)*sq (q.basis.mulVec d)) at cap
  unfold deficit
  nlinarith only [energyGain,cap,curvature,spend]

end BccSharp.Coulomb.CompactCover
