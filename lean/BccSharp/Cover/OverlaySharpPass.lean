import BccSharp.Cover.OverlaySharpLayer

set_option autoImplicit false

/-! One kernel evaluation per Overlay planar leaf.

The shared inputs are proved once here: the radius-three triangular check,
a short rational below `triangleBound 3` (the exact bound has 42,678-digit
terms), the FCC threshold `fccHUpper - 4` as a literal, and the cube-root
check behind `fccHUpper`. A leaf is then paid by `sharpPass raw = true`,
which `decide +kernel` evaluates in a single declaration. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)

theorem triangleCheck_three : triangleCheck 3=true := by
  unfold triangleCheck
  rw [toList_all_eq]
  decide +kernel

/-- `triangleBound 3` rounded down to the grid `2⁻⁹⁶`. -/
def triangleThreeLower : ℚ := -310656127136035198602788211147/79228162514264337593543950336

theorem triangleThreeLower_le : triangleThreeLower ≤ triangleBound 3 := by decide +kernel

theorem triangleThreeLower_sound : (triangleThreeLower : ℝ)≤ triangleRegularized :=
  (Rat.cast_le.mpr triangleThreeLower_le).trans (triangleRegularized_lower 3 triangleCheck_three)

/-- The exact value of `fccHUpper - 4`. -/
def fccThreshold : ℚ :=
  -5267103427540847260762869168861205063086684376060021184073250797343161583775235960616348073451267701366961926100916314104523/
    1447401115466452442794637312608598848165874808320507050493219800098914120499200000000000000000000000000000000000000000000000

theorem fccThreshold_eq : fccHUpper-4=fccThreshold := by decide +kernel

theorem scaleRoot_ok : cubeRootCheck scaleWitness scaleInput=true := by decide +kernel

/-- The single per-leaf check: the cube radius 2, the shared
triangular constant, and the strict FCC threshold. -/
def sharpPass (raw : Cell) : Bool :=
  sharpCheck raw 2 triangleThreeLower && decide (fccThreshold< sharpLower raw 2 triangleThreeLower)

theorem sharpPass_sound {raw : Cell} (ok : sharpPass raw=true) {p : Chart} (hp : raw.Mem p) :
    2*ac*energy fcc< triangularRelaxation (seamPoint raw p) := by
  obtain ⟨c,s⟩ := Bool.and_eq_true_iff.mp ok
  have strict : fccHUpper-4< sharpLower raw 2 triangleThreeLower := by
    rw [fccThreshold_eq]
    exact of_decide_eq_true s
  have h := fccHUpper_sound scaleRoot_ok
  have s' : (fccHUpper : ℝ)-4<(sharpLower raw 2 triangleThreeLower : ℝ) := by exact_mod_cast strict
  exact (show 2*ac*energy fcc≤(fccHUpper : ℝ)-4 by linarith only [h]).trans_lt
    (s'.trans_le (sharpLower_sound hp triangleThreeLower_sound c))

/-! ### Addresses

Each hexadecimal path digit `d = 2*axis+side` selects the closed lower
(`side = 0`) or upper (`side = 1`) midpoint child along `axis`. -/

def digitChild (b : Cell) (d : ℕ) : Cell :=
  (Cut.dyadic ⟨d/2 % 8,Nat.mod_lt _ (by decide)⟩).child b (d % 2=1)

def descend (b : Cell) : List ℕ → Cell
  | [] => b
  | d :: ds => descend (digitChild b d) ds

end BccSharp.Coulomb.CompactCover.OverlayPlanar
