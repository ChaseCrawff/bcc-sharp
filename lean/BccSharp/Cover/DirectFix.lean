import BccSharp.Cover.DirectFixConst
import BccSharp.Cover.OverlayFix
import BccSharp.Cover.CoverEarlyDecode

set_option autoImplicit false

/-! A fixed-point evaluator for the original direct route.

`DirectRoute.check` pays a leaf through exact rational arithmetic: a 252-step
bisection for every square root and a 96-term rational `erfc` series per
mode. In the kernel one radius-one leaf took 150 s and 13 GB. This
evaluator computes its own lower bound of the same finite positive part of
the series, with integer endpoints at the Overlay scale `S = 2^96`
(`BccSharp.Cover.OverlayFix`):

* the squared distances are `FI` interval expressions in the eight box
  coordinates (exact endpoint products, outward rounding), the same
  factorization as `DirectRoute.realDistance` and `DirectRoute.reciprocalDistance`;
* the half kernel `G(1/2, t) = √π erfc(√t)/√t` at an upper end `t = T/S` of
  `π q` is bounded below by `√π/√t - 2 series(t) - 4 t^96/96!`, with `series = Erfc.series t 96`
  evaluated exactly by Horner's rule over `ℕ` in `T²` with literal
  coefficients (`BccSharp.Cover.DirectFixConst`), for `0 < t ≤ 24`; larger arguments
  contribute the lower bound `0`;
* the reciprocal kernel `e^(-t)/t` uses the Overlay exponential `expNegPt`, and
  the phase factor `1 + cos(2π m·f)` the Overlay cosine range `cosRange`.

Every omitted term of the series is nonnegative, so the finite sum bounds
`h₂` from below; the comparison is against an integer threshold
`thrZ ≥ S (4 + 2 a_c^lo e_FCC^hi)`. Soundness is `BccSharp.Cover.DirectFixSound`. -/

namespace BccSharp.Coulomb.CompactCover.DirectFix
open BccSharp BccSharp.Coverage DirectRoute OverlayPlanar.Fix

/-! ### Scalars -/

/-- An upper end of `π q`, in units of `1/S`, from an upper end `Q/S` of `q`. -/
def piTimes (Q : ℤ) : ℕ := (cdivZ (twoPiHi * Q) (2 * Sz)).toNat

/-- A lower bound, in units of `1/S`, of the half kernel `G(1/2, t)` at
`t = T/S`: `√π/√t - 2 Erfc.series t 96 - 4 t^96/96!` for `0 < t ≤ 24`, and
`0` otherwise. `G(1/2, ·)` is decreasing, so it bounds `G(1/2, x)` for every
`0 < x ≤ t`. -/
def halfLowF (T : ℕ) : ℤ :=
  if 0 < T ∧ T ≤ halfTMax then
    let acc : ℤ := (hornerN (T * T) erfPosC : ℤ) - ((T * hornerN (T * T) erfNegC : ℕ) : ℤ)
    max 0 (((sqrtPiLo * S / sqrtHi (T * S) : ℕ) : ℤ) - 2 * cdivZ acc (erfDS : ℤ) - erfErr)
  else 0

/-- A lower bound, in units of `1/S`, of `G(1, t) = e^(-t)/t` at `t = T/S`. -/
def oneLowF (T : ℕ) : ℤ := if 0 < T then (expNegPt T).lo * Sz / (T : ℤ) else 0

/-! ### Distances and phases on a box -/

def vecF (b : Cell) (cross : Bool) (n : IntVec) (i : Fin 3) : FI :=
  if cross then (FI.ofInt (n i)).add (cx b (offset i)) else FI.ofInt (n i)

/-- The squared length of the direct image `B (n + f)` (cross) or `B n`, in the
factorized form of `DirectRoute.realDistance`. -/
def realDistF (b : Cell) (cross : Bool) (n : IntVec) : FI :=
  let v := vecF b cross n
  let r := cx b 0
  let s := cx b 1
  let u := FI.mul r ((v 0).add ((FI.mul (cx b 2) (v 1)).add (FI.mul (cx b 3) (v 2))))
  let w := FI.mul s ((v 1).add (FI.mul (cx b 4) (v 2)))
  let z := FI.mul (FI.mulPos r s).invPos (v 2)
  (FI.sq u).add ((FI.sq w).add (FI.sq z))

/-- The reciprocal squared length `nᵀ (BᵀB)⁻¹ n`, in the form of
`DirectRoute.reciprocalDistance`. -/
def recipDistF (b : Cell) (n : IntVec) : FI :=
  let r := cx b 0
  let s := cx b 1
  let a := cx b 2
  let c := cx b 4
  let u := FI.smul (n 0) r.invPos
  let v := FI.mul ((FI.ofInt (n 1)).sub (FI.smul (n 0) a)) s.invPos
  let z := ((FI.ofInt (n 2)).sub (FI.smul (n 1) c)).add (FI.smul (n 0) ((FI.mul a c).sub (cx b 3)))
  (FI.sq u).add ((FI.sq v).add (FI.sq (FI.mul z (FI.mulPos r s))))

/-- The phase `m · f` in turns. -/
def turnsF (b : Cell) (n : IntVec) : FI :=
  (FI.smul (n 0) (cx b 5)).add ((FI.smul (n 1) (cx b 6)).add (FI.smul (n 2) (cx b 7)))

/-- A lower bound, in units of `1/S`, of `1 + cos(2π m·f)` on the box. -/
def phaseLowF (b : Cell) (n : IntVec) : ℤ :=
  let v := turnsF b n
  max 0 (Sz + (cosRange v.lo v.hi).lo)

/-! ### The three families and the finite sum -/

def crossF (b : Cell) (n : IntVec) : ℤ := halfLowF (piTimes (realDistF b true n).hi)
def periodF (b : Cell) (n : IntVec) : ℤ := halfLowF (piTimes (realDistF b false n).hi)
def recipF (b : Cell) (n : IntVec) : ℤ :=
  phaseLowF b n * max 0 (oneLowF (piTimes (recipDistF b n).hi)) / Sz

def sumZ (f : IntVec → ℤ) : List IntVec → ℤ
  | [] => 0
  | n :: ns => f n + sumZ f ns

/-- A lower bound, in units of `1/S`, of `h₂` on the box: every cross mode of
the cube, and twice every lexicographically positive period and reciprocal
mode. -/
def valueF (b : Cell) (radius : ℕ) : ℤ :=
  sumZ (crossF b) (directIndices radius) + 2 * sumZ (periodF b) (pairedIndices radius) +
    2 * sumZ (recipF b) (pairedIndices radius)

/-- The positive radial coordinates and their product, as the interval
inverses require. -/
def guardsF (b : Cell) : Bool :=
  decide (0 < (cx b 0).lo ∧ 0 < (cx b 1).lo ∧ 0 < (FI.mulPos (cx b 0) (cx b 1)).lo)

/-- The per-leaf check: cube radius one, then two. -/
def directFix (b : Cell) : Bool :=
  guardsF b && (decide (thrZ < valueF b 1) || decide (thrZ < valueF b 2))

end BccSharp.Coulomb.CompactCover.DirectFix
