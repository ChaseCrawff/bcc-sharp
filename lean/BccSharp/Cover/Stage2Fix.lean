import BccSharp.Cover.DirectFixSound

set_option autoImplicit false

/-! A fixed-point evaluator for the Stage2 bulk routes.

`Stage2.bulkCheck` evaluates every anchor tangent with rational balls, a
252-step bisection per square root and a large rational `erfc` series; on
the thinnest tangent row the kernel passed 18 GB within two
minutes. This evaluator keeps the checker's mathematics (global tangents at
the recorded anchors, the reciprocal phase floor as multiplier, the joint
closed-corner maximum of the weighted squared lengths, the signed-triad
phase budget) and changes only how the numbers are computed:

* the tangent at anchor `x = ticks/2^30` is evaluated at the Overlay scale
  `S = 2^96` from the Direct fixed-point kernels (`halfLowF`, `oneLowF`) and two
  new upper bounds (`halfHighF`, `oneHighF`): intercept
  `(1+p) G(πx) + e^(-πx)` from below and penalty `(e^(-πx) + p G(πx))/x` from
  above, `p = 1/2` or `1`;
* the phase floor is the Direct `phaseLowF` (Overlay cosine range);
* the weights and moments are integer list folds (`directZ`, `recipZ`,
  `linearZ`, `massZ`), and the joint corner bound is an explicit fold over the
  32 shape and 8 offset corners in place of `Finset.univ.sup'` over functions:
  on the grid `2^-20` each corner value `S · packedCorner`, multiplied by
  `2^160 R₁²R₂²` with the grid integers `R = 2^20 r` of the radial coordinates
  (that is by `2^240 r₁²r₂²`), is the integer `K² P·X + D·R` (`foldZ`),
  compared with the cap
  `Σ intercepts - thrZ - 1` (plus the phase gain); `cornerMax` is the same
  maximum in exact rationals, kept as the reference;
* the reciprocal capacities use `oneLowF` at the exact 32-corner maximum of
  the reciprocal squared length.

Soundness is `BccSharp.Cover.Stage2FixSound`. -/

namespace BccSharp.Coulomb.CompactCover.Stage2Fix
open BccSharp BccSharp.Coverage DirectRoute OverlayPlanar.Fix DirectFix Stage2 BravaisCover

/-! ### Upper bounds of the two kernels -/

/-- An upper bound, in units of `1/S`, of `e^(-t)/t` at `t = T/S`, for `T > 0`. -/
def oneHighF (T : ℕ) : ℤ := cdivZ ((expNegPt T).hi * Sz) (T : ℤ)

/-- An upper bound, in units of `1/S`, of `G(1/2, t)` at `t = T/S`, for `T > 0`:
`√π/√t - 2 Erfc.series t 96 + 4 t^96/96!` for `t ≤ 24`, else `e^(-t)/t`. -/
def halfHighF (T : ℕ) : ℤ :=
  if T ≤ halfTMax ∧ 0 < sqrtLo (T * S) then
    let acc : ℤ := (hornerN (T * T) erfPosC : ℤ) - ((T * hornerN (T * T) erfNegC : ℕ) : ℤ)
    ((cdivN (sqrtPiHi * S) (sqrtLo (T * S)) : ℕ) : ℤ) - 2 * (acc / (erfDS : ℤ)) + erfErr
  else oneHighF T

/-! ### Tangents at the anchors -/

/-- `S / 2^30`: the anchor `ticks/2^30` is `ticks * anchorScale / S`. -/
def anchorScale : ℕ := 73786976294838206464

/-- A lower end of `π x`, in units of `1/S`, from `x = X/S`. -/
def piLow (X : ℕ) : ℕ := twoPiLo.toNat * X / (2 * S)

structure TangentF where
  intercept : ℤ
  penalty : ℤ

/-- The global tangent of `kernelValue kind (π ·)` at `x = ticks/2^30`: an
intercept from below and a nonnegative penalty slope from above. -/
def tangentF (kind : KernelKind) (ticks : ℕ) : Option TangentF :=
  let X := ticks * anchorScale
  let Thi := piTimes (X : ℤ)
  let Tlo := piLow X
  if 0 < ticks ∧ 0 < Tlo then
    let Elo := (expNegPt Thi).lo
    let Ehi := (expNegPt Tlo).hi
    match kind with
    | .half => some ⟨3 * halfLowF Thi / 2 + Elo,
        max 0 (cdivZ ((2 * Ehi + halfHighF Tlo) * Sz) (2 * (X : ℤ)))⟩
    | .one => some ⟨2 * oneLowF Thi + Elo, max 0 (cdivZ ((Ehi + oneHighF Tlo) * Sz) (X : ℤ))⟩
  else none

/-! ### Lines -/

/-- A checked line in units of `1/S`. -/
structure LineF where
  mode : Mode
  intercept : ℤ
  penalty : ℤ
  floor : ℤ

/-- The reciprocal phase floor `1 + cos(2π m·f)` from below; `1` otherwise. -/
def floorF (b : Cell) (m : Mode) : ℤ := if m.family = .reciprocal then phaseLowF b m.index else Sz

/-- The line multiplier: `1` for a cross mode, twice the floor otherwise. -/
def multF (b : Cell) (m : Mode) : ℤ := if m.family = .cross then Sz else 2 * floorF b m

def evalLineF (b : Cell) (r : AnchorRow) : Option LineF :=
  if decide r.mode.valid then
    (tangentF r.mode.kind r.ticks).map fun t =>
      ⟨r.mode, multF b r.mode * t.intercept / Sz, cdivZ (multF b r.mode * t.penalty) Sz, floorF b r.mode⟩
  else none

def prepareF (b : Cell) : List AnchorRow → Option (List LineF)
  | [] => some []
  | r :: rs =>
    match evalLineF b r, prepareF b rs with
    | some l, some ls => some (l :: ls)
    | _, _ => none

/-- The same line in the rational form of `Stage2.Line`. -/
def LineF.toLine (l : LineF) : Line :=
  ⟨l.mode, (l.intercept : ℚ) / S, (l.penalty : ℚ) / S, (l.floor : ℚ) / S⟩

/-! ### Moments and the corner maximum -/

def intMoment (n : IntVec) (j : Fin 6) : ℤ := n (metricPair j).1 * n (metricPair j).2

def sumL (f : LineF → ℤ) : List LineF → ℤ
  | [] => 0
  | l :: ls => f l + sumL f ls

/-- The integer moments of the penalty weights, in units of `1/S`. -/
def directZ (ys : List LineF) (j : Fin 6) : ℤ :=
  sumL (fun l => if l.mode.family ≠ .reciprocal then l.penalty * intMoment l.mode.index j else 0) ys
def recipZ (ys : List LineF) (j : Fin 6) : ℤ :=
  sumL (fun l => if l.mode.family = .reciprocal then l.penalty * intMoment l.mode.index j else 0) ys
def linearZ (ys : List LineF) (i : Fin 3) : ℤ :=
  sumL (fun l => if l.mode.family = .cross then l.penalty * l.mode.index i else 0) ys
def massZ (ys : List LineF) : ℤ :=
  sumL (fun l => if l.mode.family = .cross then l.penalty else 0) ys

def momentsQ (ys : List LineF) : Moments :=
  ⟨fun j => (directZ ys j : ℚ) / S, fun j => (recipZ ys j : ℚ) / S,
    fun i => (linearZ ys i : ℚ) / S, (massZ ys : ℚ) / S⟩

/-- The 32 shape corners and the 8 offset corners, as explicit lists. -/
def shapeList : List (Fin 5 → Bool) := (List.range 32).map fun k i => Nat.testBit k i.val
def offsetList : List (Fin 3 → Bool) := (List.range 8).map fun k i => Nat.testBit k i.val

def listMax (init : ℚ) : List ℚ → ℚ
  | [] => init
  | x :: xs => listMax (max init x) xs

/-- `sixDot` written out, without a `Finset` sum. -/
def dot6 (v w : Metric6) : ℚ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 + v 4 * w 4 + v 5 * w 5

/-- `Moments.shift` written out. -/
def shift6 (g : Moments) (f : Fin 3 → ℚ) : Metric6 :=
  ![g.direct 0 + g.crossLinear 0 * f 0 + g.crossLinear 0 * f 0 + g.crossMass * f 0 * f 0,
    g.direct 1 + g.crossLinear 1 * f 1 + g.crossLinear 1 * f 1 + g.crossMass * f 1 * f 1,
    g.direct 2 + g.crossLinear 2 * f 2 + g.crossLinear 2 * f 2 + g.crossMass * f 2 * f 2,
    g.direct 3 + g.crossLinear 0 * f 1 + g.crossLinear 1 * f 0 + g.crossMass * f 0 * f 1,
    g.direct 4 + g.crossLinear 0 * f 2 + g.crossLinear 2 * f 0 + g.crossMass * f 0 * f 2,
    g.direct 5 + g.crossLinear 1 * f 2 + g.crossLinear 2 * f 1 + g.crossMass * f 1 * f 2]

/-- The eight offset corners of one shape corner: the primal metric and the
reciprocal part are evaluated once. -/
def shapeMax (b : Cell) (g : Moments) (σ : Fin 5 → Bool) : ℚ :=
  let p := shapePart b σ
  let P := primalMetric p
  let d := dot6 (dualMetric p) g.reciprocal
  listMax (dot6 P (shift6 g (offsetPart b fun _ => false)) + d)
    (offsetList.map fun f => dot6 P (shift6 g (offsetPart b f)) + d)

/-- The largest `packedCorner` over the 256 closed corners. -/
def cornerMax (b : Cell) (g : Moments) : ℚ :=
  listMax (shapeMax b g fun _ => false) (shapeList.map (shapeMax b g))

def baselineF (b : Cell) (ys : List LineF) : ℚ :=
  (sumL LineF.intercept ys : ℚ) / S - cornerMax b (momentsQ ys)

/-! ### An exact integer corner fold

The corner value `S · packedCorner` is a rational function of the corner with
the inverses `(r₁²r₂²)⁻¹`, `r₁⁻²`, `r₂⁻²`. On the grid `2^-20` (every
Stage2 box is exact there), with the grid integers `R = 2^20 r`, and after
multiplication by `2^160 R₁²R₂² > 0` it is the integer `K²·P·X + D·R` of
`cornerTest`, which compares it with the scaled cap, so the fold needs no
rational arithmetic (`fold_cast`). -/

/-- The grid `2^20`. -/
def gridK : ℤ := 1048576

/-- `2^20 c`, the numerator of `c·2^20`. -/
def gz (c : ℚ) : ℤ := (c * gridK).num

/-- All sixteen endpoints lie on the grid. -/
def gridOK (b : Cell) : Bool :=
  (List.finRange 8).all fun i => (b.lo i * gridK).den == 1 && (b.hi i * gridK).den == 1

def dotZ (v w : Fin 6 → ℤ) : ℤ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 + v 4 * w 4 + v 5 * w 5

/-- The grid coordinate `i < 5` of shape corner `σ`. -/
def shapeZ (b : Cell) (σ : Fin 5 → Bool) (i : Fin 5) : ℤ :=
  if σ i then gz (b.hi ⟨i.val, by omega⟩) else gz (b.lo ⟨i.val, by omega⟩)

/-- The grid offset `i` of offset corner `f`. -/
def offsetZ (b : Cell) (f : Fin 3 → Bool) (i : Fin 3) : ℤ :=
  if f i then gz (b.hi (offset i)) else gz (b.lo (offset i))

/-- `2^40 S · shift` at an offset corner, from the integer moments. -/
def shiftZ (D : Fin 6 → ℤ) (L : Fin 3 → ℤ) (M : ℤ) (F : Fin 3 → ℤ) : Fin 6 → ℤ :=
  let K := gridK
  ![D 0 * K * K + (L 0 * F 0 + L 0 * F 0) * K + M * F 0 * F 0,
    D 1 * K * K + (L 1 * F 1 + L 1 * F 1) * K + M * F 1 * F 1,
    D 2 * K * K + (L 2 * F 2 + L 2 * F 2) * K + M * F 2 * F 2,
    D 3 * K * K + (L 0 * F 1 + L 1 * F 0) * K + M * F 0 * F 1,
    D 4 * K * K + (L 0 * F 2 + L 2 * F 0) * K + M * F 0 * F 2,
    D 5 * K * K + (L 1 * F 2 + L 2 * F 1) * K + M * F 1 * F 2]

/-- `2^160 r₁²r₂²` times the primal metric. -/
def primalZ (R1 R2 X Y Z : ℤ) : Fin 6 → ℤ :=
  let K := gridK
  let s := R1 * R1
  let t := R2 * R2
  let u := s * t
  let K2 := K * K
  let K4 := K2 * K2
  let K8 := K4 * K4
  ![s * u * K2, (s * X * X + t * K2) * u, (s * Y * Y + t * Z * Z) * u + K8, 2 * s * X * u * K,
    2 * s * Y * u * K, 2 * (s * X * Y + t * Z * K) * u]

/-- `2^240 r₁²r₂²` times the dual metric. -/
def dualZ (R1 R2 X Y Z : ℤ) : Fin 6 → ℤ :=
  let K := gridK
  let s := R1 * R1
  let t := R2 * R2
  let u := s * t
  let u2 := u * u
  let K2 := K * K
  let K4 := K2 * K2
  let K8 := K4 * K4
  let H := X * Z - Y * K
  ![t * (K8 * K2) + X * X * s * K8 + H * H * u2, s * (K8 * K2) + Z * Z * u2 * K2, u2 * K4,
    -2 * (X * s * (K8 * K) + H * Z * u2 * K), 2 * H * u2 * K2, -2 * Z * u2 * (K2 * K)]

/-- One shape corner against the cap `C` (units `1/S`) at every offset corner. -/
def cornerTest (b : Cell) (R : Fin 6 → ℤ) (C : ℤ) (shifts : List (Fin 6 → ℤ)) (σ : Fin 5 → Bool) : Bool :=
  let R1 := shapeZ b σ 0
  let R2 := shapeZ b σ 1
  let P := primalZ R1 R2 (shapeZ b σ 2) (shapeZ b σ 3) (shapeZ b σ 4)
  let d := dotZ (dualZ R1 R2 (shapeZ b σ 2) (shapeZ b σ 3) (shapeZ b σ 4)) R
  let K2 := gridK * gridK
  let K8 := K2 * K2 * (K2 * K2)
  let cap := K8 * (R1 * R1 * (R2 * R2)) * C
  shifts.all fun X => K2 * dotZ P X + d ≤ cap

/-- Every corner value `S · packedCorner` is at most `C`. -/
def foldZ (b : Cell) (ys : List LineF) (C : ℤ) : Bool :=
  (decide (0 < b.lo 0 ∧ 0 < b.lo 1 ∧ 0 < b.hi 0 ∧ 0 < b.hi 1) && gridOK b) &&
    shapeList.all (cornerTest b (recipZ ys) C
      (offsetList.map fun f => shiftZ (directZ ys) (linearZ ys) (massZ ys) (offsetZ b f)))

/-- An integer key of a mode. Distinct keys give distinct modes
(`List.Nodup.of_map`), so the check needs no injectivity. -/
def modeKeyM (m : Mode) : ℤ :=
  (match m.family with | .cross => 0 | .period => 1 | .reciprocal => 2) * 1000 +
    m.index 0 * 100 + m.index 1 * 10 + m.index 2

def modeKey (r : AnchorRow) : ℤ := modeKeyM r.mode

/-- The plain tangent route. -/
def bulkFix (b : Cell) (r : Proposal) : Bool :=
  (sameCell b r.ownerBox && decide ((r.selected.map modeKey).Nodup)) &&
  (diagonalsCheck b &&
    match prepareF b r.selected with
    | none => false
    | some ys => foldZ b ys (sumL LineF.intercept ys - thrZ - 1))

/-! ### The phase budget -/

/-- The largest reciprocal squared length over the 32 shape corners. -/
def waveUpperL (b : Cell) (n : IntVec) : ℚ :=
  listMax (dualCorner (shapePart b fun _ => false) n) (shapeList.map fun σ => dualCorner (shapePart b σ) n)

/-- `2 G(1, π u)` from below at the corner maximum `u`, in units of `1/S`. -/
def capacityF (b : Cell) (m : Mode) : ℤ :=
  let u := waveUpperL b m.index
  max 0 (2 * oneLowF (piTimes (cdivZ (u.num * Sz) (u.den : ℤ))))

def capCheckF (b : Cell) (budget : Array Allocation) (m : Mode) : Bool :=
  if spent budget m = 0 then true else decide (spent budget m ≤ (capacityF b m : ℚ) / S)

def budgetCheckF (b : Cell) (xs : List Line) (budget : Array Allocation) : Bool :=
  decide (∀ i : Fin budget.size, budget[i].valid (retained xs)) &&
    decide (∀ m ∈ retained xs, capCheckF b budget m = true)

def shrinkBudgetF (b : Cell) (xs : List Line) (budget : Array Allocation) : Array Allocation :=
  let scale := (xs.map Line.mode).dedup.foldl (fun current m =>
    let charge := spent budget m
    if 0 < charge then min current (max 0 ((capacityF b m : ℚ) / S / charge)) else current) (1 : ℚ)
  budget.map fun r => {r with amount := scale * r.amount}

def checkedBudgetF (b : Cell) (xs : List Line) (budget : Array Allocation) : Option ℚ :=
  if budgetCheckF b xs budget then some (budgetGain xs budget)
  else
    let candidate := shrinkBudgetF b xs budget
    if budgetCheckF b xs candidate then some (budgetGain xs candidate) else none

/-- The phase-budget route. -/
def phaseFix (b : Cell) (r : Proposal) (budget : Array Allocation) : Bool :=
  (sameCell b r.ownerBox && decide ((r.selected.map modeKey).Nodup)) &&
  (diagonalsCheck b &&
    match prepareF b r.selected with
    | none => false
    | some ys =>
      match checkedBudgetF b (ys.map LineF.toLine) budget with
      | none => false
      | some gain => foldZ b ys (sumL LineF.intercept ys - thrZ - 1 + ⌊gain * S⌋))

end BccSharp.Coulomb.CompactCover.Stage2Fix
