import BccSharp.Cover.OverlayFixConst

set_option autoImplicit false

/-! A fixed-point evaluator for the Overlay planar layer correction.

`BccSharp.Cover.OverlaySharpLayer` pays a leaf in about 13 s of kernel time,
almost all of it in rational arithmetic (about 65 µs per `ℚ` operation in the
kernel, against 3–7 µs per `ℕ` operation). This evaluator computes its own
lower bound of the same quantity (the triangular relaxation of the planar
numerator) with integer endpoints at the scale `S = 2^96`:

* an interval `FI` is a pair of integers `[lo/S, hi/S]`, rounded outward;
* `e^(-x)` at a point is the reciprocal of `e^(x/64)^64`, with `e^(x/64)` a
  28-term Taylor sum evaluated exactly by Horner's rule in `ℕ` with literal
  coefficients;
* `cos(2πv)` at a point reduces `v` modulo `1` exactly, then evaluates the
  Taylor polynomial of order 36 (`TrigBounds.cosPolynomial q 36`: 18 even
  terms, degree up to 34) at a rational point near `2πv` by Horner's rule in
  `Q^4`, with the `π` and series errors added;
* ranges use monotonicity: `e^(-x)` is decreasing, and `cos(2πv)` is monotone
  between consecutive half-integers, a fact checked with exact integers;
* the three retained axial terms are enclosed twice, in their original form
  `e^(-t)cos(2πw)`, `e^(-th)cos(2π(u+hw))`, `e^(-t(1-h))cos(2π(u-(1-h)w))`
  (each exponential range exact in `t` and `h` jointly; `core₁`) and in the
  product form of `axialCore` with `cosh(tδ)` and `sinh(tδ)` (which keeps the
  cancellation when `h` is near `1/2`; `core₂`), and the two enclosures are
  intersected (`coreF`).

Soundness is proved in `BccSharp.Cover.OverlayFixSound`. -/

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp BccSharp.Coverage DirectRoute

/-! ### Integer rounding and Horner's rule -/

/-- Ceiling division of naturals, for `d > 0`. -/
def cdivN (n d : ℕ) : ℕ := (n + d - 1) / d

/-- Ceiling division of integers by a positive integer. -/
def cdivZ (n d : ℤ) : ℤ := -((-n) / d)

/-- Horner's rule: `hornerN x [c₀, …, cₖ] = c₀ xᵏ + ⋯ + cₖ`. Written with
`List.rec` so that the kernel does not go through `brecOn`. -/
def hornerN (x : ℕ) (cs : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc) (fun c _ ih acc => ih (acc * x + c)) cs 0

/-! ### Intervals -/

/-- The interval `[lo/S, hi/S]`. -/
structure FI where
  lo : ℤ
  hi : ℤ

namespace FI

def add (a b : FI) : FI := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : FI) : FI := ⟨a.lo - b.hi, a.hi - b.lo⟩
def ofInt (n : ℤ) : FI := ⟨n * Sz, n * Sz⟩
def smul (n : ℤ) (a : FI) : FI := if 0 ≤ n then ⟨n * a.lo, n * a.hi⟩ else ⟨n * a.hi, n * a.lo⟩
/-- Widen both ends by `e ≥ 0`. -/
def widen (a : FI) (e : ℤ) : FI := ⟨a.lo - e, a.hi + e⟩

def mul (a b : FI) : FI :=
  let p := a.lo * b.lo
  let q := a.lo * b.hi
  let r := a.hi * b.lo
  let s := a.hi * b.hi
  ⟨min (min p q) (min r s) / Sz, cdivZ (max (max p q) (max r s)) Sz⟩

/-- Product of two intervals with nonnegative lower ends; the general product otherwise. -/
def mulPos (a b : FI) : FI :=
  if 0 ≤ a.lo ∧ 0 ≤ b.lo then ⟨a.lo * b.lo / Sz, cdivZ (a.hi * b.hi) Sz⟩ else mul a b

def sq (a : FI) : FI :=
  if 0 ≤ a.lo then ⟨a.lo * a.lo / Sz, cdivZ (a.hi * a.hi) Sz⟩
  else if a.hi ≤ 0 then ⟨a.hi * a.hi / Sz, cdivZ (a.lo * a.lo) Sz⟩
  else ⟨0, cdivZ (max (a.lo * a.lo) (a.hi * a.hi)) Sz⟩

/-- `1/x` on an interval with positive lower end (`0 < a.lo` is checked by the caller). -/
def invPos (a : FI) : FI := ⟨(S2 : ℤ) / a.hi, cdivZ (S2 : ℤ) a.lo⟩

end FI

/-- Outward-rounded fixed-point endpoints of a rational interval `[l, u]`. -/
def ofRat (l u : ℚ) : FI := ⟨l.num * Sz / l.den, cdivZ (u.num * Sz) u.den⟩

/-- Coordinate `i` of a cell. -/
def cx (b : Cell) (i : Axis) : FI := ofRat (b.lo i) (b.hi i)

/-! ### Square roots -/

def newton (n fuel g : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun g => g) (fun _ ih g => ih ((g + n / g) / 2)) fuel g

def sqrtGuess (n : ℕ) : ℕ := newton n 10 (2 ^ (n.log2 / 2 + 1))

/-- A natural `≤ √n`. -/
def sqrtLo (n : ℕ) : ℕ :=
  let g := sqrtGuess n
  if g * g ≤ n then g else if (g - 1) * (g - 1) ≤ n then g - 1 else 0

/-- A natural `≥ √n`. -/
def sqrtHi (n : ℕ) : ℕ :=
  let g := sqrtGuess n
  if n ≤ g * g then g else if n ≤ (g + 1) * (g + 1) then g + 1 else n + 1

def FI.sqrt (a : FI) : FI := ⟨(sqrtLo (a.lo.toNat * S) : ℤ), (sqrtHi (a.hi.toNat * S) : ℤ)⟩

/-! ### Exponential -/

/-- Rounded squaring of a nonnegative interval of naturals, `n` times. -/
def sqRounds (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ → ℕ × ℕ) (fun p => p)
    (fun _ ih p => ih (p.1 * p.1 / S, cdivN (p.2 * p.2) S)) n p

/-- `e^(x/S)` for `x ≤ 64 S`: `e^(x/(64 S))` by 28 Taylor terms, then six squarings. -/
def expPosPt (x : ℕ) : ℕ × ℕ :=
  let acc := hornerN x expC
  sqRounds 6 (acc / expDS - 1, cdivN acc expDS + 1)

/-- `e^(-x/S)` for `x ≥ 0`, as the reciprocal of `expPosPt`; `[0, 1]` when out of range. -/
def expNegPt (x : ℕ) : FI :=
  if x ≤ S64 then
    let e := expPosPt x
    if 0 < e.1 then ⟨((S2 / e.2 : ℕ) : ℤ), ((cdivN S2 e.1 : ℕ) : ℤ)⟩ else ⟨0, Sz⟩
  else ⟨0, Sz⟩

/-- `e^(-x)` for `x ∈ [A/S, B/S]`, `x ≥ 0`. -/
def expRange (A B : ℤ) : FI := ⟨(expNegPt B.toNat).lo, (expNegPt A.toNat).hi⟩

/-! ### Cosine -/

/-- `cos(2π r/S)` at a point: exact reduction modulo `1`, then the Taylor
polynomial of order 36 at `Q/S ≈ 2π r'/S`, `|Q| ≤ 16 S/5`; `[-1, 1]` otherwise. -/
def cosPt (r : ℤ) : FI :=
  let n := (r + halfS) / Sz
  let r' := r - n * Sz
  let Q := twoPiLo * r' / Sz
  let Y := Q.natAbs * Q.natAbs
  let Z := Y * Y
  let acc : ℤ := (hornerN Z cosPosC : ℤ) - ((Y * hornerN Z cosNegC : ℕ) : ℤ)
  if Q.natAbs ≤ qMax then ⟨acc / cosDS - cosErr, cdivZ acc cosDS + cosErr⟩ else ⟨-Sz, Sz⟩

/-- `cos(2πv)` for `v ∈ [A/S, B/S]`. The minimum is an endpoint value when
`[A, B]` lies between two consecutive odd multiples of `S/2`, the maximum
when it lies between two consecutive multiples of `S`. -/
def cosRange (A B : ℤ) : FI :=
  let k := (A + halfS) / Sz
  let k' := A / Sz
  ⟨if k * Sz - halfS ≤ A ∧ B ≤ k * Sz + halfS then min (cosPt A).lo (cosPt B).lo else -Sz,
   if B ≤ k' * Sz + Sz then max (cosPt A).hi (cosPt B).hi else Sz⟩

/-! ### One retained wave on the seam-shifted cell -/

def twoPiF : FI := ⟨twoPiLo, twoPiHi⟩

/-- `c = 1/(r₁ r₂)`. -/
def cF (b : Cell) : FI := (FI.mulPos (cx b 0) (cx b 1)).invPos

def kappaSqF (b : Cell) (m : Wave) : FI :=
  let a₁ := FI.smul m.1 (cx b 0).invPos
  let a₂ := FI.mul ((FI.ofInt m.2).sub (FI.smul m.1 (cx b 2))) (cx b 1).invPos
  a₁.sq.add a₂.sq

def kappaF (b : Cell) (m : Wave) : FI := (kappaSqF b m).sqrt

/-- `t = 2π c κ`. -/
def tF (b : Cell) (m : Wave) : FI := FI.mulPos (FI.mulPos twoPiF (cF b)) (kappaF b m)

def wF (b : Cell) (m : Wave) : FI :=
  (FI.smul m.1 ((cx b 3).sub (FI.mul (cx b 2) (cx b 4)))).add (FI.smul m.2 (cx b 4))

def uF (b : Cell) (m : Wave) : FI := (FI.smul m.1 (cx b 5)).add (FI.smul m.2 (cx b 6))

/-- `1 - h`. -/
def gF (b : Cell) : FI := ⟨Sz - (cx b 7).hi, Sz - (cx b 7).lo⟩

/-- The three retained axial terms in their original form,
`2 e^(-t) cos(2πw) + e^(-th) cos(2π(u+hw)) + e^(-t(1-h)) cos(2π(u-(1-h)w))`.
Each exponential range is exact in `t` and `h` jointly; this form is the
tighter one when `h` is far from `1/2`. -/
def core₁ (b : Cell) (m : Wave) : FI :=
  let t := tF b m
  let w := wF b m
  let u := uF b m
  let h := cx b 7
  let g := gF b
  let th := FI.mulPos t h
  let tg := FI.mulPos t g
  let v₂ := u.add (FI.mul h w)
  let v₃ := u.sub (FI.mul g w)
  (FI.smul 2 (FI.mul (expRange t.lo t.hi) (cosRange w.lo w.hi))).add
    ((FI.mul (expRange th.lo th.hi) (cosRange v₂.lo v₂.hi)).add
      (FI.mul (expRange tg.lo tg.hi) (cosRange v₃.lo v₃.hi)))

/-- `(cosh, sinh)` at `n/S` from the same exponential, for `n ≤ 64 S`. -/
def hypPt (n : ℕ) : FI × FI :=
  let ep := expPosPt n
  let en := expNegPt n
  (⟨((ep.1 : ℤ) + en.lo) / 2, cdivZ ((ep.2 : ℤ) + en.hi) 2⟩,
   ⟨((ep.1 : ℤ) - en.hi) / 2, cdivZ ((ep.2 : ℤ) - en.lo) 2⟩)

/-- `cosh z` for `z ∈ [A/S, B/S]`: even, increasing in `|z|`. -/
def coshRange (A B : ℤ) : FI :=
  ⟨if A ≤ 0 ∧ 0 ≤ B then Sz else (hypPt (min A.natAbs B.natAbs)).1.lo,
   (hypPt (max A.natAbs B.natAbs)).1.hi⟩

/-- `sinh z` for `z ∈ [A/S, B/S]`: odd and increasing. -/
def sinhRange (A B : ℤ) : FI :=
  ⟨if 0 ≤ A then (hypPt A.natAbs).2.lo else -(hypPt A.natAbs).2.hi,
   if 0 ≤ B then (hypPt B.natAbs).2.hi else -(hypPt B.natAbs).2.lo⟩

/-- `δ = h - 1/2`. -/
def deltaF (b : Cell) : FI := ⟨(cx b 7).lo - halfS, (cx b 7).hi - halfS⟩

/-- The same terms in the product form of `axialCore`,
`2 e^(-t) cos 2γ + 2 e^(-t/2) (cosh(tδ) cos γ cos φ + sinh(tδ) sin γ sin φ)` with
`γ = πw`, `φ = 2π(u + wδ)`; the tighter form when `h` is near `1/2`. -/
def core₂ (b : Cell) (m : Wave) : FI :=
  let t := tF b m
  let w := wF b m
  let u := uF b m
  let δ := deltaF b
  let z := FI.mul t δ
  let g : FI := ⟨w.lo / 2, cdivZ w.hi 2⟩
  let φ := u.add (FI.mul w δ)
  let q := Sz / 4
  let plus := FI.mul (FI.mul (coshRange z.lo z.hi) (cosRange g.lo g.hi)) (cosRange φ.lo φ.hi)
  let minus := FI.mul (FI.mul (sinhRange z.lo z.hi) (cosRange (g.lo - q) (g.hi - q)))
    (cosRange (φ.lo - q) (φ.hi - q))
  (FI.smul 2 (FI.mul (expRange t.lo t.hi) (cosRange w.lo w.hi))).add
    (FI.smul 2 (FI.mul (expRange (t.lo / 2) (cdivZ t.hi 2)) (plus.add minus)))

/-- Both forms enclose `axialCore`; keep their intersection. -/
def coreF (b : Cell) (m : Wave) : FI :=
  let a := core₁ b m
  let c := core₂ b m
  ⟨max a.lo c.lo, min a.hi c.hi⟩

/-- `η S` for the spacing `η = min(h, 1-h)` of the rounded height interval. -/
def etaN (b : Cell) : ℕ := (min (cx b 7).lo (Sz - (cx b 7).hi)).toNat

/-- Upper bound, in units of `1/S`, of `axialTail t₀ η` with `t₀ = t.lo/S`:
`(2A² + 2AB)/(1 - A)` with `A ≥ e^(-t₀)`, `B ≥ e^(-η t₀)`. -/
def tailF (b : Cell) (m : Wave) : ℤ :=
  let t₀ := (tF b m).lo.toNat
  let A := (expNegPt t₀).hi
  let B := (expNegPt (t₀ * etaN b / S)).hi
  cdivZ (2 * A * A + 2 * A * B) (Sz - A)

def waveF (b : Cell) (m : Wave) : FI :=
  FI.mul ((coreF b m).widen (tailF b m)) (kappaF b m).invPos

def waveOK (b : Cell) (m : Wave) : Bool :=
  let z := FI.mul (tF b m) (deltaF b)
  (decide (0 < (kappaF b m).lo) && (decide (0 < (tF b m).lo) && decide ((expNegPt (tF b m).lo.toNat).hi < Sz))) &&
    (decide (z.lo.natAbs ≤ S64) && decide (z.hi.natAbs ≤ S64))

/-! ### Retained sum, radial tail and layer -/

def sumF : List FI → FI
  | [] => ⟨0, 0⟩
  | a :: l => a.add (sumF l)

def retainedF (b : Cell) : FI := FI.mul (FI.smul 2 (cF b)) (sumF ((wavesList 2).map (waveF b)))

/-- An upper bound `B` of `r₁` and of the second column length `√((r₁x)² + r₂²)`. -/
def columnF (b : Cell) : ℤ :=
  max (cx b 0).hi ((FI.sq (FI.mul (cx b 0) (cx b 2))).add (FI.sq (cx b 1))).sqrt.hi

/-- `τ S` with `τ ≤ 2π c / B`. -/
def tauN (b : Cell) : ℕ := (twoPiLo * (cF b).lo / columnF b).toNat

/-- Upper bound, in units of `1/S`, of `radialTail c B τ η 3`. -/
def radialF (b : Cell) : ℤ :=
  let τ := tauN b
  let a₁ := (expNegPt τ).hi
  let a₂ := (expNegPt (τ * etaN b / S)).hi
  let e₃ := cdivZ (a₁ * a₁ * a₁) (S2 : ℤ)
  let f₃ := cdivZ (a₂ * a₂ * a₂) (S2 : ℤ)
  let g₁ := cdivZ (2 * e₃ * Sz) (Sz - a₁)
  let g₂ := cdivZ (2 * f₃ * Sz) (Sz - a₂)
  let pre := cdivZ (8 * (cF b).hi * columnF b) (Sz - e₃)
  cdivZ (pre * (g₁ + g₂)) Sz

def radialOK (b : Cell) : Bool :=
  let τ := tauN b
  let a₁ := (expNegPt τ).hi
  let a₂ := (expNegPt (τ * etaN b / S)).hi
  decide (0 < τ) && (decide (0 < columnF b) && (decide (a₁ < Sz) && (decide (a₂ < Sz) &&
    decide (cdivZ (a₁ * a₁ * a₁) (S2 : ℤ) < Sz))))

def layerF (raw : Cell) : FI :=
  let b := seamCell raw
  (retainedF b).widen (radialF b)

/-! ### Area term and the pass -/

/-- A proposal for `∛n` by Newton's method. It is not checked: the area tangent
is sound at every nonnegative anchor, and `areaAnchor` clamps it to the range of `√c`. -/
def cbrtGuess (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun g => g)
    (fun _ ih g => ih (if g = 0 then 0 else (2 * g + n / (g * g)) / 3)) 12 (2 ^ (n.log2 / 3 + 1))

/-- `d S` with `d ≤ 2π(1/12 + hd²)`, `hd` the distance of the height interval to `1/2`. -/
def areaD (b : Cell) : ℕ :=
  let h := cx b 7
  let hd := (max 0 (max (h.lo - halfS) (halfS - h.hi))).toNat
  (twoPiLo.toNat * (S / 12 + hd * hd / S)) / S

/-- The tangent anchor `a S`: the stationary point of `C s + d s⁴`, clamped to the
range of `√c`. Any nonnegative anchor is sound. -/
def areaAnchor (b : Cell) : ℕ :=
  let s := (cF b).sqrt
  let d := areaD b
  let x := if d = 0 then 0 else ((-triangleZ).toNat * S * S) / (4 * d)
  let r : ℤ := cbrtGuess (x * S)
  (min s.hi (max s.lo r)).toNat

/-- Lower bound, in units of `1/S`, of `C √c + d (√c)⁴` with `C = triangleZ/S`. -/
def areaF (b : Cell) : ℤ :=
  let s := (cF b).sqrt
  let d : ℤ := areaD b
  let a : ℤ := areaAnchor b
  let slope : FI := ⟨triangleZ + 4 * d * a * a * a / (Sz * Sz * Sz),
    triangleZ + cdivZ (4 * d * a * a * a) (Sz * Sz * Sz)⟩
  triangleZ * a / Sz + d * a * a * a * a / (Sz * Sz * Sz * Sz) + (FI.mul slope ⟨s.lo - a, s.hi - a⟩).lo

def fixCheck (raw : Cell) : Bool :=
  let b := seamCell raw
  (diagonalsCheck b && decide (0 < spacing b)) &&
    ((decide (0 < (cx b 0).lo) && (decide (0 < (cx b 1).lo) &&
      (decide (0 < (FI.mulPos (cx b 0) (cx b 1)).lo) && decide (0 < etaN b)))) &&
    ((wavesList 2).all (waveOK b) && radialOK b))

/-- The single per-leaf check. -/
def fixPass (raw : Cell) : Bool :=
  fixCheck raw && decide (thresholdZ < areaF (seamCell raw) + (layerF raw).lo)

end BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
