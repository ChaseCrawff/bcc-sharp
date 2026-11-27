import BccSharp.Cover.PlanarFibreGWeights
import BccSharp.Cover.OverlayFixSound

set_option autoImplicit false

/-! # PlanarFibre triangular fibers: second-order fixed-point jets

The PlanarFibre triangular requests (route `strictFCC`) are boxes near the
two-layer triangular (HCP-like) stacking, where `fixPass` fails on whole
boxes: its interval bound of the planar energy is first order in the box
width, and the true margin is only about `2·10⁻⁴` (in `2 a_c`-scaled energy)
at minima inside the boxes. This module defines the computable parts of a
second-order evaluator.

* `MR` is a midpoint-radius interval `[(m - r)/S, (m + r)/S]` with an integer
  midpoint and a natural radius, `S = 2^96`. Its product costs one integer
  and three natural multiplications, about an eighth of the kernel time of
  the endpoint product `FI.mul`.
* `J2` is a second-order jet with `MR` entries: enclosures, over a box, of a
  value, of the 8 first partial derivatives and of the second partial
  derivatives of a function of the chart. `J2.ok` collects the side
  conditions (positivity, ranges) of the operations used. The kernel
  evaluates lazily, so a jet whose Hessian is never read costs only its
  value and gradient.
* The operations are sums, products and composition with `x ↦ x²`, `1/x`,
  `√x`, `e^(-x)`, `cos 2πx`, `sin 2πx`, `cosh`, `sinh` and the planar kernel
  `g(t) = gKernel (1/2) t`; each composition takes enclosures of `φ`, `φ'`
  and `φ''` on the argument's value interval, computed with the endpoint
  functions of `BccSharp.Cover.OverlayFix`.
* `gPt T` encloses `g(T/S)` from the alternating erfc series of
  `BccSharp.Erfc` (64 terms, exact integer weights `gWList`).
* `phi2J`, `phi1J`, `phi0J` are the jets of the three parts of the smooth
  lower bound `Φ` of the planar energy (second, first and zeroth order).
* `taylorLower` combines them into a lower bound of `Φ` on a box, around a
  proposed point `p0`; `boxOk` adds the tails and compares with the FCC level.

Soundness is proved in `BccSharp.Cover.PlanarFibreJetSound` and `BccSharp.Cover.PlanarFibreTri`. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri
open BccSharp BccSharp.Coverage DirectRoute
open OverlayPlanar OverlayPlanar.Fix

/-! ### Endpoint helpers -/

def fiNeg (a : FI) : FI := ⟨-a.hi, -a.lo⟩
def fiHalf (a : FI) : FI := ⟨a.lo / 2, cdivZ a.hi 2⟩
/-- `π`. -/
def piF : FI := fiHalf twoPiF
/-- `√π`. -/
def sqrtPiF : FI := FI.sqrt piF

/-! ### Midpoint-radius intervals -/

/-- The interval `[(m - r)/S, (m + r)/S]`. -/
structure MR where
  m : ℤ
  r : ℕ

namespace MR

def zero : MR := ⟨0, 0⟩
def ofInt (n : ℤ) : MR := ⟨n * Sz, 0⟩
def add (a b : MR) : MR := ⟨a.m + b.m, a.r + b.r⟩
def sub (a b : MR) : MR := ⟨a.m - b.m, a.r + b.r⟩
def neg (a : MR) : MR := ⟨-a.m, a.r⟩
def smul (n : ℤ) (a : MR) : MR := ⟨n * a.m, n.natAbs * a.r⟩
def mul (a b : MR) : MR :=
  ⟨a.m * b.m / Sz, (a.m.natAbs * b.r + a.r * b.m.natAbs + a.r * b.r) / S + 2⟩
def half (a : MR) : MR := ⟨a.m / 2, a.r / 2 + 1⟩
def lo (a : MR) : ℤ := a.m - a.r
def hi (a : MR) : ℤ := a.m + a.r
/-- The endpoint interval. -/
def toFI (a : MR) : FI := ⟨a.lo, a.hi⟩
/-- From an endpoint interval. -/
def ofFI (a : FI) : MR := ⟨(a.lo + a.hi) / 2, ((a.hi - a.lo) / 2).toNat + 1⟩

end MR

/-! ### The planar kernel `g(t) = gKernel (1/2) t`

`g(q) = √π/√q - 2 Σ_{k<n} (-q)^k/(k!(2k+1)) + E`, `|E| ≤ 4 q^n/n!`, for
`q/(n+1) ≤ 1/2` (`Erfc.sqrt_remainder`). With `q = T/S` the series is
`gHorner T gWList / gD` exactly. -/

/-- `Σ_k (-T)^k w_k` by Horner's rule. -/
def gHorner (T : ℕ) (w : List ℕ) : ℤ := w.foldr (fun c acc => (c : ℤ) - (T : ℤ) * acc) 0

/-- `⌈4 q^gN / gN! · S⌉` for `q = T/S`. -/
def gErr (T : ℕ) : ℤ := cdivZ (4 * (T : ℤ) ^ gN) ((S : ℤ) ^ (gN - 1) * (Nat.factorial gN : ℤ))

/-- `g(T/S)` at a point `T > 0` with `2T ≤ (gN+1) S`. -/
def gPt (T : ℕ) : FI :=
  let A := sqrtPiF.mul (FI.sqrt ⟨T, T⟩).invPos
  let n := gHorner T gWList * Sz
  let B : FI := ⟨n / (gD : ℤ), cdivZ n gD⟩
  let e := gErr T
  ⟨A.lo - 2 * B.hi - e, A.hi - 2 * B.lo + e⟩

/-- Side condition of `gPt`. -/
def gPtOK (T : ℕ) : Bool :=
  decide (0 < (FI.sqrt (⟨T, T⟩ : FI)).lo) && decide (2 * T ≤ (gN + 1) * S)

/-- `g` on `[A/S, B/S]`, `0 < A`: `g` is decreasing. -/
def gRange (A B : ℤ) : FI := ⟨(gPt B.toNat).lo, (gPt A.toNat).hi⟩

def gRangeOK (A B : ℤ) : Bool := decide (0 < A) && (gPtOK A.toNat && gPtOK B.toNat)

/-! ### Second-order jets -/

/-- Enclosures, over a box, of a value, the first partials `g k` and the
second partials `h j k` (`∂_j ∂_k`), with the side conditions in `ok`.
`s` is a support mask: the function does not depend on coordinate `k` when
`s k = false`, and the entries for such coordinates are not computed. -/
structure J2 where
  ok : Bool
  s : Fin 8 → Bool
  v : MR
  g : Fin 8 → MR
  h : Fin 8 → Fin 8 → MR

namespace J2

/-- `if c then x else 0`. -/
def gate (c : Bool) (x : MR) : MR := if c then x else MR.zero

def const (a : MR) : J2 := ⟨true, fun _ => false, a, fun _ => MR.zero, fun _ _ => MR.zero⟩

def var (b : Cell) (i : Fin 8) : J2 :=
  ⟨true, fun k => decide (k = i), MR.ofFI (cx b i), fun k => if k = i then MR.ofInt 1 else MR.zero,
    fun _ _ => MR.zero⟩

def add (a c : J2) : J2 :=
  ⟨a.ok && c.ok, fun k => a.s k || c.s k, a.v.add c.v,
    fun k => (gate (a.s k) (a.g k)).add (gate (c.s k) (c.g k)),
    fun j k => (gate (a.s j && a.s k) (a.h j k)).add (gate (c.s j && c.s k) (c.h j k))⟩

def sub (a c : J2) : J2 :=
  ⟨a.ok && c.ok, fun k => a.s k || c.s k, a.v.sub c.v,
    fun k => (gate (a.s k) (a.g k)).sub (gate (c.s k) (c.g k)),
    fun j k => (gate (a.s j && a.s k) (a.h j k)).sub (gate (c.s j && c.s k) (c.h j k))⟩

def smul (n : ℤ) (a : J2) : J2 :=
  ⟨a.ok, a.s, MR.smul n a.v, fun k => gate (a.s k) (MR.smul n (a.g k)),
    fun j k => gate (a.s j && a.s k) (MR.smul n (a.h j k))⟩

/-- Multiplication by a constant interval. -/
def scale (t : MR) (a : J2) : J2 :=
  ⟨a.ok, a.s, t.mul a.v, fun k => gate (a.s k) (t.mul (a.g k)),
    fun j k => gate (a.s j && a.s k) (t.mul (a.h j k))⟩

def half (a : J2) : J2 :=
  ⟨a.ok, a.s, a.v.half, fun k => gate (a.s k) (a.g k).half,
    fun j k => gate (a.s j && a.s k) (a.h j k).half⟩

def mul (a c : J2) : J2 :=
  ⟨a.ok && c.ok, fun k => a.s k || c.s k, a.v.mul c.v,
    fun k => (gate (a.s k) ((a.g k).mul c.v)).add (gate (c.s k) (a.v.mul (c.g k))),
    fun j k => gate ((a.s j || c.s j) && (a.s k || c.s k))
      (((gate (a.s j && a.s k) ((a.h j k).mul c.v)).add (gate (a.s j && c.s k) ((a.g j).mul (c.g k)))).add
        ((gate (a.s k && c.s j) ((a.g k).mul (c.g j))).add (gate (c.s j && c.s k) (a.v.mul (c.h j k)))))⟩

/-- `φ ∘ a`, given enclosures `f0`, `f1`, `f2` of `φ`, `φ'`, `φ''` on the value
interval of `a`; `guard` is the side condition that makes them sound. -/
def chain (a : J2) (guard : Bool) (f0 f1 f2 : MR) : J2 :=
  ⟨a.ok && guard, a.s, f0, fun k => gate (a.s k) (f1.mul (a.g k)),
    fun j k => gate (a.s j && a.s k) ((f2.mul ((a.g j).mul (a.g k))).add (f1.mul (a.h j k)))⟩

def sq (a : J2) : J2 :=
  a.chain true (MR.ofFI (FI.sq a.v.toFI)) (MR.smul 2 a.v) (MR.ofInt 2)

/-- `1/x` for `x > 0`. -/
def inv (a : J2) : J2 :=
  let r := a.v.toFI.invPos
  let r2 := FI.sq r
  a.chain (decide (0 < a.v.lo)) (MR.ofFI r) (MR.ofFI (fiNeg r2)) (MR.ofFI (FI.smul 2 (r2.mul r)))

/-- `√x` for `x > 0`. -/
def sqrt (a : J2) : J2 :=
  let r := FI.sqrt a.v.toFI
  let q := (FI.smul 2 r).invPos
  a.chain (decide (0 < a.v.lo) && decide (0 < r.lo)) (MR.ofFI r) (MR.ofFI q)
    (MR.ofFI (fiNeg (FI.smul 2 ((FI.sq q).mul q))))

/-- `e^(-x)` for `x ≥ 0`. -/
def expNeg (a : J2) : J2 :=
  let e := Fix.expRange a.v.lo a.v.hi
  a.chain (decide (0 ≤ a.v.lo)) (MR.ofFI e) (MR.ofFI (fiNeg e)) (MR.ofFI e)

/-- `cos 2πx`. -/
def cos2pi (a : J2) : J2 :=
  let c := Fix.cosRange a.v.lo a.v.hi
  let s := Fix.cosRange (a.v.lo - Sz / 4) (a.v.hi - Sz / 4)
  a.chain true (MR.ofFI c) (MR.ofFI (fiNeg (twoPiF.mul s))) (MR.ofFI (fiNeg (twoPiF.mul (twoPiF.mul c))))

/-- `sin 2πx = cos 2π(x - 1/4)`. -/
def sin2pi (a : J2) : J2 :=
  let c := Fix.cosRange a.v.lo a.v.hi
  let s := Fix.cosRange (a.v.lo - Sz / 4) (a.v.hi - Sz / 4)
  a.chain true (MR.ofFI s) (MR.ofFI (twoPiF.mul c)) (MR.ofFI (fiNeg (twoPiF.mul (twoPiF.mul s))))

def hypOK (a : MR) : Bool := decide (a.lo.natAbs ≤ S64) && decide (a.hi.natAbs ≤ S64)

def cosh (a : J2) : J2 :=
  let c := Fix.coshRange a.v.lo a.v.hi
  let s := Fix.sinhRange a.v.lo a.v.hi
  a.chain (hypOK a.v) (MR.ofFI c) (MR.ofFI s) (MR.ofFI c)

def sinh (a : J2) : J2 :=
  let c := Fix.coshRange a.v.lo a.v.hi
  let s := Fix.sinhRange a.v.lo a.v.hi
  a.chain (hypOK a.v) (MR.ofFI s) (MR.ofFI c) (MR.ofFI s)

/-- `g(x) = gKernel (1/2) x` for `x > 0`: `g' = -(e^(-x) + g/2)/x`,
`g'' = (e^(-x) - (3/2) g')/x`. -/
def ghalf (a : J2) : J2 :=
  let r := a.v.toFI.invPos
  let e := Fix.expRange a.v.lo a.v.hi
  let g0 := gRange a.v.lo a.v.hi
  let g1 := fiNeg ((e.add (fiHalf g0)).mul r)
  let g2 := (e.sub (fiHalf (FI.smul 3 g1))).mul r
  a.chain (gRangeOK a.v.lo a.v.hi) (MR.ofFI g0) (MR.ofFI g1) (MR.ofFI g2)

end J2

def jsum : List J2 → J2
  | [] => J2.const MR.zero
  | a :: l => a.add (jsum l)

/-! ### The smooth lower bound `Φ` of the planar energy -/

/-- Chart coordinates and the shared quantities `c = 1/(r₁r₂)`, `1/r₁`,
`1/r₂`, `δ = h - 1/2`. -/
structure Vars where
  r1 : J2
  r2 : J2
  x : J2
  y : J2
  z : J2
  u1 : J2
  u2 : J2
  d : J2
  c : J2
  ir1 : J2
  ir2 : J2

def vars (b : Cell) : Vars :=
  let r1 := J2.var b 0
  let r2 := J2.var b 1
  ⟨r1, r2, J2.var b 2, J2.var b 3, J2.var b 4, J2.var b 5, J2.var b 6,
    (J2.var b 7).sub (J2.const ⟨halfS, 0⟩), (r1.mul r2).inv, r1.inv, r2.inv⟩

/-- `κ² = (m₁/r₁)² + ((m₂ - m₁x)/r₂)²` (`κSq`). -/
def kSqJ (V : Vars) (m : Wave) : J2 :=
  ((V.ir1.smul m.1).sq).add ((((J2.const (MR.ofInt m.2)).sub (V.x.smul m.1)).mul V.ir2).sq)

/-- `N = (r₁(m₁ + x m₂))² + (r₂m₂)²` (`planarNorm`). -/
def normJ (V : Vars) (m : Wave) : J2 :=
  ((V.r1.mul ((J2.const (MR.ofInt m.1)).add (V.x.smul m.2))).sq).add ((V.r2.smul m.2).sq)

/-- `2c · axialCore t w u h / κ`, with `axialCore` in the product form
`2 e^(-t) cos 2πw + 2 e^(-t/2) (cosh(tδ) cos πw cos φ + sinh(tδ) sin πw sin φ)`,
`φ = 2π(u + wδ)`, arranged so that only two products depend on all eight
coordinates: `A cos 2πw + C (cos πw cos φ) + D (sin πw sin φ)` with
`A = (4c/κ) e^(-t)`, `C = (4c/κ) e^(-t/2) cosh(tδ)`, `D = (4c/κ) e^(-t/2) sinh(tδ)`. -/
def waveJ (V : Vars) (m : Wave) : J2 :=
  let k := (kSqJ V m).sqrt
  let t := (V.c.mul k).scale (MR.ofFI twoPiF)
  let pre := (V.c.mul k.inv).smul 4
  let w := ((V.y.sub (V.x.mul V.z)).smul m.1).add (V.z.smul m.2)
  let u := (V.u1.smul m.1).add (V.u2.smul m.2)
  let hw := w.half
  let ph := u.add (w.mul V.d)
  let td := t.mul V.d
  let B := pre.mul t.half.expNeg
  ((pre.mul t.expNeg).mul w.cos2pi).add
    (((B.mul td.cosh).mul (hw.cos2pi.mul ph.cos2pi)).add ((B.mul td.sinh).mul (hw.sin2pi.mul ph.sin2pi)))

/-- `2 g(πN)`. -/
def dTermJ (V : Vars) (m : Wave) : J2 := (((normJ V m).scale (MR.ofFI piF)).ghalf).smul 2

/-- `2c g(πκ²)`. -/
def kTermJ (V : Vars) (m : Wave) : J2 := (V.c.mul (((kSqJ V m).scale (MR.ofFI piF)).ghalf)).smul 2

/-- `zeroMode - 2c - 2 = 2π c² (δ² + 1/12) - 2c - 2`. -/
def baseJ (V : Vars) : J2 :=
  ((((V.c.sq).mul ((V.d.sq).add (J2.const (MR.ofFI ⟨Sz / 12, cdivZ Sz 12⟩)))).scale (MR.ofFI twoPiF)).sub
    (V.c.smul 2)).sub (J2.const (MR.ofInt 2))

/-- Second-order part: the base, the first two shells of direct planar
modes, the first dual shell and the first two shells of layer waves. -/
def d2Modes : List Wave := [(1, 0), (0, 1), (1, -1), (1, 1), (1, -2), (2, -1)]
def k2Modes : List Wave := [(1, 0), (0, 1), (1, 1)]
def w2Modes : List Wave := [(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1)]
/-- First-order part: the third direct shell and the third layer shell. -/
def d1Modes : List Wave := [(2, 0), (0, 2), (2, -2)]
def w1Modes : List Wave := [(2, 0), (0, 2), (2, 2)]
/-- Zeroth-order part: the other layer waves of `wavesList 2`. -/
def w0Modes : List Wave := [(1, -2), (2, -1), (2, -2)]

def phi2J (b : Cell) : J2 :=
  let V := vars b
  (((baseJ V).add (jsum (d2Modes.map (dTermJ V)))).add (jsum (k2Modes.map (kTermJ V)))).add
    (jsum (w2Modes.map (waveJ V)))

def phi1J (b : Cell) : J2 :=
  let V := vars b
  (jsum (d1Modes.map (dTermJ V))).add (jsum (w1Modes.map (waveJ V)))

def phi0J (b : Cell) : J2 :=
  let V := vars b
  jsum (w0Modes.map (waveJ V))

/-! ### The Taylor lower bound on a box -/

def toQ (z : ℤ) : ℚ := (z : ℚ) / (S : ℚ)

/-- `min_{d ∈ [a, b]} (g d + A d²/2)`, a lower bound (exact when `A ≤ 0` or
the vertex is in `[a, b]`). -/
def qmin (g A a b : ℚ) : ℚ :=
  if 0 < A ∧ a ≤ -g / A ∧ -g / A ≤ b then -(g * g) / (2 * A)
  else min (g * a + A * a * a / 2) (g * b + A * b * b / 2)

/-- Lower bound of `γ d + A d²/2` for `γ ∈ G`, `A ≥ H.lo`, `d ∈ [a, b]`. -/
def quadLower (G H : MR) (a b : ℚ) : ℚ :=
  min (qmin (toQ G.lo) (toQ H.lo) a b) (qmin (toQ G.hi) (toQ H.lo) a b)

/-- Lower bound of `η dⱼ dₖ` for `η ∈ H`, `dⱼ ∈ [aj, bj]`, `dₖ ∈ [ak, bk]`. -/
def crossLower (H : MR) (aj bj ak bk : ℚ) : ℚ :=
  let l := toQ H.lo
  let u := toQ H.hi
  min (min (min (l * (aj * ak)) (l * (aj * bk))) (min (l * (bj * ak)) (l * (bj * bk))))
    (min (min (u * (aj * ak)) (u * (aj * bk))) (min (u * (bj * ak)) (u * (bj * bk))))

/-- The point cell `[p, p]`. -/
def pointCell (p : Fin 8 → ℚ) : Cell := ⟨p, p⟩

/-- Diagonal term of coordinate `k`: `min (γₖ dₖ + Hₖₖ dₖ²/2)` over `dₖ ∈ [lo - p0, hi - p0]`,
`γₖ ∈ ∂ₖΦ₂(p0) + ∂ₖΦ₁(b)`. -/
def qTerm (b : Cell) (p0 : Fin 8 → ℚ) (P2 B1 B2 : J2) (k : ℕ) : ℚ :=
  if hk : k < 8 then
    quadLower ((P2.g ⟨k, hk⟩).add (B1.g ⟨k, hk⟩)) (B2.h ⟨k, hk⟩ ⟨k, hk⟩)
      (b.lo ⟨k, hk⟩ - p0 ⟨k, hk⟩) (b.hi ⟨k, hk⟩ - p0 ⟨k, hk⟩)
  else 0

/-- Cross term `j < k`: `min (Hⱼₖ dⱼ dₖ)`. -/
def cTerm (b : Cell) (p0 : Fin 8 → ℚ) (B2 : J2) (j k : ℕ) : ℚ :=
  if hj : j < 8 then
    if hk : k < 8 then
      crossLower (B2.h ⟨j, hj⟩ ⟨k, hk⟩) (b.lo ⟨j, hj⟩ - p0 ⟨j, hj⟩) (b.hi ⟨j, hj⟩ - p0 ⟨j, hj⟩)
        (b.lo ⟨k, hk⟩ - p0 ⟨k, hk⟩) (b.hi ⟨k, hk⟩ - p0 ⟨k, hk⟩)
    else 0
  else 0

/-- Lower bound of `Φ₂ + Φ₁ + Φ₀` on the box `b` around `p0`, from the point jets
`P2`, `P1` at `p0` and the box jets `B2`, `B1`, `B0`:
`Φ₂(p0) + Φ₁(p0) + Φ₀(b).lo + Σₖ (qTerm k + Σ_{j<k} cTerm j k)`. -/
def taylorLowerOf (b : Cell) (p0 : Fin 8 → ℚ) (P2 P1 B2 B1 B0 : J2) : ℚ :=
  (toQ P2.v.lo + toQ P1.v.lo + toQ B0.v.lo) +
    ((List.range 8).map fun k => qTerm b p0 P2 B1 B2 k + ((List.range k).map fun j => cTerm b p0 B2 j k).sum).sum

/-- `taylorLowerOf` with the jets of `Φ₂`, `Φ₁`, `Φ₀`. -/
def taylorLower (b : Cell) (p0 : Fin 8 → ℚ) : ℚ :=
  taylorLowerOf b p0 (phi2J (pointCell p0)) (phi1J (pointCell p0)) (phi2J b) (phi1J b) (phi0J b)

/-- The side conditions of the five jets. -/
def jetsOk (b : Cell) (p0 : Fin 8 → ℚ) : Bool :=
  (((phi2J (pointCell p0)).ok && (phi1J (pointCell p0)).ok) && ((phi2J b).ok && (phi1J b).ok)) &&
    (phi0J b).ok

/-- `p0 ∈ b`. -/
def inCell (p0 : Fin 8 → ℚ) (b : Cell) : Bool := decide (∀ i, b.lo i ≤ p0 i ∧ p0 i ≤ b.hi i)

/-- Upper bound, in units of `1/S`, of the omitted layer terms on the seam
cell `b`: `2c Σ_{wavesList 2} axialTail/κ` plus the radial tail. -/
def tailZ (b : Cell) : ℤ :=
  let s := ((wavesList 2).map fun m => (tailF b m) * ((kappaF b m).invPos).hi).sum
  cdivZ (2 * (cF b).hi * s) (Sz * Sz) + radialF b

/-- One closed box `raw` with the proposed expansion point `p0` (seam chart). -/
def boxOk (raw : Cell) (p0 : Fin 8 → ℚ) : Bool :=
  let b := seamCell raw
  (fixCheck raw && inCell p0 b) && (jetsOk b p0 &&
    decide (toQ thresholdZ + toQ (tailZ b) < taylorLower b p0))

end BccSharp.Coulomb.CompactCover.PlanarFibreTri
