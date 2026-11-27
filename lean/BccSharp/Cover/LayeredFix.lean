import BccSharp.Cover.LayeredGain
import BccSharp.Cover.OverlayFix
import BccSharp.Cover.OverlaySharpLayer

set_option autoImplicit false

/-! # A fixed-point evaluator for the layered half-height gain matrix

On a seam cell `b` (coordinates `r, s, x, y, z, f₁, f₂, h`, anchor height
`1/2`) and lateral anchor offsets `α = k/2` this evaluator encloses, with
integer endpoints at the scale `S = 2^96` of `OverlayPlanar.Fix`, the entries of a
symmetric `3 × 3` matrix `M` such that for every point `p` of the cell

  `2 a_c (e(p) − e(anchor)) ≥ zᵀ M* z`, `z = (v₁, v₂, δ)`,

for some `M*` inside the enclosure (`Layered.layered_gain`, made a quadratic
form in `BccSharp.Cover.LayeredFixSound`). Per retained wave it uses the Overlay wave
operands `cF`, `kappaF`, `tF`, `wF`; `cos(πw)` and `sin(πw)` come from
`cosRange` at `w/2` and `w/2 − 1/4`.

`surplusF` subtracts `λ G`, with `G` the layer Gram matrix of `|R d|²`, and
`pdOk` checks every symmetric matrix inside the six entry intervals positive
definite: the three `LDLᵀ` pivots, propagated through interval arithmetic,
have positive lower ends. `splitOk` bisects the five shape coordinates `depth`
times and requires every piece to pass. -/

namespace BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix

/-! ### Interval helpers -/

def halfF (a : FI) : FI := ⟨a.lo / 2, cdivZ a.hi 2⟩
def negF (a : FI) : FI := ⟨-a.hi, -a.lo⟩
def ptF (z : ℤ) : FI := ⟨z, z⟩
/-- `x / n` for a positive natural `n`. -/
def divNatF (a : FI) (n : ℕ) : FI := ⟨a.lo / (n : ℤ), cdivZ a.hi (n : ℤ)⟩
/-- `|x|`. -/
def absF (a : FI) : FI :=
  if 0 ≤ a.lo then a else if a.hi ≤ 0 then ⟨-a.hi, -a.lo⟩ else ⟨0, max (-a.lo) a.hi⟩
/-- `max 0 (−x)`. -/
def negPartF (a : FI) : FI := ⟨max 0 (-a.hi), max 0 (-a.lo)⟩
/-- The interval `[−e, e]` for `e ≥ 0` given by an interval's upper end. -/
def symF (a : FI) : FI := ⟨-a.hi, a.hi⟩
/-- The magnitude bound `max |lo| |hi|`. -/
def magZ (a : FI) : ℤ := max |a.lo| |a.hi|

/-- `cos(πw)`. -/
def cosPiF (w : FI) : FI := cosRange (halfF w).lo (halfF w).hi
/-- `sin(πw) = cos(2π(w/2 − 1/4))`. -/
def sinPiF (w : FI) : FI := cosRange ((halfF w).lo - Sz / 4) ((halfF w).hi - Sz / 4)
/-- `e^{a/S}` for `a ≥ 0`. -/
def expPosF (a : ℤ) : FI := (expNegPt a.toNat).invPos

def parityZ (k : ℤ) : ℤ := if k % 2 = 0 then 1 else -1

/-! ### Box quantities -/

/-- The anchor: `2α₁ = k₁`, `2α₂ = k₂` and the retained cube `K`. -/
structure Anchor where
  k₁ : ℤ
  k₂ : ℤ
  cube : ℕ
  deriving DecidableEq, Repr

def alphaF (k : ℤ) : FI := ptF (k * halfS)

/-- `σ₁ = y − x z`. -/
def sigma₁F (b : Cell) : FI := (cx b 3).sub (FI.mul (cx b 2) (cx b 4))

/-- The lateral displacement `v`. -/
def v₁F (b : Cell) (an : Anchor) : FI := ((cx b 5).sub (alphaF an.k₁)).add (FI.mul (sigma₁F b) (deltaF b))
def v₂F (b : Cell) (an : Anchor) : FI := ((cx b 6).sub (alphaF an.k₂)).add (FI.mul (cx b 4) (deltaF b))

/-- `η ≥ |δ|`, `ρᵢ ≥ |vᵢ|`, at scale `S`. -/
def etaZ (b : Cell) : ℤ := magZ (deltaF b)
def rho₁Z (b : Cell) (an : Anchor) : ℤ := magZ (v₁F b an)
def rho₂Z (b : Cell) (an : Anchor) : ℤ := magZ (v₂F b an)

/-! ### One retained wave -/

/-- `W = (4c/κ) e^{−T/2}`. -/
def wF' (b : Cell) (m : Wave) : FI :=
  let t := tF b m
  FI.mulPos (FI.mulPos (FI.smul 4 (cF b)) (kappaF b m).invPos) (expRange (t.lo / 2) (cdivZ t.hi 2))

def cgF (b : Cell) (an : Anchor) (m : Wave) : FI := FI.smul (parityZ (m.1 * an.k₁ + m.2 * an.k₂)) (cosPiF (wF b m))
def sgF (b : Cell) (an : Anchor) (m : Wave) : FI := FI.smul (parityZ (m.1 * an.k₁ + m.2 * an.k₂)) (sinPiF (wF b m))

/-- `A ≥ |T δ|` and `Ψ ≥ 2π(|m₁|ρ₁ + |m₂|ρ₂)`, at scale `S`. -/
def aZ (b : Cell) (m : Wave) : ℤ := cdivZ ((tF b m).hi * etaZ b) Sz
def psiZ (b : Cell) (an : Anchor) (m : Wave) : ℤ :=
  cdivZ (twoPiHi * ((m.1.natAbs : ℤ) * rho₁Z b an + (m.2.natAbs : ℤ) * rho₂Z b an)) Sz

/-- `e^{−T} / (1 − e^{−T}) · e^{A}`. -/
def afF (b : Cell) (m : Wave) : FI :=
  let t := tF b m
  let e := expRange t.lo t.hi
  FI.mul (FI.mul e ((ptF Sz).sub e).invPos) (expPosF (aZ b m))

/-- `K' = A² e^{A} / 2 + Ψ² / 6`. -/
def kpF (b : Cell) (an : Anchor) (m : Wave) : FI :=
  (halfF (FI.mul (FI.sq (ptF (aZ b m))) (expPosF (aZ b m)))).add (divNatF (FI.sq (ptF (psiZ b an m))) 6)

def fourPiSqF : FI := FI.sq twoPiF

/-- `λ = −W · 4π² (cg/2 + max(0, −cg) Ψ²/24 + af)`. -/
def lamF (b : Cell) (an : Anchor) (m : Wave) : FI :=
  let cg := cgF b an m
  negF (FI.mul (FI.mul (wF' b m) fourPiSqF)
    (((halfF cg).add (divNatF (FI.mul (negPartF cg) (FI.sq (ptF (psiZ b an m)))) 24)).add (afF b m)))

/-- `μ = −W T² (|cg| e^{A}/2 + af)`. -/
def muF (b : Cell) (an : Anchor) (m : Wave) : FI :=
  negF (FI.mul (FI.mul (wF' b m) (FI.sq (tF b m)))
    ((halfF (FI.mul (absF (cgF b an m)) (expPosF (aZ b m)))).add (afF b m)))

/-- `χ = 2π W T sg`. -/
def chiF (b : Cell) (an : Anchor) (m : Wave) : FI :=
  FI.mul (FI.mul (FI.mul twoPiF (wF' b m)) (tF b m)) (sgF b an m)

/-- `ε = 2π W T |sg| K'`. -/
def epsF (b : Cell) (an : Anchor) (m : Wave) : FI :=
  FI.mul (FI.mul (FI.mul (FI.mul twoPiF (wF' b m)) (tF b m)) (absF (sgF b an m))) (kpF b an m)

/-- Guards for one wave: positive `κ`, `T`, `1 − e^{−T}` and `e^{−A}`. -/
def waveOk (b : Cell) (an : Anchor) (m : Wave) : Bool :=
  let t := tF b m
  decide (0 < (kappaF b m).lo ∧ 0 < t.lo ∧ 0 < ((ptF Sz).sub (expRange t.lo t.hi)).lo ∧
    0 ≤ aZ b m ∧ aZ b m ≤ (S64 : ℤ) ∧ 0 < (expNegPt (aZ b m).toNat).lo ∧ 0 ≤ psiZ b an m)

/-! ### The omitted-wave tail -/

/-- `τ` and `B` of the Overlay radial tail. -/
def tauZ (b : Cell) : ℤ := (tauN b : ℤ)

/-- `q = e^{−τ(1/2−η)}` (upper end). -/
def qUpZ (b : Cell) : ℤ := (expNegPt (tauZ b * (halfS - etaZ b) / Sz).toNat).hi

/-- The enclosure `[0, q⁺]` of `q`. -/
def qF (b : Cell) : FI := ⟨0, qUpZ b⟩

/-- `q^n` by repeated products, starting from `1`. -/
def powF (a : FI) : ℕ → FI
  | 0 => ptF Sz
  | n + 1 => FI.mulPos (powF a n) a

/-- An enclosure of `outerTail c B τ η K` with `c ∈ cF b`, `B = columnF/S`,
`τ = tauZ/S`, `η = etaZ/S`:
`c · (16 B / (1 − e^{−τ}) · (J² q^J / (1 − ((J+1)/J)² q)))`. -/
def outerF (b : Cell) (K : ℕ) : FI :=
  let J : ℤ := (K : ℤ) + 1
  let d₁ : FI := (ptF Sz).sub (expNegPt (tauZ b).toNat)
  let ratio : FI := divNatF (FI.smul ((J + 1) * (J + 1)) (qF b)) (J * J).toNat
  let d₂ : FI := (ptF Sz).sub ratio
  FI.mul (cF b) (FI.mulPos (FI.mulPos (FI.smul 16 (ptF (columnF b))) d₁.invPos)
    (FI.mulPos (FI.smul (J * J) (powF (qF b) (K + 1))) d₂.invPos))

def outerOk (b : Cell) (K : ℕ) : Bool :=
  let J : ℤ := (K : ℤ) + 1
  let q := qUpZ b
  decide (0 < tauZ b ∧ 0 < columnF b ∧ (expNegPt (tauZ b).toNat).hi < Sz ∧ 2 * etaZ b < Sz ∧
    -- 2/(1/2 − η) ≤ τ (K+1)
    (2 * Sz * Sz : ℤ) ≤ tauZ b * J * (halfS - etaZ b) ∧
    -- ((J+1)/J)² q < 1
    (J + 1) * (J + 1) * q < J * J * Sz ∧
    0 < Sz - cdivZ ((J + 1) * (J + 1) * q) (J * J))

/-! ### The matrix -/

/-- `m₁²`, `m₂²`, `m₁m₂`, `m₁`, `m₂`, `|m₁|`, `|m₂|`. -/
def sumW (l : List Wave) (f : Wave → FI) : FI := sumF (l.map f)

def m00F (b : Cell) (an : Anchor) : FI :=
  (sumW (wavesList an.cube) (fun m => FI.smul (m.1 * m.1) (lamF b an m))).sub
    (FI.mul fourPiSqF (FI.smul 2 (outerF b an.cube)))
def m11F (b : Cell) (an : Anchor) : FI :=
  (sumW (wavesList an.cube) (fun m => FI.smul (m.2 * m.2) (lamF b an m))).sub
    (FI.mul fourPiSqF (FI.smul 2 (outerF b an.cube)))
def m01F (b : Cell) (an : Anchor) : FI :=
  sumW (wavesList an.cube) (fun m => FI.smul (m.1 * m.2) (lamF b an m))
def m22F (b : Cell) (an : Anchor) : FI :=
  ((FI.mul twoPiF (FI.sq (cF b))).add (sumW (wavesList an.cube) (muF b an))).sub
    (FI.mul (FI.sq (ptF (tauZ b))) (outerF b an.cube))
def m02F (b : Cell) (an : Anchor) : FI :=
  (halfF (sumW (wavesList an.cube) (fun m => FI.smul m.1 (chiF b an m)))).add
    (symF (halfF (sumW (wavesList an.cube) (fun m => FI.smul (m.1.natAbs : ℤ) (epsF b an m)))))
def m12F (b : Cell) (an : Anchor) : FI :=
  (halfF (sumW (wavesList an.cube) (fun m => FI.smul m.2 (chiF b an m)))).add
    (symF (halfF (sumW (wavesList an.cube) (fun m => FI.smul (m.2.natAbs : ℤ) (epsF b an m)))))

/-! ### The layer Gram matrix and the surplus -/

/-- `|R d|² = r²(v₁ + x v₂)² + s² v₂² + c² δ²`. -/
def g00F (b : Cell) : FI := FI.sq (cx b 0)
def g01F (b : Cell) : FI := FI.mul (FI.sq (cx b 0)) (cx b 2)
def g11F (b : Cell) : FI := (FI.sq (FI.mul (cx b 0) (cx b 2))).add (FI.sq (cx b 1))
def g22F (b : Cell) : FI := FI.sq (cF b)

/-- `x − λ y` on intervals, for a rational `λ ≥ 0`. -/
def subScaled (x y : FI) (lam : ℚ) : FI := x.sub (FI.mul (ofRat lam lam) y)

/-- The six entries of the symmetric surplus `M − λ G`:
`(s₀₀, s₀₁, s₁₁, s₀₂, s₁₂, s₂₂)`. -/
structure Sym3 where
  s00 : FI
  s01 : FI
  s11 : FI
  s02 : FI
  s12 : FI
  s22 : FI

def surplusF (b : Cell) (an : Anchor) (lam : ℚ) : Sym3 :=
  ⟨subScaled (m00F b an) (g00F b) lam, subScaled (m01F b an) (g01F b) lam,
    subScaled (m11F b an) (g11F b) lam, m02F b an, m12F b an, subScaled (m22F b an) (g22F b) lam⟩

/-- The interval `LDLᵀ` pivots: `d₀ = s₀₀`, `d₁ = s₁₁ − s₀₁²/s₀₀`,
`t = s₁₂ − s₀₂ s₀₁/s₀₀`, `d₂ = s₂₂ − s₀₂²/s₀₀ − t²/d₁`. -/
def pivot₁ (s : Sym3) : FI := s.s11.sub (FI.mul (FI.sq s.s01) s.s00.invPos)
def tcross (s : Sym3) : FI := s.s12.sub (FI.mul (FI.mul s.s02 s.s01) s.s00.invPos)
def pivot₂ (s : Sym3) : FI :=
  (s.s22.sub (FI.mul (FI.sq s.s02) s.s00.invPos)).sub (FI.mul (FI.sq (tcross s)) (pivot₁ s).invPos)

/-- Every symmetric matrix in the intervals is positive definite. -/
def pdOk (s : Sym3) : Bool := decide (0 < s.s00.lo ∧ 0 < (pivot₁ s).lo ∧ 0 < (pivot₂ s).lo)

/-! ### The cell check -/

def guardsOk (b : Cell) : Bool :=
  decide (0 < (cx b 0).lo ∧ 0 < (cx b 1).lo ∧ 0 < (FI.mulPos (cx b 0) (cx b 1)).lo)

/-- One cell: guards, the omitted-wave tail, every retained wave, and
positive definiteness of `M − λ G`. -/
def leafOk (b : Cell) (an : Anchor) (lam : ℚ) : Bool :=
  ((guardsOk b && outerOk b an.cube) && (wavesList an.cube).all (waveOk b an)) &&
    pdOk (surplusF b an lam)

/-- The shape coordinate of largest weighted width (weights `3, 3, 3/2, 1, 1`). -/
def widest (b : Cell) : Axis :=
  let w : Fin 5 → ℚ := ![3, 3, 3 / 2, 1, 1]
  let width (i : Fin 5) : ℚ := w i * (b.hi ⟨i.val, by omega⟩ - b.lo ⟨i.val, by omega⟩)
  let best := [1, 2, 3, 4].foldl (fun (k : Fin 5) (i : Fin 5) => if width k < width i then i else k)
    (0 : Fin 5)
  ⟨best.val, by omega⟩

/-- Bisect the shape coordinates `depth` times; every piece must pass. -/
def splitOk (an : Anchor) (lam : ℚ) : ℕ → Cell → Bool
  | 0, b => leafOk b an lam
  | d + 1, b =>
    let i := widest b
    splitOk an lam d (replaceEnd b i (midpoint b i) false) &&
      splitOk an lam d (replaceEnd b i (midpoint b i) true)

end BccSharp.Coulomb.CompactCover.Layered.Fix
