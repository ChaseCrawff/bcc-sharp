import BccSharp.Cover.JLeafScreenedCheck
import BccSharp.Cover.OverlayFix

set_option autoImplicit false

/-! # A fixed-point evaluator for the late J, F and D cover leaves (definitions)

The screened J-leaf evaluator (`BccSharp.Cover.JLeafScreenedCheck`) works in exact
rational arithmetic. Its kernel time goes to rationals with the root boxes'
115-digit denominators, to shared constants recomputed by every check (the `√π`
bisection, `2 a_c`), and to the 72-bit rounded exponentials. This evaluator
computes the same certificates with integers at the scale `S = 2^96` of the Overlay
fixed-point checker (`BccSharp.Cover.OverlayFix`), whose interval type `FI`, point
exponentials (`expPosPt`, `expNegPt`) and cosine ranges (`cosRange`) it reuses
with their soundness lemmas. Soundness is proved in `BccSharp.Cover.LeafFixSound`.

* **Constants.** `π`, `√π`, `2 a_c` and the Constants brackets are literal integers,
  each checked once against the enclosure it rounds.
* **Direct tangents** (`directZ`). The anchor is `a = A/2^48`, so `a² = A²/S`
  exactly. `G(1/2, a²) = √π/a − 2 Ser(a², N) ± 4 a^{2N}/N!` with
  `Ser(q, N) = Σ_{k<N} (−q)^k/(k!(2k+1))` (`Erfc.sqrt_remainder`). The series is
  enclosed by an interval term recurrence over `ℕ` at scale `2^160`
  (`serLoop`); `e^{−a²}` is `expNegPt (A²)`. The tangent of the convex half
  kernel at `a²` gives the term.
* **Wave tangents** (`waveZ`): the joint tangent of the screened wave mode with
  a log-phase secant, as in `waveTermS`, with fixed-point enclosures.
* **Perspective terms** (`perspZ`): the affine part `2u(t − z₀)` and the exact
  penalty `−c · y eʸ` at `y = π Q*/s²`. The penalty is not replaced by a secant;
  the leaf check evaluates it at the leaf's 32 shape corners.
* **Supports** (`supportOk`): every witness is checked, its integer term is
  computed, and the 19-feature aggregate `Lin19` and the penalty list are
  compared with literals.
* **Leaves** (`jLeafOk`, `fLeafOk`, `dLeafOk`): fixed-point enclosures of the 19
  features, the penalties and the registered cost at the 256 corners, sharing
  the shape-dependent work across the eight offset corners of each shape
  corner. The D check uses a whole-box defect cap `cap` from one registration.

All integers are in units of `1/S` unless a comment says otherwise. -/

namespace BccSharp.Coulomb.CompactCover.LeafFix
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Screened (selfConst)
open BccSharp.Coulomb.CompactCover.DirectRoute (lexPositive)

/-! ### Literal constants (checked in `BccSharp.Cover.LeafFixSound`) -/

/-- `π`. -/
def piF : FI := ⟨248902613312231085230521944622, 248902613312231085230521944623⟩
/-- `√π`. -/
def sqrtPiF : FI := ⟨140428261748575876055426945548, 140428261748575876055426945551⟩
/-- `2 a_c`, the normalizing scale of the energy. -/
def acF : FI := ⟨321822038220652279784884254704, 321822038220652279784886351857⟩
/-- Upper bounds of `e_BCC`, `e_FCC` and the gap `e_FCC − e_BCC`. -/
def bccHiZ : ℤ := -70982828670438785979900039531
def fccHiZ : ℤ := -70978420376919565954174608840
def gapHiZ : ℤ := 4408293519220025725430691

def two64 : ℤ := 18446744073709551616
def two112 : ℤ := 5192296858534827628530496329220096
/-- `2^160`, the scale of the erfc series. -/
def serScale : ℕ := 1461501637330902918203684832716283019655932542976

/-! ### Rounding helpers -/

/-- `⌊z q⌋`. -/
def fmulQ (z : ℤ) (q : ℚ) : ℤ := z * q.num / (q.den : ℤ)
/-- `⌈z q⌉`. -/
def cmulQ (z : ℤ) (q : ℚ) : ℤ := cdivZ (z * q.num) (q.den : ℤ)

/-- A rational as a one-point interval, rounded outward. -/
def qF (q : ℚ) : FI := ofRat q q
def halfFI (a : FI) : FI := ⟨a.lo / 2, cdivZ a.hi 2⟩
def negF (a : FI) : FI := ⟨-a.hi, -a.lo⟩

/-! ### Exponential and cosine at points -/

/-- Upper bound of `e^(x/S)`, units `1/S`, for `x ≤ 64 S`. -/
def expUpZ (x : ℤ) : ℤ := if 0 ≤ x then ((expPosPt x.toNat).2 : ℤ) else (expNegPt (-x).toNat).hi
/-- Lower bound of `e^(x/S)`, units `1/S`, for `x ≤ 64 S`. -/
def expLoZ (x : ℤ) : ℤ := if 0 ≤ x then ((expPosPt x.toNat).1 : ℤ) else (expNegPt (-x).toNat).lo
/-- The same at a rational point `r ≤ 64`. -/
def expUpQ (r : ℚ) : ℤ := expUpZ (qF r).hi
def expLoQ (r : ℚ) : ℤ := expLoZ (qF r).lo
/-- Lower bound of `cos 2πv`, units `1/S`. -/
def cosLoQ (v : ℚ) : ℤ := (cosRange (qF v).lo (qF v).hi).lo

/-! ### Integer terms -/

/-- A support term with integer coefficients: the affine part
`(c + a Q + b t)/S` of `kind` and `index`, and a perspective penalty
`−(nl/S) y eʸ` with `y = π Q*/s²` (`nl = 0` for tangents). -/
structure ZTerm where
  kind : Kind
  index : IntVec
  c : ℤ
  a : ℤ
  b : ℤ
  nl : ℤ

/-! ### Direct (cross and period) tangents -/

/-- One step of the erfc series at `q = y/S`. The state
`(lo, hi, pLo, pHi, nLo, nHi)` encloses the current term `2^160 q^k/k!` and
`2^160` times the sums of the even and of the odd terms `q^j/(j!(2j+1))`, `j < k`,
of `Ser(q, k)`. Everything stays in `ℕ`, which the kernel evaluates faster
than `ℤ`. -/
def serStep (y k : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let d := 2 * k + 1
  let m := S * (k + 1)
  if k % 2 = 0 then
    (st.1 * y / m, cdivN (st.2.1 * y) m, st.2.2.1 + st.1 / d, st.2.2.2.1 + cdivN st.2.1 d,
      st.2.2.2.2.1, st.2.2.2.2.2)
  else
    (st.1 * y / m, cdivN (st.2.1 * y) m, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1 + st.1 / d,
      st.2.2.2.2.2 + cdivN st.2.1 d)

/-- `N` steps from `(2^160, 2^160, 0, 0, 0, 0)`; written with `Nat.rec` for the kernel. -/
def serLoop (y N : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (serScale, serScale, 0, 0, 0, 0)
    (fun k st => serStep y k st) N

/-- `G(1/2, a²)` at `a = A/2^48`: `√π/a − 2 Ser(a², N)`, widened by the series
remainder `4 a^{2N}/N!`. -/
def halfF (A N : ℕ) : FI :=
  let st := serLoop (A * A) N
  let sLo : ℤ := (st.2.2.1 : ℤ) - (st.2.2.2.2.2 : ℤ)
  let sHi : ℤ := (st.2.2.2.1 : ℤ) - (st.2.2.2.2.1 : ℤ)
  let tail : ℤ := 4 * (st.2.1 : ℤ)
  ⟨((sqrtPiF.lo * two112) / (A : ℤ) - 2 * sHi - tail) / two64,
   cdivZ (cdivZ (sqrtPiF.hi * two112) (A : ℤ) - 2 * sLo + tail) two64⟩

/-- A direct witness: mode kind and index, anchor `a = A/2^48` of the half
kernel at `a²`, and the number `N` of series terms. -/
structure DWit where
  cross : Bool
  index : IntVec
  A : ℕ
  N : ℕ

def DWit.kind (w : DWit) : Kind := if w.cross then .cross else .period
def DWit.mult (w : DWit) : ℤ := if w.cross then 1 else 2

/-- The tangent `I − P y ≤ G(1/2, π y)` at `y = s² Q`, times the prefactor
`m s`: constant `≤ m s I` and slope `≤ −m s³ P`, with
`I = (3/2) G + e^{−a²}` and `P = π (e^{−a²} + G/2)/a²`. -/
def directZ (s : ℚ) (w : DWit) : ZTerm :=
  let g := halfF w.A w.N
  let e := expNegPt (w.A * w.A)
  let iLo : ℤ := 3 * g.lo / 2 + e.lo
  let pHi : ℤ := cdivZ (piF.hi * (e.hi + cdivZ g.hi 2)) ((w.A * w.A : ℕ) : ℤ)
  ⟨w.kind, w.index, w.mult * s.num * iLo / (s.den : ℤ),
    -cdivZ (w.mult * s.num ^ 3 * pHi) ((s.den : ℤ) ^ 3), 0, 0⟩

def directOk (s : ℚ) (w : DWit) : Bool :=
  decide (0 < s) && decide (0 < w.A) && decide (2 * (w.A * w.A) ≤ S * (w.N + 1)) &&
    decide (w.A * w.A ≤ S64) && (w.cross || decide (lexPositive w.index))

/-! ### Wave tangents with a log-phase secant -/

/-- A wave witness: index, log-phase line `ℓ(t) = a + b (t − c)` and the
tangent anchor `(x̄, t̄)`. -/
structure WWit where
  index : IntVec
  a : ℚ
  b : ℚ
  xbar : ℚ
  tbar : ℚ

namespace WWit

def L (w : WWit) (box : Cell) : ℚ := windowLo box w.index
def R (w : WWit) (box : Cell) : ℚ := windowHi box w.index
def c (w : WWit) (box : Cell) : ℚ := (w.L box + w.R box) / 2
def k (w : WWit) (box : Cell) : ℤ := ⌊w.c box + 1 / 2⌋
def ell (w : WWit) (box : Cell) (t : ℚ) : ℚ := w.a + w.b * (t - w.c box)
/-- `−x̄ + ℓ(t̄)`. -/
def arg (w : WWit) (box : Cell) : ℚ := -w.xbar + w.ell box w.tbar
def fac (w : WWit) (s : ℚ) : ℚ := 2 / (w.xbar * (s * s))
/-- Enclosure of `H = 2 e^{−x̄ + ℓ(t̄)}/(x̄ s²)`. -/
def hF (w : WWit) (s : ℚ) (box : Cell) : FI :=
  ⟨fmulQ (expLoQ (w.arg box)) (w.fac s), cmulQ (expUpQ (w.arg box)) (w.fac s)⟩
/-- `Q*` coefficient, `≤ −H π (1 + 1/x̄)/s²`. -/
def cq (w : WWit) (s : ℚ) (box : Cell) : ℤ :=
  -cmulQ (cdivZ ((w.hF s box).hi * piF.hi) Sz) ((1 + 1 / w.xbar) / (s * s))
/-- Phase coefficient (any value; the constant adapts). -/
def ct (w : WWit) (s : ℚ) (box : Cell) : ℤ := fmulQ (w.hF s box).lo w.b
def gAt (w : WWit) (t : ℚ) : ℚ := 2 + w.xbar + w.b * (t - w.tbar)
/-- Lower bound of `H (2 + x̄ + b (t − t̄)) − ct t` at a window end. -/
def atZ (w : WWit) (s : ℚ) (box : Cell) (t : ℚ) : ℤ :=
  (if 0 ≤ w.gAt t then fmulQ (w.hF s box).lo (w.gAt t) else fmulQ (w.hF s box).hi (w.gAt t)) -
    cmulQ (w.ct s box) t
def kappa (w : WWit) (s : ℚ) (box : Cell) : ℤ := min (w.atZ s box (w.L box)) (w.atZ s box (w.R box))

end WWit

def waveZ (s : ℚ) (w : WWit) (box : Cell) : ZTerm :=
  ⟨.wave, w.index, w.kappa s box, w.cq s box, w.ct s box, 0⟩

def waveOk (s : ℚ) (w : WWit) (box : Cell) : Bool :=
  decide (0 < s) && decide (0 < w.xbar) && decide (lexPositive w.index) &&
    decide ((w.k box : ℚ) - 1 / 2 < w.L box) && decide (w.R box < (w.k box : ℚ) + 1 / 2) &&
    decide (w.arg box ≤ 64) && decide (w.ell box (w.L box) ≤ 64) &&
    decide (w.ell box (w.R box) ≤ 64) &&
    decide (expUpQ (w.ell box (w.L box)) ≤ Sz + cosLoQ (w.L box)) &&
    decide (expUpQ (w.ell box (w.R box)) ≤ Sz + cosLoQ (w.R box))

/-! ### Perspective terms near an extinction -/

/-- A perspective witness: index and weight `u = U/S`. -/
structure PWit where
  index : IntVec
  U : ℤ

namespace PWit

def L (w : PWit) (box : Cell) : ℚ := windowLo box w.index
def R (w : PWit) (box : Cell) : ℚ := windowHi box w.index
def k (w : PWit) (box : Cell) : ℤ := ⌊(w.L box + w.R box) / 2⌋
def z0 (w : PWit) (box : Cell) : ℚ := (w.k box : ℚ) + 1 / 2
def d (w : PWit) (box : Cell) : ℚ := max |w.L box - w.z0 box| |w.R box - w.z0 box|
/-- Lower bound of `sin πd = cos 2π(1/4 − d/2)`. -/
def sinLo (w : PWit) (box : Cell) : ℤ := cosLoQ (1 / 4 - w.d box / 2)
def coef (w : PWit) (s : ℚ) (box : Cell) : ℚ := s * s * (w.d box * w.d box)
/-- Upper bound of `u² s²/κ` with `κ = 4 sin²(πd)/d²`. -/
def nlZ (w : PWit) (s : ℚ) (box : Cell) : ℤ :=
  cdivZ (w.U * w.U * (w.coef s box).num * Sz)
    (4 * w.sinLo box * w.sinLo box * ((w.coef s box).den : ℤ))

end PWit

def perspZ (s : ℚ) (w : PWit) (box : Cell) : ZTerm :=
  ⟨.wave, w.index, -(w.U * (2 * w.k box + 1)), 0, 2 * w.U, w.nlZ s box⟩

def perspOk (s : ℚ) (w : PWit) (box : Cell) : Bool :=
  decide (0 < s) && decide (lexPositive w.index) && decide (0 < w.d box) &&
    decide (w.d box ≤ 1 / 2) && decide (0 < w.sinLo box)

/-! ### Witnesses and supports -/

inductive Wit where
  | direct (w : DWit)
  | wave (w : WWit)
  | persp (w : PWit)

def witZ (s : ℚ) (box : Cell) : Wit → ZTerm
  | .direct w => directZ s w
  | .wave w => waveZ s w box
  | .persp w => perspZ s w box

def witOk (s : ℚ) (box : Cell) : Wit → Bool
  | .direct w => directOk s w
  | .wave w => waveOk s w box
  | .persp w => perspOk s w box

/-- The aggregated affine form: constant `k` and the 19 feature weights. -/
structure Lin19 where
  k : ℤ
  w0 : ℤ
  w1 : ℤ
  w2 : ℤ
  w3 : ℤ
  w4 : ℤ
  w5 : ℤ
  w6 : ℤ
  w7 : ℤ
  w8 : ℤ
  w9 : ℤ
  w10 : ℤ
  w11 : ℤ
  w12 : ℤ
  w13 : ℤ
  w14 : ℤ
  w15 : ℤ
  w16 : ℤ
  w17 : ℤ
  w18 : ℤ
  deriving DecidableEq

def Lin19.zero : Lin19 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def Lin19.W (l : Lin19) : Fin 19 → ℤ :=
  ![l.w0, l.w1, l.w2, l.w3, l.w4, l.w5, l.w6, l.w7, l.w8, l.w9, l.w10, l.w11, l.w12, l.w13,
    l.w14, l.w15, l.w16, l.w17, l.w18]

/-- Add one term: its constant, `a · qForm` and `b · tForm` (`BccSharp.Cover.JLeafCore`). -/
def Lin19.push (l : Lin19) (t : ZTerm) : Lin19 :=
  let n0 := t.index 0
  let n1 := t.index 1
  let n2 := t.index 2
  match t.kind with
  | .cross =>
      ⟨l.k + t.c, l.w0 + t.a * (n0 * n0), l.w1 + t.a * (n1 * n1), l.w2 + t.a * (n2 * n2),
        l.w3 + t.a * (n0 * n1), l.w4 + t.a * (n0 * n2), l.w5 + t.a * (n1 * n2),
        l.w6, l.w7, l.w8, l.w9, l.w10, l.w11,
        l.w12 + t.a * (2 * n0), l.w13 + t.a * (2 * n1), l.w14 + t.a * (2 * n2), l.w15 + t.a,
        l.w16 + t.b * n0, l.w17 + t.b * n1, l.w18 + t.b * n2⟩
  | .period =>
      ⟨l.k + t.c, l.w0 + t.a * (n0 * n0), l.w1 + t.a * (n1 * n1), l.w2 + t.a * (n2 * n2),
        l.w3 + t.a * (n0 * n1), l.w4 + t.a * (n0 * n2), l.w5 + t.a * (n1 * n2),
        l.w6, l.w7, l.w8, l.w9, l.w10, l.w11, l.w12, l.w13, l.w14, l.w15,
        l.w16 + t.b * n0, l.w17 + t.b * n1, l.w18 + t.b * n2⟩
  | .wave =>
      ⟨l.k + t.c, l.w0, l.w1, l.w2, l.w3, l.w4, l.w5,
        l.w6 + t.a * (n0 * n0), l.w7 + t.a * (n1 * n1), l.w8 + t.a * (n2 * n2),
        l.w9 + t.a * (n0 * n1), l.w10 + t.a * (n0 * n2), l.w11 + t.a * (n1 * n2),
        l.w12, l.w13, l.w14, l.w15,
        l.w16 + t.b * n0, l.w17 + t.b * n1, l.w18 + t.b * n2⟩

def linOf (zs : List ZTerm) : Lin19 := zs.foldl Lin19.push Lin19.zero

def nlsOf (zs : List ZTerm) : List (IntVec × ℤ) :=
  zs.filterMap fun t => if t.nl = 0 then none else some (t.index, t.nl)

/-- A support certificate: the aggregated affine form and the penalty list. -/
structure Agg where
  lin : Lin19
  nls : List (IntVec × ℤ)

def lexLt (a b : IntVec) : Prop := a 0 < b 0 ∨ (a 0 = b 0 ∧ (a 1 < b 1 ∨ (a 1 = b 1 ∧ a 2 < b 2)))

instance (a b : IntVec) : Decidable (lexLt a b) := by unfold lexLt; infer_instance

def sortedLex : List IntVec → Bool
  | a :: b :: l => decide (lexLt a b) && sortedLex (b :: l)
  | _ => true

def kindIdxZ (k : Kind) (zs : List ZTerm) : List IntVec :=
  (zs.filter fun t => decide (t.kind = k)).map ZTerm.index

/-- Strictly increasing indices per kind (hence distinct), and lex-positive
period and wave indices. -/
def structOk (zs : List ZTerm) : Bool :=
  sortedLex (kindIdxZ .cross zs) && sortedLex (kindIdxZ .period zs) &&
    sortedLex (kindIdxZ .wave zs) &&
    (kindIdxZ .period zs).all (fun n => decide (lexPositive n)) &&
    (kindIdxZ .wave zs).all (fun n => decide (lexPositive n))

/-- The support check: every witness passes, the terms are structured, and the
literal aggregate is the aggregate of the computed terms. -/
def supportOk (s : ℚ) (box : Cell) (wits : List Wit) (agg : Agg) : Bool :=
  let zs := wits.map (witZ s box)
  decide (0 < s) && wits.all (witOk s box) && structOk zs && decide (linOf zs = agg.lin) &&
    decide (nlsOf zs = agg.nls)

/-! ### Corner enclosures

Every interval below encloses `S` times the real quantity named in its
comment (`FI.Mem`). The shape stage (32 shape corners) computes the metric
features, the penalties and the coefficients of the offset quadratics; the
offset stage (eight offset corners per shape corner) evaluates those
quadratics at the exact rational offsets. -/

def bools : List Bool := [false, true]

/-- A corner coordinate. -/
def coordF (b : Cell) (i : Axis) (bit : Bool) : FI :=
  if bit then qF (b.hi i) else qF (b.lo i)

/-- An exact corner coordinate. -/
def coordQ (b : Cell) (i : Axis) (bit : Bool) : ℚ := if bit then b.hi i else b.lo i

/-- Shape-dependent enclosures at a shape corner: the metric features `g₀ … g₅`
and `d₀ … d₅` of `featGen` and the inverses they use. -/
structure Shape where
  r1 : FI
  r2 : FI
  x : FI
  y : FI
  z : FI
  s2 : FI
  t2 : FI
  st : FI
  rr : FI
  g0 : FI
  g1 : FI
  g2 : FI
  g3 : FI
  g4 : FI
  g5 : FI
  d0 : FI
  d1 : FI
  d2 : FI
  d3 : FI
  d4 : FI
  d5 : FI

def shapeOf (b : Cell) (b0 b1 b2 b3 b4 : Bool) : Shape :=
  let r1 := coordF b 0 b0
  let r2 := coordF b 1 b1
  let x := coordF b 2 b2
  let y := coordF b 3 b3
  let z := coordF b 4 b4
  let s2 := FI.mulPos r1 r1
  let t2 := FI.mulPos r2 r2
  let st := FI.mulPos s2 t2
  let si := s2.invPos
  let ti := t2.invPos
  let h := (FI.mul x z).sub y
  ⟨r1, r2, x, y, z, s2, t2, st, (FI.mulPos r1 r2).invPos,
    s2,
    (FI.mul (FI.mul s2 x) x).add t2,
    ((FI.mul (FI.mul s2 y) y).add (FI.mul (FI.mul t2 z) z)).add st.invPos,
    FI.mul (FI.smul 2 s2) x,
    FI.mul (FI.smul 2 s2) y,
    FI.smul 2 ((FI.mul (FI.mul s2 x) y).add (FI.mul t2 z)),
    (si.add (FI.mul (FI.mul x x) ti)).add (FI.mul (FI.mul h h) st),
    ti.add (FI.mul (FI.mul z z) st),
    st,
    FI.smul 2 ((FI.mul (negF x) ti).sub (FI.mul (FI.mul h z) st)),
    FI.mul (FI.smul 2 h) st,
    FI.mul (FI.smul (-2) z) st⟩

/-- The positivity needed by the inverses. -/
def shapeGuard (sh : Shape) : Bool :=
  decide (0 < sh.r1.lo) && decide (0 < sh.r2.lo) && decide (0 < sh.s2.lo) &&
    decide (0 < sh.t2.lo) && decide (0 < sh.st.lo) && decide (0 < (FI.mulPos sh.r1 sh.r2).lo)

/-- Lower and upper bounds of `w x` for an integer `w` and `x` in an interval. -/
def lowDot (w : ℤ) (a : FI) : ℤ := if 0 ≤ w then w * a.lo else w * a.hi
def highDot (w : ℤ) (a : FI) : ℤ := if 0 ≤ w then w * a.hi else w * a.lo

/-- Lower and upper bounds of `a q` for `a` in an interval and a rational `q`. -/
def loMulQ (a : FI) (q : ℚ) : ℤ := if 0 ≤ q then fmulQ a.lo q else fmulQ a.hi q
def hiMulQ (a : FI) (q : ℚ) : ℤ := if 0 ≤ q then cmulQ a.hi q else cmulQ a.lo q

/-- Lower bound of `S² (k + Σ_{j<12} W_j feat_j)`. -/
def linShape (l : Lin19) (sh : Shape) : ℤ :=
  l.k * Sz + lowDot l.w0 sh.g0 + lowDot l.w1 sh.g1 + lowDot l.w2 sh.g2 + lowDot l.w3 sh.g3 +
    lowDot l.w4 sh.g4 + lowDot l.w5 sh.g5 + lowDot l.w6 sh.d0 + lowDot l.w7 sh.d1 +
    lowDot l.w8 sh.d2 + lowDot l.w9 sh.d3 + lowDot l.w10 sh.d4 + lowDot l.w11 sh.d5

/-- Upper bound of `S Q*` for a wave index: `Q* = Σ_k mom_k d_k`. -/
def dualHi (sh : Shape) (m : IntVec) : ℤ :=
  highDot (m 0 * m 0) sh.d0 + highDot (m 1 * m 1) sh.d1 + highDot (m 2 * m 2) sh.d2 +
    highDot (m 0 * m 1) sh.d3 + highDot (m 0 * m 2) sh.d4 + highDot (m 1 * m 2) sh.d5

/-- Upper bound of `S y` for `y = π Q*/s²`. -/
def nlY (s : ℚ) (sh : Shape) (m : IntVec) : ℤ :=
  cdivZ (piF.hi * dualHi sh m * ((s.den : ℤ) ^ 2)) (Sz * s.num ^ 2)

/-- Upper bound of `S y eʸ`. -/
def nlTerm (s : ℚ) (sh : Shape) (m : IntVec) : ℤ :=
  cdivZ (nlY s sh m * expUpZ (nlY s sh m)) Sz

def nlOk (s : ℚ) (nls : List (IntVec × ℤ)) (sh : Shape) : Bool :=
  nls.all fun e => decide (nlY s sh e.1 ≤ (S64 : ℤ))

/-- Upper bound of `S² Σ c y eʸ` over the penalty list. -/
def nlHi (s : ℚ) (nls : List (IntVec × ℤ)) (sh : Shape) : ℤ :=
  (nls.map fun e => e.2 * nlTerm s sh e.1).sum

/-- Coefficients of the offset quadratic
`Σ_{j ≥ 12} W_j feat_j = Σ_i A_i f_i + W₁₅ Σ_k g_k mono_k(f)`, each enclosing `S`
times its real value: `A₀ = W₁₂ g₀ + (W₁₃ g₃ + W₁₄ g₄)/2 + W₁₆`, … and `B_k = W₁₅ g_k`. -/
structure OffC where
  a0 : FI
  a1 : FI
  a2 : FI
  b0 : FI
  b1 : FI
  b2 : FI
  b3 : FI
  b4 : FI
  b5 : FI

def offCoef (l : Lin19) (sh : Shape) : OffC :=
  ⟨((FI.smul l.w12 sh.g0).add (halfFI ((FI.smul l.w13 sh.g3).add (FI.smul l.w14 sh.g4)))).add
      (FI.ofInt l.w16),
   ((FI.smul l.w13 sh.g1).add (halfFI ((FI.smul l.w12 sh.g3).add (FI.smul l.w14 sh.g5)))).add
      (FI.ofInt l.w17),
   ((FI.smul l.w14 sh.g2).add (halfFI ((FI.smul l.w12 sh.g4).add (FI.smul l.w13 sh.g5)))).add
      (FI.ofInt l.w18),
   FI.smul l.w15 sh.g0, FI.smul l.w15 sh.g1, FI.smul l.w15 sh.g2,
   FI.smul l.w15 sh.g3, FI.smul l.w15 sh.g4, FI.smul l.w15 sh.g5⟩

/-- Lower bound of `S² Σ_{j ≥ 12} W_j feat_j` at the offsets `(f₀, f₁, f₂)`. -/
def linOffQ (c : OffC) (f0 f1 f2 : ℚ) : ℤ :=
  loMulQ c.a0 f0 + loMulQ c.a1 f1 + loMulQ c.a2 f2 + loMulQ c.b0 (f0 * f0) +
    loMulQ c.b1 (f1 * f1) + loMulQ c.b2 (f2 * f2) + loMulQ c.b3 (f0 * f1) +
    loMulQ c.b4 (f0 * f2) + loMulQ c.b5 (f1 * f2)

/-- Upper bound of `S |R δ|² = S Σ_k g_k mono_k(δ)` for `δ = f − f₀ − n`. -/
def shiftQ (sh : Shape) (e0 e1 e2 : ℚ) : ℤ :=
  hiMulQ sh.g0 (e0 * e0) + hiMulQ sh.g1 (e1 * e1) + hiMulQ sh.g2 (e2 * e2) +
    hiMulQ sh.g3 (e0 * e1) + hiMulQ sh.g4 (e0 * e2) + hiMulQ sh.g5 (e1 * e2)

/-- Upper bound of `S ‖R B⁻¹ − U‖²_F`. -/
def strainHi (reg : RegData) (sh : Shape) : ℤ :=
  let e (a : FI) (u : ℚ) : ℤ := (FI.sq (a.sub (qF u))).hi
  let row0 (j : Fin 3) : FI :=
    FI.mul sh.r1 (((qF (reg.N 0 j)).add (FI.mul sh.x (qF (reg.N 1 j)))).add
      (FI.mul sh.y (qF (reg.N 2 j))))
  let row1 (j : Fin 3) : FI := FI.mul sh.r2 ((qF (reg.N 1 j)).add (FI.mul sh.z (qF (reg.N 2 j))))
  let row2 (j : Fin 3) : FI := FI.mul (qF (reg.N 2 j)) sh.rr
  e (row0 0) (reg.U 0 0) + e (row0 1) (reg.U 0 1) + e (row0 2) (reg.U 0 2) +
    e (row1 0) (reg.U 1 0) + e (row1 1) (reg.U 1 1) + e (row1 2) (reg.U 1 2) +
    e (row2 0) (reg.U 2 0) + e (row2 1) (reg.U 2 1) + e (row2 2) (reg.U 2 2)

/-- `⌈(2s + 2/s²) S²⌉`. -/
def scZ (s : ℚ) : ℤ := cmulQ (Sz * Sz) (selfConst s)

/-! ### Leaf checks -/

def leafGuards (box b : Cell) : Bool :=
  boxIn b box && decide (0 < b.lo 0) && decide (0 < b.lo 1) && decide (∀ i, b.lo i ≤ b.hi i)

def regGuards (reg : RegData) (b : Cell) : Bool :=
  registrationCheck reg.B reg.N reg.U reg.f0 && decide (∀ i, ∑ j, (reg.U i j) ^ 2 = 1) &&
    decide (4 * (b.hi 0 * b.hi 1) ^ 2 ≤ 9 * ∑ j, (reg.N 2 j) ^ 2)

def nlsNonneg (nls : List (IntVec × ℤ)) : Bool := nls.all fun e => decide (0 ≤ e.2)

/-- Upper bound of `2 a_c X` in units one power of `S` finer than `X`. -/
def acMulHi (X : ℤ) : ℤ := if 0 ≤ X then acF.hi * X else acF.lo * X

/-- The J comparison at one corner, from the support sum `sig` (units `1/S²`,
`selfConst` subtracted) and the registered cost `C` (units `1/S`): `C ≤ 1/2`
and `sig/S² > 2 a_c (e_BCC + g (1 − n/4096 + (n/4096) C))`. -/
def jCornerOk (n : ℤ) (sig C : ℤ) : Bool :=
  decide (2 * C ≤ Sz) &&
    decide (acMulHi (bccHiZ * Sz * 4096 + gapHiZ * ((4096 - n) * Sz + n * C)) < sig * Sz * 4096)

/-- The D comparison at one corner: `C ≤ cap` and `sig/S² > 2 a_c (e_BCC + g cap)`. -/
def dCornerOk (cap : ℤ) (sig C : ℤ) : Bool :=
  decide (C ≤ cap) && decide (acMulHi (bccHiZ * Sz + gapHiZ * cap) < sig * Sz)

/-- The F comparison at one corner: `sig/S² > 2 a_c e_FCC`. -/
def fCornerOk (sig : ℤ) : Bool := decide (acMulHi fccHiZ < sig)

/-- The support sum at a corner: shape part `base` and the offset quadratic. -/
def sigAt (base : ℤ) (c : OffC) (b : Cell) (b5 b6 b7 : Bool) : ℤ :=
  base + linOffQ c (coordQ b 5 b5) (coordQ b 6 b6) (coordQ b 7 b7)

/-- The registered cost at a corner: strain part and the shift quadratic. -/
def costAt (reg : RegData) (sh : Shape) (strain : ℤ) (b : Cell) (b5 b6 b7 : Bool) : ℤ :=
  100 * strain + 200 * shiftQ sh (coordQ b 5 b5 - reg.w 0) (coordQ b 6 b6 - reg.w 1)
    (coordQ b 7 b7 - reg.w 2)

/-- The shape-level part of the support sum. -/
def baseOf (s : ℚ) (agg : Agg) (sh : Shape) : ℤ := linShape agg.lin sh - nlHi s agg.nls sh - scZ s

def jOffsets (n : ℤ) (reg : RegData) (b : Cell) (sh : Shape) (base strain : ℤ) (c : OffC) : Bool :=
  bools.all fun b5 => bools.all fun b6 => bools.all fun b7 =>
    jCornerOk n (sigAt base c b b5 b6 b7) (costAt reg sh strain b b5 b6 b7)

def jShape (s : ℚ) (n : ℤ) (agg : Agg) (reg : RegData) (b : Cell) (sh : Shape) : Bool :=
  shapeGuard sh && nlOk s agg.nls sh &&
    jOffsets n reg b sh (baseOf s agg sh) (strainHi reg sh) (offCoef agg.lin sh)

/-- **The J leaf check** at screening `s`, mixing weight `n ≤ 4096`. -/
def jLeafOk (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (n : ℕ) : Bool :=
  (leafGuards box b && regGuards reg b && decide (n ≤ 4096) && nlsNonneg agg.nls) &&
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
      bools.all fun b4 => jShape s n agg reg b (shapeOf b b0 b1 b2 b3 b4)

def dOffsets (cap : ℤ) (reg : RegData) (b : Cell) (sh : Shape) (base strain : ℤ) (c : OffC) : Bool :=
  bools.all fun b5 => bools.all fun b6 => bools.all fun b7 =>
    dCornerOk cap (sigAt base c b b5 b6 b7) (costAt reg sh strain b b5 b6 b7)

def dShape (s : ℚ) (cap : ℤ) (agg : Agg) (reg : RegData) (b : Cell) (sh : Shape) : Bool :=
  shapeGuard sh && nlOk s agg.nls sh &&
    dOffsets cap reg b sh (baseOf s agg sh) (strainHi reg sh) (offCoef agg.lin sh)

/-- **The D leaf check**: a whole-box defect cap `cap/S ≤ 1/2` from one
registration, and the strict deficit comparison against it at every corner. -/
def dLeafOk (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (cap : ℤ) : Bool :=
  (leafGuards box b && regGuards reg b && decide (2 * cap ≤ Sz) && nlsNonneg agg.nls) &&
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
      bools.all fun b4 => dShape s cap agg reg b (shapeOf b b0 b1 b2 b3 b4)

def fOffsets (b : Cell) (base : ℤ) (c : OffC) : Bool :=
  bools.all fun b5 => bools.all fun b6 => bools.all fun b7 => fCornerOk (sigAt base c b b5 b6 b7)

def fShape (s : ℚ) (agg : Agg) (b : Cell) (sh : Shape) : Bool :=
  shapeGuard sh && nlOk s agg.nls sh && fOffsets b (baseOf s agg sh) (offCoef agg.lin sh)

/-- **The F leaf check**: the support exceeds `e_FCC` at every corner. -/
def fLeafOk (s : ℚ) (box b : Cell) (agg : Agg) : Bool :=
  (leafGuards box b && nlsNonneg agg.nls) &&
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
      bools.all fun b4 => fShape s agg b (shapeOf b b0 b1 b2 b3 b4)

end BccSharp.Coulomb.CompactCover.LeafFix
