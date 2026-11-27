import BccSharp.Cover.JensenCore
import BccSharp.Cover.OverlayFix

set_option autoImplicit false

/-! # Fixed-point evaluator for log-convex Jensen supports (definitions)

`BccSharp.Cover.JensenCore` reduces a Jensen support to its terms (`JTerm`). This
module builds the terms in the kernel from the support box `S`, the screening
`s`, the cube radius `N` and the mode limit `L` alone, with integer interval
arithmetic at the scale `S = 2^96` of `BccSharp.Cover.OverlayFix` (`FI`, `expNegPt`,
`expPosPt`, `cosRange`). No term data is proposed from outside.

* **Squared lengths** (`qF`): interval enclosures of `termQ` over a cell, from
  the chart coordinates.
* **Kernels** at an anchor `y₀ = Y/S`: `G(1, y₀) = e^{-y₀}/y₀` (`gOneF`), and
  `G(1/2, y₀) = √(π/y₀) - 2 Ser(y₀, n) ± 4 y₀ⁿ/n!` (`gHalfF`), with the
  alternating series `Ser` summed by an exact-integer term recurrence at scale
  `2^160` (`serRun`), outward rounded (the remainder is `Erfc.sqrt_remainder`).
* **Terms** (`mkTerm`): anchor `y₀` = lower end of `rate · q(centre)`; slope
  `σ` = midpoint of the enclosure of `(e^{-y₀} + a G)/(y₀ G)`; the residual
  `ε ≥ |G' + σ G|` and the range `Y ≥ |y - y₀|` over `S` give the weight
  `V = G - Y ε` (`term_lower`). A reciprocal term multiplies in a phase
  secant: endpoints `A, B` of `1 + cos 2πt` on the phase interval `[l, r]`
  (which must lie between two half-integers), slope `β` = the chord slope
  `log(B/A)/(r - l)` from four Halley steps (`secantSlope`; any slope is sound) and weight
  `p = min(A e^{βw/2}, B e^{-βw/2})` (`secantWeight`, `phase_secant`).
* **Support** (`buildSupport`): cross modes over the cube `|n_i| ≤ N`, period
  and reciprocal modes over its lex-positive half, each kept when its centre
  squared length is at most `L`.
* **F leaf** (`fLeafCheck`): at each of the 256 corners of the leaf, the exact
  rational value of the exponent's `LinTerm` sum gives `X`, and
  `M e^{X/M} - 2s - 2/s²` divided by `2 a_c` must exceed the Constants upper FCC
  energy.

Soundness: `BccSharp.Cover.JensenFixSound`. -/

namespace BccSharp.Coulomb.CompactCover.Jensen.Fix
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.DirectRoute (lexPositive cornerRat scaleInput scaleWitness offset)
open BccSharp.Coulomb.BravaisCover (cubeRootCheck)

/-! ### Constants and points -/

/-- `π`, from the `2π` enclosure of the Overlay checker. -/
def piF : FI := ⟨twoPiLo / 2, cdivZ twoPiHi 2⟩

/-- The exact point `z/S`. -/
def ptF (z : ℤ) : FI := ⟨z, z⟩

/-- The centre of a cell, as a degenerate cell. -/
def midCell (b : Cell) : Cell :=
  ⟨fun i => (b.lo i + b.hi i) / 2, fun i => (b.lo i + b.hi i) / 2⟩

/-! ### Squared lengths over a cell -/

def vecF (b : Cell) (n : IntVec) (shift : Bool) (i : Fin 3) : FI :=
  if shift then (FI.ofInt (n i)).add (cx b (offset i)) else FI.ofInt (n i)

/-- `|R(n + [shift] f)|²` over `b`. -/
def primalF (b : Cell) (n : IntVec) (shift : Bool) : FI :=
  let s2 := FI.sq (cx b 0)
  let t2 := FI.sq (cx b 1)
  let v0 := vecF b n shift 0
  let v1 := vecF b n shift 1
  let v2 := vecF b n shift 2
  let A := (v0.add (FI.mul (cx b 2) v1)).add (FI.mul (cx b 3) v2)
  let B := v1.add (FI.mul (cx b 4) v2)
  ((FI.mulPos s2 (FI.sq A)).add (FI.mulPos t2 (FI.sq B))).add
    (FI.mulPos (FI.sq v2) (FI.mulPos s2 t2).invPos)

/-- `mᵀ (Rᵀ R)⁻¹ m` over `b`. -/
def dualF (b : Cell) (m : IntVec) : FI :=
  let s2 := FI.sq (cx b 0)
  let t2 := FI.sq (cx b 1)
  let dB := (FI.ofInt (m 1)).sub (FI.smul (m 0) (cx b 2))
  let dC := ((FI.ofInt (m 2)).sub (FI.smul (m 1) (cx b 4))).add
    (FI.smul (m 0) ((FI.mul (cx b 2) (cx b 4)).sub (cx b 3)))
  ((FI.mulPos (FI.ofInt (m 0 * m 0)) s2.invPos).add (FI.mulPos (FI.sq dB) t2.invPos)).add
    (FI.mulPos (FI.mulPos s2 t2) (FI.sq dC))

def qF (b : Cell) : Kind → IntVec → FI
  | .cross, n => primalF b n true
  | .period, n => primalF b n false
  | .wave, m => dualF b m

/-- The positivity the inverses in `qF` need. -/
def qGuard (b : Cell) : Bool :=
  decide (0 < (FI.sq (cx b 0)).lo) && decide (0 < (FI.sq (cx b 1)).lo) &&
    decide (0 < (FI.mulPos (FI.sq (cx b 0)) (FI.sq (cx b 1))).lo)

/-- The rate `π s²` (direct) or `π / s²` (reciprocal). -/
def rateF (s : ℚ) : Kind → FI
  | .wave => FI.mulPos piF (ofRat (1 / (s * s)) (1 / (s * s)))
  | _ => FI.mulPos piF (ofRat (s * s) (s * s))

/-! ### Kernels at an anchor -/

/-- `2^160`, the scale of the series recurrence. -/
def T160 : ℕ := 1461501637330902918203684832716283019655932542976
/-- `2^64 = 2^160 / S`. -/
def U64 : ℕ := 18446744073709551616

/-- State of the series recurrence after `k` steps: bounds `tl ≤ T qᵏ/k! ≤ th`
and the even and odd partial sums of `qʲ/(j!(2j+1))`, `j < k`, at scale `T`. -/
structure SerSt where
  k : ℕ
  tl : ℕ
  th : ℕ
  pl : ℕ
  ph : ℕ
  nl : ℕ
  nh : ℕ

def serStep (Y : ℕ) (st : SerSt) : SerSt :=
  if st.k % 2 = 0 then
    ⟨st.k + 1, st.tl * Y / (S * (st.k + 1)), cdivN (st.th * Y) (S * (st.k + 1)),
      st.pl + st.tl / (2 * st.k + 1), st.ph + cdivN st.th (2 * st.k + 1), st.nl, st.nh⟩
  else
    ⟨st.k + 1, st.tl * Y / (S * (st.k + 1)), cdivN (st.th * Y) (S * (st.k + 1)),
      st.pl, st.ph, st.nl + st.tl / (2 * st.k + 1), st.nh + cdivN st.th (2 * st.k + 1)⟩

def serStart : SerSt := ⟨0, T160, T160, 0, 0, 0, 0⟩

def serRun (Y n : ℕ) : SerSt :=
  Nat.rec (motive := fun _ => SerSt) serStart (fun _ st => serStep Y st) n

/-- Series length for `q = Y/S`: `3⌊q⌋ + 60` terms. -/
def nTerms (Y : ℕ) : ℕ := 3 * (Y / S) + 60

/-- `G(1/2, Y/S)` with `n = nTerms Y` series terms. -/
def gHalfF (Y : ℕ) : FI :=
  let st := serRun Y (nTerms Y)
  let serLo : ℤ := ((st.pl : ℤ) - st.nh) / (U64 : ℤ)
  let serHi : ℤ := cdivZ ((st.ph : ℤ) - st.nl) U64
  let rem : ℤ := cdivN (4 * st.th) U64
  let root := FI.sqrt (FI.mulPos piF (FI.invPos (ptF Y)))
  ⟨root.lo - 2 * serHi - rem, root.hi - 2 * serLo + rem⟩

/-- `G(1, Y/S) = e^{-y}/y`. -/
def gOneF (Y : ℕ) : FI := FI.mulPos (expNegPt Y) (FI.invPos (ptF Y))

/-- The kernel value `G(a, y₀)` and `e^{-y₀} + a G(a, y₀)`, with `a = 1/2` for
direct modes and `a = 1` for reciprocal modes. -/
def kernelF (k : Kind) (Y : ℕ) : FI × FI :=
  match k with
  | .wave => let G := gOneF Y; (G, (expNegPt Y).add G)
  | _ => let G := gHalfF Y; (G, (expNegPt Y).add ⟨G.lo / 2, cdivZ G.hi 2⟩)

/-! ### Phase secants -/

def phaseLoQ (b : Cell) (m : IntVec) : ℚ :=
  min ((m 0 : ℚ) * b.lo 5) ((m 0 : ℚ) * b.hi 5) + min ((m 1 : ℚ) * b.lo 6) ((m 1 : ℚ) * b.hi 6) +
    min ((m 2 : ℚ) * b.lo 7) ((m 2 : ℚ) * b.hi 7)

def phaseHiQ (b : Cell) (m : IntVec) : ℚ :=
  max ((m 0 : ℚ) * b.lo 5) ((m 0 : ℚ) * b.hi 5) + max ((m 1 : ℚ) * b.lo 6) ((m 1 : ℚ) * b.hi 6) +
    max ((m 2 : ℚ) * b.lo 7) ((m 2 : ℚ) * b.hi 7)

/-- A lower bound of `S (1 + cos 2πv)` at a rational point `v`. -/
def onePlusCosLo (v : ℚ) : ℤ := Sz + (cosRange (ofRat v v).lo (ofRat v v).hi).lo

/-- An upper bound of `S eᶻ` at a rational point, or `0` out of range. -/
def expUpQ (z : ℚ) : ℤ :=
  let f := ofRat z z
  if 0 ≤ f.hi then (if f.hi ≤ S64 then ((expPosPt f.hi.toNat).2 : ℤ) else 0)
  else (expNegPt (-f.hi).toNat).hi

/-- A lower bound of `S eᶻ` at a rational point (`0` out of range). -/
def expLoZ (z : ℚ) : ℤ :=
  let f := ofRat z z
  if 0 ≤ f.lo then (if f.lo ≤ S64 then ((expPosPt f.lo.toNat).1 : ℤ) else 0)
  else (expNegPt (-f.lo).toNat).lo

/-- One Halley step for `eˣ = T`, rounded to `1/S`. -/
def logStep (T x : ℚ) : ℚ :=
  let e : ℚ := (expUpQ x : ℚ) / Sz
  ((((x + 2 * (T - e) / (T + e)) * Sz).floor : ℤ) : ℚ) / Sz

/-- `log(B/A)` to about `2^-90`: four Halley steps from the Padé start
`2(B-A)/(B+A)`. Only a proposal: every slope gives a sound secant. -/
def logRatio (A B : ℤ) : ℚ :=
  let T : ℚ := (B : ℚ) / A
  logStep T (logStep T (logStep T (logStep T (2 * ((B : ℚ) - A) / ((B : ℚ) + A)))))

/-- The chord slope of `log(1 + cos 2πt)` on `[l, r]` (`0` on a degenerate interval). -/
def secantSlope (l r : ℚ) : ℚ :=
  if r - l = 0 ∨ onePlusCosLo l ≤ 0 ∨ onePlusCosLo r ≤ 0 then 0
  else logRatio (onePlusCosLo l) (onePlusCosLo r) / (r - l)

/-- The secant weight (units `1/S`): the largest `p` the two endpoint bounds allow. -/
def secantWeight (l r : ℚ) : ℤ :=
  min (onePlusCosLo l * Sz / expUpQ (-(secantSlope l r * (r - l) / 2)))
    (onePlusCosLo r * Sz / expUpQ (secantSlope l r * (r - l) / 2))

/-- `[l, r]` lies strictly between two consecutive half-integers, and the
endpoint bounds are positive. -/
def secantOk (l r : ℚ) : Bool :=
  decide (((⌊(l + r) / 2 + 1 / 2⌋ : ℤ) : ℚ) - 1 / 2 < l ∧ r < ((⌊(l + r) / 2 + 1 / 2⌋ : ℤ) : ℚ) + 1 / 2 ∧
    l ≤ r ∧ 0 < onePlusCosLo l ∧ 0 < onePlusCosLo r ∧
    0 < expUpQ (-(secantSlope l r * (r - l) / 2)) ∧ 0 < expUpQ (secantSlope l r * (r - l) / 2))

/-- The phase secant on `[l, r]`: slope `β` and weight `p` (units `1/S`), or
`none` when a half-integer meets the interval or a bound fails. -/
def secantData (l r : ℚ) : Option (ℚ × ℤ) :=
  if secantOk l r then some (secantSlope l r, secantWeight l r) else none

/-! ### Terms -/

/-- The radial data of a term on the support box `S`: anchor `y₀ = Y/S`,
range `|y - y₀| ≤ Ym/S` over `S`, kernel value `G` and `e^{-y₀} + a G` at the
anchor, slope `σ = sig/S`, residual `|G' + σ G| ≤ em/S`, weight `V/S`, rate
enclosure `r`, and the centre squared length `qc` (selection only). -/
structure Radial where
  Y : ℤ
  Ym : ℤ
  G : FI
  num : FI
  sig : ℤ
  em : ℤ
  V : ℤ
  r : FI
  qc : FI

def radialOf (s : ℚ) (S : Cell) (k : Kind) (n : IntVec) : Radial :=
  let qc := qF (midCell S) k n
  let r := rateF s k
  let Y := (FI.mulPos r qc).lo
  let yr := FI.mulPos r (qF S k n)
  let Ym : ℤ := max 0 (max (yr.hi - Y) (Y - yr.lo))
  let G := (kernelF k Y.toNat).1
  let num := (kernelF k Y.toNat).2
  let iy := FI.invPos (ptF Y)
  let sigF := FI.mulPos num (FI.mulPos iy G.invPos)
  let sig := (sigF.lo + sigF.hi) / 2
  let eps := (FI.mul G (ptF sig)).sub (FI.mulPos num iy)
  let em : ℤ := max 0 (max eps.hi (-eps.lo))
  ⟨Y, Ym, G, num, sig, em, G.lo - cdivZ (Ym * em) Sz, r, qc⟩

def radialOk (s L : ℚ) (S : Cell) (d : Radial) : Bool :=
  qGuard S && decide (0 < s) && decide (0 < d.Y) && decide ((d.qc.lo : ℚ) ≤ L * Sz) &&
    decide (0 < d.G.lo) && decide (0 < d.V) && decide (0 ≤ d.sig)

/-- The term of kind `k` and index `n` on the support box `S`, or `none`. -/
def mkTerm (s L : ℚ) (S : Cell) (k : Kind) (n : IntVec) : Option JTerm :=
  let d := radialOf s S k n
  if radialOk s L S d then
    match k with
    | .cross => some ⟨.cross, n, s * ((d.V : ℚ) / Sz), (d.sig : ℚ) / Sz, (d.Y : ℚ) / Sz, 0, 0,
        (d.r.hi : ℚ) / Sz⟩
    | .period => some ⟨.period, n, 2 * s * ((d.V : ℚ) / Sz), (d.sig : ℚ) / Sz, (d.Y : ℚ) / Sz,
        0, 0, (d.r.hi : ℚ) / Sz⟩
    | .wave =>
      match secantData (phaseLoQ S n) (phaseHiQ S n) with
      | none => none
      | some (β, pz) =>
        if 0 ≤ pz then
          some ⟨.wave, n, 2 / (s * s) * ((pz : ℚ) / Sz) * ((d.V : ℚ) / Sz), (d.sig : ℚ) / Sz,
            (d.Y : ℚ) / Sz, β, (phaseLoQ S n + phaseHiQ S n) / 2, (d.r.hi : ℚ) / Sz⟩
        else none
  else none

/-! ### The support -/

def cubeRange (N : ℕ) : List ℤ := (List.range (2 * N + 1)).map fun (i : ℕ) => (i : ℤ) - N

/-- The cube `|n_i| ≤ N` in lexicographic order. -/
def cubeNodes (N : ℕ) : List IntVec :=
  (cubeRange N).flatMap fun a => (cubeRange N).flatMap fun b => (cubeRange N).map fun c => ![a, b, c]

/-- The lex-positive half of the cube. -/
def halfNodes (N : ℕ) : List IntVec := (cubeNodes N).filter fun n => decide (lexPositive n)

def buildSupport (s L : ℚ) (N : ℕ) (S : Cell) : List JTerm :=
  (cubeNodes N).filterMap (mkTerm s L S .cross) ++ (halfNodes N).filterMap (mkTerm s L S .period) ++
    (halfNodes N).filterMap (mkTerm s L S .wave)

/-! ### Aggregates -/

/-- Mass, constant and the 19 feature weights of a support. -/
structure Agg where
  M : ℚ
  C : ℚ
  w : List ℚ

def aggOf (ts : List JTerm) : Agg :=
  ⟨mass ts, centerConst ts, (List.finRange 19).map fun j => aggWeight (ts.map JTerm.lin) j⟩

/-- The exponent's lower value at a rational corner `c`: `C + Σ wⱼ featGen(c)ⱼ`. -/
def cornerValue (a : Agg) (c : Fin 8 → ℚ) : ℚ :=
  a.C + ((List.finRange 19).map fun (j : Fin 19) => a.w.getD j.val 0 * featGen c j).sum

/-! ### The F leaf check -/

def bools : List Bool := [false, true]

def cornerOf (b : Cell) (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Fin 8 → ℚ :=
  cornerRat b ![b0, b1, b2, b3, b4, b5, b6, b7]

/-- The F comparison at one corner. -/
def fCornerOk (s : ℚ) (a : Agg) (c : Fin 8 → ℚ) : Bool :=
  decide (Constants.fccBracket.hi <
    divScale (a.M * ((expLoZ (cornerValue a c / a.M) : ℚ) / Sz) - (2 * s + 2 / s ^ 2)))

def leafGuards (S b : Cell) : Bool :=
  boxIn b S && decide (0 < b.lo 0) && decide (0 < b.lo 1) && decide (∀ i, b.lo i ≤ b.hi i) &&
    cubeRootCheck scaleWitness scaleInput && decide (0 < scaleWitness.lower)

/-- **The F leaf check**: the Jensen support built on `S` exceeds `e_FCC`
at every corner of the leaf `b ⊆ S`. -/
def fLeafCheckAgg (s : ℚ) (a : Agg) (S b : Cell) : Bool :=
  (decide (0 < s) && decide (0 < a.M) && leafGuards S b) &&
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
      bools.all fun b4 => bools.all fun b5 => bools.all fun b6 => bools.all fun b7 =>
        fCornerOk s a (cornerOf b b0 b1 b2 b3 b4 b5 b6 b7)

def fLeafCheck (s L : ℚ) (N : ℕ) (S b : Cell) : Bool :=
  fLeafCheckAgg s (aggOf (buildSupport s L N S)) S b

end BccSharp.Coulomb.CompactCover.Jensen.Fix
