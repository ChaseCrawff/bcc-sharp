import BccSharp.Cover.JLeafKernels

set_option autoImplicit false

/-! Core definitions for the JointDeficit/Continuation J-leaf evaluator, in the original
(unsquared) chart coordinates `p = (r₁, r₂, x, y, z, f₁, f₂, f₃)`.

`primalQ` and `dualQ` are the squared lengths of the direct and reciprocal
images, written out in chart coordinates. A `LinTerm` is a rational affine
function of one such squared length and of one phase `m · f`. Its meaning is
fixed by `physical`: the checked witness families in later modules prove that a
term lies below the corresponding series contribution on a box.

The 19 `featGen` coordinates are the features (primal and
reciprocal metrics with folded off-diagonals, `G f`, `fᵀ G f` and `f`). Every
squared length and phase is a fixed rational linear form in them, which makes
the 256-corner evaluation of a whole support a 19-term dot product. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.DirectRoute (offset pairedTerm)

/-! ### Squared lengths and phases in chart coordinates -/

/-- Coordinates `v + [shift] f` of a lattice image, with rational `v`. -/
def img (v : Fin 3 → ℚ) (shift : Bool) (p : Chart) (i : Fin 3) : ℝ :=
  (v i : ℝ) + if shift then p (offset i) else 0

def rowA (v : Fin 3 → ℚ) (shift : Bool) (p : Chart) : ℝ :=
  img v shift p 0 + p 2 * img v shift p 1 + p 3 * img v shift p 2

def rowB (v : Fin 3 → ℚ) (shift : Bool) (p : Chart) : ℝ :=
  img v shift p 1 + p 4 * img v shift p 2

def rowC (v : Fin 3 → ℚ) (shift : Bool) (p : Chart) : ℝ := img v shift p 2

/-- `|chartBasis p · (v + [shift] f)|²`. -/
def primalQ (v : Fin 3 → ℚ) (shift : Bool) (p : Chart) : ℝ :=
  (p 0) ^ 2 * (rowA v shift p) ^ 2 + (p 1) ^ 2 * (rowB v shift p) ^ 2 +
    (rowC v shift p) ^ 2 / ((p 0) ^ 2 * (p 1) ^ 2)

def dualB (m : IntVec) (p : Chart) : ℝ := (m 1 : ℝ) - p 2 * (m 0 : ℝ)

def dualC (m : IntVec) (p : Chart) : ℝ :=
  (m 2 : ℝ) - p 4 * (m 1 : ℝ) + (p 2 * p 4 - p 3) * (m 0 : ℝ)

/-- `mᵀ (Bᵀ B)⁻¹ m` for the chart basis `B`. -/
def dualQ (m : IntVec) (p : Chart) : ℝ :=
  (m 0 : ℝ) ^ 2 / (p 0) ^ 2 + (dualB m p) ^ 2 / (p 1) ^ 2 +
    (p 0) ^ 2 * (p 1) ^ 2 * (dualC m p) ^ 2

/-- The reciprocal phase `m · f`. -/
def phaseT (m : IntVec) (p : Chart) : ℝ := ∑ i : Fin 3, (m i : ℝ) * p (offset i)

def intVec (n : IntVec) : Fin 3 → ℚ := fun i => (n i : ℚ)

/-! ### The registered cost -/

/-- Entry `(i, j)` of `chartBasis p * N`. -/
def strainEntry (N : Fin 3 → Fin 3 → ℚ) (p : Chart) (i j : Fin 3) : ℝ :=
  if i = 0 then p 0 * ((N 0 j : ℝ) + p 2 * (N 1 j : ℝ) + p 3 * (N 2 j : ℝ))
  else if i = 1 then p 1 * ((N 1 j : ℝ) + p 4 * (N 2 j : ℝ))
  else (N 2 j : ℝ) / (p 0 * p 1)

/-- `‖chartBasis p * N - U‖²_F`. -/
def strainCost (N U : Fin 3 → Fin 3 → ℚ) (p : Chart) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (strainEntry N p i j - (U i j : ℝ)) ^ 2

/-- `100 ‖R B⁻¹ - U‖²_F + 200 |R (f - w)|²` with `N = B⁻¹` and `w = f₀ + n`. -/
def regCost (N U : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (p : Chart) : ℝ :=
  100 * strainCost N U p + 200 * primalQ (fun i => -w i) true p

/-- Rational value of `regCost` at a rational point. -/
def strainEntryQ (N : Fin 3 → Fin 3 → ℚ) (c : Fin 8 → ℚ) (i j : Fin 3) : ℚ :=
  if i = 0 then c 0 * (N 0 j + c 2 * N 1 j + c 3 * N 2 j)
  else if i = 1 then c 1 * (N 1 j + c 4 * N 2 j)
  else N 2 j / (c 0 * c 1)

def imgQ (v : Fin 3 → ℚ) (shift : Bool) (c : Fin 8 → ℚ) (i : Fin 3) : ℚ :=
  v i + if shift then c (offset i) else 0

def primalQQ (v : Fin 3 → ℚ) (shift : Bool) (c : Fin 8 → ℚ) : ℚ :=
  let a := imgQ v shift c 0 + c 2 * imgQ v shift c 1 + c 3 * imgQ v shift c 2
  let b := imgQ v shift c 1 + c 4 * imgQ v shift c 2
  let z := imgQ v shift c 2
  (c 0) ^ 2 * a ^ 2 + (c 1) ^ 2 * b ^ 2 + z ^ 2 / ((c 0) ^ 2 * (c 1) ^ 2)

def regCostQ (N U : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (c : Fin 8 → ℚ) : ℚ :=
  100 * (∑ i : Fin 3, ∑ j : Fin 3, (strainEntryQ N c i j - U i j) ^ 2) +
    200 * primalQQ (fun i => -w i) true c

/-! ### Features and linear forms -/

/-- The 19 features: primal metric `(G₀₀, G₁₁, G₂₂, 2G₀₁, 2G₀₂, 2G₁₂)`, the
same for `G⁻¹`, then `G f`, `fᵀ G f` and `f`. -/
def featGen {K : Type} [Field K] (p : Fin 8 → K) : Fin 19 → K :=
  let s := p 0 * p 0
  let t := p 1 * p 1
  let x := p 2
  let y := p 3
  let z := p 4
  let f0 := p 5
  let f1 := p 6
  let f2 := p 7
  let u := (s * t)⁻¹
  let h := x * z - y
  let g0 := s
  let g1 := s * x * x + t
  let g2 := s * y * y + t * z * z + u
  let g3 := 2 * s * x
  let g4 := 2 * s * y
  let g5 := 2 * (s * x * y + t * z)
  let d0 := s⁻¹ + x * x * t⁻¹ + h * h * (s * t)
  let d1 := t⁻¹ + z * z * (s * t)
  let d2 := s * t
  let d3 := 2 * (-x * t⁻¹ - h * z * (s * t))
  let d4 := 2 * h * (s * t)
  let d5 := -2 * z * (s * t)
  let u0 := g0 * f0 + (g3 * f1 + g4 * f2) / 2
  let u1 := g1 * f1 + (g3 * f0 + g5 * f2) / 2
  let u2 := g2 * f2 + (g4 * f0 + g5 * f1) / 2
  let fu := f0 * u0 + f1 * u1 + f2 * u2
  ![g0, g1, g2, g3, g4, g5, d0, d1, d2, d3, d4, d5, u0, u1, u2, fu, f0, f1, f2]

/-- Quadratic moments `(n₀², n₁², n₂², n₀n₁, n₀n₂, n₁n₂)`. -/
def mom (n : IntVec) : Fin 6 → ℚ :=
  ![(n 0 : ℚ) * n 0, (n 1 : ℚ) * n 1, (n 2 : ℚ) * n 2,
    (n 0 : ℚ) * n 1, (n 0 : ℚ) * n 2, (n 1 : ℚ) * n 2]

inductive Kind where
  | cross | period | wave
  deriving DecidableEq, Repr

/-- Coefficients of a squared length in the 19 features. -/
def qForm (k : Kind) (n : IntVec) (j : Fin 19) : ℚ :=
  match k with
  | .period => if h : j.val < 6 then mom n ⟨j.val, h⟩ else 0
  | .cross =>
      if h : j.val < 6 then mom n ⟨j.val, h⟩
      else if j.val = 12 then 2 * (n 0 : ℚ)
      else if j.val = 13 then 2 * (n 1 : ℚ)
      else if j.val = 14 then 2 * (n 2 : ℚ)
      else if j.val = 15 then 1
      else 0
  | .wave => if h : 6 ≤ j.val ∧ j.val < 12 then mom n ⟨j.val - 6, by omega⟩ else 0

/-- Coefficients of the phase `n · f` in the 19 features. -/
def tForm (n : IntVec) (j : Fin 19) : ℚ :=
  if j.val = 16 then (n 0 : ℚ) else if j.val = 17 then (n 1 : ℚ)
  else if j.val = 18 then (n 2 : ℚ) else 0

/-- The squared length attached to a term kind. -/
def termQ (k : Kind) (n : IntVec) (p : Chart) : ℝ :=
  match k with
  | .cross => primalQ (intVec n) true p
  | .period => primalQ (intVec n) false p
  | .wave => dualQ n p

/-- The series contribution bounded by a term of this kind. Period and
wave indices are lexicographically positive and stand for `±n`. -/
def physical (k : Kind) (n : IntVec) (p : Chart) : ℝ :=
  match k with
  | .cross => seriesCrossTerm (chartPoint p) n
  | .period => 2 * seriesDirectTerm (chartPoint p) n
  | .wave => 2 * pairedTerm (chartPoint p) n

/-- A rational affine function `const + slope · q + phase · (n · f)`. -/
structure LinTerm where
  kind : Kind
  index : IntVec
  const : ℚ
  slope : ℚ
  phase : ℚ

def LinTerm.eval (t : LinTerm) (p : Chart) : ℝ :=
  (t.const : ℝ) + (t.slope : ℝ) * termQ t.kind t.index p + (t.phase : ℝ) * phaseT t.index p

/-- The term lies below its physical contribution at every valid point of the
box. Validity (determinant one and a non-integral offset) is all the Series
series bounds need; reduction and separation are not used. -/
def LinTerm.Valid (b : Cell) (t : LinTerm) : Prop :=
  t.slope ≤ 0 ∧ ∀ p, b.Mem p → (chartPoint p).Valid → t.eval p ≤ physical t.kind t.index p

def linSum (terms : List LinTerm) (p : Chart) : ℝ := (terms.map fun t => t.eval p).sum

/-- Aggregated constant and feature weights of a term list. -/
def aggConst (terms : List LinTerm) : ℚ := (terms.map LinTerm.const).sum

def aggWeight (terms : List LinTerm) (j : Fin 19) : ℚ :=
  (terms.map fun t => t.slope * qForm t.kind t.index j + t.phase * tForm t.index j).sum

/-- Evaluation of the aggregated form at a rational point. -/
def aggValueQ (K : ℚ) (w : Fin 19 → ℚ) (c : Fin 8 → ℚ) : ℚ :=
  K + ∑ j : Fin 19, w j * featGen c j

end BccSharp.Coulomb.CompactCover.JLeaf
