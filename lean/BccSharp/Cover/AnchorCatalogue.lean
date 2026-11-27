import BccSharp.Cover.LayeredDefectCutoff
import BccSharp.Cover.LayeredRoute

set_option autoImplicit false

/-! # The anchor's capped defect is one: a whole-box catalogue check

For a half class `f₀` and a chart point `p`, let `a = anchorOf (chartPoint p) f₀`.
If `D(a) < 1`, the anchor's optimal trial is registered (`anchor_registered`,
`BccSharp.Cover.LayeredDefectCutoff`): a basis `A` with `det A = 1`,
`lattice (A · bccPrimitive) = lattice R ∪ (R f₀ + lattice R)` and
`100 ‖A − O‖²_F < 1` for a proper rotation `O`. Put `b_i = A⁻¹ R e_i`, the BCC
vectors of the three lattice basis vectors, and `t_i = 2 b_i` (integer vectors
with a common parity). Then:

* for `m = e_i` and `m = e_i ± e_j`, `R m = A (Σ m_i b_i)` and
  `(81/100)|Σ m_i b_i|² ≤ |R m|² ≤ (121/100)|Σ m_i b_i|²`
  (`sq_mulVec_bounds`), so the integer `|Σ m_i t_i|²` lies in the band
  `[⌈(400/121) L_m⌉, ⌊(400/81) H_m⌋]`, where `L_m ≤ |R m|² ≤ H_m` on the box
  (`primalLo`, `primalHi`);
* `det [t₀ t₁ t₂] = 8`, since `A · [b₀ b₁ b₂] = R` and `det A = det R = 1`;
* the half class matches: `R f₀ ∈ lattice (A · bccPrimitive)`, so
  `Σ (f₀)_i b_i` is a BCC vector, that is `u = Σ (2f₀)_i t_i` is twice a vector of
  `2 · BCC`: `u ≡ (0,0,0)` or `(2,2,2)` mod 4 (`classB`).

* the frame bound: `‖A − O‖²_F = Σ_k |(A − O) ê_k|² ≥ Σ_k (|A ê_k| − 1)²` for
  the conventional axes `ê_k`, with `A ê_k = R (B⁻¹ ê_k)` and
  `B⁻¹ ê_k = adj(T) ê_k / 4` (`axisCoord`); on the box this sum is at least
  `frameLo` (`dist1Lo`), so `frameLo < 1/100`.

`catalogueOk b f2` checks four guards: `0 < lo₀`, `0 < lo₁` and `hi₀ hi₁ < 1`
on the box, and `f2 2 = −1`. They make `f₀ = f2/2` a half class and give the
anchor's coset separation (`anchor_sep`), two of the premises of
`anchor_registered`; validity and the period separation come from `good p`.
It then enumerates the integer candidates `t_i` of the three column bands
(`cands`, over a cube that the bands bound) and checks that no triple
satisfies the determinant, the class (`f₀ = f2/2`), the six pair bands and the
frame bound. Then `D(a) ≥ 1`, and with the cap `D(a) = 1`
(`catalogueOk_sound`). The test uses the determinant `8`, not `±8`. Requiring
`+8` loses nothing: `anchor_registered` gives `det A = 1`, and `det R = 1`, so
every registration has `det [t₀ t₁ t₂] = 8`. The frame bound stands in for a
cost bound on the remaining candidates. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.CompactCover.JLeaf (nrm nrm_nonneg nrm_sq nrm_add_le nrm_mulVec_lower
  nrm_mulVec_upper frobSq_nonneg BCCInt half_sq primalQ primalQ_eq img)
open BccSharp.Coulomb.CompactCover.JLeaf.Cutoff (primalLo primalLo_le rowALo rowAHi
  rowBLo rowBHi imgLo imgHi mulLo_le imgInterval_mem)

/-! ### Upper bounds of `|R v|²` on a box -/

/-- The greatest absolute value on `[lo, hi]`. -/
def greatAbs (lo hi : ℚ) : ℚ := max |lo| |hi|

theorem greatAbs_sq_ge (lo hi : ℚ) (t : ℝ) (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    t ^ 2 ≤ ((greatAbs lo hi : ℚ) : ℝ) ^ 2 := by
  unfold greatAbs
  push_cast
  have ht : |t| ≤ max |(lo : ℝ)| |(hi : ℝ)| := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
      exact (h2.trans (le_abs_self _)).trans (le_max_right _ _)
    · rw [abs_of_nonpos h]
      exact ((neg_le_neg h1).trans (neg_le_abs _)).trans (le_max_left _ _)
  calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    _ ≤ (max |(lo : ℝ)| |(hi : ℝ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht 2

/-- Whole-box upper bound of `primalQ v s` (for `0 < b.lo 0`, `0 < b.lo 1`). -/
def primalHi (v : Fin 3 → ℚ) (s : Bool) (b : Cell) : ℚ :=
  b.hi 0 ^ 2 * greatAbs (rowALo v s b) (rowAHi v s b) ^ 2 +
    b.hi 1 ^ 2 * greatAbs (rowBLo v s b) (rowBHi v s b) ^ 2 +
    greatAbs (imgLo v s b 2) (imgHi v s b 2) ^ 2 / (b.lo 0 ^ 2 * b.lo 1 ^ 2)

theorem primalHi_ge (v : Fin 3 → ℚ) (s : Bool) (b : Cell) (h0 : (0 : ℝ) < b.lo 0)
    (h1 : (0 : ℝ) < b.lo 1) (p : Chart) (hp : b.Mem p) :
    primalQ v s p ≤ ((primalHi v s b : ℚ) : ℝ) := by
  have i0 := imgInterval_mem v s b p hp 0
  have i1 := imgInterval_mem v s b p hp 1
  have i2 := imgInterval_mem v s b p hp 2
  have m2 := mulLo_le (b.lo 2) (b.hi 2) (imgLo v s b 1) (imgHi v s b 1) (p 2) (img v s p 1)
    (hp 2).1 (hp 2).2 i1.1 i1.2
  have m3 := mulLo_le (b.lo 3) (b.hi 3) (imgLo v s b 2) (imgHi v s b 2) (p 3) (img v s p 2)
    (hp 3).1 (hp 3).2 i2.1 i2.2
  have m4 := mulLo_le (b.lo 4) (b.hi 4) (imgLo v s b 2) (imgHi v s b 2) (p 4) (img v s p 2)
    (hp 4).1 (hp 4).2 i2.1 i2.2
  have rA : ((rowALo v s b : ℚ) : ℝ) ≤ JLeaf.rowA v s p ∧
      JLeaf.rowA v s p ≤ ((rowAHi v s b : ℚ) : ℝ) := by
    unfold rowALo rowAHi JLeaf.rowA
    push_cast
    constructor <;> linarith [i0.1, i0.2, m2.1, m2.2, m3.1, m3.2]
  have rB : ((rowBLo v s b : ℚ) : ℝ) ≤ JLeaf.rowB v s p ∧
      JLeaf.rowB v s p ≤ ((rowBHi v s b : ℚ) : ℝ) := by
    unfold rowBLo rowBHi JLeaf.rowB
    push_cast
    constructor <;> linarith [i1.1, i1.2, m4.1, m4.2]
  have sA := greatAbs_sq_ge (rowALo v s b) (rowAHi v s b) (JLeaf.rowA v s p) rA.1 rA.2
  have sB := greatAbs_sq_ge (rowBLo v s b) (rowBHi v s b) (JLeaf.rowB v s p) rB.1 rB.2
  have sC := greatAbs_sq_ge (imgLo v s b 2) (imgHi v s b 2) (JLeaf.rowC v s p) i2.1 i2.2
  have p0 : (b.lo 0 : ℝ) ≤ p 0 := (hp 0).1
  have p1 : (b.lo 1 : ℝ) ≤ p 1 := (hp 1).1
  have q0 : p 0 ≤ (b.hi 0 : ℝ) := (hp 0).2
  have q1 : p 1 ≤ (b.hi 1 : ℝ) := (hp 1).2
  have pp0 : 0 < p 0 := h0.trans_le p0
  have pp1 : 0 < p 1 := h1.trans_le p1
  have e0 : p 0 ^ 2 ≤ (b.hi 0 : ℝ) ^ 2 := pow_le_pow_left₀ pp0.le q0 2
  have e1 : p 1 ^ 2 ≤ (b.hi 1 : ℝ) ^ 2 := pow_le_pow_left₀ pp1.le q1 2
  have tA : p 0 ^ 2 * JLeaf.rowA v s p ^ 2 ≤
      (b.hi 0 : ℝ) ^ 2 * ((greatAbs (rowALo v s b) (rowAHi v s b) : ℚ) : ℝ) ^ 2 :=
    mul_le_mul e0 sA (sq_nonneg _) (sq_nonneg _)
  have tB : p 1 ^ 2 * JLeaf.rowB v s p ^ 2 ≤
      (b.hi 1 : ℝ) ^ 2 * ((greatAbs (rowBLo v s b) (rowBHi v s b) : ℚ) : ℝ) ^ 2 :=
    mul_le_mul e1 sB (sq_nonneg _) (sq_nonneg _)
  have den : (b.lo 0 : ℝ) ^ 2 * (b.lo 1 : ℝ) ^ 2 ≤ p 0 ^ 2 * p 1 ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ h0.le p0 2) (pow_le_pow_left₀ h1.le p1 2) (by positivity)
      (by positivity)
  have dpos : 0 < (b.lo 0 : ℝ) ^ 2 * (b.lo 1 : ℝ) ^ 2 := by positivity
  have tC : JLeaf.rowC v s p ^ 2 / (p 0 ^ 2 * p 1 ^ 2) ≤
      ((greatAbs (imgLo v s b 2) (imgHi v s b 2) : ℚ) : ℝ) ^ 2 /
        ((b.lo 0 : ℝ) ^ 2 * (b.lo 1 : ℝ) ^ 2) :=
    div_le_div₀ (sq_nonneg _) sC dpos den
  unfold primalHi primalQ
  push_cast
  linarith

/-! ### The norm bands of a necessary registration -/

/-- For `‖A − O‖²_F ≤ 1/100` with `O` orthogonal,
`(81/100)|w|² ≤ |A w|² ≤ (121/100)|w|²`. -/
theorem sq_mulVec_bounds (A O : Mat) (hO : O.transpose * O = 1) (hX : frobSq (A - O) ≤ 1 / 100)
    (w : Vec) :
    (81 / 100 : ℝ) * sq w ≤ sq (A.mulVec w) ∧ sq (A.mulVec w) ≤ (121 / 100 : ℝ) * sq w := by
  obtain ⟨x, hx⟩ : ∃ x, Real.sqrt (frobSq (A - O)) = x := ⟨_, rfl⟩
  have l := nrm_mulVec_lower A O hO w
  have u := nrm_mulVec_upper A O hO w
  rw [hx] at l u
  have hx0 : 0 ≤ x := by rw [← hx]; exact Real.sqrt_nonneg _
  have hxb : x ≤ 1 / 10 := by
    rw [← hx, Real.sqrt_le_left (by norm_num)]
    linarith
  have n0 := nrm_nonneg w
  have a0 := nrm_nonneg (A.mulVec w)
  rw [← nrm_sq w, ← nrm_sq (A.mulVec w)]
  constructor
  · have m : (9 / 10 : ℝ) * nrm w ≤ (1 - x) * nrm w :=
      mul_le_mul_of_nonneg_right (by linarith) n0
    have c := mul_self_le_mul_self (by positivity) (m.trans l)
    nlinarith [c]
  · have m : (1 + x) * nrm w ≤ (11 / 10 : ℝ) * nrm w :=
      mul_le_mul_of_nonneg_right (by linarith) n0
    have c := mul_self_le_mul_self a0 (u.trans m)
    nlinarith [c]

/-- The integer band `[⌈(400/121) L⌉, ⌊(400/81) H⌋]` of `|t|² = 4|b|²` for the
lattice vector `m`: `L` and `H` bound `|R m|²` on the box. -/
def bandLo (m : IntVec) (b : Cell) : ℤ := ⌈(400 / 121 : ℚ) * primalLo (fun i => (m i : ℚ)) false b⌉

def bandHi (m : IntVec) (b : Cell) : ℤ := ⌊(400 / 81 : ℚ) * primalHi (fun i => (m i : ℚ)) false b⌋

theorem sq_chart_intVec (m : IntVec) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    sq ((chartBasis p).mulVec (castVec m)) = primalQ (fun i => (m i : ℚ)) false p := by
  rw [primalQ_eq _ false p h0 h1]
  congr 2
  funext i
  simp [img, castVec]

/-- **The band.** If `(81/400) k ≤ |R m|² ≤ (121/400) k` at a point of the box,
then `bandLo m b ≤ k ≤ bandHi m b`. -/
theorem band_mem (m : IntVec) (b : Cell) (h0 : (0 : ℝ) < b.lo 0) (h1 : (0 : ℝ) < b.lo 1)
    (p : Chart) (hp : b.Mem p) (k : ℤ)
    (hlo : (81 / 400 : ℝ) * k ≤ sq ((chartBasis p).mulVec (castVec m)))
    (hhi : sq ((chartBasis p).mulVec (castVec m)) ≤ (121 / 400 : ℝ) * k) :
    bandLo m b ≤ k ∧ k ≤ bandHi m b := by
  have pp0 : 0 < p 0 := h0.trans_le (hp 0).1
  have pp1 : 0 < p 1 := h1.trans_le (hp 1).1
  rw [sq_chart_intVec m p pp0.ne' pp1.ne'] at hlo hhi
  have lo := primalLo_le (fun i => (m i : ℚ)) false b h0 h1 p hp
  have hi := primalHi_ge (fun i => (m i : ℚ)) false b h0 h1 p hp
  constructor
  · unfold bandLo
    rw [Int.ceil_le]
    have h : (((400 / 121 : ℚ) * primalLo (fun i => (m i : ℚ)) false b : ℚ) : ℝ) ≤
        ((k : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  · unfold bandHi
    rw [Int.le_floor]
    have h : ((k : ℚ) : ℝ) ≤
        (((400 / 81 : ℚ) * primalHi (fun i => (m i : ℚ)) false b : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h

/-! ### Integer candidates -/

/-- `|t|²` for an integer vector. -/
def normSqZ (t : IntVec) : ℤ := t 0 * t 0 + t 1 * t 1 + t 2 * t 2

/-- `t ∈ 2 · BCC`: the three coordinates have a common parity. -/
def bccB (t : IntVec) : Bool := decide ((t 0 - t 1) % 2 = 0) && decide ((t 1 - t 2) % 2 = 0)

def rangeZ (K : ℕ) : List ℤ := (List.range (2 * K + 1)).map (fun i : ℕ => (i : ℤ) - K)

/-- The integer vectors with coordinates in `[−K, K]`. -/
def cube (K : ℕ) : List IntVec :=
  (rangeZ K).flatMap fun a => (rangeZ K).flatMap fun c => (rangeZ K).map fun d => ![a, c, d]

/-- The vectors of `2 · BCC` with `lo ≤ |t|² ≤ hi`. -/
def cands (lo hi : ℤ) : List IntVec :=
  (cube (Nat.sqrt hi.toNat)).filter fun t =>
    bccB t && decide (lo ≤ normSqZ t) && decide (normSqZ t ≤ hi)

/-- The determinant of the matrix with columns `t₀`, `t₁`, `t₂`. -/
def det3Z (t0 t1 t2 : IntVec) : ℤ :=
  t0 0 * (t1 1 * t2 2 - t1 2 * t2 1) - t0 1 * (t1 0 * t2 2 - t1 2 * t2 0) +
    t0 2 * (t1 0 * t2 1 - t1 1 * t2 0)

/-- The half class `f2/2`: `u = Σ (f2)_i t_i ≡ (0,0,0)` or `(2,2,2)` mod 4. -/
def classB (f2 t0 t1 t2 : IntVec) : Bool :=
  let u0 := f2 0 * t0 0 + f2 1 * t1 0 + f2 2 * t2 0
  let u1 := f2 0 * t0 1 + f2 1 * t1 1 + f2 2 * t2 1
  let u2 := f2 0 * t0 2 + f2 1 * t1 2 + f2 2 * t2 2
  (decide (u0 % 4 = 0) && decide (u1 % 4 = 0) && decide (u2 % 4 = 0)) ||
    (decide (u0 % 4 = 2) && decide (u1 % 4 = 2) && decide (u2 % 4 = 2))

/-- The band test for the lattice vector `m` with candidate image `t`. -/
def bandB (m : IntVec) (b : Cell) (t : IntVec) : Bool :=
  decide (bandLo m b ≤ normSqZ t) && decide (normSqZ t ≤ bandHi m b)

/-- The six pair bands `e_i ± e_j`. -/
def pairsB (b : Cell) (t0 t1 t2 : IntVec) : Bool :=
  bandB ![1, 1, 0] b (t0 + t1) && bandB ![1, -1, 0] b (t0 - t1) &&
    bandB ![1, 0, 1] b (t0 + t2) && bandB ![1, 0, -1] b (t0 - t2) &&
    bandB ![0, 1, 1] b (t1 + t2) && bandB ![0, 1, -1] b (t1 - t2)

/-- The integer cross product. -/
def crossZ (u v : IntVec) : IntVec :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The lattice coordinates `B⁻¹ ê_k = adj(T) ê_k / 4` of the conventional axis
`ê_k` for the basis `B = T/2` with columns `t_i / 2` (when `det T = 8`). -/
def axisCoord (t0 t1 t2 : IntVec) (k : Fin 3) : Fin 3 → ℚ :=
  ![(crossZ t1 t2 k : ℚ) / 4, (crossZ t2 t0 k : ℚ) / 4, (crossZ t0 t1 k : ℚ) / 4]

/-- A lower bound of `(√x − 1)²` for `x ∈ [lo, hi]`, `x ≥ 0`. -/
def dist1Lo (lo hi : ℚ) : ℚ :=
  if hi < 1 then ((1 - hi) / 2) ^ 2 else if 1 < lo then (2 * (lo - 1) / (lo + 3)) ^ 2 else 0

/-- A lower bound on the box of `Σ_k (|A ê_k| − 1)² ≤ ‖A − O‖²_F` for the
registration `A = R B⁻¹` of the candidate columns. -/
def frameLo (b : Cell) (t0 t1 t2 : IntVec) : ℚ :=
  dist1Lo (primalLo (axisCoord t0 t1 t2 0) false b) (primalHi (axisCoord t0 t1 t2 0) false b) +
    dist1Lo (primalLo (axisCoord t0 t1 t2 1) false b) (primalHi (axisCoord t0 t1 t2 1) false b) +
    dist1Lo (primalLo (axisCoord t0 t1 t2 2) false b) (primalHi (axisCoord t0 t1 t2 2) false b)

/-- **The catalogue check** on a box for the half class `f₀ = f2/2`: the guards
`0 < lo₀`, `0 < lo₁`, `hi₀ hi₁ < 1` and `f2 2 = −1` hold, and no candidate
triple has determinant `8`, the class `f₀`, the six pair bands and frame bound
below `1/100`. -/
def catalogueOk (b : Cell) (f2 : IntVec) : Bool :=
  (decide (0 < b.lo 0) && decide (0 < b.lo 1) && decide (b.hi 0 * b.hi 1 < 1) &&
    decide (f2 2 = -1)) &&
  (cands (bandLo ![1, 0, 0] b) (bandHi ![1, 0, 0] b)).all fun t0 =>
    (cands (bandLo ![0, 1, 0] b) (bandHi ![0, 1, 0] b)).all fun t1 =>
      (cands (bandLo ![0, 0, 1] b) (bandHi ![0, 0, 1] b)).all fun t2 =>
        !(decide (det3Z t0 t1 t2 = 8) && classB f2 t0 t1 t2 && pairsB b t0 t1 t2 &&
          decide (frameLo b t0 t1 t2 < 1 / 100))

/-! ### Membership of the candidates -/

theorem mem_rangeZ {K : ℕ} {a : ℤ} (h1 : -(K : ℤ) ≤ a) (h2 : a ≤ K) : a ∈ rangeZ K := by
  unfold rangeZ
  rw [List.mem_map]
  refine ⟨(a + K).toNat, ?_, ?_⟩
  · rw [List.mem_range]
    omega
  · omega

theorem mem_cube {K : ℕ} (t : IntVec) (h : ∀ k, -(K : ℤ) ≤ t k ∧ t k ≤ K) : t ∈ cube K := by
  unfold cube
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨t 0, mem_rangeZ (h 0).1 (h 0).2, t 1, mem_rangeZ (h 1).1 (h 1).2, t 2,
    mem_rangeZ (h 2).1 (h 2).2, ?_⟩
  funext i
  fin_cases i <;> rfl

theorem coord_bound (t : IntVec) (hi : ℤ) (h : normSqZ t ≤ hi) (k : Fin 3) :
    -(Nat.sqrt hi.toNat : ℤ) ≤ t k ∧ t k ≤ Nat.sqrt hi.toNat := by
  have hk : t k * t k ≤ normSqZ t := by
    unfold normSqZ
    fin_cases k <;> simp <;>
      nlinarith [mul_self_nonneg (t 0), mul_self_nonneg (t 1), mul_self_nonneg (t 2)]
  have hn : (t k).natAbs * (t k).natAbs ≤ hi.toNat := by
    have : (((t k).natAbs * (t k).natAbs : ℕ) : ℤ) ≤ (hi.toNat : ℤ) := by
      push_cast
      rw [abs_mul_abs_self]
      exact hk.trans (h.trans (Int.self_le_toNat hi))
    exact_mod_cast this
  have hs : (t k).natAbs ≤ Nat.sqrt hi.toNat := Nat.le_sqrt.mpr hn
  have h3 : ((t k).natAbs : ℤ) ≤ (Nat.sqrt hi.toNat : ℤ) := by exact_mod_cast hs
  rw [← Int.abs_eq_natAbs] at h3
  exact abs_le.mp h3

theorem mem_cands (t : IntVec) (lo hi : ℤ) (hb : BCCInt t) (h1 : lo ≤ normSqZ t)
    (h2 : normSqZ t ≤ hi) : t ∈ cands lo hi := by
  unfold cands
  rw [List.mem_filter]
  refine ⟨mem_cube t (coord_bound t hi h2), ?_⟩
  have hbB : bccB t = true := by
    unfold bccB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hb
  simp [hbB, h1, h2]

/-! ### The frame bound -/

theorem dist1Lo_le (lo hi : ℚ) (x : ℝ) (hx0 : 0 ≤ x) (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    ((dist1Lo lo hi : ℚ) : ℝ) ≤ (Real.sqrt x - 1) ^ 2 := by
  obtain ⟨s, hs⟩ : ∃ s, Real.sqrt x = s := ⟨_, rfl⟩
  have s0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg x
  have sx : s ^ 2 = x := hs ▸ Real.sq_sqrt hx0
  rw [hs]
  unfold dist1Lo
  split_ifs with hhi hlo
  · have hhi' : (hi : ℝ) < 1 := by exact_mod_cast hhi
    push_cast
    have a1 : (1 - (hi : ℝ)) / 2 ≤ 1 - s := by nlinarith [sq_nonneg (1 - s)]
    have a0 : 0 ≤ (1 - (hi : ℝ)) / 2 := by linarith
    have m := mul_self_le_mul_self a0 a1
    nlinarith [m]
  · have hlo' : 1 < (lo : ℝ) := by exact_mod_cast hlo
    push_cast
    have s1 : 1 ≤ s := by nlinarith
    have l3 : 0 < (lo : ℝ) + 3 := by linarith
    have key : 2 * ((lo : ℝ) - 1) / ((lo : ℝ) + 3) ≤ s - 1 := by
      rw [div_le_iff₀ l3]
      have d0 : 0 ≤ s ^ 2 - (lo : ℝ) := by linarith
      rcases le_total s 3 with h | h
      · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr s1) (sub_nonneg.mpr s1)) (sub_nonneg.mpr s1),
          mul_nonneg d0 (sub_nonneg.mpr h)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hlo'.le) (sub_nonneg.mpr h)]
    have k0 : 0 ≤ 2 * ((lo : ℝ) - 1) / ((lo : ℝ) + 3) := div_nonneg (by linarith) l3.le
    have m := mul_self_le_mul_self k0 key
    nlinarith [m]
  · push_cast
    positivity

theorem frobSq_cols (M : Mat) :
    frobSq M = sq (M.mulVec (fun k => if k = 0 then (1 : ℝ) else 0)) +
      sq (M.mulVec (fun k => if k = 1 then (1 : ℝ) else 0)) +
      sq (M.mulVec (fun k => if k = 2 then (1 : ℝ) else 0)) := by
  unfold frobSq sq
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-! ### The soundness theorem -/

theorem sq_half_intVec (u : IntVec) :
    sq (fun i => ((u i : ℤ) : ℝ) / 2) = ((normSqZ u : ℤ) : ℝ) / 4 := by
  rw [half_sq]
  unfold normSqZ
  push_cast
  ring

/-- **The anchor's capped defect is one.** If `catalogueOk b f2`, then at every
good point of the box the anchor of the half class `f₀ = f2/2` has capped defect
`1`. -/
theorem catalogueOk_sound (b : Cell) (f2 : IntVec) (ok : catalogueOk b f2 = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) :
    defect (anchorOf (chartPoint p) (fun i => (f2 i : ℝ) / 2)) = 1 := by
  simp only [catalogueOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨hb0, hb1⟩, hbs⟩, hf2⟩, hall⟩ := ok
  have h0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast hb0
  have h1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast hb1
  have hr : 0 < p 0 := h0.trans_le (hp 0).1
  have hs : 0 < p 1 := h1.trans_le (hp 1).1
  have hrs : p 0 * p 1 < 1 := by
    have hbs' : (b.hi 0 : ℝ) * b.hi 1 < 1 := by exact_mod_cast hbs
    have m : p 0 * p 1 ≤ (b.hi 0 : ℝ) * b.hi 1 :=
      mul_le_mul (hp 0).2 (hp 1).2 hs.le (hr.le.trans (hp 0).2)
    linarith
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Vec, f₀ = fun i => (f2 i : ℝ) / 2 := ⟨_, rfl⟩
  rw [← hf₀]
  have f02 : f₀ 2 = -1 / 2 := by
    rw [hf₀]
    simp only [hf2]
    norm_num
  have half : HalfClass f₀ := by
    refine ⟨⟨f2, ?_⟩, ?_⟩
    · funext i
      rw [hf₀]
      simp only [castVec, Pi.smul_apply, smul_eq_mul]
      ring
    · intro n hn
      have h2 := congrFun hn 2
      rw [f02] at h2
      simp only [castVec] at h2
      have : (2 * n 2 : ℤ) = -1 := by
        have : (2 : ℝ) * (n 2 : ℝ) = -1 := by linarith
        exact_mod_cast this
      omega
  set q := chartPoint p with hqdef
  set R := q.basis with hR
  have hRc : R = chartBasis p := rfl
  have asep : ∀ m : IntVec, (1 / 2 : ℝ) ^ 2 < sq (q.basis.mulVec (castVec m + f₀)) :=
    fun m => anchor_sep hr hs hrs f₀ f02 m
  have hsep₁ := gp.2.2.1
  have hvalid : q.Valid := gp.1
  apply le_antisymm (defect_range _).2
  by_contra hlt
  push Not at hlt
  obtain ⟨A, O, ε, hO, hdetA, hlat, hXD, -, -, -, -⟩ :=
    anchor_registered q hvalid hsep₁ f₀ half asep hlt
  have hX : frobSq (A - O) ≤ 1 / 100 := by linarith
  have bnd := sq_mulVec_bounds A O hO.1 hX
  -- the three columns
  have col : ∀ m : IntVec, ∃ z : IntVec,
      A.mulVec (bccPrimitive.mulVec (castVec z)) = R.mulVec (castVec m) := by
    intro m
    have hm : R.mulVec (castVec m) ∈ lattice (A * bccPrimitive) := by
      rw [hlat]
      exact Or.inl ⟨m, rfl⟩
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, by rw [← hz, Matrix.mulVec_mulVec]⟩
  obtain ⟨z0, hz0⟩ := col ![1, 0, 0]
  obtain ⟨z1, hz1⟩ := col ![0, 1, 0]
  obtain ⟨z2, hz2⟩ := col ![0, 0, 1]
  obtain ⟨t0, ht0⟩ : ∃ t, t = bccTwice z0 := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ : ∃ t, t = bccTwice z1 := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ t, t = bccTwice z2 := ⟨_, rfl⟩
  have hb0' : bccPrimitive.mulVec (castVec z0) = fun k => ((t0 k : ℤ) : ℝ) / 2 := by
    rw [ht0]; exact bccPrimitive_mulVec z0
  have hb1' : bccPrimitive.mulVec (castVec z1) = fun k => ((t1 k : ℤ) : ℝ) / 2 := by
    rw [ht1]; exact bccPrimitive_mulVec z1
  have hb2' : bccPrimitive.mulVec (castVec z2) = fun k => ((t2 k : ℤ) : ℝ) / 2 := by
    rw [ht2]; exact bccPrimitive_mulVec z2
  rw [hb0'] at hz0
  rw [hb1'] at hz1
  rw [hb2'] at hz2
  -- every real combination of the basis vectors
  have comb : ∀ a0 a1 a2 : ℝ, R.mulVec (fun k => a0 * ((![1, 0, 0] : IntVec) k : ℝ) +
      a1 * ((![0, 1, 0] : IntVec) k : ℝ) + a2 * ((![0, 0, 1] : IntVec) k : ℝ)) =
      A.mulVec (fun k => a0 * (((t0 k : ℤ) : ℝ) / 2) + a1 * (((t1 k : ℤ) : ℝ) / 2) +
        a2 * (((t2 k : ℤ) : ℝ) / 2)) := by
    intro a0 a1 a2
    have e1 : (fun k => a0 * ((![1, 0, 0] : IntVec) k : ℝ) + a1 * ((![0, 1, 0] : IntVec) k : ℝ) +
        a2 * ((![0, 0, 1] : IntVec) k : ℝ)) =
        a0 • castVec ![1, 0, 0] + a1 • castVec ![0, 1, 0] + a2 • castVec ![0, 0, 1] := by
      funext k
      simp [castVec]
    have e2 : (fun k => a0 * (((t0 k : ℤ) : ℝ) / 2) + a1 * (((t1 k : ℤ) : ℝ) / 2) +
        a2 * (((t2 k : ℤ) : ℝ) / 2)) =
        a0 • (fun k => ((t0 k : ℤ) : ℝ) / 2) + a1 • (fun k => ((t1 k : ℤ) : ℝ) / 2) +
          a2 • (fun k => ((t2 k : ℤ) : ℝ) / 2) := by
      funext k
      simp
    rw [e1, e2]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hz0, hz1, hz2]
  have castComb : ∀ m : IntVec, castVec m = fun k => (m 0 : ℝ) * ((![1, 0, 0] : IntVec) k : ℝ) +
      (m 1 : ℝ) * ((![0, 1, 0] : IntVec) k : ℝ) + (m 2 : ℝ) * ((![0, 0, 1] : IntVec) k : ℝ) := by
    intro m
    funext k
    fin_cases k <;> simp [castVec]
  -- the band of an integer combination
  have bandOf : ∀ (m u : IntVec), u = (fun k => m 0 * t0 k + m 1 * t1 k + m 2 * t2 k) →
      bandLo m b ≤ normSqZ u ∧ normSqZ u ≤ bandHi m b := by
    intro m u hu
    have e := comb (m 0 : ℝ) (m 1 : ℝ) (m 2 : ℝ)
    rw [← castComb m] at e
    have hw : (fun k => (m 0 : ℝ) * (((t0 k : ℤ) : ℝ) / 2) + (m 1 : ℝ) * (((t1 k : ℤ) : ℝ) / 2) +
        (m 2 : ℝ) * (((t2 k : ℤ) : ℝ) / 2)) = fun k => ((u k : ℤ) : ℝ) / 2 := by
      rw [hu]
      funext k
      push_cast
      ring
    rw [hw] at e
    have sqw := sq_half_intVec u
    obtain ⟨blo, bhi⟩ := bnd (fun k => ((u k : ℤ) : ℝ) / 2)
    rw [← e, sqw] at blo bhi
    exact band_mem m b h0 h1 p hp _ (by rw [← hRc]; linarith) (by rw [← hRc]; linarith)
  -- the candidates
  have band0 := bandOf ![1, 0, 0] t0 (by funext k; simp)
  have band1 := bandOf ![0, 1, 0] t1 (by funext k; simp)
  have band2 := bandOf ![0, 0, 1] t2 (by funext k; simp)
  have mem0 := mem_cands t0 _ _ (by rw [ht0]; exact bccTwice_bcc z0) band0.1 band0.2
  have mem1 := mem_cands t1 _ _ (by rw [ht1]; exact bccTwice_bcc z1) band1.1 band1.2
  have mem2 := mem_cands t2 _ _ (by rw [ht2]; exact bccTwice_bcc z2) band2.1 band2.2
  have key := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hall t0 mem0) t1 mem1)
    t2 mem2
  -- the pair bands
  have pairs : pairsB b t0 t1 t2 = true := by
    have pb : ∀ (m : IntVec) (u : IntVec),
        u = (fun k => m 0 * t0 k + m 1 * t1 k + m 2 * t2 k) → bandB m b u = true := by
      intro m u hu
      have h := bandOf m u hu
      unfold bandB
      simp [h.1, h.2]
    unfold pairsB
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨pb _ _ ?_, pb _ _ ?_⟩, pb _ _ ?_⟩, pb _ _ ?_⟩, pb _ _ ?_⟩, pb _ _ ?_⟩ <;>
      (funext k; simp; try ring)
  -- the determinant
  have det8 : det3Z t0 t1 t2 = 8 := by
    let Bm : Mat := Matrix.of fun r c =>
      ((![fun k => ((t0 k : ℤ) : ℝ) / 2, fun k => ((t1 k : ℤ) : ℝ) / 2,
        fun k => ((t2 k : ℤ) : ℝ) / 2] : Fin 3 → Vec) c) r
    have hAB : A * Bm = R := by
      ext r c
      rw [Matrix.mul_apply]
      have hcol : ∀ c : Fin 3, A.mulVec (fun k => Bm k c) = R.mulVec (castVec
          ((![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] : Fin 3 → IntVec) c)) := by
        intro c
        fin_cases c
        · exact hz0
        · exact hz1
        · exact hz2
      have h1c := congrFun (hcol c) r
      have lhs : (A.mulVec (fun k => Bm k c)) r = ∑ k, A r k * Bm k c := rfl
      have rhs : (R.mulVec (castVec ((![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] : Fin 3 → IntVec) c))) r =
          R r c := by
        fin_cases c <;> simp [Matrix.mulVec, dotProduct, castVec, Fin.sum_univ_three]
      rw [← lhs, h1c, rhs]
    have hdetR : R.det = 1 := hvalid.1
    have hdetB : Bm.det = 1 := by
      have h := congrArg Matrix.det hAB
      rw [Matrix.det_mul, hdetA, one_mul, hdetR] at h
      exact h
    have formula : Bm.det = ((det3Z t0 t1 t2 : ℤ) : ℝ) / 8 := by
      rw [Matrix.det_fin_three]
      simp only [Bm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      unfold det3Z
      push_cast
      ring
    rw [formula] at hdetB
    have h8 : ((det3Z t0 t1 t2 : ℤ) : ℝ) = 8 := by linarith
    exact_mod_cast h8
  -- the half class
  have cls : classB f2 t0 t1 t2 = true := by
    have hm : R.mulVec f₀ ∈ lattice (A * bccPrimitive) := by
      rw [hlat]
      exact Or.inr ⟨0, lattice_zero R, by rw [zero_add]⟩
    obtain ⟨z, hz⟩ := hm
    have hz' : A.mulVec (bccPrimitive.mulVec (castVec z)) = R.mulVec f₀ := by
      rw [← hz, Matrix.mulVec_mulVec]
    have ef : f₀ = fun k => ((f2 0 : ℤ) : ℝ) / 2 * ((![1, 0, 0] : IntVec) k : ℝ) +
        ((f2 1 : ℤ) : ℝ) / 2 * ((![0, 1, 0] : IntVec) k : ℝ) +
        ((f2 2 : ℤ) : ℝ) / 2 * ((![0, 0, 1] : IntVec) k : ℝ) := by
      rw [hf₀]
      funext k
      fin_cases k <;> simp
    have e := comb (((f2 0 : ℤ) : ℝ) / 2) (((f2 1 : ℤ) : ℝ) / 2) (((f2 2 : ℤ) : ℝ) / 2)
    rw [← ef] at e
    rw [e] at hz'
    have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (by rw [hdetA]; exact isUnit_one)
    have inj : ∀ u v : Vec, A.mulVec u = A.mulVec v → u = v := by
      intro u v huv
      have := congrArg (fun w => A⁻¹.mulVec w) huv
      simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this
      exact this
    have hw := inj _ _ hz'
    rw [bccPrimitive_mulVec] at hw
    obtain ⟨w, hwdef⟩ : ∃ w, w = bccTwice z := ⟨_, rfl⟩
    rw [← hwdef] at hw
    have hwb : BCCInt w := by rw [hwdef]; exact bccTwice_bcc z
    have hu : ∀ k : Fin 3, f2 0 * t0 k + f2 1 * t1 k + f2 2 * t2 k = 2 * w k := by
      intro k
      have hk := congrFun hw k
      have : ((f2 0 * t0 k + f2 1 * t1 k + f2 2 * t2 k : ℤ) : ℝ) = ((2 * w k : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    unfold classB
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [hu 0, hu 1, hu 2]
    unfold BCCInt at hwb
    omega
  -- the frame bound: `Σ_k (|A ê_k| − 1)² ≤ ‖A − O‖²_F < 1/100`
  have frame : frameLo b t0 t1 t2 < 1 / 100 := by
    have hXlt : frobSq (A - O) < 1 / 100 := by linarith
    have det8r : ((det3Z t0 t1 t2 : ℤ) : ℝ) = 8 := by exact_mod_cast det8
    unfold det3Z at det8r
    push_cast at det8r
    have axis : ∀ k : Fin 3, A.mulVec (fun k' => if k' = k then (1 : ℝ) else 0) =
        R.mulVec (fun i => ((axisCoord t0 t1 t2 k i : ℚ) : ℝ)) := by
      intro k
      have e := comb ((axisCoord t0 t1 t2 k 0 : ℚ) : ℝ) ((axisCoord t0 t1 t2 k 1 : ℚ) : ℝ)
        ((axisCoord t0 t1 t2 k 2 : ℚ) : ℝ)
      have lhs : (fun k' => ((axisCoord t0 t1 t2 k 0 : ℚ) : ℝ) * ((![1, 0, 0] : IntVec) k' : ℝ) +
          ((axisCoord t0 t1 t2 k 1 : ℚ) : ℝ) * ((![0, 1, 0] : IntVec) k' : ℝ) +
          ((axisCoord t0 t1 t2 k 2 : ℚ) : ℝ) * ((![0, 0, 1] : IntVec) k' : ℝ)) =
          fun i => ((axisCoord t0 t1 t2 k i : ℚ) : ℝ) := by
        funext k'
        fin_cases k' <;> simp
      have rhs : (fun k' => ((axisCoord t0 t1 t2 k 0 : ℚ) : ℝ) * (((t0 k' : ℤ) : ℝ) / 2) +
          ((axisCoord t0 t1 t2 k 1 : ℚ) : ℝ) * (((t1 k' : ℤ) : ℝ) / 2) +
          ((axisCoord t0 t1 t2 k 2 : ℚ) : ℝ) * (((t2 k' : ℤ) : ℝ) / 2)) =
          fun k' => if k' = k then (1 : ℝ) else 0 := by
        funext k'
        fin_cases k <;> fin_cases k' <;> simp [axisCoord, crossZ] <;>
          first | ring1 | linear_combination (1 / 8 : ℝ) * det8r
      rw [lhs, rhs] at e
      exact e.symm
    have perAxis : ∀ k : Fin 3,
        ((dist1Lo (primalLo (axisCoord t0 t1 t2 k) false b)
          (primalHi (axisCoord t0 t1 t2 k) false b) : ℚ) : ℝ) ≤
          sq ((A - O).mulVec (fun k' => if k' = k then (1 : ℝ) else 0)) := by
      intro k
      obtain ⟨ek, hek⟩ : ∃ ek : Vec, ek = fun k' => if k' = k then (1 : ℝ) else 0 := ⟨_, rfl⟩
      rw [← hek]
      have ax := axis k
      rw [← hek] at ax
      have hsq : sq (A.mulVec ek) = primalQ (axisCoord t0 t1 t2 k) false p := by
        rw [ax, primalQ_eq _ false p hr.ne' hs.ne']
        congr 2
        funext i
        simp [img]
      have lo := primalLo_le (axisCoord t0 t1 t2 k) false b h0 h1 p hp
      have hi := primalHi_ge (axisCoord t0 t1 t2 k) false b h0 h1 p hp
      have d := dist1Lo_le _ _ (sq (A.mulVec ek)) (sq_nonnegative _) (by rw [hsq]; exact lo)
        (by rw [hsq]; exact hi)
      have hsqe : sq ek = 1 := by
        rw [hek]
        fin_cases k <;> simp [sq]
      have hOe : nrm (O.mulVec ek) = 1 := by
        unfold nrm
        rw [JLeaf.sq_orth O hO.1 ek, hsqe, Real.sqrt_one]
      have t1' := nrm_add_le (A.mulVec ek - O.mulVec ek) (O.mulVec ek)
      have t2' := nrm_add_le (O.mulVec ek - A.mulVec ek) (A.mulVec ek)
      rw [sub_add_cancel] at t1' t2'
      have hneg : nrm (O.mulVec ek - A.mulVec ek) = nrm (A.mulVec ek - O.mulVec ek) := by
        rw [← neg_sub, JLeaf.nrm_neg]
      rw [hneg] at t2'
      have hsub : (A - O).mulVec ek = A.mulVec ek - O.mulVec ek := Matrix.sub_mulVec A O ek
      have hab : |nrm (A.mulVec ek) - 1| ≤ nrm ((A - O).mulVec ek) := by
        rw [hsub, abs_le]
        constructor <;> linarith
      have sqr : (nrm (A.mulVec ek) - 1) ^ 2 ≤ sq ((A - O).mulVec ek) := by
        rw [← nrm_sq ((A - O).mulVec ek)]
        calc (nrm (A.mulVec ek) - 1) ^ 2 = |nrm (A.mulVec ek) - 1| ^ 2 := (sq_abs _).symm
          _ ≤ nrm ((A - O).mulVec ek) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
      have hn : nrm (A.mulVec ek) = Real.sqrt (sq (A.mulVec ek)) := rfl
      rw [hn] at sqr
      linarith
    have cols := frobSq_cols (A - O)
    have e0 := perAxis 0
    have e1 := perAxis 1
    have e2 := perAxis 2
    have hreal : ((frameLo b t0 t1 t2 : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by
      unfold frameLo
      push_cast
      linarith
    exact Rat.cast_lt.mp hreal
  have hd8 : decide (det3Z t0 t1 t2 = 8) = true := decide_eq_true det8
  have hfr : decide (frameLo b t0 t1 t2 < 1 / 100) = true := decide_eq_true frame
  simp only [hd8, cls, pairs, hfr] at key
  exact absurd key (by decide)

/-- With `D(a) = 1` the relative defect bound holds trivially:
`D(p) ≤ D(a) + 200 |h|²` for every displacement. -/
theorem catalogue_transport (b : Cell) (f2 : IntVec) (ok : catalogueOk b f2 = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) (h : Vec) :
    defect (chartPoint p) ≤ defect (anchorOf (chartPoint p) (fun i => (f2 i : ℝ) / 2)) +
      200 * sq h := by
  rw [catalogueOk_sound b f2 ok p hp gp]
  have := (defect_range (chartPoint p)).2
  have := sq_nonnegative h
  linarith

end BccSharp.Coulomb.CompactCover.Layered
