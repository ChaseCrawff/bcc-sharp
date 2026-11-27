import BccSharp.Cover.Stage2Geometry

set_option autoImplicit false

/-! The joint corner maximum of a weighted sum of squared distances, in exact integers.

For a list of weighted modes (`WTerm`: a Stage2 `Mode` and an integer weight `w ≥ 0` at
scale `S = 2^96`) and an optional reduction cut `λ c(p)`, `cornerMax` (on the box `toIBox b`, with the moments `momOf ts` and the cut) returns an
integer `U` with

  `Σ_t (w_t / S) · radial_t(p) + λ c(p) ≤ U / S` for every `p` in the box `b`

(its soundness is proved in this module). The weighted sum is chord-convex along every chart axis, so its
maximum on the box is attained at one of the 256 corners (`corner_le`). At a corner it is
`Σ_j P_j · shift_j + Σ_j D_j · R_j / S` with the six primal and six dual metric entries
`P`, `D` of the shape corner and the integer moments of the list (`Mom`). The box
endpoints must be dyadic with denominator dividing `2^64`; the corner values are then
exact integers over the common denominator `r₁² r₂² 2^(512+128+96)` of a shape corner,
and the only rounding is one ceiling division per shape corner.

The cuts are the two necessary reduction inequalities used by the Adaptive `R` and `K`
routes: `c₁ = r₂² - (3/4) r₁²` and `c₂ = r₂² + r₁² x² - r₁²`. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BccSharp.Coverage DirectRoute Stage2

/-! ### Integer moments -/

structure Mom where
  d0 : ℤ
  d1 : ℤ
  d2 : ℤ
  d3 : ℤ
  d4 : ℤ
  d5 : ℤ
  r0 : ℤ
  r1 : ℤ
  r2 : ℤ
  r3 : ℤ
  r4 : ℤ
  r5 : ℤ
  l0 : ℤ
  l1 : ℤ
  l2 : ℤ
  m : ℤ

def Mom.zero : Mom := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A weighted mode: family, index `(a, b, c)`, weight `w` at scale `S`. -/
structure WTerm where
  fam : Family
  a : ℤ
  b : ℤ
  c : ℤ
  w : ℤ

def WTerm.mode (t : WTerm) : Mode := ⟨t.fam, ![t.a, t.b, t.c]⟩

def Mom.add (M : Mom) (t : WTerm) : Mom :=
  match t.fam with
  | .cross =>
    ⟨M.d0 + t.w * (t.a * t.a), M.d1 + t.w * (t.b * t.b), M.d2 + t.w * (t.c * t.c),
      M.d3 + t.w * (t.a * t.b), M.d4 + t.w * (t.a * t.c), M.d5 + t.w * (t.b * t.c),
      M.r0, M.r1, M.r2, M.r3, M.r4, M.r5,
      M.l0 + t.w * t.a, M.l1 + t.w * t.b, M.l2 + t.w * t.c, M.m + t.w⟩
  | .period =>
    ⟨M.d0 + t.w * (t.a * t.a), M.d1 + t.w * (t.b * t.b), M.d2 + t.w * (t.c * t.c),
      M.d3 + t.w * (t.a * t.b), M.d4 + t.w * (t.a * t.c), M.d5 + t.w * (t.b * t.c),
      M.r0, M.r1, M.r2, M.r3, M.r4, M.r5, M.l0, M.l1, M.l2, M.m⟩
  | .reciprocal =>
    ⟨M.d0, M.d1, M.d2, M.d3, M.d4, M.d5,
      M.r0 + t.w * (t.a * t.a), M.r1 + t.w * (t.b * t.b), M.r2 + t.w * (t.c * t.c),
      M.r3 + t.w * (t.a * t.b), M.r4 + t.w * (t.a * t.c), M.r5 + t.w * (t.b * t.c),
      M.l0, M.l1, M.l2, M.m⟩

def momOf (ts : List WTerm) : Mom := ts.foldl Mom.add Mom.zero

/-! ### Rational corner semantics -/

/-- Primal metric entries at a shape corner `(r₁, r₂, x, y, z)`; off-diagonals doubled. -/
def primalAt (r1 r2 x y z : ℚ) : Fin 6 → ℚ :=
  let s := r1 ^ 2
  let t := r2 ^ 2
  ![s, s * x ^ 2 + t, s * y ^ 2 + t * z ^ 2 + 1 / (s * t), 2 * s * x, 2 * s * y, 2 * (s * x * y + t * z)]

/-- Dual metric entries at a shape corner; off-diagonals doubled. -/
def dualAt (r1 r2 x y z : ℚ) : Fin 6 → ℚ :=
  let s := r1 ^ 2
  let t := r2 ^ 2
  let h := x * z - y
  ![1 / s + x ^ 2 / t + h ^ 2 * (s * t), 1 / t + z ^ 2 * (s * t), s * t,
    2 * (-x / t - h * z * (s * t)), 2 * h * (s * t), -2 * z * (s * t)]

/-- `v₀², v₁², v₂², v₀v₁, v₀v₂, v₁v₂`. -/
def mono (v0 v1 v2 : ℚ) : Fin 6 → ℚ := ![v0 ^ 2, v1 ^ 2, v2 ^ 2, v0 * v1, v0 * v2, v1 * v2]

def dot6 (u v : Fin 6 → ℚ) : ℚ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5

theorem cornerDistance_dot (b : Cell) (bits : Axis → Bool) (s : Bool) (n : IntVec)
    (h0 : cornerRat b bits 0 ≠ 0) (h1 : cornerRat b bits 1 ≠ 0) :
    cornerDistance b bits s n =
      dot6 (primalAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
        (cornerRat b bits 3) (cornerRat b bits 4))
        (mono ((n 0 : ℚ) + (if s then cornerRat b bits (offset 0) else 0))
          ((n 1 : ℚ) + (if s then cornerRat b bits (offset 1) else 0))
          ((n 2 : ℚ) + (if s then cornerRat b bits (offset 2) else 0))) := by
  unfold cornerDistance dot6 primalAt mono
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  ring

theorem dualCorner_dot (b : Cell) (bits : Axis → Bool) (n : IntVec)
    (h0 : cornerRat b bits 0 ≠ 0) (h1 : cornerRat b bits 1 ≠ 0) :
    dualCorner (squaredCorner b bits) n =
      dot6 (dualAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
        (cornerRat b bits 3) (cornerRat b bits 4)) (mono (n 0 : ℚ) (n 1 : ℚ) (n 2 : ℚ)) := by
  have e0 : squaredCorner b bits 0 = (cornerRat b bits 0) ^ 2 := by simp [squaredCorner]
  have e1 : squaredCorner b bits 1 = (cornerRat b bits 1) ^ 2 := by simp [squaredCorner]
  have e2 : squaredCorner b bits 2 = cornerRat b bits 2 := by simp [squaredCorner]
  have e3 : squaredCorner b bits 3 = cornerRat b bits 3 := by simp [squaredCorner]
  have e4 : squaredCorner b bits 4 = cornerRat b bits 4 := by simp [squaredCorner]
  unfold dualCorner dot6 dualAt mono
  rw [e0, e1, e2, e3, e4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  ring

/-- The moments of a list, over `ℚ`, at the offset corner `f`. -/
def shiftQ (M : Mom) (f0 f1 f2 : ℚ) : Fin 6 → ℚ :=
  ![(M.d0 + 2 * M.l0 * f0 + M.m * f0 ^ 2 : ℚ), (M.d1 + 2 * M.l1 * f1 + M.m * f1 ^ 2 : ℚ),
    (M.d2 + 2 * M.l2 * f2 + M.m * f2 ^ 2 : ℚ), (M.d3 + M.l0 * f1 + M.l1 * f0 + M.m * f0 * f1 : ℚ),
    (M.d4 + M.l0 * f2 + M.l2 * f0 + M.m * f0 * f2 : ℚ), (M.d5 + M.l1 * f2 + M.l2 * f1 + M.m * f1 * f2 : ℚ)]

def recipQ (M : Mom) : Fin 6 → ℚ := ![(M.r0 : ℚ), M.r1, M.r2, M.r3, M.r4, M.r5]

/-- The weighted corner value of a list, as a sum over the list. -/
def listCorner (b : Cell) (bits : Axis → Bool) (ts : List WTerm) : ℚ :=
  (ts.map fun t => (t.w : ℚ) * t.mode.atCorner b bits).sum

theorem dot6_add (u v w : Fin 6 → ℚ) : dot6 u (fun j => v j + w j) = dot6 u v + dot6 u w := by
  unfold dot6; ring

/-- One term's contribution, in the packed form. -/
theorem term_corner (b : Cell) (bits : Axis → Bool) (t : WTerm)
    (h0 : cornerRat b bits 0 ≠ 0) (h1 : cornerRat b bits 1 ≠ 0) (M : Mom) :
    let P := primalAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
      (cornerRat b bits 3) (cornerRat b bits 4)
    let D := dualAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
      (cornerRat b bits 3) (cornerRat b bits 4)
    let f0 := cornerRat b bits (offset 0)
    let f1 := cornerRat b bits (offset 1)
    let f2 := cornerRat b bits (offset 2)
    dot6 P (shiftQ (M.add t) f0 f1 f2) + dot6 D (recipQ (M.add t)) =
      dot6 P (shiftQ M f0 f1 f2) + dot6 D (recipQ M) + (t.w : ℚ) * t.mode.atCorner b bits := by
  intro P D f0 f1 f2
  cases hf : t.fam with
  | cross =>
    have ac : t.mode.atCorner b bits = cornerDistance b bits true ![t.a, t.b, t.c] := by
      simp [Mode.atCorner, WTerm.mode, hf]
    rw [ac, cornerDistance_dot b bits true _ h0 h1]
    simp only [Mom.add, hf, shiftQ, recipQ, dot6, mono, ite_true, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    push_cast
    ring
  | period =>
    have ac : t.mode.atCorner b bits = cornerDistance b bits false ![t.a, t.b, t.c] := by
      simp [Mode.atCorner, WTerm.mode, hf]
    rw [ac, cornerDistance_dot b bits false _ h0 h1]
    simp only [Mom.add, hf, shiftQ, recipQ, dot6, mono, Bool.false_eq_true, ite_false, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    push_cast
    ring
  | reciprocal =>
    have ac : t.mode.atCorner b bits = dualCorner (squaredCorner b bits) ![t.a, t.b, t.c] := by
      simp [Mode.atCorner, WTerm.mode, hf]
    rw [ac, dualCorner_dot b bits _ h0 h1]
    simp only [Mom.add, hf, shiftQ, recipQ, dot6, mono, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    push_cast
    ring

theorem shiftQ_zero (f0 f1 f2 : ℚ) (P : Fin 6 → ℚ) : dot6 P (shiftQ Mom.zero f0 f1 f2) = 0 := by
  simp [dot6, shiftQ, Mom.zero]

theorem recipQ_zero (D : Fin 6 → ℚ) : dot6 D (recipQ Mom.zero) = 0 := by
  simp [dot6, recipQ, Mom.zero]

/-- **Packed form.** The weighted corner value of a list is its moments against the metric. -/
theorem listCorner_packed (b : Cell) (bits : Axis → Bool) (ts : List WTerm)
    (h0 : cornerRat b bits 0 ≠ 0) (h1 : cornerRat b bits 1 ≠ 0) :
    listCorner b bits ts =
      dot6 (primalAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
          (cornerRat b bits 3) (cornerRat b bits 4))
        (shiftQ (momOf ts) (cornerRat b bits (offset 0)) (cornerRat b bits (offset 1))
          (cornerRat b bits (offset 2))) +
      dot6 (dualAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
          (cornerRat b bits 3) (cornerRat b bits 4)) (recipQ (momOf ts)) := by
  -- generalize the fold's start
  suffices key : ∀ (M : Mom),
      dot6 (primalAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
          (cornerRat b bits 3) (cornerRat b bits 4))
        (shiftQ (ts.foldl Mom.add M) (cornerRat b bits (offset 0)) (cornerRat b bits (offset 1))
          (cornerRat b bits (offset 2))) +
      dot6 (dualAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
          (cornerRat b bits 3) (cornerRat b bits 4)) (recipQ (ts.foldl Mom.add M)) =
      dot6 (primalAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
          (cornerRat b bits 3) (cornerRat b bits 4))
        (shiftQ M (cornerRat b bits (offset 0)) (cornerRat b bits (offset 1))
          (cornerRat b bits (offset 2))) +
      dot6 (dualAt (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2)
          (cornerRat b bits 3) (cornerRat b bits 4)) (recipQ M) + listCorner b bits ts by
    have k := key Mom.zero
    rw [shiftQ_zero, recipQ_zero, zero_add, zero_add] at k
    unfold momOf
    rw [k]
  induction ts with
  | nil => intro M; simp [listCorner]
  | cons t rest ih =>
    intro M
    rw [List.foldl_cons, ih (M.add t), term_corner b bits t h0 h1 M]
    simp only [listCorner, List.map_cons, List.sum_cons]
    ring


/-! ### Exact integer corners -/

/-- Powers of `E = 2^64`, as literals. -/
def E1 : ℤ := 18446744073709551616
def E2 : ℤ := 340282366920938463463374607431768211456
def E4 : ℤ := 115792089237316195423570985008687907853269984665640564039457584007913129639936
def E5 : ℤ := 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576
def E6 : ℤ := 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816
def E8 : ℤ := 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
def E9 : ℤ := 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136
def E10 : ℤ := 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776
def E12 : ℤ := 1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856
/-- `E^8 / 4 = 2^510`. -/
def E8q : ℤ := 3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412251521024

theorem E_powers : E2 = E1 ^ 2 ∧ E4 = E1 ^ 4 ∧ E5 = E1 ^ 5 ∧ E6 = E1 ^ 6 ∧ E8 = E1 ^ 8 ∧ E9 = E1 ^ 9 ∧
    E10 = E1 ^ 10 ∧ E12 = E1 ^ 12 ∧ 4 * E8q = E1 ^ 8 := by decide +kernel

/-- `q · 2^64` when it is an integer. -/
def fix64 (q : ℚ) : Option ℤ :=
  let x := q * 18446744073709551616
  if x.den = 1 then some x.num else none

theorem fix64_eq {q : ℚ} {X : ℤ} (h : fix64 q = some X) : q = (X : ℚ) / E1 := by
  unfold fix64 at h
  dsimp only at h
  split_ifs at h with hd
  have hX : (q * 18446744073709551616).num = X := Option.some.inj h
  have c := Rat.coe_int_num_of_den_eq_one hd
  rw [hX] at c
  have e1 : ((E1 : ℤ) : ℚ) = 18446744073709551616 := by norm_num [E1]
  rw [e1, c]
  field_simp

/-- The sixteen endpoints at scale `2^64`. -/
structure IBox where
  l0 : ℤ
  l1 : ℤ
  l2 : ℤ
  l3 : ℤ
  l4 : ℤ
  l5 : ℤ
  l6 : ℤ
  l7 : ℤ
  h0 : ℤ
  h1 : ℤ
  h2 : ℤ
  h3 : ℤ
  h4 : ℤ
  h5 : ℤ
  h6 : ℤ
  h7 : ℤ

def IBox.lo (B : IBox) : Axis → ℤ := ![B.l0, B.l1, B.l2, B.l3, B.l4, B.l5, B.l6, B.l7]
def IBox.hi (B : IBox) : Axis → ℤ := ![B.h0, B.h1, B.h2, B.h3, B.h4, B.h5, B.h6, B.h7]

def toIBox (b : Cell) : Option IBox := do
  let l0 ← fix64 (b.lo 0)
  let l1 ← fix64 (b.lo 1)
  let l2 ← fix64 (b.lo 2)
  let l3 ← fix64 (b.lo 3)
  let l4 ← fix64 (b.lo 4)
  let l5 ← fix64 (b.lo 5)
  let l6 ← fix64 (b.lo 6)
  let l7 ← fix64 (b.lo 7)
  let h0 ← fix64 (b.hi 0)
  let h1 ← fix64 (b.hi 1)
  let h2 ← fix64 (b.hi 2)
  let h3 ← fix64 (b.hi 3)
  let h4 ← fix64 (b.hi 4)
  let h5 ← fix64 (b.hi 5)
  let h6 ← fix64 (b.hi 6)
  let h7 ← fix64 (b.hi 7)
  pure ⟨l0, l1, l2, l3, l4, l5, l6, l7, h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem toIBox_spec {b : Cell} {B : IBox} (h : toIBox b = some B) (i : Axis) :
    b.lo i = (B.lo i : ℚ) / E1 ∧ b.hi i = (B.hi i : ℚ) / E1 := by
  unfold toIBox at h
  obtain ⟨l0, e0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l1, e1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l2, e2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l3, e3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l4, e4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l5, e5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l6, e6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l7, e7, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h0, f0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h1, f1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h2, f2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h3, f3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h4, f4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h5, f5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h6, f6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h7, f7, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  subst e
  fin_cases i
  · exact ⟨fix64_eq e0, fix64_eq f0⟩
  · exact ⟨fix64_eq e1, fix64_eq f1⟩
  · exact ⟨fix64_eq e2, fix64_eq f2⟩
  · exact ⟨fix64_eq e3, fix64_eq f3⟩
  · exact ⟨fix64_eq e4, fix64_eq f4⟩
  · exact ⟨fix64_eq e5, fix64_eq f5⟩
  · exact ⟨fix64_eq e6, fix64_eq f6⟩
  · exact ⟨fix64_eq e7, fix64_eq f7⟩

/-- The integer coordinate of a corner. -/
def IBox.at (B : IBox) (bits : Axis → Bool) (i : Axis) : ℤ := if bits i then B.hi i else B.lo i

theorem cornerRat_eq {b : Cell} {B : IBox} (h : toIBox b = some B) (bits : Axis → Bool) (i : Axis) :
    cornerRat b bits i = (B.at bits i : ℚ) / E1 := by
  have s := toIBox_spec h i
  unfold cornerRat IBox.at
  split_ifs
  · exact s.2
  · exact s.1

/-! ### Numerators -/

/-- Primal entries times `a b E^8` (`a = X₀²`, `b = X₁²`). -/
def primalN (X0 X1 X2 X3 X4 : ℤ) : Fin 6 → ℤ :=
  let a := X0 * X0
  let b := X1 * X1
  ![a * a * b * E6, a * b * (a * (X2 * X2) * E4 + b * E6),
    a * b * (a * (X3 * X3) + b * (X4 * X4)) * E4 + E12, 2 * (a * a * b * X2) * E5,
    2 * (a * a * b * X3) * E5, 2 * (a * b) * (a * X2 * X3 * E4 + b * X4 * E5)]

/-- Dual entries times `a b E^8`, `H = X₂ X₄ - X₃ E`. -/
def dualN (X0 X1 X2 X3 X4 : ℤ) : Fin 6 → ℤ :=
  let a := X0 * X0
  let b := X1 * X1
  let H := X2 * X4 - X3 * E1
  let ab2 := a * a * (b * b)
  ![b * E10 + a * (X2 * X2) * E8 + H * H * ab2, a * E10 + X4 * X4 * ab2 * E2, ab2 * E4,
    -2 * (a * X2 * E9 + H * X4 * ab2 * E1), 2 * H * ab2 * E2, -2 * X4 * ab2 * E2 * E1]

/-- The integer moments at an offset corner, times `E²`. -/
def shiftN (M : Mom) (F0 F1 F2 : ℤ) : Fin 6 → ℤ :=
  ![M.d0 * E2 + 2 * M.l0 * F0 * E1 + M.m * (F0 * F0), M.d1 * E2 + 2 * M.l1 * F1 * E1 + M.m * (F1 * F1),
    M.d2 * E2 + 2 * M.l2 * F2 * E1 + M.m * (F2 * F2),
    M.d3 * E2 + (M.l0 * F1 + M.l1 * F0) * E1 + M.m * (F0 * F1),
    M.d4 * E2 + (M.l0 * F2 + M.l2 * F0) * E1 + M.m * (F0 * F2),
    M.d5 * E2 + (M.l1 * F2 + M.l2 * F1) * E1 + M.m * (F1 * F2)]

def recipN (M : Mom) : Fin 6 → ℤ := ![M.r0, M.r1, M.r2, M.r3, M.r4, M.r5]

def dotZ (u v : Fin 6 → ℤ) : ℤ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5

/-- A reduction cut: `false` is `r₂² - (3/4) r₁²`, `true` is `r₂² + r₁²(x² - 1)`. The weight
`lam ≥ 0` is at scale `S`. -/
structure Cut where
  second : Bool
  lam : ℤ

/-- The cut times `a b E^10`. -/
def cutN (c : Cut) (X0 X1 X2 : ℤ) : ℤ :=
  let a := X0 * X0
  let b := X1 * X1
  if c.second then (b * E2 + a * (X2 * X2) - a * E2) * (a * b) * E6
  else (4 * b - 3 * a) * (a * b) * E8q

/-- The rational cut at a shape corner. -/
def cutQ (c : Cut) (r1 r2 x : ℚ) : ℚ :=
  if c.second then r2 ^ 2 + r1 ^ 2 * (x ^ 2 - 1) else r2 ^ 2 - 3 / 4 * r1 ^ 2

def cutVal (c : Option Cut) (r1 r2 x : ℚ) : ℚ :=
  match c with
  | none => 0
  | some c => (c.lam : ℚ) * cutQ c r1 r2 x

def cutNum (c : Option Cut) (X0 X1 X2 : ℤ) : ℤ :=
  match c with
  | none => 0
  | some c => c.lam * cutN c X0 X1 X2

/-- The numerator of one corner value over `a b E^10`. -/
def cornerNum (M : Mom) (c : Option Cut) (X0 X1 X2 X3 X4 F0 F1 F2 : ℤ) : ℤ :=
  dotZ (primalN X0 X1 X2 X3 X4) (shiftN M F0 F1 F2) + E2 * dotZ (dualN X0 X1 X2 X3 X4) (recipN M) +
    cutNum c X0 X1 X2

theorem primalAt_eq (X0 X1 X2 X3 X4 : ℤ) (h0 : X0 ≠ 0) (h1 : X1 ≠ 0) (j : Fin 6) :
    primalAt ((X0 : ℚ) / E1) ((X1 : ℚ) / E1) ((X2 : ℚ) / E1) ((X3 : ℚ) / E1) ((X4 : ℚ) / E1) j =
      (primalN X0 X1 X2 X3 X4 j : ℚ) / ((X0 : ℚ) ^ 2 * (X1 : ℚ) ^ 2 * (E1 : ℚ) ^ 8) := by
  obtain ⟨p2, p4, p5, p6, p8, p9, p10, p12, q8⟩ := E_powers
  have e0 : (E1 : ℚ) ≠ 0 := by norm_num [E1]
  have x0 : (X0 : ℚ) ≠ 0 := by exact_mod_cast h0
  have x1 : (X1 : ℚ) ≠ 0 := by exact_mod_cast h1
  fin_cases j <;>
    simp only [primalAt, primalN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    (try simp only [p2, p4, p5, p6, p8, p9, p10, p12]) <;> push_cast <;> field_simp <;> ring

theorem dualAt_eq (X0 X1 X2 X3 X4 : ℤ) (h0 : X0 ≠ 0) (h1 : X1 ≠ 0) (j : Fin 6) :
    dualAt ((X0 : ℚ) / E1) ((X1 : ℚ) / E1) ((X2 : ℚ) / E1) ((X3 : ℚ) / E1) ((X4 : ℚ) / E1) j =
      (dualN X0 X1 X2 X3 X4 j : ℚ) / ((X0 : ℚ) ^ 2 * (X1 : ℚ) ^ 2 * (E1 : ℚ) ^ 8) := by
  obtain ⟨p2, p4, p5, p6, p8, p9, p10, p12, q8⟩ := E_powers
  have e0 : (E1 : ℚ) ≠ 0 := by norm_num [E1]
  have x0 : (X0 : ℚ) ≠ 0 := by exact_mod_cast h0
  have x1 : (X1 : ℚ) ≠ 0 := by exact_mod_cast h1
  fin_cases j <;>
    simp only [dualAt, dualN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    (try simp only [p2, p4, p5, p6, p8, p9, p10, p12]) <;> push_cast <;> field_simp <;> ring

theorem shiftQ_eq (M : Mom) (F0 F1 F2 : ℤ) (j : Fin 6) :
    shiftQ M ((F0 : ℚ) / E1) ((F1 : ℚ) / E1) ((F2 : ℚ) / E1) j = (shiftN M F0 F1 F2 j : ℚ) / (E1 : ℚ) ^ 2 := by
  obtain ⟨p2, -⟩ := E_powers
  have e0 : (E1 : ℚ) ≠ 0 := by norm_num [E1]
  fin_cases j <;>
    simp only [shiftQ, shiftN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    (try simp only [p2]) <;> push_cast <;> field_simp <;> ring

theorem cutQ_eq (c : Cut) (X0 X1 X2 : ℤ) (h0 : X0 ≠ 0) (h1 : X1 ≠ 0) :
    cutQ c ((X0 : ℚ) / E1) ((X1 : ℚ) / E1) ((X2 : ℚ) / E1) =
      (cutN c X0 X1 X2 : ℚ) / ((X0 : ℚ) ^ 2 * (X1 : ℚ) ^ 2 * (E1 : ℚ) ^ 10) := by
  obtain ⟨p2, p4, p5, p6, p8, p9, p10, p12, q8⟩ := E_powers
  have e0 : (E1 : ℚ) ≠ 0 := by norm_num [E1]
  have x0 : (X0 : ℚ) ≠ 0 := by exact_mod_cast h0
  have x1 : (X1 : ℚ) ≠ 0 := by exact_mod_cast h1
  have q8' : (E8q : ℚ) = (E1 : ℚ) ^ 8 / 4 := by
    have : ((4 * E8q : ℤ) : ℚ) = ((E1 ^ 8 : ℤ) : ℚ) := by rw [q8]
    push_cast at this
    linarith
  unfold cutQ cutN
  cases c.second <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    (try simp only [p2, p6]) <;> push_cast <;> (try rw [q8']) <;> field_simp <;> ring

/-- **A corner value as one numerator.** -/
theorem corner_num {b : Cell} {B : IBox} (hB : toIBox b = some B) (ts : List WTerm) (c : Option Cut)
    (bits : Axis → Bool) (h0 : B.at bits 0 ≠ 0) (h1 : B.at bits 1 ≠ 0) :
    listCorner b bits ts + cutVal c (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2) =
      (cornerNum (momOf ts) c (B.at bits 0) (B.at bits 1) (B.at bits 2) (B.at bits 3) (B.at bits 4)
          (B.at bits 5) (B.at bits 6) (B.at bits 7) : ℚ) /
        ((B.at bits 0 : ℚ) ^ 2 * (B.at bits 1 : ℚ) ^ 2 * (E1 : ℚ) ^ 10) := by
  have r0 : cornerRat b bits 0 ≠ 0 := by
    rw [cornerRat_eq hB]; exact div_ne_zero (by exact_mod_cast h0) (by norm_num [E1])
  have r1 : cornerRat b bits 1 ≠ 0 := by
    rw [cornerRat_eq hB]; exact div_ne_zero (by exact_mod_cast h1) (by norm_num [E1])
  rw [listCorner_packed b bits ts r0 r1]
  simp only [cornerRat_eq hB]
  have off : ∀ k : Fin 3, (offset k) = (⟨k.val + 5, by omega⟩ : Axis) := fun _ => rfl
  have e0 : (E1 : ℚ) ≠ 0 := by norm_num [E1]
  have x0 : (B.at bits 0 : ℚ) ≠ 0 := by exact_mod_cast h0
  have x1 : (B.at bits 1 : ℚ) ≠ 0 := by exact_mod_cast h1
  have ps := primalAt_eq (B.at bits 0) (B.at bits 1) (B.at bits 2) (B.at bits 3) (B.at bits 4) h0 h1
  have ds := dualAt_eq (B.at bits 0) (B.at bits 1) (B.at bits 2) (B.at bits 3) (B.at bits 4) h0 h1
  have ss := shiftQ_eq (momOf ts) (B.at bits 5) (B.at bits 6) (B.at bits 7)
  have o0 : offset 0 = (5 : Axis) := rfl
  have o1 : offset 1 = (6 : Axis) := rfl
  have o2 : offset 2 = (7 : Axis) := rfl
  rw [o0, o1, o2]
  have p2q : ((E2 : ℤ) : ℚ) = (E1 : ℚ) ^ 2 := by rw [E_powers.1]; push_cast; ring
  unfold dot6 cornerNum dotZ
  rw [ps 0, ps 1, ps 2, ps 3, ps 4, ps 5, ds 0, ds 1, ds 2, ds 3, ds 4, ds 5, ss 0, ss 1, ss 2, ss 3,
    ss 4, ss 5]
  cases c with
  | none =>
    simp only [cutVal, cutNum, add_zero, Int.cast_zero]
    unfold recipQ recipN
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    push_cast
    rw [p2q]
    field_simp
  | some cc =>
    simp only [cutVal, cutNum]
    rw [cutQ_eq cc _ _ _ h0 h1]
    unfold recipQ recipN
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    push_cast
    rw [p2q]
    field_simp


/-! ### The corner loop -/

def shapeList (B : IBox) : List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [B.l0, B.h0].flatMap fun x0 => [B.l1, B.h1].flatMap fun x1 => [B.l2, B.h2].flatMap fun x2 =>
    [B.l3, B.h3].flatMap fun x3 => [B.l4, B.h4].map fun x4 => (x0, x1, x2, x3, x4)

def offsetList (B : IBox) : List (ℤ × ℤ × ℤ) :=
  [B.l5, B.h5].flatMap fun f0 => [B.l6, B.h6].flatMap fun f1 => [B.l7, B.h7].map fun f2 => (f0, f1, f2)

/-- Ceiling division by a positive integer. -/
def ceilDiv (n d : ℤ) : ℤ := -((-n) / d)

theorem le_ceilDiv (n d : ℤ) (hd : 0 < d) : (n : ℝ) / d ≤ (ceilDiv n d : ℝ) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have f : ((-n) / d : ℤ) * d ≤ -n := Int.ediv_mul_le (-n) hd.ne'
  have fR : (((-n) / d : ℤ) : ℝ) * d ≤ -(n : ℝ) := by exact_mod_cast f
  unfold ceilDiv
  push_cast
  rw [div_le_iff₀ hdR]
  linarith

/-- The largest value of `f` on a list, and at least `0`. -/
def lmax {α : Type} (f : α → ℤ) (l : List α) : ℤ := l.foldl (fun acc x => max acc (f x)) 0

theorem foldl_max_ge {α : Type} (f : α → ℤ) (l : List α) (acc : ℤ) :
    acc ≤ l.foldl (fun a x => max a (f x)) acc ∧ ∀ x ∈ l, f x ≤ l.foldl (fun a x => max a (f x)) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih (max acc (f y))
    refine ⟨(le_max_left _ _).trans h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right _ _).trans h1
    · exact h2 x hx

theorem le_lmax {α : Type} (f : α → ℤ) {l : List α} {x : α} (hx : x ∈ l) : f x ≤ lmax f l :=
  (foldl_max_ge f l 0).2 x hx

theorem lmax_nonneg {α : Type} (f : α → ℤ) (l : List α) : 0 ≤ lmax f l := (foldl_max_ge f l 0).1

/-- One shape corner: the largest numerator over the offset corners, over its denominator. -/
def shapeBound (M : Mom) (c : Option Cut) (offs : List (ℤ × ℤ × ℤ)) (X : ℤ × ℤ × ℤ × ℤ × ℤ) : ℤ :=
  ceilDiv
    (lmax (fun F => cornerNum M c X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2 F.1 F.2.1 F.2.2) offs)
    (X.1 * X.1 * (X.2.1 * X.2.1) * E10)

/-- The joint corner bound at scale `S`. -/
def cornerMax (B : IBox) (M : Mom) (c : Option Cut) : ℤ :=
  lmax (shapeBound M c (offsetList B)) (shapeList B)

theorem at_mem (B : IBox) (bits : Axis → Bool) (i : Axis) : B.at bits i ∈ [B.lo i, B.hi i] := by
  unfold IBox.at; split_ifs <;> simp

theorem shape_mem (B : IBox) (bits : Axis → Bool) :
    (B.at bits 0, B.at bits 1, B.at bits 2, B.at bits 3, B.at bits 4) ∈ shapeList B := by
  have m0 := at_mem B bits 0
  have m1 := at_mem B bits 1
  have m2 := at_mem B bits 2
  have m3 := at_mem B bits 3
  have m4 := at_mem B bits 4
  simp only [IBox.lo, IBox.hi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at m0 m1 m2 m3 m4
  unfold shapeList
  exact List.mem_flatMap.mpr ⟨_, m0, List.mem_flatMap.mpr ⟨_, m1, List.mem_flatMap.mpr ⟨_, m2,
    List.mem_flatMap.mpr ⟨_, m3, List.mem_map.mpr ⟨_, m4, rfl⟩⟩⟩⟩⟩

theorem offset_mem (B : IBox) (bits : Axis → Bool) :
    (B.at bits 5, B.at bits 6, B.at bits 7) ∈ offsetList B := by
  have m5 := at_mem B bits 5
  have m6 := at_mem B bits 6
  have m7 := at_mem B bits 7
  simp only [IBox.lo, IBox.hi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at m5 m6 m7
  unfold offsetList
  exact List.mem_flatMap.mpr ⟨_, m5, List.mem_flatMap.mpr ⟨_, m6, List.mem_map.mpr ⟨_, m7, rfl⟩⟩⟩

/-- Every corner value is at most the corner bound. -/
theorem corner_le_max {b : Cell} {B : IBox} (hB : toIBox b = some B) (ts : List WTerm) (c : Option Cut)
    (bits : Axis → Bool) (h0 : B.at bits 0 ≠ 0) (h1 : B.at bits 1 ≠ 0) :
    listCorner b bits ts + cutVal c (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2) ≤
      (cornerMax B (momOf ts) c : ℚ) := by
  rw [corner_num hB ts c bits h0 h1]
  set X := (B.at bits 0, B.at bits 1, B.at bits 2, B.at bits 3, B.at bits 4)
  set F := (B.at bits 5, B.at bits 6, B.at bits 7)
  have den : (0 : ℤ) < X.1 * X.1 * (X.2.1 * X.2.1) * E10 := by
    have a : 0 < X.1 * X.1 := mul_self_pos.mpr h0
    have bb : 0 < X.2.1 * X.2.1 := mul_self_pos.mpr h1
    have e : (0:ℤ) < E10 := by norm_num [E10]
    positivity
  have num := le_lmax (fun F => cornerNum (momOf ts) c X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2 F.1 F.2.1 F.2.2)
    (offset_mem B bits)
  have shape := le_lmax (shapeBound (momOf ts) c (offsetList B)) (shape_mem B bits)
  have ceil := le_ceilDiv
    (lmax (fun F => cornerNum (momOf ts) c X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2 F.1 F.2.1 F.2.2)
      (offsetList B)) (X.1 * X.1 * (X.2.1 * X.2.1) * E10) den
  have denR : (0:ℝ) < ((X.1 * X.1 * (X.2.1 * X.2.1) * E10 : ℤ) : ℝ) := by exact_mod_cast den
  have chain : ((cornerNum (momOf ts) c (B.at bits 0) (B.at bits 1) (B.at bits 2) (B.at bits 3)
      (B.at bits 4) (B.at bits 5) (B.at bits 6) (B.at bits 7) : ℤ) : ℝ) /
      ((X.1 * X.1 * (X.2.1 * X.2.1) * E10 : ℤ) : ℝ) ≤ (cornerMax B (momOf ts) c : ℝ) := by
    refine le_trans ?_ (le_trans ceil (by exact_mod_cast shape))
    exact div_le_div_of_nonneg_right (by exact_mod_cast num) denR.le
  have eq : ((B.at bits 0 : ℚ) ^ 2 * (B.at bits 1 : ℚ) ^ 2 * (E1 : ℚ) ^ 10) =
      ((X.1 * X.1 * (X.2.1 * X.2.1) * E10 : ℤ) : ℚ) := by
    rw [E_powers.2.2.2.2.2.2.1]
    push_cast
    ring
  rw [eq]
  exact_mod_cast chain

/-! ### Chord convexity and the corner principle -/

/-- The cut, on the squared chart. -/
def cutR (c : Option Cut) (q : Chart) : ℝ :=
  match c with
  | none => 0
  | some c => (c.lam : ℝ) * (if c.second then q 1 + q 0 * (q 2 ^ 2 - 1) else q 1 - 3 / 4 * q 0)

theorem chord_add {b : Cell} {f g : Chart → ℝ} (hf : ChordUpper b f) (hg : ChordUpper b g) :
    ChordUpper b (fun q => f q + g q) := by
  intro p hp i t lo hi e
  have a := hf p hp i t lo hi e
  have c := hg p hp i t lo hi e
  simp only at a c ⊢
  linarith

theorem chord_smul {b : Cell} {f : Chart → ℝ} (hf : ChordUpper b f) {k : ℝ} (hk : 0 ≤ k) :
    ChordUpper b (fun q => k * f q) := by
  intro p hp i t lo hi e
  have a := hf p hp i t lo hi e
  simp only at a ⊢
  nlinarith [mul_le_mul_of_nonneg_left a hk]

theorem chord_zero (b : Cell) : ChordUpper b (fun _ => 0) := by
  intro p hp i t lo hi e
  simp

theorem chord_list (b : Cell) (hd : diagonalsCheck b = true) (ts : List WTerm) (nn : ∀ t ∈ ts, 0 ≤ t.w) :
    ChordUpper (squareDiag b) (fun q => (ts.map fun t => (t.w : ℝ) * t.mode.radial q).sum) := by
  induction ts with
  | nil => simpa using chord_zero (squareDiag b)
  | cons t rest ih =>
    have h1 := chord_smul (t.mode.chord b hd) (by exact_mod_cast nn t List.mem_cons_self : (0:ℝ) ≤ t.w)
    have h2 := ih (fun x hx => nn x (List.mem_cons_of_mem t hx))
    simpa only [List.map_cons, List.sum_cons] using chord_add h1 h2

theorem chord_cut (b : Cell) (c : Option Cut) (hc : ∀ cc, c = some cc → 0 ≤ cc.lam) :
    ChordUpper (squareDiag b) (cutR c) := by
  cases c with
  | none => exact chord_zero _
  | some cc =>
    have lam0 : (0:ℝ) ≤ cc.lam := by exact_mod_cast hc cc rfl
    apply chord_smul _ lam0
    intro p hp i t lo hi e
    have q0 : (0:ℝ) ≤ p 0 := by
      have := (hp 0).1
      have s : ((squareDiag b).lo 0 : ℝ) = ((b.lo 0 : ℚ) : ℝ) ^ 2 := by
        simp [squareDiag]
      rw [s] at this
      exact (sq_nonneg _).trans this
    cases hs : cc.second
    · simp only [Bool.false_eq_true, ite_false]
      fin_cases i <;> simp [atLower, atUpper] at e ⊢ <;> nlinarith
    · simp only [ite_true]
      by_cases h2 : i = 2
      · subst h2
        simp [atLower, atUpper] at e ⊢
        have key := mul_le_mul_of_nonneg_left
          (affineSq_chord ((squareDiag b).lo 2 : ℝ) ((squareDiag b).hi 2 : ℝ) t lo hi) q0
        rw [← e] at key
        nlinarith [key]
      · fin_cases i <;> simp_all [atLower, atUpper] <;> nlinarith

theorem cutR_corner (b : Cell) (bits : Axis → Bool) (c : Option Cut) :
    cutR c (corner (squareDiag b) bits) =
      ((cutVal c (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2) : ℚ) : ℝ) := by
  have s0 : corner (squareDiag b) bits 0 = ((cornerRat b bits 0 : ℚ) : ℝ) ^ 2 := by
    rw [← squaredCorner_cast]; simp [squaredCorner]
  have s1 : corner (squareDiag b) bits 1 = ((cornerRat b bits 1 : ℚ) : ℝ) ^ 2 := by
    rw [← squaredCorner_cast]; simp [squaredCorner]
  have s2 : corner (squareDiag b) bits 2 = ((cornerRat b bits 2 : ℚ) : ℝ) := by
    rw [← squaredCorner_cast]; simp [squaredCorner]
  cases c with
  | none => simp [cutR, cutVal]
  | some cc =>
    simp only [cutR, cutVal, cutQ, s0, s1, s2]
    cases cc.second <;> simp <;> push_cast <;> ring

/-- **The corner bound.** For every point of the box, the weighted sum of squared distances
plus the cut is at most `cornerMax` (all at scale `S`). -/
theorem cornerMax_sound {b : Cell} {B : IBox} (hB : toIBox b = some B) (hd : diagonalsCheck b = true)
    (ts : List WTerm) (nn : ∀ t ∈ ts, 0 ≤ t.w) (c : Option Cut) (hc : ∀ cc, c = some cc → 0 ≤ cc.lam)
    (pos : ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0) (p : Chart) (hp : b.Mem p) :
    (ts.map fun t => (t.w : ℝ) * t.mode.radial (squarePoint p)).sum + cutR c (squarePoint p) ≤
      (cornerMax B (momOf ts) c : ℝ) := by
  let f : Chart → ℝ := fun q => (ts.map fun t => (t.w : ℝ) * t.mode.radial q).sum + cutR c q
  have chord : ChordUpper (squareDiag b) f := chord_add (chord_list b hd ts nn) (chord_cut b c hc)
  obtain ⟨bits, maximal⟩ := corner_le (squareDiag b) (fun q => -f q) chord _ (squarePoint_mem hp hd)
  have top : f (squarePoint p) ≤ f (corner (squareDiag b) bits) := by
    have m : -f (corner (squareDiag b) bits) ≤ -f (squarePoint p) := maximal
    linarith
  have hsum : (((ts.map fun t => (t.w : ℚ) * t.mode.atCorner b bits).sum : ℚ) : ℝ) =
      (ts.map fun t => (t.w : ℝ) * t.mode.radial (corner (squareDiag b) bits)).sum := by
    rw [Rat.cast_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp [Mode.atCorner_eq]
  have atc : f (corner (squareDiag b) bits) =
      ((listCorner b bits ts + cutVal c (cornerRat b bits 0) (cornerRat b bits 1) (cornerRat b bits 2) : ℚ) : ℝ) := by
    simp only [f, listCorner]
    rw [cutR_corner, Rat.cast_add, hsum]
  have bound := corner_le_max hB ts c bits (pos bits).1 (pos bits).2
  have boundR : ((listCorner b bits ts + cutVal c (cornerRat b bits 0) (cornerRat b bits 1)
      (cornerRat b bits 2) : ℚ) : ℝ) ≤ (cornerMax B (momOf ts) c : ℝ) := by exact_mod_cast bound
  exact top.trans (atc ▸ boundR)


/-! ### A faster corner loop

The same numbers as `cornerMax`, computed with six-field structures instead of
`Fin 6` vectors, with each offset corner's shift and each shape corner's dual part and
cut computed once. `cornerMaxF_eq` shows the two loops agree. -/

structure V6 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  x5 : ℤ

def V6.dot (u v : V6) : ℤ := u.x0 * v.x0 + u.x1 * v.x1 + u.x2 * v.x2 + u.x3 * v.x3 + u.x4 * v.x4 + u.x5 * v.x5

def primalV (X0 X1 X2 X3 X4 : ℤ) : V6 :=
  let a := X0 * X0
  let b := X1 * X1
  ⟨a * a * b * E6, a * b * (a * (X2 * X2) * E4 + b * E6),
    a * b * (a * (X3 * X3) + b * (X4 * X4)) * E4 + E12, 2 * (a * a * b * X2) * E5,
    2 * (a * a * b * X3) * E5, 2 * (a * b) * (a * X2 * X3 * E4 + b * X4 * E5)⟩

def dualV (X0 X1 X2 X3 X4 : ℤ) : V6 :=
  let a := X0 * X0
  let b := X1 * X1
  let H := X2 * X4 - X3 * E1
  let ab2 := a * a * (b * b)
  ⟨b * E10 + a * (X2 * X2) * E8 + H * H * ab2, a * E10 + X4 * X4 * ab2 * E2, ab2 * E4,
    -2 * (a * X2 * E9 + H * X4 * ab2 * E1), 2 * H * ab2 * E2, -2 * X4 * ab2 * E2 * E1⟩

def shiftV (M : Mom) (F0 F1 F2 : ℤ) : V6 :=
  ⟨M.d0 * E2 + 2 * M.l0 * F0 * E1 + M.m * (F0 * F0), M.d1 * E2 + 2 * M.l1 * F1 * E1 + M.m * (F1 * F1),
    M.d2 * E2 + 2 * M.l2 * F2 * E1 + M.m * (F2 * F2),
    M.d3 * E2 + (M.l0 * F1 + M.l1 * F0) * E1 + M.m * (F0 * F1),
    M.d4 * E2 + (M.l0 * F2 + M.l2 * F0) * E1 + M.m * (F0 * F2),
    M.d5 * E2 + (M.l1 * F2 + M.l2 * F1) * E1 + M.m * (F1 * F2)⟩

def recipV (M : Mom) : V6 := ⟨M.r0, M.r1, M.r2, M.r3, M.r4, M.r5⟩

theorem primal_dot (X0 X1 X2 X3 X4 F0 F1 F2 : ℤ) (M : Mom) :
    (primalV X0 X1 X2 X3 X4).dot (shiftV M F0 F1 F2) = dotZ (primalN X0 X1 X2 X3 X4) (shiftN M F0 F1 F2) := by
  simp only [V6.dot, primalV, shiftV, dotZ, primalN, shiftN, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]

theorem dual_dot (X0 X1 X2 X3 X4 : ℤ) (M : Mom) :
    (dualV X0 X1 X2 X3 X4).dot (recipV M) = dotZ (dualN X0 X1 X2 X3 X4) (recipN M) := by
  simp only [V6.dot, dualV, recipV, dotZ, dualN, recipN, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]

def shapeBoundF (M : Mom) (c : Option Cut) (offs : List (ℤ × ℤ × ℤ)) (hs : List V6)
    (X : ℤ × ℤ × ℤ × ℤ × ℤ) : ℤ :=
  let P := primalV X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2
  let base := E2 * (dualV X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2).dot (recipV M) + cutNum c X.1 X.2.1 X.2.2.1
  ceilDiv (lmax (fun h => P.dot h + base) hs) (X.1 * X.1 * (X.2.1 * X.2.1) * E10)

/-- The fast joint corner bound. -/
def cornerMaxF (B : IBox) (M : Mom) (c : Option Cut) : ℤ :=
  let offs := offsetList B
  lmax (shapeBoundF M c offs (offs.map fun F => shiftV M F.1 F.2.1 F.2.2)) (shapeList B)

theorem lmax_map {α β : Type} (f : β → ℤ) (g : α → β) (l : List α) :
    lmax f (l.map g) = lmax (fun x => f (g x)) l := by
  unfold lmax
  rw [List.foldl_map]

theorem shapeBoundF_eq (M : Mom) (c : Option Cut) (offs : List (ℤ × ℤ × ℤ)) :
    shapeBoundF M c offs (offs.map fun F => shiftV M F.1 F.2.1 F.2.2) = shapeBound M c offs := by
  funext X
  unfold shapeBoundF shapeBound
  dsimp only
  rw [lmax_map]
  have e : (fun F : ℤ × ℤ × ℤ => (primalV X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2).dot (shiftV M F.1 F.2.1 F.2.2) +
      (E2 * (dualV X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2).dot (recipV M) + cutNum c X.1 X.2.1 X.2.2.1)) =
      fun F => cornerNum M c X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2 F.1 F.2.1 F.2.2 := by
    funext F
    unfold cornerNum
    rw [primal_dot, dual_dot, add_assoc]
  rw [e]

theorem cornerMaxF_eq (B : IBox) (M : Mom) (c : Option Cut) : cornerMaxF B M c = cornerMax B M c := by
  unfold cornerMaxF cornerMax
  dsimp only
  rw [shapeBoundF_eq]

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
