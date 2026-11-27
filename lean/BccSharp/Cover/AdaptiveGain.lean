import BccSharp.Cover.AdaptiveSupport

set_option autoImplicit false

/-! The reciprocal phase-triad gain of the Adaptive support (used by the `Z`, `R` and `K`
routes).

A reciprocal term `2 φ_n k_n` of the series (`φ_n = 1 + cos 2π n·f`, `k_n = G(1, π q*_n)`)
enters the Jensen support of `supportValue` only through its phase floor `ℓ_n ≤ φ_n`
(the multiplier `μ = 2 ℓ_n`). The rest, `2 (φ_n - ℓ_n) k_n ≥ 0` (`resid`), is unused there.
For three reciprocal terms whose indices satisfy `n_i ± n_j ± n_k = 0`, the phases add up to
zero, so `φ_i + φ_j + φ_k ≥ 3/2` (`triad_floor`). A list of allocations (`Alloc`: three
positions in the term list, the signs, an amount `a ≥ 0` at scale `S`) then gives

  `Σ_r a_r (3/2 - ℓ_i - ℓ_j - ℓ_k) ≤ Σ_n spent_n (φ_n - ℓ_n) ≤ Σ_n resid_n`

provided every mode's total amount `spent_n` is at most a lower bound of `2 k_n` on the box
(`capS`: the corner maximum of `q*_n`, then `2 e^{-x}/x`). `supportGainCheck` accepts a box
when `L + gain > fccHZ`; `supportGainCheck_sound` gives `energy fcc < energy (chartPoint p)` at
every `good` point. With no allocations it is `supportCheck`. Allocations are proposal data:
the kernel checks the signed-zero relation, the families and every capacity. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BccSharp.Coverage BravaisCover DirectRoute Stage2 OverlayPlanar.Fix

/-! ### Capacities -/

/-- The moments `a², b², c², ab, ac, bc` of a term's index. -/
def momV (t : Term) : V6 := ⟨t.a * t.a, t.b * t.b, t.c * t.c, t.a * t.b, t.a * t.c, t.b * t.c⟩

/-- The term as a reciprocal mode of weight `S`. -/
def capW (t : Term) : WTerm := ⟨.reciprocal, t.a, t.b, t.c, Sz⟩

/-- At scale `S`, an upper bound of the dual quadratic form of the term's index on the box:
the corner maximum of one reciprocal mode of weight `S` (`dualMax_eq`). -/
def dualMax (B : IBox) (t : Term) : ℤ :=
  lmax (fun X => ceilDiv (max 0 (E2 * Sz * (dualV X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2).dot (momV t)))
    (X.1 * X.1 * (X.2.1 * X.2.1) * E10)) (shapeList B)

/-- At scale `S`, a lower bound of `2 G(1, π q*) = 2 e^{-π q*} / (π q*)` on the box. -/
def capS (B : IBox) (t : Term) : ℤ :=
  let X := cdivZ (dualMax B t * (piHiN : ℤ)) Sz
  if 0 < X then 2 * (expNegPt X.toNat).lo * Sz / X else 0

theorem foldl_max_const {α : Type} (c : ℤ) : ∀ (l : List α) (a : ℤ),
    l.foldl (fun acc _ => max acc c) (max a c) = max a c
  | [], _ => rfl
  | _ :: rest, a => by
    simp only [List.foldl_cons, max_assoc, max_self]
    exact foldl_max_const c rest a

theorem lmax_const {α : Type} (x : α) (rest : List α) (c : ℤ) :
    lmax (fun _ => c) (x :: rest) = max 0 c := by
  unfold lmax
  simp only [List.foldl_cons]
  exact foldl_max_const c rest 0

theorem dualMax_eq (B : IBox) (t : Term) : dualMax B t = cornerMax B (momOf [capW t]) none := by
  unfold dualMax cornerMax
  congr 1
  funext X
  unfold shapeBound
  congr 1
  have hc : ∀ F : ℤ × ℤ × ℤ,
      cornerNum (momOf [capW t]) none X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2 F.1 F.2.1 F.2.2 =
        E2 * Sz * (dualV X.1 X.2.1 X.2.2.1 X.2.2.2.1 X.2.2.2.2).dot (momV t) := by
    intro F
    unfold cornerNum
    rw [← dual_dot]
    simp [momOf, Mom.add, capW, Mom.zero, shiftN, recipV, cutNum, dotZ, V6.dot, momV]
    ring
  simp only [hc]
  cases h : offsetList B with
  | nil => simp [offsetList] at h
  | cons x rest => exact (lmax_const x rest _).symm

theorem term_mode_recip (t : Term) (hf : t.fam = .reciprocal) :
    t.mode = ⟨.reciprocal, t.mode.index⟩ := by
  simp [Term.mode, hf]

/-- **Capacities.** On the box, `capS / S ≤ 2 G(1, π q*)` for a valid reciprocal term. -/
theorem capS_sound {bx : Cell} {B : IBox} (hB : toIBox bx = some B) (hd : diagonalsCheck bx = true)
    (pos : ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0) (t : Term) (hf : t.fam = .reciprocal)
    (valid : t.mode.valid) {p : Chart} (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    (capS B t : ℝ) / Sz ≤ 2 * seriesReciprocalTerm (chartPoint p) t.mode.index := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  have lex : lexPositive t.mode.index := valid.2.resolve_left (by simp [Term.mode, hf])
  have qpos := reciprocalPositive hv (lex_ne lex)
  set q := quad (gram (chartPoint p).basis)⁻¹ (castVec t.mode.index) with hq
  have xpos : 0 < Real.pi * q := mul_pos Real.pi_pos qpos
  have kEq : seriesReciprocalTerm (chartPoint p) t.mode.index = Real.exp (-(Real.pi * q)) / (Real.pi * q) := by
    rw [seriesReciprocalTerm, ite_eq_right (lex_ne lex), gKernel_one xpos]
  have kpos : 0 < seriesReciprocalTerm (chartPoint p) t.mode.index := by
    rw [kEq]; exact div_pos (Real.exp_pos _) xpos
  -- the corner bound of `q`
  obtain ⟨h0, h1⟩ := radialLoPos bx hd
  have d0 := h0.trans_le (hp 0).1
  have d1 := h1.trans_le (hp 1).1
  have radial : t.mode.radial (squarePoint p) = q := by
    rw [term_mode_recip t hf]
    simp only [Mode.radial]
    exact dualRadial_eq _ p d0.ne' d1.ne'
  have wmode : (capW t).mode = t.mode := by simp [WTerm.mode, capW, Term.mode, hf]
  have corner := cornerMax_sound hB hd [capW t] (by simp [capW, Sz]) none (by simp) pos p hp
  rw [← dualMax_eq] at corner
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, cutR, wmode, radial] at corner
  have capWw : ((capW t).w : ℝ) = Sz := by simp [capW]
  rw [capWw] at corner
  -- `π q ≤ X / S`
  set X := cdivZ (dualMax B t * (piHiN : ℤ)) Sz with hX
  have ph := pi_bounds.2
  rw [S_eq] at ph
  have piN : (0:ℝ) ≤ (piHiN : ℝ) := by positivity
  have Xge : Real.pi * q ≤ (X : ℝ) / Sz := by
    have c1 := le_cdiv (dualMax B t * (piHiN : ℤ)) Sz spZ
    rw [← hX] at c1
    have qle : q ≤ (dualMax B t : ℝ) / Sz := by rw [le_div_iff₀ sp]; linarith
    calc Real.pi * q ≤ ((piHiN : ℝ) / Sz) * ((dualMax B t : ℝ) / Sz) :=
          mul_le_mul ph qle qpos.le (div_nonneg piN sp.le)
      _ = (((dualMax B t * (piHiN : ℤ) : ℤ) : ℝ) / Sz) / Sz := by push_cast; ring
      _ ≤ (X : ℝ) / Sz := div_le_div_of_nonneg_right c1 sp.le
  unfold capS
  simp only [← hX]
  split_ifs with hXp
  · have XR : (0:ℝ) < X := by exact_mod_cast hXp
    have Xn : ((X.toNat : ℕ) : ℝ) = (X : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hXp.le
    have m := (expNegPt_mem X.toNat).1
    rw [Xn] at m
    have f := fdiv_le (2 * (expNegPt X.toNat).lo * Sz) X hXp
    have x2 : 0 < (X : ℝ) / Sz := div_pos XR sp
    calc ((2 * (expNegPt X.toNat).lo * Sz / X : ℤ) : ℝ) / Sz
        ≤ ((2 * (expNegPt X.toNat).lo * Sz : ℤ) : ℝ) / X / Sz := div_le_div_of_nonneg_right f sp.le
      _ = 2 * (((expNegPt X.toNat).lo : ℝ) / Sz) / ((X : ℝ) / Sz) := by push_cast; field_simp
      _ ≤ 2 * Real.exp (-((X : ℝ) / Sz)) / ((X : ℝ) / Sz) := by
          apply div_le_div_of_nonneg_right _ x2.le
          linarith
      _ ≤ 2 * Real.exp (-(Real.pi * q)) / ((X : ℝ) / Sz) := by
          apply div_le_div_of_nonneg_right _ x2.le
          have := Real.exp_le_exp.mpr (neg_le_neg Xge)
          linarith
      _ ≤ 2 * Real.exp (-(Real.pi * q)) / (Real.pi * q) :=
          div_le_div_of_nonneg_left (by positivity) xpos Xge
      _ = 2 * seriesReciprocalTerm (chartPoint p) t.mode.index := by rw [kEq]; ring
  · simp only [Int.cast_zero, zero_div]
    linarith

/-! ### Triads -/

/-- A triad allocation: three positions in the term list, the signs of the second and third
index, and an amount at scale `S`. -/
structure Alloc where
  i : ℕ
  j : ℕ
  k : ℕ
  minusB : Bool
  minusC : Bool
  amount : ℕ

def sgnZ (minus : Bool) (x : ℤ) : ℤ := if minus then -x else x

def isRecip (t : Term) : Bool :=
  match t.fam with
  | .reciprocal => true
  | _ => false

theorem isRecip_iff (t : Term) : isRecip t = true ↔ t.fam = .reciprocal := by
  unfold isRecip
  cases t.fam <;> simp

/-- Three reciprocal terms with `n_i + (±n_j) + (±n_k) = 0`. -/
def Alloc.valid (ts : List Term) (r : Alloc) : Bool :=
  match ts[r.i]?, ts[r.j]?, ts[r.k]? with
  | some x, some y, some z =>
    isRecip x && isRecip y && isRecip z &&
      decide (x.a + sgnZ r.minusB y.a + sgnZ r.minusC z.a = 0 ∧
        x.b + sgnZ r.minusB y.b + sgnZ r.minusC z.b = 0 ∧
        x.c + sgnZ r.minusB y.c + sgnZ r.minusC z.c = 0)
  | _, _, _ => false

/-- How often position `u` occurs in the allocation. -/
def Alloc.count (r : Alloc) (u : ℕ) : ℕ :=
  (if r.i = u then 1 else 0) + (if r.j = u then 1 else 0) + (if r.k = u then 1 else 0)

/-- The total amount charged to position `u`. -/
def spentAt (rs : List Alloc) (u : ℕ) : ℕ := (rs.map fun r => r.count u * r.amount).sum

def floorAt (bx : Cell) (ts : List Term) (u : ℕ) : ℤ :=
  match ts[u]? with
  | some t => phaseLoS bx t
  | none => 0

def capAt (B : IBox) (ts : List Term) (u : ℕ) : ℤ :=
  match ts[u]? with
  | some t => capS B t
  | none => 0

/-- `3/2` at scale `S`. -/
def threeHalvesS : ℤ := 118842243771396506390315925504

def Alloc.gainNum (bx : Cell) (ts : List Term) (r : Alloc) : ℤ :=
  (r.amount : ℤ) * (threeHalvesS - floorAt bx ts r.i - floorAt bx ts r.j - floorAt bx ts r.k)

def capsOk (B : IBox) (ts : List Term) (rs : List Alloc) : Bool :=
  rs.all fun r => decide ((spentAt rs r.i : ℤ) ≤ capAt B ts r.i) &&
    decide ((spentAt rs r.j : ℤ) ≤ capAt B ts r.j) && decide ((spentAt rs r.k : ℤ) ≤ capAt B ts r.k)

/-- The gain at scale `S`, if every allocation is valid and every capacity holds. -/
def gainValue (bx : Cell) (ts : List Term) (rs : List Alloc) : Option ℤ :=
  match toIBox bx with
  | none => none
  | some B =>
    if rs.all (Alloc.valid ts) && capsOk B ts rs then
      some ((rs.map (Alloc.gainNum bx ts)).sum / Sz)
    else none

/-- **The support check with the phase-triad gain.** -/
def supportGainCheck (bx : Cell) (ts : List Term) (c : Option Cut) (rs : List Alloc) : Bool :=
  match supportValue bx ts c, gainValue bx ts rs with
  | some L, some g => decide (fccHZ < L + g)
  | _, _ => false

/-! ### Soundness: one term -/

/-- The part of a reciprocal term left unused by the Jensen support. -/
def resid (bx : Cell) (p : Chart) (t : Term) : ℝ :=
  if t.fam = .reciprocal then
    2 * (phaseFactor (chartPoint p) t.mode.index - (phaseLoS bx t : ℝ) / Sz) *
      seriesReciprocalTerm (chartPoint p) t.mode.index
  else 0

/-- The tangent minorant of a term against its kernel. -/
theorem per_term_kernel (bx : Cell) (hd : diagonalsCheck bx = true) (t : Term) (hok : t.ok = true) {p : Chart}
    (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    tC bx t * Real.exp (tX p t) ≤ tMu bx t * kernelValue (famKind t.fam) (Real.pi * tR p t) := by
  have sp := Sz_pos
  obtain ⟨Tpos, Gm, Wm, G0, W0⟩ := term_kernels t hok
  have valid : t.mode.valid := term_valid (by
    simp only [Term.ok, Bool.and_eq_true] at hok; exact hok.1.1.1)
  obtain ⟨mu0, muC, muP, muR⟩ := mu_sound bx t hp
  obtain ⟨argPos, -⟩ := mode_term_lower bx hd t.mode valid p hp hv (tMu bx t) mu0 ⟨muC, muP, muR⟩
  have Glo : (t.G.lo : ℝ) / Sz ≤ tG t := Gm.1
  have Wlo : (t.W.lo : ℝ) / Sz ≤ tW t := Wm.1
  have Gpos : 0 < tG t := lt_of_lt_of_le (div_pos (by exact_mod_cast G0) sp) Glo
  have Wpos : 0 < tW t := lt_of_lt_of_le (div_pos (by exact_mod_cast W0) sp) Wlo
  have lt := logTangent (famKind t.fam) Tpos argPos
  have rate : (Real.exp (-(tT t)) + ((famKind t.fam).power : ℝ) * kernelValue (famKind t.fam) (tT t)) /
      (tT t * kernelValue (famKind t.fam) (tT t)) = tW t / tG t := by
    unfold tW tG
    field_simp
  have lt' : tG t * Real.exp (tX p t) ≤ kernelValue (famKind t.fam) (Real.pi * tR p t) := by
    unfold tX
    rw [← rate]
    exact lt
  calc tC bx t * Real.exp (tX p t) = tMu bx t * (tG t * Real.exp (tX p t)) := by unfold tC; ring
    _ ≤ tMu bx t * kernelValue (famKind t.fam) (Real.pi * tR p t) := mul_le_mul_of_nonneg_left lt' mu0

/-- A term is at least its tangent minorant plus its unused residual. -/
theorem term_split (bx : Cell) (hd : diagonalsCheck bx = true) (t : Term) (hok : t.ok = true) {p : Chart}
    (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    tC bx t * Real.exp (tX p t) + resid bx p t ≤ t.mode.term (chartPoint p) := by
  by_cases hf : t.fam = .reciprocal
  · have sp := Sz_pos
    have valid : t.mode.valid := term_valid (by
      simp only [Term.ok, Bool.and_eq_true] at hok; exact hok.1.1.1)
    have lex : lexPositive t.mode.index := valid.2.resolve_left (by simp [Term.mode, hf])
    have kt := per_term_kernel bx hd t hok hp hv
    obtain ⟨h0, h1⟩ := radialLoPos bx hd
    have d0 := h0.trans_le (hp 0).1
    have d1 := h1.trans_le (hp 1).1
    have radial : tR p t = quad (gram (chartPoint p).basis)⁻¹ (castVec t.mode.index) := by
      unfold tR
      rw [term_mode_recip t hf]
      simp only [Mode.radial]
      exact dualRadial_eq _ p d0.ne' d1.ne'
    have kern : kernelValue (famKind t.fam) (Real.pi * tR p t) = seriesReciprocalTerm (chartPoint p) t.mode.index := by
      rw [hf, radial, seriesReciprocalTerm, ite_eq_right (lex_ne lex)]
      simp only [famKind]
      exact kernel_one_eq _
    have mu : tMu bx t = 2 * ((phaseLoS bx t : ℝ) / Sz) := by
      unfold tMu Term.mu
      rw [hf]
      push_cast
      ring
    have term : t.mode.term (chartPoint p) =
        2 * (phaseFactor (chartPoint p) t.mode.index * seriesReciprocalTerm (chartPoint p) t.mode.index) := by
      rw [term_mode_recip t hf]
      simp only [Mode.term]
      rw [pairedTerm_eq]
      rfl
    rw [kern, mu] at kt
    rw [term]
    unfold resid
    rw [ite_eq_left hf]
    linarith
  · have f := (per_term bx hd t hok hp hv).2.2.2.2.1
    unfold resid
    rw [ite_eq_right hf, add_zero]
    exact f

/-! ### Soundness: sums over positions -/

/-- `f` of the term at position `u`, or `0`. -/
def termAt (ts : List Term) (u : ℕ) (f : Term → ℝ) : ℝ :=
  match ts[u]? with
  | some t => f t
  | none => 0

theorem sum_range_termAt (ts : List Term) (f : Term → ℝ) :
    (∑ u ∈ Finset.range ts.length, termAt ts u f) = (ts.map f).sum := by
  induction ts with
  | nil => simp
  | cons t rest ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have e : ∀ u, termAt (t :: rest) (u + 1) f = termAt rest u f := by
      intro u; simp [termAt]
    have e0 : termAt (t :: rest) 0 f = f t := by simp [termAt]
    simp only [e, e0, ih, List.map_cons, List.sum_cons]
    ring

theorem sum_spent (rs : List Alloc) (n : ℕ) (g : ℕ → ℝ)
    (hin : ∀ r ∈ rs, r.i < n ∧ r.j < n ∧ r.k < n) :
    (∑ u ∈ Finset.range n, (spentAt rs u : ℝ) * g u) =
      (rs.map fun r => (r.amount : ℝ) * (g r.i + g r.j + g r.k)).sum := by
  induction rs with
  | nil => simp [spentAt]
  | cons r rest ih =>
    have hr := hin r List.mem_cons_self
    have ih' := ih (fun r' h => hin r' (List.mem_cons_of_mem _ h))
    have split : ∀ u, (spentAt (r :: rest) u : ℝ) * g u =
        (r.amount : ℝ) * ((r.count u : ℝ) * g u) + (spentAt rest u : ℝ) * g u := by
      intro u
      simp only [spentAt, List.map_cons, List.sum_cons]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun u _ => split u), Finset.sum_add_distrib, ← Finset.mul_sum, ih']
    have cnt : (∑ u ∈ Finset.range n, (r.count u : ℝ) * g u) = g r.i + g r.j + g r.k := by
      simp only [Alloc.count]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq, Finset.sum_ite_eq]
      simp [Finset.mem_range, hr.1, hr.2.1, hr.2.2]
    rw [cnt]
    simp [List.map_cons, List.sum_cons]

/-! ### Soundness: triads -/

theorem cos_triangle' (x y z : ℝ) (sum : x + y + z = 0) :
    3 / 2 ≤ (1 + Real.cos x) + (1 + Real.cos y) + (1 + Real.cos z) := by
  have cosz : Real.cos z = Real.cos (x + y) := by
    rw [show z = -(x + y) by linarith only [sum], Real.cos_neg]
  rw [cosz, Real.cos_add]
  nlinarith only [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y,
    sq_nonneg (1 + Real.cos x + Real.cos y), sq_nonneg (Real.sin x - Real.sin y)]

theorem phaseFactor_term (q : TwoSite) (t : Term) :
    phaseFactor q t.mode.index =
      1 + Real.cos (2 * Real.pi * ((t.a : ℝ) * q.offset 0 + (t.b : ℝ) * q.offset 1 + (t.c : ℝ) * q.offset 2)) := by
  simp only [phaseFactor, dot, Fin.sum_univ_three, castVec, Term.mode]
  simp

def sgnR (m : Bool) : ℝ := if m then -1 else 1

theorem sgnZ_cast (m : Bool) (v : ℤ) : ((sgnZ m v : ℤ) : ℝ) = sgnR m * (v : ℝ) := by
  cases m <;> simp [sgnZ, sgnR]

theorem cos_sgn (m : Bool) (θ : ℝ) : Real.cos (sgnR m * θ) = Real.cos θ := by
  cases m <;> simp [sgnR, Real.cos_neg]

/-- **Triads.** Signed-zero indices have phase factors summing to at least `3/2`. -/
theorem triad_floor (q : TwoSite) (x y z : Term) (mB mC : Bool)
    (ha : x.a + sgnZ mB y.a + sgnZ mC z.a = 0) (hb : x.b + sgnZ mB y.b + sgnZ mC z.b = 0)
    (hc : x.c + sgnZ mB y.c + sgnZ mC z.c = 0) :
    (3 : ℝ) / 2 ≤ phaseFactor q x.mode.index + phaseFactor q y.mode.index + phaseFactor q z.mode.index := by
  rw [phaseFactor_term, phaseFactor_term, phaseFactor_term]
  have cast3 : ∀ {u v w : ℤ}, u + v + w = 0 → (u : ℝ) + (v : ℝ) + (w : ℝ) = 0 := by
    intro u v w h
    have : ((u + v + w : ℤ) : ℝ) = 0 := by rw [h]; simp
    push_cast at this
    exact this
  have ha' := cast3 ha
  have hb' := cast3 hb
  have hc' := cast3 hc
  rw [sgnZ_cast, sgnZ_cast] at ha' hb' hc'
  set f0 := q.offset 0
  set f1 := q.offset 1
  set f2 := q.offset 2
  have key := cos_triangle' (2 * Real.pi * ((x.a : ℝ) * f0 + (x.b : ℝ) * f1 + (x.c : ℝ) * f2))
    (sgnR mB * (2 * Real.pi * ((y.a : ℝ) * f0 + (y.b : ℝ) * f1 + (y.c : ℝ) * f2)))
    (sgnR mC * (2 * Real.pi * ((z.a : ℝ) * f0 + (z.b : ℝ) * f1 + (z.c : ℝ) * f2)))
    (by linear_combination (2 * Real.pi * f0) * ha' + (2 * Real.pi * f1) * hb' + (2 * Real.pi * f2) * hc')
  rw [cos_sgn, cos_sgn] at key
  linarith

/-! ### Soundness: the gain -/

theorem lsum_add (l : List Term) (f g : Term → ℝ) :
    (l.map fun t => f t + g t).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem asum_le {l : List Alloc} {f g : Alloc → ℝ} (h : ∀ r ∈ l, f r ≤ g r) :
    (l.map f).sum ≤ (l.map g).sum := List.sum_le_sum h

theorem asum_div (l : List Alloc) (f : Alloc → ℝ) (d : ℝ) :
    (l.map f).sum / d = (l.map fun r => f r / d).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

theorem asum_cast (l : List Alloc) (f : Alloc → ℤ) :
    (((l.map f).sum : ℤ) : ℝ) = (l.map fun r => (f r : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => simp [ih]

theorem floorAt_eq (bx : Cell) (ts : List Term) (u : ℕ) :
    (floorAt bx ts u : ℝ) / Sz = termAt ts u (fun t => (phaseLoS bx t : ℝ) / Sz) := by
  unfold floorAt termAt
  cases ts[u]? <;> simp

/-- **The gain bound.** -/
theorem gainValue_sound (bx : Cell) (ts : List Term) (rs : List Alloc) (g : ℤ) (hg : gainValue bx ts rs = some g)
    (hd : diagonalsCheck bx = true) (allOk : ∀ t ∈ ts, t.ok = true)
    (pos : ∀ B, toIBox bx = some B → ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0)
    (p : Chart) (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    (g : ℝ) / Sz ≤ (ts.map (resid bx p)).sum := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  unfold gainValue at hg
  cases hB : toIBox bx with
  | none => rw [hB] at hg; simp at hg
  | some B =>
    rw [hB] at hg
    simp only at hg
    split_ifs at hg with conds
    have gEq : (rs.map (Alloc.gainNum bx ts)).sum / Sz = g := Option.some.inj hg
    simp only [Bool.and_eq_true] at conds
    obtain ⟨valid, caps⟩ := conds
    have validR : ∀ r ∈ rs, r.valid ts = true := List.all_eq_true.mp valid
    have capsR := List.all_eq_true.mp caps
    have posB := pos B hB
    -- the gap at a position
    let gap : Term → ℝ := fun t => phaseFactor (chartPoint p) t.mode.index - (phaseLoS bx t : ℝ) / Sz
    let G : ℕ → ℝ := fun u => termAt ts u gap
    have gapNN : ∀ t, 0 ≤ gap t := by
      intro t
      have := (phaseLoS_sound bx t hp).2
      simp only [gap]
      linarith
    -- a valid allocation: positions, families, triad
    have alloc : ∀ r ∈ rs, ∃ x y z, ts[r.i]? = some x ∧ ts[r.j]? = some y ∧ ts[r.k]? = some z ∧
        x.fam = .reciprocal ∧ y.fam = .reciprocal ∧ z.fam = .reciprocal ∧
        (3 : ℝ) / 2 ≤ phaseFactor (chartPoint p) x.mode.index + phaseFactor (chartPoint p) y.mode.index +
          phaseFactor (chartPoint p) z.mode.index := by
      intro r hr
      have v := validR r hr
      unfold Alloc.valid at v
      cases hx : ts[r.i]? with
      | none => rw [hx] at v; simp at v
      | some x =>
        cases hy : ts[r.j]? with
        | none => rw [hx, hy] at v; simp at v
        | some y =>
          cases hz : ts[r.k]? with
          | none => rw [hx, hy, hz] at v; simp at v
          | some z =>
            rw [hx, hy, hz] at v
            simp only [Bool.and_eq_true, decide_eq_true_eq] at v
            obtain ⟨⟨⟨rx, ry⟩, rz⟩, ha, hb, hc⟩ := v
            exact ⟨x, y, z, rfl, rfl, rfl, (isRecip_iff x).mp rx, (isRecip_iff y).mp ry, (isRecip_iff z).mp rz,
              triad_floor (chartPoint p) x y z r.minusB r.minusC ha hb hc⟩
    have inRange : ∀ r ∈ rs, r.i < ts.length ∧ r.j < ts.length ∧ r.k < ts.length := by
      intro r hr
      obtain ⟨x, y, z, hx, hy, hz, -⟩ := alloc r hr
      exact ⟨(List.getElem?_eq_some_iff.mp hx).1, (List.getElem?_eq_some_iff.mp hy).1,
        (List.getElem?_eq_some_iff.mp hz).1⟩
    -- step 1: the floor division
    have s1 : (g : ℝ) / Sz ≤ (((rs.map (Alloc.gainNum bx ts)).sum : ℤ) : ℝ) / Sz / Sz := by
      rw [← gEq]
      exact div_le_div_of_nonneg_right (fdiv_le _ Sz spZ) sp.le
    -- step 2: per allocation, against the gaps
    have s2 : (((rs.map (Alloc.gainNum bx ts)).sum : ℤ) : ℝ) / Sz / Sz ≤
        (rs.map fun r => (r.amount : ℝ) * (G r.i + G r.j + G r.k)).sum / Sz := by
      rw [asum_cast, asum_div, asum_div, asum_div]
      apply asum_le
      intro r hr
      obtain ⟨x, y, z, hx, hy, hz, -, -, -, tri⟩ := alloc r hr
      have Gi : G r.i = gap x := by simp only [G, termAt, hx]
      have Gj : G r.j = gap y := by simp only [G, termAt, hy]
      have Gk : G r.k = gap z := by simp only [G, termAt, hz]
      have Fi : (floorAt bx ts r.i : ℝ) = phaseLoS bx x := by simp [floorAt, hx]
      have Fj : (floorAt bx ts r.j : ℝ) = phaseLoS bx y := by simp [floorAt, hy]
      have Fk : (floorAt bx ts r.k : ℝ) = phaseLoS bx z := by simp [floorAt, hz]
      have th : (threeHalvesS : ℝ) / Sz = 3 / 2 := by norm_num [threeHalvesS, Sz]
      have am : (0:ℝ) ≤ (r.amount : ℝ) := Nat.cast_nonneg _
      unfold Alloc.gainNum
      push_cast
      rw [Fi, Fj, Fk, Gi, Gj, Gk]
      simp only [gap]
      have expand : ((r.amount : ℝ) * ((threeHalvesS : ℝ) - (phaseLoS bx x : ℝ) - (phaseLoS bx y : ℝ) -
          (phaseLoS bx z : ℝ))) / Sz / Sz =
          (r.amount : ℝ) * ((threeHalvesS : ℝ) / Sz - (phaseLoS bx x : ℝ) / Sz - (phaseLoS bx y : ℝ) / Sz -
            (phaseLoS bx z : ℝ) / Sz) / Sz := by
        field_simp
      rw [expand, th]
      apply div_le_div_of_nonneg_right _ sp.le
      apply mul_le_mul_of_nonneg_left _ am
      linarith
    -- step 3: exchange the sums
    have s3 : (rs.map fun r => (r.amount : ℝ) * (G r.i + G r.j + G r.k)).sum =
        ∑ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u :=
      (sum_spent rs ts.length G inRange).symm
    -- step 4: per position, against the residual
    have s4 : ∀ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u / Sz ≤ termAt ts u (resid bx p) := by
      intro u _
      cases ht : ts[u]? with
      | none => simp [G, termAt, ht]
      | some t =>
        have tmem : t ∈ ts := List.mem_of_getElem? ht
        have Gu : G u = gap t := by simp only [G, termAt, ht]
        have Ru : termAt ts u (resid bx p) = resid bx p t := by simp only [termAt, ht]
        rw [Gu, Ru]
        by_cases zero : spentAt rs u = 0
        · rw [zero]
          simp only [Nat.cast_zero, zero_mul, zero_div]
          unfold resid
          split_ifs with hf
          · have valid : t.mode.valid := term_valid (by
              have := allOk t tmem
              simp only [Term.ok, Bool.and_eq_true] at this
              exact this.1.1.1)
            have lex : lexPositive t.mode.index := valid.2.resolve_left (by simp [Term.mode, hf])
            have k0 : 0 ≤ seriesReciprocalTerm (chartPoint p) t.mode.index := by
              have qpos := reciprocalPositive hv (lex_ne lex)
              rw [seriesReciprocalTerm, ite_eq_right (lex_ne lex), gKernel_one (mul_pos Real.pi_pos qpos)]
              exact div_nonneg (Real.exp_pos _).le (mul_pos Real.pi_pos qpos).le
            have := gapNN t
            simp only [gap] at this
            positivity
          · exact le_refl 0
        · -- some allocation uses position `u`
          obtain ⟨r, hr, cnt⟩ : ∃ r ∈ rs, r.count u ≠ 0 := by
            by_contra none
            push Not at none
            apply zero
            unfold spentAt
            apply List.sum_eq_zero
            intro x hx
            obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
            rw [none r hr, zero_mul]
          have which : r.i = u ∨ r.j = u ∨ r.k = u := by
            unfold Alloc.count at cnt
            by_contra h
            push Not at h
            simp [h.1, h.2.1, h.2.2] at cnt
          obtain ⟨x, y, z, hx, hy, hz, rx, ry, rz, -⟩ := alloc r hr
          have cr := capsR r hr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at cr
          -- the capacity at `u` and the family of `t`
          have capU : ((spentAt rs u : ℕ) : ℤ) ≤ capS B t ∧ t.fam = .reciprocal := by
            rcases which with e | e | e
            · rw [← e] at ht ⊢
              have : capAt B ts r.i = capS B t := by simp [capAt, ht]
              rw [hx] at ht; cases ht
              exact ⟨this ▸ cr.1.1, rx⟩
            · rw [← e] at ht ⊢
              have : capAt B ts r.j = capS B t := by simp [capAt, ht]
              rw [hy] at ht; cases ht
              exact ⟨this ▸ cr.1.2, ry⟩
            · rw [← e] at ht ⊢
              have : capAt B ts r.k = capS B t := by simp [capAt, ht]
              rw [hz] at ht; cases ht
              exact ⟨this ▸ cr.2, rz⟩
          obtain ⟨capLe, hf⟩ := capU
          have valid : t.mode.valid := term_valid (by
            have := allOk t tmem
            simp only [Term.ok, Bool.and_eq_true] at this
            exact this.1.1.1)
          have cs := capS_sound hB hd posB t hf valid hp hv
          have capR : (spentAt rs u : ℝ) / Sz ≤ (capS B t : ℝ) / Sz := by
            apply div_le_div_of_nonneg_right _ sp.le
            exact_mod_cast capLe
          unfold resid
          rw [ite_eq_left hf]
          have g0 := gapNN t
          calc (spentAt rs u : ℝ) * gap t / Sz = ((spentAt rs u : ℝ) / Sz) * gap t := by ring
            _ ≤ (2 * seriesReciprocalTerm (chartPoint p) t.mode.index) * gap t :=
                mul_le_mul_of_nonneg_right (capR.trans cs) g0
            _ = _ := by simp only [gap]; ring
    -- step 5: back to the list
    have s5 : (∑ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u) / Sz ≤ (ts.map (resid bx p)).sum := by
      rw [Finset.sum_div, ← sum_range_termAt]
      exact Finset.sum_le_sum s4
    calc (g : ℝ) / Sz ≤ _ := s1
      _ ≤ _ := s2
      _ = (∑ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u) / Sz := by rw [s3]
      _ ≤ _ := s5

/-- **Soundness of the support check with the gain.** -/
theorem supportGainCheck_sound (bx : Cell) (ts : List Term) (c : Option Cut) (rs : List Alloc)
    (ok : supportGainCheck bx ts c rs = true) (p : Chart) (hp : bx.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) := by
  have sp := Sz_pos
  unfold supportGainCheck at ok
  cases hL : supportValue bx ts c with
  | none => rw [hL] at ok; simp at ok
  | some L =>
    cases hg : gainValue bx ts rs with
    | none => rw [hL, hg] at ok; simp at ok
    | some g =>
      rw [hL, hg] at ok
      have strict : fccHZ < L + g := of_decide_eq_true ok
      obtain ⟨hd, inc, allOk, ⟨B, hB, pos⟩, bound⟩ := supportValue_sound bx ts c L hL p hp gp
      have gain := gainValue_sound bx ts rs g hg hd allOk
        (fun B' hB' => by rw [hB] at hB'; cases hB'; exact pos) p hp gp.1
      have split : (ts.map fun t => tC bx t * Real.exp (tX p t)).sum + (ts.map (resid bx p)).sum ≤
          (ts.map fun t => t.mode.term (chartPoint p)).sum := by
        rw [← lsum_add]
        exact sum_le_map (fun t ht => term_split bx hd t (allOk t ht) hp gp.1)
      have phys := physical_le ts inc allOk _ gp.1
      apply aboveFCC_of_Z strict p
      push_cast
      rw [add_div]
      linarith

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
