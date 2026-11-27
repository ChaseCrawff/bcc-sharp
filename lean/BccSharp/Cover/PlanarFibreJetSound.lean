import BccSharp.Cover.PlanarFibreJet
import BccSharp.Lattice.KernelJet

set_option autoImplicit false

/-! # Soundness of the PlanarFibre second-order jets

* `MR.Mem` and a membership lemma per operation of `MR`, with the
  conversions to and from endpoint intervals.
* `J2Mem B J f`: when `J.ok`, there are functions `D k` (first partials) and
  `D2 j k` (`∂_j` of `D k`) such that on every point `q` of the box `B` the
  value, the coordinate-line derivatives `HasDerivAt (s ↦ f(q[k ↦ s]))` and
  `HasDerivAt (s ↦ D k (q[j ↦ s]))` are enclosed by `J`, and they vanish
  outside the support mask `J.s`.
* One lemma per jet operation (`J2Mem.add`, `J2Mem.mul`, `J2Mem.chain`, …)
  and per scalar function. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri
open BccSharp BccSharp.Coverage DirectRoute
open OverlayPlanar OverlayPlanar.Fix

/-! ### Midpoint-radius intervals -/

/-- `x ∈ [(m - r)/S, (m + r)/S]`. -/
def MR.Mem (a : MR) (x : ℝ) : Prop := |x - (a.m : ℝ) / Sz| ≤ (a.r : ℝ) / Sz

namespace MR

theorem zero_mem : zero.Mem 0 := by
  unfold Mem zero
  simp

theorem ofInt_mem (n : ℤ) : (ofInt n).Mem (n : ℝ) := by
  have sp := Sz_pos
  unfold Mem ofInt
  push_cast
  rw [mul_div_assoc, div_self sp.ne', mul_one, sub_self, abs_zero]
  simp

theorem add_mem {a b : MR} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  unfold Mem add at *
  push_cast
  calc |x + y - ((a.m : ℝ) + b.m) / Sz| = |(x - (a.m : ℝ) / Sz) + (y - (b.m : ℝ) / Sz)| := by
        congr 1; ring
    _ ≤ |x - (a.m : ℝ) / Sz| + |y - (b.m : ℝ) / Sz| := abs_add_le _ _
    _ ≤ (a.r : ℝ) / Sz + (b.r : ℝ) / Sz := add_le_add hx hy
    _ = ((a.r : ℝ) + b.r) / Sz := by ring

theorem neg_mem {a : MR} {x : ℝ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  unfold Mem neg at *
  push_cast
  rw [show -x - -(a.m : ℝ) / Sz = -(x - (a.m : ℝ) / Sz) by ring, abs_neg]
  exact hx

theorem sub_mem {a b : MR} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.sub b).Mem (x - y) := by
  have h := add_mem hx (neg_mem hy)
  unfold Mem add neg sub at *
  simpa [sub_eq_add_neg] using h

theorem smul_mem (n : ℤ) {a : MR} {x : ℝ} (hx : a.Mem x) : (smul n a).Mem ((n : ℝ) * x) := by
  have sp := Sz_pos
  unfold Mem smul at *
  push_cast
  rw [show (n : ℝ) * x - (n : ℝ) * (a.m : ℝ) / Sz = (n : ℝ) * (x - (a.m : ℝ) / Sz) by ring, abs_mul,
    Nat.cast_natAbs, Int.cast_abs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

theorem mul_mem {a b : MR} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.mul b).Mem (x * y) := by
  have sp := Sz_pos
  unfold Mem mul at *
  set X : ℝ := (a.m : ℝ) / Sz
  set Y : ℝ := (b.m : ℝ) / Sz
  have hX : |X| = ((a.m.natAbs : ℕ) : ℝ) / Sz := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_div, abs_of_pos sp]
  have hY : |Y| = ((b.m.natAbs : ℕ) : ℝ) / Sz := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_div, abs_of_pos sp]
  -- the product error
  have e1 : |x * y - X * Y| ≤ |X| * ((b.r : ℝ) / Sz) + ((a.r : ℝ) / Sz) * |Y| +
      ((a.r : ℝ) / Sz) * ((b.r : ℝ) / Sz) := by
    have : x * y - X * Y = X * (y - Y) + (x - X) * Y + (x - X) * (y - Y) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  -- the rounding of the midpoint
  have e2 : |X * Y - ((a.m * b.m / Sz : ℤ) : ℝ) / Sz| ≤ 1 / Sz := by
    have f1 := fdiv_le (a.m * b.m) Sz Sz_posZ
    have f2 := lt_fdiv (a.m * b.m) Sz Sz_posZ
    have hXY : X * Y = ((a.m * b.m : ℤ) : ℝ) / Sz / Sz := by
      simp only [X, Y]; push_cast; ring
    rw [hXY, abs_le]
    constructor
    · have := div_le_div_of_nonneg_right f1 sp.le
      have h0 : (0 : ℝ) ≤ 1 / Sz := by positivity
      linarith
    · have := div_le_div_of_nonneg_right (le_of_lt f2) sp.le
      rw [add_div] at this
      linarith
  -- the radius
  set N : ℕ := a.m.natAbs * b.r + a.r * b.m.natAbs + a.r * b.r
  have hN : |X| * ((b.r : ℝ) / Sz) + ((a.r : ℝ) / Sz) * |Y| + ((a.r : ℝ) / Sz) * ((b.r : ℝ) / Sz) =
      (N : ℝ) / Sz / Sz := by
    rw [hX, hY]; simp only [N]; push_cast; ring
  have hR : (N : ℝ) / Sz ≤ ((N / S : ℕ) : ℝ) + 1 := by
    have := Nat.lt_div_mul_add (a := N) (b := S) S_pos
    rw [div_le_iff₀ sp, ← S_eq]
    have h' : (N : ℝ) < ((N / S : ℕ) : ℝ) * S + S := by exact_mod_cast this
    nlinarith
  calc |x * y - ((a.m * b.m / Sz : ℤ) : ℝ) / Sz|
      ≤ |x * y - X * Y| + |X * Y - ((a.m * b.m / Sz : ℤ) : ℝ) / Sz| := abs_sub_le _ _ _
    _ ≤ (N : ℝ) / Sz / Sz + 1 / Sz := by rw [← hN]; exact add_le_add e1 e2
    _ ≤ (((N / S : ℕ) : ℝ) + 1) / Sz + 1 / Sz := by
        gcongr
    _ = ((((N / S + 2 : ℕ)) : ℝ)) / Sz := by push_cast; ring

theorem half_mem {a : MR} {x : ℝ} (hx : a.Mem x) : a.half.Mem (x / 2) := by
  have sp := Sz_pos
  unfold Mem half at *
  have hq1 : 2 * (a.m / 2) ≤ a.m := by omega
  have hq2 : a.m ≤ 2 * (a.m / 2) + 1 := by omega
  have hr : a.r ≤ 2 * (a.r / 2) + 1 := by omega
  have hq1' : 2 * ((a.m / 2 : ℤ) : ℝ) ≤ a.m := by exact_mod_cast hq1
  have hq2' : (a.m : ℝ) ≤ 2 * ((a.m / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast hq2
  have hr' : (a.r : ℝ) ≤ 2 * ((a.r / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hr
  have key : x / 2 - ((a.m / 2 : ℤ) : ℝ) / Sz =
      (x - (a.m : ℝ) / Sz) / 2 + ((a.m : ℝ) - 2 * ((a.m / 2 : ℤ) : ℝ)) / (2 * Sz) := by
    field_simp
    ring
  have d0 : 0 ≤ ((a.m : ℝ) - 2 * ((a.m / 2 : ℤ) : ℝ)) / (2 * Sz) :=
    div_nonneg (by linarith) (by positivity)
  have d1 : ((a.m : ℝ) - 2 * ((a.m / 2 : ℤ) : ℝ)) / (2 * Sz) ≤ 1 / (2 * Sz) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have rr : (a.r : ℝ) / Sz / 2 + 1 / (2 * Sz) ≤ ((((a.r / 2 : ℕ) + 1 : ℕ)) : ℝ) / Sz := by
    have e : (a.r : ℝ) / Sz / 2 + 1 / (2 * Sz) = ((a.r : ℝ) + 1) / 2 / Sz := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ sp.le
    push_cast
    linarith
  have ha := abs_le.mp hx
  rw [key, abs_le]
  constructor
  · have : -((a.r : ℝ) / Sz) / 2 ≤ (x - (a.m : ℝ) / Sz) / 2 := by linarith [ha.1]
    have h0 : (0 : ℝ) ≤ 1 / (2 * Sz) := by positivity
    linarith
  · have : (x - (a.m : ℝ) / Sz) / 2 ≤ (a.r : ℝ) / Sz / 2 := by linarith [ha.2]
    linarith

theorem toFI_mem {a : MR} {x : ℝ} (hx : a.Mem x) : a.toFI.Mem x := by
  unfold Mem at hx
  unfold toFI FI.Mem lo hi
  rw [abs_le] at hx
  push_cast
  rw [sub_div, add_div]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem ofFI_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (ofFI a).Mem x := by
  have sp := Sz_pos
  unfold FI.Mem at hx
  unfold Mem ofFI
  have hlh : (a.lo : ℝ) ≤ a.hi := by
    have := hx.1.trans hx.2
    rwa [div_le_div_iff_of_pos_right sp] at this
  have hlh' : a.lo ≤ a.hi := by exact_mod_cast hlh
  set M := (a.lo + a.hi) / 2 with hM
  set R := (a.hi - a.lo) / 2 with hR
  have nn : 0 ≤ R := by omega
  have i1 : M - (R + 1) ≤ a.lo := by omega
  have i2 : a.hi ≤ M + (R + 1) := by omega
  have ht : (((R.toNat + 1 : ℕ)) : ℝ) = (R : ℝ) + 1 := by
    push_cast
    rw [show ((R.toNat : ℕ) : ℝ) = (R : ℝ) by exact_mod_cast Int.toNat_of_nonneg nn]
  rw [ht, abs_le]
  have i1' : ((M : ℝ) - ((R : ℝ) + 1)) / Sz ≤ (a.lo : ℝ) / Sz :=
    div_le_div_of_nonneg_right (by exact_mod_cast i1) sp.le
  have i2' : (a.hi : ℝ) / Sz ≤ ((M : ℝ) + ((R : ℝ) + 1)) / Sz :=
    div_le_div_of_nonneg_right (by exact_mod_cast i2) sp.le
  rw [sub_div] at i1'
  rw [add_div] at i2'
  constructor
  · linarith [hx.1]
  · linarith [hx.2]

/-- `gate c x` encloses `v` when `x` does under `c` and `v = 0` otherwise. -/
theorem gate_mem {c : Bool} {x : MR} {v : ℝ} (h1 : c = true → x.Mem v) (h0 : c = false → v = 0) :
    (J2.gate c x).Mem v := by
  cases c with
  | true => exact h1 rfl
  | false =>
    rw [h0 rfl]
    exact zero_mem

theorem lo_le {a : MR} {x : ℝ} (hx : a.Mem x) : (a.lo : ℝ) / Sz ≤ x := (toFI_mem hx).1
theorem le_hi {a : MR} {x : ℝ} (hx : a.Mem x) : x ≤ (a.hi : ℝ) / Sz := (toFI_mem hx).2

end MR

theorem fiNeg_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (fiNeg a).Mem (-x) := by
  unfold FI.Mem fiNeg at *
  push_cast
  rw [neg_div, neg_div]
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem fiHalf_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (fiHalf a).Mem (x / 2) := half_mem hx

theorem piF_mem : piF.Mem Real.pi := by
  have h := fiHalf_mem twoPiF_mem
  rwa [show 2 * Real.pi / 2 = Real.pi by ring] at h

/-! ### Second-order jet membership -/

/-- `J` encloses `f` to second order on `B`: when `J.ok`, there are the
coordinate-line derivatives `D k` of `f` and `D2 j k` (`∂_j` of `D k`), enclosed
by `J` and vanishing outside its support mask, at every point of `B`. -/
def J2Mem (B : Cell) (J : J2) (f : Chart → ℝ) : Prop :=
  J.ok = true → ∃ D : Fin 8 → Chart → ℝ, ∃ D2 : Fin 8 → Fin 8 → Chart → ℝ, ∀ q, B.Mem q →
    J.v.Mem (f q) ∧
    (∀ k, HasDerivAt (fun s => f (Function.update q k s)) (D k q) (q k) ∧ (J.g k).Mem (D k q) ∧
      (J.s k = false → D k q = 0)) ∧
    (∀ j k, HasDerivAt (fun s => D k (Function.update q j s)) (D2 j k q) (q j) ∧
      (J.h j k).Mem (D2 j k q) ∧ ((J.s j && J.s k) = false → D2 j k q = 0))

theorem bool_or_false {p r : Bool} (h : (p || r) = false) : p = false ∧ r = false := by
  cases p <;> cases r <;> simp_all

theorem bool_and_or_false {p q r t : Bool} (h : ((p || r) && (q || t)) = false) :
    (p && q) = false ∧ (r && t) = false ∧ (p = false ∨ t = false) ∧ (q = false ∨ r = false) := by
  cases p <;> cases q <;> cases r <;> cases t <;> simp_all

theorem bool_and_false {p q : Bool} (h : (p && q) = false) : p = false ∨ q = false := by
  cases p <;> cases q <;> simp_all

namespace J2Mem

variable {B : Cell}

theorem const {a : MR} {x : ℝ} (h : a.Mem x) : J2Mem B (J2.const a) (fun _ => x) := by
  intro _
  refine ⟨fun _ _ => 0, fun _ _ _ => 0, fun q _ => ⟨h, fun k => ⟨hasDerivAt_const _ _, ?_, fun _ => rfl⟩,
    fun j k => ⟨hasDerivAt_const _ _, ?_, fun _ => rfl⟩⟩⟩
  · exact MR.zero_mem
  · exact MR.zero_mem

theorem var (b : Cell) (i : Fin 8) : J2Mem b (J2.var b i) (fun p => p i) := by
  intro _
  refine ⟨fun k _ => if k = i then 1 else 0, fun _ _ _ => 0, fun q hq => ⟨?_, fun k => ⟨?_, ?_, ?_⟩,
    fun j k => ⟨hasDerivAt_const _ _, MR.zero_mem, fun _ => rfl⟩⟩⟩
  · exact MR.ofFI_mem (cx_mem hq i)
  · by_cases hk : k = i
    · subst hk
      have e : (fun s => Function.update q k s k) = fun s => s := by
        funext s; exact Function.update_self k s q
      simp only [e, ↓reduceIte]
      exact hasDerivAt_id _
    · have e : (fun s => Function.update q k s i) = fun _ => q i := by
        funext s; exact Function.update_of_ne (Ne.symm hk) s q
      simp only [e, hk, ↓reduceIte]
      exact hasDerivAt_const _ _
  · by_cases hk : k = i
    · simp only [J2.var, hk, ↓reduceIte]
      simpa using MR.ofInt_mem 1
    · simp only [J2.var, hk, ↓reduceIte]
      exact MR.zero_mem
  · intro h
    have hk : k ≠ i := by simpa [J2.var] using h
    simp [hk]

theorem add {a c : J2} {f g : Chart → ℝ} (ha : J2Mem B a f) (hc : J2Mem B c g) :
    J2Mem B (a.add c) (fun p => f p + g p) := by
  intro ok
  simp only [J2.add, Bool.and_eq_true] at ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok.1
  obtain ⟨Dc, D2c, Hc⟩ := hc ok.2
  refine ⟨fun k q => Da k q + Dc k q, fun j k q => D2a j k q + D2c j k q, fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  obtain ⟨vc, gc, hc2⟩ := Hc q hq
  refine ⟨MR.add_mem va vc, fun k => ⟨(ga k).1.add (gc k).1, ?_, ?_⟩,
    fun j k => ⟨(ha2 j k).1.add (hc2 j k).1, ?_, ?_⟩⟩
  · exact MR.add_mem (MR.gate_mem (fun _ => (ga k).2.1) (ga k).2.2)
      (MR.gate_mem (fun _ => (gc k).2.1) (gc k).2.2)
  · intro h
    obtain ⟨h1, h2⟩ := bool_or_false h
    simp only [(ga k).2.2 h1, (gc k).2.2 h2, add_zero]
  · exact MR.add_mem (MR.gate_mem (fun _ => (ha2 j k).2.1) (ha2 j k).2.2)
      (MR.gate_mem (fun _ => (hc2 j k).2.1) (hc2 j k).2.2)
  · intro h
    obtain ⟨h1, h2, _, _⟩ := bool_and_or_false h
    simp only [(ha2 j k).2.2 h1, (hc2 j k).2.2 h2, add_zero]

theorem neg {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B (J2.smul (-1) a) (fun p => -f p) := by
  intro ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok
  refine ⟨fun k q => -Da k q, fun j k q => -D2a j k q, fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  refine ⟨?_, fun k => ⟨(ga k).1.neg, ?_, ?_⟩, fun j k => ⟨(ha2 j k).1.neg, ?_, ?_⟩⟩
  · simpa [J2.smul] using MR.smul_mem (-1) va
  · exact MR.gate_mem (fun _ => by simpa using MR.smul_mem (-1) (ga k).2.1)
      (fun h => by simp [(ga k).2.2 h])
  · intro h; simp [(ga k).2.2 h]
  · exact MR.gate_mem (fun _ => by simpa using MR.smul_mem (-1) (ha2 j k).2.1)
      (fun h => by simp [(ha2 j k).2.2 h])
  · intro h; simp [(ha2 j k).2.2 h]

theorem sub {a c : J2} {f g : Chart → ℝ} (ha : J2Mem B a f) (hc : J2Mem B c g) :
    J2Mem B (a.sub c) (fun p => f p - g p) := by
  intro ok
  simp only [J2.sub, Bool.and_eq_true] at ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok.1
  obtain ⟨Dc, D2c, Hc⟩ := hc ok.2
  refine ⟨fun k q => Da k q - Dc k q, fun j k q => D2a j k q - D2c j k q, fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  obtain ⟨vc, gc, hc2⟩ := Hc q hq
  refine ⟨MR.sub_mem va vc, fun k => ⟨(ga k).1.sub (gc k).1, ?_, ?_⟩,
    fun j k => ⟨(ha2 j k).1.sub (hc2 j k).1, ?_, ?_⟩⟩
  · exact MR.sub_mem (MR.gate_mem (fun _ => (ga k).2.1) (ga k).2.2)
      (MR.gate_mem (fun _ => (gc k).2.1) (gc k).2.2)
  · intro h
    obtain ⟨h1, h2⟩ := bool_or_false h
    simp only [(ga k).2.2 h1, (gc k).2.2 h2, sub_zero]
  · exact MR.sub_mem (MR.gate_mem (fun _ => (ha2 j k).2.1) (ha2 j k).2.2)
      (MR.gate_mem (fun _ => (hc2 j k).2.1) (hc2 j k).2.2)
  · intro h
    obtain ⟨h1, h2, _, _⟩ := bool_and_or_false h
    simp only [(ha2 j k).2.2 h1, (hc2 j k).2.2 h2, sub_zero]

theorem smul (n : ℤ) {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B (a.smul n) (fun p => (n : ℝ) * f p) := by
  intro ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok
  refine ⟨fun k q => (n : ℝ) * Da k q, fun j k q => (n : ℝ) * D2a j k q, fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  refine ⟨MR.smul_mem n va, fun k => ⟨(ga k).1.const_mul _, ?_, ?_⟩,
    fun j k => ⟨(ha2 j k).1.const_mul _, ?_, ?_⟩⟩
  · exact MR.gate_mem (fun _ => MR.smul_mem n (ga k).2.1) (fun h => by simp [(ga k).2.2 h])
  · intro h; simp [(ga k).2.2 h]
  · exact MR.gate_mem (fun _ => MR.smul_mem n (ha2 j k).2.1) (fun h => by simp [(ha2 j k).2.2 h])
  · intro h; simp [(ha2 j k).2.2 h]

theorem scale {t : MR} {τ : ℝ} (ht : t.Mem τ) {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B (a.scale t) (fun p => τ * f p) := by
  intro ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok
  refine ⟨fun k q => τ * Da k q, fun j k q => τ * D2a j k q, fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  refine ⟨MR.mul_mem ht va, fun k => ⟨(ga k).1.const_mul _, ?_, ?_⟩,
    fun j k => ⟨(ha2 j k).1.const_mul _, ?_, ?_⟩⟩
  · exact MR.gate_mem (fun _ => MR.mul_mem ht (ga k).2.1) (fun h => by simp [(ga k).2.2 h])
  · intro h; simp [(ga k).2.2 h]
  · exact MR.gate_mem (fun _ => MR.mul_mem ht (ha2 j k).2.1) (fun h => by simp [(ha2 j k).2.2 h])
  · intro h; simp [(ha2 j k).2.2 h]

theorem half {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) : J2Mem B a.half (fun p => f p / 2) := by
  intro ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok
  refine ⟨fun k q => Da k q / 2, fun j k q => D2a j k q / 2, fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  refine ⟨MR.half_mem va, fun k => ⟨(ga k).1.div_const _, ?_, ?_⟩,
    fun j k => ⟨(ha2 j k).1.div_const _, ?_, ?_⟩⟩
  · exact MR.gate_mem (fun _ => MR.half_mem (ga k).2.1) (fun h => by simp [(ga k).2.2 h])
  · intro h; simp [(ga k).2.2 h]
  · exact MR.gate_mem (fun _ => MR.half_mem (ha2 j k).2.1) (fun h => by simp [(ha2 j k).2.2 h])
  · intro h; simp [(ha2 j k).2.2 h]

theorem mul {a c : J2} {f g : Chart → ℝ} (ha : J2Mem B a f) (hc : J2Mem B c g) :
    J2Mem B (a.mul c) (fun p => f p * g p) := by
  intro ok
  simp only [J2.mul, Bool.and_eq_true] at ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok.1
  obtain ⟨Dc, D2c, Hc⟩ := hc ok.2
  refine ⟨fun k q => Da k q * g q + f q * Dc k q,
    fun j k q => (D2a j k q * g q + Da j q * Dc k q) + (Da k q * Dc j q + f q * D2c j k q),
    fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  obtain ⟨vc, gc, hc2⟩ := Hc q hq
  have eq : ∀ k, Function.update q k (q k) = q := fun k => Function.update_eq_self k q
  refine ⟨MR.mul_mem va vc, fun k => ⟨?_, ?_, ?_⟩, fun j k => ⟨?_, ?_, ?_⟩⟩
  · have h := (ga k).1.mul (gc k).1
    simp only [eq] at h
    exact h
  · exact MR.add_mem (MR.gate_mem (fun _ => MR.mul_mem (ga k).2.1 vc) (fun h => by simp [(ga k).2.2 h]))
      (MR.gate_mem (fun _ => MR.mul_mem va (gc k).2.1) (fun h => by simp [(gc k).2.2 h]))
  · intro h
    obtain ⟨h1, h2⟩ := bool_or_false h
    simp [(ga k).2.2 h1, (gc k).2.2 h2]
  · have h := ((ha2 j k).1.mul (gc j).1).add ((ga j).1.mul (hc2 j k).1)
    simp only [eq] at h
    convert h using 1
    ring
  · show (J2.gate _ _).Mem _
    by_cases hout : ((a.s j || c.s j) && (a.s k || c.s k)) = true
    · rw [hout]
      refine MR.add_mem (MR.add_mem ?_ ?_) (MR.add_mem ?_ ?_)
      · exact MR.gate_mem (fun _ => MR.mul_mem (ha2 j k).2.1 vc) (fun h => by simp [(ha2 j k).2.2 h])
      · exact MR.gate_mem (fun _ => MR.mul_mem (ga j).2.1 (gc k).2.1) (fun h => by
          rcases bool_and_false h with h' | h'
          · simp [(ga j).2.2 h']
          · simp [(gc k).2.2 h'])
      · exact MR.gate_mem (fun _ => MR.mul_mem (ga k).2.1 (gc j).2.1) (fun h => by
          rcases bool_and_false h with h' | h'
          · simp [(ga k).2.2 h']
          · simp [(gc j).2.2 h'])
      · exact MR.gate_mem (fun _ => MR.mul_mem va (hc2 j k).2.1) (fun h => by simp [(hc2 j k).2.2 h])
    · have hf : ((a.s j || c.s j) && (a.s k || c.s k)) = false := by simpa using hout
      rw [hf]
      obtain ⟨h1, h2, h3, h4⟩ := bool_and_or_false hf
      have e1 := (ha2 j k).2.2 h1
      have e2 := (hc2 j k).2.2 h2
      have e3 : Da j q * Dc k q = 0 := by
        rcases h3 with h' | h'
        · simp [(ga j).2.2 h']
        · simp [(gc k).2.2 h']
      have e4 : Da k q * Dc j q = 0 := by
        rcases h4 with h' | h'
        · simp [(ga k).2.2 h']
        · simp [(gc j).2.2 h']
      simp only [J2.gate, Bool.false_eq_true, ↓reduceIte]
      rw [e1, e2, e3, e4]
      simpa using MR.zero_mem
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := bool_and_or_false h
    have e3 : Da j q * Dc k q = 0 := by
      rcases h3 with h' | h'
      · simp [(ga j).2.2 h']
      · simp [(gc k).2.2 h']
    have e4 : Da k q * Dc j q = 0 := by
      rcases h4 with h' | h'
      · simp [(ga k).2.2 h']
      · simp [(gc j).2.2 h']
    show (D2a j k q * g q + Da j q * Dc k q) + (Da k q * Dc j q + f q * D2c j k q) = 0
    rw [(ha2 j k).2.2 h1, (hc2 j k).2.2 h2, e3, e4]
    ring

/-- Composition with a scalar function `φ`, given enclosures of `φ`, `φ'`,
`φ''` on the value interval and the two derivatives. -/
theorem chain {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) {guard : Bool} {f0 f1 f2 : MR}
    {φ φ1 φ2 : ℝ → ℝ}
    (hφ : guard = true → ∀ x, a.v.Mem x → f0.Mem (φ x) ∧ f1.Mem (φ1 x) ∧ f2.Mem (φ2 x) ∧
      HasDerivAt φ (φ1 x) x ∧ HasDerivAt φ1 (φ2 x) x) :
    J2Mem B (a.chain guard f0 f1 f2) (fun p => φ (f p)) := by
  intro ok
  simp only [J2.chain, Bool.and_eq_true] at ok
  obtain ⟨Da, D2a, Ha⟩ := ha ok.1
  refine ⟨fun k q => φ1 (f q) * Da k q,
    fun j k q => φ2 (f q) * (Da j q * Da k q) + φ1 (f q) * D2a j k q, fun q hq => ?_⟩
  obtain ⟨va, ga, ha2⟩ := Ha q hq
  obtain ⟨m0, m1, m2, d1, d2⟩ := hφ ok.2 (f q) va
  have eq : ∀ k, Function.update q k (q k) = q := fun k => Function.update_eq_self k q
  refine ⟨m0, fun k => ⟨?_, ?_, ?_⟩, fun j k => ⟨?_, ?_, ?_⟩⟩
  · have hf := (ga k).1
    have d1' : HasDerivAt φ (φ1 (f q)) (f (Function.update q k (q k))) := by rw [eq]; exact d1
    exact d1'.comp (q k) hf
  · exact MR.gate_mem (fun _ => MR.mul_mem m1 (ga k).2.1) (fun h => by simp [(ga k).2.2 h])
  · intro h; simp [(ga k).2.2 h]
  · have hf := (ga j).1
    have d2' : HasDerivAt φ1 (φ2 (f q)) (f (Function.update q j (q j))) := by rw [eq]; exact d2
    have h1 := d2'.comp (q j) hf
    have h := h1.mul (ha2 j k).1
    convert h using 1
    · funext s
      rfl
    · show φ2 (f q) * (Da j q * Da k q) + φ1 (f q) * D2a j k q =
        φ2 (f q) * Da j q * Da k (Function.update q j (q j)) + φ1 (f (Function.update q j (q j))) * D2a j k q
      rw [eq]
      ring
  · exact MR.gate_mem (fun _ => MR.add_mem (MR.mul_mem m2 (MR.mul_mem (ga j).2.1 (ga k).2.1))
      (MR.mul_mem m1 (ha2 j k).2.1)) (fun h => by
        have h0 : (a.s j && a.s k) = false := h
        rcases bool_and_false h0 with h' | h'
        · simp [(ga j).2.2 h', (ha2 j k).2.2 h0]
        · simp [(ga k).2.2 h', (ha2 j k).2.2 h0])
  · intro h
    have h0 : (a.s j && a.s k) = false := h
    rcases bool_and_false h0 with h' | h'
    · simp [(ga j).2.2 h', (ha2 j k).2.2 h0]
    · simp [(ga k).2.2 h', (ha2 j k).2.2 h0]

/-! ### Scalar functions -/

theorem sq {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) : J2Mem B a.sq (fun p => f p ^ 2) := by
  unfold J2.sq
  apply J2Mem.chain ha (φ := fun x => x ^ 2) (φ1 := fun x => 2 * x) (φ2 := fun _ => 2)
  intro _ x hx
  refine ⟨MR.ofFI_mem (FI.sq_mem (MR.toFI_mem hx)), by simpa using MR.smul_mem 2 hx,
    by simpa using MR.ofInt_mem 2, ?_, ?_⟩
  · simpa using hasDerivAt_pow 2 x
  · simpa using (hasDerivAt_id x).const_mul (2 : ℝ)

theorem pos_of_mem {a : MR} {x : ℝ} (h0 : 0 < a.lo) (hx : a.Mem x) : 0 < x :=
  lt_of_lt_of_le (div_pos (by exact_mod_cast h0) Sz_pos) (MR.lo_le hx)

theorem inv {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) : J2Mem B a.inv (fun p => (f p)⁻¹) := by
  unfold J2.inv
  apply J2Mem.chain ha (φ := fun x => x⁻¹) (φ1 := fun x => -(x⁻¹ ^ 2)) (φ2 := fun x => 2 * (x⁻¹ ^ 2 * x⁻¹))
  intro hg x hx
  have h0 : 0 < a.v.lo := of_decide_eq_true hg
  have hfi := MR.toFI_mem hx
  have xpos : 0 < x := pos_of_mem h0 hx
  have hr := FI.invPos_mem (a := a.v.toFI) h0 hfi
  refine ⟨MR.ofFI_mem hr, MR.ofFI_mem (fiNeg_mem (FI.sq_mem hr)), ?_, ?_, ?_⟩
  · have := FI.smul_mem 2 (FI.mul_mem (FI.sq_mem hr) hr)
    exact MR.ofFI_mem (by simpa using this)
  · have := hasDerivAt_inv xpos.ne'
    convert this using 1
    rw [inv_pow]
  · have h1 := ((hasDerivAt_inv xpos.ne').pow 2).neg
    convert h1 using 1
    simp only [Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one, ← inv_pow]
    ring

theorem sqrt {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) : J2Mem B a.sqrt (fun p => Real.sqrt (f p)) := by
  unfold J2.sqrt
  apply J2Mem.chain ha (φ := Real.sqrt) (φ1 := fun x => (2 * Real.sqrt x)⁻¹)
    (φ2 := fun x => -(2 * ((2 * Real.sqrt x)⁻¹ ^ 2 * (2 * Real.sqrt x)⁻¹)))
  intro hg x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨h0, hr0⟩ := hg
  have hfi := MR.toFI_mem hx
  have xpos : 0 < x := pos_of_mem h0 hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr xpos
  have hr := FI.sqrt_mem hfi
  have h2 : 0 < (FI.smul 2 (FI.sqrt a.v.toFI)).lo := by
    simp only [FI.smul]
    norm_num
    exact hr0
  have hq : ((FI.smul 2 (FI.sqrt a.v.toFI)).invPos).Mem (2 * Real.sqrt x)⁻¹ := by
    have := FI.invPos_mem h2 (FI.smul_mem 2 hr)
    simpa using this
  refine ⟨MR.ofFI_mem hr, MR.ofFI_mem hq, ?_, ?_, ?_⟩
  · have := fiNeg_mem (FI.smul_mem 2 (FI.mul_mem (FI.sq_mem hq) hq))
    exact MR.ofFI_mem (by simpa using this)
  · have := Real.hasDerivAt_sqrt xpos.ne'
    convert this using 1
    rw [one_div]
  · have h1 := ((Real.hasDerivAt_sqrt xpos.ne').const_mul (2 : ℝ)).inv (by positivity)
    convert h1 using 1
    field_simp

theorem expNeg {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B a.expNeg (fun p => Real.exp (-f p)) := by
  unfold J2.expNeg
  apply J2Mem.chain ha (φ := fun x => Real.exp (-x)) (φ1 := fun x => -Real.exp (-x))
    (φ2 := fun x => Real.exp (-x))
  intro hg x hx
  have h0 : 0 ≤ a.v.lo := of_decide_eq_true hg
  have hfi := MR.toFI_mem hx
  have x0 : 0 ≤ x := le_trans (div_nonneg (by exact_mod_cast h0) Sz_pos.le) hfi.1
  have he := expRange_mem hfi x0
  refine ⟨MR.ofFI_mem he, MR.ofFI_mem (fiNeg_mem he), MR.ofFI_mem he, ?_, ?_⟩
  · have := (hasDerivAt_neg x).exp
    convert this using 1
    ring
  · have := (hasDerivAt_neg x).exp.neg
    convert this using 1
    ring

theorem shift_quarter {a : MR} {x : ℝ} (hx : a.Mem x) :
    (⟨a.lo - Sz / 4, a.hi - Sz / 4⟩ : FI).Mem (x - 1 / 4) := by
  have := shift_mem (MR.toFI_mem hx) (Sz / 4)
  rwa [quarter_eq] at this

theorem sin_eq_cos (x : ℝ) : Real.sin (2 * Real.pi * x) = Real.cos (2 * Real.pi * (x - 1 / 4)) := by
  rw [show 2 * Real.pi * (x - 1 / 4) = 2 * Real.pi * x - Real.pi / 2 by ring, Real.cos_sub_pi_div_two]

theorem cos2pi {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B a.cos2pi (fun p => Real.cos (2 * Real.pi * f p)) := by
  unfold J2.cos2pi
  apply J2Mem.chain ha (φ := fun x => Real.cos (2 * Real.pi * x))
    (φ1 := fun x => -(2 * Real.pi * Real.sin (2 * Real.pi * x)))
    (φ2 := fun x => -(2 * Real.pi * (2 * Real.pi * Real.cos (2 * Real.pi * x))))
  intro _ x hx
  have hc := Fix.cosRange_mem (MR.toFI_mem hx)
  have hs := Fix.cosRange_mem (shift_quarter hx)
  rw [← sin_eq_cos] at hs
  refine ⟨MR.ofFI_mem hc, MR.ofFI_mem (fiNeg_mem (FI.mul_mem twoPiF_mem hs)),
    MR.ofFI_mem (fiNeg_mem (FI.mul_mem twoPiF_mem (FI.mul_mem twoPiF_mem hc))), ?_, ?_⟩
  · have := ((hasDerivAt_id' x).const_mul (2 * Real.pi)).cos
    convert this using 1
    ring
  · have := (((hasDerivAt_id' x).const_mul (2 * Real.pi)).sin.const_mul (2 * Real.pi)).neg
    convert this using 1
    ring

theorem sin2pi {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B a.sin2pi (fun p => Real.sin (2 * Real.pi * f p)) := by
  unfold J2.sin2pi
  apply J2Mem.chain ha (φ := fun x => Real.sin (2 * Real.pi * x))
    (φ1 := fun x => 2 * Real.pi * Real.cos (2 * Real.pi * x))
    (φ2 := fun x => -(2 * Real.pi * (2 * Real.pi * Real.sin (2 * Real.pi * x))))
  intro _ x hx
  have hc := Fix.cosRange_mem (MR.toFI_mem hx)
  have hs := Fix.cosRange_mem (shift_quarter hx)
  rw [← sin_eq_cos] at hs
  refine ⟨MR.ofFI_mem hs, MR.ofFI_mem (FI.mul_mem twoPiF_mem hc),
    MR.ofFI_mem (fiNeg_mem (FI.mul_mem twoPiF_mem (FI.mul_mem twoPiF_mem hs))), ?_, ?_⟩
  · have := ((hasDerivAt_id' x).const_mul (2 * Real.pi)).sin
    convert this using 1
    ring
  · have := ((hasDerivAt_id' x).const_mul (2 * Real.pi)).cos.const_mul (2 * Real.pi)
    convert this using 1
    ring

theorem cosh {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B a.cosh (fun p => Real.cosh (f p)) := by
  unfold J2.cosh
  apply J2Mem.chain ha (φ := Real.cosh) (φ1 := Real.sinh) (φ2 := Real.cosh)
  intro hg x hx
  simp only [J2.hypOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hfi := MR.toFI_mem hx
  have hc := Fix.coshRange_mem hfi hg.1 hg.2
  have hs := Fix.sinhRange_mem hfi hg.1 hg.2
  exact ⟨MR.ofFI_mem hc, MR.ofFI_mem hs, MR.ofFI_mem hc, Real.hasDerivAt_cosh x, Real.hasDerivAt_sinh x⟩

theorem sinh {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B a.sinh (fun p => Real.sinh (f p)) := by
  unfold J2.sinh
  apply J2Mem.chain ha (φ := Real.sinh) (φ1 := Real.cosh) (φ2 := Real.sinh)
  intro hg x hx
  simp only [J2.hypOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hfi := MR.toFI_mem hx
  have hc := Fix.coshRange_mem hfi hg.1 hg.2
  have hs := Fix.sinhRange_mem hfi hg.1 hg.2
  exact ⟨MR.ofFI_mem hs, MR.ofFI_mem hc, MR.ofFI_mem hs, Real.hasDerivAt_sinh x, Real.hasDerivAt_cosh x⟩

theorem jsum {ι : Type*} (l : List ι) (F : ι → J2) (fs : ι → Chart → ℝ)
    (h : ∀ i ∈ l, J2Mem B (F i) (fs i)) :
    J2Mem B (PlanarFibreTri.jsum (l.map F)) (fun p => (l.map fun i => fs i p).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, PlanarFibreTri.jsum, List.sum_nil]
    exact J2Mem.const MR.zero_mem
  | cons i l ih =>
    simp only [List.map_cons, PlanarFibreTri.jsum, List.sum_cons]
    exact J2Mem.add (h i List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

end J2Mem

/-! ### The planar kernel at a point -/

open BravaisCover in
/-- `kernelValue .half` is `gKernel (1/2)`. -/
theorem kernel_half (x : ℝ) : kernelValue .half x = gKernel (1 / 2) x := by
  norm_num [kernelValue, KernelKind.power]

theorem gL_pos : 0 < gL := by
  unfold gL
  decide

theorem gD_pos : 0 < gD := by
  unfold gD
  exact Nat.mul_pos (Nat.mul_pos (pow_pos S_pos _) (Nat.factorial_pos _)) gL_pos

theorem gHorner_cons (T : ℕ) (c : ℕ) (w : List ℕ) :
    gHorner T (c :: w) = (c : ℤ) - (T : ℤ) * gHorner T w := rfl

/-- Horner's rule computes `Σ_k (-T)^k w_k`. -/
theorem gHorner_eq (T : ℕ) (w : List ℕ) :
    gHorner T w = ∑ k ∈ Finset.range w.length, (-(T : ℤ)) ^ k * (w.getD k 0 : ℤ) := by
  induction w with
  | nil => simp [gHorner]
  | cons c w ih =>
    rw [gHorner_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul]
    rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- The exact series value: `gHorner T gWList / gD = Erfc.series (T/S) gN`. -/
theorem gHorner_series (T : ℕ) :
    ((gHorner T gWList : ℤ) : ℚ) / (gD : ℚ) = Erfc.series ((T : ℚ) / (S : ℚ)) gN := by
  rw [gHorner_eq, gWList_length]
  unfold Erfc.series
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have spec := gWList_spec k hk'
  have hS : (0 : ℚ) < S := by exact_mod_cast S_pos
  have hD : (gD : ℚ) = (gWList.getD k 0 : ℚ) * ((S : ℚ) ^ k * (Nat.factorial k : ℚ) * (2 * k + 1)) := by
    exact_mod_cast spec.symm
  have hf : (0 : ℚ) < (Nat.factorial k : ℚ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (0 : ℚ) < 2 * (k : ℚ) + 1 := by positivity
  have hw : (gWList.getD k 0 : ℚ) ≠ 0 := by
    intro h0
    have hpos : (0 : ℚ) < gD := by exact_mod_cast gD_pos
    rw [hD, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [hD, ← neg_div, div_pow]
  field_simp

theorem sqrtPiF_mem : sqrtPiF.Mem (Real.sqrt Real.pi) := FI.sqrt_mem piF_mem

open BravaisCover in
/-- `gPt T` encloses `g(T/S)`. -/
theorem gPt_mem {T : ℕ} (ok : gPtOK T = true) :
    (gPt T).Mem (kernelValue .half ((T : ℝ) / Sz)) := by
  simp only [gPtOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨hroot, hguard⟩ := ok
  have sp := Sz_pos
  set q : ℚ := (T : ℚ) / (S : ℚ) with hq
  have hqR : ((q : ℚ) : ℝ) = (T : ℝ) / Sz := by
    rw [hq]; push_cast; rw [S_eq]
  have hT : (⟨T, T⟩ : FI).Mem ((T : ℝ) / Sz) := ⟨le_rfl, le_rfl⟩
  have hsq := FI.sqrt_mem hT
  have Tpos : 0 < (T : ℝ) / Sz := by
    by_contra hc
    have h0 : (T : ℝ) / Sz = 0 := le_antisymm (not_lt.mp hc) (by positivity)
    rw [h0, Real.sqrt_zero] at hsq
    have := hsq.1
    have : ((FI.sqrt (⟨T, T⟩ : FI)).lo : ℝ) ≤ 0 := by
      have := mul_le_mul_of_nonneg_right this sp.le
      rwa [div_mul_cancel₀ _ sp.ne', zero_mul] at this
    have h' : (0 : ℝ) < (FI.sqrt (⟨T, T⟩ : FI)).lo := by exact_mod_cast hroot
    linarith
  have hq0 : (0 : ℚ) ≤ q := by rw [hq]; positivity
  have hqpos : (0 : ℝ) < (q : ℝ) := by rw [hqR]; exact Tpos
  have guard : q / ((gN + 1 : ℕ) : ℚ) ≤ 1 / 2 := by
    have hS : (0 : ℚ) < (S : ℚ) := by exact_mod_cast S_pos
    rw [hq, div_div, div_le_iff₀ (mul_pos hS (by positivity))]
    have : (2 * T : ℚ) ≤ ((gN + 1) * S : ℕ) := by exact_mod_cast hguard
    push_cast at this ⊢
    linarith
  have rem := Erfc.sqrt_remainder hq0 gN guard
  -- the analytic identity
  have hs := Real.sqrt_pos.mpr hqpos
  have hpi := Real.sqrt_pos.mpr Real.pi_pos
  have form := halfKernel_formula hqpos
  rw [← kernel_half] at form
  set ser : ℝ := (Erfc.series q gN : ℝ)
  have close : |kernelValue .half (q : ℝ) - (Real.sqrt Real.pi * (Real.sqrt (q : ℝ))⁻¹ - 2 * ser)| ≤
      4 * (q : ℝ) ^ gN / (Nat.factorial gN : ℝ) := by
    rw [form]
    have e : Real.sqrt Real.pi * Gaussian.erfcIntegral (Real.sqrt (q : ℝ)) / Real.sqrt (q : ℝ) -
        (Real.sqrt Real.pi * (Real.sqrt (q : ℝ))⁻¹ - 2 * ser) =
        (Real.sqrt Real.pi / Real.sqrt (q : ℝ)) * (Gaussian.erfcIntegral (Real.sqrt (q : ℝ)) -
          (1 - 2 * Real.sqrt (q : ℝ) / Real.sqrt Real.pi * ser)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (div_pos hpi hs)]
    calc Real.sqrt Real.pi / Real.sqrt (q : ℝ) * |Gaussian.erfcIntegral (Real.sqrt (q : ℝ)) -
          (1 - 2 * Real.sqrt (q : ℝ) / Real.sqrt Real.pi * ser)|
        ≤ Real.sqrt Real.pi / Real.sqrt (q : ℝ) *
          (4 * Real.sqrt (q : ℝ) * (q : ℝ) ^ gN / (Real.sqrt Real.pi * (Nat.factorial gN : ℝ))) :=
          mul_le_mul_of_nonneg_left rem (div_pos hpi hs).le
      _ = 4 * (q : ℝ) ^ gN / (Nat.factorial gN : ℝ) := by
          field_simp
  -- the fixed-point pieces
  have hA := FI.mul_mem sqrtPiF_mem (FI.invPos_mem hroot hsq)
  rw [← hqR] at hA
  have hser : ser = ((gHorner T gWList : ℤ) : ℝ) / (gD : ℝ) := by
    simp only [ser]
    rw [← gHorner_series]
    push_cast
    ring
  have hD : (0 : ℤ) < gD := by exact_mod_cast gD_pos
  have hBlo := fdiv_le (gHorner T gWList * Sz) gD hD
  have hBhi := le_cdiv (gHorner T gWList * Sz) gD hD
  have hBmem : (⟨(gHorner T gWList * Sz) / (gD : ℤ), cdivZ (gHorner T gWList * Sz) gD⟩ : FI).Mem ser := by
    have e : ser = (((gHorner T gWList * Sz : ℤ) : ℝ) / ((gD : ℤ) : ℝ)) / Sz := by
      rw [hser]; push_cast; field_simp
    unfold FI.Mem
    rw [e]
    exact ⟨div_le_div_of_nonneg_right hBlo sp.le, div_le_div_of_nonneg_right hBhi sp.le⟩
  have hE : 4 * (q : ℝ) ^ gN / (Nat.factorial gN : ℝ) ≤ (gErr T : ℝ) / Sz := by
    unfold gErr
    have hS : (0 : ℤ) < (S : ℤ) := by exact_mod_cast S_pos
    have hden : (0 : ℤ) < (S : ℤ) ^ (gN - 1) * (Nat.factorial gN : ℤ) :=
      mul_pos (pow_pos hS _) (by exact_mod_cast Nat.factorial_pos gN)
    have hpow : (Sz : ℝ) ^ gN = (Sz : ℝ) ^ (gN - 1) * Sz := by
      rw [← pow_succ, Nat.sub_add_cancel (by norm_num [gN] : 1 ≤ gN)]
    calc 4 * (q : ℝ) ^ gN / (Nat.factorial gN : ℝ)
        = (((4 * (T : ℤ) ^ gN : ℤ) : ℝ) / (((S : ℤ) ^ (gN - 1) * (Nat.factorial gN : ℤ) : ℤ) : ℝ)) / Sz := by
          rw [hqR, div_pow, hpow]
          push_cast
          rw [S_eq]
          field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (le_cdiv _ _ hden) sp.le
  rw [abs_le] at close
  rw [← hqR]
  unfold gPt
  dsimp only
  unfold FI.Mem
  constructor
  · have eq1 : (((sqrtPiF.mul (FI.sqrt ⟨T, T⟩).invPos).lo - 2 * cdivZ (gHorner T gWList * Sz) gD - gErr T : ℤ) : ℝ) / Sz =
        ((sqrtPiF.mul (FI.sqrt ⟨T, T⟩).invPos).lo : ℝ) / Sz -
          2 * (((cdivZ (gHorner T gWList * Sz) gD : ℤ) : ℝ) / Sz) - (gErr T : ℝ) / Sz := by
      push_cast; ring
    rw [eq1]
    have := hBmem.2
    dsimp only at this
    linarith [hA.1, close.1]
  · have eq2 : (((sqrtPiF.mul (FI.sqrt ⟨T, T⟩).invPos).hi - 2 * (gHorner T gWList * Sz / (gD : ℤ)) + gErr T : ℤ) : ℝ) / Sz =
        ((sqrtPiF.mul (FI.sqrt ⟨T, T⟩).invPos).hi : ℝ) / Sz -
          2 * (((gHorner T gWList * Sz / (gD : ℤ) : ℤ) : ℝ) / Sz) + (gErr T : ℝ) / Sz := by
      push_cast; ring
    rw [eq2]
    have := hBmem.1
    dsimp only at this
    linarith [hA.2, close.2]

open BravaisCover in
/-- `g` is decreasing on `(0, ∞)`. -/
theorem kernelValue_half_antitone : AntitoneOn (kernelValue .half) (Set.Ioi 0) := by
  have hd : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (kernelValue .half) (kernelSlope .half x) x :=
    fun x hx => kernelValue_hasDerivAt .half hx
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    rw [(hd x hx).deriv]
    unfold kernelSlope
    have g0 := Stage2.value_nonnegative .half (Set.mem_Ioi.mp hx)
    have e0 := Real.exp_pos (-x)
    have : (0 : ℝ) ≤ ((KernelKind.half.power : ℚ) : ℝ) := by norm_num [KernelKind.power]
    have hx' : (0 : ℝ) < x := hx
    apply div_nonpos_of_nonpos_of_nonneg _ hx'.le
    have := mul_nonneg this g0
    linarith

open BravaisCover in
theorem gRange_mem {A B : ℤ} {x : ℝ} (hx : (⟨A, B⟩ : FI).Mem x) (ok : gRangeOK A B = true) :
    (gRange A B).Mem (kernelValue .half x) := by
  simp only [gRangeOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨hA, okA, okB⟩ := ok
  have sp := Sz_pos
  unfold FI.Mem at hx
  dsimp only at hx
  have hAB : A ≤ B := by
    have := hx.1.trans hx.2
    rw [div_le_div_iff_of_pos_right sp] at this
    exact_mod_cast this
  have eA : ((A.toNat : ℕ) : ℝ) = (A : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hA.le
  have eB : ((B.toNat : ℕ) : ℝ) = (B : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  have pA : (0 : ℝ) < (A : ℝ) / Sz := div_pos (by exact_mod_cast hA) sp
  have pB : (0 : ℝ) < (B : ℝ) / Sz := div_pos (by exact_mod_cast (show (0 : ℤ) < B by omega)) sp
  have px : 0 < x := pA.trans_le hx.1
  have gA := gPt_mem okA
  have gB := gPt_mem okB
  rw [eA] at gA
  rw [eB] at gB
  unfold gRange FI.Mem
  constructor
  · exact gB.1.trans (kernelValue_half_antitone px pB hx.2)
  · exact (kernelValue_half_antitone pA px hx.1).trans gA.2

namespace J2Mem

open BravaisCover in
theorem ghalf {B : Cell} {a : J2} {f : Chart → ℝ} (ha : J2Mem B a f) :
    J2Mem B a.ghalf (fun p => kernelValue .half (f p)) := by
  unfold J2.ghalf
  apply J2Mem.chain ha (φ := kernelValue .half) (φ1 := kernelSlope .half) (φ2 := kernelCurvature .half)
  intro hg x hx
  have hfi := MR.toFI_mem hx
  have hg' := hg
  simp only [gRangeOK, Bool.and_eq_true, decide_eq_true_eq] at hg'
  have h0 : 0 < a.v.lo := hg'.1
  have xpos : 0 < x := pos_of_mem h0 hx
  have hr := FI.invPos_mem (a := a.v.toFI) h0 hfi
  have he := expRange_mem hfi xpos.le
  have hgr := gRange_mem hfi hg
  have hs : (fiNeg (((Fix.expRange a.v.lo a.v.hi).add (fiHalf (gRange a.v.lo a.v.hi))).mul
      a.v.toFI.invPos)).Mem (kernelSlope .half x) := by
    have := fiNeg_mem (FI.mul_mem (FI.add_mem he (fiHalf_mem hgr)) hr)
    convert this using 1
    unfold kernelSlope
    norm_num [KernelKind.power]
    ring
  refine ⟨MR.ofFI_mem hgr, MR.ofFI_mem hs, ?_, kernelValue_hasDerivAt .half xpos,
    kernelSlope_hasDerivAt .half xpos⟩
  have := FI.mul_mem (FI.sub_mem he (fiHalf_mem (FI.smul_mem 3 hs))) hr
  refine MR.ofFI_mem ?_
  convert this using 1
  unfold kernelCurvature
  norm_num [KernelKind.power]
  ring

end J2Mem

end BccSharp.Coulomb.CompactCover.PlanarFibreTri
