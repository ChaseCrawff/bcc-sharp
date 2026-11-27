import BccSharp.Cover.OverlayFix
import BccSharp.Cover.OverlaySoundCheck

set_option autoImplicit false

/-! Soundness of the fixed-point Overlay evaluator `BccSharp.Cover.OverlayFix`.

* Integer rounding and the interval operations: `FI.Mem` and a membership
  lemma per operation (`FI.add_mem`, `FI.mul_mem`, `FI.mulPos_mem`,
  `FI.sq_mem`, `FI.invPos_mem`, `FI.sqrt_mem`, `ofRat_mem`).
* Point values and ranges: the literal Horner coefficients against their
  formulas (`expC_eq`, `cosPosC_eq`, `cosNegC_eq`, by `decide +kernel`), the
  exponential (`expPosPt_mem`, `expNegPt_mem`, `expRange_mem`), the cosine
  (`cosPt_mem` with `twoPi_bounds` and `cosErr_ok`, `cosRange_mem`) and the
  hyperbolic ranges (`hypPt_mem`, `coshRange_mem`, `sinhRange_mem`).
* The layer: both forms of the retained axial terms (`axialCore_three`,
  `axialCore_product`, `coreF_mem`), the axial tail (`tailF_bound`), one wave
  (`waveF_mem`), the retained sum (`retainedF_mem`), the radial tail
  (`radialTail_le`, `radialF_bound`) and the layer (`layerF_mem`).
* The area tangent (`areaF_bound`) and the pass: `fixPass_sound` (the shape of
  `sharpPass_sound`), `energy_fcc_lt_of_fixPass`, `overlayFixCheck` and
  `overlayFixCheck_sound : SoundCheck overlayFixCheck`. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp BccSharp.Coverage DirectRoute
open BccSharp.Intervals (Ball)

/-! ### The scale and rounding -/

theorem Sz_pos : (0:ℝ) < Sz := by norm_num [Sz]
theorem Sz_posZ : (0:ℤ) < Sz := by norm_num [Sz]
theorem S_eq : (S : ℝ) = (Sz : ℝ) := by norm_num [S, Sz]
theorem S_pos : 0 < S := by norm_num [S]
theorem S2_eq : (S2 : ℝ) = (Sz : ℝ) * Sz := by norm_num [S2, Sz]
theorem S64_eq : (S64 : ℝ) = 64 * (Sz : ℝ) := by norm_num [S64, Sz]
theorem halfS_eq : (halfS : ℝ) = (Sz : ℝ) / 2 := by norm_num [halfS, Sz]

theorem fdiv_le (n d : ℤ) (hd : 0 < d) : ((n / d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Int.ediv_mul_le n hd.ne'

theorem lt_fdiv (n d : ℤ) (hd : 0 < d) : (n : ℝ) / d < ((n / d : ℤ) : ℝ) + 1 := by
  rw [div_lt_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Int.lt_ediv_add_one_mul_self n hd

theorem le_cdiv (n d : ℤ) (hd : 0 < d) : (n : ℝ) / d ≤ (cdivZ n d : ℝ) := by
  have h := fdiv_le (-n) d hd
  unfold cdivZ
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

theorem cdivN_ge (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d ≤ (cdivN n d : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have h1 := Nat.div_add_mod (n + d - 1) d
  have h2 := Nat.mod_lt (n + d - 1) hd
  have key : n ≤ (n + d - 1) / d * d := by
    rw [Nat.mul_comm]
    generalize d * ((n + d - 1) / d) = P at h1 ⊢
    omega
  unfold cdivN
  exact_mod_cast key

theorem fdivN_le (n d : ℕ) : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le

/-! ### Intervals -/

/-- `x ∈ [lo/S, hi/S]`. -/
def FI.Mem (a : FI) (x : ℝ) : Prop := (a.lo : ℝ) / Sz ≤ x ∧ x ≤ (a.hi : ℝ) / Sz

namespace FI

theorem add_mem {a b : FI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  unfold Mem add at *
  push_cast
  rw [add_div, add_div]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem sub_mem {a b : FI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.sub b).Mem (x - y) := by
  unfold Mem sub at *
  push_cast
  rw [sub_div, sub_div]
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

theorem ofInt_mem (n : ℤ) : (ofInt n).Mem (n : ℝ) := by
  unfold Mem ofInt
  push_cast
  rw [mul_div_assoc, div_self Sz_pos.ne', mul_one]
  exact ⟨le_rfl, le_rfl⟩

theorem smul_mem (n : ℤ) {a : FI} {x : ℝ} (hx : a.Mem x) : (smul n a).Mem ((n : ℝ) * x) := by
  unfold Mem smul at *
  have p := Sz_pos
  split_ifs with h
  · have h' : (0:ℝ) ≤ n := by exact_mod_cast h
    push_cast
    rw [mul_div_assoc, mul_div_assoc]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 h', mul_le_mul_of_nonneg_left hx.2 h'⟩
  · have h' : (n : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge h))
    push_cast
    rw [mul_div_assoc, mul_div_assoc]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 h', mul_le_mul_of_nonpos_left hx.1 h'⟩

theorem widen_mem {a : FI} {x y : ℝ} (hx : a.Mem x) (k : ℤ) (he : |y - x| ≤ (k : ℝ) / Sz) :
    (a.widen k).Mem y := by
  unfold Mem widen at *
  push_cast
  rw [sub_div, add_div]
  have := abs_le.mp he
  constructor <;> linarith [hx.1, hx.2, this.1, this.2]

/-- Both of two enclosures: their intersection. -/
theorem meet_mem {a b : FI} {x : ℝ} (ha : a.Mem x) (hb : b.Mem x) :
    (⟨max a.lo b.lo, min a.hi b.hi⟩ : FI).Mem x := by
  unfold Mem at *
  have p := Sz_pos
  simp only
  constructor
  · rw [Int.cast_max, ← max_div_div_right p.le]
    exact max_le ha.1 hb.1
  · rw [Int.cast_min, ← min_div_div_right p.le]
    exact le_min ha.2 hb.2

private theorem scalar_range (c a x b : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (c * a) (c * b) ≤ c * x ∧ c * x ≤ max (c * a) (c * b) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ha hc),
      (mul_le_mul_of_nonneg_left hb hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hb (le_of_not_ge hc)),
      (mul_le_mul_of_nonpos_left ha (le_of_not_ge hc)).trans (le_max_left _ _)⟩

/-- The real product lies between the extreme corner products. -/
theorem corner_bounds {xl xh yl yh x y : ℝ} (hx : xl ≤ x ∧ x ≤ xh) (hy : yl ≤ y ∧ y ≤ yh) :
    min (min (xl * yl) (xl * yh)) (min (xh * yl) (xh * yh)) ≤ x * y ∧
      x * y ≤ max (max (xl * yl) (xl * yh)) (max (xh * yl) (xh * yh)) := by
  have l := scalar_range yl xl x xh hx.1 hx.2
  have u := scalar_range yh xl x xh hx.1 hx.2
  have m := scalar_range x yl y yh hy.1 hy.2
  rw [mul_comm yl xl, mul_comm yl xh, mul_comm yl x] at l
  rw [mul_comm yh xl, mul_comm yh xh, mul_comm yh x] at u
  constructor
  · refine le_trans ?_ m.1
    rcases le_total (x * yl) (x * yh) with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_min (min_le_left _ _) (min_le_left _ _)) l.1
    · rw [min_eq_right h]
      exact le_trans (min_le_min (min_le_right _ _) (min_le_right _ _)) u.1
  · refine le_trans m.2 ?_
    rcases le_total (x * yl) (x * yh) with h | h
    · rw [max_eq_right h]
      exact le_trans u.2 (max_le_max (le_max_right _ _) (le_max_right _ _))
    · rw [max_eq_left h]
      exact le_trans l.2 (max_le_max (le_max_left _ _) (le_max_left _ _))

theorem mul_mem {a b : FI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (mul a b).Mem (x * y) := by
  have p := Sz_pos
  have c := corner_bounds hx hy
  have e (u v : ℤ) : ((u : ℝ) / Sz) * ((v : ℝ) / Sz) = ((u * v : ℤ) : ℝ) / Sz / Sz := by
    push_cast; field_simp
  rw [e, e, e, e] at c
  simp only [min_div_div_right p.le, max_div_div_right p.le, ← Int.cast_min, ← Int.cast_max] at c
  unfold Mem mul
  simp only
  constructor
  · exact (div_le_div_of_nonneg_right (fdiv_le _ _ Sz_posZ) p.le).trans c.1
  · exact c.2.trans (div_le_div_of_nonneg_right (le_cdiv _ _ Sz_posZ) p.le)

theorem mulPos_mem {a b : FI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (mulPos a b).Mem (x * y) := by
  unfold mulPos
  split_ifs with h
  · have p := Sz_pos
    have a0 : (0:ℝ) ≤ (a.lo : ℝ) / Sz := div_nonneg (by exact_mod_cast h.1) p.le
    have b0 : (0:ℝ) ≤ (b.lo : ℝ) / Sz := div_nonneg (by exact_mod_cast h.2) p.le
    have e (u v : ℤ) : ((u : ℝ) / Sz) * ((v : ℝ) / Sz) = ((u * v : ℤ) : ℝ) / Sz / Sz := by
      push_cast; field_simp
    constructor
    · refine (div_le_div_of_nonneg_right (fdiv_le _ _ Sz_posZ) p.le).trans ?_
      rw [← e]
      exact mul_le_mul hx.1 hy.1 b0 (a0.trans hx.1)
    · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv _ _ Sz_posZ) p.le)
      rw [← e]
      exact mul_le_mul hx.2 hy.2 (b0.trans hy.1) ((a0.trans hx.1).trans hx.2)
  · exact mul_mem hx hy

theorem sq_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (sq a).Mem (x ^ 2) := by
  have p := Sz_pos
  have e (u : ℤ) : ((u * u : ℤ) : ℝ) / Sz / Sz = ((u : ℝ) / Sz) ^ 2 := by push_cast; field_simp
  have lo (u : ℤ) := (div_le_div_of_nonneg_right (fdiv_le (u * u) _ Sz_posZ) p.le).trans_eq (e u)
  have hi (u : ℤ) := (e u).symm.trans_le (div_le_div_of_nonneg_right (le_cdiv (u * u) _ Sz_posZ) p.le)
  unfold sq Mem
  split_ifs with h₁ h₂
  · have a0 : (0:ℝ) ≤ (a.lo : ℝ) / Sz := div_nonneg (by exact_mod_cast h₁) p.le
    exact ⟨(lo a.lo).trans (pow_le_pow_left₀ a0 hx.1 2),
      (pow_le_pow_left₀ (a0.trans hx.1) hx.2 2).trans (hi a.hi)⟩
  · have b0 : (a.hi : ℝ) / Sz ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h₂) p.le
    constructor
    · refine (lo a.hi).trans ?_
      nlinarith [hx.1, hx.2]
    · refine le_trans ?_ (hi a.lo)
      nlinarith [hx.1, hx.2]
  · constructor
    · simp only [Int.cast_zero, zero_div]
      positivity
    · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv _ _ Sz_posZ) p.le)
      rw [Int.cast_max, ← max_div_div_right p.le, ← max_div_div_right p.le, e, e]
      rcases le_total 0 x with h | h
      · exact (pow_le_pow_left₀ h hx.2 2).trans (le_max_right _ _)
      · refine le_trans ?_ (le_max_left _ _)
        nlinarith [hx.1]

theorem invPos_mem {a : FI} {x : ℝ} (ha : 0 < a.lo) (hx : a.Mem x) : (invPos a).Mem x⁻¹ := by
  have p := Sz_pos
  have l0 : (0:ℝ) < (a.lo : ℝ) / Sz := div_pos (by exact_mod_cast ha) p
  have x0 := l0.trans_le hx.1
  have h0 : (0:ℝ) < (a.hi : ℝ) := by
    have := l0.trans_le (hx.1.trans hx.2)
    exact (div_pos_iff_of_pos_right p).mp this
  have hZ : (0:ℤ) < a.hi := by exact_mod_cast h0
  unfold invPos Mem
  constructor
  · refine (div_le_div_of_nonneg_right (fdiv_le _ _ hZ) p.le).trans ?_
    rw [Int.cast_natCast, S2_eq, show ((Sz : ℝ) * Sz) / a.hi / Sz = ((a.hi : ℝ) / Sz)⁻¹ by field_simp]
    exact inv_anti₀ x0 hx.2
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv _ _ ha) p.le)
    rw [Int.cast_natCast, S2_eq, show ((Sz : ℝ) * Sz) / a.lo / Sz = ((a.lo : ℝ) / Sz)⁻¹ by field_simp]
    exact inv_anti₀ l0 hx.1

end FI

theorem ofRat_mem {l u : ℚ} {x : ℝ} (h : (l : ℝ) ≤ x ∧ x ≤ (u : ℝ)) : (ofRat l u).Mem x := by
  have p := Sz_pos
  have e (q : ℚ) : ((q.num * Sz : ℤ) : ℝ) / ((q.den : ℤ) : ℝ) / Sz = (q : ℝ) := by
    push_cast
    rw [show ((q.num : ℝ) * Sz) / q.den / Sz = (q.num : ℝ) / q.den by field_simp]
    exact_mod_cast Rat.num_div_den q
  unfold ofRat FI.Mem
  constructor
  · refine (div_le_div_of_nonneg_right (fdiv_le _ _ (by exact_mod_cast l.pos)) p.le).trans ?_
    rw [e]
    exact h.1
  · refine h.2.trans ?_
    rw [← e u]
    exact div_le_div_of_nonneg_right (le_cdiv _ _ (by exact_mod_cast u.pos)) p.le

theorem cx_mem {b : Cell} {p : Chart} (hp : b.Mem p) (i : Axis) : (cx b i).Mem (p i) :=
  ofRat_mem (hp i)

/-! ### Square roots -/

theorem sqrtLo_sq (n : ℕ) : sqrtLo n * sqrtLo n ≤ n := by
  unfold sqrtLo
  dsimp only
  split_ifs with h₁ h₂
  · exact h₁
  · exact h₂
  · simp

theorem le_sqrtHi_sq (n : ℕ) : n ≤ sqrtHi n * sqrtHi n := by
  unfold sqrtHi
  dsimp only
  split_ifs with h₁ h₂
  · exact h₁
  · exact h₂
  · nlinarith

theorem FI.sqrt_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (FI.sqrt a).Mem (Real.sqrt x) := by
  have p := Sz_pos
  unfold FI.sqrt FI.Mem
  simp only [Int.cast_natCast]
  constructor
  · have r2 := sqrtLo_sq (a.lo.toNat * S)
    have r0 : (0:ℝ) ≤ (sqrtLo (a.lo.toNat * S) : ℝ) / Sz := by positivity
    rcases le_or_gt a.lo 0 with h | h
    · rw [Int.toNat_eq_zero.mpr h, zero_mul] at r2 ⊢
      have z : sqrtLo 0 = 0 := by nlinarith
      rw [z]
      simp [Real.sqrt_nonneg]
    · have hl : ((a.lo.toNat : ℕ) : ℝ) = (a.lo : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h.le
      apply (Real.le_sqrt r0 ((div_nonneg (by exact_mod_cast h.le) p.le).trans hx.1)).mpr
      refine le_trans ?_ hx.1
      have c : ((sqrtLo (a.lo.toNat * S) : ℝ)) * (sqrtLo (a.lo.toNat * S) : ℝ) ≤
          ((a.lo.toNat : ℕ) : ℝ) * (S : ℝ) := by exact_mod_cast r2
      rw [hl, S_eq] at c
      rw [div_pow, div_le_div_iff₀ (by positivity) p]
      nlinarith
  · have r2 := le_sqrtHi_sq (a.hi.toNat * S)
    have R0 : (0:ℝ) ≤ (sqrtHi (a.hi.toNat * S) : ℝ) / Sz := by positivity
    apply (Real.sqrt_le_left R0).mpr
    have hhi : (a.hi : ℝ) ≤ ((a.hi.toNat : ℕ) : ℝ) := by exact_mod_cast Int.self_le_toNat a.hi
    have c : ((a.hi.toNat : ℕ) : ℝ) * (S : ℝ) ≤
        ((sqrtHi (a.hi.toNat * S) : ℝ)) * (sqrtHi (a.hi.toNat * S) : ℝ) := by exact_mod_cast r2
    rw [S_eq] at c
    refine hx.2.trans ((div_le_div_of_nonneg_right hhi p.le).trans ?_)
    rw [div_pow, div_le_div_iff₀ p (by positivity)]
    nlinarith

/-! ### Horner's rule -/

/-- The value of Horner's rule: `c₀ xᵏ + ⋯ + cₖ`. -/
def hornerVal (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => c * x ^ cs.length + hornerVal x cs

theorem hornerN_aux (x : ℕ) (cs : List ℕ) (acc : ℕ) :
    List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc) (fun c _ ih acc => ih (acc * x + c)) cs acc =
      acc * x ^ cs.length + hornerVal x cs := by
  induction cs generalizing acc with
  | nil => simp [hornerVal]
  | cons c cs ih =>
    change List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc) (fun c _ ih acc => ih (acc * x + c)) cs
      (acc * x + c) = _
    rw [ih, hornerVal, List.length_cons, pow_succ]
    ring

theorem hornerN_eq (x : ℕ) (cs : List ℕ) : hornerN x cs = hornerVal x cs := by
  simpa [hornerN] using hornerN_aux x cs 0

theorem hornerVal_range (x : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    hornerVal x ((List.range n).reverse.map f) = ∑ k ∈ Finset.range n, f k * x ^ k := by
  induction n with
  | zero => simp [hornerVal]
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, hornerVal, ih, Finset.sum_range_succ, List.length_map, List.length_reverse,
      List.length_range]
    ring

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k = ∑ i ∈ Finset.range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-! ### The exponential -/

def expCoef (k : ℕ) : ℕ := S64 ^ (27 - k) * (Nat.factorial 27 / Nat.factorial k)

theorem expC_eq : expC = (List.range 28).reverse.map expCoef := by decide +kernel
theorem expDS_eq : expDS * S = S64 ^ 27 * Nat.factorial 27 := by decide +kernel

theorem expHorner_eq (x : ℕ) :
    ((hornerN x expC : ℕ) : ℝ) =
      ((S64 ^ 27 * Nat.factorial 27 : ℕ) : ℝ) * (SpecialFunctions.taylor ((x : ℚ) / S64) 28 : ℝ) := by
  rw [hornerN_eq, expC_eq, hornerVal_range]
  unfold SpecialFunctions.taylor
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 27 := by simp only [Finset.mem_range] at hk; omega
  unfold expCoef
  rw [Nat.cast_mul, Nat.cast_div (Nat.factorial_dvd_factorial hk') (by positivity)]
  push_cast
  have s0 : (S64 : ℝ) ≠ 0 := by norm_num [S64]
  rw [pow_sub₀ _ s0 hk', div_pow]
  field_simp

/-- Rounded squaring keeps an enclosure `l ≤ e^z S ≤ h` and doubles `z`. -/
theorem sqRounds_mem (n : ℕ) (p : ℕ × ℕ) (z : ℝ)
    (h : (p.1 : ℝ) ≤ Real.exp z * Sz ∧ Real.exp z * Sz ≤ (p.2 : ℝ)) :
    ((sqRounds n p).1 : ℝ) ≤ Real.exp (2 ^ n * z) * Sz ∧
      Real.exp (2 ^ n * z) * Sz ≤ ((sqRounds n p).2 : ℝ) := by
  induction n generalizing p z with
  | zero => simpa [sqRounds] using h
  | succ n ih =>
    have step : sqRounds (n + 1) p = sqRounds n (p.1 * p.1 / S, cdivN (p.2 * p.2) S) := rfl
    rw [step, show (2:ℝ) ^ (n + 1) * z = 2 ^ n * (2 * z) by ring]
    apply ih
    have sp := Sz_pos
    have e : Real.exp (2 * z) * Sz = (Real.exp z * Sz) ^ 2 / Sz := by
      rw [two_mul, Real.exp_add]; field_simp
    have l0 : (0:ℝ) ≤ p.1 := Nat.cast_nonneg _
    rw [e]
    have e0 := Real.exp_pos z
    have lo2 := mul_self_le_mul_self l0 h.1
    have hi2 := mul_self_le_mul_self (by positivity) h.2
    constructor
    · refine (fdivN_le _ _).trans ?_
      push_cast
      rw [S_eq, pow_two]
      exact div_le_div_of_nonneg_right lo2 sp.le
    · refine le_trans ?_ (cdivN_ge _ _ S_pos)
      push_cast
      rw [S_eq, pow_two]
      exact div_le_div_of_nonneg_right hi2 sp.le

theorem expPosPt_mem (x : ℕ) (hx : x ≤ S64) :
    ((expPosPt x).1 : ℝ) ≤ Real.exp ((x : ℝ) / Sz) * Sz ∧
      Real.exp ((x : ℝ) / Sz) * Sz ≤ ((expPosPt x).2 : ℝ) := by
  have sp := Sz_pos
  set y : ℚ := (x : ℚ) / S64 with hy
  have y0 : 0 ≤ y := by positivity
  have y1 : y ≤ 1 := by
    rw [hy, div_le_one (by norm_num [S64])]
    exact_mod_cast hx
  have t := SpecialFunctions.exp_taylor y 28 (by rw [abs_of_nonneg y0]; exact y1) (by norm_num)
  rw [SpecialFunctions.contains_iff_endpoints] at t
  dsimp only at t
  have err : SpecialFunctions.taylorError y 28 ≤ 29 / 8536873649127988094042112000000 := by
    unfold SpecialFunctions.taylorError
    rw [abs_of_nonneg y0, show Nat.factorial 28 = 304888344611713860501504000000 by decide]
    have : y ^ 28 ≤ 1 := pow_le_one₀ y0 y1
    push_cast
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  have errR : ((SpecialFunctions.taylorError y 28 : ℚ) : ℝ) * Sz ≤ 1 := by
    have e2 : ((29 / 8536873649127988094042112000000 : ℚ) : ℝ) * Sz ≤ 1 := by
      norm_num [Sz]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast err) sp.le).trans e2
  -- acc / expDS = taylor · S
  set acc := hornerN x expC with hacc
  have D : ((expDS : ℕ) : ℝ) * Sz = ((S64 ^ 27 * Nat.factorial 27 : ℕ) : ℝ) := by
    rw [← S_eq]; exact_mod_cast expDS_eq
  have Dp : (0:ℝ) < expDS := by norm_num [expDS]
  have val : (acc : ℝ) / expDS = (SpecialFunctions.taylor y 28 : ℝ) * Sz := by
    rw [hacc, expHorner_eq, ← D, ← hy]
    field_simp
  have tl : (SpecialFunctions.taylor y 28 : ℝ) * Sz - (SpecialFunctions.taylorError y 28 : ℝ) * Sz ≤
      Real.exp y * Sz := by
    rw [← sub_mul]; exact mul_le_mul_of_nonneg_right t.1 sp.le
  have tu : Real.exp y * Sz ≤
      (SpecialFunctions.taylor y 28 : ℝ) * Sz + (SpecialFunctions.taylorError y 28 : ℝ) * Sz := by
    rw [← add_mul]; exact mul_le_mul_of_nonneg_right t.2 sp.le
  clear t err
  have ey : Real.exp ((x : ℝ) / Sz) = Real.exp (2 ^ 6 * (y : ℝ)) := by
    congr 1
    rw [hy]
    push_cast
    rw [S64_eq]
    field_simp
    ring
  rw [ey]
  apply sqRounds_mem 6
  constructor
  · rcases Nat.lt_or_ge (acc / expDS) 1 with h | h
    · have : acc / expDS - 1 = 0 := by omega
      rw [this]
      simp only [Nat.cast_zero]
      positivity
    · rw [Nat.cast_sub h, Nat.cast_one]
      have f := fdivN_le acc expDS
      rw [val] at f
      linarith
  · push_cast
    have f := cdivN_ge acc expDS (by exact_mod_cast Dp)
    rw [val] at f
    linarith

theorem expNegPt_mem (x : ℕ) : (expNegPt x).Mem (Real.exp (-((x : ℝ) / Sz))) := by
  have sp := Sz_pos
  have e0 := Real.exp_pos (-((x : ℝ) / Sz))
  have e1 : Real.exp (-((x : ℝ) / Sz)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have fallback : (⟨0, Sz⟩ : FI).Mem (Real.exp (-((x : ℝ) / Sz))) := by
    unfold FI.Mem
    simp only [Int.cast_zero, zero_div]
    rw [div_self sp.ne']
    exact ⟨e0.le, e1⟩
  unfold expNegPt
  dsimp only
  split_ifs with h₁ h₂
  · obtain ⟨l, u⟩ := expPosPt_mem x h₁
    have E := Real.exp_pos ((x : ℝ) / Sz)
    have l0 : (0:ℝ) < (expPosPt x).1 := by exact_mod_cast h₂
    have inv : Real.exp (-((x : ℝ) / Sz)) = (Real.exp ((x : ℝ) / Sz))⁻¹ := Real.exp_neg _
    unfold FI.Mem
    simp only [Int.cast_natCast]
    rw [inv]
    constructor
    · refine (div_le_div_of_nonneg_right (fdivN_le _ _) sp.le).trans ?_
      rw [S2_eq, show (Sz : ℝ) * Sz / ((expPosPt x).2 : ℝ) / Sz = (((expPosPt x).2 : ℝ) / Sz)⁻¹ by
        field_simp]
      exact inv_anti₀ E (by rw [le_div_iff₀ sp]; exact u)
    · refine le_trans ?_ (div_le_div_of_nonneg_right (cdivN_ge _ _ (by exact_mod_cast h₂)) sp.le)
      rw [S2_eq, show (Sz : ℝ) * Sz / ((expPosPt x).1 : ℝ) / Sz = (((expPosPt x).1 : ℝ) / Sz)⁻¹ by
        field_simp]
      exact inv_anti₀ (div_pos l0 sp) (by rw [div_le_iff₀ sp]; exact l)
  · exact fallback
  · exact fallback

theorem expRange_mem {A B : ℤ} {x : ℝ} (hx : (⟨A, B⟩ : FI).Mem x) (x0 : 0 ≤ x) :
    (expRange A B).Mem (Real.exp (-x)) := by
  have sp := Sz_pos
  unfold expRange FI.Mem
  have hB := expNegPt_mem B.toNat
  have hA := expNegPt_mem A.toNat
  constructor
  · refine hB.1.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
    refine hx.2.trans (div_le_div_of_nonneg_right ?_ sp.le)
    exact_mod_cast Int.self_le_toNat B
  · refine (Real.exp_le_exp.mpr (neg_le_neg ?_)).trans hA.2
    rcases le_or_gt A 0 with h | h
    · rw [Int.toNat_eq_zero.mpr h]; simpa using x0
    · have : ((A.toNat : ℕ) : ℝ) = (A : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h.le
      rw [this]
      exact hx.1

/-! ### Cosine -/

theorem iPower_two_mul (j : ℕ) :
    TrigBounds.iPower (2 * j) = ((-1) ^ j, 0) ∧ TrigBounds.iPower (2 * j + 1) = (0, (-1) ^ j) := by
  induction j with
  | zero => simp [TrigBounds.iPower]
  | succ j ih =>
    have e : TrigBounds.iPower (2 * (j + 1)) = ((-1) ^ (j + 1), 0) := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, TrigBounds.iPower, ih.2]
      simp [pow_succ]
    refine ⟨e, ?_⟩
    rw [TrigBounds.iPower, e]
    simp

theorem cosPolynomial_even (q : ℚ) (m : ℕ) :
    TrigBounds.cosPolynomial q (2 * m) =
      ∑ i ∈ Finset.range m, (-1) ^ i * q ^ (2 * i) / ((2 * i).factorial : ℚ) := by
  unfold TrigBounds.cosPolynomial
  rw [sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(iPower_two_mul i).1, (iPower_two_mul i).2]
  simp only [mul_zero, add_zero]
  ring

def cosCoef (j : ℕ) : ℕ := S ^ (2 * (17 - j)) * (Nat.factorial 34 / Nat.factorial (2 * j))

theorem cosPosC_eq : cosPosC = (List.range 9).reverse.map (fun i => cosCoef (2 * i)) := by decide +kernel
theorem cosNegC_eq : cosNegC = (List.range 9).reverse.map (fun i => cosCoef (2 * i + 1)) := by
  decide +kernel
theorem cosDS_eq : cosDS * S = S ^ 34 * Nat.factorial 34 := by decide +kernel

theorem natAbs_sq_real (Q : ℤ) : ((Q.natAbs * Q.natAbs : ℕ) : ℝ) = (Q : ℝ) ^ 2 := by
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, abs_mul_abs_self, pow_two]

/-- The cosine Horner value is `S^34 34!` times the Taylor polynomial of order 36 at `Q/S`. -/
theorem cosHorner_eq (Q : ℤ) :
    (((hornerN (Q.natAbs * Q.natAbs * (Q.natAbs * Q.natAbs)) cosPosC : ℕ) : ℝ) -
      ((Q.natAbs * Q.natAbs * hornerN (Q.natAbs * Q.natAbs * (Q.natAbs * Q.natAbs)) cosNegC : ℕ) : ℝ)) =
    ((S ^ 34 * Nat.factorial 34 : ℕ) : ℝ) * (TrigBounds.cosPolynomial ((Q : ℚ) / S) 36 : ℝ) := by
  have s0 : (S : ℝ) ≠ 0 := by norm_num [S]
  rw [hornerN_eq, hornerN_eq, cosPosC_eq, cosNegC_eq, hornerVal_range, hornerVal_range,
    show (36 : ℕ) = 2 * 18 from rfl, cosPolynomial_even, show (18 : ℕ) = 2 * 9 from rfl, sum_range_two_mul]
  push_cast
  simp only [Nat.cast_natAbs, Int.cast_abs, abs_mul_abs_self]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 8 := by simp only [Finset.mem_range] at hi; omega
  unfold cosCoef
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity),
    Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
  push_cast
  have m1 : ((-1 : ℝ)) ^ (2 * i) = 1 := by rw [pow_mul]; simp
  have m2 : ((-1 : ℝ)) ^ (2 * i + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  rw [m1, m2, show 2 * (17 - 2 * i) = 34 - 4 * i by omega,
    show 2 * (16 - 2 * i) = 34 - (4 * i + 2) by omega, pow_sub₀ _ s0 (by omega),
    pow_sub₀ _ s0 (by omega), show 2 * (2 * i) = 4 * i by ring, show 2 * (2 * i + 1) = 4 * i + 2 by ring,
    div_pow, div_pow]
  field_simp
  ring

theorem twoPi_bounds : (twoPiLo : ℝ) / Sz ≤ 2 * Real.pi ∧ 2 * Real.pi ≤ (twoPiHi : ℝ) / Sz := by
  have h := SpecialFunctions.pi_enclosure
  rw [SpecialFunctions.contains_iff_endpoints] at h
  dsimp only at h
  have sp := Sz_pos
  constructor
  · have c : (twoPiLo : ℝ) / Sz ≤ 2 * (3141592653589793238465 / 10 ^ 21 - 5 / 10 ^ 21 : ℝ) := by
      rw [div_le_iff₀ sp]; norm_num [twoPiLo, Sz]
    push_cast at h
    linarith [h.1]
  · have c : 2 * (3141592653589793238465 / 10 ^ 21 + 5 / 10 ^ 21 : ℝ) ≤ (twoPiHi : ℝ) / Sz := by
      rw [le_div_iff₀ sp]; norm_num [twoPiHi, Sz]
    push_cast at h
    linarith [h.2]

/-- `TrigBounds.error q 36` for `|q| ≤ 16/5`. -/
def cosTaylorBound : ℚ := 2 * (16 / 5) ^ 36 / 371993326789901217467999448150835200000000

theorem cosErr_ok : ((twoPiHi : ℝ) - twoPiLo) / 2 + 1 + (Sz : ℝ) * (cosTaylorBound : ℝ) ≤ cosErr := by
  norm_num [twoPiHi, twoPiLo, Sz, cosErr, cosTaylorBound]

theorem cosPt_mem (r : ℤ) : (cosPt r).Mem (Real.cos (2 * Real.pi * ((r : ℝ) / Sz))) := by
  have sp := Sz_pos
  have fallback : (⟨-Sz, Sz⟩ : FI).Mem (Real.cos (2 * Real.pi * ((r : ℝ) / Sz))) := by
    unfold FI.Mem
    rw [Int.cast_neg, neg_div, div_self sp.ne']
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  unfold cosPt
  dsimp only
  split_ifs with hq
  swap
  · exact fallback
  set n := (r + halfS) / Sz with hn
  set r' := r - n * Sz with hr'
  set Q := twoPiLo * r' / Sz with hQ
  -- exact reduction modulo one turn
  have red : Real.cos (2 * Real.pi * ((r : ℝ) / Sz)) = Real.cos (2 * Real.pi * ((r' : ℝ) / Sz)) := by
    have e : 2 * Real.pi * ((r : ℝ) / Sz) = 2 * Real.pi * ((r' : ℝ) / Sz) + (n : ℝ) * (2 * Real.pi) := by
      rw [hr']; push_cast; field_simp; ring
    rw [e, Real.cos_add_int_mul_two_pi]
  -- |r'| ≤ S/2
  have hs2 : (Sz : ℝ) = 2 * halfS := by rw [halfS_eq]; ring
  have f1 := fdiv_le (r + halfS) Sz Sz_posZ
  have f2 := lt_fdiv (r + halfS) Sz Sz_posZ
  rw [← hn] at f1 f2
  push_cast at f1 f2
  rw [le_div_iff₀ sp] at f1
  rw [div_lt_iff₀ sp] at f2
  have rlo : -(Sz : ℝ) / 2 ≤ r' := by rw [hr']; push_cast; rw [halfS_eq] at f1; linarith
  have rhi : (r' : ℝ) ≤ (Sz : ℝ) / 2 := by rw [hr']; push_cast; rw [halfS_eq] at f2; nlinarith
  have rabs : |(r' : ℝ) / Sz| ≤ 1 / 2 := by
    rw [abs_le]; constructor
    · rw [le_div_iff₀ sp]; linarith
    · rw [div_le_iff₀ sp]; linarith
  -- the rounded point q = Q/S
  set q : ℚ := (Q : ℚ) / S with hq'
  have qR : ((q : ℚ) : ℝ) = (Q : ℝ) / Sz := by rw [hq']; push_cast; rw [S_eq]
  have g1 := fdiv_le (twoPiLo * r') Sz Sz_posZ
  have g2 := lt_fdiv (twoPiLo * r') Sz Sz_posZ
  rw [← hQ] at g1 g2
  push_cast at g1 g2
  obtain ⟨tl, th⟩ := twoPi_bounds
  have close : |2 * Real.pi * ((r' : ℝ) / Sz) - q| ≤ (((twoPiHi : ℝ) - twoPiLo) / 2 + 1) / Sz := by
    rw [qR]
    have d0 : 0 ≤ 2 * Real.pi - (twoPiLo : ℝ) / Sz := by linarith
    have d1 : 2 * Real.pi - (twoPiLo : ℝ) / Sz ≤ ((twoPiHi : ℝ) - twoPiLo) / Sz := by
      rw [sub_div]; linarith
    have split : 2 * Real.pi * ((r' : ℝ) / Sz) - (Q : ℝ) / Sz =
        (2 * Real.pi - (twoPiLo : ℝ) / Sz) * ((r' : ℝ) / Sz) + ((twoPiLo : ℝ) * r' / Sz - Q) / Sz := by
      field_simp; ring
    rw [split]
    have a1 : |(2 * Real.pi - (twoPiLo : ℝ) / Sz) * ((r' : ℝ) / Sz)| ≤ ((twoPiHi : ℝ) - twoPiLo) / Sz / 2 := by
      rw [abs_mul, abs_of_nonneg d0]
      calc _ ≤ ((twoPiHi : ℝ) - twoPiLo) / Sz * (1 / 2) :=
            mul_le_mul d1 rabs (abs_nonneg _) (d0.trans d1)
        _ = _ := by ring
    have a2 : |((twoPiLo : ℝ) * r' / Sz - Q) / Sz| ≤ 1 / Sz := by
      rw [abs_div, abs_of_pos sp]
      apply div_le_div_of_nonneg_right _ sp.le
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ((twoPiHi : ℝ) - twoPiLo) / Sz / 2 + 1 / Sz := add_le_add a1 a2
      _ = _ := by field_simp
  -- Taylor at q
  have qabs : |q| ≤ 16 / 5 := by
    have hQ' : |(Q : ℚ)| ≤ (qMax : ℚ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hq
    have s0 : (0:ℚ) < S := by norm_num [S]
    rw [hq', abs_div, abs_of_pos s0, div_le_iff₀ s0]
    refine hQ'.trans ?_
    norm_num [qMax, S]
  have tp := TrigBounds.cos_point q 36 (by norm_num) (by
    rw [div_le_iff₀ (by norm_num)]; push_cast; linarith)
  rw [SpecialFunctions.contains_iff_endpoints] at tp
  dsimp only at tp
  have terr : TrigBounds.error q 36 ≤ cosTaylorBound := by
    unfold TrigBounds.error cosTaylorBound
    rw [show Nat.factorial 36 = 371993326789901217467999448150835200000000 by decide]
    push_cast
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have := pow_le_pow_left₀ (abs_nonneg q) qabs 36
    linarith
  have terrR : ((TrigBounds.error q 36 : ℚ) : ℝ) ≤ (cosTaylorBound : ℝ) := by exact_mod_cast terr
  -- the Horner value
  have D : ((cosDS : ℕ) : ℝ) * Sz = ((S ^ 34 * Nat.factorial 34 : ℕ) : ℝ) := by
    rw [← S_eq]; exact_mod_cast cosDS_eq
  have Dp : (0:ℝ) < cosDS := by norm_num [cosDS]
  set acc : ℤ := ((hornerN (Q.natAbs * Q.natAbs * (Q.natAbs * Q.natAbs)) cosPosC : ℕ) : ℤ) -
    ((Q.natAbs * Q.natAbs * hornerN (Q.natAbs * Q.natAbs * (Q.natAbs * Q.natAbs)) cosNegC : ℕ) : ℤ) with hacc
  have val : (acc : ℝ) / (cosDS : ℕ) = (TrigBounds.cosPolynomial q 36 : ℝ) * Sz := by
    rw [hacc]
    simp only [Int.cast_sub, Int.cast_natCast]
    rw [cosHorner_eq, ← D, ← hq']
    field_simp
  have lip := Real.abs_cos_sub_cos_le (2 * Real.pi * ((r' : ℝ) / Sz)) q
  have ce := cosErr_ok
  unfold FI.Mem
  rw [red]
  have cZ : ((cosDS : ℕ) : ℤ) > 0 := by norm_num [cosDS]
  have c := mul_le_mul_of_nonneg_right close sp.le
  rw [div_mul_cancel₀ _ sp.ne'] at c
  have d := mul_le_mul_of_nonneg_right terrR sp.le
  constructor
  · push_cast
    have fl := fdiv_le acc (cosDS : ℕ) cZ
    push_cast at fl
    rw [val] at fl
    rw [div_le_iff₀ sp]
    have a := mul_le_mul_of_nonneg_right tp.1 sp.le
    have b := mul_le_mul_of_nonneg_right (abs_le.mp lip).1 sp.le
    rw [sub_mul] at a b
    rw [neg_mul] at b
    linarith
  · push_cast
    have cl := le_cdiv acc (cosDS : ℕ) cZ
    push_cast at cl
    rw [val] at cl
    rw [le_div_iff₀ sp]
    have a := mul_le_mul_of_nonneg_right tp.2 sp.le
    have b := mul_le_mul_of_nonneg_right (abs_le.mp lip).2 sp.le
    rw [add_mul] at a
    rw [sub_mul] at b
    linarith

theorem cos_turns (x : ℝ) (k : ℤ) : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * (x - k)) := by
  rw [show 2 * Real.pi * x = 2 * Real.pi * (x - k) + (k : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi]

theorem cos_half_turn (x : ℝ) (k : ℤ) :
    Real.cos (2 * Real.pi * (x - k) - Real.pi) = -Real.cos (2 * Real.pi * x) := by
  rw [Real.cos_sub_pi, cos_turns x k]

/-- The range rule of `cosRange`: an endpoint minimum between two odd multiples of
`1/2`, an endpoint maximum between two consecutive integers. -/
theorem cosRange_mem {A B : ℤ} {v : ℝ} (hv : (⟨A, B⟩ : FI).Mem v) :
    (cosRange A B).Mem (Real.cos (2 * Real.pi * v)) := by
  have sp := Sz_pos
  have pi0 := Real.pi_pos
  have pA := cosPt_mem A
  have pB := cosPt_mem B
  unfold FI.Mem at hv pA pB
  unfold cosRange FI.Mem
  dsimp only
  constructor
  · split_ifs with h
    · set k := (A + halfS) / Sz
      have hlo : ((k * Sz - halfS : ℤ) : ℝ) ≤ A := by exact_mod_cast h.1
      have hhi : (B : ℝ) ≤ ((k * Sz + halfS : ℤ) : ℝ) := by exact_mod_cast h.2
      push_cast at hlo hhi
      rw [halfS_eq] at hlo hhi
      have a1 : -(1 / 2 : ℝ) ≤ (A : ℝ) / Sz - k := by
        rw [le_sub_iff_add_le, le_div_iff₀ sp]; linarith
      have b1 : (B : ℝ) / Sz - k ≤ 1 / 2 := by
        rw [sub_le_iff_le_add, div_le_iff₀ sp]; linarith
      have wl : -Real.pi ≤ 2 * Real.pi * ((A : ℝ) / Sz - k) := by nlinarith
      have wh : 2 * Real.pi * ((B : ℝ) / Sz - k) ≤ Real.pi := by nlinarith
      have wy : 2 * Real.pi * ((A : ℝ) / Sz - k) ≤ 2 * Real.pi * (v - k) ∧
          2 * Real.pi * (v - k) ≤ 2 * Real.pi * ((B : ℝ) / Sz - k) := by
        constructor <;> apply mul_le_mul_of_nonneg_left _ (by positivity) <;> linarith [hv.1, hv.2]
      have c := cos_window_lower wl wh wy
      rw [← cos_turns, ← cos_turns, ← cos_turns] at c
      rw [Int.cast_min, ← min_div_div_right sp.le]
      exact (min_le_min pA.1 pB.1).trans c
    · rw [Int.cast_neg, neg_div, div_self sp.ne']; exact Real.neg_one_le_cos _
  · split_ifs with h
    · set k := A / Sz
      have f := fdiv_le A Sz Sz_posZ
      have hhi : (B : ℝ) ≤ ((k * Sz + Sz : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at hhi
      have a1 : (0 : ℝ) ≤ (A : ℝ) / Sz - k := by linarith
      have b1 : (B : ℝ) / Sz - k ≤ 1 := by
        rw [sub_le_iff_le_add, div_le_iff₀ sp]; linarith
      have wl : -Real.pi ≤ 2 * Real.pi * ((A : ℝ) / Sz - k) - Real.pi := by nlinarith
      have wh : 2 * Real.pi * ((B : ℝ) / Sz - k) - Real.pi ≤ Real.pi := by nlinarith
      have wy : 2 * Real.pi * ((A : ℝ) / Sz - k) - Real.pi ≤ 2 * Real.pi * (v - k) - Real.pi ∧
          2 * Real.pi * (v - k) - Real.pi ≤ 2 * Real.pi * ((B : ℝ) / Sz - k) - Real.pi := by
        constructor <;> apply sub_le_sub_right <;> apply mul_le_mul_of_nonneg_left _ (by positivity) <;>
          linarith [hv.1, hv.2]
      have c := cos_window_lower wl wh wy
      rw [cos_half_turn, cos_half_turn, cos_half_turn, min_neg_neg, neg_le_neg_iff] at c
      rw [Int.cast_max, ← max_div_div_right sp.le]
      exact c.trans (max_le_max pA.2 pB.2)
    · rw [div_self sp.ne']; exact Real.cos_le_one _

/-! ### Hyperbolic functions -/

theorem hypPt_mem (n : ℕ) (hn : n ≤ S64) :
    (hypPt n).1.Mem (Real.cosh ((n : ℝ) / Sz)) ∧ (hypPt n).2.Mem (Real.sinh ((n : ℝ) / Sz)) := by
  have sp := Sz_pos
  obtain ⟨l, u⟩ := expPosPt_mem n hn
  have en := expNegPt_mem n
  unfold FI.Mem at en
  have l' : ((expPosPt n).1 : ℝ) / Sz ≤ Real.exp ((n : ℝ) / Sz) := by rw [div_le_iff₀ sp]; exact l
  have u' : Real.exp ((n : ℝ) / Sz) ≤ ((expPosPt n).2 : ℝ) / Sz := by rw [le_div_iff₀ sp]; exact u
  have t2 : (0:ℤ) < 2 := by norm_num
  unfold hypPt FI.Mem
  dsimp only
  rw [Real.cosh_eq, Real.sinh_eq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine (div_le_div_of_nonneg_right (fdiv_le _ 2 t2) sp.le).trans ?_
    push_cast
    calc (((expPosPt n).1 : ℝ) + (expNegPt n).lo) / 2 / Sz =
          (((expPosPt n).1 : ℝ) / Sz + ((expNegPt n).lo : ℝ) / Sz) / 2 := by ring
      _ ≤ _ := by linarith [en.1]
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv _ 2 t2) sp.le)
    push_cast
    calc _ ≤ (((expPosPt n).2 : ℝ) / Sz + ((expNegPt n).hi : ℝ) / Sz) / 2 := by linarith [en.2]
      _ = _ := by ring
  · refine (div_le_div_of_nonneg_right (fdiv_le _ 2 t2) sp.le).trans ?_
    push_cast
    calc (((expPosPt n).1 : ℝ) - (expNegPt n).hi) / 2 / Sz =
          (((expPosPt n).1 : ℝ) / Sz - ((expNegPt n).hi : ℝ) / Sz) / 2 := by ring
      _ ≤ _ := by linarith [en.2]
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv _ 2 t2) sp.le)
    push_cast
    calc _ ≤ (((expPosPt n).2 : ℝ) / Sz - ((expNegPt n).lo : ℝ) / Sz) / 2 := by linarith [en.1]
      _ = _ := by ring

theorem natAbs_div (A : ℤ) : ((A.natAbs : ℕ) : ℝ) / Sz = |(A : ℝ) / Sz| := by
  rw [abs_div, abs_of_pos Sz_pos, Nat.cast_natAbs, Int.cast_abs]

theorem coshRange_mem {A B : ℤ} {z : ℝ} (hz : (⟨A, B⟩ : FI).Mem z) (hA : A.natAbs ≤ S64)
    (hB : B.natAbs ≤ S64) : (coshRange A B).Mem (Real.cosh z) := by
  have sp := Sz_pos
  unfold FI.Mem at hz
  dsimp only at hz
  unfold coshRange FI.Mem
  dsimp only
  constructor
  · split_ifs with h
    · rw [div_self sp.ne']; exact Real.one_le_cosh z
    · have m := (hypPt_mem (min A.natAbs B.natAbs) ((min_le_left _ _).trans hA)).1.1
      refine m.trans (Real.cosh_le_cosh.mpr ?_)
      rw [abs_of_nonneg (by positivity)]
      rcases not_and_or.mp h with h | h
      · have hA0 : (0 : ℝ) < A := by exact_mod_cast lt_of_not_ge h
        have z0 : 0 < z := (div_pos hA0 sp).trans_le hz.1
        rw [abs_of_pos z0]
        refine le_trans ?_ hz.1
        rw [← abs_of_pos (div_pos hA0 sp), ← natAbs_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) sp.le
      · have hB0 : (B : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
        have z0 : z < 0 := hz.2.trans_lt (div_neg_of_neg_of_pos hB0 sp)
        rw [abs_of_neg z0]
        have : ((B.natAbs : ℕ) : ℝ) / Sz = -((B : ℝ) / Sz) := by
          rw [natAbs_div, abs_of_neg (div_neg_of_neg_of_pos hB0 sp)]
        refine le_trans ?_ (neg_le_neg hz.2)
        rw [← this]
        exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) sp.le
  · have m := (hypPt_mem _ (max_le hA hB)).1.2
    refine (Real.cosh_le_cosh.mpr ?_).trans m
    rw [abs_of_nonneg (show (0:ℝ) ≤ ((max A.natAbs B.natAbs : ℕ) : ℝ) / Sz by positivity)]
    have e : (((max A.natAbs B.natAbs : ℕ) : ℝ)) / Sz = max |(A : ℝ) / Sz| |(B : ℝ) / Sz| := by
      rw [Nat.cast_max, ← max_div_div_right sp.le, natAbs_div, natAbs_div]
    rw [e]
    exact abs_le_max_abs_abs hz.1 hz.2

theorem sinhRange_mem {A B : ℤ} {z : ℝ} (hz : (⟨A, B⟩ : FI).Mem z) (hA : A.natAbs ≤ S64)
    (hB : B.natAbs ≤ S64) : (sinhRange A B).Mem (Real.sinh z) := by
  have sp := Sz_pos
  unfold FI.Mem at hz
  dsimp only at hz
  have mA := hypPt_mem _ hA
  have mB := hypPt_mem _ hB
  unfold FI.Mem at mA mB
  unfold sinhRange FI.Mem
  dsimp only
  constructor
  · refine le_trans ?_ (Real.sinh_le_sinh.mpr hz.1)
    split_ifs with h
    · have : ((A.natAbs : ℕ) : ℝ) / Sz = (A : ℝ) / Sz := by
        rw [natAbs_div, abs_of_nonneg (div_nonneg (by exact_mod_cast h) sp.le)]
      rw [← this]; exact mA.2.1
    · have hA0 : (A : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      have : (A : ℝ) / Sz = -(((A.natAbs : ℕ) : ℝ) / Sz) := by
        rw [natAbs_div, abs_of_neg (div_neg_of_neg_of_pos hA0 sp), neg_neg]
      rw [this, Real.sinh_neg, Int.cast_neg, neg_div]
      exact neg_le_neg mA.2.2
  · refine (Real.sinh_le_sinh.mpr hz.2).trans ?_
    split_ifs with h
    · have : ((B.natAbs : ℕ) : ℝ) / Sz = (B : ℝ) / Sz := by
        rw [natAbs_div, abs_of_nonneg (div_nonneg (by exact_mod_cast h) sp.le)]
      rw [← this]; exact mB.2.2
    · have hB0 : (B : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      have : (B : ℝ) / Sz = -(((B.natAbs : ℕ) : ℝ) / Sz) := by
        rw [natAbs_div, abs_of_neg (div_neg_of_neg_of_pos hB0 sp), neg_neg]
      rw [this, Real.sinh_neg, Int.cast_neg, neg_div]
      exact neg_le_neg mB.2.1

/-! ### Small interval facts -/

theorem FI.smul2_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (FI.smul 2 a).Mem (2 * x) := by
  simpa using FI.smul_mem 2 hx

theorem half_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (⟨a.lo / 2, cdivZ a.hi 2⟩ : FI).Mem (x / 2) := by
  have sp := Sz_pos
  unfold FI.Mem at *
  dsimp only
  have t2 : (0:ℤ) < 2 := by norm_num
  constructor
  · refine (div_le_div_of_nonneg_right (fdiv_le _ 2 t2) sp.le).trans ?_
    push_cast
    calc (a.lo : ℝ) / 2 / Sz = (a.lo : ℝ) / Sz / 2 := by ring
      _ ≤ x / 2 := div_le_div_of_nonneg_right hx.1 (by norm_num)
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv _ 2 t2) sp.le)
    push_cast
    calc x / 2 ≤ (a.hi : ℝ) / Sz / 2 := div_le_div_of_nonneg_right hx.2 (by norm_num)
      _ = (a.hi : ℝ) / 2 / Sz := by ring

theorem shift_mem {a : FI} {x : ℝ} (hx : a.Mem x) (q : ℤ) :
    (⟨a.lo - q, a.hi - q⟩ : FI).Mem (x - (q : ℝ) / Sz) := by
  unfold FI.Mem at *
  dsimp only
  push_cast
  rw [sub_div, sub_div]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem quarter_eq : ((Sz / 4 : ℤ) : ℝ) / Sz = 1 / 4 := by norm_num [Sz]

theorem FI.lo_le {a : FI} {x : ℝ} (hx : a.Mem x) : (a.lo : ℝ) / Sz ≤ x := hx.1

/-! ### Wave operands on the seam-shifted cell -/

theorem twoPiF_mem : twoPiF.Mem (2 * Real.pi) := ⟨twoPi_bounds.1, twoPi_bounds.2⟩

/-- The positivity checks on the two diagonal coordinates and their product. -/
structure Guards (b : Cell) : Prop where
  r₀ : 0 < (cx b 0).lo
  r₁ : 0 < (cx b 1).lo
  r₀₁ : 0 < (FI.mulPos (cx b 0) (cx b 1)).lo

section Wave
variable {b : Cell} {p : Chart}

theorem cF_mem (hp : b.Mem p) (g : Guards b) : (cF b).Mem (cReal p) := by
  unfold cF cReal
  exact FI.invPos_mem g.r₀₁ (FI.mulPos_mem (cx_mem hp 0) (cx_mem hp 1))

theorem kappaSqF_mem (hp : b.Mem p) (g : Guards b) (m : Wave) : (kappaSqF b m).Mem (κSq p m) := by
  unfold kappaSqF κSq
  exact FI.add_mem (FI.sq_mem (FI.smul_mem m.1 (FI.invPos_mem g.r₀ (cx_mem hp 0))))
    (FI.sq_mem (FI.mul_mem (FI.sub_mem (FI.ofInt_mem m.2) (FI.smul_mem m.1 (cx_mem hp 2)))
      (FI.invPos_mem g.r₁ (cx_mem hp 1))))

theorem kappaF_mem (hp : b.Mem p) (g : Guards b) (m : Wave) : (kappaF b m).Mem (κReal p m) :=
  FI.sqrt_mem (kappaSqF_mem hp g m)

theorem tF_mem (hp : b.Mem p) (g : Guards b) (m : Wave) : (tF b m).Mem (tReal p m) := by
  unfold tF tReal
  exact FI.mulPos_mem (FI.mulPos_mem twoPiF_mem (cF_mem hp g)) (kappaF_mem hp g m)

theorem wF_mem (hp : b.Mem p) (m : Wave) : (wF b m).Mem (wReal p m) := by
  unfold wF wReal
  exact FI.add_mem (FI.smul_mem _ (FI.sub_mem (cx_mem hp 3) (FI.mul_mem (cx_mem hp 2) (cx_mem hp 4))))
    (FI.smul_mem _ (cx_mem hp 4))

theorem uF_mem (hp : b.Mem p) (m : Wave) : (uF b m).Mem (uReal p m) := by
  unfold uF uReal
  exact FI.add_mem (FI.smul_mem _ (cx_mem hp 5)) (FI.smul_mem _ (cx_mem hp 6))

theorem gF_mem (hp : b.Mem p) : (gF b).Mem (1 - p 7) := by
  have h := cx_mem hp 7
  have sp := Sz_pos
  unfold gF FI.Mem at *
  dsimp only
  push_cast
  rw [sub_div, sub_div, div_self sp.ne']
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

theorem deltaF_mem (hp : b.Mem p) : (deltaF b).Mem (p 7 - 1 / 2) := by
  have h := cx_mem hp 7
  have sp := Sz_pos
  have e : (halfS : ℝ) / Sz = 1 / 2 := by rw [halfS_eq]; field_simp
  unfold deltaF FI.Mem at *
  dsimp only
  push_cast
  rw [sub_div, sub_div, e]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The spacing `η = etaN/S` lies below the height and its complement. -/
theorem eta_bounds (hp : b.Mem p) (η0 : 0 < etaN b) :
    0 < (etaN b : ℝ) / Sz ∧ (etaN b : ℝ) / Sz ≤ p 7 ∧ p 7 ≤ 1 - (etaN b : ℝ) / Sz := by
  have h := cx_mem hp 7
  have sp := Sz_pos
  unfold FI.Mem at h
  unfold etaN at η0 ⊢
  have mpos : 0 < min (cx b 7).lo (Sz - (cx b 7).hi) := by
    by_contra hc
    rw [Int.toNat_eq_zero.mpr (le_of_not_gt hc)] at η0
    exact lt_irrefl _ η0
  have e : (((min (cx b 7).lo (Sz - (cx b 7).hi)).toNat : ℕ) : ℝ) =
      ((min (cx b 7).lo (Sz - (cx b 7).hi) : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg mpos.le
  rw [e]
  refine ⟨div_pos (by exact_mod_cast mpos) sp, ?_, ?_⟩
  · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) sp.le) h.1
  · have m : ((min (cx b 7).lo (Sz - (cx b 7).hi) : ℤ) : ℝ) ≤ (Sz : ℝ) - (cx b 7).hi := by
      exact_mod_cast min_le_right _ _
    have := div_le_div_of_nonneg_right m sp.le
    rw [sub_div, div_self sp.ne'] at this
    linarith [h.2]

/-! ### The two forms of the retained axial terms -/

theorem axialCore_three (t w u h : ℝ) :
    axialCore t w u h = 2 * (Real.exp (-t) * Real.cos (2 * Real.pi * w)) +
      (Real.exp (-(t * h)) * Real.cos (2 * Real.pi * (u + h * w)) +
        Real.exp (-(t * (1 - h))) * Real.cos (2 * Real.pi * (u - (1 - h) * w))) := by
  rw [← axialPair_zero]
  unfold axialPair axialTerm
  simp only [Nat.cast_zero, zero_add]
  have c : Real.cos (2 * Real.pi * (-1 * w)) = Real.cos (2 * Real.pi * (1 * w)) := by
    rw [show 2 * Real.pi * (-1 * w) = -(2 * Real.pi * (1 * w)) by ring, Real.cos_neg]
  rw [c]
  ring_nf

theorem axialCore_product (t w u h : ℝ) :
    axialCore t w u h = 2 * (Real.exp (-t) * Real.cos (2 * Real.pi * w)) +
      2 * (Real.exp (-(t / 2)) *
        (Real.cosh (t * (h - 1 / 2)) * Real.cos (2 * Real.pi * (w / 2)) *
            Real.cos (2 * Real.pi * (u + w * (h - 1 / 2))) +
          Real.sinh (t * (h - 1 / 2)) * Real.cos (2 * Real.pi * (w / 2 - 1 / 4)) *
            Real.cos (2 * Real.pi * (u + w * (h - 1 / 2) - 1 / 4)))) := by
  unfold axialCore coshExp sinhExp
  dsimp only
  rw [← Real.cosh_eq, ← Real.sinh_eq]
  have c1 : Real.cos (2 * (Real.pi * w)) = Real.cos (2 * Real.pi * w) := by ring_nf
  have c2 : Real.cos (Real.pi * w) = Real.cos (2 * Real.pi * (w / 2)) := by ring_nf
  have s1 : Real.sin (Real.pi * w) = Real.cos (2 * Real.pi * (w / 2 - 1 / 4)) := by
    rw [show 2 * Real.pi * (w / 2 - 1 / 4) = Real.pi * w - Real.pi / 2 by ring, Real.cos_sub_pi_div_two]
  have s2 : Real.sin (2 * Real.pi * (u + w * (h - 1 / 2))) =
      Real.cos (2 * Real.pi * (u + w * (h - 1 / 2) - 1 / 4)) := by
    rw [show 2 * Real.pi * (u + w * (h - 1 / 2) - 1 / 4) = 2 * Real.pi * (u + w * (h - 1 / 2)) - Real.pi / 2 by
      ring, Real.cos_sub_pi_div_two]
  rw [c1, c2, s1, s2, neg_div]
  ring

theorem core₁_mem (hp : b.Mem p) (g : Guards b) (m : Wave) (t0 : 0 ≤ tReal p m)
    (h0 : 0 ≤ p 7) (h1 : p 7 ≤ 1) :
    (core₁ b m).Mem (axialCore (tReal p m) (wReal p m) (uReal p m) (p 7)) := by
  have ht := tF_mem hp g m
  have hw := wF_mem hp m
  have hu := uF_mem hp m
  have hh := cx_mem hp 7
  have hg := gF_mem hp
  rw [axialCore_three]
  exact FI.add_mem (FI.smul2_mem (FI.mul_mem (expRange_mem ht t0) (cosRange_mem hw)))
    (FI.add_mem (FI.mul_mem (expRange_mem (FI.mulPos_mem ht hh) (mul_nonneg t0 h0))
      (cosRange_mem (FI.add_mem hu (FI.mul_mem hh hw))))
      (FI.mul_mem (expRange_mem (FI.mulPos_mem ht hg) (mul_nonneg t0 (by linarith)))
        (cosRange_mem (FI.sub_mem hu (FI.mul_mem hg hw)))))

theorem core₂_mem (hp : b.Mem p) (g : Guards b) (m : Wave) (t0 : 0 ≤ tReal p m)
    (zlo : (FI.mul (tF b m) (deltaF b)).lo.natAbs ≤ S64) (zhi : (FI.mul (tF b m) (deltaF b)).hi.natAbs ≤ S64) :
    (core₂ b m).Mem (axialCore (tReal p m) (wReal p m) (uReal p m) (p 7)) := by
  have ht := tF_mem hp g m
  have hw := wF_mem hp m
  have hu := uF_mem hp m
  have hd := deltaF_mem hp
  have hz := FI.mul_mem ht hd
  have hg := half_mem hw
  have hφ := FI.add_mem hu (FI.mul_mem hw hd)
  have hq := quarter_eq
  rw [axialCore_product]
  unfold core₂
  dsimp only
  refine FI.add_mem (FI.smul2_mem (FI.mul_mem (expRange_mem ht t0) (cosRange_mem hw)))
    (FI.smul2_mem (FI.mul_mem (expRange_mem (half_mem ht) (by linarith)) (FI.add_mem
      (FI.mul_mem (FI.mul_mem (coshRange_mem hz zlo zhi) (cosRange_mem hg)) (cosRange_mem hφ))
      (FI.mul_mem (FI.mul_mem (sinhRange_mem hz zlo zhi) ?_) ?_))))
  · have := cosRange_mem (shift_mem hg (Sz / 4))
    rwa [hq] at this
  · have := cosRange_mem (shift_mem hφ (Sz / 4))
    rwa [hq] at this

theorem coreF_mem (hp : b.Mem p) (g : Guards b) (m : Wave) (t0 : 0 ≤ tReal p m)
    (h0 : 0 ≤ p 7) (h1 : p 7 ≤ 1)
    (zlo : (FI.mul (tF b m) (deltaF b)).lo.natAbs ≤ S64) (zhi : (FI.mul (tF b m) (deltaF b)).hi.natAbs ≤ S64) :
    (coreF b m).Mem (axialCore (tReal p m) (wReal p m) (uReal p m) (p 7)) :=
  FI.meet_mem (core₁_mem hp g m t0 h0 h1) (core₂_mem hp g m t0 zlo zhi)

/-! ### The axial tail and one wave -/

theorem tailF_bound (m : Wave) (A1 : (expNegPt (tF b m).lo.toNat).hi < Sz) :
    axialTail (((tF b m).lo.toNat : ℕ) / Sz) ((etaN b : ℝ) / Sz) ≤ (tailF b m : ℝ) / Sz := by
  have sp := Sz_pos
  set t0N := (tF b m).lo.toNat with ht0N
  set t₀ : ℝ := (t0N : ℝ) / Sz with ht₀
  set η : ℝ := (etaN b : ℝ) / Sz with hη
  set A := (expNegPt t0N).hi with hA
  set B := (expNegPt (t0N * etaN b / S)).hi with hB
  have eA : Real.exp (-t₀) ≤ (A : ℝ) / Sz := (expNegPt_mem t0N).2
  have eB : Real.exp (-(t₀ * η)) ≤ (B : ℝ) / Sz := by
    refine le_trans (Real.exp_le_exp.mpr (neg_le_neg ?_)) (expNegPt_mem _).2
    rw [ht₀, hη]
    refine (div_le_div_of_nonneg_right (fdivN_le _ _) sp.le).trans_eq ?_
    push_cast
    rw [S_eq]
    field_simp
  have A1' : (A : ℝ) / Sz < 1 := by rw [div_lt_one sp]; exact_mod_cast A1
  have e0 := Real.exp_pos (-t₀)
  have e1 := Real.exp_pos (-(t₀ * η))
  unfold axialTail axialNumerator
  have num : 2 * Real.exp (-2 * t₀) + 2 * Real.exp (-(1 + η) * t₀) ≤
      2 * ((A : ℝ) / Sz) ^ 2 + 2 * ((A : ℝ) / Sz) * ((B : ℝ) / Sz) := by
    rw [show -2 * t₀ = -t₀ + -t₀ by ring, Real.exp_add, show -(1 + η) * t₀ = -t₀ + -(t₀ * η) by ring,
      Real.exp_add]
    have := mul_le_mul eA eA e0.le (e0.le.trans eA)
    have := mul_le_mul eA eB e1.le (e0.le.trans eA)
    nlinarith
  have den : 1 - (A : ℝ) / Sz ≤ 1 - Real.exp (-t₀) := by linarith
  have den0 : 0 < 1 - (A : ℝ) / Sz := by linarith
  have A0 : 0 ≤ (A : ℝ) / Sz := e0.le.trans eA
  have B0 : 0 ≤ (B : ℝ) / Sz := e1.le.trans eB
  have n0 : 0 ≤ 2 * ((A : ℝ) / Sz) ^ 2 + 2 * ((A : ℝ) / Sz) * ((B : ℝ) / Sz) := by
    have := mul_nonneg A0 B0
    nlinarith [sq_nonneg ((A : ℝ) / Sz)]
  calc _ ≤ (2 * ((A : ℝ) / Sz) ^ 2 + 2 * ((A : ℝ) / Sz) * ((B : ℝ) / Sz)) / (1 - (A : ℝ) / Sz) :=
        div_le_div₀ n0 num den0 den
    _ = ((2 * A * A + 2 * A * B : ℤ) : ℝ) / ((Sz - A : ℤ) : ℝ) / Sz := by
        push_cast
        have : (Sz : ℝ) - A ≠ 0 := by
          have : (A : ℝ) < Sz := by exact_mod_cast A1
          linarith
        field_simp
    _ ≤ (tailF b m : ℝ) / Sz := by
        apply div_le_div_of_nonneg_right _ sp.le
        exact le_cdiv _ _ (by linarith [A1])

theorem waveF_mem (hp : b.Mem p) (g : Guards b) (η0 : 0 < etaN b) (m : Wave) (ok : waveOK b m = true) :
    (waveF b m).Mem (waveValue p m) := by
  have sp := Sz_pos
  simp only [waveOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨κ0, tpos, A1⟩, zlo, zhi⟩ := ok
  have ht := tF_mem hp g m
  have t0 : 0 ≤ tReal p m := le_trans (div_nonneg (by exact_mod_cast tpos.le) sp.le) ht.1
  obtain ⟨ηp, ηl, ηu⟩ := eta_bounds hp η0
  have tl : ((((tF b m).lo.toNat : ℕ) : ℝ) / Sz) ≤ tReal p m := by
    have : (((tF b m).lo.toNat : ℕ) : ℝ) = ((tF b m).lo : ℝ) := by exact_mod_cast Int.toNat_of_nonneg tpos.le
    rw [this]; exact ht.1
  have t0p : 0 < (((tF b m).lo.toNat : ℕ) : ℝ) / Sz := by
    have : (((tF b m).lo.toNat : ℕ) : ℝ) = ((tF b m).lo : ℝ) := by exact_mod_cast Int.toNat_of_nonneg tpos.le
    rw [this]; exact div_pos (by exact_mod_cast tpos) sp
  obtain ⟨_, tail⟩ := axialTail_sound (wReal p m) (uReal p m) (p 7) ((etaN b : ℝ) / Sz) t0p tl ηp.le ηl ηu
  have series := FI.widen_mem (coreF_mem hp g m t0 (by linarith) (by linarith) zlo zhi) (tailF b m)
    (tail.trans (tailF_bound m A1))
  unfold waveF waveValue
  rw [div_eq_mul_inv]
  exact FI.mul_mem series (FI.invPos_mem κ0 (kappaF_mem hp g m))

/-! ### Retained sum, radial tail and layer -/

theorem sumF_mem (l : List Wave) (F : Wave → FI) (v : Wave → ℝ) (h : ∀ m ∈ l, (F m).Mem (v m)) :
    (sumF (l.map F)).Mem ((l.map v).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, sumF, List.sum_nil, FI.Mem, Int.cast_zero, zero_div]
    exact ⟨le_rfl, le_rfl⟩
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, sumF]
    exact FI.add_mem (h a List.mem_cons_self) (ih (fun m hm => h m (List.mem_cons_of_mem _ hm)))

theorem retainedF_mem (hp : b.Mem p) (g : Guards b) (η0 : 0 < etaN b)
    (ok : (wavesList 2).all (waveOK b) = true) : (retainedF b).Mem (retainedLayer p 2) := by
  unfold retainedF retainedLayer
  rw [sum_waves_eq]
  exact FI.mul_mem (FI.smul2_mem (cF_mem hp g))
    (sumF_mem _ _ _ (fun m hm => waveF_mem hp g η0 m (List.all_eq_true.mp ok m hm)))

theorem radialTail_le {c cH B τ η A₁ A₂ E₃ F₃ : ℝ} (c0 : 0 ≤ c) (hc : c ≤ cH) (B0 : 0 ≤ B)
    (hA₁ : Real.exp (-τ) ≤ A₁) (A₁1 : A₁ < 1) (hA₂ : Real.exp (-(τ * η)) ≤ A₂) (A₂1 : A₂ < 1)
    (hE₃ : A₁ ^ 3 ≤ E₃) (E₃1 : E₃ < 1) (hF₃ : A₂ ^ 3 ≤ F₃) :
    radialTail c B τ η 3 ≤ 8 * cH * B / (1 - E₃) * (2 * E₃ / (1 - A₁) + 2 * F₃ / (1 - A₂)) := by
  have e1 := Real.exp_pos (-τ)
  have e2 := Real.exp_pos (-(τ * η))
  have x3 : Real.exp (-τ * ((3 : ℕ) : ℝ)) ≤ E₃ := by
    rw [show -τ * ((3 : ℕ) : ℝ) = -τ + -τ + -τ by push_cast; ring, Real.exp_add, Real.exp_add]
    calc _ = Real.exp (-τ) ^ 3 := by ring
      _ ≤ A₁ ^ 3 := pow_le_pow_left₀ e1.le hA₁ 3
      _ ≤ E₃ := hE₃
  have y3 : Real.exp (-(τ * η) * ((3 : ℕ) : ℝ)) ≤ F₃ := by
    rw [show -(τ * η) * ((3 : ℕ) : ℝ) = -(τ * η) + -(τ * η) + -(τ * η) by push_cast; ring,
      Real.exp_add, Real.exp_add]
    calc _ = Real.exp (-(τ * η)) ^ 3 := by ring
      _ ≤ A₂ ^ 3 := pow_le_pow_left₀ e2.le hA₂ 3
      _ ≤ F₃ := hF₃
  have x0 := Real.exp_pos (-τ * ((3 : ℕ) : ℝ))
  have y0 := Real.exp_pos (-(τ * η) * ((3 : ℕ) : ℝ))
  unfold radialTail radialDen
  have d1 : 0 < 1 - E₃ := by linarith
  have d2 : 0 < 1 - A₁ := by linarith
  have d3 : 0 < 1 - A₂ := by linarith
  have cH0 : 0 ≤ cH := c0.trans hc
  have q1 : 0 < 1 - Real.exp (-τ) := by linarith
  have q2 : 0 < 1 - Real.exp (-(τ * η)) := by linarith
  have n0 : 0 ≤ 8 * cH * B := mul_nonneg (mul_nonneg (by norm_num) cH0) B0
  have X : 8 * c * B / (1 - Real.exp (-τ * ((3 : ℕ) : ℝ))) ≤ 8 * cH * B / (1 - E₃) :=
    div_le_div₀ n0 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) B0) d1
      (by linarith)
  have Y : 2 * Real.exp (-τ * ((3 : ℕ) : ℝ)) / (1 - Real.exp (-τ)) +
      2 * Real.exp (-(τ * η) * ((3 : ℕ) : ℝ)) / (1 - Real.exp (-(τ * η))) ≤
      2 * E₃ / (1 - A₁) + 2 * F₃ / (1 - A₂) :=
    add_le_add (div_le_div₀ (by linarith) (by linarith) d2 (by linarith))
      (div_le_div₀ (by linarith) (by linarith) d3 (by linarith))
  exact mul_le_mul X Y (add_nonneg (div_nonneg (by positivity) q1.le) (div_nonneg (by positivity) q2.le))
    (div_nonneg n0 d1.le)

theorem columnF_bounds (hp : b.Mem p) : p 0 ≤ (columnF b : ℝ) / Sz ∧ secondColumn p ≤ (columnF b : ℝ) / Sz := by
  have sp := Sz_pos
  have sc := FI.sqrt_mem (FI.add_mem (FI.sq_mem (FI.mul_mem (cx_mem hp 0) (cx_mem hp 2)))
    (FI.sq_mem (cx_mem hp 1)))
  unfold columnF
  constructor
  · exact (cx_mem hp 0).2.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) sp.le)
  · unfold secondColumn
    exact sc.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) sp.le)

theorem radialF_bound (hp : b.Mem p) (g : Guards b) (η0 : 0 < etaN b) (ok : radialOK b = true) :
    Summable (waveValue p) ∧ |layerValue p - retainedLayer p 2| ≤ (radialF b : ℝ) / Sz := by
  have sp := Sz_pos
  simp only [radialOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨τ0, B0, a1, a2, e3⟩ := ok
  obtain ⟨ηp, ηl, ηu⟩ := eta_bounds hp η0
  obtain ⟨h₁, h₂⟩ := columnF_bounds hp
  have hc := cF_mem hp g
  have hr : 0 < p 0 := (div_pos (by exact_mod_cast g.r₀) sp).trans_le (cx_mem hp 0).1
  have hs : 0 < p 1 := (div_pos (by exact_mod_cast g.r₁) sp).trans_le (cx_mem hp 1).1
  have Bp : (0:ℝ) < (columnF b : ℝ) / Sz := div_pos (by exact_mod_cast B0) sp
  have τp : (0:ℝ) < (tauN b : ℝ) / Sz := div_pos (by exact_mod_cast τ0) sp
  have cpos : 0 < cReal p := inv_pos.mpr (mul_pos hr hs)
  -- τ ≤ 2π c / B
  have hstep : (tauN b : ℝ) / Sz ≤ 2 * Real.pi * cReal p / ((columnF b : ℝ) / Sz) := by
    have q0 : 0 ≤ twoPiLo * (cF b).lo / columnF b := by
      by_contra hq
      unfold tauN at τ0
      rw [Int.toNat_eq_zero.mpr (le_of_lt (lt_of_not_ge hq))] at τ0
      exact lt_irrefl _ τ0
    have e : ((tauN b : ℕ) : ℝ) = ((twoPiLo * (cF b).lo / columnF b : ℤ) : ℝ) := by
      unfold tauN; exact_mod_cast Int.toNat_of_nonneg q0
    rw [e, le_div_iff₀ Bp]
    have f := fdiv_le (twoPiLo * (cF b).lo) (columnF b) B0
    have key : ((twoPiLo : ℝ) / Sz) * (((cF b).lo : ℝ) / Sz) ≤ 2 * Real.pi * cReal p := by
      rcases le_or_gt 0 (cF b).lo with h | h
      · exact mul_le_mul twoPi_bounds.1 hc.1 (div_nonneg (by exact_mod_cast h) sp.le) (by positivity)
      · have : ((twoPiLo : ℝ) / Sz) * (((cF b).lo : ℝ) / Sz) < 0 :=
          mul_neg_of_pos_of_neg (div_pos (by norm_num [twoPiLo]) sp)
            (div_neg_of_neg_of_pos (by exact_mod_cast h) sp)
        nlinarith [Real.pi_pos]
    have cF0 : (columnF b : ℝ) ≠ 0 := by exact_mod_cast B0.ne'
    calc ((twoPiLo * (cF b).lo / columnF b : ℤ) : ℝ) / Sz * ((columnF b : ℝ) / Sz)
        ≤ ((twoPiLo * (cF b).lo : ℤ) : ℝ) / columnF b / Sz * ((columnF b : ℝ) / Sz) := by
          gcongr
      _ = ((twoPiLo : ℝ) / Sz) * (((cF b).lo : ℝ) / Sz) := by
          push_cast; field_simp
      _ ≤ _ := key
  obtain ⟨hsum, hrad⟩ := radialTail_sound 2 hr hs h₁ h₂ τp hstep ηp ηl ηu
  refine ⟨hsum, ?_⟩
  rw [layer_diff p 2 hsum]
  refine hrad.trans ?_
  -- the exponentials of the radial tail
  have hA₁ : Real.exp (-((tauN b : ℝ) / Sz)) ≤ ((expNegPt (tauN b)).hi : ℝ) / Sz := (expNegPt_mem _).2
  have hA₂ : Real.exp (-((tauN b : ℝ) / Sz * ((etaN b : ℝ) / Sz))) ≤
      ((expNegPt (tauN b * etaN b / S)).hi : ℝ) / Sz := by
    refine le_trans (Real.exp_le_exp.mpr (neg_le_neg ?_)) (expNegPt_mem _).2
    refine (div_le_div_of_nonneg_right (fdivN_le _ _) sp.le).trans_eq ?_
    push_cast
    rw [S_eq]
    field_simp
  have cube (a : ℤ) : ((a : ℝ) / Sz) ^ 3 ≤ (cdivZ (a * a * a) (S2 : ℤ) : ℝ) / Sz := by
    have h := le_cdiv (a * a * a) (S2 : ℤ) (by norm_num [S2])
    have s2 : (((S2 : ℕ) : ℤ) : ℝ) = (Sz : ℝ) * Sz := by push_cast; exact S2_eq
    rw [s2] at h
    calc ((a : ℝ) / Sz) ^ 3 = ((a * a * a : ℤ) : ℝ) / ((Sz : ℝ) * Sz) / Sz := by
          push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right h sp.le
  have A₁1 : ((expNegPt (tauN b)).hi : ℝ) / Sz < 1 := by rw [div_lt_one sp]; exact_mod_cast a1
  have A₂1 : ((expNegPt (tauN b * etaN b / S)).hi : ℝ) / Sz < 1 := by
    rw [div_lt_one sp]; exact_mod_cast a2
  have E₃1 : (cdivZ ((expNegPt (tauN b)).hi * (expNegPt (tauN b)).hi * (expNegPt (tauN b)).hi) (S2 : ℤ) : ℝ) /
      Sz < 1 := by rw [div_lt_one sp]; exact_mod_cast e3
  refine (radialTail_le cpos.le hc.2 Bp.le hA₁ A₁1 hA₂ A₂1 (cube _) E₃1 (cube _)).trans ?_
  -- the integer evaluation in `radialF`
  set a₁ := (expNegPt (tauN b)).hi with ha₁
  set a₂ := (expNegPt (tauN b * etaN b / S)).hi with ha₂
  set e₃ := cdivZ (a₁ * a₁ * a₁) (S2 : ℤ) with he₃
  set f₃ := cdivZ (a₂ * a₂ * a₂) (S2 : ℤ) with hf₃
  have a₁0 : 0 ≤ (a₁ : ℝ) / Sz := (Real.exp_pos _).le.trans hA₁
  have a₂0 : 0 ≤ (a₂ : ℝ) / Sz := (Real.exp_pos _).le.trans hA₂
  have e₃0 : 0 ≤ (e₃ : ℝ) / Sz := (pow_nonneg a₁0 3).trans (cube a₁)
  have f₃0 : 0 ≤ (f₃ : ℝ) / Sz := (pow_nonneg a₂0 3).trans (cube a₂)
  have d₁ : (0:ℤ) < Sz - a₁ := by linarith
  have d₂ : (0:ℤ) < Sz - a₂ := by linarith
  have d₃ : (0:ℤ) < Sz - e₃ := by linarith
  have rd₁ : (0:ℝ) < (Sz : ℝ) - a₁ := by exact_mod_cast d₁
  have rd₂ : (0:ℝ) < (Sz : ℝ) - a₂ := by exact_mod_cast d₂
  have rd₃ : (0:ℝ) < (Sz : ℝ) - e₃ := by exact_mod_cast d₃
  have g₁ : 2 * ((e₃ : ℝ) / Sz) / (1 - (a₁ : ℝ) / Sz) ≤ (cdivZ (2 * e₃ * Sz) (Sz - a₁) : ℝ) / Sz := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (le_cdiv _ _ d₁) sp.le)
    push_cast
    field_simp
  have g₂ : 2 * ((f₃ : ℝ) / Sz) / (1 - (a₂ : ℝ) / Sz) ≤ (cdivZ (2 * f₃ * Sz) (Sz - a₂) : ℝ) / Sz := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (le_cdiv _ _ d₂) sp.le)
    push_cast
    field_simp
  have pre : 8 * (((cF b).hi : ℝ) / Sz) * ((columnF b : ℝ) / Sz) / (1 - (e₃ : ℝ) / Sz) ≤
      (cdivZ (8 * (cF b).hi * columnF b) (Sz - e₃) : ℝ) / Sz := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (le_cdiv _ _ d₃) sp.le)
    push_cast
    field_simp
  have pre0 : 0 ≤ 8 * (((cF b).hi : ℝ) / Sz) * ((columnF b : ℝ) / Sz) / (1 - (e₃ : ℝ) / Sz) := by
    have : 0 ≤ ((cF b).hi : ℝ) / Sz := cpos.le.trans hc.2
    have : 0 < 1 - (e₃ : ℝ) / Sz := by linarith
    positivity
  have sum0 : 0 ≤ 2 * ((e₃ : ℝ) / Sz) / (1 - (a₁ : ℝ) / Sz) + 2 * ((f₃ : ℝ) / Sz) / (1 - (a₂ : ℝ) / Sz) := by
    have : 0 < 1 - (a₁ : ℝ) / Sz := by linarith
    have : 0 < 1 - (a₂ : ℝ) / Sz := by linarith
    positivity
  unfold radialF
  dsimp only
  rw [← ha₁, ← ha₂, ← he₃, ← hf₃]
  calc _ ≤ ((cdivZ (8 * (cF b).hi * columnF b) (Sz - e₃) : ℝ) / Sz) *
        (((cdivZ (2 * e₃ * Sz) (Sz - a₁) : ℝ) / Sz) + ((cdivZ (2 * f₃ * Sz) (Sz - a₂) : ℝ) / Sz)) :=
        mul_le_mul pre (add_le_add g₁ g₂) sum0 (pre0.trans pre)
    _ = ((cdivZ (8 * (cF b).hi * columnF b) (Sz - e₃) *
          (cdivZ (2 * e₃ * Sz) (Sz - a₁) + cdivZ (2 * f₃ * Sz) (Sz - a₂)) : ℤ) : ℝ) / Sz / Sz := by
        push_cast; field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (le_cdiv _ _ Sz_posZ) sp.le

end Wave

/-! ### Layer, area and the pass -/

theorem layerF_mem {raw : Cell} {p : Chart} (hp : raw.Mem p) (g : Guards (seamCell raw))
    (η0 : 0 < etaN (seamCell raw)) (waves : (wavesList 2).all (waveOK (seamCell raw)) = true)
    (rad : radialOK (seamCell raw) = true) : (layerF raw).Mem (layerValue (seamPoint raw p)) := by
  have hq := seamPoint_mem hp
  have ret := retainedF_mem hq g η0 waves
  obtain ⟨_, bound⟩ := radialF_bound hq g η0 rad
  unfold layerF
  dsimp only
  refine FI.widen_mem ret _ ?_
  exact bound

theorem areaF_bound {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) :
    (areaF b : ℝ) / Sz ≤ (triangleZ : ℝ) / Sz * Real.sqrt (cReal p) + zeroMode p := by
  have sp := Sz_pos
  have hc := cF_mem hp g
  have hs := FI.sqrt_mem hc
  have hh := cx_mem hp 7
  unfold FI.Mem at hh
  have hr : 0 < p 0 := (div_pos (by exact_mod_cast g.r₀) sp).trans_le (cx_mem hp 0).1
  have hr1 : 0 < p 1 := (div_pos (by exact_mod_cast g.r₁) sp).trans_le (cx_mem hp 1).1
  have cp : 0 ≤ cReal p := (inv_pos.mpr (mul_pos hr hr1)).le
  set d := areaD b with hd
  set a := areaAnchor b with ha
  set C := triangleZ
  set dR : ℝ := (d : ℝ) / Sz with hdR'
  set aR : ℝ := (a : ℝ) / Sz with haR'
  set x := Real.sqrt (cReal p)
  have x0 : 0 ≤ x := Real.sqrt_nonneg _
  have aR0 : 0 ≤ aR := by rw [haR']; positivity
  have dR0 : 0 ≤ dR := by rw [hdR']; positivity
  have s3 : (0:ℤ) < Sz * Sz * Sz := mul_pos (mul_pos Sz_posZ Sz_posZ) Sz_posZ
  have s4 : (0:ℤ) < Sz * Sz * Sz * Sz := mul_pos s3 Sz_posZ
  -- the slope interval contains C + 4 d a³
  have hslope : (⟨C + 4 * (d : ℤ) * a * a * a / (Sz * Sz * Sz),
      C + cdivZ (4 * (d : ℤ) * a * a * a) (Sz * Sz * Sz)⟩ : FI).Mem ((C : ℝ) / Sz + 4 * dR * aR ^ 3) := by
    have e : (4 * dR * aR ^ 3) = ((4 * (d : ℤ) * a * a * a : ℤ) : ℝ) / ((Sz * Sz * Sz : ℤ) : ℝ) / Sz := by
      rw [hdR', haR']; push_cast; field_simp
    unfold FI.Mem
    dsimp only
    push_cast
    rw [add_div, add_div, e]
    have f1 := fdiv_le (4 * (d : ℤ) * a * a * a) (Sz * Sz * Sz) s3
    have f2 := le_cdiv (4 * (d : ℤ) * a * a * a) (Sz * Sz * Sz) s3
    push_cast at f1 f2 ⊢
    constructor
    · exact add_le_add le_rfl (div_le_div_of_nonneg_right f1 sp.le)
    · exact add_le_add le_rfl (div_le_div_of_nonneg_right f2 sp.le)
  have hshift := shift_mem hs (a : ℤ)
  have prod := FI.mul_mem hslope hshift
  -- the two leading terms
  have t1 : ((C * a / Sz : ℤ) : ℝ) / Sz ≤ (C : ℝ) / Sz * aR := by
    refine (div_le_div_of_nonneg_right (fdiv_le _ _ Sz_posZ) sp.le).trans_eq ?_
    rw [haR']; push_cast; field_simp
  have t2 : (((d : ℤ) * a * a * a * a / (Sz * Sz * Sz * Sz) : ℤ) : ℝ) / Sz ≤ dR * aR ^ 4 := by
    refine (div_le_div_of_nonneg_right (fdiv_le _ _ s4) sp.le).trans_eq ?_
    rw [hdR', haR']; push_cast; field_simp
  have tangent := quarticTangent aR0 x0 dR0 ((C : ℝ) / Sz)
  -- d ≤ 2π(p₇² - p₇ + 1/3)
  have dle : dR ≤ 2 * Real.pi * ((p 7) ^ 2 - p 7 + 1 / 3) := by
    set hdz := max 0 (max ((cx b 7).lo - halfS) (halfS - (cx b 7).hi)) with hhdz
    have hd0 : 0 ≤ hdz := le_max_left _ _
    have hdR : (((hdz.toNat : ℕ)) : ℝ) / Sz ≤ |p 7 - 1 / 2| := by
      have e : (((hdz.toNat : ℕ)) : ℝ) = (hdz : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hd0
      rw [e, hhdz]
      push_cast
      rw [← max_div_div_right sp.le, ← max_div_div_right sp.le, sub_div, sub_div, halfS_eq,
        show (Sz : ℝ) / 2 / Sz = 1 / 2 by field_simp]
      simp only [zero_div]
      refine max_le (abs_nonneg _) (max_le ?_ ?_)
      · exact (sub_le_sub_right hh.1 _).trans (le_abs_self _)
      · exact (sub_le_sub_left hh.2 _).trans (by rw [abs_sub_comm]; exact le_abs_self _)
    have hdR0 : (0:ℝ) ≤ (((hdz.toNat : ℕ)) : ℝ) / Sz := by positivity
    have sq := pow_le_pow_left₀ hdR0 hdR 2
    rw [sq_abs] at sq
    have tp : ((twoPiLo.toNat : ℕ) : ℝ) = (twoPiLo : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by norm_num [twoPiLo])
    have tpl := twoPi_bounds.1
    -- areaD = ⌊twoPiLo (S/12 + hd²/S) / S⌋
    have step : dR ≤ ((twoPiLo : ℝ) / Sz) * (1 / 12 + ((((hdz.toNat : ℕ)) : ℝ) / Sz) ^ 2) := by
      rw [show dR = (d : ℝ) / Sz from rfl, hd]
      unfold areaD
      dsimp only
      rw [← hhdz]
      refine (div_le_div_of_nonneg_right (fdivN_le _ _) sp.le).trans ?_
      push_cast
      rw [tp, S_eq]
      have h12 := fdivN_le S 12
      have hsq := fdivN_le (hdz.toNat * hdz.toNat) S
      push_cast at h12 hsq
      rw [S_eq] at h12 hsq
      have tp0 : (0:ℝ) ≤ twoPiLo := by norm_num [twoPiLo]
      calc (twoPiLo : ℝ) * (((S / 12 : ℕ) : ℝ) + ((hdz.toNat * hdz.toNat / S : ℕ) : ℝ)) / Sz / Sz
          ≤ (twoPiLo : ℝ) * ((Sz : ℝ) / 12 + ((hdz.toNat : ℝ) * hdz.toNat) / Sz) / Sz / Sz := by
            gcongr
        _ = _ := by field_simp
    calc dR ≤ ((twoPiLo : ℝ) / Sz) * (1 / 12 + ((((hdz.toNat : ℕ)) : ℝ) / Sz) ^ 2) := step
      _ ≤ 2 * Real.pi * (1 / 12 + (p 7 - 1 / 2) ^ 2) := by
          gcongr
      _ = _ := by ring
  have zero : dR * x ^ 4 ≤ zeroMode p := by
    have x4 : x ^ 4 = (cReal p) ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt cp]
    rw [x4]
    unfold zeroMode
    calc dR * cReal p ^ 2 ≤ (2 * Real.pi * ((p 7) ^ 2 - p 7 + 1 / 3)) * cReal p ^ 2 :=
          mul_le_mul_of_nonneg_right dle (sq_nonneg _)
      _ = _ := by ring
  unfold areaF
  dsimp only
  rw [← ha, ← hd]
  push_cast
  rw [add_div, add_div]
  have pl := prod.1
  calc _ ≤ (C : ℝ) / Sz * aR + dR * aR ^ 4 + ((C : ℝ) / Sz + 4 * dR * aR ^ 3) * (x - (a : ℝ) / Sz) :=
        add_le_add (add_le_add t1 t2) pl
    _ ≤ (C : ℝ) / Sz * x + dR * x ^ 4 := tangent
    _ ≤ _ := by linarith

theorem triangleZ_le : (triangleZ : ℝ) / Sz ≤ triangleRegularized := by
  refine le_trans ?_ triangleThreeLower_sound
  rw [div_le_iff₀ Sz_pos]
  norm_num [triangleZ, triangleThreeLower, Sz]

theorem threshold_ge : (fccThreshold : ℝ) ≤ (thresholdZ : ℝ) / Sz := by
  rw [le_div_iff₀ Sz_pos]
  norm_num [thresholdZ, fccThreshold, Sz]

/-- A passing fixed-point check bounds the triangular relaxation strictly above the FCC level. -/
theorem fixPass_sound {raw : Cell} (ok : fixPass raw = true) {p : Chart} (hp : raw.Mem p) :
    2 * ac * energy fcc < triangularRelaxation (seamPoint raw p) := by
  have sp := Sz_pos
  simp only [fixPass, fixCheck, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨_, _⟩, ⟨r₀, r₁, r₀₁, η0⟩, waves, rad⟩, strict⟩ := ok
  have g : Guards (seamCell raw) := ⟨r₀, r₁, r₀₁⟩
  have hq := seamPoint_mem hp
  have lay := layerF_mem hp g η0 waves rad
  have area := areaF_bound hq g
  have hr : 0 < seamPoint raw p 0 := (div_pos (by exact_mod_cast r₀) sp).trans_le (cx_mem hq 0).1
  have hr1 : 0 < seamPoint raw p 1 := (div_pos (by exact_mod_cast r₁) sp).trans_le (cx_mem hq 1).1
  have tri := mul_le_mul_of_nonneg_right triangleZ_le (Real.sqrt_nonneg (cReal (seamPoint raw p)))
  have h := fccHUpper_sound scaleRoot_ok
  have th := threshold_ge
  have fe := fccThreshold_eq
  have strictR : (thresholdZ : ℝ) / Sz < ((areaF (seamCell raw) : ℝ) + (layerF raw).lo) / Sz := by
    apply div_lt_div_of_pos_right _ sp
    exact_mod_cast strict
  rw [add_div] at strictR
  have fe' : (fccHUpper : ℝ) - 4 = (fccThreshold : ℝ) := by exact_mod_cast fe
  unfold triangularRelaxation
  linarith [lay.1]

theorem energy_fcc_lt_of_fixPass {raw : Cell} (ok : fixPass raw = true) {p : Chart} (hp : raw.Mem p) :
    energy fcc < energy (chartPoint p) := by
  have h1 := fixPass_sound ok hp
  have guards := ok
  simp only [fixPass, fixCheck, Bool.and_eq_true, decide_eq_true_eq] at guards
  have hd : diagonalsCheck (seamCell raw) = true := guards.1.1.1
  have hη : 0 < spacing (seamCell raw) := guards.1.1.2
  have h2 := addressed_energy_planar_of_guards hp hd hη
  let q := seamPoint raw p
  let B := seamCell raw
  have hm : B.Mem q := seamPoint_mem hp
  have h := diagonalsCheck_sound hd
  have r : 0 < q 0 := (show (0:ℝ) < (coord B 0).lo by exact_mod_cast h.1).trans_le (endpoints (coord_sound hm 0)).1
  have t : 0 < q 1 := (show (0:ℝ) < (coord B 1).lo by exact_mod_cast h.2.1).trans_le (endpoints (coord_sound hm 1)).1
  have h3 := planarRegularized_ge_triangle q r t
  have hac := ac_positive
  unfold triangularRelaxation at h1
  have h4 : 2 * ac * energy fcc < 2 * ac * energy (chartPoint p) := by linarith
  exact lt_of_mul_lt_mul_left h4 (by positivity)

/-- The fixed-point Overlay check in `SoundCheck` form, on route `.strictFCC`. -/
def overlayFixCheck (w : WitnessRef) (b : Cell) : Bool :=
  decide (w.route = Route.strictFCC) && fixPass b

theorem overlayFixCheck_sound : SoundCheck overlayFixCheck := by
  intro w b ok p hp _
  obtain ⟨route, pass⟩ := Bool.and_eq_true_iff.mp ok
  rw [of_decide_eq_true route]
  exact energy_fcc_lt_of_fixPass pass hp

end BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
