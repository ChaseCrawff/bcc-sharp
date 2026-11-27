import BccSharp.Cover.PlanarFibreJetSound

set_option autoImplicit false

/-! # The second-order Taylor bound on a box

For a point `p` and an expansion point `p0` of a box `b`, the coordinate path
`q m` (coordinates `< m` from `p`, the others from `p0`) goes from `p0` to `p`
in eight steps. Step `k` is a one-variable Taylor bound with Lagrange-type
remainder (`taylor_segment`); the first partial at the start of step `k`
differs from its value at `p0` by the cross terms `∂_j ∂_k` along the earlier
steps (`mvt_segment`). With the jets of `BccSharp.Cover.PlanarFibreJet` this gives
`taylorLowerOf_le`: for `f₂` enclosed to second order (point jet at `p0`, box
jet on `b`), `f₁` to first order (point value, box gradient) and `f₀` by its
box value, `taylorLowerOf` is a lower bound of `f₂ + f₁ + f₀` on `b`. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri
open BccSharp BccSharp.Coverage DirectRoute
open OverlayPlanar OverlayPlanar.Fix

/-! ### One variable -/

theorem mvt_segment {φ φ1 : ℝ → ℝ} {x0 x : ℝ} (h : ∀ s ∈ Set.uIcc x0 x, HasDerivAt φ (φ1 s) s) :
    ∃ ξ ∈ Set.uIcc x0 x, φ x - φ x0 = φ1 ξ * (x - x0) := by
  rcases lt_trichotomy x0 x with hlt | heq | hgt
  · have hc : ContinuousOn φ (Set.Icc x0 x) := fun s hs =>
      (h s (Set.Icc_subset_uIcc hs)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope φ φ1 hlt hc
      (fun s hs => h s (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hs)))
    refine ⟨ξ, Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hξ), ?_⟩
    rw [e]
    field_simp [sub_ne_zero.mpr hlt.ne']
  · subst heq
    exact ⟨x0, Set.left_mem_uIcc, by ring⟩
  · have hc : ContinuousOn φ (Set.Icc x x0) := fun s hs =>
      (h s (Set.Icc_subset_uIcc' hs)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope φ φ1 hgt hc
      (fun s hs => h s (Set.Icc_subset_uIcc' (Set.Ioo_subset_Icc_self hs)))
    refine ⟨ξ, Set.Icc_subset_uIcc' (Set.Ioo_subset_Icc_self hξ), ?_⟩
    rw [e]
    field_simp [sub_ne_zero.mpr hgt.ne']
    ring

theorem taylor_segment {φ φ1 φ2 : ℝ → ℝ} {x0 x m : ℝ}
    (h1 : ∀ s ∈ Set.uIcc x0 x, HasDerivAt φ (φ1 s) s)
    (h2 : ∀ s ∈ Set.uIcc x0 x, HasDerivAt φ1 (φ2 s) s)
    (hm : ∀ s ∈ Set.uIcc x0 x, m ≤ φ2 s) :
    φ x0 + φ1 x0 * (x - x0) + m / 2 * (x - x0) ^ 2 ≤ φ x := by
  let ψ : ℝ → ℝ := fun s => φ s - φ x0 - φ1 x0 * (s - x0) - m / 2 * (s - x0) ^ 2
  let ψ1 : ℝ → ℝ := fun s => φ1 s - φ1 x0 - m * (s - x0)
  have hψ : ∀ s ∈ Set.uIcc x0 x, HasDerivAt ψ (ψ1 s) s := by
    intro s hs
    have a := (h1 s hs).sub_const (φ x0)
    have b := ((hasDerivAt_id' s).sub_const x0).const_mul (φ1 x0)
    have c := (((hasDerivAt_id' s).sub_const x0).pow 2).const_mul (m / 2)
    convert (a.sub b).sub c using 1
    simp only [ψ1]
    push_cast
    ring
  obtain ⟨ξ, hξ, e1⟩ := mvt_segment hψ
  have hsub : Set.uIcc x0 ξ ⊆ Set.uIcc x0 x := Set.uIcc_subset_uIcc Set.left_mem_uIcc hξ
  have hψ1 : ∀ s ∈ Set.uIcc x0 ξ, HasDerivAt ψ1 (φ2 s - m) s := by
    intro s hs
    have a := (h2 s (hsub hs)).sub_const (φ1 x0)
    have b := ((hasDerivAt_id' s).sub_const x0).const_mul m
    convert a.sub b using 1
    ring
  obtain ⟨ζ, hζ, e2⟩ := mvt_segment hψ1
  have hpos : 0 ≤ φ2 ζ - m := sub_nonneg.mpr (hm ζ (hsub hζ))
  have hsign : 0 ≤ (ξ - x0) * (x - x0) := by
    rcases Set.mem_uIcc.mp hξ with h | h <;> nlinarith [h.1, h.2]
  have e0 : ψ x0 = 0 := by simp [ψ]
  have e0' : ψ1 x0 = 0 := by simp [ψ1]
  rw [e0, sub_zero] at e1
  rw [e0', sub_zero] at e2
  have : 0 ≤ ψ x := by
    rw [e1, e2]
    have := mul_nonneg hpos hsign
    nlinarith
  simp only [ψ] at this
  linarith

/-! ### Elementary lower bounds -/

theorem toQ_cast (z : ℤ) : ((toQ z : ℚ) : ℝ) = (z : ℝ) / Sz := by
  unfold toQ
  push_cast
  rw [S_eq]

/-- `γ d ≥ min(l d, u d)` for `γ ∈ [l, u]`. -/
theorem lin_min {γ l u d : ℝ} (h : l ≤ γ ∧ γ ≤ u) : min (l * d) (u * d) ≤ γ * d := by
  rcases le_total 0 d with hd | hd
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right h.1 hd)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right h.2 hd)

theorem qmin_le (g A a b : ℚ) {d : ℝ} (hd : (a : ℝ) ≤ d ∧ d ≤ b) :
    ((qmin g A a b : ℚ) : ℝ) ≤ (g : ℝ) * d + (A : ℝ) * d * d / 2 := by
  unfold qmin
  split_ifs with h
  · obtain ⟨hA, -, -⟩ := h
    have hA' : (0 : ℝ) < A := by exact_mod_cast hA
    push_cast
    have key : (g : ℝ) * d + (A : ℝ) * d * d / 2 - (-((g : ℝ) * g) / (2 * A)) =
        ((A : ℝ) * d + g) ^ 2 / (2 * A) := by
      field_simp
      ring
    have : 0 ≤ ((A : ℝ) * d + g) ^ 2 / (2 * A) := by positivity
    linarith
  · push_cast
    set f : ℝ → ℝ := fun x => (g : ℝ) * x + (A : ℝ) * x * x / 2
    show min (f a) (f b) ≤ f d
    by_cases hA : (A : ℝ) ≤ 0
    · -- concave: compare with the chord
      have hab : (a : ℝ) ≤ b := hd.1.trans hd.2
      have key : ((b : ℝ) - a) * (f d - f a) =
          (d - a) * (f b - f a) + (A : ℝ) / 2 * (d - a) * (d - b) * (b - a) := by
        simp only [f]
        ring
      have key' : ((b : ℝ) - a) * (f d - f b) =
          (b - d) * (f a - f b) + (A : ℝ) / 2 * (d - a) * (d - b) * (b - a) := by
        simp only [f]
        ring
      have t : 0 ≤ (A : ℝ) / 2 * (d - a) * (d - b) * (b - a) := by
        have h1 : 0 ≤ d - (a : ℝ) := by linarith [hd.1]
        have h2 : d - (b : ℝ) ≤ 0 := by linarith [hd.2]
        have h3 : 0 ≤ (b : ℝ) - a := by linarith
        have : (A : ℝ) / 2 * (d - a) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h1
        have := mul_nonneg_of_nonpos_of_nonpos this h2
        exact mul_nonneg this h3
      rcases eq_or_lt_of_le hab with he | hlt
      · have : d = a := le_antisymm (he ▸ hd.2) hd.1
        rw [this]
        exact min_le_left _ _
      · have hpos : (0 : ℝ) < b - a := by linarith
        rcases le_total (f a) (f b) with hfab | hfab
        · refine (min_le_left _ _).trans ?_
          have : 0 ≤ ((b : ℝ) - a) * (f d - f a) := by
            rw [key]
            have := mul_nonneg (by linarith [hd.1] : (0 : ℝ) ≤ d - a) (by linarith : (0 : ℝ) ≤ f b - f a)
            linarith
          nlinarith
        · refine (min_le_right _ _).trans ?_
          have : 0 ≤ ((b : ℝ) - a) * (f d - f b) := by
            rw [key']
            have := mul_nonneg (by linarith [hd.2] : (0 : ℝ) ≤ b - d) (by linarith : (0 : ℝ) ≤ f a - f b)
            linarith
          nlinarith
    · have hA : (0 : ℝ) < A := lt_of_not_ge hA
      have hAq : (0 : ℚ) < A := by exact_mod_cast hA
      have hv : -g / A < a ∨ b < -g / A := by
        by_contra hc
        simp only [not_or, not_lt] at hc
        exact h ⟨hAq, hc.1, hc.2⟩
      rcases hv with hv | hv
      · -- increasing on [a, b]
        have hv' : (0 : ℝ) < g + A * a := by
          have : (-g / A : ℚ) < a := hv
          rw [div_lt_iff₀ hAq] at this
          have : (0 : ℚ) < g + A * a := by linarith
          exact_mod_cast this
        refine (min_le_left _ _).trans ?_
        have : f d - f a = (d - a) * (g + (A : ℝ) / 2 * (d + a)) := by
          simp only [f]
          ring
        have h1 : 0 ≤ d - (a : ℝ) := by linarith [hd.1]
        have h2 : (0 : ℝ) ≤ g + (A : ℝ) / 2 * (d + a) := by nlinarith [hd.1]
        nlinarith
      · -- decreasing on [a, b]
        have hv' : (g : ℝ) + A * b < 0 := by
          have : (b : ℚ) < -g / A := hv
          rw [lt_div_iff₀ hAq] at this
          have : (g + A * b : ℚ) < 0 := by linarith
          exact_mod_cast this
        refine (min_le_right _ _).trans ?_
        have : f d - f b = (d - b) * (g + (A : ℝ) / 2 * (d + b)) := by
          simp only [f]
          ring
        have h1 : d - (b : ℝ) ≤ 0 := by linarith [hd.2]
        have h2 : (g : ℝ) + (A : ℝ) / 2 * (d + b) ≤ 0 := by nlinarith [hd.2]
        nlinarith

/-- `quadLower` bounds `γ d + η d²/2` for `γ ∈ G`, `η ≥ H.lo/S`, `d ∈ [a, b]`. -/
theorem quadLower_le {G H : MR} {a b : ℚ} {γ η d : ℝ} (hγ : G.Mem γ) (hη : (H.lo : ℝ) / Sz ≤ η)
    (hd : (a : ℝ) ≤ d ∧ d ≤ b) :
    ((quadLower G H a b : ℚ) : ℝ) ≤ γ * d + η / 2 * d ^ 2 := by
  unfold quadLower
  have hγ' := MR.toFI_mem hγ
  have eA : ((toQ H.lo : ℚ) : ℝ) = (H.lo : ℝ) / Sz := toQ_cast _
  have q1 := qmin_le (toQ G.lo) (toQ H.lo) a b hd
  have q2 := qmin_le (toQ G.hi) (toQ H.lo) a b hd
  rw [toQ_cast, eA] at q1 q2
  dsimp only [MR.toFI, FI.Mem] at hγ'
  have hl := lin_min (d := d) ⟨hγ'.1, hγ'.2⟩
  have hdd : (H.lo : ℝ) / Sz * d * d / 2 ≤ η / 2 * d ^ 2 := by
    have : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith
  rw [Rat.cast_min]
  rcases le_total ((G.lo : ℝ) / Sz * d) ((G.hi : ℝ) / Sz * d) with hc | hc
  · rw [min_eq_left hc] at hl
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right hc] at hl
    exact (min_le_right _ _).trans (by linarith)

/-- `crossLower` bounds `η dⱼ dₖ` for `η ∈ H`. -/
theorem crossLower_le {H : MR} {aj bj ak bk : ℚ} {η dj dk : ℝ} (hη : H.Mem η)
    (hj : (aj : ℝ) ≤ dj ∧ dj ≤ bj) (hk : (ak : ℝ) ≤ dk ∧ dk ≤ bk) :
    ((crossLower H aj bj ak bk : ℚ) : ℝ) ≤ η * dj * dk := by
  have hη' := MR.toFI_mem hη
  have hl : (H.lo : ℝ) / Sz ≤ η := hη'.1
  have hu : η ≤ (H.hi : ℝ) / Sz := hη'.2
  unfold crossLower
  dsimp only
  push_cast
  rw [toQ_cast, toQ_cast]
  set l := (H.lo : ℝ) / Sz
  set u := (H.hi : ℝ) / Sz
  set M := min (min (min (l * ((aj : ℝ) * ak)) (l * ((aj : ℝ) * bk))) (min (l * ((bj : ℝ) * ak)) (l * ((bj : ℝ) * bk))))
    (min (min (u * ((aj : ℝ) * ak)) (u * ((aj : ℝ) * bk))) (min (u * ((bj : ℝ) * ak)) (u * ((bj : ℝ) * bk))))
  have mA1 : M ≤ l * ((aj : ℝ) * ak) := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have mA2 : M ≤ l * ((aj : ℝ) * bk) := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have mA3 : M ≤ l * ((bj : ℝ) * ak) := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have mA4 : M ≤ l * ((bj : ℝ) * bk) := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have mB1 : M ≤ u * ((aj : ℝ) * ak) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have mB2 : M ≤ u * ((aj : ℝ) * bk) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have mB3 : M ≤ u * ((bj : ℝ) * ak) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have mB4 : M ≤ u * ((bj : ℝ) * bk) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the four vertices in `η`
  have v : ∀ w : ℝ, M ≤ l * w → M ≤ u * w → M ≤ η * w := fun w h1 h2 =>
    le_trans (le_min h1 h2) (lin_min (d := w) ⟨hl, hu⟩)
  have v1 := v _ mA1 mB1
  have v2 := v _ mA2 mB2
  have v3 := v _ mA3 mB3
  have v4 := v _ mA4 mB4
  -- then `dj`
  have w1 : M ≤ η * ak * dj := by
    have := lin_min (γ := dj) (d := η * ak) hj
    have e1 : (aj : ℝ) * (η * ak) = η * ((aj : ℝ) * ak) := by ring
    have e2 : (bj : ℝ) * (η * ak) = η * ((bj : ℝ) * ak) := by ring
    rw [e1, e2] at this
    have := le_trans (le_min v1 v3) this
    linarith
  have w2 : M ≤ η * bk * dj := by
    have := lin_min (γ := dj) (d := η * bk) hj
    have e1 : (aj : ℝ) * (η * bk) = η * ((aj : ℝ) * bk) := by ring
    have e2 : (bj : ℝ) * (η * bk) = η * ((bj : ℝ) * bk) := by ring
    rw [e1, e2] at this
    have := le_trans (le_min v2 v4) this
    linarith
  -- then `dk`
  have := lin_min (γ := dk) (d := η * dj) hk
  have e1 : (ak : ℝ) * (η * dj) = η * ak * dj := by ring
  have e2 : (bk : ℝ) * (η * dj) = η * bk * dj := by ring
  rw [e1, e2] at this
  have := le_trans (le_min w1 w2) this
  linarith

/-! ### The coordinate path -/

/-- Coordinates `< m` from `p`, the others from `p0`. -/
def pathPt (p0 p : Chart) (m : ℕ) : Chart := fun i => if i.val < m then p i else p0 i

theorem pathPt_zero (p0 p : Chart) : pathPt p0 p 0 = p0 := by
  funext i
  simp [pathPt]

theorem pathPt_eight (p0 p : Chart) : pathPt p0 p 8 = p := by
  funext i
  simp [pathPt, i.isLt]

theorem pathPt_succ (p0 p : Chart) (k : Fin 8) :
    pathPt p0 p (k.val + 1) = Function.update (pathPt p0 p k.val) k (p k) := by
  funext i
  by_cases h : i = k
  · subst h
    simp [pathPt]
  · rw [Function.update_of_ne h]
    have : i.val ≠ k.val := fun e => h (Fin.ext e)
    simp only [pathPt]
    by_cases hi : i.val < k.val
    · simp [hi, show i.val < k.val + 1 by omega]
    · simp [hi, show ¬ i.val < k.val + 1 by omega]

theorem pathPt_self (p0 p : Chart) (k : Fin 8) : pathPt p0 p k.val k = p0 k := by
  simp [pathPt]

theorem pathPt_mem {b : Cell} {p0 p : Chart} (h0 : b.Mem p0) (hp : b.Mem p) (m : ℕ) :
    b.Mem (pathPt p0 p m) := by
  intro i
  simp only [pathPt]
  split_ifs
  · exact hp i
  · exact h0 i

theorem update_mem {b : Cell} {q : Chart} (hq : b.Mem q) (k : Fin 8) {s : ℝ}
    (hs : (b.lo k : ℝ) ≤ s ∧ s ≤ b.hi k) : b.Mem (Function.update q k s) := by
  intro i
  by_cases h : i = k
  · subst h
    simpa using hs
  · rw [Function.update_of_ne h]
    exact hq i

theorem seg_mem {b : Cell} {p0 p : Chart} (h0 : b.Mem p0) (hp : b.Mem p) (k : Fin 8) {s : ℝ}
    (hs : s ∈ Set.uIcc (p0 k) (p k)) : (b.lo k : ℝ) ≤ s ∧ s ≤ b.hi k :=
  Set.uIcc_subset_Icc (h0 k) (hp k) hs

/-- The coordinate-line derivative at a moved point. -/
theorem line_deriv {b : Cell} {f : Chart → ℝ} {D : Fin 8 → Chart → ℝ}
    (hD : ∀ q, b.Mem q → ∀ k, HasDerivAt (fun s => f (Function.update q k s)) (D k q) (q k))
    {q : Chart} (hq : b.Mem q) (k : Fin 8) {s : ℝ} (hs : (b.lo k : ℝ) ≤ s ∧ s ≤ b.hi k) :
    HasDerivAt (fun s' => f (Function.update q k s')) (D k (Function.update q k s)) s := by
  have h := hD (Function.update q k s) (update_mem hq k hs) k
  simp only [Function.update_idem, Function.update_self] at h
  exact h

/-! ### Steps along the path -/

section Path
variable {b : Cell} {D : Fin 8 → Chart → ℝ} {D2 : Fin 8 → Fin 8 → Chart → ℝ} {H : Fin 8 → Fin 8 → MR}
  {p0 p : Chart}

/-- Step `k` of the path: a one-variable Taylor bound. -/
theorem taylor_step {f : Chart → ℝ}
    (hD : ∀ q, b.Mem q → ∀ k, HasDerivAt (fun s => f (Function.update q k s)) (D k q) (q k))
    (hD2 : ∀ q, b.Mem q → ∀ j k, HasDerivAt (fun s => D k (Function.update q j s)) (D2 j k q) (q j) ∧
      (H j k).Mem (D2 j k q))
    (h0 : b.Mem p0) (hp : b.Mem p) (k : Fin 8) :
    f (pathPt p0 p k.val) + D k (pathPt p0 p k.val) * (p k - p0 k) +
      ((H k k).lo : ℝ) / Sz / 2 * (p k - p0 k) ^ 2 ≤ f (pathPt p0 p (k.val + 1)) := by
  set q := pathPt p0 p k.val with hqd
  have hq : b.Mem q := pathPt_mem h0 hp _
  have hqk : q k = p0 k := pathPt_self p0 p k
  have h1 : ∀ s ∈ Set.uIcc (p0 k) (p k),
      HasDerivAt (fun s' => f (Function.update q k s')) (D k (Function.update q k s)) s :=
    fun s hs => line_deriv hD hq k (seg_mem h0 hp k hs)
  have h2 : ∀ s ∈ Set.uIcc (p0 k) (p k),
      HasDerivAt (fun s' => D k (Function.update q k s')) (D2 k k (Function.update q k s)) s := by
    intro s hs
    have h := (hD2 (Function.update q k s) (update_mem hq k (seg_mem h0 hp k hs)) k k).1
    simp only [Function.update_idem, Function.update_self] at h
    exact h
  have hm : ∀ s ∈ Set.uIcc (p0 k) (p k), ((H k k).lo : ℝ) / Sz ≤ D2 k k (Function.update q k s) :=
    fun s hs => MR.lo_le (hD2 _ (update_mem hq k (seg_mem h0 hp k hs)) k k).2
  have t := taylor_segment h1 h2 hm
  have e0 : Function.update q k (p0 k) = q := by rw [← hqk]; exact Function.update_eq_self k q
  have e1 : Function.update q k (p k) = pathPt p0 p (k.val + 1) := (pathPt_succ p0 p k).symm
  simp only [e0, e1] at t
  exact t

/-- Along a coordinate step the value changes by the derivative at an
intermediate point of the box. -/
theorem mvt_step {f : Chart → ℝ}
    (hD : ∀ q, b.Mem q → ∀ k, HasDerivAt (fun s => f (Function.update q k s)) (D k q) (q k))
    (h0 : b.Mem p0) (hp : b.Mem p) (k : Fin 8) :
    ∃ ξ, b.Mem ξ ∧ f (pathPt p0 p (k.val + 1)) - f (pathPt p0 p k.val) = D k ξ * (p k - p0 k) := by
  set q := pathPt p0 p k.val with hqd
  have hq : b.Mem q := pathPt_mem h0 hp _
  have hqk : q k = p0 k := pathPt_self p0 p k
  have h1 : ∀ s ∈ Set.uIcc (p0 k) (p k),
      HasDerivAt (fun s' => f (Function.update q k s')) (D k (Function.update q k s)) s :=
    fun s hs => line_deriv hD hq k (seg_mem h0 hp k hs)
  obtain ⟨s, hs, e⟩ := mvt_segment h1
  refine ⟨Function.update q k s, update_mem hq k (seg_mem h0 hp k hs), ?_⟩
  have e0 : Function.update q k (p0 k) = q := by rw [← hqk]; exact Function.update_eq_self k q
  have e1 : Function.update q k (p k) = pathPt p0 p (k.val + 1) := (pathPt_succ p0 p k).symm
  simp only [e0, e1] at e
  exact e

/-- The cross terms: `D k` at the start of step `k` against its value at `p0`. -/
theorem grad_path
    (hD2 : ∀ q, b.Mem q → ∀ j k, HasDerivAt (fun s => D k (Function.update q j s)) (D2 j k q) (q j) ∧
      (H j k).Mem (D2 j k q))
    (p0q : Fin 8 → ℚ) (hp0 : p0 = fun i => (p0q i : ℝ))
    (h0 : b.Mem p0) (hp : b.Mem p) (k : Fin 8) :
    ∀ m, m ≤ k.val → D k p0 * (p k - p0 k) + ∑ j ∈ Finset.range m,
      (if hj : j < 8 then ((crossLower (H ⟨j, hj⟩ k) (b.lo ⟨j, hj⟩ - p0q ⟨j, hj⟩)
        (b.hi ⟨j, hj⟩ - p0q ⟨j, hj⟩) (b.lo k - p0q k) (b.hi k - p0q k) : ℚ) : ℝ) else 0) ≤
      D k (pathPt p0 p m) * (p k - p0 k) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [pathPt_zero]
  | succ m ih =>
    intro hm
    have hm8 : m < 8 := by omega
    set j : Fin 8 := ⟨m, hm8⟩
    have hrow := ih (by omega)
    -- the step in coordinate `j` of `D k`
    set q := pathPt p0 p m with hqd
    have hq : b.Mem q := pathPt_mem h0 hp _
    have hqj : q j = p0 j := pathPt_self p0 p j
    have h1 : ∀ s ∈ Set.uIcc (p0 j) (p j),
        HasDerivAt (fun s' => D k (Function.update q j s')) (D2 j k (Function.update q j s)) s := by
      intro s hs
      have h := (hD2 (Function.update q j s) (update_mem hq j (seg_mem h0 hp j hs)) j k).1
      simp only [Function.update_idem, Function.update_self] at h
      exact h
    obtain ⟨s, hs, e⟩ := mvt_segment h1
    have e0 : Function.update q j (p0 j) = q := by rw [← hqj]; exact Function.update_eq_self j q
    have e1 : Function.update q j (p j) = pathPt p0 p (m + 1) := (pathPt_succ p0 p j).symm
    simp only [e0, e1] at e
    have hξ := (hD2 _ (update_mem hq j (seg_mem h0 hp j hs)) j k).2
    have bj : ((b.lo j - p0q j : ℚ) : ℝ) ≤ p j - p0 j ∧ p j - p0 j ≤ ((b.hi j - p0q j : ℚ) : ℝ) := by
      rw [hp0]
      push_cast
      exact ⟨by linarith [(hp j).1], by linarith [(hp j).2]⟩
    have bk : ((b.lo k - p0q k : ℚ) : ℝ) ≤ p k - p0 k ∧ p k - p0 k ≤ ((b.hi k - p0q k : ℚ) : ℝ) := by
      rw [hp0]
      push_cast
      exact ⟨by linarith [(hp k).1], by linarith [(hp k).2]⟩
    have cl := crossLower_le hξ bj bk
    rw [Finset.sum_range_succ]
    simp only [hm8, ↓reduceDIte]
    have : D k (pathPt p0 p (m + 1)) * (p k - p0 k) =
        D k (pathPt p0 p m) * (p k - p0 k) + D2 j k (Function.update q j s) * (p j - p0 j) * (p k - p0 k) := by
      rw [← sub_eq_iff_eq_add', ← sub_mul, e]
    rw [this]
    linarith

end Path

/-! ### The assembled bound -/

theorem list_range_sum (n : ℕ) (f : ℕ → ℚ) :
    ((((List.range n).map f).sum : ℚ) : ℝ) = ∑ k ∈ Finset.range n, ((f k : ℚ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Rat.cast_add, ih, Finset.sum_range_succ]
    simp

theorem taylorLowerOf_le {b : Cell} {p0q : Fin 8 → ℚ} {P2 P1 B2 B1 B0 : J2} {f2 f1 f0 : Chart → ℝ}
    (hin : inCell p0q b = true)
    (oP2 : P2.ok = true) (oP1 : P1.ok = true) (oB2 : B2.ok = true) (oB1 : B1.ok = true)
    (oB0 : B0.ok = true)
    (hP2 : J2Mem (pointCell p0q) P2 f2) (hP1 : J2Mem (pointCell p0q) P1 f1)
    (hB2 : J2Mem b B2 f2) (hB1 : J2Mem b B1 f1) (hB0 : J2Mem b B0 f0)
    {p : Chart} (hp : b.Mem p) :
    ((taylorLowerOf b p0q P2 P1 B2 B1 B0 : ℚ) : ℝ) ≤ f2 p + f1 p + f0 p := by
  set p0 : Chart := fun i => (p0q i : ℝ) with hp0
  have h0 : b.Mem p0 := by
    have h := of_decide_eq_true hin
    intro i
    simp only [hp0]
    exact ⟨by exact_mod_cast (h i).1, by exact_mod_cast (h i).2⟩
  have hpt : (pointCell p0q).Mem p0 := fun i => ⟨le_rfl, le_rfl⟩
  obtain ⟨Dp, D2p, HP2⟩ := hP2 oP2
  obtain ⟨_, _, HP1⟩ := hP1 oP1
  obtain ⟨D, D2, HB2⟩ := hB2 oB2
  obtain ⟨D1, _, HB1⟩ := hB1 oB1
  obtain ⟨_, _, HB0⟩ := hB0 oB0
  have hD : ∀ q, b.Mem q → ∀ k, HasDerivAt (fun s => f2 (Function.update q k s)) (D k q) (q k) :=
    fun q hq k => ((HB2 q hq).2.1 k).1
  have hD2 : ∀ q, b.Mem q → ∀ j k, HasDerivAt (fun s => D k (Function.update q j s)) (D2 j k q) (q j) ∧
      (B2.h j k).Mem (D2 j k q) := fun q hq j k => ⟨((HB2 q hq).2.2 j k).1, ((HB2 q hq).2.2 j k).2.1⟩
  have hD1 : ∀ q, b.Mem q → ∀ k, HasDerivAt (fun s => f1 (Function.update q k s)) (D1 k q) (q k) :=
    fun q hq k => ((HB1 q hq).2.1 k).1
  -- the point gradient of `f₂`
  have hgp : ∀ k, (P2.g k).Mem (D k p0) := by
    intro k
    have e : Dp k p0 = D k p0 := HasDerivAt.unique ((HP2 p0 hpt).2.1 k).1 (hD p0 h0 k)
    rw [← e]
    exact ((HP2 p0 hpt).2.1 k).2.1
  -- one step
  have step : ∀ k : ℕ, (hk : k < 8) →
      ((qTerm b p0q P2 B1 B2 k : ℚ) : ℝ) + ∑ j ∈ Finset.range k, ((cTerm b p0q B2 j k : ℚ) : ℝ) ≤
        (f2 (pathPt p0 p (k + 1)) + f1 (pathPt p0 p (k + 1))) - (f2 (pathPt p0 p k) + f1 (pathPt p0 p k)) := by
    intro k hk
    let kk : Fin 8 := ⟨k, hk⟩
    have t2 : f2 (pathPt p0 p k) + D kk (pathPt p0 p k) * (p kk - p0 kk) +
        ((B2.h kk kk).lo : ℝ) / Sz / 2 * (p kk - p0 kk) ^ 2 ≤ f2 (pathPt p0 p (k + 1)) :=
      taylor_step hD hD2 h0 hp kk
    obtain ⟨ξ, hξ, e1⟩ := mvt_step hD1 h0 hp kk
    have e1' : f1 (pathPt p0 p (k + 1)) - f1 (pathPt p0 p k) = D1 kk ξ * (p kk - p0 kk) := e1
    have g1 := ((HB1 ξ hξ).2.1 kk).2.1
    have gp := grad_path (H := B2.h) hD2 p0q hp0 h0 hp kk k le_rfl
    have bk : ((b.lo kk - p0q kk : ℚ) : ℝ) ≤ p kk - p0 kk ∧ p kk - p0 kk ≤ ((b.hi kk - p0q kk : ℚ) : ℝ) := by
      simp only [hp0]
      push_cast
      exact ⟨by linarith [(hp kk).1], by linarith [(hp kk).2]⟩
    have ql := quadLower_le (H := B2.h kk kk) (MR.add_mem (hgp kk) g1) le_rfl bk
    rw [add_mul] at ql
    have eq : (qTerm b p0q P2 B1 B2 k : ℚ) = quadLower ((P2.g kk).add (B1.g kk)) (B2.h kk kk)
        (b.lo kk - p0q kk) (b.hi kk - p0q kk) := by
      simp only [qTerm, hk, ↓reduceDIte]
      rfl
    have ec : ∀ j ∈ Finset.range k, ((cTerm b p0q B2 j k : ℚ) : ℝ) =
        if hj : j < 8 then ((crossLower (B2.h ⟨j, hj⟩ kk) (b.lo ⟨j, hj⟩ - p0q ⟨j, hj⟩)
          (b.hi ⟨j, hj⟩ - p0q ⟨j, hj⟩) (b.lo kk - p0q kk) (b.hi kk - p0q kk) : ℚ) : ℝ) else 0 := by
      intro j _
      simp only [cTerm, hk, ↓reduceDIte]
      split_ifs with hj
      · rfl
      · simp
    rw [eq, Finset.sum_congr rfl ec]
    linarith [t2, gp, ql, e1']
  -- telescoping
  have tel : ∑ k ∈ Finset.range 8, (((qTerm b p0q P2 B1 B2 k : ℚ) : ℝ) +
      ∑ j ∈ Finset.range k, ((cTerm b p0q B2 j k : ℚ) : ℝ)) ≤
      (f2 p + f1 p) - (f2 p0 + f1 p0) := by
    have hs := Finset.sum_le_sum (s := Finset.range 8) (fun k hk => step k (Finset.mem_range.mp hk))
    rw [Finset.sum_range_sub (fun k => f2 (pathPt p0 p k) + f1 (pathPt p0 p k)), pathPt_eight,
      pathPt_zero] at hs
    exact hs
  have v2 := MR.lo_le (HP2 p0 hpt).1
  have v1 := MR.lo_le (HP1 p0 hpt).1
  have v0 := MR.lo_le (HB0 p hp).1
  unfold taylorLowerOf
  rw [Rat.cast_add, Rat.cast_add, Rat.cast_add, toQ_cast, toQ_cast, toQ_cast, list_range_sum]
  have inner : ∀ k ∈ Finset.range 8, ((qTerm b p0q P2 B1 B2 k +
      ((List.range k).map fun j => cTerm b p0q B2 j k).sum : ℚ) : ℝ) =
      ((qTerm b p0q P2 B1 B2 k : ℚ) : ℝ) + ∑ j ∈ Finset.range k, ((cTerm b p0q B2 j k : ℚ) : ℝ) := by
    intro k _
    rw [Rat.cast_add, list_range_sum]
  rw [Finset.sum_congr rfl inner]
  linarith

end BccSharp.Coulomb.CompactCover.PlanarFibreTri
