import BccSharp.Cover.OverlayMontgomery

set_option autoImplicit false

/-! # A finite lower bound of the planar integral

For a chart with positive diagonals, splitting `planarRegularized p =
∫_{s>0} planarRegularHeat p s` at `s = 1`, keeping finitely many terms of the
planar theta series on `s > 1` and of its Poisson dual on `0 < s ≤ 1` (every
term is positive) and integrating gives, for lists `D`, `K` of nonzero planar
modes in one half plane,

`planarRegularized p ≥ 2 Σ_{m∈D} g(π N_m) + 2c Σ_{m∈K} g(π κ²_m) - 2c - 2`,

with `N_m = planarNorm p m₁ m₂`, `κ²_m = κSq p m`, `c = cReal p` and
`g = gKernel (1/2)` (`planarRegularized_ge`). This keeps the exact in-plane
energy that `triangularRelaxation` drops; the PlanarFibre triangular evaluator needs
it on about a tenth of its boxes. The integrals of the kernels repeat private
lemmas of `BccSharp.Cover.OverlayMontgomery` (proved there for the triangular chart). -/

noncomputable section

open MeasureTheory Set

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri
open BccSharp OverlayPlanar

/-- `∫_{s>1} 2 e^{-t s²} ds = gKernel (1/2) t`. -/
theorem large_kernel {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => 2 * Real.exp (-t * s ^ 2)) (Ioi 1) ∧
    ∫ s in Ioi (1:ℝ), 2 * Real.exp (-t * s ^ 2) = gKernel (1/2) t := by
  refine ⟨((integrable_exp_neg_mul_sq ht).const_mul 2).integrableOn, ?_⟩
  rw [integral_const_mul, gKernel_half]

/-- `∫_{0<s≤1} 2 s⁻² e^{-t s⁻²} ds = gKernel (1/2) t`. -/
theorem small_kernel_eq {t : ℝ} (_ht : 0 < t) :
    ∫ s in Ioc (0:ℝ) 1, 2 * (s ^ 2)⁻¹ * Real.exp (-t * (s⁻¹) ^ 2) = gKernel (1/2) t := by
  set g : ℝ → ℝ := (Ioi (1:ℝ)).indicator (fun y => 2 * Real.exp (-t * y ^ 2)) with hg
  have key := integral_comp_rpow_Ioi g (p := (-1:ℝ)) (by norm_num)
  have hR : ∫ y in Ioi (0:ℝ), g y = gKernel (1/2) t := by
    rw [hg, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one), integral_const_mul, gKernel_half]
  have hL : ∫ x in Ioi (0:ℝ), (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) • g (x ^ (-1:ℝ)) =
      ∫ x in Ioo (0:ℝ) 1, 2 * (x ^ 2)⁻¹ * Real.exp (-t * (x⁻¹) ^ 2) := by
    rw [← Set.Ioi_inter_Iio, ← setIntegral_indicator measurableSet_Iio]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := hx
    simp only [hg, Set.indicator, Set.mem_Ioi, Set.mem_Iio, smul_eq_mul]
    rw [Real.rpow_neg_one, show (-1:ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx0.le,
      Real.rpow_two]
    by_cases h1 : x < 1
    · simp only [(one_lt_inv₀ hx0).mpr h1, h1, ↓reduceIte]
      norm_num
      ring
    · have h2 : ¬ 1 < x⁻¹ := by rwa [one_lt_inv₀ hx0]
      simp only [h2, h1, ↓reduceIte, mul_zero]
  rw [← setIntegral_congr_set Ioo_ae_eq_Ioc, ← hL, key, hR]

theorem small_kernel_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => 2 * (s ^ 2)⁻¹ * Real.exp (-t * (s⁻¹) ^ 2)) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2 / t) (by simp [Real.volume_Ioc])
    (by fun_prop) (ae_of_all _ fun s => ?_)
  have hu : 0 ≤ (s ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg s)
  have hexp : t * (s ^ 2)⁻¹ * Real.exp (-t * (s ^ 2)⁻¹) ≤ 1 := by
    have := Real.add_one_le_exp (t * (s ^ 2)⁻¹)
    have hpos := Real.exp_pos (t * (s ^ 2)⁻¹)
    rw [show -t * (s ^ 2)⁻¹ = -(t * (s ^ 2)⁻¹) by ring, Real.exp_neg]
    rw [mul_inv_le_iff₀ hpos]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow]
  rw [le_div_iff₀ ht]
  nlinarith [hexp, Real.exp_pos (-t * (s ^ 2)⁻¹)]

theorem inv_sq_integral :
    IntegrableOn (fun s : ℝ => 2 * (s ^ 2)⁻¹) (Ioi 1) ∧
    ∫ s in Ioi (1:ℝ), 2 * (s ^ 2)⁻¹ = 2 := by
  have e : EqOn (fun s : ℝ => 2 * (s ^ 2)⁻¹) (fun s => 2 * s ^ (-2:ℝ)) (Ioi 1) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := zero_le_one.trans (le_of_lt hs)
    simp only
    rw [Real.rpow_neg hs0, Real.rpow_two]
  have hi : IntegrableOn (fun s : ℝ => 2 * s ^ (-2:ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) zero_lt_one).const_mul 2
  refine ⟨hi.congr_fun e.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) zero_lt_one]
  norm_num

/-- Integrals of finite list sums. -/
theorem list_integral {S : Set ℝ} {ι : Type*} (L : List ι) (F : ι → ℝ → ℝ)
    (h : ∀ i ∈ L, IntegrableOn (F i) S) :
    IntegrableOn (fun s => (L.map fun i => F i s).sum) S ∧
      ∫ s in S, (L.map fun i => F i s).sum = (L.map fun i => ∫ s in S, F i s).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := h i List.mem_cons_self
    obtain ⟨i1, i2⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hi.add i1, by rw [integral_add hi i1, i2]⟩

/-! ### Finite parts of a series -/

/-- A wave in the open upper half plane of the index lattice. -/
def UpperWave (m : Wave) : Prop := 0 < m.1 ∨ (m.1 = 0 ∧ 0 < m.2)

theorem upper_ne_zero {m : Wave} (h : UpperWave m) : m ≠ 0 := by
  intro e
  rw [Prod.ext_iff] at e
  simp only [Prod.fst_zero, Prod.snd_zero] at e
  rcases h with h | h <;> omega

theorem upper_neg {m n : Wave} (hm : UpperWave m) (hn : UpperWave n) : -m ≠ n := by
  intro e
  rw [Prod.ext_iff] at e
  simp only [Prod.fst_neg, Prod.snd_neg] at e
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> omega

/-- A nonnegative summable series over the waves is at least its zero term
plus the terms at `±m` for `m` in a duplicate-free list of upper waves. -/
theorem tsum_ge_list {f : Wave → ℝ} (hf : Summable f) (h0 : ∀ m, 0 ≤ f m) (L : List Wave)
    (hL : L.Nodup) (hu : ∀ m ∈ L, UpperWave m) :
    f 0 + (L.map fun m => f m + f (-m)).sum ≤ ∑' m, f m := by
  classical
  set A := L.toFinset
  set Bn := A.image (fun m : Wave => -m)
  have hAB : Disjoint A Bn := by
    rw [Finset.disjoint_left]
    intro m hmA hmB
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hmB
    exact upper_neg (hu n (List.mem_toFinset.mp hn)) (hu (-n) (List.mem_toFinset.mp hmA)) rfl
  have h0A : (0 : Wave) ∉ A ∪ Bn := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact upper_ne_zero (hu 0 (List.mem_toFinset.mp h)) rfl
    · obtain ⟨n, hn, e⟩ := Finset.mem_image.mp h
      exact upper_ne_zero (hu n (List.mem_toFinset.mp hn)) (neg_eq_zero.mp e)
  have hs := hf.sum_le_tsum (insert 0 (A ∪ Bn)) (fun m _ => h0 m)
  rw [Finset.sum_insert h0A, Finset.sum_union hAB, Finset.sum_image (fun x _ y _ e => neg_injective e),
    List.sum_toFinset _ hL, List.sum_toFinset _ hL] at hs
  rw [List.sum_map_add]
  linarith

/-! ### The planar integral -/

theorem sq_pos_ne {x : ℝ} (h : x ≠ 0) : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))

theorem planarNorm_pos (p : Chart) (hr : 0 < p 0) (ht : 0 < p 1) {m : Wave} (hm : m ≠ 0) :
    0 < planarNorm p (m.1 : ℝ) (m.2 : ℝ) := by
  unfold planarNorm
  by_cases h2 : m.2 = 0
  · have h1 : m.1 ≠ 0 := by
      intro h1; exact hm (Prod.ext h1 h2)
    have : 0 < (p 0 * ((m.1 : ℝ) + p 2 * (m.2 : ℝ))) ^ 2 := by
      rw [h2]
      simp only [Int.cast_zero, mul_zero, add_zero]
      exact sq_pos_ne (mul_ne_zero hr.ne' (by exact_mod_cast h1))
    have := sq_nonneg (p 1 * (m.2 : ℝ))
    linarith
  · have : 0 < (p 1 * (m.2 : ℝ)) ^ 2 := sq_pos_ne (mul_ne_zero ht.ne' (by exact_mod_cast h2))
    have := sq_nonneg (p 0 * ((m.1 : ℝ) + p 2 * (m.2 : ℝ)))
    linarith

theorem κSq_pos (p : Chart) (hr : 0 < p 0) (ht : 0 < p 1) {m : Wave} (hm : m ≠ 0) : 0 < κSq p m := by
  unfold κSq
  by_cases h1 : m.1 = 0
  · have h2 : m.2 ≠ 0 := by
      intro h2; exact hm (Prod.ext h1 h2)
    have : 0 < (((m.2 : ℝ) - (m.1 : ℝ) * p 2) * (p 1)⁻¹) ^ 2 := by
      rw [h1]
      simp only [Int.cast_zero, zero_mul, sub_zero]
      exact sq_pos_ne (mul_ne_zero (by exact_mod_cast h2) (inv_ne_zero ht.ne'))
    have := sq_nonneg ((m.1 : ℝ) * (p 0)⁻¹)
    linarith
  · have : 0 < ((m.1 : ℝ) * (p 0)⁻¹) ^ 2 := sq_pos_ne (mul_ne_zero (by exact_mod_cast h1) (inv_ne_zero hr.ne'))
    have := sq_nonneg (((m.2 : ℝ) - (m.1 : ℝ) * p 2) * (p 1)⁻¹)
    linarith

theorem planarNorm_neg (p : Chart) (m : Wave) :
    planarNorm p ((-m).1 : ℝ) ((-m).2 : ℝ) = planarNorm p (m.1 : ℝ) (m.2 : ℝ) := by
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, planarNorm]
  ring

theorem κSq_neg (p : Chart) (m : Wave) : κSq p (-m) = κSq p m := by
  simp only [κSq, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

/-- The finite lower bound of the planar integral. -/
theorem planarRegularized_ge (p : Chart) (hr : 0 < p 0) (ht : 0 < p 1) (D K : List Wave)
    (hD : D.Nodup) (huD : ∀ m ∈ D, UpperWave m) (hK : K.Nodup) (huK : ∀ m ∈ K, UpperWave m) :
    2 * (D.map fun m => gKernel (1/2) (Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ))).sum +
      2 * cReal p * (K.map fun m => gKernel (1/2) (Real.pi * κSq p m)).sum - 2 * cReal p - 2 ≤
    planarRegularized p := by
  have cp : 0 < cReal p := inv_pos.mpr (mul_pos hr ht)
  have hI := planarRegularHeat_integrable p hr ht
  -- the two lower-bound integrands
  let fL : ℝ → ℝ := fun s =>
    (D.map fun m => 2 * (2 * Real.exp (-(Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ)) * s ^ 2))).sum -
      cReal p * (2 * (s ^ 2)⁻¹)
  let fS : ℝ → ℝ := fun s =>
    (K.map fun m => cReal p * 2 * (2 * (s ^ 2)⁻¹ * Real.exp (-(Real.pi * κSq p m) * (s⁻¹) ^ 2))).sum - 2
  have tN : ∀ m ∈ D, 0 < Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ) :=
    fun m hm => mul_pos Real.pi_pos (planarNorm_pos p hr ht (upper_ne_zero (huD m hm)))
  have tK : ∀ m ∈ K, 0 < Real.pi * κSq p m :=
    fun m hm => mul_pos Real.pi_pos (κSq_pos p hr ht (upper_ne_zero (huK m hm)))
  -- integrability and integrals of the lower bounds
  have LD := list_integral (S := Ioi (1:ℝ)) D
    (fun m s => 2 * (2 * Real.exp (-(Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ)) * s ^ 2)))
    (fun m hm => (large_kernel (tN m hm)).1.const_mul 2)
  have LK := list_integral (S := Ioc (0:ℝ) 1) K
    (fun m s => cReal p * 2 * (2 * (s ^ 2)⁻¹ * Real.exp (-(Real.pi * κSq p m) * (s⁻¹) ^ 2)))
    (fun m hm => (small_kernel_integrable (tK m hm)).const_mul _)
  have hc : IntegrableOn (fun _ : ℝ => (2:ℝ)) (Ioc 0 1) := by
    refine integrableOn_const ?_
    simp [Real.volume_Ioc]
  have iL : IntegrableOn fL (Ioi 1) := LD.1.sub ((inv_sq_integral.1).const_mul _)
  have iS : IntegrableOn fS (Ioc 0 1) := LK.1.sub hc
  have vL : ∫ s in Ioi (1:ℝ), fL s =
      2 * (D.map fun m => gKernel (1/2) (Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ))).sum - 2 * cReal p := by
    simp only [fL]
    rw [integral_sub LD.1 ((inv_sq_integral.1).const_mul _), LD.2, integral_const_mul, inv_sq_integral.2]
    have e : ∀ m ∈ D, (∫ s in Ioi (1:ℝ), 2 * (2 * Real.exp (-(Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ)) * s ^ 2))) =
        2 * gKernel (1/2) (Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ)) := fun m hm => by
      rw [integral_const_mul, (large_kernel (tN m hm)).2]
    rw [List.map_congr_left e, List.sum_map_mul_left]
    ring
  have vS : ∫ s in Ioc (0:ℝ) 1, fS s =
      2 * cReal p * (K.map fun m => gKernel (1/2) (Real.pi * κSq p m)).sum - 2 := by
    simp only [fS]
    rw [integral_sub LK.1 hc, LK.2, setIntegral_const]
    have e : ∀ m ∈ K, (∫ s in Ioc (0:ℝ) 1, cReal p * 2 * (2 * (s ^ 2)⁻¹ * Real.exp (-(Real.pi * κSq p m) * (s⁻¹) ^ 2))) =
        2 * cReal p * gKernel (1/2) (Real.pi * κSq p m) := fun m hm => by
      rw [integral_const_mul, small_kernel_eq (tK m hm)]
      ring
    rw [List.map_congr_left e, List.sum_map_mul_left]
    simp
  -- pointwise bounds
  have pL : ∀ s ∈ Ioi (1:ℝ), fL s ≤ planarRegularHeat p s := by
    intro s hs
    have s0 : 0 < s := zero_lt_one.trans hs
    have hsum := planeHeat_summable p hr.ne' ht.ne' s s0 0 0
    have ge := tsum_ge_list hsum (fun m => (Real.exp_pos _).le) D hD huD
    have e0 : planeHeat p s 0 0 0 = 1 := by simp [planeHeat, planarNorm]
    have eN : ∀ m : Wave, planeHeat p s 0 0 m = Real.exp (-(Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ)) * s ^ 2) := by
      intro m; simp only [planeHeat, add_zero]; ring_nf
    have eNn : ∀ m : Wave, planeHeat p s 0 0 (-m) = planeHeat p s 0 0 m := by
      intro m; rw [eN, eN, planarNorm_neg]
    simp only [planarRegularHeat, planeTheta, fL]
    rw [e0] at ge
    simp only [eNn] at ge
    have hs2 : (D.map fun m => 2 * (2 * Real.exp (-(Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ)) * s ^ 2))).sum =
        2 * (D.map fun m => planeHeat p s 0 0 m + planeHeat p s 0 0 m).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun m _ => ?_
      rw [eN]
      ring
    rw [hs2]
    linarith
  have pS : ∀ s ∈ Ioc (0:ℝ) 1, fS s ≤ planarRegularHeat p s := by
    intro s hs
    have s0 : 0 < s := hs.1
    have hsum := planeDual_summable p hr.ne' ht.ne' s⁻¹ (inv_pos.mpr s0) 0 0
    have eK : ∀ m : Wave, planeDualTerm p s⁻¹ 0 0 m = Real.exp (-(Real.pi * κSq p m) * (s⁻¹) ^ 2) := by
      intro m; simp only [planeDualTerm, mul_zero, add_zero, Real.cos_zero, mul_one]; ring_nf
    have ge := tsum_ge_list hsum (fun m => by rw [eK]; exact (Real.exp_pos _).le) K hK huK
    have e0 : planeDualTerm p s⁻¹ 0 0 0 = 1 := by rw [eK]; simp [κSq]
    have eKn : ∀ m : Wave, planeDualTerm p s⁻¹ 0 0 (-m) = planeDualTerm p s⁻¹ 0 0 m := by
      intro m; rw [eK, eK, κSq_neg]
    simp only [planarRegularHeat, fS]
    rw [plane_poisson p hr ht s s0 0 0]
    unfold planeDual
    rw [e0] at ge
    simp only [eKn] at ge
    have hs2 : (K.map fun m => cReal p * 2 * (2 * (s ^ 2)⁻¹ * Real.exp (-(Real.pi * κSq p m) * (s⁻¹) ^ 2))).sum =
        2 * (cReal p * (s ^ 2)⁻¹) * (K.map fun m => planeDualTerm p s⁻¹ 0 0 m + planeDualTerm p s⁻¹ 0 0 m).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun m _ => ?_
      rw [eK]
      ring
    rw [hs2]
    have hc : 0 ≤ cReal p * (s ^ 2)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ge hc]
  -- integrate
  have mL := setIntegral_mono_on iL (hI.mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi pL
  have mS := setIntegral_mono_on iS (hI.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc pS
  unfold planarRegularized
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi zero_le_one))]
  rw [vL] at mL
  rw [vS] at mS
  linarith

end BccSharp.Coulomb.CompactCover.PlanarFibreTri
