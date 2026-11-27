import BccSharp.TwoSite.ScreeningDifference

set_option autoImplicit false

/-! Screening independence for the explicit periodic Ewald kernel
and its regular self term. The continuous difference is compared by all
Fourier coefficients, including the background coefficient at zero. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace BccSharp.Coulomb
open BccSharp

theorem cellPeriodize_eq_integer (B : Mat) (hB : B.det ≠ 0) (f : Vec → ℂ) (x : Vec) :
    cellPeriodize B f x = ∑' n : IntVec, f (x+linearImage B n) := by
  unfold cellPeriodize
  change (∑' z : periodGroup B, f (z.val+x)) = _
  rw [← (periodIndices B hB).tsum_eq (fun z : periodGroup B => f (z.val+x))]
  exact tsum_congr (fun n => congrArg f (add_comm (linearImage B n) x))

theorem cycleFrequency_neg (B : Mat) (n : IntVec) : cycleFrequency B (-n) = -cycleFrequency B n := by
  simp [cycleFrequency, castVec_neg, Matrix.mulVec_neg]

theorem dualWave_cycleFrequency (B : Mat) (n : IntVec) :
    dualWave B n = (2*Real.pi) • cycleFrequency B n := rfl

theorem cellWave_real (B : Mat) (n : IntVec) (x : Vec) :
    (cellWave B (-n) x).re = Real.cos (dot (dualWave B n) x) := by
  have h : cellWave B (-n) x = physicalWave (dualWave B n) x := by
    unfold cellWave CoulombLaplace.wave physicalWave
    change Complex.exp (-((2*Real.pi*dot (cycleFrequency B (-n)) x : ℝ) : ℂ)*Complex.I) = _
    rw [cycleFrequency_neg, dualWave_cycleFrequency, dot_left_smul]
    have hneg : dot (-cycleFrequency B n) x = -dot (cycleFrequency B n) x := by
      simp [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hneg]
    congr 1
    push_cast
    ring
  rw [h, physicalWave, Complex.exp_ofReal_mul_I_re]

theorem cellReciprocal_real (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    (cellSeries B (reciprocalGreenTerm α B) x).re = reciprocalPair α B x := by
  have hs := reciprocal_lattice_summable α ha B hB
  unfold cellSeries reciprocalPair
  rw [Complex.re_tsum (cellSeries_summable B hs x)]
  simp_rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, cellWave_real]

theorem reciprocal_cycle (α : ℝ) (B : Mat) (hB : B.det ≠ 0) (n : IntVec) (hn : n ≠ 0) :
    (4*Real.pi)*reciprocalGreenTerm α B n =
      1/(Real.pi*sq (cycleFrequency B n))*
        Real.exp (-(Real.pi^2*sq (cycleFrequency B n)/α^2)) := by
  have hq : sq (cycleFrequency B n) ≠ 0 := by
    intro h
    have he := (sq_eq_zero_iff _).mp h
    exact hn (cycleFrequency_injective B hB (he.trans (cycleFrequency_zero B).symm))
  rw [reciprocalGreenTerm, if_neg hn, dualWave_cycleFrequency, sq_smul]
  have hex : (2*Real.pi)^2*sq (cycleFrequency B n)/(4*α^2) =
      Real.pi^2*sq (cycleFrequency B n)/α^2 := by ring
  change (4*Real.pi)*(Real.exp (-((2*Real.pi)^2*sq (cycleFrequency B n)/(4*α^2)))/
    ((2*Real.pi)^2*sq (cycleFrequency B n))) = _
  rw [hex]
  generalize Real.exp (-(Real.pi^2*sq (cycleFrequency B n)/α^2)) = E
  field_simp [Real.pi_pos.ne', hq]
  ring

theorem greenBackground_mul_volume (α : ℝ) (B : Mat) (hB : B.det ≠ 0) :
    greenBackground α B*volumeOf B = Real.pi/α^2 := by
  have hv : volumeOf B ≠ 0 := (abs_pos.mpr hB).ne'
  unfold greenBackground
  by_cases hα : α=0
  · simp [hα]
  · field_simp [hα, hv]

private theorem cellWave_conj (B : Mat) (n : IntVec) (x : Vec) :
    conj (cellWave B n x) = cellWave B (-n) x := by
  have he : dot (cycleFrequency B (-n)) x = -dot (cycleFrequency B n) x := by
    rw [cycleFrequency_neg]
    simp [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  unfold cellWave CoulombLaplace.wave
  rw [← Complex.exp_conj]
  congr 1
  change conj (-((2*Real.pi*dot (cycleFrequency B n) x : ℝ) : ℂ)*Complex.I) =
    -((2*Real.pi*dot (cycleFrequency B (-n)) x : ℝ) : ℂ)*Complex.I
  rw [he]
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem reciprocalGreenTerm_neg (α : ℝ) (B : Mat) (n : IntVec) :
    reciprocalGreenTerm α B (-n) = reciprocalGreenTerm α B n := by
  have h : sq (dualWave B (-n)) = sq (dualWave B n) := by
    rw [dualWave_cycleFrequency, dualWave_cycleFrequency, cycleFrequency_neg]
    simp [sq_smul, sq, Pi.neg_apply]
  simp only [reciprocalGreenTerm, neg_eq_zero, h]

theorem cellReciprocal_eq_ofReal (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    cellSeries B (reciprocalGreenTerm α B) x = (reciprocalPair α B x : ℂ) := by
  have h : conj (cellSeries B (reciprocalGreenTerm α B) x) =
      cellSeries B (reciprocalGreenTerm α B) x := by
    unfold cellSeries
    rw [Complex.conj_tsum]
    simp_rw [map_mul, Complex.conj_ofReal, cellWave_conj, neg_neg]
    have he := (Equiv.neg IntVec).tsum_eq (fun n =>
      (reciprocalGreenTerm α B n : ℂ)*cellWave B (-n) x)
    change (∑' n : IntVec, (reciprocalGreenTerm α B (-n) : ℂ)*cellWave B (-(-n)) x) = _ at he
    simpa only [reciprocalGreenTerm_neg, neg_neg] using he
  apply Complex.ext
  · simpa using cellReciprocal_real α ha B hB x
  · have he := congrArg Complex.im h
    simp only [Complex.conj_im] at he
    simp only [Complex.ofReal_im]
    linarith

private theorem periodicGreen_complex (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) :
    (fun x => (periodicGreen α B x : ℂ)) =
      fun x => cellPeriodize B (fun y => (screened α y : ℂ)) x +
        ((4*Real.pi/volumeOf B : ℝ) : ℂ)*cellSeries B (reciprocalGreenTerm α B) x -
        (greenBackground α B : ℂ) := by
  funext x
  rw [cellPeriodize_eq_integer B hB, cellReciprocal_eq_ofReal α ha B hB]
  unfold periodicGreen reciprocalPair
  simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_tsum]

/-- Physical-cell Fourier coefficient of the actual Ewald kernel.
Divide by the proved cell volume for probability-Haar normalization. -/
theorem periodicGreen_fourier_on_cell (α : ℝ) (ha : 0 < α) (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    cellFourier B hB (fun x => (periodicGreen α B x : ℂ)) n =
      if n=0 then 0 else ((4*Real.pi/sq (dualWave B n) : ℝ) : ℂ) := by
  classical
  letI : IsFiniteMeasure (volume.restrict (periodCell B hB)) :=
    isFiniteMeasure_restrict.mpr (periodCell_finite B hB).ne
  have hscr : screenedPhaseAt α 0 = fun y => (screened α y : ℂ) := by
    funext y
    simp only [screenedPhaseAt, CoulombPeriodization.wave_zero, mul_one]
  have hr : IntegrableOn (cellPeriodize B (fun y => (screened α y : ℂ))) (periodCell B hB) := by
    apply cellPeriodize_integrable B hB
    rw [← hscr]
    exact screenedPhaseAt_integrable α ha 0
  have hd := reciprocal_lattice_summable α ha B hB
  have hdual := cellSeries_integrable B hB hd
  have hv : volumeOf B ≠ 0 := (abs_pos.mpr hB).ne'
  have hfactor : ((4*Real.pi/volumeOf B : ℝ) : ℂ) *
      ((volumeOf B : ℂ)*(reciprocalGreenTerm α B n : ℂ)) =
      (((4*Real.pi)*reciprocalGreenTerm α B n : ℝ) : ℂ) := by
    push_cast
    field_simp [hv] <;> ring
  have hsum : IntegrableOn (fun x => cellPeriodize B (fun y => (screened α y : ℂ)) x +
      ((4*Real.pi/volumeOf B : ℝ) : ℂ)*cellSeries B (reciprocalGreenTerm α B) x) (periodCell B hB) :=
    hr.add (hdual.const_mul _)
  rw [periodicGreen_complex α ha B hB,
    cellFourier_sub B hB n hsum (integrable_const (greenBackground α B : ℂ)),
    cellFourier_add B hB n hr (hdual.const_mul _), cellFourier_const_mul, cellSeries_fourier B hB hd,
    cellFourier_periodize B hB _ n (screenedPhaseAt_integrable α ha (cycleFrequency B n)),
    cellConstant_fourier B hB, hfactor]
  change (∫ x : Vec, screenedPhaseAt α (cycleFrequency B n) x) + _ - _ = _
  by_cases hn : n=0
  · subst n
    simp only [ite_true, cycleFrequency_zero, screenedPhaseAt_mass α ha, reciprocalGreenTerm, mul_zero,
      Complex.ofReal_zero, add_zero, ← Complex.ofReal_mul, greenBackground_mul_volume α B hB, sub_self]
  · have hu : cycleFrequency B n ≠ 0 := fun h =>
      hn (cycleFrequency_injective B hB (h.trans (cycleFrequency_zero B).symm))
    have hsq : sq (cycleFrequency B n) ≠ 0 := fun h => hu ((sq_eq_zero_iff _).mp h)
    rw [if_neg hn, if_neg hn, sub_zero, screenedPhaseAt_fourier α ha _ hu, reciprocal_cycle α B hB n hn,
      dualWave_cycleFrequency, sq_smul]
    push_cast
    field_simp [Real.pi_pos.ne', hsq] <;> ring

private def realScreenDifference (α β : ℝ) (B : Mat) : Vec → ℂ :=
  cellPeriodize B (fun x => (screenedDifference α β x : ℂ))

private def dualScreenDifference (α β : ℝ) (B : Mat) (x : Vec) : ℂ :=
  (4*Real.pi/volumeOf B : ℝ) *
    (cellSeries B (reciprocalGreenTerm β B) x - cellSeries B (reciprocalGreenTerm α B) x) +
    ((greenBackground α B-greenBackground β B : ℝ) : ℂ)

private theorem realScreenDifference_continuous (α β : ℝ) (ha : 0 < α) (hab : α ≤ β)
    (B : Mat) (hB : B.det ≠ 0) :
    Continuous (realScreenDifference α β B) := by
  have h (x : Vec) : realScreenDifference α β B x =
      ((∑' n : IntVec, screenedDifference α β (x+linearImage B n) : ℝ) : ℂ) := by
    rw [realScreenDifference, cellPeriodize_eq_integer B hB, Complex.ofReal_tsum]
  rw [funext h]
  exact Complex.continuous_ofReal.comp (screenedDifference_lattice_continuous α β ha hab B hB)

private theorem realScreenDifference_integrable (α β : ℝ) (ha : 0 < α) (hb : 0 < β) (hab : α ≤ β)
    (B : Mat) (hB : B.det ≠ 0) :
    IntegrableOn (realScreenDifference α β B) (periodCell B hB) := by
  apply cellPeriodize_integrable B hB
  simpa only [CoulombPeriodization.wave_zero, mul_one] using screenedDifference_phase_integrable α β ha hb hab 0

private theorem dualScreenDifference_continuous (α β : ℝ) (ha : 0 < α) (hb : 0 < β)
    (B : Mat) (hB : B.det ≠ 0) : Continuous (dualScreenDifference α β B) := by
  have h₁ := cellSeries_continuous B (reciprocal_lattice_summable α ha B hB)
  have h₂ := cellSeries_continuous B (reciprocal_lattice_summable β hb B hB)
  exact (continuous_const.mul (h₂.sub h₁)).add continuous_const

private theorem dualScreenDifference_integrable (α β : ℝ) (ha : 0 < α) (hb : 0 < β)
    (B : Mat) (hB : B.det ≠ 0) :
    IntegrableOn (dualScreenDifference α β B) (periodCell B hB) := by
  letI : IsFiniteMeasure (volume.restrict (periodCell B hB)) :=
    isFiniteMeasure_restrict.mpr (periodCell_finite B hB).ne
  have h₁ := cellSeries_integrable B hB (reciprocal_lattice_summable α ha B hB)
  have h₂ := cellSeries_integrable B hB (reciprocal_lattice_summable β hb B hB)
  exact ((h₂.sub h₁).const_mul _).add (integrable_const _)

private theorem screenDifference_coefficients (α β : ℝ) (ha : 0 < α) (hb : 0 < β) (hab : α ≤ β)
    (B : Mat) (hB : B.det ≠ 0) (n : IntVec) :
    cellFourier B hB (realScreenDifference α β B) n = cellFourier B hB (dualScreenDifference α β B) n := by
  classical
  have h₁ := reciprocal_lattice_summable α ha B hB
  have h₂ := reciprocal_lattice_summable β hb B hB
  have hv : volumeOf B ≠ 0 := (abs_pos.mpr hB).ne'
  letI : IsFiniteMeasure (volume.restrict (periodCell B hB)) :=
    isFiniteMeasure_restrict.mpr (periodCell_finite B hB).ne
  have hc : IntegrableOn (fun x => cellSeries B (reciprocalGreenTerm β B) x -
      cellSeries B (reciprocalGreenTerm α B) x) (periodCell B hB) :=
    (cellSeries_integrable B hB h₂).sub (cellSeries_integrable B hB h₁)
  have hu := screenedDifference_phase_integrable α β ha hb hab (cycleFrequency B n)
  have hdual : dualScreenDifference α β B = fun x =>
      ((4*Real.pi/volumeOf B : ℝ) : ℂ) *
        (cellSeries B (reciprocalGreenTerm β B) x - cellSeries B (reciprocalGreenTerm α B) x) +
        ((greenBackground α B-greenBackground β B : ℝ) : ℂ) := rfl
  rw [realScreenDifference, cellFourier_periodize B hB _ n hu]
  change (∫ x : Vec, (screenedDifference α β x : ℂ)*CoulombLaplace.wave (cycleFrequency B n) x) = _
  rw [screenedDifference_phase_integral α β ha hb hab, hdual,
    cellFourier_add B hB n (hc.const_mul _) (integrable_const _),
    cellFourier_const_mul, cellFourier_sub B hB n (cellSeries_integrable B hB h₂) (cellSeries_integrable B hB h₁),
    cellSeries_fourier B hB h₂, cellSeries_fourier B hB h₁, cellConstant_fourier B hB]
  by_cases hn : n=0
  · subst n
    simp only [cycleFrequency_zero, screenedPhaseAt_mass α ha, screenedPhaseAt_mass β hb, ite_true,
      reciprocalGreenTerm, Complex.ofReal_zero, mul_zero, sub_zero, zero_add]
    have he : (greenBackground α B-greenBackground β B)*volumeOf B = Real.pi/α^2-Real.pi/β^2 := by
      rw [sub_mul, greenBackground_mul_volume α B hB, greenBackground_mul_volume β B hB]
    exact_mod_cast he.symm
  · have hu0 : cycleFrequency B n ≠ 0 := fun e =>
      hn (cycleFrequency_injective B hB (e.trans (cycleFrequency_zero B).symm))
    rw [screenedPhaseAt_fourier α ha _ hu0, screenedPhaseAt_fourier β hb _ hu0, if_neg hn, add_zero]
    have hc : ((4*Real.pi/volumeOf B : ℝ) : ℂ)*
        ((volumeOf B : ℂ)*(reciprocalGreenTerm β B n : ℂ) -
          (volumeOf B : ℂ)*(reciprocalGreenTerm α B n : ℂ)) =
        (((4*Real.pi)*reciprocalGreenTerm β B n : ℝ) : ℂ) -
          (((4*Real.pi)*reciprocalGreenTerm α B n : ℝ) : ℂ) := by
      push_cast
      field_simp [hv] <;> ring
    rw [hc, reciprocal_cycle β B hB n hn, reciprocal_cycle α B hB n hn]
    push_cast
    ring

theorem screenedDifference_poisson (α β : ℝ) (ha : 0 < α) (hb : 0 < β) (hab : α ≤ β)
    (B : Mat) (hB : B.det ≠ 0) (x : Vec) :
    (∑' n : IntVec, screenedDifference α β (x+linearImage B n)) =
      (4*Real.pi/volumeOf B)*(reciprocalPair β B x - reciprocalPair α B x) +
        (greenBackground α B-greenBackground β B) := by
  have hperiod (z : periodModule B) (x : Vec) :
      dualScreenDifference α β B (x+z.val) = dualScreenDifference α β B x := by
    simp_rw [dualScreenDifference, cellSeries_periodic B hB]
  have hAE := cellFourier_unique_periodic B hB
    (realScreenDifference_integrable α β ha hb hab B hB) (dualScreenDifference_integrable α β ha hb B hB)
    (fun z y => cellPeriodize_periodic B _ z y) hperiod
    (screenDifference_coefficients α β ha hb hab B hB)
  have h := Measure.eq_of_ae_eq hAE (realScreenDifference_continuous α β ha hab B hB)
    (dualScreenDifference_continuous α β ha hb B hB)
  have hreal := congrArg Complex.re (congrFun h x)
  simpa [realScreenDifference, cellPeriodize_eq_integer B hB, ← Complex.ofReal_tsum, dualScreenDifference,
    Complex.mul_re, Complex.add_re, Complex.sub_re, cellReciprocal_real α ha B hB,
    cellReciprocal_real β hb B hB] using hreal

private theorem linearImage_zero (B : Mat) : linearImage B 0 = 0 := by
  rw [linearImage, castVec_zero, Matrix.mulVec_zero]

private theorem linearImage_nonzero (B : Mat) (hB : B.det ≠ 0) {n : IntVec} (hn : n ≠ 0) :
    linearImage B n ≠ 0 := by
  intro h
  apply hn
  apply (periodIndices B hB).injective
  apply Subtype.ext
  change linearImage B n = linearImage B 0
  rwa [linearImage_zero]

theorem ewaldRegularSelf_screening_independent (α β : ℝ) (B : Mat) (hB : B.det ≠ 0)
    (ha : 0 < α) (hb : 0 < β) : ewaldRegularSelf α B = ewaldRegularSelf β B := by
  classical
  suffices go : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b → ewaldRegularSelf a B = ewaldRegularSelf b B by
    rcases le_total α β with h | h
    · exact go α β ha hb h
    · exact (go β α hb ha h).symm
  intro a b hA hB' hab
  have ms (u : ℝ) (hu : 0 < u) : Summable (fun n : IntVec =>
      if n=0 then 0 else screened u (linearImage B n)) := by
    have h := screened_lattice_summable u hu B hB 0
    simp only [zero_add] at h
    apply h.summable_of_eq_zero_or_self
    intro n
    by_cases hn : n=0 <;> simp [hn]
  let r (u : ℝ) := fun n : IntVec => if n=0 then 0 else screened u (linearImage B n)
  let v := (2/Real.sqrt Real.pi)*(b-a)
  let extra := fun n : IntVec => if n=0 then v else 0
  have hs : HasSum extra v := by
    simpa [extra] using (hasSum_single (f := extra) (0 : IntVec) (by intro n hn; simp [extra, hn]))
  have he (n : IntVec) : screenedDifference a b (0+linearImage B n) =
      (r a n-r b n) + extra n := by
    by_cases hn : n=0
    · subst n
      simp [linearImage_zero, screenedDifference_zero, r, v, extra]
    · simp [hn, r, extra, screenedDifference_eq_sub a b hab _ (by simpa using linearImage_nonzero B hB hn)]
  have h := screenedDifference_poisson a b hA hB' hab B hB 0
  simp_rw [he] at h
  rw [((ms a hA).sub (ms b hB')).tsum_add hs.summable, (ms a hA).tsum_sub (ms b hB'), hs.tsum_eq] at h
  simp only [reciprocalPair, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    Real.cos_zero, mul_one] at h
  unfold ewaldRegularSelf
  simp only [v] at h
  linear_combination h

theorem periodicGreen_screening_independent (α β : ℝ) (B : Mat) (hB : B.det ≠ 0)
    (ha : 0 < α) (hb : 0 < β) {x : Vec} (hx : x ∉ lattice B) :
    periodicGreen α B x = periodicGreen β B x := by
  suffices go : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b → periodicGreen a B x = periodicGreen b B x by
    rcases le_total α β with h | h
    · exact go α β ha hb h
    · exact (go β α hb ha h).symm
  intro a b hA hB' hab
  have nz (n : IntVec) : x+linearImage B n ≠ 0 := by
    intro he
    apply hx
    refine ⟨-n, ?_⟩
    change linearImage B (-n) = x
    rw [linearImage, castVec_neg, Matrix.mulVec_neg]
    have h : x = -linearImage B n := by
      calc
        _ = x+linearImage B n-linearImage B n := by abel
        _ = _ := by rw [he, zero_sub]
    exact h.symm
  have h := screenedDifference_poisson a b hA hB' hab B hB x
  have he (n : IntVec) := screenedDifference_eq_sub a b hab (x+linearImage B n) (nz n)
  simp_rw [he] at h
  rw [(screened_lattice_summable a hA B hB x).tsum_sub (screened_lattice_summable b hB' B hB x)] at h
  unfold reciprocalPair at h
  unfold periodicGreen
  linear_combination h

end BccSharp.Coulomb
