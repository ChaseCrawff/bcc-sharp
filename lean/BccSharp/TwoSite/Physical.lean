import BccSharp.TwoSite.Interface

set_option autoImplicit false

/-! The two-site theorem physical bridge. `periodicGreen` and `ewaldRegularSelf` are
the explicit Ewald expressions, while `GreenAnalysis` states the Fourier,
summability, and limiting facts still needed to identify them physically. -/

noncomputable section
open scoped BigOperators Topology
open Classical
open MeasureTheory

namespace BccSharp.Coulomb

theorem summable_of_finset_compl {ι : Type} (s : Finset ι) (f : ι → ℝ)
    (h : Summable (fun i : {i // i ∉ s} => f i.val)) : Summable f := by
  exact (summable_subtype_and_compl (s := (s : Set ι))).mp ⟨s.summable f, h⟩

def linearImage (B : Mat) (n : IntVec) : Vec := B.mulVec (castVec n)
def gram (B : Mat) : Mat := B.transpose * B
def dualWave (B : Mat) (n : IntVec) : Vec :=
  (2 * Real.pi) • (B⁻¹).transpose.mulVec (castVec n)

def erfcIntegral (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in Set.Ioi x, Real.exp (-t^2)

def screened (α : ℝ) (x : Vec) : ℝ :=
  erfcIntegral (α * Real.sqrt (sq x)) / Real.sqrt (sq x)

/-- Arbitrary screening version of the repository's CoulombLaplace change of
variables. This supplies the screened real-space Fourier integral. -/
theorem screened_gaussian_integral (α : ℝ) (x : Vec) (hx : 0 < sq x) :
    screened α x = (2 / Real.sqrt Real.pi) *
      ∫ s in Set.Ioi α, Real.exp (-s^2 * sq x) := by
  have hr : 0 < Real.sqrt (sq x) := Real.sqrt_pos.mpr hx
  have changeVar := integral_comp_mul_right_Ioi (fun y : ℝ => Real.exp (-y^2)) α hr
  simp only [smul_eq_mul] at changeVar
  have integrand : (fun s : ℝ => Real.exp (-(s * Real.sqrt (sq x))^2)) =
      fun s => Real.exp (-s^2 * sq x) := by
    funext s
    rw [mul_pow, Real.sq_sqrt hx.le]
    congr 1
    ring
  rw [integrand] at changeVar
  unfold screened erfcIntegral
  rw [changeVar]
  ring

def reciprocalGreenTerm (α : ℝ) (B : Mat) (n : IntVec) : ℝ :=
  let k := dualWave B n
  if n = 0 then 0 else Real.exp (-(sq k / (4 * α^2))) / sq k

def volumeOf (B : Mat) : ℝ := |B.det|
def greenBackground (α : ℝ) (B : Mat) : ℝ := Real.pi / (volumeOf B * α^2)

def periodicGreen (α : ℝ) (B : Mat) (x : Vec) : ℝ :=
  (∑' n : IntVec, screened α (x + linearImage B n)) +
  (4 * Real.pi / volumeOf B) *
    (∑' n : IntVec, reciprocalGreenTerm α B n * Real.cos (dot (dualWave B n) x)) -
  greenBackground α B

def ewaldRegularSelf (α : ℝ) (B : Mat) : ℝ :=
  (∑' n : IntVec, if n = 0 then 0 else screened α (linearImage B n)) +
  (4 * Real.pi / volumeOf B) * (∑' n : IntVec, reciprocalGreenTerm α B n) -
  2 * α / Real.sqrt Real.pi - greenBackground α B

def periodicPoints {ι : Type} (B : Mat) (s : ι → Vec) : Set Vec :=
  {x | ∃ i n, x = s i + linearImage B n}

def distinctModulo {ι : Type} (B : Mat) (s : ι → Vec) : Prop :=
  ∀ i j, i ≠ j → s i - s j ∉ lattice B

def greenCellEnergy {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec) : ℝ :=
  (1/2) * (∑ i, ∑ j, if i = j then 0 else periodicGreen α B (s i - s j)) +
  (Fintype.card ι : ℝ) * ewaldRegularSelf α B / 2

def greenPerParticle {ι : Type} [Fintype ι] (α : ℝ) (B : Mat) (s : ι → Vec) : ℝ :=
  greenCellEnergy α B s / Fintype.card ι

def fundamentalCoordinates : Set Vec := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

/-- Substitution x=Bθ cancels the Jacobian against the inverse cell volume
in the normalized Fourier coefficient. -/
def cellFourierCoefficient (B : Mat) (f : Vec → ℝ) (n : IntVec) : ℂ :=
  ∫ θ in fundamentalCoordinates,
    (f (B.mulVec θ) : ℂ) * Complex.exp (Complex.I * ((-2 * Real.pi * dot (castVec n) θ : ℝ) : ℂ))

/-- Finite-index repetition data from E.3. Multiplicities of real-space
offsets and reciprocal character sums must be proved from this presentation. -/
structure PeriodRepetition (B enlarged : Mat) (ι : Type) where
  representative : ι → Vec
  uniquePeriod : ∀ x ∈ lattice B, ∃! i : ι, x - representative i ∈ lattice enlarged
  representativesInPeriod : ∀ i, representative i ∈ lattice B
  subperiod : lattice enlarged ⊆ lattice B

def normalizedTwoPositions (q : TwoSite) (i : Fin 2) : Vec :=
  if i = 0 then 0 else q.basis.mulVec q.offset

def physicalBasis (q : TwoSite) : Mat := ac • q.basis
def physicalTwoPositions (q : TwoSite) (i : Fin 2) : Vec := ac • normalizedTwoPositions q i
def seriesScreen : ℝ := Real.sqrt Real.pi / ac

theorem ac_positive : 0 < ac := by
  unfold ac
  positivity

theorem ac_cube : ac ^ 3 = 8 * Real.pi / 3 := by
  rw [ac, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 8 * Real.pi / 3)]
  norm_num

theorem physicalBasis_volume (q : TwoSite) (hq : q.Valid) : volumeOf (physicalBasis q) = ac ^ 3 := by
  have hDet : (physicalBasis q).det = ac ^ 3 := by
    rw [physicalBasis, Matrix.det_smul, Fintype.card_fin, hq.1, mul_one]
  rw [volumeOf, hDet, abs_of_pos (pow_pos ac_positive _)]

theorem series_background_exact (q : TwoSite) (hq : q.Valid) :
    greenBackground seriesScreen (physicalBasis q) = 1 / ac := by
  rw [greenBackground, physicalBasis_volume q hq, seriesScreen, div_pow,
    Real.sq_sqrt Real.pi_pos.le]
  field_simp [ac_positive.ne', Real.pi_pos.ne'] <;> ring

theorem series_self_exact : 2 * seriesScreen / Real.sqrt Real.pi = 2 / ac := by
  rw [seriesScreen]
  field_simp [ac_positive.ne', (Real.sqrt_pos.2 Real.pi_pos).ne'] <;> ring

theorem sq_smul (t : ℝ) (v : Vec) : sq (t • v) = t^2 * sq v := by
  simp [sq, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, mul_pow]

theorem norm_smul_nonnegative (t : ℝ) (v : Vec) (ht : 0 ≤ t) :
    Real.sqrt (sq (t • v)) = t * Real.sqrt (sq v) := by
  rw [sq_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

theorem gKernel_one {t : ℝ} (ht : 0 < t) : gKernel 1 t = Real.exp (-t) / t := by
  unfold gKernel
  simp only [sub_self, Real.rpow_zero, mul_one]
  rw [integral_exp_mul_Ioi (neg_neg_of_pos ht)]
  ring

theorem liftedNeighbors_translate (S : Set Vec) (site t : Vec) :
    liftedNeighbors (translate t S) (site + t) = liftedNeighbors S site := by
  ext v
  constructor
  · rintro ⟨⟨x, hx, h⟩, hzero, hlen⟩
    have he : site + v = x := by
      have hcancel : (site + v) + t = x + t := (show (site + v) + t = (site + t) + v by abel).trans h
      exact add_right_cancel hcancel
    exact ⟨by rwa [he], hzero, hlen⟩
  · rintro ⟨hv, hzero, hlen⟩
    exact ⟨⟨site + v, hv, by abel⟩, hzero, hlen⟩

theorem siteDefect_translate (S : Set Vec) (site t : Vec) :
    cappedDefect (liftedNeighbors (translate t S) (site + t)) =
      cappedDefect (liftedNeighbors S site) := by
  rw [liftedNeighbors_translate]

theorem samePointSet_sameSiteDefect {S₁ S₂ : Set Vec} (same : S₁ = S₂) (x : Vec) :
    cappedDefect (liftedNeighbors S₁ x) = cappedDefect (liftedNeighbors S₂ x) := by
  rw [same]

theorem castVec_add (m n : IntVec) : castVec (m + n) = castVec m + castVec n := by
  funext i
  exact Int.cast_add (m i) (n i)

theorem castVec_neg (n : IntVec) : castVec (-n) = -castVec n := by
  funext i
  exact Int.cast_neg (n i)

theorem dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_integer (a b : IntVec) : dot (castVec a) (castVec b) =
    ((∑ i, a i * b i : ℤ) : ℝ) := by
  simp [dot, castVec, Int.cast_sum, Int.cast_mul]

theorem cosine_wrap (h n : IntVec) (f : Vec) :
    Real.cos (2 * Real.pi * dot (castVec h) (f + castVec n)) =
      Real.cos (2 * Real.pi * dot (castVec h) f) := by
  rw [dot_add_right, dot_integer]
  let m : ℤ := ∑ i, h i * n i
  change Real.cos (2 * Real.pi * (dot (castVec h) f + (m : ℝ))) = _
  rw [show 2 * Real.pi * (dot (castVec h) f + (m : ℝ)) =
    2 * Real.pi * dot (castVec h) f + (m : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_add_int_mul_two_pi _ _

def addPeriodIndex (n : IntVec) : IntVec ≃ IntVec where
  toFun h := h + n
  invFun h := h - n
  left_inv h := add_sub_cancel_right h n
  right_inv h := sub_add_cancel h n

def wrap (q : TwoSite) (n : IntVec) : TwoSite := ⟨q.basis, q.offset + castVec n⟩

def seriesDirectTerm (q : TwoSite) (n : IntVec) : ℝ :=
  if n = 0 then 0 else gKernel (1/2) (Real.pi * quad (gram q.basis) (castVec n))

def seriesCrossTerm (q : TwoSite) (n : IntVec) : ℝ :=
  gKernel (1/2) (Real.pi * quad (gram q.basis) (castVec n + q.offset))

def seriesReciprocalTerm (q : TwoSite) (n : IntVec) : ℝ :=
  if n = 0 then 0 else gKernel 1 (Real.pi * quad (gram q.basis)⁻¹ (castVec n))

def seriesCosineTerm (q : TwoSite) (n : IntVec) : ℝ :=
  Real.cos (2 * Real.pi * dot (castVec n) q.offset) * seriesReciprocalTerm q n

theorem seriesCross_wrap (q : TwoSite) (n : IntVec) :
    (∑' h, seriesCrossTerm (wrap q n) h) = ∑' h, seriesCrossTerm q h := by
  calc
    _ = ∑' h, seriesCrossTerm q (addPeriodIndex n h) := by
      apply tsum_congr
      intro h
      simp [seriesCrossTerm, wrap, addPeriodIndex, castVec_add, add_comm, add_left_comm]
    _ = _ := (addPeriodIndex n).tsum_eq (seriesCrossTerm q)

theorem energy_wrap (q : TwoSite) (n : IntVec) : energy (wrap q n) = energy q := by
  have hCross := seriesCross_wrap q n
  change (∑' h, gKernel (1/2) (Real.pi * quad (gram q.basis) (castVec h + (q.offset + castVec n)))) =
    (∑' h, gKernel (1/2) (Real.pi * quad (gram q.basis) (castVec h + q.offset))) at hCross
  simp only [energy, h₂, wrap]
  unfold gram at hCross
  rw [hCross]
  simp only [cosine_wrap]

theorem series_reciprocal_split (q : TwoSite) (hR : Summable (seriesReciprocalTerm q))
    (hC : Summable (seriesCosineTerm q)) :
    h₂ q = (∑' n, seriesDirectTerm q n) + (∑' n, seriesCrossTerm q n) +
      ((∑' n, seriesReciprocalTerm q n) + (∑' n, seriesCosineTerm q n)) := by
  unfold h₂
  change (∑' n, seriesDirectTerm q n) + (∑' n, seriesCrossTerm q n) + _ = _
  rw [← hR.tsum_add hC]
  congr 1
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [seriesReciprocalTerm, seriesCosineTerm, hn]
  · simp [seriesReciprocalTerm, seriesCosineTerm, gram, hn]
    ring

/-- CoulombGreen and CoulombUniqueness in the repository are the proof model
for this general lattice statement. The limit excludes all periods. -/
structure GreenAnalysis (α : ℝ) (B : Mat) : Prop where
  even : ∀ x, x ∉ lattice B → periodicGreen α B (-x) = periodicGreen α B x
  regular : Filter.Tendsto
    (fun x => periodicGreen α B x - 1 / Real.sqrt (sq x))
    (𝓝[Set.univ \ lattice B] (0 : Vec)) (𝓝 (ewaldRegularSelf α B))
  period : ∀ y ∈ lattice B, ∀ x, x ∉ lattice B →
    periodicGreen α B (x + y) = periodicGreen α B x
  screening_independent : ∀ β > 0, ∀ x, x ∉ lattice B →
    periodicGreen α B x = periodicGreen β B x
  coefficients : ∀ n, cellFourierCoefficient B (periodicGreen α B) n =
    if n = 0 then 0 else ((4 * Real.pi / (volumeOf B * sq (dualWave B n)) : ℝ) : ℂ)

/-- Intermediate identities from the scaled direct/reciprocal arguments and
the erfc and exponential integral identities. The two subtractive constants
are tied to the physical screened potential and the regular self term. -/
structure SeriesModeIdentification (q : TwoSite) : Prop where
  reciprocalSummable : Summable (seriesReciprocalTerm q)
  cosineSummable : Summable (seriesCosineTerm q)
  greenOffset : periodicGreen seriesScreen (physicalBasis q) (physicalTwoPositions q 1) =
    ((∑' n, seriesCrossTerm q n) + (∑' n, seriesCosineTerm q n) - 1) / ac
  greenNegativeOffset : periodicGreen seriesScreen (physicalBasis q) (-physicalTwoPositions q 1) =
    periodicGreen seriesScreen (physicalBasis q) (physicalTwoPositions q 1)
  regularSelf : ewaldRegularSelf seriesScreen (physicalBasis q) =
    ((∑' n, seriesDirectTerm q n) + (∑' n, seriesReciprocalTerm q n) - 3) / ac

theorem green_two_eq_h₂ (q : TwoSite) (m : SeriesModeIdentification q) (ha : ac ≠ 0) :
    greenPerParticle seriesScreen (physicalBasis q) (physicalTwoPositions q) = energy q := by
  have h0 : physicalTwoPositions q 0 = 0 := by simp [physicalTwoPositions, normalizedTwoPositions]
  unfold greenPerParticle greenCellEnergy energy
  simp [Fin.sum_univ_two, h0]
  rw [m.greenNegativeOffset, m.greenOffset, m.regularSelf,
    series_reciprocal_split q m.reciprocalSummable m.cosineSummable]
  field_simp [ha] <;> ring

end BccSharp.Coulomb
