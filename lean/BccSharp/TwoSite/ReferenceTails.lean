import BccSharp.TwoSite.Pi
import BccSharp.Analysis.GaussianSummability

set_option autoImplicit false

/-! Exact Constants indexing and signed tail proof for the first recorded
split parameter at BCC and FCC. The tails are bounded independently of the
rounded scalar tail diagnostics in the published receipt. -/

noncomputable section
open scoped BigOperators
open Classical

namespace BccSharp.Coulomb.Constants
open BccSharp
open BccSharp.Intervals (Ball)

def Reference.realRadius (ref : Reference) (z : Triple) : ℚ := ref.directForm (asVector z)
def Reference.dualRadius (ref : Reference) (z : Triple) : ℚ := ref.dualForm (asVector z)

theorem directPoints_iff (ref : Reference) (z : Triple) :
    z ∈ ref.directPoints ↔ z ≠ 0 ∧ ref.realRadius z ≤ ref.realCut := by
  simp only [Reference.directPoints, Finset.mem_filter, Reference.realRadius]
  refine ⟨And.right, ?_⟩
  intro h
  refine ⟨?_, h⟩
  have hx := direct_cube_complete ref (asVector z) h.2 0
  have hy := direct_cube_complete ref (asVector z) h.2 1
  have hz := direct_cube_complete ref (asVector z) h.2 2
  simpa [cube, asVector, Finset.mem_product, Finset.mem_Icc] using And.intro hx (And.intro hy hz)

theorem reciprocalPoints_iff (ref : Reference) (z : Triple) :
    z ∈ ref.reciprocalPoints ↔ z ≠ 0 ∧ ref.dualRadius z ≤ ref.reciprocalCut := by
  simp only [Reference.reciprocalPoints, Finset.mem_filter, Reference.dualRadius]
  refine ⟨And.right, ?_⟩
  intro h
  refine ⟨?_, h⟩
  have hx := reciprocal_cube_complete ref (asVector z) h.2 0
  have hy := reciprocal_cube_complete ref (asVector z) h.2 1
  have hz := reciprocal_cube_complete ref (asVector z) h.2 2
  simpa [cube, asVector, Finset.mem_product, Finset.mem_Icc] using And.intro hx (And.intro hy hz)

theorem gram_inverse_eq (ref : Reference) : (gram ref.naturalBasis)⁻¹ = ref.reciprocalGram := by
  rw [natural_gram_eq]
  exact Matrix.inv_eq_right_inv (gram_dual_product ref)

def shellKeys (points : Finset Triple) (radius : Triple → ℚ) := points.image radius
def multiplicity (points : Finset Triple) (radius : Triple → ℚ) (r : ℚ) : ℕ :=
  (points.filter fun z => radius z = r).card

theorem shell_fold (points : Finset Triple) (radius : Triple → ℚ) (value : ℚ → ℝ) :
    (∑ r ∈ shellKeys points radius, (multiplicity points radius r : ℝ) * value r) =
      ∑ z ∈ points, value (radius z) := by
  have h := Finset.sum_fiberwise_of_maps_to' (s := points) (t := shellKeys points radius) (g := radius)
    (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩) value
  simpa [multiplicity, Finset.sum_const, nsmul_eq_mul] using h

theorem radiusSum (ref : Reference) (z : Triple) :
    LatticeTails.normSq z ≤ 3 * (ref.directDiagonal : ℝ) * (ref.realRadius z : ℝ) ∧
    LatticeTails.normSq z ≤ 3 * (ref.dualDiagonal : ℝ) * (ref.dualRadius z : ℝ) := by
  have d i : ((asVector z i : ℤ) : ℝ)^2 ≤ (ref.directDiagonal : ℝ) * (ref.realRadius z : ℝ) := by
    exact_mod_cast direct_coordinate_bound ref (asVector z) i
  have r i : ((asVector z i : ℤ) : ℝ)^2 ≤ (ref.dualDiagonal : ℝ) * (ref.dualRadius z : ℝ) := by
    exact_mod_cast reciprocal_coordinate_bound ref (asVector z) i
  unfold LatticeTails.normSq
  constructor
  · have h0 := d 0; have h1 := d 1; have h2 := d 2
    norm_num [asVector] at h0 h1 h2
    linarith
  · have h0 := r 0; have h1 := r 1; have h2 := r 2
    norm_num [asVector] at h0 h1 h2
    linarith

theorem realRadius_nonneg (ref : Reference) (z : Triple) : (0 : ℝ) ≤ ref.realRadius z := by
  have h := (radiusSum ref z).1
  have h0 : 0 ≤ LatticeTails.normSq z := by unfold LatticeTails.normSq; positivity
  cases ref <;> norm_num [Reference.directDiagonal] at h <;> linarith

theorem dualRadius_nonneg (ref : Reference) (z : Triple) : (0 : ℝ) ≤ ref.dualRadius z := by
  have h := (radiusSum ref z).2
  have h0 : 0 ≤ LatticeTails.normSq z := by unfold LatticeTails.normSq; positivity
  cases ref <;> norm_num [Reference.dualDiagonal] at h <;> linarith

def Reference.realExponent (ref : Reference) (z : Triple) : ℝ :=
  (ref.alpha : ℝ)^2 * (ref.realRadius z : ℝ)
def Reference.dualExponent (ref : Reference) (z : Triple) : ℝ :=
  Real.pi^2 / (ref.alpha : ℝ)^2 * (ref.dualRadius z : ℝ)

theorem real_spend (ref : Reference) (z : Triple) :
    LatticeTails.normSq z/20 ≤ ref.realExponent z/10 := by
  have hα : (3/2 : ℝ) * (ref.directDiagonal : ℝ) ≤ (ref.alpha : ℝ)^2 := by
    cases ref <;> norm_num [Reference.alpha, Reference.directDiagonal]
  have h := mul_le_mul_of_nonneg_right hα (realRadius_nonneg ref z)
  unfold Reference.realExponent
  linarith [(radiusSum ref z).1]

theorem reciprocal_spend (ref : Reference) (z : Triple) :
    LatticeTails.normSq z/20 ≤ ref.dualExponent z/10 := by
  have hα : (0 : ℝ) < (ref.alpha : ℝ)^2 := by cases ref <;> norm_num [Reference.alpha]
  have hπ : (9 : ℝ) < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hc : (3/2 : ℝ) * (ref.dualDiagonal : ℝ) * (ref.alpha : ℝ)^2 ≤ 9 := by
    cases ref <;> norm_num [Reference.alpha, Reference.dualDiagonal]
  have hd := (le_div_iff₀ hα).mpr (hc.trans hπ.le)
  have h := mul_le_mul_of_nonneg_right hd (dualRadius_nonneg ref z)
  unfold Reference.dualExponent
  linarith [(radiusSum ref z).2]

theorem real_cutoff (ref : Reference) (z : Triple) (hz : z ≠ 0) (hout : z ∉ ref.directPoints) :
    (160 : ℝ) ≤ ref.realExponent z := by
  have hQ : ref.realCut ≤ ref.realRadius z := le_of_lt (lt_of_not_ge fun h => hout ((directPoints_iff ref z).mpr ⟨hz, h⟩))
  have h : (160 : ℝ) = (ref.alpha : ℝ)^2 * (ref.realCut : ℝ) := by exact_mod_cast (first_real_cut_exact ref).symm
  rw [h]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQ) (sq_nonneg _)

theorem reciprocal_cutoff (ref : Reference) (z : Triple) (hz : z ≠ 0) (hout : z ∉ ref.reciprocalPoints) :
    (160 : ℝ) ≤ ref.dualExponent z := by
  have hQ : ref.reciprocalCut ≤ ref.dualRadius z :=
    le_of_lt (lt_of_not_ge fun h => hout ((reciprocalPoints_iff ref z).mpr ⟨hz, h⟩))
  have hp : (314159265/100000000 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hp2 : (314159265/100000000 : ℝ)^2 ≤ Real.pi^2 := by nlinarith [Real.pi_pos]
  have hc : (160 : ℝ) ≤ (314159265/100000000 : ℝ)^2 / (ref.alpha : ℝ)^2 * (ref.reciprocalCut : ℝ) := by
    cases ref <;> norm_num [Reference.alpha, Reference.reciprocalCut]
  have hcut : (0 : ℝ) ≤ (ref.reciprocalCut : ℝ) := by cases ref <;> norm_num [Reference.reciprocalCut]
  refine hc.trans ?_
  unfold Reference.dualExponent
  exact mul_le_mul (div_le_div_of_nonneg_right hp2 (sq_nonneg _)) (by exact_mod_cast hQ) hcut (by positivity)

def Reference.realTerm (ref : Reference) (z : Triple) : ℝ :=
  if z = 0 then 0 else ref.directValue (ref.realRadius z)
def Reference.dualTerm (ref : Reference) (z : Triple) : ℝ :=
  if z = 0 then 0 else ref.reciprocalValue (ref.dualRadius z)

theorem realTerm_nonneg (ref : Reference) (z : Triple) : 0 ≤ ref.realTerm z := by
  unfold Reference.realTerm
  split_ifs
  · exact le_rfl
  · unfold Reference.directValue
    exact div_nonneg (by rw [erfc_agrees]; exact Ewald.erfc_nonneg _) (by positivity)

theorem dualTerm_nonneg (ref : Reference) (z : Triple) : 0 ≤ ref.dualTerm z := by
  unfold Reference.dualTerm
  split_ifs
  · exact le_rfl
  · unfold Reference.reciprocalValue
    exact div_nonneg (Real.exp_pos _).le (by
      have h := dualRadius_nonneg ref z
      cases ref <;> unfold Reference.naturalVolume <;> positivity)

theorem realTerm_omitted (ref : Reference) (z : Triple) (hz : z ≠ 0) (hout : z ∉ ref.directPoints) :
    ref.realTerm z ≤ Real.exp (-ref.realExponent z) := by
  have hQ : (1 : ℝ) ≤ ref.realRadius z := by
    have hcut : ref.realCut ≤ ref.realRadius z :=
      le_of_lt (lt_of_not_ge fun h => hout ((directPoints_iff ref z).mpr ⟨hz,h⟩))
    have hr : (1 : ℚ) ≤ ref.realCut := by cases ref <;> norm_num [Reference.realCut]
    exact_mod_cast hr.trans hcut
  have hα : (1 : ℝ) ≤ ref.alpha := by cases ref <;> norm_num [Reference.alpha]
  have hs : (1 : ℝ) ≤ Real.sqrt Real.pi := by nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_gt_three]
  let r := Real.sqrt (ref.realRadius z : ℝ)
  have rpos : 0 < r := Real.sqrt_pos.mpr (zero_lt_one.trans_le hQ)
  have ha : 0 < (ref.alpha : ℝ)*r := mul_pos (zero_lt_one.trans_le hα) rpos
  have hp : 1 ≤ 2 * (ref.alpha : ℝ) * Real.sqrt Real.pi * (ref.realRadius z : ℝ) := by
    have a := one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 2) hα
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a hs) hQ
  unfold Reference.realTerm Reference.directValue
  rw [if_neg hz]
  change Gaussian.erfcIntegral ((ref.alpha : ℝ)*r)/(2*r) ≤ _
  calc
    _ ≤ (Real.exp (-((ref.alpha : ℝ)*r)^2)/(((ref.alpha : ℝ)*r)*Real.sqrt Real.pi))/(2*r) :=
      div_le_div_of_nonneg_right (Gaussian.erfc_upper ha) (by positivity)
    _ = Real.exp (-ref.realExponent z)/(2*(ref.alpha : ℝ)*Real.sqrt Real.pi*(ref.realRadius z : ℝ)) := by
      rw [mul_pow, show r^2 = (ref.realRadius z : ℝ) from Real.sq_sqrt (realRadius_nonneg ref z)]
      unfold Reference.realExponent
      rw [div_div]
      congr 1
      rw [← show r^2 = (ref.realRadius z : ℝ) from Real.sq_sqrt (realRadius_nonneg ref z)]
      ring
    _ ≤ _ := div_le_self (Real.exp_pos _).le hp

theorem dualTerm_omitted (ref : Reference) (z : Triple) (hz : z ≠ 0) (hout : z ∉ ref.reciprocalPoints) :
    ref.dualTerm z ≤ Real.exp (-ref.dualExponent z) := by
  have hQ : (1 : ℝ) ≤ ref.dualRadius z := by
    have hcut : ref.reciprocalCut ≤ ref.dualRadius z :=
      le_of_lt (lt_of_not_ge fun h => hout ((reciprocalPoints_iff ref z).mpr ⟨hz,h⟩))
    have hr : (1 : ℚ) ≤ ref.reciprocalCut := by cases ref <;> norm_num [Reference.reciprocalCut]
    exact_mod_cast hr.trans hcut
  have hbase : (1 : ℝ) ≤ 2*Real.pi*(ref.naturalVolume : ℝ) := by
    cases ref <;> norm_num [Reference.naturalVolume] <;> linarith [Real.pi_gt_three]
  unfold Reference.dualTerm Reference.reciprocalValue Reference.dualExponent
  have he : Real.pi^2 * (ref.dualRadius z : ℝ) / (ref.alpha : ℝ)^2 =
      Real.pi^2 / (ref.alpha : ℝ)^2 * (ref.dualRadius z : ℝ) := by ring
  rw [if_neg hz, he]
  exact div_le_self (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le hbase hQ)

private theorem omitted_dominated {f : Triple → ℝ} {t : Triple → ℝ} {kept : Finset Triple}
    (origin : f 0 = 0) (hterm : ∀ z, z ≠ 0 → z ∉ kept → f z ≤ Real.exp (-t z))
    (cut : ∀ z, z ≠ 0 → z ∉ kept → 160 ≤ t z)
    (spend : ∀ z, LatticeTails.normSq z/20 ≤ t z/10) :
    ∀ z : {z // z ∉ kept}, f z.val ≤ Real.exp (-129) * LatticeTails.weight z.val := by
  intro z
  by_cases hz : z.val = 0
  · rw [hz, origin]
    exact mul_nonneg (Real.exp_pos _).le (LatticeTails.weight_nonneg _)
  · calc
      _ ≤ Real.exp (-t z.val) := hterm z.val hz z.property
      _ ≤ Real.exp (-(9/10 : ℝ)*160)*Real.exp (-t z.val/10) := HighPrecision.exponential_cutoff (cut z.val hz z.property)
      _ ≤ Real.exp (-(9/10 : ℝ)*160)*Real.exp (-(1/20 : ℝ)*LatticeTails.normSq z.val) := by
        gcongr
        linarith [spend z.val]
      _ ≤ Real.exp (-(9/10 : ℝ)*160)*
          (Real.exp (3/(4*(1/20 : ℝ)))*LatticeTails.weight z.val) :=
        mul_le_mul_of_nonneg_left (LatticeTails.scaled_gaussian_le_weight (by norm_num) z.val) (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]; norm_num

private theorem positive_omitted_sum {f : Triple → ℝ} {kept : Finset Triple}
    (hn : ∀ z, 0 ≤ f z) (bound : ∀ z : {z // z ∉ kept}, f z.val ≤ Real.exp (-129) * LatticeTails.weight z.val) :
    Summable (fun z : {z // z ∉ kept} => f z.val) ∧
    0 ≤ (∑' z : {z // z ∉ kept}, f z.val) ∧
    (∑' z : {z // z ∉ kept}, f z.val) ≤ Real.exp (-129) * 27 := by
  have hW := LatticeTails.weight_summable.mul_left (Real.exp (-129))
  have hw := hW.subtype (fun z => z ∉ kept)
  have hs := Summable.of_nonneg_of_le (fun z => hn z.val) bound hw
  refine ⟨hs, tsum_nonneg (fun z => hn z.val), ?_⟩
  calc
    _ ≤ ∑' z : {z // z ∉ kept}, Real.exp (-129) * LatticeTails.weight z.val := hs.tsum_le_tsum bound hw
    _ ≤ ∑' z : Triple, Real.exp (-129) * LatticeTails.weight z :=
      Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun z _ => mul_nonneg (Real.exp_pos _).le (LatticeTails.weight_nonneg _)) (fun _ => le_rfl) hw hW
    _ = _ := by rw [tsum_mul_left, LatticeTails.tsum_weight]

theorem real_tail (ref : Reference) :
    Summable (fun z : {z // z ∉ ref.directPoints} => ref.realTerm z.val) ∧
    0 ≤ (∑' z : {z // z ∉ ref.directPoints}, ref.realTerm z.val) ∧
    (∑' z : {z // z ∉ ref.directPoints}, ref.realTerm z.val) ≤ Real.exp (-129) * 27 :=
  positive_omitted_sum (realTerm_nonneg ref) (omitted_dominated (by simp [Reference.realTerm])
    (realTerm_omitted ref) (real_cutoff ref) (real_spend ref))

theorem reciprocal_tail (ref : Reference) :
    Summable (fun z : {z // z ∉ ref.reciprocalPoints} => ref.dualTerm z.val) ∧
    0 ≤ (∑' z : {z // z ∉ ref.reciprocalPoints}, ref.dualTerm z.val) ∧
    (∑' z : {z // z ∉ ref.reciprocalPoints}, ref.dualTerm z.val) ≤ Real.exp (-129) * 27 :=
  positive_omitted_sum (dualTerm_nonneg ref) (omitted_dominated (by simp [Reference.dualTerm])
    (dualTerm_omitted ref) (reciprocal_cutoff ref) (reciprocal_spend ref))

def exactTailUpper : ℚ := 54 * (3/8 : ℚ)^129

theorem two_tails_rational : 2 * (Real.exp (-129) * 27) ≤ (exactTailUpper : ℝ) := by
  have hh := SpecialFunctions.exp_taylor (q := (1 : ℚ)) (n := 6) (by norm_num) (by norm_num)
  have he := (SpecialFunctions.contains_iff_endpoints _ _).mp hh
  norm_num [SpecialFunctions.taylor, SpecialFunctions.taylorError, Finset.sum_range_succ] at he
  have h8 : (8/3 : ℝ) ≤ Real.exp 1 := by linarith [he.1]
  have hi : Real.exp (-1) ≤ (3/8 : ℝ) := by
    rw [Real.exp_neg]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8/3) h8
    simpa [one_div] using hh
  have hP : Real.exp (-129) ≤ (3/8 : ℝ)^129 := by
    calc
      _ = (Real.exp (-1))^129 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hi _
  unfold exactTailUpper
  push_cast
  linarith

theorem tail_small : exactTailUpper < 1 / 10^53 := by norm_num [exactTailUpper]

def Reference.fullNatural (ref : Reference) : ℝ :=
  (∑' z, ref.realTerm z) + (∑' z, ref.dualTerm z) -
    (ref.alpha : ℝ) / Real.sqrt Real.pi - Real.pi / (2 * (ref.naturalVolume : ℝ) * (ref.alpha : ℝ)^2)

def Reference.primitiveWS (ref : Reference) : ℝ := ref.wsFactor * ref.fullNatural

theorem wsFactor_nonneg_le_one (ref : Reference) : 0 ≤ ref.wsFactor ∧ ref.wsFactor ≤ 1 := by
  have hV : (0 : ℝ) ≤ (ref.naturalVolume : ℝ) ∧ (ref.naturalVolume : ℝ) ≤ 1 := by
    cases ref <;> norm_num [Reference.naturalVolume]
  have ha : (0 : ℝ) ≤ 3 * (ref.naturalVolume : ℝ) / (4 * Real.pi) :=
    div_nonneg (mul_nonneg (by norm_num) hV.1) (by positivity)
  have hb : 3 * (ref.naturalVolume : ℝ) / (4 * Real.pi) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)).mpr
    linarith [Real.pi_gt_three, hV.2]
  exact ⟨Real.rpow_nonneg ha _, Real.rpow_le_one ha hb (by norm_num)⟩

theorem wsFactor_cube (ref : Reference) : ref.wsFactor^3 = 3 * (ref.naturalVolume : ℝ) / (4 * Real.pi) := by
  have hV : (0 : ℝ) ≤ (ref.naturalVolume : ℝ) := by cases ref <;> norm_num [Reference.naturalVolume]
  unfold Reference.wsFactor
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem finite_and_tail (ref : Reference) :
    (⟨0, exactTailUpper⟩ : Interval).contains (ref.primitiveWS - ref.finiteEnergy) := by
  have hR := real_tail ref
  have hD := reciprocal_tail ref
  have hsR := summable_of_finset_compl ref.directPoints ref.realTerm hR.1
  have hsD := summable_of_finset_compl ref.reciprocalPoints ref.dualTerm hD.1
  have splitR := hsR.sum_add_tsum_subtype_compl ref.directPoints
  have splitD := hsD.sum_add_tsum_subtype_compl ref.reciprocalPoints
  have fr : (∑ z ∈ ref.directPoints, ref.realTerm z) =
      ∑ z ∈ ref.directPoints, ref.directValue (ref.realRadius z) := by
    apply Finset.sum_congr rfl
    intro z hz
    simp [Reference.realTerm, ((directPoints_iff ref z).mp hz).1]
  have fd : (∑ z ∈ ref.reciprocalPoints, ref.dualTerm z) =
      ∑ z ∈ ref.reciprocalPoints, ref.reciprocalValue (ref.dualRadius z) := by
    apply Finset.sum_congr rfl
    intro z hz
    simp [Reference.dualTerm, ((reciprocalPoints_iff ref z).mp hz).1]
  let u := (∑' z : {z // z ∉ ref.directPoints}, ref.realTerm z.val) +
    (∑' z : {z // z ∉ ref.reciprocalPoints}, ref.dualTerm z.val)
  have hsplit : ref.primitiveWS - ref.finiteEnergy = ref.wsFactor * u := by
    unfold Reference.primitiveWS Reference.fullNatural Reference.finiteEnergy
    rw [← splitR, ← splitD, fr, fd]
    unfold u Reference.realRadius Reference.dualRadius
    ring
  have u0 : 0 ≤ u := add_nonneg hR.2.1 hD.2.1
  have uu : u ≤ (exactTailUpper : ℝ) := by
    exact (add_le_add hR.2.2 hD.2.2).trans (by linarith [two_tails_rational])
  have a := wsFactor_nonneg_le_one ref
  rw [hsplit]
  constructor
  · show ((0 : ℚ) : ℝ) ≤ ref.wsFactor * u
    rw [Rat.cast_zero]
    exact mul_nonneg a.1 u0
  · show ref.wsFactor * u ≤ ((exactTailUpper : ℚ) : ℝ)
    exact (mul_le_of_le_one_left u0 a.2).trans uu

end BccSharp.Coulomb.Constants
