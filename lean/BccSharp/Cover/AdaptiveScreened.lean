import BccSharp.Cover.AdaptiveGain
import BccSharp.TwoSite.ScreenedSeries

set_option autoImplicit false

/-! The screened Adaptive support (route `I`, at Ewald screening
`s = 11/10`).

At screening `s` the Series identity reads (`ScreenedSeries.finite_lower_lex`)

  `h₂ − 4 ≥ s Σ_cross g½(π s² R) + 2s Σ_period g½(π s² R) + (2/s²) Σ_waves φ g₁(π R*/s²) − 2s − 2/s²`

over any finite sets of distinct modes (lex-positive for period and wave modes). So the
support of `BccSharp.Cover.AdaptiveSupport` applies with three changes: the multipliers are
`s, 2s, 2ℓ/s²` (`Term.muI`, at scale `S` and rounded down), the kernel argument of a mode is
`π σ R` with `σ = s²` (direct) or `1/s²` (reciprocal) (`Term.sigN / Term.sigD`), so the corner
weights carry the factor `σ` (`Term.wtermI`), and the bound gains the constant
`4 − 2s − 2/s² = 89/605` (`screenConstS`). `screenCheck_sound`: if `screenCheck` accepts a box,
then `energy fcc < energy (chartPoint p)` at every `good` point of it. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BccSharp.Coverage BravaisCover DirectRoute Stage2 OverlayPlanar.Fix

/-! ### The evaluator -/

/-- The multiplier at screening `11/10`, at scale `S`: `s`, `2s`, `2ℓ/s²`, rounded down. -/
def Term.muI (bx : Cell) (t : Term) : ℤ :=
  match t.fam with
  | .cross => 11 * Sz / 10
  | .period => 11 * Sz / 5
  | .reciprocal => 200 * phaseLoS bx t / 121

/-- The rate factor `σ = sigN / sigD`: `s² = 121/100` (direct), `1/s² = 100/121` (reciprocal). -/
def Term.sigN (t : Term) : ℤ :=
  match t.fam with
  | .reciprocal => 100
  | _ => 121

def Term.sigD (t : Term) : ℤ :=
  match t.fam with
  | .reciprocal => 121
  | _ => 100

def Term.kLoI (bx : Cell) (t : Term) : ℤ := t.muI bx * t.G.lo / Sz
def Term.kHiI (bx : Cell) (t : Term) : ℤ := cdivZ (t.muI bx * t.G.hi) Sz
def Term.aLoI (bx : Cell) (t : Term) : ℤ := t.muI bx * t.W.lo * (t.anchor : ℤ) / (Sz * (RA : ℤ))
def Term.wtermI (bx : Cell) (t : Term) : WTerm :=
  ⟨t.fam, t.a, t.b, t.c, cdivZ (t.muI bx * t.W.hi * (piHiN : ℤ) * t.sigN) (Sz * Sz * t.sigD)⟩

def Acc.stepI (bx : Cell) (acc : Acc) (t : Term) : Acc :=
  ⟨acc.kLo + t.kLoI bx, acc.kHi + t.kHiI bx, acc.aLo + t.aLoI bx, acc.ok && t.ok, t.wtermI bx :: acc.ws⟩

/-- `4 − 2s − 2/s² = 89/605` at `s = 11/10`, at scale `S`, rounded down. -/
def screenConstS : ℤ := 89 * Sz / 605

/-- The certified lower bound of `(h₂ − 89/605) · S`, if the guards hold. -/
def screenValue (bx : Cell) (ts : List Term) (c : Option Cut) : Option ℤ :=
  match toIBox bx with
  | none => none
  | some B =>
    let acc := ts.foldl (Acc.stepI bx) Acc.init
    let U := cornerMaxF B (momOf acc.ws) c
    let sLo := acc.aLo - U
    let K' := if 0 ≤ sLo then acc.kHi else acc.kLo
    let E := expLower (sLo * Sz / K')
    if boxGuard bx B && cutGuard c && increasing ts && acc.ok && decide (0 < acc.kLo) &&
        decide (acc.kLo ≤ acc.kHi) then
      some (acc.kLo * E / Sz)
    else none

/-- **The screened support check.** -/
def screenCheck (bx : Cell) (ts : List Term) (c : Option Cut) : Bool :=
  match screenValue bx ts c with
  | some L => decide (fccHZ < L + screenConstS)
  | none => false

/-! ### Soundness: accumulator -/

theorem foldl_stepI (bx : Cell) (ts : List Term) (acc : Acc) :
    (ts.foldl (Acc.stepI bx) acc).kLo = acc.kLo + (ts.map (Term.kLoI bx)).sum ∧
    (ts.foldl (Acc.stepI bx) acc).kHi = acc.kHi + (ts.map (Term.kHiI bx)).sum ∧
    (ts.foldl (Acc.stepI bx) acc).aLo = acc.aLo + (ts.map (Term.aLoI bx)).sum ∧
    (ts.foldl (Acc.stepI bx) acc).ok = (acc.ok && ts.all Term.ok) ∧
    (ts.foldl (Acc.stepI bx) acc).ws = (ts.map (Term.wtermI bx)).reverse ++ acc.ws := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (acc.stepI bx t)
    simp only [List.foldl_cons, Acc.stepI] at h1 h2 h3 h4 h5 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1]; simp; ring
    · rw [h2]; simp; ring
    · rw [h3]; simp; ring
    · rw [h4]; simp [Bool.and_assoc]
    · rw [h5]; simp

/-! ### Soundness: one term -/

def tMuI (bx : Cell) (t : Term) : ℝ := (t.muI bx : ℝ) / Sz
def tSig (t : Term) : ℝ := (t.sigN : ℝ) / t.sigD
def tCI (bx : Cell) (t : Term) : ℝ := tMuI bx t * tG t
def tXI (p : Chart) (t : Term) : ℝ := -(Real.pi * tSig t * tR p t - tT t) * (tW t / tG t)

/-- The screened series term of a retained mode at `s = 11/10`, with its prefactor. -/
def Term.screened (t : Term) (q : TwoSite) : ℝ :=
  match t.fam with
  | .cross => 11 / 10 * ScreenedSeries.crossTerm (11 / 10) q t.mode.index
  | .period => 11 / 5 * ScreenedSeries.periodTerm (11 / 10) q t.mode.index
  | .reciprocal => 200 / 121 * ScreenedSeries.waveTerm (11 / 10) q t.mode.index

theorem tSig_pos (t : Term) : 0 < tSig t := by
  unfold tSig Term.sigN Term.sigD
  cases t.fam <;> norm_num

theorem muI_sound (bx : Cell) (t : Term) {p : Chart} (hp : bx.Mem p) :
    0 ≤ tMuI bx t ∧ (t.fam = .cross → tMuI bx t ≤ 11 / 10) ∧ (t.fam = .period → tMuI bx t ≤ 11 / 5) ∧
      (t.fam = .reciprocal → tMuI bx t ≤ 200 / 121 * phaseFactor (chartPoint p) t.mode.index) := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  have ph := phaseLoS_sound bx t hp
  have l0 : (0:ℤ) ≤ phaseLoS bx t := by exact_mod_cast ph.1
  unfold tMuI Term.muI
  cases hf : t.fam with
  | cross =>
    have f := fdiv_le (11 * Sz) 10 (by norm_num)
    have n0 : (0:ℤ) ≤ 11 * Sz / 10 := Int.ediv_nonneg (by omega) (by norm_num)
    refine ⟨div_nonneg (by exact_mod_cast n0) sp.le, fun _ => ?_, fun h => absurd h (by simp),
      fun h => absurd h (by simp)⟩
    rw [div_le_iff₀ sp]
    calc ((11 * Sz / 10 : ℤ) : ℝ) ≤ ((11 * Sz : ℤ) : ℝ) / ((10 : ℤ) : ℝ) := f
      _ = 11 / 10 * Sz := by push_cast; ring
  | period =>
    have f := fdiv_le (11 * Sz) 5 (by norm_num)
    have n0 : (0:ℤ) ≤ 11 * Sz / 5 := Int.ediv_nonneg (by omega) (by norm_num)
    refine ⟨div_nonneg (by exact_mod_cast n0) sp.le, fun h => absurd h (by simp), fun _ => ?_,
      fun h => absurd h (by simp)⟩
    rw [div_le_iff₀ sp]
    calc ((11 * Sz / 5 : ℤ) : ℝ) ≤ ((11 * Sz : ℤ) : ℝ) / ((5 : ℤ) : ℝ) := f
      _ = 11 / 5 * Sz := by push_cast; ring
  | reciprocal =>
    have f := fdiv_le (200 * phaseLoS bx t) 121 (by norm_num)
    have n0 : (0:ℤ) ≤ 200 * phaseLoS bx t / 121 := Int.ediv_nonneg (by omega) (by norm_num)
    refine ⟨div_nonneg (by exact_mod_cast n0) sp.le, fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun _ => ?_⟩
    have pl := ph.2
    rw [div_le_iff₀ sp]
    calc ((200 * phaseLoS bx t / 121 : ℤ) : ℝ) ≤ ((200 * phaseLoS bx t : ℤ) : ℝ) / ((121 : ℤ) : ℝ) := f
      _ = 200 / 121 * ((phaseLoS bx t : ℝ) / Sz) * Sz := by push_cast; field_simp
      _ ≤ 200 / 121 * phaseFactor (chartPoint p) t.mode.index * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          exact mul_le_mul_of_nonneg_left pl (by norm_num)

/-- A screened series term is at least `μ` times its kernel at `π σ R`; `π σ R > 0`. -/
theorem screened_term_lower (bx : Cell) (hd : diagonalsCheck bx = true) (t : Term) (hm : t.mode.valid)
    (p : Chart) (hp : bx.Mem p) (hv : (chartPoint p).Valid) (μ : ℝ) (_hμ : 0 ≤ μ)
    (hμv : (t.fam = .cross → μ ≤ 11 / 10) ∧ (t.fam = .period → μ ≤ 11 / 5) ∧
      (t.fam = .reciprocal → μ ≤ 200 / 121 * phaseFactor (chartPoint p) t.mode.index)) :
    0 < Real.pi * tSig t * tR p t ∧
      μ * kernelValue (famKind t.fam) (Real.pi * tSig t * tR p t) ≤ t.screened (chartPoint p) := by
  set idx := t.mode.index with hidx
  have modeEq : t.mode = ⟨t.fam, idx⟩ := rfl
  cases hf : t.fam with
  | cross =>
    have pos := cross_distance_positive hv idx
    have radial : tR p t = quad (gram (chartBasis p)) (chartVector p true idx) := by
      unfold tR
      rw [modeEq, hf]
      simp only [Mode.radial]
      exact squaredRadial_eq p true _
    have sig : tSig t = 121 / 100 := by unfold tSig Term.sigN Term.sigD; rw [hf]; norm_num
    have term : t.screened (chartPoint p) =
        11 / 10 * gKernel (1/2) (Real.pi * (121 / 100) * quad (gram (chartBasis p)) (chartVector p true idx)) := by
      unfold Term.screened ScreenedSeries.crossTerm
      rw [hf]
      simp only [chartVector, ite_true]
      norm_num
      rfl
    rw [radial, sig, term]
    have arg : 0 < Real.pi * (121 / 100) * quad (gram (chartBasis p)) (chartVector p true idx) := by
      have := Real.pi_pos; positivity
    refine ⟨arg, ?_⟩
    have k0 := value_nonnegative .half arg
    show μ * kernelValue .half _ ≤ _
    rw [kernel_half_eq] at k0 ⊢
    nlinarith [hμv.1 hf]
  | period =>
    have lex : lexPositive idx := hm.2.resolve_left (by simp [Term.mode, hf])
    have pos := period_distance_positive hv idx lex
    have radial : tR p t = quad (gram (chartBasis p)) (chartVector p false idx) := by
      unfold tR
      rw [modeEq, hf]
      simp only [Mode.radial]
      exact squaredRadial_eq p false _
    have sig : tSig t = 121 / 100 := by unfold tSig Term.sigN Term.sigD; rw [hf]; norm_num
    have term : t.screened (chartPoint p) =
        11 / 5 * gKernel (1/2) (Real.pi * (121 / 100) * quad (gram (chartBasis p)) (chartVector p false idx)) := by
      unfold Term.screened ScreenedSeries.periodTerm
      rw [hf, ite_eq_right (lex_ne lex)]
      simp only [chartVector, Bool.false_eq_true, ite_false]
      norm_num
      rfl
    rw [radial, sig, term]
    have arg : 0 < Real.pi * (121 / 100) * quad (gram (chartBasis p)) (chartVector p false idx) := by
      have := Real.pi_pos; positivity
    refine ⟨arg, ?_⟩
    have k0 := value_nonnegative .half arg
    show μ * kernelValue .half _ ≤ _
    rw [kernel_half_eq] at k0 ⊢
    nlinarith [hμv.2.1 hf]
  | reciprocal =>
    have lex : lexPositive idx := hm.2.resolve_left (by simp [Term.mode, hf])
    have pos := reciprocalPositive hv (lex_ne lex)
    obtain ⟨h0, h1⟩ := radialLoPos bx hd
    have d0 := h0.trans_le (hp 0).1
    have d1 := h1.trans_le (hp 1).1
    have radial : tR p t = quad (gram (chartPoint p).basis)⁻¹ (castVec idx) := by
      unfold tR
      rw [modeEq, hf]
      simp only [Mode.radial]
      exact dualRadial_eq _ p d0.ne' d1.ne'
    have sig : tSig t = 100 / 121 := by unfold tSig Term.sigN Term.sigD; rw [hf]; norm_num
    have term : t.screened (chartPoint p) =
        200 / 121 * (phaseFactor (chartPoint p) idx *
          gKernel 1 (Real.pi * (100 / 121) * quad (gram (chartPoint p).basis)⁻¹ (castVec idx))) := by
      unfold Term.screened ScreenedSeries.waveTerm
      rw [hf, ite_eq_right (lex_ne lex)]
      have e : Real.pi * quad (gram (chartPoint p).basis)⁻¹ (castVec idx) / (11 / 10) ^ 2 =
          Real.pi * (100 / 121) * quad (gram (chartPoint p).basis)⁻¹ (castVec idx) := by ring
      rw [e]
      rfl
    rw [radial, sig, term]
    have arg : 0 < Real.pi * (100 / 121) * quad (gram (chartPoint p).basis)⁻¹ (castVec idx) := by
      have := Real.pi_pos; positivity
    refine ⟨arg, ?_⟩
    have k0 := value_nonnegative .one arg
    show μ * kernelValue .one _ ≤ _
    rw [kernel_one_eq] at k0 ⊢
    have hb := hμv.2.2 hf
    nlinarith [mul_le_mul_of_nonneg_right hb k0]

theorem per_termI (bx : Cell) (hd : diagonalsCheck bx = true) (t : Term) (hok : t.ok = true) {p : Chart}
    (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    0 ≤ tMuI bx t ∧ 0 < tG t ∧ 0 < tT t ∧ 0 < tR p t ∧
    tCI bx t * Real.exp (tXI p t) ≤ t.screened (chartPoint p) ∧
    (t.kLoI bx : ℝ) / Sz ≤ tCI bx t ∧ tCI bx t ≤ (t.kHiI bx : ℝ) / Sz ∧
    (t.aLoI bx : ℝ) / Sz ≤ tMuI bx t * tW t * tT t ∧
    Real.pi * tMuI bx t * tW t * tSig t ≤ ((t.wtermI bx).w : ℝ) / Sz ∧ 0 ≤ (t.wtermI bx).w ∧
    tCI bx t * tXI p t = tMuI bx t * tW t * tT t - Real.pi * tMuI bx t * tW t * tSig t * tR p t := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  obtain ⟨Tpos, Gm, Wm, G0, W0⟩ := term_kernels t hok
  have valid : t.mode.valid := term_valid (by
    simp only [Term.ok, Bool.and_eq_true] at hok; exact hok.1.1.1)
  obtain ⟨mu0, muC, muP, muR⟩ := muI_sound bx t hp
  obtain ⟨argPos, termLow⟩ := screened_term_lower bx hd t valid p hp hv (tMuI bx t) mu0 ⟨muC, muP, muR⟩
  have sg := tSig_pos t
  have Glo : (t.G.lo : ℝ) / Sz ≤ tG t := Gm.1
  have Ghi : tG t ≤ (t.G.hi : ℝ) / Sz := Gm.2
  have Wlo : (t.W.lo : ℝ) / Sz ≤ tW t := Wm.1
  have Whi : tW t ≤ (t.W.hi : ℝ) / Sz := Wm.2
  have Gpos : 0 < tG t := lt_of_lt_of_le (div_pos (by exact_mod_cast G0) sp) Glo
  have Wpos : 0 < tW t := lt_of_lt_of_le (div_pos (by exact_mod_cast W0) sp) Wlo
  have rpos : 0 < tR p t := by
    have := argPos
    have : 0 < Real.pi * tSig t := mul_pos Real.pi_pos sg
    nlinarith
  have lt := logTangent (famKind t.fam) Tpos argPos
  have rate : (Real.exp (-(tT t)) + ((famKind t.fam).power : ℝ) * kernelValue (famKind t.fam) (tT t)) /
      (tT t * kernelValue (famKind t.fam) (tT t)) = tW t / tG t := by
    unfold tW tG
    field_simp
  have lt' : tG t * Real.exp (tXI p t) ≤ kernelValue (famKind t.fam) (Real.pi * tSig t * tR p t) := by
    unfold tXI
    rw [← rate]
    exact lt
  have sigN0 : (0:ℤ) < t.sigN := by unfold Term.sigN; cases t.fam <;> norm_num
  have sigD0 : (0:ℤ) < t.sigD := by unfold Term.sigD; cases t.fam <;> norm_num
  refine ⟨mu0, Gpos, Tpos, rpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc tCI bx t * Real.exp (tXI p t) = tMuI bx t * (tG t * Real.exp (tXI p t)) := by unfold tCI; ring
      _ ≤ tMuI bx t * kernelValue (famKind t.fam) (Real.pi * tSig t * tR p t) :=
          mul_le_mul_of_nonneg_left lt' mu0
      _ ≤ _ := termLow
  · have f := fdiv_le (t.muI bx * t.G.lo) Sz spZ
    unfold Term.kLoI tCI tMuI
    rw [div_le_iff₀ sp]
    calc ((t.muI bx * t.G.lo / Sz : ℤ) : ℝ) ≤ ((t.muI bx * t.G.lo : ℤ) : ℝ) / Sz := f
      _ = (t.muI bx : ℝ) / Sz * ((t.G.lo : ℝ) / Sz) * Sz := by push_cast; field_simp
      _ ≤ (t.muI bx : ℝ) / Sz * tG t * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          exact mul_le_mul_of_nonneg_left Glo mu0
  · have f := le_cdiv (t.muI bx * t.G.hi) Sz spZ
    unfold Term.kHiI tCI tMuI
    rw [le_div_iff₀ sp]
    calc (t.muI bx : ℝ) / Sz * tG t * Sz ≤ (t.muI bx : ℝ) / Sz * ((t.G.hi : ℝ) / Sz) * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          exact mul_le_mul_of_nonneg_left Ghi mu0
      _ = ((t.muI bx * t.G.hi : ℤ) : ℝ) / Sz := by push_cast; field_simp
      _ ≤ _ := f
  · have dpos : (0:ℤ) < Sz * (RA : ℤ) := mul_pos spZ (by norm_num [RA])
    have f := fdiv_le (t.muI bx * t.W.lo * (t.anchor : ℤ)) (Sz * (RA : ℤ)) dpos
    unfold Term.aLoI tMuI tT
    rw [div_le_iff₀ sp]
    have Tn : (0:ℝ) ≤ (t.anchor : ℝ) / RA := Tpos.le
    calc ((t.muI bx * t.W.lo * (t.anchor : ℤ) / (Sz * (RA : ℤ)) : ℤ) : ℝ)
        ≤ ((t.muI bx * t.W.lo * (t.anchor : ℤ) : ℤ) : ℝ) / ((Sz * (RA : ℤ) : ℤ) : ℝ) := f
      _ = (t.muI bx : ℝ) / Sz * ((t.W.lo : ℝ) / Sz) * ((t.anchor : ℝ) / RA) * Sz := by
          push_cast; field_simp [RA_pos.ne']
      _ ≤ (t.muI bx : ℝ) / Sz * tW t * ((t.anchor : ℝ) / RA) * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          apply mul_le_mul_of_nonneg_right _ Tn
          exact mul_le_mul_of_nonneg_left Wlo mu0
  · have dpos : (0:ℤ) < Sz * Sz * t.sigD := mul_pos (mul_pos spZ spZ) sigD0
    have f := le_cdiv (t.muI bx * t.W.hi * (piHiN : ℤ) * t.sigN) (Sz * Sz * t.sigD) dpos
    have ph := pi_bounds.2
    rw [S_eq] at ph
    unfold Term.wtermI tMuI tSig
    simp only
    rw [le_div_iff₀ sp]
    have Whn : 0 ≤ (t.W.hi : ℝ) / Sz := Wpos.le.trans Whi
    have sgR : (0:ℝ) ≤ (t.sigN : ℝ) / t.sigD := by
      have a : (0:ℝ) < t.sigN := by exact_mod_cast sigN0
      have b : (0:ℝ) < t.sigD := by exact_mod_cast sigD0
      positivity
    have sD : (t.sigD : ℝ) ≠ 0 := by exact_mod_cast sigD0.ne'
    calc Real.pi * ((t.muI bx : ℝ) / Sz) * tW t * ((t.sigN : ℝ) / t.sigD) * Sz
        ≤ ((piHiN : ℝ) / Sz) * ((t.muI bx : ℝ) / Sz) * ((t.W.hi : ℝ) / Sz) * ((t.sigN : ℝ) / t.sigD) * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          apply mul_le_mul_of_nonneg_right _ sgR
          apply mul_le_mul (mul_le_mul_of_nonneg_right ph mu0) Whi Wpos.le
          exact mul_nonneg ((Real.pi_pos.le).trans ph) mu0
      _ = ((t.muI bx * t.W.hi * (piHiN : ℤ) * t.sigN : ℤ) : ℝ) / ((Sz * Sz * t.sigD : ℤ) : ℝ) := by
          push_cast; field_simp
      _ ≤ _ := f
  · unfold Term.wtermI
    simp only
    apply cdivZ_nonneg _ (mul_pos (mul_pos spZ spZ) sigD0)
    have m0 : 0 ≤ t.muI bx := by
      have := mu0
      unfold tMuI at this
      have h2 : (0:ℝ) ≤ (t.muI bx : ℝ) := by
        have := mul_nonneg this sp.le
        rwa [div_mul_cancel₀ _ sp.ne'] at this
      exact_mod_cast h2
    have wh : 0 ≤ t.W.hi := by
      have : (0:ℝ) ≤ (t.W.hi : ℝ) / Sz := Wpos.le.trans Whi
      have h2 : (0:ℝ) ≤ (t.W.hi : ℝ) := by
        have := mul_nonneg this sp.le
        rwa [div_mul_cancel₀ _ sp.ne'] at this
      exact_mod_cast h2
    have pn : (0:ℤ) ≤ (piHiN : ℤ) := by positivity
    have := sigN0.le
    positivity
  · unfold tCI tXI
    field_simp
    ring

/-! ### Soundness: the evaluation -/

/-- **The Jensen bound of an accepted screened evaluation.** -/
theorem screenValue_sound (bx : Cell) (ts : List Term) (c : Option Cut) (L : ℤ)
    (hL : screenValue bx ts c = some L) (p : Chart) (hp : bx.Mem p) (gp : good p) :
    diagonalsCheck bx = true ∧ increasing ts = true ∧ (∀ t ∈ ts, t.ok = true) ∧
      (∃ B, toIBox bx = some B ∧ ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0) ∧
      (L : ℝ) / Sz ≤ (ts.map fun t => tCI bx t * Real.exp (tXI p t)).sum := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  unfold screenValue at hL
  cases hB : toIBox bx with
  | none => rw [hB] at hL; simp at hL
  | some B =>
    rw [hB] at hL
    simp only at hL
    set acc := ts.foldl (Acc.stepI bx) Acc.init with hacc
    set U := cornerMaxF B (momOf acc.ws) c with hU
    set sLo := acc.aLo - U with hsLo
    set K' := (if 0 ≤ sLo then acc.kHi else acc.kLo) with hK'
    set x' := sLo * Sz / K' with hx'
    split_ifs at hL with guards
    have hLe : acc.kLo * expLower x' / Sz = L := Option.some.inj hL
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guards
    obtain ⟨⟨⟨⟨⟨bg, cg⟩, inc⟩, accOk⟩, kpos⟩, kle⟩ := guards
    simp only [boxGuard, Bool.and_eq_true, decide_eq_true_eq] at bg
    obtain ⟨⟨hd, ⟨l0, h0, l1, h1⟩⟩, ⟨xlo, xhi⟩⟩ := bg
    have fk1 : acc.kLo = (ts.map (Term.kLoI bx)).sum := by
      rw [hacc, (foldl_stepI bx ts Acc.init).1]; simp [Acc.init]
    have fk2 : acc.kHi = (ts.map (Term.kHiI bx)).sum := by
      rw [hacc, (foldl_stepI bx ts Acc.init).2.1]; simp [Acc.init]
    have fa : acc.aLo = (ts.map (Term.aLoI bx)).sum := by
      rw [hacc, (foldl_stepI bx ts Acc.init).2.2.1]; simp [Acc.init]
    have fok : acc.ok = ts.all Term.ok := by
      rw [hacc, (foldl_stepI bx ts Acc.init).2.2.2.1]; simp [Acc.init]
    have fws : acc.ws = (ts.map (Term.wtermI bx)).reverse := by
      rw [hacc, (foldl_stepI bx ts Acc.init).2.2.2.2]; simp [Acc.init]
    have allOk : ∀ t ∈ ts, t.ok = true := List.all_eq_true.mp (by rw [← fok]; exact accOk)
    have hv := gp.1
    have facts := fun t (ht : t ∈ ts) => per_termI bx hd t (allOk t ht) hp hv
    set l := ts.map fun t => (tCI bx t, tXI p t) with hl
    have lC : (l.map Prod.fst).sum = (ts.map (tCI bx)).sum := by rw [hl, List.map_map]; rfl
    have lX : (l.map fun z => z.1 * z.2).sum = (ts.map fun t => tCI bx t * tXI p t).sum := by
      rw [hl, List.map_map]; rfl
    have lE : (l.map fun z => z.1 * Real.exp z.2).sum = (ts.map fun t => tCI bx t * Real.exp (tXI p t)).sum := by
      rw [hl, List.map_map]; rfl
    have Klo : (acc.kLo : ℝ) / Sz ≤ (ts.map (tCI bx)).sum := by
      rw [fk1, sum_cast_int, lsum_div]
      exact sum_le_map (fun t ht => (facts t ht).2.2.2.2.2.1)
    have Khi : (ts.map (tCI bx)).sum ≤ (acc.kHi : ℝ) / Sz := by
      rw [fk2, sum_cast_int, lsum_div]
      exact sum_le_map (fun t ht => (facts t ht).2.2.2.2.2.2.1)
    have KloPos : (0:ℝ) < (acc.kLo : ℝ) / Sz := div_pos (by exact_mod_cast kpos) sp
    have Cpos : 0 < (ts.map (tCI bx)).sum := KloPos.trans_le Klo
    have c0 : ∀ z ∈ l, 0 ≤ z.1 := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      exact mul_nonneg (facts t ht).1 (facts t ht).2.1.le
    have jensen := jensen_list l c0 (by rw [lC]; exact Cpos)
    rw [lC, lX, lE] at jensen
    have Xeq : (ts.map fun t => tCI bx t * tXI p t).sum =
        (ts.map fun t => tMuI bx t * tW t * tT t).sum -
          Real.pi * (ts.map fun t => tMuI bx t * tW t * tSig t * tR p t).sum := by
      rw [lsum_mul, ← lsum_sub]
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [(facts t ht).2.2.2.2.2.2.2.2.2.2]
      ring
    have Alow : (acc.aLo : ℝ) / Sz ≤ (ts.map fun t => tMuI bx t * tW t * tT t).sum := by
      rw [fa, sum_cast_int, lsum_div]
      exact sum_le_map (fun t ht => (facts t ht).2.2.2.2.2.2.2.1)
    have nn : ∀ w ∈ acc.ws, 0 ≤ w.w := by
      intro w hw
      rw [fws] at hw
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hw)
      exact (facts t ht).2.2.2.2.2.2.2.2.2.1
    have hc : ∀ cc, c = some cc → 0 ≤ cc.lam := by
      intro cc e
      subst e
      simpa [cutGuard] using cg
    have pos : ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0 := by
      intro bits
      constructor
      · unfold IBox.at IBox.lo IBox.hi; split_ifs <;> simp <;> omega
      · unfold IBox.at IBox.lo IBox.hi; split_ifs <;> simp <;> omega
    have corner := cornerMax_sound hB hd acc.ws nn c hc pos p hp
    rw [← cornerMaxF_eq] at corner
    have p2 : (p 2) ^ 2 ≤ 1 / 4 := by
      have lo2 := (hp 2).1
      have hi2 := (hp 2).2
      have a : (((-1/2 : ℚ)) : ℝ) ≤ ((bx.lo 2 : ℚ) : ℝ) := Rat.cast_le.mpr xlo
      have b : ((bx.hi 2 : ℚ) : ℝ) ≤ (((1/2 : ℚ)) : ℝ) := Rat.cast_le.mpr xhi
      push_cast at a b
      nlinarith
    have cutNN := cutR_nonneg c cg p gp.2.1 p2
    have wsSum : (acc.ws.map fun w => (w.w : ℝ) * w.mode.radial (squarePoint p)).sum =
        (ts.map fun t => ((t.wtermI bx).w : ℝ) * tR p t).sum := by
      rw [fws, List.map_reverse, List.sum_reverse, List.map_map]
      rfl
    rw [wsSum] at corner
    have wsBound : Real.pi * (ts.map fun t => tMuI bx t * tW t * tSig t * tR p t).sum ≤ (U : ℝ) / Sz := by
      rw [lsum_mul]
      have step : (ts.map fun t => Real.pi * (tMuI bx t * tW t * tSig t * tR p t)).sum ≤
          (ts.map fun t => ((t.wtermI bx).w : ℝ) * tR p t).sum / Sz := by
        rw [lsum_div]
        apply sum_le_map
        intro t ht
        have f := facts t ht
        have r0 := f.2.2.2.1.le
        calc Real.pi * (tMuI bx t * tW t * tSig t * tR p t) = (Real.pi * tMuI bx t * tW t * tSig t) * tR p t := by ring
          _ ≤ (((t.wtermI bx).w : ℝ) / Sz) * tR p t := mul_le_mul_of_nonneg_right f.2.2.2.2.2.2.2.2.1 r0
          _ = ((t.wtermI bx).w : ℝ) * tR p t / Sz := by ring
      refine step.trans ?_
      apply div_le_div_of_nonneg_right _ sp.le
      linarith
    have Xlow : (sLo : ℝ) / Sz ≤ (ts.map fun t => tCI bx t * tXI p t).sum := by
      rw [Xeq, hsLo]
      push_cast
      rw [sub_div]
      linarith
    have kexp := kexp_lower Klo Khi KloPos Xlow
    have Kq : (0:ℤ) < K' := by
      rw [hK']; split_ifs
      · exact kpos.trans_le kle
      · exact kpos
    have ifEq : (if 0 ≤ (sLo : ℝ) / Sz then (acc.kHi : ℝ) / Sz else (acc.kLo : ℝ) / Sz) = (K' : ℝ) / Sz := by
      rw [hK']
      by_cases h : 0 ≤ sLo
      · have : 0 ≤ (sLo : ℝ) / Sz := div_nonneg (by exact_mod_cast h) sp.le
        simp [h, this]
      · have : ¬ 0 ≤ (sLo : ℝ) / Sz := by
          intro h'
          have := (div_nonneg_iff.mp h')
          rcases this with ⟨a, _⟩ | ⟨_, b⟩
          · exact h (by exact_mod_cast a)
          · linarith
        simp [h, this]
    rw [ifEq] at kexp
    have xle : (x' : ℝ) / Sz ≤ ((sLo : ℝ) / Sz) / ((K' : ℝ) / Sz) := by
      have f := fdiv_le (sLo * Sz) K' Kq
      have KR : (0:ℝ) < K' := by exact_mod_cast Kq
      rw [div_le_iff₀ sp]
      calc ((sLo * Sz / K' : ℤ) : ℝ) ≤ ((sLo * Sz : ℤ) : ℝ) / K' := f
        _ = ((sLo : ℝ) / Sz) / ((K' : ℝ) / Sz) * Sz := by push_cast; field_simp
    have expMono := Real.exp_le_exp.mpr xle
    have Elow := expLower_le x'
    have Lle : (L : ℝ) / Sz ≤ ((acc.kLo : ℝ) / Sz) * Real.exp (((sLo : ℝ) / Sz) / ((K' : ℝ) / Sz)) := by
      rw [← hLe]
      have f := fdiv_le (acc.kLo * expLower x') Sz spZ
      have kl0 : (0:ℝ) ≤ (acc.kLo : ℝ) / Sz := KloPos.le
      calc ((acc.kLo * expLower x' / Sz : ℤ) : ℝ) / Sz ≤ ((acc.kLo * expLower x' : ℤ) : ℝ) / Sz / Sz :=
            div_le_div_of_nonneg_right f sp.le
        _ = ((acc.kLo : ℝ) / Sz) * ((expLower x' : ℝ) / Sz) := by push_cast; ring
        _ ≤ ((acc.kLo : ℝ) / Sz) * Real.exp ((x' : ℝ) / Sz) := mul_le_mul_of_nonneg_left Elow kl0
        _ ≤ _ := mul_le_mul_of_nonneg_left expMono kl0
    exact ⟨hd, inc, allOk, ⟨B, rfl, pos⟩, Lle.trans (kexp.trans jensen)⟩

/-! ### Soundness: the screened series -/

/-- The indices of the terms of one family. -/
def famIdx (f : Stage2.Family) (ts : List Term) : List IntVec :=
  (ts.filter fun t => decide (t.fam = f)).map fun t => t.mode.index

theorem screened_split (ts : List Term) (q : TwoSite) :
    (ts.map fun t => t.screened q).sum =
      11 / 10 * ((famIdx .cross ts).map (ScreenedSeries.crossTerm (11 / 10) q)).sum +
      11 / 5 * ((famIdx .period ts).map (ScreenedSeries.periodTerm (11 / 10) q)).sum +
      200 / 121 * ((famIdx .reciprocal ts).map (ScreenedSeries.waveTerm (11 / 10) q)).sum := by
  induction ts with
  | nil => simp [famIdx]
  | cons t rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, famIdx, List.filter_cons]
    unfold Term.screened
    cases hf : t.fam <;> simp <;> ring

theorem famIdx_nodup (f : Stage2.Family) {ts : List Term} (h : (ts.map Term.mode).Nodup) :
    (famIdx f ts).Nodup := by
  unfold famIdx
  have sub : ((ts.filter fun t => decide (t.fam = f)).map Term.mode).Nodup :=
    h.sublist ((List.filter_sublist).map Term.mode)
  have e : ((ts.filter fun t => decide (t.fam = f)).map fun t => t.mode.index) =
      ((ts.filter fun t => decide (t.fam = f)).map Term.mode).map Mode.index := by
    rw [List.map_map]; rfl
  rw [e]
  apply sub.map_on
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
  have fu : u.fam = f := by simpa using (List.mem_filter.mp hu).2
  have fv : v.fam = f := by simpa using (List.mem_filter.mp hv).2
  show (⟨u.fam, ![u.a, u.b, u.c]⟩ : Mode) = ⟨v.fam, ![v.a, v.b, v.c]⟩
  have hi : (![u.a, u.b, u.c] : IntVec) = ![v.a, v.b, v.c] := hxy
  rw [fu, fv, hi]

theorem famIdx_lex (f : Stage2.Family) (hf : f ≠ .cross) {ts : List Term} (allOk : ∀ t ∈ ts, t.ok = true) :
    ∀ n ∈ famIdx f ts, lexPositive n := by
  intro n hn
  unfold famIdx at hn
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
  have mem := List.mem_filter.mp ht
  have tf : t.fam = f := by simpa using mem.2
  have valid : t.mode.valid := term_valid (by
    have := allOk t mem.1
    simp only [Term.ok, Bool.and_eq_true] at this
    exact this.1.1.1)
  exact valid.2.resolve_left (by simp [Term.mode, tf, hf])

/-- The retained screened terms of an increasing list are at most `h₂ − 89/605`. -/
theorem screened_le (ts : List Term) (inc : increasing ts = true) (allOk : ∀ t ∈ ts, t.ok = true)
    (q : TwoSite) (hv : q.Valid) : (ts.map fun t => t.screened q).sum ≤ h₂ q - 89 / 605 := by
  have nodup := modes_nodup inc
  have h := ScreenedSeries.finite_lower_lex q hv (11 / 10) (by norm_num) (famIdx .cross ts).toFinset
    (famIdx .period ts).toFinset (famIdx .reciprocal ts).toFinset
    (fun n hn => famIdx_lex .period (by simp) allOk n (List.mem_toFinset.mp hn))
    (fun n hn => famIdx_lex .reciprocal (by simp) allOk n (List.mem_toFinset.mp hn))
  rw [List.sum_toFinset _ (famIdx_nodup .cross nodup), List.sum_toFinset _ (famIdx_nodup .period nodup),
    List.sum_toFinset _ (famIdx_nodup .reciprocal nodup)] at h
  rw [screened_split]
  norm_num at h ⊢
  linarith

/-- **Soundness of the screened support check.** -/
theorem screenCheck_sound (bx : Cell) (ts : List Term) (c : Option Cut) (ok : screenCheck bx ts c = true)
    (p : Chart) (hp : bx.Mem p) (gp : good p) : energy fcc < energy (chartPoint p) := by
  have sp := Sz_pos
  unfold screenCheck at ok
  cases hL : screenValue bx ts c with
  | none => rw [hL] at ok; simp at ok
  | some L =>
    rw [hL] at ok
    have strict : fccHZ < L + screenConstS := of_decide_eq_true ok
    obtain ⟨hd, inc, allOk, -, bound⟩ := screenValue_sound bx ts c L hL p hp gp
    have termSum : (ts.map fun t => tCI bx t * Real.exp (tXI p t)).sum ≤
        (ts.map fun t => t.screened (chartPoint p)).sum :=
      sum_le_map (fun t ht => (per_termI bx hd t (allOk t ht) hp gp.1).2.2.2.2.1)
    have phys := screened_le ts inc allOk _ gp.1
    have cst : (screenConstS : ℝ) / Sz ≤ 89 / 605 := by
      have f := fdiv_le (89 * Sz) 605 (by norm_num)
      unfold screenConstS
      rw [div_le_iff₀ sp]
      calc ((89 * Sz / 605 : ℤ) : ℝ) ≤ ((89 * Sz : ℤ) : ℝ) / ((605 : ℤ) : ℝ) := f
        _ = 89 / 605 * Sz := by push_cast; ring
    apply aboveFCC_of_Z strict p
    push_cast
    rw [add_div]
    linarith

/-! ### The screened phase-triad gain

As in `BccSharp.Cover.AdaptiveGain`, with the screened reciprocal term `(2/s²) φ G₁(π R*/s²)`: its floor
part `μ G₁` enters the support, the rest `resI = (200/121)(φ − ℓ) G₁(π (100/121) R*)` is left,
and the capacities are lower bounds of `(200/121) G₁(π (100/121) R*)` on the box. The
allocations, triads and gain formula are those of `BccSharp.Cover.AdaptiveGain`. -/

/-- The screened reciprocal kernel `G₁(π R*/s²)` of a term at a point. -/
def kI (p : Chart) (t : Term) : ℝ :=
  gKernel 1 (Real.pi * (100 / 121) * quad (gram (chartPoint p).basis)⁻¹ (castVec t.mode.index))

/-- At scale `S`, a lower bound of `(200/121) G₁(π (100/121) R*)` on the box. -/
def capSI (B : IBox) (t : Term) : ℤ :=
  let X := cdivZ (dualMax B t * (piHiN : ℤ) * 100) (Sz * 121)
  if 0 < X then 200 * (expNegPt X.toNat).lo * Sz / (121 * X) else 0

theorem capSI_sound {bx : Cell} {B : IBox} (hB : toIBox bx = some B) (hd : diagonalsCheck bx = true)
    (pos : ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0) (t : Term) (hf : t.fam = .reciprocal)
    (valid : t.mode.valid) {p : Chart} (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    (capSI B t : ℝ) / Sz ≤ 200 / 121 * kI p t := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  have lex : lexPositive t.mode.index := valid.2.resolve_left (by simp [Term.mode, hf])
  have qpos := reciprocalPositive hv (lex_ne lex)
  set q := quad (gram (chartPoint p).basis)⁻¹ (castVec t.mode.index) with hq
  have xpos : 0 < Real.pi * (100 / 121) * q := by have := Real.pi_pos; positivity
  have kEq : kI p t = Real.exp (-(Real.pi * (100 / 121) * q)) / (Real.pi * (100 / 121) * q) := by
    unfold kI
    rw [← hq, gKernel_one xpos]
  have kpos : 0 < kI p t := by rw [kEq]; exact div_pos (Real.exp_pos _) xpos
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
  set X := cdivZ (dualMax B t * (piHiN : ℤ) * 100) (Sz * 121) with hX
  have ph := pi_bounds.2
  rw [S_eq] at ph
  have piN : (0:ℝ) ≤ (piHiN : ℝ) := by positivity
  have Xge : Real.pi * (100 / 121) * q ≤ (X : ℝ) / Sz := by
    have c1 := le_cdiv (dualMax B t * (piHiN : ℤ) * 100) (Sz * 121) (by positivity)
    rw [← hX] at c1
    have qle : q ≤ (dualMax B t : ℝ) / Sz := by rw [le_div_iff₀ sp]; linarith
    calc Real.pi * (100 / 121) * q ≤ ((piHiN : ℝ) / Sz) * (100 / 121) * ((dualMax B t : ℝ) / Sz) := by
          apply mul_le_mul _ qle qpos.le (by positivity)
          exact mul_le_mul_of_nonneg_right ph (by norm_num)
      _ = (((dualMax B t * (piHiN : ℤ) * 100 : ℤ) : ℝ) / ((Sz * 121 : ℤ) : ℝ)) / Sz := by
          push_cast; field_simp
      _ ≤ (X : ℝ) / Sz := div_le_div_of_nonneg_right c1 sp.le
  unfold capSI
  simp only [← hX]
  split_ifs with hXp
  · have XR : (0:ℝ) < X := by exact_mod_cast hXp
    have Xn : ((X.toNat : ℕ) : ℝ) = (X : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hXp.le
    have m := (expNegPt_mem X.toNat).1
    rw [Xn] at m
    have d121 : (0:ℤ) < 121 * X := by positivity
    have f := fdiv_le (200 * (expNegPt X.toNat).lo * Sz) (121 * X) d121
    have x2 : 0 < (X : ℝ) / Sz := div_pos XR sp
    calc ((200 * (expNegPt X.toNat).lo * Sz / (121 * X) : ℤ) : ℝ) / Sz
        ≤ ((200 * (expNegPt X.toNat).lo * Sz : ℤ) : ℝ) / ((121 * X : ℤ) : ℝ) / Sz :=
          div_le_div_of_nonneg_right f sp.le
      _ = 200 / 121 * ((((expNegPt X.toNat).lo : ℝ) / Sz) / ((X : ℝ) / Sz)) := by
          push_cast; field_simp
      _ ≤ 200 / 121 * (Real.exp (-((X : ℝ) / Sz)) / ((X : ℝ) / Sz)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact div_le_div_of_nonneg_right m x2.le
      _ ≤ 200 / 121 * (Real.exp (-(Real.pi * (100 / 121) * q)) / ((X : ℝ) / Sz)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg Xge)) x2.le
      _ ≤ 200 / 121 * (Real.exp (-(Real.pi * (100 / 121) * q)) / (Real.pi * (100 / 121) * q)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact div_le_div_of_nonneg_left (by positivity) xpos Xge
      _ = 200 / 121 * kI p t := by rw [kEq]
  · simp only [Int.cast_zero, zero_div]
    positivity

/-- The part of a screened reciprocal term left unused by the screened support. -/
def residI (bx : Cell) (p : Chart) (t : Term) : ℝ :=
  if t.fam = .reciprocal then
    200 / 121 * (phaseFactor (chartPoint p) t.mode.index - (phaseLoS bx t : ℝ) / Sz) * kI p t
  else 0

/-- The tangent minorant of a screened term against its kernel. -/
theorem per_term_kernelI (bx : Cell) (hd : diagonalsCheck bx = true) (t : Term) (hok : t.ok = true)
    {p : Chart} (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    tCI bx t * Real.exp (tXI p t) ≤ tMuI bx t * kernelValue (famKind t.fam) (Real.pi * tSig t * tR p t) := by
  have sp := Sz_pos
  obtain ⟨Tpos, Gm, Wm, G0, W0⟩ := term_kernels t hok
  have valid : t.mode.valid := term_valid (by
    simp only [Term.ok, Bool.and_eq_true] at hok; exact hok.1.1.1)
  obtain ⟨mu0, muC, muP, muR⟩ := muI_sound bx t hp
  obtain ⟨argPos, -⟩ := screened_term_lower bx hd t valid p hp hv (tMuI bx t) mu0 ⟨muC, muP, muR⟩
  have Glo : (t.G.lo : ℝ) / Sz ≤ tG t := Gm.1
  have Wlo : (t.W.lo : ℝ) / Sz ≤ tW t := Wm.1
  have Gpos : 0 < tG t := lt_of_lt_of_le (div_pos (by exact_mod_cast G0) sp) Glo
  have Wpos : 0 < tW t := lt_of_lt_of_le (div_pos (by exact_mod_cast W0) sp) Wlo
  have lt := logTangent (famKind t.fam) Tpos argPos
  have rate : (Real.exp (-(tT t)) + ((famKind t.fam).power : ℝ) * kernelValue (famKind t.fam) (tT t)) /
      (tT t * kernelValue (famKind t.fam) (tT t)) = tW t / tG t := by
    unfold tW tG
    field_simp
  have lt' : tG t * Real.exp (tXI p t) ≤ kernelValue (famKind t.fam) (Real.pi * tSig t * tR p t) := by
    unfold tXI
    rw [← rate]
    exact lt
  calc tCI bx t * Real.exp (tXI p t) = tMuI bx t * (tG t * Real.exp (tXI p t)) := by unfold tCI; ring
    _ ≤ tMuI bx t * kernelValue (famKind t.fam) (Real.pi * tSig t * tR p t) := mul_le_mul_of_nonneg_left lt' mu0

/-- A screened term is at least its tangent minorant plus its unused residual. -/
theorem term_splitI (bx : Cell) (hd : diagonalsCheck bx = true) (t : Term) (hok : t.ok = true) {p : Chart}
    (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    tCI bx t * Real.exp (tXI p t) + residI bx p t ≤ t.screened (chartPoint p) := by
  by_cases hf : t.fam = .reciprocal
  · have sp := Sz_pos
    have valid : t.mode.valid := term_valid (by
      simp only [Term.ok, Bool.and_eq_true] at hok; exact hok.1.1.1)
    have lex : lexPositive t.mode.index := valid.2.resolve_left (by simp [Term.mode, hf])
    have kt := per_term_kernelI bx hd t hok hp hv
    obtain ⟨h0, h1⟩ := radialLoPos bx hd
    have d0 := h0.trans_le (hp 0).1
    have d1 := h1.trans_le (hp 1).1
    have radial : tR p t = quad (gram (chartPoint p).basis)⁻¹ (castVec t.mode.index) := by
      unfold tR
      rw [term_mode_recip t hf]
      simp only [Mode.radial]
      exact dualRadial_eq _ p d0.ne' d1.ne'
    have sig : tSig t = 100 / 121 := by unfold tSig Term.sigN Term.sigD; rw [hf]; norm_num
    have kern : kernelValue (famKind t.fam) (Real.pi * tSig t * tR p t) = kI p t := by
      rw [hf, radial, sig]
      simp only [famKind]
      exact kernel_one_eq _
    have k0 : 0 ≤ kI p t := ScreenedSeries.gKernel_nonneg 1 _
    have mu : tMuI bx t ≤ 200 / 121 * ((phaseLoS bx t : ℝ) / Sz) := by
      have f := fdiv_le (200 * phaseLoS bx t) 121 (by norm_num)
      unfold tMuI Term.muI
      rw [hf, div_le_iff₀ sp]
      calc ((200 * phaseLoS bx t / 121 : ℤ) : ℝ) ≤ ((200 * phaseLoS bx t : ℤ) : ℝ) / ((121 : ℤ) : ℝ) := f
        _ = 200 / 121 * ((phaseLoS bx t : ℝ) / Sz) * Sz := by push_cast; field_simp
    have term : t.screened (chartPoint p) = 200 / 121 * (phaseFactor (chartPoint p) t.mode.index * kI p t) := by
      unfold Term.screened ScreenedSeries.waveTerm kI
      rw [hf, ite_eq_right (lex_ne lex)]
      have e : Real.pi * quad (gram (chartPoint p).basis)⁻¹ (castVec t.mode.index) / (11 / 10) ^ 2 =
          Real.pi * (100 / 121) * quad (gram (chartPoint p).basis)⁻¹ (castVec t.mode.index) := by ring
      rw [e]
      rfl
    rw [kern] at kt
    rw [term]
    unfold residI
    rw [ite_eq_left hf]
    have := mul_le_mul_of_nonneg_right mu k0
    nlinarith
  · have f := (per_termI bx hd t hok hp hv).2.2.2.2.1
    unfold residI
    rw [ite_eq_right hf, add_zero]
    exact f

def capAtI (B : IBox) (ts : List Term) (u : ℕ) : ℤ :=
  match ts[u]? with
  | some t => capSI B t
  | none => 0

def capsOkI (B : IBox) (ts : List Term) (rs : List Alloc) : Bool :=
  rs.all fun r => decide ((spentAt rs r.i : ℤ) ≤ capAtI B ts r.i) &&
    decide ((spentAt rs r.j : ℤ) ≤ capAtI B ts r.j) && decide ((spentAt rs r.k : ℤ) ≤ capAtI B ts r.k)

/-- The screened gain at scale `S`, if every allocation is valid and every capacity holds. -/
def gainValueI (bx : Cell) (ts : List Term) (rs : List Alloc) : Option ℤ :=
  match toIBox bx with
  | none => none
  | some B =>
    if rs.all (Alloc.valid ts) && capsOkI B ts rs then
      some ((rs.map (Alloc.gainNum bx ts)).sum / Sz)
    else none

/-- **The screened support check with the phase-triad gain.** -/
def screenGainCheck (bx : Cell) (ts : List Term) (c : Option Cut) (rs : List Alloc) : Bool :=
  match screenValue bx ts c, gainValueI bx ts rs with
  | some L, some g => decide (fccHZ < L + g + screenConstS)
  | _, _ => false

/-- **The screened gain bound.** -/
theorem gainValueI_sound (bx : Cell) (ts : List Term) (rs : List Alloc) (g : ℤ)
    (hg : gainValueI bx ts rs = some g)
    (hd : diagonalsCheck bx = true) (allOk : ∀ t ∈ ts, t.ok = true)
    (pos : ∀ B, toIBox bx = some B → ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0)
    (p : Chart) (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    (g : ℝ) / Sz ≤ (ts.map (residI bx p)).sum := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  unfold gainValueI at hg
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
    let gap : Term → ℝ := fun t => phaseFactor (chartPoint p) t.mode.index - (phaseLoS bx t : ℝ) / Sz
    let G : ℕ → ℝ := fun u => termAt ts u gap
    have gapNN : ∀ t, 0 ≤ gap t := by
      intro t
      have := (phaseLoS_sound bx t hp).2
      simp only [gap]
      linarith
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
    have s1 : (g : ℝ) / Sz ≤ (((rs.map (Alloc.gainNum bx ts)).sum : ℤ) : ℝ) / Sz / Sz := by
      rw [← gEq]
      exact div_le_div_of_nonneg_right (fdiv_le _ Sz spZ) sp.le
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
    have s3 : (rs.map fun r => (r.amount : ℝ) * (G r.i + G r.j + G r.k)).sum =
        ∑ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u :=
      (sum_spent rs ts.length G inRange).symm
    have s4 : ∀ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u / Sz ≤ termAt ts u (residI bx p) := by
      intro u _
      cases ht : ts[u]? with
      | none => simp [G, termAt, ht]
      | some t =>
        have tmem : t ∈ ts := List.mem_of_getElem? ht
        have Gu : G u = gap t := by simp only [G, termAt, ht]
        have Ru : termAt ts u (residI bx p) = residI bx p t := by simp only [termAt, ht]
        rw [Gu, Ru]
        by_cases zero : spentAt rs u = 0
        · rw [zero]
          simp only [Nat.cast_zero, zero_mul, zero_div]
          unfold residI
          split_ifs with hf
          · have k0 : 0 ≤ kI p t := ScreenedSeries.gKernel_nonneg 1 _
            have := gapNN t
            simp only [gap] at this
            positivity
          · exact le_refl 0
        · obtain ⟨r, hr, cnt⟩ : ∃ r ∈ rs, r.count u ≠ 0 := by
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
          have capU : ((spentAt rs u : ℕ) : ℤ) ≤ capSI B t ∧ t.fam = .reciprocal := by
            rcases which with e | e | e
            · rw [← e] at ht ⊢
              have : capAtI B ts r.i = capSI B t := by simp [capAtI, ht]
              rw [hx] at ht; cases ht
              exact ⟨this ▸ cr.1.1, rx⟩
            · rw [← e] at ht ⊢
              have : capAtI B ts r.j = capSI B t := by simp [capAtI, ht]
              rw [hy] at ht; cases ht
              exact ⟨this ▸ cr.1.2, ry⟩
            · rw [← e] at ht ⊢
              have : capAtI B ts r.k = capSI B t := by simp [capAtI, ht]
              rw [hz] at ht; cases ht
              exact ⟨this ▸ cr.2, rz⟩
          obtain ⟨capLe, hf⟩ := capU
          have valid : t.mode.valid := term_valid (by
            have := allOk t tmem
            simp only [Term.ok, Bool.and_eq_true] at this
            exact this.1.1.1)
          have cs := capSI_sound hB hd posB t hf valid hp hv
          have capR : (spentAt rs u : ℝ) / Sz ≤ (capSI B t : ℝ) / Sz := by
            apply div_le_div_of_nonneg_right _ sp.le
            exact_mod_cast capLe
          unfold residI
          rw [ite_eq_left hf]
          have g0 := gapNN t
          calc (spentAt rs u : ℝ) * gap t / Sz = ((spentAt rs u : ℝ) / Sz) * gap t := by ring
            _ ≤ (200 / 121 * kI p t) * gap t := mul_le_mul_of_nonneg_right (capR.trans cs) g0
            _ = _ := by simp only [gap]; ring
    have s5 : (∑ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u) / Sz ≤ (ts.map (residI bx p)).sum := by
      rw [Finset.sum_div, ← sum_range_termAt]
      exact Finset.sum_le_sum s4
    calc (g : ℝ) / Sz ≤ _ := s1
      _ ≤ _ := s2
      _ = (∑ u ∈ Finset.range ts.length, (spentAt rs u : ℝ) * G u) / Sz := by rw [s3]
      _ ≤ _ := s5

/-- **Soundness of the screened support check with the gain.** -/
theorem screenGainCheck_sound (bx : Cell) (ts : List Term) (c : Option Cut) (rs : List Alloc)
    (ok : screenGainCheck bx ts c rs = true) (p : Chart) (hp : bx.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) := by
  have sp := Sz_pos
  unfold screenGainCheck at ok
  cases hL : screenValue bx ts c with
  | none => rw [hL] at ok; simp at ok
  | some L =>
    cases hg : gainValueI bx ts rs with
    | none => rw [hL, hg] at ok; simp at ok
    | some g =>
      rw [hL, hg] at ok
      have strict : fccHZ < L + g + screenConstS := of_decide_eq_true ok
      obtain ⟨hd, inc, allOk, ⟨B, hB, pos⟩, bound⟩ := screenValue_sound bx ts c L hL p hp gp
      have gain := gainValueI_sound bx ts rs g hg hd allOk
        (fun B' hB' => by rw [hB] at hB'; cases hB'; exact pos) p hp gp.1
      have split : (ts.map fun t => tCI bx t * Real.exp (tXI p t)).sum + (ts.map (residI bx p)).sum ≤
          (ts.map fun t => t.screened (chartPoint p)).sum := by
        rw [← lsum_add]
        exact sum_le_map (fun t ht => term_splitI bx hd t (allOk t ht) hp gp.1)
      have phys := screened_le ts inc allOk _ gp.1
      have cst : (screenConstS : ℝ) / Sz ≤ 89 / 605 := by
        have f := fdiv_le (89 * Sz) 605 (by norm_num)
        unfold screenConstS
        rw [div_le_iff₀ sp]
        calc ((89 * Sz / 605 : ℤ) : ℝ) ≤ ((89 * Sz : ℤ) : ℝ) / ((605 : ℤ) : ℝ) := f
          _ = 89 / 605 * Sz := by push_cast; ring
      apply aboveFCC_of_Z strict p
      push_cast
      rw [add_div, add_div]
      linarith

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
