import BccSharp.Cover.DirectFixSound

set_option autoImplicit false

/-! Fixed-point versions of the two Direct sidecar checks.

`DirectRoute.exactRealCheck` and `DirectRoute.momentCheck` evaluate every kernel
at its archived distance upper through `directLower` and `reciprocalLower`
(rational square-root bisection, rational `erfc` series), and the reciprocal
terms through rational cosine balls; the thinnest exact-real row took 251 s of
kernel time and 18 GB. These checks keep the archived operands, the exact
corner tests (`exactUpperCheck`, `maximumCheck`) and the moment argument, and
evaluate the scalars with the Direct fixed-point kernels:

* `exactRealFix`: each archived distance upper `u` that passes
  `exactUpperCheck` contributes `halfLowF` at `π u` from above; a term whose
  operand is missing or fails contributes `0`, a sound lower bound because
  every term of the series is nonnegative. The reciprocal terms are the
  direct evaluator's `recipF`.
* `momentFix`: each term is the endpoint tangent
  `min(kernelLower, G) + min(slopeLower⁺, slope) u` with `G` and the slope
  magnitude `π G(1, πu) + G(1/2, πu)/(2u)` from the fixed-point kernels; the
  archived joint moment is subtracted after `maximumCheck`. A failed or
  missing operand contributes `0`.

Both prove `energy fcc < energy (chartPoint p)` on the box
(`exactRealFix_sound`, `momentFix_sound`), the conclusions of
`exactRealCheck_sound` and `momentCheck_sound`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.DirectSidecarFix
open BccSharp BccSharp.Coverage DirectRoute OverlayPlanar.Fix DirectFix BravaisCover

/-! ### Definitions -/

/-- `⌈u S⌉`. -/
def ceilS (u : ℚ) : ℤ := cdivZ (u.num * Sz) (u.den : ℤ)

def exactTermF (b : Cell) (w : ExactRealProposal) (s : Bool) (n : IntVec) : ℤ :=
  match readDistance w s n with
  | none => 0
  | some r => if exactUpperCheck b s n r.upper then halfLowF (piTimes (ceilS r.upper)) else 0

def exactValueF (b : Cell) (w : ExactRealProposal) : ℤ :=
  sumZ (exactTermF b w true) (directIndices 1) + 2 * sumZ (exactTermF b w false) (pairedIndices 1) +
    2 * sumZ (recipF b) (pairedIndices 1)

def exactRealFix (b : Cell) (w : ExactRealProposal) : Bool :=
  (sameCell w.ownerBox b && operandRoster w) &&
    ((diagonalsCheck b && guardsF b) && decide (thrZ < exactValueF b w))

/-- A lower bound of the slope magnitude `π G(1, πu) + G(1/2, πu)/(2u)` from the
fixed-point values `aF ≤ S G(1/2, πu)` and `cF ≤ S G(1, πu)`. -/
def slopeF (u : ℚ) (aF cF : ℤ) : ℚ :=
  max 0 ((twoPiLo : ℚ) / (2 * S) * (((max 0 cF : ℤ) : ℚ) / S) + ((max 0 aF : ℤ) : ℚ) / S / (2 * u))

def momentTermF (b : Cell) (w : ExactRealProposal) (s : Bool) (n : IntVec) : ℚ :=
  match readDistance w s n with
  | none => 0
  | some row =>
    if exactUpperCheck b s n row.upper then
      min row.kernelLower ((halfLowF (piTimes (ceilS row.upper)) : ℚ) / S) +
        min (max 0 row.slopeLower)
          (slopeF row.upper (halfLowF (piTimes (ceilS row.upper))) (oneLowF (piTimes (ceilS row.upper)))) *
          row.upper
    else 0

def sumQ (f : IntVec → ℚ) : List IntVec → ℚ
  | [] => 0
  | n :: ns => f n + sumQ f ns

def momentValueF (b : Cell) (w : MomentProposal) : ℚ :=
  sumQ (momentTermF b w.exactReal true) (directIndices 1) +
    2 * sumQ (momentTermF b w.exactReal false) (pairedIndices 1) +
    2 * ((sumZ (recipF b) (pairedIndices 1) : ℚ) / S) - w.maximum

def momentFix (b : Cell) (w : MomentProposal) : Bool :=
  (sameCell w.exactReal.ownerBox b && operandRoster w.exactReal) &&
    ((diagonalsCheck b && guardsF b) && (maximumCheck b w && decide ((thrZ : ℚ) / S < momentValueF b w)))

/-! ### Scalars -/

theorem ceilS_ge (u : ℚ) : (u : ℝ) ≤ (ceilS u : ℝ) / Sz := by
  have sp := Sz_pos
  have c := le_cdiv (u.num * Sz) (u.den : ℤ) (by exact_mod_cast u.pos)
  rw [le_div_iff₀ sp]
  refine le_trans (le_of_eq ?_) c
  rw [Rat.cast_def]
  push_cast
  ring

theorem half_nonneg' {x : ℝ} (h : 0 < x) : 0 ≤ gKernel (1/2) x := half_nonneg h

theorem exactTermF_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b = true)
    (w : ExactRealProposal) (s : Bool) (n : IntVec) (pos : 0 < quad (gram (chartBasis p)) (chartVector p s n)) :
    (exactTermF b w s n : ℝ) / Sz ≤ gKernel (1/2) (Real.pi * quad (gram (chartBasis p)) (chartVector p s n)) := by
  have G0 := half_nonneg (mul_pos Real.pi_pos pos)
  unfold exactTermF
  cases readDistance w s n with
  | none => simpa using G0
  | some r =>
    dsimp only
    by_cases tested : exactUpperCheck b s n r.upper = true
    · rw [ite_eq_left tested]
      have upper := exactUpperCheck_sound b s n r.upper tested hd p hp
      have T := piTimes_sound pos.le (upper.trans (ceilS_ge r.upper))
      exact halfLowF_sound _ (mul_pos Real.pi_pos pos) T
    · rw [ite_eq_right tested]; simpa using G0

/-- The finite sum of the direct evaluator with any cross and period evaluators. -/
theorem valueWith_sound {b : Cell} {p : Chart} (hp : b.Mem p) (g : guardsF b = true)
    (hq : (chartPoint p).Valid) (cross period : IntVec → ℤ)
    (hc : ∀ n, (cross n : ℝ) / Sz ≤ seriesCrossTerm (chartPoint p) n)
    (hs : ∀ n, lexPositive n → (period n : ℝ) / Sz ≤ seriesDirectTerm (chartPoint p) n) :
    ((sumZ cross (directIndices 1) + 2 * sumZ period (pairedIndices 1) +
      2 * sumZ (recipF b) (pairedIndices 1) : ℤ) : ℝ) / Sz ≤ h₂ (chartPoint p) := by
  let q := chartPoint p
  let half := (pairedIndices 1).toFinset
  have nd := radius_nodup_one
  have pos (n : IntVec) (hn : n ∈ pairedIndices 1) : lexPositive n :=
    of_decide_eq_true (List.mem_filter.mp hn).2
  have pos' (n : IntVec) (hn : n ∈ half) : lexPositive n := pos n (List.mem_toFinset.mp hn)
  have hC := sumZ_sound cross (seriesCrossTerm q) _ nd.1 (fun n _ => hc n)
  have hS := sumZ_sound period (seriesDirectTerm q) _ nd.2 (fun n hn => hs n (pos n hn))
  have hR := sumZ_sound (recipF b) (pairedTerm q) _ nd.2 (fun n hn => recipF_sound hp g hq n (pos n hn))
  have pS : 2 * ((sumZ period (pairedIndices 1) : ℝ) / Sz) ≤ ∑ n ∈ bothSigns half, seriesDirectTerm q n := by
    rw [← sum_pairs half pos' _ (even_direct q), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS (by norm_num)
  have rS : 2 * ((sumZ (recipF b) (pairedIndices 1) : ℝ) / Sz) ≤ ∑ n ∈ bothSigns half, pairedTerm q n := by
    rw [← sum_pairs half pos' _ (even_pair q), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hR (by norm_num)
  have hFull := finite_lower q hq (bothSigns half) (directIndices 1).toFinset (bothSigns half)
  push_cast
  rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
  linarith

theorem exactRealFix_sound (b : Cell) (w : ExactRealProposal) (p : Chart) (hp : b.Mem p)
    (valid : (chartPoint p).Valid) (ok : exactRealFix b w = true) : energy fcc < energy (chartPoint p) := by
  obtain ⟨_, work⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨guards, cmp⟩ := Bool.and_eq_true_iff.mp work
  obtain ⟨hd, g⟩ := Bool.and_eq_true_iff.mp guards
  have bound := valueWith_sound hp g valid (exactTermF b w true) (exactTermF b w false)
    (fun n => exactTermF_sound hp hd w true n (cross_distance_positive valid n))
    (fun n hn => by
      rw [seriesDirectTerm, ite_eq_right (lex_ne hn)]
      exact exactTermF_sound hp hd w false n (period_distance_positive valid n hn))
  have lt : (thrZ : ℝ) / Sz < (exactValueF b w : ℝ) / Sz :=
    div_lt_div_of_pos_right (by exact_mod_cast of_decide_eq_true cmp) Sz_pos
  have thr := thr_sound
  change energy fcc < (h₂ (chartPoint p) - 4) / (2 * ac)
  apply (lt_div_iff₀ (mul_pos two_pos ac_positive : (0:ℝ) < 2 * ac)).2
  have b2 : (exactValueF b w : ℝ) / Sz ≤ h₂ (chartPoint p) := bound
  linarith

/-! ### The moment route -/

theorem slopeF_le {u : ℚ} (hu : (0 : ℝ) < u) (aF cF : ℤ)
    (ha : (aF : ℝ) / Sz ≤ gKernel (1/2) (Real.pi * u)) (hc : (cF : ℝ) / Sz ≤ gKernel 1 (Real.pi * u)) :
    (slopeF u aF cF : ℝ) ≤ -Real.pi * kernelSlope .half (Real.pi * u) := by
  have sp := Sz_pos
  have t := mul_pos Real.pi_pos hu
  have G0 := half_nonneg t
  have G1 : 0 ≤ gKernel 1 (Real.pi * u) := by rw [gKernel_one t]; positivity
  have equality : Real.pi * gKernel 1 (Real.pi * u) + gKernel (1/2) (Real.pi * u) / (2 * (u : ℝ)) =
      -Real.pi * kernelSlope .half (Real.pi * u) := by
    have hv : kernelValue .half (Real.pi * u) = gKernel (1/2) (Real.pi * u) := by
      norm_num [kernelValue, KernelKind.power]
    unfold kernelSlope
    rw [hv, gKernel_one t]
    norm_num [KernelKind.power]
    field_simp
    ring
  have cMax : max 0 (cF : ℝ) / Sz ≤ gKernel 1 (Real.pi * u) := by
    rcases le_total (cF : ℝ) 0 with h | h
    · rw [max_eq_left h]; simpa using G1
    · rw [max_eq_right h]; exact hc
  have aMax : max 0 (aF : ℝ) / Sz ≤ gKernel (1/2) (Real.pi * u) := by
    rcases le_total (aF : ℝ) 0 with h | h
    · rw [max_eq_left h]; simpa using G0
    · rw [max_eq_right h]; exact ha
  have piLo : (twoPiLo : ℝ) / (2 * Sz) ≤ Real.pi := by
    have := twoPi_bounds.1
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ sp] at this
    linarith
  have cnn : (0 : ℝ) ≤ max 0 (cF : ℝ) / Sz := div_nonneg (le_max_left _ _) sp.le
  have prod := mul_le_mul piLo cMax cnn Real.pi_pos.le
  have div := div_le_div_of_nonneg_right aMax (by positivity : (0 : ℝ) ≤ 2 * (u : ℝ))
  unfold slopeF
  push_cast
  simp only [S_eq]
  apply max_le
  · rw [← equality]; positivity
  · rw [← equality]
    linarith

theorem momentTermF_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b = true)
    (w : ExactRealProposal) (s : Bool) (n : IntVec) (pos : 0 < quad (gram (chartBasis p)) (chartVector p s n)) :
    (momentTermF b w s n : ℝ) ≤ gKernel (1/2) (Real.pi * quad (gram (chartBasis p)) (chartVector p s n)) +
      (momentWeight w s n : ℝ) * quad (gram (chartBasis p)) (chartVector p s n) := by
  set q := quad (gram (chartBasis p)) (chartVector p s n) with hq
  have G0 := half_nonneg (mul_pos Real.pi_pos pos)
  have wnn : (0 : ℝ) ≤ (momentWeight w s n : ℝ) := by
    unfold momentWeight; split
    · simp
    · exact_mod_cast le_max_left _ _
  have base : (0 : ℝ) ≤ gKernel (1/2) (Real.pi * q) + (momentWeight w s n : ℝ) * q :=
    add_nonneg G0 (mul_nonneg wnn pos.le)
  unfold momentTermF
  cases hr : readDistance w s n with
  | none => simpa using base
  | some row =>
    dsimp only
    by_cases tested : exactUpperCheck b s n row.upper = true
    · rw [ite_eq_left tested]
      have upper := exactUpperCheck_sound b s n row.upper tested hd p hp
      have upos : (0 : ℝ) < row.upper := pos.trans_le upper
      set T := piTimes (ceilS row.upper)
      have hT := piTimes_sound upos.le (ceilS_ge row.upper)
      have aLo := halfLowF_sound T (mul_pos Real.pi_pos upos) hT
      have cLo := oneLowF_sound T (mul_pos Real.pi_pos upos) hT
      have sLo := slopeF_le upos (halfLowF T) (oneLowF T) aLo cLo
      set weight := min (max 0 row.slopeLower) (slopeF row.upper (halfLowF T) (oneLowF T))
      rw [← hq] at upper
      have k : min (row.kernelLower : ℝ) ((halfLowF T : ℝ) / (S : ℝ)) ≤ gKernel (1/2) (Real.pi * row.upper) := by
        rw [S_eq]; exact (min_le_right _ _).trans aLo
      have wS : (weight : ℝ) ≤ -Real.pi * kernelSlope .half (Real.pi * row.upper) :=
        (Rat.cast_le.mpr (min_le_right _ _)).trans sLo
      have wW : (weight : ℝ) ≤ (momentWeight w s n : ℝ) := by
        unfold momentWeight; rw [hr]
        exact_mod_cast min_le_left _ _
      have tangent := Stage2.globalTangent .half (mul_pos Real.pi_pos upos) (mul_pos Real.pi_pos pos)
      have hv (x : ℝ) : kernelValue .half x = gKernel (1/2) x := by norm_num [kernelValue, KernelKind.power]
      rw [hv, hv] at tangent
      have along := mul_le_mul_of_nonneg_right wS (sub_nonneg.mpr upper)
      have atPoint := mul_le_mul_of_nonneg_right wW pos.le
      push_cast
      have e : -Real.pi * kernelSlope .half (Real.pi * row.upper) * ((row.upper : ℝ) - q) =
          kernelSlope .half (Real.pi * row.upper) * (Real.pi * q - Real.pi * row.upper) := by ring
      have dist : (weight : ℝ) * row.upper = (weight : ℝ) * ((row.upper : ℝ) - q) + (weight : ℝ) * q := by ring
      linarith [k, along, atPoint, tangent, e, dist]
    · rw [ite_eq_right tested]; simpa using base

theorem sumQ_sound (f : IntVec → ℚ) (v : IntVec → ℝ) (l : List IntVec) (nd : l.Nodup)
    (h : ∀ n ∈ l, (f n : ℝ) ≤ v n) : (sumQ f l : ℝ) ≤ ∑ n ∈ l.toFinset, v n := by
  induction l with
  | nil => simp [sumQ]
  | cons a ns ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp nd
    rw [sumQ, List.toFinset_cons, Finset.sum_insert (by simpa using fresh)]
    push_cast
    exact add_le_add (h a (by simp)) (ih rest (fun n hn => h n (List.mem_cons_of_mem _ hn)))

theorem momentFix_sound (b : Cell) (w : MomentProposal) (p : Chart) (hp : b.Mem p)
    (valid : (chartPoint p).Valid) (ok : momentFix b w = true) : energy fcc < energy (chartPoint p) := by
  obtain ⟨_, work⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨guards, rest⟩ := Bool.and_eq_true_iff.mp work
  obtain ⟨hd, g⟩ := Bool.and_eq_true_iff.mp guards
  obtain ⟨top, cmp⟩ := Bool.and_eq_true_iff.mp rest
  let half := (pairedIndices 1).toFinset
  have nd := radius_nodup_one
  have pos (n : IntVec) (hn : n ∈ pairedIndices 1) : lexPositive n :=
    of_decide_eq_true (List.mem_filter.mp hn).2
  have pos' (n : IntVec) (hn : n ∈ half) : lexPositive n := pos n (List.mem_toFinset.mp hn)
  let extra (s : Bool) (n : IntVec) := (momentWeight w.exactReal s n : ℝ) * squaredRadial s n (squarePoint p)
  have hC := sumQ_sound (momentTermF b w.exactReal true) (fun n => seriesCrossTerm (chartPoint p) n + extra true n)
    _ nd.1 (fun n _ => by
      have h := momentTermF_sound hp hd w.exactReal true n (cross_distance_positive valid n)
      have e1 := squaredRadial_eq p true n
      show _ ≤ seriesCrossTerm (chartPoint p) n +
        (momentWeight w.exactReal true n : ℝ) * squaredRadial true n (squarePoint p)
      rw [e1]
      exact h)
  have hS := sumQ_sound (momentTermF b w.exactReal false) (fun n => seriesDirectTerm (chartPoint p) n + extra false n)
    _ nd.2 (fun n hn => by
      have hn' := pos n hn
      have h := momentTermF_sound hp hd w.exactReal false n (period_distance_positive valid n hn')
      have e1 := squaredRadial_eq p false n
      show _ ≤ seriesDirectTerm (chartPoint p) n +
        (momentWeight w.exactReal false n : ℝ) * squaredRadial false n (squarePoint p)
      rw [e1, seriesDirectTerm, ite_eq_right (lex_ne hn')]
      exact h)
  have hR := sumZ_sound (recipF b) (pairedTerm (chartPoint p)) _ nd.2 (fun n hn => recipF_sound hp g valid n (pos n hn))
  rw [Finset.sum_add_distrib] at hC hS
  have pS : 2 * (sumQ (momentTermF b w.exactReal false) (pairedIndices 1) : ℝ) ≤
      (∑ n ∈ bothSigns half, seriesDirectTerm (chartPoint p) n) + 2 * (∑ n ∈ half, extra false n) := by
    rw [← sum_pairs half pos' _ (even_direct (chartPoint p)), ← Finset.mul_sum]
    linarith only [hS]
  have rS : 2 * ((sumZ (recipF b) (pairedIndices 1) : ℝ) / Sz) ≤ ∑ n ∈ bothSigns half, pairedTerm (chartPoint p) n := by
    rw [← sum_pairs half pos' _ (even_pair (chartPoint p)), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hR (by norm_num)
  have hFull := finite_lower (chartPoint p) valid (bothSigns half) (directIndices 1).toFinset (bothSigns half)
  have maximum := maximumCheck_sound b w p hp hd top
  have moment : momentReal w.exactReal (squarePoint p) =
      (∑ n ∈ (directIndices 1).toFinset, extra true n) + 2 * (∑ n ∈ half, extra false n) := rfl
  have strict : (thrZ : ℚ) / S < momentValueF b w := of_decide_eq_true cmp
  have strictR : (thrZ : ℝ) / Sz < (momentValueF b w : ℝ) := by
    have h : (((thrZ : ℚ) / S : ℚ) : ℝ) < (momentValueF b w : ℝ) := by exact_mod_cast strict
    push_cast at h
    rwa [S_eq] at h
  have value : (momentValueF b w : ℝ) = (sumQ (momentTermF b w.exactReal true) (directIndices 1) : ℝ) +
      2 * (sumQ (momentTermF b w.exactReal false) (pairedIndices 1) : ℝ) +
      2 * ((sumZ (recipF b) (pairedIndices 1) : ℝ) / Sz) - (w.maximum : ℝ) := by
    unfold momentValueF; push_cast; rw [S_eq]
  have thr := thr_sound
  change energy fcc < (h₂ (chartPoint p) - 4) / (2 * ac)
  apply (lt_div_iff₀ (mul_pos two_pos ac_positive : (0:ℝ) < 2 * ac)).2
  linarith

end BccSharp.Coulomb.CompactCover.DirectSidecarFix
