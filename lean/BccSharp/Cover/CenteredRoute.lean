import BccSharp.Cover.CenteredAnchor
import BccSharp.Cover.LayeredRoute

set_option autoImplicit false

/-! # The centered PlanarAnchor requests as a late checker

A centered PlanarAnchor request (`.centered method wrap hint slack`) asks for
`0 < deficit (chartPoint p)` at every `good` point of its box. Its anchor is the
all-half anchor `anchorOf (chartPoint p) halfAll` of the relative route, with
wrap `n` from the request. A certificate (`CenteredCert`) is accepted
(`centeredCertOk`) when

* the layered gain passes `Fix.splitOk` on the seam cell with a *negative*
  `k`, `0 ≤ 200 g⁻ + k`, and the literal registration, guards, coset
  separation and cost bound of `planarAnchorCertOk` pass; then
  `deficit(anchor) + k |R d|² ≤ deficit` (`centered_gain`, the argument of
  `planarAnchorCertOk_sound` with the sign of `k` changed);
* the anchor basis passes `anchorBasisOk`: `det N = 1` and `N M₀ = M₀ Γ` with
  `Γ` integral and invertible over `ℤ`, where `M₀` is the BCC cubic cell. Then
  `strainBasis .bcc (chartBasis p · N)` is a primitive basis of the anchor's
  points and `deficit(anchor) = oneSiteDeficit (strainBasis .bcc (chartBasis p · N))`
  (`anchor_deficit_eq`);
* the anchor tree passes `anchorTreeOk`: a binary subdivision of the box whose
  every leaf encloses the whitened strain point `framePoint .bcc (chartBasis p · N)`
  in a rectangle (`wRect`, fixed point at scale `2⁹⁶`) on which the E2 strain
  leaf check with margin `m`, `StrainTangent.zLeafCheckQ`, passes with the
  atlas aggregate `D.agg`. Then `m / 2⁶⁴ / (2 scaleHi) ≤ deficit(anchor)`
  (`anchorTreeOk_sound`);
* `0 < m / 2⁶⁴ / (2 scaleHi) + k · |R d|²⁺`.

`centeredCheck_sound` proves `CheckerSound (centeredCheck D table)` for every
valid atlas `D`; it does not use `LatticeCase`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-! ### The strain point of the anchor basis on a cell -/

theorem strainEntry_eq (N : Fin 3 → Fin 3 → ℚ) (p : Chart) (i j : Fin 3) :
    JLeaf.strainEntry N p i j = (chartBasis p * JLeaf.ofQ N) i j := by
  fin_cases i <;>
    simp [JLeaf.strainEntry, chartBasis, JLeaf.ofQ, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv] <;>
    ring

/-- `(Aᵀ A)ᵢⱼ` for `A = chartBasis p · N` on the cell (squares on the diagonal). -/
def gramEntryF (b : Cell) (N : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) : FI :=
  if i = j then
    ((FI.sq (strainEntryF b N 0 i)).add (FI.sq (strainEntryF b N 1 i))).add (FI.sq (strainEntryF b N 2 i))
  else
    ((FI.mul (strainEntryF b N 0 i) (strainEntryF b N 0 j)).add
      (FI.mul (strainEntryF b N 1 i) (strainEntryF b N 1 j))).add
      (FI.mul (strainEntryF b N 2 i) (strainEntryF b N 2 j))

theorem gramEntryF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) (N : Fin 3 → Fin 3 → ℚ)
    (i j : Fin 3) : (gramEntryF b N i j).Mem (gram (chartBasis p * JLeaf.ofQ N) i j) := by
  have e (k l : Fin 3) := strainEntryF_mem hp g N k l
  have hg : gram (chartBasis p * JLeaf.ofQ N) i j =
      JLeaf.strainEntry N p 0 i * JLeaf.strainEntry N p 0 j + JLeaf.strainEntry N p 1 i * JLeaf.strainEntry N p 1 j +
        JLeaf.strainEntry N p 2 i * JLeaf.strainEntry N p 2 j := by
    simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, strainEntry_eq, Fin.sum_univ_three]
  rw [hg]
  unfold gramEntryF
  split_ifs with h
  · subst h
    have := FI.add_mem (FI.add_mem (FI.sq_mem (e 0 i)) (FI.sq_mem (e 1 i))) (FI.sq_mem (e 2 i))
    convert this using 1
    ring
  · exact FI.add_mem (FI.add_mem (FI.mul_mem (e 0 i) (e 0 j)) (FI.mul_mem (e 1 i) (e 1 j)))
      (FI.mul_mem (e 2 i) (e 2 j))

/-- The trace of `Aᵀ A` on the cell. -/
def traceF (b : Cell) (N : Fin 3 → Fin 3 → ℚ) : FI :=
  ((gramEntryF b N 0 0).add (gramEntryF b N 1 1)).add (gramEntryF b N 2 2)

theorem traceF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) (N : Fin 3 → Fin 3 → ℚ) :
    (traceF b N).Mem (BravaisCover.diagonalSum (gram (chartBasis p * JLeaf.ofQ N))) :=
  FI.add_mem (FI.add_mem (gramEntryF_mem hp g N 0 0) (gramEntryF_mem hp g N 1 1)) (gramEntryF_mem hp g N 2 2)

/-- An interval at scale `2⁹⁶` around `√y`, from squares. -/
theorem fi_sqrt_mem (y : ℚ) (lo hi : ℤ) (h0 : 0 ≤ lo) (hlo : (lo : ℚ) ^ 2 ≤ y * (Sz : ℚ) ^ 2)
    (hhi : y * (Sz : ℚ) ^ 2 ≤ (hi : ℚ) ^ 2) (h1 : 0 ≤ hi) : FI.Mem ⟨lo, hi⟩ (Real.sqrt (y : ℝ)) := by
  have hS := Sz_pos
  have hS2 : (0 : ℝ) < (Sz : ℝ) ^ 2 := by positivity
  have hloR : ((lo : ℝ) / Sz) ^ 2 ≤ (y : ℝ) := by
    rw [div_pow, div_le_iff₀ hS2]
    exact_mod_cast hlo
  have hhiR : (y : ℝ) ≤ ((hi : ℝ) / Sz) ^ 2 := by
    rw [div_pow, le_div_iff₀ hS2]
    exact_mod_cast hhi
  have l0 : (0 : ℝ) ≤ (lo : ℝ) / Sz := div_nonneg (by exact_mod_cast h0) hS.le
  have u0 : (0 : ℝ) ≤ (hi : ℝ) / Sz := div_nonneg (by exact_mod_cast h1) hS.le
  constructor
  · show (lo : ℝ) / Sz ≤ Real.sqrt y
    calc (lo : ℝ) / Sz = Real.sqrt (((lo : ℝ) / Sz) ^ 2) := (Real.sqrt_sq l0).symm
      _ ≤ Real.sqrt y := Real.sqrt_le_sqrt hloR
  · show Real.sqrt y ≤ (hi : ℝ) / Sz
    calc Real.sqrt y ≤ Real.sqrt (((hi : ℝ) / Sz) ^ 2) := Real.sqrt_le_sqrt hhiR
      _ = (hi : ℝ) / Sz := Real.sqrt_sq u0

/-- `1 / (√2 σ_E)` for BCC at scale `2⁹⁶`. -/
def cWE2 : FI := ⟨9707896751440276555184236444, 9707896751440276555184236445⟩
/-- `1 / (√6 σ_E)` for BCC at scale `2⁹⁶`. -/
def cWE6 : FI := ⟨5604856802709137149837756590, 5604856802709137149837756591⟩
/-- `√2 / σ_T` for BCC at scale `2⁹⁶`. -/
def cWT : FI := ⟨59834353602014085783925505366, 59834353602014085783925505367⟩

theorem sqrt_inv_eq (k c : ℝ) (hk : 0 < k) (hc : 0 < c) :
    Real.sqrt (1 / (k * c ^ 2)) = 1 / (Real.sqrt k * c) := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have e : 1 / (k * c ^ 2) = (1 / (Real.sqrt k * c)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hk.le, one_pow]
  rw [e, Real.sqrt_sq (by positivity)]

theorem cWE2_mem : cWE2.Mem (1 / (Real.sqrt 2 * (BravaisCover.whitenE .bcc : ℝ))) := by
  have hw : (0 : ℝ) < (BravaisCover.whitenE .bcc : ℝ) := by norm_num [BravaisCover.whitenE]
  rw [← sqrt_inv_eq 2 _ (by norm_num) hw]
  have h := fi_sqrt_mem (1 / (2 * BravaisCover.whitenE .bcc ^ 2)) 9707896751440276555184236444
    9707896751440276555184236445 (by norm_num) (by norm_num [BravaisCover.whitenE, Sz])
    (by norm_num [BravaisCover.whitenE, Sz]) (by norm_num)
  push_cast at h
  exact h

theorem cWE6_mem : cWE6.Mem (1 / (Real.sqrt 6 * (BravaisCover.whitenE .bcc : ℝ))) := by
  have hw : (0 : ℝ) < (BravaisCover.whitenE .bcc : ℝ) := by norm_num [BravaisCover.whitenE]
  rw [← sqrt_inv_eq 6 _ (by norm_num) hw]
  have h := fi_sqrt_mem (1 / (6 * BravaisCover.whitenE .bcc ^ 2)) 5604856802709137149837756590
    5604856802709137149837756591 (by norm_num) (by norm_num [BravaisCover.whitenE, Sz])
    (by norm_num [BravaisCover.whitenE, Sz]) (by norm_num)
  push_cast at h
  exact h

theorem cWT_mem : cWT.Mem (Real.sqrt 2 / (BravaisCover.whitenT .bcc : ℝ)) := by
  have hw : (0 : ℝ) < (BravaisCover.whitenT .bcc : ℝ) := by norm_num [BravaisCover.whitenT]
  have e : Real.sqrt 2 / (BravaisCover.whitenT .bcc : ℝ) =
      Real.sqrt ((2 / BravaisCover.whitenT .bcc ^ 2 : ℚ) : ℝ) := by
    push_cast
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hw.le]
  rw [e]
  exact fi_sqrt_mem _ 59834353602014085783925505366 59834353602014085783925505367 (by norm_num)
    (by norm_num [BravaisCover.whitenT, Sz]) (by norm_num [BravaisCover.whitenT, Sz]) (by norm_num)

/-- A rectangle of whitened strain coordinates holding `framePoint .bcc (chartBasis p · N)` for
every point `p` of the cell (`wRect_mem`). -/
def wRect (b : Cell) (N : Fin 3 → Fin 3 → ℚ) : BravaisCover.Rectangle :=
  let s := FI.smul 3 (FI.invPos (traceF b N))
  let g00 := gramEntryF b N 0 0
  let g11 := gramEntryF b N 1 1
  let g22 := gramEntryF b N 2 2
  let w0 := FI.mul (FI.mul s (g00.sub g11)) cWE2
  let w1 := FI.mul (FI.mul s ((g00.add g11).sub (FI.smul 2 g22))) cWE6
  let w2 := FI.mul (FI.mul s (gramEntryF b N 0 1)) cWT
  let w3 := FI.mul (FI.mul s (gramEntryF b N 0 2)) cWT
  let w4 := FI.mul (FI.mul s (gramEntryF b N 1 2)) cWT
  ⟨![(w0.lo : ℚ) / Sz, (w1.lo : ℚ) / Sz, (w2.lo : ℚ) / Sz, (w3.lo : ℚ) / Sz, (w4.lo : ℚ) / Sz],
    ![(w0.hi : ℚ) / Sz, (w1.hi : ℚ) / Sz, (w2.hi : ℚ) / Sz, (w3.hi : ℚ) / Sz, (w4.hi : ℚ) / Sz]⟩

theorem fi_mem_cast {a : FI} {x : ℝ} (h : a.Mem x) :
    (((a.lo : ℚ) / Sz : ℚ) : ℝ) ≤ x ∧ x ≤ (((a.hi : ℚ) / Sz : ℚ) : ℝ) := by
  push_cast
  exact h

theorem wRect_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) (N : Fin 3 → Fin 3 → ℚ)
    (ht : 0 < (traceF b N).lo) :
    (wRect b N).Mem (BravaisCover.framePoint .bcc (chartBasis p * JLeaf.ofQ N)) := by
  set C := gram (chartBasis p * JLeaf.ofQ N) with hCdef
  have hC (i j : Fin 3) := gramEntryF_mem hp g N i j
  rw [← hCdef] at hC
  have htr := traceF_mem hp g N
  rw [← hCdef] at htr
  set d := BravaisCover.diagonalSum C with hd
  have hs : (FI.smul 3 (FI.invPos (traceF b N))).Mem (((3 : ℤ) : ℝ) * d⁻¹) :=
    FI.smul_mem 3 (FI.invPos_mem ht htr)
  have hS (i j : Fin 3) : BravaisCover.normalizedStrain C i j = 3 / d * C i j - if i = j then 1 else 0 := by
    simp [BravaisCover.normalizedStrain, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hd]
  set w := BravaisCover.framePoint .bcc (chartBasis p * JLeaf.ofQ N) with hw
  have hw' (i : Fin 5) : w i = BravaisCover.strainCoordinates .bcc (BravaisCover.normalizedStrain C) i := by
    rw [hw, hCdef]
    rfl
  have b0 : (((wRect b N).lo 0 : ℚ) : ℝ) ≤ w 0 ∧ w 0 ≤ (((wRect b N).hi 0 : ℚ) : ℝ) := by
    have h := FI.mul_mem (FI.mul_mem hs (FI.sub_mem (hC 0 0) (hC 1 1))) cWE2_mem
    have e : w 0 = ((3 : ℤ) : ℝ) * d⁻¹ * (C 0 0 - C 1 1) *
        (1 / (Real.sqrt 2 * (BravaisCover.whitenE .bcc : ℝ))) := by
      rw [hw']
      simp only [BravaisCover.strainCoordinates, hS]
      simp
      ring
    rw [e]
    exact fi_mem_cast h
  have b1 : (((wRect b N).lo 1 : ℚ) : ℝ) ≤ w 1 ∧ w 1 ≤ (((wRect b N).hi 1 : ℚ) : ℝ) := by
    have h := FI.mul_mem (FI.mul_mem hs (FI.sub_mem (FI.add_mem (hC 0 0) (hC 1 1)) (FI.smul_mem 2 (hC 2 2))))
      cWE6_mem
    have e : w 1 = ((3 : ℤ) : ℝ) * d⁻¹ * (C 0 0 + C 1 1 - ((2 : ℤ) : ℝ) * C 2 2) *
        (1 / (Real.sqrt 6 * (BravaisCover.whitenE .bcc : ℝ))) := by
      rw [hw']
      simp only [BravaisCover.strainCoordinates, hS]
      simp
      ring
    rw [e]
    exact fi_mem_cast h
  have b2 : (((wRect b N).lo 2 : ℚ) : ℝ) ≤ w 2 ∧ w 2 ≤ (((wRect b N).hi 2 : ℚ) : ℝ) := by
    have h := FI.mul_mem (FI.mul_mem hs (hC 0 1)) cWT_mem
    have e : w 2 = ((3 : ℤ) : ℝ) * d⁻¹ * C 0 1 * (Real.sqrt 2 / (BravaisCover.whitenT .bcc : ℝ)) := by
      rw [hw']
      simp only [BravaisCover.strainCoordinates, hS]
      simp
      ring
    rw [e]
    exact fi_mem_cast h
  have b3 : (((wRect b N).lo 3 : ℚ) : ℝ) ≤ w 3 ∧ w 3 ≤ (((wRect b N).hi 3 : ℚ) : ℝ) := by
    have h := FI.mul_mem (FI.mul_mem hs (hC 0 2)) cWT_mem
    have e : w 3 = ((3 : ℤ) : ℝ) * d⁻¹ * C 0 2 * (Real.sqrt 2 / (BravaisCover.whitenT .bcc : ℝ)) := by
      rw [hw']
      simp only [BravaisCover.strainCoordinates, hS]
      simp
      ring
    rw [e]
    exact fi_mem_cast h
  have b4 : (((wRect b N).lo 4 : ℚ) : ℝ) ≤ w 4 ∧ w 4 ≤ (((wRect b N).hi 4 : ℚ) : ℝ) := by
    have h := FI.mul_mem (FI.mul_mem hs (hC 1 2)) cWT_mem
    have e : w 4 = ((3 : ℤ) : ℝ) * d⁻¹ * C 1 2 * (Real.sqrt 2 / (BravaisCover.whitenT .bcc : ℝ)) := by
      rw [hw']
      simp only [BravaisCover.strainCoordinates, hS]
      simp
      ring
    rw [e]
    exact fi_mem_cast h
  intro i
  fin_cases i
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4

/-! ### The anchor tree -/

/-- A binary subdivision of a cell at coordinate midpoints. -/
inductive AnchorTree where
  | leaf
  | split (axis : Axis) (lower upper : AnchorTree)

/-- One anchor leaf: guards, a positive trace, and the E2 strain leaf check with margin `m` on
the enclosing strain rectangle. -/
def anchorLeafOk (D : BravaisCover.StrainAtlas.AtlasData) (N : Fin 3 → Fin 3 → ℚ) (m : ℤ) (b : Cell) :
    Bool :=
  (guardsOk b && decide (0 < (traceF b N).lo)) &&
    BravaisCover.StrainTangent.zLeafCheckQ
      (D.agg .bcc (BravaisCover.StrainTangent.zBox .bcc (wRect b N))) (wRect b N) m

def anchorTreeOk (D : BravaisCover.StrainAtlas.AtlasData) (N : Fin 3 → Fin 3 → ℚ) (m : ℤ) :
    AnchorTree → Cell → Bool
  | .leaf, b => anchorLeafOk D N m b
  | .split i lower upper, b =>
    anchorTreeOk D N m lower ((Cut.dyadic i).child b false) &&
      anchorTreeOk D N m upper ((Cut.dyadic i).child b true)

theorem anchorTreeOk_sound (D : BravaisCover.StrainAtlas.AtlasData) (hD : D.Valid)
    (N : Fin 3 → Fin 3 → ℚ) (hN : JLeaf.det3Q N = 1) (m : ℤ) :
    ∀ (t : AnchorTree) (b : Cell), anchorTreeOk D N m t b = true → ∀ p : Chart, b.Mem p →
      (m : ℝ) / 2 ^ 64 / (2 * (BravaisCover.scaleHi : ℝ)) ≤
        oneSiteDeficit (BravaisCover.strainBasis .bcc (chartBasis p * JLeaf.ofQ N)) := by
  intro t
  induction t with
  | leaf =>
    intro b ok p hp
    simp only [anchorTreeOk, anchorLeafOk, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨hg, ht⟩, hz⟩ := ok
    have g : Guards b := by
      have := of_decide_eq_true hg
      exact ⟨this.1, this.2.1, this.2.2⟩
    have sp := Sz_pos
    have hr : 0 < p 0 := (div_pos (by exact_mod_cast g.r₀) sp).trans_le (cx_mem hp 0).1
    have hs : 0 < p 1 := (div_pos (by exact_mod_cast g.r₁) sp).trans_le (cx_mem hp 1).1
    have hA : (chartBasis p * JLeaf.ofQ N).det = 1 := by
      rw [Matrix.det_mul, chartBasis_det_one p hr hs, JLeaf.ofQ_det N hN, one_mul]
    have hGram := BravaisCover.framePoint_reconstruct .bcc (chartBasis p * JLeaf.ofQ N) (by rw [hA, abs_one])
    exact BravaisCover.StrainTangent.zLeafCheckQ_sound _ (D.agg_certified hD .bcc _) _ m hz _
      (wRect_mem hp g N ht) _ hA hGram.symm
  | split i lower upper ihl ihu =>
    intro b ok p hp
    simp only [anchorTreeOk, Bool.and_eq_true] at ok
    rcases two_closed_children b i (midpoint b i) p hp with h | h
    · exact ihl _ ok.1 p (by simpa only [Cut.child, Cut.position] using h)
    · exact ihu _ ok.2 p (by simpa only [Cut.child, Cut.position] using h)

/-! ### The anchor as a one-site lattice -/

/-- The BCC cubic cell at unit scale. -/
def M0Q : Fin 3 → Fin 3 → ℚ := ![![1, 0, 1 / 2], ![0, 1, 1 / 2], ![0, 0, 1 / 2]]

theorem M0Q_real : (!![1, 0, 1 / 2; 0, 1, 1 / 2; 0, 0, 1 / 2] : Mat) = JLeaf.ofQ M0Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [JLeaf.ofQ, M0Q]

theorem strainBasis_bcc (A : Mat) : BravaisCover.strainBasis .bcc A = A * JLeaf.ofQ M0Q := by
  have hf : Constants.fccLength ≠ 0 := by unfold Constants.fccLength; positivity
  unfold BravaisCover.strainBasis BravaisCover.cubicBasis
  rw [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hf, one_smul, M0Q_real]

theorem M0Q_det : (JLeaf.ofQ M0Q).det = 1 / 2 := by
  rw [Matrix.det_fin_three]
  norm_num [JLeaf.ofQ, M0Q]

theorem M0Q_mulVec (v : Vec) :
    (JLeaf.ofQ M0Q).mulVec v = ![v 0 + v 2 / 2, v 1 + v 2 / 2, v 2 / 2] := by
  funext i
  fin_cases i <;> simp [JLeaf.ofQ, M0Q, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- `chartBasis p · M₀` is a basis of the all-half anchor's points. -/
theorem lattice_mul_M0 (R : Mat) :
    lattice (R * JLeaf.ofQ M0Q) = lattice R ∪ translate (R.mulVec halfAll) (lattice R) := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    show (R * JLeaf.ofQ M0Q).mulVec (castVec n) ∈ _
    rw [← Matrix.mulVec_mulVec, M0Q_mulVec]
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (n 2)
    · left
      refine ⟨![n 0 + k, n 1 + k, k], ?_⟩
      show R.mulVec (castVec ![n 0 + k, n 1 + k, k]) = _
      congr 1
      funext i
      fin_cases i <;> simp [castVec, hk]
    · right
      refine ⟨R.mulVec (castVec ![n 0 + k + 1, n 1 + k + 1, k + 1]), ⟨_, rfl⟩, ?_⟩
      rw [← Matrix.mulVec_add]
      congr 1
      funext i
      fin_cases i <;> simp [castVec, hk, halfAll] <;> ring
  · rintro (⟨m, rfl⟩ | ⟨y, ⟨m, rfl⟩, rfl⟩)
    · refine ⟨![m 0 - m 2, m 1 - m 2, 2 * m 2], ?_⟩
      show (R * JLeaf.ofQ M0Q).mulVec _ = _
      rw [← Matrix.mulVec_mulVec, M0Q_mulVec]
      congr 1
      funext i
      fin_cases i <;> simp [castVec]
    · refine ⟨![m 0 - m 2, m 1 - m 2, 2 * m 2 - 1], ?_⟩
      show (R * JLeaf.ofQ M0Q).mulVec _ = _
      rw [← Matrix.mulVec_mulVec, M0Q_mulVec, ← Matrix.mulVec_add]
      congr 1
      funext i
      fin_cases i <;> simp [castVec, halfAll] <;> ring

/-- `det N = 1`, `N M₀ = M₀ Γ` and `Γ Γ' = 1` over `ℤ`. -/
def anchorBasisOk (N : Fin 3 → Fin 3 → ℚ) (Γ Γ' : Matrix (Fin 3) (Fin 3) ℤ) : Bool :=
  decide (JLeaf.det3Q N = 1 ∧
    (∀ i j : Fin 3, ∑ k, N i k * M0Q k j = ∑ k, M0Q i k * (Γ k j : ℚ)) ∧
    (∀ i j : Fin 3, ∑ k, Γ i k * Γ' k j = if i = j then 1 else 0))

theorem anchorBasisOk_sound {N : Fin 3 → Fin 3 → ℚ} {Γ Γ' : Matrix (Fin 3) (Fin 3) ℤ}
    (ok : anchorBasisOk N Γ Γ' = true) :
    JLeaf.det3Q N = 1 ∧ JLeaf.ofQ N * JLeaf.ofQ M0Q = JLeaf.ofQ M0Q * BravaisCover.toRealMatrix Γ ∧
      Γ * Γ' = 1 := by
  obtain ⟨hdet, hNM, hΓ⟩ := of_decide_eq_true ok
  refine ⟨hdet, ?_, ?_⟩
  · ext i j
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hNM i j)
    simp only [Matrix.mul_apply, JLeaf.ofQ, BravaisCover.toRealMatrix, Matrix.of_apply, Matrix.map_apply,
      Int.coe_castRingHom]
    push_cast at h
    exact h
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hΓ i j

/-- The deficit of the all-half anchor is the one-site deficit of `strainBasis .bcc (chartBasis p · N)`. -/
theorem anchor_deficit_eq (p : Chart) (hv : (chartPoint p).Valid) (N : Fin 3 → Fin 3 → ℚ)
    (Γ Γ' : Matrix (Fin 3) (Fin 3) ℤ) (hN : JLeaf.det3Q N = 1)
    (hNM : JLeaf.ofQ N * JLeaf.ofQ M0Q = JLeaf.ofQ M0Q * BravaisCover.toRealMatrix Γ) (hΓ : Γ * Γ' = 1) :
    deficit (anchorOf (chartPoint p) halfAll) =
      oneSiteDeficit (BravaisCover.strainBasis .bcc (chartBasis p * JLeaf.ofQ N)) := by
  set q := anchorOf (chartPoint p) halfAll with hqdef
  have hq : q.Valid := anchor_valid _ hv halfAll halfAll_half
  set P := BravaisCover.strainBasis .bcc (chartBasis p * JLeaf.ofQ N) with hPdef
  have hR : (chartBasis p).det = 1 := hv.1
  have hP : P = chartBasis p * JLeaf.ofQ M0Q * BravaisCover.toRealMatrix Γ := by
    rw [hPdef, strainBasis_bcc, Matrix.mul_assoc, hNM, ← Matrix.mul_assoc]
  have hdet : P.det = 1 / 2 := by
    rw [hPdef, strainBasis_bcc, Matrix.det_mul, Matrix.det_mul, hR, JLeaf.ofQ_det N hN, M0Q_det]
    norm_num
  have hpoints : lattice P = q.points := by
    rw [hP, BravaisCover.rebase_sameLattice _ Γ Γ' hΓ, lattice_mul_M0]
    rfl
  have hs : (ac • P).det ≠ 0 := by
    rw [Matrix.det_smul, Fintype.card_fin, hdet]
    exact (mul_pos (pow_pos ac_positive _) (by norm_num)).ne'
  have hphys : lattice (ac • P) = periodicPoints (physicalBasis q) (physicalTwoPositions q) := by
    rw [Constants.scaled_lattice, hpoints, Constants.physical_points_eq_twoSite]
  have hpos : 0 < seriesScreen := div_pos (Real.sqrt_pos.mpr Real.pi_pos) ac_positive
  have he := Constants.pointsRepetition_energy (ac • P) hs q hq hphys seriesScreen hpos
  have hE : oneSiteEnergy P = energy q := by
    unfold oneSiteEnergy
    rw [← he, green_two_eq_energy q hq]
  let model : PrimitiveAnchorModel q := ⟨P, hdet, hpoints, hE⟩
  have hD : oneSiteDefect P = defect q := anchor_same_defect model
  unfold oneSiteDeficit deficit
  rw [hE, hD]

/-! ### The layered gain with a negative `k` -/

/-- The argument of `planarAnchorCertOk_sound` with `k < 0` and `0 ≤ 200 g⁻ + k` in place of `0 < k`:
`deficit(anchor) + k |R d|²⁺ ≤ deficit` on the box. -/
theorem centered_gain (depth : ℕ) (k : ℚ) (reg : JLeaf.RegData) (box : Cell) (n : IntVec)
    (hneg : k < 0) (hk : 0 ≤ 200 * Constants.gapBracket.lo + k)
    (hsplit : splitOk (anchorW n) (lamOf k) depth (shiftCell box (seamShiftW n)) = true)
    (hreg : JLeaf.registrationCheck reg.B reg.N reg.U reg.f0 = true)
    (hw : reg.w = ![((anchorW n).k₁ : ℚ) / 2, ((anchorW n).k₂ : ℚ) / 2, 1 / 2])
    (hg : guardsOk (shiftCell box (seamShiftW n)) = true)
    (hsep : sepOk (shiftCell box (seamShiftW n)) = true)
    (hcost : 2 * (100 * (strainF (shiftCell box (seamShiftW n)) reg.N reg.U).hi +
      200 * (gramF (shiftCell box (seamShiftW n)) (anchorW n)).hi) ≤ Sz)
    (p : Chart) (hp : box.Mem p) (gp : good p) :
    deficit (anchorOf (chartPoint p) halfAll) +
        (k : ℝ) * ((gramF (shiftCell box (seamShiftW n)) (anchorW n)).hi : ℝ) / Sz ≤
      deficit (chartPoint p) := by
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨an, han⟩ : ∃ an, an = anchorW n := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb] at hsplit hg hsep hcost ⊢
  rw [← han] at hsplit hcost hw ⊢
  have hp' : b.Mem p' := by
    rw [hb, shifted_iff]
    have : shiftChart p' (-seamShiftW n) = p := by
      rw [hp'def]; funext i; fin_cases i <;> simp [shiftChart, seamShiftW]
      ring
    rw [this]; exact hp
  have g : Guards b := by
    have := of_decide_eq_true hg
    exact ⟨this.1, this.2.1, this.2.2⟩
  have sp := Sz_pos
  have e0 : p' 0 = p 0 := by rw [hp'def]; rfl
  have e1 : p' 1 = p 1 := by rw [hp'def]; rfl
  have hr : 0 < p 0 := by
    have := (div_pos (by exact_mod_cast g.r₀) sp).trans_le (cx_mem hp' 0).1
    rwa [e0] at this
  have hs : 0 < p 1 := by
    have := (div_pos (by exact_mod_cast g.r₁) sp).trans_le (cx_mem hp' 1).1
    rwa [e1] at this
  -- the gain
  have gain := splitOk_gain depth hsplit hp'
  have hE : energy (chartPoint p') = energy (chartPoint p) := by
    rw [hp'def, chartPoint_shift, energy_wrap]
  have hA := anchor_chart_wrap p n
  rw [← hp'def, ← han] at hA
  have hEa : energy (chartPoint (anchorChart p' (an.k₁ / 2) (an.k₂ / 2))) =
      energy (anchorOf (chartPoint p) halfAll) := by rw [hA, energy_wrap]
  have hDa : defect (chartPoint (anchorChart p' (an.k₁ / 2) (an.k₂ / 2))) =
      defect (anchorOf (chartPoint p) halfAll) := by rw [hA, defect_wrap]
  have hG := gram_eq p n
  rw [← hp'def, ← han] at hG
  obtain ⟨bq, hbq⟩ : ∃ x, x = sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) :=
    ⟨_, rfl⟩
  rw [← hbq] at hG
  rw [hE, hEa, hG] at gain
  -- the scale and the gap
  obtain ⟨_, acHi⟩ := JLeaf.ac_bounds scale_check
  have ac0 : 0 < ac := ac_positive
  have gapB := Constants.reference_gap_checked
  have gap0 : 0 < gap := gapB.2
  have gapLo : (Constants.gapBracket.lo : ℝ) ≤ gap := gapB.1.1
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := gapB.1.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  -- the anchor defect from the literal registration
  obtain ⟨pa, hpa⟩ : ∃ q, q = anchorChart p' (an.k₁ / 2) (an.k₂ / 2) := ⟨_, rfl⟩
  rw [← hpa] at hEa hDa hA
  have hstrain : JLeaf.strainCost reg.N reg.U pa = JLeaf.strainCost reg.N reg.U p' := by
    have h0 : pa 0 = p' 0 := by rw [hpa]; rfl
    have h1 : pa 1 = p' 1 := by rw [hpa]; rfl
    have h2 : pa 2 = p' 2 := by rw [hpa]; rfl
    have h3 : pa 3 = p' 3 := by rw [hpa]; rfl
    have h4 : pa 4 = p' 4 := by rw [hpa]; rfl
    unfold JLeaf.strainCost JLeaf.strainEntry
    rw [h0, h1, h2, h3, h4]
  have himg (i : Fin 3) : JLeaf.img (fun i => -reg.w i) true pa i = 0 := by
    rw [hw, hpa]
    fin_cases i <;> simp [JLeaf.img, anchorChart, DirectRoute.offset]
  have hprimal : JLeaf.primalQ (fun i => -reg.w i) true pa = 0 := by
    simp only [JLeaf.primalQ, JLeaf.rowA, JLeaf.rowB, JLeaf.rowC, himg]
    ring
  have hregCost : JLeaf.regCost reg.N reg.U reg.w pa = 100 * JLeaf.strainCost reg.N reg.U p' := by
    unfold JLeaf.regCost
    rw [hprimal, hstrain]
    ring
  have strainUp := (strainF_mem hp' g reg.N reg.U).2
  have gramUp := (gramF_mem hp' g an).2
  rw [hG] at gramUp
  have hcostR : 2 * (100 * ((strainF b reg.N reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) ≤ (Sz : ℝ) := by
    exact_mod_cast hcost
  have dUp : 100 * JLeaf.strainCost reg.N reg.U p' + 200 * bq ≤ 1 / 2 := by
    have q1 : 100 * JLeaf.strainCost reg.N reg.U p' + 200 * bq ≤
        (100 * ((strainF b reg.N reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) / Sz := by
      rw [add_div, mul_div_assoc, mul_div_assoc]
      linarith
    have q2 : (100 * ((strainF b reg.N reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) / Sz ≤ 1 / 2 := by
      rw [div_le_iff₀ sp]; linarith
    linarith
  have hvalid : (chartPoint p).Valid := gp.1
  have paValid : (chartPoint pa).Valid := by
    rw [hA]
    have av := anchor_valid _ hvalid halfAll halfAll_half
    refine ⟨av.1, fun m h => av.2 (m - ![n 0, n 1, 1]) ?_⟩
    simp only [wrap] at h
    rw [JLeaf.castVec_sub', ← h]
    abel
  have regSmall : JLeaf.regCost reg.N reg.U (fun i => reg.f0 i + (reg.wrap i : ℚ)) pa ≤ 1 / 2 := by
    show JLeaf.regCost reg.N reg.U reg.w pa ≤ 1 / 2
    rw [hregCost]; linarith
  have dAnchor := JLeaf.defect_le_regCost reg.B reg.N reg.U reg.f0 reg.wrap hreg pa paValid regSmall
  have dAnchor' : defect (anchorOf (chartPoint p) halfAll) ≤ 100 * JLeaf.strainCost reg.N reg.U p' := by
    rw [← hDa, ← hregCost]; exact dAnchor
  -- the defect transport
  have hsep₁ := gp.2.2.1
  have hrs : p 0 * p 1 < 1 := by
    have hlt := of_decide_eq_true hsep
    have h1 := FI.mulPos_mem (cx_mem hp' 0) (cx_mem hp' 1)
    have h2 : ((FI.mulPos (cx b 0) (cx b 1)).hi : ℝ) / Sz < 1 := by
      rw [div_lt_one sp]; exact_mod_cast hlt
    rw [e0, e1] at h1
    linarith [h1.2]
  have asep : ∀ m : IntVec, (1 / 2 : ℝ) ^ 2 < sq ((chartPoint p).basis.mulVec (castVec m + halfAll)) :=
    fun m => anchor_sep hr hs hrs halfAll rfl m
  have trans := defect_transport (chartPoint p) hvalid hsep₁ halfAll halfAll_half asep n
    (by rw [← hbq]; linarith)
  rw [← hbq] at trans
  -- combine, with `0 ≤ 200 gap + k`
  have hk0 : 0 ≤ 200 * gap + (k : ℝ) := by
    have h1 : (0 : ℝ) ≤ 200 * (Constants.gapBracket.lo : ℝ) + k := by exact_mod_cast hk
    linarith
  have hlam : (2 * ac) * (200 * gap + (k : ℝ)) ≤ (lamOf k : ℝ) := by
    unfold lamOf
    push_cast
    have h2 : 200 * gap + (k : ℝ) ≤ 200 * (Constants.gapBracket.hi : ℝ) + k := by linarith
    have h3 : (2 * ac) * (200 * gap + (k : ℝ)) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + k) :=
      mul_le_mul_of_nonneg_right (by linarith) hk0
    have h4 : (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + k) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + k) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (200 * gap + (k : ℝ)) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((200 * gap + (k : ℝ)) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  have deficitGain : deficit (anchorOf (chartPoint p) halfAll) + (k : ℝ) * bq ≤ deficit (chartPoint p) := by
    unfold deficit
    have h1 := mul_le_mul_of_nonneg_left trans gap0.le
    nlinarith
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hneg
  have hkb : (k : ℝ) * (((gramF b an).hi : ℝ) / Sz) ≤ (k : ℝ) * bq := mul_le_mul_of_nonpos_left gramUp hkR.le
  have e : (k : ℝ) * ((gramF b an).hi : ℝ) / Sz = (k : ℝ) * (((gramF b an).hi : ℝ) / Sz) := by ring
  rw [e]
  linarith

/-! ### The checker -/

/-- The proposal data of one centered PlanarAnchor request. -/
structure CenteredCert where
  /-- Split depth of the layered gain. -/
  depth : ℕ
  /-- The (negative) gain coefficient. -/
  k : ℚ
  /-- The literal registration of the anchor. -/
  reg : JLeaf.RegData
  /-- The anchor margin, in units of `2⁻⁶⁴` of the series inequality. -/
  margin : ℤ
  /-- `Γ` with `N M₀ = M₀ Γ`, and its inverse. -/
  gamma : Matrix (Fin 3) (Fin 3) ℤ
  gammaInv : Matrix (Fin 3) (Fin 3) ℤ
  /-- The subdivision of the box for the anchor deficit. -/
  tree : AnchorTree

/-- The layered gain with a negative `k`: the conjuncts of `planarAnchorCertOk` with `0 < k` replaced by
`k < 0 ∧ 0 ≤ 200 g⁻ + k`. -/
def centeredGainOk (c : CenteredCert) (box : Cell) (n : IntVec) : Bool :=
  let b := shiftCell box (seamShiftW n)
  let an := anchorW n
  ((decide (c.k < 0 ∧ 0 ≤ 200 * Constants.gapBracket.lo + c.k) && splitOk an (lamOf c.k) c.depth b) &&
      (JLeaf.registrationCheck c.reg.B c.reg.N c.reg.U c.reg.f0 &&
        decide (c.reg.w = ![(an.k₁ : ℚ) / 2, (an.k₂ : ℚ) / 2, 1 / 2]))) &&
    ((guardsOk b && sepOk b) &&
      decide (2 * (100 * (strainF b c.reg.N c.reg.U).hi + 200 * (gramF b an).hi) ≤ Sz))

/-- The anchor basis and the final inequality `0 < m / 2⁶⁴ / (2 scaleHi) + k |R d|²⁺`. -/
def centeredAnchorOk (c : CenteredCert) (box : Cell) (n : IntVec) : Bool :=
  anchorBasisOk c.reg.N c.gamma c.gammaInv &&
    decide (0 < (c.margin : ℚ) / 2 ^ 64 / (2 * BravaisCover.scaleHi) +
      c.k * ((gramF (shiftCell box (seamShiftW n)) (anchorW n)).hi : ℚ) / Sz)

def centeredCertOk (D : BravaisCover.StrainAtlas.AtlasData) (c : CenteredCert) (box : Cell) (n : IntVec) :
    Bool :=
  (centeredGainOk c box n && centeredAnchorOk c box n) && anchorTreeOk D c.reg.N c.margin c.tree box

/-- `centeredCertOk` from its three parts (each can be its own kernel check). -/
theorem centeredCertOk_of (D : BravaisCover.StrainAtlas.AtlasData) (c : CenteredCert) (box : Cell)
    (n : IntVec) (h₁ : centeredGainOk c box n = true) (h₂ : centeredAnchorOk c box n = true)
    (h₃ : anchorTreeOk D c.reg.N c.margin c.tree box = true) : centeredCertOk D c box n = true := by
  rw [centeredCertOk, h₁, h₂, h₃]
  rfl

/-- One split of an anchor tree from its two halves (each can be its own kernel check). -/
theorem anchorTreeOk_split_of (D : BravaisCover.StrainAtlas.AtlasData) (N : Fin 3 → Fin 3 → ℚ) (m : ℤ)
    (i : Axis) (lower upper : AnchorTree) (b : Cell)
    (hl : anchorTreeOk D N m lower ((Cut.dyadic i).child b false) = true)
    (hu : anchorTreeOk D N m upper ((Cut.dyadic i).child b true) = true) :
    anchorTreeOk D N m (.split i lower upper) b = true := by
  rw [anchorTreeOk, hl, hu]
  rfl

theorem centeredCertOk_sound (D : BravaisCover.StrainAtlas.AtlasData) (hD : D.Valid) (c : CenteredCert)
    (box : Cell) (n : IntVec) (ok : centeredCertOk D c box n = true) (p : Chart) (hp : box.Mem p)
    (gp : good p) : 0 < deficit (chartPoint p) := by
  simp only [centeredCertOk, centeredGainOk, centeredAnchorOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨hk, hsplit⟩, hreg, hw⟩, ⟨hg, hsep⟩, hcost⟩, ⟨hbasis, hfinal⟩⟩, htree⟩ := ok
  have gain := centered_gain c.depth c.k c.reg box n hk.1 hk.2 hsplit hreg hw hg hsep hcost p hp gp
  obtain ⟨hN, hNM, hΓ⟩ := anchorBasisOk_sound hbasis
  have hanchor := anchorTreeOk_sound D hD c.reg.N hN c.margin c.tree box htree p hp
  rw [← anchor_deficit_eq p gp.1 c.reg.N c.gamma c.gammaInv hN hNM hΓ] at hanchor
  have hf : (0 : ℝ) < (c.margin : ℝ) / 2 ^ 64 / (2 * (BravaisCover.scaleHi : ℝ)) +
      (c.k : ℝ) * ((gramF (shiftCell box (seamShiftW n)) (anchorW n)).hi : ℝ) / Sz := by
    exact_mod_cast hfinal
  linarith

/-- The centered PlanarAnchor checker, from a valid atlas and a table of certificates. -/
def centeredCheck (D : BravaisCover.StrainAtlas.AtlasData) (table : Request → Option CenteredCert) :
    Checker := fun q =>
  match q.packet, q.proposal.payload with
  | .planarAnchor, .centered _ wrap _ _ =>
    match table q with
    | some c => centeredCertOk D c q.target.box wrap
    | none => false
  | _, _ => false

theorem centeredCheck_sound (D : BravaisCover.StrainAtlas.AtlasData) (hD : D.Valid)
    (table : Request → Option CenteredCert) : CheckerSound (centeredCheck D table) := by
  intro q _ _ _ h p hp gp
  unfold centeredCheck at h
  rcases q with ⟨packet, root, path, ⟨ancestor, payload⟩⟩
  cases packet <;> try (simp at h)
  cases payload with
  | centered method wrap hint slack =>
    cases hc : table ⟨.planarAnchor, root, path, ⟨ancestor, .centered method wrap hint slack⟩⟩ with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      have pos := centeredCertOk_sound D hD c _ wrap h p hp gp
      show (Proposal.route (.centered method wrap hint slack)).result p
      cases method <;> simpa only [Proposal.route, Route.result] using pos
  | _ => simp at h


end BccSharp.Coulomb.CompactCover.Layered
