import BccSharp.Cover.PlanarFibreTaylor
import BccSharp.Cover.PlanarFibrePlanar
import BccSharp.Cover.LateCompose

set_option autoImplicit false

/-! # The PlanarFibre triangular check

* The real functions `dTermR`, `kTermR`, `baseR`, `waveR` and the parts
  `phi2R`, `phi1R`, `phi0R` of the smooth lower bound `Φ`, with the jet
  enclosures `phi2J_mem`, `phi1J_mem`, `phi0J_mem` on every cell.
* `energy_ge`: on the seam cell of a box that passes `fixCheck`,
  `2 a_c energy ≥ Φ₂ + Φ₁ + Φ₀ - tailZ/S`, from the planar identity
  (`addressed_energy_planar_of_guards`), the finite planar lower bound
  (`planarRegularized_ge`), the axial and radial tails of `BccSharp.Cover.OverlayFixSound`
  and the partition of `wavesList 2` into the three tiers.
* `boxOk_sound`: a passing `boxOk raw p0` proves `energy fcc < energy` on `raw`.
* `TriTree`: closed dyadic splits with an expansion point at each leaf,
  `TriTree.ok_sound`; `planarFibreTriCheck` and `planarFibreTriCheck_sound:
  CheckerSound (planarFibreTriCheck t)` for the late checker's triangular family. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri
open BccSharp BccSharp.Coverage DirectRoute
open OverlayPlanar OverlayPlanar.Fix
open BravaisCover (kernelValue KernelKind)

theorem J2Mem.of_eq {B : Cell} {J : J2} {f g : Chart → ℝ} (h : J2Mem B J f) (e : ∀ p, f p = g p) :
    J2Mem B J g := by
  have : f = g := funext e
  subst this
  exact h

/-! ### The real parts of `Φ` -/

def dTermR (p : Chart) (m : Wave) : ℝ := 2 * gKernel (1/2) (Real.pi * planarNorm p (m.1 : ℝ) (m.2 : ℝ))
def kTermR (p : Chart) (m : Wave) : ℝ := 2 * cReal p * gKernel (1/2) (Real.pi * κSq p m)
def baseR (p : Chart) : ℝ := zeroMode p - 2 * cReal p - 2
def waveR (p : Chart) (m : Wave) : ℝ :=
  2 * cReal p * axialCore (tReal p m) (wReal p m) (uReal p m) (p 7) / κReal p m

def phi2R (p : Chart) : ℝ :=
  baseR p + (d2Modes.map (dTermR p)).sum + (k2Modes.map (kTermR p)).sum + (w2Modes.map (waveR p)).sum
def phi1R (p : Chart) : ℝ := (d1Modes.map (dTermR p)).sum + (w1Modes.map (waveR p)).sum
def phi0R (p : Chart) : ℝ := (w0Modes.map (waveR p)).sum

/-! ### Constants -/

theorem half_const_mem : (⟨halfS, 0⟩ : MR).Mem (1 / 2) := by
  unfold MR.Mem
  rw [halfS_eq]
  have := Sz_pos
  simp only [Nat.cast_zero, zero_div]
  rw [show (Sz : ℝ) / 2 / Sz = 1 / 2 by field_simp]
  simp

theorem twelfth_mem : (MR.ofFI ⟨Sz / 12, cdivZ Sz 12⟩).Mem (1 / 12) := by
  apply MR.ofFI_mem
  have sp := Sz_pos
  have t : (0 : ℤ) < 12 := by norm_num
  constructor
  · refine (div_le_div_of_nonneg_right (fdiv_le Sz 12 t) sp.le).trans ?_
    rw [div_div, mul_comm, ← div_div, div_self sp.ne']
    norm_num
  · refine le_trans ?_ (div_le_div_of_nonneg_right (le_cdiv Sz 12 t) sp.le)
    rw [div_div, mul_comm, ← div_div, div_self sp.ne']
    norm_num

/-! ### The jets enclose the parts -/

section Jets
variable (B : Cell)

theorem c_mem : J2Mem B (vars B).c (fun p => cReal p) :=
  (((J2Mem.var B 0).mul (J2Mem.var B 1)).inv).of_eq fun _ => rfl

theorem d_mem : J2Mem B (vars B).d (fun p => p 7 - 1 / 2) :=
  (J2Mem.var B 7).sub (J2Mem.const half_const_mem)

theorem kSqJ_mem (m : Wave) : J2Mem B (kSqJ (vars B) m) (fun p => κSq p m) :=
  (((((J2Mem.var B 0).inv).smul m.1).sq).add
    ((((J2Mem.const (MR.ofInt_mem m.2)).sub ((J2Mem.var B 2).smul m.1)).mul (J2Mem.var B 1).inv).sq)).of_eq
    fun _ => rfl

theorem normJ_mem (m : Wave) : J2Mem B (normJ (vars B) m) (fun p => planarNorm p (m.1 : ℝ) (m.2 : ℝ)) :=
  ((((J2Mem.var B 0).mul ((J2Mem.const (MR.ofInt_mem m.1)).add ((J2Mem.var B 2).smul m.2))).sq).add
    (((J2Mem.var B 1).smul m.2).sq)).of_eq fun p => by
      simp only [planarNorm]
      ring

theorem dTermJ_mem (m : Wave) : J2Mem B (dTermJ (vars B) m) (fun p => dTermR p m) :=
  (((((normJ_mem B m).scale (MR.ofFI_mem piF_mem)).ghalf).smul 2)).of_eq fun p => by
    simp only [dTermR, kernel_half]
    push_cast
    ring_nf

theorem kTermJ_mem (m : Wave) : J2Mem B (kTermJ (vars B) m) (fun p => kTermR p m) :=
  (((c_mem B).mul (((kSqJ_mem B m).scale (MR.ofFI_mem piF_mem)).ghalf)).smul 2).of_eq fun p => by
    simp only [kTermR, kernel_half]
    push_cast
    ring_nf

theorem baseJ_mem : J2Mem B (baseJ (vars B)) baseR :=
  (((((c_mem B).sq.mul ((d_mem B).sq.add (J2Mem.const twelfth_mem))).scale (MR.ofFI_mem twoPiF_mem)).sub
    ((c_mem B).smul 2)).sub (J2Mem.const (MR.ofInt_mem 2))).of_eq fun p => by
      simp only [baseR, zeroMode]
      push_cast
      ring

theorem waveJ_mem (m : Wave) : J2Mem B (waveJ (vars B) m) (fun p => waveR p m) := by
  have hk := (kSqJ_mem B m).sqrt
  have ht := ((c_mem B).mul hk).scale (MR.ofFI_mem twoPiF_mem)
  have hpre := ((c_mem B).mul hk.inv).smul 4
  have hw := ((((J2Mem.var B 3).sub ((J2Mem.var B 2).mul (J2Mem.var B 4))).smul m.1).add
    ((J2Mem.var B 4).smul m.2))
  have hu := (((J2Mem.var B 5).smul m.1).add ((J2Mem.var B 6).smul m.2))
  have hd := d_mem B
  have hph := hu.add (hw.mul hd)
  have htd := ht.mul hd
  have hB := hpre.mul ht.half.expNeg
  refine (((hpre.mul ht.expNeg).mul hw.cos2pi).add (((hB.mul htd.cosh).mul (hw.half.cos2pi.mul hph.cos2pi)).add
    ((hB.mul htd.sinh).mul (hw.half.sin2pi.mul hph.sin2pi)))).of_eq fun p => ?_
  simp only [waveR, axialCore, tReal, κReal, wReal, uReal, coshExp, sinhExp]
  rw [← Real.cosh_eq, ← Real.sinh_eq]
  have hk0 : Real.sqrt (κSq p m) = κReal p m := rfl
  push_cast
  have e1 : 2 * Real.pi * (((m.1 : ℝ) * (p 3 - p 2 * p 4) + (m.2 : ℝ) * p 4) / 2) =
      Real.pi * ((m.1 : ℝ) * (p 3 - p 2 * p 4) + (m.2 : ℝ) * p 4) := by ring
  have e2 : 2 * (Real.pi * ((m.1 : ℝ) * (p 3 - p 2 * p 4) + (m.2 : ℝ) * p 4)) =
      2 * Real.pi * ((m.1 : ℝ) * (p 3 - p 2 * p 4) + (m.2 : ℝ) * p 4) := by ring
  have e3 : -(2 * Real.pi * (cReal p * Real.sqrt (κSq p m)) / 2) =
      -(2 * Real.pi * cReal p * Real.sqrt (κSq p m)) / 2 := by ring
  have e4 : -(2 * Real.pi * (cReal p * Real.sqrt (κSq p m))) = -(2 * Real.pi * cReal p * Real.sqrt (κSq p m)) := by
    ring
  rw [e1, e2, e3, e4]
  field_simp
  ring

theorem phi2J_mem : J2Mem B (phi2J B) phi2R :=
  (((((baseJ_mem B).add (J2Mem.jsum d2Modes (dTermJ (vars B)) (fun m p => dTermR p m) fun m _ => dTermJ_mem B m)).add
    (J2Mem.jsum k2Modes (kTermJ (vars B)) (fun m p => kTermR p m) fun m _ => kTermJ_mem B m)).add
    (J2Mem.jsum w2Modes (waveJ (vars B)) (fun m p => waveR p m) fun m _ => waveJ_mem B m))).of_eq fun _ => rfl

theorem phi1J_mem : J2Mem B (phi1J B) phi1R :=
  ((J2Mem.jsum d1Modes (dTermJ (vars B)) (fun m p => dTermR p m) fun m _ => dTermJ_mem B m).add
    (J2Mem.jsum w1Modes (waveJ (vars B)) (fun m p => waveR p m) fun m _ => waveJ_mem B m)).of_eq fun _ => rfl

theorem phi0J_mem : J2Mem B (phi0J B) phi0R :=
  (J2Mem.jsum w0Modes (waveJ (vars B)) (fun m p => waveR p m) fun m _ => waveJ_mem B m).of_eq fun _ => rfl

end Jets

/-! ### The energy bound on a box -/

/-- One retained wave: `waveValue ≥ axialCore/κ - (tailF/S)(κ⁻¹.hi/S)`. -/
theorem waveValue_ge {b : Cell} {q : Chart} (hq : b.Mem q) (g : Guards b) (η0 : 0 < etaN b) (m : Wave)
    (ok : waveOK b m = true) :
    axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m -
        ((tailF b m : ℝ) / Sz) * ((((kappaF b m).invPos).hi : ℝ) / Sz) ≤ waveValue q m ∧
      0 ≤ (tailF b m : ℝ) / Sz := by
  have sp := Sz_pos
  simp only [waveOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨κ0, tpos, A1⟩, _, _⟩ := ok
  have ht := tF_mem hq g m
  have e : (((tF b m).lo.toNat : ℕ) : ℝ) = ((tF b m).lo : ℝ) := by exact_mod_cast Int.toNat_of_nonneg tpos.le
  have tl : ((((tF b m).lo.toNat : ℕ) : ℝ) / Sz) ≤ tReal q m := by rw [e]; exact ht.1
  have t0p : 0 < (((tF b m).lo.toNat : ℕ) : ℝ) / Sz := by rw [e]; exact div_pos (by exact_mod_cast tpos) sp
  obtain ⟨ηp, ηl, ηu⟩ := eta_bounds hq η0
  obtain ⟨_, tail⟩ := axialTail_sound (wReal q m) (uReal q m) (q 7) ((etaN b : ℝ) / Sz) t0p tl ηp.le ηl ηu
  have hT := tail.trans (tailF_bound m A1)
  have T0 : 0 ≤ (tailF b m : ℝ) / Sz := (abs_nonneg _).trans hT
  have hk := kappaF_mem hq g m
  have kpos : 0 < κReal q m := (div_pos (by exact_mod_cast κ0) sp).trans_le hk.1
  have hinv := FI.invPos_mem κ0 hk
  refine ⟨?_, T0⟩
  have lo := (abs_le.mp hT).1
  unfold waveValue
  have h1 : (axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) - (tailF b m : ℝ) / Sz) / κReal q m ≤
      axialSeries (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m :=
    div_le_div_of_nonneg_right (by linarith) kpos.le
  have h2 : (tailF b m : ℝ) / Sz / κReal q m ≤ ((tailF b m : ℝ) / Sz) * ((((kappaF b m).invPos).hi : ℝ) / Sz) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv.2 T0
  rw [sub_div] at h1
  linarith

instance : DecidablePred UpperWave := fun m => by unfold UpperWave; infer_instance

theorem list_sum_map_sub {ι : Type*} (l : List ι) (f g : ι → ℝ) :
    (l.map fun i => f i - g i).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem list_sum_div {ι : Type*} (l : List ι) (f : ι → ℝ) (c : ℝ) :
    (l.map f).sum / c = (l.map fun i => f i / c).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    ring

theorem waves_perm : (w2Modes ++ w1Modes ++ w0Modes).Perm (wavesList 2) := by decide

/-- On the seam cell of a box that passes `fixCheck`,
`2 a_c energy ≥ Φ₂ + Φ₁ + Φ₀ - tailZ/S`. -/
theorem energy_ge {raw : Cell} (fix : fixCheck raw = true) {p : Chart} (hp : raw.Mem p) :
    phi2R (seamPoint raw p) + phi1R (seamPoint raw p) + phi0R (seamPoint raw p) -
      (tailZ (seamCell raw) : ℝ) / Sz ≤ 2 * ac * energy (chartPoint p) := by
  have sp := Sz_pos
  simp only [fixCheck, Bool.and_eq_true, decide_eq_true_eq] at fix
  obtain ⟨⟨hd, hη⟩, ⟨r₀, r₁, r₀₁, η0⟩, waves, rad⟩ := fix
  set q := seamPoint raw p with hqd
  set b := seamCell raw with hbd
  have hq : b.Mem q := seamPoint_mem hp
  have g : Guards b := ⟨r₀, r₁, r₀₁⟩
  have E := addressed_energy_planar_of_guards hp hd hη
  have hr : 0 < q 0 := (div_pos (by exact_mod_cast r₀) sp).trans_le (cx_mem hq 0).1
  have ht : 0 < q 1 := (div_pos (by exact_mod_cast r₁) sp).trans_le (cx_mem hq 1).1
  -- the planar part
  have hpl := planarRegularized_ge q hr ht (d2Modes ++ d1Modes) k2Modes (by decide) (by decide)
    (by decide) (by decide)
  have hD : 2 * ((d2Modes ++ d1Modes).map fun m => gKernel (1/2) (Real.pi * planarNorm q (m.1 : ℝ) (m.2 : ℝ))).sum =
      (d2Modes.map (dTermR q)).sum + (d1Modes.map (dTermR q)).sum := by
    rw [List.map_append, List.sum_append, mul_add, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    rfl
  have hK : 2 * cReal q * (k2Modes.map fun m => gKernel (1/2) (Real.pi * κSq q m)).sum =
      (k2Modes.map (kTermR q)).sum := by
    rw [← List.sum_map_mul_left]
    rfl
  -- the layer
  obtain ⟨_, hrad⟩ := radialF_bound hq g η0 rad
  have hret : retainedLayer q 2 = 2 * cReal q * ((wavesList 2).map (waveValue q)).sum := by
    unfold retainedLayer
    rw [sum_waves_eq]
  set τ : Wave → ℝ := fun m => ((tailF b m : ℝ) / Sz) * ((((kappaF b m).invPos).hi : ℝ) / Sz) with hτ
  have each : ∀ m ∈ wavesList 2,
      axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m - τ m ≤ waveValue q m :=
    fun m hm => (waveValue_ge hq g η0 m (List.all_eq_true.mp waves m hm)).1
  have τ0 : ∀ m ∈ wavesList 2, 0 ≤ τ m := by
    intro m hm
    have T0 := (waveValue_ge hq g η0 m (List.all_eq_true.mp waves m hm)).2
    have hk := kappaF_mem hq g m
    have hok := List.all_eq_true.mp waves m hm
    simp only [waveOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    have kpos : 0 < κReal q m := (div_pos (by exact_mod_cast hok.1.1) sp).trans_le hk.1
    have hinv := FI.invPos_mem hok.1.1 hk
    have : 0 ≤ (((kappaF b m).invPos).hi : ℝ) / Sz := (inv_pos.mpr kpos).le.trans hinv.2
    exact mul_nonneg T0 this
  have hsum := List.sum_le_sum each
  have hτsum : 0 ≤ ((wavesList 2).map τ).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    exact τ0 m hm)
  have hc := cF_mem hq g
  have cpos : 0 < cReal q := inv_pos.mpr (mul_pos hr ht)
  have hcore : ((wavesList 2).map fun m => axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m - τ m).sum =
      ((wavesList 2).map fun m => axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m).sum -
        ((wavesList 2).map τ).sum := by
    rw [list_sum_map_sub]
  have hwaves : 2 * cReal q * ((wavesList 2).map fun m => axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m).sum =
      (w2Modes.map (waveR q)).sum + (w1Modes.map (waveR q)).sum + (w0Modes.map (waveR q)).sum := by
    rw [← List.sum_map_mul_left]
    have e : ((wavesList 2).map fun m => 2 * cReal q * (axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m)) =
        (wavesList 2).map (waveR q) := by
      refine List.map_congr_left fun m _ => ?_
      simp only [waveR]
      ring
    rw [e, ← (waves_perm.map (waveR q)).sum_eq, List.map_append, List.map_append, List.sum_append, List.sum_append]
  -- the tail sum
  have htail : 2 * cReal q * ((wavesList 2).map τ).sum + (radialF b : ℝ) / Sz ≤ (tailZ b : ℝ) / Sz := by
    set s : ℤ := ((wavesList 2).map fun m => (tailF b m) * ((kappaF b m).invPos).hi).sum with hs
    have hsR : ((wavesList 2).map τ).sum = (s : ℝ) / Sz / Sz := by
      have hs' : (s : ℝ) = ((wavesList 2).map fun m => (tailF b m : ℝ) * (((kappaF b m).invPos).hi : ℝ)).sum := by
        rw [hs, Int.cast_list_sum, List.map_map]
        congr 1
        refine List.map_congr_left fun m _ => ?_
        simp only [Function.comp_apply, Int.cast_mul]
      rw [hs', list_sum_div, list_sum_div]
      congr 1
      refine List.map_congr_left fun m _ => ?_
      simp only [hτ]
      ring
    have hcl : cReal q ≤ ((cF b).hi : ℝ) / Sz := hc.2
    have h1 : 2 * cReal q * ((wavesList 2).map τ).sum ≤ 2 * (((cF b).hi : ℝ) / Sz) * ((wavesList 2).map τ).sum :=
      mul_le_mul_of_nonneg_right (by linarith) hτsum
    have h2 : 2 * (((cF b).hi : ℝ) / Sz) * ((s : ℝ) / Sz / Sz) =
        ((2 * (cF b).hi * s : ℤ) : ℝ) / ((Sz * Sz : ℤ) : ℝ) / Sz := by
      push_cast
      field_simp
    have h3 := le_cdiv (2 * (cF b).hi * s) (Sz * Sz) (mul_pos Sz_posZ Sz_posZ)
    unfold tailZ
    rw [← hs]
    push_cast
    rw [add_div, hsR]
    rw [hsR] at h1
    have h4 := div_le_div_of_nonneg_right h3 sp.le
    linarith
  -- assemble
  have hlay : layerValue q ≥ retainedLayer q 2 - (radialF b : ℝ) / Sz := by
    have := (abs_le.mp hrad).1
    linarith
  rw [hret] at hlay
  have hlay2 : 2 * cReal q * ((wavesList 2).map (waveValue q)).sum ≥
      2 * cReal q * (((wavesList 2).map fun m => axialCore (tReal q m) (wReal q m) (uReal q m) (q 7) / κReal q m).sum -
        ((wavesList 2).map τ).sum) := by
    rw [← hcore]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  rw [E]
  unfold phi2R phi1R phi0R baseR
  rw [mul_sub] at hlay2
  rw [hwaves] at hlay2
  linarith

/-! ### One box -/

theorem twoAc_fcc_le : 2 * ac * energy fcc ≤ (thresholdZ : ℝ) / Sz := by
  have h := fccHUpper_sound scaleRoot_ok
  have th := threshold_ge
  have fe : (fccHUpper : ℝ) - 4 = (fccThreshold : ℝ) := by exact_mod_cast fccThreshold_eq
  linarith

/-- A passing box check proves the strict FCC route on the box. -/
theorem boxOk_sound {raw : Cell} {p0 : Fin 8 → ℚ} (ok : boxOk raw p0 = true) {p : Chart} (hp : raw.Mem p) :
    energy fcc < energy (chartPoint p) := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨fix, hin⟩, jets, strict⟩ := ok
  set b := seamCell raw with hbd
  have hq := seamPoint_mem hp
  simp only [jetsOk, Bool.and_eq_true] at jets
  obtain ⟨⟨⟨o2p, o1p⟩, ⟨o2b, o1b⟩⟩, o0b⟩ := jets
  have tl := taylorLowerOf_le hin o2p o1p o2b o1b o0b (phi2J_mem _) (phi1J_mem _) (phi2J_mem b)
    (phi1J_mem b) (phi0J_mem b) hq
  have E := energy_ge fix hp
  have strictR : ((toQ thresholdZ + toQ (tailZ b) : ℚ) : ℝ) < ((taylorLower b p0 : ℚ) : ℝ) := by
    exact_mod_cast strict
  rw [Rat.cast_add, toQ_cast, toQ_cast] at strictR
  have hT : ((taylorLower b p0 : ℚ) : ℝ) ≤ phi2R (seamPoint raw p) + phi1R (seamPoint raw p) +
      phi0R (seamPoint raw p) := tl
  have hfcc := twoAc_fcc_le
  have hac := ac_positive
  have h4 : 2 * ac * energy fcc < 2 * ac * energy (chartPoint p) := by linarith
  exact lt_of_mul_lt_mul_left h4 (mul_pos two_pos hac).le

/-! ### Split trees -/

/-- Closed dyadic splits of a box, with an expansion point at each leaf. -/
inductive TriTree where
  | leaf (p0 : Fin 8 → ℚ)
  | split (axis : Fin 8) (low high : TriTree)

/-- The lower closed half along axis `i`. -/
def lowHalf (c : Cell) (i : Fin 8) : Cell := ⟨c.lo, Function.update c.hi i ((c.lo i + c.hi i) / 2)⟩
/-- The upper closed half along axis `i`. -/
def highHalf (c : Cell) (i : Fin 8) : Cell := ⟨Function.update c.lo i ((c.lo i + c.hi i) / 2), c.hi⟩

def TriTree.ok : TriTree → Cell → Bool
  | .leaf p0, c => boxOk c p0
  | .split i low high, c => low.ok (lowHalf c i) && high.ok (highHalf c i)

theorem half_cover {c : Cell} {p : Chart} (hp : c.Mem p) (i : Fin 8) :
    (lowHalf c i).Mem p ∨ (highHalf c i).Mem p := by
  by_cases h : p i ≤ (((c.lo i + c.hi i) / 2 : ℚ) : ℝ)
  · left
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [lowHalf, Function.update_self]
      exact ⟨(hp j).1, h⟩
    · simp only [lowHalf, Function.update_of_ne hj]
      exact hp j
  · right
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [highHalf, Function.update_self]
      exact ⟨(not_le.mp h).le, (hp j).2⟩
    · simp only [highHalf, Function.update_of_ne hj]
      exact hp j

theorem TriTree.ok_sound : ∀ (t : TriTree) (c : Cell), t.ok c = true →
    ∀ p, c.Mem p → energy fcc < energy (chartPoint p)
  | .leaf p0, c, h, p, hp => boxOk_sound h hp
  | .split i low high, c, h, p, hp => by
    simp only [TriTree.ok, Bool.and_eq_true] at h
    rcases half_cover hp i with h1 | h2
    · exact TriTree.ok_sound low _ h.1 p h1
    · exact TriTree.ok_sound high _ h.2 p h2

/-! ### The late checker's triangular family -/

open LatePackets in
/-- The PlanarFibre triangular check: a request with a triangular payload is accepted
when its table entry is a tree that passes on the request's target box. -/
def planarFibreTriCheck (t : Request → Option TriTree) : Checker := fun q =>
  match q.proposal.payload with
  | .triangular _ _ =>
    match t q with
    | some tr => tr.ok q.target.box
    | none => false
  | _ => false

open LatePackets in
theorem planarFibreTriCheck_sound (t : Request → Option TriTree) : CheckerSound (planarFibreTriCheck t) := by
  intro q _ _ _ h p hp _
  unfold planarFibreTriCheck at h
  revert h
  cases hpay : q.proposal.payload with
  | triangular radius hint =>
    intro h
    cases ht : t q with
    | none =>
      rw [ht] at h
      exact absurd h (by simp)
    | some tr =>
      rw [ht] at h
      show energy fcc < energy (chartPoint p)
      exact TriTree.ok_sound tr _ h p hp
  | corner _ _ _ => intro h; exact absurd h (by simp)
  | joint _ _ _ => intro h; exact absurd h (by simp)
  | optical _ _ _ _ => intro h; exact absurd h (by simp)
  | centered _ _ _ _ => intro h; exact absurd h (by simp)

open LatePackets in
/-- Request-level acceptance: a triangular request whose table entry is a tree
that passes on its target box is accepted. -/
theorem planarFibreTriCheck_of (t : Request → Option TriTree) (q : Request) (radius hint : ℚ) (tr : TriTree)
    (hpay : q.proposal.payload = .triangular radius hint) (ht : t q = some tr)
    (ok : tr.ok q.target.box = true) : planarFibreTriCheck t q = true := by
  simp only [planarFibreTriCheck, hpay, ht, ok]

end BccSharp.Coulomb.CompactCover.PlanarFibreTri
