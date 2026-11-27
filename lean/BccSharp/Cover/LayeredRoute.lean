import BccSharp.Cover.LayeredFixSound
import BccSharp.Cover.LayeredDefect
import BccSharp.Cover.LateCompose
import BccSharp.Cover.JLeafCheck
import BccSharp.Cover.CoverEarlyTransport

set_option autoImplicit false

/-! # The PlanarAnchor relative comparisons as a late checker

A PlanarAnchor relative request (`.optical .layered .basin half hint`, all three half
bits set, wrap `n`) is accepted when its certificate passes:

* `Fix.splitOk` on the seam cell (the box with its third offset shifted by
  `1 − n₂`, so that the anchor height is `1/2`), with anchor integers
  `k = 2(f₀ + n)`, retained cube 3 and `λ = 2 a_c⁺ (200 g⁺ + k)`;
* a literal registration `(B, N, U, f₀, wrap)` with `registrationCheck`, whose
  half translation plus wrap is the anchor offset, and the cost bound
  `100 · strain⁺ + 200 · |R d|²⁺ ≤ 1/2` on the cell;
* `r s < 1` on the cell (the coset separation of the anchor).

`planarAnchorCheck_sound` proves `CheckerSound (planarAnchorCheck table)` from `LatticeCase`:
at every `good` point of the box, `Fix.splitOk_gain` bounds the energy gain
over the anchor by `λ |R d|² / (2 a_c)`; `JLeaf.defect_le_regCost` bounds the
anchor's defect by the literal registration; `defect_transport` bounds the
defect change by `200 |R d|²`; and `relativeOptical_route_of_lattice` turns the
resulting `deficit(anchor) + k |R d|² ≤ deficit` into the route result. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.Layered
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.Layered.Fix

/-! ### Fixed-point bounds on a cell -/

def ptQ (q : ℚ) : FI := ofRat q q

theorem ptQ_mem (q : ℚ) : (ptQ q).Mem (q : ℝ) := ofRat_mem ⟨le_rfl, le_rfl⟩

/-- Entry `(i, j)` of `chartBasis p · N`, as in `JLeaf.strainEntry`. -/
def strainEntryF (b : Cell) (N : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) : FI :=
  if i = 0 then FI.mul (cx b 0) (((ptQ (N 0 j)).add (FI.mul (cx b 2) (ptQ (N 1 j)))).add
    (FI.mul (cx b 3) (ptQ (N 2 j))))
  else if i = 1 then FI.mul (cx b 1) ((ptQ (N 1 j)).add (FI.mul (cx b 4) (ptQ (N 2 j))))
  else FI.mul (ptQ (N 2 j)) (cF b)

def strainTerm (b : Cell) (N U : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) : FI :=
  FI.sq ((strainEntryF b N i j).sub (ptQ (U i j)))

/-- An enclosure of `‖chartBasis p · N − U‖²_F`. -/
def strainF (b : Cell) (N U : Fin 3 → Fin 3 → ℚ) : FI :=
  sumF [strainTerm b N U 0 0, strainTerm b N U 0 1, strainTerm b N U 0 2,
    strainTerm b N U 1 0, strainTerm b N U 1 1, strainTerm b N U 1 2,
    strainTerm b N U 2 0, strainTerm b N U 2 1, strainTerm b N U 2 2]

theorem strainEntryF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b)
    (N : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) :
    (strainEntryF b N i j).Mem (JLeaf.strainEntry N p i j) := by
  unfold strainEntryF JLeaf.strainEntry
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ite_true]
    have h := FI.mul_mem (cx_mem hp 0) (FI.add_mem (FI.add_mem (ptQ_mem (N 0 j))
      (FI.mul_mem (cx_mem hp 2) (ptQ_mem (N 1 j)))) (FI.mul_mem (cx_mem hp 3) (ptQ_mem (N 2 j))))
    exact h
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, ite_true]
    exact FI.mul_mem (cx_mem hp 1) (FI.add_mem (ptQ_mem (N 1 j)) (FI.mul_mem (cx_mem hp 4) (ptQ_mem (N 2 j))))
  · simp only [Fin.reduceFinMk, Fin.isValue, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      ite_false]
    have h := FI.mul_mem (ptQ_mem (N 2 j)) (cF_mem hp g)
    unfold cReal at h
    rw [div_eq_mul_inv]
    exact h

theorem sumF_mem' {ι : Type} (l : List ι) (F : ι → FI) (v : ι → ℝ) (h : ∀ x ∈ l, (F x).Mem (v x)) :
    (sumF (l.map F)).Mem ((l.map v).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, sumF, List.sum_nil, FI.Mem, Int.cast_zero, zero_div]
    exact ⟨le_rfl, le_rfl⟩
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, sumF]
    exact FI.add_mem (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem strainF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) (N U : Fin 3 → Fin 3 → ℚ) :
    (strainF b N U).Mem (JLeaf.strainCost N U p) := by
  have t (i j : Fin 3) : (strainTerm b N U i j).Mem ((JLeaf.strainEntry N p i j - (U i j : ℝ)) ^ 2) :=
    FI.sq_mem (FI.sub_mem (strainEntryF_mem hp g N i j) (ptQ_mem (U i j)))
  have h := sumF_mem' ([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)] :
      List (Fin 3 × Fin 3))
    (fun ij => strainTerm b N U ij.1 ij.2) (fun ij => (JLeaf.strainEntry N p ij.1 ij.2 - (U ij.1 ij.2 : ℝ)) ^ 2)
    (fun ij _ => t ij.1 ij.2)
  have e : JLeaf.strainCost N U p =
      (([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)] : List (Fin 3 × Fin 3)).map
        (fun ij => (JLeaf.strainEntry N p ij.1 ij.2 - (U ij.1 ij.2 : ℝ)) ^ 2)).sum := by
    unfold JLeaf.strainCost
    simp only [Fin.sum_univ_three, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  rw [e]
  exact h

/-- An enclosure of `|R d|² = r²(v₁ + x v₂)² + s² v₂² + c² δ²` on a seam cell. -/
def gramF (b : Cell) (an : Anchor) : FI :=
  ((FI.sq (FI.mul (cx b 0) ((v₁F b an).add (FI.mul (cx b 2) (v₂F b an))))).add
    (FI.sq (FI.mul (cx b 1) (v₂F b an)))).add (FI.sq (FI.mul (cF b) (deltaF b)))

theorem gramF_mem {b : Cell} {p : Chart} (hp : b.Mem p) (g : Guards b) (an : Anchor) :
    (gramF b an).Mem (layerGram p (an.k₁ / 2) (an.k₂ / 2)) := by
  have h := FI.add_mem (FI.add_mem
    (FI.sq_mem (FI.mul_mem (cx_mem hp 0) (FI.add_mem (v₁F_mem hp an) (FI.mul_mem (cx_mem hp 2) (v₂F_mem hp an)))))
    (FI.sq_mem (FI.mul_mem (cx_mem hp 1) (v₂F_mem hp an))))
    (FI.sq_mem (FI.mul_mem (cF_mem hp g) (deltaF_mem hp)))
  unfold gramF layerGram quad6
  convert h using 1
  ring

/-! ### The anchor coset separation -/

def sepOk (b : Cell) : Bool := decide ((FI.mulPos (cx b 0) (cx b 1)).hi < Sz)

theorem anchor_sep {p : Chart} (hr : 0 < p 0) (hs : 0 < p 1) (hrs : p 0 * p 1 < 1) (f₀ : Vec)
    (hf : f₀ 2 = -1 / 2) (m : IntVec) :
    (1 / 2 : ℝ) ^ 2 < sq ((chartBasis p).mulVec (castVec m + f₀)) := by
  have hrs0 : 0 < p 0 * p 1 := mul_pos hr hs
  set x := castVec m + f₀
  have hx2 : x 2 = (m 2 : ℝ) - 1 / 2 := by
    show (castVec m + f₀) 2 = _
    simp [castVec, hf]; ring
  have habs : (1 / 2 : ℝ) ≤ |x 2| := by
    rw [hx2]
    rcases le_or_gt (m 2) 0 with h | h
    · have : (m 2 : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ m 2 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  have h3 : ((chartBasis p).mulVec x) 2 = x 2 / (p 0 * p 1) := by
    simp [chartBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three, div_eq_mul_inv]
    ring
  have hsq : ((chartBasis p).mulVec x 2) ^ 2 ≤ sq ((chartBasis p).mulVec x) := by
    unfold sq
    rw [Fin.sum_univ_three]
    nlinarith [sq_nonneg ((chartBasis p).mulVec x 0), sq_nonneg ((chartBasis p).mulVec x 1)]
  rw [h3, div_pow] at hsq
  have hx2sq : (1 / 2 : ℝ) ^ 2 ≤ x 2 ^ 2 := by
    rw [← sq_abs (x 2)]; exact pow_le_pow_left₀ (by norm_num) habs 2
  have hden : (p 0 * p 1) ^ 2 < 1 := by nlinarith
  have hden0 : 0 < (p 0 * p 1) ^ 2 := by positivity
  have : (1 / 2 : ℝ) ^ 2 < x 2 ^ 2 / (p 0 * p 1) ^ 2 := by
    rw [lt_div_iff₀ hden0]; nlinarith
  linarith

/-! ### The seam chart and the anchor -/

def seamShiftW (n : IntVec) : IntVec := ![0, 0, 1 - n 2]

def anchorW (n : IntVec) : Anchor := ⟨2 * n 0 - 1, 2 * n 1 - 1, 3⟩

/-- The all-half anchor `(−1/2, −1/2, −1/2)`. -/
def halfAll : Vec := fun _ => -1 / 2

theorem halfAll_half : HalfClass halfAll := by
  refine ⟨⟨fun _ => -1, ?_⟩, ?_⟩
  · funext i
    simp only [halfAll, castVec, Pi.smul_apply, smul_eq_mul, Int.cast_neg, Int.cast_one]
    norm_num
  · intro n h
    have h0 := congrFun h 0
    simp only [halfAll, castVec] at h0
    have : (2 : ℝ) * (n 0 : ℝ) = -1 := by linarith
    have : (2 * n 0 : ℤ) = -1 := by exact_mod_cast this
    omega

theorem anchor_chart_wrap (p : Chart) (n : IntVec) :
    chartPoint (anchorChart (shiftChart p (seamShiftW n)) ((anchorW n).k₁ / 2) ((anchorW n).k₂ / 2)) =
      wrap (anchorOf (chartPoint p) halfAll) ![n 0, n 1, 1] := by
  have hB : chartBasis (anchorChart (shiftChart p (seamShiftW n)) ((anchorW n).k₁ / 2) ((anchorW n).k₂ / 2)) =
      chartBasis p := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  unfold chartPoint
  rw [hB]
  simp only [wrap, anchorOf]
  congr 1
  funext i
  fin_cases i <;> simp [anchorChart, anchorW, halfAll, castVec] <;> ring

theorem sq_chartBasis (p : Chart) (d : Vec) :
    sq ((chartBasis p).mulVec d) = (p 0 * (d 0 + p 2 * d 1 + p 3 * d 2)) ^ 2 +
      (p 1 * (d 1 + p 4 * d 2)) ^ 2 + (d 2 * (p 0 * p 1)⁻¹) ^ 2 := by
  simp [sq, chartBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem gram_eq (p : Chart) (n : IntVec) :
    layerGram (shiftChart p (seamShiftW n)) ((anchorW n).k₁ / 2) ((anchorW n).k₂ / 2) =
      sq ((chartPoint p).basis.mulVec ((chartPoint p).offset - halfAll - castVec n)) := by
  rw [show (chartPoint p).basis = chartBasis p from rfl, sq_chartBasis]
  unfold layerGram quad6
  rw [latV_zero, latV_one]
  have s0 : shiftChart p (seamShiftW n) 0 = p 0 := rfl
  have s1 : shiftChart p (seamShiftW n) 1 = p 1 := rfl
  have s2 : shiftChart p (seamShiftW n) 2 = p 2 := rfl
  have s3 : shiftChart p (seamShiftW n) 3 = p 3 := rfl
  have s4 : shiftChart p (seamShiftW n) 4 = p 4 := rfl
  have s5 : shiftChart p (seamShiftW n) 5 = p 5 := by simp [shiftChart, seamShiftW]
  have s6 : shiftChart p (seamShiftW n) 6 = p 6 := by simp [shiftChart, seamShiftW]
  have s7 : shiftChart p (seamShiftW n) 7 = p 7 + 1 - (n 2 : ℝ) := by
    simp [shiftChart, seamShiftW]; ring
  have hc : cReal (shiftChart p (seamShiftW n)) = (p 0 * p 1)⁻¹ := rfl
  have k1 : ((anchorW n).k₁ : ℝ) = 2 * (n 0 : ℝ) - 1 := by simp [anchorW]
  have k2 : ((anchorW n).k₂ : ℝ) = 2 * (n 1 : ℝ) - 1 := by simp [anchorW]
  have d0 : ((chartPoint p).offset - halfAll - castVec n) 0 = p 5 + 1 / 2 - (n 0 : ℝ) := by
    show (chartPoint p).offset 0 - halfAll 0 - castVec n 0 = _
    simp [chartPoint, halfAll, castVec]; ring
  have d1 : ((chartPoint p).offset - halfAll - castVec n) 1 = p 6 + 1 / 2 - (n 1 : ℝ) := by
    show (chartPoint p).offset 1 - halfAll 1 - castVec n 1 = _
    simp [chartPoint, halfAll, castVec]; ring
  have d2 : ((chartPoint p).offset - halfAll - castVec n) 2 = p 7 + 1 / 2 - (n 2 : ℝ) := by
    show (chartPoint p).offset 2 - halfAll 2 - castVec n 2 = _
    simp [chartPoint, halfAll, castVec]; ring
  rw [s0, s1, s2, s3, s4, s5, s6, s7, hc, k1, k2, d0, d1, d2]
  ring

theorem defect_wrap (q : TwoSite) (n : IntVec) : defect (wrap q n) = defect q := by
  unfold defect neighbors
  rw [points_wrap]

/-! ### The checker -/

/-- The proposal data of one PlanarAnchor relative request. -/
structure PlanarAnchorCert where
  depth : ℕ
  k : ℚ
  reg : JLeaf.RegData

def lamOf (k : ℚ) : ℚ := 2 * DirectRoute.scaleWitness.upper * (200 * Constants.gapBracket.hi + k)

def planarAnchorCertOk (c : PlanarAnchorCert) (box : Cell) (n : IntVec) : Bool :=
  let b := shiftCell box (seamShiftW n)
  let an := anchorW n
  (((decide (0 < c.k) && splitOk an (lamOf c.k) c.depth b) &&
    (JLeaf.registrationCheck c.reg.B c.reg.N c.reg.U c.reg.f0 &&
      decide (c.reg.w = ![(an.k₁ : ℚ) / 2, (an.k₂ : ℚ) / 2, 1 / 2]))) &&
    ((guardsOk b && sepOk b) &&
      decide (2 * (100 * (strainF b c.reg.N c.reg.U).hi + 200 * (gramF b an).hi) ≤ Sz)))

/-- The PlanarAnchor relative checker, from a table of certificates indexed by requests. -/
def planarAnchorCheck (table : Request → Option PlanarAnchorCert) : Checker := fun q =>
  match q.packet, q.proposal.payload with
  | .planarAnchor, .optical .layered .basin half _ =>
    match table q with
    | some c => planarAnchorCertOk c q.target.box half.wrap
    | none => false
  | _, _ => false

theorem scale_check : BravaisCover.cubeRootCheck DirectRoute.scaleWitness DirectRoute.scaleInput = true := by
  decide +kernel

/-- The route result of one accepted certificate. -/
theorem planarAnchorCertOk_sound (latticeCase : LatticeCase) (c : PlanarAnchorCert) (box : Cell) (n : IntVec)
    (ok : planarAnchorCertOk c box n = true) (p : Chart) (hp : box.Mem p) (gp : good p) :
    OpticalEvidence (chartPoint p) := by
  simp only [planarAnchorCertOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨hk, hsplit⟩, hreg, hw⟩, ⟨hg, hsep⟩, hcost⟩ := ok
  obtain ⟨b, hb⟩ : ∃ b, b = shiftCell box (seamShiftW n) := ⟨_, rfl⟩
  obtain ⟨an, han⟩ : ∃ an, an = anchorW n := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ q, q = shiftChart p (seamShiftW n) := ⟨_, rfl⟩
  rw [← hb] at hsplit hg hsep hcost
  rw [← han] at hsplit hcost hw
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
  have gain := splitOk_gain c.depth hsplit hp'
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
  have gapHi : gap ≤ (Constants.gapBracket.hi : ℝ) := gapB.1.2
  have bq0 : 0 ≤ bq := by rw [hbq]; exact sq_nonnegative _
  -- the anchor defect from the literal registration
  obtain ⟨pa, hpa⟩ : ∃ q, q = anchorChart p' (an.k₁ / 2) (an.k₂ / 2) := ⟨_, rfl⟩
  rw [← hpa] at hEa hDa hA
  have hstrain : JLeaf.strainCost c.reg.N c.reg.U pa = JLeaf.strainCost c.reg.N c.reg.U p' := by
    have h0 : pa 0 = p' 0 := by rw [hpa]; rfl
    have h1 : pa 1 = p' 1 := by rw [hpa]; rfl
    have h2 : pa 2 = p' 2 := by rw [hpa]; rfl
    have h3 : pa 3 = p' 3 := by rw [hpa]; rfl
    have h4 : pa 4 = p' 4 := by rw [hpa]; rfl
    unfold JLeaf.strainCost JLeaf.strainEntry
    rw [h0, h1, h2, h3, h4]
  have himg (i : Fin 3) : JLeaf.img (fun i => -c.reg.w i) true pa i = 0 := by
    rw [hw, hpa]
    fin_cases i <;> simp [JLeaf.img, anchorChart, DirectRoute.offset]
  have hprimal : JLeaf.primalQ (fun i => -c.reg.w i) true pa = 0 := by
    simp only [JLeaf.primalQ, JLeaf.rowA, JLeaf.rowB, JLeaf.rowC, himg]
    ring
  have hregCost : JLeaf.regCost c.reg.N c.reg.U c.reg.w pa = 100 * JLeaf.strainCost c.reg.N c.reg.U p' := by
    unfold JLeaf.regCost
    rw [hprimal, hstrain]
    ring
  have strainUp := (strainF_mem hp' g c.reg.N c.reg.U).2
  have gramUp := (gramF_mem hp' g an).2
  rw [hG] at gramUp
  have hcostR : 2 * (100 * ((strainF b c.reg.N c.reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) ≤ (Sz : ℝ) := by
    exact_mod_cast hcost
  have dUp : 100 * JLeaf.strainCost c.reg.N c.reg.U p' + 200 * bq ≤ 1 / 2 := by
    have q1 : 100 * JLeaf.strainCost c.reg.N c.reg.U p' + 200 * bq ≤
        (100 * ((strainF b c.reg.N c.reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) / Sz := by
      rw [add_div, mul_div_assoc, mul_div_assoc]
      linarith
    have q2 : (100 * ((strainF b c.reg.N c.reg.U).hi : ℝ) + 200 * ((gramF b an).hi : ℝ)) / Sz ≤ 1 / 2 := by
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
  have regSmall : JLeaf.regCost c.reg.N c.reg.U (fun i => c.reg.f0 i + (c.reg.wrap i : ℚ)) pa ≤ 1 / 2 := by
    show JLeaf.regCost c.reg.N c.reg.U c.reg.w pa ≤ 1 / 2
    rw [hregCost]; linarith
  have dAnchor := JLeaf.defect_le_regCost c.reg.B c.reg.N c.reg.U c.reg.f0 c.reg.wrap hreg pa paValid regSmall
  have dAnchor' : defect (anchorOf (chartPoint p) halfAll) ≤ 100 * JLeaf.strainCost c.reg.N c.reg.U p' := by
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
  -- combine
  have hk0 : (0 : ℝ) < c.k := by exact_mod_cast hk
  have hlam : (2 * ac) * (200 * gap + (c.k : ℝ)) ≤ (lamOf c.k : ℝ) := by
    unfold lamOf
    push_cast
    have h1 : 0 ≤ 200 * gap + (c.k : ℝ) := by positivity
    have h2 : 200 * gap + (c.k : ℝ) ≤ 200 * (Constants.gapBracket.hi : ℝ) + c.k := by linarith
    have h3 : (2 * ac) * (200 * gap + (c.k : ℝ)) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + c.k) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    have h4 : (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * gap + c.k) ≤
        (2 * (DirectRoute.scaleWitness.upper : ℝ)) * (200 * (Constants.gapBracket.hi : ℝ) + c.k) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have h2ac : 0 < 2 * ac := by positivity
  have gainE : (200 * gap + (c.k : ℝ)) * bq ≤
      energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll) := by
    have h1 := mul_le_mul_of_nonneg_right hlam bq0
    have e : (2 * ac) * ((200 * gap + (c.k : ℝ)) * bq) ≤
        2 * ac * (energy (chartPoint p) - energy (anchorOf (chartPoint p) halfAll)) := by
      linarith
    exact le_of_mul_le_mul_left e h2ac
  have deficitGain : deficit (anchorOf (chartPoint p) halfAll) + ((0 : ℚ) : ℝ) +
      ((c.k : ℚ) : ℝ) * bq ≤ deficit (chartPoint p) := by
    unfold deficit
    have h1 := mul_le_mul_of_nonneg_left trans gap0.le
    push_cast
    nlinarith
  have rel : relativeCheck 0 c.k = true := by
    unfold relativeCheck
    exact decide_eq_true ⟨le_rfl, hk⟩
  exact relativeOptical_route_of_lattice latticeCase p hvalid halfAll n halfAll_half 0 c.k rel (by
    rw [hbq] at deficitGain; exact deficitGain)

theorem planarAnchorCheck_sound (latticeCase : LatticeCase) (table : Request → Option PlanarAnchorCert) :
    CheckerSound (planarAnchorCheck table) := by
  intro q _ _ _ h p hp gp
  unfold planarAnchorCheck at h
  rcases q with ⟨packet, root, path, ⟨ancestor, payload⟩⟩
  cases packet <;> try (simp at h)
  cases payload with
  | optical method result half hint =>
    cases method with
    | transport s => simp at h
    | layered =>
      cases result <;> try (simp at h)
      cases hc : table ⟨.planarAnchor, root, path, ⟨ancestor, .optical .layered .basin half hint⟩⟩ with
      | none => rw [hc] at h; simp at h
      | some c =>
        rw [hc] at h
        have ev := planarAnchorCertOk_sound latticeCase c _ half.wrap h p hp gp
        show (Proposal.route (.optical .layered .basin half hint)).result p
        simp only [Proposal.route, Route.result]
        exact ev
  | _ => simp at h

end BccSharp.Coulomb.CompactCover.Layered
