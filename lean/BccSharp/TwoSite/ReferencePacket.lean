import BccSharp.TwoSite.ReferenceTails

set_option autoImplicit false

/-! Constants rational packet for the first BCC and FCC splittings.
Every input to the finite arithmetic is computed from the stated exact
rationals. The acceptance comparisons use the literal published endpoints. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.Constants
open BccSharp
open BccSharp.Intervals (Ball)
open HighPrecision

def grid : ℚ := 2^248

def round (b : Ball) : Ball :=
  let m : ℚ := (⌊b.mid*grid + 1/2⌋ : ℤ) / grid
  ⟨m, (⌈(|m-b.mid|+b.rad)*grid⌉ : ℤ) / grid⟩

theorem round_sound {b : Ball} {x : ℝ} (h : b.Contains x) : (round b).Contains x := by
  apply Ball.covers_sound _ h
  unfold Ball.Covers round
  dsimp only
  rw [abs_sub_comm b.mid]
  exact (le_div_iff₀ (by norm_num [grid])).2 (Int.le_ceil _)

def bisect (power : ℕ) (x : ℚ) : ℕ → (ℚ × ℚ) → (ℚ × ℚ)
  | 0, b => b
  | n+1, (lo, hi) =>
      let m := (lo+hi)/2
      bisect power x n (if m^power ≤ x then (m, hi) else (lo, m))

def rootPair (power : ℕ) (xlo xhi hi : ℚ) : RootProposal :=
  ⟨(bisect power xlo 252 (0, hi)).1, (bisect power xhi 252 (0, hi)).2⟩

def piInput : Ball := round referencePi
theorem piInput_sound : piInput.Contains Real.pi := round_sound referencePi_sound

def piRoot : RootProposal := rootPair 2 (piInput.mid - piInput.rad) (piInput.mid + piInput.rad) 2
def piInverseRoot : Ball := round piRoot.ball.inv

theorem piInverseRoot_sound (ok : piRoot.check piInput = true) :
    piInverseRoot.Contains (Real.sqrt Real.pi)⁻¹ :=
  round_sound (piRoot.inverse_sound piInput Real.pi Real.pi_pos.le piInput_sound ok)

def expSquares : ℕ → Ball → List Ball
  | 0, _ => []
  | n+1, a => let b := round (a.mul a); b :: expSquares n b

def expPoint (x : ℚ) : ExpBounds.PointWitness :=
  let t := x/256
  let s := round ⟨SpecialFunctions.taylor t 84, SpecialFunctions.taylorError t 84⟩
  ⟨84, s, expSquares 8 s⟩

def expProposal (a : Ball) : ExpBounds.Witness :=
  let l := expPoint (a.mid-a.rad)
  let u := expPoint (a.mid+a.rad)
  let lo := l.bound.mid - l.bound.rad
  let hi := u.bound.mid + u.bound.rad
  ⟨l, u, round ⟨(lo+hi)/2, (hi-lo)/2⟩⟩

def erfcProposal (q : ℚ) (p : Ball) : ErfcSeriesProposal :=
  let s := rootPair 2 q q 16
  let n := 768
  ⟨s, n, 4 * (s.ball.mid+s.ball.rad) * (p.mid+p.rad) * q^n / (n.factorial : ℚ)⟩

/-- Exact evaluation of `Erfc.series` by the term recurrence
`t_{k+1} = t_k (-q)/(k+1)`, `t_k = (-q)^k/k!`. Each step costs a few rational
operations, instead of recomputing `k!` and `(-q)^k` for every term. -/
def seriesLoop (q : ℚ) : ℕ → ℚ → ℚ → ℚ → ℚ
  | 0, _, _, acc => acc
  | fuel + 1, kq, t, acc => seriesLoop q fuel (kq + 1) (t * (-q) / (kq + 1)) (acc + t / (2 * kq + 1))

theorem seriesLoop_eq (q : ℚ) (fuel k : ℕ) (acc : ℚ) :
    seriesLoop q fuel (k : ℚ) ((-q) ^ k / (k.factorial : ℚ)) acc =
      acc + ∑ j ∈ Finset.Ico k (k + fuel), (-q) ^ j / ((j.factorial : ℚ) * (2 * j + 1 : ℕ)) := by
  induction fuel generalizing k acc with
  | zero => simp [seriesLoop]
  | succ n ih =>
    have hstep : (-q) ^ k / (k.factorial : ℚ) * (-q) / ((k : ℚ) + 1) =
        (-q) ^ (k + 1) / ((k + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
      have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      field_simp
    have hcast : ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
    have hterm : (-q) ^ k / (k.factorial : ℚ) / (2 * (k : ℚ) + 1) =
        (-q) ^ k / ((k.factorial : ℚ) * (2 * k + 1 : ℕ)) := by
      push_cast
      rw [div_div]
    simp only [seriesLoop]
    rw [hstep, hcast, ih, hterm, Finset.sum_eq_sum_Ico_succ_bot (by omega : k < k + (n + 1)),
      show k + 1 + n = k + (n + 1) by omega]
    ring

/-- Same value as `Erfc.series q n`; used for kernel evaluation. -/
def seriesFast (q : ℚ) (n : ℕ) : ℚ := seriesLoop q n 0 1 0

theorem seriesFast_eq (q : ℚ) (n : ℕ) : seriesFast q n = Erfc.series q n := by
  have h := seriesLoop_eq q n 0 0
  simp only [Nat.cast_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add] at h
  rw [seriesFast, h, Erfc.series, Finset.range_eq_Ico]

/-- `ErfcSeriesProposal.result` evaluated with `seriesFast`. -/
def fastResult (w : ErfcSeriesProposal) (q : ℚ) (p : Ball) : Ball :=
  let b := (Ball.exact 1).sub ((((Ball.exact 2).mul w.root.ball).mul p).mul
    (Ball.exact (seriesFast q w.order)))
  ⟨b.mid,b.rad+w.error⟩

theorem fastResult_eq (w : ErfcSeriesProposal) (q : ℚ) (p : Ball) :
    fastResult w q p = w.result q p := by
  simp only [fastResult, ErfcSeriesProposal.result, seriesFast_eq]

def directCheck (ref : Reference) (r : ℚ) : Bool :=
  let q := DirectShell.argument ref r
  (erfcProposal q piInverseRoot).check q piInverseRoot

def directBall (ref : Reference) (r : ℚ) : Ball :=
  let q := DirectShell.argument ref r
  let w := erfcProposal q piInverseRoot
  round ((Ball.exact (ref.alpha/2)).mul ((fastResult w q piInverseRoot).mul w.root.ball.inv))

theorem directBall_sound (ref : Reference) (r : ℚ) (pCheck : piRoot.check piInput = true)
    (check : directCheck ref r = true) : (directBall ref r).Contains (ref.directValue r) := by
  let q := DirectShell.argument ref r
  let w := erfcProposal q piInverseRoot
  have hCheck : w.check q piInverseRoot = true := check
  have he := ErfcSeriesProposal.sound w q piInverseRoot (piInverseRoot_sound pCheck) hCheck
  have hnon : 0 ≤ q := (of_decide_eq_true (Bool.and_eq_true_iff.mp hCheck).2 :
    0 ≤ q ∧ q / (w.order + 1 : ℕ) ≤ 1/2 ∧
      4 * (w.root.ball.mid+w.root.ball.rad) * (piInverseRoot.mid+piInverseRoot.rad) * q^w.order /
        (w.order.factorial : ℚ) ≤ w.error).1
  have hi := RootProposal.inverse_sound w.root (Ball.exact q) (q : ℝ)
      (Rat.cast_nonneg.mpr hnon) (Ball.contains_exact q) (Bool.and_eq_true_iff.mp hCheck).1
  have raw := Ball.contains_mul (Ball.contains_exact (ref.alpha/2)) (Ball.contains_mul he hi)
  have hα : 0 < (ref.alpha : ℝ) := by cases ref <;> norm_num [Reference.alpha]
  have eq : Real.sqrt (q : ℝ) = (ref.alpha : ℝ)*Real.sqrt (r : ℝ) := by
    unfold q DirectShell.argument
    push_cast
    rw [Real.sqrt_mul (sq_nonneg (ref.alpha : ℝ)), Real.sqrt_sq hα.le]
  rw [eq, ← erfc_agrees] at raw
  apply round_sound
  rw [fastResult_eq]
  convert raw using 1
  unfold Reference.directValue
  push_cast
  by_cases hz : Real.sqrt (r : ℝ) = 0
  · simp [hz]
  · field_simp [hα.ne', hz] <;> ring

def reciprocalCheck (ref : Reference) (r : ℚ) : Bool :=
  (expProposal (ReciprocalShell.argument ref r piInput)).check (ReciprocalShell.argument ref r piInput) &&
    decide (ReciprocalShell.denominator ref r piInput).invertible

def reciprocalBall (ref : Reference) (r : ℚ) : Ball :=
  round (ReciprocalShell.bound ref r piInput (expProposal (ReciprocalShell.argument ref r piInput)))

theorem reciprocalBall_sound (ref : Reference) (r : ℚ) (check : reciprocalCheck ref r = true) :
    (reciprocalBall ref r).Contains (ref.reciprocalValue r) :=
  round_sound (ReciprocalShell.sound ref r piInput _ piInput_sound check)

def sumBalls {ι : Type} (s : Finset ι) (B : ι → Ball) : Ball :=
  ⟨∑ i ∈ s, (B i).mid, ∑ i ∈ s, (B i).rad⟩

theorem sumBalls_sound {ι : Type} (s : Finset ι) (B : ι → Ball) (value : ι → ℝ)
    (h : ∀ i ∈ s, (B i).Contains (value i)) : (sumBalls s B).Contains (∑ i ∈ s, value i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [sumBalls, Finset.sum_empty]
      exact_mod_cast Ball.contains_exact 0
  | @insert i s hi ih =>
      have h₁ := h i (Finset.mem_insert_self _ _)
      have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa [sumBalls, Ball.add, Finset.sum_insert hi] using Ball.contains_add h₁ h₂

/-! ### Integer shell enumeration

The kernel enumerates the lattice points with integer arithmetic on explicit
coordinate lists and groups them by an integer shell key. The lemmas below
identify these lists with the `Finset` sums in `Reference.finiteEnergy`. -/

/-- Four times the direct form, as an integer. -/
def directKey (ref : Reference) (z : Triple) : ℤ :=
  match ref with
  | .bcc => 4 * (z.1 * z.1 + z.2.1 * z.2.1 + z.2.2 * z.2.2) -
      (z.1 + z.2.1 + z.2.2) * (z.1 + z.2.1 + z.2.2)
  | .fcc => (z.1 * z.1 + z.2.1 * z.2.1 + z.2.2 * z.2.2) +
      (z.1 + z.2.1 + z.2.2) * (z.1 + z.2.1 + z.2.2)

/-- The dual form, as an integer. -/
def dualKey (ref : Reference) (z : Triple) : ℤ :=
  match ref with
  | .bcc => (z.1 * z.1 + z.2.1 * z.2.1 + z.2.2 * z.2.2) +
      (z.1 + z.2.1 + z.2.2) * (z.1 + z.2.1 + z.2.2)
  | .fcc => 4 * (z.1 * z.1 + z.2.1 * z.2.1 + z.2.2 * z.2.2) -
      (z.1 + z.2.1 + z.2.2) * (z.1 + z.2.1 + z.2.2)

theorem realRadius_key (ref : Reference) (z : Triple) :
    ref.realRadius z = (directKey ref z : ℚ) / 4 := by
  rcases z with ⟨a, b, c⟩
  cases ref <;>
    simp [Reference.realRadius, Reference.directForm, directKey, qSquare, qSum, asVector,
      Fin.sum_univ_three] <;> ring

theorem dualRadius_key (ref : Reference) (z : Triple) :
    ref.dualRadius z = (dualKey ref z : ℚ) := by
  rcases z with ⟨a, b, c⟩
  cases ref <;>
    simp [Reference.dualRadius, Reference.dualForm, dualKey, qSquare, qSum, asVector,
      Fin.sum_univ_three] <;> ring

def directKeyCut (ref : Reference) : ℤ := ⌊4 * ref.realCut⌋
def dualKeyCut (ref : Reference) : ℤ := ⌊ref.reciprocalCut⌋

theorem realRadius_le_cut (ref : Reference) (z : Triple) :
    ref.realRadius z ≤ ref.realCut ↔ directKey ref z ≤ directKeyCut ref := by
  rw [realRadius_key, directKeyCut, Int.le_floor, div_le_iff₀ (by norm_num : (0 : ℚ) < 4)]
  constructor <;> intro h <;> linarith

theorem dualRadius_le_cut (ref : Reference) (z : Triple) :
    ref.dualRadius z ≤ ref.reciprocalCut ↔ dualKey ref z ≤ dualKeyCut ref := by
  rw [dualRadius_key, dualKeyCut, Int.le_floor]

/-- The integers `-R, …, R`. -/
def rangeZ (R : ℕ) : List ℤ := (List.range (2 * R + 1)).map (fun i : ℕ => (i : ℤ) - R)

theorem mem_rangeZ (R : ℕ) (a : ℤ) : a ∈ rangeZ R ↔ -(R : ℤ) ≤ a ∧ a ≤ R := by
  simp only [rangeZ, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨(a + R).toNat, by omega, by omega⟩

theorem rangeZ_nodup (R : ℕ) : (rangeZ R).Nodup := by
  refine List.Nodup.map (fun i j h => ?_) List.nodup_range
  have h' : (i : ℤ) - R = (j : ℤ) - R := h
  omega

def cubeList (R : ℕ) : List Triple := rangeZ R ×ˢ (rangeZ R ×ˢ rangeZ R)

theorem cubeList_nodup (R : ℕ) : (cubeList R).Nodup :=
  (rangeZ_nodup R).product ((rangeZ_nodup R).product (rangeZ_nodup R))

theorem mem_cubeList (R : ℕ) (z : Triple) : z ∈ cubeList R ↔ z ∈ cube (R : ℤ) := by
  rcases z with ⟨a, b, c⟩
  simp only [cubeList, cube, List.mem_product, Finset.mem_product, mem_rangeZ, Finset.mem_Icc]

def directList (ref : Reference) : List Triple :=
  (cubeList 10).filter (fun z => decide (z ≠ 0) && decide (directKey ref z ≤ directKeyCut ref))

def dualList (ref : Reference) : List Triple :=
  (cubeList 7).filter (fun z => decide (z ≠ 0) && decide (dualKey ref z ≤ dualKeyCut ref))

theorem directPoints_eq (ref : Reference) : ref.directPoints = (directList ref).toFinset := by
  ext z
  have hc := mem_cubeList 10 z
  simp only [Nat.cast_ofNat] at hc
  simp only [Reference.directPoints, Finset.mem_filter, List.mem_toFinset, directList,
    List.mem_filter, hc, Bool.and_eq_true, decide_eq_true_eq]
  have hr := realRadius_le_cut ref z
  simp only [Reference.realRadius] at hr
  rw [hr]

theorem reciprocalPoints_eq (ref : Reference) : ref.reciprocalPoints = (dualList ref).toFinset := by
  ext z
  have hc := mem_cubeList 7 z
  simp only [Nat.cast_ofNat] at hc
  simp only [Reference.reciprocalPoints, Finset.mem_filter, List.mem_toFinset, dualList,
    List.mem_filter, hc, Bool.and_eq_true, decide_eq_true_eq]
  have hr := dualRadius_le_cut ref z
  simp only [Reference.dualRadius] at hr
  rw [hr]

theorem sum_directPoints (ref : Reference) (g : Triple → ℝ) :
    ∑ z ∈ ref.directPoints, g z = ((directList ref).map g).sum := by
  rw [directPoints_eq, List.sum_toFinset _ (show (directList ref).Nodup from (cubeList_nodup 10).filter _)]

theorem sum_reciprocalPoints (ref : Reference) (g : Triple → ℝ) :
    ∑ z ∈ ref.reciprocalPoints, g z = ((dualList ref).map g).sum := by
  rw [reciprocalPoints_eq, List.sum_toFinset _ (show (dualList ref).Nodup from (cubeList_nodup 7).filter _)]

/-- Insert one occurrence of `k` into an association list of key counts. -/
def bump (k : ℤ) : List (ℤ × ℕ) → List (ℤ × ℕ)
  | [] => [(k, 1)]
  | e :: rest => if e.1 = k then (e.1, e.2 + 1) :: rest else e :: bump k rest

def histogram (key : Triple → ℤ) : List Triple → List (ℤ × ℕ)
  | [] => []
  | z :: rest => bump (key z) (histogram key rest)

theorem bump_sum (f : ℤ → ℝ) (k : ℤ) (acc : List (ℤ × ℕ)) :
    ((bump k acc).map (fun e => (e.2 : ℝ) * f e.1)).sum =
      f k + (acc.map (fun e => (e.2 : ℝ) * f e.1)).sum := by
  induction acc with
  | nil => simp [bump]
  | cons e rest ih =>
    by_cases h : e.1 = k
    · simp only [bump, h, if_true, List.map_cons, List.sum_cons]
      push_cast
      ring
    · simp only [bump, h, if_false, List.map_cons, List.sum_cons, ih]
      ring

theorem histogram_sum (f : ℤ → ℝ) (key : Triple → ℤ) (L : List Triple) :
    ((histogram key L).map (fun e => (e.2 : ℝ) * f e.1)).sum = (L.map (fun z => f (key z))).sum := by
  induction L with
  | nil => simp [histogram]
  | cons z rest ih => simp only [histogram, bump_sum, ih, List.map_cons, List.sum_cons]

def directShells (ref : Reference) : List (ℤ × ℕ) := histogram (directKey ref) (directList ref)
def reciprocalShells (ref : Reference) : List (ℤ × ℕ) := histogram (dualKey ref) (dualList ref)

def sumList (H : List (ℤ × ℕ)) (B : ℤ × ℕ → Ball) : Ball :=
  ⟨(H.map (fun e => (B e).mid)).sum, (H.map (fun e => (B e).rad)).sum⟩

theorem sumList_sound (H : List (ℤ × ℕ)) (B : ℤ × ℕ → Ball) (v : ℤ × ℕ → ℝ)
    (h : ∀ e ∈ H, (B e).Contains (v e)) : (sumList H B).Contains ((H.map v).sum) := by
  induction H with
  | nil =>
      simp only [sumList, List.map_nil, List.sum_nil]
      exact_mod_cast Ball.contains_exact 0
  | cons e rest ih =>
      have h₁ := h e (by simp)
      have h₂ := ih (fun e' he' => h e' (List.mem_cons_of_mem e he'))
      simpa [sumList, Ball.add] using Ball.contains_add h₁ h₂

def directSumBall (ref : Reference) : Ball := sumList (directShells ref) fun e =>
  (Ball.exact (e.2 : ℚ)).mul (directBall ref ((e.1 : ℚ) / 4))
def reciprocalSumBall (ref : Reference) : Ball := sumList (reciprocalShells ref) fun e =>
  (Ball.exact (e.2 : ℚ)).mul (reciprocalBall ref (e.1 : ℚ))

theorem directSum_sound (ref : Reference) (pCheck : piRoot.check piInput = true)
    (h : ∀ e ∈ directShells ref, directCheck ref ((e.1 : ℚ) / 4) = true) :
    (directSumBall ref).Contains (∑ z ∈ ref.directPoints, ref.directValue (ref.realRadius z)) := by
  have hs : ∑ z ∈ ref.directPoints, ref.directValue (ref.realRadius z) =
      ((directShells ref).map (fun e => (e.2 : ℝ) * ref.directValue ((e.1 : ℚ) / 4))).sum := by
    rw [sum_directPoints]
    simp only [realRadius_key]
    rw [directShells, histogram_sum (fun k => ref.directValue ((k : ℚ) / 4))]
  rw [hs]
  apply sumList_sound
  intro e he
  simpa only [Rat.cast_natCast] using Ball.contains_mul (Ball.contains_exact (e.2 : ℚ))
    (directBall_sound ref _ pCheck (h e he))

theorem reciprocalSum_sound (ref : Reference)
    (h : ∀ e ∈ reciprocalShells ref, reciprocalCheck ref (e.1 : ℚ) = true) :
    (reciprocalSumBall ref).Contains (∑ z ∈ ref.reciprocalPoints, ref.reciprocalValue (ref.dualRadius z)) := by
  have hs : ∑ z ∈ ref.reciprocalPoints, ref.reciprocalValue (ref.dualRadius z) =
      ((reciprocalShells ref).map (fun e => (e.2 : ℝ) * ref.reciprocalValue (e.1 : ℚ))).sum := by
    rw [sum_reciprocalPoints]
    simp only [dualRadius_key]
    rw [reciprocalShells, histogram_sum (fun k => ref.reciprocalValue (k : ℚ))]
  rw [hs]
  apply sumList_sound
  intro e he
  simpa only [Rat.cast_natCast] using Ball.contains_mul (Ball.contains_exact (e.2 : ℚ))
    (reciprocalBall_sound ref _ (h e he))

def cubeInput (ref : Reference) : Ball :=
  round ((Ball.exact (3*ref.naturalVolume/4)).mul piInput.inv)

def cubeRoot (ref : Reference) : RootProposal :=
  let b := cubeInput ref
  rootPair 3 (b.mid-b.rad) (b.mid+b.rad) 1

def cubeCheck (ref : Reference) : Bool :=
  let w := cubeRoot ref
  let b := cubeInput ref
  decide (piInput.invertible ∧ 0 ≤ w.lower ∧ 0 ≤ w.upper ∧
    w.lower^3 ≤ b.mid-b.rad ∧ b.mid+b.rad ≤ w.upper^3)

private theorem cube_le_reflect {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^3 ≤ y^3) : x ≤ y := by
  by_contra! hn
  have hxp : 0 < x := hy.trans_lt hn
  have hprod := mul_pos (sub_pos.mpr hn)
    (show 0 < x^2 + x*y + y^2 by positivity)
  nlinarith

theorem cubeRoot_sound (ref : Reference) (ok : cubeCheck ref = true) :
    (cubeRoot ref).ball.Contains ref.wsFactor := by
  let b := cubeInput ref
  let w := cubeRoot ref
  have h : piInput.invertible ∧ 0 ≤ w.lower ∧ 0 ≤ w.upper ∧ w.lower^3 ≤ b.mid-b.rad ∧
      b.mid+b.rad ≤ w.upper^3 := of_decide_eq_true ok
  have hb : b.Contains (3*(ref.naturalVolume : ℝ)/(4*Real.pi)) := by
    have raw := round_sound (Ball.contains_mul (Ball.contains_exact (3*ref.naturalVolume/4))
      (Ball.contains_inv h.1 piInput_sound))
    convert raw using 1
    · rfl
    · push_cast
      ring
  have hl : (w.lower : ℝ)^3 ≤ (b.mid : ℝ)-b.rad := by exact_mod_cast h.2.2.2.1
  have hu : (b.mid : ℝ)+b.rad ≤ (w.upper : ℝ)^3 := by exact_mod_cast h.2.2.2.2
  have base := (SpecialFunctions.contains_iff_endpoints b _).mp hb
  have hlo : (w.lower : ℝ) ≤ ref.wsFactor := cube_le_reflect (by exact_mod_cast h.2.1)
    (wsFactor_nonneg_le_one ref).1 (by rw [wsFactor_cube]; exact hl.trans base.1)
  have hup : ref.wsFactor ≤ (w.upper : ℝ) := cube_le_reflect (wsFactor_nonneg_le_one ref).1
    (by exact_mod_cast h.2.2.1) (by rw [wsFactor_cube]; exact base.2.trans hu)
  exact SpecialFunctions.contains_of_endpoints hlo hup

def selfBall (ref : Reference) : Ball := (Ball.exact (-ref.alpha)).mul piInverseRoot
def backgroundBall (ref : Reference) : Ball :=
  (Ball.exact (-1/(2*ref.naturalVolume*ref.alpha^2))).mul piInput

def finiteBall (ref : Reference) : Ball :=
  let s := (directSumBall ref).add (reciprocalSumBall ref)
  let u := (s.add (selfBall ref)).add (backgroundBall ref)
  round ((cubeRoot ref).ball.mul u)

theorem finiteBall_sound (ref : Reference) (pc : piRoot.check piInput = true) (cc : cubeCheck ref = true)
    (hr : ∀ e ∈ directShells ref, directCheck ref ((e.1 : ℚ) / 4) = true)
    (hd : ∀ e ∈ reciprocalShells ref, reciprocalCheck ref (e.1 : ℚ) = true) :
    (finiteBall ref).Contains ref.finiteEnergy := by
  have hself := Ball.contains_mul (Ball.contains_exact (-ref.alpha)) (piInverseRoot_sound pc)
  have hbg := Ball.contains_mul (Ball.contains_exact (-1/(2*ref.naturalVolume*ref.alpha^2))) piInput_sound
  have hsum := Ball.contains_add (Ball.contains_add (Ball.contains_add (directSum_sound ref pc hr)
    (reciprocalSum_sound ref hd)) hself) hbg
  have raw := round_sound (Ball.contains_mul (cubeRoot_sound ref cc) hsum)
  convert raw using 1
  · rfl
  · unfold Reference.finiteEnergy Reference.realRadius Reference.dualRadius
    push_cast
    ring

def finiteBounds (ref : Reference) : Interval :=
  let b := finiteBall ref
  ⟨b.mid-b.rad, b.mid+b.rad⟩
def finalBounds (ref : Reference) : Interval := (finiteBounds ref).add ⟨0, exactTailUpper⟩

/-- Diagnostic shell counts from the published packet (point counts and
numbers of distinct shells). Not used by the soundness proof. -/
def expectedShellCounts (ref : Reference) : ℕ × ℕ :=
  match ref with | .bcc => (64, 26) | .fcc => (56, 30)

def constantsCheck (ref : Reference) : Bool := piRoot.check piInput && cubeCheck ref
def sumsCheck (ref : Reference) : Bool :=
  (directShells ref).all (fun e => directCheck ref ((e.1 : ℚ) / 4)) &&
  (reciprocalShells ref).all (fun e => reciprocalCheck ref (e.1 : ℚ))
def inclusionCheck (ref : Reference) : Bool := (finalBounds ref).inside ref.bracket

theorem checked_primitive_bounds (ref : Reference) (hc : constantsCheck ref = true)
    (hs : sumsCheck ref = true) (hi : inclusionCheck ref = true) : ref.bracket.contains ref.primitiveWS := by
  have cc := Bool.and_eq_true_iff.mp hc
  have sc := Bool.and_eq_true_iff.mp hs
  have finite := (SpecialFunctions.contains_iff_endpoints _ _).mp
    (finiteBall_sound ref cc.1 cc.2 (List.all_eq_true.mp sc.1) (List.all_eq_true.mp sc.2))
  have hf : (finiteBounds ref).contains ref.finiteEnergy := by
    simpa [finiteBounds, Interval.contains, Rat.cast_add, Rat.cast_sub] using finite
  have hb := Interval.add_sound hf (finite_and_tail ref)
  rw [show ref.finiteEnergy + (ref.primitiveWS - ref.finiteEnergy) = ref.primitiveWS by ring] at hb
  exact Interval.inside_sound hi hb

end BccSharp.Coulomb.Constants
