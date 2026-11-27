import BccSharp.Cover.Stage2FixSound

set_option autoImplicit false

/-! Shared checked tangents for the Stage2 fixed-point routes.

The half-kernel tangents are about half the kernel time of a `bulkFix` row,
and the 243,457 bulk rows use only 237,841 distinct tangent keys
`(kernelKind, ticks)` for 10.6 million anchor uses.
A `CheckedTangent` carries the tangent of one key together with the kernel's
check that `tangentF` computes it; every row that uses the key refers to the
same `CheckedTangent`, so the tangent is evaluated once.

`bulkFixT` and `phaseFixT` are `bulkFix` and `phaseFix` with the tangents read
from the given `CheckedTangent`s (one per anchor row, matched by kind and
ticks) and with the distinctness of the mode keys checked as a strictly
increasing list (linear, in place of the quadratic `List.Nodup` decision).
Each acceptance implies the acceptance of the original (`bulkFixT_imp`,
`phaseFixT_imp`), so the soundness theorems are those of `bulkFix` and
`phaseFix`. -/

namespace BccSharp.Coulomb.CompactCover.Stage2Fix
open BccSharp BccSharp.Coverage DirectRoute OverlayPlanar.Fix DirectFix Stage2 BravaisCover

/-- `tangentF kind ticks = some ⟨intercept, penalty⟩`, as a Boolean test. -/
def tangentCheck (kind : KernelKind) (ticks : ℕ) (intercept penalty : ℤ) : Bool :=
  match tangentF kind ticks with
  | some t => t.intercept == intercept && t.penalty == penalty
  | none => false

theorem tangentCheck_eq {kind : KernelKind} {ticks : ℕ} {i p : ℤ} (h : tangentCheck kind ticks i p = true) :
    tangentF kind ticks = some ⟨i, p⟩ := by
  unfold tangentCheck at h
  cases ht : tangentF kind ticks with
  | none => rw [ht] at h; exact absurd h Bool.false_ne_true
  | some t =>
    rw [ht] at h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    cases t with
    | mk a c =>
      simp only [beq_iff_eq] at h1 h2
      subst h1; subst h2; rfl

/-- The tangent at the key `(kind, ticks)`, with the kernel's check. -/
structure CheckedTangent where
  kind : KernelKind
  ticks : ℕ
  intercept : ℤ
  penalty : ℤ
  ok : tangentCheck kind ticks intercept penalty = true

/-- `evalLineF` with the tangent read from `t`, which must carry the row's key. -/
def evalLineT (b : Cell) (r : AnchorRow) (t : CheckedTangent) : Option LineF :=
  if decide r.mode.valid = true ∧ t.kind = r.mode.kind ∧ t.ticks = r.ticks then
    some ⟨r.mode, multF b r.mode * t.intercept / Sz, cdivZ (multF b r.mode * t.penalty) Sz, floorF b r.mode⟩
  else none

theorem evalLineT_eq {b : Cell} {r : AnchorRow} {t : CheckedTangent} {l : LineF}
    (h : evalLineT b r t = some l) : evalLineF b r = some l := by
  unfold evalLineT at h
  split_ifs at h with c
  obtain ⟨v, hk, hticks⟩ := c
  have ht := tangentCheck_eq t.ok
  rw [hk, hticks] at ht
  rw [← h]
  simp only [evalLineF, v, ↓reduceIte, ht, Option.map_some]

def prepareT (b : Cell) : List AnchorRow → List CheckedTangent → Option (List LineF)
  | [], [] => some []
  | r :: rs, t :: ts =>
    match evalLineT b r t, prepareT b rs ts with
    | some l, some ls => some (l :: ls)
    | _, _ => none
  | _, _ => none

theorem prepareT_eq (b : Cell) :
    ∀ (rs : List AnchorRow) (ts : List CheckedTangent) (ys : List LineF),
      prepareT b rs ts = some ys → prepareF b rs = some ys
  | [], [], ys, h => by
    have e : prepareT b [] [] = some [] := rfl
    rw [e] at h
    rw [← h]; rfl
  | [], t :: ts, ys, h => by
    have e : prepareT b [] (t :: ts) = none := rfl
    rw [e] at h; exact absurd h (by simp)
  | r :: rs, [], ys, h => by
    have e : prepareT b (r :: rs) [] = none := rfl
    rw [e] at h; exact absurd h (by simp)
  | r :: rs, t :: ts, ys, h => by
    have e : prepareT b (r :: rs) (t :: ts) =
        (match evalLineT b r t, prepareT b rs ts with
          | some l, some ls => some (l :: ls)
          | _, _ => none) := rfl
    rw [e] at h
    cases e1 : evalLineT b r t with
    | none => rw [e1] at h; exact absurd h (by simp)
    | some l =>
      cases e2 : prepareT b rs ts with
      | none => rw [e1, e2] at h; exact absurd h (by simp)
      | some ls =>
        rw [e1, e2] at h
        rw [← h]
        simp only [prepareF, evalLineT_eq e1, prepareT_eq b rs ts ls e2]

/-- A strictly increasing list of integers. -/
def incrZ : List ℤ → Bool
  | a :: b :: l => decide (a < b) && incrZ (b :: l)
  | _ => true

theorem incrZ_pairwise : ∀ l : List ℤ, incrZ l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [incrZ, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := incrZ_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

theorem incrZ_nodup (l : List ℤ) (h : incrZ l = true) : l.Nodup :=
  (incrZ_pairwise l h).imp fun hab => ne_of_lt hab

/-- The plain tangent route with shared tangents. -/
def bulkFixT (b : Cell) (r : Proposal) (ts : List CheckedTangent) : Bool :=
  (sameCell b r.ownerBox && incrZ (r.selected.map modeKey)) &&
  (diagonalsCheck b &&
    match prepareT b r.selected ts with
    | none => false
    | some ys => foldZ b ys (sumL LineF.intercept ys - thrZ - 1))

theorem bulkFixT_imp {b : Cell} {r : Proposal} {ts : List CheckedTangent} (h : bulkFixT b r ts = true) :
    bulkFix b r = true := by
  unfold bulkFixT at h
  obtain ⟨data, work⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨same, keys⟩ := Bool.and_eq_true_iff.mp data
  obtain ⟨diag, compare⟩ := Bool.and_eq_true_iff.mp work
  cases e : prepareT b r.selected ts with
  | none => rw [e] at compare; exact absurd compare Bool.false_ne_true
  | some ys =>
    rw [e] at compare
    unfold bulkFix
    rw [prepareT_eq b _ _ ys e]
    simp only [same, decide_eq_true (incrZ_nodup _ keys), diag, compare, Bool.and_self]

theorem bulkFixT_sound (b : Cell) (r : Proposal) (ts : List CheckedTangent) (p : Chart) (hp : b.Mem p)
    (hv : (chartPoint p).Valid) (ok : bulkFixT b r ts = true) : energy fcc < energy (chartPoint p) :=
  bulkFix_sound b r p hp hv (bulkFixT_imp ok)

/-- The phase-budget route with shared tangents. -/
def phaseFixT (b : Cell) (r : Proposal) (budget : Array Allocation) (ts : List CheckedTangent) : Bool :=
  (sameCell b r.ownerBox && incrZ (r.selected.map modeKey)) &&
  (diagonalsCheck b &&
    match prepareT b r.selected ts with
    | none => false
    | some ys =>
      match checkedBudgetF b (ys.map LineF.toLine) budget with
      | none => false
      | some gain => foldZ b ys (sumL LineF.intercept ys - thrZ - 1 + ⌊gain * S⌋))

theorem phaseFixT_imp {b : Cell} {r : Proposal} {budget : Array Allocation} {ts : List CheckedTangent}
    (h : phaseFixT b r budget ts = true) : phaseFix b r budget = true := by
  unfold phaseFixT at h
  obtain ⟨data, work⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨same, keys⟩ := Bool.and_eq_true_iff.mp data
  obtain ⟨diag, compare⟩ := Bool.and_eq_true_iff.mp work
  cases e : prepareT b r.selected ts with
  | none => rw [e] at compare; exact absurd compare Bool.false_ne_true
  | some ys =>
    rw [e] at compare
    dsimp only at compare
    unfold phaseFix
    rw [prepareT_eq b _ _ ys e]
    cases cap : checkedBudgetF b (ys.map LineF.toLine) budget with
    | none => rw [cap] at compare; exact absurd compare Bool.false_ne_true
    | some gain =>
      rw [cap] at compare
      dsimp only at compare
      simp only [same, decide_eq_true (incrZ_nodup _ keys), diag, cap, compare, Bool.and_self]

theorem phaseFixT_sound (b : Cell) (r : Proposal) (budget : Array Allocation) (ts : List CheckedTangent)
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) (ok : phaseFixT b r budget ts = true) :
    energy fcc < energy (chartPoint p) :=
  phaseFix_sound b r budget p hp hv (phaseFixT_imp ok)

end BccSharp.Coulomb.CompactCover.Stage2Fix
