import BccSharp.Cover.Round7Leaves

set_option autoImplicit false

/-! The Continuation round-seven fixture, end to end.

`Round7Geometry.round7_covers` reduces a statement on both round-seven
root boxes to one certified statement per receipt row, on the exact box derived
from the row's tree path. `BccSharp.Cover.Round7Leaves` proves the strict J
comparison on each of the five derived boxes through `jleaf_sound`; here the
two are joined. The root boxes are derived from the round-six parent along the
receipt's held paths (`rb0`, `rb1`), and `roots_match` identifies them with the
boxes of the reconstructed round-seven manifest.

The leaf theorems are stated for *valid* chart points (determinant one and a
non-integral offset). Every point of both roots is valid (`round7_roots_valid`),
so `round7_fixture_all` holds at every point of both root boxes with no premise.

No point of either root is reduced (`round7_roots_not_reduced`). A statement restricted to `good` points is therefore vacuous
here, and these leaves certify nothing through `Route.result`. In the full
cover these boxes would be closed by a reduction exclusion. The J leaves
certify the strict deficit for the represented configurations regardless.

The receipt rows carry the registration of each J leaf (wrap, quaternion and
mixing weight). `rows_bind` checks three things:

* every row holds its root's rotation record;
* the rotations used by the Lean leaf checks are exactly the rotations of
  those integer quaternions;
* the wraps and the weight are the receipt's.

Both records carry selector 0, and no leaf check uses it.

The energy supports were re-proposed at the Series screening, so the recorded
corner mixtures and margins are not reused. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.JLeaf.Round7
open BccSharp.Coulomb
open BccSharp.Coulomb.CompactCover

/-- Rotation of an integer quaternion `(x, y, z, w)`. -/
def quatMatrix (q : List Int) : Fin 3 → Fin 3 → ℚ :=
  match q with
  | [x, y, z, w] =>
      let a : ℚ := x
      let b : ℚ := y
      let c : ℚ := z
      let d : ℚ := w
      let n : ℚ := a * a + b * b + c * c + d * d
      fun i j => (![![n - 2 * (b * b + c * c), 2 * (a * b - c * d), 2 * (a * c + b * d)],
        ![2 * (a * b + c * d), n - 2 * (a * a + c * c), 2 * (b * c - a * d)],
        ![2 * (a * c - b * d), 2 * (b * c + a * d), n - 2 * (a * a + b * b)]] i j) / n
  | _ => fun _ _ => 0

/-- The receipt rows' registrations are the ones used by the leaf checks.

* Every row of each root holds that root's rotation record.
* The row's integer quaternion gives exactly the rotation `U` of each leaf
  check.
* The row's wrap is each leaf's wrap. The field `halfClass` holds the
  wrap, and `quaternionScale` holds the mixing weight 4096.

`selector` is the index of the catalogue entry of `(B, f₀)`. Both records carry 0, and no leaf check uses it. Lean does not
identify the literal `(B, N, U, f₀)` with that entry.

The leaf check runs `registrationCheck`, which verifies the conditions that
`defect_le_regCost` uses (see `BccSharp.Cover.JLeafDefect`):

* `N B = B N = 1`;
* `U` is a proper rotation;
* `2B` and `2 B f₀` are integral with BCC parity;
* `f₀ ∉ ℤ³`;
* the star labels.

It does not check `det B = 1` and does not link the literal to the interface's
`IndexTwoBCC`. Soundness needs neither. -/
theorem rows_bind :
    (∀ row ∈ Round7Geometry.rows0, row.rotation = Round7Geometry.rotation0) ∧
    (∀ row ∈ Round7Geometry.rows1, row.rotation = Round7Geometry.rotation1) ∧
    (∀ i j : Fin 3, quatMatrix Round7Geometry.rotation0.quaternionNumerator i j = reg0_0.U i j ∧
      reg0_0.U i j = reg0_1.U i j ∧ reg0_1.U i j = reg0_2.U i j) ∧
    (∀ i j : Fin 3, quatMatrix Round7Geometry.rotation1.quaternionNumerator i j = reg1_0.U i j ∧
      reg1_0.U i j = reg1_1.U i j) ∧
    (∀ i : Fin 3, (Round7Geometry.rotation0.halfClass.getD i.val 0 : ℤ) = reg0_0.wrap i ∧
      reg0_0.wrap i = reg0_1.wrap i ∧ reg0_1.wrap i = reg0_2.wrap i ∧
      (Round7Geometry.rotation1.halfClass.getD i.val 0 : ℤ) = reg1_0.wrap i ∧
      reg1_0.wrap i = reg1_1.wrap i) ∧
    Round7Geometry.rotation0.quaternionScale = 4096 ∧
    Round7Geometry.rotation1.quaternionScale = 4096 ∧
    Round7Geometry.rotation0.selector = 0 ∧ Round7Geometry.rotation1.selector = 0 := by
  decide +kernel

/-- A row certifies its cell when the strict J comparison holds at every valid
point of the cell. -/
def certifies (_ : Round7Geometry.ParentAddress) (_ : Round7Geometry.JointRow)
    (cell : Round7Geometry.Box) : Prop :=
  ∀ x, (toCell cell).Mem x → (chartPoint x).Valid → 0 < deficit (chartPoint x)

theorem closed0 : Round7Geometry.tree0.Valid
    (Round7Geometry.BoundLeaf Round7Geometry.rows0
      (certifies Round7Geometry.parent0)) rb0 := by
  refine ⟨⟨Round7Geometry.rows0.get ⟨0, by decide⟩, List.get_mem _ _, rfl, leaf0_0_strict⟩,
    ⟨Round7Geometry.rows0.get ⟨1, by decide⟩, List.get_mem _ _, rfl, leaf0_1_strict⟩,
    ⟨Round7Geometry.rows0.get ⟨2, by decide⟩, List.get_mem _ _, rfl, leaf0_2_strict⟩⟩

theorem closed1 : Round7Geometry.tree1.Valid
    (Round7Geometry.BoundLeaf Round7Geometry.rows1
      (certifies Round7Geometry.parent1)) rb1 := by
  refine ⟨⟨Round7Geometry.rows1.get ⟨0, by decide⟩, List.get_mem _ _, rfl, leaf1_0_strict⟩,
    ⟨Round7Geometry.rows1.get ⟨1, by decide⟩, List.get_mem _ _, rfl, leaf1_1_strict⟩⟩

/-- Every valid chart point in either round-seven root box has strictly
positive deficit `e − e_BCC − g D`. -/
theorem round7_strict (p : Chart) (hv : (chartPoint p).Valid)
    (h : (toCell rb0).Mem p ∨ (toCell rb1).Mem p) : 0 < deficit (chartPoint p) :=
  Round7Geometry.round7_covers (α := ℝ) le_total (fun q : ℚ => (q : ℝ)) p
    (0 < deficit (chartPoint p)) rb0 rb1 certifies closed0 closed1
    (fun _ _ _ hc hm => hc p hm hv) h

/-- The same statement on the boxes of the reconstructed round-seven manifest. -/
theorem round7_fixture (p : Chart) (hv : (chartPoint p).Valid)
    (h : (toCell rootLiteral0).Mem p ∨ (toCell rootLiteral1).Mem p) :
    0 < deficit (chartPoint p) := by
  have m := roots_match
  apply round7_strict p hv
  rcases h with h | h
  · left
    intro i
    obtain ⟨elo, ehi⟩ := m.1 i
    have hi := h i
    change ((rootLiteral0.lo i : ℚ) : ℝ) ≤ p i ∧ p i ≤ ((rootLiteral0.hi i : ℚ) : ℝ) at hi
    change ((rb0.lo i : ℚ) : ℝ) ≤ p i ∧ p i ≤ ((rb0.hi i : ℚ) : ℝ)
    rw [elo, ehi]
    exact hi
  · right
    intro i
    obtain ⟨elo, ehi⟩ := m.2 i
    have hi := h i
    change ((rootLiteral1.lo i : ℚ) : ℝ) ≤ p i ∧ p i ≤ ((rootLiteral1.hi i : ℚ) : ℝ) at hi
    change ((rb1.lo i : ℚ) : ℝ) ≤ p i ∧ p i ≤ ((rb1.hi i : ℚ) : ℝ)
    rw [elo, ehi]
    exact hi

/-- Every point of either root is a valid chart point: both radial coordinates
are positive, and the first offset coordinate lies in `[2047/4096, 1/2]`. -/
theorem round7_roots_valid (p : Chart)
    (h : (toCell rootLiteral0).Mem p ∨ (toCell rootLiteral1).Mem p) : (chartPoint p).Valid := by
  rcases h with h | h
  · exact valid_of_box (toCell rootLiteral0) 0 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) p h
  · exact valid_of_box (toCell rootLiteral1) 0 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) p h

/-- The fixture at every point of both round-seven root boxes, with no
validity premise: `e − e_BCC − g D > 0` throughout. -/
theorem round7_fixture_all (p : Chart)
    (h : (toCell rootLiteral0).Mem p ∨ (toCell rootLiteral1).Mem p) :
    0 < deficit (chartPoint p) :=
  round7_fixture p (round7_roots_valid p h) h

/-- Non-vacuity: the lower corner of root 0 is a valid chart point of the box. -/
theorem round7_nonvacuous : ∃ p : Chart, (toCell rootLiteral0).Mem p ∧ (chartPoint p).Valid := by
  have ord : ∀ i, rootLiteral0.lo i ≤ rootLiteral0.hi i := by decide +kernel
  have l0 : (0 : ℚ) < rootLiteral0.lo 0 := by decide +kernel
  have l1 : (0 : ℚ) < rootLiteral0.lo 1 := by decide +kernel
  have l5 : rootLiteral0.lo 5 * 4096 = 2047 := by decide +kernel
  let q : Chart := fun i => ((rootLiteral0.lo i : ℚ) : ℝ)
  refine ⟨q, ?_, ?_⟩
  · intro i
    refine ⟨le_rfl, ?_⟩
    show ((rootLiteral0.lo i : ℚ) : ℝ) ≤ ((rootLiteral0.hi i : ℚ) : ℝ)
    exact_mod_cast ord i
  show (chartPoint q).basis.det = 1 ∧ ∀ n, (chartPoint q).offset ≠ castVec n
  refine ⟨?_, ?_⟩
  · have r0 : q 0 ≠ 0 := by
      show ((rootLiteral0.lo 0 : ℚ) : ℝ) ≠ 0
      exact_mod_cast l0.ne'
    have r1 : q 1 ≠ 0 := by
      show ((rootLiteral0.lo 1 : ℚ) : ℝ) ≠ 0
      exact_mod_cast l1.ne'
    have e : (chartPoint q).basis.det = q 0 * q 1 * (q 0 * q 1)⁻¹ := by
      simp [chartPoint, chartBasis, Matrix.det_fin_three]
    rw [e]
    field_simp
  · intro n hn
    have h5 := congrFun hn 0
    have e : (chartPoint q).offset 0 = ((rootLiteral0.lo 5 : ℚ) : ℝ) := rfl
    rw [e] at h5
    have h5' : ((rootLiteral0.lo 5 : ℚ) : ℝ) = ((n 0 : ℤ) : ℝ) := h5
    have hq : rootLiteral0.lo 5 = ((n 0 : ℤ) : ℚ) := by exact_mod_cast h5'
    have h1 : ((n 0 : ℤ) : ℚ) * 4096 = 2047 := by rw [← hq]; exact l5
    have h2 : (n 0 : ℤ) * 4096 = 2047 := by exact_mod_cast h1
    omega

/-- No point of either root is reduced, because
`B e₂` is shorter than `B e₁` throughout both boxes. -/
theorem round7_roots_not_reduced (p : Chart)
    (h : (toCell rootLiteral0).Mem p ∨ (toCell rootLiteral1).Mem p) : ¬ reductionInequalities p := by
  have key (b : Round7Geometry.Box) (c0 : (8660254 / 10000000 : ℚ) ≤ b.lo 0)
      (c1 : (0 : ℚ) ≤ b.lo 1) (c1' : b.hi 1 ≤ 8162525 / 10000000) (c2 : (0 : ℚ) ≤ b.lo 2)
      (c2' : b.hi 2 ≤ 34201 / 102400) (hm : (toCell b).Mem p) :
      (8660254 / 10000000 : ℝ) ≤ p 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ (8162525 / 10000000 : ℝ) ∧
        0 ≤ p 2 ∧ p 2 ≤ (34201 / 102400 : ℝ) := by
    have m0 : ((b.lo 0 : ℚ) : ℝ) ≤ p 0 ∧ p 0 ≤ ((b.hi 0 : ℚ) : ℝ) := hm 0
    have m1 : ((b.lo 1 : ℚ) : ℝ) ≤ p 1 ∧ p 1 ≤ ((b.hi 1 : ℚ) : ℝ) := hm 1
    have m2 : ((b.lo 2 : ℚ) : ℝ) ≤ p 2 ∧ p 2 ≤ ((b.hi 2 : ℚ) : ℝ) := hm 2
    have d0 := (Rat.cast_le (K := ℝ)).mpr c0
    have d1 := (Rat.cast_le (K := ℝ)).mpr c1
    have d1' := (Rat.cast_le (K := ℝ)).mpr c1'
    have d2 := (Rat.cast_le (K := ℝ)).mpr c2
    have d2' := (Rat.cast_le (K := ℝ)).mpr c2'
    push_cast at d0 d1 d1' d2 d2'
    exact ⟨d0.trans m0.1, d1.trans m1.1, m1.2.trans d1', d2.trans m2.1, m2.2.trans d2'⟩
  have bounds : (8660254 / 10000000 : ℝ) ≤ p 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ (8162525 / 10000000 : ℝ) ∧
      0 ≤ p 2 ∧ p 2 ≤ (34201 / 102400 : ℝ) := by
    rcases h with h | h
    · exact key rootLiteral0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) h
    · exact key rootLiteral1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) h
  obtain ⟨a0, h1', a1, h2, a2⟩ := bounds
  intro hr
  have e := hr.1 ![0, 1, 0] (by decide)
  have e2 : BccSharp.Coulomb.sq ((chartBasis p).mulVec (castVec ![0, 1, 0])) =
      (p 0 * p 2) ^ 2 + (p 1) ^ 2 := by
    simp [BccSharp.Coulomb.sq, chartBasis, castVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  rw [e2] at e
  have s2 : p 2 ^ 2 ≤ (34201 / 102400 : ℝ) ^ 2 := pow_le_pow_left₀ h2 a2 2
  have s0 : (8660254 / 10000000 : ℝ) ^ 2 ≤ p 0 ^ 2 := pow_le_pow_left₀ (by norm_num) a0 2
  have s1 : p 1 ^ 2 ≤ (8162525 / 10000000 : ℝ) ^ 2 := pow_le_pow_left₀ h1' a1 2
  have m : p 0 ^ 2 * (1 - (34201 / 102400 : ℝ) ^ 2) ≤ p 0 ^ 2 * (1 - p 2 ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have m2 : (8660254 / 10000000 : ℝ) ^ 2 * (1 - (34201 / 102400 : ℝ) ^ 2) ≤
      p 0 ^ 2 * (1 - (34201 / 102400 : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right s0 (by norm_num)
  have num : (8162525 / 10000000 : ℝ) ^ 2 <
      (8660254 / 10000000 : ℝ) ^ 2 * (1 - (34201 / 102400 : ℝ) ^ 2) := by norm_num
  have expand : (p 0 * p 2) ^ 2 = p 0 ^ 2 * p 2 ^ 2 := by ring
  rw [expand] at e
  nlinarith [m, m2, num, s1, e]

/-- Negative control: changing one literal coefficient makes the item fail,
because the checker recomputes the term from its witness. -/
theorem item_mutation_rejected :
    itemOk S0_0 ⟨it0_0_24.wit, { it0_0_24.lin with const := it0_0_24.lin.const + 1 }⟩ = false := by
  decide +kernel

/-- Negative control at leaf level: lowering the support constant by 10⁻⁸
(about 2.5·10⁻⁹ per particle, more than the leaf's minimum margin) makes some
corner margin negative, so the 256-corner check fails. -/
theorem leaf_mutation_rejected :
    leafCheck leaf0_0 S0_0 (K0_0 - 1 / 100000000) w0_0 reg0_0 = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.JLeaf.Round7
