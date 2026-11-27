module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Complete integer-cube enumeration and explicit tails for Gaussian-dominated
lattice sums. The bcc and reciprocal parity restrictions are predicates on the
same integer triples; no external enumeration or lattice-counting oracle is used. -/

@[expose] public section
namespace BccSharp.LatticeTails

abbrev Triple := ℤ × ℤ × ℤ

def length (z : Triple) : ℕ := z.1.natAbs + z.2.1.natAbs + z.2.2.natAbs

def square (z : Triple) : ℕ := z.1.natAbs ^ 2 + z.2.1.natAbs ^ 2 + z.2.2.natAbs ^ 2

noncomputable def normSq (z : Triple) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.2.1 : ℝ) ^ 2 + (z.2.2 : ℝ) ^ 2

def cube (R : ℕ) : Finset Triple :=
  (Finset.Icc (-(R : ℤ)) R) ×ˢ ((Finset.Icc (-(R : ℤ)) R) ×ˢ
    (Finset.Icc (-(R : ℤ)) R))

def bcc (z : Triple) : Prop := z.1 % 2 = z.2.1 % 2 ∧ z.2.1 % 2 = z.2.2 % 2

def reciprocal (z : Triple) : Prop := (z.1 + z.2.1 + z.2.2) % 2 = 0

instance (z : Triple) : Decidable (bcc z) := inferInstanceAs (Decidable (_ ∧ _))
instance (z : Triple) : Decidable (reciprocal z) := inferInstanceAs (Decidable (_ = _))

def bccCube (R : ℕ) : Finset Triple := (cube R).filter fun z => bcc z ∧ z ≠ 0

def reciprocalCube (R : ℕ) : Finset Triple := (cube R).filter reciprocal

@[simp] theorem mem_cube (R : ℕ) (z : Triple) : z ∈ cube R ↔
    z.1.natAbs ≤ R ∧ z.2.1.natAbs ≤ R ∧ z.2.2.natAbs ≤ R := by
  simp only [cube, Finset.mem_product, Finset.mem_Icc]
  simp only [← abs_le, ← Int.natCast_natAbs, Nat.cast_le]

@[simp] theorem mem_bccCube (R : ℕ) (z : Triple) : z ∈ bccCube R ↔
    z ∈ cube R ∧ bcc z ∧ z ≠ 0 := by simp [bccCube]

@[simp] theorem mem_reciprocalCube (R : ℕ) (z : Triple) : z ∈ reciprocalCube R ↔
    z ∈ cube R ∧ reciprocal z := by simp [reciprocalCube]

theorem normSq_eq_square (z : Triple) : normSq z = (square z : ℝ) := by
  simp [normSq, square]

theorem length_le_square (z : Triple) : length z ≤ square z := by
  have h (n : ℕ) : n ≤ n ^ 2 := Nat.le_self_pow (by decide) n
  exact Nat.add_le_add (Nat.add_le_add (h _) (h _)) (h _)

theorem outside_square (R : ℕ) {z : Triple} (hz : z ∉ cube R) :
    length z + R * (R + 1) ≤ square z := by
  have h (n : ℕ) : n ≤ n ^ 2 := Nat.le_self_pow (by decide) n
  have hg (n : ℕ) (hn : R < n) : n + R * (R + 1) ≤ n ^ 2 := by
    have hp : (R + 1) * (n - (R + 1)) ≥ 0 := Nat.zero_le _
    nlinarith
  simp only [mem_cube, not_and_or, not_le] at hz
  rcases hz with h₁ | h₂ | h₃
  · have := hg _ h₁
    dsimp [length, square]; nlinarith [h z.2.1.natAbs, h z.2.2.natAbs]
  · have := hg _ h₂
    dsimp [length, square]; nlinarith [h z.1.natAbs, h z.2.2.natAbs]
  · have := hg _ h₃
    dsimp [length, square]; nlinarith [h z.1.natAbs, h z.2.1.natAbs]

noncomputable def weight (z : Triple) : ℝ := (1 / 2 : ℝ) ^ length z

theorem weight_nonneg (z : Triple) : 0 ≤ weight z := by unfold weight; positivity

theorem hasSum_integer_geometric :
    HasSum (fun z : ℤ => (1 / 2 : ℝ) ^ z.natAbs) 3 := by
  have h := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hn : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
    convert h.mul_right (1 / 2) using 1
    · funext n; rw [pow_succ]
    · norm_num
  have h₁ : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n : ℤ).natAbs) 2 := by
    convert h using 1 <;> norm_num
  have h₂ : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (-(↑n + 1) : ℤ).natAbs) 1 := by
    simpa only [Int.natAbs_neg, ← Int.natCast_succ, Int.natAbs_natCast] using hn
  convert HasSum.of_nat_of_neg_add_one (f := fun z : ℤ => (1 / 2 : ℝ) ^ z.natAbs)
    h₁ h₂ using 1; norm_num

theorem weight_summable : Summable weight := by
  have h := hasSum_integer_geometric.summable
  have hp := h.mul_of_nonneg h (fun _ => by positivity) (fun _ => by positivity)
  have hpp := h.mul_of_nonneg hp (fun _ => by positivity) (fun _ => by positivity)
  change Summable (fun z : Triple => (1 / 2 : ℝ) ^ length z)
  simpa only [length, pow_add, mul_assoc] using hpp

theorem tsum_weight : ∑' z : Triple, weight z = 27 := by
  have h := hasSum_integer_geometric.summable
  have hp := h.mul_of_nonneg h (fun _ => by positivity) (fun _ => by positivity)
  have he := h.tsum_mul_tsum h hp
  have he' := h.tsum_mul_tsum hp (h.mul_of_nonneg hp
    (fun _ => by positivity) (fun _ => by positivity))
  simp only [hasSum_integer_geometric.tsum_eq] at he he'
  rw [← he] at he'
  norm_num at he'
  simpa only [weight, length, pow_add, mul_assoc] using he'.symm

theorem gaussian_le_weight (z : Triple) : Real.exp (-normSq z) ≤ weight z := by
  rw [normSq_eq_square]
  calc
    _ ≤ Real.exp (-(length z : ℝ)) := Real.exp_le_exp.mpr (by
      apply neg_le_neg; exact_mod_cast length_le_square z)
    _ = Real.exp (-1) ^ length z := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le _

theorem gaussian_outside (R : ℕ) {z : Triple} (hz : z ∉ cube R) :
    Real.exp (-normSq z) ≤ (1 / 2 : ℝ) ^ (R * (R + 1)) * weight z := by
  rw [normSq_eq_square]
  calc
    _ ≤ Real.exp (-((length z + R * (R + 1) : ℕ) : ℝ)) :=
      Real.exp_le_exp.mpr (by apply neg_le_neg; exact_mod_cast outside_square R hz)
    _ = Real.exp (-1) ^ (length z + R * (R + 1)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ (1 / 2 : ℝ) ^ (length z + R * (R + 1)) :=
      pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le _
    _ = _ := by rw [pow_add]; exact mul_comm _ _

/-- Absolute convergence follows from a pointwise analytic majorant. -/
theorem summable_of_gaussian_bound {f : Triple → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, |f z| ≤ C * Real.exp (-normSq z)) : Summable f := by
  apply (weight_summable.mul_left C).of_norm_bounded
  intro z
  exact (hf z).trans (mul_le_mul_of_nonneg_left (gaussian_le_weight z) hC)

/-- Every omitted integer triple is accounted for, with an explicit rational
remainder. The same theorem applies to parity-filtered sums by setting other
terms to zero. There is no summability hypothesis or assumed tail bound. -/
theorem cube_error {f : Triple → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, |f z| ≤ C * Real.exp (-normSq z)) (R : ℕ) :
    |(∑' z, f z) - ∑ z ∈ cube R, f z| ≤
      C * (1 / 2 : ℝ) ^ (R * (R + 1)) * 27 := by
  have hs := summable_of_gaussian_bound hC hf
  have hw := (weight_summable.mul_left (C * (1 / 2 : ℝ) ^ (R * (R + 1)))).subtype
    (fun z => z ∉ cube R)
  have hbound (z : {z // z ∉ cube R}) :
      ‖f z.val‖ ≤ (C * (1 / 2 : ℝ) ^ (R * (R + 1))) * weight z.val := by
    calc
      _ ≤ C * Real.exp (-normSq z.val) := hf z.val
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussian_outside R z.property) hC
  have hn := Summable.of_nonneg_of_le (fun z => norm_nonneg (f z.val)) hbound hw
  have he := hs.sum_add_tsum_subtype_compl (cube R)
  have ht : (∑' z, f z) - ∑ z ∈ cube R, f z = ∑' z : {z // z ∉ cube R}, f z := by
    linarith
  rw [ht, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' z : {z // z ∉ cube R}, ‖f z.val‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' z : {z // z ∉ cube R},
        (C * (1 / 2 : ℝ) ^ (R * (R + 1))) * weight z.val := hn.tsum_le_tsum hbound hw
    _ ≤ ∑' z : Triple, (C * (1 / 2 : ℝ) ^ (R * (R + 1))) * weight z := by
      exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun z _ => mul_nonneg (mul_nonneg hC (by positivity)) (weight_nonneg z)) (fun _ => le_rfl) hw
        (weight_summable.mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_weight]

set_option maxRecDepth 8192 in
/-- Concrete enumeration sizes, checked by Lean reduction (not native_decide). -/
theorem cube_five_card : (cube 5).card = 1331 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem bccCube_five_card : (bccCube 5).card = 340 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem reciprocalCube_five_card : (reciprocalCube 5).card = 665 := by decide

end BccSharp.LatticeTails
