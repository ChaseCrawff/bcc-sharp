module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exact rational balls. Invalid (negative-radius) balls represent the empty
set. Every operation below comes with a theorem about the real values it encloses.
No floating-point computation or external interval implementation is trusted. -/

@[expose] public section

namespace BccSharp.Intervals

structure Ball where
  mid : ℚ
  rad : ℚ
  deriving DecidableEq, Repr

namespace Ball

def Contains (b : Ball) (x : ℝ) : Prop := |x - (b.mid : ℝ)| ≤ (b.rad : ℝ)

def exact (q : ℚ) : Ball := ⟨q, 0⟩
def neg (b : Ball) : Ball := ⟨-b.mid, b.rad⟩
def add (b c : Ball) : Ball := ⟨b.mid + c.mid, b.rad + c.rad⟩
def sub (b c : Ball) : Ball := b.add c.neg
def mul (b c : Ball) : Ball :=
  ⟨b.mid * c.mid, |b.mid| * c.rad + |c.mid| * b.rad + b.rad * c.rad⟩

def positive (b : Ball) : Bool := decide (0 < b.mid - b.rad)

@[simp] theorem contains_exact (q : ℚ) : (exact q).Contains (q : ℝ) := by
  simp [Contains, exact]

theorem radius_nonneg {b : Ball} {x : ℝ} (h : b.Contains x) : 0 ≤ (b.rad : ℝ) :=
  (abs_nonneg _).trans h

theorem contains_neg {b : Ball} {x : ℝ} (h : b.Contains x) : b.neg.Contains (-x) := by
  change |-x - ((-b.mid : ℚ) : ℝ)| ≤ (b.rad : ℝ)
  rw [Rat.cast_neg, neg_sub_neg, abs_sub_comm]
  exact h

theorem contains_add {b c : Ball} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (b.add c).Contains (x + y) := by
  change |x + y - ((b.mid + c.mid : ℚ) : ℝ)| ≤ ((b.rad + c.rad : ℚ) : ℝ)
  push_cast
  calc
    _ = |(x - b.mid) + (y - c.mid)| := by congr 1; ring
    _ ≤ |x - b.mid| + |y - c.mid| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem contains_sub {b c : Ball} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (b.sub c).Contains (x - y) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

theorem contains_mul {b c : Ball} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (b.mul c).Contains (x * y) := by
  change |x * y - ((b.mid * c.mid : ℚ) : ℝ)| ≤
    ((|b.mid| * c.rad + |c.mid| * b.rad + b.rad * c.rad : ℚ) : ℝ)
  push_cast
  calc
    _ = |(b.mid : ℝ) * (y - c.mid) + (c.mid : ℝ) * (x - b.mid) +
        (x - b.mid) * (y - c.mid)| := by congr 1; ring
    _ ≤ |(b.mid : ℝ) * (y - c.mid) + (c.mid : ℝ) * (x - b.mid)| +
        |(x - b.mid) * (y - c.mid)| := abs_add_le _ _
    _ ≤ (|(b.mid : ℝ)| * |y - c.mid| + |(c.mid : ℝ)| * |x - b.mid|) +
        |x - b.mid| * |y - c.mid| := by
      rw [abs_mul (x - b.mid)]
      exact add_le_add
        (by simpa only [abs_mul] using
          (abs_add_le ((b.mid : ℝ) * (y - c.mid)) ((c.mid : ℝ) * (x - b.mid)))) (le_refl _)
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
      (mul_le_mul hx hy (abs_nonneg _) (radius_nonneg hx))

theorem positive_sound {b : Ball} {x : ℝ} (hb : b.positive = true)
    (hx : b.Contains x) : 0 < x := by
  have hq : 0 < b.mid - b.rad := of_decide_eq_true hb
  have hr : (0 : ℝ) < (b.mid : ℝ) - (b.rad : ℝ) := by exact_mod_cast hq
  have h := (abs_le.mp hx).1
  linarith

/-- Square roots are certified by rational endpoint witnesses, not by evaluating
an approximate square root inside the trusted checker. -/
theorem sqrt_enclosure {x : ℝ} {l u : ℚ} (hl : 0 ≤ l) (hx : 0 ≤ x)
    (hlo : (l : ℝ) ^ 2 ≤ x) (hup : x ≤ (u : ℝ) ^ 2) (hu : 0 ≤ u) :
    (⟨(l + u) / 2, (u - l) / 2⟩ : Ball).Contains (Real.sqrt x) := by
  have hlr : (0 : ℝ) ≤ l := by exact_mod_cast hl
  have hur : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  have h₁ : (l : ℝ) ≤ Real.sqrt x := by nlinarith
  have h₂ : Real.sqrt x ≤ (u : ℝ) := by nlinarith
  simp only [Contains, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ball

end BccSharp.Intervals
