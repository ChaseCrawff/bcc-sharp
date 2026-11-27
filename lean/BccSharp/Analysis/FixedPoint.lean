module

public import BccSharp.Analysis.IntervalChecks
public import Mathlib.Algebra.Order.Floor.Ring

/-! Fixed precision integer balls. Integer arithmetic computes the endpoints;
all operations are proved to enclose the corresponding real operations. -/

@[expose] public section
namespace BccSharp.FixedPoint

open Intervals

@[ext] theorem interval_ext (a b : Intervals.Ball) (hm : a.mid = b.mid) (hr : a.rad = b.rad) : a = b := by
  cases a
  cases b
  simp_all

def scale : ℤ := 1461501637330902918203684832716283019655932542976

theorem scale_pos : 0 < scale := by decide
theorem scale_rat_pos : (0 : ℚ) < scale := by exact_mod_cast scale_pos

structure Ball where
  mid : ℤ
  rad : ℤ
  deriving DecidableEq, Repr

namespace Ball

def rational (b : Ball) : Intervals.Ball := ⟨(b.mid : ℚ) / scale, (b.rad : ℚ) / scale⟩
def Contains (b : Ball) (x : ℝ) : Prop := b.rational.Contains x

def zero : Ball := ⟨0,0⟩
def neg (b : Ball) : Ball := ⟨-b.mid,b.rad⟩
def add (b c : Ball) : Ball := ⟨b.mid+c.mid,b.rad+c.rad⟩
def sub (b c : Ball) : Ball := b.add c.neg

def ceilingDiv (n d : ℤ) : ℤ := -((-n) / d)
def roundingError (m n : ℤ) : ℤ := if m % n = 0 then 0 else 1
def rounded (m n r d : ℤ) : Ball := ⟨m / n, ceilingDiv r d + roundingError m n⟩

theorem floor_bounds (n d : ℤ) (hd : 0 < d) :
    ((n / d : ℤ) : ℚ) ≤ (n : ℚ) / d ∧ (n : ℚ) / d < (n / d : ℤ) + 1 := by
  have he : ⌊(n : ℚ) / d⌋ = n / d := by
    rw [Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast]
  rw [← he]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem ceiling_bound (n d : ℤ) (hd : 0 < d) : (n : ℚ) / d ≤ ceilingDiv n d := by
  have h := (floor_bounds (-n) d hd).1
  simpa only [ceilingDiv, Int.cast_neg, neg_div, neg_neg] using neg_le_neg h

/-- Both divisions round outward, with an extra unit only when the midpoint division is inexact. -/
theorem rounded_covers (m n r d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (⟨(m : ℚ) / n / scale, (r : ℚ) / d / scale⟩ : Intervals.Ball).Covers (rounded m n r d).rational := by
  have hm := floor_bounds m n hn
  have hr := ceiling_bound r d hd
  have hab : |(m : ℚ) / n - (m / n : ℤ)| ≤ (roundingError m n : ℚ) := by
    unfold roundingError
    split_ifs with he
    · have heq : (m : ℚ) / n = (m / n : ℤ) := by
        apply (div_eq_iff (by exact_mod_cast hn.ne')).2
        exact_mod_cast (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero he)).symm
      simp [heq]
    · rw [abs_of_nonneg (sub_nonneg.mpr hm.1)]
      norm_num only [Int.cast_one]
      linarith [hm.2]
  unfold Intervals.Ball.Covers rational rounded
  simp only [Int.cast_add]
  rw [← sub_div, abs_div, abs_of_pos scale_rat_pos, ← add_div]
  apply (div_le_div_iff_of_pos_right scale_rat_pos).2
  linarith

def fromRat (q : ℚ) : Ball := rounded (q.num * scale) q.den 0 1

def fromBall (b : Intervals.Ball) : Ball :=
  rounded (b.mid.num * scale) b.mid.den (b.rad.num * scale) b.rad.den

theorem fromRat_contains (q : ℚ) : (fromRat q).Contains (q : ℝ) := by
  have h := rounded_covers (q.num * scale) q.den 0 1 (by exact_mod_cast q.pos) (by decide)
  have he : (⟨((q.num * scale : ℤ) : ℚ) / q.den / scale, (0 : ℚ) / 1 / scale⟩ : Intervals.Ball) =
      Intervals.Ball.exact q := by
    ext <;> simp [Intervals.Ball.exact, Int.cast_mul, mul_div_right_comm,
      div_mul_cancel₀ _ scale_rat_pos.ne', Rat.num_div_den]
  simp only [Int.cast_natCast, Int.cast_zero, Int.cast_one] at h
  rw [he] at h
  exact Intervals.Ball.covers_sound h (Intervals.Ball.contains_exact q)

theorem fromBall_covers (b : Intervals.Ball) : b.Covers (fromBall b).rational := by
  have h := rounded_covers (b.mid.num * scale) b.mid.den (b.rad.num * scale) b.rad.den
    (by exact_mod_cast b.mid.pos) (by exact_mod_cast b.rad.pos)
  have he : (⟨((b.mid.num * scale : ℤ) : ℚ) / b.mid.den / scale,
      ((b.rad.num * scale : ℤ) : ℚ) / b.rad.den / scale⟩ : Intervals.Ball) = b := by
    ext <;> simp [Int.cast_mul, mul_div_right_comm, div_mul_cancel₀ _ scale_rat_pos.ne', Rat.num_div_den]
  simp only [Int.cast_natCast] at h
  rw [he] at h
  exact h

theorem fromBall_contains {b : Intervals.Ball} {x : ℝ} (h : b.Contains x) : (fromBall b).Contains x :=
  Intervals.Ball.covers_sound (fromBall_covers b) h

theorem zero_contains : zero.Contains 0 := by simp [Contains, rational, zero, Intervals.Ball.Contains]

theorem neg_rational (b : Ball) : b.neg.rational = b.rational.neg := by
  ext <;> simp [rational, neg, Intervals.Ball.neg, neg_div]

theorem add_rational (b c : Ball) : (b.add c).rational = b.rational.add c.rational := by
  ext <;> simp [rational, add, Intervals.Ball.add, add_div]

theorem neg_contains {b : Ball} {x : ℝ} (h : b.Contains x) : b.neg.Contains (-x) := by
  rw [Contains, neg_rational]
  exact Intervals.Ball.contains_neg h

theorem add_contains {b c : Ball} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (b.add c).Contains (x+y) := by
  rw [Contains, add_rational]
  exact Intervals.Ball.contains_add hx hy

theorem sub_contains {b c : Ball} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (b.sub c).Contains (x-y) := by
  simpa only [sub, sub_eq_add_neg] using add_contains hx (neg_contains hy)

def mul (b c : Ball) : Ball := rounded (b.mid * c.mid) scale
  (|b.mid| * c.rad + |c.mid| * b.rad + b.rad * c.rad) scale

theorem mul_covers (b c : Ball) : (b.rational.mul c.rational).Covers (b.mul c).rational := by
  have h := rounded_covers (b.mid * c.mid) scale
    (|b.mid| * c.rad + |c.mid| * b.rad + b.rad * c.rad) scale scale_pos scale_pos
  have he : (⟨((b.mid * c.mid : ℤ) : ℚ) / scale / scale,
      ((|b.mid| * c.rad + |c.mid| * b.rad + b.rad * c.rad : ℤ) : ℚ) / scale / scale⟩ : Intervals.Ball) =
      b.rational.mul c.rational := by
    ext <;> simp only [rational, Intervals.Ball.mul, Int.cast_mul, Int.cast_add, Int.cast_abs,
      abs_div, abs_of_pos scale_rat_pos] <;> ring
  rw [he] at h
  exact h

theorem mul_contains {b c : Ball} {x y : ℝ} (hx : b.Contains x) (hy : c.Contains y) :
    (b.mul c).Contains (x*y) :=
  Intervals.Ball.covers_sound (mul_covers b c) (Intervals.Ball.contains_mul hx hy)

def invertible (b : Ball) : Prop := 0 ≤ b.rad ∧ b.rad < |b.mid|
instance (b : Ball) : Decidable b.invertible := inferInstanceAs (Decidable (_ ∧ _))

def invPositive (b : Ball) : Ball := rounded (scale * scale) b.mid
  (scale * scale * b.rad) (b.mid * (b.mid - b.rad))
def inv (b : Ball) : Ball := if b.mid < 0 then b.neg.invPositive.neg else b.invPositive

theorem invPositive_covers (b : Ball) (hr : 0 ≤ b.rad) (hgap : b.rad < b.mid) :
    b.rational.inv.Covers b.invPositive.rational := by
  have hm : 0 < b.mid := lt_of_le_of_lt hr hgap
  have hd : 0 < b.mid * (b.mid-b.rad) := mul_pos hm (sub_pos.mpr hgap)
  have h := rounded_covers (scale * scale) b.mid (scale * scale * b.rad)
    (b.mid * (b.mid-b.rad)) hm hd
  have hmq : (0 : ℚ) < b.mid := by exact_mod_cast hm
  have he : (⟨((scale * scale : ℤ) : ℚ) / b.mid / scale,
      ((scale * scale * b.rad : ℤ) : ℚ) / ((b.mid * (b.mid-b.rad) : ℤ) : ℚ) / scale⟩ : Intervals.Ball) =
      b.rational.inv := by
    ext <;> simp only [rational, Intervals.Ball.inv, Int.cast_mul, Int.cast_sub, abs_div,
      abs_of_pos scale_rat_pos, abs_of_pos hmq]
    · field_simp
    · field_simp
  rw [he] at h
  exact h

theorem rational_invertible {b : Ball} (h : b.invertible) : b.rational.invertible := by
  unfold Intervals.Ball.invertible rational
  rw [abs_div, abs_of_pos scale_rat_pos]
  exact (div_lt_div_iff_of_pos_right scale_rat_pos).2 (by exact_mod_cast h.2)

theorem invPositive_contains {b : Ball} {x : ℝ} (hx : b.Contains x)
    (hr : 0 ≤ b.rad) (hgap : b.rad < b.mid) : b.invPositive.Contains x⁻¹ := by
  have hb : b.invertible := ⟨hr, by rwa [abs_of_pos (lt_of_le_of_lt hr hgap)]⟩
  exact Intervals.Ball.covers_sound (invPositive_covers b hr hgap)
    (Intervals.Ball.contains_inv (rational_invertible hb) hx)

theorem inv_contains {b : Ball} {x : ℝ} (hx : b.Contains x) (hb : b.invertible) : b.inv.Contains x⁻¹ := by
  unfold inv
  split_ifs with hm
  · have hn : b.rad < -b.mid := by simpa only [abs_of_neg hm] using hb.2
    have h := neg_contains (invPositive_contains (neg_contains hx) hb.1 hn)
    simpa using h
  · exact invPositive_contains hx hb.1 (by simpa only [abs_of_nonneg (le_of_not_gt hm)] using hb.2)

end Ball
end BccSharp.FixedPoint
