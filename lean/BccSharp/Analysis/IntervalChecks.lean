module

public import BccSharp.Analysis.Intervals

/-! Exact checks for outward-rounded rational interval witnesses. Rounding
proposals may be generated externally; only the inequalities below determine
acceptance. Inversion refuses intervals meeting zero. -/

@[expose] public section
namespace BccSharp.Intervals.Ball

def Covers (b c : Ball) : Prop := |b.mid - c.mid| + b.rad ≤ c.rad
instance (b c : Ball) : Decidable (Covers b c) := inferInstanceAs (Decidable (_ ≤ _))

theorem covers_sound {b c : Ball} (hc : Covers b c) {x : ℝ} (hx : b.Contains x) : c.Contains x := by
  have hh : |(b.mid : ℝ) - c.mid| + b.rad ≤ c.rad := by exact_mod_cast hc
  unfold Contains at *
  calc
    _ = |(x - b.mid) + (b.mid - c.mid)| := by congr 1; ring
    _ ≤ |x - b.mid| + |(b.mid : ℝ) - c.mid| := abs_add_le _ _
    _ ≤ _ := by linarith

def invertible (b : Ball) : Prop := b.rad < |b.mid|
instance (b : Ball) : Decidable b.invertible := inferInstanceAs (Decidable (_ < _))
def inv (b : Ball) : Ball := ⟨b.mid⁻¹, b.rad / (|b.mid| * (|b.mid| - b.rad))⟩

theorem contains_inv {b : Ball} {x : ℝ} (hb : b.invertible) (hx : b.Contains x) :
    b.inv.Contains x⁻¹ := by
  have hr : 0 ≤ (b.rad : ℝ) := radius_nonneg hx
  have hg : (b.rad : ℝ) < |(b.mid : ℝ)| := by exact_mod_cast hb
  have hm : 0 < |(b.mid : ℝ)| := lt_of_le_of_lt hr hg
  have hgap : 0 < |(b.mid : ℝ)| - b.rad := sub_pos.mpr hg
  have hdist := abs_sub_abs_le_abs_sub (b.mid : ℝ) x
  rw [abs_sub_comm] at hdist
  have hlow : |(b.mid : ℝ)| - b.rad ≤ |x| := by dsimp [Contains] at hx; linarith
  have hxp : 0 < |x| := lt_of_lt_of_le hgap hlow
  have hx0 : x ≠ 0 := abs_pos.mp hxp
  have hm0 : (b.mid : ℝ) ≠ 0 := abs_pos.mp hm
  unfold Contains inv
  push_cast
  have he : x⁻¹ - (b.mid : ℝ)⁻¹ = ((b.mid : ℝ) - x) / (x * (b.mid : ℝ)) := by field_simp
  rw [he, abs_div, abs_mul, abs_sub_comm]
  calc
    _ ≤ (b.rad : ℝ) / (|x| * |(b.mid : ℝ)|) :=
      div_le_div_of_nonneg_right hx (mul_nonneg hxp.le hm.le)
    _ ≤ _ := div_le_div_of_nonneg_left hr (mul_pos hm hgap)
      (by nlinarith [mul_le_mul_of_nonneg_right hlow hm.le])

end BccSharp.Intervals.Ball
