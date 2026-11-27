import BccSharp.Lattice.Curvature
import BccSharp.Lattice.Energy

set_option autoImplicit false

/-! Centered first-order leaf rule.
This consumes interval witnesses for derivatives of the actual finite
positive series along the closed segment. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp

def boxCenter (b : Rectangle) (i : Fin 5) : ℝ := (coordinateBall b i).mid
def segment (b : Rectangle) (p : Point) (t : ℝ) : Point :=
  fun i => (1-t)*boxCenter b i+t*p i

theorem boxCenter_mem {b : Rectangle} {p : Point} (hp : b.Mem p) : b.Mem (boxCenter b) := by
  intro i
  have h := hp i
  unfold boxCenter coordinateBall ballOf
  push_cast
  constructor <;> linarith [h.1,h.2]

theorem segment_mem {b : Rectangle} {p : Point} (hp : b.Mem p) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    b.Mem (segment b p t) := by
  intro i
  have hc := boxCenter_mem hp i
  have hlo := add_le_add (mul_le_mul_of_nonneg_left hc.1 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (hp i).1 ht.1)
  have hhi := add_le_add (mul_le_mul_of_nonneg_left hc.2 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (hp i).2 ht.1)
  exact ⟨by unfold segment; linarith,by unfold segment; linarith⟩

def gradientLoss (b : Rectangle) (gradient : Fin 5 → Ball) : ℚ :=
  ∑ i, (coordinateBall b i).rad * absUpper (gradient i)

def meanValueLower (b : Rectangle) (atCenter : Ball) (gradient : Fin 5 → Ball) : ℚ :=
  atCenter.lo-gradientLoss b gradient

theorem meanValueLower_sound (b : Rectangle) (p : Point) (hp : b.Mem p) (f : Point → ℝ)
    (g : Point → Fin 5 → ℝ) (atCenter : Ball) (gradient : Fin 5 → Ball)
    (hCenter : atCenter.Contains (f (boxCenter b)))
    (hGradient : ∀ x, b.Mem x → ∀ i, (gradient i).Contains (g x i))
    (continuity : ContinuousOn (fun t => f (segment b p t)) (Set.Icc 0 1))
    (differentiate : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt
      (fun s => f (segment b p s))
      (∑ i, g (segment b p t) i * (p i-boxCenter b i)) t) :
    (meanValueLower b atCenter gradient : ℝ) ≤ f p := by
  obtain ⟨t,ht,hSlope⟩ := exists_hasDerivAt_eq_slope (fun t => f (segment b p t))
    (fun t => ∑ i, g (segment b p t) i * (p i-boxCenter b i))
    (by norm_num : (0 : ℝ) < 1) continuity differentiate
  have pt := segment_mem hp (Set.Ioo_subset_Icc_self ht)
  have hd (i : Fin 5) :
      -((coordinateBall b i).rad : ℝ)*(absUpper (gradient i) : ℝ) ≤
        g (segment b p t) i*(p i-boxCenter b i) := by
    have ha := absUpper_sound (hGradient _ pt i)
    have hb := coordinateBall_sound hp i
    have hc : |p i-boxCenter b i| ≤ ((coordinateBall b i).rad : ℝ) := hb
    have hm := mul_le_mul ha hc (abs_nonneg _) ((abs_nonneg _).trans ha)
    have he₁ := neg_abs_le (g (segment b p t) i*(p i-boxCenter b i))
    rw [abs_mul] at he₁
    have he := (neg_le_neg hm).trans he₁
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => hd i)
  have h₀ : segment b p 0=boxCenter b := by funext i; simp [segment]
  have h₁ : segment b p 1=p := by funext i; simp [segment]
  simp only [h₀,h₁,sub_zero,div_one] at hSlope
  simp_rw [neg_mul,Finset.sum_neg_distrib] at hs
  have hc : (atCenter.lo : ℝ) ≤ f (boxCenter b) := by
    simpa [Ball.lo] using ((SpecialFunctions.contains_iff_endpoints _ _).mp hCenter).1
  unfold meanValueLower gradientLoss
  push_cast
  linarith

theorem meanValue_above_fcc (b : Rectangle) (p : Point) (hp : b.Mem p)
    (h₁ : p 0 ≠ 0) (h₂ : p 1 ≠ 0) (f : Point → ℝ) (g : Point → Fin 5 → ℝ)
    (atCenter : Ball) (gradient : Fin 5 → Ball)
    (hCenter : atCenter.Contains (f (boxCenter b)))
    (hGradient : ∀ x, b.Mem x → ∀ i, (gradient i).Contains (g x i))
    (continuity : ContinuousOn (fun t => f (segment b p t)) (Set.Icc 0 1))
    (differentiate : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt
      (fun s => f (segment b p s))
      (∑ i, g (segment b p t) i * (p i-boxCenter b i)) t)
    (finiteLower : f p ≤ positiveSeries (normalizedChart p))
    (positive : HfccUpper < meanValueLower b atCenter gradient) : Sharp (primitiveChart p) := by
  apply chart_above_fcc_of_series p h₁ h₂
  exact (by exact_mod_cast positive : (HfccUpper : ℝ) < (meanValueLower b atCenter gradient : ℝ)).trans_le
    ((meanValueLower_sound b p hp f g atCenter gradient hCenter hGradient continuity differentiate).trans finiteLower)

end BccSharp.Coulomb.BravaisCover
