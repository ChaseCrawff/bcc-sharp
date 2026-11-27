import BccSharp.Cover.CoverAssembly
import BccSharp.Lattice.GeometricLeaves

set_option autoImplicit false

/-! Reuse of the physical KZ reduction checker for Direct and Adaptive.
The recorded terminal mark only selects the route. The integer stencil
and the two necessary diagonal-ratio inequalities are checked exactly. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover
open BccSharp.Coverage
open BravaisCover

def takeShape (p : Chart) : Point := fun i => p (Fin.castLE (by decide : 5≤8) i)

def shapeBox (b : Cell) : Rectangle :=
  ⟨fun i => b.lo (Fin.castLE (by decide : 5≤8) i),fun i => b.hi (Fin.castLE (by decide : 5≤8) i)⟩

theorem takeShape_mem {b : Cell} {p : Chart} (h : b.Mem p) : (shapeBox b).Mem (takeShape p) :=
  fun i => h (Fin.castLE (by decide : 5≤8) i)

theorem takeShape_reduced (p : Chart) (hr : reductionInequalities p) : reduced (takeShape p) := by
  have basis : chartBasis (coordLift (takeShape p))=chartBasis p := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  unfold reduced reductionInequalities
  rw [basis]
  exact hr

def reductionStencil : List ReductionWitness :=
  let values : List ℤ := [-1,0,1]
  (values.flatMap fun a => values.flatMap fun b => values.map fun c => .full ![a,b,c]) ++
    (values.flatMap fun a => values.map fun b => .projected a b)

def compactStencilCheck (b : Cell) : Bool := reductionStencil.any (fun w => reductionCheck w (shapeBox b))

theorem compactStencilCheck_sound (b : Cell) (ok : compactStencilCheck b=true)
    (p : Chart) (hp : b.Mem p) : Route.result .invalidReduction p := by
  obtain ⟨w,_,hw⟩ := List.any_eq_true.mp ok
  exact fun h => reductionCheck_sound w (shapeBox b) hw (takeShape p) (takeShape_mem hp) (takeShape_reduced p h)

def compactRatioCheck (b : Cell) : Bool :=
  LatePackets.boxInside b root &&
    decide (0<b.lo 0 ∧ 0<b.lo 1 ∧
      ((b.hi 1)^2 < (3/4 : ℚ)*(b.lo 0)^2 ∨
       ((b.lo 0*b.lo 1)⁻¹)^2 < (3/4 : ℚ)*(b.lo 1)^2))

private theorem ratios_needed (p : Chart) (hp : root.Mem p) (hr : reductionInequalities p) :
    (3/4 : ℝ)*(p 0)^2 ≤ (p 1)^2 ∧ (3/4 : ℝ)*(p 1)^2 ≤ ((p 0*p 1)⁻¹)^2 := by
  have all := takeShape_reduced p hr
  have d₁ := reduced_firstLength all (![0,1,0] : IntVec) (by decide)
  have d₂ := reduced_projectedLength all 0 1 (Or.inr one_ne_zero)
  have hx : (0 : ℝ)≤p 2 ∧ p 2≤1/2 := by simpa [root] using hp 2
  have hz : (-1/2 : ℝ)≤p 4 ∧ p 4≤1/2 := by simpa [root] using hp 4
  have bound (x : ℝ) (h : (-1/2 : ℝ)≤x) (h' : x≤1/2) : x^2≤1/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h') (by linarith only [h] : 0≤1/2+x)]
  have a := mul_le_mul_of_nonneg_left (bound (p 2) (by linarith only [hx.1]) hx.2) (sq_nonneg (p 0))
  have c := mul_le_mul_of_nonneg_left (bound (p 4) hz.1 hz.2) (sq_nonneg (p 1))
  norm_num [firstLength,projectedLength,takeShape] at d₁ d₂
  constructor
  · nlinarith only [d₁,a]
  · rw [mul_inv_rev]
    nlinarith only [d₂,c]

theorem compactRatioCheck_sound (b : Cell) (ok : compactRatioCheck b=true)
    (p : Chart) (hp : b.Mem p) : Route.result .invalidReduction p := by
  obtain ⟨interior,raw⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨l₀,l₁,verdict⟩ := (of_decide_eq_true raw : 0<b.lo 0 ∧ 0<b.lo 1 ∧ _)
  have bound := LatePackets.boxInside_sound interior hp
  intro hr
  obtain ⟨needed₀,needed₁⟩ := ratios_needed p bound hr
  have lo₀ : (0 : ℝ)<b.lo 0 := by exact_mod_cast l₀
  have lo₁ : (0 : ℝ)<b.lo 1 := by exact_mod_cast l₁
  have r₀ : (0 : ℝ)<p 0 := lo₀.trans_le (hp 0).1
  have r₁ : (0 : ℝ)<p 1 := lo₁.trans_le (hp 1).1
  have p₀ := pow_le_pow_left₀ lo₀.le (hp 0).1 2
  have p₁ := pow_le_pow_left₀ lo₁.le (hp 1).1 2
  rcases verdict with left | right
  · have bad : (b.hi 1 : ℝ)^2 < (3/4 : ℝ)*(b.lo 0 : ℝ)^2 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr left
      push_cast at h
      exact h
    have hi := pow_le_pow_left₀ r₁.le (hp 1).2 2
    linarith only [bad,hi,p₀,needed₀]
  · have bad : (((b.lo 0 : ℝ)*b.lo 1)⁻¹)^2 < (3/4 : ℝ)*(b.lo 1 : ℝ)^2 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr right
      push_cast at h
      exact h
    have product := mul_le_mul (hp 0).1 (hp 1).1 lo₁.le r₀.le
    have e := inv_anti₀ (mul_pos lo₀ lo₁) product
    have hi := pow_le_pow_left₀ (inv_nonneg.mpr (mul_nonneg r₀.le r₁.le)) e 2
    linarith only [bad,hi,p₁,needed₁]

def compactReductionCheck (b : Cell) : Bool := compactRatioCheck b || compactStencilCheck b

theorem compactReductionCheck_sound (b : Cell) (ok : compactReductionCheck b=true)
    (p : Chart) (hp : b.Mem p) : Route.result .invalidReduction p := by
  rcases Bool.or_eq_true_iff.mp ok with h | h
  · exact compactRatioCheck_sound b h p hp
  · exact compactStencilCheck_sound b h p hp

end BccSharp.Coulomb.CompactCover
