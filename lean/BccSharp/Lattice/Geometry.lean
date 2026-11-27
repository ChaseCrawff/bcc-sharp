import BccSharp.Lattice.Addressed
import BccSharp.Analysis.SpecialFunctions

set_option autoImplicit false

/-! Exact Lattice artifact literals and algebraic leaf checks. The
endpoints and whitening constants are the decoded binary64 data. A
certificate applies to the exact closed rectangle selected by its address. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp.Coverage
open BccSharp.Intervals (Ball)
open BccSharp

def globalRoot : Rectangle :=
  ⟨![7205759403792791/2^53, 6240370697243165/2^53, 0, 0, -1/2],
    ![1300414392403231/2^50, 5410650294669431/2^52, 1/2, 1/2, 1/2]⟩

def strainRadiusE : Reference → ℚ
  | .bcc => 2/25
  | .fcc => 13/200

def strainRadiusT : ℚ := 4/25

def strainBox (a b : ℚ) : Rectangle := ⟨![0,0,0,0,-b], ![a,a,b,b,b]⟩

def strainRoot : Reference → Rectangle
  | .bcc => strainBox (5764607523034235/2^56) (5764607523034235/2^55)
  | .fcc => strainBox (1170935903116329/2^54) (5764607523034235/2^55)

def beta : ℚ := 4611686018427387/2^64
def ballRoot : Rectangle := strainBox beta beta

def whitenE : Reference → ℚ
  | .bcc => 6497394259185887/2^50
  | .fcc => 6167579148436093/2^50

def whitenT : Reference → ℚ
  | .bcc => 8433420444866866/2^52
  | .fcc => 8240234420342477/2^52

def coordLift (p : Point) : Chart := ![p 0,p 1,p 2,p 3,p 4,0,0,0]
def reduced (p : Point) : Prop := reductionInequalities (coordLift p)

def proofRoot (p : Point) : Prop :=
  (4/5 : ℝ) ≤ p 0 ∧ p 0 ≤ 231/200 ∧
  (2/5 : ℝ)*Real.sqrt 3 ≤ p 1 ∧ p 1 ≤ Real.sqrt (2/(Real.sqrt 3*(4/5))) ∧
  p 2 ∈ Set.Icc (0 : ℝ) (1/2) ∧ p 3 ∈ Set.Icc (0 : ℝ) (1/2) ∧
  p 4 ∈ Set.Icc (-1/2 : ℝ) (1/2)

theorem globalRoot_contains (p : Point) (hp : proofRoot p) : globalRoot.Mem p := by
  have hs : (173205080756887729352/10^20 : ℝ) ≤ Real.sqrt 3 := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg 3)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hlo : (globalRoot.lo 1 : ℝ) ≤ (2/5 : ℝ)*Real.sqrt 3 := by
    have hh := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2/5)
    exact (by norm_num [globalRoot] : (globalRoot.lo 1 : ℝ) ≤
      (2/5 : ℝ)*(173205080756887729352/10^20)).trans hh
  have hhi : Real.sqrt (2/(Real.sqrt 3*(4/5))) ≤ (globalRoot.hi 1 : ℝ) := by
    have hpos : 0 < (globalRoot.hi 1 : ℝ) := by norm_num [globalRoot]
    have hden : 0 < Real.sqrt 3*(4/5 : ℝ) := by positivity
    have hex : (2 : ℝ) ≤ (globalRoot.hi 1 : ℝ)^2*(Real.sqrt 3*(4/5)) := by
      have hh := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 4/5))
        (sq_nonneg (globalRoot.hi 1 : ℝ))
      exact (by norm_num [globalRoot] : (2 : ℝ) ≤
        (globalRoot.hi 1 : ℝ)^2*((173205080756887729352/10^20)*(4/5))).trans hh
    have hsquare := (div_le_iff₀ hden).mpr hex
    rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2/(Real.sqrt 3*(4/5)))] at hsquare
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hpos.le).mp hsquare
  intro i
  fin_cases i
  · exact ⟨(by norm_num [globalRoot] : (globalRoot.lo 0 : ℝ) ≤ 4/5).trans hp.1,
      hp.2.1.trans (by norm_num [globalRoot])⟩
  · exact ⟨hlo.trans hp.2.2.1,hp.2.2.2.1.trans hhi⟩
  · have h := Set.mem_Icc.mp hp.2.2.2.2.1
    exact ⟨(by norm_num [globalRoot] : (globalRoot.lo 2 : ℝ) ≤ 0).trans h.1,
      h.2.trans (by norm_num [globalRoot] : (1/2 : ℝ) ≤ globalRoot.hi 2)⟩
  · have h := Set.mem_Icc.mp hp.2.2.2.2.2.1
    exact ⟨(by norm_num [globalRoot] : (globalRoot.lo 3 : ℝ) ≤ 0).trans h.1,
      h.2.trans (by norm_num [globalRoot] : (1/2 : ℝ) ≤ globalRoot.hi 3)⟩
  · have h := Set.mem_Icc.mp hp.2.2.2.2.2.2
    exact ⟨(by norm_num [globalRoot] : (globalRoot.lo 4 : ℝ) ≤ -1/2).trans h.1,
      h.2.trans (by norm_num [globalRoot] : (1/2 : ℝ) ≤ globalRoot.hi 4)⟩

def folded (p : Point) : Prop :=
  0 ≤ p 0 ∧ p 0 ≤ Real.sqrt 3*p 1 ∧ 0 ≤ p 2 ∧ 0 ≤ p 3

def inProductBall (e t : ℚ) (p : Point) : Prop :=
  (p 0)^2+(p 1)^2 ≤ (e : ℝ)^2 ∧
    ∀ i : Fin 5, 2 ≤ i.val → |p i| ≤ (t : ℝ)

def strainEligible (ref : Reference) (p : Point) : Prop :=
  folded p ∧ inProductBall (strainRadiusE ref) strainRadiusT p

theorem productBall_abs_le {e t : ℚ} {p : Point} (he : 0 ≤ e) (hp : inProductBall e t p)
    (i : Fin 5) (hi : i.val < 2) : |p i| ≤ (e : ℝ) := by
  have he' : 0 ≤ (e : ℝ) := by exact_mod_cast he
  have hsq : (p i)^2 ≤ (e : ℝ)^2 := by
    fin_cases i
    · show (p 0)^2 ≤ (e : ℝ)^2
      linarith [hp.1, sq_nonneg (p 1)]
    · show (p 1)^2 ≤ (e : ℝ)^2
      linarith [hp.1, sq_nonneg (p 0)]
    all_goals exact absurd hi (by decide)
  exact (sq_le_sq₀ (abs_nonneg _) he').mp (by simpa using hsq)

theorem productBall_in_strainBox {e t : ℚ} (he : 0 ≤ e) {p : Point}
    (hf : folded p) (hp : inProductBall e t p) : (strainBox e t).Mem p := by
  have h0 := abs_le.mp (productBall_abs_le he hp 0 (by decide))
  have h1 := abs_le.mp (productBall_abs_le he hp 1 (by decide))
  have h2 := abs_le.mp (hp.2 2 (by decide))
  have h3 := abs_le.mp (hp.2 3 (by decide))
  have h4 := abs_le.mp (hp.2 4 (by decide))
  have nonneg1 : 0 ≤ p 1 := by nlinarith [hf.1,hf.2.1,Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
  intro i
  fin_cases i
  · change ((0 : ℚ) : ℝ) ≤ p 0 ∧ p 0 ≤ (e : ℝ)
    rw [Rat.cast_zero]
    exact ⟨hf.1,h0.2⟩
  · change ((0 : ℚ) : ℝ) ≤ p 1 ∧ p 1 ≤ (e : ℝ)
    rw [Rat.cast_zero]
    exact ⟨nonneg1,h1.2⟩
  · change ((0 : ℚ) : ℝ) ≤ p 2 ∧ p 2 ≤ (t : ℝ)
    rw [Rat.cast_zero]
    exact ⟨hf.2.2.1,h2.2⟩
  · change ((0 : ℚ) : ℝ) ≤ p 3 ∧ p 3 ≤ (t : ℝ)
    rw [Rat.cast_zero]
    exact ⟨hf.2.2.2,h3.2⟩
  · change ((-t : ℚ) : ℝ) ≤ p 4 ∧ p 4 ≤ (t : ℝ)
    rw [Rat.cast_neg]
    exact h4

theorem strainRoot_contains (ref : Reference) (p : Point) (hp : strainEligible ref p) :
    (strainRoot ref).Mem p := by
  have hb := productBall_in_strainBox (by cases ref <;> norm_num [strainRadiusE]) hp.1 hp.2
  intro i
  have h := hb i
  cases ref <;> fin_cases i <;> norm_num [strainRoot,strainBox,strainRadiusE,strainRadiusT] at h ⊢ <;>
    constructor <;> linarith

theorem ballRoot_contains (p : Point) (hf : folded p) (hp : inProductBall beta beta p) :
    ballRoot.Mem p := productBall_in_strainBox (by norm_num [beta]) hf hp

def _root_.BccSharp.Intervals.Ball.lo (b : Ball) : ℚ := b.mid-b.rad
def _root_.BccSharp.Intervals.Ball.hi (b : Ball) : ℚ := b.mid+b.rad

def ballOf (l u : ℚ) : Ball := ⟨(l+u)/2,(u-l)/2⟩

theorem ballOf_sound {l u : ℚ} {x : ℝ} (h : (l : ℝ) ≤ x ∧ x ≤ (u : ℝ)) :
    (ballOf l u).Contains x := by
  apply (SpecialFunctions.contains_iff_endpoints _ _).mpr
  unfold ballOf
  push_cast
  constructor <;> linarith [h.1,h.2]

def coordinateBall (b : Rectangle) (i : Fin 5) : Ball := ballOf (b.lo i) (b.hi i)
theorem coordinateBall_sound {b : Rectangle} {p : Point} (h : b.Mem p) (i : Fin 5) :
    (coordinateBall b i).Contains (p i) := ballOf_sound (h i)

def sqLower (l u : ℚ) : ℚ := if 0 ≤ l then l^2 else if u ≤ 0 then u^2 else 0
def sqUpper (l u : ℚ) : ℚ := max (l^2) (u^2)

theorem sqLower_sound {l u : ℚ} {x : ℝ} (h : (l : ℝ) ≤ x ∧ x ≤ (u : ℝ)) :
    (sqLower l u : ℝ) ≤ x^2 := by
  unfold sqLower
  split_ifs with hl hu
  · push_cast
    have hl' : 0 ≤ (l : ℝ) := by exact_mod_cast hl
    exact pow_le_pow_left₀ hl' h.1 2
  · push_cast
    have hu' : 0 ≤ -(u : ℝ) := by exact_mod_cast (neg_nonneg.mpr hu)
    simpa using pow_le_pow_left₀ hu' (neg_le_neg h.2) 2
  · simpa using sq_nonneg x

theorem sqUpper_sound {l u : ℚ} {x : ℝ} (h : (l : ℝ) ≤ x ∧ x ≤ (u : ℝ)) :
    x^2 ≤ (sqUpper l u : ℝ) := by
  unfold sqUpper
  push_cast
  by_cases hx : 0 ≤ x
  · exact (pow_le_pow_left₀ hx h.2 2).trans (le_max_right _ _)
  · have hh := pow_le_pow_left₀ (show 0 ≤ -x by linarith) (neg_le_neg h.1) 2
    exact (by simpa using hh : x^2 ≤ (l : ℝ)^2).trans (le_max_left _ _)

def sqBall (a : Ball) : Ball := ballOf (sqLower a.lo a.hi) (sqUpper a.lo a.hi)

theorem sqBall_sound {a : Ball} {x : ℝ} (h : a.Contains x) : (sqBall a).Contains (x^2) := by
  have hs : (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ) := by
    simpa [Ball.lo,Ball.hi] using (SpecialFunctions.contains_iff_endpoints _ _).mp h
  exact ballOf_sound ⟨sqLower_sound hs,sqUpper_sound hs⟩

end BccSharp.Coulomb.BravaisCover
