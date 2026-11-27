import BccSharp.Cover.Stage2Tangents
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

/-! Signed Overlay axial modes, in the indexing of the planar
Poisson formula. The estimates concern this series itself. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BravaisCover DirectRoute
open BccSharp.Intervals (Ball)

def axialTerm (t d phase : ℝ) : ℝ := Real.exp (-t*d)*Real.cos (2*Real.pi*phase)

def sameMode (t w : ℝ) (k : ℤ) : ℝ := axialTerm t |(k : ℝ)| ((k : ℝ)*w)
def crossMode (t w u h : ℝ) (k : ℤ) : ℝ :=
  axialTerm t |(k : ℝ)+h| (u+((k : ℝ)+h)*w)

-- The same-coset row omits zero. For the cross coset the two terms
-- at n are the original k=n and k=-n-1, after simplifying |k+h|.
def axialPair (t w u h : ℝ) (n : ℕ) : ℝ :=
  let s := (n : ℝ)+1
  axialTerm t s (s*w) + axialTerm t s (-s*w) +
    (axialTerm t ((n : ℝ)+h) (u+((n : ℝ)+h)*w) +
      axialTerm t (s-h) (u-(s-h)*w))

def axialSeries (t w u h : ℝ) : ℝ := ∑' n : ℕ, axialPair t w u h n

theorem axialPair_indices (t w u h : ℝ) (h₀ : 0<h) (h₁ : h<1) (n : ℕ) :
    axialPair t w u h n =
      sameMode t w ((n : ℤ)+1)+sameMode t w (-((n : ℤ)+1))+
        (crossMode t w u h n+crossMode t w u h (-((n : ℤ)+1))) := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg _
  have e : -((n : ℝ)+1)+h= -((n : ℝ)+1-h) := by ring
  have plus : (0:ℝ)≤(n : ℝ)+h := by linarith
  have minus : (0:ℝ)≤(n : ℝ)+1-h := by linarith
  have minus' : (0:ℝ)≤(n : ℝ)+1+-h := by linarith
  simp only [axialPair,sameMode,crossMode,Int.cast_add,Int.cast_neg,Int.cast_one,Int.cast_natCast,
    e,abs_neg,abs_of_nonneg (by positivity : 0≤(n : ℝ)+1),abs_of_nonneg plus,
    abs_of_nonneg minus,abs_of_nonneg minus',neg_mul,sub_eq_add_neg]

-- Giving both hyperbolic factors as checked exponentials allows the
-- rational evaluator to use the same exponential kernel as the tail.
def coshExp (z : ℝ) : ℝ := (Real.exp z+Real.exp (-z))/2
def sinhExp (z : ℝ) : ℝ := (Real.exp z-Real.exp (-z))/2

def axialCore (t w u h : ℝ) : ℝ :=
  let δ := h-1/2
  let γ := Real.pi*w
  let φ := 2*Real.pi*(u+w*δ)
  2*Real.exp (-t)*Real.cos (2*γ) +
    2*Real.exp (-t/2)*(coshExp (t*δ)*Real.cos γ*Real.cos φ +
      sinhExp (t*δ)*Real.sin γ*Real.sin φ)

theorem axialPair_zero (t w u h : ℝ) : axialPair t w u h 0=axialCore t w u h := by
  let δ := h-1/2
  let γ := Real.pi*w
  let φ := 2*Real.pi*(u+w*δ)
  have c₁ : 2*Real.pi*(u+h*w)=φ+γ := by dsimp [φ,γ,δ]; ring
  have c₂ : 2*Real.pi*(u-(1-h)*w)=φ-γ := by dsimp [φ,γ,δ]; ring
  have e₁ : -t*h= -t/2+ -(t*δ) := by dsimp [δ]; ring
  have e₂ : -t*(1-h)= -t/2+t*δ := by dsimp [δ]; ring
  have c₀ : 2*Real.pi*(-(1:ℝ)*w)= -(2*γ) := by dsimp [γ]; ring
  have c : 2*Real.pi*w=2*γ := by dsimp [γ]; ring
  change axialPair t w u h 0 = 2*Real.exp (-t)*Real.cos (2*γ) +
    2*Real.exp (-t/2)*(coshExp (t*δ)*Real.cos γ*Real.cos φ +
      sinhExp (t*δ)*Real.sin γ*Real.sin φ)
  simp only [axialPair, axialTerm, Nat.cast_zero, zero_add, one_mul, mul_one,
    c₀, c, Real.cos_neg, c₁, c₂, e₁, e₂, Real.exp_add,
    Real.cos_add, Real.cos_sub, coshExp, sinhExp]
  ring

theorem exp_add_nat (t d : ℝ) (n : ℕ) :
    Real.exp (-t*((n : ℝ)+d))=Real.exp (-t*d)*(Real.exp (-t))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, show -t*((n : ℝ)+1+d)= -t*((n : ℝ)+d)+ -t by ring,
      Real.exp_add, ih, pow_succ, mul_assoc]

private theorem axialTerm_bound {t t₀ d q phase : ℝ} {n : ℕ}
    (ht₀ : 0≤t₀) (ht : t₀≤t) (hq : 0≤q) (hd : (n : ℝ)+q≤d) :
    |axialTerm t d phase|≤Real.exp (-t₀*q)*(Real.exp (-t₀))^n := by
  have hq' : 0≤(n : ℝ)+q := add_nonneg (Nat.cast_nonneg _) hq
  have e : -t*d≤ -t₀*((n : ℝ)+q) := by
    have := (mul_le_mul_of_nonneg_left hd ht₀).trans
      (mul_le_mul_of_nonneg_right ht (hq'.trans hd))
    linarith only [this]
  rw [← exp_add_nat, axialTerm, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (-t*d)*1 := mul_le_mul_of_nonneg_left (abs_le.mpr
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (Real.exp_pos _).le
    _ ≤ _ := by simpa only [mul_one] using Real.exp_le_exp.mpr e

private theorem abs_add_four (a b c d : ℝ) :
    |a+b+(c+d)|≤|a|+|b|+(|c|+|d|) :=
  (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))

def axialNumerator (t η : ℝ) : ℝ := 2*Real.exp (-2*t)+2*Real.exp (-(1+η)*t)

def axialTail (t η : ℝ) : ℝ := axialNumerator t η/(1-Real.exp (-t))

theorem abs_sum_bound {ι : Type*} {f g : ι → ℝ} (hg : Summable g)
    (bound : ∀ n, |f n|≤g n) : Summable f ∧ |∑' n, f n|≤∑' n, g n := by
  have hf : Summable f := hg.of_norm_bounded (fun n => by rw [Real.norm_eq_abs]; exact bound n)
  have up := hf.tsum_le_tsum (fun n => (le_abs_self _).trans (bound n)) hg
  have down := hf.neg.tsum_le_tsum (fun n => (neg_le_abs _).trans (bound n)) hg
  rw [tsum_neg] at down
  exact ⟨hf,abs_le.mpr ⟨neg_le.mp down,up⟩⟩

private theorem axialPair_succ_bound {t t₀ η w u h : ℝ} (ht₀ : 0≤t₀) (ht : t₀≤t)
    (hη : 0≤η) (hh₀ : η≤h) (hh₁ : h≤1-η) (n : ℕ) :
    |axialPair t w u h (n+1)|≤axialNumerator t₀ η*(Real.exp (-t₀))^n := by
  have same (phase : ℝ) : |axialTerm t ((↑(n+1) : ℝ)+1) phase| ≤
      Real.exp (-t₀*2)*(Real.exp (-t₀))^n :=
    axialTerm_bound ht₀ ht (by norm_num) (by push_cast; linarith)
  have plus (phase : ℝ) : |axialTerm t ((↑(n+1) : ℝ)+h) phase| ≤
      Real.exp (-t₀*(1+η))*(Real.exp (-t₀))^n :=
    axialTerm_bound ht₀ ht (by linarith) (by push_cast; linarith)
  have minus (phase : ℝ) : |axialTerm t ((↑(n+1) : ℝ)+1-h) phase| ≤
      Real.exp (-t₀*(1+η))*(Real.exp (-t₀))^n :=
    axialTerm_bound ht₀ ht (by linarith) (by push_cast; linarith)
  unfold axialPair
  refine (abs_add_four _ _ _ _).trans ((add_le_add (add_le_add (same _) (same _))
    (add_le_add (plus _) (minus _))).trans_eq ?_)
  unfold axialNumerator
  rw [show -t₀*2= -2*t₀ by ring, show -t₀*(1+η)= -(1+η)*t₀ by ring]
  ring

theorem axialTail_sound {t t₀ : ℝ} (w u h η : ℝ) (ht₀ : 0<t₀) (ht : t₀≤t)
    (hη : 0≤η) (hh₀ : η≤h) (hh₁ : h≤1-η) :
    Summable (axialPair t w u h) ∧ |axialSeries t w u h-axialCore t w u h|≤axialTail t₀ η := by
  let r := Real.exp (-t₀)
  have hr : 0≤ r := (Real.exp_pos _).le
  have hr₁ : r<1 := by simpa [r] using (Real.exp_lt_exp.mpr (neg_lt_zero.mpr ht₀))
  let F := fun n : ℕ => axialPair t w u h (n+1)
  let G := fun n : ℕ => axialNumerator t₀ η*r^n
  have hg : Summable G := (summable_geometric_of_lt_one hr hr₁).mul_left _
  have bound (n : ℕ) : |F n|≤G n := axialPair_succ_bound ht₀.le ht hη hh₀ hh₁ n
  obtain ⟨hf,absolute⟩ := abs_sum_bound hg bound
  have hs : Summable (axialPair t w u h) := (summable_nat_add_iff 1).mp hf
  refine ⟨hs, ?_⟩
  have split : axialPair t w u h 0+(∑' n, F n)=axialSeries t w u h := by
    simpa only [axialSeries, F, Finset.sum_range_one] using hs.sum_add_tsum_nat_add 1
  rw [axialPair_zero] at split
  rw [← split, add_sub_cancel_left]
  have e : (∑' n, G n)=axialTail t₀ η := by
    unfold G axialTail
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr₁, div_eq_mul_inv]
  exact absolute.trans_eq e

-- Also used by the radial shell estimate. This restores the four
-- retained terms to the absolute majorant at exactly the same spacing.
def axialAbsPair (t w u h : ℝ) (n : ℕ) : ℝ :=
  let s := (n : ℝ)+1
  |axialTerm t s (s*w)|+|axialTerm t s (-s*w)|+
    (|axialTerm t ((n : ℝ)+h) (u+((n : ℝ)+h)*w)|+|axialTerm t (s-h) (u-(s-h)*w)|)

theorem axialAbsPair_nonneg (t w u h : ℝ) (n : ℕ) : 0≤axialAbsPair t w u h n := by
  unfold axialAbsPair
  positivity

theorem axialPair_le_absPair (t w u h : ℝ) (n : ℕ) : |axialPair t w u h n|≤axialAbsPair t w u h n :=
  abs_add_four _ _ _ _

theorem axialAbsPair_bound {t t₀ η : ℝ} (w u h : ℝ) (ht₀ : 0≤t₀) (ht : t₀≤t) (hη : 0≤η)
    (hh₀ : η≤h) (hh₁ : h≤1-η) (n : ℕ) :
    axialAbsPair t w u h n≤
      (2*Real.exp (-t₀)+2*Real.exp (-t₀*η))*(Real.exp (-t₀))^n := by
  have same (phase : ℝ) : |axialTerm t ((n : ℝ)+1) phase| ≤
      Real.exp (-t₀)*(Real.exp (-t₀))^n := by
    simpa only [mul_one] using axialTerm_bound (n := n) (q := 1) ht₀ ht zero_le_one le_rfl (phase := phase)
  have cross₁ (phase : ℝ) : |axialTerm t ((n : ℝ)+h) phase| ≤
      Real.exp (-t₀*η)*(Real.exp (-t₀))^n :=
    axialTerm_bound ht₀ ht hη (by linarith)
  have cross₂ (phase : ℝ) : |axialTerm t ((n : ℝ)+1-h) phase| ≤
      Real.exp (-t₀*η)*(Real.exp (-t₀))^n :=
    axialTerm_bound ht₀ ht hη (by linarith)
  unfold axialAbsPair
  refine (add_le_add (add_le_add (same _) (same _)) (add_le_add (cross₁ _) (cross₂ _))).trans_eq ?_
  ring

theorem axialAll_sound {t t₀ : ℝ} (w u h η : ℝ) (ht₀ : 0<t₀) (ht : t₀≤t)
    (hη : 0≤η) (hh₀ : η≤h) (hh₁ : h≤1-η) :
    |axialSeries t w u h|≤(2*Real.exp (-t₀)+2*Real.exp (-t₀*η))/(1-Real.exp (-t₀)) := by
  have hr : 0≤Real.exp (-t₀) := (Real.exp_pos _).le
  have hr₁ : Real.exp (-t₀)<1 := by
    simpa using (Real.exp_lt_exp.mpr (neg_lt_zero.mpr ht₀))
  let a := 2*Real.exp (-t₀)+2*Real.exp (-t₀*η)
  have hg : Summable (fun n : ℕ => a*(Real.exp (-t₀))^n) :=
    (summable_geometric_of_lt_one hr hr₁).mul_left _
  unfold axialSeries
  refine (abs_sum_bound hg (fun n => (axialPair_le_absPair t w u h n).trans
    (axialAbsPair_bound w u h ht₀.le ht hη hh₀ hh₁ n))).2.trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr₁, div_eq_mul_inv]

private theorem sum_int_omit_zero (f : ℤ → ℝ) (hf : f 0=0)
    (pos : Summable (fun n : ℕ => f ((n : ℤ)+1)))
    (neg : Summable (fun n : ℕ => f (-((n : ℤ)+1)))) :
    HasSum f ((∑' n : ℕ, f ((n : ℤ)+1))+(∑' n : ℕ, f (-((n : ℤ)+1)))) := by
  have all : Summable (fun n : ℕ => f n) := (summable_nat_add_iff 1).mp (by
    simpa only [Nat.cast_add,Nat.cast_one] using pos)
  have shift : (∑' n : ℕ, f ((n : ℤ)+1))=∑' n : ℕ, f n := by
    simpa only [Finset.sum_range_one,Nat.cast_add,Nat.cast_one,Nat.cast_zero,hf,zero_add] using
      all.sum_add_tsum_nat_add 1
  have h : HasSum (fun n : ℕ => f n) (∑' n : ℕ, f ((n : ℤ)+1)) := by
    rw [shift]
    exact all.hasSum
  exact HasSum.of_nat_of_neg_add_one (f := f) h neg.hasSum

theorem axialSeries_integer (t w u h η : ℝ) (ht : 0<t) (he : 0<η)
    (hl : η≤h) (hu : h≤1-η) :
    Summable (fun k : ℤ => if k=0 then 0 else sameMode t w k) ∧
    Summable (crossMode t w u h) ∧
    axialSeries t w u h=(∑' k : ℤ, if k=0 then 0 else sameMode t w k)+
      (∑' k : ℤ, crossMode t w u h k) := by
  let S (k : ℤ) := if k=0 then 0 else sameMode t w k
  let C := crossMode t w u h
  let sPos (n : ℕ) := S ((n : ℤ)+1)
  let sNeg (n : ℕ) := S (-((n : ℤ)+1))
  let cPos (n : ℕ) := C n
  let cNeg (n : ℕ) := C (-((n : ℤ)+1))
  have h₀ := he.trans_le hl
  have h₁ : h<1 := by linarith
  have rhs (n : ℕ) : axialPair t w u h n=sPos n+sNeg n+(cPos n+cNeg n) := by
    have nz : (n : ℤ)+1≠0 := by omega
    simpa only [sPos,sNeg,S,ite_eq_right nz,neg_eq_zero,C,cPos,cNeg] using axialPair_indices t w u h h₀ h₁ n
  let G (n : ℕ) := (2*Real.exp (-t)+2*Real.exp (-t*η))*(Real.exp (-t))^n
  have hg : Summable G := (summable_geometric_of_lt_one (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))).mul_left _
  have bound (n : ℕ) : |sPos n|+|sNeg n|+(|cPos n|+|cNeg n|)≤G n := by
    have nz : (n : ℤ)+1≠0 := by omega
    have ds : (0:ℝ)≤(n : ℝ)+1 := by positivity
    have d₁ : (0:ℝ)≤(n : ℝ)+h := by positivity
    have d₂ : (0:ℝ)≤(n : ℝ)+1-h := by linarith
    have d₂' : (0:ℝ)≤(n : ℝ)+1+-h := by linarith
    have e : -((n : ℝ)+1)+h= -((n : ℝ)+1-h) := by ring
    simpa only [G,sPos,sNeg,cPos,cNeg,S,C,ite_eq_right nz,neg_eq_zero,sameMode,crossMode,
      Int.cast_add,Int.cast_one,Int.cast_neg,Int.cast_natCast,axialAbsPair,e,abs_neg,
      abs_of_nonneg ds,abs_of_nonneg d₁,abs_of_nonneg d₂,abs_of_nonneg d₂',neg_mul,
      sub_eq_add_neg] using
      axialAbsPair_bound w u h ht.le le_rfl he.le hl hu n
  have hsPos : Summable sPos := hg.of_norm_bounded (fun n => by
    rw [Real.norm_eq_abs]
    linarith only [bound n,abs_nonneg (sNeg n),abs_nonneg (cPos n),abs_nonneg (cNeg n)])
  have hsNeg : Summable sNeg := hg.of_norm_bounded (fun n => by
    rw [Real.norm_eq_abs]
    linarith only [bound n,abs_nonneg (sPos n),abs_nonneg (cPos n),abs_nonneg (cNeg n)])
  have hcPos : Summable cPos := hg.of_norm_bounded (fun n => by
    rw [Real.norm_eq_abs]
    linarith only [bound n,abs_nonneg (sPos n),abs_nonneg (sNeg n),abs_nonneg (cNeg n)])
  have hcNeg : Summable cNeg := hg.of_norm_bounded (fun n => by
    rw [Real.norm_eq_abs]
    linarith only [bound n,abs_nonneg (sPos n),abs_nonneg (sNeg n),abs_nonneg (cPos n)])
  have s := sum_int_omit_zero S (by simp [S]) hsPos hsNeg
  have c := HasSum.of_nat_of_neg_add_one (f := C) hcPos.hasSum hcNeg.hasSum
  refine ⟨s.summable,c.summable,?_⟩
  unfold axialSeries
  simp_rw [rhs]
  rw [(hsPos.add hsNeg).tsum_add (hcPos.add hcNeg),hsPos.tsum_add hsNeg,hcPos.tsum_add hcNeg]
  exact congrArg₂ (· + ·) s.tsum_eq.symm c.tsum_eq.symm

end BccSharp.Coulomb.CompactCover.OverlayPlanar
