import BccSharp.Lattice.LocalMetricJet
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

/-! Exact max-norm shell enumeration for Lattice. The expansion
partitions the entire omitted cube complement, with no index truncation
inside a shell. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover
open BccSharp
open BccSharp.Intervals (Ball)
open Constants.HighPrecision

def localTriple : LatticeTails.Triple ≃ IntVec where
  toFun z := ![z.1,z.2.1,z.2.2]
  invFun n := (n 0,n 1,n 2)
  left_inv z := by rcases z with ⟨a,b,c⟩; rfl
  right_inv n := by ext i; fin_cases i <;> rfl

def cubeRadius (n : IntVec) : ℕ := max (n 0).natAbs (max (n 1).natAbs (n 2).natAbs)

def localCube (r : ℕ) : Finset IntVec := (LatticeTails.cube r).map localTriple.toEmbedding

@[simp] theorem mem_localCube (n : IntVec) (r : ℕ) : n ∈ localCube r ↔ cubeRadius n ≤ r := by
  simp only [localCube, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨z,hz,rfl⟩
    simpa [cubeRadius, localTriple, max_le_iff] using (LatticeTails.mem_cube r z).mp hz
  · intro h
    refine ⟨localTriple.symm n, ?_, localTriple.apply_symm_apply n⟩
    exact (LatticeTails.mem_cube _ _).mpr (by simpa [cubeRadius, localTriple, max_le_iff] using h)

def localShell (r : ℕ) : Finset IntVec := localCube r \ localCube (r-1)

theorem mem_localShell (n : IntVec) {r : ℕ} (hr : 0 < r) : n ∈ localShell r ↔ cubeRadius n=r := by
  simp only [localShell, Finset.mem_sdiff, mem_localCube]
  omega

theorem card_localCube (r : ℕ) : (localCube r).card=(2*r+1)^3 := by
  have side : (Finset.Icc (-(r : ℤ)) (r : ℤ)).card=2*r+1 := by
    rw [Int.card_Icc]; omega
  simp only [localCube, Finset.card_map, LatticeTails.cube, Finset.card_product, side]
  ring

theorem card_localShell_add_one (r : ℕ) : (localShell (r+1)).card=24*(r+1)^2+2 := by
  have sub : localCube r ⊆ localCube (r+1) := by
    intro n hn; exact (mem_localCube _ _).mpr ((mem_localCube _ _).mp hn |>.trans (Nat.le_succ _))
  simp only [localShell, Nat.add_sub_cancel] at *
  have h := Finset.card_sdiff_add_card_eq_card sub
  have e : (localCube (r+1) \ localCube r).card + (2*r+1)^3=(2*(r+1)+1)^3 := by
    simpa only [card_localCube] using h
  have f : (24*(r+1)^2+2)+(2*r+1)^3=(2*(r+1)+1)^3 := by ring
  omega

private theorem shellCount_le (r : ℕ) : ((localShell (r+1)).card : ℝ) ≤ 26*((r+1 : ℕ) : ℝ)^2 := by
  rw [card_localShell_add_one]
  push_cast
  nlinarith only [Nat.cast_nonneg (α := ℝ) r, sq_nonneg (r : ℝ)]

def shellTailEquiv (r : ℕ) : {n // n ∉ localCube r} ≃ (Σ k : ℕ, ↥(localShell (r+1+k))) where
  toFun n := ⟨cubeRadius n.val-(r+1), ⟨n.val, by
    have h := Nat.lt_of_not_ge ((mem_localCube n.val r).not.mp n.property)
    apply (mem_localShell _ (by omega)).mpr
    omega⟩⟩
  invFun x := ⟨x.2.val, by
    have h := (mem_localShell _ (by omega)).mp x.2.property
    exact (mem_localCube _ _).not.mpr (by omega)⟩
  left_inv n := rfl
  right_inv x := by
    obtain ⟨k,n,hn⟩ := x
    have h := (mem_localShell _ (by omega)).mp hn
    have ek : cubeRadius n-(r+1)=k := by omega
    exact Sigma.subtype_ext ek rfl

/-- A per-mode envelope times the exact shell count controls the entire
omitted real sum in absolute value, and also proves its summability. -/
theorem shellTail_sound (r : ℕ) (f : IntVec → ℝ) (envelope : ℕ → ℝ)
    (nn : ∀ k, 0 ≤ envelope k)
    (bound : ∀ k n, n ∈ localShell (r+1+k) → |f n| ≤ envelope k)
    (s : Summable (fun k => ((localShell (r+1+k)).card : ℝ)*envelope k)) :
    Summable f ∧ |∑' n : {n // n ∉ localCube r}, f n.val| ≤
      ∑' k, ((localShell (r+1+k)).card : ℝ)*envelope k := by
  have fold (k : ℕ) : (∑' _n : ↥(localShell (r+1+k)), envelope k) =
      ((localShell (r+1+k)).card : ℝ)*envelope k := by
    simp [tsum_fintype, nsmul_eq_mul]
  have hs : Summable (fun x : (Σ k : ℕ, ↥(localShell (r+1+k))) => envelope x.1) :=
    (summable_sigma_of_nonneg (fun x : (Σ k : ℕ, ↥(localShell (r+1+k))) => nn x.1)).mpr
      ⟨fun _ => Summable.of_finite, by simpa only [fold] using s⟩
  have hF : Summable (fun x : (Σ k : ℕ, ↥(localShell (r+1+k))) => f x.2.val) :=
    hs.of_norm_bounded (fun x => by rw [Real.norm_eq_abs]; exact bound x.1 x.2.val x.2.property)
  have hF' : Summable (fun n : {n // n ∉ localCube r} => f n.val) :=
    (shellTailEquiv r).symm.summable_iff.mp hF
  refine ⟨summable_of_finset_compl (localCube r) f hF', ?_⟩
  have eq : (∑' x : (Σ k : ℕ, ↥(localShell (r+1+k))), f x.2.val) =
      ∑' n : {n // n ∉ localCube r}, f n.val :=
    (shellTailEquiv r).symm.tsum_eq (fun n : {n // n ∉ localCube r} => f n.val)
  rw [← eq, abs_le]
  have up : (∑' x : (Σ k : ℕ, ↥(localShell (r+1+k))), f x.2.val) ≤
      ∑' x : (Σ k : ℕ, ↥(localShell (r+1+k))), envelope x.1 :=
    hF.tsum_le_tsum (fun x => (le_abs_self _).trans (bound x.1 x.2.val x.2.property)) hs
  have down : (∑' x : (Σ k : ℕ, ↥(localShell (r+1+k))), -f x.2.val) ≤
      ∑' x : (Σ k : ℕ, ↥(localShell (r+1+k))), envelope x.1 :=
    hF.neg.tsum_le_tsum (fun x => (neg_le_abs _).trans (bound x.1 x.2.val x.2.property)) hs
  rw [tsum_neg] at down
  have e : (∑' x : (Σ k : ℕ, ↥(localShell (r+1+k))), envelope x.1) =
      ∑' k, ((localShell (r+1+k)).card : ℝ)*envelope k := by
    rw [hs.tsum_sigma]
    exact tsum_congr fold
  rw [e] at up down
  exact ⟨neg_le.mp down, up⟩

def shellEnvelope (a k₁ k₂ : ℝ) (n : ℕ) : ℝ :=
  (5/a)*(k₂+k₁^2*(n : ℝ)^2)*Real.exp (-a*(n : ℝ)^2)

theorem modeHessian_shell_bound (kind : KernelKind) {a x g₁ g₂ h k₁ k₂ : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : 0 < n) (hx : 1 ≤ x) (lo : a*(n : ℝ)^2 ≤ x)
    (g₁b : |g₁| ≤ k₁*(n : ℝ)^2) (g₂b : |g₂| ≤ k₁*(n : ℝ)^2)
    (hb : |h| ≤ k₂*(n : ℝ)^2) (p₁ : 0 ≤ k₁) (p₂ : 0 ≤ k₂) :
    |kernelCurvature kind x*g₁*g₂+kernelSlope kind x*h| ≤ shellEnvelope a k₁ k₂ n := by
  let z : ℝ := (n : ℝ)^2
  have hz : 0 < z := by dsimp [z]; exact sq_pos_of_pos (by exact_mod_cast hn)
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have ex : Real.exp (-x) ≤ Real.exp (-a*z) :=
    Real.exp_le_exp.mpr (by rw [neg_mul]; exact neg_le_neg lo)
  have e : Real.exp (-x)/x ≤ Real.exp (-a*z)/(a*z) :=
    (div_le_div_of_nonneg_right ex hx'.le).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos ha hz) lo)
  obtain ⟨hs,hc⟩ := kernelDerivative_bounds kind hx
  have h₅ : 2*Real.exp (-x)/x ≤ 5*Real.exp (-x)/x := by
    apply div_le_div_of_nonneg_right _ hx'.le; linarith [Real.exp_pos (-x)]
  have B₅ : 5*Real.exp (-x)/x ≤ 5*(Real.exp (-a*z)/(a*z)) := by
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left e (by norm_num : (0 : ℝ) ≤ 5)
  have g := mul_le_mul g₁b g₂b (abs_nonneg _) (by positivity : 0 ≤ k₁*z)
  calc
    _ ≤ |kernelCurvature kind x*g₁*g₂| + |kernelSlope kind x*h| := abs_add_le _ _
    _ ≤ (5*(Real.exp (-a*z)/(a*z)))*((k₁*z)*(k₁*z)) + (5*(Real.exp (-a*z)/(a*z)))*(k₂*z) := by
      simp only [abs_mul]
      rw [mul_assoc |kernelCurvature kind x|]
      exact add_le_add (mul_le_mul (hc.trans B₅) g (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity))
        (mul_le_mul (hs.trans (h₅.trans B₅)) hb (abs_nonneg _) (by positivity))
    _ = _ := by unfold shellEnvelope; change _ = (5/a)*(k₂+k₁^2*z)*Real.exp (-a*z)
                field_simp [ha.ne',hz.ne'] <;> ring

def shellTailC₂ (a k₂ : ℚ) : ℚ := 130*k₂/a
def shellTailC₄ (a k₁ : ℚ) : ℚ := 130*k₁^2/a

theorem shellTail_gaussian (r : ℕ) (f : IntVec → ℝ) (a k₁ k₂ : ℝ) (ha : 0 < a)
    (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂)
    (perMode : ∀ k n, n ∈ localShell (r+1+k) → |f n| ≤ shellEnvelope a k₁ k₂ (r+1+k))
    (s : Summable (fun k => gaussianShell a (130*k₂/a) (130*k₁^2/a) (r+1+k))) :
    Summable f ∧ |∑' n : {n // n ∉ localCube r}, f n.val| ≤
      ∑' k, gaussianShell a (130*k₂/a) (130*k₁^2/a) (r+1+k) := by
  have nn (k : ℕ) : 0 ≤ shellEnvelope a k₁ k₂ (r+1+k) := by unfold shellEnvelope; positivity
  have sh (k : ℕ) : ((localShell (r+1+k)).card : ℝ)*shellEnvelope a k₁ k₂ (r+1+k) ≤
      gaussianShell a (130*k₂/a) (130*k₁^2/a) (r+1+k) := by
    have e := shellCount_le (r+k)
    rw [show r+k+1=r+1+k by omega] at e
    refine (mul_le_mul_of_nonneg_right e (nn k)).trans_eq ?_
    unfold shellEnvelope gaussianShell
    ring
  have h := Summable.of_nonneg_of_le (fun k => mul_nonneg (Nat.cast_nonneg _) (nn k)) sh s
  obtain ⟨hs, hb⟩ := shellTail_sound r f _ nn perMode h
  exact ⟨hs,hb.trans (h.tsum_le_tsum sh s)⟩

structure LocalTailWitness where
  extra : ℕ
  initial : ℕ → ExpBounds.Witness
  remainder : RemainderWitness

def localTailCheck (w : LocalTailWitness) (r : ℕ) (a c₂ c₄ : ℚ) : Bool :=
  decide (∀ k : Fin w.extra, (w.initial k).check (edgeArgument a (r+1+k))=true) &&
    remainderCheck w.remainder a c₂ c₄ (r+w.extra)

def localTailUpper (w : LocalTailWitness) (r : ℕ) (c₂ c₄ : ℚ) : ℚ :=
  (∑ k ∈ Finset.range w.extra, (c₂*((r+1+k : ℕ) : ℚ)^2+c₄*((r+1+k : ℕ) : ℚ)^4)*(w.initial k).result.hi) +
    remainderUpper w.remainder c₂ c₄ (r+w.extra)

theorem localTailUpper_sound (w : LocalTailWitness) (r : ℕ) (a c₂ c₄ : ℚ)
    (ok : localTailCheck w r a c₂ c₄=true) :
    Summable (fun k => gaussianShell (a : ℝ) (c₂ : ℝ) (c₄ : ℝ) (r+1+k)) ∧
    (∑' k, gaussianShell (a : ℝ) (c₂ : ℝ) (c₄ : ℝ) (r+1+k)) ≤ (localTailUpper w r c₂ c₄ : ℝ) := by
  obtain ⟨firstOK, tailOK⟩ := Bool.and_eq_true_iff.mp ok
  let f (k : ℕ) := gaussianShell (a : ℝ) (c₂ : ℝ) (c₄ : ℝ) (r+1+k)
  have hs := remainderUpper_sound w.remainder a c₂ c₄ (r+w.extra) tailOK
  have eq (k : ℕ) : r+1+(k+w.extra)=r+w.extra+1+k := by omega
  have h : Summable f := (summable_nat_add_iff w.extra).mp (by simpa [f,eq] using hs.1)
  refine ⟨h,?_⟩
  have flags : (0 : ℝ) ≤ c₂ ∧ (0 : ℝ) ≤ c₄ := by
    have pos : 0 ≤ a ∧ 0 ≤ c₂ ∧ 0 ≤ c₄ ∧ 0< r+w.extra ∧ ratioUpper w.remainder (r+w.extra)<1 :=
      of_decide_eq_true ((Bool.and_eq_true_iff.mp tailOK).1)
    exact ⟨by exact_mod_cast pos.2.1, by exact_mod_cast pos.2.2.1⟩
  have fin : (∑ k ∈ Finset.range w.extra, f k) ≤
      ∑ k ∈ Finset.range w.extra,
        ((c₂ : ℝ)*((r+1+k : ℕ) : ℝ)^2+(c₄ : ℝ)*((r+1+k : ℕ) : ℝ)^4)*((w.initial k).result.hi : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    have h := (of_decide_eq_true firstOK : ∀ k : Fin w.extra,
      (w.initial k).check (edgeArgument a (r+1+k))=true) ⟨k,Finset.mem_range.mp hk⟩
    have e := ExpBounds.Witness.sound h
      (Ball.contains_exact (-a*((r+1+k : ℕ) : ℚ)^2))
    have u := ((SpecialFunctions.contains_iff_endpoints _ _).mp e).2
    have u' : Real.exp (-(a : ℝ)*((r+1+k : ℕ) : ℝ)^2) ≤ ((w.initial k).result.hi : ℝ) := by
      have hc : (((-a*((r+1+k : ℕ) : ℚ)^2 : ℚ)) : ℝ) = -(a : ℝ)*((r+1+k : ℕ) : ℝ)^2 := by
        push_cast; ring
      rw [hc] at u
      simpa only [Ball.hi, Rat.cast_add] using u
    exact mul_le_mul_of_nonneg_left u'
      (add_nonneg (mul_nonneg flags.1 (by positivity)) (mul_nonneg flags.2 (by positivity)))
  have shift : (∑' k, f (k+w.extra)) ≤ (remainderUpper w.remainder c₂ c₄ (r+w.extra) : ℝ) := by
    simpa [f,eq] using hs.2
  change (∑' k, f k) ≤ _
  rw [← h.sum_add_tsum_nat_add w.extra]
  simpa [localTailUpper] using add_le_add fin shift

theorem cubeRadius_coord (n : IntVec) (i : Fin 3) : |castVec n i| ≤ (cubeRadius n : ℝ) := by
  have h : (n i).natAbs ≤ cubeRadius n := by
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have e : |castVec n i| = ((n i).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]; rfl
  rw [e]
  exact_mod_cast h

theorem cubeRadius_sq_le (n : IntVec) : (cubeRadius n : ℝ)^2 ≤ sq (castVec n) := by
  have h (i : Fin 3) : |castVec n i|^2 ≤ sq (castVec n) := by
    rw [sq_abs, sq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have eq (i : Fin 3) : ((n i).natAbs : ℝ)=|castVec n i| := by simp [castVec, Int.natCast_natAbs]
  unfold cubeRadius
  push_cast
  rw [eq,eq,eq]
  rcases le_total |castVec n 1| |castVec n 2| with h₁ | h₁
  · rw [max_eq_right h₁]; rcases le_total |castVec n 0| |castVec n 2| with h₂ | h₂
    · rw [max_eq_right h₂]; exact h 2
    · rw [max_eq_left h₂]; exact h 0
  · rw [max_eq_left h₁]; rcases le_total |castVec n 0| |castVec n 1| with h₂ | h₂
    · rw [max_eq_right h₂]; exact h 1
    · rw [max_eq_left h₂]; exact h 0

private theorem absQuad_bound (B : Fin 3 → Fin 3 → Ball) (F : Mat)
    (entry : ∀ i j, (B i j).Contains (F i j)) (n : IntVec) :
    |hessianQuadratic F (castVec n)| ≤ (∑ i, ∑ j, (absUpper (B i j) : ℝ))*(cubeRadius n : ℝ)^2 := by
  unfold hessianQuadratic
  calc
    _ ≤ ∑ i, |∑ j, F i j*castVec n i*castVec n j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (absUpper (B i j) : ℝ)*(cubeRadius n : ℝ)^2 := by
      refine Finset.sum_le_sum (fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_)
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul, pow_two, mul_assoc]
      exact mul_le_mul (absUpper_sound (entry i j))
        (mul_le_mul (cubeRadius_coord n i) (cubeRadius_coord n j) (abs_nonneg _) (Nat.cast_nonneg _))
        (by positivity) ((abs_nonneg _).trans (absUpper_sound (entry i j)))
    _ = _ := by simp [Finset.sum_mul]

def coefficient₁ (J : Fin 3 → Fin 3 → StrainJet Ball) (i : Fin 5) : ℚ :=
  ∑ k, ∑ l, absUpper ((J k l).gradient i)

def coefficient₂ (J : Fin 3 → Fin 3 → StrainJet Ball) (i j : Fin 5) : ℚ :=
  ∑ k, ∑ l, absUpper ((J k l).hessian i j)

def shiftedIndexMetric (J : Fin 3 → Fin 3 → StrainJet Ball) (a : ℚ) : MetricBalls :=
  fun i j => (J i j).value.sub (Ball.exact (if i=j then a else 0))

def exponentCheck (J : Fin 3 → Fin 3 → StrainJet Ball) (a : ℚ) (f : LdlWitness 3) : Bool :=
  decide (0<a) && ldlCheck (shiftedIndexMetric J a) f

private theorem rat_cast_ite (c : Prop) [Decidable c] (x y : ℚ) :
    (((if c then x else y : ℚ)) : ℝ) = if c then (x : ℝ) else (y : ℝ) := by
  split_ifs <;> rfl

theorem exponentCheck_sound (ref : Reference) (dual : Bool) (b : Rectangle)
    (w : StrainMetricWitness) (r : RootProposal) (hw : strainMetricCheck ref b w=true)
    (hr : cubeRootCheck r (Ball.exact 2)=true) (a : ℚ) (f : LdlWitness 3)
    (ok : exponentCheck (indexJetBall ref dual b w r) a f=true) (p : Point) (hp : b.Mem p) :
    ∀ n : IntVec, (a : ℝ)*sq (castVec n) ≤ (localArgumentJet ref dual n p).value := by
  intro n
  let J := indexJetBall ref dual b w r
  let M : Mat := fun k l => (indexJet ref dual p k l).value-(if k=l then (a : ℝ) else 0)
  have bd (i j : Fin 3) : (shiftedIndexMetric J a i j).Contains (M i j) := by
    unfold M shiftedIndexMetric
    simpa only [rat_cast_ite, Rat.cast_zero] using Ball.contains_sub
      (indexJetBall_sound ref dual b w r hw hr p hp i j).1 (Ball.contains_exact (if i=j then a else 0))
  by_cases hn : castVec n=0
  · rw [(indexJet_expansion ref dual n p).1, hn]; simp [sq,hessianQuadratic]
  have h := ldlCheck_sound (shiftedIndexMetric J a) f (Bool.and_eq_true_iff.mp ok).2 M bd (castVec n) hn
  rw [(indexJet_expansion ref dual n p).1]
  have expand : hessianQuadratic M (castVec n) =
      hessianQuadratic (fun i j => (indexJet ref dual p i j).value) (castVec n) - (a : ℝ)*sq (castVec n) := by
    simp only [hessianQuadratic, M, sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp [Finset.mul_sum, sq, pow_two, ite_mul, mul_assoc]
  rw [expand] at h
  linarith

theorem derivativeCoefficients_sound (ref : Reference) (dual : Bool) (b : Rectangle)
    (w : StrainMetricWitness) (r : RootProposal) (hw : strainMetricCheck ref b w=true)
    (hr : cubeRootCheck r (Ball.exact 2)=true) (p : Point) (hp : b.Mem p) (n : IntVec) :
    let J := indexJetBall ref dual b w r
    (∀ i, |(localArgumentJet ref dual n p).gradient i| ≤
      (coefficient₁ J i : ℝ)*(cubeRadius n : ℝ)^2) ∧
    (∀ i j, |(localArgumentJet ref dual n p).hessian i j| ≤
      (coefficient₂ J i j : ℝ)*(cubeRadius n : ℝ)^2) := by
  obtain ⟨_,g,h⟩ := indexJet_expansion ref dual n p
  have field := indexJetBall_sound ref dual b w r hw hr p hp
  dsimp only
  constructor
  · intro i; rw [g]; unfold coefficient₁; push_cast
    exact absQuad_bound _ _ (fun k l => (field k l).2.1 i) n
  · intro i j; rw [h]; unfold coefficient₂; push_cast
    exact absQuad_bound _ _ (fun k l => (field k l).2.2 i j) n

def pairCoefficient (J : Fin 3 → Fin 3 → StrainJet Ball) (i j : Fin 5) : ℚ :=
  max (coefficient₁ J i) (coefficient₁ J j)

private theorem absUpper_nonneg (b : Ball) : 0 ≤ absUpper b := (abs_nonneg b.lo).trans (le_max_left _ _)

private theorem pairCoefficient_nonneg (J : Fin 3 → Fin 3 → StrainJet Ball) (i j : Fin 5) :
    0 ≤ pairCoefficient J i j := by
  apply (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => absUpper_nonneg ((J k l).gradient i)))).trans
  exact le_max_left _ _

private theorem coefficient₂_nonneg (J : Fin 3 → Fin 3 → StrainJet Ball) (i j : Fin 5) :
    0 ≤ coefficient₂ J i j :=
  Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => absUpper_nonneg ((J k l).hessian i j)))

def checkedLocalRadius : ℕ := 6

def localFamilyTailCheck (J : Fin 3 → Fin 3 → StrainJet Ball) (a : ℚ)
    (w : Fin 5 → Fin 5 → LocalTailWitness) : Bool :=
  decide (1 ≤ a*(checkedLocalRadius+1 : ℚ)^2) && decide (∀ i j,
    localTailCheck (w i j) checkedLocalRadius a (shellTailC₂ a (coefficient₂ J i j))
      (shellTailC₄ a (pairCoefficient J i j))=true)

def localFamilyTailUpper (J : Fin 3 → Fin 3 → StrainJet Ball) (a : ℚ)
    (w : Fin 5 → Fin 5 → LocalTailWitness) (i j : Fin 5) : ℚ :=
  localTailUpper (w i j) checkedLocalRadius (shellTailC₂ a (coefficient₂ J i j))
    (shellTailC₄ a (pairCoefficient J i j))

theorem localFamilyTail_sound (ref : Reference) (dual : Bool) (b : Rectangle)
    (metric : StrainMetricWitness) (r : RootProposal) (hw : strainMetricCheck ref b metric=true)
    (hr : cubeRootCheck r (Ball.exact 2)=true) (a : ℚ) (f : LdlWitness 3)
    (tail : Fin 5 → Fin 5 → LocalTailWitness)
    (ex : exponentCheck (indexJetBall ref dual b metric r) a f=true)
    (ok : localFamilyTailCheck (indexJetBall ref dual b metric r) a tail=true)
    (p : Point) (hp : b.Mem p) (i j : Fin 5) :
    Summable (fun n => (localModeJet ref dual n p).hessian i j) ∧
    |∑' n : {n // n ∉ localCube checkedLocalRadius}, (localModeJet ref dual n.val p).hessian i j| ≤
      (localFamilyTailUpper (indexJetBall ref dual b metric r) a tail i j : ℝ) := by
  let J := indexJetBall ref dual b metric r
  have ap : 0<a := of_decide_eq_true (Bool.and_eq_true_iff.mp ex).1
  have a' : (0 : ℝ)<a := by exact_mod_cast ap
  obtain ⟨rOK, tOK⟩ := Bool.and_eq_true_iff.mp ok
  have hN : (1 : ℝ) ≤ (a : ℝ)*(checkedLocalRadius+1 : ℝ)^2 := by
    exact_mod_cast (of_decide_eq_true rOK : 1 ≤ a*(checkedLocalRadius+1 : ℚ)^2)
  have t := localTailUpper_sound (tail i j) checkedLocalRadius a (shellTailC₂ a (coefficient₂ J i j))
    (shellTailC₄ a (pairCoefficient J i j)) ((of_decide_eq_true tOK : ∀ i j, _) i j)
  have nn₁ : (0 : ℝ)≤pairCoefficient J i j := by exact_mod_cast pairCoefficient_nonneg J i j
  have nn₂ : (0 : ℝ)≤ coefficient₂ J i j := by exact_mod_cast coefficient₂_nonneg J i j
  have gaussian := shellTail_gaussian checkedLocalRadius (fun n => (localModeJet ref dual n p).hessian i j)
    (a : ℝ) (pairCoefficient J i j) (coefficient₂ J i j) a' nn₁ nn₂
  have mode : ∀ k n, n ∈ localShell (checkedLocalRadius+1+k) →
      |(localModeJet ref dual n p).hessian i j| ≤
        shellEnvelope (a : ℝ) (pairCoefficient J i j) (coefficient₂ J i j) (checkedLocalRadius+1+k) := by
    intro k n hn
    let N := checkedLocalRadius+1+k
    have pos : 0<N := by dsimp [N]; omega
    have size : cubeRadius n=N := (mem_localShell n pos).mp hn
    have nz : n≠0 := by intro eq; simp [eq,cubeRadius] at size; omega
    let A := localArgumentJet ref dual n p
    have low : (a : ℝ)*(N : ℝ)^2 ≤ A.value := by
      rw [← size]
      exact (mul_le_mul_of_nonneg_left (cubeRadius_sq_le n) a'.le).trans
        (exponentCheck_sound ref dual b metric r hw hr a f ex p hp n)
    have big : 1≤A.value := hN.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(checkedLocalRadius+1 : ℝ))
        (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; dsimp only [N]; push_cast; linarith) 2) a'.le).trans low)
    obtain ⟨G,H⟩ := derivativeCoefficients_sound ref dual b metric r hw hr p hp n
    have g (k : Fin 5) (hh : coefficient₁ J k ≤ pairCoefficient J i j) :
        |A.gradient k| ≤ (pairCoefficient J i j : ℝ)*(N : ℝ)^2 := by
      rw [← size]
      exact (G k).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (sq_nonneg _))
    simp only [localModeJet,if_neg nz,StrainJet.realKernel,StrainJet.chain]
    exact modeHessian_shell_bound (localKernelKind dual) a' pos big low
      (g i (le_max_left _ _)) (g j (le_max_right _ _)) (by simpa only [size] using H i j) nn₁ nn₂
  have t' : Summable (fun k => gaussianShell (a : ℝ) (130*(coefficient₂ J i j : ℝ)/a)
      (130*(pairCoefficient J i j : ℝ)^2/a) (checkedLocalRadius+1+k)) := by
    simpa [shellTailC₂,shellTailC₄] using t.1
  obtain ⟨ss, bound⟩ := gaussian mode t'
  exact ⟨ss,bound.trans (by simpa [localFamilyTailUpper,J,shellTailC₂,shellTailC₄] using t.2)⟩

end BccSharp.Coulomb.BravaisCover
