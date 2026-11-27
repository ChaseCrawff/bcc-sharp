import BccSharp.Cover.OverlayLayerCheck
import BccSharp.Lattice.HessianTail

set_option autoImplicit false

/-! Finite triangular theta packet and area tangent. The latter
applies to the same area in the planar and zero-mode terms. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)
open Constants.HighPrecision (RootProposal)

def triangleRoot : RootProposal := Constants.rootPair 2 3 3 2
def triangleNorm : Ball := sc 2 (positiveInv triangleRoot.ball)

def triangleForm (m : Wave) (dual : Bool) : ℤ :=
  m.1^2+(if dual then -(m.1*m.2) else m.1*m.2)+m.2^2

def triangleQ (m : Wave) (dual : Bool) : ℝ := (triangleForm m dual : ℝ)*(2/Real.sqrt 3)
def triangleQBall (m : Wave) (dual : Bool) : Ball := sc (triangleForm m dual : ℚ) triangleNorm

theorem triangleQ_pos (m : Wave) (dual : Bool) (nz : m≠(0,0)) : 0<triangleQ m dual := by
  have h : m.1≠0 ∨ m.2≠0 := by
    by_contra! hz
    exact nz (Prod.ext hz.1 hz.2)
  have hs : 0<(m.1 : ℝ)^2+(m.2 : ℝ)^2 := by
    rcases h with x | y
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (by exact_mod_cast x)) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (by exact_mod_cast y))
  have f : (0:ℝ)<(triangleForm m dual : ℝ) := by
    cases dual <;> simp [triangleForm] <;> nlinarith only [hs,
      sq_nonneg ((m.1 : ℝ)+(m.2 : ℝ)),sq_nonneg ((m.1 : ℝ)-(m.2 : ℝ))]
  exact mul_pos f (by positivity)

private theorem triangleQBall_sound (m : Wave) (dual : Bool)
    (hr : triangleRoot.check (Ball.exact 3)=true) (hi : 0<triangleRoot.ball.lo) :
    (triangleQBall m dual).Contains (triangleQ m dual) := by
  have h := positiveInv_sound hi (RootProposal.sound _ _ 3 (by norm_num) (Ball.contains_exact 3) hr)
  simpa only [triangleQBall,triangleQ,triangleNorm,Rat.cast_ofNat,Rat.cast_intCast,div_eq_mul_inv] using
    sc_sound (triangleForm m dual : ℚ) (sc_sound 2 h)

private def triangleTerm (m : Wave) (dual : Bool) : Option ℚ := directLower (triangleQBall m dual)

def triangleCheck (n : ℕ) : Bool :=
  (triangleRoot.check (Ball.exact 3) && decide (0<triangleRoot.ball.lo)) &&
    (waves n).toList.all (fun m => (triangleTerm m false).isSome && (triangleTerm m true).isSome)

def triangleBound (n : ℕ) : ℚ := -4+2*(∑ m ∈ waves n,
  ((triangleTerm m false).getD 0+(triangleTerm m true).getD 0))

def triangleValue (m : Wave) : ℝ :=
  gKernel (1/2) (Real.pi*triangleQ m false)+gKernel (1/2) (Real.pi*triangleQ m true)

theorem triangleBound_sound (n : ℕ) (ok : triangleCheck n=true) :
    (triangleBound n : ℝ)≤-4+2*(∑ m ∈ waves n, triangleValue m) := by
  simp only [triangleCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨root,inv⟩,terms⟩ := ok
  have term (m : Wave) (nz : m≠(0,0)) (d : Bool) (h : (triangleTerm m d).isSome=true) :
      ((triangleTerm m d).getD 0 : ℝ)≤gKernel (1/2) (Real.pi*triangleQ m d) := by
    cases e : triangleTerm m d with
    | none => simp [e] at h
    | some q =>
      have e' : halfLower (triangleQBall m d)
          (.check (halfProposal (Constants.piInput.mul (triangleQBall m d)).hi))=some q := e
      have bound := halfLower_sound (triangleQBall_sound m d root (of_decide_eq_true inv))
        (triangleQ_pos m d nz) _ _ e'
      simpa only [e,Option.getD_some] using bound
  unfold triangleBound
  push_cast
  refine add_le_add le_rfl ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro m hm
  have nz : m≠(0,0) := by
    intro hz
    subst m
    have bad := (Finset.mem_filter.mp hm).2
    simp at bad
  obtain ⟨p,d⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp terms m (by simpa using hm))
  exact add_le_add (term m nz false p) (term m nz true d)

def triangleTermAll (m : Wave) : ℝ := if m=(0,0) then 0 else triangleValue m
def triangleRegularized : ℝ := -4+(∑' m : Wave, triangleTermAll m)

private theorem kernel_half (x : ℝ) : kernelValue .half x=gKernel (1/2) x := by
  norm_num [kernelValue,KernelKind.power]

private theorem triangleQ_dominates (m : Wave) (d : Bool) :
    LatticeTails.normSq (m.1,m.2,0) ≤ Real.pi*triangleQ m d := by
  have f : (m.1 : ℝ)^2+(m.2 : ℝ)^2≤2*(triangleForm m d : ℝ) := by
    cases d <;> simp [triangleForm] <;> nlinarith only [
      sq_nonneg ((m.1 : ℝ)+(m.2 : ℝ)),sq_nonneg ((m.1 : ℝ)-(m.2 : ℝ))]
  have nn : 0≤(triangleForm m d : ℝ) := by nlinarith only [f,sq_nonneg (m.1 : ℝ),sq_nonneg (m.2 : ℝ)]
  have hs : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs₁ : Real.sqrt 3≤2 := (sq_le_sq₀ hs.le (by norm_num)).mp (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
  have co : 2≤2*Real.pi/Real.sqrt 3 := (le_div_iff₀ hs).mpr (by linarith [Real.pi_gt_three])
  calc
    _ = (m.1 : ℝ)^2+(m.2 : ℝ)^2 := by norm_num [LatticeTails.normSq]
    _ ≤ 2*(triangleForm m d : ℝ) := f
    _ ≤ (2*Real.pi/Real.sqrt 3)*(triangleForm m d : ℝ) := mul_le_mul_of_nonneg_right co nn
    _ = _ := by unfold triangleQ; ring

private theorem triangleTermAll_nonneg (m : Wave) : 0≤triangleTermAll m := by
  by_cases h : m=(0,0)
  · simp [triangleTermAll,h]
  · rw [triangleTermAll,if_neg h]
    rw [triangleValue,← kernel_half,← kernel_half]
    exact add_nonneg (Stage2.value_nonnegative .half (mul_pos Real.pi_pos (triangleQ_pos m false h)))
      (Stage2.value_nonnegative .half (mul_pos Real.pi_pos (triangleQ_pos m true h)))

private theorem triangleTermAll_summable : Summable triangleTermAll := by
  have g := LatticeTails.hasSum_integer_geometric.summable
  have h := (g.mul_of_nonneg g (fun _ => by positivity) (fun _ => by positivity)).mul_left (2:ℝ)
  apply h.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs,abs_of_nonneg (triangleTermAll_nonneg m)]
  by_cases hz : m=(0,0)
  · simp [triangleTermAll,hz]
  have len : 1≤LatticeTails.length (m.1,m.2,0) := by
    by_contra! hbad
    simp only [LatticeTails.length,Int.natAbs_zero,add_zero] at hbad
    have e : m.1.natAbs+m.2.natAbs=0 := by omega
    obtain ⟨e₁,e₂⟩ := Nat.add_eq_zero.mp e
    exact hz (Prod.ext (Int.natAbs_eq_zero.mp e₁) (Int.natAbs_eq_zero.mp e₂))
  have normLower : (1:ℝ)≤LatticeTails.normSq (m.1,m.2,0) := by
    rw [LatticeTails.normSq_eq_square]
    exact_mod_cast len.trans (LatticeTails.length_le_square (m.1,m.2,0))
  have b (d : Bool) : gKernel (1/2) (Real.pi*triangleQ m d)≤LatticeTails.weight (m.1,m.2,0) := by
    have t := normLower.trans (triangleQ_dominates m d)
    have b₀ := (kernelValue_positive_bound .half (zero_lt_one.trans_le t)).2
    rw [kernel_half] at b₀
    exact b₀.trans ((div_le_self (Real.exp_pos _).le t).trans
      ((Real.exp_le_exp.mpr (neg_le_neg (triangleQ_dominates m d))).trans
        (LatticeTails.gaussian_le_weight (m.1,m.2,0))))
  simpa [triangleTermAll,hz,triangleValue,LatticeTails.weight,LatticeTails.length,pow_add,two_mul] using
    add_le_add (b false) (b true)

private theorem triangleTermAll_even (m : Wave) : triangleTermAll (waveNeg m)=triangleTermAll m := by
  have f (d : Bool) : triangleForm (waveNeg m) d=triangleForm m d := by
    cases d <;> simp [triangleForm,waveNeg] <;> ring
  have h : waveNeg m=(0,0) ↔ m=(0,0) := by
    rcases m with ⟨i,j⟩
    simp [waveNeg,Prod.mk.injEq]
  simp only [triangleTermAll,triangleValue,triangleQ,f,h]

theorem triangleRegularized_lower (n : ℕ) (check : triangleCheck n=true) :
    (triangleBound n : ℝ)≤triangleRegularized := by
  have e : ∑ m ∈ waves n, triangleTermAll m = ∑ m ∈ waves n, triangleValue m := by
    apply Finset.sum_congr rfl
    intro m hm
    unfold triangleTermAll
    apply if_neg
    intro h
    subst m
    have impossible := (Finset.mem_filter.mp hm).2
    simp at impossible
  have part := triangleTermAll_summable.sum_le_tsum (waveCube n) (fun m _ => triangleTermAll_nonneg m)
  rw [sum_waveCube n _ (by simp [triangleTermAll]) triangleTermAll_even,e] at part
  exact (triangleBound_sound n check).trans (add_le_add le_rfl part)

def areaRoot (b : Cell) : RootProposal :=
  let c := cBall b
  Constants.rootPair 2 c.lo c.hi (max 2 (c.hi+1))

def areaCoeff (b : Cell) : Ball := sc (2*(1/12+(halfDistance b)^2)) Constants.piInput

-- The stationary point only supplies the anchor proposal. Convexity
-- validates every nonnegative anchor, independently of optimality.
def areaAnchor (b : Cell) (C : ℚ) : ℚ :=
  let d := (areaCoeff b).lo
  let x := -C/(4*d)
  let s := (Constants.rootPair 3 x x (max 2 (x+1))).ball.mid
  min (areaRoot b).ball.hi (max (areaRoot b).ball.lo s)

def areaCheck (b : Cell) (C : ℚ) : Bool :=
  (areaRoot b).check (cBall b) && decide (0≤(areaCoeff b).lo ∧ 0≤areaAnchor b C)

def areaLower (b : Cell) (C : ℚ) : ℚ :=
  let d := (areaCoeff b).lo
  let a := areaAnchor b C
  let s := C+4*d*a^3
  C*a+d*a^4+(sc s ((areaRoot b).ball.sub (Ball.exact a))).lo

def zeroMode (p : Chart) : ℝ := 2*Real.pi*(cReal p)^2*((p 7)^2-p 7+1/3)

theorem quarticTangent {a x d : ℝ} (ha : 0≤a) (hx : 0≤x) (hd : 0≤d) (C : ℝ) :
    C*a+d*a^4+(C+4*d*a^3)*(x-a)≤C*x+d*x^4 := by
  have h : 0≤d*(x-a)^2*(x^2+2*a*x+3*a^2) := by positivity
  linarith only [show C*x+d*x^4-(C*a+d*a^4+(C+4*d*a^3)*(x-a))=
    d*(x-a)^2*(x^2+2*a*x+3*a^2) by ring,h]

theorem areaLower_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (C : ℚ) (ok : areaCheck b C=true) :
    (areaLower b C : ℝ)≤(C : ℝ)*Real.sqrt (cReal p)+zeroMode p := by
  let a := areaAnchor b C
  let d := (areaCoeff b).lo
  have cp : 0≤ cReal p := by
    have g := diagonalsCheck_sound hd
    have hp₀ : (0:ℝ)<p 0 := (show (0:ℝ)<(coord b 0).lo by exact_mod_cast g.1).trans_le (endpoints (coord_sound hp 0)).1
    have hp₁ : (0:ℝ)<p 1 := (show (0:ℝ)<(coord b 1).lo by exact_mod_cast g.2.1).trans_le (endpoints (coord_sound hp 1)).1
    apply inv_nonneg.mpr
    exact mul_nonneg hp₀.le hp₁.le
  obtain ⟨root,pos⟩ := Bool.and_eq_true_iff.mp ok
  have h : 0≤d ∧ 0≤a := of_decide_eq_true pos
  have r := RootProposal.sound _ _ _ cp (cBall_sound hp hd) root
  have l := (endpoints (sc_sound (C+4*d*a^3) (Ball.contains_sub r (Ball.contains_exact a)))).1
  push_cast at l
  have tangent := quarticTangent (show (0:ℝ)≤a by exact_mod_cast h.2)
    (Real.sqrt_nonneg (cReal p)) (show (0:ℝ)≤d by exact_mod_cast h.1) (C : ℝ)
  have aBound : (areaLower b C : ℝ)≤(C : ℝ)*Real.sqrt (cReal p)+(d : ℝ)*(Real.sqrt (cReal p))^4 := by
    unfold areaLower
    push_cast
    exact (add_le_add le_rfl l).trans tangent
  obtain ⟨df,dle⟩ := halfDistance_sound hp
  have dSq : (halfDistance b : ℝ)^2≤(p 7-1/2)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ df (abs_nonneg _)).mpr dle
  have cBound := (endpoints (sc_sound (2*(1/12+(halfDistance b)^2)) Constants.piInput_sound)).1
  push_cast at cBound
  have dBound : (d : ℝ)≤2*Real.pi*((p 7)^2-p 7+1/3) := by
    apply cBound.trans
    calc
      _ ≤ (2*(1/12+(p 7-1/2)^2))*Real.pi :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl dSq) (by norm_num)) Real.pi_pos.le
      _ = _ := by ring
  have sqr : (Real.sqrt (cReal p))^4=(cReal p)^2 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt cp]
  rw [sqr] at aBound
  unfold zeroMode
  convert aBound.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right dBound (sq_nonneg (cReal p)))) using 1
  ring

def numeratorLower (raw : Cell) (cube : ℕ) : ℚ :=
  areaLower (seamCell raw) (triangleBound (cube+1))+(layerBall raw cube).lo

def numeratorCheck (raw : Cell) (cube : ℕ) : Bool :=
  ((triangleCheck (cube+1) && decide (triangleBound (cube+1)<0)) &&
    areaCheck (seamCell raw) (triangleBound (cube+1))) && layerCheck raw cube

def triangularRelaxation (p : Chart) : ℝ :=
  triangleRegularized*Real.sqrt (cReal p)+zeroMode p+layerValue p

theorem numeratorLower_sound {raw : Cell} {p : Chart} (hp : raw.Mem p) (cube : ℕ)
    (ok : numeratorCheck raw cube=true) :
    (numeratorLower raw cube : ℝ)≤triangularRelaxation (seamPoint raw p) := by
  simp only [numeratorCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨triangle,_⟩,area⟩,layer⟩ := ok
  have hd := ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp layer).1).1).1 : diagonalsCheck (seamCell raw)=true)
  have base := areaLower_sound (seamPoint_mem hp) hd (triangleBound (cube+1)) area
  have tri := mul_le_mul_of_nonneg_right (triangleRegularized_lower (cube+1) triangle) (Real.sqrt_nonneg (cReal (seamPoint raw p)))
  have signed := (endpoints (layerBall_sound hp cube layer)).1
  unfold numeratorLower triangularRelaxation
  push_cast
  exact add_le_add (base.trans (add_le_add tri le_rfl)) signed

-- This is the pre-normalization numerical comparison. A physical
-- leaf additionally needs the planar identity and Montgomery's comparison.
theorem triangularRelaxation_aboveFCC {raw : Cell} {p : Chart} (hp : raw.Mem p) (cube : ℕ)
    (ok : numeratorCheck raw cube=true) (hs : cubeRootCheck scaleWitness scaleInput=true)
    (strict : fccHUpper-4<numeratorLower raw cube) :
    2*ac*energy fcc<triangularRelaxation (seamPoint raw p) := by
  have h := fccHUpper_sound hs
  have s : (fccHUpper : ℝ)-4<(numeratorLower raw cube : ℝ) := by exact_mod_cast strict
  exact (show 2*ac*energy fcc≤(fccHUpper : ℝ)-4 by linarith only [h]).trans_lt
    (s.trans_le (numeratorLower_sound hp cube ok))

end BccSharp.Coulomb.CompactCover.OverlayPlanar
