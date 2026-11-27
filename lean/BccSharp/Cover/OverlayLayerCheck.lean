import BccSharp.Cover.OverlayRadial

set_option autoImplicit false

/-! Real and rational enclosures of the full signed layer
correction in the planar expansion of Lemma 7.6, including every omitted planar wave. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)
open Constants.HighPrecision (RootProposal)

def waveNeg (m : Wave) : Wave := (-m.1,-m.2)

theorem waveValue_zero (p : Chart) : waveValue p (0,0)=0 := by
  simp [waveValue,κReal,κSq]

theorem waveValue_even (p : Chart) (m : Wave) : waveValue p (waveNeg m)=waveValue p m := by
  have k : κReal p (waveNeg m)=κReal p m := by
    unfold κReal
    congr 1
    simp only [κSq,waveNeg,Int.cast_neg]
    ring
  have w : wReal p (waveNeg m)= -wReal p m := by simp only [wReal,waveNeg,Int.cast_neg]; ring
  have u : uReal p (waveNeg m)= -uReal p m := by simp only [uReal,waveNeg,Int.cast_neg]; ring
  have t : tReal p (waveNeg m)=tReal p m := by simp only [tReal,k]
  have phase (T d x : ℝ) : axialTerm T d (-x)=axialTerm T d x := by
    unfold axialTerm
    rw [mul_neg,Real.cos_neg]
  have even (T W U H : ℝ) (n : ℕ) : axialPair T (-W) (-U) H n=axialPair T W U H n := by
    have cross (d : ℝ) : -U+d*W= -(U-d*W) := by ring
    simp only [axialPair,mul_neg,← neg_add,sub_neg_eq_add,cross,phase]
  simp only [waveValue,k,w,u,t,axialSeries,even]

theorem signedCube (r : ℕ) : waves r ∪ (waves r).image waveNeg=(waveCube r).erase (0,0) := by
  ext m
  rcases m with ⟨i,j⟩
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_erase,waves,Finset.mem_filter,mem_waveCube]
  constructor
  · rintro (⟨inCube,pos⟩ | ⟨⟨a,b⟩,⟨inCube,pos⟩,e⟩)
    · exact ⟨by intro e; simp only [Prod.mk.injEq] at e; omega,inCube⟩
    · simp only [waveNeg,Prod.mk.injEq] at e
      obtain ⟨rfl,rfl⟩ := e
      refine ⟨fun hz => ?_,by simpa [waveRadius] using inCube⟩
      simp only [Prod.mk.injEq,neg_eq_zero] at hz pos
      omega
  · rintro ⟨nz,inside⟩
    have pos : (0< i ∨ (i=0 ∧ 0<j)) ∨ (0< -i ∨ (-i=0 ∧ 0< -j)) := by
      by_contra! h
      apply nz
      apply Prod.ext <;> simp <;> omega
    rcases pos with h | h
    · exact Or.inl ⟨inside,h⟩
    · exact Or.inr ⟨(-i,-j),⟨by simpa [waveRadius] using inside,h⟩,by simp [waveNeg]⟩

theorem sum_waveCube (r : ℕ) (f : Wave → ℝ) (zeroValue : f (0,0)=0)
    (even : ∀ m, f (waveNeg m)=f m) :
    ∑ m ∈ waveCube r, f m = 2*(∑ m ∈ waves r, f m) := by
  have hdis : Disjoint (waves r) ((waves r).image waveNeg) := by
    apply Finset.disjoint_left.mpr
    intro m hm hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    have h := (Finset.mem_filter.mp hm).2
    have h' := (Finset.mem_filter.mp ha).2
    simp only [waveNeg] at h
    omega
  have zero : (0,0)∈waveCube r := (mem_waveCube _ _).mpr (by simp [waveRadius])
  rw [← Finset.sum_erase_add _ _ zero,zeroValue,add_zero,← signedCube r,Finset.sum_union hdis]
  rw [Finset.sum_image (fun a _ b _ e => by
    rcases a with ⟨a₁,a₂⟩; rcases b with ⟨b₁,b₂⟩; simpa [waveNeg] using e)]
  simp_rw [even]
  ring

def layerValue (p : Chart) : ℝ := cReal p*(∑' m : Wave, waveValue p m)

theorem layer_diff (p : Chart) (cube : ℕ) (hs : Summable (waveValue p)) :
    layerValue p-retainedLayer p cube=cReal p*(∑' m : {m // m∉waveCube cube}, waveValue p m.val) := by
  unfold layerValue retainedLayer
  rw [← hs.sum_add_tsum_subtype_compl (waveCube cube),
    sum_waveCube cube _ (waveValue_zero p) (waveValue_even p)]
  ring

def columnSqBall (b : Cell) : Ball :=
  (sqBall (intervalMul (coord b 0) (coord b 2))).add (sqBall (coord b 1))
def columnRoot (b : Cell) : RootProposal :=
  let q := columnSqBall b
  Constants.rootPair 2 q.lo q.hi (max 2 (q.hi+1))
def columnUpper (b : Cell) : ℚ := max (coord b 0).hi (columnRoot b).ball.hi

theorem columnUpper_sound {b : Cell} {p : Chart} (hp : b.Mem p)
    (ok : (columnRoot b).check (columnSqBall b)=true) :
    p 0≤(columnUpper b : ℝ) ∧ secondColumn p≤(columnUpper b : ℝ) := by
  have h := Ball.contains_add (sqBall_sound (intervalMul_sound (coord_sound hp 0) (coord_sound hp 2)))
    (sqBall_sound (coord_sound hp 1))
  have r := RootProposal.sound _ _ _ (by positivity) h ok
  unfold columnUpper
  push_cast
  exact ⟨(endpoints (coord_sound hp 0)).2.trans (le_max_left _ _),
    (endpoints r).2.trans (le_max_right _ _)⟩

def radialStep (b : Cell) : ℚ := (sc ((columnUpper b)⁻¹) (intervalMul (sc 2 Constants.piInput) (cBall b))).lo

private theorem radialStep_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) :
    (radialStep b : ℝ)≤2*Real.pi*cReal p/(columnUpper b : ℝ) := by
  have x := (endpoints (sc_sound ((columnUpper b)⁻¹)
    (intervalMul_sound (sc_sound 2 Constants.piInput_sound) (cBall_sound hp hd)))).1
  rw [Rat.cast_inv, Rat.cast_ofNat] at x
  simpa only [radialStep,div_eq_mul_inv,mul_comm ((columnUpper b : ℝ)⁻¹)] using x

private def negPoint (s : ℚ) : Ball := Ball.exact (-s)
private def pointExp (s : ℚ) : Ball := eBall (negPoint s)
private def pointDen (s : ℚ) : Ball := (Ball.exact 1).sub (pointExp s)

private theorem pointExp_sound {s : ℚ} (ok : eCheck (negPoint s)=true) :
    (pointExp s).Contains (Real.exp (-(s : ℝ))) := by
  simpa only [pointExp,negPoint,Rat.cast_neg] using eBall_sound ok (Ball.contains_exact (-s))

private theorem pointDen_sound {s : ℚ} (ok : eCheck (negPoint s)=true) :
    (pointDen s).Contains (1-Real.exp (-(s : ℝ))) := by
  simpa only [pointDen,Rat.cast_one] using Ball.contains_sub (Ball.contains_exact 1) (pointExp_sound ok)

private def geomCheck (s : ℚ) (J : ℕ) : Bool :=
  (eCheck (negPoint s) && eCheck (negPoint (s*(J : ℚ)))) && decide (0<(pointDen s).lo)
private def geomBall (s : ℚ) (J : ℕ) : Ball :=
  intervalMul (sc 2 (pointExp (s*(J : ℚ)))) (positiveInv (pointDen s))

private theorem geomBall_sound {s : ℚ} {J : ℕ} (ok : geomCheck s J=true) :
    (geomBall s J).Contains (2*Real.exp (-(s : ℝ)*(J : ℝ))/(1-Real.exp (-(s : ℝ)))) := by
  simp only [geomCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨x,y⟩,hp⟩ := ok
  simpa only [geomBall,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,neg_mul,div_eq_mul_inv] using
    intervalMul_sound (sc_sound 2 (pointExp_sound y)) (positiveInv_sound (of_decide_eq_true hp) (pointDen_sound x))

def radialCheck (b : Cell) (J : ℕ) : Bool :=
  let τ := radialStep b
  let η := spacing b
  let rate := τ*(J : ℚ)
  (((columnRoot b).check (columnSqBall b) && decide (0<τ)) &&
    (eCheck (negPoint rate) && decide (0<(pointDen rate).lo))) &&
    (geomCheck τ J && geomCheck (τ*η) J)

def radialBall (b : Cell) (J : ℕ) : Ball :=
  let τ := radialStep b
  let η := spacing b
  let factor := intervalMul (sc (8*columnUpper b) (cBall b)) (positiveInv (pointDen (τ*(J : ℚ))))
  intervalMul factor ((geomBall τ J).add (geomBall (τ*η) J))

theorem radialBall_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hη : 0<spacing b) (cube : ℕ) (ok : radialCheck b (cube+1)=true) :
    Summable (waveValue p) ∧ |layerValue p-retainedLayer p cube|≤(radialBall b (cube+1)).hi := by
  simp only [radialCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨br,pr⟩,dr,pos⟩,g₁,g₂⟩ := ok
  have hDiag := diagonalsCheck_sound hd
  have hr := (show (0:ℝ)<(coord b 0).lo by exact_mod_cast hDiag.1).trans_le (endpoints (coord_sound hp 0)).1
  have hs := (show (0:ℝ)<(coord b 1).lo by exact_mod_cast hDiag.2.1).trans_le (endpoints (coord_sound hp 1)).1
  have hcol := columnUpper_sound hp br
  have e := spacing_sound hp
  have ht : (0:ℝ)<(radialStep b : ℝ) := by exact_mod_cast (of_decide_eq_true pr : 0< radialStep b)
  obtain ⟨summable,tail⟩ := radialTail_sound cube hr hs hcol.1 hcol.2 ht (radialStep_sound hp hd)
    (by exact_mod_cast hη) e.1 e.2
  have d := positiveInv_sound (of_decide_eq_true pos) (pointDen_sound dr)
  have bound := intervalMul_sound (intervalMul_sound (sc_sound (8*columnUpper b) (cBall_sound hp hd)) d)
    (Ball.contains_add (geomBall_sound g₁) (geomBall_sound g₂))
  have r : (radialBall b (cube+1)).Contains
      (radialTail (cReal p) (columnUpper b : ℝ) (radialStep b : ℝ) (spacing b : ℝ) (cube+1)) := by
    convert bound using 1
    · rfl
    · simp only [radialTail,radialDen,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,neg_mul,div_eq_mul_inv]
      ring
  exact ⟨summable, (by rw [layer_diff p cube summable]; exact tail.trans (endpoints r).2)⟩

def layerCheck (raw : Cell) (cube : ℕ) : Bool :=
  retainedCheck raw cube && radialCheck (seamCell raw) (cube+1)

def layerBall (raw : Cell) (cube : ℕ) : Ball :=
  (retainedBall raw cube).add ⟨0,(radialBall (seamCell raw) (cube+1)).hi⟩

theorem layerBall_sound {raw : Cell} {p : Chart} (hp : raw.Mem p) (cube : ℕ)
    (ok : layerCheck raw cube=true) : (layerBall raw cube).Contains (layerValue (seamPoint raw p)) := by
  obtain ⟨hax,hrad⟩ := Bool.and_eq_true_iff.mp ok
  have main := retainedBall_sound hp cube hax
  simp only [retainedCheck,Bool.and_eq_true] at hax
  have rad := (radialBall_sound (seamPoint_mem hp) hax.1.1 (of_decide_eq_true hax.1.2) cube hrad).2
  have err : (⟨0,(radialBall (seamCell raw) (cube+1)).hi⟩ : Ball).Contains
      (layerValue (seamPoint raw p)-retainedLayer (seamPoint raw p) cube) := by
    simpa only [Ball.Contains,Rat.cast_zero,sub_zero] using rad
  have h := Ball.contains_add main err
  have e : retainedLayer (seamPoint raw p) cube +
      (layerValue (seamPoint raw p)-retainedLayer (seamPoint raw p) cube)=layerValue (seamPoint raw p) := by ring
  rw [e] at h
  exact h

end BccSharp.Coulomb.CompactCover.OverlayPlanar
