import BccSharp.Cover.OverlayPlanarOperands

set_option autoImplicit false

/-! Rational checker for all axial rows of the retained planar
wave vectors. The irrational quantities are the actual real operands
of the signed Poisson correction. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)

def eCheck (a : Ball) : Bool := (Stage2.expRange a).check a
def eBall (a : Ball) : Ball := (Stage2.expRange a).result
theorem eBall_sound {a : Ball} {x : ℝ} (ok : eCheck a=true) (h : a.Contains x) :
    (eBall a).Contains (Real.exp x) := ExpBounds.Witness.sound ok h

private def turns (a : Ball) : ℤ := ⌊a.mid/(6283185307179586/10^15)+1/2⌋
private def trigCheck (a : Ball) : Bool := decide (|(TrigBounds.reduce a (turns a)).mid|/(65:ℚ)≤1/2)
private def cosBall (a : Ball) := TrigBounds.cosBall (TrigBounds.reduce a (turns a)) 64
private def sinBall (a : Ball) := TrigBounds.sinBall (TrigBounds.reduce a (turns a)) 64

private theorem cosBall_sound {a : Ball} {x : ℝ} (ok : trigCheck a=true) (h : a.Contains x) :
    (cosBall a).Contains (Real.cos x) := by
  have small : |(TrigBounds.reduce a (turns a)).mid|/(65:ℚ)≤1/2 := of_decide_eq_true ok
  exact TrigBounds.reduced_cos h _ (by decide) (by simpa using small)

private theorem sinBall_sound {a : Ball} {x : ℝ} (ok : trigCheck a=true) (h : a.Contains x) :
    (sinBall a).Contains (Real.sin x) := by
  have small : |(TrigBounds.reduce a (turns a)).mid|/(65:ℚ)≤1/2 := of_decide_eq_true ok
  exact TrigBounds.reduced_sin h _ (by decide) (by simpa using small)

private def deltaBall (h : Ball) : Ball := h.sub (Ball.exact (1/2))
private def gammaBall (w : Ball) : Ball := intervalMul Constants.piInput w
private def phiBall (w u h : Ball) : Ball :=
  intervalMul (sc 2 Constants.piInput) (u.add (intervalMul w (deltaBall h)))
private def hyperArg (t h : Ball) : Ball := intervalMul t (deltaBall h)

def coreCheck (t w u h : Ball) : Bool :=
  let γ := gammaBall w
  let φ := phiBall w u h
  let z := hyperArg t h
  (((eCheck t.neg && eCheck (sc (-1/2) t)) && (eCheck z && eCheck z.neg)) &&
    ((trigCheck (sc 2 γ) && trigCheck γ) && trigCheck φ))

def coreBall (t w u h : Ball) : Ball :=
  let γ := gammaBall w
  let φ := phiBall w u h
  let z := hyperArg t h
  let C := sc (1/2) ((eBall z).add (eBall z.neg))
  let S := sc (1/2) ((eBall z).sub (eBall z.neg))
  let same := intervalMul (sc 2 (eBall t.neg)) (cosBall (sc 2 γ))
  let plus := intervalMul (intervalMul C (cosBall γ)) (cosBall φ)
  let minus := intervalMul (intervalMul S (sinBall γ)) (sinBall φ)
  let adjacent := intervalMul (sc 2 (eBall (sc (-1/2) t))) (plus.add minus)
  same.add adjacent

theorem coreBall_sound {T W U H : Ball} {t w u h : ℝ} (ht : T.Contains t)
    (hw : W.Contains w) (hu : U.Contains u) (hh : H.Contains h) (ok : coreCheck T W U H=true) :
    (coreBall T W U H).Contains (axialCore t w u h) := by
  simp only [coreCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨e₁,e₂⟩,e₃,e₄⟩,⟨c₂,c⟩,f⟩ := ok
  have hd : (deltaBall H).Contains (h-1/2) := by
    simpa [deltaBall] using Ball.contains_sub hh (Ball.contains_exact (1/2))
  have hg := intervalMul_sound Constants.piInput_sound hw
  have hz := intervalMul_sound ht hd
  have hp := eBall_sound e₃ hz
  have hm := eBall_sound e₄ (Ball.contains_neg hz)
  have ht₂ : (sc (-1/2) T).Contains (-(t/2)) := by
    convert sc_sound (-1/2) ht using 1 <;> push_cast <;> ring
  have hf := intervalMul_sound (sc_sound 2 Constants.piInput_sound)
    (Ball.contains_add hu (intervalMul_sound hw hd))
  have same := intervalMul_sound (sc_sound 2 (eBall_sound e₁ (Ball.contains_neg ht)))
    (cosBall_sound c₂ (sc_sound 2 hg))
  have plus := intervalMul_sound (intervalMul_sound (sc_sound (1/2) (Ball.contains_add hp hm))
    (cosBall_sound c hg)) (cosBall_sound f hf)
  have minus := intervalMul_sound (intervalMul_sound (sc_sound (1/2) (Ball.contains_sub hp hm))
    (sinBall_sound c hg)) (sinBall_sound f hf)
  have adj := intervalMul_sound (sc_sound 2 (eBall_sound e₂ ht₂)) (Ball.contains_add plus minus)
  convert Ball.contains_add same adj using 1
  all_goals first
    | rfl
    | (simp only [axialCore,coshExp,sinhExp,Rat.cast_ofNat,Rat.cast_div,Rat.cast_one]
       congr 1 <;> ring)

private def denBall (t₀ : ℚ) : Ball := (Ball.exact 1).sub (eBall (Ball.exact (-t₀)))

def tailCheck (t₀ η : ℚ) : Bool :=
  ((eCheck (Ball.exact (-t₀)) && eCheck (Ball.exact (-2*t₀))) &&
    eCheck (Ball.exact (-(1+η)*t₀))) && decide (0<(denBall t₀).lo)

def tailBall (t₀ η : ℚ) : Ball :=
  let E₂ := eBall (Ball.exact (-2*t₀))
  let Eη := eBall (Ball.exact (-(1+η)*t₀))
  intervalMul (sc 2 (E₂.add Eη)) (positiveInv (denBall t₀))

theorem tailBall_sound {t₀ η : ℚ} (ok : tailCheck t₀ η=true) :
    (tailBall t₀ η).Contains (axialTail (t₀ : ℝ) (η : ℝ)) := by
  simp only [tailCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨e₁,e₂⟩,eη⟩,pos⟩ := ok
  have d := Ball.contains_sub (Ball.contains_exact 1)
    (eBall_sound e₁ (Ball.contains_exact (-t₀)))
  have n := Ball.contains_add (eBall_sound e₂ (Ball.contains_exact (-2*t₀)))
    (eBall_sound eη (Ball.contains_exact (-(1+η)*t₀)))
  simpa only [tailBall,axialTail,axialNumerator,div_eq_mul_inv,denBall,Rat.cast_neg,
    Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,mul_add] using
    intervalMul_sound (sc_sound 2 n) (positiveInv_sound (of_decide_eq_true pos) d)

def waveCheck (b : Cell) (m : Wave) : Bool :=
  let k := κRoot b m
  let t := tBall b m
  ((k.check (κSqBall b m) && decide (0<k.ball.lo ∧ 0<t.lo)) &&
    coreCheck t (wBall b m) (uBall b m) (coord b 7)) && tailCheck t.lo (spacing b)

def waveBall (b : Cell) (m : Wave) : Ball :=
  let t := tBall b m
  let e := tailBall t.lo (spacing b)
  let main := coreBall t (wBall b m) (uBall b m) (coord b 7)
  intervalMul (main.add ⟨0,e.hi⟩) (positiveInv (κRoot b m).ball)

def waveValue (p : Chart) (m : Wave) : ℝ :=
  axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7)/κReal p m

theorem waveBall_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (ηpos : 0<spacing b) (m : Wave) (ok : waveCheck b m=true) :
    (waveBall b m).Contains (waveValue p m) := by
  simp only [waveCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨root,guards⟩,hc⟩,he⟩ := ok
  have pos : 0<(κRoot b m).ball.lo ∧ 0<(tBall b m).lo := of_decide_eq_true guards
  have ht := tBall_sound hp hd m root
  have k := positiveInv_sound pos.1 (κRoot_sound hp hd m root)
  have signed := coreBall_sound ht (wBall_sound hp m) (uBall_sound hp m) (coord_sound hp 7) hc
  have η := spacing_sound hp
  have r := (axialTail_sound (wReal p m) (uReal p m) (p 7) (spacing b : ℝ)
    (by exact_mod_cast pos.2) (endpoints ht).1 (by exact_mod_cast ηpos.le) η.1 η.2).2
  have upper := (endpoints (tailBall_sound he)).2
  have radius : (⟨0,(tailBall (tBall b m).lo (spacing b)).hi⟩ : Ball).Contains
      (axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7)-
        axialCore (tReal p m) (wReal p m) (uReal p m) (p 7)) := by
    simpa only [Ball.Contains,Rat.cast_zero,sub_zero] using r.trans upper
  have bounds := intervalMul_sound (Ball.contains_add signed radius) k
  have e : axialCore (tReal p m) (wReal p m) (uReal p m) (p 7)+
      (axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7)-
        axialCore (tReal p m) (wReal p m) (uReal p m) (p 7))=
      axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7) := by ring
  rw [e] at bounds
  simpa only [waveBall,waveValue,div_eq_mul_inv] using bounds

def retainedLayer (p : Chart) (cube : ℕ) : ℝ :=
  (2*cReal p)*(∑ m ∈ waves cube, waveValue p m)

def retainedCheck (raw : Cell) (cube : ℕ) : Bool :=
  let b := seamCell raw
  (diagonalsCheck b && decide (0<spacing b)) && (waves cube).toList.all (waveCheck b)

def retainedBall (raw : Cell) (cube : ℕ) : Ball :=
  let b := seamCell raw
  intervalMul (sc 2 (cBall b)) (Constants.sumBalls (waves cube) (waveBall b))

theorem retainedBall_sound {raw : Cell} {p : Chart} (hp : raw.Mem p) (cube : ℕ)
    (ok : retainedCheck raw cube=true) :
    (retainedBall raw cube).Contains (retainedLayer (seamPoint raw p) cube) := by
  simp only [retainedCheck,Bool.and_eq_true] at ok
  obtain ⟨⟨hd,hη⟩,h⟩ := ok
  have mem := seamPoint_mem hp
  have finite := Constants.sumBalls_sound (waves cube) (waveBall (seamCell raw))
    (waveValue (seamPoint raw p)) (fun m hm => waveBall_sound mem hd (of_decide_eq_true hη) m
      (List.all_eq_true.mp h m (by simpa using hm)))
  simpa only [retainedBall,retainedLayer,Rat.cast_ofNat] using
    intervalMul_sound (sc_sound 2 (cBall_sound mem hd)) finite

end BccSharp.Coulomb.CompactCover.OverlayPlanar
