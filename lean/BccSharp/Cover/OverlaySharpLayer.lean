import BccSharp.Cover.OverlayKernelCheck

set_option autoImplicit false

/-! A sharpened, rounded evaluator for the Overlay signed layer correction.

The checker `layerBall` encloses `cos`, `sin` by the value at the
midpoint plus the input radius, and `cosh`, `sinh` by two separately
enclosed exponentials. Its rationals are never rounded. On 23 of the 28
sampled terminals its lower endpoint falls below that of an Arb
evaluator.

Here every elementary enclosure is the exact range on the input interval, up
to outward rounding to the grid `2⁻⁹⁶` and series and bisection errors below
`10⁻¹⁷`:
* `cos`, `sin` on `[a,b]` from the values at `a` and `b`, each side certified
  by a window of length `2π` around an extremum (`shiftedCosBall_sound`);
* monotone `sinh`, and `cosh` from its minimum at zero (`coshRange_sound`);
* `exp` by argument halving, a short Taylor series and rounded squaring.
Products and sums use exact interval arithmetic, as before. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)
open Constants.HighPrecision (RootProposal)

/-! ### Outward rounding -/

def sharpGrid : ℚ := 2^96

def rnd (b : Ball) : Ball :=
  ballOf ((⌊b.lo*sharpGrid⌋ : ℤ)/sharpGrid) ((⌈b.hi*sharpGrid⌉ : ℤ)/sharpGrid)

theorem rnd_sound {b : Ball} {x : ℝ} (h : b.Contains x) : (rnd b).Contains x := by
  obtain ⟨l,u⟩ := endpoints h
  have g : (0:ℚ)< sharpGrid := by norm_num [sharpGrid]
  have lo : ((⌊b.lo*sharpGrid⌋ : ℤ) : ℚ)/sharpGrid≤ b.lo := (div_le_iff₀ g).mpr (Int.floor_le _)
  have hi : b.hi≤((⌈b.hi*sharpGrid⌉ : ℤ) : ℚ)/sharpGrid := (le_div_iff₀ g).mpr (Int.le_ceil _)
  apply ballOf_sound
  exact ⟨(Rat.cast_le.mpr lo).trans l,u.trans (Rat.cast_le.mpr hi)⟩

/-! ### Exponential at a rational point -/

def expShift : ℕ := 10
def expOrder : ℕ := 14

def squareRounds : ℕ → Ball → Ball
  | 0, b => b
  | n+1, b => squareRounds n (rnd (b.mul b))

theorem squareRounds_sound (n : ℕ) {b : Ball} {x : ℝ} (h : b.Contains (Real.exp x)) :
    (squareRounds n b).Contains (Real.exp (2^n*x)) := by
  induction n generalizing b x with
  | zero => simpa [squareRounds] using h
  | succ n ih =>
    have h₂ : (rnd (b.mul b)).Contains (Real.exp (2*x)) := by
      have s := rnd_sound (Ball.contains_mul h h)
      rwa [← Real.exp_add,← two_mul] at s
    have s := ih h₂
    rw [show (2:ℝ)^n*(2*x)=2^(n+1)*x by ring] at s
    simpa [squareRounds] using s

def expPtCheck (q : ℚ) : Bool := decide (|q/2^expShift|≤1)

def expPt (q : ℚ) : Ball :=
  squareRounds expShift (rnd ⟨SpecialFunctions.taylor (q/2^expShift) expOrder,
    SpecialFunctions.taylorError (q/2^expShift) expOrder⟩)

theorem expPt_sound {q : ℚ} (ok : expPtCheck q=true) : (expPt q).Contains (Real.exp q) := by
  have t := rnd_sound (SpecialFunctions.exp_taylor (q/2^expShift) expOrder (of_decide_eq_true ok)
    (by norm_num [expOrder]))
  have s := squareRounds_sound expShift t
  have e : (2:ℝ)^expShift*(((q/2^expShift : ℚ)) : ℝ)=(q : ℝ) := by
    push_cast
    field_simp
  rwa [e] at s

/-- Exact range of `exp` on `[a,b]`, from the two endpoint values. -/
def expRangeS (a b : ℚ) : Ball := ballOf (expPt a).lo (expPt b).hi

theorem expRangeS_sound {a b : ℚ} {x : ℝ} (ha : expPtCheck a=true) (hb : expPtCheck b=true)
    (hx : (a : ℝ)≤ x ∧ x≤ b) : (expRangeS a b).Contains (Real.exp x) := by
  apply ballOf_sound
  exact ⟨(endpoints (expPt_sound ha)).1.trans (Real.exp_le_exp.mpr hx.1),
    (Real.exp_le_exp.mpr hx.2).trans (endpoints (expPt_sound hb)).2⟩

/-! ### Cosine and sine at a rational point -/

def trigOrder : ℕ := 32
def trigTurns (q : ℚ) : ℤ := ⌊q/(6283185307179586/10^15)+1/2⌋
def trigArg (q : ℚ) : Ball := rnd (TrigBounds.reduce (Ball.exact q) (trigTurns q))
def trigPtCheck (q : ℚ) : Bool := decide (|(trigArg q).mid|/((trigOrder+1 : ℕ) : ℚ)≤1/2)
def cosPt (q : ℚ) : Ball := rnd (TrigBounds.cosBall (trigArg q) trigOrder)
def sinPt (q : ℚ) : Ball := rnd (TrigBounds.sinBall (trigArg q) trigOrder)

private theorem trigArg_sound (q : ℚ) :
    (trigArg q).Contains ((q : ℝ)-(trigTurns q : ℝ)*(2*Real.pi)) :=
  rnd_sound (TrigBounds.reduce_contains (Ball.contains_exact q) (trigTurns q))

theorem cosPt_sound {q : ℚ} (ok : trigPtCheck q=true) : (cosPt q).Contains (Real.cos q) := by
  have c := TrigBounds.cos_contains (trigArg_sound q) (n := trigOrder) (by norm_num [trigOrder])
    (of_decide_eq_true ok)
  rw [Real.cos_sub_int_mul_two_pi] at c
  exact rnd_sound c

theorem sinPt_sound {q : ℚ} (ok : trigPtCheck q=true) : (sinPt q).Contains (Real.sin q) := by
  have c := TrigBounds.sin_contains (trigArg_sound q) (n := trigOrder) (by norm_num [trigOrder])
    (of_decide_eq_true ok)
  rw [Real.sin_sub_int_mul_two_pi] at c
  exact rnd_sound c

/-! ### Ranges of `cos (x - c π)` inside a window around an extremum -/

theorem cos_window_lower {A B y : ℝ} (hA : -Real.pi≤ A) (hB : B≤ Real.pi) (hy : A≤ y ∧ y≤ B) :
    min (Real.cos A) (Real.cos B)≤ Real.cos y := by
  have m := abs_le_max_abs_abs hy.1 hy.2
  have aA : |A|≤ Real.pi := abs_le.mpr ⟨by linarith,by linarith [hy.1,hy.2]⟩
  have aB : |B|≤ Real.pi := abs_le.mpr ⟨by linarith [hy.1,hy.2],hB⟩
  rcases le_total |A| |B| with h | h
  · have c := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) aB (m.trans (max_le h le_rfl))
    rw [Real.cos_abs,Real.cos_abs] at c
    exact (min_le_right _ _).trans c
  · have c := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) aA (m.trans (max_le le_rfl h))
    rw [Real.cos_abs,Real.cos_abs] at c
    exact (min_le_left _ _).trans c

def piS : Ball := TrigBounds.piBall

theorem piS_sound : piS.Contains Real.pi := SpecialFunctions.pi_enclosure

private theorem piMul_sound (c : ℚ) : ((Ball.exact c).mul piS).Contains ((c : ℝ)*Real.pi) :=
  Ball.contains_mul (Ball.contains_exact c) piS_sound

/-- `[a,b] ⊆ [(c-1)π, (c+1)π]`, certified with the rational `π` enclosure. -/
def windowFits (a b c : ℚ) : Bool :=
  decide (((Ball.exact (c-1)).mul piS).hi≤ a ∧ b≤((Ball.exact (c+1)).mul piS).lo)

theorem windowFits_sound {a b c : ℚ} {x : ℝ} (w : windowFits a b c=true) (hx : (a : ℝ)≤ x ∧ x≤ b) :
    -Real.pi≤(a : ℝ)-c*Real.pi ∧ (b : ℝ)-c*Real.pi≤ Real.pi ∧
      ((a : ℝ)-c*Real.pi≤ x-c*Real.pi ∧ x-c*Real.pi≤(b : ℝ)-c*Real.pi) := by
  obtain ⟨lw,uw⟩ := of_decide_eq_true w
  have l₁ := (endpoints (piMul_sound (c-1))).2
  have u₁ := (endpoints (piMul_sound (c+1))).1
  have lw' : (((Ball.exact (c-1)).mul piS).hi : ℝ)≤(a : ℝ) := by exact_mod_cast lw
  have uw' : (b : ℝ)≤(((Ball.exact (c+1)).mul piS).lo : ℝ) := by exact_mod_cast uw
  push_cast at l₁ u₁
  exact ⟨by linarith only [l₁,lw'],by linarith only [u₁,uw'],by linarith only [hx.1],
    by linarith only [hx.2]⟩

/-- The integer `m` that puts `(h + 2m + e)π` nearest the midpoint of `[a,b]`. Any
integer is sound; this one makes the window most likely to fit. -/
def windowIndex (a b h e : ℚ) : ℤ := ⌊((a+b)/2/(3141592653589793/10^15)-h-e)/2+1/2⌋

/-- The range of `cos (x - hπ)` on `[a,b]` from enclosures `ga`, `gb` of its endpoint
values. Its minimum is an endpoint value unless a point `(h + 2m + 1)π` may lie in
`[a,b]`, and its maximum likewise for the points `(h + 2m)π`; each side is certified
by a window of length `2π` centred on the other kind of extremum. -/
def shiftedCosBall (a b h : ℚ) (ga gb : Ball) : Ball :=
  let m₀ := windowIndex a b h 0
  let m₁ := windowIndex a b h 1
  ballOf (if windowFits a b (h+2*(m₀ : ℚ)) then min ga.lo gb.lo else -1)
    (if windowFits a b (h+2*(m₁ : ℚ)+1) then max ga.hi gb.hi else 1)

theorem shiftedCosBall_sound {a b h : ℚ} {ga gb : Ball} {x : ℝ}
    (ha : ga.Contains (Real.cos ((a : ℝ)-(h : ℝ)*Real.pi)))
    (hb : gb.Contains (Real.cos ((b : ℝ)-(h : ℝ)*Real.pi))) (hx : (a : ℝ)≤ x ∧ x≤ b) :
    (shiftedCosBall a b h ga gb).Contains (Real.cos (x-(h : ℝ)*Real.pi)) := by
  have ea := endpoints ha
  have eb := endpoints hb
  set m₀ := windowIndex a b h 0
  set m₁ := windowIndex a b h 1
  have even (y : ℝ) : Real.cos (y-((h+2*(m₀ : ℚ) : ℚ) : ℝ)*Real.pi)=Real.cos (y-(h : ℝ)*Real.pi) := by
    rw [show y-((h+2*(m₀ : ℚ) : ℚ) : ℝ)*Real.pi=(y-(h : ℝ)*Real.pi)-(m₀ : ℝ)*(2*Real.pi) by
      push_cast; ring,Real.cos_sub_int_mul_two_pi]
  have odd (y : ℝ) : Real.cos (y-((h+2*(m₁ : ℚ)+1 : ℚ) : ℝ)*Real.pi)= -Real.cos (y-(h : ℝ)*Real.pi) := by
    rw [show y-((h+2*(m₁ : ℚ)+1 : ℚ) : ℝ)*Real.pi=((y-(h : ℝ)*Real.pi)-(m₁ : ℝ)*(2*Real.pi))-Real.pi by
      push_cast; ring,Real.cos_sub_pi,Real.cos_sub_int_mul_two_pi]
  apply ballOf_sound
  constructor
  · split_ifs with w
    · obtain ⟨hA,hB,hy⟩ := windowFits_sound w hx
      have c := cos_window_lower hA hB hy
      rw [even,even,even] at c
      push_cast
      exact (min_le_min ea.1 eb.1).trans c
    · push_cast
      exact Real.neg_one_le_cos _
  · split_ifs with w
    · obtain ⟨hA,hB,hy⟩ := windowFits_sound w hx
      have c := cos_window_lower hA hB hy
      rw [odd,odd,odd,min_neg_neg] at c
      push_cast
      exact (neg_le_neg_iff.mp c).trans (max_le_max ea.2 eb.2)
    · push_cast
      exact Real.cos_le_one _

def cosRangeCheck (a b : ℚ) : Bool := trigPtCheck a && trigPtCheck b

def cosRange (a b : ℚ) : Ball := shiftedCosBall a b 0 (cosPt a) (cosPt b)

theorem cosRange_sound {a b : ℚ} {x : ℝ} (ok : cosRangeCheck a b=true) (hx : (a : ℝ)≤ x ∧ x≤ b) :
    (cosRange a b).Contains (Real.cos x) := by
  obtain ⟨pa,pb⟩ := Bool.and_eq_true_iff.mp ok
  have z (y : ℝ) : Real.cos (y-((0 : ℚ) : ℝ)*Real.pi)=Real.cos y := by simp
  have r := shiftedCosBall_sound (h := 0) (by rw [z]; exact cosPt_sound pa)
    (by rw [z]; exact cosPt_sound pb) hx
  rwa [z] at r

def sinRangeCheck (a b : ℚ) : Bool := trigPtCheck a && trigPtCheck b

def sinRange (a b : ℚ) : Ball := shiftedCosBall a b (1/2) (sinPt a) (sinPt b)

theorem sinRange_sound {a b : ℚ} {x : ℝ} (ok : sinRangeCheck a b=true) (hx : (a : ℝ)≤ x ∧ x≤ b) :
    (sinRange a b).Contains (Real.sin x) := by
  obtain ⟨pa,pb⟩ := Bool.and_eq_true_iff.mp ok
  have z (y : ℝ) : Real.cos (y-((1/2 : ℚ) : ℝ)*Real.pi)=Real.sin y := by
    rw [show y-((1/2 : ℚ) : ℝ)*Real.pi=y-Real.pi/2 by push_cast; ring,Real.cos_sub_pi_div_two]
  have r := shiftedCosBall_sound (h := 1/2) (by rw [z]; exact sinPt_sound pa)
    (by rw [z]; exact sinPt_sound pb) hx
  rwa [z] at r

/-! ### Hyperbolic ranges -/

def hypPtCheck (q : ℚ) : Bool := expPtCheck q && decide (0<(expPt q).lo)
def coshPt (q : ℚ) : Ball := sc (1/2) ((expPt q).add (positiveInv (expPt q)))
def sinhPt (q : ℚ) : Ball := sc (1/2) ((expPt q).sub (positiveInv (expPt q)))

theorem coshPt_sound {q : ℚ} (ok : hypPtCheck q=true) : (coshPt q).Contains (Real.cosh q) := by
  obtain ⟨e,p⟩ := Bool.and_eq_true_iff.mp ok
  have h := expPt_sound e
  have i := positiveInv_sound (of_decide_eq_true p) h
  rw [← Real.exp_neg] at i
  have s := sc_sound (1/2) (Ball.contains_add h i)
  have e : ((1/2 : ℚ) : ℝ)*(Real.exp q+Real.exp (-q))=Real.cosh q := by
    rw [Real.cosh_eq]
    push_cast
    ring
  rw [e] at s
  exact s

theorem sinhPt_sound {q : ℚ} (ok : hypPtCheck q=true) : (sinhPt q).Contains (Real.sinh q) := by
  obtain ⟨e,p⟩ := Bool.and_eq_true_iff.mp ok
  have h := expPt_sound e
  have i := positiveInv_sound (of_decide_eq_true p) h
  rw [← Real.exp_neg] at i
  have s := sc_sound (1/2) (Ball.contains_sub h i)
  have e : ((1/2 : ℚ) : ℝ)*(Real.exp q-Real.exp (-q))=Real.sinh q := by
    rw [Real.sinh_eq]
    push_cast
    ring
  rw [e] at s
  exact s

def sinhRange (a b : ℚ) : Ball := ballOf (sinhPt a).lo (sinhPt b).hi

theorem sinhRange_sound {a b : ℚ} {x : ℝ} (ha : hypPtCheck a=true) (hb : hypPtCheck b=true)
    (hx : (a : ℝ)≤ x ∧ x≤ b) : (sinhRange a b).Contains (Real.sinh x) := by
  apply ballOf_sound
  exact ⟨(endpoints (sinhPt_sound ha)).1.trans (Real.sinh_le_sinh.mpr hx.1),
    (Real.sinh_le_sinh.mpr hx.2).trans (endpoints (sinhPt_sound hb)).2⟩

def coshRange (a b : ℚ) : Ball :=
  ballOf (if a≤0 ∧ 0≤ b then 1 else if 0< a then (coshPt a).lo else (coshPt b).lo)
    (if -a≤ b then (coshPt b).hi else (coshPt a).hi)

theorem coshRange_sound {a b : ℚ} {x : ℝ} (ha : hypPtCheck a=true) (hb : hypPtCheck b=true)
    (hx : (a : ℝ)≤ x ∧ x≤ b) : (coshRange a b).Contains (Real.cosh x) := by
  have ca := endpoints (coshPt_sound ha)
  have cb := endpoints (coshPt_sound hb)
  apply ballOf_sound
  constructor
  · split_ifs with z p
    · push_cast
      exact Real.one_le_cosh x
    · have p' : (0:ℝ)< a := by exact_mod_cast p
      refine ca.1.trans (Real.cosh_le_cosh.mpr ?_)
      rw [abs_of_pos p',abs_of_pos (p'.trans_le hx.1)]
      exact hx.1
    · have neg : b<0 := by
        by_contra! nb
        exact z ⟨le_of_not_gt p,nb⟩
      have n' : (b : ℝ)<0 := by exact_mod_cast neg
      refine cb.1.trans (Real.cosh_le_cosh.mpr ?_)
      rw [abs_of_neg n',abs_of_neg (hx.2.trans_lt n')]
      linarith only [hx.2]
  · split_ifs with h
    · have h' : -(a : ℝ)≤ b := by exact_mod_cast h
      refine (Real.cosh_le_cosh.mpr ?_).trans cb.2
      rw [abs_le]
      constructor
      · have : 0≤(b : ℝ) := by linarith only [h',hx.1,hx.2]
        rw [abs_of_nonneg this]
        linarith only [h',hx.1]
      · exact hx.2.trans (le_abs_self _)
    · have h' : (b : ℝ)< -(a : ℝ) := by
        have : b< -a := lt_of_not_ge h
        exact_mod_cast this
      refine (Real.cosh_le_cosh.mpr ?_).trans ca.2
      rw [abs_le]
      constructor
      · exact (neg_abs_le _).trans hx.1
      · have : (a : ℝ)<0 := by linarith only [h',hx.1,hx.2]
        rw [abs_of_neg this]
        linarith only [h',hx.2]

/-! ### Retained wave operands -/

def rootSteps : ℕ := 64

def κRootS (b : Cell) (m : Wave) : RootProposal :=
  let a := rnd (κSqBall b m)
  let top := max 2 (a.hi+1)
  ⟨(Constants.bisect 2 a.lo rootSteps (0,top)).1,(Constants.bisect 2 a.hi rootSteps (0,top)).2⟩

theorem κRootS_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) (m : Wave)
    (hκ : (κRootS b m).check (rnd (κSqBall b m))=true) : (κRootS b m).ball.Contains (κReal p m) :=
  RootProposal.sound _ _ _ (by unfold κSq; positivity) (rnd_sound (κSqBall_sound hp hd m)) hκ

def tBallS (b : Cell) (m : Wave) : Ball :=
  rnd (intervalMul (rnd (intervalMul (sc 2 piS) (cBall b))) (κRootS b m).ball)

theorem tBallS_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) (m : Wave)
    (hκ : (κRootS b m).check (rnd (κSqBall b m))=true) : (tBallS b m).Contains (tReal p m) := by
  have h := rnd_sound (intervalMul_sound
    (rnd_sound (intervalMul_sound (sc_sound 2 piS_sound) (cBall_sound hp hd))) (κRootS_sound hp hd m hκ))
  simpa only [tBallS,tReal,Rat.cast_ofNat] using h

/-! ### Sharp core of one axial row -/

def deltaS (h : Ball) : Ball := h.sub (Ball.exact (1/2))

def coreCheckS (t w u h : Ball) : Bool :=
  let δ := deltaS h
  let γ := rnd (intervalMul piS w)
  let γ₂ := rnd (sc 2 γ)
  let φ := rnd (intervalMul (sc 2 piS) (u.add (intervalMul w δ)))
  let z := rnd (intervalMul t δ)
  ((expPtCheck (-t.hi/2) && expPtCheck (-t.lo/2)) && (hypPtCheck z.lo && hypPtCheck z.hi)) &&
    ((cosRangeCheck γ₂.lo γ₂.hi && cosRangeCheck γ.lo γ.hi) &&
      (sinRangeCheck γ.lo γ.hi && (cosRangeCheck φ.lo φ.hi && sinRangeCheck φ.lo φ.hi)))

def coreBallS (t w u h : Ball) : Ball :=
  let δ := deltaS h
  let γ := rnd (intervalMul piS w)
  let γ₂ := rnd (sc 2 γ)
  let φ := rnd (intervalMul (sc 2 piS) (u.add (intervalMul w δ)))
  let z := rnd (intervalMul t δ)
  let Eh := expRangeS (-t.hi/2) (-t.lo/2)
  let E := rnd (intervalMul Eh Eh)
  let same := intervalMul (sc 2 E) (cosRange γ₂.lo γ₂.hi)
  let plus := intervalMul (intervalMul (coshRange z.lo z.hi) (cosRange γ.lo γ.hi)) (cosRange φ.lo φ.hi)
  let minus := intervalMul (intervalMul (sinhRange z.lo z.hi) (sinRange γ.lo γ.hi)) (sinRange φ.lo φ.hi)
  rnd (same.add (intervalMul (sc 2 Eh) (plus.add minus)))

theorem coreBallS_sound {T W U H : Ball} {t w u h : ℝ} (ht : T.Contains t)
    (hw : W.Contains w) (hu : U.Contains u) (hh : H.Contains h) (ok : coreCheckS T W U H=true) :
    (coreBallS T W U H).Contains (axialCore t w u h) := by
  simp only [coreCheckS,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨e₁,e₂⟩,z₁,z₂⟩,⟨c₂,c₁⟩,s₁,f₁,f₂⟩ := ok
  have hd : (deltaS H).Contains (h-1/2) := by
    simpa [deltaS] using Ball.contains_sub hh (Ball.contains_exact (1/2))
  have hg := rnd_sound (intervalMul_sound piS_sound hw)
  have hg₂ := rnd_sound (sc_sound 2 hg)
  have hf := rnd_sound (intervalMul_sound (sc_sound 2 piS_sound)
    (Ball.contains_add hu (intervalMul_sound hw hd)))
  have hz := rnd_sound (intervalMul_sound ht hd)
  have et := endpoints ht
  have eh : (expRangeS (-T.hi/2) (-T.lo/2)).Contains (Real.exp (-t/2)) :=
    expRangeS_sound e₁ e₂ ⟨by push_cast; linarith only [et.2],by push_cast; linarith only [et.1]⟩
  have ee : (rnd (intervalMul (expRangeS (-T.hi/2) (-T.lo/2)) (expRangeS (-T.hi/2) (-T.lo/2)))).Contains
      (Real.exp (-t)) := by
    have s := rnd_sound (intervalMul_sound eh eh)
    rwa [← Real.exp_add,show -t/2+ -t/2= -t by ring] at s
  have cg₂ := cosRange_sound c₂ (endpoints hg₂)
  have cg := cosRange_sound c₁ (endpoints hg)
  have sg := sinRange_sound s₁ (endpoints hg)
  have cf := cosRange_sound f₁ (endpoints hf)
  have sf := sinRange_sound f₂ (endpoints hf)
  have ch := coshRange_sound z₁ z₂ (endpoints hz)
  have sh := sinhRange_sound z₁ z₂ (endpoints hz)
  have same := intervalMul_sound (sc_sound 2 ee) cg₂
  have plus := intervalMul_sound (intervalMul_sound ch cg) cf
  have minus := intervalMul_sound (intervalMul_sound sh sg) sf
  have all := rnd_sound (Ball.contains_add same
    (intervalMul_sound (sc_sound 2 eh) (Ball.contains_add plus minus)))
  convert all using 1
  all_goals first
    | rfl
    | (simp only [axialCore,coshExp,sinhExp,Real.cosh_eq,Real.sinh_eq]
       push_cast
       ring)

def tailCheckS (t₀ η : ℚ) : Bool :=
  (expPtCheck (-t₀) && expPtCheck (-(1+η)*t₀)) && decide (0<((Ball.exact 1).sub (expPt (-t₀))).lo)

def tailBallS (t₀ η : ℚ) : Ball :=
  let E := expPt (-t₀)
  rnd (intervalMul (sc 2 ((intervalMul E E).add (expPt (-(1+η)*t₀))))
    (positiveInv ((Ball.exact 1).sub E)))

theorem tailBallS_sound {t₀ η : ℚ} (ok : tailCheckS t₀ η=true) :
    (tailBallS t₀ η).Contains (axialTail (t₀ : ℝ) (η : ℝ)) := by
  simp only [tailCheckS,Bool.and_eq_true] at ok
  obtain ⟨⟨e₁,eη⟩,pos⟩ := ok
  have E := expPt_sound e₁
  have E₂ : (intervalMul (expPt (-t₀)) (expPt (-t₀))).Contains (Real.exp (-2*(t₀ : ℝ))) := by
    have s := intervalMul_sound E E
    rwa [← Real.exp_add,show ((-t₀ : ℚ) : ℝ)+((-t₀ : ℚ) : ℝ)= -2*(t₀ : ℝ) by push_cast; ring] at s
  have d := positiveInv_sound (of_decide_eq_true pos) (Ball.contains_sub (Ball.contains_exact 1) E)
  have n := Ball.contains_add E₂ (expPt_sound eη)
  have r := rnd_sound (intervalMul_sound (sc_sound 2 n) d)
  convert r using 1
  all_goals first
    | rfl
    | (simp only [axialTail,axialNumerator,div_eq_mul_inv]
       push_cast
       ring)

/-! ### Waves, retained sum and layer -/

def waveCheckS (b : Cell) (m : Wave) : Bool :=
  let k := κRootS b m
  let t := tBallS b m
  ((k.check (rnd (κSqBall b m)) && decide (0< k.ball.lo ∧ 0< t.lo)) &&
    coreCheckS t (wBall b m) (uBall b m) (coord b 7)) && tailCheckS t.lo (spacing b)

def waveBallS (b : Cell) (m : Wave) : Ball :=
  let t := tBallS b m
  let e := tailBallS t.lo (spacing b)
  rnd (intervalMul ((coreBallS t (wBall b m) (uBall b m) (coord b 7)).add ⟨0,e.hi⟩)
    (positiveInv (κRootS b m).ball))

theorem waveBallS_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (ηpos : 0< spacing b) (m : Wave) (ok : waveCheckS b m=true) :
    (waveBallS b m).Contains (waveValue p m) := by
  simp only [waveCheckS,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨root,guards⟩,hc⟩,he⟩ := ok
  have pos : 0<(κRootS b m).ball.lo ∧ 0<(tBallS b m).lo := of_decide_eq_true guards
  have ht := tBallS_sound hp hd m root
  have k := positiveInv_sound pos.1 (κRootS_sound hp hd m root)
  have signed := coreBallS_sound ht (wBall_sound hp m) (uBall_sound hp m) (coord_sound hp 7) hc
  have η := spacing_sound hp
  have r := (axialTail_sound (wReal p m) (uReal p m) (p 7) (spacing b : ℝ)
    (by exact_mod_cast pos.2) (endpoints ht).1 (by exact_mod_cast ηpos.le) η.1 η.2).2
  have upper := (endpoints (tailBallS_sound he)).2
  have radius : (⟨0,(tailBallS (tBallS b m).lo (spacing b)).hi⟩ : Ball).Contains
      (axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7)-
        axialCore (tReal p m) (wReal p m) (uReal p m) (p 7)) := by
    simpa only [Ball.Contains,Rat.cast_zero,sub_zero] using r.trans upper
  have bounds := rnd_sound (intervalMul_sound (Ball.contains_add signed radius) k)
  have e : axialCore (tReal p m) (wReal p m) (uReal p m) (p 7)+
      (axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7)-
        axialCore (tReal p m) (wReal p m) (uReal p m) (p 7))=
      axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7) := by ring
  rw [e] at bounds
  simpa only [waveBallS,waveValue,div_eq_mul_inv] using bounds

def ballSum : List Ball → Ball
  | [] => Ball.exact 0
  | b :: l => b.add (ballSum l)

theorem ballSum_sound (l : List Wave) (B : Wave → Ball) (v : Wave → ℝ)
    (h : ∀ m ∈ l, (B m).Contains (v m)) : (ballSum (l.map B)).Contains ((l.map v).sum) := by
  induction l with
  | nil => simpa [ballSum] using Ball.contains_exact 0
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,ballSum]
    exact Ball.contains_add (h a List.mem_cons_self) (ih (fun m hm => h m (List.mem_cons_of_mem _ hm)))

theorem waveSpan_nodup (n : ℕ) : (waveSpan n).Nodup := by
  unfold waveSpan
  exact List.nodup_range.map (fun a b e => by simpa using e)

theorem wavesList_nodup (n : ℕ) : (wavesList n).Nodup := by
  unfold wavesList
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (waveSpan_nodup n).map (fun a b e => (Prod.mk.inj e).2),?_⟩
  exact (waveSpan_nodup n).imp (fun {i j} hij => List.disjoint_left.mpr (fun {x} hx hy => by
    simp only [List.mem_map] at hx hy
    obtain ⟨a,_,rfl⟩ := hx
    obtain ⟨c,_,e⟩ := hy
    exact hij (Prod.mk.inj e).1.symm))

theorem sum_waves_eq (n : ℕ) (f : Wave → ℝ) : ∑ m ∈ waves n, f m=((wavesList n).map f).sum := by
  have e : waves n=(wavesList n).toFinset := by
    ext m
    rw [List.mem_toFinset,mem_wavesList]
  rw [e]
  exact List.sum_toFinset f (wavesList_nodup n)

def retainedCheckS (raw : Cell) (cube : ℕ) : Bool :=
  let b := seamCell raw
  (diagonalsCheck b && decide (0< spacing b)) && (wavesList cube).all (waveCheckS b)

def retainedBallS (raw : Cell) (cube : ℕ) : Ball :=
  let b := seamCell raw
  rnd (intervalMul (sc 2 (cBall b)) (ballSum ((wavesList cube).map (waveBallS b))))

theorem retainedBallS_sound {raw : Cell} {p : Chart} (hp : raw.Mem p) (cube : ℕ)
    (ok : retainedCheckS raw cube=true) :
    (retainedBallS raw cube).Contains (retainedLayer (seamPoint raw p) cube) := by
  simp only [retainedCheckS,Bool.and_eq_true] at ok
  obtain ⟨⟨hd,hη⟩,h⟩ := ok
  have mem := seamPoint_mem hp
  have finite := ballSum_sound (wavesList cube) (waveBallS (seamCell raw)) (waveValue (seamPoint raw p))
    (fun m hm => waveBallS_sound mem hd (of_decide_eq_true hη) m (List.all_eq_true.mp h m hm))
  rw [← sum_waves_eq] at finite
  simpa only [retainedBallS,retainedLayer,Rat.cast_ofNat] using
    rnd_sound (intervalMul_sound (sc_sound 2 (cBall_sound mem hd)) finite)

/-! ### Radial tail with the same exponential and root kernels -/

def columnRootS (b : Cell) : RootProposal :=
  let q := rnd (columnSqBall b)
  let top := max 2 (q.hi+1)
  ⟨(Constants.bisect 2 q.lo rootSteps (0,top)).1,(Constants.bisect 2 q.hi rootSteps (0,top)).2⟩

def columnUpperS (b : Cell) : ℚ := max (coord b 0).hi (columnRootS b).ball.hi

theorem columnUpperS_sound {b : Cell} {p : Chart} (hp : b.Mem p)
    (ok : (columnRootS b).check (rnd (columnSqBall b))=true) :
    p 0≤(columnUpperS b : ℝ) ∧ secondColumn p≤(columnUpperS b : ℝ) := by
  have h := Ball.contains_add (sqBall_sound (intervalMul_sound (coord_sound hp 0) (coord_sound hp 2)))
    (sqBall_sound (coord_sound hp 1))
  have r := RootProposal.sound _ _ _ (by positivity) (rnd_sound h) ok
  unfold columnUpperS
  push_cast
  exact ⟨(endpoints (coord_sound hp 0)).2.trans (le_max_left _ _),
    (endpoints r).2.trans (le_max_right _ _)⟩

def radialStepS (b : Cell) : ℚ := (rnd (sc ((columnUpperS b)⁻¹) (intervalMul (sc 2 piS) (cBall b)))).lo

theorem radialStepS_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) :
    (radialStepS b : ℝ)≤2*Real.pi*cReal p/(columnUpperS b : ℝ) := by
  have x := (endpoints (rnd_sound (sc_sound ((columnUpperS b)⁻¹)
    (intervalMul_sound (sc_sound 2 piS_sound) (cBall_sound hp hd))))).1
  rw [Rat.cast_inv,Rat.cast_ofNat] at x
  simpa only [radialStepS,div_eq_mul_inv,mul_comm ((columnUpperS b : ℝ)⁻¹)] using x

/-- Enclosure of `1 - exp (-s)`. -/
def oneMinusExp (s : ℚ) : Ball := (Ball.exact 1).sub (expPt (-s))

theorem oneMinusExp_sound {s : ℚ} (ok : expPtCheck (-s)=true) :
    (oneMinusExp s).Contains (1-Real.exp (-(s : ℝ))) := by
  have h := Ball.contains_sub (Ball.contains_exact 1) (expPt_sound ok)
  simpa only [oneMinusExp,Rat.cast_one,Rat.cast_neg] using h

def radialCheckS (b : Cell) (J : ℕ) : Bool :=
  let τ := radialStepS b
  let η := spacing b
  ((columnRootS b).check (rnd (columnSqBall b)) && decide (0<τ)) &&
    (((expPtCheck (-(τ*J)) && decide (0<(oneMinusExp (τ*J)).lo)) &&
      (expPtCheck (-τ) && decide (0<(oneMinusExp τ).lo))) &&
      (expPtCheck (-(τ*η*J)) && (expPtCheck (-(τ*η)) && decide (0<(oneMinusExp (τ*η)).lo))))

def radialBallS (b : Cell) (J : ℕ) : Ball :=
  let τ := radialStepS b
  let η := spacing b
  let g₁ := intervalMul (sc 2 (expPt (-(τ*J)))) (positiveInv (oneMinusExp τ))
  let g₂ := intervalMul (sc 2 (expPt (-(τ*η*J)))) (positiveInv (oneMinusExp (τ*η)))
  rnd (intervalMul (intervalMul (sc (8*columnUpperS b) (cBall b)) (positiveInv (oneMinusExp (τ*J))))
    (g₁.add g₂))

theorem radialBallS_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true)
    (hη : 0< spacing b) (cube : ℕ) (ok : radialCheckS b (cube+1)=true) :
    Summable (waveValue p) ∧ |layerValue p-retainedLayer p cube|≤(radialBallS b (cube+1)).hi := by
  simp only [radialCheckS,Bool.and_eq_true] at ok
  obtain ⟨⟨root,pτ⟩,⟨⟨eJ,dJ⟩,e₁,d₁⟩,eηJ,eη,dη⟩ := ok
  have hDiag := diagonalsCheck_sound hd
  have hr := (show (0:ℝ)<(coord b 0).lo by exact_mod_cast hDiag.1).trans_le (endpoints (coord_sound hp 0)).1
  have hs := (show (0:ℝ)<(coord b 1).lo by exact_mod_cast hDiag.2.1).trans_le (endpoints (coord_sound hp 1)).1
  have hcol := columnUpperS_sound hp root
  have e := spacing_sound hp
  have ht : (0:ℝ)<(radialStepS b : ℝ) := by exact_mod_cast (of_decide_eq_true pτ : 0< radialStepS b)
  obtain ⟨summable,tail⟩ := radialTail_sound cube hr hs hcol.1 hcol.2 ht (radialStepS_sound hp hd)
    (by exact_mod_cast hη) e.1 e.2
  have dJ' := positiveInv_sound (of_decide_eq_true dJ) (oneMinusExp_sound eJ)
  have d₁' := positiveInv_sound (of_decide_eq_true d₁) (oneMinusExp_sound e₁)
  have dη' := positiveInv_sound (of_decide_eq_true dη) (oneMinusExp_sound eη)
  have g₁ := intervalMul_sound (sc_sound 2 (expPt_sound eJ)) d₁'
  have g₂ := intervalMul_sound (sc_sound 2 (expPt_sound eηJ)) dη'
  have bound := rnd_sound (intervalMul_sound
    (intervalMul_sound (sc_sound (8*columnUpperS b) (cBall_sound hp hd)) dJ') (Ball.contains_add g₁ g₂))
  have r : (radialBallS b (cube+1)).Contains
      (radialTail (cReal p) (columnUpperS b : ℝ) (radialStepS b : ℝ) (spacing b : ℝ) (cube+1)) := by
    convert bound using 1
    all_goals first
      | rfl
      | (simp only [radialTail,radialDen,div_eq_mul_inv,neg_mul]
         push_cast
         ring_nf)
  exact ⟨summable,(by rw [layer_diff p cube summable]; exact tail.trans (endpoints r).2)⟩

def layerCheckS (raw : Cell) (cube : ℕ) : Bool :=
  retainedCheckS raw cube && radialCheckS (seamCell raw) (cube+1)

def layerBallS (raw : Cell) (cube : ℕ) : Ball :=
  (retainedBallS raw cube).add ⟨0,(radialBallS (seamCell raw) (cube+1)).hi⟩

theorem layerBallS_sound {raw : Cell} {p : Chart} (hp : raw.Mem p) (cube : ℕ)
    (ok : layerCheckS raw cube=true) : (layerBallS raw cube).Contains (layerValue (seamPoint raw p)) := by
  obtain ⟨hax,hrad⟩ := Bool.and_eq_true_iff.mp ok
  have main := retainedBallS_sound hp cube hax
  simp only [retainedCheckS,Bool.and_eq_true] at hax
  have rad := (radialBallS_sound (seamPoint_mem hp) hax.1.1 (of_decide_eq_true hax.1.2) cube hrad).2
  have err : (⟨0,(radialBallS (seamCell raw) (cube+1)).hi⟩ : Ball).Contains
      (layerValue (seamPoint raw p)-retainedLayer (seamPoint raw p) cube) := by
    simpa only [Ball.Contains,Rat.cast_zero,sub_zero] using rad
  have h := Ball.contains_add main err
  have e : retainedLayer (seamPoint raw p) cube+
      (layerValue (seamPoint raw p)-retainedLayer (seamPoint raw p) cube)=layerValue (seamPoint raw p) := by
    ring
  rw [e] at h
  exact h

/-! ### The sharpened numerator lower bound -/

def sharpCheck (raw : Cell) (cube : ℕ) (T : ℚ) : Bool :=
  areaCheck (seamCell raw) T && layerCheckS raw cube

def sharpLower (raw : Cell) (cube : ℕ) (T : ℚ) : ℚ :=
  areaLower (seamCell raw) T+(layerBallS raw cube).lo

theorem sharpLower_sound {raw : Cell} {p : Chart} (hp : raw.Mem p) {cube : ℕ} {T : ℚ}
    (hT : (T : ℝ)≤ triangleRegularized) (ok : sharpCheck raw cube T=true) :
    (sharpLower raw cube T : ℝ)≤ triangularRelaxation (seamPoint raw p) := by
  obtain ⟨area,layer⟩ := Bool.and_eq_true_iff.mp ok
  have hd : diagonalsCheck (seamCell raw)=true := by
    simp only [layerCheckS,retainedCheckS,Bool.and_eq_true] at layer
    exact layer.1.1.1
  have base := areaLower_sound (seamPoint_mem hp) hd T area
  have tri := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg (cReal (seamPoint raw p)))
  have signed := (endpoints (layerBallS_sound hp cube layer)).1
  unfold sharpLower triangularRelaxation
  push_cast
  linarith only [base,tri,signed]

end BccSharp.Coulomb.CompactCover.OverlayPlanar
