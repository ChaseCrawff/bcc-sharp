import BccSharp.Cover.OverlayAxial
import BccSharp.Cover.CoverEarlyTransport

set_option autoImplicit false

/-! Exact operands for the retained Overlay planar modes. The ordered
closed rectangle is derived from the address upstream. The integer seam
shift is computed from its lower endpoint and applies to the whole box. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)
open Constants.HighPrecision (RootProposal)

def seamShift (b : Cell) : IntVec := ![0,0,-⌊b.lo 7⌋]
def seamCell (b : Cell) : Cell := shiftCell b (seamShift b)
def seamPoint (b : Cell) (p : Chart) : Chart := shiftChart p (seamShift b)

theorem seamPoint_mem {b : Cell} {p : Chart} (hp : b.Mem p) : (seamCell b).Mem (seamPoint b p) := by
  apply (shifted_iff b (seamShift b) _).mpr
  have e : shiftChart (seamPoint b p) (-seamShift b)=p := by
    funext i
    fin_cases i <;> simp [seamPoint,shiftChart,add_assoc]
  simpa only [e] using hp

theorem seamPoint_energy (b : Cell) (p : Chart) :
    energy (chartPoint (seamPoint b p))=energy (chartPoint p) := by
  rw [seamPoint,chartPoint_shift,energy_wrap]

def spacing (b : Cell) : ℚ := min (b.lo 7) (1-b.hi 7)
def halfDistance (b : Cell) : ℚ := max 0 (max (b.lo 7-1/2) (1/2-b.hi 7))

theorem spacing_sound {b : Cell} {p : Chart} (hp : b.Mem p) :
    (spacing b : ℝ)≤p 7 ∧ p 7≤1-(spacing b : ℝ) := by
  have hl : (spacing b : ℝ)≤(b.lo 7 : ℝ) := by exact_mod_cast min_le_left (b.lo 7) (1-b.hi 7)
  have hu : spacing b≤1-b.hi 7 := min_le_right _ _
  have hu' : (spacing b : ℝ)≤1-(b.hi 7 : ℝ) := by exact_mod_cast hu
  exact ⟨hl.trans (hp 7).1,by linarith only [(hp 7).2,hu']⟩

theorem halfDistance_sound {b : Cell} {p : Chart} (hp : b.Mem p) :
    0≤(halfDistance b : ℝ) ∧ (halfDistance b : ℝ)≤|p 7-1/2| := by
  unfold halfDistance
  push_cast
  refine ⟨le_max_left _ _,max_le (abs_nonneg _) (max_le ?_ ?_)⟩
  · exact (sub_le_sub_right (hp 7).1 _).trans (le_abs_self _)
  · exact (sub_le_sub_left (hp 7).2 _).trans (by simpa only [neg_sub] using neg_le_abs (p 7-1/2))

def sc (q : ℚ) (b : Ball) : Ball := intervalMul (Ball.exact q) b
theorem sc_sound (q : ℚ) {b : Ball} {x : ℝ} (h : b.Contains x) :
    (sc q b).Contains ((q : ℝ)*x) := intervalMul_sound (Ball.contains_exact q) h

abbrev Wave := ℤ × ℤ
def waveCube (n : ℕ) : Finset Wave :=
  let span := Finset.Icc (-(n : ℤ)) (n : ℤ)
  span.product span

def waves (n : ℕ) : Finset Wave :=
  (waveCube n).filter (fun m => 0< m.1 ∨ (m.1=0 ∧ 0< m.2))

def cReal (p : Chart) : ℝ := (p 0*p 1)⁻¹
def κSq (p : Chart) (m : Wave) : ℝ :=
  ((m.1 : ℝ)*(p 0)⁻¹)^2 + (((m.2 : ℝ)-(m.1 : ℝ)*p 2)*(p 1)⁻¹)^2
def κReal (p : Chart) (m : Wave) : ℝ := Real.sqrt (κSq p m)
def tReal (p : Chart) (m : Wave) : ℝ := 2*Real.pi*cReal p*κReal p m
def wReal (p : Chart) (m : Wave) : ℝ := (m.1 : ℝ)*(p 3-p 2*p 4)+(m.2 : ℝ)*p 4
def uReal (p : Chart) (m : Wave) : ℝ := (m.1 : ℝ)*p 5+(m.2 : ℝ)*p 6

def cBall (b : Cell) : Ball := positiveInv (intervalMul (coord b 0) (coord b 1))
def κSqBall (b : Cell) (m : Wave) : Ball :=
  let i := (m.1 : ℚ)
  let j := (m.2 : ℚ)
  (sqBall (sc i (positiveInv (coord b 0)))).add
    (sqBall (intervalMul ((Ball.exact j).sub (sc i (coord b 2))) (positiveInv (coord b 1))))

def κRoot (b : Cell) (m : Wave) : RootProposal :=
  let a := κSqBall b m
  Constants.rootPair 2 a.lo a.hi (max 2 (a.hi+1))

def tBall (b : Cell) (m : Wave) : Ball :=
  intervalMul (intervalMul (sc 2 Constants.piInput) (cBall b)) (κRoot b m).ball
def wBall (b : Cell) (m : Wave) : Ball :=
  (sc (m.1 : ℚ) ((coord b 3).sub (intervalMul (coord b 2) (coord b 4)))).add
    (sc (m.2 : ℚ) (coord b 4))
def uBall (b : Cell) (m : Wave) : Ball :=
  (sc (m.1 : ℚ) (coord b 5)).add (sc (m.2 : ℚ) (coord b 6))

theorem cBall_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) :
    (cBall b).Contains (cReal p) :=
  positiveInv_sound (diagonalsCheck_sound hd).2.2 (intervalMul_sound (coord_sound hp 0) (coord_sound hp 1))

theorem κSqBall_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) (m : Wave) :
    (κSqBall b m).Contains (κSq p m) := by
  obtain ⟨r,s,_⟩ := diagonalsCheck_sound hd
  simpa only [κSq,κSqBall,Rat.cast_intCast] using Ball.contains_add
    (sqBall_sound (sc_sound (m.1 : ℚ) (positiveInv_sound r (coord_sound hp 0))))
    (sqBall_sound (intervalMul_sound (Ball.contains_sub (Ball.contains_exact (m.2 : ℚ))
      (sc_sound (m.1 : ℚ) (coord_sound hp 2))) (positiveInv_sound s (coord_sound hp 1))))

theorem κRoot_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) (m : Wave)
    (hκ : (κRoot b m).check (κSqBall b m)=true) : (κRoot b m).ball.Contains (κReal p m) :=
  RootProposal.sound _ _ _ (by unfold κSq; positivity) (κSqBall_sound hp hd m) hκ

theorem tBall_sound {b : Cell} {p : Chart} (hp : b.Mem p) (hd : diagonalsCheck b=true) (m : Wave)
    (hκ : (κRoot b m).check (κSqBall b m)=true) : (tBall b m).Contains (tReal p m) := by
  simpa only [tBall,tReal,Rat.cast_ofNat] using intervalMul_sound
    (intervalMul_sound (sc_sound 2 Constants.piInput_sound) (cBall_sound hp hd)) (κRoot_sound hp hd m hκ)

theorem wBall_sound {b : Cell} {p : Chart} (hp : b.Mem p) (m : Wave) : (wBall b m).Contains (wReal p m) := by
  simpa only [wBall,wReal,Rat.cast_intCast] using Ball.contains_add
    (sc_sound (m.1 : ℚ) (Ball.contains_sub (coord_sound hp 3) (intervalMul_sound (coord_sound hp 2) (coord_sound hp 4))))
    (sc_sound (m.2 : ℚ) (coord_sound hp 4))

theorem uBall_sound {b : Cell} {p : Chart} (hp : b.Mem p) (m : Wave) : (uBall b m).Contains (uReal p m) := by
  simpa only [uBall,uReal,Rat.cast_intCast] using Ball.contains_add
    (sc_sound (m.1 : ℚ) (coord_sound hp 5)) (sc_sound (m.2 : ℚ) (coord_sound hp 6))

end BccSharp.Coulomb.CompactCover.OverlayPlanar
