import BccSharp.Cover.LeafFixSupport

set_option autoImplicit false

/-! # Soundness of the fixed-point J, F and D leaf checks

* Corner enclosures (`shapeOf_mem`, `linShape_le`, `linOffQ_le`, `nlHi_ge`,
  `strainHi_ge`, `shiftQ_ge`): at every corner `corner b bits` of a leaf box,
  the integer support sum `sig` is at most `S² · 2 a_c` times the minorant and
  the integer cost `C` is at least `S` times the registered cost.
* The three leaf theorems, on valid points and on the cover framework's `good`
  points:
  - `jleafFix_sound`: `0 < deficit` (route `strictJoint`), from the joint
    comparison `T − e_BCC − g (1 − t + t C) > 0` at all corners;
  - `dleafFix_sound`: `0 < deficit` (route `strictDeficit`), from a whole-box
    defect cap `cap` (`defect_le_cap`: `defect ≤ regCost ≤ cap/S ≤ 1/2` on the
    box) and `T − e_BCC − g cap/S > 0` at all corners;
  - `fleafFix_sound`: `energy fcc < energy` (route `strictFCC`).
* Certificates in the shape the cover composition consumes: `LeafCert`,
  `LeafCert.sound`, and the adapters `certCheck_sound : SoundCheck (certCheck T)`
  and `lateCheck_sound : LatePackets.CheckerSound (lateCheck T)`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.LeafFix
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Screened

/-! ### Corner coordinates -/

theorem coordF_mem (b : Cell) (bits : Axis → Bool) (i : Axis) :
    (coordF b i (bits i)).Mem (corner b bits i) := by
  unfold coordF corner
  cases bits i <;> simp [qF_mem]

theorem coordQ_eq (b : Cell) (bits : Axis → Bool) (i : Axis) :
    ((coordQ b i (bits i) : ℚ) : ℝ) = corner b bits i := by
  unfold coordQ corner
  cases bits i <;> simp

theorem corner_pos (b : Cell) (bits : Axis → Bool) (i : Axis) (lo : (0 : ℝ) < b.lo i)
    (ord : (b.lo i : ℝ) ≤ b.hi i) : 0 < corner b bits i := by
  unfold corner
  split
  · exact lo.trans_le ord
  · exact lo

/-! ### Shape enclosures -/

/-- The real values a shape record encloses at a point `p`. -/
structure ShapeMem (sh : Shape) (p : Chart) : Prop where
  r1 : sh.r1.Mem (p 0)
  r2 : sh.r2.Mem (p 1)
  x : sh.x.Mem (p 2)
  y : sh.y.Mem (p 3)
  z : sh.z.Mem (p 4)
  s2 : sh.s2.Mem (p 0 * p 0)
  t2 : sh.t2.Mem (p 1 * p 1)
  st : sh.st.Mem (p 0 * p 0 * (p 1 * p 1))
  rr : sh.rr.Mem ((p 0 * p 1)⁻¹)
  g0 : sh.g0.Mem (featGen p 0)
  g1 : sh.g1.Mem (featGen p 1)
  g2 : sh.g2.Mem (featGen p 2)
  g3 : sh.g3.Mem (featGen p 3)
  g4 : sh.g4.Mem (featGen p 4)
  g5 : sh.g5.Mem (featGen p 5)
  d0 : sh.d0.Mem (featGen p 6)
  d1 : sh.d1.Mem (featGen p 7)
  d2 : sh.d2.Mem (featGen p 8)
  d3 : sh.d3.Mem (featGen p 9)
  d4 : sh.d4.Mem (featGen p 10)
  d5 : sh.d5.Mem (featGen p 11)

theorem smulN2_mem {a : FI} {x : ℝ} (hx : a.Mem x) : (FI.smul (-2) a).Mem (-2 * x) := by
  have h := FI.smul_mem (-2) hx
  push_cast at h
  exact h

theorem shapeOf_mem (b : Cell) (bits : Axis → Bool)
    (hg : shapeGuard (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) = true) :
    ShapeMem (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) (corner b bits) := by
  simp only [shapeGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨_, _⟩, gs⟩, gt⟩, gst⟩, grr⟩ := hg
  set p := corner b bits with hp
  have hr1 : (coordF b 0 (bits 0)).Mem (p 0) := coordF_mem b bits 0
  have hr2 : (coordF b 1 (bits 1)).Mem (p 1) := coordF_mem b bits 1
  have hx : (coordF b 2 (bits 2)).Mem (p 2) := coordF_mem b bits 2
  have hy : (coordF b 3 (bits 3)).Mem (p 3) := coordF_mem b bits 3
  have hz : (coordF b 4 (bits 4)).Mem (p 4) := coordF_mem b bits 4
  have hs2 := FI.mulPos_mem hr1 hr1
  have ht2 := FI.mulPos_mem hr2 hr2
  have hst := FI.mulPos_mem hs2 ht2
  have hsi := FI.invPos_mem gs hs2
  have hti := FI.invPos_mem gt ht2
  have hui := FI.invPos_mem gst hst
  have hrr := FI.invPos_mem grr (FI.mulPos_mem hr1 hr2)
  have hh := FI.sub_mem (FI.mul_mem hx hz) hy
  exact
    { r1 := hr1, r2 := hr2, x := hx, y := hy, z := hz, s2 := hs2, t2 := ht2, st := hst, rr := hrr
      g0 := hs2
      g1 := FI.add_mem (FI.mul_mem (FI.mul_mem hs2 hx) hx) ht2
      g2 := FI.add_mem (FI.add_mem (FI.mul_mem (FI.mul_mem hs2 hy) hy)
        (FI.mul_mem (FI.mul_mem ht2 hz) hz)) hui
      g3 := FI.mul_mem (FI.smul2_mem hs2) hx
      g4 := FI.mul_mem (FI.smul2_mem hs2) hy
      g5 := FI.smul2_mem (FI.add_mem (FI.mul_mem (FI.mul_mem hs2 hx) hy) (FI.mul_mem ht2 hz))
      d0 := FI.add_mem (FI.add_mem hsi (FI.mul_mem (FI.mul_mem hx hx) hti))
        (FI.mul_mem (FI.mul_mem hh hh) hst)
      d1 := FI.add_mem hti (FI.mul_mem (FI.mul_mem hz hz) hst)
      d2 := hst
      d3 := FI.smul2_mem (FI.sub_mem (FI.mul_mem (negF_mem hx) hti) (FI.mul_mem (FI.mul_mem hh hz) hst))
      d4 := FI.mul_mem (FI.smul2_mem hh) hst
      d5 := FI.mul_mem (smulN2_mem hz) hst }

/-! ### The support sum at a corner -/

theorem lowDot_le (w : ℤ) {a : FI} {x : ℝ} (hx : a.Mem x) : (lowDot w a : ℝ) ≤ (w : ℝ) * (Sz * x) := by
  have sp := Sz_pos
  have h1 := hx.1
  have h2 := hx.2
  rw [div_le_iff₀ sp] at h1
  rw [le_div_iff₀ sp] at h2
  unfold lowDot
  split_ifs with hw
  · have hw' : (0 : ℝ) ≤ w := by exact_mod_cast hw
    push_cast
    nlinarith
  · have hw' : (w : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hw))
    push_cast
    nlinarith

theorem highDot_ge (w : ℤ) {a : FI} {x : ℝ} (hx : a.Mem x) : (w : ℝ) * (Sz * x) ≤ (highDot w a : ℝ) := by
  have sp := Sz_pos
  have h1 := hx.1
  have h2 := hx.2
  rw [div_le_iff₀ sp] at h1
  rw [le_div_iff₀ sp] at h2
  unfold highDot
  split_ifs with hw
  · have hw' : (0 : ℝ) ≤ w := by exact_mod_cast hw
    push_cast
    nlinarith
  · have hw' : (w : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hw))
    push_cast
    nlinarith

theorem loMulQ_le {a : FI} {x : ℝ} (hx : a.Mem x) (q : ℚ) : (loMulQ a q : ℝ) ≤ Sz * x * q := by
  unfold loMulQ
  split_ifs with hq
  · exact fmulQ_mono_lo hx hq
  · have sp := Sz_pos
    have h := hx.2
    rw [le_div_iff₀ sp] at h
    have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hq))
    have := mul_le_mul_of_nonpos_right h hq'
    linarith [fmulQ_le a.hi q]

theorem hiMulQ_ge {a : FI} {x : ℝ} (hx : a.Mem x) (q : ℚ) : Sz * x * q ≤ (hiMulQ a q : ℝ) := by
  unfold hiMulQ
  split_ifs with hq
  · exact cmulQ_mono_hi hx hq
  · have sp := Sz_pos
    have h := hx.1
    rw [div_le_iff₀ sp] at h
    have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hq))
    have := mul_le_mul_of_nonpos_right h hq'
    linarith [le_cmulQ a.lo q]

/-! The components of `featGen` used below. -/

theorem fg0 (p : Chart) : featGen p 0 = p 0 * p 0 := rfl
theorem fg1 (p : Chart) : featGen p 1 = p 0 * p 0 * p 2 * p 2 + p 1 * p 1 := rfl
theorem fg2 (p : Chart) :
    featGen p 2 = p 0 * p 0 * p 3 * p 3 + p 1 * p 1 * p 4 * p 4 + (p 0 * p 0 * (p 1 * p 1))⁻¹ := rfl
theorem fg3 (p : Chart) : featGen p 3 = 2 * (p 0 * p 0) * p 2 := rfl
theorem fg4 (p : Chart) : featGen p 4 = 2 * (p 0 * p 0) * p 3 := rfl
theorem fg5 (p : Chart) : featGen p 5 = 2 * (p 0 * p 0 * p 2 * p 3 + p 1 * p 1 * p 4) := rfl
theorem fg12 (p : Chart) :
    featGen p 12 = featGen p 0 * p 5 + (featGen p 3 * p 6 + featGen p 4 * p 7) / 2 := rfl
theorem fg13 (p : Chart) :
    featGen p 13 = featGen p 1 * p 6 + (featGen p 3 * p 5 + featGen p 5 * p 7) / 2 := rfl
theorem fg14 (p : Chart) :
    featGen p 14 = featGen p 2 * p 7 + (featGen p 4 * p 5 + featGen p 5 * p 6) / 2 := rfl
theorem fg15 (p : Chart) :
    featGen p 15 = p 5 * featGen p 12 + p 6 * featGen p 13 + p 7 * featGen p 14 := rfl
theorem fg16 (p : Chart) : featGen p 16 = p 5 := rfl
theorem fg17 (p : Chart) : featGen p 17 = p 6 := rfl
theorem fg18 (p : Chart) : featGen p 18 = p 7 := rfl

/-- The value of the aggregate split into the shape features `j < 12` and the
offset features `j ≥ 12`. -/
def shapePart (l : Lin19) (p : Chart) : ℝ :=
  (l.k : ℝ) / Sz + (l.w0 : ℝ) / Sz * featGen p 0 + (l.w1 : ℝ) / Sz * featGen p 1 +
    (l.w2 : ℝ) / Sz * featGen p 2 + (l.w3 : ℝ) / Sz * featGen p 3 + (l.w4 : ℝ) / Sz * featGen p 4 +
    (l.w5 : ℝ) / Sz * featGen p 5 + (l.w6 : ℝ) / Sz * featGen p 6 + (l.w7 : ℝ) / Sz * featGen p 7 +
    (l.w8 : ℝ) / Sz * featGen p 8 + (l.w9 : ℝ) / Sz * featGen p 9 + (l.w10 : ℝ) / Sz * featGen p 10 +
    (l.w11 : ℝ) / Sz * featGen p 11

def offPart (l : Lin19) (p : Chart) : ℝ :=
  (l.w12 : ℝ) / Sz * featGen p 12 + (l.w13 : ℝ) / Sz * featGen p 13 +
    (l.w14 : ℝ) / Sz * featGen p 14 + (l.w15 : ℝ) / Sz * featGen p 15 +
    (l.w16 : ℝ) / Sz * featGen p 16 + (l.w17 : ℝ) / Sz * featGen p 17 + (l.w18 : ℝ) / Sz * featGen p 18

theorem val_split (l : Lin19) (p : Chart) : l.val p = shapePart l p + offPart l p := by
  simp only [Lin19.val, Lin19.W, shapePart, offPart, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

theorem linShape_le (l : Lin19) (sh : Shape) (p : Chart) (hm : ShapeMem sh p) :
    (linShape l sh : ℝ) ≤ Sz * Sz * shapePart l p := by
  have sp := Sz_pos
  have e0 := lowDot_le l.w0 hm.g0
  have e1 := lowDot_le l.w1 hm.g1
  have e2 := lowDot_le l.w2 hm.g2
  have e3 := lowDot_le l.w3 hm.g3
  have e4 := lowDot_le l.w4 hm.g4
  have e5 := lowDot_le l.w5 hm.g5
  have e6 := lowDot_le l.w6 hm.d0
  have e7 := lowDot_le l.w7 hm.d1
  have e8 := lowDot_le l.w8 hm.d2
  have e9 := lowDot_le l.w9 hm.d3
  have e10 := lowDot_le l.w10 hm.d4
  have e11 := lowDot_le l.w11 hm.d5
  have key : Sz * Sz * shapePart l p = (l.k : ℝ) * Sz + (l.w0 : ℝ) * (Sz * featGen p 0) +
      (l.w1 : ℝ) * (Sz * featGen p 1) + (l.w2 : ℝ) * (Sz * featGen p 2) +
      (l.w3 : ℝ) * (Sz * featGen p 3) + (l.w4 : ℝ) * (Sz * featGen p 4) +
      (l.w5 : ℝ) * (Sz * featGen p 5) + (l.w6 : ℝ) * (Sz * featGen p 6) +
      (l.w7 : ℝ) * (Sz * featGen p 7) + (l.w8 : ℝ) * (Sz * featGen p 8) +
      (l.w9 : ℝ) * (Sz * featGen p 9) + (l.w10 : ℝ) * (Sz * featGen p 10) +
      (l.w11 : ℝ) * (Sz * featGen p 11) := by
    unfold shapePart
    field_simp
  rw [key]
  unfold linShape
  push_cast
  linarith

theorem offCoef_mem (l : Lin19) (sh : Shape) (p : Chart) (hm : ShapeMem sh p) :
    (offCoef l sh).a0.Mem ((l.w12 : ℝ) * featGen p 0 + ((l.w13 : ℝ) * featGen p 3 +
        (l.w14 : ℝ) * featGen p 4) / 2 + l.w16) ∧
    (offCoef l sh).a1.Mem ((l.w13 : ℝ) * featGen p 1 + ((l.w12 : ℝ) * featGen p 3 +
        (l.w14 : ℝ) * featGen p 5) / 2 + l.w17) ∧
    (offCoef l sh).a2.Mem ((l.w14 : ℝ) * featGen p 2 + ((l.w12 : ℝ) * featGen p 4 +
        (l.w13 : ℝ) * featGen p 5) / 2 + l.w18) ∧
    (offCoef l sh).b0.Mem ((l.w15 : ℝ) * featGen p 0) ∧ (offCoef l sh).b1.Mem ((l.w15 : ℝ) * featGen p 1) ∧
    (offCoef l sh).b2.Mem ((l.w15 : ℝ) * featGen p 2) ∧ (offCoef l sh).b3.Mem ((l.w15 : ℝ) * featGen p 3) ∧
    (offCoef l sh).b4.Mem ((l.w15 : ℝ) * featGen p 4) ∧ (offCoef l sh).b5.Mem ((l.w15 : ℝ) * featGen p 5) := by
  refine ⟨?_, ?_, ?_, FI.smul_mem _ hm.g0, FI.smul_mem _ hm.g1, FI.smul_mem _ hm.g2,
    FI.smul_mem _ hm.g3, FI.smul_mem _ hm.g4, FI.smul_mem _ hm.g5⟩
  · exact FI.add_mem (FI.add_mem (FI.smul_mem _ hm.g0)
      (halfFI_mem (FI.add_mem (FI.smul_mem _ hm.g3) (FI.smul_mem _ hm.g4)))) (FI.ofInt_mem _)
  · exact FI.add_mem (FI.add_mem (FI.smul_mem _ hm.g1)
      (halfFI_mem (FI.add_mem (FI.smul_mem _ hm.g3) (FI.smul_mem _ hm.g5)))) (FI.ofInt_mem _)
  · exact FI.add_mem (FI.add_mem (FI.smul_mem _ hm.g2)
      (halfFI_mem (FI.add_mem (FI.smul_mem _ hm.g4) (FI.smul_mem _ hm.g5)))) (FI.ofInt_mem _)

theorem offPart_eq (l : Lin19) (p : Chart) :
    Sz * offPart l p = ((l.w12 : ℝ) * featGen p 0 + ((l.w13 : ℝ) * featGen p 3 +
        (l.w14 : ℝ) * featGen p 4) / 2 + l.w16) * p 5 +
      ((l.w13 : ℝ) * featGen p 1 + ((l.w12 : ℝ) * featGen p 3 + (l.w14 : ℝ) * featGen p 5) / 2 + l.w17) * p 6 +
      ((l.w14 : ℝ) * featGen p 2 + ((l.w12 : ℝ) * featGen p 4 + (l.w13 : ℝ) * featGen p 5) / 2 + l.w18) * p 7 +
      (l.w15 : ℝ) * featGen p 0 * (p 5 * p 5) + (l.w15 : ℝ) * featGen p 1 * (p 6 * p 6) +
      (l.w15 : ℝ) * featGen p 2 * (p 7 * p 7) + (l.w15 : ℝ) * featGen p 3 * (p 5 * p 6) +
      (l.w15 : ℝ) * featGen p 4 * (p 5 * p 7) + (l.w15 : ℝ) * featGen p 5 * (p 6 * p 7) := by
  have sp := Sz_pos
  unfold offPart
  rw [fg15, fg12, fg13, fg14, fg16, fg17, fg18]
  field_simp
  ring

theorem linOffQ_le (l : Lin19) (sh : Shape) (b : Cell) (bits : Axis → Bool) (hm : ShapeMem sh (corner b bits)) :
    (linOffQ (offCoef l sh) (coordQ b 5 (bits 5)) (coordQ b 6 (bits 6)) (coordQ b 7 (bits 7)) : ℝ) ≤
      Sz * Sz * offPart l (corner b bits) := by
  set p := corner b bits with hp
  obtain ⟨ha0, ha1, ha2, hb0, hb1, hb2, hb3, hb4, hb5⟩ := offCoef_mem l sh p hm
  have f5 := coordQ_eq b bits 5
  have f6 := coordQ_eq b bits 6
  have f7 := coordQ_eq b bits 7
  rw [← hp] at f5 f6 f7
  have q0 := loMulQ_le ha0 (coordQ b 5 (bits 5))
  have q1 := loMulQ_le ha1 (coordQ b 6 (bits 6))
  have q2 := loMulQ_le ha2 (coordQ b 7 (bits 7))
  have q3 := loMulQ_le hb0 (coordQ b 5 (bits 5) * coordQ b 5 (bits 5))
  have q4 := loMulQ_le hb1 (coordQ b 6 (bits 6) * coordQ b 6 (bits 6))
  have q5 := loMulQ_le hb2 (coordQ b 7 (bits 7) * coordQ b 7 (bits 7))
  have q6 := loMulQ_le hb3 (coordQ b 5 (bits 5) * coordQ b 6 (bits 6))
  have q7 := loMulQ_le hb4 (coordQ b 5 (bits 5) * coordQ b 7 (bits 7))
  have q8 := loMulQ_le hb5 (coordQ b 6 (bits 6) * coordQ b 7 (bits 7))
  push_cast at q3 q4 q5 q6 q7 q8
  rw [f5] at q0 q3
  rw [f6] at q1 q4
  rw [f7] at q2 q5
  rw [f5, f6] at q6
  rw [f5, f7] at q7
  rw [f6, f7] at q8
  have e := offPart_eq l p
  unfold linOffQ
  push_cast
  have : Sz * Sz * offPart l p = Sz * (Sz * offPart l p) := by ring
  rw [this, e]
  nlinarith [q0, q1, q2, q3, q4, q5, q6, q7, q8]

/-- `Q*` as a linear form in the reciprocal metric features. -/
theorem dualQ_feat (m : IntVec) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    dualQ m p = ((m 0 * m 0 : ℤ) : ℝ) * featGen p 6 + ((m 1 * m 1 : ℤ) : ℝ) * featGen p 7 +
      ((m 2 * m 2 : ℤ) : ℝ) * featGen p 8 + ((m 0 * m 1 : ℤ) : ℝ) * featGen p 9 +
      ((m 0 * m 2 : ℤ) : ℝ) * featGen p 10 + ((m 1 * m 2 : ℤ) : ℝ) * featGen p 11 := by
  have h := termQ_feat .wave m p h0 h1
  have e : termQ .wave m p = dualQ m p := rfl
  rw [e] at h
  rw [h]
  simp [qForm, mom, Fin.sum_univ_succ]
  ring

theorem dualHi_ge (sh : Shape) (m : IntVec) (p : Chart) (hm : ShapeMem sh p)
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) : Sz * dualQ m p ≤ (dualHi sh m : ℝ) := by
  rw [dualQ_feat m p h0 h1]
  have e0 := highDot_ge (m 0 * m 0) hm.d0
  have e1 := highDot_ge (m 1 * m 1) hm.d1
  have e2 := highDot_ge (m 2 * m 2) hm.d2
  have e3 := highDot_ge (m 0 * m 1) hm.d3
  have e4 := highDot_ge (m 0 * m 2) hm.d4
  have e5 := highDot_ge (m 1 * m 2) hm.d5
  unfold dualHi
  push_cast at e0 e1 e2 e3 e4 e5 ⊢
  nlinarith [e0, e1, e2, e3, e4, e5]

theorem nlTerm_ge (s : ℚ) (hs : 0 < s) (sh : Shape) (m : IntVec) (p : Chart) (hm : ShapeMem sh p)
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (hy : nlY s sh m ≤ (S64 : ℤ)) :
    Sz * nlVal s m p ≤ (nlTerm s sh m : ℝ) := by
  have sp := Sz_pos
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  set y : ℝ := Real.pi * dualQ m p / (s : ℝ) ^ 2 with hyy
  have y0 : 0 ≤ y := by have := dualQ_nonneg m p; positivity
  have dh := dualHi_ge sh m p hm h0 h1
  have dq0 : 0 ≤ Sz * dualQ m p := mul_nonneg sp.le (dualQ_nonneg m p)
  have pih := piF_mem.2
  rw [le_div_iff₀ sp] at pih
  have num0 : (0 : ℝ) < (s.num : ℝ) := by exact_mod_cast Rat.num_pos.mpr hs
  have den0 : (0 : ℝ) < (s.den : ℝ) := by exact_mod_cast s.pos
  have sNum : (s : ℝ) = (s.num : ℝ) / (s.den : ℝ) := Rat.cast_def s
  -- `nlY ≥ S y`
  have yLe : Sz * y ≤ (nlY s sh m : ℝ) := by
    unfold nlY
    refine le_trans ?_ (le_cdiv _ _ (by
      have : (0 : ℤ) < s.num := Rat.num_pos.mpr hs
      have := Sz_posZ
      positivity))
    push_cast
    rw [le_div_iff₀ (by positivity), hyy, sNum]
    have prod : Real.pi * Sz * (Sz * dualQ m p) ≤ (piF.hi : ℝ) * (dualHi sh m : ℝ) :=
      mul_le_mul pih dh dq0 (le_of_lt piF_hi_pos)
    have e : Sz * (Real.pi * dualQ m p / ((s.num : ℝ) / (s.den : ℝ)) ^ 2) * (Sz * (s.num : ℝ) ^ 2) =
        Real.pi * Sz * (Sz * dualQ m p) * (s.den : ℝ) ^ 2 := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right prod (by positivity)
  have nY0 : (0 : ℝ) ≤ (nlY s sh m : ℝ) := le_trans (by positivity) yLe
  have ex := expUpZ_ge hy
  have exy : Real.exp y ≤ Real.exp ((nlY s sh m : ℝ) / Sz) := by
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ sp]
    linarith
  have ex0 : (0 : ℝ) ≤ (expUpZ (nlY s sh m) : ℝ) := by
    have := (Real.exp_pos ((nlY s sh m : ℝ) / Sz)).le.trans ex
    rw [le_div_iff₀ sp] at this
    linarith
  unfold nlTerm
  refine le_trans ?_ (le_cdiv _ _ Sz_posZ)
  push_cast
  rw [le_div_iff₀ sp]
  have h1' : Sz * y * (Sz * Real.exp y) ≤ (nlY s sh m : ℝ) * (expUpZ (nlY s sh m) : ℝ) := by
    apply mul_le_mul yLe _ (by positivity) nY0
    rw [le_div_iff₀ sp] at ex
    have := mul_le_mul_of_nonneg_left exy sp.le
    linarith
  have nv : nlVal s m p = y * Real.exp y := by
    unfold nlVal
    rw [hyy]
  rw [nv]
  calc Sz * (y * Real.exp y) * Sz = Sz * y * (Sz * Real.exp y) := by ring
    _ ≤ _ := h1'

theorem nlHi_ge (s : ℚ) (hs : 0 < s) (nls : List (IntVec × ℤ)) (sh : Shape) (p : Chart)
    (hm : ShapeMem sh p) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (hok : nlOk s nls sh = true)
    (hnn : nlsNonneg nls = true) : Sz * Sz * aggNLR s nls p ≤ (nlHi s nls sh : ℝ) := by
  have sp := Sz_pos
  induction nls with
  | nil => simp [aggNLR, nlHi]
  | cons e rest ih =>
    simp only [nlOk, nlsNonneg, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok hnn
    have t := nlTerm_ge s hs sh e.1 p hm h0 h1 hok.1
    have c0 : (0 : ℝ) ≤ (e.2 : ℝ) := by exact_mod_cast hnn.1
    have r := ih hok.2 hnn.2
    have aC : aggNLR s (e :: rest) p = (e.2 : ℝ) / Sz * nlVal s e.1 p + aggNLR s rest p := by
      simp [aggNLR]
    have nC : nlHi s (e :: rest) sh = e.2 * nlTerm s sh e.1 + nlHi s rest sh := by
      simp [nlHi]
    rw [aC, nC, Int.cast_add, Int.cast_mul]
    have key : Sz * Sz * ((e.2 : ℝ) / Sz * nlVal s e.1 p + aggNLR s rest p) =
        (e.2 : ℝ) * (Sz * nlVal s e.1 p) + Sz * Sz * aggNLR s rest p := by
      field_simp
    have k2 := mul_le_mul_of_nonneg_left t c0
    rw [key]
    linarith

theorem scZ_ge (s : ℚ) : Sz * Sz * (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2) ≤ (scZ s : ℝ) := by
  unfold scZ
  have h := le_cmulQ (Sz * Sz) (selfConst s)
  rw [selfConst_cast] at h
  push_cast at h
  exact h

/-- **The support sum at a corner.** -/
theorem sig_le (s : ℚ) (hs : 0 < s) (agg : Agg) (b : Cell) (bits : Axis → Bool)
    (hm : ShapeMem (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) (corner b bits))
    (h0 : corner b bits 0 ≠ 0) (h1 : corner b bits 1 ≠ 0)
    (hok : nlOk s agg.nls (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) = true)
    (hnn : nlsNonneg agg.nls = true) :
    (sigAt (baseOf s agg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)))
      (offCoef agg.lin (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) : ℝ) ≤ Sz * Sz * (2 * ac * minorant s agg (corner b bits)) := by
  set sh := shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4) with hsh
  set p := corner b bits with hp
  have l1 := linShape_le agg.lin sh p hm
  have l2 := linOffQ_le agg.lin sh b bits hm
  have l3 := nlHi_ge s hs agg.nls sh p hm h0 h1 hok hnn
  have l4 := scZ_ge s
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  have e : 2 * ac * minorant s agg p = shapePart agg.lin p + offPart agg.lin p - aggNLR s agg.nls p -
      (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2) := by
    have hac : ac ≠ 0 := ne_of_gt ac_positive
    unfold minorant
    rw [val_split]
    field_simp
  rw [e]
  unfold sigAt baseOf
  push_cast
  nlinarith [l1, l2, l3, l4]

/-! ### The registered cost at a corner -/

theorem strainHi_ge (reg : RegData) (sh : Shape) (p : Chart) (hm : ShapeMem sh p) :
    Sz * strainCost reg.N reg.U p ≤ (strainHi reg sh : ℝ) := by
  have sp := Sz_pos
  have row0 (j : Fin 3) : (FI.mul sh.r1 (((qF (reg.N 0 j)).add (FI.mul sh.x (qF (reg.N 1 j)))).add
      (FI.mul sh.y (qF (reg.N 2 j))))).Mem (strainEntry reg.N p 0 j) :=
    FI.mul_mem hm.r1 (FI.add_mem (FI.add_mem (qF_mem _) (FI.mul_mem hm.x (qF_mem _)))
      (FI.mul_mem hm.y (qF_mem _)))
  have row1 (j : Fin 3) : (FI.mul sh.r2 ((qF (reg.N 1 j)).add (FI.mul sh.z (qF (reg.N 2 j))))).Mem
      (strainEntry reg.N p 1 j) :=
    FI.mul_mem hm.r2 (FI.add_mem (qF_mem _) (FI.mul_mem hm.z (qF_mem _)))
  have row2 (j : Fin 3) : (FI.mul (qF (reg.N 2 j)) sh.rr).Mem (strainEntry reg.N p 2 j) := by
    have h := FI.mul_mem (qF_mem (reg.N 2 j)) hm.rr
    have e : strainEntry reg.N p 2 j = (reg.N 2 j : ℝ) * (p 0 * p 1)⁻¹ := by
      simp [strainEntry, div_eq_mul_inv]
    rw [e]
    exact h
  have sqHi {a : FI} {x : ℝ} (hx : a.Mem x) (u : ℚ) :
      Sz * (x - (u : ℝ)) ^ 2 ≤ ((FI.sq (a.sub (qF u))).hi : ℝ) := by
    have h := (FI.sq_mem (FI.sub_mem hx (qF_mem u))).2
    rw [le_div_iff₀ sp] at h
    linarith
  have c00 := sqHi (row0 0) (reg.U 0 0)
  have c01 := sqHi (row0 1) (reg.U 0 1)
  have c02 := sqHi (row0 2) (reg.U 0 2)
  have c10 := sqHi (row1 0) (reg.U 1 0)
  have c11 := sqHi (row1 1) (reg.U 1 1)
  have latticeCase := sqHi (row1 2) (reg.U 1 2)
  have c20 := sqHi (row2 0) (reg.U 2 0)
  have c21 := sqHi (row2 1) (reg.U 2 1)
  have c22 := sqHi (row2 2) (reg.U 2 2)
  unfold strainCost strainHi
  simp only [Fin.sum_univ_three]
  push_cast
  nlinarith [c00, c01, c02, c10, c11, latticeCase, c20, c21, c22]

theorem offset_0 : DirectRoute.offset 0 = 5 := rfl
theorem offset_1 : DirectRoute.offset 1 = 6 := rfl
theorem offset_2 : DirectRoute.offset 2 = 7 := rfl

/-- `|R (f + v)|²` as a quadratic form in the metric features. -/
theorem primalQ_feat (v : Fin 3 → ℚ) (p : Chart) (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    primalQ v true p = featGen p 0 * ((v 0 : ℝ) + p 5) ^ 2 + featGen p 1 * ((v 1 : ℝ) + p 6) ^ 2 +
      featGen p 2 * ((v 2 : ℝ) + p 7) ^ 2 + featGen p 3 * (((v 0 : ℝ) + p 5) * ((v 1 : ℝ) + p 6)) +
      featGen p 4 * (((v 0 : ℝ) + p 5) * ((v 2 : ℝ) + p 7)) +
      featGen p 5 * (((v 1 : ℝ) + p 6) * ((v 2 : ℝ) + p 7)) := by
  rw [fg0, fg1, fg2, fg3, fg4, fg5]
  simp only [primalQ, rowA, rowB, rowC, img, ite_true, offset_0, offset_1, offset_2]
  field_simp
  ring

theorem shiftQ_ge (reg : RegData) (sh : Shape) (b : Cell) (bits : Axis → Bool)
    (hm : ShapeMem sh (corner b bits)) (h0 : corner b bits 0 ≠ 0) (h1 : corner b bits 1 ≠ 0) :
    Sz * primalQ (fun i => -reg.w i) true (corner b bits) ≤
      (shiftQ sh (coordQ b 5 (bits 5) - reg.w 0) (coordQ b 6 (bits 6) - reg.w 1)
        (coordQ b 7 (bits 7) - reg.w 2) : ℝ) := by
  set p := corner b bits with hp
  have f5 := coordQ_eq b bits 5
  have f6 := coordQ_eq b bits 6
  have f7 := coordQ_eq b bits 7
  rw [← hp] at f5 f6 f7
  rw [primalQ_feat _ p h0 h1]
  set e0 : ℚ := coordQ b 5 (bits 5) - reg.w 0
  set e1 : ℚ := coordQ b 6 (bits 6) - reg.w 1
  set e2 : ℚ := coordQ b 7 (bits 7) - reg.w 2
  have r0 : ((-reg.w 0 : ℚ) : ℝ) + p 5 = (e0 : ℝ) := by simp [e0, f5]; ring
  have r1 : ((-reg.w 1 : ℚ) : ℝ) + p 6 = (e1 : ℝ) := by simp [e1, f6]; ring
  have r2 : ((-reg.w 2 : ℚ) : ℝ) + p 7 = (e2 : ℝ) := by simp [e2, f7]; ring
  rw [r0, r1, r2]
  have q0 := hiMulQ_ge hm.g0 (e0 * e0)
  have q1 := hiMulQ_ge hm.g1 (e1 * e1)
  have q2 := hiMulQ_ge hm.g2 (e2 * e2)
  have q3 := hiMulQ_ge hm.g3 (e0 * e1)
  have q4 := hiMulQ_ge hm.g4 (e0 * e2)
  have q5 := hiMulQ_ge hm.g5 (e1 * e2)
  push_cast at q0 q1 q2 q3 q4 q5
  unfold shiftQ
  push_cast
  nlinarith [q0, q1, q2, q3, q4, q5]

/-- **The registered cost at a corner.** -/
theorem cost_ge (reg : RegData) (b : Cell) (bits : Axis → Bool)
    (hm : ShapeMem (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) (corner b bits))
    (h0 : corner b bits 0 ≠ 0) (h1 : corner b bits 1 ≠ 0) :
    Sz * regCost reg.N reg.U reg.w (corner b bits) ≤
      (costAt reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))
        (strainHi reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
        (bits 7) : ℝ) := by
  have c1 := strainHi_ge reg _ _ hm
  have c2 := shiftQ_ge reg _ b bits hm h0 h1
  unfold regCost costAt
  push_cast
  nlinarith [c1, c2]

/-! ### From the nested checks to the corners -/

theorem all_bool {P : Bool → Bool} (h : bools.all P = true) (c : Bool) : P c = true := by
  simp only [bools, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  cases c
  · exact h.1
  · exact h.2

theorem pos_of_corners {b : Cell} {f : Chart → ℝ} (chord : ChordLower b f)
    (h : ∀ bits, 0 < f (corner b bits)) (p : Chart) (hp : b.Mem p) : 0 < f p := by
  obtain ⟨bits, hb⟩ := corner_le b f chord p hp
  exact (h bits).trans_le hb

theorem le_of_corners {b : Cell} {f : Chart → ℝ} {c : ℝ} (chord : ChordUpper b f)
    (h : ∀ bits, f (corner b bits) ≤ c) (p : Chart) (hp : b.Mem p) : f p ≤ c := by
  obtain ⟨bits, hb⟩ := corner_le b (fun x => -f x) chord p hp
  have := h bits
  linarith

theorem acMulHi_ge (X : ℤ) : Sz * (2 * ac) * (X : ℝ) ≤ (acMulHi X : ℝ) := by
  have sp := Sz_pos
  have l := acF_mem.1
  have u := acF_mem.2
  rw [div_le_iff₀ sp] at l
  rw [le_div_iff₀ sp] at u
  unfold acMulHi
  split_ifs with hX
  · have hX' : (0 : ℝ) ≤ X := by exact_mod_cast hX
    push_cast
    have := mul_le_mul_of_nonneg_right u hX'
    linarith
  · have hX' : (X : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hX))
    push_cast
    have := mul_le_mul_of_nonpos_right l hX'
    linarith

theorem regCost_nonneg (N U : Fin 3 → Fin 3 → ℚ) (w : Fin 3 → ℚ) (p : Chart) :
    0 ≤ regCost N U w p := by
  unfold regCost strainCost primalQ
  have a : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, (strainEntry N p i j - (U i j : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have b : 0 ≤ (rowC (fun i => -w i) true p) ^ 2 / ((p 0) ^ 2 * (p 1) ^ 2) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have c : 0 ≤ (p 0) ^ 2 * (rowA (fun i => -w i) true p) ^ 2 := by positivity
  have d : 0 ≤ (p 1) ^ 2 * (rowB (fun i => -w i) true p) ^ 2 := by positivity
  linarith

/-- The facts at one corner shared by the three leaf checks. -/
theorem corner_facts (s : ℚ) (hs : 0 < s) (agg : Agg) (b : Cell) (bits : Axis → Bool)
    (b0 : (0 : ℝ) < b.lo 0) (b1 : (0 : ℝ) < b.lo 1) (ord : ∀ i, (b.lo i : ℝ) ≤ b.hi i)
    (hg : shapeGuard (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) = true)
    (hok : nlOk s agg.nls (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) = true)
    (hnn : nlsNonneg agg.nls = true) :
    ShapeMem (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)) (corner b bits) ∧
    corner b bits 0 ≠ 0 ∧ corner b bits 1 ≠ 0 ∧
    (sigAt (baseOf s agg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)))
      (offCoef agg.lin (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) : ℝ) ≤ Sz * Sz * (2 * ac * minorant s agg (corner b bits)) := by
  have hm := shapeOf_mem b bits hg
  have c0 := (corner_pos b bits 0 b0 (ord 0)).ne'
  have c1 := (corner_pos b bits 1 b1 (ord 1)).ne'
  exact ⟨hm, c0, c1, sig_le s hs agg b bits hm c0 c1 hok hnn⟩

theorem leafGuards_sound {box b : Cell} (h : leafGuards box b = true) :
    boxIn b box = true ∧ (0 : ℝ) < b.lo 0 ∧ (0 : ℝ) < b.lo 1 ∧ ∀ i, (b.lo i : ℝ) ≤ b.hi i := by
  simp only [leafGuards, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hin, l0⟩, l1⟩, ord⟩ := h
  exact ⟨hin, by exact_mod_cast l0, by exact_mod_cast l1, fun i => by exact_mod_cast ord i⟩

theorem regGuards_sound {reg : RegData} {b : Cell} (h : regGuards reg b = true) :
    registrationCheck reg.B reg.N reg.U reg.f0 = true ∧ (∀ i, ∑ j, (reg.U i j) ^ 2 = 1) ∧
      4 * (b.hi 0 * b.hi 1) ^ 2 ≤ 9 * ∑ j, (reg.N 2 j) ^ 2 := by
  simp only [regGuards, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ### The whole-box defect cap -/

/-- **Whole-box defect cap.** If a registration passes `regGuards` and its
registered cost is at most `cap/S ≤ 1/2` at every corner of a box with positive
radial coordinates, then the actual capped defect is at most `cap/S` at every
valid point of the box. -/
theorem defect_le_cap (reg : RegData) (b : Cell) (cap : ℤ) (hr : regGuards reg b = true)
    (b0 : (0 : ℝ) < b.lo 0) (b1 : (0 : ℝ) < b.lo 1) (hcap : 2 * cap ≤ Sz)
    (hc : ∀ bits, regCost reg.N reg.U reg.w (corner b bits) ≤ (cap : ℝ) / Sz)
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) : defect (chartPoint p) ≤ (cap : ℝ) / Sz := by
  obtain ⟨hreg, unit, cond⟩ := regGuards_sound hr
  have chord := regCost_chord reg.N reg.U reg.w b b0 b1 unit cond
  have hpC := le_of_corners chord hc p hp
  have sp := Sz_pos
  have half : (cap : ℝ) / Sz ≤ 1 / 2 := by
    rw [div_le_iff₀ sp]
    have : ((2 * cap : ℤ) : ℝ) ≤ (Sz : ℝ) := by exact_mod_cast hcap
    push_cast at this
    linarith
  have small : regCost reg.N reg.U (fun i => reg.f0 i + (reg.wrap i : ℚ)) p ≤ 1 / 2 := by
    have e : (fun i => reg.f0 i + (reg.wrap i : ℚ)) = reg.w := rfl
    rw [e]
    linarith
  have hd := defect_le_regCost reg.B reg.N reg.U reg.f0 reg.wrap hreg p hv small
  have e : (fun i => reg.f0 i + (reg.wrap i : ℚ)) = reg.w := rfl
  rw [e] at hd
  linarith

/-! ### The J leaf -/

/-- **Soundness of the fixed-point J leaf check.** -/
theorem jleafFix_sound (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (n : ℕ)
    (hs : SupportFacts s box agg) (hl : jLeafOk s box b agg reg n = true) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) : 0 < deficit (chartPoint p) := by
  unfold jLeafOk at hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨hgd, hrg⟩, hn⟩, hnn⟩, hall⟩ := hl
  obtain ⟨inside, b0, b1, ord⟩ := leafGuards_sound hgd
  obtain ⟨hreg, unit, cond⟩ := regGuards_sound hrg
  have sp := Sz_pos
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  set T := minorant s agg with hT
  set C : Chart → ℝ := regCost reg.N reg.U reg.w with hC
  set t : ℝ := (n : ℝ) / 4096 with ht
  have t0 : 0 ≤ t := by positivity
  have t1 : t ≤ 1 := by
    rw [ht, div_le_one (by norm_num)]
    exact_mod_cast hn
  have g0 := gap_pos.le
  have gle := gap_le
  have ble := bcc_le
  -- the corners
  have corners : ∀ bits, C (corner b bits) ≤ 1 / 2 ∧
      0 < T (corner b bits) - energy bcc - gap * (1 - t + t * C (corner b bits)) := by
    intro bits
    have h5 := all_bool (all_bool (all_bool (all_bool (all_bool hall (bits 0)) (bits 1)) (bits 2))
      (bits 3)) (bits 4)
    simp only [jShape, Bool.and_eq_true] at h5
    obtain ⟨⟨hg, hok⟩, hoff⟩ := h5
    obtain ⟨hm, c0, c1, hsig⟩ := corner_facts s hs.pos agg b bits b0 b1 ord hg hok hnn
    have hcost := cost_ge reg b bits hm c0 c1
    rw [← hC] at hcost
    have h8 := all_bool (all_bool (all_bool hoff (bits 5)) (bits 6)) (bits 7)
    simp only [jCornerOk, Bool.and_eq_true, decide_eq_true_eq] at h8
    obtain ⟨hC2, hcmp⟩ := h8
    set Cz := costAt reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))
      (strainHi reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hCz
    set sig := sigAt (baseOf s agg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)))
      (offCoef agg.lin (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hsigd
    have hC2r : 2 * (Cz : ℝ) ≤ Sz := by exact_mod_cast hC2
    have cLe : C (corner b bits) ≤ (Cz : ℝ) / Sz := by
      rw [le_div_iff₀ sp]
      linarith
    have cNn : 0 ≤ C (corner b bits) := regCost_nonneg _ _ _ _
    refine ⟨cLe.trans (by rw [div_le_iff₀ sp]; linarith), ?_⟩
    have X := acMulHi_ge (bccHiZ * Sz * 4096 + gapHiZ * ((4096 - (n : ℤ)) * Sz + (n : ℤ) * Cz))
    have hcmpR : (acMulHi (bccHiZ * Sz * 4096 + gapHiZ * ((4096 - (n : ℤ)) * Sz + (n : ℤ) * Cz)) : ℝ) <
        (sig : ℝ) * Sz * 4096 := by exact_mod_cast hcmp
    -- `T > X/(S² 4096)`
    set Xr : ℝ := ((bccHiZ * Sz * 4096 + gapHiZ * ((4096 - (n : ℤ)) * Sz + (n : ℤ) * Cz) : ℤ) : ℝ)
      with hXr
    have step1 : Sz * (2 * ac) * Xr < Sz * Sz * (2 * ac * T (corner b bits)) * Sz * 4096 := by
      have := mul_le_mul_of_nonneg_right hsig (by norm_num : (0 : ℝ) ≤ 4096)
      have h2 : (sig : ℝ) * Sz * 4096 ≤ Sz * Sz * (2 * ac * T (corner b bits)) * Sz * 4096 := by
        have := mul_le_mul_of_nonneg_right hsig (by positivity : (0 : ℝ) ≤ Sz * 4096)
        linarith
      linarith
    have step2 : Xr < Sz * Sz * T (corner b bits) * 4096 := by
      have hpos : 0 < Sz * (2 * ac) := mul_pos sp acpos
      have e : Sz * Sz * (2 * ac * T (corner b bits)) * Sz * 4096 =
          Sz * (2 * ac) * (Sz * Sz * T (corner b bits) * 4096) := by ring
      rw [e] at step1
      exact lt_of_mul_lt_mul_left step1 hpos.le
    -- `X/(S² 4096) ≥ e_BCC + g (1 − t + t C)`
    have nR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have mixLe : Sz * (1 - t + t * C (corner b bits)) * 4096 ≤
        (4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz := by
      rw [ht]
      have := mul_le_mul_of_nonneg_left hcost nR
      field_simp
      nlinarith
    have mix0 : 0 ≤ 1 - t + t * C (corner b bits) := by nlinarith
    have gapM : Sz * Sz * (gap * (1 - t + t * C (corner b bits))) * 4096 ≤
        (gapHiZ : ℝ) * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) := by
      rw [le_div_iff₀ sp] at gle
      have hM := mul_le_mul_of_nonneg_left mixLe g0
      have hG : gap * Sz * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) ≤
          (gapHiZ : ℝ) * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) := by
        apply mul_le_mul_of_nonneg_right gle
        have := mul_nonneg (mul_nonneg sp.le mix0) (by norm_num : (0 : ℝ) ≤ 4096)
        linarith
      nlinarith
    have bccM : Sz * Sz * energy bcc * 4096 ≤ (bccHiZ : ℝ) * Sz * 4096 := by
      rw [le_div_iff₀ sp] at ble
      nlinarith
    have Xe : Xr = (bccHiZ : ℝ) * Sz * 4096 + (gapHiZ : ℝ) * ((4096 - (n : ℝ)) * Sz + (n : ℝ) * Cz) := by
      rw [hXr]; push_cast; ring
    rw [Xe] at step2
    have fin : Sz * Sz * (energy bcc + gap * (1 - t + t * C (corner b bits))) * 4096 <
        Sz * Sz * T (corner b bits) * 4096 := by
      nlinarith
    have hpos : (0 : ℝ) < Sz * Sz * 4096 := by positivity
    have : energy bcc + gap * (1 - t + t * C (corner b bits)) < T (corner b bits) := by
      have e1 : Sz * Sz * (energy bcc + gap * (1 - t + t * C (corner b bits))) * 4096 =
          (Sz * Sz * 4096) * (energy bcc + gap * (1 - t + t * C (corner b bits))) := by ring
      have e2 : Sz * Sz * T (corner b bits) * 4096 = (Sz * Sz * 4096) * T (corner b bits) := by ring
      rw [e1, e2] at fin
      exact lt_of_mul_lt_mul_left fin hpos.le
    linarith
  -- chords
  have hTc : ChordLower b T := hs.chord b b0 b1
  have hCc : ChordUpper b C := regCost_chord reg.N reg.U reg.w b b0 b1 unit cond
  set f : Chart → ℝ := fun x => T x - energy bcc - gap * (1 - t + t * C x) with hf
  have fc : ChordLower b f := by
    have h1 := chordLower_add hTc (chordLower_const b (-(energy bcc) - gap * (1 - t)))
    have h2 := chordLower_negSmul (c := -(gap * t)) (by nlinarith) hCc
    exact chordLower_congr (fun x => by simp only [hf]; ring) (chordLower_add h1 h2)
  have fpos := pos_of_corners fc (fun bits => (corners bits).2) p hp
  have cHalf := le_of_corners hCc (fun bits => (corners bits).1) p hp
  -- the deficit
  have hE := hs.lower p (boxIn_sound inside hp) hv
  have small : regCost reg.N reg.U (fun i => reg.f0 i + (reg.wrap i : ℚ)) p ≤ 1 / 2 := cHalf
  have hD := defect_le_regCost reg.B reg.N reg.U reg.f0 reg.wrap hreg p hv small
  have hd := defect_range (chartPoint p)
  have cap : defect (chartPoint p) ≤ 1 - t + t * C p := by
    have c1 := mul_le_mul_of_nonneg_left hd.2 (sub_nonneg.mpr t1)
    have c2 := mul_le_mul_of_nonneg_left hD t0
    show defect (chartPoint p) ≤ 1 - t + t * regCost reg.N reg.U reg.w p
    have e : (fun i => reg.f0 i + (reg.wrap i : ℚ)) = reg.w := rfl
    rw [e] at c2
    nlinarith
  have credit := mul_le_mul_of_nonneg_left cap g0
  have fp : 0 < T p - energy bcc - gap * (1 - t + t * C p) := fpos
  unfold deficit
  linarith

theorem jleafFix_sound_good (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (n : ℕ)
    (hs : SupportFacts s box agg) (hl : jLeafOk s box b agg reg n = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) : Route.result .strictJoint p :=
  jleafFix_sound s box b agg reg n hs hl p hp gp.1

/-! ### The D leaf -/

/-- **Soundness of the fixed-point D leaf check**, with its whole-box defect cap. -/
theorem dleafFix_sound (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (cap : ℤ)
    (hs : SupportFacts s box agg) (hl : dLeafOk s box b agg reg cap = true) (p : Chart)
    (hp : b.Mem p) (hv : (chartPoint p).Valid) : 0 < deficit (chartPoint p) := by
  unfold dLeafOk at hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨hgd, hrg⟩, hcap⟩, hnn⟩, hall⟩ := hl
  obtain ⟨inside, b0, b1, ord⟩ := leafGuards_sound hgd
  have sp := Sz_pos
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  set T := minorant s agg with hT
  set C : Chart → ℝ := regCost reg.N reg.U reg.w with hC
  have g0 := gap_pos.le
  have gle := gap_le
  have ble := bcc_le
  have corners : ∀ bits, C (corner b bits) ≤ (cap : ℝ) / Sz ∧
      0 < T (corner b bits) - energy bcc - gap * ((cap : ℝ) / Sz) := by
    intro bits
    have h5 := all_bool (all_bool (all_bool (all_bool (all_bool hall (bits 0)) (bits 1)) (bits 2))
      (bits 3)) (bits 4)
    simp only [dShape, Bool.and_eq_true] at h5
    obtain ⟨⟨hg, hok⟩, hoff⟩ := h5
    obtain ⟨hm, c0, c1, hsig⟩ := corner_facts s hs.pos agg b bits b0 b1 ord hg hok hnn
    have hcost := cost_ge reg b bits hm c0 c1
    rw [← hC] at hcost
    have h8 := all_bool (all_bool (all_bool hoff (bits 5)) (bits 6)) (bits 7)
    simp only [dCornerOk, Bool.and_eq_true, decide_eq_true_eq] at h8
    obtain ⟨hCc, hcmp⟩ := h8
    set Cz := costAt reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))
      (strainHi reg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hCz
    set sig := sigAt (baseOf s agg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)))
      (offCoef agg.lin (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hsigd
    have hCcr : (Cz : ℝ) ≤ cap := by exact_mod_cast hCc
    have cLe : C (corner b bits) ≤ (cap : ℝ) / Sz := by
      rw [le_div_iff₀ sp]
      linarith
    have cap0 : (0 : ℝ) ≤ (cap : ℝ) := by
      have := regCost_nonneg reg.N reg.U reg.w (corner b bits)
      have := mul_nonneg sp.le this
      linarith
    refine ⟨cLe, ?_⟩
    have X := acMulHi_ge (bccHiZ * Sz + gapHiZ * cap)
    have hcmpR : (acMulHi (bccHiZ * Sz + gapHiZ * cap) : ℝ) < (sig : ℝ) * Sz := by exact_mod_cast hcmp
    have step2 : ((bccHiZ * Sz + gapHiZ * cap : ℤ) : ℝ) < Sz * Sz * T (corner b bits) := by
      have h2 : (sig : ℝ) * Sz ≤ Sz * Sz * (2 * ac * T (corner b bits)) * Sz :=
        mul_le_mul_of_nonneg_right hsig sp.le
      have hpos : 0 < Sz * (2 * ac) := mul_pos sp acpos
      have e : Sz * Sz * (2 * ac * T (corner b bits)) * Sz = Sz * (2 * ac) * (Sz * Sz * T (corner b bits)) := by
        ring
      have : Sz * (2 * ac) * ((bccHiZ * Sz + gapHiZ * cap : ℤ) : ℝ) <
          Sz * (2 * ac) * (Sz * Sz * T (corner b bits)) := by linarith
      exact lt_of_mul_lt_mul_left this hpos.le
    push_cast at step2
    have gapM : Sz * Sz * (gap * ((cap : ℝ) / Sz)) ≤ (gapHiZ : ℝ) * cap := by
      rw [le_div_iff₀ sp] at gle
      have e : Sz * Sz * (gap * ((cap : ℝ) / Sz)) = gap * Sz * cap := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right gle cap0
    have bccM : Sz * Sz * energy bcc ≤ (bccHiZ : ℝ) * Sz := by
      rw [le_div_iff₀ sp] at ble
      nlinarith
    have hpos : (0 : ℝ) < Sz * Sz := by positivity
    have : energy bcc + gap * ((cap : ℝ) / Sz) < T (corner b bits) := by
      have fin : (Sz * Sz) * (energy bcc + gap * ((cap : ℝ) / Sz)) < (Sz * Sz) * T (corner b bits) := by
        nlinarith
      exact lt_of_mul_lt_mul_left fin hpos.le
    linarith
  have hTc : ChordLower b T := hs.chord b b0 b1
  set f : Chart → ℝ := fun x => T x - energy bcc - gap * ((cap : ℝ) / Sz) with hf
  have fc : ChordLower b f :=
    chordLower_congr (fun x => by simp only [hf]; ring)
      (chordLower_add hTc (chordLower_const b (-(energy bcc) - gap * ((cap : ℝ) / Sz))))
  have fpos := pos_of_corners fc (fun bits => (corners bits).2) p hp
  have capR : 2 * cap ≤ Sz := hcap
  have hD := defect_le_cap reg b cap hrg b0 b1 capR (fun bits => (corners bits).1) p hp hv
  have hE := hs.lower p (boxIn_sound inside hp) hv
  have credit := mul_le_mul_of_nonneg_left hD g0
  have fp : 0 < T p - energy bcc - gap * ((cap : ℝ) / Sz) := fpos
  unfold deficit
  linarith

theorem dleafFix_sound_good (s : ℚ) (box b : Cell) (agg : Agg) (reg : RegData) (cap : ℤ)
    (hs : SupportFacts s box agg) (hl : dLeafOk s box b agg reg cap = true) (p : Chart)
    (hp : b.Mem p) (gp : good p) : Route.result .strictDeficit p :=
  dleafFix_sound s box b agg reg cap hs hl p hp gp.1

/-! ### The F leaf -/

/-- **Soundness of the fixed-point F leaf check.** -/
theorem fleafFix_sound (s : ℚ) (box b : Cell) (agg : Agg) (hs : SupportFacts s box agg)
    (hl : fLeafOk s box b agg = true) (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) := by
  unfold fLeafOk at hl
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨hgd, hnn⟩, hall⟩ := hl
  obtain ⟨inside, b0, b1, ord⟩ := leafGuards_sound hgd
  have sp := Sz_pos
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  set T := minorant s agg with hT
  have fle := fcc_le
  have corners : ∀ bits, 0 < T (corner b bits) - energy fcc := by
    intro bits
    have h5 := all_bool (all_bool (all_bool (all_bool (all_bool hall (bits 0)) (bits 1)) (bits 2))
      (bits 3)) (bits 4)
    simp only [fShape, Bool.and_eq_true] at h5
    obtain ⟨⟨hg, hok⟩, hoff⟩ := h5
    obtain ⟨_, _, _, hsig⟩ := corner_facts s hs.pos agg b bits b0 b1 ord hg hok hnn
    have h8 := all_bool (all_bool (all_bool hoff (bits 5)) (bits 6)) (bits 7)
    simp only [fCornerOk, decide_eq_true_eq] at h8
    set sig := sigAt (baseOf s agg (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)))
      (offCoef agg.lin (shapeOf b (bits 0) (bits 1) (bits 2) (bits 3) (bits 4))) b (bits 5) (bits 6)
      (bits 7) with hsigd
    have X := acMulHi_ge fccHiZ
    have hcmp : (acMulHi fccHiZ : ℝ) < (sig : ℝ) := by exact_mod_cast h8
    have hpos : 0 < Sz * (2 * ac) := mul_pos sp acpos
    have step : Sz * (2 * ac) * (fccHiZ : ℝ) < Sz * (2 * ac) * (Sz * T (corner b bits)) := by
      have e : Sz * Sz * (2 * ac * T (corner b bits)) = Sz * (2 * ac) * (Sz * T (corner b bits)) := by ring
      linarith
    have s2 := lt_of_mul_lt_mul_left step hpos.le
    rw [le_div_iff₀ sp] at fle
    nlinarith
  have hTc : ChordLower b T := hs.chord b b0 b1
  have fc : ChordLower b (fun x => T x - energy fcc) :=
    chordLower_congr (fun x => by ring) (chordLower_add hTc (chordLower_const b (-(energy fcc))))
  have fpos := pos_of_corners fc corners p hp
  have hE := hs.lower p (boxIn_sound inside hp) hv
  linarith

theorem fleafFix_sound_good (s : ℚ) (box b : Cell) (agg : Agg) (hs : SupportFacts s box agg)
    (hl : fLeafOk s box b agg = true) (p : Chart) (hp : b.Mem p) (gp : good p) :
    Route.result .strictFCC p :=
  fleafFix_sound s box b agg hs hl p hp gp.1

/-! ### Boxes without reduced points -/

/-- If `r₂² < r₁² (1 − x²)` at the extreme corner of a box with `r₁, r₂ ≥ 0` and
`0 ≤ x ≤ 1`, then `B e₂` is shorter than `B e₁` everywhere in the box, so no
point of the box is reduced (and none is `good`). -/
theorem not_reduced_of_box (b : Cell) (h0 : (0 : ℚ) ≤ b.lo 0) (h1 : (0 : ℚ) ≤ b.lo 1)
    (h2 : (0 : ℚ) ≤ b.lo 2) (h2' : b.hi 2 ≤ 1) (key : b.hi 1 ^ 2 < b.lo 0 ^ 2 * (1 - b.hi 2 ^ 2))
    (p : Chart) (hp : b.Mem p) : ¬ reductionInequalities p := by
  have m0 := hp 0
  have m1 := hp 1
  have m2 := hp 2
  have d0 : (0 : ℝ) ≤ b.lo 0 := by exact_mod_cast h0
  have d1 : (0 : ℝ) ≤ b.lo 1 := by exact_mod_cast h1
  have d2 : (0 : ℝ) ≤ b.lo 2 := by exact_mod_cast h2
  have d2' : (b.hi 2 : ℝ) ≤ 1 := by exact_mod_cast h2'
  have k : (b.hi 1 : ℝ) ^ 2 < (b.lo 0 : ℝ) ^ 2 * (1 - (b.hi 2 : ℝ) ^ 2) := by exact_mod_cast key
  intro hr
  have e := hr.1 ![0, 1, 0] (by decide)
  have e2 : BccSharp.Coulomb.sq ((chartBasis p).mulVec (castVec ![0, 1, 0])) =
      (p 0 * p 2) ^ 2 + (p 1) ^ 2 := by
    simp [BccSharp.Coulomb.sq, chartBasis, castVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  rw [e2] at e
  have p2 : 0 ≤ p 2 := d2.trans m2.1
  have p1 : 0 ≤ p 1 := d1.trans m1.1
  have s2 : p 2 ^ 2 ≤ (b.hi 2 : ℝ) ^ 2 := pow_le_pow_left₀ p2 m2.2 2
  have s0 : (b.lo 0 : ℝ) ^ 2 ≤ p 0 ^ 2 := pow_le_pow_left₀ d0 m0.1 2
  have s1 : p 1 ^ 2 ≤ (b.hi 1 : ℝ) ^ 2 := pow_le_pow_left₀ p1 m1.2 2
  have h22 : (b.hi 2 : ℝ) ^ 2 ≤ 1 := by
    have : (0 : ℝ) ≤ b.hi 2 := d2.trans (m2.1.trans m2.2)
    nlinarith
  have m : p 0 ^ 2 * (1 - (b.hi 2 : ℝ) ^ 2) ≤ p 0 ^ 2 * (1 - p 2 ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have m2' : (b.lo 0 : ℝ) ^ 2 * (1 - (b.hi 2 : ℝ) ^ 2) ≤ p 0 ^ 2 * (1 - (b.hi 2 : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right s0 (by linarith)
  have expand : (p 0 * p 2) ^ 2 = p 0 ^ 2 * p 2 ^ 2 := by ring
  rw [expand] at e
  nlinarith [m, m2', k, s1, e]

/-! ### Certificates in the shape of the cover composition -/

/-- The leaf comparison of a certificate. -/
inductive LeafKind where
  | f
  | d (reg : RegData) (cap : ℤ)
  | j (reg : RegData) (weight : ℕ)

def LeafKind.route : LeafKind → Route
  | .f => .strictFCC
  | .d _ _ => .strictDeficit
  | .j _ _ => .strictJoint

/-- A fixed-point leaf certificate: screening, support box, witnesses,
aggregate, leaf box and leaf comparison. -/
structure LeafCert where
  s : ℚ
  support : Cell
  wits : List Wit
  agg : Agg
  leaf : Cell
  kind : LeafKind

def LeafCert.leafOk (c : LeafCert) : Bool :=
  match c.kind with
  | .f => fLeafOk c.s c.support c.leaf c.agg
  | .d reg cap => dLeafOk c.s c.support c.leaf c.agg reg cap
  | .j reg n => jLeafOk c.s c.support c.leaf c.agg reg n

def LeafCert.check (c : LeafCert) : Bool := supportOk c.s c.support c.wits c.agg && c.leafOk

/-- A certificate whose support facts are already known (for a support shared
by several leaves) proves its route result on its leaf box. -/
theorem LeafCert.sound_of_facts (c : LeafCert) (hs : SupportFacts c.s c.support c.agg)
    (h : c.leafOk = true) (p : Chart) (hp : c.leaf.Mem p) (gp : good p) : c.kind.route.result p := by
  unfold LeafCert.leafOk at h
  cases hk : c.kind with
  | f =>
    rw [hk] at h
    exact fleafFix_sound_good c.s c.support c.leaf c.agg hs h p hp gp
  | d reg cap =>
    rw [hk] at h
    exact dleafFix_sound_good c.s c.support c.leaf c.agg reg cap hs h p hp gp
  | j reg n =>
    rw [hk] at h
    exact jleafFix_sound_good c.s c.support c.leaf c.agg reg n hs h p hp gp

theorem LeafCert.sound (c : LeafCert) (h : c.check = true) (p : Chart) (hp : c.leaf.Mem p)
    (gp : good p) : c.kind.route.result p := by
  obtain ⟨hs, hl⟩ := Bool.and_eq_true_iff.mp h
  exact c.sound_of_facts (support_facts hs) hl p hp gp

/-- A `SoundCheck` from a table of certificates indexed by witness references. -/
def certCheck (table : WitnessRef → Option LeafCert) (w : WitnessRef) (b : Cell) : Bool :=
  match table w with
  | some c => decide (c.kind.route = w.route) && sameCell c.leaf b && c.check
  | none => false

theorem certCheck_sound (table : WitnessRef → Option LeafCert) : SoundCheck (certCheck table) := by
  intro w b h p hp gp
  unfold certCheck at h
  cases hw : table w with
  | none => rw [hw] at h; exact absurd h (by simp)
  | some c =>
    rw [hw] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hc⟩, hk⟩ := h
    have e := sameCell_sound hc
    rw [← e] at hp
    rw [← hr]
    exact c.sound hk p hp gp

/-- A `LatePackets.Checker` from a table of certificates indexed by requests. -/
def lateCheck (table : LatePackets.Request → Option LeafCert) (q : LatePackets.Request) : Bool :=
  match table q with
  | some c => decide (c.kind.route = q.proposal.payload.route) && sameCell c.leaf q.target.box && c.check
  | none => false

theorem lateCheck_sound (table : LatePackets.Request → Option LeafCert) :
    LatePackets.CheckerSound (lateCheck table) := by
  intro q _ _ _ h p hp gp
  unfold lateCheck at h
  cases hq : table q with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some c =>
    rw [hq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hc⟩, hk⟩ := h
    have e := sameCell_sound hc
    rw [← e] at hp
    rw [← hr]
    exact c.sound hk p hp gp

end BccSharp.Coulomb.CompactCover.LeafFix
