import BccSharp.Lattice.CubicMoves

set_option autoImplicit false

/-! Closed chamber reduction. The
folded frame is obtained by integer reindexing of the very same lattice.
No strict inequality is used for chamber membership. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover

private theorem whitenE_pos (ref : Reference) : 0 < (whitenE ref : ℝ) := by
  cases ref <;> norm_num [whitenE]

private theorem whitenT_pos (ref : Reference) : 0 < (whitenT ref : ℝ) := by
  cases ref <;> norm_num [whitenT]

private theorem diagonalCoordinateNorm (ref : Reference) (S : Mat) (ht : diagonalSum S=0) :
    (strainCoordinates ref S 0)^2+(strainCoordinates ref S 1)^2=
      ((S 0 0)^2+(S 1 1)^2+(S 2 2)^2)/(whitenE ref : ℝ)^2 := by
  have e := (whitenE_pos ref).ne'
  have s2 := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have s6 := Real.sq_sqrt (by norm_num : (0 : ℝ)≤6)
  simp only [strainCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,div_pow,mul_pow,s2,s6]
  unfold diagonalSum at ht
  have hz : S 2 2= - (S 0 0) - (S 1 1) := by linarith
  rw [hz]
  field_simp [e] <;> ring

private def shear (ref : Reference) (S : Mat) (i j : Fin 3) : ℝ :=
  Real.sqrt 2*S i j/(whitenT ref : ℝ)

private theorem offDiagonalCoordinateBounds (ref : Reference) (S : Mat) (hs : S.transpose=S)
    (t : ℚ) :
    (∀ i : Fin 5, 2≤ i.val → |strainCoordinates ref S i|≤(t : ℝ)) ↔
      (∀ i j : Fin 3, i≠j → |shear ref S i j|≤(t : ℝ)) := by
  have sym (i j : Fin 3) : shear ref S j i=shear ref S i j := by
    have e : S j i=S i j := congrFun (congrFun hs i) j
    unfold shear
    rw [e]
  constructor
  · intro h i j hij
    have h01 : |shear ref S 0 1|≤(t : ℝ) := h 2 (by decide)
    have h02 : |shear ref S 0 2|≤(t : ℝ) := h 3 (by decide)
    have h12 : |shear ref S 1 2|≤(t : ℝ) := h 4 (by decide)
    have h10 : |shear ref S 1 0|≤(t : ℝ) := by rw [sym 0 1]; exact h01
    have h20 : |shear ref S 2 0|≤(t : ℝ) := by rw [sym 0 2]; exact h02
    have h21 : |shear ref S 2 1|≤(t : ℝ) := by rw [sym 1 2]; exact h12
    rcases (by decide : ∀ a : Fin 3, a=0 ∨ a=1 ∨ a=2) i with rfl | rfl | rfl <;>
    rcases (by decide : ∀ a : Fin 3, a=0 ∨ a=1 ∨ a=2) j with rfl | rfl | rfl
    all_goals first | exact (hij rfl).elim | assumption
  · intro h i hi
    rcases (by decide : ∀ a : Fin 5, a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4) i with rfl | rfl | rfl | rfl | rfl
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact h 0 1 (by decide)
    · exact h 0 2 (by decide)
    · exact h 1 2 (by decide)

private theorem CubicMove.permutation_injective (m : CubicMove) : Function.Injective m.permutation := by
  have e (i : Fin 3) : m.permutation (m.permutation i)=i := by
    cases m <;> fin_cases i <;> decide
  intro i j h
  exact (e i).symm.trans ((congrArg m.permutation h).trans (e j))

private theorem CubicMove.abs_shear (m : CubicMove) (ref : Reference) (S : Mat) (i j : Fin 3) :
    |shear ref (m.act S) i j|=|shear ref S (m.permutation i) (m.permutation j)| := by
  unfold shear
  rw [m.act_apply]
  cases m <;> fin_cases i <;> fin_cases j <;>
    norm_num [CubicMove.sign,CubicMove.permutation,abs_neg,neg_div]

private theorem coordinateRegion_move (ref : Reference) (m : CubicMove) (S : Mat)
    (hs : S.transpose=S) (ht : diagonalSum S=0) (e t : ℚ)
    (inside : inProductBall e t (strainCoordinates ref S)) :
    inProductBall e t (strainCoordinates ref (m.act S)) := by
  refine ⟨?_,?_⟩
  · rw [diagonalCoordinateNorm ref _ (by rw [m.diagonalSum_act,ht]), m.diagonalSquares_act,
      ← diagonalCoordinateNorm ref S ht]
    exact inside.1
  · apply (offDiagonalCoordinateBounds ref _ (m.symmetric_act S hs) t).2
    intro i j hij
    rw [m.abs_shear]
    exact (offDiagonalCoordinateBounds ref S hs t).1 inside.2 _ _
      (fun he => hij (m.permutation_injective he))

private theorem folded_of_ordered (ref : Reference) (S : Mat)
    (h01 : S 1 1≤S 0 0) (h12 : S 2 2≤S 1 1)
    (h1 : 0≤S 0 1) (h2 : 0≤S 0 2) : folded (strainCoordinates ref S) := by
  have r2 : 0<Real.sqrt 2 := by positivity
  have r3 : 0<Real.sqrt 3 := by positivity
  have hE := whitenE_pos ref
  have hT := whitenT_pos ref
  have er : Real.sqrt 6=Real.sqrt 2*Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ)≤2)]
    norm_num
  have ratio (x : ℝ) : Real.sqrt 3*(x/(Real.sqrt 6*(whitenE ref : ℝ))) =
      x/(Real.sqrt 2*(whitenE ref : ℝ)) := by
    rw [er]
    field_simp [r2.ne',r3.ne',hE.ne'] <;> ring
  change 0≤(S 0 0-S 1 1)/(Real.sqrt 2*(whitenE ref : ℝ)) ∧
    (S 0 0-S 1 1)/(Real.sqrt 2*(whitenE ref : ℝ)) ≤
      Real.sqrt 3*((S 0 0+S 1 1-2*S 2 2)/(Real.sqrt 6*(whitenE ref : ℝ))) ∧
    0≤ shear ref S 0 1 ∧ 0≤ shear ref S 0 2
  exact ⟨div_nonneg (sub_nonneg.mpr h01) (mul_nonneg r2.le hE.le),
    by rw [ratio]; exact div_le_div_of_nonneg_right (by linarith) (mul_nonneg r2.le hE.le),
    div_nonneg (mul_nonneg r2.le h1) hT.le,div_nonneg (mul_nonneg r2.le h2) hT.le⟩

private def move01 (S : Mat) : CubicMove := if S 1 1≤S 0 0 then .keep else .swap01
private def move12 (S : Mat) : CubicMove := if S 2 2≤S 1 1 then .keep else .swap12
private def fix01 (S : Mat) : CubicMove := if 0≤S 0 1 then .keep else .flip1
private def fix02 (S : Mat) : CubicMove := if 0≤S 0 2 then .keep else .flip2

private theorem move01_order (S : Mat) :
    ((move01 S).act S) 1 1≤((move01 S).act S) 0 0 := by
  unfold move01
  split_ifs with h <;> norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation] <;> linarith

private theorem move12_tail (S : Mat) (h : S 1 1≤S 0 0) :
    ((move12 S).act S) 2 2≤((move12 S).act S) 0 0 ∧
    ((move12 S).act S) 2 2≤((move12 S).act S) 1 1 := by
  unfold move12
  split_ifs with k <;> norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation] <;>
    constructor <;> linarith

private theorem move01_tail (S : Mat) (h : S 2 2≤S 0 0 ∧ S 2 2≤S 1 1) :
    ((move01 S).act S) 2 2≤((move01 S).act S) 1 1 := by
  unfold move01
  split_ifs <;> norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation] <;>
    first | exact h.1 | exact h.2

private theorem fix01_diag (S : Mat) (i : Fin 3) : ((fix01 S).act S) i i=S i i := by
  unfold fix01
  split_ifs <;> fin_cases i <;> norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation]

private theorem fix02_diag (S : Mat) (i : Fin 3) : ((fix02 S).act S) i i=S i i := by
  unfold fix02
  split_ifs <;> fin_cases i <;> norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation]

private theorem fix01_sign (S : Mat) : 0≤((fix01 S).act S) 0 1 := by
  unfold fix01
  split_ifs with h <;> norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation] <;> linarith

private theorem fix02_sign (S : Mat) (h : 0≤S 0 1) :
    0≤((fix02 S).act S) 0 1 ∧ 0≤((fix02 S).act S) 0 2 := by
  unfold fix02
  split_ifs with k <;> norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation] <;>
    constructor <;> linarith

def framePoint (ref : Reference) (A : Mat) : Point :=
  strainCoordinates ref (normalizedStrain (gram A))

theorem framePoint_reconstruct (ref : Reference) (A : Mat) (ha : |A.det|=1) :
    reconstructedMetric ref (framePoint ref A)=gram A := by
  have hn : A.det≠0 := by intro e; rw [e,abs_zero] at ha; exact zero_ne_one ha
  have hdet : (gram A).det=1 := by
    rw [gram,Matrix.det_mul,Matrix.det_transpose,← pow_two,← sq_abs,ha,one_pow]
  exact normalizedStrain_metric ref (gram A) (by simp [gram,Matrix.transpose_mul]) hdet
    (gram_trace_positive A hn)

private theorem framePoint_move (ref : Reference) (m : CubicMove) (A : Mat) (ha : |A.det|=1)
    (e t : ℚ) (inside : inProductBall e t (framePoint ref A)) :
    inProductBall e t (framePoint ref (A*m.matrix)) := by
  have hn : A.det≠0 := by intro h; rw [h,abs_zero] at ha; exact zero_ne_one ha
  unfold framePoint
  rw [m.normalizedStrain_act]
  exact coordinateRegion_move ref m _
    (normalizedStrain_symm _ (by simp [gram,Matrix.transpose_mul]))
    (normalizedStrain_trace _ (gram_trace_positive A hn).ne') e t inside

private theorem frameVolume_move (m : CubicMove) (A : Mat) (ha : |A.det|=1) :
    |(A*m.matrix).det|=1 := by
  rw [Matrix.det_mul,abs_mul,ha,m.abs_det,one_mul]

private def orient (A : Mat) : CubicMove := if A.det=1 then .keep else .invert

private theorem orient_det (A : Mat) (ha : |A.det|=1) : (A*(orient A).matrix).det=1 := by
  unfold orient
  split_ifs with h
  · simpa [CubicMove.matrix] using h
  · have hn : A.det<0 := by
      by_contra! hp
      rw [abs_of_nonneg hp] at ha
      exact h ha
    have hn' : A.det=-1 := by rw [abs_of_neg hn] at ha; linarith
    rw [Matrix.det_mul,hn']
    norm_num [CubicMove.matrix,Matrix.det_fin_three,Matrix.one_apply]

private theorem orient_point (ref : Reference) (A : Mat) : framePoint ref (A*(orient A).matrix)=framePoint ref A := by
  unfold framePoint
  rw [CubicMove.normalizedStrain_act]
  congr 1
  ext i j
  unfold orient
  split_ifs <;> fin_cases i <;> fin_cases j <;>
    norm_num [CubicMove.act_apply,CubicMove.sign,CubicMove.permutation]

/-- The exact weak chamber conditions hold even on ties and zero
off-diagonal faces. The reported basis gives the same physical point
set, energy and deficit throughout, including the origin. -/
theorem fold_strain_frame (ref : Reference) (A : Mat) (ha : |A.det|=1) (e t : ℚ)
    (hi : inProductBall e t (framePoint ref A)) :
    ∃ B : Mat, B.det=1 ∧ folded (framePoint ref B) ∧ inProductBall e t (framePoint ref B) ∧
      gram B=reconstructedMetric ref (framePoint ref B) ∧
      lattice (strainBasis ref B)=lattice (strainBasis ref A) ∧
      oneSiteDeficit (strainBasis ref B)=oneSiteDeficit (strainBasis ref A) := by
  let S (B : Mat) := normalizedStrain (gram B)
  let m₁ := move01 (S A)
  let A₁ := A*m₁.matrix
  let m₂ := move12 (S A₁)
  let A₂ := A₁*m₂.matrix
  let m₃ := move01 (S A₂)
  let A₃ := A₂*m₃.matrix
  let m₄ := fix01 (S A₃)
  let A₄ := A₃*m₄.matrix
  let m₅ := fix02 (S A₄)
  let A₅ := A₄*m₅.matrix
  let m₆ := orient A₅
  let B := A₅*m₆.matrix
  have hb₁ := frameVolume_move m₁ A ha
  have hb₂ := frameVolume_move m₂ A₁ hb₁
  have hb₃ := frameVolume_move m₃ A₂ hb₂
  have hb₄ := frameVolume_move m₄ A₃ hb₃
  have hb₅ := frameVolume_move m₅ A₄ hb₄
  have hB : B.det=1 := orient_det A₅ hb₅
  have bi₁ := framePoint_move ref m₁ A ha e t hi
  have bi₂ := framePoint_move ref m₂ A₁ hb₁ e t bi₁
  have bi₃ := framePoint_move ref m₃ A₂ hb₂ e t bi₂
  have bi₄ := framePoint_move ref m₄ A₃ hb₃ e t bi₃
  have bi₅ := framePoint_move ref m₅ A₄ hb₄ e t bi₄
  have b₁ : S A₁=m₁.act (S A) := m₁.normalizedStrain_act A
  have b₂ : S A₂=m₂.act (S A₁) := m₂.normalizedStrain_act A₁
  have b₃ : S A₃=m₃.act (S A₂) := m₃.normalizedStrain_act A₂
  have b₄ : S A₄=m₄.act (S A₃) := m₄.normalizedStrain_act A₃
  have b₅ : S A₅=m₅.act (S A₄) := m₅.normalizedStrain_act A₄
  have h₁ : S A₁ 1 1≤S A₁ 0 0 := by rw [b₁]; exact move01_order _
  have h₂ : S A₂ 2 2≤S A₂ 0 0 ∧ S A₂ 2 2≤S A₂ 1 1 := by
    rw [b₂]; exact move12_tail _ h₁
  have h₃ : S A₃ 1 1≤S A₃ 0 0 ∧ S A₃ 2 2≤S A₃ 1 1 := by
    rw [b₃]
    exact ⟨move01_order _,move01_tail _ h₂⟩
  have h₄ : 0≤S A₄ 0 1 := by rw [b₄]; exact fix01_sign _
  have h₅ : 0≤S A₅ 0 1 ∧ 0≤S A₅ 0 2 := by rw [b₅]; exact fix02_sign _ h₄
  have hdiag (i : Fin 3) : S A₅ i i=S A₃ i i := by
    calc
      _ = S A₄ i i := by rw [b₅]; exact fix02_diag _ _
      _ = _ := by rw [b₄]; exact fix01_diag _ _
  have f : folded (framePoint ref A₅) := folded_of_ordered ref (S A₅)
    (by rw [hdiag 1,hdiag 0]; exact h₃.1) (by rw [hdiag 2,hdiag 1]; exact h₃.2) h₅.1 h₅.2
  have hpt : framePoint ref B=framePoint ref A₅ := orient_point ref A₅
  refine ⟨B,hB,hpt.symm ▸ f,hpt.symm ▸ bi₅,
    (framePoint_reconstruct ref B (by simp [hB])).symm,?_,?_⟩
  · exact (strainBasis_move_lattice ref m₆ A₅).trans
      ((strainBasis_move_lattice ref m₅ A₄).trans ((strainBasis_move_lattice ref m₄ A₃).trans
      ((strainBasis_move_lattice ref m₃ A₂).trans ((strainBasis_move_lattice ref m₂ A₁).trans
       (strainBasis_move_lattice ref m₁ A)))))
  · exact (strainBasis_move_deficit ref m₆ A₅).trans
      ((strainBasis_move_deficit ref m₅ A₄).trans ((strainBasis_move_deficit ref m₄ A₃).trans
      ((strainBasis_move_deficit ref m₃ A₂).trans ((strainBasis_move_deficit ref m₂ A₁).trans
       (strainBasis_move_deficit ref m₁ A)))))

/-- Closed chamber and product-ball membership along the radial segment,
including the anchor and the endpoint on any chamber face. -/
theorem folded_productBall_ray (w : Point) (hf : folded w) (e t : ℚ) (hb : inProductBall e t w)
    (s : ℝ) (hs : s∈Set.Icc (0 : ℝ) 1) :
    folded (s • w) ∧ inProductBall e t (s • w) := by
  simp only [folded,Pi.smul_apply,smul_eq_mul] at hf ⊢
  have hshape : s*w 0≤Real.sqrt 3*(s*w 1) := by
    calc
      _ ≤ s*(Real.sqrt 3*w 1) := mul_le_mul_of_nonneg_left hf.2.1 hs.1
      _ = _ := by ring
  refine ⟨⟨mul_nonneg hs.1 hf.1,hshape,mul_nonneg hs.1 hf.2.2.1,mul_nonneg hs.1 hf.2.2.2⟩,?_⟩
  refine ⟨?_,?_⟩
  · change (s*w 0)^2+(s*w 1)^2≤(e : ℝ)^2
    rw [mul_pow,mul_pow,← mul_add]
    have hh : s^2≤1 := by simpa using pow_le_pow_left₀ hs.1 hs.2 2
    calc
      _ ≤ 1*((w 0)^2+(w 1)^2) :=
        mul_le_mul_of_nonneg_right hh (add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ _ := by simpa using hb.1
  · intro i hi
    change |s*w i|≤(t : ℝ)
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)).trans
      (by simpa using hb.2 i hi)

end BccSharp.Coulomb.BravaisCover
