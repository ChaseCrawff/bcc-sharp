import BccSharp.Cover.OverlayPlanarAxialCheck

set_option autoImplicit false

/-! Outer tail of the planar expansion of Lemma 7.6. This counts signed waves in
the entire omitted square complement and all their axial terms. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)

def waveRadius (m : Wave) : ℕ := max m.1.natAbs m.2.natAbs
def waveShell (j : ℕ) : Finset Wave := waveCube j \ waveCube (j-1)

theorem mem_waveCube (m : Wave) (j : ℕ) : m∈waveCube j ↔ waveRadius m≤j := by
  rcases m with ⟨a,b⟩
  simp only [waveCube,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,waveRadius,
    max_le_iff,← abs_le,← Int.natCast_natAbs,Nat.cast_le]

theorem mem_waveShell (m : Wave) {j : ℕ} (hj : 0<j) : m∈waveShell j ↔ waveRadius m=j := by
  simp only [waveShell,Finset.mem_sdiff,mem_waveCube]
  omega

theorem card_waveCube (j : ℕ) : (waveCube j).card=(2*j+1)^2 := by
  have side : (Finset.Icc (-(j : ℤ)) (j : ℤ)).card=2*j+1 := by
    rw [Int.card_Icc]; omega
  simp only [waveCube,Finset.product_eq_sprod,Finset.card_product,side,pow_two]

theorem card_waveShell {j : ℕ} (hj : 0<j) : (waveShell j).card=8*j := by
  have sub : waveCube (j-1)⊆waveCube j := fun m hm =>
    (mem_waveCube _ _).mpr ((mem_waveCube _ _).mp hm |>.trans (by omega))
  have count : (waveShell j).card+(2*(j-1)+1)^2=(2*j+1)^2 := by
    simpa only [waveShell,card_waveCube] using Finset.card_sdiff_add_card_eq_card sub
  have e : 8*j+(2*(j-1)+1)^2=(2*j+1)^2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
    ring
  omega

def waveTailEquiv (r : ℕ) : {m // m∉waveCube r} ≃ (Σ k : ℕ, ↥(waveShell (r+1+k))) where
  toFun m := ⟨waveRadius m.val-(r+1), ⟨m.val, by
    have h := (mem_waveCube m.val r).not.mp m.property
    apply (mem_waveShell _ (by omega)).mpr
    omega⟩⟩
  invFun x := ⟨x.2.val, by
    have h := (mem_waveShell _ (by omega)).mp x.2.property
    exact (mem_waveCube _ _).not.mpr (by omega)⟩
  left_inv m := rfl
  right_inv x := by
    obtain ⟨k,m,hm⟩ := x
    have h := (mem_waveShell _ (by omega)).mp hm
    have e : waveRadius m-(r+1)=k := by omega
    exact Sigma.subtype_ext e rfl

def secondColumn (p : Chart) : ℝ := Real.sqrt ((p 0*p 2)^2+(p 1)^2)

theorem waveRadius_le {p : Chart} (hr : 0<p 0) (hs : 0<p 1) (m : Wave)
    {B : ℝ} (h₁ : p 0≤B) (h₂ : secondColumn p≤B) :
    (waveRadius m : ℝ)≤κReal p m*B := by
  let u := (m.1 : ℝ)*(p 0)⁻¹
  let v := ((m.2 : ℝ)-(m.1 : ℝ)*p 2)*(p 1)⁻¹
  let k := κReal p m
  have kn : 0≤k := Real.sqrt_nonneg _
  have ksq : k^2=u^2+v^2 := Real.sq_sqrt (by dsimp [κSq]; positivity)
  have i : (m.1 : ℝ)=u*p 0 := by dsimp [u]; field_simp [hr.ne']
  have j : (m.2 : ℝ)=u*(p 0*p 2)+v*p 1 := by
    dsimp [u,v]
    field_simp [hr.ne',hs.ne']
    ring
  have uc : |u|≤k := by
    apply (sq_le_sq₀ (abs_nonneg _) kn).mp
    rw [sq_abs,ksq]
    linarith only [sq_nonneg v]
  have vc : |u*(p 0*p 2)+v*p 1|≤k*secondColumn p := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg kn (Real.sqrt_nonneg _))).mp
    rw [sq_abs,mul_pow,ksq,Real.sq_sqrt (by positivity)]
    nlinarith only [sq_nonneg (u*p 1-v*(p 0*p 2))]
  have one : |(m.1 : ℝ)|≤k*B := by
    rw [i,abs_mul,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_right uc hr.le).trans (mul_le_mul_of_nonneg_left h₁ kn)
  have two : |(m.2 : ℝ)|≤k*B := by
    rw [j]
    exact vc.trans (mul_le_mul_of_nonneg_left h₂ kn)
  simpa only [waveRadius,Nat.cast_max,Nat.cast_natAbs,Int.cast_abs] using max_le one two

def radialNumerator (τ η : ℝ) (j : ℕ) : ℝ :=
  2*Real.exp (-τ*(j : ℝ))+2*Real.exp (-(τ*η)*(j : ℝ))

def radialDen (τ : ℝ) (J : ℕ) : ℝ := 1-Real.exp (-τ*(J : ℝ))

def radialTail (cPos B τ η : ℝ) (J : ℕ) : ℝ :=
  8*cPos*B/radialDen τ J *
    (2*Real.exp (-τ*(J : ℝ))/(1-Real.exp (-τ)) +
      2*Real.exp (-(τ*η)*(J : ℝ))/(1-Real.exp (-(τ*η))))

private theorem radialDen_pos {τ : ℝ} {J : ℕ} (hτ : 0<τ) (hj : 0<J) :
    0< radialDen τ J := by
  apply sub_pos.mpr
  have hJ : (0:ℝ)<J := by exact_mod_cast hj
  exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hτ) hJ)

private theorem radialNumerator_sum {τ η : ℝ} (ht : 0<τ) (he : 0<η) (J : ℕ) :
    Summable (fun n : ℕ => radialNumerator τ η (J+n)) ∧
    (∑' n : ℕ, radialNumerator τ η (J+n)) =
      2*Real.exp (-τ*(J : ℝ))/(1-Real.exp (-τ)) +
      2*Real.exp (-(τ*η)*(J : ℝ))/(1-Real.exp (-(τ*η))) := by
  have each (s : ℝ) (hs : 0<s) : Summable (fun n : ℕ => 2*Real.exp (-s*((J+n : ℕ):ℝ))) ∧
      (∑' n : ℕ, 2*Real.exp (-s*((J+n : ℕ):ℝ)))=2*Real.exp (-s*(J : ℝ))/(1-Real.exp (-s)) := by
    have ratio := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
    have e (n : ℕ) : 2*Real.exp (-s*((J+n : ℕ):ℝ))=(2*Real.exp (-s*(J : ℝ)))*(Real.exp (-s))^n := by
      rw [Nat.cast_add,add_comm (J : ℝ),exp_add_nat,mul_assoc]
    simp_rw [e]
    exact ⟨(summable_geometric_of_lt_one (Real.exp_pos _).le ratio).mul_left _, by
      rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.exp_pos _).le ratio,div_eq_mul_inv]⟩
  obtain ⟨s₁,e₁⟩ := each τ ht
  obtain ⟨s₂,e₂⟩ := each (τ*η) (mul_pos ht he)
  refine ⟨s₁.add s₂,?_⟩
  unfold radialNumerator
  rw [s₁.tsum_add s₂, e₁, e₂]

private def radialEnvelope (B τ η : ℝ) (J j : ℕ) : ℝ :=
  (B/(j : ℝ))*(radialNumerator τ η j/radialDen τ J)

private theorem wave_majorant {p : Chart} {B τ η : ℝ} {J j : ℕ} {m : Wave}
    (hr : 0<p 0) (hs : 0<p 1) (h₁ : p 0≤B) (h₂ : secondColumn p≤B)
    (ht : 0<τ) (hstep : τ≤2*Real.pi*cReal p/B) (hη : 0<η)
    (hl : η≤p 7) (hu : p 7≤1-η) (hJ : 0<J) (hj : J≤j) (hm : waveRadius m=j) :
    |waveValue p m|≤ radialEnvelope B τ η J j := by
  have Bpos := hr.trans_le h₁
  have jr : (J : ℝ)≤j := by exact_mod_cast hj
  have jp : (0:ℝ)<j := by exact_mod_cast hJ.trans_le hj
  have k := waveRadius_le hr hs m h₁ h₂
  rw [hm] at k
  have kn : 0<κReal p m := by
    by_contra! notPos
    exact jp.not_ge (k.trans (mul_nonpos_of_nonpos_of_nonneg notPos Bpos.le))
  have cp : 0<cReal p := inv_pos.mpr (mul_pos hr hs)
  have T : τ*(j : ℝ)≤tReal p m := by
    calc
      _ ≤ (2*Real.pi*cReal p/B)*(j : ℝ) := mul_le_mul_of_nonneg_right hstep jp.le
      _ ≤ (2*Real.pi*cReal p/B)*(κReal p m*B) := mul_le_mul_of_nonneg_left k (by positivity)
      _ = _ := by unfold tReal; field_simp [Bpos.ne']
  have hA := axialAll_sound (wReal p m) (uReal p m) (p 7) η (mul_pos ht jp) T hη.le hl hu
  have dd : radialDen τ J≤ radialDen τ j := by
    apply sub_le_sub_left (Real.exp_le_exp.mpr _) _
    exact mul_le_mul_of_nonpos_left jr (neg_nonpos.mpr ht.le)
  have nn : 0≤ radialNumerator τ η j := by unfold radialNumerator; positivity
  have inv : (κReal p m)⁻¹≤B/(j : ℝ) := by
    apply (le_div_iff₀ jp).mpr
    calc
      _ = (j : ℝ)/κReal p m := by rw [div_eq_mul_inv,mul_comm]
      _ ≤ B := (div_le_iff₀ kn).mpr (by simpa only [mul_comm B (κReal p m)] using k)
  have aux : |axialSeries (tReal p m) (wReal p m) (uReal p m) (p 7)|≤
      radialNumerator τ η j/radialDen τ J := by
    apply le_trans _ (div_le_div_of_nonneg_left nn (radialDen_pos ht hJ) dd)
    simpa [radialNumerator,radialDen,show -(τ*(j : ℝ))*η= -(τ*η)*(j : ℝ) by ring] using hA
  rw [waveValue,div_eq_mul_inv,abs_mul,abs_of_pos (inv_pos.mpr kn),radialEnvelope,mul_comm (B/(j : ℝ))]
  exact mul_le_mul aux inv (by positivity) (div_nonneg nn (radialDen_pos ht hJ).le)

theorem radialTail_sound {p : Chart} {B τ η : ℝ} (r : ℕ) (hr : 0<p 0) (hs : 0<p 1)
    (h₁ : p 0≤B) (h₂ : secondColumn p≤B) (ht : 0<τ) (hstep : τ≤2*Real.pi*cReal p/B)
    (hη : 0<η) (hl : η≤p 7) (hu : p 7≤1-η) : Summable (waveValue p) ∧
    |cReal p*(∑' m : {m // m∉waveCube r}, waveValue p m.val)|≤ radialTail (cReal p) B τ η (r+1) := by
  let J := r+1
  have hJ : 0<J := by omega
  have hB := hr.trans_le h₁
  have hc : 0<cReal p := inv_pos.mpr (mul_pos hr hs)
  obtain ⟨hsum,e⟩ := radialNumerator_sum ht hη J
  let I := Σ n : ℕ, ↥(waveShell (J+n))
  let g (x : I) := radialEnvelope B τ η J (J+x.1)
  let f (x : I) := waveValue p x.2.val
  let a := 8*B/radialDen τ J
  have fold (n : ℕ) : (∑' m : ↥(waveShell (J+n)), g ⟨n,m⟩)=a*radialNumerator τ η (J+n) := by
    have hj : 0<J+n := by omega
    have jpos : (0:ℝ)<(J+n : ℕ) := by exact_mod_cast hj
    simp only [g,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,
      card_waveShell hj,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [a,radialEnvelope]
    field_simp [jpos.ne',(radialDen_pos ht hJ).ne']
  have hg : Summable g := (summable_sigma_of_nonneg fun x => by
    dsimp [g,radialEnvelope,radialNumerator]
    exact mul_nonneg (div_nonneg hB.le (Nat.cast_nonneg _))
      (div_nonneg (by positivity) (radialDen_pos ht hJ).le)).mpr
    ⟨fun _ => Summable.of_finite,by simpa only [fold] using hsum.mul_left a⟩
  obtain ⟨hf,ab⟩ := abs_sum_bound hg (fun x => wave_majorant hr hs h₁ h₂ ht hstep hη hl hu hJ
    (by omega) ((mem_waveShell _ (by omega)).mp x.2.property))
  have rest : Summable (fun m : {m // m∉waveCube r} => waveValue p m.val) :=
    (waveTailEquiv r).symm.summable_iff.mp hf
  refine ⟨(Finset.summable_compl_iff (waveCube r)).mp rest,?_⟩
  have ident := (waveTailEquiv r).symm.tsum_eq (fun m : {m // m∉waveCube r} => waveValue p m.val)
  change (∑' x, f x)=_ at ident
  have total : (∑' x, g x)=a*(∑' n, radialNumerator τ η (J+n)) := by
    rw [hg.tsum_sigma]
    simp only [fold,tsum_mul_left]
  rw [ident,total,e] at ab
  rw [abs_mul,abs_of_pos hc]
  refine (mul_le_mul_of_nonneg_left ab hc.le).trans_eq ?_
  unfold a radialTail
  ring

end BccSharp.Coulomb.CompactCover.OverlayPlanar
