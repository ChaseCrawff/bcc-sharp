import BccSharp.Cover.OverlayGaussianPoisson
import BccSharp.Cover.OverlayPlanarOperands

set_option autoImplicit false

/-! Dimension descent for the Overlay shifted heat sums. Extrusion
by an orthogonal unit line lets us reuse the three-dimensional kernel
uniqueness argument and cancel a positive unshifted factor. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp

def planeIndex : (Wave × ℤ) ≃ IntVec where
  toFun z := ![z.1.1,z.1.2,z.2]
  invFun n := ((n 0,n 1),n 2)
  left_inv z := by rcases z with ⟨⟨i,j⟩,k⟩; rfl
  right_inv n := by funext i; fin_cases i <;> rfl

theorem productHeat_sum {ι κ : Type*} (f : ι → ℝ) (g : κ → ℝ)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun z : ι × κ => f z.1*g z.2) ∧
      (∑' z : ι × κ, f z.1*g z.2)=(∑' i, f i)*(∑' j, g j) := by
  have h := hf.norm.mul_of_nonneg hg.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hp : Summable (fun z : ι × κ => f z.1*g z.2) := h.of_norm_bounded (fun z => by rw [norm_mul])
  exact ⟨hp,(hf.tsum_mul_tsum hg hp).symm⟩

def lineHeat (s h : ℝ) (k : ℤ) : ℝ := Real.exp (-Real.pi*s^2*((k : ℝ)+h)^2)
def lineTheta (s h : ℝ) : ℝ := ∑' k : ℤ, lineHeat s h k
def lineDualTerm (s h : ℝ) (k : ℤ) : ℝ :=
  lineHeat s 0 k*Real.cos (2*Real.pi*(k : ℝ)*h)
def lineDual (s h : ℝ) : ℝ := ∑' k : ℤ, lineDualTerm s h k

theorem lineHeat_nonneg (s h : ℝ) (k : ℤ) : 0≤lineHeat s h k := (Real.exp_pos _).le

theorem lineHeat_summable (s : ℝ) (hs : 0<s) (h : ℝ) : Summable (lineHeat s h) := by
  let e (k : ℤ) : IntVec := ![0,0,k]
  have inj : Function.Injective e := fun _ _ h => congrFun h 2
  have b : (1 : Mat).det≠0 := by simp
  have ss := (heat_lattice_summable s hs 1 b ![0,0,h]).comp_injective inj
  refine ss.congr (fun k => ?_)
  simp [e,lineHeat,heat,sq,linearImage,castVec,Fin.sum_univ_three,add_comm]

theorem lineDual_summable (s : ℝ) (hs : 0<s) (h : ℝ) : Summable (lineDualTerm s h) := by
  apply (lineHeat_summable s hs 0).of_norm_bounded
  intro k
  unfold lineDualTerm
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (lineHeat_nonneg s 0 k),Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_le.mpr
    ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) (lineHeat_nonneg s 0 k)

theorem lineDual_zero (s : ℝ) : lineDual s 0=lineTheta s 0 := by
  simp [lineDual,lineDualTerm,lineTheta]

theorem lineTheta_zero_pos (s : ℝ) (hs : 0<s) : 0<lineTheta s 0 := by
  have one := (lineHeat_summable s hs 0).sum_le_tsum {0} (fun k _ => (Real.exp_pos _).le)
  exact zero_lt_one.trans_le (by simpa [lineTheta,lineHeat] using one)

def planarNorm (p : Chart) (x y : ℝ) : ℝ := (p 0*(x+p 2*y))^2+(p 1*y)^2
def planeHeat (p : Chart) (s x y : ℝ) (m : Wave) : ℝ :=
  Real.exp (-Real.pi*s^2*planarNorm p ((m.1 : ℝ)+x) ((m.2 : ℝ)+y))
def planeTheta (p : Chart) (s x y : ℝ) : ℝ := ∑' m : Wave, planeHeat p s x y m
def planeDualTerm (p : Chart) (s x y : ℝ) (m : Wave) : ℝ :=
  Real.exp (-Real.pi*s^2*κSq p m)*Real.cos (2*Real.pi*((m.1 : ℝ)*x+(m.2 : ℝ)*y))
def planeDual (p : Chart) (s x y : ℝ) : ℝ := ∑' m : Wave, planeDualTerm p s x y m

def planeExtrude (p : Chart) : Mat := !![p 0,p 0*p 2,0;0,p 1,0;0,0,1]

theorem planeExtrude_det (p : Chart) : (planeExtrude p).det=p 0*p 1 := by
  norm_num [planeExtrude,Matrix.det_fin_three]

theorem plane_frequency (p : Chart) (hr : p 0≠0) (ht : p 1≠0) (m : Wave) (k : ℤ) :
    cycleFrequency (planeExtrude p) (planeIndex (m,k)) =
      ![(m.1 : ℝ)*(p 0)⁻¹,((m.2 : ℝ)-(m.1 : ℝ)*p 2)*(p 1)⁻¹,(k : ℝ)] := by
  let B := planeExtrude p
  have hB : B.det≠0 := by rw [planeExtrude_det]; exact mul_ne_zero hr ht
  have unit : IsUnit B.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose]))
  apply Matrix.mulVec_injective_of_isUnit unit
  rw [cycleFrequency_transpose B hB]
  funext i
  fin_cases i <;> norm_num [B,planeExtrude,planeIndex,castVec,Matrix.mulVec,dotProduct,Fin.sum_univ_three] <;>
    field_simp [hr,ht] <;> ring

private theorem extruded_direct_term (p : Chart) (s x y h : ℝ) (m : Wave) (k : ℤ) :
    heat s ((planeExtrude p).mulVec ![x,y,h]+linearImage (planeExtrude p) (planeIndex (m,k))) =
      planeHeat p s x y m*lineHeat s h k := by
  simp only [heat,planeHeat,lineHeat,← Real.exp_add]
  congr 1
  norm_num [planeExtrude,planeIndex,linearImage,castVec,planarNorm,Matrix.mulVec,dotProduct,sq,Fin.sum_univ_three]
  ring

theorem planeHeat_summable (p : Chart) (hr : p 0≠0) (ht : p 1≠0) (s : ℝ) (hs : 0<s) (x y : ℝ) :
    Summable (planeHeat p s x y) := by
  let e (m : Wave) := planeIndex (m,0)
  have inj : Function.Injective e := by
    intro m n he
    exact congrArg Prod.fst (planeIndex.injective he)
  have hB : (planeExtrude p).det≠0 := by rw [planeExtrude_det]; exact mul_ne_zero hr ht
  have h := (heat_lattice_summable s hs (planeExtrude p) hB ((planeExtrude p).mulVec ![x,y,0])).comp_injective inj
  simpa [Function.comp_def,e,extruded_direct_term,lineHeat] using h

private theorem extruded_dual_term (p : Chart) (hr : p 0≠0) (ht : p 1≠0) (s x y : ℝ) (m : Wave) (k : ℤ) :
    heat s (cycleFrequency (planeExtrude p) (planeIndex (m,k)))*
        Real.cos (2*Real.pi*dot (castVec (planeIndex (m,k))) ![x,y,0]) =
      planeDualTerm p s x y m*lineHeat s 0 k := by
  rw [plane_frequency p hr ht]
  have h : sq (![(m.1 : ℝ)*(p 0)⁻¹,((m.2 : ℝ)-(m.1 : ℝ)*p 2)*(p 1)⁻¹,(k : ℝ)] : Vec)=κSq p m+(k : ℝ)^2 := by
    norm_num [sq,κSq,Fin.sum_univ_three]
  have d : dot (castVec (planeIndex (m,k))) ![x,y,0]=(m.1 : ℝ)*x+(m.2 : ℝ)*y := by
    norm_num [dot,castVec,planeIndex,Fin.sum_univ_three]
  rw [heat,h,d,planeDualTerm,lineHeat,add_zero,mul_add,Real.exp_add]
  ring

theorem planeDual_summable (p : Chart) (hr : p 0≠0) (ht : p 1≠0) (s : ℝ) (hs : 0<s) (x y : ℝ) :
    Summable (planeDualTerm p s x y) := by
  have hB : (planeExtrude p).det≠0 := by rw [planeExtrude_det]; exact mul_ne_zero hr ht
  let f (n : IntVec) := heat s (cycleFrequency (planeExtrude p) n)*
    Real.cos (2*Real.pi*dot (castVec n) ![x,y,0])
  have h : Summable f := (heat_cycle_summable s hs (planeExtrude p) hB).of_norm_bounded (fun n => by
    simp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (heat_nonneg _ _),Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_le.mpr
      ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) (heat_nonneg s (cycleFrequency (planeExtrude p) n)))
  let e (m : Wave) := planeIndex (m,0)
  have inj : Function.Injective e := fun _ _ he => congrArg Prod.fst (planeIndex.injective he)
  simpa [Function.comp_def,e,f,extruded_dual_term p hr ht,lineHeat] using h.comp_injective inj

private theorem extruded_theta (p : Chart) (hr : p 0≠0) (ht : p 1≠0) (s : ℝ) (hs : 0<s) (x y h : ℝ) :
    heatTheta (planeExtrude p) ![x,y,h] s=planeTheta p s x y*lineTheta s h := by
  unfold heatTheta heatThetaAt
  rw [← planeIndex.tsum_eq]
  calc
    _ = ∑' z : Wave × ℤ, planeHeat p s x y z.1*lineHeat s h z.2 :=
      tsum_congr (fun z => extruded_direct_term p s x y h z.1 z.2)
    _ = _ := (productHeat_sum _ _ (planeHeat_summable p hr ht s hs x y) (lineHeat_summable s hs h)).2

private theorem extruded_dual (p : Chart) (hr : p 0≠0) (ht : p 1≠0) (s : ℝ) (hs : 0<s) (x y : ℝ) :
    heatDual (planeExtrude p) ![x,y,0] s=planeDual p s x y*lineTheta s 0 := by
  unfold heatDual
  rw [← planeIndex.tsum_eq]
  simp_rw [extruded_dual_term p hr ht]
  exact (productHeat_sum _ _ (planeDual_summable p hr ht s hs x y) (lineHeat_summable s hs 0)).2

private def unitPlane : Chart := ![1,1,0,0,0,0,0,0]

private theorem unit_plane_theta (s : ℝ) (hs : 0<s) (h : ℝ) :
    planeTheta unitPlane s h 0=lineTheta s h*lineTheta s 0 := by
  unfold planeTheta
  have e (m : Wave) : planeHeat unitPlane s h 0 m=lineHeat s h m.1*lineHeat s 0 m.2 := by
    simp only [planeHeat,lineHeat,← Real.exp_add]
    congr 1
    norm_num [planarNorm,unitPlane]
    ring
  simp_rw [e]
  exact (productHeat_sum _ _ (lineHeat_summable s hs h) (lineHeat_summable s hs 0)).2

private theorem unit_plane_dual (s : ℝ) (hs : 0<s) (h : ℝ) :
    planeDual unitPlane s h 0=lineDual s h*lineTheta s 0 := by
  unfold planeDual
  have e (m : Wave) : planeDualTerm unitPlane s h 0 m=lineDualTerm s h m.1*lineHeat s 0 m.2 := by
    unfold planeDualTerm lineDualTerm lineHeat
    norm_num [κSq,unitPlane,mul_add,Real.exp_add]
    ring
  simp_rw [e]
  exact (productHeat_sum _ _ (lineDual_summable s hs h) (lineHeat_summable s hs 0)).2

private theorem line_poisson_cube (s : ℝ) (hs : 0<s) (h : ℝ) :
    lineTheta s h*(lineTheta s 0)^2 = (s^3)⁻¹*(lineDual s⁻¹ h*(lineTheta s⁻¹ 0)^2) := by
  have hdet : (planeExtrude unitPlane).det=1 := by norm_num [planeExtrude_det,unitPlane]
  have hB := hdet.symm ▸ (one_ne_zero : (1:ℝ)≠0)
  have e := heat_poisson (planeExtrude unitPlane) hB ![h,0,0] s hs
  have hr : unitPlane 0≠0 := by norm_num [unitPlane]
  have ht : unitPlane 1≠0 := by norm_num [unitPlane]
  rw [extruded_theta _ hr ht _ hs,extruded_dual _ hr ht _ (inv_pos.mpr hs),
    unit_plane_theta _ hs,unit_plane_dual _ (inv_pos.mpr hs),volumeOf,hdet,abs_one,one_mul] at e
  simpa only [pow_two,mul_assoc] using e

theorem line_poisson_unshifted (s : ℝ) (hs : 0<s) : lineTheta s 0=s⁻¹*lineTheta s⁻¹ 0 := by
  have e := line_poisson_cube s hs 0
  rw [lineDual_zero] at e
  have e' : (lineTheta s 0)^3=(s⁻¹*lineTheta s⁻¹ 0)^3 := by
    calc
      _ = lineTheta s 0*(lineTheta s 0)^2 := by ring
      _ = _ := e
      _ = _ := by rw [mul_pow,inv_pow]; ring
  let a := lineTheta s 0
  let b := s⁻¹*lineTheta s⁻¹ 0
  have apos : 0<a := lineTheta_zero_pos s hs
  have bpos : 0<b := mul_pos (inv_pos.mpr hs) (lineTheta_zero_pos s⁻¹ (inv_pos.mpr hs))
  have fact : (a-b)*(a^2+a*b+b^2)=0 := by
    calc
      _ = a^3-b^3 := by ring
      _ = 0 := sub_eq_zero.mpr e'
  exact sub_eq_zero.mp ((mul_eq_zero.mp fact).resolve_right (by positivity : a^2+a*b+b^2≠0))

theorem line_poisson (s : ℝ) (hs : 0<s) (h : ℝ) : lineTheta s h=s⁻¹*lineDual s⁻¹ h := by
  have e := line_poisson_cube s hs h
  rw [line_poisson_unshifted s hs] at e
  have K := lineTheta_zero_pos s⁻¹ (inv_pos.mpr hs)
  have hfactor : (s⁻¹*lineTheta s⁻¹ 0)^2≠0 := (pow_pos (mul_pos (inv_pos.mpr hs) K) 2).ne'
  apply mul_right_cancel₀ hfactor
  calc
    _ = (s^3)⁻¹*(lineDual s⁻¹ h*(lineTheta s⁻¹ 0)^2) := e
    _ = _ := by field_simp [hs.ne'] <;> ring

theorem plane_poisson (p : Chart) (hr : 0<p 0) (ht : 0<p 1) (s : ℝ) (hs : 0<s) (x y : ℝ) :
    planeTheta p s x y=cReal p*(s^2)⁻¹*planeDual p s⁻¹ x y := by
  have hB : (planeExtrude p).det≠0 := by rw [planeExtrude_det]; exact (mul_pos hr ht).ne'
  have e := heat_poisson (planeExtrude p) hB ![x,y,0] s hs
  rw [extruded_theta _ hr.ne' ht.ne' _ hs,extruded_dual _ hr.ne' ht.ne' _ (inv_pos.mpr hs),
    volumeOf,planeExtrude_det,abs_of_pos (mul_pos hr ht),line_poisson_unshifted s hs] at e
  apply mul_right_cancel₀ (mul_pos (inv_pos.mpr hs) (lineTheta_zero_pos s⁻¹ (inv_pos.mpr hs))).ne'
  calc
    _ = (p 0*p 1*s^3)⁻¹*(planeDual p s⁻¹ x y*lineTheta s⁻¹ 0) := e
    _ = _ := by unfold cReal; field_simp [hr.ne',ht.ne',hs.ne'] <;> ring

end BccSharp.Coulomb.CompactCover.OverlayPlanar
