module

public import BccSharp.Analysis.ScreenedBounds
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! A common open neighborhood of each noncolliding half-integer lattice
configuration, with summable bounds uniform throughout that neighborhood. -/
@[expose] public section
namespace BccSharp.LatticeNeighborhood
open Real Ewald LatticeTails RealSpaceHessian Filter
open scoped Topology

noncomputable def center (z : Triple) : Vec := (1/2 : ℝ) • coord z
noncomputable def shifted (x : Vec) (z : Triple) : Vec := x + center z
noncomputable def domain (L : Triple) : Set Vec := {x | ∀ i, |x i-center L i| < 1/16}
noncomputable def bound (L : Triple) : ℝ := 2*Ewald.sq (center L)+1
noncomputable def majorant (L z : Triple) : ℝ := exp (4*bound L)*exp (-(1/2)*normSq z)

theorem center_mem (L : Triple) : center L ∈ domain L := by
  intro i
  simp

theorem domain_open (L : Triple) : IsOpen (domain L) := by
  have he : domain L = ⋂ i : Fin 3, {x : Vec | |x i-center L i| < (1 : ℝ)/16} := by
    ext x
    simp [domain]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem difference_bound {L : Triple} {x : Vec} (hx : x ∈ domain L) :
    Ewald.sq (x-center L) ≤ 3/256 := by
  have hh (i : Fin 3) : (x i-center L i)^2 ≤ 1/256 := by
    have h := abs_lt.mp (hx i)
    nlinarith
  simp only [Ewald.sq,Pi.sub_apply]
  linarith [hh 0,hh 1,hh 2]

theorem square_bound {L : Triple} {x : Vec} (hx : x ∈ domain L) : Ewald.sq x ≤ bound L := by
  have hh := difference_bound hx
  dsimp [bound,Ewald.sq] at hh ⊢
  nlinarith [sq_nonneg (x 0-2*center L 0),sq_nonneg (x 1-2*center L 1),sq_nonneg (x 2-2*center L 2)]

theorem gap {L z : Triple} (hz : L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) :
    1/4 ≤ radius (shifted x z) := by
  have hd := difference_bound hx
  have hs := shifted_square_all ((2 : ℝ) • (x-center L)) (L+z)
  have he : (fun i => coord (L+z) i + ((2 : ℝ) • (x-center L)) i) = (2 : ℝ) • shifted x z := by
    funext i
    simp only [coord_add,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,shifted,Pi.add_apply,center]
    ring
  rw [he,sq_smul,sq_smul] at hs
  have hn := normSq_ge_one hz
  have hr := radius_square (sq_nonnegative (shifted x z))
  have hr0 : 0 ≤ radius (shifted x z) := Real.sqrt_nonneg _
  nlinarith

theorem majorant_nonneg (L z : Triple) : 0 ≤ majorant L z := by unfold majorant; positivity

theorem majorant_summable (L : Triple) : Summable (majorant L) :=
  (scaled_gaussian_summable (by norm_num : (0 : ℝ) < 1/2)).mul_left (exp (4*bound L))

theorem gaussian_bound {L : Triple} {x : Vec} (hx : x ∈ domain L) (z : Triple) :
    exp (-4*Ewald.sq (shifted x z)) ≤ majorant L z := by
  have hs := shifted_square_all ((2 : ℝ) • x) z
  have he : (fun i => coord z i + ((2 : ℝ) • x) i) = (2 : ℝ) • shifted x z := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,shifted,Pi.add_apply,center]
    ring
  rw [he,sq_smul,sq_smul] at hs
  unfold majorant
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [square_bound hx])

theorem potential_bound {L z : Triple} (hz : L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) :
    |potential (shifted x z)| ≤ 8*majorant L z :=
  (RealSpaceHessian.potential_bound (gap hz hx)).trans
    (mul_le_mul_of_nonneg_left (gaussian_bound hx z) (by norm_num))

theorem gradient_bound {L z : Triple} (hz : L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) (i : Fin 3) :
    |gradient (shifted x z) i| ≤ 48*majorant L z :=
  (RealSpaceHessian.gradient_bound (gap hz hx) i).trans
    (mul_le_mul_of_nonneg_left (gaussian_bound hx z) (by norm_num))

theorem hessian_bound {L z : Triple} (hz : L+z ≠ 0) {x : Vec} (hx : x ∈ domain L) (i j : Fin 3) :
    |hessian (shifted x z) i j| ≤ 800*majorant L z :=
  (RealSpaceHessian.hessian_bound (gap hz hx) i j).trans
    (mul_le_mul_of_nonneg_left (gaussian_bound hx z) (by norm_num))

/-- Every coordinate line has a real open interval remaining in the common domain. -/
theorem line_neighborhood {L : Triple} {x : Vec} (hx : x ∈ domain L) (i : Fin 3) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Metric.ball (0 : ℝ) r, line x (basis i) t ∈ domain L := by
  have hc : Continuous (fun t : ℝ => line x (basis i) t) := by unfold line; fun_prop
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), line x (basis i) t ∈ domain L :=
    hc.continuousAt (IsOpen.mem_nhds (domain_open L) (by simpa only [line_zero] using hx))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨r,hr,fun t ht => hsub ht⟩

end BccSharp.LatticeNeighborhood
