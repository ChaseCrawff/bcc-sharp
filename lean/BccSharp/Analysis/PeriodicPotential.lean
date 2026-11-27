module

public import BccSharp.Analysis.RealSpaceSeries

/-! The actual Ewald pair potential and its Hessian. Period-lattice membership
is an explicit predicate; the finite torus normalization is retained. The
identification with the zero-mean Coulomb Green function is a separate step. -/
@[expose] public section
namespace BccSharp.PeriodicPotential
open Real Ewald LatticeTails LatticeNeighborhood Filter
open RealSpaceHessian (basis line_zero)
open ReciprocalSeries (mask frequency)
open scoped Topology

noncomputable def potential (P Q : Triple → Prop) (m N : ℝ) (x : Vec) : ℝ :=
  RealSpaceSeries.potential P x + (1/N)*ReciprocalSeries.potential m Q x - π/(2*N)

noncomputable def gradient (P Q : Triple → Prop) (m N : ℝ) (x : Vec) (i : Fin 3) : ℝ :=
  RealSpaceSeries.gradient P x i + (1/N)*ReciprocalSeries.gradient m Q x i

noncomputable def hessian (P Q : Triple → Prop) (m N : ℝ) (x : Vec) (i j : Fin 3) : ℝ :=
  deriv (fun t => deriv (fun s => potential P Q m N (line (line x (basis j) t) (basis i) s)) 0) 0

theorem potential_hasDerivAt {P Q : Triple → Prop} {L : Triple} {m : ℝ}
    (hP : ∀ z, P z → L+z ≠ 0) (hm : 0 < m) (N : ℝ) {x : Vec} (hx : x ∈ domain L) (i : Fin 3) :
    HasDerivAt (fun t => potential P Q m N (line x (basis i) t)) (gradient P Q m N x i) 0 := by
  exact ((RealSpaceSeries.potential_hasDerivAt hP hx i).add
    ((ReciprocalSeries.potential_hasDerivAt hm Q x i).const_mul (1/N))).sub_const (π/(2*N))

theorem hessian_formula {P Q : Triple → Prop} {L : Triple} {m : ℝ}
    (hP : ∀ z, P z → L+z ≠ 0) (hm : 0 < m) (N : ℝ) {x : Vec} (hx : x ∈ domain L) (i j : Fin 3) :
    hessian P Q m N x i j = RealSpaceSeries.hessian P x i j + (1/N)*ReciprocalSeries.hessian m Q x i j := by
  obtain ⟨r,hr,hline⟩ := line_neighborhood hx j
  have he : (fun t => deriv (fun s => potential P Q m N (line (line x (basis j) t) (basis i) s)) 0) =ᶠ[𝓝 0]
      (fun t => gradient P Q m N (line x (basis j) t) i) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
    exact (potential_hasDerivAt hP hm N (hline t ht) i).deriv
  have hd := (RealSpaceSeries.gradient_hasDerivAt hP hx i j).add
    ((ReciprocalSeries.gradient_hasDerivAt hm Q x i j).const_mul (1/N))
  have hh := (hd.congr_of_eventuallyEq he).deriv
  rw [RealSpaceSeries.hessian_formula hP hx,ReciprocalSeries.hessian_formula hm]
  simpa only [hessian,ReciprocalPotential.hessian_formula] using hh

theorem hessian_at_lattice {P Q : Triple → Prop} {L : Triple} {m : ℝ}
    (hP : ∀ z, P z → L+z ≠ 0) (hm : 0 < m) (N : ℝ) (i j : Fin 3) :
    hessian P Q m N (center L) i j =
      (∑' z, mask P (fun z => phi (L+z) i j) z) +
      (1/N)*(∑' z, mask Q (fun z => -(8*π)*kernel (frequency m z) i j *
        cos (ReciprocalPotential.phase (frequency m z) (center L))) z) := by
  rw [hessian_formula hP hm N (center_mem L),RealSpaceSeries.hessian_at_lattice hP,
    ReciprocalSeries.hessian_formula hm]

end BccSharp.PeriodicPotential
