import BccSharp.Cover.JLeafScreenedTerms
import BccSharp.Cover.JLeafF
import BccSharp.Lattice.KernelJet

set_option autoImplicit false

/-! # Log-convex Jensen supports (Stage5b phase, Stage6 F/D, Adaptive `Z`)

The Stage5b phase pass, the Stage6 shared supports and the Adaptive `Z` route
bound the screened series below by one construction:

* **Log tangents.** Each kernel `G(a, ·)` is log-convex. For any anchor
  `y₀ > 0` and any slope `σ`,
  `G(a, y) ≥ e^{-σ(y-y₀)} (G(a,y₀) + (y-y₀)(G'(a,y₀) + σ G(a,y₀)))`
  (`kernel_log_tangent`). The bracket is the exact tangent value when `σ` is the
  log-derivative; for a rational `σ` near it, the bracket stays above
  `G(a,y₀) - Y ε` with `|y - y₀| ≤ Y` and `|G' + σ G| ≤ ε` (`term_lower`).
  The proof integrates `1 + z ≤ eᶻ` against the kernel's integrand
  (`gKernel_tangent`), and identifies the moment `G(a+1, y₀)` with `-G'(a, y₀)`
  by Fermat's theorem at the supporting line (`gKernel_succ`).
* **Phase secants.** On an interval of phases between two half-integers,
  `1 + cos 2πt = 2 cos²(π(t-k))` and `cos` is concave, so a log-affine minorant
  `p e^{β(t-t₀)}` that holds at both endpoints holds throughout
  (`phase_secant`; the exponential is convex, so no logarithm is needed).
* **Jensen.** `Σ W_j e^{u_j} ≥ M exp(Σ W_j u_j / M)` with `M = Σ W_j`
  (`jensen_exp`, from `1 + z ≤ eᶻ` at the weighted mean).
* **Corners.** The exponent is a constant plus a `LinTerm` sum with
  nonpositive slopes, which is separately concave in the eight chart
  coordinates (`linSum_chord`), so its minimum over a box is at a corner.

`JTerm.Valid` says a term lies below its screened series contribution on a
support box. `jensen_support` turns valid terms with distinct indices into a
lower bound for the energy, and `jensen_fcc` gives the `strictFCC` route
result from finitely many rational corner checks. The fixed-point evaluator
that builds and checks the terms is `BccSharp.Cover.JensenFix`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BccSharp.Coulomb.CompactCover.Jensen
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover (KernelKind kernelValue kernelSlope kernelValue_hasDerivAt
  cubeRootCheck)
open BccSharp.Coulomb.CompactCover.JLeaf
open BccSharp.Coulomb.CompactCover.JLeaf.Screened (physicalS)
open BccSharp.Coulomb.CompactCover.DirectRoute (lexPositive cornerRat scaleInput scaleWitness)

/-! ### The log tangent of a kernel -/

theorem gIntegrand_integrable {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => Real.exp (-t * u) * u ^ (a - 1)) (Set.Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := t)
    (by linarith) one_pos ht
  have h' : IntegrableOn (fun u : ℝ => Real.exp (-t * u) * u ^ (a - 1)) (Set.Ioi 0) := by
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    ring
  exact h'.mono_set (Set.Ioi_subset_Ioi zero_le_one)

/-- **Integrated tangent.** For `a > 0`, anchors `y₀, y > 0` and any `σ`,
`e^{-σ(y-y₀)} (G(a,y₀) - (y-y₀)(G(a+1,y₀) - σ G(a,y₀))) ≤ G(a,y)`. -/
theorem gKernel_tangent {a : ℝ} (ha : 0 < a) {y0 y : ℝ} (h0 : 0 < y0) (hy : 0 < y) (σ : ℝ) :
    Real.exp (-σ * (y - y0)) *
        (gKernel a y0 - (y - y0) * (gKernel (a + 1) y0 - σ * gKernel a y0)) ≤
      gKernel a y := by
  have i0 := gIntegrand_integrable ha h0
  have i1 := gIntegrand_integrable (a := a + 1) (by linarith) h0
  have iy := gIntegrand_integrable ha hy
  have j1 : IntegrableOn (fun u : ℝ => (y - y0) * (Real.exp (-y0 * u) * u ^ (a + 1 - 1) -
      σ * (Real.exp (-y0 * u) * u ^ (a - 1)))) (Set.Ioi 1) :=
    (i1.sub (i0.const_mul σ)).const_mul (y - y0)
  have lowerInt : IntegrableOn (fun u : ℝ => Real.exp (-σ * (y - y0)) *
      (Real.exp (-y0 * u) * u ^ (a - 1) - (y - y0) * (Real.exp (-y0 * u) * u ^ (a + 1 - 1) -
        σ * (Real.exp (-y0 * u) * u ^ (a - 1))))) (Set.Ioi 1) :=
    (i0.sub j1).const_mul _
  have point : ∀ u ∈ Set.Ioi (1 : ℝ),
      Real.exp (-σ * (y - y0)) * (Real.exp (-y0 * u) * u ^ (a - 1) -
        (y - y0) * (Real.exp (-y0 * u) * u ^ (a + 1 - 1) -
          σ * (Real.exp (-y0 * u) * u ^ (a - 1)))) ≤
      Real.exp (-y * u) * u ^ (a - 1) := by
    intro u hu
    have u0 : 0 < u := zero_lt_one.trans hu
    have pw : u ^ (a + 1 - 1) = u * u ^ (a - 1) := by
      rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add u0, Real.rpow_one]
      ring
    have key := Real.add_one_le_exp (-(y - y0) * (u - σ))
    have split : Real.exp (-y * u) =
        Real.exp (-y0 * u) * (Real.exp (-σ * (y - y0)) * Real.exp (-(y - y0) * (u - σ))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have pos : 0 ≤ Real.exp (-y0 * u) * u ^ (a - 1) :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg u0.le _)
    have Epos : 0 ≤ Real.exp (-σ * (y - y0)) := (Real.exp_pos _).le
    rw [pw, split]
    have e : Real.exp (-σ * (y - y0)) * (Real.exp (-y0 * u) * u ^ (a - 1) -
        (y - y0) * (Real.exp (-y0 * u) * (u * u ^ (a - 1)) -
          σ * (Real.exp (-y0 * u) * u ^ (a - 1)))) =
        (Real.exp (-y0 * u) * u ^ (a - 1)) * Real.exp (-σ * (y - y0)) *
          (-(y - y0) * (u - σ) + 1) := by
      ring
    rw [e]
    calc (Real.exp (-y0 * u) * u ^ (a - 1)) * Real.exp (-σ * (y - y0)) * (-(y - y0) * (u - σ) + 1)
        ≤ (Real.exp (-y0 * u) * u ^ (a - 1)) * Real.exp (-σ * (y - y0)) *
            Real.exp (-(y - y0) * (u - σ)) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg pos Epos)
      _ = Real.exp (-y0 * u) * (Real.exp (-σ * (y - y0)) * Real.exp (-(y - y0) * (u - σ))) *
            u ^ (a - 1) := by ring
  have mono := setIntegral_mono_on lowerInt iy measurableSet_Ioi point
  have eval : (∫ u in Set.Ioi (1 : ℝ), Real.exp (-σ * (y - y0)) *
        (Real.exp (-y0 * u) * u ^ (a - 1) - (y - y0) * (Real.exp (-y0 * u) * u ^ (a + 1 - 1) -
          σ * (Real.exp (-y0 * u) * u ^ (a - 1))))) =
      Real.exp (-σ * (y - y0)) *
        (gKernel a y0 - (y - y0) * (gKernel (a + 1) y0 - σ * gKernel a y0)) := by
    rw [integral_const_mul, integral_sub i0 j1, integral_const_mul,
      integral_sub i1 (i0.const_mul σ), integral_const_mul]
    rfl
  rw [eval] at mono
  exact mono

theorem kind_power_pos (k : KernelKind) : (0 : ℝ) < (k.power : ℝ) := by
  cases k <;> norm_num [KernelKind.power]

/-- **The next moment is minus the slope** (Fermat's theorem at the supporting
line of `gKernel_tangent` with `σ = 0`). -/
theorem gKernel_succ (k : KernelKind) {y0 : ℝ} (h0 : 0 < y0) :
    gKernel ((k.power : ℝ) + 1) y0 = -kernelSlope k y0 := by
  have ha := kind_power_pos k
  let g : ℝ → ℝ := fun y =>
    kernelValue k y - kernelValue k y0 + (y - y0) * gKernel ((k.power : ℝ) + 1) y0
  have hmin : IsLocalMin g y0 := by
    filter_upwards [Ioi_mem_nhds h0] with y hy
    have t := gKernel_tangent ha h0 hy 0
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, sub_zero] at t
    show g y0 ≤ g y
    simp only [g, kernelValue, sub_self, zero_mul, add_zero]
    linarith
  have hd : HasDerivAt g (kernelSlope k y0 + gKernel ((k.power : ℝ) + 1) y0) y0 := by
    have h1 := ((kernelValue_hasDerivAt k h0).sub_const (kernelValue k y0)).add
      (((hasDerivAt_id y0).sub_const y0).mul_const (gKernel ((k.power : ℝ) + 1) y0))
    convert h1 using 1
    · funext y
      simp [g]
    · ring
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- **Log tangent of a kernel** at any anchor and any slope. -/
theorem kernel_log_tangent (k : KernelKind) {y0 y : ℝ} (h0 : 0 < y0) (hy : 0 < y) (σ : ℝ) :
    Real.exp (-σ * (y - y0)) *
        (kernelValue k y0 + (y - y0) * (kernelSlope k y0 + σ * kernelValue k y0)) ≤
      kernelValue k y := by
  have t := gKernel_tangent (kind_power_pos k) h0 hy σ
  rw [gKernel_succ k h0] at t
  have e : kernelValue k y0 + (y - y0) * (kernelSlope k y0 + σ * kernelValue k y0) =
      gKernel (k.power : ℝ) y0 -
        (y - y0) * (-kernelSlope k y0 - σ * gKernel (k.power : ℝ) y0) := by
    simp only [kernelValue]
    ring
  rw [e]
  exact t

/-- **Term lower bound.** With `|y - y₀| ≤ Y` and `|G' + σ G| ≤ ε` at the
anchor, `V ≤ G(y₀) - Y ε` gives `V e^{-σ(y-y₀)} ≤ G(y)`. -/
theorem term_lower (k : KernelKind) {y0 y σ V Ymax ε : ℝ} (h0 : 0 < y0) (hy : 0 < y)
    (hY : |y - y0| ≤ Ymax) (hε : |kernelSlope k y0 + σ * kernelValue k y0| ≤ ε)
    (hV : V ≤ kernelValue k y0 - Ymax * ε) :
    V * Real.exp (-σ * (y - y0)) ≤ kernelValue k y := by
  have t := kernel_log_tangent k h0 hy σ
  have h2 : |y - y0| * |kernelSlope k y0 + σ * kernelValue k y0| ≤ Ymax * ε :=
    mul_le_mul hY hε (abs_nonneg _) ((abs_nonneg _).trans hY)
  have h3 : -(|y - y0| * |kernelSlope k y0 + σ * kernelValue k y0|) ≤
      (y - y0) * (kernelSlope k y0 + σ * kernelValue k y0) := by
    rw [← abs_mul]
    exact neg_abs_le _
  have b : V ≤ kernelValue k y0 + (y - y0) * (kernelSlope k y0 + σ * kernelValue k y0) := by
    linarith
  calc V * Real.exp (-σ * (y - y0))
      ≤ (kernelValue k y0 + (y - y0) * (kernelSlope k y0 + σ * kernelValue k y0)) *
          Real.exp (-σ * (y - y0)) :=
        mul_le_mul_of_nonneg_right b (Real.exp_pos _).le
    _ ≤ kernelValue k y := by rw [mul_comm]; exact t

/-! ### Phase secants -/

theorem one_add_cos_eq (k : ℤ) (x : ℝ) :
    1 + Real.cos (2 * Real.pi * x) = 2 * Real.cos (Real.pi * (x - k)) ^ 2 := by
  have h1 : Real.cos (2 * Real.pi * x) = Real.cos (2 * (Real.pi * (x - k))) := by
    have e : 2 * (Real.pi * (x - k)) = 2 * Real.pi * x - (k : ℝ) * (2 * Real.pi) := by ring
    rw [e, Real.cos_sub_int_mul_two_pi]
  rw [h1, Real.cos_two_mul]
  ring

/-- **Phase secant.** Between two consecutive half-integers `k ± 1/2`, a
log-affine function below `1 + cos 2πt` at both ends of `[l, r]` stays below it
on the whole interval. -/
theorem phase_secant {l r t0 β p : ℝ} (k : ℤ) (hl : (k : ℝ) - 1 / 2 < l)
    (hr : r < (k : ℝ) + 1 / 2) (hp : 0 ≤ p)
    (hA : p * Real.exp (β * (l - t0)) ≤ 1 + Real.cos (2 * Real.pi * l))
    (hB : p * Real.exp (β * (r - t0)) ≤ 1 + Real.cos (2 * Real.pi * r))
    {t : ℝ} (htl : l ≤ t) (htr : t ≤ r) :
    p * Real.exp (β * (t - t0)) ≤ 1 + Real.cos (2 * Real.pi * t) := by
  have gsq : ∀ x, p * Real.exp (β * (x - t0)) =
      2 * (Real.sqrt (p / 2) * Real.exp (β * (x - t0) / 2)) ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (div_nonneg hp (by norm_num : (0 : ℝ) ≤ 2)), ← Real.exp_nat_mul]
    have e : ((2 : ℕ) : ℝ) * (β * (x - t0) / 2) = β * (x - t0) := by push_cast; ring
    rw [e]
    ring
  have gnn : ∀ x, 0 ≤ Real.sqrt (p / 2) * Real.exp (β * (x - t0) / 2) :=
    fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have inArc : ∀ x, l ≤ x → x ≤ r →
      Real.pi * (x - k) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x h1 h2
    have pp := Real.pi_pos
    constructor <;> nlinarith
  have cnn : ∀ x, l ≤ x → x ≤ r → 0 ≤ Real.cos (Real.pi * (x - k)) := by
    intro x h1 h2
    exact Real.cos_nonneg_of_mem_Icc (inArc x h1 h2)
  have le_of_sq : ∀ x, l ≤ x → x ≤ r →
      p * Real.exp (β * (x - t0)) ≤ 1 + Real.cos (2 * Real.pi * x) →
      Real.sqrt (p / 2) * Real.exp (β * (x - t0) / 2) ≤ Real.cos (Real.pi * (x - k)) := by
    intro x h1 h2 h
    rw [gsq, one_add_cos_eq k] at h
    have g0 := gnn x
    have c0 := cnn x h1 h2
    by_contra hc
    have hlt := lt_of_not_ge hc
    nlinarith
  have lr : l ≤ r := htl.trans htr
  have gl := le_of_sq l le_rfl lr hA
  have gr := le_of_sq r lr le_rfl hB
  have gct : Real.sqrt (p / 2) * Real.exp (β * (t - t0) / 2) ≤ Real.cos (Real.pi * (t - k)) := by
    rcases eq_or_lt_of_le lr with e | lt
    · have et : t = l := le_antisymm (e ▸ htr) htl
      rw [et]
      exact gl
    · have den : 0 < r - l := sub_pos.mpr lt
      set θ := (t - l) / (r - l) with hθ
      have θ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr htl) den.le
      have θ1 : θ ≤ 1 := (div_le_one den).mpr (by linarith)
      have ht : t = (1 - θ) * l + θ * r := by
        rw [hθ]
        field_simp
        ring
      have cv := convexOn_exp.2 (Set.mem_univ (β * (l - t0) / 2))
        (Set.mem_univ (β * (r - t0) / 2)) (sub_nonneg.mpr θ1) θ0 (by ring)
      simp only [smul_eq_mul] at cv
      have e1 : (1 - θ) * (β * (l - t0) / 2) + θ * (β * (r - t0) / 2) = β * (t - t0) / 2 := by
        rw [ht]
        ring
      rw [e1] at cv
      have cc := strictConcaveOn_cos_Icc.concaveOn.2 (inArc l le_rfl lr) (inArc r lr le_rfl)
        (sub_nonneg.mpr θ1) θ0 (by ring)
      simp only [smul_eq_mul] at cc
      have e2 : (1 - θ) * (Real.pi * (l - k)) + θ * (Real.pi * (r - k)) = Real.pi * (t - k) := by
        rw [ht]
        ring
      rw [e2] at cc
      have sq := Real.sqrt_nonneg (p / 2)
      have gconv := mul_le_mul_of_nonneg_left cv sq
      have m1 := mul_le_mul_of_nonneg_left gl (sub_nonneg.mpr θ1)
      have m2 := mul_le_mul_of_nonneg_left gr θ0
      nlinarith
  rw [gsq, one_add_cos_eq k]
  have sq' := mul_le_mul gct gct (gnn t) ((gnn t).trans gct)
  nlinarith

/-! ### Jensen for the exponential -/

theorem list_affine_sum (l : List (ℝ × ℝ)) (c d : ℝ) :
    (l.map fun x => x.1 * (c + d * x.2)).sum =
      c * (l.map Prod.fst).sum + d * (l.map fun x => x.1 * x.2).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- **Jensen's inequality for `exp`** with nonnegative weights `x.1`. -/
theorem jensen_exp (l : List (ℝ × ℝ)) (hw : ∀ x ∈ l, 0 ≤ x.1)
    (hM : 0 < (l.map Prod.fst).sum) :
    (l.map Prod.fst).sum * Real.exp ((l.map fun x => x.1 * x.2).sum / (l.map Prod.fst).sum) ≤
      (l.map fun x => x.1 * Real.exp x.2).sum := by
  have each : ∀ x ∈ l, x.1 * (Real.exp ((l.map fun x => x.1 * x.2).sum / (l.map Prod.fst).sum) *
      (1 - (l.map fun x => x.1 * x.2).sum / (l.map Prod.fst).sum) +
      Real.exp ((l.map fun x => x.1 * x.2).sum / (l.map Prod.fst).sum) * x.2) ≤
        x.1 * Real.exp x.2 := by
    intro x hx
    set m := (l.map fun x => x.1 * x.2).sum / (l.map Prod.fst).sum
    have key := Real.add_one_le_exp (x.2 - m)
    have e : Real.exp x.2 = Real.exp m * Real.exp (x.2 - m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h : Real.exp m * (1 - m) + Real.exp m * x.2 ≤ Real.exp x.2 := by
      rw [e]
      have := mul_le_mul_of_nonneg_left key (Real.exp_pos m).le
      linarith
    exact mul_le_mul_of_nonneg_left h (hw x hx)
  have sum := List.sum_le_sum each
  rw [list_affine_sum] at sum
  generalize (l.map Prod.fst).sum = M at hM sum ⊢
  generalize (l.map fun x => x.1 * x.2).sum = X at sum ⊢
  have hM0 : M ≠ 0 := hM.ne'
  have e : Real.exp (X / M) * (1 - X / M) * M + Real.exp (X / M) * X = M * Real.exp (X / M) := by
    field_simp
    ring
  linarith

/-! ### Jensen terms -/

/-- The exponential rate of a term kind at screening `s`: `π s²` for the
direct modes and `π / s²` for the reciprocal modes. -/
def rate (s : ℚ) : Kind → ℝ
  | .cross => Real.pi * (s : ℝ) ^ 2
  | .period => Real.pi * (s : ℝ) ^ 2
  | .wave => Real.pi / (s : ℝ) ^ 2

/-- One term of a Jensen support: weight `W`, radial anchor `y₀` and
log-slope `σ` in the variable `y = rate · q`, phase anchor `t₀` and log-slope
`β` (zero for direct modes), and a rational upper bound `rhi` of the rate. -/
structure JTerm where
  kind : Kind
  index : IntVec
  W : ℚ
  sig : ℚ
  y0 : ℚ
  beta : ℚ
  t0 : ℚ
  rhi : ℚ

/-- The exponent `u = -σ(rate·q - y₀) + β(m·f - t₀)`. -/
def JTerm.u (s : ℚ) (t : JTerm) (p : Chart) : ℝ :=
  -(t.sig : ℝ) * (rate s t.kind * termQ t.kind t.index p - t.y0) +
    (t.beta : ℝ) * (phaseT t.index p - t.t0)

/-- A term is valid on the support box `S` when `W e^{u} ≤` its screened
contribution at every valid point of `S`, with nonnegative weight and slope and
an upper bound for the rate. -/
def JTerm.Valid (s : ℚ) (S : Cell) (t : JTerm) : Prop :=
  0 ≤ t.W ∧ 0 ≤ t.sig ∧ rate s t.kind ≤ t.rhi ∧
    ∀ p, S.Mem p → (chartPoint p).Valid →
      (t.W : ℝ) * Real.exp (t.u s p) ≤ physicalS s t.kind t.index p

/-- The distance part of the exponent with the rate replaced by `rhi`, as a
`LinTerm` with a nonpositive slope. -/
def JTerm.lin (t : JTerm) : LinTerm :=
  ⟨t.kind, t.index, 0, -(t.W * t.sig * t.rhi), t.W * t.beta⟩

def mass (ts : List JTerm) : ℚ := (ts.map JTerm.W).sum

def centerConst (ts : List JTerm) : ℚ :=
  (ts.map fun t => t.W * (t.sig * t.y0 - t.beta * t.t0)).sum

theorem cast_sum_map {α : Type} (ts : List α) (f : α → ℚ) :
    (((ts.map f).sum : ℚ) : ℝ) = (ts.map fun t => (f t : ℝ)).sum := by
  rw [Rat.cast_list_sum, List.map_map]
  rfl

theorem termQ_nonneg (k : Kind) (n : IntVec) (p : Chart) : 0 ≤ termQ k n p := by
  cases k <;> simp only [termQ, primalQ, dualQ] <;> positivity

theorem lin_slope_nonpos {s : ℚ} {S : Cell} {t : JTerm} (h : t.Valid s S) (hr : 0 ≤ t.rhi) :
    t.lin.slope ≤ 0 := by
  simp only [JTerm.lin]
  have := mul_nonneg (mul_nonneg h.1 h.2.1) hr
  linarith

/-- The weighted exponent is at least the constant plus the `LinTerm` sum. -/
theorem weighted_u_ge (s : ℚ) (S : Cell) (ts : List JTerm) (valid : ∀ t ∈ ts, t.Valid s S)
    (p : Chart) :
    (centerConst ts : ℝ) + linSum (ts.map JTerm.lin) p ≤
      (ts.map fun t => (t.W : ℝ) * t.u s p).sum := by
  induction ts with
  | nil => simp [centerConst, linSum]
  | cons t rest ih =>
    have vt := valid t List.mem_cons_self
    have vr : ∀ x ∈ rest, x.Valid s S := fun x hx => valid x (List.mem_cons_of_mem _ hx)
    have hrest := ih vr
    have q0 := termQ_nonneg t.kind t.index p
    have w0 : (0 : ℝ) ≤ t.W := by exact_mod_cast vt.1
    have s0 : (0 : ℝ) ≤ t.sig := by exact_mod_cast vt.2.1
    have rr : rate s t.kind ≤ (t.rhi : ℝ) := vt.2.2.1
    have key : ((t.W * (t.sig * t.y0 - t.beta * t.t0) : ℚ) : ℝ) + (JTerm.lin t).eval p ≤
        (t.W : ℝ) * t.u s p := by
      have e : (t.W : ℝ) * t.u s p -
          (((t.W * (t.sig * t.y0 - t.beta * t.t0) : ℚ) : ℝ) + (JTerm.lin t).eval p) =
          (t.W : ℝ) * t.sig * termQ t.kind t.index p * ((t.rhi : ℝ) - rate s t.kind) := by
        simp only [JTerm.lin, LinTerm.eval, JTerm.u]
        push_cast
        ring
      have := mul_nonneg (mul_nonneg (mul_nonneg w0 s0) q0) (sub_nonneg.mpr rr)
      linarith
    have hc : (centerConst (t :: rest) : ℝ) =
        ((t.W * (t.sig * t.y0 - t.beta * t.t0) : ℚ) : ℝ) + centerConst rest := by
      simp only [centerConst, List.map_cons, List.sum_cons]
      push_cast
      ring
    have hl : linSum ((t :: rest).map JTerm.lin) p =
        (JTerm.lin t).eval p + linSum (rest.map JTerm.lin) p := by
      simp [linSum]
    have hs : ((t :: rest).map fun x => (x.W : ℝ) * x.u s p).sum =
        (t.W : ℝ) * t.u s p + (rest.map fun x => (x.W : ℝ) * x.u s p).sum := by
      simp
    rw [hc, hl, hs]
    linarith

/-! ### Structure of a term list (distinct indices per kind) -/

private theorem sum_by_kind (l : List LinTerm) (g : LinTerm → ℝ) :
    (l.map g).sum = ((l.filter (fun t => decide (t.kind = .cross))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .period))).map g).sum +
      ((l.filter (fun t => decide (t.kind = .wave))).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hk : a.kind <;> simp [hk, ih] <;> ring

private theorem filter_kind_sum (l : List LinTerm) (k : Kind) (G : Kind → IntVec → ℝ) :
    ((l.filter (fun t => decide (t.kind = k))).map (fun t => G t.kind t.index)).sum =
      ((kindIdx k l).map (fun n => G k n)).sum := by
  induction l with
  | nil => simp [kindIdx]
  | cons a l ih =>
    by_cases hk : a.kind = k
    · simp [hk, kindIdx] at ih ⊢
      rw [ih]
    · simp [hk, kindIdx] at ih ⊢
      exact ih

/-- The screened contributions of terms with distinct indices per kind and
lex-positive period and wave indices sum to at most `h₂ - 4 + 2s + 2/s²`. -/
theorem physical_sum_le (s : ℚ) (hs : 0 < s) (lins : List LinTerm)
    (hst : structureOk lins = true) (p : Chart) (hv : (chartPoint p).Valid) :
    (lins.map fun t => physicalS s t.kind t.index p).sum ≤
      h₂ (chartPoint p) - 4 + (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2) := by
  have st := of_decide_eq_true hst
  obtain ⟨ncross, nperiod, nwave, lexP, lexW⟩ := st
  have fc := filter_kind_sum lins .cross (fun k n => physicalS s k n p)
  have fp := filter_kind_sum lins .period (fun k n => physicalS s k n p)
  have fw := filter_kind_sum lins .wave (fun k n => physicalS s k n p)
  rw [sum_by_kind lins, fc, fp, fw]
  have cross : ((kindIdx .cross lins).map (fun n => physicalS s .cross n p)).sum =
      (s : ℝ) * ∑ n ∈ (kindIdx .cross lins).toFinset,
        ScreenedSeries.crossTerm (s : ℝ) (chartPoint p) n := by
    rw [Finset.mul_sum, List.sum_toFinset _ ncross]
    rfl
  have period : ((kindIdx .period lins).map (fun n => physicalS s .period n p)).sum =
      2 * (s : ℝ) * ∑ n ∈ (kindIdx .period lins).toFinset,
        ScreenedSeries.periodTerm (s : ℝ) (chartPoint p) n := by
    rw [Finset.mul_sum, List.sum_toFinset _ nperiod]
    refine congrArg List.sum (List.map_congr_left fun n hn => ?_)
    simp only [physicalS, ScreenedSeries.periodTerm, ite_eq_right (DirectRoute.lex_ne (lexP n hn))]
  have wave : ((kindIdx .wave lins).map (fun n => physicalS s .wave n p)).sum =
      2 / (s : ℝ) ^ 2 * ∑ n ∈ (kindIdx .wave lins).toFinset,
        ScreenedSeries.waveTerm (s : ℝ) (chartPoint p) n := by
    rw [Finset.mul_sum, List.sum_toFinset _ nwave]
    refine congrArg List.sum (List.map_congr_left fun n hn => ?_)
    simp only [physicalS, ScreenedSeries.waveTerm, ite_eq_right (DirectRoute.lex_ne (lexW n hn))]
  rw [cross, period, wave]
  have sr : (0 : ℝ) < s := by exact_mod_cast hs
  have fl := ScreenedSeries.finite_lower_lex (chartPoint p) hv (s : ℝ) sr
    (kindIdx .cross lins).toFinset (kindIdx .period lins).toFinset (kindIdx .wave lins).toFinset
    (fun n hn => lexP n (List.mem_toFinset.mp hn)) (fun n hn => lexW n (List.mem_toFinset.mp hn))
  linarith

/-! ### The support bound -/

/-- **Jensen support.** Valid terms with distinct indices per kind bound the
energy below at every valid point of the support box:
`(M exp((C + Σ lin)/M) - 2s - 2/s²) / (2 a_c) ≤ e`. -/
theorem jensen_support (s : ℚ) (hs : 0 < s) (S : Cell) (ts : List JTerm)
    (valid : ∀ t ∈ ts, t.Valid s S) (hst : structureOk (ts.map JTerm.lin) = true)
    (hM : 0 < mass ts) (p : Chart) (hp : S.Mem p) (hv : (chartPoint p).Valid) :
    ((mass ts : ℝ) * Real.exp (((centerConst ts : ℝ) + linSum (ts.map JTerm.lin) p) / mass ts) -
        (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2)) / (2 * ac) ≤ energy (chartPoint p) := by
  have phys := physical_sum_le s hs (ts.map JTerm.lin) hst p hv
  have phys' : (ts.map fun t => physicalS s t.kind t.index p).sum ≤
      h₂ (chartPoint p) - 4 + (2 * (s : ℝ) + 2 / (s : ℝ) ^ 2) := by
    simpa [List.map_map, Function.comp_def, JTerm.lin] using phys
  have each : (ts.map fun t => (t.W : ℝ) * Real.exp (t.u s p)).sum ≤
      (ts.map fun t => physicalS s t.kind t.index p).sum :=
    List.sum_le_sum fun t ht => (valid t ht).2.2.2 p hp hv
  let l : List (ℝ × ℝ) := ts.map fun t => ((t.W : ℝ), t.u s p)
  have lw : ∀ x ∈ l, 0 ≤ x.1 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    show (0 : ℝ) ≤ t.W
    exact_mod_cast (valid t ht).1
  have lM : (l.map Prod.fst).sum = (mass ts : ℝ) := by
    simp only [l, List.map_map, mass, cast_sum_map]
    rfl
  have lX : (l.map fun x => x.1 * x.2).sum = (ts.map fun t => (t.W : ℝ) * t.u s p).sum := by
    simp only [l, List.map_map]
    rfl
  have lE : (l.map fun x => x.1 * Real.exp x.2).sum =
      (ts.map fun t => (t.W : ℝ) * Real.exp (t.u s p)).sum := by
    simp only [l, List.map_map]
    rfl
  have Mr : (0 : ℝ) < mass ts := by exact_mod_cast hM
  have jen := jensen_exp l lw (by rw [lM]; exact Mr)
  rw [lM, lX, lE] at jen
  have wu := weighted_u_ge s S ts valid p
  have expmono : Real.exp (((centerConst ts : ℝ) + linSum (ts.map JTerm.lin) p) / mass ts) ≤
      Real.exp ((ts.map fun t => (t.W : ℝ) * t.u s p).sum / mass ts) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right wu Mr.le)
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  unfold energy
  refine div_le_div_of_nonneg_right ?_ acpos.le
  have m1 := mul_le_mul_of_nonneg_left expmono Mr.le
  linarith

/-! ### Leaf comparisons from corner checks -/

/-- On a leaf `b`, the exponent's `LinTerm` sum is at least its least value over
the 256 corners of `b`. -/
theorem lin_corner_lower (S b : Cell) (ts : List JTerm) (s : ℚ) (valid : ∀ t ∈ ts, t.Valid s S)
    (rhi : ∀ t ∈ ts, 0 ≤ t.rhi) (lo0 : 0 < b.lo 0) (lo1 : 0 < b.lo 1)
    (ord : ∀ i, b.lo i ≤ b.hi i) (X : ℚ)
    (corners : ∀ bits, X ≤ centerConst ts +
      aggValueQ (aggConst (ts.map JTerm.lin)) (fun j => aggWeight (ts.map JTerm.lin) j)
        (cornerRat b bits))
    (p : Chart) (hp : b.Mem p) :
    (X : ℝ) ≤ (centerConst ts : ℝ) + linSum (ts.map JTerm.lin) p := by
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast lo0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast lo1
  have neg : ∀ t ∈ ts.map JTerm.lin, t.slope ≤ 0 := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact lin_slope_nonpos (valid u hu) (rhi u hu)
  have chord := linSum_chord (ts.map JTerm.lin) b b0 b1 neg
  obtain ⟨bits, hbits⟩ := corner_le b _ chord p hp
  have c0 : cornerRat b bits 0 ≠ 0 := (cornerRat_pos b bits 0 lo0 (ord 0)).ne'
  have c1 : cornerRat b bits 1 ≠ 0 := (cornerRat_pos b bits 1 lo1 (ord 1)).ne'
  have cr0 : (corner b bits) 0 ≠ 0 := by rw [corner_coord]; exact_mod_cast c0
  have cr1 : (corner b bits) 1 ≠ 0 := by rw [corner_coord]; exact_mod_cast c1
  have agg : linSum (ts.map JTerm.lin) (corner b bits) =
      ((aggValueQ (aggConst (ts.map JTerm.lin)) (fun j => aggWeight (ts.map JTerm.lin) j)
        (cornerRat b bits) : ℚ) : ℝ) := by
    rw [linSum_feat _ _ cr0 cr1]
    unfold aggValueQ
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [featGen_cast, cornerRat_cast]
  have hX := corners bits
  have hXr : (X : ℝ) ≤ (centerConst ts : ℝ) +
      ((aggValueQ (aggConst (ts.map JTerm.lin)) (fun j => aggWeight (ts.map JTerm.lin) j)
        (cornerRat b bits) : ℚ) : ℝ) := by exact_mod_cast hX
  rw [← agg] at hXr
  linarith

/-- The energy lower bound on a leaf from its corner minimum `X` and a rational
lower bound `E ≤ exp(X / M)`. -/
theorem jensen_leaf_energy (s : ℚ) (hs : 0 < s) (S b : Cell) (ts : List JTerm)
    (valid : ∀ t ∈ ts, t.Valid s S) (rhi : ∀ t ∈ ts, 0 ≤ t.rhi)
    (hst : structureOk (ts.map JTerm.lin) = true) (hM : 0 < mass ts)
    (inside : boxIn b S = true) (lo0 : 0 < b.lo 0) (lo1 : 0 < b.lo 1)
    (ord : ∀ i, b.lo i ≤ b.hi i) (X : ℚ)
    (corners : ∀ bits, X ≤ centerConst ts +
      aggValueQ (aggConst (ts.map JTerm.lin)) (fun j => aggWeight (ts.map JTerm.lin) j)
        (cornerRat b bits))
    (E : ℚ) (hE : (E : ℝ) ≤ Real.exp ((X : ℝ) / mass ts))
    (hsc : cubeRootCheck scaleWitness scaleInput = true) (hlo : 0 < scaleWitness.lower)
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    (divScale (mass ts * E - (2 * s + 2 / s ^ 2)) : ℝ) ≤ energy (chartPoint p) := by
  have sup := jensen_support s hs S ts valid hst hM p (boxIn_sound inside hp) hv
  have cl := lin_corner_lower S b ts s valid rhi lo0 lo1 ord X corners p hp
  have Mr : (0 : ℝ) < mass ts := by exact_mod_cast hM
  have e1 : Real.exp ((X : ℝ) / mass ts) ≤
      Real.exp (((centerConst ts : ℝ) + linSum (ts.map JTerm.lin) p) / mass ts) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right cl Mr.le)
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  have dv := divScale_le (mass ts * E - (2 * s + 2 / s ^ 2)) hsc hlo
  refine dv.trans (le_trans ?_ sup)
  refine div_le_div_of_nonneg_right ?_ acpos.le
  push_cast
  have m1 := mul_le_mul_of_nonneg_left (hE.trans e1) Mr.le
  linarith

/-- **`strictFCC` from a Jensen support.** -/
theorem jensen_fcc (s : ℚ) (hs : 0 < s) (S b : Cell) (ts : List JTerm)
    (valid : ∀ t ∈ ts, t.Valid s S) (rhi : ∀ t ∈ ts, 0 ≤ t.rhi)
    (hst : structureOk (ts.map JTerm.lin) = true) (hM : 0 < mass ts)
    (inside : boxIn b S = true) (lo0 : 0 < b.lo 0) (lo1 : 0 < b.lo 1)
    (ord : ∀ i, b.lo i ≤ b.hi i) (X : ℚ)
    (corners : ∀ bits, X ≤ centerConst ts +
      aggValueQ (aggConst (ts.map JTerm.lin)) (fun j => aggWeight (ts.map JTerm.lin) j)
        (cornerRat b bits))
    (E : ℚ) (hE : (E : ℝ) ≤ Real.exp ((X : ℝ) / mass ts))
    (hsc : cubeRootCheck scaleWitness scaleInput = true) (hlo : 0 < scaleWitness.lower)
    (final : Constants.fccBracket.hi < divScale (mass ts * E - (2 * s + 2 / s ^ 2)))
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) := by
  have low := jensen_leaf_energy s hs S b ts valid rhi hst hM inside lo0 lo1 ord X corners E hE
    hsc hlo p hp hv
  have fccUp : energy fcc ≤ (Constants.fccBracket.hi : ℝ) := (Constants.reference_bounds .fcc).2
  have fr : (Constants.fccBracket.hi : ℝ) < divScale (mass ts * E - (2 * s + 2 / s ^ 2)) := by
    exact_mod_cast final
  linarith

/-- Some corner of `b` has exponent value at most the value at `p`. -/
theorem lin_corner_exists (S b : Cell) (ts : List JTerm) (s : ℚ) (valid : ∀ t ∈ ts, t.Valid s S)
    (rhi : ∀ t ∈ ts, 0 ≤ t.rhi) (lo0 : 0 < b.lo 0) (lo1 : 0 < b.lo 1)
    (ord : ∀ i, b.lo i ≤ b.hi i) (p : Chart) (hp : b.Mem p) :
    ∃ bits : Axis → Bool, ((centerConst ts + aggValueQ (aggConst (ts.map JTerm.lin))
        (fun j => aggWeight (ts.map JTerm.lin) j) (cornerRat b bits) : ℚ) : ℝ) ≤
      (centerConst ts : ℝ) + linSum (ts.map JTerm.lin) p := by
  have b0 : (0 : ℝ) < b.lo 0 := by exact_mod_cast lo0
  have b1 : (0 : ℝ) < b.lo 1 := by exact_mod_cast lo1
  have neg : ∀ t ∈ ts.map JTerm.lin, t.slope ≤ 0 := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact lin_slope_nonpos (valid u hu) (rhi u hu)
  have chord := linSum_chord (ts.map JTerm.lin) b b0 b1 neg
  obtain ⟨bits, hbits⟩ := corner_le b _ chord p hp
  refine ⟨bits, ?_⟩
  have c0 : cornerRat b bits 0 ≠ 0 := (cornerRat_pos b bits 0 lo0 (ord 0)).ne'
  have c1 : cornerRat b bits 1 ≠ 0 := (cornerRat_pos b bits 1 lo1 (ord 1)).ne'
  have cr0 : (corner b bits) 0 ≠ 0 := by rw [corner_coord]; exact_mod_cast c0
  have cr1 : (corner b bits) 1 ≠ 0 := by rw [corner_coord]; exact_mod_cast c1
  have agg : linSum (ts.map JTerm.lin) (corner b bits) =
      ((aggValueQ (aggConst (ts.map JTerm.lin)) (fun j => aggWeight (ts.map JTerm.lin) j)
        (cornerRat b bits) : ℚ) : ℝ) := by
    rw [linSum_feat _ _ cr0 cr1]
    unfold aggValueQ
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [featGen_cast, cornerRat_cast]
  push_cast
  rw [← agg]
  linarith

/-- **`strictFCC` from a Jensen support, corner by corner.** At each corner of
the leaf, `E` is a lower bound of the exponential of the exponent's corner
value, and the resulting energy lower bound exceeds the Constants upper FCC energy. -/
theorem jensen_fcc_corners (s : ℚ) (hs : 0 < s) (S b : Cell) (ts : List JTerm)
    (valid : ∀ t ∈ ts, t.Valid s S) (rhi : ∀ t ∈ ts, 0 ≤ t.rhi)
    (hst : structureOk (ts.map JTerm.lin) = true) (hM : 0 < mass ts)
    (inside : boxIn b S = true) (lo0 : 0 < b.lo 0) (lo1 : 0 < b.lo 1)
    (ord : ∀ i, b.lo i ≤ b.hi i) (E : (Axis → Bool) → ℚ)
    (hE : ∀ bits, (E bits : ℝ) ≤ Real.exp (((centerConst ts + aggValueQ (aggConst (ts.map JTerm.lin))
        (fun j => aggWeight (ts.map JTerm.lin) j) (cornerRat b bits) : ℚ) : ℝ) / mass ts))
    (hsc : cubeRootCheck scaleWitness scaleInput = true) (hlo : 0 < scaleWitness.lower)
    (final : ∀ bits, Constants.fccBracket.hi < divScale (mass ts * E bits - (2 * s + 2 / s ^ 2)))
    (p : Chart) (hp : b.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) := by
  obtain ⟨bits, hbits⟩ := lin_corner_exists S b ts s valid rhi lo0 lo1 ord p hp
  have sup := jensen_support s hs S ts valid hst hM p (boxIn_sound inside hp) hv
  have Mr : (0 : ℝ) < mass ts := by exact_mod_cast hM
  have e1 := (hE bits).trans (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hbits Mr.le))
  have acpos : (0 : ℝ) < 2 * ac := mul_pos two_pos ac_positive
  have dv := divScale_le (mass ts * E bits - (2 * s + 2 / s ^ 2)) hsc hlo
  have low : (divScale (mass ts * E bits - (2 * s + 2 / s ^ 2)) : ℝ) ≤ energy (chartPoint p) := by
    refine dv.trans (le_trans ?_ sup)
    refine div_le_div_of_nonneg_right ?_ acpos.le
    push_cast
    have m1 := mul_le_mul_of_nonneg_left e1 Mr.le
    linarith
  have fccUp : energy fcc ≤ (Constants.fccBracket.hi : ℝ) := (Constants.reference_bounds .fcc).2
  have fr : (Constants.fccBracket.hi : ℝ) < divScale (mass ts * E bits - (2 * s + 2 / s ^ 2)) := by
    exact_mod_cast final bits
  linarith

end BccSharp.Coulomb.CompactCover.Jensen
