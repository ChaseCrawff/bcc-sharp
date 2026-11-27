import BccSharp.Cover.AdaptiveKernel
import BccSharp.Cover.AdaptiveCorner
import BccSharp.Cover.Stage2Bulk

set_option autoImplicit false

/-! The Adaptive log-convex support check (routes `T`, `J`, `U`, `Z`, `R` and the `K` survivor).

A proposal is a list of modes of the series (`Term`: a Stage2 `Mode` and an anchor `A`,
standing for `T = A / RA`) and an optional reduction cut. For a box `b`, `supportCheck`
evaluates in fixed point (scale `S = 2^96`):

* per term, the kernel value `G` and slope `W` at the anchor (`BccSharp.Cover.AdaptiveKernel`), the
  multiplier `μ` (`1` for cross, `2` for period modes, `2ℓ` for reciprocal modes with a
  lower bound `ℓ` of the phase factor `1 + cos 2π n·f` on the box);
* `K = Σ μ G` (enclosed), `A = Σ μ W T` (lower bound), and the corner weights
  `w ≥ π μ W` of the squared distances;
* the joint corner bound `U` of `Σ w q(p) + λ c(p)` on the box (`BccSharp.Cover.AdaptiveCorner`);
* `L ≤ K e^{(A - U)/K}` (`kexp_lower`), and accepts when `L > fccHZ / S`.

`supportCheck_sound`: if the check accepts `b`, then `energy fcc < energy (chartPoint p)` at
every `good` point `p` of `b`. The chain is: each retained term of the series is at
least `μ G(T) e^{-(πq - T) W/G(T)}` (`logTangent`); their sum is at most `h₂`
(`physical_sum_le`); Jensen's inequality (`jensen_list`) bounds the sum of exponentials
by `K e^{X/K}` with `X = A - π Σ μ W q ≥ (A - U)`, using `cornerMax_sound` and, for a cut,
the reduction inequality `c(p) ≥ 0` on reduced points (`cutR_nonneg`). -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp BccSharp.Coverage BravaisCover DirectRoute Stage2 OverlayPlanar.Fix

/-! ### Proposals -/

/-- A retained mode and its anchor `A` (`T = A / RA`). -/
structure Term where
  fam : Stage2.Family
  a : ℤ
  b : ℤ
  c : ℤ
  anchor : ℕ

def Term.mode (t : Term) : Mode := ⟨t.fam, ![t.a, t.b, t.c]⟩

def famCode : Stage2.Family → ℤ
  | .cross => 0
  | .period => 1
  | .reciprocal => 2

/-- A key that orders the modes; proposals list strictly increasing keys. -/
def Term.key (t : Term) : ℤ := famCode t.fam * 125 + (t.a + 2) * 25 + (t.b + 2) * 5 + (t.c + 2)

def Term.valid (t : Term) : Bool :=
  decide (-2 ≤ t.a ∧ t.a ≤ 2 ∧ -2 ≤ t.b ∧ t.b ≤ 2 ∧ -2 ≤ t.c ∧ t.c ≤ 2) &&
    match t.fam with
    | .cross => true
    | _ => decide (0 < t.a ∨ (t.a = 0 ∧ (0 < t.b ∨ (t.b = 0 ∧ 0 < t.c))))

def increasing : List Term → Bool
  | t :: u :: rest => decide (t.key < u.key) && increasing (u :: rest)
  | _ => true

def Term.G (t : Term) : FI :=
  match t.fam with
  | .reciprocal => oneG t.anchor
  | _ => halfG t.anchor

def Term.W (t : Term) : FI :=
  match t.fam with
  | .reciprocal => oneW t.anchor
  | _ => halfW t.anchor

/-- A lower bound, at scale `S` and at least `0`, of `1 + cos 2π n·f` on the box. -/
def phaseLoS (bx : Cell) (t : Term) : ℤ :=
  let v : FI := (FI.smul t.a (cx bx 5)).add ((FI.smul t.b (cx bx 6)).add (FI.smul t.c (cx bx 7)))
  max 0 (Sz + (cosRange v.lo v.hi).lo)

/-- The multiplier `μ` at scale `S`. -/
def Term.mu (bx : Cell) (t : Term) : ℤ :=
  match t.fam with
  | .cross => Sz
  | .period => 2 * Sz
  | .reciprocal => 2 * phaseLoS bx t

/-! ### The evaluator -/

structure Acc where
  kLo : ℤ
  kHi : ℤ
  aLo : ℤ
  ok : Bool
  ws : List WTerm

def Term.kLo (bx : Cell) (t : Term) : ℤ := t.mu bx * t.G.lo / Sz
def Term.kHi (bx : Cell) (t : Term) : ℤ := cdivZ (t.mu bx * t.G.hi) Sz
def Term.aLo (bx : Cell) (t : Term) : ℤ := t.mu bx * t.W.lo * (t.anchor : ℤ) / (Sz * (RA : ℤ))
def Term.ok (t : Term) : Bool := t.valid && anchorGuard t.anchor && decide (0 < t.G.lo) && decide (0 < t.W.lo)
def Term.wterm (bx : Cell) (t : Term) : WTerm :=
  ⟨t.fam, t.a, t.b, t.c, cdivZ (t.mu bx * t.W.hi * (piHiN : ℤ)) (Sz * Sz)⟩

def Acc.step (bx : Cell) (acc : Acc) (t : Term) : Acc :=
  ⟨acc.kLo + t.kLo bx, acc.kHi + t.kHi bx, acc.aLo + t.aLo bx, acc.ok && t.ok, t.wterm bx :: acc.ws⟩

def Acc.init : Acc := ⟨0, 0, 0, true, []⟩

/-- A lower bound, at scale `S`, of `e^{x/S}`. -/
def expLower (x : ℤ) : ℤ :=
  if 0 ≤ x then (if x.toNat ≤ S64 then ((expPosPt x.toNat).1 : ℤ) else Sz)
  else (expNegPt (-x).toNat).lo

/-- Box guards: positive diagonals, positive radial endpoints (`toIBox` already requires
exact dyadic endpoints), and `|x| ≤ 1/2`, which the reduction cuts use (`cutR_nonneg`); the
Adaptive chart has `x ∈ [0, 1/2]`, so the last guard never rejects an Adaptive box. -/
def boxGuard (bx : Cell) (B : IBox) : Bool :=
  diagonalsCheck bx && decide (0 < B.l0 ∧ 0 < B.h0 ∧ 0 < B.l1 ∧ 0 < B.h1) &&
    decide (-1/2 ≤ bx.lo 2 ∧ bx.hi 2 ≤ 1/2)

def cutGuard (c : Option Cut) : Bool :=
  match c with
  | none => true
  | some cc => decide (0 ≤ cc.lam)

/-- The certified lower bound of `h₂ · S`, if the guards hold. -/
def supportValue (bx : Cell) (ts : List Term) (c : Option Cut) : Option ℤ :=
  match toIBox bx with
  | none => none
  | some B =>
    let acc := ts.foldl (Acc.step bx) Acc.init
    let U := cornerMaxF B (momOf acc.ws) c
    let sLo := acc.aLo - U
    let K' := if 0 ≤ sLo then acc.kHi else acc.kLo
    let E := expLower (sLo * Sz / K')
    if boxGuard bx B && cutGuard c && increasing ts && acc.ok && decide (0 < acc.kLo) &&
        decide (acc.kLo ≤ acc.kHi) then
      some (acc.kLo * E / Sz)
    else none

/-- **The support check.** -/
def supportCheck (bx : Cell) (ts : List Term) (c : Option Cut) : Bool :=
  match supportValue bx ts c with
  | some L => decide (fccHZ < L)
  | none => false

/-! ### Soundness: accumulator -/

theorem foldl_step (bx : Cell) (ts : List Term) (acc : Acc) :
    (ts.foldl (Acc.step bx) acc).kLo = acc.kLo + (ts.map (Term.kLo bx)).sum ∧
    (ts.foldl (Acc.step bx) acc).kHi = acc.kHi + (ts.map (Term.kHi bx)).sum ∧
    (ts.foldl (Acc.step bx) acc).aLo = acc.aLo + (ts.map (Term.aLo bx)).sum ∧
    (ts.foldl (Acc.step bx) acc).ok = (acc.ok && ts.all Term.ok) ∧
    (ts.foldl (Acc.step bx) acc).ws = (ts.map (Term.wterm bx)).reverse ++ acc.ws := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (acc.step bx t)
    simp only [List.foldl_cons, Acc.step] at h1 h2 h3 h4 h5 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1]; simp; ring
    · rw [h2]; simp; ring
    · rw [h3]; simp; ring
    · rw [h4]; simp [Bool.and_assoc]
    · rw [h5]; simp

/-! ### Soundness: modes -/

theorem increasing_pairwise : ∀ ts : List Term, increasing ts = true →
    ts.Pairwise (fun t u => t.key < u.key)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | t :: u :: rest, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := increasing_pairwise (u :: rest) h.2
    refine List.Pairwise.cons (fun v hv => ?_) ih
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hv)

def keyM (m : Mode) : ℤ := famCode m.family * 125 + (m.index 0 + 2) * 25 + (m.index 1 + 2) * 5 + (m.index 2 + 2)

theorem key_eq (t : Term) : t.key = keyM t.mode := by
  simp [Term.key, keyM, Term.mode]

theorem modes_nodup {ts : List Term} (h : increasing ts = true) : (ts.map Term.mode).Nodup := by
  have p := increasing_pairwise ts h
  have pk : (ts.map Term.key).Pairwise (· < ·) := List.pairwise_map.mpr p
  have nk : (ts.map Term.key).Nodup := pk.nodup
  have e : ts.map Term.key = (ts.map Term.mode).map keyM := by
    rw [List.map_map]
    exact List.map_congr_left (fun t _ => key_eq t)
  rw [e] at nk
  exact nk.of_map keyM

theorem term_valid {t : Term} (h : t.valid = true) : t.mode.valid := by
  simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨a0, a1, b0, b1, c0, c1⟩, fam⟩ := h
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [Term.mode] <;> omega
  · cases hf : t.fam with
    | cross => exact Or.inl hf
    | period =>
      rw [hf] at fam
      right
      simpa [Term.mode, lexPositive] using fam
    | reciprocal =>
      rw [hf] at fam
      right
      simpa [Term.mode, lexPositive] using fam

/-! ### Soundness: one term -/

theorem kernel_half_eq (x : ℝ) : kernelValue .half x = gKernel (1/2) x := by
  norm_num [kernelValue, KernelKind.power]

theorem kernel_one_eq (x : ℝ) : kernelValue .one x = gKernel 1 x := by
  norm_num [kernelValue, KernelKind.power]

/-- The kernel kind of a family. -/
def famKind : Stage2.Family → KernelKind
  | .reciprocal => .one
  | _ => .half

/-- A retained series term is at least `μ` times its kernel at `π q`; `π q > 0`. -/
theorem mode_term_lower (bx : Cell) (hd : diagonalsCheck bx = true) (m : Mode) (hm : m.valid)
    (p : Chart) (hp : bx.Mem p) (hv : (chartPoint p).Valid) (μ : ℝ) (_hμ : 0 ≤ μ)
    (hμv : (m.family = .cross → μ ≤ 1) ∧ (m.family = .period → μ ≤ 2) ∧
      (m.family = .reciprocal → μ ≤ 2 * phaseFactor (chartPoint p) m.index)) :
    0 < Real.pi * m.radial (squarePoint p) ∧
      μ * kernelValue (famKind m.family) (Real.pi * m.radial (squarePoint p)) ≤ m.term (chartPoint p) := by
  cases m with
  | mk fam idx =>
    cases fam with
    | cross =>
      have pos := cross_distance_positive hv idx
      have radial : (Mode.mk .cross idx).radial (squarePoint p) =
          quad (gram (chartBasis p)) (chartVector p true idx) := by
        simp only [Mode.radial]; exact squaredRadial_eq p true _
      have term : (Mode.mk .cross idx).term (chartPoint p) =
          gKernel (1/2) (Real.pi * quad (gram (chartBasis p)) (chartVector p true idx)) := by
        simp only [Mode.term]; rfl
      rw [radial, term]
      have arg := mul_pos Real.pi_pos pos
      refine ⟨arg, ?_⟩
      have k0 := value_nonnegative .half arg
      show μ * kernelValue .half _ ≤ _
      rw [kernel_half_eq] at k0 ⊢
      nlinarith [hμv.1 rfl]
    | period =>
      have lex : lexPositive idx := hm.2.resolve_left (by simp)
      have pos := period_distance_positive hv idx lex
      have radial : (Mode.mk .period idx).radial (squarePoint p) =
          quad (gram (chartBasis p)) (chartVector p false idx) := by
        simp only [Mode.radial]; exact squaredRadial_eq p false _
      have term : (Mode.mk .period idx).term (chartPoint p) =
          2 * gKernel (1/2) (Real.pi * quad (gram (chartBasis p)) (chartVector p false idx)) := by
        simp only [Mode.term]
        rw [seriesDirectTerm, ite_eq_right (lex_ne lex)]
        rfl
      rw [radial, term]
      have arg := mul_pos Real.pi_pos pos
      refine ⟨arg, ?_⟩
      have k0 := value_nonnegative .half arg
      show μ * kernelValue .half _ ≤ _
      rw [kernel_half_eq] at k0 ⊢
      nlinarith [hμv.2.1 rfl]
    | reciprocal =>
      have lex : lexPositive idx := hm.2.resolve_left (by simp)
      have pos := reciprocalPositive hv (lex_ne lex)
      obtain ⟨h0, h1⟩ := radialLoPos bx hd
      have d0 := h0.trans_le (hp 0).1
      have d1 := h1.trans_le (hp 1).1
      have radial : (Mode.mk .reciprocal idx).radial (squarePoint p) =
          quad (gram (chartPoint p).basis)⁻¹ (castVec idx) := by
        simp only [Mode.radial]
        exact dualRadial_eq _ p d0.ne' d1.ne'
      have base : seriesReciprocalTerm (chartPoint p) idx =
          gKernel 1 (Real.pi * quad (gram (chartPoint p).basis)⁻¹ (castVec idx)) := by
        rw [seriesReciprocalTerm, ite_eq_right (lex_ne lex)]
      have term : (Mode.mk .reciprocal idx).term (chartPoint p) =
          2 * (phaseFactor (chartPoint p) idx * seriesReciprocalTerm (chartPoint p) idx) := by
        simp only [Mode.term]
        rw [pairedTerm_eq]
        rfl
      rw [radial, term, base]
      have arg := mul_pos Real.pi_pos pos
      refine ⟨arg, ?_⟩
      have k0 := value_nonnegative .one arg
      show μ * kernelValue .one _ ≤ _
      rw [kernel_one_eq] at k0 ⊢
      have hb := hμv.2.2 rfl
      nlinarith [mul_le_mul_of_nonneg_right hb k0]


/-! ### Soundness: phase floors, exponentials, cuts, constants -/

theorem phaseLoS_sound (bx : Cell) (t : Term) {p : Chart} (hp : bx.Mem p) :
    0 ≤ (phaseLoS bx t : ℝ) ∧ (phaseLoS bx t : ℝ) / Sz ≤ phaseFactor (chartPoint p) t.mode.index := by
  have sp := Sz_pos
  set v : FI := (FI.smul t.a (cx bx 5)).add ((FI.smul t.b (cx bx 6)).add (FI.smul t.c (cx bx 7))) with hv
  have dotv : dot (castVec t.mode.index) (chartPoint p).offset = (t.a : ℝ) * p 5 + ((t.b : ℝ) * p 6 + (t.c : ℝ) * p 7) := by
    simp [dot, Fin.sum_univ_three, castVec, Term.mode, chartPoint]
    ring
  have vm : v.Mem (dot (castVec t.mode.index) (chartPoint p).offset) := by
    rw [dotv, hv]
    exact FI.add_mem (FI.smul_mem _ (cx_mem hp 5))
      (FI.add_mem (FI.smul_mem _ (cx_mem hp 6)) (FI.smul_mem _ (cx_mem hp 7)))
  have cm := cosRange_mem (A := v.lo) (B := v.hi) vm
  have c1 := Real.neg_one_le_cos (2 * Real.pi * dot (castVec t.mode.index) (chartPoint p).offset)
  unfold phaseLoS
  rw [← hv]
  refine ⟨by exact_mod_cast le_max_left (0:ℤ) _, ?_⟩
  unfold phaseFactor
  rcases le_total (Sz + (cosRange v.lo v.hi).lo) 0 with h | h
  · rw [max_eq_left h]
    simp
    linarith
  · rw [max_eq_right h]
    push_cast
    rw [add_div, div_self sp.ne']
    linarith [cm.1]

theorem expLower_le (x : ℤ) : (expLower x : ℝ) / Sz ≤ Real.exp ((x : ℝ) / Sz) := by
  have sp := Sz_pos
  unfold expLower
  split_ifs with h0 h1
  · have hx : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0
    have m := (expPosPt_mem x.toNat h1).1
    rw [hx] at m
    push_cast
    rw [div_le_iff₀ sp]
    exact m
  · rw [div_self sp.ne']
    exact Real.one_le_exp (div_nonneg (by exact_mod_cast h0) sp.le)
  · have hneg : (((-x).toNat : ℕ) : ℝ) = -(x : ℝ) := by
      have nn : 0 ≤ -x := by omega
      have h1 : (((-x).toNat : ℕ) : ℤ) = -x := Int.toNat_of_nonneg nn
      have h2 : (((-x).toNat : ℕ) : ℝ) = ((((-x).toNat : ℕ) : ℤ) : ℝ) := by norm_cast
      rw [h2, h1]
      push_cast
      ring
    have m := (expNegPt_mem (-x).toNat).1
    rw [hneg] at m
    simpa [neg_div, neg_neg] using m

theorem cutR_nonneg (c : Option Cut) (hc : cutGuard c = true) (p : Chart) (hred : reductionInequalities p)
    (hx : (p 2) ^ 2 ≤ 1 / 4) : 0 ≤ cutR c (squarePoint p) := by
  cases c with
  | none => simp [cutR]
  | some cc =>
    have lam : (0:ℝ) ≤ cc.lam := by
      have : 0 ≤ cc.lam := by simpa [cutGuard] using hc
      exact_mod_cast this
    have n010 : (![0, 1, 0] : IntVec) ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
    have base := hred.1 ![0, 1, 0] n010
    have col : sq ((chartBasis p).mulVec (castVec ![0, 1, 0])) = (p 0 * p 2) ^ 2 + (p 1) ^ 2 := by
      simp [sq, chartBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three, castVec]
    rw [col] at base
    have s0 : squarePoint p 0 = (p 0) ^ 2 := by simp [squarePoint]
    have s1 : squarePoint p 1 = (p 1) ^ 2 := by simp [squarePoint]
    have s2 : squarePoint p 2 = p 2 := by simp [squarePoint]
    unfold cutR
    rw [s0, s1, s2]
    apply mul_nonneg lam
    split_ifs
    · nlinarith
    · nlinarith [sq_nonneg (p 0)]

theorem scaleOK : cubeRootCheck scaleWitness scaleInput = true := by decide +kernel

theorem fccHZ_ge : fccHUpper ≤ (fccHZ : ℚ) / S := by decide +kernel

/-! ### Jensen's inequality over a list -/

theorem jensen_list (l : List (ℝ × ℝ)) (c0 : ∀ z ∈ l, 0 ≤ z.1) (C0 : 0 < (l.map Prod.fst).sum) :
    (l.map Prod.fst).sum * Real.exp ((l.map fun z => z.1 * z.2).sum / (l.map Prod.fst).sum) ≤
      (l.map fun z => z.1 * Real.exp z.2).sum := by
  set C := (l.map Prod.fst).sum
  set X := (l.map fun z => z.1 * z.2).sum
  set m := X / C
  have term : ∀ z ∈ l, z.1 * (Real.exp m * (z.2 - m + 1)) ≤ z.1 * Real.exp z.2 := by
    intro z hz
    apply mul_le_mul_of_nonneg_left _ (c0 z hz)
    calc Real.exp m * (z.2 - m + 1) ≤ Real.exp m * Real.exp (z.2 - m) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (z.2 - m)]) (Real.exp_pos m).le
      _ = Real.exp z.2 := by rw [← Real.exp_add]; ring_nf
  have total := List.sum_le_sum term
  have expand : ∀ l' : List (ℝ × ℝ), (l'.map fun z => z.1 * (Real.exp m * (z.2 - m + 1))).sum =
      Real.exp m * (l'.map fun z => z.1 * z.2).sum + Real.exp m * (1 - m) * (l'.map Prod.fst).sum := by
    intro l'
    induction l' with
    | nil => simp
    | cons z rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [expand l] at total
  have mC : m * C = X := by simp only [m]; field_simp
  calc C * Real.exp m = Real.exp m * X + Real.exp m * (1 - m) * C := by rw [← mC]; ring
    _ ≤ _ := total

/-! ### Soundness: one term in fixed point -/

theorem mu_sound (bx : Cell) (t : Term) {p : Chart} (hp : bx.Mem p) :
    0 ≤ (t.mu bx : ℝ) / Sz ∧
      (t.mode.family = .cross → (t.mu bx : ℝ) / Sz ≤ 1) ∧
      (t.mode.family = .period → (t.mu bx : ℝ) / Sz ≤ 2) ∧
      (t.mode.family = .reciprocal → (t.mu bx : ℝ) / Sz ≤ 2 * phaseFactor (chartPoint p) t.mode.index) := by
  have sp := Sz_pos
  have ph := phaseLoS_sound bx t hp
  simp only [Term.mode]
  cases hf : t.fam with
  | cross =>
    simp only [Term.mu, hf, div_self sp.ne']
    refine ⟨zero_le_one, fun _ => le_rfl, fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  | period =>
    simp only [Term.mu, hf]
    push_cast
    rw [mul_div_assoc, div_self sp.ne']
    refine ⟨by norm_num, fun h => absurd h (by simp), fun _ => by norm_num, fun h => absurd h (by simp)⟩
  | reciprocal =>
    simp only [Term.mu, hf]
    push_cast
    rw [mul_div_assoc]
    refine ⟨by have := ph.1; positivity, fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun _ => by simpa [Term.mode] using mul_le_mul_of_nonneg_left ph.2 (by norm_num : (0:ℝ) ≤ 2)⟩

theorem famKind_power (f : Stage2.Family) :
    ((famKind f).power : ℝ) = if f = .reciprocal then 1 else 1 / 2 := by
  cases f <;> norm_num [famKind, KernelKind.power]

/-- The kernel enclosures of a term that passes its checks. -/
theorem term_kernels (t : Term) (hok : t.ok = true) :
    0 < (t.anchor : ℝ) / RA ∧
    (t.G).Mem (kernelValue (famKind t.fam) ((t.anchor : ℝ) / RA)) ∧
    (t.W).Mem ((Real.exp (-((t.anchor : ℝ) / RA)) + ((famKind t.fam).power : ℝ) *
      kernelValue (famKind t.fam) ((t.anchor : ℝ) / RA)) / ((t.anchor : ℝ) / RA)) ∧
    0 < t.G.lo ∧ 0 < t.W.lo := by
  simp only [Term.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨_, guard⟩, g0⟩, w0⟩ := hok
  simp only [anchorGuard, Bool.and_eq_true, decide_eq_true_eq] at guard
  obtain ⟨a0, a1⟩ := guard
  have Tpos : 0 < (t.anchor : ℝ) / RA := div_pos (by exact_mod_cast a0) RA_pos
  refine ⟨Tpos, ?_, ?_, g0, w0⟩
  · cases hf : t.fam with
    | reciprocal =>
      simp only [Term.G, hf, famKind, kernel_one_eq]
      exact oneG_mem a0
    | cross =>
      simp only [Term.G, hf, famKind, kernel_half_eq]
      exact halfG_mem a0 a1
    | period =>
      simp only [Term.G, hf, famKind, kernel_half_eq]
      exact halfG_mem a0 a1
  · cases hf : t.fam with
    | reciprocal =>
      simp only [Term.W, hf, famKind, kernel_one_eq, KernelKind.power, Rat.cast_one, one_mul]
      exact oneW_mem a0
    | cross =>
      simp only [Term.W, hf, famKind, kernel_half_eq, KernelKind.power]
      have e : (((1 / 2 : ℚ)) : ℝ) * gKernel (1/2) ((t.anchor : ℝ) / RA) =
          gKernel (1/2) ((t.anchor : ℝ) / RA) / 2 := by push_cast; ring
      rw [e]
      exact halfW_mem a0 a1
    | period =>
      simp only [Term.W, hf, famKind, kernel_half_eq, KernelKind.power]
      have e : (((1 / 2 : ℚ)) : ℝ) * gKernel (1/2) ((t.anchor : ℝ) / RA) =
          gKernel (1/2) ((t.anchor : ℝ) / RA) / 2 := by push_cast; ring
      rw [e]
      exact halfW_mem a0 a1


/-! ### Soundness: per-term real quantities -/

def tT (t : Term) : ℝ := (t.anchor : ℝ) / RA
def tG (t : Term) : ℝ := kernelValue (famKind t.fam) (tT t)
def tW (t : Term) : ℝ := (Real.exp (-(tT t)) + ((famKind t.fam).power : ℝ) * tG t) / tT t
def tMu (bx : Cell) (t : Term) : ℝ := (t.mu bx : ℝ) / Sz
def tR (p : Chart) (t : Term) : ℝ := t.mode.radial (squarePoint p)
def tC (bx : Cell) (t : Term) : ℝ := tMu bx t * tG t
def tX (p : Chart) (t : Term) : ℝ := -(Real.pi * tR p t - tT t) * (tW t / tG t)

theorem cdivZ_nonneg {n d : ℤ} (hn : 0 ≤ n) (hd : 0 < d) : 0 ≤ cdivZ n d := by
  have h := le_cdiv n d hd
  have : (0:ℝ) ≤ (n : ℝ) / d := div_nonneg (by exact_mod_cast hn) (by exact_mod_cast hd.le)
  exact_mod_cast this.trans h

theorem per_term (bx : Cell) (hd : diagonalsCheck bx = true) (t : Term) (hok : t.ok = true) {p : Chart}
    (hp : bx.Mem p) (hv : (chartPoint p).Valid) :
    0 ≤ tMu bx t ∧ 0 < tG t ∧ 0 < tT t ∧ 0 < tR p t ∧
    tC bx t * Real.exp (tX p t) ≤ t.mode.term (chartPoint p) ∧
    (t.kLo bx : ℝ) / Sz ≤ tC bx t ∧ tC bx t ≤ (t.kHi bx : ℝ) / Sz ∧
    (t.aLo bx : ℝ) / Sz ≤ tMu bx t * tW t * tT t ∧
    Real.pi * tMu bx t * tW t ≤ ((t.wterm bx).w : ℝ) / Sz ∧ 0 ≤ (t.wterm bx).w ∧
    tC bx t * tX p t = tMu bx t * tW t * tT t - Real.pi * tMu bx t * tW t * tR p t := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  obtain ⟨Tpos, Gm, Wm, G0, W0⟩ := term_kernels t hok
  have valid : t.mode.valid := term_valid (by
    simp only [Term.ok, Bool.and_eq_true] at hok; exact hok.1.1.1)
  obtain ⟨mu0, muC, muP, muR⟩ := mu_sound bx t hp
  have muv : (t.mode.family = .cross → tMu bx t ≤ 1) ∧ (t.mode.family = .period → tMu bx t ≤ 2) ∧
      (t.mode.family = .reciprocal → tMu bx t ≤ 2 * phaseFactor (chartPoint p) t.mode.index) :=
    ⟨muC, muP, muR⟩
  obtain ⟨argPos, termLow⟩ := mode_term_lower bx hd t.mode valid p hp hv (tMu bx t) mu0 muv
  have famEq : t.mode.family = t.fam := rfl
  rw [famEq] at termLow
  have Glo : (t.G.lo : ℝ) / Sz ≤ tG t := Gm.1
  have Ghi : tG t ≤ (t.G.hi : ℝ) / Sz := Gm.2
  have Wlo : (t.W.lo : ℝ) / Sz ≤ tW t := Wm.1
  have Whi : tW t ≤ (t.W.hi : ℝ) / Sz := Wm.2
  have Gpos : 0 < tG t := lt_of_lt_of_le (div_pos (by exact_mod_cast G0) sp) Glo
  have Wpos : 0 < tW t := lt_of_lt_of_le (div_pos (by exact_mod_cast W0) sp) Wlo
  have rpos : 0 < tR p t := by
    have := argPos
    unfold tR
    nlinarith [Real.pi_pos]
  -- the log-convex tangent
  have lt := logTangent (famKind t.fam) Tpos argPos
  have rate : (Real.exp (-(tT t)) + ((famKind t.fam).power : ℝ) * kernelValue (famKind t.fam) (tT t)) /
      (tT t * kernelValue (famKind t.fam) (tT t)) = tW t / tG t := by
    unfold tW tG
    field_simp
  have lt' : tG t * Real.exp (tX p t) ≤ kernelValue (famKind t.fam) (Real.pi * tR p t) := by
    unfold tX
    rw [← rate]
    exact lt
  refine ⟨mu0, Gpos, Tpos, rpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc tC bx t * Real.exp (tX p t) = tMu bx t * (tG t * Real.exp (tX p t)) := by unfold tC; ring
      _ ≤ tMu bx t * kernelValue (famKind t.fam) (Real.pi * tR p t) := mul_le_mul_of_nonneg_left lt' mu0
      _ ≤ _ := termLow
  · -- floor of μ G.lo / S
    have f := fdiv_le (t.mu bx * t.G.lo) Sz spZ
    unfold Term.kLo tC tMu
    rw [div_le_iff₀ sp]
    calc ((t.mu bx * t.G.lo / Sz : ℤ) : ℝ) ≤ ((t.mu bx * t.G.lo : ℤ) : ℝ) / Sz := f
      _ = (t.mu bx : ℝ) / Sz * ((t.G.lo : ℝ) / Sz) * Sz := by push_cast; field_simp
      _ ≤ (t.mu bx : ℝ) / Sz * tG t * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          exact mul_le_mul_of_nonneg_left Glo mu0
  · have f := le_cdiv (t.mu bx * t.G.hi) Sz spZ
    unfold Term.kHi tC tMu
    rw [le_div_iff₀ sp]
    calc (t.mu bx : ℝ) / Sz * tG t * Sz ≤ (t.mu bx : ℝ) / Sz * ((t.G.hi : ℝ) / Sz) * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          exact mul_le_mul_of_nonneg_left Ghi mu0
      _ = ((t.mu bx * t.G.hi : ℤ) : ℝ) / Sz := by push_cast; field_simp
      _ ≤ _ := f
  · have dpos : (0:ℤ) < Sz * (RA : ℤ) := mul_pos spZ (by norm_num [RA])
    have f := fdiv_le (t.mu bx * t.W.lo * (t.anchor : ℤ)) (Sz * (RA : ℤ)) dpos
    unfold Term.aLo tMu tT
    rw [div_le_iff₀ sp]
    have Tn : (0:ℝ) ≤ (t.anchor : ℝ) / RA := Tpos.le
    calc ((t.mu bx * t.W.lo * (t.anchor : ℤ) / (Sz * (RA : ℤ)) : ℤ) : ℝ)
        ≤ ((t.mu bx * t.W.lo * (t.anchor : ℤ) : ℤ) : ℝ) / ((Sz * (RA : ℤ) : ℤ) : ℝ) := f
      _ = (t.mu bx : ℝ) / Sz * ((t.W.lo : ℝ) / Sz) * ((t.anchor : ℝ) / RA) * Sz := by
          push_cast; field_simp [RA_pos.ne']
      _ ≤ (t.mu bx : ℝ) / Sz * tW t * ((t.anchor : ℝ) / RA) * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          apply mul_le_mul_of_nonneg_right _ Tn
          exact mul_le_mul_of_nonneg_left Wlo mu0
  · have dpos : (0:ℤ) < Sz * Sz := mul_pos spZ spZ
    have f := le_cdiv (t.mu bx * t.W.hi * (piHiN : ℤ)) (Sz * Sz) dpos
    have ph := pi_bounds.2
    rw [S_eq] at ph
    unfold Term.wterm tMu
    simp only
    rw [le_div_iff₀ sp]
    have Whn : 0 ≤ (t.W.hi : ℝ) / Sz := Wpos.le.trans Whi
    calc Real.pi * ((t.mu bx : ℝ) / Sz) * tW t * Sz
        ≤ ((piHiN : ℝ) / Sz) * ((t.mu bx : ℝ) / Sz) * ((t.W.hi : ℝ) / Sz) * Sz := by
          apply mul_le_mul_of_nonneg_right _ sp.le
          apply mul_le_mul (mul_le_mul_of_nonneg_right ph mu0) Whi Wpos.le
          exact mul_nonneg ((Real.pi_pos.le).trans ph) mu0
      _ = ((t.mu bx * t.W.hi * (piHiN : ℤ) : ℤ) : ℝ) / ((Sz * Sz : ℤ) : ℝ) := by
          push_cast; field_simp
      _ ≤ _ := f
  · unfold Term.wterm
    simp only
    apply cdivZ_nonneg _ (mul_pos spZ spZ)
    have m0 : 0 ≤ t.mu bx := by
      have := mu0
      have h2 : (0:ℝ) ≤ (t.mu bx : ℝ) := by
        have := mul_nonneg this sp.le
        rwa [div_mul_cancel₀ _ sp.ne'] at this
      exact_mod_cast h2
    have wh : 0 ≤ t.W.hi := by
      have : (0:ℝ) ≤ (t.W.hi : ℝ) / Sz := Wpos.le.trans Whi
      have h2 : (0:ℝ) ≤ (t.W.hi : ℝ) := by
        have := mul_nonneg this sp.le
        rwa [div_mul_cancel₀ _ sp.ne'] at this
      exact_mod_cast h2
    positivity
  · unfold tC tX
    field_simp
    ring

/-! ### The main theorem -/

theorem lsum_div (l : List Term) (f : Term → ℝ) (d : ℝ) :
    (l.map f).sum / d = (l.map fun t => f t / d).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

theorem lsum_mul (l : List Term) (f : Term → ℝ) (r : ℝ) :
    r * (l.map f).sum = (l.map fun t => r * f t).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

theorem lsum_sub (l : List Term) (f g : Term → ℝ) :
    (l.map fun t => f t - g t).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_cast_int (l : List Term) (f : Term → ℤ) :
    (((l.map f).sum : ℤ) : ℝ) = (l.map fun t => (f t : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => simp [ih]

theorem sum_le_map {l : List Term} {f g : Term → ℝ} (h : ∀ t ∈ l, f t ≤ g t) :
    (l.map f).sum ≤ (l.map g).sum := List.sum_le_sum h

/-- **The Jensen bound of an accepted evaluation.** If `supportValue` returns `L`, then at
every `good` point of the box `L / S` is at most the sum of the tangent minorants
`Σ μ G(T) e^{X}` of the terms; the guards it checked are returned too. -/
theorem supportValue_sound (bx : Cell) (ts : List Term) (c : Option Cut) (L : ℤ)
    (hL : supportValue bx ts c = some L) (p : Chart) (hp : bx.Mem p) (gp : good p) :
    diagonalsCheck bx = true ∧ increasing ts = true ∧ (∀ t ∈ ts, t.ok = true) ∧
      (∃ B, toIBox bx = some B ∧ ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0) ∧
      (L : ℝ) / Sz ≤ (ts.map fun t => tC bx t * Real.exp (tX p t)).sum := by
  have sp := Sz_pos
  have spZ := Sz_posZ
  unfold supportValue at hL
  cases hB : toIBox bx with
  | none => rw [hB] at hL; simp at hL
  | some B =>
    rw [hB] at hL
    simp only at hL
    set acc := ts.foldl (Acc.step bx) Acc.init with hacc
    set U := cornerMaxF B (momOf acc.ws) c with hU
    set sLo := acc.aLo - U with hsLo
    set K' := (if 0 ≤ sLo then acc.kHi else acc.kLo) with hK'
    set x' := sLo * Sz / K' with hx'
    split_ifs at hL with guards
    have hLe : acc.kLo * expLower x' / Sz = L := Option.some.inj hL
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guards
    obtain ⟨⟨⟨⟨⟨bg, cg⟩, inc⟩, accOk⟩, kpos⟩, kle⟩ := guards
    simp only [boxGuard, Bool.and_eq_true, decide_eq_true_eq] at bg
    obtain ⟨⟨hd, ⟨l0, h0, l1, h1⟩⟩, ⟨xlo, xhi⟩⟩ := bg
    have fk1 : acc.kLo = (ts.map (Term.kLo bx)).sum := by
      rw [hacc, (foldl_step bx ts Acc.init).1]; simp [Acc.init]
    have fk2 : acc.kHi = (ts.map (Term.kHi bx)).sum := by
      rw [hacc, (foldl_step bx ts Acc.init).2.1]; simp [Acc.init]
    have fa : acc.aLo = (ts.map (Term.aLo bx)).sum := by
      rw [hacc, (foldl_step bx ts Acc.init).2.2.1]; simp [Acc.init]
    have fok : acc.ok = ts.all Term.ok := by
      rw [hacc, (foldl_step bx ts Acc.init).2.2.2.1]; simp [Acc.init]
    have fws : acc.ws = (ts.map (Term.wterm bx)).reverse := by
      rw [hacc, (foldl_step bx ts Acc.init).2.2.2.2]; simp [Acc.init]
    have allOk : ∀ t ∈ ts, t.ok = true := List.all_eq_true.mp (by rw [← fok]; exact accOk)
    have hv := gp.1
    have facts := fun t (ht : t ∈ ts) => per_term bx hd t (allOk t ht) hp hv
    -- Jensen
    set l := ts.map fun t => (tC bx t, tX p t) with hl
    have lC : (l.map Prod.fst).sum = (ts.map (tC bx)).sum := by rw [hl, List.map_map]; rfl
    have lX : (l.map fun z => z.1 * z.2).sum = (ts.map fun t => tC bx t * tX p t).sum := by
      rw [hl, List.map_map]; rfl
    have lE : (l.map fun z => z.1 * Real.exp z.2).sum = (ts.map fun t => tC bx t * Real.exp (tX p t)).sum := by
      rw [hl, List.map_map]; rfl
    -- K bounds
    have Klo : (acc.kLo : ℝ) / Sz ≤ (ts.map (tC bx)).sum := by
      rw [fk1, sum_cast_int, lsum_div]
      exact sum_le_map (fun t ht => (facts t ht).2.2.2.2.2.1)
    have Khi : (ts.map (tC bx)).sum ≤ (acc.kHi : ℝ) / Sz := by
      rw [fk2, sum_cast_int, lsum_div]
      exact sum_le_map (fun t ht => (facts t ht).2.2.2.2.2.2.1)
    have KloPos : (0:ℝ) < (acc.kLo : ℝ) / Sz := div_pos (by exact_mod_cast kpos) sp
    have Cpos : 0 < (ts.map (tC bx)).sum := KloPos.trans_le Klo
    have c0 : ∀ z ∈ l, 0 ≤ z.1 := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      exact mul_nonneg (facts t ht).1 (facts t ht).2.1.le
    have jensen := jensen_list l c0 (by rw [lC]; exact Cpos)
    rw [lC, lX, lE] at jensen
    -- X lower bound
    have Xeq : (ts.map fun t => tC bx t * tX p t).sum =
        (ts.map fun t => tMu bx t * tW t * tT t).sum -
          Real.pi * (ts.map fun t => tMu bx t * tW t * tR p t).sum := by
      rw [lsum_mul, ← lsum_sub]
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [(facts t ht).2.2.2.2.2.2.2.2.2.2]
      ring
    have Alow : (acc.aLo : ℝ) / Sz ≤ (ts.map fun t => tMu bx t * tW t * tT t).sum := by
      rw [fa, sum_cast_int, lsum_div]
      exact sum_le_map (fun t ht => (facts t ht).2.2.2.2.2.2.2.1)
    -- corner bound
    have nn : ∀ w ∈ acc.ws, 0 ≤ w.w := by
      intro w hw
      rw [fws] at hw
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hw)
      exact (facts t ht).2.2.2.2.2.2.2.2.2.1
    have hc : ∀ cc, c = some cc → 0 ≤ cc.lam := by
      intro cc e
      subst e
      simpa [cutGuard] using cg
    have pos : ∀ bits, B.at bits 0 ≠ 0 ∧ B.at bits 1 ≠ 0 := by
      intro bits
      constructor
      · unfold IBox.at IBox.lo IBox.hi; split_ifs <;> simp <;> omega
      · unfold IBox.at IBox.lo IBox.hi; split_ifs <;> simp <;> omega
    have corner := cornerMax_sound hB hd acc.ws nn c hc pos p hp
    rw [← cornerMaxF_eq] at corner
    have p2 : (p 2) ^ 2 ≤ 1 / 4 := by
      have lo2 := (hp 2).1
      have hi2 := (hp 2).2
      have a : (((-1/2 : ℚ)) : ℝ) ≤ ((bx.lo 2 : ℚ) : ℝ) := Rat.cast_le.mpr xlo
      have b : ((bx.hi 2 : ℚ) : ℝ) ≤ (((1/2 : ℚ)) : ℝ) := Rat.cast_le.mpr xhi
      push_cast at a b
      nlinarith
    have cutNN := cutR_nonneg c cg p gp.2.1 p2
    have wsSum : (acc.ws.map fun w => (w.w : ℝ) * w.mode.radial (squarePoint p)).sum =
        (ts.map fun t => ((t.wterm bx).w : ℝ) * tR p t).sum := by
      rw [fws, List.map_reverse, List.sum_reverse, List.map_map]
      rfl
    rw [wsSum] at corner
    have wsBound : Real.pi * (ts.map fun t => tMu bx t * tW t * tR p t).sum ≤ (U : ℝ) / Sz := by
      rw [lsum_mul]
      have step : (ts.map fun t => Real.pi * (tMu bx t * tW t * tR p t)).sum ≤
          (ts.map fun t => ((t.wterm bx).w : ℝ) * tR p t).sum / Sz := by
        rw [lsum_div]
        apply sum_le_map
        intro t ht
        have f := facts t ht
        have r0 := f.2.2.2.1.le
        calc Real.pi * (tMu bx t * tW t * tR p t) = (Real.pi * tMu bx t * tW t) * tR p t := by ring
          _ ≤ (((t.wterm bx).w : ℝ) / Sz) * tR p t := mul_le_mul_of_nonneg_right f.2.2.2.2.2.2.2.2.1 r0
          _ = ((t.wterm bx).w : ℝ) * tR p t / Sz := by ring
      refine step.trans ?_
      apply div_le_div_of_nonneg_right _ sp.le
      linarith
    have Xlow : (sLo : ℝ) / Sz ≤ (ts.map fun t => tC bx t * tX p t).sum := by
      rw [Xeq, hsLo]
      push_cast
      rw [sub_div]
      linarith
    -- kexp_lower and the exponential
    have kexp := kexp_lower Klo Khi KloPos Xlow
    have Kq : (0:ℤ) < K' := by
      rw [hK']; split_ifs
      · exact kpos.trans_le kle
      · exact kpos
    have ifEq : (if 0 ≤ (sLo : ℝ) / Sz then (acc.kHi : ℝ) / Sz else (acc.kLo : ℝ) / Sz) = (K' : ℝ) / Sz := by
      rw [hK']
      by_cases h : 0 ≤ sLo
      · have : 0 ≤ (sLo : ℝ) / Sz := div_nonneg (by exact_mod_cast h) sp.le
        simp [h, this]
      · have : ¬ 0 ≤ (sLo : ℝ) / Sz := by
          intro h'
          have := (div_nonneg_iff.mp h')
          rcases this with ⟨a, _⟩ | ⟨_, b⟩
          · exact h (by exact_mod_cast a)
          · linarith
        simp [h, this]
    rw [ifEq] at kexp
    have xle : (x' : ℝ) / Sz ≤ ((sLo : ℝ) / Sz) / ((K' : ℝ) / Sz) := by
      have f := fdiv_le (sLo * Sz) K' Kq
      have KR : (0:ℝ) < K' := by exact_mod_cast Kq
      rw [div_le_iff₀ sp]
      calc ((sLo * Sz / K' : ℤ) : ℝ) ≤ ((sLo * Sz : ℤ) : ℝ) / K' := f
        _ = ((sLo : ℝ) / Sz) / ((K' : ℝ) / Sz) * Sz := by push_cast; field_simp
    have expMono := Real.exp_le_exp.mpr xle
    have Elow := expLower_le x'
    have Lle : (L : ℝ) / Sz ≤ ((acc.kLo : ℝ) / Sz) * Real.exp (((sLo : ℝ) / Sz) / ((K' : ℝ) / Sz)) := by
      rw [← hLe]
      have f := fdiv_le (acc.kLo * expLower x') Sz spZ
      have kl0 : (0:ℝ) ≤ (acc.kLo : ℝ) / Sz := KloPos.le
      calc ((acc.kLo * expLower x' / Sz : ℤ) : ℝ) / Sz ≤ ((acc.kLo * expLower x' : ℤ) : ℝ) / Sz / Sz :=
            div_le_div_of_nonneg_right f sp.le
        _ = ((acc.kLo : ℝ) / Sz) * ((expLower x' : ℝ) / Sz) := by push_cast; ring
        _ ≤ ((acc.kLo : ℝ) / Sz) * Real.exp ((x' : ℝ) / Sz) := mul_le_mul_of_nonneg_left Elow kl0
        _ ≤ _ := mul_le_mul_of_nonneg_left expMono kl0
    exact ⟨hd, inc, allOk, ⟨B, rfl, pos⟩, Lle.trans (kexp.trans jensen)⟩

/-- The retained terms of an increasing list sum to at most `h₂`. -/
theorem physical_le (ts : List Term) (inc : increasing ts = true) (allOk : ∀ t ∈ ts, t.ok = true)
    (q : TwoSite) (hv : q.Valid) : (ts.map fun t => t.mode.term q).sum ≤ h₂ q := by
  have nodup := modes_nodup inc
  have hval : ∀ m ∈ (ts.map Term.mode).toFinset, m.valid := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    exact term_valid (by
      have := allOk t ht
      simp only [Term.ok, Bool.and_eq_true] at this
      exact this.1.1.1)
  have h := physical_sum_le _ q hv hval
  rw [List.sum_toFinset _ nodup, List.map_map] at h
  exact h

/-- The FCC comparison at scale `S`. -/
theorem aboveFCC_of_Z {L : ℤ} (strict : fccHZ < L) (p : Chart)
    (bound : (L : ℝ) / Sz ≤ h₂ (chartPoint p)) : energy fcc < energy (chartPoint p) := by
  have strictQ : fccHUpper < (L : ℚ) / S := by
    have e : ((fccHZ : ℤ) : ℚ) / S < (L : ℚ) / S := by
      apply div_lt_div_of_pos_right (by exact_mod_cast strict) (by norm_num [S])
    exact lt_of_le_of_lt fccHZ_ge e
  have boundQ : (((L : ℚ) / S : ℚ) : ℝ) ≤ h₂ (chartPoint p) := by
    have e : (((L : ℚ) / S : ℚ) : ℝ) = (L : ℝ) / Sz := by rw [← S_eq]; push_cast; rfl
    rw [e]; exact bound
  exact aboveFCC_of_lower _ scaleOK _ strictQ boundQ

/-- **Soundness of the support check.** -/
theorem supportCheck_sound (bx : Cell) (ts : List Term) (c : Option Cut) (ok : supportCheck bx ts c = true)
    (p : Chart) (hp : bx.Mem p) (gp : good p) : energy fcc < energy (chartPoint p) := by
  unfold supportCheck at ok
  cases hL : supportValue bx ts c with
  | none => rw [hL] at ok; simp at ok
  | some L =>
    rw [hL] at ok
    have strict : fccHZ < L := of_decide_eq_true ok
    obtain ⟨hd, inc, allOk, -, bound⟩ := supportValue_sound bx ts c L hL p hp gp
    have expSum : (ts.map fun t => tC bx t * Real.exp (tX p t)).sum ≤
        (ts.map fun t => t.mode.term (chartPoint p)).sum :=
      sum_le_map (fun t ht => (per_term bx hd t (allOk t ht) hp gp.1).2.2.2.2.1)
    exact aboveFCC_of_Z strict p (bound.trans (expSum.trans (physical_le ts inc allOk _ gp.1)))

end BccSharp.Coulomb.CompactCover.AdaptiveSupport
