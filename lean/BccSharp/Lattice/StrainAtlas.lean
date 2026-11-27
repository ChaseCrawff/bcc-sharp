import BccSharp.Lattice.StrainLeaf
import BccSharp.Lattice.TangentCover

set_option autoImplicit false

/-! # Strain atlases for `LatticeCase`

A strain atlas is a binary tree of cuts of the strain root box (`ATree`). A leaf is outside
the eligible strains, inside the local product ball, or a tangent leaf: the integer leaf check
`zLeafCheck` of `BccSharp.Lattice.StrainLeaf` on an aggregate of certified tangents.

The tangents come from two tables of integer tangents (`ZTree`), one per kernel: an entry
`(ic, ip)` is the line `ic / 2^96 - (ip / 2^96) q`. An entry is valid when it is the fast
tangent at its anchor (`ZTree.check`) or the copy of an entry of the certified tables of the
tangent cover (`ZTree.mirror`).

The aggregate of a tangent leaf is computed inside the check (`AtlasData.agg`). For every
candidate index `n` of a fixed list (one of `±n`), the squared length at the centre of the box
picks a table position, and `n` and `-n` both enter the aggregate with that tangent. The
soundness proof uses only the validity of the tables and the distinctness of the candidates
(`candsOK`); the choice of positions is free.

`AtlasClosed ref b` says that every eligible strain in `b` is in the local ball or is
strain-sharp. A checked tree closes its box (`ATree.closed`), cuts combine closed boxes
(`closed_cut`), and a closed strain root gives `strainSharp` on every eligible strain
(`sharp_of_closed`). That replaces the `AtlasRows` premise of
`latticeCase_from_tangent_forest` (`latticeCase_from_tangent_forest_closed`). -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.StrainAtlas
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentE1
open BccSharp.Coulomb.BravaisCover.TangentCover
open BccSharp.Coulomb.BravaisCover.StrainTangent
open BccSharp.Coulomb.CompactCover

/-! ## Integer tangent tables -/

/-- The tangent line `ic / 2^96 - (ip / 2^96) q`. -/
def zTangent (ic ip : ℤ) : Stage2.Tangent := ⟨(ic : ℚ) / pwQ 96, (ip : ℚ) / pwQ 96⟩

/-- `t` is the tangent `(ic, ip)`. -/
def tangentIs (t : Stage2.Tangent) (ic ip : ℤ) : Bool :=
  decide (t.intercept = (ic : ℚ) / pwQ 96 ∧ t.penalty = (ip : ℚ) / pwQ 96)

theorem tangentIs_eq {t : Stage2.Tangent} {ic ip : ℤ} (h : tangentIs t ic ip = true) :
    t = zTangent ic ip := by
  have e := of_decide_eq_true h
  cases t
  simp only at e
  obtain ⟨rfl, rfl⟩ := e
  rfl

/-- A binary tree of integer tangents; leaves at depth `h` are indexed from the left. -/
inductive ZTree where
  | tip
  | leaf (anchor : ℚ) (ic ip : ℤ)
  | node (l r : ZTree)

def ZTree.get : ZTree → ℕ → ℕ → Option (ℤ × ℤ)
  | .leaf _ ic ip, 0, _ => some (ic, ip)
  | .node l r, h + 1, k => if k < 2 ^ h then l.get h k else r.get h (k - 2 ^ h)
  | _, _, _ => none

def ZTree.Valid (kind : KernelKind) : ZTree → Prop
  | .tip => True
  | .leaf _ ic ip => ValidTangent kind (zTangent ic ip)
  | .node l r => l.Valid kind ∧ r.Valid kind

theorem ZTree.get_valid (kind : KernelKind) :
    ∀ (t : ZTree), t.Valid kind → ∀ (h k : ℕ) (ic ip : ℤ), t.get h k = some (ic, ip) →
      ValidTangent kind (zTangent ic ip)
  | .tip, _, h, k, ic, ip, hg => by cases h <;> simp [ZTree.get] at hg
  | .leaf _ a b, hv, h, k, ic, ip, hg => by
    cases h with
    | zero =>
      simp only [ZTree.get, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact hv
    | succ h => simp [ZTree.get] at hg
  | .node l r, hv, h, k, ic, ip, hg => by
    cases h with
    | zero => simp [ZTree.get] at hg
    | succ h =>
      simp only [ZTree.get] at hg
      split_ifs at hg
      · exact ZTree.get_valid kind l hv.1 h k ic ip hg
      · exact ZTree.get_valid kind r hv.2 h _ ic ip hg

/-- Every leaf is the fast tangent at its anchor. -/
def ZTree.check (kind : KernelKind) : ZTree → Bool
  | .tip => true
  | .leaf x ic ip => match fastTangent kind x with
    | some u => tangentIs u ic ip
    | none => false
  | .node l r => l.check kind && r.check kind

theorem ZTree.check_valid (kind : KernelKind) : ∀ (t : ZTree), t.check kind = true → t.Valid kind
  | .tip, _ => trivial
  | .leaf x ic ip, h => by
    simp only [ZTree.check] at h
    split at h
    next u hu =>
      have hv := fastTangent_sound kind x u hu
      rw [tangentIs_eq h] at hv
      exact hv
    next => contradiction
  | .node l r, h => by
    simp only [ZTree.check, Bool.and_eq_true] at h
    exact ⟨ZTree.check_valid kind l h.1, ZTree.check_valid kind r h.2⟩

/-- `z` has the shape of `t`, and each leaf of `z` is the tangent of the matching leaf of `t`. -/
def ZTree.mirror : TTree → ZTree → Bool
  | .tip, .tip => true
  | .leaf _ t, .leaf _ ic ip => tangentIs t ic ip
  | .node l r, .node l' r' => ZTree.mirror l l' && ZTree.mirror r r'
  | _, _ => false

theorem ZTree.mirror_valid (kind : KernelKind) :
    ∀ (t : TTree) (z : ZTree), t.Valid kind → ZTree.mirror t z = true → z.Valid kind
  | .tip, .tip, _, _ => trivial
  | .leaf _ t, .leaf _ ic ip, hv, h => by
    have e := tangentIs_eq h
    show ValidTangent kind (zTangent ic ip)
    rw [← e]
    exact hv
  | .node l r, .node l' r', hv, h => by
    simp only [ZTree.mirror, Bool.and_eq_true] at h
    exact ⟨ZTree.mirror_valid kind l l' hv.1 h.1, ZTree.mirror_valid kind r r' hv.2 h.2⟩
  | .tip, .leaf _ _ _, _, h => by simp [ZTree.mirror] at h
  | .tip, .node _ _, _, h => by simp [ZTree.mirror] at h
  | .leaf _ _, .tip, _, h => by simp [ZTree.mirror] at h
  | .leaf _ _, .node _ _, _, h => by simp [ZTree.mirror] at h
  | .node _ _, .tip, _, h => by simp [ZTree.mirror] at h
  | .node _ _, .leaf _ _ _, _, h => by simp [ZTree.mirror] at h

/-- Two tables of integer tangents of height `height`: `.half` for direct and `.one` for dual
indices. -/
structure ZTables where
  height : ℕ
  half : ZTree
  one : ZTree

def ZTables.Valid (T : ZTables) : Prop := T.half.Valid .half ∧ T.one.Valid .one

/-! ## Candidate indices -/

/-- A candidate index `n = (i, j, k)`, standing for `n` and `-n`, with the coefficients
`g0..g5` of `aᵀ M a = g0 M00 + g1 M11 + g2 M22 + g3 M01 + g4 M02 + g5 M12`, where `a` is
twice the frame vector of `n` (`dirFrame2 ref` or `dualFrame2 ref` applied to `n`). They only
choose the anchor. -/
structure Cand where
  i : ℤ
  j : ℤ
  k : ℤ
  g0 : ℤ
  g1 : ℤ
  g2 : ℤ
  g3 : ℤ
  g4 : ℤ
  g5 : ℤ

def Cand.vec (c : Cand) : IntVec := ![c.i, c.j, c.k]
def Cand.nvec (c : Cand) : IntVec := ![-c.i, -c.j, -c.k]

def keyVec (t : ℤ × ℤ × ℤ) : IntVec := ![t.1, t.2.1, t.2.2]

theorem keyVec_injective : Function.Injective keyVec := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [keyVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  rw [h0, h1, h2]

/-- The keys of `n` and `-n` for every candidate. -/
def candKeys (l : List Cand) : List (ℤ × ℤ × ℤ) :=
  l.flatMap fun c => [(c.i, c.j, c.k), (-c.i, -c.j, -c.k)]

def keysDistinct : List (ℤ × ℤ × ℤ) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !decide (y = x)) && keysDistinct xs

theorem keysDistinct_nodup : ∀ (l : List (ℤ × ℤ × ℤ)), keysDistinct l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [keysDistinct, Bool.and_eq_true, List.all_eq_true] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, keysDistinct_nodup xs h.2⟩
    have := h.1 x hx
    simp at this

/-- The indices `±n` of all candidates are distinct and nonzero. -/
def candsOK (l : List Cand) : Bool :=
  keysDistinct (candKeys l) && l.all fun c => !(decide (c.i = 0) && decide (c.j = 0) && decide (c.k = 0))

theorem flatMap_vecs (l : List Cand) :
    l.flatMap (fun c => [c.vec, c.nvec]) = (candKeys l).map keyVec := by
  unfold candKeys
  induction l with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, ih]
    rfl

theorem cands_nodup (l : List Cand) (h : candsOK l = true) :
    (l.flatMap fun c => [c.vec, c.nvec]).Nodup := by
  rw [flatMap_vecs]
  exact List.Nodup.map keyVec_injective (keysDistinct_nodup _ (Bool.and_eq_true_iff.mp h).1)

theorem cand_ne_zero (l : List Cand) (h : candsOK l = true) (c : Cand) (hc : c ∈ l) :
    c.vec ≠ 0 ∧ c.nvec ≠ 0 := by
  have h2 := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 c hc
  have hnz : ¬ (c.i = 0 ∧ c.j = 0 ∧ c.k = 0) := by
    rintro ⟨a, b, d⟩
    simp [a, b, d] at h2
  constructor
  · intro hv
    apply hnz
    have e0 := congrFun hv 0
    have e1 := congrFun hv 1
    have e2 := congrFun hv 2
    simp [Cand.vec] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  · intro hv
    apply hnz
    have e0 := congrFun hv 0
    have e1 := congrFun hv 1
    have e2 := congrFun hv 2
    simp [Cand.nvec] at e0 e1 e2
    exact ⟨e0, e1, e2⟩

/-! ## Anchor positions

Nothing here enters the soundness proof: a position only selects a table entry. -/

/-- Anchors `k / 2^bits` for `lo ≤ k ≤ hi`, at table positions `offset + (k - lo)`. An index
divisible by `skip` (when `skip ≠ 0`) is left to a later segment. -/
structure TableSeg where
  bits : ℕ
  lo : ℤ
  hi : ℤ
  offset : ℕ
  skip : ℤ

/-- The position of the anchor nearest to `Q / 2^24` in the first segment that takes it. -/
def segPos (Q : ℤ) : List TableSeg → Option ℕ
  | [] => none
  | s :: rest =>
    let k := (Q + pw (23 - s.bits)) >>> (24 - s.bits)
    if decide (k ≤ s.hi) && decide (s.lo ≤ k) && (decide (s.skip = 0) || !decide (k % s.skip = 0)) then
      some (s.offset + (k - s.lo).toNat)
    else segPos Q rest

/-- The entries `(M00, M11, M22, M01, M02, M12)` of a symmetric integer matrix. -/
structure Sym6 where
  m00 : ℤ
  m11 : ℤ
  m22 : ℤ
  m01 : ℤ
  m02 : ℤ
  m12 : ℤ

def Sym6.quad (M : Sym6) (c : Cand) : ℤ :=
  M.m00 * c.g0 + M.m11 * c.g1 + M.m22 * c.g2 + M.m01 * c.g3 + M.m02 * c.g4 + M.m12 * c.g5

/-- At the centre of an `s`-box: `J` (scale `2^64`), `adj J` (scale `2^128`), `c1 λ / 4` and
`c2 λ² / 4` (scale `2^64`). -/
structure CentreData where
  J : Sym6
  A : Sym6
  fd : ℤ
  fu : ℤ

def centreData (ref : Reference) (zb : ZBox) : CentreData :=
  let s : Fin 5 → ℤ := ![(zb.lo 0 + zb.hi 0) / 2, (zb.lo 1 + zb.hi 1) / 2, (zb.lo 2 + zb.hi 2) / 2,
    (zb.lo 3 + zb.hi 3) / 2, (zb.lo 4 + zb.hi 4) / 2]
  let J := sJZ s
  let A := adj3 J
  let d := J 0 0 * A 0 0 + J 0 1 * A 1 0 + J 0 2 * A 2 0
  let m : ℤ := (icbrt ((2 ^ 384 : ℕ) / d.toNat) : ℤ)
  ⟨⟨J 0 0, J 1 1, J 2 2, J 0 1, J 0 2, J 1 2⟩, ⟨A 0 0, A 1 1, A 2 2, A 0 1, A 0 2, A 1 2⟩,
    ((c1Z ref).lo * m) >>> 66, ((c2Z ref).lo * (m * m)) >>> 130⟩

/-- The table entry of a candidate whose squared length is `Q / 2^24` with
`Q = (f · aᵀ M a) / 2^sh`; no entry when `Q > cap`. -/
def pickTangent (t : ZTree) (h : ℕ) (segs : List TableSeg) (cap : ℤ) (M : Sym6) (f : ℤ) (sh : ℕ)
    (c : Cand) : Option (ℤ × ℤ) :=
  let Q := (f * M.quad c) >>> sh
  if Q ≤ cap then
    match segPos Q segs with
    | some k => t.get h k
    | none => none
  else none

theorem pickTangent_valid (kind : KernelKind) (t : ZTree) (ht : t.Valid kind) (h : ℕ)
    (segs : List TableSeg) (cap : ℤ) (M : Sym6) (f : ℤ) (sh : ℕ) (c : Cand) (ic ip : ℤ)
    (e : pickTangent t h segs cap M f sh c = some (ic, ip)) : ValidTangent kind (zTangent ic ip) := by
  unfold pickTangent at e
  simp only at e
  split_ifs at e
  split at e
  · exact ZTree.get_valid kind t ht h _ ic ip e
  · contradiction

/-! ## Integer aggregates of candidate terms -/

def zAggZero : ZAgg := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem zAggZero_toAgg : zAggZero.toAgg = Aggregate.zero := by
  simp [zAggZero, ZAgg.toAgg, Aggregate.zero]

/-- The direct terms `n` and `-n` with the tangent `(ic, ip)`. -/
def zAddDir2 (z : ZAgg) (c : Cand) (ic ip : ℤ) : ZAgg :=
  ⟨z.a + 2 * ic, z.p00 + 2 * ip * (c.i * c.i), z.p01 + 2 * ip * (c.i * c.j), z.p02 + 2 * ip * (c.i * c.k),
    z.p11 + 2 * ip * (c.j * c.j), z.p12 + 2 * ip * (c.j * c.k), z.p22 + 2 * ip * (c.k * c.k),
    z.d00, z.d01, z.d02, z.d11, z.d12, z.d22⟩

/-- The dual terms `n` and `-n` with the tangent `(ic, ip)`. -/
def zAddDual2 (z : ZAgg) (c : Cand) (ic ip : ℤ) : ZAgg :=
  ⟨z.a + 2 * ic, z.p00, z.p01, z.p02, z.p11, z.p12, z.p22,
    z.d00 + 2 * ip * (c.i * c.i), z.d01 + 2 * ip * (c.i * c.j), z.d02 + 2 * ip * (c.i * c.k),
    z.d11 + 2 * ip * (c.j * c.j), z.d12 + 2 * ip * (c.j * c.k), z.d22 + 2 * ip * (c.k * c.k)⟩

theorem zAddDir2_toAgg (z : ZAgg) (c : Cand) (ic ip : ℤ) :
    (zAddDir2 z c ic ip).toAgg =
      (z.toAgg.addDir (c.vec, zTangent ic ip)).addDir (c.nvec, zTangent ic ip) := by
  simp only [zAddDir2, ZAgg.toAgg, Aggregate.addDir, zTangent, Cand.vec, Cand.nvec, pwQ_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Aggregate.mk.injEq]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

theorem zAddDual2_toAgg (z : ZAgg) (c : Cand) (ic ip : ℤ) :
    (zAddDual2 z c ic ip).toAgg =
      (z.toAgg.addDual (c.vec, zTangent ic ip)).addDual (c.nvec, zTangent ic ip) := by
  simp only [zAddDual2, ZAgg.toAgg, Aggregate.addDual, zTangent, Cand.vec, Cand.nvec, pwQ_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Aggregate.mk.injEq]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

def foldDir (sel : Cand → Option (ℤ × ℤ)) : List Cand → ZAgg → ZAgg
  | [], z => z
  | c :: rest, z => foldDir sel rest (match sel c with
    | some (ic, ip) => zAddDir2 z c ic ip
    | none => z)

def foldDual (sel : Cand → Option (ℤ × ℤ)) : List Cand → ZAgg → ZAgg
  | [], z => z
  | c :: rest, z => foldDual sel rest (match sel c with
    | some (ic, ip) => zAddDual2 z c ic ip
    | none => z)

/-- The terms behind `foldDir` and `foldDual`. -/
def termsOf (sel : Cand → Option (ℤ × ℤ)) : List Cand → List Term
  | [] => []
  | c :: rest => match sel c with
    | some (ic, ip) => (c.vec, zTangent ic ip) :: (c.nvec, zTangent ic ip) :: termsOf sel rest
    | none => termsOf sel rest

theorem foldDir_toAgg (sel : Cand → Option (ℤ × ℤ)) : ∀ (l : List Cand) (z : ZAgg),
    (foldDir sel l z).toAgg = (termsOf sel l).foldl Aggregate.addDir z.toAgg
  | [], _ => rfl
  | c :: rest, z => by
    rcases h : sel c with _ | ⟨ic, ip⟩
    · simp only [foldDir, termsOf, h]
      exact foldDir_toAgg sel rest z
    · simp only [foldDir, termsOf, h, List.foldl_cons]
      rw [foldDir_toAgg sel rest, zAddDir2_toAgg]

theorem foldDual_toAgg (sel : Cand → Option (ℤ × ℤ)) : ∀ (l : List Cand) (z : ZAgg),
    (foldDual sel l z).toAgg = (termsOf sel l).foldl Aggregate.addDual z.toAgg
  | [], _ => rfl
  | c :: rest, z => by
    rcases h : sel c with _ | ⟨ic, ip⟩
    · simp only [foldDual, termsOf, h]
      exact foldDual_toAgg sel rest z
    · simp only [foldDual, termsOf, h, List.foldl_cons]
      rw [foldDual_toAgg sel rest, zAddDual2_toAgg]

theorem termsOf_fst_sublist (sel : Cand → Option (ℤ × ℤ)) : ∀ (l : List Cand),
    ((termsOf sel l).map Prod.fst).Sublist (l.flatMap fun c => [c.vec, c.nvec])
  | [] => List.Sublist.slnil
  | c :: rest => by
    have ih := termsOf_fst_sublist sel rest
    rcases h : sel c with _ | ⟨ic, ip⟩
    · simp only [termsOf, h, List.flatMap_cons, List.cons_append, List.nil_append]
      exact (ih.cons _).cons _
    · simp only [termsOf, h, List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons]
      exact (ih.cons_cons _).cons_cons _

theorem termsOf_mem (sel : Cand → Option (ℤ × ℤ)) : ∀ (l : List Cand) (x : Term),
    x ∈ termsOf sel l → ∃ c ∈ l, ∃ ic ip, sel c = some (ic, ip) ∧
      (x = (c.vec, zTangent ic ip) ∨ x = (c.nvec, zTangent ic ip))
  | [], x, hx => by simp [termsOf] at hx
  | c :: rest, x, hx => by
    rcases h : sel c with _ | ⟨ic, ip⟩
    · simp only [termsOf, h] at hx
      obtain ⟨c', hc', ic', ip', e, hx'⟩ := termsOf_mem sel rest x hx
      exact ⟨c', List.mem_cons_of_mem _ hc', ic', ip', e, hx'⟩
    · simp only [termsOf, h, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ⟨c, List.mem_cons.mpr (Or.inl rfl), ic, ip, h, Or.inl rfl⟩
      · exact ⟨c, List.mem_cons.mpr (Or.inl rfl), ic, ip, h, Or.inr rfl⟩
      · obtain ⟨c', hc', ic', ip', e, hx'⟩ := termsOf_mem sel rest x hx
        exact ⟨c', List.mem_cons_of_mem _ hc', ic', ip', e, hx'⟩

theorem termsOf_valid (kind : KernelKind) (sel : Cand → Option (ℤ × ℤ)) (l : List Cand)
    (hl : candsOK l = true) (v : ∀ c ic ip, sel c = some (ic, ip) → ValidTangent kind (zTangent ic ip)) :
    ∀ x ∈ termsOf sel l, x.1 ≠ 0 ∧ ValidTangent kind x.2 := by
  intro x hx
  obtain ⟨c, hc, ic, ip, e, rfl | rfl⟩ := termsOf_mem sel l x hx
  · exact ⟨(cand_ne_zero l hl c hc).1, v c ic ip e⟩
  · exact ⟨(cand_ne_zero l hl c hc).2, v c ic ip e⟩

/-- The aggregate of valid tangents on distinct candidates is certified. -/
theorem fold_certified (sd su : Cand → Option (ℤ × ℤ)) (ld lu : List Cand)
    (hd : candsOK ld = true) (hu : candsOK lu = true)
    (vd : ∀ c ic ip, sd c = some (ic, ip) → ValidTangent .half (zTangent ic ip))
    (vu : ∀ c ic ip, su c = some (ic, ip) → ValidTangent .one (zTangent ic ip)) :
    Certified (foldDual su lu (foldDir sd ld zAggZero)).toAgg := by
  refine ⟨⟨termsOf sd ld, termsOf su lu⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (cands_nodup ld hd).sublist (termsOf_fst_sublist sd ld)
  · exact (cands_nodup lu hu).sublist (termsOf_fst_sublist su lu)
  · exact termsOf_valid .half sd ld hd vd
  · exact termsOf_valid .one su lu hu vu
  · show (termsOf su lu).foldl Aggregate.addDual ((termsOf sd ld).foldl Aggregate.addDir Aggregate.zero) = _
    rw [foldDual_toAgg, foldDir_toAgg, zAggZero_toAgg]

/-! ## Tangent leaves -/

/-- The tables, the table segments, the length cap and the candidates of the tangent leaves. -/
structure AtlasData where
  T : ZTables
  segHalf : List TableSeg
  segOne : List TableSeg
  cap : ℤ
  dirC : Reference → List Cand
  dualC : Reference → List Cand

def AtlasData.Valid (D : AtlasData) : Prop :=
  D.T.Valid ∧ ∀ ref, candsOK (D.dirC ref) = true ∧ candsOK (D.dualC ref) = true

/-- The aggregate of a tangent leaf with `s`-box `zb`. -/
def AtlasData.agg (D : AtlasData) (ref : Reference) (zb : ZBox) : ZAgg :=
  let C := centreData ref zb
  foldDual (pickTangent D.T.one D.T.height D.segOne D.cap C.A C.fu 168) (D.dualC ref)
    (foldDir (pickTangent D.T.half D.T.height D.segHalf D.cap C.J C.fd 104) (D.dirC ref) zAggZero)

theorem AtlasData.agg_certified (D : AtlasData) (hD : D.Valid) (ref : Reference) (zb : ZBox) :
    Certified (D.agg ref zb).toAgg :=
  fold_certified _ _ _ _ (hD.2 ref).1 (hD.2 ref).2
    (fun c ic ip e => pickTangent_valid .half _ hD.1.1 _ _ _ _ _ _ c ic ip e)
    (fun c ic ip e => pickTangent_valid .one _ hD.1.2 _ _ _ _ _ _ c ic ip e)

/-- A tangent leaf: the integer leaf check on the aggregate of the box. -/
def tanCheck (D : AtlasData) (ref : Reference) (e2 : Bool) (b : Rectangle) : Bool :=
  zLeafCheck ref e2 (D.agg ref (zBox ref b)) b

/-! ## Atlas trees -/

inductive APay where
  | outside
  | ball
  | tangent (e2 : Bool)

def APay.check (D : AtlasData) (ref : Reference) : APay → Rectangle → Bool
  | .outside, b => strainOutsideCheck ref b
  | .ball, b => insideBallCheck beta beta b
  | .tangent e2, b => tanCheck D ref e2 b

inductive ATree where
  | cut (axis : Fin 5) (face : ℚ) (lower upper : ATree)
  | leaf (w : APay)

def ATree.check (D : AtlasData) (ref : Reference) : ATree → Rectangle → Bool
  | .cut axis face l u, b => l.check D ref (split b axis face false) && u.check D ref (split b axis face true)
  | .leaf w, b => w.check D ref b

/-- Every eligible strain of `b` is in the local product ball or is strain-sharp. -/
def AtlasClosed (ref : Reference) (b : Rectangle) : Prop :=
  ∀ w, b.Mem w → strainEligible ref w → inProductBall beta beta w ∨ strainSharp ref w

theorem APay.closed (D : AtlasData) (hD : D.Valid) (ref : Reference) (w : APay) (b : Rectangle)
    (ok : w.check D ref b = true) : AtlasClosed ref b := by
  intro p hp live
  cases w with
  | outside => exact (strainOutsideCheck_sound ref b ok p hp live).elim
  | ball => exact Or.inl (insideBallCheck_sound beta beta b ok p hp)
  | tangent e2 => exact Or.inr (zLeafCheck_sound ref e2 _ (D.agg_certified hD ref _) b ok p hp)

theorem ATree.closed (D : AtlasData) (hD : D.Valid) (ref : Reference) :
    ∀ (t : ATree) (b : Rectangle), t.check D ref b = true → AtlasClosed ref b
  | .leaf w, b, ok => w.closed D hD ref b ok
  | .cut axis face l u, b, ok => by
    simp only [ATree.check, Bool.and_eq_true] at ok
    intro p hp live
    rcases split_covers b axis face p hp with hl | hu
    · exact ATree.closed D hD ref l _ ok.1 p hl live
    · exact ATree.closed D hD ref u _ ok.2 p hu live

theorem closed_cut (ref : Reference) (b : Rectangle) (axis : Fin 5) (face : ℚ)
    (hl : AtlasClosed ref (split b axis face false)) (hu : AtlasClosed ref (split b axis face true)) :
    AtlasClosed ref b := by
  intro p hp live
  rcases split_covers b axis face p hp with h | h
  · exact hl p h live
  · exact hu p h live

/-- A closed strain root makes every eligible strain sharp (the local balls are proved). -/
theorem sharp_of_closed (ref : Reference) (root : AtlasClosed ref (strainRoot ref)) (w : Point)
    (live : strainEligible ref w) : strainSharp ref w := by
  rcases root w (strainRoot_contains ref w live) live with ball | sharp
  · intro A hA gramEq
    by_cases zero : w = 0
    · rw [zero, reconstructedMetric_zero] at gramEq
      have properA : proper A := ⟨gramEq, hA⟩
      have rigid := strain_origin_rigid ref A properA
      have equality := strain_origin_deficit_zero ref A properA
      refine ⟨equality.ge, fun _ => ?_⟩
      cases ref
      · exact Or.inl rigid
      · exact Or.inr rigid
    · have strict := localBalls ref w live.1 ball zero A hA gramEq
      exact ⟨strict.le, fun e => (strict.ne' e).elim⟩
  · exact sharp

/-! ## The global forest with closed strain roots -/

theorem handoff_fold_of_sharp (ref : Reference) (b : Rectangle) (ok : handoffAnyRegionCheck ref b = true)
    (p : Point) (hp : b.Mem p) (hSharp : ∀ w, strainEligible ref w → strainSharp ref w) :
    Sharp (primitiveChart p) := by
  obtain ⟨j, into⟩ := handoffAnyRegionCheck_sound ref b ok
  have hc := chartInverses_sound (handoffAnyRegion_chartInverses ref b ok)
  have h₀ : 0 < p 0 := (by exact_mod_cast hc.1 : (0 : ℝ) < b.lo 0).trans_le (hp 0).1
  have h₁ : 0 < p 1 := (by exact_mod_cast hc.2.1 : (0 : ℝ) < b.lo 1).trans_le (hp 1).1
  let A := handoffMatrix ref j p
  have ha : |A.det| = 1 := handoff_unitVolume ref j p h₀.ne' h₁.ne'
  obtain ⟨B, hDet, hFold, hRegion, hGram, hL, hD⟩ := fold_strain_frame ref A ha
    (strainRadiusE ref) strainRadiusT (into p hp)
  have sharp := hSharp (framePoint ref B) ⟨hFold, hRegion⟩ B hDet hGram
  apply handoff_transferSharp ref j p
  change Sharp (strainBasis ref A)
  unfold Sharp at sharp ⊢
  simpa only [hL, hD] using sharp

theorem globalWithHandoffsCheck_sound_of_sharp (hSharp : ∀ ref w, strainEligible ref w → strainSharp ref w) :
    AddressedSound globalWithHandoffsCheck reduced (fun p => Sharp (primitiveChart p)) := by
  intro a r w b ok p hp live
  unfold globalWithHandoffsCheck at ok
  split at ok
  · exact handoff_fold_of_sharp .bcc b ok p hp (hSharp .bcc)
  · exact handoff_fold_of_sharp .fcc b ok p hp (hSharp .fcc)
  · exact globalCheck_sound a _ _ b ok p hp live

theorem tangentGlobalCheck_sound_of_sharp (T : Tables) (hT : T.Valid)
    (hSharp : ∀ ref w, strainEligible ref w → strainSharp ref w) :
    AddressedSound (tangentGlobalCheck T) reduced (fun p => Sharp (primitiveChart p)) := by
  intro a r w b ok p hp live
  cases w with
  | old w => exact globalWithHandoffsCheck_sound_of_sharp hSharp a r w b ok p hp live
  | tangent dir dual => exact tangentLeafCheck_sound T hT dir dual b (Bool.and_eq_true_iff.mp ok).2 p hp

/-- `latticeCase_from_tangent_forest` with the strain-sharp conclusion of the atlases as premise. -/
theorem latticeCase_from_tangent_forest_of_sharp {count : ℕ} (positive : 0 < count) (g : Grid count)
    (gOK : g.check globalRoot = true) (T : Tables) (hT : T.Valid)
    (forest : (Fin 2 → Fin count) → (Fin 3 → Fin count) → AddressedTree TPayload)
    (checked : ∀ owner suffix, (forest owner suffix).check (tangentGlobalCheck T)
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix)) = true)
    (hSharp : ∀ ref w, strainEligible ref w → strainSharp ref w) : LatticeCase := by
  intro B hB
  rcases KZ.physical_escape_or_root B hB with strict | ⟨r, root⟩
  · exact strict
  · apply r.transport
    exact addressed_grid_sound g positive globalRoot gOK .global (tangentGlobalCheck T)
      (tangentGlobalCheck_sound_of_sharp T hT hSharp) forest checked r.point
      (globalRoot_contains r.point root) r.reducedPoint

/-- `LatticeCase` from a checked tangent forest and the two closed strain roots. -/
theorem latticeCase_from_tangent_forest_closed {count : ℕ} (positive : 0 < count) (g : Grid count)
    (gOK : g.check globalRoot = true) (T : Tables) (hT : T.Valid)
    (forest : (Fin 2 → Fin count) → (Fin 3 → Fin count) → AddressedTree TPayload)
    (checked : ∀ owner suffix, (forest owner suffix).check (tangentGlobalCheck T)
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix)) = true)
    (closedRoot : ∀ ref, AtlasClosed ref (strainRoot ref)) : LatticeCase :=
  latticeCase_from_tangent_forest_of_sharp positive g gOK T hT forest checked
    (fun ref => sharp_of_closed ref (closedRoot ref))

end BccSharp.Coulomb.BravaisCover.StrainAtlas
