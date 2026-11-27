import BccSharp.Cover.OverlayArea

set_option autoImplicit false

/-! Kernel-evaluable form of the Overlay planar checker.

`Finset.toList` is noncomputable, so the kernel cannot reduce
`(waves n).toList.all f` in `retainedCheck` and `triangleCheck`: `decide`
gets stuck there. `wavesList n` enumerates the same waves as an explicit
list, and `toList_all_eq` turns each such `all` into a list check. The checks
`retainedCheckL` and `layerCheckL` are equal to the originals. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp BccSharp.Coverage BravaisCover DirectRoute
open BccSharp.Intervals (Ball)

def waveSpan (n : ℕ) : List ℤ := (List.range (2*n+1)).map (fun k : ℕ => (k : ℤ)-n)

theorem mem_waveSpan (n : ℕ) (i : ℤ) : i ∈ waveSpan n ↔ -(n : ℤ) ≤ i ∧ i ≤ n := by
  unfold waveSpan
  rw [List.mem_map]
  constructor
  · rintro ⟨k,hk,rfl⟩
    have := List.mem_range.mp hk
    omega
  · rintro ⟨h₁,h₂⟩
    exact ⟨(i+n).toNat,List.mem_range.mpr (by omega),by omega⟩

def wavesList (n : ℕ) : List Wave :=
  ((waveSpan n).flatMap (fun i => (waveSpan n).map (fun j => (i,j)))).filter
    (fun m => decide (0< m.1 ∨ (m.1=0 ∧ 0< m.2)))

theorem mem_wavesList (n : ℕ) (m : Wave) : m ∈ wavesList n ↔ m ∈ waves n := by
  rcases m with ⟨i,j⟩
  simp only [wavesList,waves,List.mem_filter,List.mem_flatMap,List.mem_map,Finset.mem_filter,
    mem_waveCube,waveRadius,decide_eq_true_eq,mem_waveSpan,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a,ha,b,hb,rfl,rfl⟩,h⟩
    exact ⟨by omega,h⟩
  · rintro ⟨hr,h⟩
    exact ⟨⟨i,by omega,j,by omega,rfl,rfl⟩,h⟩

theorem toList_all_eq (n : ℕ) (f : Wave → Bool) : (waves n).toList.all f=(wavesList n).all f := by
  rw [Bool.eq_iff_iff,List.all_eq_true,List.all_eq_true]
  simp only [Finset.mem_toList,mem_wavesList]

def retainedCheckL (raw : Cell) (cube : ℕ) : Bool :=
  let b := seamCell raw
  (diagonalsCheck b && decide (0< spacing b)) && (wavesList cube).all (waveCheck b)

theorem retainedCheck_eq (raw : Cell) (cube : ℕ) : retainedCheck raw cube=retainedCheckL raw cube := by
  simp only [retainedCheck,retainedCheckL,toList_all_eq]

def layerCheckL (raw : Cell) (cube : ℕ) : Bool :=
  retainedCheckL raw cube && radialCheck (seamCell raw) (cube+1)

theorem layerCheck_eq (raw : Cell) (cube : ℕ) : layerCheck raw cube=layerCheckL raw cube := by
  simp only [layerCheck,layerCheckL,retainedCheck_eq]

end BccSharp.Coulomb.CompactCover.OverlayPlanar
