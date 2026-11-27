import BccSharp.Cover.OverlayFixSound

set_option autoImplicit false

/-! Assembly lemmas for the generated Overlay row modules.

A row's replacement tree is checked with `Tree.check overlayFixCheck`. The
leaves are paid in separate modules, one `decide +kernel` declaration per
leaf; the row module puts them together along the tree:

* `Tree.fitsAll` checks every cut of the tree in one kernel evaluation;
* `Tree.check_split_of_fits`, `Tree.check_close_of` and `Tree.check_hold_of`
  rebuild `Tree.check` node by node from the leaf facts, so no leaf is
  evaluated twice.

`rowSound` restates `Tree.sound` for a checked row. -/

namespace BccSharp.Coulomb.CompactCover
open BccSharp BccSharp.Coverage

def Tree.fitsAll (b : Cell) : Tree → Bool
  | .close _ => true
  | .hold _ => true
  | .split cut l r => cut.fits b && (l.fitsAll (cut.child b false) && r.fitsAll (cut.child b true))

theorem Tree.check_split_of_fits {check : WitnessRef → Cell → Bool} {cut : Cut} {l r : Tree} {b : Cell}
    (h : (Tree.split cut l r).fitsAll b = true)
    (hl : l.fitsAll (cut.child b false) = true → l.check check (cut.child b false) = true)
    (hr : r.fitsAll (cut.child b true) = true → r.check check (cut.child b true) = true) :
    (Tree.split cut l r).check check b = true := by
  simp only [Tree.fitsAll, Bool.and_eq_true] at h
  simp only [Tree.check, h.1, hl h.2.1, hr h.2.2, Bool.and_self]

theorem Tree.check_close_of {check : WitnessRef → Cell → Bool} {w : WitnessRef} {b : Cell}
    (h : check w b = true) : (Tree.close w).fitsAll b = true → (Tree.close w).check check b = true :=
  fun _ => h

theorem Tree.check_hold_of {check : WitnessRef → Cell → Bool} {k : Key} {b : Cell} :
    (Tree.hold k).fitsAll b = true → (Tree.hold k).check check b = true :=
  fun _ => rfl

namespace OverlayPlanar.Fix

def hardBank : String := "overlay/hard-roots.json"
def adaptiveBank : String := "overlay/full-frontier.json"

theorem rowSound {tree : Tree} {root : Cell} (h : tree.check overlayFixCheck root = true) (p : Chart)
    (hp : root.Mem p) (gp : good p) : LeafProof (chartPoint p) ∨ Held (tree.holds root) p :=
  Tree.sound overlayFixCheck_sound tree root h p gp hp

end OverlayPlanar.Fix

end BccSharp.Coulomb.CompactCover
