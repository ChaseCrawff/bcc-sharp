import BccSharp.Cover.PlanarFibreTri

set_option autoImplicit false

/-! # Literal cells for per-leaf certificates

`TriTree.ok` checks a leaf on the half-cell expression (`lowHalf`, `highHalf`)
that it builds from the request's box. Generated per-leaf modules
 check `boxOk` on a literal cell
in one theorem per leaf, and identify the half-cell expression with the literal
cell by `cell_eq_of`, whose premises `decide +kernel` evaluates (eight rational
equalities each). One kernel evaluation per leaf keeps the kernel's memory to
one leaf at a time. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri
open BccSharp.Coulomb.CompactCover

theorem cell_eq_of {a b : Cell} (hlo : ∀ i, a.lo i = b.lo i) (hhi : ∀ i, a.hi i = b.hi i) :
    a = b := by
  cases a with
  | mk alo ahi =>
    cases b with
    | mk blo bhi =>
      have h1 : alo = blo := funext hlo
      have h2 : ahi = bhi := funext hhi
      subst h1
      subst h2
      rfl

end BccSharp.Coulomb.CompactCover.PlanarFibreTri
