import BccSharp.TwoSite.JacobiTriple
import BccSharp.TwoSite.MontgomeryBasic
import BccSharp.TwoSite.MontgomerySmallT
import BccSharp.TwoSite.MontgomeryX
import BccSharp.TwoSite.MontgomeryY

/-!
# Montgomery's Theorem 1 (the inequality)

H. L. Montgomery, *Minimal theta functions*, Glasgow Math. J. 30 (1988) 75–85.

For `α > 0` and every positive definite binary quadratic form of discriminant `-1`,
written as `θ(α; x, y)` with `y > 0`, the hexagonal form has the least theta value:
`θ_h(α) ≤ θ(α; x, y)`. The monotonicity statements are non-strict throughout, so the
equality case of the paper is not proved.

* `BccSharp.TwoSite.JacobiTriple`: the Jacobi triple product and Lemma 1 (`lemma1_of`).
* `BccSharp.TwoSite.MontgomeryBasic`: the `β`-derivative of `θ(t; β)` (`theta1_hasDerivAt`),
  duality (2) (`duality`) and the unfolding (13) (`unfold13`).
* `BccSharp.TwoSite.MontgomerySmallT`: bounds on `Q(t; 0)` and `Q(t; 1/2)` for `0 < t < 1`
  (`smallT_bounds`).
* `BccSharp.TwoSite.MontgomeryX`: Lemma 4 (`xMonotone_of`) and the reduction to the
  fundamental domain of `SL(2, ℤ)` (`theorem1_of`).
* `BccSharp.TwoSite.MontgomeryY`: Lemma 7 on the line `x = 1/2` (`yMonotoneHalf_of_duality`).
-/

set_option autoImplicit false

namespace BccSharp.Coulomb.Montgomery

/-- Montgomery, Theorem 1 (the inequality): `θ_h(α) ≤ θ(α; x, y)` for `α > 0`, `y > 0`. -/
theorem theorem1 : Theorem1 :=
  theorem1_of
    (xMonotone_of (lemma1_of theta1_hasDerivAt fun _ ht => Qser_continuous ht) smallT_bounds)
    (yMonotoneHalf_of_duality duality)

end BccSharp.Coulomb.Montgomery
