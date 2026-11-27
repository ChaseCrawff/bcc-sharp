import BccSharp.Cover.LayeredPilot

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-! # Negative controls for the PlanarAnchor relative check

Each control changes one part of the certificate of the thinnest PlanarAnchor relative
item (`Pilot.cert0` on `Pilot.box0`, wrap `(1, 1, 1)`) and proves in the
kernel that `planarAnchorCertOk` rejects it. In the first two the inequality
`deficit(anchor) + k |R d|² ≤ deficit(p)` that a passing certificate implies
would be false; in the third a premise of the check fails.

* `control_wrap`: the anchor one lattice step away, `(3/2, 1/2, 1/2)` (wrap
  `(2, 1, 1)`, registration translated to match). At the corner of the box
  with offsets `(1/2, 1/2, 1/2)` the point is the anchor configuration itself,
  and `d = (−1, 0, 0)`, so the inequality would read `k r² ≤ 0` with
  `r² ≈ 0.75`. On the whole box `|d₀| ≥ 1` and `r > 0.86` give
  `|R d|² > 1/2`, so the defect-transport premise
  `D(anchor) + 200 |R d|² ≤ 1/2` fails too.
* `control_margin`: the relative margin `k = 10⁶` at split depth 3. The
  inequality fails near the anchor face of the box, where `|R d|²` is small
  but positive and the deficit difference is of order `|R d|²` with a
  coefficient far below `10⁶`.
* `control_rotation`: one entry of the rotation `U` moved by `10⁻¹²`, so `U`
  is not orthogonal and the exact `registrationCheck` fails. The conclusion
  itself is `item0`'s, which holds; the control shows that the registration
  premise is checked. -/

namespace BccSharp.Coulomb.CompactCover.Layered.Pilot

theorem control_wrap :
    planarAnchorCertOk { cert0 with reg := { cert0.reg with wrap := ![2, 1, 1] } } box0 ![2, 1, 1] = false := by
  decide +kernel

theorem control_margin :
    planarAnchorCertOk { cert0 with depth := 3, k := 1000000 } box0 ![1, 1, 1] = false := by
  decide +kernel

theorem control_rotation :
    planarAnchorCertOk { cert0 with reg := { cert0.reg with
      U := fun i j => if i = 0 ∧ j = 0 then cert0.reg.U 0 0 + 1 / 10 ^ 12 else cert0.reg.U i j } }
      box0 ![1, 1, 1] = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.Layered.Pilot
