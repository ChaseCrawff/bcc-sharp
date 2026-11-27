import BccSharp.Cover.LayeredFarRoute

/-! # HalfShift relative items past the cost budget in the kernel

Certificates for single HalfShift relative boxes (half bits 111) whose
registration cost bound `100 strain⁺ + 200 |R d|²⁺` exceeds `1/2`, checked by
`decide +kernel` on `Layered.planarAnchorCertOkFar` (far-annulus transport, no cost
budget). Generated; the boxes are the Stage6
atoms of the Corner jobs (geometry folder `cornerRule`) named in the comments. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.PilotFarHalfShift

-- [704559, '133bddeeeee89ad307bc48217bc582', -1, 'local_basin'] hint 1.097542e-05 cost estimate 0.733179
noncomputable def box0 : Cell :=
  ⟨![(1773/2048 : ℚ), (417/512 : ℚ), (21/64 : ℚ), (3/64 : ℚ), (1/32 : ℚ), (59/128 : ℚ), (15/32 : ℚ), (-1/2 : ℚ)],
    ![(895/1024 : ℚ), (1675/2048 : ℚ), (11/32 : ℚ), (1/16 : ℚ), (5/128 : ℚ), (15/32 : ℚ), (61/128 : ℚ), (-63/128 : ℚ)]⟩
noncomputable def cert0 : PlanarAnchorCert where
  depth := 1
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(81094007576433/140737482348067 : ℚ), (79645539124934/140737482348067 : ℚ), (82990294434738/140737482348067 : ℚ)], ![(-115025053264046/140737482348067 : ℚ), (56322947527338/140737482348067 : ℚ), (58343822647377/140737482348067 : ℚ)], ![(-194921700378/140737482348067 : ℚ), (-101446304107167/140737482348067 : ℚ), (97548184638154/140737482348067 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item0 : planarAnchorCertOkFar cert0 box0 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request0 (table : LatePackets.Request → Option PlanarAnchorCert) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box0)
    (ht : table q = some cert0) : halfShiftCheckFar table q = true :=
  halfShiftCheckFar_accept table q s half hint cert0 hq hpay ht (by rw [hb, hw]; exact item0)

-- [704559, '133bddeeeee89ad307bc48217bd582', -1, 'local_basin'] hint 1.097542e-05 cost estimate 0.636138
noncomputable def box1 : Cell :=
  ⟨![(1773/2048 : ℚ), (417/512 : ℚ), (21/64 : ℚ), (3/64 : ℚ), (1/32 : ℚ), (59/128 : ℚ), (61/128 : ℚ), (-1/2 : ℚ)],
    ![(895/1024 : ℚ), (1675/2048 : ℚ), (11/32 : ℚ), (1/16 : ℚ), (5/128 : ℚ), (15/32 : ℚ), (31/64 : ℚ), (-63/128 : ℚ)]⟩
noncomputable def cert1 : PlanarAnchorCert where
  depth := 1
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(81094007576433/140737482348067 : ℚ), (79645539124934/140737482348067 : ℚ), (82990294434738/140737482348067 : ℚ)], ![(-115025053264046/140737482348067 : ℚ), (56322947527338/140737482348067 : ℚ), (58343822647377/140737482348067 : ℚ)], ![(-194921700378/140737482348067 : ℚ), (-101446304107167/140737482348067 : ℚ), (97548184638154/140737482348067 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item1 : planarAnchorCertOkFar cert1 box1 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request1 (table : LatePackets.Request → Option PlanarAnchorCert) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box1)
    (ht : table q = some cert1) : halfShiftCheckFar table q = true :=
  halfShiftCheckFar_accept table q s half hint cert1 hq hpay ht (by rw [hb, hw]; exact item1)

-- [704559, '133bddeeeee88306ad59207bd49207', -1, 'local_basin'] hint 1.695015e-05 cost estimate 0.595314
noncomputable def box2 : Cell :=
  ⟨![(439/512 : ℚ), (417/512 : ℚ), (11/32 : ℚ), (3/128 : ℚ), (3/128 : ℚ), (29/64 : ℚ), (31/64 : ℚ), (-1/2 : ℚ)],
    ![(3529/4096 : ℚ), (1675/2048 : ℚ), (23/64 : ℚ), (1/32 : ℚ), (1/32 : ℚ), (15/32 : ℚ), (1/2 : ℚ), (-63/128 : ℚ)]⟩
noncomputable def cert2 : PlanarAnchorCert where
  depth := 4
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(16029037365739/28147497168989 : ℚ), (16195402031136/28147497168989 : ℚ), (16524542688252/28147497168989 : ℚ)], ![(-115688073538932/140737485844945 : ℚ), (11177573350980/28147497168989 : ℚ), (57444372330049/140737485844945 : ℚ)], ![(242055779376/140737485844945 : ℚ), (-20125913741035/28147497168989 : ℚ), (98390402139468/140737485844945 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item2 : planarAnchorCertOkFar cert2 box2 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request2 (table : LatePackets.Request → Option PlanarAnchorCert) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box2)
    (ht : table q = some cert2) : halfShiftCheckFar table q = true :=
  halfShiftCheckFar_accept table q s half hint cert2 hq hpay ht (by rw [hb, hw]; exact item2)

end BccSharp.Coulomb.CompactCover.Layered.PilotFarHalfShift
