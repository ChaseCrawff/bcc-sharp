import BccSharp.Cover.LateChecker

/-! # HalfShift relative items in the kernel

Certificates for single HalfShift relative boxes (half bits 111), checked by
`decide +kernel` on `Layered.planarAnchorCertOk`. Generated; the boxes are the Stage6 atoms of the Corner jobs
(geometry folder `cornerRule`) named in the comments. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.PilotHalfShift

-- [704559, '133bddeeeee89b307db5d8207bc493', -1, 'local_basin'] hint 2.997642e-05 cost estimate 0.332323
noncomputable def box0 : Cell :=
  ⟨![(439/512 : ℚ), (1675/2048 : ℚ), (11/32 : ℚ), (3/64 : ℚ), (5/128 : ℚ), (63/128 : ℚ), (31/64 : ℚ), (-1/2 : ℚ)],
    ![(1773/2048 : ℚ), (841/1024 : ℚ), (23/64 : ℚ), (1/16 : ℚ), (3/64 : ℚ), (1/2 : ℚ), (63/128 : ℚ), (-63/128 : ℚ)]⟩
noncomputable def cert0 : PlanarAnchorCert where
  depth := 4
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(80146038797022/140737489454767 : ℚ), (80132355031806/140737489454767 : ℚ), (83441351140987/140737489454767 : ℚ)], ![(-115687702157454/140737489454767 : ℚ), (55430880332917/140737489454767 : ℚ), (57886216088778/140737489454767 : ℚ)], ![(94724363867/140737489454767 : ℚ), (-101554242258042/140737489454767 : ℚ), (97435967921094/140737489454767 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item0 : planarAnchorCertOk cert0 box0 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request0 (t : LatePackets.LateTables) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box0)
    (ht : t.halfShift q = some cert0) : LatePackets.lateChecker t q = true :=
  LatePackets.lateChecker_halfShift t q s half hint cert0 hq hpay ht (by rw [hb, hw]; exact item0)

-- [704559, '133bddeeeee89b307db5d8207ad493', -1, 'local_basin'] hint 3.224214e-05 cost estimate 0.331550
noncomputable def box1 : Cell :=
  ⟨![(439/512 : ℚ), (1675/2048 : ℚ), (11/32 : ℚ), (3/64 : ℚ), (5/128 : ℚ), (31/64 : ℚ), (63/128 : ℚ), (-1/2 : ℚ)],
    ![(1773/2048 : ℚ), (841/1024 : ℚ), (23/64 : ℚ), (1/16 : ℚ), (3/64 : ℚ), (63/128 : ℚ), (1/2 : ℚ), (-63/128 : ℚ)]⟩
noncomputable def cert1 : PlanarAnchorCert where
  depth := 4
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(80146038797022/140737489454767 : ℚ), (80132355031806/140737489454767 : ℚ), (83441351140987/140737489454767 : ℚ)], ![(-115687702157454/140737489454767 : ℚ), (55430880332917/140737489454767 : ℚ), (57886216088778/140737489454767 : ℚ)], ![(94724363867/140737489454767 : ℚ), (-101554242258042/140737489454767 : ℚ), (97435967921094/140737489454767 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item1 : planarAnchorCertOk cert1 box1 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request1 (t : LatePackets.LateTables) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box1)
    (ht : t.halfShift q = some cert1) : LatePackets.lateChecker t q = true :=
  LatePackets.lateChecker_halfShift t q s half hint cert1 hq hpay ht (by rw [hb, hw]; exact item1)

-- [704559, '133bddeeeee89b207db5d830649216', -1, 'basin'] hint 4.255461e-05 cost estimate 0.300434
noncomputable def box2 : Cell :=
  ⟨![(3529/4096 : ℚ), (827/1024 : ℚ), (11/32 : ℚ), (1/32 : ℚ), (5/128 : ℚ), (31/64 : ℚ), (31/64 : ℚ), (-1/2 : ℚ)],
    ![(1773/2048 : ℚ), (1661/2048 : ℚ), (23/64 : ℚ), (5/128 : ℚ), (3/64 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-63/128 : ℚ)]⟩
noncomputable def cert2 : PlanarAnchorCert where
  depth := 4
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(160279491155647/281474975969571 : ℚ), (161484619283306/281474975969571 : ℚ), (165714708299786/281474975969571 : ℚ)], ![(-231381459532666/281474975969571 : ℚ), (110878167121249/281474975969571 : ℚ), (115744608243478/281474975969571 : ℚ)], ![(1125609386374/281474975969571 : ℚ), (-202130927588602/281474975969571 : ℚ), (195882575061569/281474975969571 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item2 : planarAnchorCertOk cert2 box2 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request2 (t : LatePackets.LateTables) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box2)
    (ht : t.halfShift q = some cert2) : LatePackets.lateChecker t q = true :=
  LatePackets.lateChecker_halfShift t q s half hint cert2 hq hpay ht (by rw [hb, hw]; exact item2)

end BccSharp.Coulomb.CompactCover.Layered.PilotHalfShift
