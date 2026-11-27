import BccSharp.Cover.LateChecker

/-! # PlanarAnchor relative items in the kernel

Certificates for single PlanarAnchor relative boxes, checked by `decide +kernel` on
`Layered.planarAnchorCertOk`. Generated; the
boxes are the round-2 geometry of the corpus rows named in the comments. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb.CompactCover.Layered.Fix
open BccSharp.Coulomb.CompactCover.OverlayPlanar
open BccSharp.Coulomb.CompactCover.OverlayPlanar.Fix
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.Pilot

-- [710155, '338bddfffff18206bd5830', 1, 'fd5b643b6f49'] hint 6.887512e-04 cost estimate 0.139705
noncomputable def box0 : Cell :=
  ⟨![(3545351/4096000 : ℚ), (207593/256000 : ℚ), (23/64 : ℚ), (0 : ℚ), (1/128 : ℚ), (63/128 : ℚ), (31/64 : ℚ), (255/512 : ℚ)],
    ![(1773/2048 : ℚ), (52109/64000 : ℚ), (93/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ)]⟩
noncomputable def cert0 : PlanarAnchorCert where
  depth := 1
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(79536399783352/140737485547645 : ℚ), (16396854686343/28147497109529 : ℚ), (82216664111664/140737485547645 : ℚ)], ![(-116107332960789/140737485547645 : ℚ), (11181202471464/28147497109529 : ℚ), (56574241959652/140737485547645 : ℚ)], ![(59390406252/28147497109529 : ℚ), (-19960096723664/28147497109529 : ℚ), (19846223950479/28147497109529 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item0 : planarAnchorCertOk cert0 box0 ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] = true := by decide +kernel

theorem request0 (t : LatePackets.LateTables) (q : LatePackets.Request)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .planarAnchor)
    (hpay : q.proposal.payload = .optical .layered .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (1 : ℤ)]) (hb : q.target.box = box0)
    (ht : t.planarAnchor q = some cert0) : LatePackets.lateChecker t q = true :=
  LatePackets.lateChecker_planarAnchor t q half hint cert0 hq hpay ht (by rw [hb, hw]; exact item0)

-- [710155, '338bddfffff18206bd5830', 1, 'fd5b643b6f48'] hint 7.883905e-04 cost estimate 0.137606
noncomputable def box1 : Cell :=
  ⟨![(3545351/4096000 : ℚ), (207593/256000 : ℚ), (23/64 : ℚ), (0 : ℚ), (0 : ℚ), (63/128 : ℚ), (31/64 : ℚ), (255/512 : ℚ)],
    ![(1773/2048 : ℚ), (52109/64000 : ℚ), (93/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (1/2 : ℚ)]⟩
noncomputable def cert1 : PlanarAnchorCert where
  depth := 1
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(39768130711919/70368743798745 : ℚ), (8198269314472/14073748759749 : ℚ), (41109188628308/70368743798745 : ℚ)], ![(-58053902332808/70368743798745 : ℚ), (5612974577501/14073748759749 : ℚ), (28175653276444/70368743798745 : ℚ)], ![(3506713148/14073748759749 : ℚ), (-9967612592404/14073748759749 : ℚ), (9935647490891/14073748759749 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item1 : planarAnchorCertOk cert1 box1 ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] = true := by decide +kernel

theorem request1 (t : LatePackets.LateTables) (q : LatePackets.Request)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .planarAnchor)
    (hpay : q.proposal.payload = .optical .layered .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (1 : ℤ)]) (hb : q.target.box = box1)
    (ht : t.planarAnchor q = some cert1) : LatePackets.lateChecker t q = true :=
  LatePackets.lateChecker_planarAnchor t q half hint cert1 hq hpay ht (by rw [hb, hw]; exact item1)

-- [660673, '133bddeeeee99206bd5', 0, 'ed4b963ed12b47c9'] hint 8.258127e-04 cost estimate 0.101095
noncomputable def box2 : Cell :=
  ⟨![(441061/512000 : ℚ), (827/1024 : ℚ), (11/32 : ℚ), (1/128 : ℚ), (-1/128 : ℚ), (63/128 : ℚ), (63/128 : ℚ), (-1/2 : ℚ)],
    ![(221561/256000 : ℚ), (1661/2048 : ℚ), (45/128 : ℚ), (1/64 : ℚ), (0 : ℚ), (1/2 : ℚ), (127/256 : ℚ), (-255/512 : ℚ)]⟩
noncomputable def cert2 : PlanarAnchorCert where
  depth := 1
  k := (1/1099511627776 : ℚ)
  reg :=
    { B := ![![(1/2 : ℚ), (-1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (-1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(-1 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (-1/2 : ℚ), (1/2 : ℚ)]]
      U := ![![(80376335462437/140737482347589 : ℚ), (81334906513736/140737482347589 : ℚ), (82044601391984/140737482347589 : ℚ)], ![(-115527094961104/140737482347589 : ℚ), (56947710657292/140737482347589 : ℚ), (56722901180029/140737482347589 : ℚ)], ![(-417091136056/140737482347589 : ℚ), (-99742820146781/140737482347589 : ℚ), (99288643870732/140737482347589 : ℚ)]]
      f0 := ![(-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)]
      wrap := ![(1 : ℤ), (1 : ℤ), (1 : ℤ)] }
theorem item2 : planarAnchorCertOk cert2 box2 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request2 (t : LatePackets.LateTables) (q : LatePackets.Request)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .planarAnchor)
    (hpay : q.proposal.payload = .optical .layered .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box2)
    (ht : t.planarAnchor q = some cert2) : LatePackets.lateChecker t q = true :=
  LatePackets.lateChecker_planarAnchor t q half hint cert2 hq hpay ht (by rw [hb, hw]; exact item2)

end BccSharp.Coulomb.CompactCover.Layered.Pilot
