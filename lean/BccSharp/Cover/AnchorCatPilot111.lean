import BccSharp.Cover.LayeredCatRoute

/-! # HalfShift relative items whose anchor has no registration, in the kernel

Certificates for single HalfShift relative boxes (half bits 111) whose all-half
anchor has no BCC registration of cost below one: `decide +kernel` checks
`Layered.planarAnchorCertOkCat` (the gain check with penalty 0 and the catalogue check
`catalogueOk`). Generated; the boxes are the
Stage6 atoms of the Corner jobs (geometry folder `cornerRule`) named in the comments. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.Layered
open BccSharp.Coulomb

namespace BccSharp.Coulomb.CompactCover.Layered.CatPilot111

noncomputable def box0 : Cell :=
  ⟨![(895/1024 : ℚ), (785/1024 : ℚ), (15/32 : ℚ), (15/32 : ℚ), (9/32 : ℚ), (31/64 : ℚ), (-31/64 : ℚ), (-1/2 : ℚ)],
    ![(1807/2048 : ℚ), (99/128 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (5/16 : ℚ), (1/2 : ℚ), (-15/32 : ℚ), (-63/128 : ℚ)]⟩
theorem item0 : planarAnchorCertOkCat (catCert 0 (1/1099511627776 : ℚ)) box0 ![(1 : ℤ), (0 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request0 (table : LatePackets.Request → Option PlanarAnchorCert) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (0 : ℤ), (0 : ℤ)]) (hb : q.target.box = box0)
    (ht : table q = some (catCert 0 (1/1099511627776 : ℚ))) : halfShiftCheckCat table q = true :=
  halfShiftCheckCat_accept table q s half hint _ hq hpay ht (by rw [hb, hw]; exact item0)

noncomputable def box1 : Cell :=
  ⟨![(895/1024 : ℚ), (785/1024 : ℚ), (15/32 : ℚ), (15/32 : ℚ), (9/32 : ℚ), (15/32 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)],
    ![(1807/2048 : ℚ), (99/128 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (5/16 : ℚ), (31/64 : ℚ), (-31/64 : ℚ), (-63/128 : ℚ)]⟩
theorem item1 : planarAnchorCertOkCat (catCert 0 (1/1099511627776 : ℚ)) box1 ![(1 : ℤ), (0 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request1 (table : LatePackets.Request → Option PlanarAnchorCert) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (0 : ℤ), (0 : ℤ)]) (hb : q.target.box = box1)
    (ht : table q = some (catCert 0 (1/1099511627776 : ℚ))) : halfShiftCheckCat table q = true :=
  halfShiftCheckCat_accept table q s half hint _ hq hpay ht (by rw [hb, hw]; exact item1)

noncomputable def box2 : Cell :=
  ⟨![(1807/2048 : ℚ), (785/1024 : ℚ), (31/64 : ℚ), (15/32 : ℚ), (23/64 : ℚ), (31/64 : ℚ), (31/64 : ℚ), (-1/2 : ℚ)],
    ![(57/64 : ℚ), (99/128 : ℚ), (1/2 : ℚ), (31/64 : ℚ), (3/8 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (-31/64 : ℚ)]⟩
theorem item2 : planarAnchorCertOkCat (catCert 0 (1/1099511627776 : ℚ)) box2 ![(1 : ℤ), (1 : ℤ), (0 : ℤ)] = true := by decide +kernel

theorem request2 (table : LatePackets.Request → Option PlanarAnchorCert) (q : LatePackets.Request) (s : ℕ)
    (half : LatePackets.HalfWitness) (hint : ℚ) (hq : q.packet = .halfShift)
    (hpay : q.proposal.payload = .optical (.transport s) .basin half hint)
    (hw : half.wrap = ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]) (hb : q.target.box = box2)
    (ht : table q = some (catCert 0 (1/1099511627776 : ℚ))) : halfShiftCheckCat table q = true :=
  halfShiftCheckCat_accept table q s half hint _ hq hpay ht (by rw [hb, hw]; exact item2)

end BccSharp.Coulomb.CompactCover.Layered.CatPilot111
