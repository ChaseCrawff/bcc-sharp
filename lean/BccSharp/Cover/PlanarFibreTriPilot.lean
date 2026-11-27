import BccSharp.Cover.PlanarFibreTri

set_option autoImplicit false
set_option maxRecDepth 65536

/-! Generated. PlanarFibre triangular items in the kernel:
each `item_i` is a `decide +kernel` evaluation of `TriTree.ok` on the item's raw box.
Positions are ranks in recorded-margin order. `request_i` proves `planarFibreTriCheck t q = true`,
the check of the late checker's triangular family, for a triangular request whose table
entry and target box are these literals. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Pilot
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

noncomputable def box0 : Cell := ⟨![(1807/2048 : ℚ), (1591/2048 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (-1/128 : ℚ), (9/32 : ℚ), (3/8 : ℚ), (-1/2 : ℚ)], ![(7245/8192 : ℚ), (799/1024 : ℚ), (31/64 : ℚ), (1/64 : ℚ), (0 : ℚ), (19/64 : ℚ), (25/64 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree0 : TriTree := (.leaf ![(14473/16384 : ℚ), (3189/4096 : ℚ), (123/256 : ℚ), (3/256 : ℚ), (-1/256 : ℚ), (37/128 : ℚ), (49/128 : ℚ), (65/128 : ℚ)])
theorem item0 : tree0.ok box0 = true := by decide +kernel
theorem request0 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree0) (hbox : q.target.box = box0) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree0 hpay ht (by rw [hbox]; exact item0)

noncomputable def box1 : Cell := ⟨![(1807/2048 : ℚ), (1591/2048 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (-1/128 : ℚ), (19/64 : ℚ), (3/8 : ℚ), (-1/2 : ℚ)], ![(7245/8192 : ℚ), (799/1024 : ℚ), (31/64 : ℚ), (1/64 : ℚ), (0 : ℚ), (5/16 : ℚ), (25/64 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree1 : TriTree := (.leaf ![(14473/16384 : ℚ), (3189/4096 : ℚ), (123/256 : ℚ), (3/256 : ℚ), (-1/256 : ℚ), (39/128 : ℚ), (49/128 : ℚ), (65/128 : ℚ)])
theorem item1 : tree1.ok box1 = true := by decide +kernel
theorem request1 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree1) (hbox : q.target.box = box1) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree1 hpay ht (by rw [hbox]; exact item1)

noncomputable def box2 : Cell := ⟨![(1807/2048 : ℚ), (1591/2048 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (-1/128 : ℚ), (19/64 : ℚ), (11/32 : ℚ), (-1/2 : ℚ)], ![(7245/8192 : ℚ), (799/1024 : ℚ), (31/64 : ℚ), (1/64 : ℚ), (0 : ℚ), (5/16 : ℚ), (23/64 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree2 : TriTree := (.leaf ![(14473/16384 : ℚ), (3189/4096 : ℚ), (123/256 : ℚ), (3/256 : ℚ), (-1/256 : ℚ), (39/128 : ℚ), (45/128 : ℚ), (65/128 : ℚ)])
theorem item2 : tree2.ok box2 = true := by decide +kernel
theorem request2 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree2) (hbox : q.target.box = box2) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree2 hpay ht (by rw [hbox]; exact item2)

noncomputable def box3 : Cell := ⟨![(3597/4096 : ℚ), (799/1024 : ℚ), (63/128 : ℚ), (3/64 : ℚ), (1/64 : ℚ), (19/64 : ℚ), (21/64 : ℚ), (-1/2 : ℚ)], ![(1807/2048 : ℚ), (1605/2048 : ℚ), (1/2 : ℚ), (1/16 : ℚ), (1/32 : ℚ), (5/16 : ℚ), (11/32 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree3 : TriTree := (.leaf ![(7211/8192 : ℚ), (3203/4096 : ℚ), (127/256 : ℚ), (7/128 : ℚ), (3/128 : ℚ), (39/128 : ℚ), (43/128 : ℚ), (65/128 : ℚ)])
theorem item3 : tree3.ok box3 = true := by decide +kernel
theorem request3 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree3) (hbox : q.target.box = box3) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree3 hpay ht (by rw [hbox]; exact item3)

noncomputable def box4 : Cell := ⟨![(1807/2048 : ℚ), (389/512 : ℚ), (61/128 : ℚ), (0 : ℚ), (-3/64 : ℚ), (5/16 : ℚ), (21/64 : ℚ), (-1/2 : ℚ)], ![(3631/4096 : ℚ), (785/1024 : ℚ), (31/64 : ℚ), (1/64 : ℚ), (-1/32 : ℚ), (21/64 : ℚ), (11/32 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree4 : TriTree := (.leaf ![(7245/8192 : ℚ), (1563/2048 : ℚ), (123/256 : ℚ), (1/128 : ℚ), (-5/128 : ℚ), (41/128 : ℚ), (43/128 : ℚ), (65/128 : ℚ)])
theorem item4 : tree4.ok box4 = true := by decide +kernel
theorem request4 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree4) (hbox : q.target.box = box4) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree4 hpay ht (by rw [hbox]; exact item4)

noncomputable def box5 : Cell := ⟨![(1807/2048 : ℚ), (99/128 : ℚ), (31/64 : ℚ), (1/16 : ℚ), (-1/64 : ℚ), (21/64 : ℚ), (21/64 : ℚ), (31/64 : ℚ)], ![(3631/4096 : ℚ), (799/1024 : ℚ), (63/128 : ℚ), (5/64 : ℚ), (0 : ℚ), (11/32 : ℚ), (11/32 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree5 : TriTree := (.split 5 (.leaf ![(7245/8192 : ℚ), (1591/2048 : ℚ), (125/256 : ℚ), (9/128 : ℚ), (-1/128 : ℚ), (85/256 : ℚ), (43/128 : ℚ), (63/128 : ℚ)]) (.leaf ![(7245/8192 : ℚ), (1591/2048 : ℚ), (125/256 : ℚ), (9/128 : ℚ), (-1/128 : ℚ), (87/256 : ℚ), (43/128 : ℚ), (63/128 : ℚ)]))
theorem item5 : tree5.ok box5 = true := by decide +kernel
theorem request5 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree5) (hbox : q.target.box = box5) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree5 hpay ht (by rw [hbox]; exact item5)

noncomputable def box6 : Cell := ⟨![(1807/2048 : ℚ), (389/512 : ℚ), (31/64 : ℚ), (0 : ℚ), (-5/64 : ℚ), (21/64 : ℚ), (21/64 : ℚ), (-1/2 : ℚ)], ![(3631/4096 : ℚ), (785/1024 : ℚ), (1/2 : ℚ), (1/64 : ℚ), (-1/16 : ℚ), (11/32 : ℚ), (11/32 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree6 : TriTree := (.split 5 (.split 6 (.leaf ![(7245/8192 : ℚ), (1563/2048 : ℚ), (63/128 : ℚ), (1/128 : ℚ), (-9/128 : ℚ), (85/256 : ℚ), (85/256 : ℚ), (65/128 : ℚ)]) (.leaf ![(7245/8192 : ℚ), (1563/2048 : ℚ), (63/128 : ℚ), (1/128 : ℚ), (-9/128 : ℚ), (85/256 : ℚ), (87/256 : ℚ), (65/128 : ℚ)])) (.leaf ![(7245/8192 : ℚ), (1563/2048 : ℚ), (63/128 : ℚ), (1/128 : ℚ), (-9/128 : ℚ), (87/256 : ℚ), (43/128 : ℚ), (65/128 : ℚ)]))
theorem item6 : tree6.ok box6 = true := by decide +kernel
theorem request6 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree6) (hbox : q.target.box = box6) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree6 hpay ht (by rw [hbox]; exact item6)

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Pilot
