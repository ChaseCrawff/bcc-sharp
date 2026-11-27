import BccSharp.Cover.PlanarFibreTri

set_option autoImplicit false
set_option maxRecDepth 65536

/-! Generated. PlanarFibre triangular items in the kernel:
each `item_i` is a `decide +kernel` evaluation of `TriTree.ok` on the item's raw box.
Positions are ranks in recorded-margin order. `request_i` proves `planarFibreTriCheck t q = true`,
the check of the late checker's triangular family, for a triangular request whose table
entry and target box are these literals. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Sample
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

noncomputable def box0 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (5/128 : ℚ), (-1/128 : ℚ), (9/32 : ℚ), (3/8 : ℚ), (-1/2 : ℚ)], ![(7211/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (3/64 : ℚ), (0 : ℚ), (19/64 : ℚ), (25/64 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree0 : TriTree := (.leaf ![(14405/16384 : ℚ), (3217/4096 : ℚ), (121/256 : ℚ), (11/256 : ℚ), (-1/256 : ℚ), (37/128 : ℚ), (49/128 : ℚ), (65/128 : ℚ)])
theorem item0 : tree0.ok box0 = true := by decide +kernel
theorem request0 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree0) (hbox : q.target.box = box0) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree0 hpay ht (by rw [hbox]; exact item0)

noncomputable def box1 : Cell := ⟨![(3631/4096 : ℚ), (389/512 : ℚ), (63/128 : ℚ), (1/64 : ℚ), (-1/32 : ℚ), (19/64 : ℚ), (21/64 : ℚ), (-1/2 : ℚ)], ![(57/64 : ℚ), (785/1024 : ℚ), (1/2 : ℚ), (1/32 : ℚ), (-1/64 : ℚ), (5/16 : ℚ), (11/32 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree1 : TriTree := (.split 5 (.split 6 (.leaf ![(7279/8192 : ℚ), (1563/2048 : ℚ), (127/256 : ℚ), (3/128 : ℚ), (-3/128 : ℚ), (77/256 : ℚ), (85/256 : ℚ), (65/128 : ℚ)]) (.leaf ![(7279/8192 : ℚ), (1563/2048 : ℚ), (127/256 : ℚ), (3/128 : ℚ), (-3/128 : ℚ), (77/256 : ℚ), (87/256 : ℚ), (65/128 : ℚ)])) (.split 6 (.split 0 (.leaf ![(14541/16384 : ℚ), (1563/2048 : ℚ), (127/256 : ℚ), (3/128 : ℚ), (-3/128 : ℚ), (79/256 : ℚ), (85/256 : ℚ), (65/128 : ℚ)]) (.leaf ![(14575/16384 : ℚ), (1563/2048 : ℚ), (127/256 : ℚ), (3/128 : ℚ), (-3/128 : ℚ), (79/256 : ℚ), (85/256 : ℚ), (65/128 : ℚ)])) (.split 0 (.leaf ![(14541/16384 : ℚ), (1563/2048 : ℚ), (127/256 : ℚ), (3/128 : ℚ), (-3/128 : ℚ), (79/256 : ℚ), (87/256 : ℚ), (65/128 : ℚ)]) (.leaf ![(14575/16384 : ℚ), (1563/2048 : ℚ), (127/256 : ℚ), (3/128 : ℚ), (-3/128 : ℚ), (79/256 : ℚ), (87/256 : ℚ), (65/128 : ℚ)]))))
theorem item1 : tree1.ok box1 = true := by decide +kernel
theorem request1 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree1) (hbox : q.target.box = box1) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree1 hpay ht (by rw [hbox]; exact item1)

noncomputable def box2 : Cell := ⟨![(7245/8192 : ℚ), (799/1024 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (19/64 : ℚ), (31/64 : ℚ)], ![(3631/4096 : ℚ), (1605/2048 : ℚ), (31/64 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (23/64 : ℚ), (5/16 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree2 : TriTree := (.leaf ![(14507/16384 : ℚ), (3203/4096 : ℚ), (123/256 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (45/128 : ℚ), (39/128 : ℚ), (63/128 : ℚ)])
theorem item2 : tree2.ok box2 = true := by decide +kernel
theorem request2 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree2) (hbox : q.target.box = box2) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree2 hpay ht (by rw [hbox]; exact item2)

noncomputable def box3 : Cell := ⟨![(7211/8192 : ℚ), (799/1024 : ℚ), (31/64 : ℚ), (0 : ℚ), (-3/128 : ℚ), (9/32 : ℚ), (3/8 : ℚ), (-1/2 : ℚ)], ![(1807/2048 : ℚ), (1605/2048 : ℚ), (63/128 : ℚ), (1/128 : ℚ), (-1/64 : ℚ), (19/64 : ℚ), (25/64 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree3 : TriTree := (.leaf ![(14439/16384 : ℚ), (3203/4096 : ℚ), (125/256 : ℚ), (1/256 : ℚ), (-5/256 : ℚ), (37/128 : ℚ), (49/128 : ℚ), (65/128 : ℚ)])
theorem item3 : tree3.ok box3 = true := by decide +kernel
theorem request3 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree3) (hbox : q.target.box = box3) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree3 hpay ht (by rw [hbox]; exact item3)

noncomputable def box4 : Cell := ⟨![(3631/4096 : ℚ), (785/1024 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (-3/128 : ℚ), (23/64 : ℚ), (19/64 : ℚ), (-1/2 : ℚ)], ![(7279/8192 : ℚ), (1577/2048 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (-1/64 : ℚ), (3/8 : ℚ), (5/16 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree4 : TriTree := (.leaf ![(14541/16384 : ℚ), (3147/4096 : ℚ), (121/256 : ℚ), (3/256 : ℚ), (-5/256 : ℚ), (47/128 : ℚ), (39/128 : ℚ), (65/128 : ℚ)])
theorem item4 : tree4.ok box4 = true := by decide +kernel
theorem request4 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree4) (hbox : q.target.box = box4) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree4 hpay ht (by rw [hbox]; exact item4)

noncomputable def box5 : Cell := ⟨![(3597/4096 : ℚ), (99/128 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (-1/64 : ℚ), (11/32 : ℚ), (19/64 : ℚ), (31/64 : ℚ)], ![(7211/8192 : ℚ), (1591/2048 : ℚ), (61/128 : ℚ), (3/128 : ℚ), (-1/128 : ℚ), (23/64 : ℚ), (5/16 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree5 : TriTree := (.leaf ![(14405/16384 : ℚ), (3175/4096 : ℚ), (121/256 : ℚ), (5/256 : ℚ), (-3/256 : ℚ), (45/128 : ℚ), (39/128 : ℚ), (63/128 : ℚ)])
theorem item5 : tree5.ok box5 = true := by decide +kernel
theorem request5 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree5) (hbox : q.target.box = box5) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree5 hpay ht (by rw [hbox]; exact item5)

noncomputable def box6 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (63/128 : ℚ), (1/16 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (21/64 : ℚ), (-1/2 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (1/2 : ℚ), (5/64 : ℚ), (1/32 : ℚ), (23/64 : ℚ), (11/32 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree6 : TriTree := (.leaf ![(7177/8192 : ℚ), (3217/4096 : ℚ), (127/256 : ℚ), (9/128 : ℚ), (3/128 : ℚ), (45/128 : ℚ), (43/128 : ℚ), (65/128 : ℚ)])
theorem item6 : tree6.ok box6 = true := by decide +kernel
theorem request6 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree6) (hbox : q.target.box = box6) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree6 hpay ht (by rw [hbox]; exact item6)

noncomputable def box7 : Cell := ⟨![(3631/4096 : ℚ), (1563/2048 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (-3/64 : ℚ), (21/64 : ℚ), (5/16 : ℚ), (-1/2 : ℚ)], ![(57/64 : ℚ), (785/1024 : ℚ), (31/64 : ℚ), (1/32 : ℚ), (-1/32 : ℚ), (11/32 : ℚ), (21/64 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree7 : TriTree := (.split 5 (.leaf ![(7279/8192 : ℚ), (3133/4096 : ℚ), (123/256 : ℚ), (3/128 : ℚ), (-5/128 : ℚ), (85/256 : ℚ), (41/128 : ℚ), (65/128 : ℚ)]) (.leaf ![(7279/8192 : ℚ), (3133/4096 : ℚ), (123/256 : ℚ), (3/128 : ℚ), (-5/128 : ℚ), (87/256 : ℚ), (41/128 : ℚ), (65/128 : ℚ)]))
theorem item7 : tree7.ok box7 = true := by decide +kernel
theorem request7 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree7) (hbox : q.target.box = box7) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree7 hpay ht (by rw [hbox]; exact item7)

noncomputable def box8 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (63/128 : ℚ), (1/16 : ℚ), (1/64 : ℚ), (21/64 : ℚ), (21/64 : ℚ), (-1/2 : ℚ)], ![(1807/2048 : ℚ), (403/512 : ℚ), (1/2 : ℚ), (5/64 : ℚ), (1/32 : ℚ), (11/32 : ℚ), (11/32 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree8 : TriTree := (.leaf ![(7211/8192 : ℚ), (3217/4096 : ℚ), (127/256 : ℚ), (9/128 : ℚ), (3/128 : ℚ), (43/128 : ℚ), (43/128 : ℚ), (65/128 : ℚ)])
theorem item8 : tree8.ok box8 = true := by decide +kernel
theorem request8 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree8) (hbox : q.target.box = box8) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree8 hpay ht (by rw [hbox]; exact item8)

noncomputable def box9 : Cell := ⟨![(895/1024 : ℚ), (389/512 : ℚ), (31/64 : ℚ), (1/64 : ℚ), (-1/32 : ℚ), (23/64 : ℚ), (21/64 : ℚ), (-1/2 : ℚ)], ![(3597/4096 : ℚ), (785/1024 : ℚ), (1/2 : ℚ), (1/32 : ℚ), (-1/64 : ℚ), (3/8 : ℚ), (11/32 : ℚ), (-31/64 : ℚ)]⟩
noncomputable def tree9 : TriTree := (.leaf ![(7177/8192 : ℚ), (1563/2048 : ℚ), (63/128 : ℚ), (3/128 : ℚ), (-3/128 : ℚ), (47/128 : ℚ), (43/128 : ℚ), (65/128 : ℚ)])
theorem item9 : tree9.ok box9 = true := by decide +kernel
theorem request9 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree9) (hbox : q.target.box = box9) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree9 hpay ht (by rw [hbox]; exact item9)

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Sample
