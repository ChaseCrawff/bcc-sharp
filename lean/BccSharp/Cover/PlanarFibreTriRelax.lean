import BccSharp.Cover.PlanarFibreTri

set_option autoImplicit false
set_option maxRecDepth 65536
set_option Elab.async false

/-! Generated. PlanarFibre triangular items in the kernel:
each `item_i` is a `decide +kernel` evaluation of `TriTree.ok` on the item's raw box.
Positions are ranks in recorded-margin order. `request_i` proves `planarFibreTriCheck t q = true`,
the check of the late checker's triangular family, for a triangular request whose table
entry and target box are these literals.
`Elab.async false` checks the theorems one at a time. -/

namespace BccSharp.Coulomb.CompactCover.PlanarFibreTri.Relax
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.PlanarFibreTri

noncomputable def box0 : Cell := ⟨![(3631/4096 : ℚ), (1577/2048 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (-1/64 : ℚ), (11/32 : ℚ), (11/32 : ℚ), (63/128 : ℚ)], ![(7279/8192 : ℚ), (99/128 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (-1/128 : ℚ), (45/128 : ℚ), (23/64 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree0 : TriTree := (.leaf ![(14541/16384 : ℚ), (3161/4096 : ℚ), (121/256 : ℚ), (3/256 : ℚ), (-3/256 : ℚ), (89/256 : ℚ), (45/128 : ℚ), (127/256 : ℚ)])
theorem item0 : tree0.ok box0 = true := by decide +kernel
theorem request0 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree0) (hbox : q.target.box = box0) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree0 hpay ht (by rw [hbox]; exact item0)

noncomputable def box1 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree1 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item1 : tree1.ok box1 = true := by decide +kernel
theorem request1 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree1) (hbox : q.target.box = box1) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree1 hpay ht (by rw [hbox]; exact item1)

noncomputable def box2 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree2 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item2 : tree2.ok box2 = true := by decide +kernel
theorem request2 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree2) (hbox : q.target.box = box2) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree2 hpay ht (by rw [hbox]; exact item2)

noncomputable def box3 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree3 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item3 : tree3.ok box3 = true := by decide +kernel
theorem request3 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree3) (hbox : q.target.box = box3) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree3 hpay ht (by rw [hbox]; exact item3)

noncomputable def box4 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree4 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item4 : tree4.ok box4 = true := by decide +kernel
theorem request4 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree4) (hbox : q.target.box = box4) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree4 hpay ht (by rw [hbox]; exact item4)

noncomputable def box5 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree5 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item5 : tree5.ok box5 = true := by decide +kernel
theorem request5 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree5) (hbox : q.target.box = box5) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree5 hpay ht (by rw [hbox]; exact item5)

noncomputable def box6 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree6 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item6 : tree6.ok box6 = true := by decide +kernel
theorem request6 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree6) (hbox : q.target.box = box6) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree6 hpay ht (by rw [hbox]; exact item6)

noncomputable def box7 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree7 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item7 : tree7.ok box7 = true := by decide +kernel
theorem request7 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree7) (hbox : q.target.box = box7) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree7 hpay ht (by rw [hbox]; exact item7)

noncomputable def box8 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/32 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree8 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (7/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item8 : tree8.ok box8 = true := by decide +kernel
theorem request8 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree8) (hbox : q.target.box = box8) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree8 hpay ht (by rw [hbox]; exact item8)

noncomputable def box9 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree9 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item9 : tree9.ok box9 = true := by decide +kernel
theorem request9 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree9) (hbox : q.target.box = box9) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree9 hpay ht (by rw [hbox]; exact item9)

noncomputable def box10 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree10 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item10 : tree10.ok box10 = true := by decide +kernel
theorem request10 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree10) (hbox : q.target.box = box10) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree10 hpay ht (by rw [hbox]; exact item10)

noncomputable def box11 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree11 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item11 : tree11.ok box11 = true := by decide +kernel
theorem request11 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree11) (hbox : q.target.box = box11) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree11 hpay ht (by rw [hbox]; exact item11)

noncomputable def box12 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree12 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item12 : tree12.ok box12 = true := by decide +kernel
theorem request12 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree12) (hbox : q.target.box = box12) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree12 hpay ht (by rw [hbox]; exact item12)

noncomputable def box13 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7211/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree13 : TriTree := (.leaf ![(14405/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item13 : tree13.ok box13 = true := by decide +kernel
theorem request13 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree13) (hbox : q.target.box = box13) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree13 hpay ht (by rw [hbox]; exact item13)

noncomputable def box14 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree14 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item14 : tree14.ok box14 = true := by decide +kernel
theorem request14 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree14) (hbox : q.target.box = box14) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree14 hpay ht (by rw [hbox]; exact item14)

noncomputable def box15 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (3/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/32 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree15 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (7/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item15 : tree15.ok box15 = true := by decide +kernel
theorem request15 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree15) (hbox : q.target.box = box15) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree15 hpay ht (by rw [hbox]; exact item15)

noncomputable def box16 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7211/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree16 : TriTree := (.leaf ![(14405/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item16 : tree16.ok box16 = true := by decide +kernel
theorem request16 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree16) (hbox : q.target.box = box16) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree16 hpay ht (by rw [hbox]; exact item16)

noncomputable def box17 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7211/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree17 : TriTree := (.leaf ![(14405/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item17 : tree17.ok box17 = true := by decide +kernel
theorem request17 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree17) (hbox : q.target.box = box17) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree17 hpay ht (by rw [hbox]; exact item17)

noncomputable def box18 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree18 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item18 : tree18.ok box18 = true := by decide +kernel
theorem request18 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree18) (hbox : q.target.box = box18) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree18 hpay ht (by rw [hbox]; exact item18)

noncomputable def box19 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/32 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree19 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (7/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item19 : tree19.ok box19 = true := by decide +kernel
theorem request19 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree19) (hbox : q.target.box = box19) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree19 hpay ht (by rw [hbox]; exact item19)

noncomputable def box20 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree20 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item20 : tree20.ok box20 = true := by decide +kernel
theorem request20 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree20) (hbox : q.target.box = box20) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree20 hpay ht (by rw [hbox]; exact item20)

noncomputable def box21 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7211/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree21 : TriTree := (.leaf ![(14405/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item21 : tree21.ok box21 = true := by decide +kernel
theorem request21 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree21) (hbox : q.target.box = box21) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree21 hpay ht (by rw [hbox]; exact item21)

noncomputable def box22 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7211/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree22 : TriTree := (.leaf ![(14405/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item22 : tree22.ok box22 = true := by decide +kernel
theorem request22 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree22) (hbox : q.target.box = box22) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree22 hpay ht (by rw [hbox]; exact item22)

noncomputable def box23 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree23 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item23 : tree23.ok box23 = true := by decide +kernel
theorem request23 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree23) (hbox : q.target.box = box23) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree23 hpay ht (by rw [hbox]; exact item23)

noncomputable def box24 : Cell := ⟨![(3597/4096 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7211/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree24 : TriTree := (.leaf ![(14405/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item24 : tree24.ok box24 = true := by decide +kernel
theorem request24 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree24) (hbox : q.target.box = box24) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree24 hpay ht (by rw [hbox]; exact item24)

noncomputable def box25 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree25 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item25 : tree25.ok box25 = true := by decide +kernel
theorem request25 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree25) (hbox : q.target.box = box25) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree25 hpay ht (by rw [hbox]; exact item25)

noncomputable def box26 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree26 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item26 : tree26.ok box26 = true := by decide +kernel
theorem request26 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree26) (hbox : q.target.box = box26) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree26 hpay ht (by rw [hbox]; exact item26)

noncomputable def box27 : Cell := ⟨![(7177/8192 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree27 : TriTree := (.leaf ![(14371/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item27 : tree27.ok box27 = true := by decide +kernel
theorem request27 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree27) (hbox : q.target.box = box27) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree27 hpay ht (by rw [hbox]; exact item27)

noncomputable def box28 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree28 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item28 : tree28.ok box28 = true := by decide +kernel
theorem request28 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree28) (hbox : q.target.box = box28) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree28 hpay ht (by rw [hbox]; exact item28)

noncomputable def box29 : Cell := ⟨![(7177/8192 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree29 : TriTree := (.leaf ![(14371/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item29 : tree29.ok box29 = true := by decide +kernel
theorem request29 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree29) (hbox : q.target.box = box29) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree29 hpay ht (by rw [hbox]; exact item29)

noncomputable def box30 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (15/32 : ℚ), (3/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (121/256 : ℚ), (1/32 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree30 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (241/512 : ℚ), (7/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item30 : tree30.ok box30 = true := by decide +kernel
theorem request30 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree30) (hbox : q.target.box = box30) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree30 hpay ht (by rw [hbox]; exact item30)

noncomputable def box31 : Cell := ⟨![(7177/8192 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree31 : TriTree := (.leaf ![(14371/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item31 : tree31.ok box31 = true := by decide +kernel
theorem request31 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree31) (hbox : q.target.box = box31) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree31 hpay ht (by rw [hbox]; exact item31)

noncomputable def box32 : Cell := ⟨![(7177/8192 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree32 : TriTree := (.leaf ![(14371/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item32 : tree32.ok box32 = true := by decide +kernel
theorem request32 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree32) (hbox : q.target.box = box32) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree32 hpay ht (by rw [hbox]; exact item32)

noncomputable def box33 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree33 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item33 : tree33.ok box33 = true := by decide +kernel
theorem request33 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree33) (hbox : q.target.box = box33) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree33 hpay ht (by rw [hbox]; exact item33)

noncomputable def box34 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree34 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item34 : tree34.ok box34 = true := by decide +kernel
theorem request34 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree34) (hbox : q.target.box = box34) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree34 hpay ht (by rw [hbox]; exact item34)

noncomputable def box35 : Cell := ⟨![(7177/8192 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree35 : TriTree := (.leaf ![(14371/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item35 : tree35.ok box35 = true := by decide +kernel
theorem request35 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree35) (hbox : q.target.box = box35) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree35 hpay ht (by rw [hbox]; exact item35)

noncomputable def box36 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree36 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item36 : tree36.ok box36 = true := by decide +kernel
theorem request36 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree36) (hbox : q.target.box = box36) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree36 hpay ht (by rw [hbox]; exact item36)

noncomputable def box37 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/32 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree37 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (7/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item37 : tree37.ok box37 = true := by decide +kernel
theorem request37 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree37) (hbox : q.target.box = box37) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree37 hpay ht (by rw [hbox]; exact item37)

noncomputable def box38 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree38 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item38 : tree38.ok box38 = true := by decide +kernel
theorem request38 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree38) (hbox : q.target.box = box38) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree38 hpay ht (by rw [hbox]; exact item38)

noncomputable def box39 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree39 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item39 : tree39.ok box39 = true := by decide +kernel
theorem request39 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree39) (hbox : q.target.box = box39) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree39 hpay ht (by rw [hbox]; exact item39)

noncomputable def box40 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree40 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item40 : tree40.ok box40 = true := by decide +kernel
theorem request40 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree40) (hbox : q.target.box = box40) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree40 hpay ht (by rw [hbox]; exact item40)

noncomputable def box41 : Cell := ⟨![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(3597/4096 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/32 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree41 : TriTree := (.leaf ![(14371/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (7/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item41 : tree41.ok box41 = true := by decide +kernel
theorem request41 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree41) (hbox : q.target.box = box41) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree41 hpay ht (by rw [hbox]; exact item41)

noncomputable def box42 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/32 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree42 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (7/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item42 : tree42.ok box42 = true := by decide +kernel
theorem request42 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree42) (hbox : q.target.box = box42) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree42 hpay ht (by rw [hbox]; exact item42)

noncomputable def box43 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (61/128 : ℚ), (1/32 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree43 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (243/512 : ℚ), (7/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item43 : tree43.ok box43 = true := by decide +kernel
theorem request43 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree43) (hbox : q.target.box = box43) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree43 hpay ht (by rw [hbox]; exact item43)

noncomputable def box44 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (123/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree44 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (245/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item44 : tree44.ok box44 = true := by decide +kernel
theorem request44 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree44) (hbox : q.target.box = box44) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree44 hpay ht (by rw [hbox]; exact item44)

noncomputable def box45 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (61/128 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (123/256 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree45 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (245/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item45 : tree45.ok box45 = true := by decide +kernel
theorem request45 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree45) (hbox : q.target.box = box45) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree45 hpay ht (by rw [hbox]; exact item45)

noncomputable def box46 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (61/128 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (123/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree46 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (245/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item46 : tree46.ok box46 = true := by decide +kernel
theorem request46 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree46) (hbox : q.target.box = box46) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree46 hpay ht (by rw [hbox]; exact item46)

noncomputable def box47 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (123/256 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree47 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (245/512 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item47 : tree47.ok box47 = true := by decide +kernel
theorem request47 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree47) (hbox : q.target.box = box47) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree47 hpay ht (by rw [hbox]; exact item47)

noncomputable def box48 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (61/128 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (123/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree48 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (245/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item48 : tree48.ok box48 = true := by decide +kernel
theorem request48 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree48) (hbox : q.target.box = box48) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree48 hpay ht (by rw [hbox]; exact item48)

noncomputable def box49 : Cell := ⟨![(895/1024 : ℚ), (1605/2048 : ℚ), (61/128 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (403/512 : ℚ), (123/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree49 : TriTree := (.leaf ![(14337/16384 : ℚ), (3217/4096 : ℚ), (245/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item49 : tree49.ok box49 = true := by decide +kernel
theorem request49 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree49) (hbox : q.target.box = box49) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree49 hpay ht (by rw [hbox]; exact item49)

noncomputable def box50 : Cell := ⟨![(895/1024 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree50 : TriTree := (.leaf ![(14337/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item50 : tree50.ok box50 = true := by decide +kernel
theorem request50 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree50) (hbox : q.target.box = box50) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree50 hpay ht (by rw [hbox]; exact item50)

noncomputable def box51 : Cell := ⟨![(895/1024 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (1/128 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree51 : TriTree := (.leaf ![(14337/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (3/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item51 : tree51.ok box51 = true := by decide +kernel
theorem request51 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree51) (hbox : q.target.box = box51) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree51 hpay ht (by rw [hbox]; exact item51)

noncomputable def box52 : Cell := ⟨![(895/1024 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree52 : TriTree := (.leaf ![(14337/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item52 : tree52.ok box52 = true := by decide +kernel
theorem request52 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree52) (hbox : q.target.box = box52) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree52 hpay ht (by rw [hbox]; exact item52)

noncomputable def box53 : Cell := ⟨![(895/1024 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (0 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree53 : TriTree := (.leaf ![(14337/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item53 : tree53.ok box53 = true := by decide +kernel
theorem request53 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree53) (hbox : q.target.box = box53) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree53 hpay ht (by rw [hbox]; exact item53)

noncomputable def box54 : Cell := ⟨![(895/1024 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (0 : ℚ), (1/128 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (1/128 : ℚ), (1/64 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree54 : TriTree := (.leaf ![(14337/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (1/256 : ℚ), (3/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item54 : tree54.ok box54 = true := by decide +kernel
theorem request54 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree54) (hbox : q.target.box = box54) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree54 hpay ht (by rw [hbox]; exact item54)

noncomputable def box55 : Cell := ⟨![(895/1024 : ℚ), (799/1024 : ℚ), (15/32 : ℚ), (1/64 : ℚ), (0 : ℚ), (21/64 : ℚ), (23/64 : ℚ), (63/128 : ℚ)], ![(7177/8192 : ℚ), (1605/2048 : ℚ), (121/256 : ℚ), (3/128 : ℚ), (1/128 : ℚ), (11/32 : ℚ), (3/8 : ℚ), (1/2 : ℚ)]⟩
noncomputable def tree55 : TriTree := (.leaf ![(14337/16384 : ℚ), (3203/4096 : ℚ), (241/512 : ℚ), (5/256 : ℚ), (1/256 : ℚ), (43/128 : ℚ), (47/128 : ℚ), (127/256 : ℚ)])
theorem item55 : tree55.ok box55 = true := by decide +kernel
theorem request55 (t : LatePackets.Request → Option TriTree) (q : LatePackets.Request)
    (radius hint : ℚ) (hpay : q.proposal.payload = .triangular radius hint)
    (ht : t q = some tree55) (hbox : q.target.box = box55) : planarFibreTriCheck t q = true :=
  planarFibreTriCheck_of t q radius hint tree55 hpay ht (by rw [hbox]; exact item55)

end BccSharp.Coulomb.CompactCover.PlanarFibreTri.Relax
