import BccSharp.Cover.DirectFixSound

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-! Generated. The Direct pilot: original archive
leaves of the frontier
(`energy_direct` and `energy_above_fcc`, paid by the fixed-point direct check
`DirectFix.directFix`; `invalid_reduced`, paid by the existing
`compactReductionCheck`), each bound to the Direct root by its split digits. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.PrefixItems.Direct
open BccSharp BccSharp.Coverage

noncomputable def box_18327 : Cell :=
  ⟨![57/64, 23/32, 1/4, 0, (-1/4 : ℚ), 0, 0, (-1/4 : ℚ)],
    ![245/256, 15/16, 3/8, 1/8, 0, 1/4, 1/4, 0]⟩

theorem addr_18327 : box_18327 = OverlayPlanar.descend CompactCover.root [1, 2, 5, 6, 8, 11, 13, 14, 0, 3, 4, 6, 9, 10, 12, 15, 0] :=
  sameCell_sound (by decide +kernel)

theorem check_18327 : DirectFix.directFix box_18327 = true := by decide +kernel

theorem strict_18327 (p : Chart) (hp : box_18327.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_18327 hp hv

noncomputable def box_17996 : Cell :=
  ⟨![57/64, 23/32, 1/4, 0, (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), 0],
    ![245/256, 15/16, 3/8, 1/8, 0, 0, 0, 1/4]⟩

theorem addr_17996 : box_17996 = OverlayPlanar.descend CompactCover.root [1, 2, 5, 6, 8, 10, 12, 15, 0, 3, 4, 6, 9, 11, 13, 14, 0] :=
  sameCell_sound (by decide +kernel)

theorem check_17996 : DirectFix.directFix box_17996 = true := by decide +kernel

theorem strict_17996 (p : Chart) (hp : box_17996.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_17996 hp hv

noncomputable def box_17613 : Cell :=
  ⟨![245/256, 23/32, 1/8, 3/8, (-1/4 : ℚ), 0, 0, (-1/4 : ℚ)],
    ![131/128, 15/16, 1/4, 1/2, 0, 1/4, 1/4, 0]⟩

theorem addr_17613 : box_17613 = OverlayPlanar.descend CompactCover.root [1, 2, 4, 7, 8, 11, 13, 14, 0, 3, 5, 7, 9, 10, 12, 15, 1] :=
  sameCell_sound (by decide +kernel)

theorem check_17613 : DirectFix.directFix box_17613 = true := by decide +kernel

theorem strict_17613 (p : Chart) (hp : box_17613.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_17613 hp hv

noncomputable def box_17451 : Cell :=
  ⟨![245/256, 23/32, 1/8, 3/8, (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), 0],
    ![131/128, 15/16, 1/4, 1/2, 0, 0, 0, 1/4]⟩

theorem addr_17451 : box_17451 = OverlayPlanar.descend CompactCover.root [1, 2, 4, 7, 8, 10, 12, 15, 0, 3, 5, 7, 9, 11, 13, 14, 1] :=
  sameCell_sound (by decide +kernel)

theorem check_17451 : DirectFix.directFix box_17451 = true := by decide +kernel

theorem strict_17451 (p : Chart) (hp : box_17451.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_17451 hp hv

noncomputable def box_16322 : Cell :=
  ⟨![5/8, 37/32, 1/4, 3/8, 0, (-1/4 : ℚ), (-1/4 : ℚ), 1/4],
    ![177/256, 11/8, 3/8, 1/2, 1/4, 0, 0, 1/2]⟩

theorem addr_16322 : box_16322 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 7, 9, 10, 12, 15, 0, 3, 4, 7, 8, 11, 13, 15, 0] :=
  sameCell_sound (by decide +kernel)

theorem check_16322 : DirectFix.directFix box_16322 = true := by decide +kernel

theorem strict_16322 (p : Chart) (hp : box_16322.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_16322 hp hv

noncomputable def box_16678 : Cell :=
  ⟨![5/8, 37/32, 1/4, 3/8, 0, 0, 0, (-1/2 : ℚ)],
    ![177/256, 11/8, 3/8, 1/2, 1/4, 1/4, 1/4, (-1/4 : ℚ)]⟩

theorem addr_16678 : box_16678 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 7, 9, 11, 13, 14, 0, 3, 4, 7, 8, 10, 12, 14, 0] :=
  sameCell_sound (by decide +kernel)

theorem check_16678 : DirectFix.directFix box_16678 = true := by decide +kernel

theorem strict_16678 (p : Chart) (hp : box_16678.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_16678 hp hv

noncomputable def box_59412 : Cell :=
  ⟨![97/128, 15/16, 3/8, 1/16, 1/4, 1/4, (-1/4 : ℚ), (-1/4 : ℚ)],
    ![211/256, 67/64, 7/16, 1/8, 1/2, 1/2, 0, 0]⟩

theorem addr_59412 : box_59412 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 6, 9, 11, 12, 14, 1, 2, 5, 6, 9, 11, 13, 15, 0, 2, 4, 7] :=
  sameCell_sound (by decide +kernel)

theorem check_59412 : DirectFix.directFix box_59412 = true := by decide +kernel

theorem strict_59412 (p : Chart) (hp : box_59412.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_59412 hp hv

noncomputable def box_59404 : Cell :=
  ⟨![97/128, 15/16, 3/8, 1/16, 1/4, (-1/2 : ℚ), 0, 0],
    ![211/256, 67/64, 7/16, 1/8, 1/2, (-1/4 : ℚ), 1/4, 1/4]⟩

theorem addr_59404 : box_59404 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 6, 9, 10, 13, 15, 1, 2, 5, 6, 9, 10, 12, 14, 0, 2, 4, 7] :=
  sameCell_sound (by decide +kernel)

theorem check_59404 : DirectFix.directFix box_59404 = true := by decide +kernel

theorem strict_59404 (p : Chart) (hp : box_59404.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_59404 hp hv

noncomputable def box_66466 : Cell :=
  ⟨![5/8, 81/64, 1/8, 1/4, 1/4, (-1/4 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ)],
    ![177/256, 11/8, 3/16, 5/16, 3/8, 0, 0, (-1/4 : ℚ)]⟩

theorem addr_66466 : box_66466 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 9, 10, 12, 14, 0, 3, 5, 6, 9, 11, 13, 14, 0, 3, 4, 6, 8] :=
  sameCell_sound (by decide +kernel)

theorem check_66466 : DirectFix.directFix box_66466 = true := by decide +kernel

theorem strict_66466 (p : Chart) (hp : box_66466.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_66466 hp hv

noncomputable def box_66375 : Cell :=
  ⟨![5/8, 81/64, 0, 5/16, 1/4, (-1/4 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ)],
    ![177/256, 11/8, 1/16, 3/8, 3/8, 0, 0, (-1/4 : ℚ)]⟩

theorem addr_66375 : box_66375 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 9, 10, 12, 14, 0, 3, 4, 6, 9, 11, 13, 14, 0, 3, 4, 7, 8] :=
  sameCell_sound (by decide +kernel)

theorem check_66375 : DirectFix.directFix box_66375 = true := by decide +kernel

theorem strict_66375 (p : Chart) (hp : box_66375.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_66375 hp hv

noncomputable def box_63772 : Cell :=
  ⟨![5/8, 81/64, 0, 0, 1/4, (-1/2 : ℚ), 0, 1/4],
    ![177/256, 11/8, 1/16, 1/16, 3/8, (-1/4 : ℚ), 1/4, 1/2]⟩

theorem addr_63772 : box_63772 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 6, 9, 10, 13, 15, 0, 3, 4, 6, 9, 10, 12, 15, 0, 3, 4, 6, 8] :=
  sameCell_sound (by decide +kernel)

theorem check_63772 : DirectFix.directFix box_63772 = true := by decide +kernel

theorem strict_63772 (p : Chart) (hp : box_63772.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_63772 hp hv

noncomputable def box_63987 : Cell :=
  ⟨![5/8, 81/64, 0, 0, 1/4, 1/4, (-1/4 : ℚ), (-1/2 : ℚ)],
    ![177/256, 11/8, 1/16, 1/16, 3/8, 1/2, 0, (-1/4 : ℚ)]⟩

theorem addr_63987 : box_63987 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 6, 9, 11, 12, 14, 0, 3, 4, 6, 9, 11, 13, 14, 0, 3, 4, 6, 8] :=
  sameCell_sound (by decide +kernel)

theorem check_63987 : DirectFix.directFix box_63987 = true := by decide +kernel

theorem strict_63987 (p : Chart) (hp : box_63987.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_63987 hp hv

noncomputable def box_65228 : Cell :=
  ⟨![5/8, 81/64, 3/16, 1/4, (-3/8 : ℚ), (-1/4 : ℚ), 0, (-1/2 : ℚ)],
    ![177/256, 11/8, 1/4, 5/16, (-1/4 : ℚ), 0, 1/4, (-1/4 : ℚ)]⟩

theorem addr_65228 : box_65228 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 10, 13, 14, 0, 3, 5, 6, 8, 11, 12, 14, 0, 3, 5, 6, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_65228 : DirectFix.directFix box_65228 = true := by decide +kernel

theorem strict_65228 (p : Chart) (hp : box_65228.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_65228 hp hv

noncomputable def box_65739 : Cell :=
  ⟨![5/8, 81/64, 3/16, 1/4, (-3/8 : ℚ), 0, (-1/4 : ℚ), 1/4],
    ![177/256, 11/8, 1/4, 5/16, (-1/4 : ℚ), 1/4, 0, 1/2]⟩

theorem addr_65739 : box_65739 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 11, 12, 15, 0, 3, 5, 6, 8, 10, 13, 15, 0, 3, 5, 6, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_65739 : DirectFix.directFix box_65739 = true := by decide +kernel

theorem strict_65739 (p : Chart) (hp : box_65739.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_65739 hp hv

noncomputable def box_65131 : Cell :=
  ⟨![5/8, 81/64, 0, 5/16, (-3/8 : ℚ), (-1/4 : ℚ), 0, (-1/2 : ℚ)],
    ![177/256, 11/8, 1/16, 3/8, (-1/4 : ℚ), 0, 1/4, (-1/4 : ℚ)]⟩

theorem addr_65131 : box_65131 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 10, 13, 14, 0, 3, 4, 6, 8, 11, 12, 14, 0, 3, 4, 7, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_65131 : DirectFix.directFix box_65131 = true := by decide +kernel

theorem strict_65131 (p : Chart) (hp : box_65131.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_65131 hp hv

noncomputable def box_65645 : Cell :=
  ⟨![5/8, 81/64, 0, 5/16, (-3/8 : ℚ), 0, (-1/4 : ℚ), 1/4],
    ![177/256, 11/8, 1/16, 3/8, (-1/4 : ℚ), 1/4, 0, 1/2]⟩

theorem addr_65645 : box_65645 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 11, 12, 15, 0, 3, 4, 6, 8, 10, 13, 15, 0, 3, 4, 7, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_65645 : DirectFix.directFix box_65645 = true := by decide +kernel

theorem strict_65645 (p : Chart) (hp : box_65645.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_65645 hp hv

noncomputable def box_65320 : Cell :=
  ⟨![97/128, 15/16, 3/16, 1/4, (-3/8 : ℚ), (-1/2 : ℚ), 0, (-1/4 : ℚ)],
    ![211/256, 67/64, 1/4, 5/16, (-1/4 : ℚ), (-1/4 : ℚ), 1/4, 0]⟩

theorem addr_65320 : box_65320 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 10, 13, 14, 1, 2, 5, 6, 8, 10, 12, 15, 0, 2, 5, 6, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_65320 : DirectFix.directFix box_65320 = true := by decide +kernel

theorem strict_65320 (p : Chart) (hp : box_65320.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_65320 hp hv

noncomputable def box_55209 : Cell :=
  ⟨![97/128, 37/32, 0, 1/8, 0, (-1/2 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ)],
    ![211/256, 81/64, 1/16, 1/4, 1/4, (-1/4 : ℚ), 0, 0]⟩

theorem addr_55209 : box_55209 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 6, 9, 10, 12, 14, 1, 3, 4, 7, 8, 10, 13, 15, 0, 2, 4] :=
  sameCell_sound (by decide +kernel)

theorem check_55209 : DirectFix.directFix box_55209 = true := by decide +kernel

theorem strict_55209 (p : Chart) (hp : box_55209.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_55209 hp hv

noncomputable def box_61666 : Cell :=
  ⟨![211/256, 53/64, 7/16, 5/16, 3/8, (-1/4 : ℚ), 1/4, (-1/4 : ℚ)],
    ![57/64, 15/16, 1/2, 3/8, 1/2, 0, 1/2, 0]⟩

theorem addr_61666 : box_61666 = OverlayPlanar.descend CompactCover.root [0, 2, 5, 7, 9, 10, 13, 14, 1, 3, 5, 6, 9, 11, 13, 15, 1, 3, 5, 7, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_61666 : DirectFix.directFix box_61666 = true := by decide +kernel

theorem strict_61666 (p : Chart) (hp : box_61666.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_61666 hp hv

noncomputable def box_54728 : Cell :=
  ⟨![211/256, 53/64, 7/16, 0, 0, (-1/2 : ℚ), 0, 0],
    ![57/64, 15/16, 1/2, 1/8, 1/4, (-1/4 : ℚ), 1/4, 1/4]⟩

theorem addr_54728 : box_54728 = OverlayPlanar.descend CompactCover.root [0, 2, 5, 6, 9, 10, 13, 15, 1, 3, 5, 6, 8, 10, 12, 14, 1, 3, 5] :=
  sameCell_sound (by decide +kernel)

theorem check_54728 : DirectFix.directFix box_54728 = true := by decide +kernel

theorem strict_54728 (p : Chart) (hp : box_54728.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_54728 hp hv

noncomputable def box_64863 : Cell :=
  ⟨![97/128, 37/32, 1/8, 7/16, (-1/8 : ℚ), (-1/2 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ)],
    ![211/256, 81/64, 3/16, 1/2, 0, (-1/4 : ℚ), 0, 0]⟩

theorem addr_64863 : box_64863 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 10, 12, 14, 1, 3, 5, 7, 9, 10, 13, 15, 0, 2, 4, 7, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_64863 : DirectFix.directFix box_64863 = true := by decide +kernel

theorem strict_64863 (p : Chart) (hp : box_64863.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_64863 hp hv

noncomputable def box_30740 : Cell :=
  ⟨![97/128, 15/16, 0, 3/8, (-1/4 : ℚ), 1/4, 0, (-1/4 : ℚ)],
    ![211/256, 67/64, 1/8, 1/2, 0, 1/2, 1/4, 0]⟩

theorem addr_30740 : box_30740 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 11, 13, 14, 1, 2, 4, 7, 9, 11, 12, 15, 0, 2] :=
  sameCell_sound (by decide +kernel)

theorem check_30740 : DirectFix.directFix box_30740 = true := by decide +kernel

theorem strict_30740 (p : Chart) (hp : box_30740.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_30740 hp hv

noncomputable def box_58538 : Cell :=
  ⟨![57/64, 67/64, 3/16, 3/8, 1/4, 0, (-1/4 : ℚ), 0],
    ![245/256, 37/32, 1/4, 1/2, 1/2, 1/4, 0, 1/4]⟩

theorem addr_58538 : box_58538 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 7, 9, 11, 12, 15, 0, 2, 5, 7, 9, 10, 13, 14, 0, 3, 5] :=
  sameCell_sound (by decide +kernel)

theorem check_58538 : DirectFix.directFix box_58538 = true := by decide +kernel

theorem strict_58538 (p : Chart) (hp : box_58538.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_58538 hp hv

noncomputable def box_21580 : Cell :=
  ⟨![211/256, 53/64, 0, 1/8, (-1/2 : ℚ), 1/4, (-1/4 : ℚ), (-1/4 : ℚ)],
    ![57/64, 15/16, 1/8, 1/4, (-1/4 : ℚ), 1/2, 0, 0]⟩

theorem addr_21580 : box_21580 = OverlayPlanar.descend CompactCover.root [0, 2, 4, 6, 8, 11, 12, 14, 1, 3, 4, 7, 8, 11, 13, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_21580 : DirectFix.directFix box_21580 = true := by decide +kernel

theorem strict_21580 (p : Chart) (hp : box_21580.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_21580 hp hv

noncomputable def box_11502 : Cell :=
  ⟨![97/128, 23/32, 1/4, 1/8, 1/4, 1/4, 0, (-1/4 : ℚ)],
    ![211/256, 15/16, 3/8, 1/4, 1/2, 1/2, 1/4, 0]⟩

theorem addr_11502 : box_11502 = OverlayPlanar.descend CompactCover.root [0, 2, 5, 6, 9, 11, 13, 14, 1, 3, 4, 7, 9, 11, 12, 15, 0] :=
  sameCell_sound (by decide +kernel)

theorem check_11502 : DirectFix.directFix box_11502 = true := by decide +kernel

theorem strict_11502 (p : Chart) (hp : box_11502.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_11502 hp hv

noncomputable def box_15486 : Cell :=
  ⟨![5/8, 37/32, 1/4, 0, 1/4, 1/4, (-1/4 : ℚ), (-1/4 : ℚ)],
    ![177/256, 11/8, 3/8, 1/8, 1/2, 1/2, 0, 0]⟩

theorem addr_15486 : box_15486 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 6, 9, 11, 12, 14, 0, 3, 4, 6, 9, 11, 13, 15, 0] :=
  sameCell_sound (by decide +kernel)

theorem check_15486 : DirectFix.directFix box_15486 = true := by decide +kernel

theorem strict_15486 (p : Chart) (hp : box_15486.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_15486 hp hv

noncomputable def box_31447 : Cell :=
  ⟨![211/256, 67/64, 0, 3/8, 1/4, (-1/4 : ℚ), 0, (-1/4 : ℚ)],
    ![57/64, 37/32, 1/8, 1/2, 1/2, 0, 1/4, 0]⟩

theorem addr_31447 : box_31447 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 9, 10, 13, 14, 1, 2, 4, 7, 9, 11, 12, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_31447 : DirectFix.directFix box_31447 = true := by decide +kernel

theorem strict_31447 (p : Chart) (hp : box_31447.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_31447 hp hv

noncomputable def box_7968 : Cell :=
  ⟨![131/128, 15/16, 1/8, 1/8, (-1/2 : ℚ), (-1/4 : ℚ), 0, 0],
    ![37/32, 37/32, 1/4, 1/4, (-1/4 : ℚ), 0, 1/4, 1/4]⟩

theorem addr_7968 : box_7968 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 13, 15, 1, 2, 5, 7, 8, 11, 12, 14] :=
  sameCell_sound (by decide +kernel)

theorem check_7968 : DirectFix.directFix box_7968 = true := by decide +kernel

theorem strict_7968 (p : Chart) (hp : box_7968.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_7968 hp hv

noncomputable def box_4547 : Cell :=
  ⟨![5/8, 23/32, 3/8, 1/4, (-1/2 : ℚ), (-1/4 : ℚ), 1/4, 0],
    ![97/128, 15/16, 1/2, 3/8, (-1/4 : ℚ), 0, 1/2, 1/4]⟩

theorem addr_4547 : box_4547 = OverlayPlanar.descend CompactCover.root [0, 2, 5, 7, 8, 10, 13, 15, 0, 3, 5, 6, 8, 11, 13, 14] :=
  sameCell_sound (by decide +kernel)

theorem check_4547 : DirectFix.directFix box_4547 = true := by decide +kernel

theorem strict_4547 (p : Chart) (hp : box_4547.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_4547 hp hv

noncomputable def box_25217 : Cell :=
  ⟨![97/128, 23/32, 3/8, 1/4, (-1/4 : ℚ), (-1/2 : ℚ), 1/4, (-1/4 : ℚ)],
    ![211/256, 53/64, 1/2, 3/8, 0, (-1/4 : ℚ), 1/2, 0]⟩

theorem addr_25217 : box_25217 = OverlayPlanar.descend CompactCover.root [0, 2, 5, 7, 8, 10, 13, 14, 1, 3, 5, 6, 9, 10, 13, 15, 0, 2] :=
  sameCell_sound (by decide +kernel)

theorem check_25217 : DirectFix.directFix box_25217 = true := by decide +kernel

theorem strict_25217 (p : Chart) (hp : box_25217.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_25217 hp hv

noncomputable def box_1580 : Cell :=
  ⟨![97/128, 1/2, 1/8, 1/4, (-1/2 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ), 0],
    ![57/64, 23/32, 1/4, 3/8, (-1/4 : ℚ), 0, (-1/4 : ℚ), 1/4]⟩

theorem addr_1580 : box_1580 = OverlayPlanar.descend CompactCover.root [0, 2, 4, 7, 8, 10, 12, 15, 1, 2, 5, 6, 8, 11, 12, 14] :=
  sameCell_sound (by decide +kernel)

theorem check_1580 : DirectFix.directFix box_1580 = true := by decide +kernel

theorem strict_1580 (p : Chart) (hp : box_1580.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_1580 hp hv

noncomputable def box_610 : Cell :=
  ⟨![5/8, 1/2, 1/8, 0, (-1/4 : ℚ), 0, (-1/4 : ℚ), (-1/4 : ℚ)],
    ![97/128, 23/32, 1/4, 1/8, 0, 1/4, 0, 0]⟩

theorem addr_610 : box_610 = OverlayPlanar.descend CompactCover.root [0, 2, 4, 6, 8, 11, 12, 14, 0, 2, 5, 6, 9, 10, 13, 15] :=
  sameCell_sound (by decide +kernel)

theorem check_610 : DirectFix.directFix box_610 = true := by decide +kernel

theorem strict_610 (p : Chart) (hp : box_610.Mem p) (hv : (chartPoint p).Valid) :
    energy fcc < energy (chartPoint p) :=
  DirectFix.directFix_sound check_610 hp hv

noncomputable def box_44528 : Cell :=
  ⟨![245/256, 67/64, 0, 0, (-1/4 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)],
    ![131/128, 37/32, 1/8, 1/8, 0, (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ)]⟩

theorem addr_44528 : box_44528 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 9, 10, 12, 14, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44528 : compactReductionCheck box_44528 = true := by decide +kernel

theorem invalid_44528 (p : Chart) (hp : box_44528.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44528 check_44528 p hp

noncomputable def box_44529 : Cell :=
  ⟨![245/256, 67/64, 0, 0, (-1/4 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (-1/4 : ℚ)],
    ![131/128, 37/32, 1/8, 1/8, 0, (-1/4 : ℚ), (-1/4 : ℚ), 0]⟩

theorem addr_44529 : box_44529 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 9, 10, 12, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44529 : compactReductionCheck box_44529 = true := by decide +kernel

theorem invalid_44529 (p : Chart) (hp : box_44529.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44529 check_44529 p hp

noncomputable def box_44530 : Cell :=
  ⟨![245/256, 67/64, 0, 0, (-1/4 : ℚ), (-1/2 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ)],
    ![131/128, 37/32, 1/8, 1/8, 0, (-1/4 : ℚ), 0, (-1/4 : ℚ)]⟩

theorem addr_44530 : box_44530 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 9, 10, 13, 14, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44530 : compactReductionCheck box_44530 = true := by decide +kernel

theorem invalid_44530 (p : Chart) (hp : box_44530.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44530 check_44530 p hp

noncomputable def box_44531 : Cell :=
  ⟨![245/256, 67/64, 0, 0, (-1/4 : ℚ), (-1/2 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ)],
    ![131/128, 37/32, 1/8, 1/8, 0, (-1/4 : ℚ), 0, 0]⟩

theorem addr_44531 : box_44531 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 9, 10, 13, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44531 : compactReductionCheck box_44531 = true := by decide +kernel

theorem invalid_44531 (p : Chart) (hp : box_44531.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44531 check_44531 p hp

noncomputable def box_44532 : Cell :=
  ⟨![245/256, 67/64, 0, 0, (-1/4 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)],
    ![131/128, 37/32, 1/8, 1/8, 0, 0, (-1/4 : ℚ), (-1/4 : ℚ)]⟩

theorem addr_44532 : box_44532 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 9, 11, 12, 14, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44532 : compactReductionCheck box_44532 = true := by decide +kernel

theorem invalid_44532 (p : Chart) (hp : box_44532.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44532 check_44532 p hp

noncomputable def box_44533 : Cell :=
  ⟨![245/256, 67/64, 0, 0, (-1/4 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ), (-1/4 : ℚ)],
    ![131/128, 37/32, 1/8, 1/8, 0, 0, (-1/4 : ℚ), 0]⟩

theorem addr_44533 : box_44533 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 9, 11, 12, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44533 : compactReductionCheck box_44533 = true := by decide +kernel

theorem invalid_44533 (p : Chart) (hp : box_44533.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44533 check_44533 p hp

noncomputable def box_44534 : Cell :=
  ⟨![245/256, 67/64, 0, 0, (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ)],
    ![131/128, 37/32, 1/8, 1/8, 0, 0, 0, (-1/4 : ℚ)]⟩

theorem addr_44534 : box_44534 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 9, 11, 13, 14, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44534 : compactReductionCheck box_44534 = true := by decide +kernel

theorem invalid_44534 (p : Chart) (hp : box_44534.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44534 check_44534 p hp

noncomputable def box_44537 : Cell :=
  ⟨![245/256, 67/64, 0, 1/8, (-1/4 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ), (-1/2 : ℚ)],
    ![131/128, 37/32, 1/8, 1/4, 0, (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ)]⟩

theorem addr_44537 : box_44537 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 6, 8, 10, 12, 14, 0, 2, 4, 7, 9, 10, 12, 14, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_44537 : compactReductionCheck box_44537 = true := by decide +kernel

theorem invalid_44537 (p : Chart) (hp : box_44537.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_44537 check_44537 p hp

noncomputable def box_47845 : Cell :=
  ⟨![279/256, 15/16, 1/8, 1/4, (-1/4 : ℚ), 0, 0, (-1/2 : ℚ)],
    ![37/32, 67/64, 1/4, 3/8, 0, 1/4, 1/4, (-1/4 : ℚ)]⟩

theorem addr_47845 : box_47845 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 7, 8, 11, 13, 14, 1, 2, 5, 6, 9, 10, 12, 14, 1, 2] :=
  sameCell_sound (by decide +kernel)

theorem check_47845 : compactReductionCheck box_47845 = true := by decide +kernel

theorem invalid_47845 (p : Chart) (hp : box_47845.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_47845 check_47845 p hp

noncomputable def box_61763 : Cell :=
  ⟨![177/256, 81/64, 0, 1/16, (-3/8 : ℚ), (-1/4 : ℚ), (-1/2 : ℚ), (-1/4 : ℚ)],
    ![97/128, 11/8, 1/16, 1/8, (-1/4 : ℚ), 0, (-1/4 : ℚ), 0]⟩

theorem addr_61763 : box_61763 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 6, 8, 10, 12, 14, 0, 3, 4, 6, 8, 11, 12, 15, 1, 3, 4, 7, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_61763 : compactReductionCheck box_61763 = true := by decide +kernel

theorem invalid_61763 (p : Chart) (hp : box_61763.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_61763 check_61763 p hp

noncomputable def box_66174 : Cell :=
  ⟨![177/256, 81/64, 1/16, 7/16, (-3/8 : ℚ), 0, 1/4, 0],
    ![97/128, 11/8, 1/8, 1/2, (-1/4 : ℚ), 1/4, 1/2, 1/4]⟩

theorem addr_66174 : box_66174 = OverlayPlanar.descend CompactCover.root [0, 3, 4, 7, 8, 11, 13, 15, 0, 3, 4, 7, 8, 10, 13, 14, 1, 3, 5, 7, 9] :=
  sameCell_sound (by decide +kernel)

theorem check_66174 : compactReductionCheck box_66174 = true := by decide +kernel

theorem invalid_66174 (p : Chart) (hp : box_66174.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_66174 check_66174 p hp

noncomputable def box_60668 : Cell :=
  ⟨![279/256, 15/16, 5/16, 1/4, 0, (-1/2 : ℚ), 1/4, (-1/4 : ℚ)],
    ![37/32, 67/64, 3/8, 5/16, 1/4, (-1/4 : ℚ), 1/2, 0]⟩

theorem addr_60668 : box_60668 = OverlayPlanar.descend CompactCover.root [1, 3, 5, 7, 9, 10, 13, 14, 1, 2, 4, 6, 8, 10, 13, 15, 1, 2, 5, 6] :=
  sameCell_sound (by decide +kernel)

theorem check_60668 : compactReductionCheck box_60668 = true := by decide +kernel

theorem invalid_60668 (p : Chart) (hp : box_60668.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_60668 check_60668 p hp

noncomputable def box_49541 : Cell :=
  ⟨![279/256, 67/64, 0, 1/4, 1/4, 1/4, 1/4, 1/4],
    ![37/32, 37/32, 1/8, 3/8, 1/2, 1/2, 1/2, 1/2]⟩

theorem addr_49541 : box_49541 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 7, 9, 11, 13, 15, 1, 2, 4, 6, 9, 11, 13, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_49541 : compactReductionCheck box_49541 = true := by decide +kernel

theorem invalid_49541 (p : Chart) (hp : box_49541.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_49541 check_49541 p hp

noncomputable def box_11137 : Cell :=
  ⟨![211/256, 1/2, 1/4, 0, 1/4, (-1/4 : ℚ), (-1/4 : ℚ), 1/4],
    ![57/64, 23/32, 3/8, 1/8, 1/2, 0, 0, 1/2]⟩

theorem addr_11137 : box_11137 = OverlayPlanar.descend CompactCover.root [0, 2, 5, 6, 9, 10, 12, 15, 1, 2, 4, 6, 9, 11, 13, 15, 1] :=
  sameCell_sound (by decide +kernel)

theorem check_11137 : compactReductionCheck box_11137 = true := by decide +kernel

theorem invalid_11137 (p : Chart) (hp : box_11137.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_11137 check_11137 p hp

noncomputable def box_21494 : Cell :=
  ⟨![177/256, 1/2, 1/8, 0, (-1/2 : ℚ), (-1/2 : ℚ), 0, 1/4],
    ![97/128, 39/64, 1/4, 1/8, (-1/4 : ℚ), (-1/4 : ℚ), 1/4, 1/2]⟩

theorem addr_21494 : box_21494 = OverlayPlanar.descend CompactCover.root [0, 2, 4, 6, 8, 10, 13, 15, 0, 2, 5, 6, 8, 10, 12, 15, 1, 2] :=
  sameCell_sound (by decide +kernel)

theorem check_21494 : compactReductionCheck box_21494 = true := by decide +kernel

theorem invalid_21494 (p : Chart) (hp : box_21494.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_21494 check_21494 p hp

noncomputable def box_15059 : Cell :=
  ⟨![211/256, 37/32, 3/8, 0, (-1/4 : ℚ), 1/4, (-1/2 : ℚ), 0],
    ![57/64, 11/8, 1/2, 1/8, 0, 1/2, (-1/4 : ℚ), 1/4]⟩

theorem addr_15059 : box_15059 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 6, 8, 11, 12, 15, 1, 3, 5, 6, 9, 11, 12, 14, 1] :=
  sameCell_sound (by decide +kernel)

theorem check_15059 : compactReductionCheck box_15059 = true := by decide +kernel

theorem invalid_15059 (p : Chart) (hp : box_15059.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_15059 check_15059 p hp

noncomputable def box_39815 : Cell :=
  ⟨![57/64, 23/32, 0, 3/8, (-1/2 : ℚ), 0, (-1/2 : ℚ), (-1/2 : ℚ)],
    ![245/256, 53/64, 1/8, 1/2, (-1/4 : ℚ), 1/4, (-1/4 : ℚ), (-1/4 : ℚ)]⟩

theorem addr_39815 : box_39815 = OverlayPlanar.descend CompactCover.root [1, 2, 4, 7, 8, 11, 12, 14, 0, 3, 4, 7, 8, 10, 12, 14, 0, 2] :=
  sameCell_sound (by decide +kernel)

theorem check_39815 : compactReductionCheck box_39815 = true := by decide +kernel

theorem invalid_39815 (p : Chart) (hp : box_39815.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_39815 check_39815 p hp

noncomputable def box_32918 : Cell :=
  ⟨![97/128, 81/64, 3/8, 1/8, (-1/2 : ℚ), (-1/2 : ℚ), 0, (-1/2 : ℚ)],
    ![211/256, 11/8, 1/2, 1/4, (-1/4 : ℚ), (-1/4 : ℚ), 1/4, (-1/4 : ℚ)]⟩

theorem addr_32918 : box_32918 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 6, 8, 10, 13, 14, 1, 3, 5, 7, 8, 10, 12, 14, 0, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_32918 : compactReductionCheck box_32918 = true := by decide +kernel

theorem invalid_32918 (p : Chart) (hp : box_32918.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_32918 check_32918 p hp

noncomputable def box_10324 : Cell :=
  ⟨![211/256, 1/2, 1/8, 3/8, 0, 0, 0, (-1/2 : ℚ)],
    ![57/64, 23/32, 1/4, 1/2, 1/4, 1/4, 1/4, (-1/4 : ℚ)]⟩

theorem addr_10324 : box_10324 = OverlayPlanar.descend CompactCover.root [0, 2, 4, 7, 9, 11, 13, 14, 1, 2, 5, 7, 8, 10, 12, 14, 1] :=
  sameCell_sound (by decide +kernel)

theorem check_10324 : compactReductionCheck box_10324 = true := by decide +kernel

theorem invalid_10324 (p : Chart) (hp : box_10324.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_10324 check_10324 p hp

noncomputable def box_50901 : Cell :=
  ⟨![131/128, 67/64, 1/4, 1/8, 0, 1/4, (-1/2 : ℚ), (-1/4 : ℚ)],
    ![279/256, 37/32, 3/8, 1/4, 1/4, 1/2, (-1/4 : ℚ), 0]⟩

theorem addr_50901 : box_50901 = OverlayPlanar.descend CompactCover.root [1, 3, 5, 6, 9, 11, 12, 14, 1, 2, 4, 7, 8, 11, 12, 15, 0, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_50901 : compactReductionCheck box_50901 = true := by decide +kernel

theorem invalid_50901 (p : Chart) (hp : box_50901.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_50901 check_50901 p hp

noncomputable def box_35962 : Cell :=
  ⟨![177/256, 81/64, 1/4, 1/4, (-1/4 : ℚ), 1/4, (-1/2 : ℚ), (-1/4 : ℚ)],
    ![97/128, 11/8, 3/8, 3/8, 0, 1/2, (-1/4 : ℚ), 0]⟩

theorem addr_35962 : box_35962 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 7, 8, 11, 12, 14, 0, 3, 4, 6, 9, 11, 12, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_35962 : compactReductionCheck box_35962 = true := by decide +kernel

theorem invalid_35962 (p : Chart) (hp : box_35962.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_35962 check_35962 p hp

noncomputable def box_47232 : Cell :=
  ⟨![279/256, 67/64, 0, 1/4, (-1/4 : ℚ), (-1/4 : ℚ), 0, 1/4],
    ![37/32, 37/32, 1/8, 3/8, 0, 0, 1/4, 1/2]⟩

theorem addr_47232 : box_47232 = OverlayPlanar.descend CompactCover.root [1, 3, 4, 7, 8, 10, 13, 15, 1, 2, 4, 6, 9, 11, 12, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_47232 : compactReductionCheck box_47232 = true := by decide +kernel

theorem invalid_47232 (p : Chart) (hp : box_47232.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_47232 check_47232 p hp

noncomputable def box_34789 : Cell :=
  ⟨![211/256, 81/64, 1/4, 0, 1/4, 0, (-1/2 : ℚ), 1/4],
    ![57/64, 11/8, 3/8, 1/8, 1/2, 1/4, (-1/4 : ℚ), 1/2]⟩

theorem addr_34789 : box_34789 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 6, 9, 11, 12, 15, 1, 3, 4, 6, 9, 10, 12, 15, 1, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_34789 : compactReductionCheck box_34789 = true := by decide +kernel

theorem invalid_34789 (p : Chart) (hp : box_34789.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_34789 check_34789 p hp

noncomputable def box_37993 : Cell :=
  ⟨![97/128, 81/64, 3/8, 3/8, 0, 1/4, 1/4, 1/4],
    ![211/256, 11/8, 1/2, 1/2, 1/4, 1/2, 1/2, 1/2]⟩

theorem addr_37993 : box_37993 = OverlayPlanar.descend CompactCover.root [0, 3, 5, 7, 9, 11, 13, 15, 1, 3, 5, 7, 8, 11, 13, 15, 0, 3] :=
  sameCell_sound (by decide +kernel)

theorem check_37993 : compactReductionCheck box_37993 = true := by decide +kernel

theorem invalid_37993 (p : Chart) (hp : box_37993.Mem p) : Route.result .invalidReduction p :=
  compactReductionCheck_sound box_37993 check_37993 p hp

end BccSharp.Coulomb.CompactCover.PrefixItems.Direct
