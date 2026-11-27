import BccSharp.Cover.OverlaySoundCheck

set_option autoImplicit false

/-! Generated.

The Overlay pilot sample: strict terminals of the planar banks
(rows by pass-seven index and by original baseline index). Each
box is bound to its row root and recorded path by `leafNN_address`, and
paid by one kernel evaluation of `sharpPass`. -/

noncomputable section

namespace BccSharp.Coulomb.CompactCover.OverlayPlanar.Pilot
open BccSharp BccSharp.Coverage
open BccSharp.Coulomb.CompactCover.OverlayPlanar

noncomputable def root_h297 : Cell :=
  ⟨![439/512, 23/32, 7/16, 7/16, 1/4, 3/8, -1/4, 127/256],
    ![57/64, 53/64, 1/2, 1/2, 3/8, 1/2, 0, 1/2]⟩

noncomputable def root_h295 : Cell :=
  ⟨![439/512, 23/32, 7/16, 7/16, 1/4, 3/8, -1/4, 63/128],
    ![57/64, 53/64, 1/2, 1/2, 3/8, 1/2, 0, 127/256]⟩

noncomputable def root_h289 : Cell :=
  ⟨![211/256, 23/32, 7/16, 7/16, 1/4, 3/8, -1/4, 31/64],
    ![57/64, 53/64, 1/2, 1/2, 3/8, 1/2, 0, 497/1024]⟩

noncomputable def root_h296 : Cell :=
  ⟨![211/256, 23/32, 7/16, 7/16, 1/4, 3/8, -1/4, 127/256],
    ![439/512, 53/64, 1/2, 1/2, 3/8, 1/2, 0, 1/2]⟩

noncomputable def root_h292 : Cell :=
  ⟨![211/256, 23/32, 7/16, 7/16, 1/4, 3/8, -1/4, 499/1024],
    ![57/64, 53/64, 1/2, 1/2, 3/8, 1/2, 0, 125/256]⟩

noncomputable def root_h291 : Cell :=
  ⟨![211/256, 23/32, 7/16, 7/16, 1/4, 3/8, -1/4, 249/512],
    ![57/64, 53/64, 1/2, 1/2, 3/8, 1/2, 0, 499/1024]⟩

noncomputable def root_a487334 : Cell :=
  ⟨![177/256, 23/32, 3/16, 1/8, -1/4, -1/4, -1/2, -1/2],
    ![97/128, 53/64, 1/4, 3/16, -1/8, -1/8, -1/4, -1/4]⟩

noncomputable def root_a532440 : Cell :=
  ⟨![211/256, 23/32, 1/8, 3/16, 1/4, -1/2, 1/4, -1/2],
    ![57/64, 53/64, 3/16, 1/4, 3/8, -3/8, 1/2, -1/4]⟩

noncomputable def root_a675855 : Cell :=
  ⟨![177/256, 53/64, 3/8, 3/16, 0, -3/8, -1/2, 1/4],
    ![97/128, 15/16, 7/16, 1/4, 1/8, -1/4, -1/4, 1/2]⟩

noncomputable def root_a535868 : Cell :=
  ⟨![97/128, 23/32, 1/8, 1/16, 1/8, -1/2, 1/4, 1/4],
    ![211/256, 53/64, 3/16, 1/8, 1/4, -3/8, 1/2, 1/2]⟩

noncomputable def root_a890970 : Cell :=
  ⟨![5/8, 15/16, 1/16, 3/16, 0, -1/2, 1/4, -1/2],
    ![177/256, 67/64, 1/8, 1/4, 1/8, -3/8, 1/2, -1/4]⟩

noncomputable def root_a542836 : Cell :=
  ⟨![5/8, 53/64, 1/8, 1/8, 0, 0, -1/4, 1/4],
    ![177/256, 15/16, 3/16, 3/16, 1/8, 1/8, 0, 1/2]⟩

noncomputable def root_a688095 : Cell :=
  ⟨![211/256, 23/32, 5/16, 1/16, 1/8, -1/8, 0, 1/4],
    ![57/64, 53/64, 3/8, 1/8, 1/4, 0, 1/4, 1/2]⟩

noncomputable def root_a670159 : Cell :=
  ⟨![177/256, 23/32, 7/16, 1/16, 1/4, -1/8, -1/4, -1/2],
    ![97/128, 53/64, 1/2, 1/8, 3/8, 0, 0, -1/4]⟩

noncomputable def root_a617847 : Cell :=
  ⟨![211/256, 23/32, 1/16, 3/8, 1/8, 3/8, 0, -1/2],
    ![57/64, 53/64, 1/8, 7/16, 1/4, 1/2, 1/4, -1/4]⟩

noncomputable def root_a737895 : Cell :=
  ⟨![211/256, 53/64, 1/4, 5/16, -1/2, 1/8, -1/2, -1/2],
    ![57/64, 15/16, 5/16, 3/8, -3/8, 1/4, -1/4, -1/4]⟩

noncomputable def root_a505196 : Cell :=
  ⟨![211/256, 23/32, 1/16, 1/8, -1/2, 0, -1/2, -1/2],
    ![57/64, 53/64, 1/8, 3/16, -3/8, 1/8, -1/4, -1/4]⟩

noncomputable def leaf00 : Cell :=
  ⟨![895/1024, 99/128, 7/16, 7/16, 9/32, 27/64, -1/4, 127/256],
    ![57/64, 403/512, 1/2, 1/2, 5/16, 7/16, -15/64, 1/2]⟩

theorem leaf00_address : leaf00=descend root_h297 [12, 3, 10, 12, 8, 2, 11, 12, 9, 2, 1, 11, 12] :=
  sameCell_sound (by decide +kernel)

theorem leaf00_pass : sharpPass leaf00=true := by decide +kernel

theorem leaf00_strictFCC {p : Chart} (hp : leaf00.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf00_pass hp

noncomputable def leaf01 : Cell :=
  ⟨![439/512, 403/512, 7/16, 15/32, 23/64, 13/32, -1/4, 63/128],
    ![895/1024, 205/256, 1/2, 1/2, 3/8, 27/64, -15/64, 127/256]⟩

theorem leaf01_address : leaf01=descend root_h295 [12, 3, 10, 12, 9, 2, 11, 12, 9, 3, 0, 10, 12, 7, 9] :=
  sameCell_sound (by decide +kernel)

theorem leaf01_pass : sharpPass leaf01=true := by decide +kernel

theorem leaf01_strictFCC {p : Chart} (hp : leaf01.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf01_pass hp

noncomputable def leaf02 : Cell :=
  ⟨![895/1024, 389/512, 7/16, 7/16, 11/32, 7/16, -1/4, 31/64],
    ![57/64, 99/128, 1/2, 1/2, 3/8, 15/32, -7/32, 497/1024]⟩

theorem leaf02_address : leaf02=descend root_h289 [12, 2, 11, 12, 9, 3, 1, 10, 12, 9, 3, 1] :=
  sameCell_sound (by decide +kernel)

theorem leaf02_pass : sharpPass leaf02=true := by decide +kernel

theorem leaf02_strictFCC {p : Chart} (hp : leaf02.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf02_pass hp

noncomputable def leaf03 : Cell :=
  ⟨![439/512, 191/256, 7/16, 7/16, 1/4, 3/8, -3/16, 127/256],
    ![57/64, 99/128, 1/2, 1/2, 5/16, 7/16, -1/8, 1/2]⟩

theorem leaf03_address : leaf03=descend root_h297 [12, 2, 10, 13, 8, 3] :=
  sameCell_sound (by decide +kernel)

theorem leaf03_pass : sharpPass leaf03=true := by decide +kernel

theorem leaf03_strictFCC {p : Chart} (hp : leaf03.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf03_pass hp

noncomputable def leaf04 : Cell :=
  ⟨![439/512, 417/512, 7/16, 7/16, 11/32, 13/32, -1/4, 63/128],
    ![895/1024, 53/64, 1/2, 15/32, 3/8, 27/64, -15/64, 127/256]⟩

theorem leaf04_address : leaf04=descend root_h295 [12, 3, 10, 12, 9, 3, 11, 12, 9, 3, 0, 10, 12, 6] :=
  sameCell_sound (by decide +kernel)

theorem leaf04_pass : sharpPass leaf04=true := by decide +kernel

theorem leaf04_strictFCC {p : Chart} (hp : leaf04.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf04_pass hp

noncomputable def leaf05 : Cell :=
  ⟨![211/256, 205/256, 7/16, 7/16, 5/16, 3/8, -5/32, 127/256],
    ![439/512, 53/64, 1/2, 1/2, 3/8, 13/32, -1/8, 1/2]⟩

theorem leaf05_address : leaf05=descend root_h296 [12, 3, 10, 13, 9, 3, 10, 13] :=
  sameCell_sound (by decide +kernel)

theorem leaf05_pass : sharpPass leaf05=true := by decide +kernel

theorem leaf05_strictFCC {p : Chart} (hp : leaf05.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf05_pass hp

noncomputable def leaf06 : Cell :=
  ⟨![439/512, 205/256, 7/16, 7/16, 1/4, 3/8, -3/16, 127/256],
    ![57/64, 53/64, 1/2, 1/2, 9/32, 13/32, -5/32, 1/2]⟩

theorem leaf06_address : leaf06=descend root_h297 [12, 3, 10, 13, 8, 3, 10, 12, 8] :=
  sameCell_sound (by decide +kernel)

theorem leaf06_pass : sharpPass leaf06=true := by decide +kernel

theorem leaf06_strictFCC {p : Chart} (hp : leaf06.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf06_pass hp

noncomputable def leaf07 : Cell :=
  ⟨![439/512, 205/256, 7/16, 7/16, 11/32, 3/8, -7/32, 63/128],
    ![895/1024, 417/512, 1/2, 1/2, 3/8, 25/64, -3/16, 127/256]⟩

theorem leaf07_address : leaf07=descend root_h295 [12, 3, 10, 12, 9, 3, 10, 13, 9, 2, 0, 10] :=
  sameCell_sound (by decide +kernel)

theorem leaf07_pass : sharpPass leaf07=true := by decide +kernel

theorem leaf07_strictFCC {p : Chart} (hp : leaf07.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf07_pass hp

noncomputable def leaf08 : Cell :=
  ⟨![211/256, 99/128, 7/16, 7/16, 5/16, 13/32, -1/4, 499/1024],
    ![439/512, 205/256, 1/2, 1/2, 11/32, 7/16, -7/32, 125/256]⟩

theorem leaf08_address : leaf08=descend root_h292 [12, 3, 10, 12, 9, 2, 0, 11, 12, 8] :=
  sameCell_sound (by decide +kernel)

theorem leaf08_pass : sharpPass leaf08=true := by decide +kernel

theorem leaf08_strictFCC {p : Chart} (hp : leaf08.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf08_pass hp

noncomputable def leaf09 : Cell :=
  ⟨![439/512, 99/128, 7/16, 7/16, 11/32, 3/8, -3/16, 499/1024],
    ![895/1024, 403/512, 1/2, 1/2, 3/8, 13/32, -5/32, 125/256]⟩

theorem leaf09_address : leaf09=descend root_h292 [12, 3, 10, 13, 9, 2, 1, 10, 12, 9, 2, 0] :=
  sameCell_sound (by decide +kernel)

theorem leaf09_pass : sharpPass leaf09=true := by decide +kernel

theorem leaf09_strictFCC {p : Chart} (hp : leaf09.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf09_pass hp

noncomputable def leaf10 : Cell :=
  ⟨![439/512, 99/128, 7/16, 7/16, 11/32, 7/16, -7/32, 31/64],
    ![895/1024, 403/512, 1/2, 1/2, 3/8, 15/32, -3/16, 497/1024]⟩

theorem leaf10_address : leaf10=descend root_h289 [12, 3, 11, 12, 9, 2, 1, 10, 13, 9, 2, 0] :=
  sameCell_sound (by decide +kernel)

theorem leaf10_pass : sharpPass leaf10=true := by decide +kernel

theorem leaf10_strictFCC {p : Chart} (hp : leaf10.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf10_pass hp

noncomputable def leaf11 : Cell :=
  ⟨![895/1024, 205/256, 7/16, 7/16, 9/32, 3/8, -15/64, 63/128],
    ![57/64, 417/512, 1/2, 1/2, 5/16, 25/64, -7/32, 127/256]⟩

theorem leaf11_address : leaf11=descend root_h295 [12, 3, 10, 12, 8, 3, 10, 12, 9, 2, 1, 10, 13] :=
  sameCell_sound (by decide +kernel)

theorem leaf11_pass : sharpPass leaf11=true := by decide +kernel

theorem leaf11_strictFCC {p : Chart} (hp : leaf11.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf11_pass hp

noncomputable def leaf12 : Cell :=
  ⟨![439/512, 99/128, 7/16, 7/16, 11/32, 13/32, -7/32, 499/1024],
    ![895/1024, 403/512, 1/2, 1/2, 3/8, 7/16, -3/16, 125/256]⟩

theorem leaf12_address : leaf12=descend root_h292 [12, 3, 10, 12, 9, 2, 1, 11, 13, 9, 2, 0] :=
  sameCell_sound (by decide +kernel)

theorem leaf12_pass : sharpPass leaf12=true := by decide +kernel

theorem leaf12_strictFCC {p : Chart} (hp : leaf12.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf12_pass hp

noncomputable def leaf13 : Cell :=
  ⟨![439/512, 205/256, 7/16, 7/16, 5/16, 3/8, -5/32, 249/512],
    ![57/64, 417/512, 1/2, 1/2, 11/32, 13/32, -1/8, 499/1024]⟩

theorem leaf13_address : leaf13=descend root_h291 [12, 3, 10, 13, 9, 3, 1, 10, 13, 8, 2] :=
  sameCell_sound (by decide +kernel)

theorem leaf13_pass : sharpPass leaf13=true := by decide +kernel

theorem leaf13_strictFCC {p : Chart} (hp : leaf13.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf13_pass hp

noncomputable def leaf14 : Cell :=
  ⟨![759/1024, 417/512, 3/16, 1/8, -1/4, -5/32, -13/32, -1/2],
    ![97/128, 53/64, 1/4, 3/16, -7/32, -1/8, -3/8, -7/16]⟩

theorem leaf14_address : leaf14=descend root_a487334 [12, 3, 11, 13, 14, 8, 3, 1, 11, 13, 14, 8, 3, 1] :=
  sameCell_sound (by decide +kernel)

theorem leaf14_pass : sharpPass leaf14=true := by decide +kernel

theorem leaf14_strictFCC {p : Chart} (hp : leaf14.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf14_pass hp

noncomputable def leaf15 : Cell :=
  ⟨![1739/2048, 1521/2048, 5/32, 3/16, 35/128, -63/128, 17/64, -1/2],
    ![439/512, 191/256, 3/16, 13/64, 9/32, -31/64, 35/128, -31/64]⟩

theorem leaf15_address : leaf15=descend root_a532440 [12, 2, 10, 12, 14, 8, 2, 0, 10, 12, 14, 8, 3, 1, 10, 13, 14, 6, 9, 3, 5, 1, 11, 12, 14, 6, 9, 3] :=
  sameCell_sound (by decide +kernel)

theorem leaf15_pass : sharpPass leaf15=true := by decide +kernel

theorem leaf15_strictFCC {p : Chart} (hp : leaf15.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf15_pass hp

noncomputable def leaf16 : Cell :=
  ⟨![1535/2048, 1717/2048, 25/64, 3/16, 1/64, -3/8, -125/256, 31/64],
    ![3087/4096, 431/512, 13/32, 13/64, 3/128, -95/256, -31/64, 1/2]⟩

theorem leaf16_address : leaf16=descend root_a675855 [12, 2, 10, 12, 15, 8, 2, 1, 10, 12, 15, 8, 2, 1, 10, 12, 15, 6, 9, 3, 4, 1, 10, 13, 15, 6, 8, 3, 5, 0, 10, 13] :=
  sameCell_sound (by decide +kernel)

theorem leaf16_pass : sharpPass leaf16=true := by decide +kernel

theorem leaf16_strictFCC {p : Chart} (hp : leaf16.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf16_pass hp

noncomputable def leaf17 : Cell :=
  ⟨![1671/2048, 785/1024, 5/32, 3/32, 11/64, -61/128, 35/128, 15/32],
    ![211/256, 99/128, 3/16, 1/8, 3/16, -15/32, 9/32, 1/2]⟩

theorem leaf17_address : leaf17=descend root_a535868 [12, 2, 10, 12, 15, 8, 3, 1, 10, 12, 15, 9, 3, 1, 11, 13, 15, 7, 9, 3, 5, 1, 11, 13] :=
  sameCell_sound (by decide +kernel)

theorem leaf17_pass : sharpPass leaf17=true := by decide +kernel

theorem leaf17_strictFCC {p : Chart} (hp : leaf17.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf17_pass hp

noncomputable def leaf18 : Cell :=
  ⟨![1671/2048, 785/1024, 5/32, 3/32, 1/8, -61/128, 37/128, 15/32],
    ![211/256, 99/128, 3/16, 1/8, 9/64, -15/32, 19/64, 31/64]⟩

theorem leaf18_address : leaf18=descend root_a535868 [12, 2, 10, 12, 15, 8, 3, 1, 10, 13, 15, 8, 3, 1, 11, 12, 15, 7, 8, 3, 5, 1, 11, 13, 14] :=
  sameCell_sound (by decide +kernel)

theorem leaf18_pass : sharpPass leaf18=true := by decide +kernel

theorem leaf18_strictFCC {p : Chart} (hp : leaf18.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf18_pass hp

noncomputable def leaf19 : Cell :=
  ⟨![657/1024, 487/512, 1/16, 3/16, 0, -1/2, 9/32, -15/32],
    ![337/512, 247/256, 1/8, 1/4, 1/32, -31/64, 19/64, -7/16]⟩

theorem leaf19_address : leaf19=descend root_a890970 [12, 2, 10, 12, 14, 8, 2, 0, 10, 13, 14, 8, 3, 1, 10, 12, 15] :=
  sameCell_sound (by decide +kernel)

theorem leaf19_pass : sharpPass leaf19=true := by decide +kernel

theorem leaf19_strictFCC {p : Chart} (hp : leaf19.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf19_pass hp

noncomputable def leaf20 : Cell :=
  ⟨![337/512, 113/128, 1/8, 1/8, 1/16, 1/16, -1/4, 3/8],
    ![177/256, 233/256, 3/16, 3/16, 1/8, 3/32, -7/32, 7/16]⟩

theorem leaf20_address : leaf20=descend root_a542836 [12, 3, 11, 12, 15, 9, 2, 1, 10, 12, 14] :=
  sameCell_sound (by decide +kernel)

theorem leaf20_pass : sharpPass leaf20=true := by decide +kernel

theorem leaf20_strictFCC {p : Chart} (hp : leaf20.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf20_pass hp

noncomputable def leaf21 : Cell :=
  ⟨![211/256, 99/128, 5/16, 1/16, 3/16, -1/32, 1/32, 7/16],
    ![439/512, 205/256, 3/8, 1/8, 1/4, 0, 1/16, 1/2]⟩

theorem leaf21_address : leaf21=descend root_a688095 [12, 3, 11, 12, 15, 9, 2, 0, 11, 13, 15] :=
  sameCell_sound (by decide +kernel)

theorem leaf21_pass : sharpPass leaf21=true := by decide +kernel

theorem leaf21_strictFCC {p : Chart} (hp : leaf21.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf21_pass hp

noncomputable def leaf22 : Cell :=
  ⟨![371/512, 219/256, 3/8, 3/16, 1/32, -3/8, -15/32, 1/4],
    ![97/128, 445/512, 7/16, 1/4, 1/16, -11/32, -7/16, 5/16]⟩

theorem leaf22_address : leaf22=descend root_a675855 [12, 2, 10, 12, 14, 8, 3, 1, 10, 13, 14, 9, 2] :=
  sameCell_sound (by decide +kernel)

theorem leaf22_pass : sharpPass leaf22=true := by decide +kernel

theorem leaf22_strictFCC {p : Chart} (hp : leaf22.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf22_pass hp

noncomputable def leaf23 : Cell :=
  ⟨![1535/2048, 53/64, 13/32, 3/16, 1/64, -47/128, -1/2, 31/64],
    ![97/128, 855/1024, 7/16, 7/32, 1/32, -23/64, -63/128, 1/2]⟩

theorem leaf23_address : leaf23=descend root_a675855 [12, 2, 10, 12, 15, 8, 2, 1, 10, 12, 15, 8, 2, 1, 10, 12, 15, 6, 9, 2, 5, 1, 11, 12, 15] :=
  sameCell_sound (by decide +kernel)

theorem leaf23_pass : sharpPass leaf23=true := by decide +kernel

theorem leaf23_strictFCC {p : Chart} (hp : leaf23.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf23_pass hp

noncomputable def leaf24 : Cell :=
  ⟨![177/256, 191/256, 7/16, 1/16, 1/4, -1/16, -3/16, -1/2],
    ![371/512, 99/128, 1/2, 1/8, 5/16, 0, -1/8, -3/8]⟩

theorem leaf24_address : leaf24=descend root_a670159 [12, 2, 11, 13, 14, 8, 3, 0] :=
  sameCell_sound (by decide +kernel)

theorem leaf24_pass : sharpPass leaf24=true := by decide +kernel

theorem leaf24_strictFCC {p : Chart} (hp : leaf24.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf24_pass hp

noncomputable def leaf25 : Cell :=
  ⟨![895/1024, 191/256, 1/16, 3/8, 1/8, 25/64, 3/64, -15/32],
    ![57/64, 389/512, 1/8, 7/16, 5/32, 13/32, 1/16, -7/16]⟩

theorem leaf25_address : leaf25=descend root_a617847 [12, 2, 10, 12, 14, 8, 3, 1, 10, 13, 14, 8, 2, 1, 11, 13, 15] :=
  sameCell_sound (by decide +kernel)

theorem leaf25_pass : sharpPass leaf25=true := by decide +kernel

theorem leaf25_strictFCC {p : Chart} (hp : leaf25.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf25_pass hp

noncomputable def leaf26 : Cell :=
  ⟨![439/512, 445/512, 1/4, 5/16, -1/2, 1/8, -31/64, -1/2],
    ![895/1024, 113/128, 5/16, 3/8, -15/32, 9/64, -15/32, -7/16]⟩

theorem leaf26_address : leaf26=descend root_a737895 [12, 2, 10, 12, 14, 8, 3, 1, 10, 12, 14, 8, 3, 0, 10, 13] :=
  sameCell_sound (by decide +kernel)

theorem leaf26_pass : sharpPass leaf26=true := by decide +kernel

theorem leaf26_strictFCC {p : Chart} (hp : leaf26.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf26_pass hp

noncomputable def leaf27 : Cell :=
  ⟨![211/256, 191/256, 1/16, 1/8, -13/32, 1/16, -1/2, -1/2],
    ![439/512, 389/512, 1/8, 3/16, -3/8, 3/32, -15/32, -7/16]⟩

theorem leaf27_address : leaf27=descend root_a505196 [12, 2, 11, 12, 14, 9, 3, 0, 10, 12, 14, 9, 2] :=
  sameCell_sound (by decide +kernel)

theorem leaf27_pass : sharpPass leaf27=true := by decide +kernel

theorem leaf27_strictFCC {p : Chart} (hp : leaf27.Mem p) :
    energy fcc< energy (chartPoint p) :=
  energy_fcc_lt_of_sharpPass leaf27_pass hp

/-! ### Negative controls on the thinnest sampled leaf

`leaf15` has the smallest predicted Lean margin of the sample. Raising
the threshold by twice that margin makes the strict comparison fail,
so the kernel check responds at the scale of the margin. -/

theorem leaf15_threshold_raised_rejected :
    decide (fccThreshold+113477968/974962728041<
      sharpLower leaf15 2 triangleThreeLower)=false := by
  decide +kernel

def leaf15_parent : Cell := descend root_a532440 [12, 2, 10, 12, 14, 8, 2, 0, 10, 12, 14, 8, 3, 1, 10, 13, 14, 6, 9, 3, 5, 1, 11, 12, 14, 6, 9]

theorem leaf15_parent_rejected :
    (sharpCheck leaf15_parent 2 triangleThreeLower &&
      !decide (fccThreshold< sharpLower leaf15_parent 2 triangleThreeLower))=true := by
  decide +kernel

noncomputable def seamBox : Cell :=
  ⟨![895/1024, 99/128, 7/16, 7/16, 9/32, 27/64, -1/4, -1/64],
    ![57/64, 403/512, 1/2, 1/2, 5/16, 7/16, -15/64, 1/64]⟩

theorem seamBox_spacing : spacing (seamCell seamBox)= -1/64 := by decide +kernel

theorem seamBox_rejected :
    (decide (fccThreshold< sharpLower seamBox 2 triangleThreeLower) &&
      !sharpCheck seamBox 2 triangleThreeLower)=true := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.OverlayPlanar.Pilot
