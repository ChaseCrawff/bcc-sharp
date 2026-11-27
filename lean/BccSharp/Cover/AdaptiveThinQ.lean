import BccSharp.Cover.AdaptiveCheck

set_option autoImplicit false
set_option maxRecDepth 100000

/-! The thinnest Adaptive `Q` items (half-shift optical comparisons, route `relativeOptical`, checked by `adaptiveFull` and sound from `LatticeCase`), with the sign-aware layered gain of `BccSharp.Cover.AdaptiveLayeredSign` (cosh-refined vertical term), all at split depth 0: `q00` is the recorded minimum of all `Q` (stage 7, surplus 2.18e-4), `q01` the next (5.08e-4), `q02` (3.00e-3); `q03` (5.40e-3) and `q04` (1.44e-2) fail the old separation guard `sepOk` (`q03_sepOk_false`) and pass through `sep2Ok`; `q05` (2.20e-2) failed the gain with `e^A` at every split depth up to 7; `q06`, the recorded minimum of stage 5 (5.70e-4), and `q07` (1.51e-3) have registered cost above 1/2 and take the far route `.planarAnchorsFar` (`BccSharp.Cover.AdaptiveFarQ`). `q08`-`q13` are all six FCC-reference `Q` boxes (stage 5, window 66, in increasing surplus), which have no registration: they take the radial-gap route `.gapSat` (`BccSharp.Cover.AdaptiveGap`, `g = 41/500`) with the layered gain. Negative controls: `q00` with the unsigned layered gain (`.planarAnchor`), with its wrap moved, and with the curvature surplus `k = 1`; `q06` on the budget route `.planarAnchors`; `q08` with the gap `g = 2/25` and `g = 1/10`, and with its wrap moved; the gap check alone on `q00`'s box (`q00_gapOk_false`), and `q00` on the gap route. Generated. -/

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport.QItems
open BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp.Coulomb.CompactCover.AdaptiveOptical

noncomputable def q00Box : Cell := ⟨![(997 / 1024 : ℚ), (1023 / 1024 : ℚ), (0 : ℚ), (1 / 64 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(2011 / 2048 : ℚ), (515 / 512 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

noncomputable def q00Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(140723988071472 / 140737480829677 : ℚ), (-1088892283501 / 140737480829677 : ℚ), (-1616169897888 / 140737480829677 : ℚ)], ![(-1082627271451 / 140737480829677 : ℚ), (-140732237784528 / 140737480829677 : ℚ), (551068629012 / 140737480829677 : ℚ)], ![(-1620373331988 / 140737480829677 : ℚ), (-538583361888 / 140737480829677 : ℚ), (-140727121865371 / 140737480829677 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q00_check : adaptiveFull (fun _ => some (.optical (.planarAnchors q00Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q00Box = true := by
  decide +kernel

noncomputable def q01Box : Cell := ⟨![(507 / 512 : ℚ), (1009 / 1024 : ℚ), (0 : ℚ), (1 / 32 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(2045 / 2048 : ℚ), (127 / 128 : ℚ), (1 / 32 : ℚ), (3 / 64 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

noncomputable def q01Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(70353428289123 / 70368744206501 : ℚ), (-553803556096 / 70368744206501 : ℚ), (-1359628915716 / 70368744206501 : ℚ)], ![(-548565277024 / 70368744206501 : ℚ), (-70366063917819 / 70368744206501 : ℚ), (276199294392 / 70368744206501 : ℚ)], ![(-1361750823036 / 70368744206501 : ℚ), (-265540081032 / 70368744206501 : ℚ), (-70355065804541 / 70368744206501 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q01_check : adaptiveFull (fun _ => some (.optical (.planarAnchors q01Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q01Box = true := by
  decide +kernel

noncomputable def q02Box : Cell := ⟨![(2011 / 2048 : ℚ), (501 / 512 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(507 / 512 : ℚ), (1009 / 1024 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

noncomputable def q02Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(7036606704485 / 7036874367541 : ℚ), (-55140552180 / 7036874367541 : ℚ), (-26953115916 / 7036874367541 : ℚ)], ![(-275187664836 / 35184371837705 : ℚ), (-35183038625848 / 35184371837705 : ℚ), (26897148621 / 7036874367541 : ℚ)], ![(-135814295748 / 35184371837705 : ℚ), (-133426585089 / 35184371837705 : ℚ), (-7036771343272 / 7036874367541 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q02_check : adaptiveFull (fun _ => some (.optical (.planarAnchors q02Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q02Box = true := by
  decide +kernel

noncomputable def q03Box : Cell := ⟨![(507 / 512 : ℚ), (1023 / 1024 : ℚ), (0 : ℚ), (0 : ℚ), (-3 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(2045 / 2048 : ℚ), (515 / 512 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (-1 / 32 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

noncomputable def q03Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(281464171579249 / 281474990575873 : ℚ), (-2201207292228 / 281474990575873 : ℚ), (-1115850953988 / 281474990575873 : ℚ)], ![(-2179006044348 / 281474990575873 : ℚ), (-281412837785671 / 281474990575873 : ℚ), (5498816396472 / 281474990575873 : ℚ)], ![(-1158606729468 / 281474990575873 : ℚ), (-5489966808648 / 281474990575873 : ℚ), (-281419061569351 / 281474990575873 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q03_check : adaptiveFull (fun _ => some (.optical (.planarAnchors q03Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q03Box = true := by
  decide +kernel

noncomputable def q04Box : Cell := ⟨![(2011 / 2048 : ℚ), (515 / 512 : ℚ), (0 : ℚ), (1 / 64 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(507 / 512 : ℚ), (1037 / 1024 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

noncomputable def q04Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(281447531227857 / 281474984504593 : ℚ), (-2179742747640 / 281474984504593 : ℚ), (-3271511754440 / 281474984504593 : ℚ)], ![(-2166918333560 / 281474984504593 : ℚ), (-281464436749425 / 281474984504593 : ℚ), (1114545703632 / 281474984504593 : ℚ)], ![(-3280020204360 / 281474984504593 : ℚ), (-1089251460368 / 281474984504593 : ℚ), (-281453765120625 / 281474984504593 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q04_check : adaptiveFull (fun _ => some (.optical (.planarAnchors q04Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q04Box = true := by
  decide +kernel

noncomputable def q05Box : Cell := ⟨![(2011 / 2048 : ℚ), (1023 / 1024 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ), (-31 / 64 : ℚ)], ![(507 / 512 : ℚ), (515 / 512 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ), (-15 / 32 : ℚ)]⟩

noncomputable def q05Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(4330058797315 / 4330384198903 : ℚ), (-50358806922 / 4330384198903 : ℚ), (-16796204010 / 4330384198903 : ℚ)], ![(-3269052492786 / 281474972928695 : ℚ), (-56290767214137 / 56294994585739 : ℚ), (1100837001998 / 281474972928695 : ℚ)], ![(-1104473106402 / 281474972928695 : ℚ), (-217614930034 / 56294994585739 : ℚ), (-281470702947789 / 281474972928695 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q05_check : adaptiveFull (fun _ => some (.optical (.planarAnchors q05Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q05Box = true := by
  decide +kernel

noncomputable def q06Box : Cell := ⟨![(1977 / 2048 : ℚ), (1009 / 1024 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 64 : ℚ), (31 / 64 : ℚ), (-31 / 64 : ℚ), (-1 / 2 : ℚ)], ![(997 / 1024 : ℚ), (127 / 128 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (-15 / 32 : ℚ), (-31 / 64 : ℚ)]⟩

noncomputable def q06Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(35183856194613 / 35184370444367 : ℚ), (-136340274006 / 35184370444367 : ℚ), (-132658105378 / 35184370444367 : ℚ)], ![(-135835008646 / 35184370444367 : ℚ), (-35183853047502 / 35184370444367 : ℚ), (134004285963 / 35184370444367 : ℚ)], ![(-133175424402 / 35184370444367 : ℚ), (-133490179093 / 35184370444367 : ℚ), (-35183865169206 / 35184370444367 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q06_check : adaptiveFull (fun _ => some (.optical (.planarAnchorsFar q06Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q06Box = true := by
  decide +kernel

noncomputable def q07Box : Cell := ⟨![(997 / 1024 : ℚ), (127 / 128 : ℚ), (0 : ℚ), (1 / 64 : ℚ), (-1 / 32 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(2011 / 2048 : ℚ), (1023 / 1024 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 64 : ℚ), (1 / 2 : ℚ), (-31 / 64 : ℚ), (-31 / 64 : ℚ)]⟩

noncomputable def q07Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      N := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)]]
      U := ![![(281447868201681 / 281474972697505 : ℚ), (-2197832619892 / 281474972697505 : ℚ), (-645825721548 / 56294994539501 : ℚ)], ![(-432088445796 / 56294994539501 : ℚ), (-56289562966533 / 56294994539501 : ℚ), (651775125464 / 56294994539501 : ℚ)], ![(-3254263229308 / 281474972697505 : ℚ), (-3233776855944 / 281474972697505 : ℚ), (-56287516453701 / 56294994539501 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem q07_check : adaptiveFull (fun _ => some (.optical (.planarAnchorsFar q07Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q07Box = true := by
  decide +kernel

noncomputable def q08Box : Cell := ⟨![(1807 / 2048 : ℚ), (233 / 256 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 128 : ℚ), (31 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)], ![(3631 / 4096 : ℚ), (1871 / 2048 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem q08_check : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q08Box = true := by
  decide +kernel

noncomputable def q09Box : Cell := ⟨![(1807 / 2048 : ℚ), (233 / 256 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (31 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)], ![(3631 / 4096 : ℚ), (1871 / 2048 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (1 / 128 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem q09_check : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q09Box = true := by
  decide +kernel

noncomputable def q10Box : Cell := ⟨![(3631 / 4096 : ℚ), (233 / 256 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (1 / 128 : ℚ), (31 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)], ![(57 / 64 : ℚ), (1871 / 2048 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem q10_check : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q10Box = true := by
  decide +kernel

noncomputable def q11Box : Cell := ⟨![(3631 / 4096 : ℚ), (233 / 256 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (0 : ℚ), (31 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)], ![(57 / 64 : ℚ), (1871 / 2048 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ), (1 / 128 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem q11_check : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q11Box = true := by
  decide +kernel

noncomputable def q12Box : Cell := ⟨![(3631 / 4096 : ℚ), (233 / 256 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 128 : ℚ), (31 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)], ![(57 / 64 : ℚ), (1871 / 2048 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem q12_check : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q12Box = true := by
  decide +kernel

noncomputable def q13Box : Cell := ⟨![(3631 / 4096 : ℚ), (233 / 256 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (31 / 64 : ℚ), (31 / 64 : ℚ), (-1 / 2 : ℚ)], ![(57 / 64 : ℚ), (1871 / 2048 : ℚ), (1 / 64 : ℚ), (1 / 64 : ℚ), (1 / 128 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-63 / 128 : ℚ)]⟩

theorem q13_check : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ q13Box = true := by
  decide +kernel

theorem q00_unsigned_rejected : adaptiveFull (fun _ => some (.optical (.planarAnchor q00Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q00Box = false := by
  decide +kernel

theorem q00_wrap_rejected : adaptiveFull (fun _ => some (.optical (.planarAnchors q00Cert ![(2 : ℤ), (0 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q00Box = false := by
  decide +kernel

theorem q00_k1_rejected : adaptiveFull (fun _ => some (.optical (.planarAnchors { q00Cert with k := 1 } ![(1 : ℤ), (0 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q00Box = false := by
  decide +kernel

theorem q06_budget_rejected : adaptiveFull (fun _ => some (.optical (.planarAnchors q06Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q06Box = false := by
  decide +kernel

theorem q08_gap_small_rejected : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (2 / 25 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q08Box = false := by
  decide +kernel

theorem q08_gap_tenth_rejected : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (1 / 10 : ℚ) ![(1 : ℤ), (1 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q08Box = false := by
  decide +kernel

theorem q08_gap_wrap_rejected : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(2 : ℤ), (1 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q08Box = false := by
  decide +kernel

theorem q00_gapOk_false : AdaptiveGap.gapOk (41 / 500 : ℚ) q00Box = false := by
  decide +kernel

theorem q00_gap_rejected : adaptiveFull (fun _ => some (.optical (.gapSat 0 (1 / 1099511627776 : ℚ) (41 / 500 : ℚ) ![(1 : ℤ), (0 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ q00Box = false := by
  decide +kernel

theorem q03_sepOk_false : Layered.sepOk (shiftCell q03Box (Layered.seamShiftW ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])) = false := by
  decide +kernel

theorem q03_sep2Ok : Layered.sep2Ok q03Box = true := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.AdaptiveSupport.QItems
