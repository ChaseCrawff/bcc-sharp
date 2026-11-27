import BccSharp.Cover.AdaptiveCheck

set_option autoImplicit false
set_option maxRecDepth 100000

/-! The thinnest Adaptive `X` items (half-shift optical comparisons, route `relativeOptical`, checked by `adaptiveFull` and sound from `LatticeCase`): `x00` is the recorded minimum of stage 7 (gram_basin surplus 1.197e-4), `x01` the next stage-7 value (2.77e-4), both with a saturated anchor of class (0, -1/2, -1/2); `x02` the thinnest of stage 10 (9.73e-4), a PlanarAnchor certificate of the all-half class. Generated. -/

namespace BccSharp.Coulomb.CompactCover.AdaptiveSupport.XItems
open BccSharp.Coulomb.CompactCover.AdaptiveSupport
open BccSharp.Coulomb.CompactCover.AdaptiveOptical

noncomputable def x00Box : Cell := ⟨![(7313 / 8192 : ℚ), (3161 / 4096 : ℚ), (63 / 128 : ℚ), (61 / 128 : ℚ), (-39 / 128 : ℚ), (0 : ℚ), (63 / 128 : ℚ), (-1 / 2 : ℚ)], ![(3665 / 4096 : ℚ), (99 / 128 : ℚ), (1 / 2 : ℚ), (31 / 64 : ℚ), (-77 / 256 : ℚ), (1 / 128 : ℚ), (1 / 2 : ℚ), (-127 / 256 : ℚ)]⟩

noncomputable def x00Labels : Fin 18 → IntVec × Bool :=
  ![(![(0 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(0 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(0 : ℤ), (0 : ℤ), (0 : ℤ)], true), (![(0 : ℤ), (1 : ℤ), (1 : ℤ)], true), (![(0 : ℤ), (-1 : ℤ), (0 : ℤ)], false), (![(0 : ℤ), (1 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (0 : ℤ), (0 : ℤ)], false), (![(1 : ℤ), (0 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (1 : ℤ), (0 : ℤ)], false), (![(1 : ℤ), (-1 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (1 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (0 : ℤ), (0 : ℤ)], true), (![(-1 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(1 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(-1 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(-1 : ℤ), (2 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (-1 : ℤ), (0 : ℤ)], true)]

theorem x00_check : adaptiveFull (fun _ => some (.optical (.saturated false true 0 (1 / 1099511627776 : ℚ) x00Labels ![(0 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ x00Box = true := by
  decide +kernel

noncomputable def x01Box : Cell := ⟨![(7313 / 8192 : ℚ), (3161 / 4096 : ℚ), (63 / 128 : ℚ), (63 / 128 : ℚ), (-19 / 64 : ℚ), (0 : ℚ), (63 / 128 : ℚ), (-1 / 2 : ℚ)], ![(3665 / 4096 : ℚ), (99 / 128 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-75 / 256 : ℚ), (1 / 128 : ℚ), (1 / 2 : ℚ), (-127 / 256 : ℚ)]⟩

noncomputable def x01Labels : Fin 18 → IntVec × Bool :=
  ![(![(0 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(0 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(0 : ℤ), (-1 : ℤ), (0 : ℤ)], false), (![(0 : ℤ), (1 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (0 : ℤ), (0 : ℤ)], false), (![(1 : ℤ), (0 : ℤ), (0 : ℤ)], false), (![(0 : ℤ), (0 : ℤ), (0 : ℤ)], true), (![(0 : ℤ), (1 : ℤ), (1 : ℤ)], true), (![(-1 : ℤ), (1 : ℤ), (0 : ℤ)], false), (![(1 : ℤ), (-1 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (1 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (0 : ℤ), (0 : ℤ)], true), (![(-1 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(-1 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(1 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(-1 : ℤ), (2 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (-1 : ℤ), (0 : ℤ)], true)]

theorem x01_check : adaptiveFull (fun _ => some (.optical (.saturated false true 0 (1 / 1099511627776 : ℚ) x01Labels ![(0 : ℤ), (1 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ x01Box = true := by
  decide +kernel

noncomputable def x02Box : Cell := ⟨![(1773 / 2048 : ℚ), (841 / 1024 : ℚ), (11 / 32 : ℚ), (1 / 16 : ℚ), (35 / 1024 : ℚ), (503 / 1024 : ℚ), (-63 / 128 : ℚ), (-1 / 2 : ℚ)], ![(14201 / 16384 : ℚ), (13463 / 16384 : ℚ), (177 / 512 : ℚ), (33 / 512 : ℚ), (9 / 256 : ℚ), (63 / 128 : ℚ), (-503 / 1024 : ℚ), (-511 / 1024 : ℚ)]⟩

noncomputable def x02Cert : Layered.PlanarAnchorCert where
  depth := 0
  k := (1 / 1099511627776 : ℚ)
  reg :=
    { B := ![![(1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 : ℚ)], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)]]
      N := ![![(1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(0 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]]
      U := ![![(40278574004402 / 70368746877147 : ℚ), (39820714865506 / 70368746877147 : ℚ), (41757726001687 / 70368746877147 : ℚ)], ![(-57700557732457 / 70368746877147 : ℚ), (27979246126882 / 70368746877147 : ℚ), (28975299145906 / 70368746877147 : ℚ)], ![(-206520205534 / 70368746877147 : ℚ), (-50825515155593 / 70368746877147 : ℚ), (48667082259298 / 70368746877147 : ℚ)]]
      f0 := ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]
      wrap := ![(1 : ℤ), (0 : ℤ), (1 : ℤ)] }

theorem x02_check : adaptiveFull (fun _ => some (.optical (.planarAnchor x02Cert ![(1 : ℤ), (0 : ℤ), (0 : ℤ)])))
    ⟨.relativeOptical, adaptiveSource, 0⟩ x02Box = true := by
  decide +kernel

theorem x00_repeat_rejected : adaptiveFull (fun _ => some (.optical (.saturated false true 0 (1 / 1099511627776 : ℚ)
    ![(![(0 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(0 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(0 : ℤ), (0 : ℤ), (0 : ℤ)], true), (![(0 : ℤ), (1 : ℤ), (1 : ℤ)], true), (![(0 : ℤ), (-1 : ℤ), (0 : ℤ)], false), (![(0 : ℤ), (1 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (0 : ℤ), (0 : ℤ)], false), (![(1 : ℤ), (0 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (1 : ℤ), (0 : ℤ)], false), (![(1 : ℤ), (-1 : ℤ), (0 : ℤ)], false), (![(-1 : ℤ), (1 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (0 : ℤ), (0 : ℤ)], true), (![(-1 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(1 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(-1 : ℤ), (0 : ℤ), (1 : ℤ)], true), (![(1 : ℤ), (1 : ℤ), (0 : ℤ)], true), (![(-1 : ℤ), (2 : ℤ), (1 : ℤ)], true), (![(0 : ℤ), (0 : ℤ), (1 : ℤ)], true)]
    ![(0 : ℤ), (1 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ x00Box = false := by
  decide +kernel

theorem x00_class_rejected : adaptiveFull (fun _ => some (.optical (.saturated true true 0 (1 / 1099511627776 : ℚ) x00Labels ![(0 : ℤ), (1 : ℤ), (0 : ℤ)]))) ⟨.relativeOptical, adaptiveSource, 0⟩ x00Box = false := by
  decide +kernel

end BccSharp.Coulomb.CompactCover.AdaptiveSupport.XItems
