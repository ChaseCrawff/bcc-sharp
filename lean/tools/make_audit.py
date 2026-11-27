"""Generate the axiom audit of the scope of the package.

Usage: python make_audit.py <scope.json> <out ScopeAxioms.lean> <out theorems.json>

The generated Lean file imports every module of the scope and

1. lists the axioms declared in modules of the scope (expected: none);
2. runs `Lean.collectAxioms` on every constant defined in a module of the
   scope, internal names included, and reports how many constants use which
   set of axioms, and every constant that uses an axiom other than `propext`,
   `Classical.choice` and `Quot.sound`;
3. prints the statements of the headline theorems (`#check`, full names);
4. runs `#print axioms` on each theorem of the table below.

Run it from the Lake package directory after the build:  lake env lean <ScopeAxioms.lean>
"""
import json
import sys

scope = json.load(open(sys.argv[1], encoding="utf-8"))
out_lean = sys.argv[2]
out_json = sys.argv[3]

P = "BccSharp.Coulomb."

# (item of Section 9.5, what it supports, Lean name, print the statement)
TABLE = [
    # --- definitions and invariances
    ("A", "Fourier coefficients of the periodic Coulomb kernel", P + "periodicGreen_fourier_on_cell", False),
    ("A", "regular limit of the kernel at the origin", P + "periodicGreen_regular_limit", False),
    ("A", "the kernel does not depend on the splitting parameter", P + "periodicGreen_screening_independent", False),
    ("A", "the self term does not depend on the splitting parameter", P + "ewaldRegularSelf_screening_independent", False),
    ("A", "Ewald energy per particle at every splitting parameter", P + "Full.greenPerParticle_screening", False),
    ("A", "two-site energy equals the Ewald energy at every splitting parameter", P + "Full.ewald_energy", True),
    ("A", "positive series (two sites) equals the Ewald energy", P + "green_two_eq_energy", False),
    ("A", "positive series (two sites) at any screening", P + "ScreenedSeries.h₂_screened", False),
    ("A", "positive series (one site) equals the Ewald energy", P + "BravaisCover.oneSiteEnergy_from_normalized", True),
    ("A", "energy unchanged by a sublattice of finite index", P + "greenPerParticle_repetition", False),
    ("A", "energy depends only on the point set", P + "DefectInvariance.energy_of_points_eq", True),
    ("A", "energy invariant under orthogonal maps and translations", P + "DefectInvariance.energy_of_isometric", False),
    ("A", "energy invariant under distance-preserving bijections", P + "Full.energy_of_rigidImage", True),
    ("A", "energy under dilation", P + "greenPerParticle_scale", False),
    ("A", "energy under dilation, two sites", P + "Full.density_energy", False),
    ("A", "independent definition of the defect equals the interface's", P + "SpecBridge.specDefect_one", False),
    ("A", "defect invariant under orthogonal images", P + "DefectInvariance.cappedDefect_orthogonal_image", False),
    ("A", "defect invariant under orthogonal maps and translations", P + "DefectInvariance.defect_of_isometric", False),
    ("A", "defect invariant under distance-preserving bijections", P + "Full.defect_of_rigidImage", True),
    ("A", "defect under change of basis", P + "DefectInvariance.defect_rebase", False),
    ("A", "defect under integer shifts of the offset", P + "DefectInvariance.defect_wrap", False),
    ("A", "defect under exchange of the cosets", P + "DefectInvariance.defect_swap", False),
    ("A", "defect at the second site", P + "DefectInvariance.siteDefect_second_site", False),
    ("A", "defect equal at all points", P + "DefectInvariance.siteDefect_of_mem", True),
    ("A", "defect equal at all points, independent definition", P + "SpecBridge.spec_physical", True),
    ("A", "defect under repetition of the cell", P + "DefectInvariance.repetition_siteDefect", False),
    ("A", "defect under dilation", P + "SpecBridge.spec_dilated", False),
    ("A", "defect is an attained minimum", P + "DefectInvariance.defect_eq_min", False),
    ("A", "every valid pair is a two-coset configuration", P + "SpecBridge.twoCoset_of_valid", False),
    ("A", "every two-coset configuration is represented", P + "SpecBridge.valid_of_twoCoset", False),
    ("A", "unions of two translates", P + "SpecBridge.spec_translates", False),
    ("A", "BCC as rigid image", P + "SpecBridge.isBCC_iff_physical", False),
    ("A", "FCC as rigid image", P + "SpecBridge.isFCC_iff_physical", False),
    # --- constants
    ("B", "BCC primitive-cell energy in its bracket", P + "Constants.bcc_primitive_enclosed", False),
    ("B", "FCC primitive-cell energy in its bracket", P + "Constants.fcc_primitive_enclosed", False),
    ("B", "e_BCC and e_FCC in the fifty-digit brackets", P + "Constants.reference_bounds", True),
    ("B", "gap in its bracket and positive", P + "Constants.reference_gap_checked", True),
    ("B", "gap to twenty digits", P + "Full.gap_value", True),
    # --- lattice case
    ("C", "lattice inequality and its equality case", P + "BravaisCover.StrainAtlas.latticeCase_proved", True),
    ("C", "local balls at BCC and FCC", P + "BravaisCover.localBalls", False),
    ("C", "tangent tables", P + "BravaisCover.TangentCover.Tables.tables_valid", False),
    ("C", "grid of the reduced domain", P + "BravaisCover.TangentCover.Forest.grid_check", False),
    ("C", "cover of the reduced domain (5,671 leaves)", P + "BravaisCover.TangentCover.Forest.forest_checked", False),
    ("C", "BCC strain chart", P + "BravaisCover.StrainAtlas.bccClosed", False),
    ("C", "FCC strain chart", P + "BravaisCover.StrainAtlas.fccClosed", False),
    ("C", "strain charts give the sharp inequality", P + "BravaisCover.StrainAtlas.strainAtlases_sharp", False),
    ("C", "lattice theorem from forest and atlases", P + "BravaisCover.StrainAtlas.latticeCase_from_tangent_forest_atlases", False),
    ("C", "half-period two-site configurations are lattices", P + "primitive_anchor_exists", False),
    ("C", "energy and D = 0 on BCC", P + "GlobalInputs.bccValues_proof", True),
    ("C", "energy and D = 1 on FCC", P + "GlobalInputs.fccValues_proof", True),
    ("C", "D(FCC) = 1", P + "GlobalInputs.fccSaturated_proof", False),
    # --- analytic part of the two-site theorem
    ("D", "compact reduction", P + "GlobalInputs.compact_proof", True),
    ("D", "separation below the FCC energy", P + "GlobalInputs.separated_of_energy", False),
    ("D", "registration, existence, reduced frame", P + "GlobalInputs.register_proof", True),
    ("D", "registration, existence, every frame", P + "Full.register_frame", True),
    ("D", "all analytic inputs", P + "GlobalInputs.globalAnalyticInputs", True),
    ("D", "defect bound from a registration, cost at most 1/2", P + "CompactCover.JLeaf.defect_le_regCost", False),
    ("D", "defect bound from a registration, up to the cutoff", P + "CompactCover.JLeaf.Cutoff.defect_le_regCost_cutoff", True),
    ("D", "defect bound from a registration with annular terms", P + "CompactCover.JLeaf.Cutoff.defect_le_annulus", True),
    ("D", "defect bound on a box, cutoff", P + "CompactCover.JLeaf.Cutoff.defect_le_box_cutoff", False),
    ("D", "defect bound on a box, far", P + "CompactCover.JLeaf.Cutoff.defect_le_box_far", False),
    ("D", "growth of the defect away from an anchor", P + "CompactCover.Layered.defect_transport", True),
    ("D", "growth of the defect, cutoff form", P + "CompactCover.Layered.defect_transport_cutoff", True),
    ("D", "growth of the defect, annular form", P + "CompactCover.Layered.defect_transport_annulus", False),
    ("D", "Montgomery's inequality for the planar theta function", P + "Montgomery.theorem1", True),
    ("D", "Jacobi triple product", P + "Montgomery.jacobi_triple_product", False),
    ("D", "planar expansion of the energy", P + "CompactCover.OverlayPlanar.chart_energy_planar", False),
    ("D", "planar integral above the triangular value", P + "CompactCover.OverlayPlanar.planarRegularized_ge_triangle", False),
    # --- checking functions with soundness proofs
    ("E", "direct leaves of stage 2 (fixed point)", P + "CompactCover.DirectFix.directFix_sound", False),
    ("E", "initial witnesses (fixed point)", P + "CompactCover.EarlyReplay.initialWitnessCheckFix_sound", False),
    ("E", "direct-moment leaves of stage 2 (fixed point)", P + "CompactCover.EarlyReplay.checkWithDirectSidecarFix_sound", False),
    ("E", "stage 2 bulk and phase (fixed point)", P + "CompactCover.EarlyReplay.checkWithStage2Fix_sound", False),
    ("E", "stage 2 with the tangent table (fixed point)", P + "CompactCover.EarlyReplay.checkWithStage2FixT_sound", False),
    ("E", "planar check, numerator form", P + "CompactCover.OverlayPlanar.energy_fcc_lt_of_numeratorCheck", False),
    ("E", "planar check", P + "CompactCover.OverlayPlanar.overlayCheck_sound", False),
    ("E", "planar check, sharpened", P + "CompactCover.OverlayPlanar.overlaySharpCheck_sound", False),
    ("E", "planar check, fixed point", P + "CompactCover.OverlayPlanar.Fix.overlayFixCheck_sound", False),
    ("E", "planar check over earlier checks", P + "CompactCover.OverlayPlanar.Fix.checkWithOverlay_sound", False),
    ("E", "prefix check", P + "CompactCover.OverlayCorpus.corpusCheck_sound", False),
    ("E", "prefix check, fixed point", P + "CompactCover.OverlayCorpus.corpusCheckFix_sound", True),
    ("E", "adaptive support checks", P + "CompactCover.AdaptiveSupport.adaptiveCheck_sound", False),
    ("E", "adaptive support checks with optical kinds", P + "CompactCover.AdaptiveSupport.adaptiveFull_sound", True),
    ("E", "radial gap saturation", P + "CompactCover.AdaptiveOptical.gapSatOk_sound", False),
    ("E", "Jensen leaf check", P + "CompactCover.Jensen.Fix.fLeafCheck_sound", False),
    ("E", "stage 5 phase check", P + "CompactCover.Stage5bPhase.stage5bPhaseCheck_sound", False),
    ("E", "stage 3 leaf check", P + "CompactCover.Stage3Stage6.stage3Check_sound", False),
    ("E", "stage 5 hybrid check", P + "CompactCover.Stage3Stage6.stage5bHybridCheck_sound", False),
    ("E", "stage 5 optical check", P + "CompactCover.Stage5bOptical.stage5bOpticalCheck_sound", False),
    ("E", "stages 4 and 5 check", P + "CompactCover.Stage4Stage5a.stage4stage5aCheck_sound", False),
    ("E", "stage 5 anchored check", P + "CompactCover.Stage4Stage5a.stage5aCheck_sound", False),
    ("E", "stage 6 checker", P + "CompactCover.Stage3Stage6.stage6Check_sound", False),
    ("E", "stage 6 D evaluator", P + "CompactCover.Stage3Stage6.stage6DEval_sound", False),
    ("E", "stage 6 checker with D evaluator", P + "CompactCover.Stage3Stage6.stage6FullCheck_sound", False),
    ("E", "stage 6 hybrid checker", P + "CompactCover.Stage3Stage6.stage6HybridCheck_sound", False),
    ("E", "J leaf", P + "CompactCover.JLeaf.jleaf_sound", False),
    ("E", "F leaf", P + "CompactCover.JLeaf.fleaf_sound", False),
    ("E", "J leaf at any screening", P + "CompactCover.JLeaf.Screened.jleaf_sound_screened", False),
    ("E", "J leaf, fixed point", P + "CompactCover.LeafFix.jleafFix_sound", False),
    ("E", "D leaf, fixed point", P + "CompactCover.LeafFix.dleafFix_sound", False),
    ("E", "F leaf, fixed point", P + "CompactCover.LeafFix.fleafFix_sound", False),
    ("E", "late leaf certificates", P + "CompactCover.LeafFix.certCheck_sound", False),
    ("E", "late leaf check", P + "CompactCover.LeafFix.lateCheck_sound", False),
    ("E", "late leaf check, far", P + "CompactCover.LeafFix.lateCheckFar_sound", False),
    ("E", "planar-anchor relative check", P + "CompactCover.Layered.planarAnchorCheck_sound", False),
    ("E", "half-shift relative check", P + "CompactCover.Layered.halfShiftCheck_sound", False),
    ("E", "far transport", P + "CompactCover.Layered.farTransportOk_sound", False),
    ("E", "relative certificate, far", P + "CompactCover.Layered.planarAnchorCertOkFar_sound", False),
    ("E", "planar-anchor relative check, far", P + "CompactCover.Layered.planarAnchorCheckFar_sound", False),
    ("E", "half-shift relative check, far", P + "CompactCover.Layered.halfShiftCheckFar_sound", False),
    ("E", "planar-fibre relative check, far", P + "CompactCover.Layered.planarFibreCheckFar_sound", False),
    ("E", "anchor catalogue", P + "CompactCover.Layered.catalogueOk_sound", False),
    ("E", "half-shift relative check, catalogue", P + "CompactCover.Layered.halfShiftCheckCat_sound", False),
    ("E", "centered check", P + "CompactCover.Layered.centeredCheck_sound", False),
    ("E", "planar-fibre triangular check", P + "CompactCover.PlanarFibreTri.planarFibreTriCheck_sound", False),
    ("E", "late checker", P + "CompactCover.LatePackets.lateChecker_sound", True),
    ("E", "lattice: tangent E1 leaf check", P + "BravaisCover.TangentE1.leafCheck_sound", False),
    ("E", "lattice: strain atlas leaf check", P + "BravaisCover.StrainTangent.zLeafCheck_sound", False),
    # --- reduction of the theorem
    ("F", "interface statement from analytic inputs and a cover", P + "assemble", False),
    ("F", "statement from a checked corpus", P + "GlobalInputs.assemble_from_cover_corpus_cover", False),
    ("F", "full statement from the interface statement", P + "Full.statementFull_of_statement", False),
    ("F", "full statement equivalent to the interface statement", P + "Full.statementFull_iff", False),
    ("F", "full statement on point sets", P + "Full.StatementFull.physical", True),
    ("F", "soundness of the later checks", P + "FinalAssembly.later_sound", False),
    ("F", "soundness of the prefix check", P + "FinalAssembly.prefix_sound", False),
    ("F", "soundness of the late checker", P + "FinalAssembly.late_sound", False),
    ("F", "soundness of the merged pending checks", P + "FinalAssembly.mergedPending_sound", False),
    ("F", "reduction, first form", P + "FinalAssembly.statementFull_of_replay", True),
    ("F", "reduction, first form, nothing pending", P + "FinalAssembly.statementFull_of_runs", True),
    ("F", "reduction, merged form", P + "FinalAssembly.statementFull_of_replay_merged", True),
    ("F", "reduction, merged form, nothing pending", P + "FinalAssembly.statementFull_of_runs_merged", True),
]

DEFS = [
    P + "TwoSite.Valid", P + "energy", P + "h₂", P + "gKernel", P + "gap", P + "defect", P + "cappedDefect",
    P + "defectTrial", P + "deficit", P + "Statement", P + "Full.StatementFull", P + "LatticeCase",
    P + "oneSiteEnergy", P + "oneSiteDefect", P + "oneSiteDeficit", P + "GlobalAnalyticInputs",
    P + "Registration", "TwoSiteSpec.specDefect", "TwoSiteSpec.specSiteDefect", "TwoSiteSpec.TwoCosetConfig",
    "TwoSiteSpec.TwoTranslates", "TwoSiteSpec.RigidImage", "TwoSiteSpec.RegisteredBound", "TwoSiteSpec.bccUnit",
    "TwoSiteSpec.fccUnit", P + "Constants.bccBracket", P + "Constants.fccBracket", P + "Constants.gapBracket",
]

mods = scope["order"]
L = []
for m in mods:
    L.append(f"import {m}")
L.append("")
L.append("/-! Axiom audit of the scope of the package. Generated by `tools/make_audit.py`; do not edit.")
L.append("Run from the Lake package directory after the build: `lake env lean <this file>`. -/")
L.append("")
L.append("open Lean Elab Command")
L.append("")
L.append("def scopeModules : Array Name := #[")
for i in range(0, len(mods), 4):
    L.append("  " + ", ".join("`" + m for m in mods[i:i + 4]) + ("," if i + 4 < len(mods) else ""))
L.append("]")
L.append("")
L.append("def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]")
L.append("")
L.append('elab "#audit_scope" : command => do')
L.append("  let env ← getEnv")
L.append("  let mut scope : NameSet := {}")
L.append("  for m in scopeModules do scope := scope.insert m")
L.append("  let loaded := scopeModules.filter fun m => env.header.moduleNames.contains m")
L.append('  logInfo m!"scope modules listed: {scopeModules.size}; present in the environment: {loaded.size}"')
L.append("  let mut checked : Nat := 0")
L.append("  let mut internal : Nat := 0")
L.append("  let mut theorems : Nat := 0")
L.append("  let mut declared : Array Name := #[]")
L.append("  let mut bad : Array (Name × Array Name) := #[]")
L.append("  let mut n0 : Nat := 0")
L.append("  let mut sets : Array (List Name × Nat) := #[]")
L.append("  for (name, info) in env.constants.toList do")
L.append("    let some idx := env.getModuleIdxFor? name | continue")
L.append("    let modName := env.header.moduleNames[idx.toNat]!")
L.append("    unless scope.contains modName do continue")
L.append("    if let .axiomInfo _ := info then declared := declared.push name")
L.append("    if let .thmInfo _ := info then theorems := theorems + 1")
L.append("    if name.isInternal then internal := internal + 1")
L.append("    let axs ← liftCoreM <| Lean.collectAxioms name")
L.append("    checked := checked + 1")
L.append("    let key := (axs.qsort (fun a b => a.toString < b.toString)).toList")
L.append("    if key.isEmpty then n0 := n0 + 1")
L.append("    match sets.findIdx? (fun p => p.1 == key) with")
L.append("    | some i => sets := sets.modify i (fun p => (p.1, p.2 + 1))")
L.append("    | none => sets := sets.push (key, 1)")
L.append("    let extra := axs.filter (fun a => !allowedAxioms.contains a)")
L.append("    unless extra.isEmpty do bad := bad.push (name, extra)")
L.append('  logInfo m!"axioms declared in modules of the scope: {declared.size} {declared}"')
L.append('  logInfo m!"constants checked: {checked} (theorems {theorems}, internal names {internal}); using an axiom outside propext, Classical.choice, Quot.sound: {bad.size}"')
L.append("  for (k, n) in sets do")
L.append('    logInfo m!"axiom set {k}: {n} constants"')
L.append("  for (n, a) in bad do")
L.append('    logInfo m!"OFFENDER {n}: {a}"')
L.append("")
L.append("#audit_scope")
L.append("")
L.append("set_option pp.fullNames true")
L.append("")
L.append("-- statements of the headline theorems")
for item, what, name, show in TABLE:
    if show:
        L.append(f"#check @{name}")
L.append("")
L.append("-- definitions named in the scope table (existence check)")
for d in DEFS:
    L.append(f"#check @{d}")
L.append("")
L.append("-- axioms of each theorem of the scope table")
for item, what, name, show in TABLE:
    L.append(f"#print axioms {name}")
L.append("")
with open(out_lean, "w", encoding="utf-8", newline="\n") as fh:
    fh.write("\n".join(L))
with open(out_json, "w", encoding="utf-8", newline="\n") as fh:
    json.dump([dict(item=i, supports=w, name=n, statement_printed=s) for i, w, n, s in TABLE], fh, indent=1,
              ensure_ascii=False)
    fh.write("\n")
print(f"{len(mods)} imports, {len(TABLE)} theorems, {sum(1 for t in TABLE if t[3])} statements printed, {len(DEFS)} definitions")
