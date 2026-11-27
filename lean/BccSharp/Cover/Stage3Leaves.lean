import BccSharp.Cover.Stage3
import BccSharp.Cover.Stage6FLeaves
import BccSharp.TwoSite.GoodPoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # The thinnest Stage3 leaves through `stage3Check` (generated)

Generated. Each leaf is the
literal `hullN` refined along the stage-3 seed and the leaf's split path (`leafN_address`,
kernel: `FLeaves.seedOk`). The kernel checks only that refinement; that `hullN` is the Direct
hull of the leaf's original is not checked here. Each leaf has:
* a `supportGainCheck` hint from the Adaptive proposal (`leafN_hint`, kernel), or the
  box-built Jensen check with the source's profile (`leafN_check`, kernel);
* `energy fcc < energy` at every good point of the leaf (`leafN_fcc`);
* the acceptance of the leaf's witness by `stage3Check` (`leafN_stage3`): for a hint leaf, for
  every hint function giving the witness this hint; for a box-built leaf, for every hint
  function;
* the coverage theorem (a good point, or no reduced point). -/

namespace BccSharp.Coulomb.CompactCover.Stage3Stage6.Stage3Leaves
open BccSharp
open BccSharp.Coverage
open BccSharp.Coulomb.CompactCover
open BccSharp.Coulomb.CompactCover.LatePackets
open BccSharp.Coulomb.CompactCover.Stage3Stage6

def hull0 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)]⟩

def leaf0 : Cell := ⟨![(3631 / 4096 : ℚ), (785 / 1024 : ℚ), (63 / 128 : ℚ), (0 : ℚ), (0 : ℚ), (89 / 256 : ℚ), (21 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (1577 / 2048 : ℚ), (1 / 2 : ℚ), (1 / 128 : ℚ), (1 / 128 : ℚ), (45 / 128 : ℚ), (85 / 256 : ℚ), (-63 / 128 : ℚ)]⟩

theorem leaf0_address : FLeaves.seedOk hull0 "2bcdeeee13e18bc836ad58316ac582165bc" leaf0 = true := by
  decide +kernel

noncomputable def leaf0Hint : SupportHint where
  terms := [
    ⟨.cross, -2, -1, 0, 57022734691126119791⟩,
    ⟨.cross, -2, -1, 1, 56943584801812147718⟩,
    ⟨.cross, -2, 0, 0, 34234394936321139473⟩,
    ⟨.cross, -2, 0, 1, 34233925054776117198⟩,
    ⟨.cross, -2, 1, 0, 34309475028616598205⟩,
    ⟨.cross, -2, 1, 1, 34387376784956826582⟩,
    ⟨.cross, -2, 2, 0, 57217887005151634792⟩,
    ⟨.cross, -2, 2, 1, 57375515100362647831⟩,
    ⟨.cross, -1, -2, 0, 57083290175998470387⟩,
    ⟨.cross, -1, -2, 1, 56987910078337312367⟩,
    ⟨.cross, -1, -1, 0, 22826754945885187278⟩,
    ⟨.cross, -1, -1, 1, 22810947960158641369⟩,
    ⟨.cross, -1, 0, -1, 73451736205687468058⟩,
    ⟨.cross, -1, 0, 0, 11441857119681226628⟩,
    ⟨.cross, -1, 0, 1, 11505737046169292768⟩,
    ⟨.cross, -1, 1, 0, 22889983968234387276⟩,
    ⟨.cross, -1, 1, 1, 23032486273727367200⟩,
    ⟨.cross, -1, 2, 0, 57220206566277343763⟩,
    ⟨.cross, -1, 2, 1, 57441884074023029444⟩,
    ⟨.cross, 0, -2, 0, 34479146307644706964⟩,
    ⟨.cross, 0, -2, 1, 34447969483627166250⟩,
    ⟨.cross, 0, -1, -1, 73658526507607811982⟩,
    ⟨.cross, 0, -1, 0, 11639700997881964273⟩,
    ⟨.cross, 0, -1, 1, 11688353316189478975⟩,
    ⟨.cross, 0, 0, -1, 73617975759957072618⟩,
    ⟨.cross, 0, 0, 0, 11670987102011873910⟩,
    ⟨.cross, 0, 0, 1, 11798471211269476578⟩,
    ⟨.cross, 0, 1, 0, 34541414490778967948⟩,
    ⟨.cross, 0, 1, 1, 34746985130035124718⟩,
    ⟨.cross, 1, -2, 0, 34922716941878596587⟩,
    ⟨.cross, 1, -2, 1, 34955447516173888420⟩,
    ⟨.cross, 1, -1, 0, 23485051245457751860⟩,
    ⟨.cross, 1, -1, 1, 23596905694490321448⟩,
    ⟨.cross, 1, 0, 0, 34908343658873344665⟩,
    ⟨.cross, 1, 0, 1, 35099025405674446613⟩,
    ⟨.cross, 1, 1, 0, 69200188724904327513⟩,
    ⟨.cross, 1, 1, 1, 69469551680354734962⟩,
    ⟨.cross, 2, -2, 0, 58412218865823185035⟩,
    ⟨.cross, 2, -2, 1, 58508156603746595540⟩,
    ⟨.cross, 2, -1, 0, 58351997711439077086⟩,
    ⟨.cross, 2, -1, 1, 58527644463172859647⟩,
    ⟨.period, 0, 0, 1, 30986927700464391976⟩,
    ⟨.period, 0, 1, -1, 42332047714189479101⟩,
    ⟨.period, 0, 1, 0, 11421313537998885310⟩,
    ⟨.period, 0, 1, 1, 42489289233870257585⟩,
    ⟨.period, 0, 2, 0, 45685254151995541238⟩,
    ⟨.period, 1, -2, -1, 65398633754720166802⟩,
    ⟨.period, 1, -2, 0, 34363801182771902121⟩,
    ⟨.period, 1, -2, 1, 65211263158892641444⟩,
    ⟨.period, 1, -1, -1, 42539582467479094618⟩,
    ⟨.period, 1, -1, 0, 11535174374752041912⟩,
    ⟨.period, 1, -1, 1, 42509382323502758027⟩,
    ⟨.period, 1, 0, -1, 42409990732239007906⟩,
    ⟨.period, 1, 0, 0, 11492099228170201228⟩,
    ⟨.period, 1, 0, 1, 42536364243056189072⟩,
    ⟨.period, 1, 1, -1, 65128325773895010040⟩,
    ⟨.period, 1, 1, 0, 34320638277472831225⟩,
    ⟨.period, 1, 1, 1, 65411718169270845076⟩,
    ⟨.period, 2, -2, 0, 46140697512501205354⟩,
    ⟨.period, 2, -1, -1, 65562597897083431586⟩,
    ⟨.period, 2, -1, 0, 34661771388618514223⟩,
    ⟨.period, 2, -1, 1, 65658548642295189251⟩,
    ⟨.period, 2, 0, 0, 45968396912680804912⟩,
    ⟨.reciprocal, 0, 0, 2, 27256045186879130834⟩,
    ⟨.reciprocal, 0, 1, -2, 51800132484023061178⟩,
    ⟨.reciprocal, 0, 1, -1, 31353805149745247260⟩,
    ⟨.reciprocal, 0, 1, 0, 24504820128676984455⟩,
    ⟨.reciprocal, 0, 1, 1, 31278859407626212453⟩,
    ⟨.reciprocal, 0, 1, 2, 51649767623543203819⟩,
    ⟨.reciprocal, 1, 0, -2, 51629384163739302063⟩,
    ⟨.reciprocal, 1, 0, -1, 31177132913652883320⟩,
    ⟨.reciprocal, 1, 0, 0, 24356704652033734848⟩,
    ⟨.reciprocal, 1, 0, 1, 31139314222783517870⟩,
    ⟨.reciprocal, 1, 0, 2, 51553527682054325134⟩,
    ⟨.reciprocal, 1, 1, -2, 51947456418595450410⟩,
    ⟨.reciprocal, 1, 1, -1, 31457218165487340009⟩,
    ⟨.reciprocal, 1, 1, 0, 24599675913879020158⟩,
    ⟨.reciprocal, 1, 1, 1, 31344135715093281872⟩,
    ⟨.reciprocal, 1, 1, 2, 51720632382915468236⟩]
  cut := none
  allocs := [
    ⟨66, 71, 76, false, true, 136278021848969981636351576⟩,
    ⟨68, 71, 78, false, true, 185794144923740874019531⟩,
    ⟨64, 71, 74, false, true, 172193458255500286074071⟩]

theorem leaf0_hint : hintCheck (some leaf0Hint) leaf0 = true := by
  decide +kernel

theorem leaf0_fcc (p : Chart) (hp : leaf0.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  hintCheck_sound leaf0_hint p hp gp

theorem leaf0_stage3 (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (hs : w.source = "stage3/Z") (hr : w.route = .strictFCC)
    (hh : hint w = some leaf0Hint) : stage3Check hint w leaf0 = true := by
  simp only [stage3Check, hr, hs, hh, stage3Profile, leaf0_hint, Bool.true_or, decide_true,
    Bool.true_and]

def leaf0Pt : Fin 8 → ℚ := ![(14541 / 16384 : ℚ), (6301 / 8192 : ℚ), (511 / 1024 : ℚ), (1 / 256 : ℚ), (1 / 256 : ℚ), (179 / 512 : ℚ), (169 / 512 : ℚ), (-127 / 256 : ℚ)]

theorem leaf0_nonvacuous : ∃ p : Chart, leaf0.Mem p ∧ good p := by
  have hall : ∀ i, leaf0.lo i ≤ leaf0Pt i ∧ leaf0Pt i ≤ leaf0.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf0Pt i : ℝ), fun i => ?_,
    good_of_check leaf0Pt (0) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def hull1 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (-1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)]⟩

def leaf1 : Cell := ⟨![(3631 / 4096 : ℚ), (1577 / 2048 : ℚ), (63 / 128 : ℚ), (0 : ℚ), (-1 / 128 : ℚ), (47 / 128 : ℚ), (41 / 128 : ℚ), (63 / 128 : ℚ)],
    ![(57 / 64 : ℚ), (99 / 128 : ℚ), (1 / 2 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (21 / 64 : ℚ), (1 / 2 : ℚ)]⟩

theorem leaf1_address : FLeaves.seedOk hull1 "cdffff213bf9bc9316bc59316bd59315" leaf1 = true := by
  decide +kernel

noncomputable def leaf1Hint : SupportHint where
  terms := [
    ⟨.cross, -2, -1, -1, 56416172519672782739⟩,
    ⟨.cross, -2, -1, 0, 56126637135528172259⟩,
    ⟨.cross, -2, 0, -1, 33757493368572333014⟩,
    ⟨.cross, -2, 0, 0, 33489143227518102397⟩,
    ⟨.cross, -2, 1, -1, 34093633408101533047⟩,
    ⟨.cross, -2, 1, 0, 33846496143878901155⟩,
    ⟨.cross, -2, 2, -1, 57394170196487864248⟩,
    ⟨.cross, -2, 2, 0, 57167114485350495432⟩,
    ⟨.cross, -1, -2, -1, 56853275090873519574⟩,
    ⟨.cross, -1, -2, 0, 56663882495880783069⟩,
    ⟨.cross, -1, -1, -1, 22574030484609866908⟩,
    ⟨.cross, -1, -1, 0, 22405155348778475767⟩,
    ⟨.cross, -1, 0, -2, 72970458805331971995⟩,
    ⟨.cross, -1, 0, -1, 11283496541425385906⟩,
    ⟨.cross, -1, 0, 0, 11135389632861078671⟩,
    ⟨.cross, -1, 0, 1, 72526826359492357956⟩,
    ⟨.cross, -1, 1, -1, 22972597115535979015⟩,
    ⟨.cross, -1, 1, 0, 22846858290226343156⟩,
    ⟨.cross, -1, 2, -1, 57685939150628892780⟩,
    ⟨.cross, -1, 2, 0, 57580477608409461794⟩,
    ⟨.cross, 0, -2, -1, 34641039228241214505⟩,
    ⟨.cross, 0, -2, 0, 34571842963939340462⟩,
    ⟨.cross, 0, -1, -1, 11744557714686290060⟩,
    ⟨.cross, 0, -1, 0, 11696776601344243231⟩,
    ⟨.cross, 0, -1, 1, 73172593172675918142⟩,
    ⟨.cross, 0, 0, -1, 11874859035286219880⟩,
    ⟨.cross, 0, 0, 0, 11847441924787704887⟩,
    ⟨.cross, 0, 0, 1, 73364338454201928220⟩,
    ⟨.cross, 0, 1, -1, 34975862212360076144⟩,
    ⟨.cross, 0, 1, 0, 34970630637809128049⟩,
    ⟨.cross, 1, -2, -1, 35508330430178589455⟩,
    ⟨.cross, 1, -2, 0, 35560426927318409629⟩,
    ⟨.cross, 1, -1, -1, 24002485453200698215⟩,
    ⟨.cross, 1, -1, 0, 24075271998947142295⟩,
    ⟨.cross, 1, 0, -1, 35501947440748163678⟩,
    ⟨.cross, 1, 0, 0, 35595311462687662835⟩,
    ⟨.cross, 1, 1, -1, 69986947999647807019⟩,
    ⟨.cross, 1, 1, 0, 70101477848196429232⟩,
    ⟨.cross, 2, -2, -1, 59447912313099520743⟩,
    ⟨.cross, 2, -2, 0, 59620788417964094458⟩,
    ⟨.cross, 2, -1, -1, 59296299171222504939⟩,
    ⟨.cross, 2, -1, 0, 59488847153561557031⟩,
    ⟨.period, 0, 0, 1, 30714256683946042274⟩,
    ⟨.period, 0, 1, -1, 42188817405340189395⟩,
    ⟨.period, 0, 1, 0, 11479307437128220923⟩,
    ⟨.period, 0, 1, 1, 42231154928029836975⟩,
    ⟨.period, 0, 2, 0, 45917229748512883691⟩,
    ⟨.period, 1, -2, -1, 65260840290004424085⟩,
    ⟨.period, 1, -2, 0, 34670107792103499062⟩,
    ⟨.period, 1, -2, 1, 65419669360022403516⟩,
    ⟨.period, 1, -1, -1, 42261794729146737712⟩,
    ⟨.period, 1, -1, 0, 11630333780288504770⟩,
    ⟨.period, 1, -1, 1, 42460581676231757514⟩,
    ⟨.period, 1, 0, -1, 42108995738158022285⟩,
    ⟨.period, 1, 0, 0, 11492099228170201228⟩,
    ⟨.period, 1, 0, 1, 42348339275379107509⟩,
    ⟨.period, 1, 1, -1, 64920273832470180194⟩,
    ⟨.period, 1, 1, 0, 34341466670195039595⟩,
    ⟨.period, 1, 1, 1, 65201064419357603067⟩,
    ⟨.period, 2, -2, 0, 46521335121154019078⟩,
    ⟨.period, 2, -1, -1, 65294319538989789027⟩,
    ⟨.period, 2, -1, 0, 34794096287069066620⟩,
    ⟨.period, 2, -1, 1, 65731559550272584123⟩,
    ⟨.period, 2, 0, 0, 45968396912680804912⟩,
    ⟨.reciprocal, 0, 0, 2, 27498550911937534725⟩,
    ⟨.reciprocal, 0, 1, -2, 51691084465395692830⟩,
    ⟨.reciprocal, 0, 1, -1, 31130123156797290901⟩,
    ⟨.reciprocal, 0, 1, 0, 24288382277811831878⟩,
    ⟨.reciprocal, 0, 1, 1, 31191047487348332311⟩,
    ⟨.reciprocal, 0, 1, 2, 51813408013959786302⟩,
    ⟨.reciprocal, 1, -1, 0, 72585791500968702769⟩,
    ⟨.reciprocal, 1, 0, -2, 51951613043311592350⟩,
    ⟨.reciprocal, 1, 0, -1, 31231506887133812062⟩,
    ⟨.reciprocal, 1, 0, 0, 24265572392023601337⟩,
    ⟨.reciprocal, 1, 0, 1, 31057851775230405473⟩,
    ⟨.reciprocal, 1, 0, 2, 51603527455586126518⟩,
    ⟨.reciprocal, 1, 1, -2, 52208376240632630250⟩,
    ⟨.reciprocal, 1, 1, -1, 31518980170805153555⟩,
    ⟨.reciprocal, 1, 1, 0, 24583979139284444784⟩,
    ⟨.reciprocal, 1, 1, 1, 31406699975953893184⟩,
    ⟨.reciprocal, 1, 1, 2, 51983354591436180423⟩]
  cut := none
  allocs := [
    ⟨67, 73, 78, false, true, 138240733607834880741155470⟩,
    ⟨67, 75, 80, false, true, 173248293856373364237553⟩,
    ⟨65, 73, 76, false, true, 160566917472596217762685⟩]

theorem leaf1_hint : hintCheck (some leaf1Hint) leaf1 = true := by
  decide +kernel

theorem leaf1_fcc (p : Chart) (hp : leaf1.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  hintCheck_sound leaf1_hint p hp gp

theorem leaf1_stage3 (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (hs : w.source = "stage3/Z") (hr : w.route = .strictFCC)
    (hh : hint w = some leaf1Hint) : stage3Check hint w leaf1 = true := by
  simp only [stage3Check, hr, hs, hh, stage3Profile, leaf1_hint, Bool.true_or, decide_true,
    Bool.true_and]

def leaf1Pt : Fin 8 → ℚ := ![(7279 / 8192 : ℚ), (3161 / 4096 : ℚ), (127 / 256 : ℚ), (1 / 128 : ℚ), (-1 / 256 : ℚ), (95 / 256 : ℚ), (83 / 256 : ℚ), (127 / 256 : ℚ)]

theorem leaf1_nonvacuous : ∃ p : Chart, leaf1.Mem p ∧ good p := by
  have hall : ∀ i, leaf1.lo i ≤ leaf1Pt i ∧ leaf1Pt i ≤ leaf1.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf1Pt i : ℝ), fun i => ?_,
    good_of_check leaf1Pt (0) (0) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def hull2 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)]⟩

def leaf2 : Cell := ⟨![(7279 / 8192 : ℚ), (785 / 1024 : ℚ), (63 / 128 : ℚ), (0 : ℚ), (0 : ℚ), (21 / 64 : ℚ), (21 / 64 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (1577 / 2048 : ℚ), (1 / 2 : ℚ), (1 / 128 : ℚ), (1 / 128 : ℚ), (85 / 256 : ℚ), (85 / 256 : ℚ), (-63 / 128 : ℚ)]⟩

theorem leaf2_address : FLeaves.seedOk hull2 "2bcdeeee13e18ac836bd58316ac582165ac1" leaf2 = true := by
  decide +kernel

noncomputable def leaf2Hint : SupportHint where
  terms := [
    ⟨.cross, -2, -1, 0, 57853055900772706021⟩,
    ⟨.cross, -2, -1, 1, 57779294051274903681⟩,
    ⟨.cross, -2, 0, 0, 34783392381695408643⟩,
    ⟨.cross, -2, 0, 1, 34786126421953325121⟩,
    ⟨.cross, -2, 1, 0, 34645641231145907307⟩,
    ⟨.cross, -2, 1, 1, 34724562818261918867⟩,
    ⟨.cross, -2, 2, 0, 57401967161818460001⟩,
    ⟨.cross, -2, 2, 1, 57558000029153818221⟩,
    ⟨.cross, -1, -2, 0, 57767789050759690527⟩,
    ⟨.cross, -1, -2, 1, 57676972352422352673⟩,
    ⟨.cross, -1, -1, 0, 23230096938264419886⟩,
    ⟨.cross, -1, -1, 1, 23216669247341500867⟩,
    ⟨.cross, -1, 0, -1, 73541114087442221911⟩,
    ⟨.cross, -1, 0, 0, 11624441384215977708⟩,
    ⟨.cross, -1, 0, 1, 11687944787486899162⟩,
    ⟨.cross, -1, 1, 0, 22923519429214829256⟩,
    ⟨.cross, -1, 1, 1, 23063140971157893730⟩,
    ⟨.cross, -1, 2, 0, 57180059867640666311⟩,
    ⟨.cross, -1, 2, 1, 57397262814222778399⟩,
    ⟨.cross, 0, -2, 0, 34660303373102337636⟩,
    ⟨.cross, 0, -2, 1, 34630252435136937649⟩,
    ⟨.cross, 0, -1, -1, 73528952933996475557⟩,
    ⟨.cross, 0, -1, 0, 11602974541428704471⟩,
    ⟨.cross, 0, -1, 1, 11650248910246720271⟩,
    ⟨.cross, 0, 0, -1, 73349980998529903702⟩,
    ⟨.cross, 0, 0, 0, 11494549995594548971⟩,
    ⟨.cross, 0, 0, 1, 11618915728908259556⟩,
    ⟨.cross, 0, 1, 0, 34295200973410625338⟩,
    ⟨.cross, 0, 1, 1, 34495765196436009372⟩,
    ⟨.cross, 1, -2, 0, 34606663515323798824⟩,
    ⟨.cross, 1, -2, 1, 34637639967731427386⟩,
    ⟨.cross, 1, -1, 0, 23032449734581263355⟩,
    ⟨.cross, 1, -1, 1, 23140517821345340791⟩,
    ⟨.cross, 1, 0, 0, 34380279460617285705⟩,
    ⟨.cross, 1, 0, 1, 34565130137202227644⟩,
    ⟨.cross, 1, 1, 0, 68664095400110928794⟩,
    ⟨.cross, 1, 1, 1, 68925443194318020664⟩,
    ⟨.cross, 2, -2, 0, 57607128948539132049⟩,
    ⟨.cross, 2, -2, 1, 57698595107260301662⟩,
    ⟨.cross, 2, -1, 0, 57472247078964459616⟩,
    ⟨.cross, 2, -1, 1, 57641238146975808011⟩,
    ⟨.period, 0, 0, 1, 30940024025871232510⟩,
    ⟨.period, 0, 1, -1, 42325608337354486126⟩,
    ⟨.period, 0, 1, 0, 11455320621126213448⟩,
    ⟨.period, 0, 1, 1, 42478616241045980668⟩,
    ⟨.period, 0, 2, 0, 45821282484504853793⟩,
    ⟨.period, 1, -2, -1, 65349717998344509012⟩,
    ⟨.period, 1, -2, 0, 34362730091945879458⟩,
    ⟨.period, 1, -2, 1, 65165071565871300422⟩,
    ⟨.period, 1, -1, -1, 42463368501253174083⟩,
    ⟨.period, 1, -1, 0, 11500631752958221295⟩,
    ⟨.period, 1, -1, 1, 42431655801243198277⟩,
    ⟨.period, 1, 0, -1, 42383191319513568226⟩,
    ⟨.period, 1, 0, 0, 11492099228170201228⟩,
    ⟨.period, 1, 0, 1, 42503815527923078786⟩,
    ⟨.period, 1, 1, -1, 65227637958631869048⟩,
    ⟨.period, 1, 1, 0, 34423195079014345825⟩,
    ⟨.period, 1, 1, 1, 65501046437125959402⟩,
    ⟨.period, 2, -2, 0, 46002526998339847473⟩,
    ⟨.period, 2, -1, -1, 65455303217747539647⟩,
    ⟨.period, 2, -1, 0, 34558679034917469440⟩,
    ⟨.period, 2, -1, 1, 65543991065554084245⟩,
    ⟨.period, 2, 0, 0, 45968396912680804912⟩,
    ⟨.reciprocal, 0, 0, 2, 27256045186879130834⟩,
    ⟨.reciprocal, 0, 1, -2, 51798622599610887460⟩,
    ⟨.reciprocal, 0, 1, -1, 31353048730051531755⟩,
    ⟨.reciprocal, 0, 1, 0, 24504817187194764869⟩,
    ⟨.reciprocal, 0, 1, 1, 31279609930862451081⟩,
    ⟨.reciprocal, 0, 1, 2, 51651271624990938366⟩,
    ⟨.reciprocal, 1, 0, -2, 51698604675029931132⟩,
    ⟨.reciprocal, 1, 0, -1, 31230661143530492621⟩,
    ⟨.reciprocal, 1, 0, 0, 24401504843006985559⟩,
    ⟨.reciprocal, 1, 0, 1, 31195897627216411274⟩,
    ⟨.reciprocal, 1, 0, 2, 51629017868244737404⟩,
    ⟨.reciprocal, 1, 1, -2, 51869302693269127789⟩,
    ⟨.reciprocal, 1, 1, -1, 31364206838060399352⟩,
    ⟨.reciprocal, 1, 1, 0, 24498609580268422469⟩,
    ⟨.reciprocal, 1, 1, 1, 31255525951495933344⟩,
    ⟨.reciprocal, 1, 1, 2, 51651762218348837082⟩]
  cut := none
  allocs := [
    ⟨66, 71, 76, false, true, 139326866994776696434723894⟩,
    ⟨66, 73, 78, false, true, 185794144923740874019531⟩,
    ⟨64, 71, 74, false, true, 172193458255500286074071⟩]

theorem leaf2_hint : hintCheck (some leaf2Hint) leaf2 = true := by
  decide +kernel

theorem leaf2_fcc (p : Chart) (hp : leaf2.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  hintCheck_sound leaf2_hint p hp gp

theorem leaf2_stage3 (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (hs : w.source = "stage3/Z") (hr : w.route = .strictFCC)
    (hh : hint w = some leaf2Hint) : stage3Check hint w leaf2 = true := by
  simp only [stage3Check, hr, hs, hh, stage3Profile, leaf2_hint, Bool.true_or, decide_true,
    Bool.true_and]

def leaf2Pt : Fin 8 → ℚ := ![(7453713 / 8388608 : ℚ), (1614841 / 2097152 : ℚ), (65535 / 131072 : ℚ), (1 / 131072 : ℚ), (1 / 131072 : ℚ), (169 / 512 : ℚ), (169 / 512 : ℚ), (-127 / 256 : ℚ)]

theorem leaf2_nonvacuous : ∃ p : Chart, leaf2.Mem p ∧ good p := by
  have hall : ∀ i, leaf2.lo i ≤ leaf2Pt i ∧ leaf2Pt i ≤ leaf2.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf2Pt i : ℝ), fun i => ?_,
    good_of_check leaf2Pt (0) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def hull3 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)]⟩

def leaf3 : Cell := ⟨![(1807 / 2048 : ℚ), (785 / 1024 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (-1 / 64 : ℚ), (49 / 128 : ℚ), (23 / 64 : ℚ), (31 / 64 : ℚ)],
    ![(3631 / 4096 : ℚ), (99 / 128 : ℚ), (31 / 64 : ℚ), (1 / 64 : ℚ), (0 : ℚ), (25 / 64 : ℚ), (47 / 128 : ℚ), (1 / 2 : ℚ)]⟩

theorem leaf3_address : FLeaves.seedOk hull3 "23cffffad91ad9316ad59316b4c0" leaf3 = true := by
  decide +kernel

noncomputable def leaf3Hint : SupportHint where
  terms := [
    ⟨.cross, -2, -1, -1, 53395391150789923111⟩,
    ⟨.cross, -2, -1, 0, 53242103239579984329⟩,
    ⟨.cross, -2, 0, -1, 32906293531624164479⟩,
    ⟨.cross, -2, 0, 0, 32743451186922615950⟩,
    ⟨.cross, -2, 1, -1, 34846965085207980521⟩,
    ⟨.cross, -2, 1, 0, 34674881116107926180⟩,
    ⟨.cross, -2, 2, -1, 59173812221971809705⟩,
    ⟨.cross, -2, 2, 0, 58990249779668669301⟩,
    ⟨.cross, -1, -2, -1, 53224327336298556862⟩,
    ⟨.cross, -1, -2, 0, 53119101382517446830⟩,
    ⟨.cross, -1, -1, -1, 21036403159049220082⟩,
    ⟨.cross, -1, -1, 0, 20919805961235661823⟩,
    ⟨.cross, -1, 0, -1, 11280209583468413524⟩,
    ⟨.cross, -1, 0, 0, 11153192967488159431⟩,
    ⟨.cross, -1, 0, 1, 73131503054335978214⟩,
    ⟨.cross, -1, 1, -1, 23918765984751637306⟩,
    ⟨.cross, -1, 1, 0, 23783729930235115300⟩,
    ⟨.cross, -1, 2, -1, 59020549178430360356⟩,
    ⟨.cross, -1, 2, 0, 58874655438389461936⟩,
    ⟨.cross, 0, -2, -1, 32902702373132143648⟩,
    ⟨.cross, 0, -2, 0, 32833387275647205880⟩,
    ⟨.cross, 0, -1, -1, 11472574181932023459⟩,
    ⟨.cross, 0, -1, 0, 11392537705589600357⟩,
    ⟨.cross, 0, -1, 1, 73413238963444979900⟩,
    ⟨.cross, 0, 0, -1, 12479995802236451226⟩,
    ⟨.cross, 0, 0, 0, 12389477596879212807⟩,
    ⟨.cross, 0, 0, 1, 74408963091558301802⟩,
    ⟨.cross, 0, 1, -1, 35894008835322247038⟩,
    ⟨.cross, 0, 1, 0, 35795492928712482692⟩,
    ⟨.cross, 1, -2, -1, 35448952212845958405⟩,
    ⟨.cross, 1, -2, 0, 35416800287472624999⟩,
    ⟨.cross, 1, -1, -1, 24758119163976876486⟩,
    ⟨.cross, 1, -1, 0, 24714554247112437061⟩,
    ⟨.cross, 1, 0, -1, 36487437045790454811⟩,
    ⟨.cross, 1, 0, 0, 36433626892383047226⟩,
    ⟨.cross, 1, 1, -1, 70655126896881993027⟩,
    ⟨.cross, 1, 1, 0, 70592189863868718886⟩,
    ⟨.cross, 2, -2, -1, 60838363763190510058⟩,
    ⟨.cross, 2, -2, 0, 60842920996196099256⟩,
    ⟨.cross, 2, -1, -1, 60845106288103610529⟩,
    ⟨.cross, 2, -1, 0, 60837120244835661308⟩,
    ⟨.period, 0, 0, 1, 30990121502489052338⟩,
    ⟨.period, 0, 1, -1, 42209665848716426685⟩,
    ⟨.period, 0, 1, 0, 11202376385252761824⟩,
    ⟨.period, 0, 1, 1, 42190731514175915185⟩,
    ⟨.period, 0, 2, 0, 44809505527518009591⟩,
    ⟨.period, 1, -2, -1, 65589386582843896172⟩,
    ⟨.period, 1, -2, 0, 34711775695810984327⟩,
    ⟨.period, 1, -2, 1, 65703101627324655414⟩,
    ⟨.period, 1, -1, -1, 42832689445211054372⟩,
    ⟨.period, 1, -1, 0, 11880042790511543150⟩,
    ⟨.period, 1, -1, 1, 42924319692763748677⟩,
    ⟨.period, 1, 0, -1, 42353539262728789319⟩,
    ⟨.period, 1, 0, 0, 11385240414431278464⟩,
    ⟨.period, 1, 0, 1, 42424582993753166516⟩,
    ⟨.period, 1, 1, -1, 64297847788643334969⟩,
    ⟨.period, 1, 1, 0, 33332437435406344256⟩,
    ⟨.period, 1, 1, 1, 64349406453300252895⟩,
    ⟨.period, 2, -2, 0, 47520171162046172598⟩,
    ⟨.period, 2, -1, -1, 66270874432269201406⟩,
    ⟨.period, 2, -1, 0, 35362101145276054981⟩,
    ⟨.period, 2, -1, 1, 66432997692512362842⟩,
    ⟨.period, 2, 0, 0, 45540961657725113855⟩,
    ⟨.reciprocal, 0, 0, 2, 27242856767993826104⟩,
    ⟨.reciprocal, 0, 1, -2, 51462021098192192773⟩,
    ⟨.reciprocal, 0, 1, -1, 31092678641356509551⟩,
    ⟨.reciprocal, 0, 1, 0, 24306263021996223481⟩,
    ⟨.reciprocal, 0, 1, 1, 31134823186620907056⟩,
    ⟨.reciprocal, 0, 1, 2, 51547487577698046670⟩,
    ⟨.reciprocal, 1, -1, 0, 71134128305130528021⟩,
    ⟨.reciprocal, 1, 0, -2, 51200128414643479191⟩,
    ⟨.reciprocal, 1, 0, -1, 30726249457774273898⟩,
    ⟨.reciprocal, 1, 0, 0, 23886010799155572425⟩,
    ⟨.reciprocal, 1, 0, 1, 30662928507359192992⟩,
    ⟨.reciprocal, 1, 0, 2, 51073024997951671907⟩,
    ⟨.reciprocal, 1, 1, -2, 52600052098640382303⟩,
    ⟨.reciprocal, 1, 1, -1, 32146987866046190699⟩,
    ⟨.reciprocal, 1, 1, 0, 25331312918256553539⟩,
    ⟨.reciprocal, 1, 1, 1, 32127330075303075842⟩,
    ⟨.reciprocal, 1, 1, 2, 52559906870744814643⟩]
  cut := none
  allocs := [
    ⟨66, 74, 79, false, true, 149569824667175673018587⟩,
    ⟨64, 74, 77, false, true, 57576792936404303385647⟩,
    ⟨68, 70, 77, false, true, 178274335094591658832028⟩,
    ⟨64, 72, 75, false, true, 142656429657321087248289⟩]

theorem leaf3_hint : hintCheck (some leaf3Hint) leaf3 = true := by
  decide +kernel

theorem leaf3_fcc (p : Chart) (hp : leaf3.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  hintCheck_sound leaf3_hint p hp gp

theorem leaf3_stage3 (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (hs : w.source = "stage3/Z") (hr : w.route = .strictFCC)
    (hh : hint w = some leaf3Hint) : stage3Check hint w leaf3 = true := by
  simp only [stage3Check, hr, hs, hh, stage3Profile, leaf3_hint, Bool.true_or, decide_true,
    Bool.true_and]

def leaf3Pt : Fin 8 → ℚ := ![(3700753 / 4194304 : ℚ), (811001 / 1048576 : ℚ), (31743 / 65536 : ℚ), (1 / 65536 : ℚ), (-1023 / 65536 : ℚ), (99 / 256 : ℚ), (93 / 256 : ℚ), (63 / 128 : ℚ)]

theorem leaf3_nonvacuous : ∃ p : Chart, leaf3.Mem p ∧ good p := by
  have hall : ∀ i, leaf3.lo i ≤ leaf3Pt i ∧ leaf3Pt i ≤ leaf3.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf3Pt i : ℝ), fun i => ?_,
    good_of_check leaf3Pt (0) (0) (63 / 128 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def hull4 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)]⟩

def leaf4 : Cell := ⟨![(1807 / 2048 : ℚ), (785 / 1024 : ℚ), (31 / 64 : ℚ), (0 : ℚ), (0 : ℚ), (43 / 128 : ℚ), (47 / 128 : ℚ), (63 / 128 : ℚ)],
    ![(3631 / 4096 : ℚ), (1577 / 2048 : ℚ), (63 / 128 : ℚ), (1 / 64 : ℚ), (1 / 128 : ℚ), (11 / 32 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)]⟩

theorem leaf4_address : FLeaves.seedOk hull4 "cdffff213bf8ad8316bd58316bd58204" leaf4 = true := by
  decide +kernel

theorem leaf4_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 leaf4 leaf4 = true := by
  decide +kernel

theorem leaf4_fcc (p : Chart) (hp : leaf4.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  Jensen.Fix.fLeafCheck_route _ _ _ leaf4 leaf4 leaf4_check p hp gp

theorem leaf4_stage3 (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (hs : w.source = "stage3/correlated_phase") (hr : w.route = .strictFCC) :
    stage3Check hint w leaf4 = true := by
  simp only [stage3Check, hr, hs, stage3Profile, leaf4_check, Bool.or_true, decide_true,
    Bool.true_and]

def leaf4Pt : Fin 8 → ℚ := ![(14473 / 16384 : ℚ), (12609 / 16384 : ℚ), (503 / 1024 : ℚ), (1 / 128 : ℚ), (1 / 256 : ℚ), (87 / 256 : ℚ), (95 / 256 : ℚ), (127 / 256 : ℚ)]

theorem leaf4_nonvacuous : ∃ p : Chart, leaf4.Mem p ∧ good p := by
  have hall : ∀ i, leaf4.lo i ≤ leaf4Pt i ∧ leaf4Pt i ≤ leaf4.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf4Pt i : ℝ), fun i => ?_,
    good_of_check leaf4Pt (0) (0) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

def hull5 : Cell := ⟨![(211 / 256 : ℚ), (23 / 32 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (-1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (53 / 64 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)]⟩

def leaf5 : Cell := ⟨![(3631 / 4096 : ℚ), (785 / 1024 : ℚ), (31 / 64 : ℚ), (0 : ℚ), (-1 / 128 : ℚ), (95 / 256 : ℚ), (45 / 128 : ℚ), (-1 / 2 : ℚ)],
    ![(57 / 64 : ℚ), (99 / 128 : ℚ), (63 / 128 : ℚ), (1 / 128 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (23 / 64 : ℚ), (-63 / 128 : ℚ)]⟩

theorem leaf5_address : FLeaves.seedOk hull5 "23ceeeebd91bd9316bc59316bde51469b" leaf5 = true := by
  decide +kernel

theorem leaf5_check : Jensen.Fix.fLeafCheck (6 / 5 : ℚ) (5 : ℚ) 2 leaf5 leaf5 = true := by
  decide +kernel

theorem leaf5_fcc (p : Chart) (hp : leaf5.Mem p) (gp : good p) :
    energy fcc < energy (chartPoint p) :=
  Jensen.Fix.fLeafCheck_route _ _ _ leaf5 leaf5 leaf5_check p hp gp

theorem leaf5_stage3 (hint : WitnessRef → Option SupportHint) (w : WitnessRef)
    (hs : w.source = "stage3/correlated_phase") (hr : w.route = .strictFCC) :
    stage3Check hint w leaf5 = true := by
  simp only [stage3Check, hr, hs, stage3Profile, leaf5_check, Bool.or_true, decide_true,
    Bool.true_and]

def leaf5Pt : Fin 8 → ℚ := ![(3718161 / 4194304 : ℚ), (811001 / 1048576 : ℚ), (64511 / 131072 : ℚ), (1 / 131072 : ℚ), (-1023 / 131072 : ℚ), (191 / 512 : ℚ), (91 / 256 : ℚ), (-127 / 256 : ℚ)]

theorem leaf5_nonvacuous : ∃ p : Chart, leaf5.Mem p ∧ good p := by
  have hall : ∀ i, leaf5.lo i ≤ leaf5Pt i ∧ leaf5Pt i ≤ leaf5.hi i := by
    decide +kernel
  refine ⟨fun i => (leaf5Pt i : ℝ), fun i => ?_,
    good_of_check leaf5Pt (0) (-1) (127 / 256 : ℚ) (by decide +kernel)⟩
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (hall i).1, (Rat.cast_le (K := ℝ)).mpr (hall i).2⟩

end BccSharp.Coulomb.CompactCover.Stage3Stage6.Stage3Leaves
