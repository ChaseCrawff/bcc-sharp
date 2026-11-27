import BccSharp.Lattice.ForestBase

set_option autoImplicit false

/-! Lattice global forest of the tangent route, group 0: grid cells 0 to 939
(940 cells, 2689 leaves). Cell `i` has owner `![a, b]` and suffix `![c, d, e]` with
`i = 256a + 64b + 16c + 4d + e`. Each `decide +kernel` checks a plan, or a subtree of at most 40
leaves joined to its cell by `checkAt_cut`. Generated; the plans are
untrusted proposals. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.TangentCover.Forest
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentCover

def plan0 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root0 : rootCheck plan0 ![0, 0] ![0, 0, 0] = true := by decide +kernel

def plan1 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root1 : rootCheck plan1 ![0, 0] ![0, 0, 1] = true := by decide +kernel

def plan2 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root2 : rootCheck plan2 ![0, 0] ![0, 0, 2] = true := by decide +kernel

def plan3 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root3 : rootCheck plan3 ![0, 0] ![0, 0, 3] = true := by decide +kernel

def plan4 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root4 : rootCheck plan4 ![0, 0] ![0, 1, 0] = true := by decide +kernel

def plan5 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root5 : rootCheck plan5 ![0, 0] ![0, 1, 1] = true := by decide +kernel

def plan6 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root6 : rootCheck plan6 ![0, 0] ![0, 1, 2] = true := by decide +kernel

def plan7 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root7 : rootCheck plan7 ![0, 0] ![0, 1, 3] = true := by decide +kernel

def plan8 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root8 : rootCheck plan8 ![0, 0] ![0, 2, 0] = true := by decide +kernel

def plan9 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root9 : rootCheck plan9 ![0, 0] ![0, 2, 1] = true := by decide +kernel

def plan10 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root10 : rootCheck plan10 ![0, 0] ![0, 2, 2] = true := by decide +kernel

def plan11 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root11 : rootCheck plan11 ![0, 0] ![0, 2, 3] = true := by decide +kernel

def plan12 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root12 : rootCheck plan12 ![0, 0] ![0, 3, 0] = true := by decide +kernel

def plan13 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root13 : rootCheck plan13 ![0, 0] ![0, 3, 1] = true := by decide +kernel

def plan14 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root14 : rootCheck plan14 ![0, 0] ![0, 3, 2] = true := by decide +kernel

def plan15 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root15 : rootCheck plan15 ![0, 0] ![0, 3, 3] = true := by decide +kernel

def plan16 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root16 : rootCheck plan16 ![0, 0] ![1, 0, 0] = true := by decide +kernel

def plan17 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root17 : rootCheck plan17 ![0, 0] ![1, 0, 1] = true := by decide +kernel

def plan18 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root18 : rootCheck plan18 ![0, 0] ![1, 0, 2] = true := by decide +kernel

def plan19 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root19 : rootCheck plan19 ![0, 0] ![1, 0, 3] = true := by decide +kernel

def plan20 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root20 : rootCheck plan20 ![0, 0] ![1, 1, 0] = true := by decide +kernel

def plan21 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root21 : rootCheck plan21 ![0, 0] ![1, 1, 1] = true := by decide +kernel

def plan22 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root22 : rootCheck plan22 ![0, 0] ![1, 1, 2] = true := by decide +kernel

def plan23 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root23 : rootCheck plan23 ![0, 0] ![1, 1, 3] = true := by decide +kernel

def plan24 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root24 : rootCheck plan24 ![0, 0] ![1, 2, 0] = true := by decide +kernel

def plan25 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root25 : rootCheck plan25 ![0, 0] ![1, 2, 1] = true := by decide +kernel

def plan26 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root26 : rootCheck plan26 ![0, 0] ![1, 2, 2] = true := by decide +kernel

def plan27 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root27 : rootCheck plan27 ![0, 0] ![1, 2, 3] = true := by decide +kernel

def plan28 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root28 : rootCheck plan28 ![0, 0] ![1, 3, 0] = true := by decide +kernel

def plan29 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root29 : rootCheck plan29 ![0, 0] ![1, 3, 1] = true := by decide +kernel

def plan30 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root30 : rootCheck plan30 ![0, 0] ![1, 3, 2] = true := by decide +kernel

def plan31 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root31 : rootCheck plan31 ![0, 0] ![1, 3, 3] = true := by decide +kernel

def plan32 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root32 : rootCheck plan32 ![0, 0] ![2, 0, 0] = true := by decide +kernel

def plan33 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root33 : rootCheck plan33 ![0, 0] ![2, 0, 1] = true := by decide +kernel

def plan34 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root34 : rootCheck plan34 ![0, 0] ![2, 0, 2] = true := by decide +kernel

def plan35 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root35 : rootCheck plan35 ![0, 0] ![2, 0, 3] = true := by decide +kernel

def plan36 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root36 : rootCheck plan36 ![0, 0] ![2, 1, 0] = true := by decide +kernel

def plan37 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root37 : rootCheck plan37 ![0, 0] ![2, 1, 1] = true := by decide +kernel

def plan38 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root38 : rootCheck plan38 ![0, 0] ![2, 1, 2] = true := by decide +kernel

def plan39 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root39 : rootCheck plan39 ![0, 0] ![2, 1, 3] = true := by decide +kernel

def plan40 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root40 : rootCheck plan40 ![0, 0] ![2, 2, 0] = true := by decide +kernel

def plan41 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root41 : rootCheck plan41 ![0, 0] ![2, 2, 1] = true := by decide +kernel

def plan42 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root42 : rootCheck plan42 ![0, 0] ![2, 2, 2] = true := by decide +kernel

def plan43 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root43 : rootCheck plan43 ![0, 0] ![2, 2, 3] = true := by decide +kernel

def plan44 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root44 : rootCheck plan44 ![0, 0] ![2, 3, 0] = true := by decide +kernel

def plan45 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root45 : rootCheck plan45 ![0, 0] ![2, 3, 1] = true := by decide +kernel

def plan46 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root46 : rootCheck plan46 ![0, 0] ![2, 3, 2] = true := by decide +kernel

def plan47 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root47 : rootCheck plan47 ![0, 0] ![2, 3, 3] = true := by decide +kernel

def plan48 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root48 : rootCheck plan48 ![0, 0] ![3, 0, 0] = true := by decide +kernel

def plan49 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root49 : rootCheck plan49 ![0, 0] ![3, 0, 1] = true := by decide +kernel

def plan50 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root50 : rootCheck plan50 ![0, 0] ![3, 0, 2] = true := by decide +kernel

def plan51 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root51 : rootCheck plan51 ![0, 0] ![3, 0, 3] = true := by decide +kernel

def plan52 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root52 : rootCheck plan52 ![0, 0] ![3, 1, 0] = true := by decide +kernel

def plan53 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root53 : rootCheck plan53 ![0, 0] ![3, 1, 1] = true := by decide +kernel

def plan54 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root54 : rootCheck plan54 ![0, 0] ![3, 1, 2] = true := by decide +kernel

def plan55 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root55 : rootCheck plan55 ![0, 0] ![3, 1, 3] = true := by decide +kernel

def plan56 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root56 : rootCheck plan56 ![0, 0] ![3, 2, 0] = true := by decide +kernel

def plan57 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root57 : rootCheck plan57 ![0, 0] ![3, 2, 1] = true := by decide +kernel

def plan58 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root58 : rootCheck plan58 ![0, 0] ![3, 2, 2] = true := by decide +kernel

def plan59 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root59 : rootCheck plan59 ![0, 0] ![3, 2, 3] = true := by decide +kernel

def plan60 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root60 : rootCheck plan60 ![0, 0] ![3, 3, 0] = true := by decide +kernel

def plan61 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root61 : rootCheck plan61 ![0, 0] ![3, 3, 1] = true := by decide +kernel

def plan62 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root62 : rootCheck plan62 ![0, 0] ![3, 3, 2] = true := by decide +kernel

def plan63 : Plan :=
  (.e1 [] [(170, 17), (172, 17)])

theorem root63 : rootCheck plan63 ![0, 0] ![3, 3, 3] = true := by decide +kernel

def plan64 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root64 : rootCheck plan64 ![0, 1] ![0, 0, 0] = true := by decide +kernel

def plan65 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root65 : rootCheck plan65 ![0, 1] ![0, 0, 1] = true := by decide +kernel

def plan66 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root66 : rootCheck plan66 ![0, 1] ![0, 0, 2] = true := by decide +kernel

def plan67 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root67 : rootCheck plan67 ![0, 1] ![0, 0, 3] = true := by decide +kernel

def plan68 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root68 : rootCheck plan68 ![0, 1] ![0, 1, 0] = true := by decide +kernel

def plan69 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root69 : rootCheck plan69 ![0, 1] ![0, 1, 1] = true := by decide +kernel

def plan70 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root70 : rootCheck plan70 ![0, 1] ![0, 1, 2] = true := by decide +kernel

def plan71 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root71 : rootCheck plan71 ![0, 1] ![0, 1, 3] = true := by decide +kernel

def plan72 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root72 : rootCheck plan72 ![0, 1] ![0, 2, 0] = true := by decide +kernel

def plan73 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root73 : rootCheck plan73 ![0, 1] ![0, 2, 1] = true := by decide +kernel

def plan74 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root74 : rootCheck plan74 ![0, 1] ![0, 2, 2] = true := by decide +kernel

def plan75 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root75 : rootCheck plan75 ![0, 1] ![0, 2, 3] = true := by decide +kernel

def plan76 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root76 : rootCheck plan76 ![0, 1] ![0, 3, 0] = true := by decide +kernel

def plan77 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root77 : rootCheck plan77 ![0, 1] ![0, 3, 1] = true := by decide +kernel

def plan78 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root78 : rootCheck plan78 ![0, 1] ![0, 3, 2] = true := by decide +kernel

def plan79 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root79 : rootCheck plan79 ![0, 1] ![0, 3, 3] = true := by decide +kernel

def plan80 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root80 : rootCheck plan80 ![0, 1] ![1, 0, 0] = true := by decide +kernel

def plan81 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root81 : rootCheck plan81 ![0, 1] ![1, 0, 1] = true := by decide +kernel

def plan82 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root82 : rootCheck plan82 ![0, 1] ![1, 0, 2] = true := by decide +kernel

def plan83 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root83 : rootCheck plan83 ![0, 1] ![1, 0, 3] = true := by decide +kernel

def plan84 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root84 : rootCheck plan84 ![0, 1] ![1, 1, 0] = true := by decide +kernel

def plan85 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root85 : rootCheck plan85 ![0, 1] ![1, 1, 1] = true := by decide +kernel

def plan86 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root86 : rootCheck plan86 ![0, 1] ![1, 1, 2] = true := by decide +kernel

def plan87 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root87 : rootCheck plan87 ![0, 1] ![1, 1, 3] = true := by decide +kernel

def plan88 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root88 : rootCheck plan88 ![0, 1] ![1, 2, 0] = true := by decide +kernel

def plan89 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root89 : rootCheck plan89 ![0, 1] ![1, 2, 1] = true := by decide +kernel

def plan90 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root90 : rootCheck plan90 ![0, 1] ![1, 2, 2] = true := by decide +kernel

def plan91 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root91 : rootCheck plan91 ![0, 1] ![1, 2, 3] = true := by decide +kernel

def plan92 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root92 : rootCheck plan92 ![0, 1] ![1, 3, 0] = true := by decide +kernel

def plan93 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root93 : rootCheck plan93 ![0, 1] ![1, 3, 1] = true := by decide +kernel

def plan94 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root94 : rootCheck plan94 ![0, 1] ![1, 3, 2] = true := by decide +kernel

def plan95 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root95 : rootCheck plan95 ![0, 1] ![1, 3, 3] = true := by decide +kernel

def plan96 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root96 : rootCheck plan96 ![0, 1] ![2, 0, 0] = true := by decide +kernel

def plan97 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root97 : rootCheck plan97 ![0, 1] ![2, 0, 1] = true := by decide +kernel

def plan98 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root98 : rootCheck plan98 ![0, 1] ![2, 0, 2] = true := by decide +kernel

def plan99 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root99 : rootCheck plan99 ![0, 1] ![2, 0, 3] = true := by decide +kernel

def plan100 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root100 : rootCheck plan100 ![0, 1] ![2, 1, 0] = true := by decide +kernel

def plan101 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root101 : rootCheck plan101 ![0, 1] ![2, 1, 1] = true := by decide +kernel

def plan102 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root102 : rootCheck plan102 ![0, 1] ![2, 1, 2] = true := by decide +kernel

def plan103 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root103 : rootCheck plan103 ![0, 1] ![2, 1, 3] = true := by decide +kernel

def plan104 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root104 : rootCheck plan104 ![0, 1] ![2, 2, 0] = true := by decide +kernel

def plan105 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root105 : rootCheck plan105 ![0, 1] ![2, 2, 1] = true := by decide +kernel

def plan106 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root106 : rootCheck plan106 ![0, 1] ![2, 2, 2] = true := by decide +kernel

def plan107 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root107 : rootCheck plan107 ![0, 1] ![2, 2, 3] = true := by decide +kernel

def plan108 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root108 : rootCheck plan108 ![0, 1] ![2, 3, 0] = true := by decide +kernel

def plan109 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root109 : rootCheck plan109 ![0, 1] ![2, 3, 1] = true := by decide +kernel

def plan110 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root110 : rootCheck plan110 ![0, 1] ![2, 3, 2] = true := by decide +kernel

def plan111 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root111 : rootCheck plan111 ![0, 1] ![2, 3, 3] = true := by decide +kernel

def plan112 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root112 : rootCheck plan112 ![0, 1] ![3, 0, 0] = true := by decide +kernel

def plan113 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root113 : rootCheck plan113 ![0, 1] ![3, 0, 1] = true := by decide +kernel

def plan114 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root114 : rootCheck plan114 ![0, 1] ![3, 0, 2] = true := by decide +kernel

def plan115 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root115 : rootCheck plan115 ![0, 1] ![3, 0, 3] = true := by decide +kernel

def plan116 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root116 : rootCheck plan116 ![0, 1] ![3, 1, 0] = true := by decide +kernel

def plan117 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root117 : rootCheck plan117 ![0, 1] ![3, 1, 1] = true := by decide +kernel

def plan118 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root118 : rootCheck plan118 ![0, 1] ![3, 1, 2] = true := by decide +kernel

def plan119 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root119 : rootCheck plan119 ![0, 1] ![3, 1, 3] = true := by decide +kernel

def plan120 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root120 : rootCheck plan120 ![0, 1] ![3, 2, 0] = true := by decide +kernel

def plan121 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root121 : rootCheck plan121 ![0, 1] ![3, 2, 1] = true := by decide +kernel

def plan122 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root122 : rootCheck plan122 ![0, 1] ![3, 2, 2] = true := by decide +kernel

def plan123 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root123 : rootCheck plan123 ![0, 1] ![3, 2, 3] = true := by decide +kernel

def plan124 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root124 : rootCheck plan124 ![0, 1] ![3, 3, 0] = true := by decide +kernel

def plan125 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root125 : rootCheck plan125 ![0, 1] ![3, 3, 1] = true := by decide +kernel

def plan126 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root126 : rootCheck plan126 ![0, 1] ![3, 3, 2] = true := by decide +kernel

def plan127 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(170, 57), (172, 57)])

theorem root127 : rootCheck plan127 ![0, 1] ![3, 3, 3] = true := by decide +kernel

def plan128 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root128 : rootCheck plan128 ![0, 2] ![0, 0, 0] = true := by decide +kernel

def plan129 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root129 : rootCheck plan129 ![0, 2] ![0, 0, 1] = true := by decide +kernel

def plan130 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root130 : rootCheck plan130 ![0, 2] ![0, 0, 2] = true := by decide +kernel

def plan131 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root131 : rootCheck plan131 ![0, 2] ![0, 0, 3] = true := by decide +kernel

def plan132 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root132 : rootCheck plan132 ![0, 2] ![0, 1, 0] = true := by decide +kernel

def plan133 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root133 : rootCheck plan133 ![0, 2] ![0, 1, 1] = true := by decide +kernel

def plan134 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root134 : rootCheck plan134 ![0, 2] ![0, 1, 2] = true := by decide +kernel

def plan135 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root135 : rootCheck plan135 ![0, 2] ![0, 1, 3] = true := by decide +kernel

def plan136 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root136 : rootCheck plan136 ![0, 2] ![0, 2, 0] = true := by decide +kernel

def plan137 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root137 : rootCheck plan137 ![0, 2] ![0, 2, 1] = true := by decide +kernel

def plan138 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root138 : rootCheck plan138 ![0, 2] ![0, 2, 2] = true := by decide +kernel

def plan139 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root139 : rootCheck plan139 ![0, 2] ![0, 2, 3] = true := by decide +kernel

def plan140 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root140 : rootCheck plan140 ![0, 2] ![0, 3, 0] = true := by decide +kernel

def plan141 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root141 : rootCheck plan141 ![0, 2] ![0, 3, 1] = true := by decide +kernel

def plan142 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root142 : rootCheck plan142 ![0, 2] ![0, 3, 2] = true := by decide +kernel

def plan143 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root143 : rootCheck plan143 ![0, 2] ![0, 3, 3] = true := by decide +kernel

def plan144 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root144 : rootCheck plan144 ![0, 2] ![1, 0, 0] = true := by decide +kernel

def plan145 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root145 : rootCheck plan145 ![0, 2] ![1, 0, 1] = true := by decide +kernel

def plan146 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root146 : rootCheck plan146 ![0, 2] ![1, 0, 2] = true := by decide +kernel

def plan147 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root147 : rootCheck plan147 ![0, 2] ![1, 0, 3] = true := by decide +kernel

def plan148 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root148 : rootCheck plan148 ![0, 2] ![1, 1, 0] = true := by decide +kernel

def plan149 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root149 : rootCheck plan149 ![0, 2] ![1, 1, 1] = true := by decide +kernel

def plan150 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root150 : rootCheck plan150 ![0, 2] ![1, 1, 2] = true := by decide +kernel

def plan151 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root151 : rootCheck plan151 ![0, 2] ![1, 1, 3] = true := by decide +kernel

def plan152 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root152 : rootCheck plan152 ![0, 2] ![1, 2, 0] = true := by decide +kernel

def plan153 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root153 : rootCheck plan153 ![0, 2] ![1, 2, 1] = true := by decide +kernel

def plan154 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root154 : rootCheck plan154 ![0, 2] ![1, 2, 2] = true := by decide +kernel

def plan155 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root155 : rootCheck plan155 ![0, 2] ![1, 2, 3] = true := by decide +kernel

def plan156 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root156 : rootCheck plan156 ![0, 2] ![1, 3, 0] = true := by decide +kernel

def plan157 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root157 : rootCheck plan157 ![0, 2] ![1, 3, 1] = true := by decide +kernel

def plan158 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root158 : rootCheck plan158 ![0, 2] ![1, 3, 2] = true := by decide +kernel

def plan159 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root159 : rootCheck plan159 ![0, 2] ![1, 3, 3] = true := by decide +kernel

def plan160 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root160 : rootCheck plan160 ![0, 2] ![2, 0, 0] = true := by decide +kernel

def plan161 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root161 : rootCheck plan161 ![0, 2] ![2, 0, 1] = true := by decide +kernel

def plan162 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root162 : rootCheck plan162 ![0, 2] ![2, 0, 2] = true := by decide +kernel

def plan163 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root163 : rootCheck plan163 ![0, 2] ![2, 0, 3] = true := by decide +kernel

def plan164 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root164 : rootCheck plan164 ![0, 2] ![2, 1, 0] = true := by decide +kernel

def plan165 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root165 : rootCheck plan165 ![0, 2] ![2, 1, 1] = true := by decide +kernel

def plan166 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root166 : rootCheck plan166 ![0, 2] ![2, 1, 2] = true := by decide +kernel

def plan167 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root167 : rootCheck plan167 ![0, 2] ![2, 1, 3] = true := by decide +kernel

def plan168 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root168 : rootCheck plan168 ![0, 2] ![2, 2, 0] = true := by decide +kernel

def plan169 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root169 : rootCheck plan169 ![0, 2] ![2, 2, 1] = true := by decide +kernel

def plan170 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root170 : rootCheck plan170 ![0, 2] ![2, 2, 2] = true := by decide +kernel

def plan171 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root171 : rootCheck plan171 ![0, 2] ![2, 2, 3] = true := by decide +kernel

def plan172 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root172 : rootCheck plan172 ![0, 2] ![2, 3, 0] = true := by decide +kernel

def plan173 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root173 : rootCheck plan173 ![0, 2] ![2, 3, 1] = true := by decide +kernel

def plan174 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root174 : rootCheck plan174 ![0, 2] ![2, 3, 2] = true := by decide +kernel

def plan175 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root175 : rootCheck plan175 ![0, 2] ![2, 3, 3] = true := by decide +kernel

def plan176 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root176 : rootCheck plan176 ![0, 2] ![3, 0, 0] = true := by decide +kernel

def plan177 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root177 : rootCheck plan177 ![0, 2] ![3, 0, 1] = true := by decide +kernel

def plan178 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root178 : rootCheck plan178 ![0, 2] ![3, 0, 2] = true := by decide +kernel

def plan179 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root179 : rootCheck plan179 ![0, 2] ![3, 0, 3] = true := by decide +kernel

def plan180 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root180 : rootCheck plan180 ![0, 2] ![3, 1, 0] = true := by decide +kernel

def plan181 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root181 : rootCheck plan181 ![0, 2] ![3, 1, 1] = true := by decide +kernel

def plan182 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root182 : rootCheck plan182 ![0, 2] ![3, 1, 2] = true := by decide +kernel

def plan183 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root183 : rootCheck plan183 ![0, 2] ![3, 1, 3] = true := by decide +kernel

def plan184 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root184 : rootCheck plan184 ![0, 2] ![3, 2, 0] = true := by decide +kernel

def plan185 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root185 : rootCheck plan185 ![0, 2] ![3, 2, 1] = true := by decide +kernel

def plan186 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root186 : rootCheck plan186 ![0, 2] ![3, 2, 2] = true := by decide +kernel

def plan187 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root187 : rootCheck plan187 ![0, 2] ![3, 2, 3] = true := by decide +kernel

def plan188 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 167), (165, 217), (170, 102), (172, 102), (177, 217), (178, 167)])

theorem root188 : rootCheck plan188 ![0, 2] ![3, 3, 0] = true := by decide +kernel

def plan189 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root189 : rootCheck plan189 ![0, 2] ![3, 3, 1] = true := by decide +kernel

def plan190 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 143), (170, 102), (172, 102), (178, 143)])

theorem root190 : rootCheck plan190 ![0, 2] ![3, 3, 2] = true := by decide +kernel

def plan191 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(163, 217), (164, 167), (170, 102), (172, 102), (178, 167), (179, 217)])

theorem root191 : rootCheck plan191 ![0, 2] ![3, 3, 3] = true := by decide +kernel

def plan192 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root192 : rootCheck plan192 ![0, 3] ![0, 0, 0] = true := by decide +kernel

def plan193 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root193 : rootCheck plan193 ![0, 3] ![0, 0, 1] = true := by decide +kernel

def plan194 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root194 : rootCheck plan194 ![0, 3] ![0, 0, 2] = true := by decide +kernel

def plan195 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root195 : rootCheck plan195 ![0, 3] ![0, 0, 3] = true := by decide +kernel

def plan196 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root196 : rootCheck plan196 ![0, 3] ![0, 1, 0] = true := by decide +kernel

def plan197 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root197 : rootCheck plan197 ![0, 3] ![0, 1, 1] = true := by decide +kernel

def plan198 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root198 : rootCheck plan198 ![0, 3] ![0, 1, 2] = true := by decide +kernel

def plan199 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root199 : rootCheck plan199 ![0, 3] ![0, 1, 3] = true := by decide +kernel

def plan200 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root200 : rootCheck plan200 ![0, 3] ![0, 2, 0] = true := by decide +kernel

def plan201 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root201 : rootCheck plan201 ![0, 3] ![0, 2, 1] = true := by decide +kernel

def plan202 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root202 : rootCheck plan202 ![0, 3] ![0, 2, 2] = true := by decide +kernel

def plan203 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root203 : rootCheck plan203 ![0, 3] ![0, 2, 3] = true := by decide +kernel

def plan204 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root204 : rootCheck plan204 ![0, 3] ![0, 3, 0] = true := by decide +kernel

def plan205 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root205 : rootCheck plan205 ![0, 3] ![0, 3, 1] = true := by decide +kernel

def plan206 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root206 : rootCheck plan206 ![0, 3] ![0, 3, 2] = true := by decide +kernel

def plan207 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root207 : rootCheck plan207 ![0, 3] ![0, 3, 3] = true := by decide +kernel

def plan208 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root208 : rootCheck plan208 ![0, 3] ![1, 0, 0] = true := by decide +kernel

def plan209 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root209 : rootCheck plan209 ![0, 3] ![1, 0, 1] = true := by decide +kernel

def plan210 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root210 : rootCheck plan210 ![0, 3] ![1, 0, 2] = true := by decide +kernel

def plan211 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root211 : rootCheck plan211 ![0, 3] ![1, 0, 3] = true := by decide +kernel

def plan212 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root212 : rootCheck plan212 ![0, 3] ![1, 1, 0] = true := by decide +kernel

def plan213 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root213 : rootCheck plan213 ![0, 3] ![1, 1, 1] = true := by decide +kernel

def plan214 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root214 : rootCheck plan214 ![0, 3] ![1, 1, 2] = true := by decide +kernel

def plan215 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root215 : rootCheck plan215 ![0, 3] ![1, 1, 3] = true := by decide +kernel

def plan216 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root216 : rootCheck plan216 ![0, 3] ![1, 2, 0] = true := by decide +kernel

def plan217 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root217 : rootCheck plan217 ![0, 3] ![1, 2, 1] = true := by decide +kernel

def plan218 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root218 : rootCheck plan218 ![0, 3] ![1, 2, 2] = true := by decide +kernel

def plan219 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root219 : rootCheck plan219 ![0, 3] ![1, 2, 3] = true := by decide +kernel

def plan220 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root220 : rootCheck plan220 ![0, 3] ![1, 3, 0] = true := by decide +kernel

def plan221 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root221 : rootCheck plan221 ![0, 3] ![1, 3, 1] = true := by decide +kernel

def plan222 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root222 : rootCheck plan222 ![0, 3] ![1, 3, 2] = true := by decide +kernel

def plan223 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root223 : rootCheck plan223 ![0, 3] ![1, 3, 3] = true := by decide +kernel

def plan224 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root224 : rootCheck plan224 ![0, 3] ![2, 0, 0] = true := by decide +kernel

def plan225 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root225 : rootCheck plan225 ![0, 3] ![2, 0, 1] = true := by decide +kernel

def plan226 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root226 : rootCheck plan226 ![0, 3] ![2, 0, 2] = true := by decide +kernel

def plan227 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root227 : rootCheck plan227 ![0, 3] ![2, 0, 3] = true := by decide +kernel

def plan228 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root228 : rootCheck plan228 ![0, 3] ![2, 1, 0] = true := by decide +kernel

def plan229 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root229 : rootCheck plan229 ![0, 3] ![2, 1, 1] = true := by decide +kernel

def plan230 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root230 : rootCheck plan230 ![0, 3] ![2, 1, 2] = true := by decide +kernel

def plan231 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root231 : rootCheck plan231 ![0, 3] ![2, 1, 3] = true := by decide +kernel

def plan232 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root232 : rootCheck plan232 ![0, 3] ![2, 2, 0] = true := by decide +kernel

def plan233 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root233 : rootCheck plan233 ![0, 3] ![2, 2, 1] = true := by decide +kernel

def plan234 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root234 : rootCheck plan234 ![0, 3] ![2, 2, 2] = true := by decide +kernel

def plan235 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root235 : rootCheck plan235 ![0, 3] ![2, 2, 3] = true := by decide +kernel

def plan236 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root236 : rootCheck plan236 ![0, 3] ![2, 3, 0] = true := by decide +kernel

def plan237 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root237 : rootCheck plan237 ![0, 3] ![2, 3, 1] = true := by decide +kernel

def plan238 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root238 : rootCheck plan238 ![0, 3] ![2, 3, 2] = true := by decide +kernel

def plan239 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root239 : rootCheck plan239 ![0, 3] ![2, 3, 3] = true := by decide +kernel

def plan240 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root240 : rootCheck plan240 ![0, 3] ![3, 0, 0] = true := by decide +kernel

def plan241 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root241 : rootCheck plan241 ![0, 3] ![3, 0, 1] = true := by decide +kernel

def plan242 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root242 : rootCheck plan242 ![0, 3] ![3, 0, 2] = true := by decide +kernel

def plan243 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root243 : rootCheck plan243 ![0, 3] ![3, 0, 3] = true := by decide +kernel

def plan244 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root244 : rootCheck plan244 ![0, 3] ![3, 1, 0] = true := by decide +kernel

def plan245 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root245 : rootCheck plan245 ![0, 3] ![3, 1, 1] = true := by decide +kernel

def plan246 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root246 : rootCheck plan246 ![0, 3] ![3, 1, 2] = true := by decide +kernel

def plan247 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root247 : rootCheck plan247 ![0, 3] ![3, 1, 3] = true := by decide +kernel

def plan248 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root248 : rootCheck plan248 ![0, 3] ![3, 2, 0] = true := by decide +kernel

def plan249 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root249 : rootCheck plan249 ![0, 3] ![3, 2, 1] = true := by decide +kernel

def plan250 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root250 : rootCheck plan250 ![0, 3] ![3, 2, 2] = true := by decide +kernel

def plan251 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root251 : rootCheck plan251 ![0, 3] ![3, 2, 3] = true := by decide +kernel

def plan252 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(164, 137), (165, 199), (170, 153), (172, 153), (177, 199), (178, 137)])

theorem root252 : rootCheck plan252 ![0, 3] ![3, 3, 0] = true := by decide +kernel

def plan253 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root253 : rootCheck plan253 ![0, 3] ![3, 3, 1] = true := by decide +kernel

def plan254 : Plan :=
  (.e1 [(122, 55), (220, 55)] [(164, 110), (170, 140), (172, 140), (178, 110)])

theorem root254 : rootCheck plan254 ![0, 3] ![3, 3, 2] = true := by decide +kernel

def plan255 : Plan :=
  (.e1 [(122, 64), (220, 64)] [(163, 199), (164, 137), (170, 153), (172, 153), (178, 137), (179, 199)])

theorem root255 : rootCheck plan255 ![0, 3] ![3, 3, 3] = true := by decide +kernel

def plan256 : Plan :=
  (.redFull 178)

theorem root256 : rootCheck plan256 ![1, 0] ![0, 0, 0] = true := by decide +kernel

def plan257 : Plan :=
  (.redFull 178)

theorem root257 : rootCheck plan257 ![1, 0] ![0, 0, 1] = true := by decide +kernel

def plan258 : Plan :=
  (.redFull 178)

theorem root258 : rootCheck plan258 ![1, 0] ![0, 0, 2] = true := by decide +kernel

def plan259 : Plan :=
  (.redFull 178)

theorem root259 : rootCheck plan259 ![1, 0] ![0, 0, 3] = true := by decide +kernel

def plan260 : Plan :=
  (.redFull 178)

theorem root260 : rootCheck plan260 ![1, 0] ![0, 1, 0] = true := by decide +kernel

def plan261 : Plan :=
  (.redFull 178)

theorem root261 : rootCheck plan261 ![1, 0] ![0, 1, 1] = true := by decide +kernel

def plan262 : Plan :=
  (.redFull 178)

theorem root262 : rootCheck plan262 ![1, 0] ![0, 1, 2] = true := by decide +kernel

def plan263 : Plan :=
  (.redFull 178)

theorem root263 : rootCheck plan263 ![1, 0] ![0, 1, 3] = true := by decide +kernel

def plan264 : Plan :=
  (.redFull 178)

theorem root264 : rootCheck plan264 ![1, 0] ![0, 2, 0] = true := by decide +kernel

def plan265 : Plan :=
  (.redFull 178)

theorem root265 : rootCheck plan265 ![1, 0] ![0, 2, 1] = true := by decide +kernel

def plan266 : Plan :=
  (.redFull 178)

theorem root266 : rootCheck plan266 ![1, 0] ![0, 2, 2] = true := by decide +kernel

def plan267 : Plan :=
  (.redFull 178)

theorem root267 : rootCheck plan267 ![1, 0] ![0, 2, 3] = true := by decide +kernel

def plan268 : Plan :=
  (.redFull 178)

theorem root268 : rootCheck plan268 ![1, 0] ![0, 3, 0] = true := by decide +kernel

def plan269 : Plan :=
  (.redFull 178)

theorem root269 : rootCheck plan269 ![1, 0] ![0, 3, 1] = true := by decide +kernel

def plan270 : Plan :=
  (.redFull 178)

theorem root270 : rootCheck plan270 ![1, 0] ![0, 3, 2] = true := by decide +kernel

def plan271 : Plan :=
  (.redFull 178)

theorem root271 : rootCheck plan271 ![1, 0] ![0, 3, 3] = true := by decide +kernel

def plan272 : Plan :=
  (.redFull 178)

theorem root272 : rootCheck plan272 ![1, 0] ![1, 0, 0] = true := by decide +kernel

def plan273 : Plan :=
  (.redFull 178)

theorem root273 : rootCheck plan273 ![1, 0] ![1, 0, 1] = true := by decide +kernel

def plan274 : Plan :=
  (.redFull 178)

theorem root274 : rootCheck plan274 ![1, 0] ![1, 0, 2] = true := by decide +kernel

def plan275 : Plan :=
  (.redFull 178)

theorem root275 : rootCheck plan275 ![1, 0] ![1, 0, 3] = true := by decide +kernel

def plan276 : Plan :=
  (.redFull 178)

theorem root276 : rootCheck plan276 ![1, 0] ![1, 1, 0] = true := by decide +kernel

def plan277 : Plan :=
  (.redFull 178)

theorem root277 : rootCheck plan277 ![1, 0] ![1, 1, 1] = true := by decide +kernel

def plan278 : Plan :=
  (.redFull 178)

theorem root278 : rootCheck plan278 ![1, 0] ![1, 1, 2] = true := by decide +kernel

def plan279 : Plan :=
  (.redFull 178)

theorem root279 : rootCheck plan279 ![1, 0] ![1, 1, 3] = true := by decide +kernel

def plan280 : Plan :=
  (.redFull 178)

theorem root280 : rootCheck plan280 ![1, 0] ![1, 2, 0] = true := by decide +kernel

def plan281 : Plan :=
  (.redFull 178)

theorem root281 : rootCheck plan281 ![1, 0] ![1, 2, 1] = true := by decide +kernel

def plan282 : Plan :=
  (.redFull 178)

theorem root282 : rootCheck plan282 ![1, 0] ![1, 2, 2] = true := by decide +kernel

def plan283 : Plan :=
  (.redFull 178)

theorem root283 : rootCheck plan283 ![1, 0] ![1, 2, 3] = true := by decide +kernel

def plan284 : Plan :=
  (.redFull 178)

theorem root284 : rootCheck plan284 ![1, 0] ![1, 3, 0] = true := by decide +kernel

def plan285 : Plan :=
  (.redFull 178)

theorem root285 : rootCheck plan285 ![1, 0] ![1, 3, 1] = true := by decide +kernel

def plan286 : Plan :=
  (.redFull 178)

theorem root286 : rootCheck plan286 ![1, 0] ![1, 3, 2] = true := by decide +kernel

def plan287 : Plan :=
  (.redFull 178)

theorem root287 : rootCheck plan287 ![1, 0] ![1, 3, 3] = true := by decide +kernel

def plan288 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root288 : rootCheck plan288 ![1, 0] ![2, 0, 0] = true := by decide +kernel

def plan289 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root289 : rootCheck plan289 ![1, 0] ![2, 0, 1] = true := by decide +kernel

def plan290 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root290 : rootCheck plan290 ![1, 0] ![2, 0, 2] = true := by decide +kernel

def plan291 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root291 : rootCheck plan291 ![1, 0] ![2, 0, 3] = true := by decide +kernel

def plan292 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root292 : rootCheck plan292 ![1, 0] ![2, 1, 0] = true := by decide +kernel

def plan293 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root293 : rootCheck plan293 ![1, 0] ![2, 1, 1] = true := by decide +kernel

def plan294 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root294 : rootCheck plan294 ![1, 0] ![2, 1, 2] = true := by decide +kernel

def plan295 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root295 : rootCheck plan295 ![1, 0] ![2, 1, 3] = true := by decide +kernel

def plan296 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root296 : rootCheck plan296 ![1, 0] ![2, 2, 0] = true := by decide +kernel

def plan297 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root297 : rootCheck plan297 ![1, 0] ![2, 2, 1] = true := by decide +kernel

def plan298 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root298 : rootCheck plan298 ![1, 0] ![2, 2, 2] = true := by decide +kernel

def plan299 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root299 : rootCheck plan299 ![1, 0] ![2, 2, 3] = true := by decide +kernel

def plan300 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root300 : rootCheck plan300 ![1, 0] ![2, 3, 0] = true := by decide +kernel

def plan301 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root301 : rootCheck plan301 ![1, 0] ![2, 3, 1] = true := by decide +kernel

def plan302 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root302 : rootCheck plan302 ![1, 0] ![2, 3, 2] = true := by decide +kernel

def plan303 : Plan :=
  (.e1 [(178, 53)] [(170, 42), (172, 42)])

theorem root303 : rootCheck plan303 ![1, 0] ![2, 3, 3] = true := by decide +kernel

def plan304 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root304 : rootCheck plan304 ![1, 0] ![3, 0, 0] = true := by decide +kernel

def plan305 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root305 : rootCheck plan305 ![1, 0] ![3, 0, 1] = true := by decide +kernel

def plan306 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root306 : rootCheck plan306 ![1, 0] ![3, 0, 2] = true := by decide +kernel

def plan307 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root307 : rootCheck plan307 ![1, 0] ![3, 0, 3] = true := by decide +kernel

def plan308 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root308 : rootCheck plan308 ![1, 0] ![3, 1, 0] = true := by decide +kernel

def plan309 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root309 : rootCheck plan309 ![1, 0] ![3, 1, 1] = true := by decide +kernel

def plan310 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root310 : rootCheck plan310 ![1, 0] ![3, 1, 2] = true := by decide +kernel

def plan311 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root311 : rootCheck plan311 ![1, 0] ![3, 1, 3] = true := by decide +kernel

def plan312 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root312 : rootCheck plan312 ![1, 0] ![3, 2, 0] = true := by decide +kernel

def plan313 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root313 : rootCheck plan313 ![1, 0] ![3, 2, 1] = true := by decide +kernel

def plan314 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root314 : rootCheck plan314 ![1, 0] ![3, 2, 2] = true := by decide +kernel

def plan315 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root315 : rootCheck plan315 ![1, 0] ![3, 2, 3] = true := by decide +kernel

def plan316 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root316 : rootCheck plan316 ![1, 0] ![3, 3, 0] = true := by decide +kernel

def plan317 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root317 : rootCheck plan317 ![1, 0] ![3, 3, 1] = true := by decide +kernel

def plan318 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root318 : rootCheck plan318 ![1, 0] ![3, 3, 2] = true := by decide +kernel

def plan319 : Plan :=
  (.e1 [(178, 74)] [(170, 42), (172, 42)])

theorem root319 : rootCheck plan319 ![1, 0] ![3, 3, 3] = true := by decide +kernel

def plan320 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 201), (170, 91), (172, 91), (220, 201)])

theorem root320 : rootCheck plan320 ![1, 1] ![0, 0, 0] = true := by decide +kernel

def plan321 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 200), (170, 91), (172, 91), (220, 200)])

theorem root321 : rootCheck plan321 ![1, 1] ![0, 0, 1] = true := by decide +kernel

def plan322 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 200), (170, 91), (172, 91), (220, 200)])

theorem root322 : rootCheck plan322 ![1, 1] ![0, 0, 2] = true := by decide +kernel

def plan323 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 199), (170, 91), (172, 91), (220, 199)])

theorem root323 : rootCheck plan323 ![1, 1] ![0, 0, 3] = true := by decide +kernel

def plan324 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 208), (170, 91), (172, 91), (220, 208)])

theorem root324 : rootCheck plan324 ![1, 1] ![0, 1, 0] = true := by decide +kernel

def plan325 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 206), (170, 91), (172, 91), (220, 206)])

theorem root325 : rootCheck plan325 ![1, 1] ![0, 1, 1] = true := by decide +kernel

def plan326 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 205), (170, 91), (172, 91), (220, 205)])

theorem root326 : rootCheck plan326 ![1, 1] ![0, 1, 2] = true := by decide +kernel

def plan327 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 204), (170, 91), (172, 91), (220, 204)])

theorem root327 : rootCheck plan327 ![1, 1] ![0, 1, 3] = true := by decide +kernel

def plan328 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 220), (170, 91), (172, 91), (178, 236), (220, 220)])

theorem root328 : rootCheck plan328 ![1, 1] ![0, 2, 0] = true := by decide +kernel

def plan329 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(164, 213), (170, 91), (172, 91), (178, 213), (220, 218)])

theorem root329 : rootCheck plan329 ![1, 1] ![0, 2, 1] = true := by decide +kernel

def plan330 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 217), (170, 91), (172, 91), (178, 213), (220, 217)])

theorem root330 : rootCheck plan330 ![1, 1] ![0, 2, 2] = true := by decide +kernel

def plan331 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 215), (170, 91), (172, 91), (178, 236), (220, 215)])

theorem root331 : rootCheck plan331 ![1, 1] ![0, 2, 3] = true := by decide +kernel

def plan332 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(121, 253), (122, 239), (170, 91), (172, 91), (220, 239), (221, 253)])

theorem root332 : rootCheck plan332 ![1, 1] ![0, 3, 0] = true := by decide +kernel

def plan333 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(164, 213), (170, 91), (172, 91), (178, 213), (220, 236)])

theorem root333 : rootCheck plan333 ![1, 1] ![0, 3, 1] = true := by decide +kernel

def plan334 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(164, 213), (170, 91), (172, 91), (178, 213), (220, 234)])

theorem root334 : rootCheck plan334 ![1, 1] ![0, 3, 2] = true := by decide +kernel

def plan335 : Plan :=
  (.e1 [(122, 95), (164, 87), (178, 87), (220, 95)] [(122, 231), (170, 91), (172, 91), (178, 236), (220, 231)])

theorem root335 : rootCheck plan335 ![1, 1] ![0, 3, 3] = true := by decide +kernel

def plan336 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (220, 204)])

theorem root336 : rootCheck plan336 ![1, 1] ![1, 0, 0] = true := by decide +kernel

def plan337 : Plan :=
  (.e1 [(122, 95), (164, 94), (178, 94), (220, 95)] [(122, 210), (170, 91), (172, 91), (178, 213), (220, 210)])

theorem root337 : rootCheck plan337 ![1, 1] ![1, 0, 1] = true := by decide +kernel

def plan338 : Plan :=
  (.e1 [(122, 95), (164, 94), (178, 94), (220, 95)] [(122, 209), (170, 91), (172, 91), (178, 213), (220, 209)])

theorem root338 : rootCheck plan338 ![1, 1] ![1, 0, 2] = true := by decide +kernel

def plan339 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (220, 196)])

theorem root339 : rootCheck plan339 ![1, 1] ![1, 0, 3] = true := by decide +kernel

def plan340 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (220, 219)])

theorem root340 : rootCheck plan340 ![1, 1] ![1, 1, 0] = true := by decide +kernel

def plan341 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (178, 209)])

theorem root341 : rootCheck plan341 ![1, 1] ![1, 1, 1] = true := by decide +kernel

def plan342 : Plan :=
  (.e1 [(122, 95), (164, 94), (178, 94), (220, 95)] [(122, 214), (170, 91), (172, 91), (178, 213), (220, 214)])

theorem root342 : rootCheck plan342 ![1, 1] ![1, 1, 2] = true := by decide +kernel

def plan343 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (220, 195)])

theorem root343 : rootCheck plan343 ![1, 1] ![1, 1, 3] = true := by decide +kernel

def plan344 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root344 : rootCheck plan344 ![1, 1] ![1, 2, 0] = true := by decide +kernel

def plan345 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (178, 209)])

theorem root345 : rootCheck plan345 ![1, 1] ![1, 2, 1] = true := by decide +kernel

def plan346 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (178, 209)])

theorem root346 : rootCheck plan346 ![1, 1] ![1, 2, 2] = true := by decide +kernel

def plan347 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (220, 207)])

theorem root347 : rootCheck plan347 ![1, 1] ![1, 2, 3] = true := by decide +kernel

def plan348 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root348 : rootCheck plan348 ![1, 1] ![1, 3, 0] = true := by decide +kernel

def plan349 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (178, 209)])

theorem root349 : rootCheck plan349 ![1, 1] ![1, 3, 1] = true := by decide +kernel

def plan350 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (178, 209)])

theorem root350 : rootCheck plan350 ![1, 1] ![1, 3, 2] = true := by decide +kernel

def plan351 : Plan :=
  (.e1 [(122, 111), (164, 107), (178, 107), (220, 111)] [(170, 111), (172, 111), (178, 245), (220, 223)])

theorem root351 : rootCheck plan351 ![1, 1] ![1, 3, 3] = true := by decide +kernel

def plan352 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (213, 192), (220, 111)] [(122, 232), (170, 111), (172, 111), (220, 232)])

theorem root352 : rootCheck plan352 ![1, 1] ![2, 0, 0] = true := by decide +kernel

def plan353 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root353 : rootCheck plan353 ![1, 1] ![2, 0, 1] = true := by decide +kernel

def plan354 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root354 : rootCheck plan354 ![1, 1] ![2, 0, 2] = true := by decide +kernel

def plan355 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (213, 192), (220, 111)] [(122, 221), (170, 111), (172, 111), (220, 221)])

theorem root355 : rootCheck plan355 ![1, 1] ![2, 0, 3] = true := by decide +kernel

def plan356 : Plan :=
  (.e1 [(122, 111), (129, 192), (164, 125), (178, 125), (213, 192), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root356 : rootCheck plan356 ![1, 1] ![2, 1, 0] = true := by decide +kernel

def plan357 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root357 : rootCheck plan357 ![1, 1] ![2, 1, 1] = true := by decide +kernel

def plan358 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root358 : rootCheck plan358 ![1, 1] ![2, 1, 2] = true := by decide +kernel

def plan359 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(122, 216), (170, 111), (172, 111), (178, 245), (220, 216)])

theorem root359 : rootCheck plan359 ![1, 1] ![2, 1, 3] = true := by decide +kernel

def plan360 : Plan :=
  (.e1 [(122, 111), (129, 192), (164, 125), (178, 125), (213, 192), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root360 : rootCheck plan360 ![1, 1] ![2, 2, 0] = true := by decide +kernel

def plan361 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root361 : rootCheck plan361 ![1, 1] ![2, 2, 1] = true := by decide +kernel

def plan362 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root362 : rootCheck plan362 ![1, 1] ![2, 2, 2] = true := by decide +kernel

def plan363 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(122, 224), (170, 111), (172, 111), (178, 245), (220, 224)])

theorem root363 : rootCheck plan363 ![1, 1] ![2, 2, 3] = true := by decide +kernel

def plan364 : Plan :=
  (.e1 [(122, 111), (129, 192), (164, 125), (178, 125), (213, 192), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root364 : rootCheck plan364 ![1, 1] ![2, 3, 0] = true := by decide +kernel

def plan365 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root365 : rootCheck plan365 ![1, 1] ![2, 3, 1] = true := by decide +kernel

def plan366 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root366 : rootCheck plan366 ![1, 1] ![2, 3, 2] = true := by decide +kernel

def plan367 : Plan :=
  (.e1 [(122, 111), (164, 125), (178, 125), (213, 192), (220, 111)] [(122, 226), (170, 111), (172, 111), (178, 245), (220, 226)])

theorem root367 : rootCheck plan367 ![1, 1] ![2, 3, 3] = true := by decide +kernel

def plan368 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root368 : rootCheck plan368 ![1, 1] ![3, 0, 0] = true := by decide +kernel

def plan369 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root369 : rootCheck plan369 ![1, 1] ![3, 0, 1] = true := by decide +kernel

def plan370 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root370 : rootCheck plan370 ![1, 1] ![3, 0, 2] = true := by decide +kernel

def plan371 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(170, 111), (172, 111), (178, 245), (220, 257)])

theorem root371 : rootCheck plan371 ![1, 1] ![3, 0, 3] = true := by decide +kernel

def plan372 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root372 : rootCheck plan372 ![1, 1] ![3, 1, 0] = true := by decide +kernel

def plan373 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root373 : rootCheck plan373 ![1, 1] ![3, 1, 1] = true := by decide +kernel

def plan374 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root374 : rootCheck plan374 ![1, 1] ![3, 1, 2] = true := by decide +kernel

def plan375 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(170, 111), (172, 111), (178, 245), (220, 249)])

theorem root375 : rootCheck plan375 ![1, 1] ![3, 1, 3] = true := by decide +kernel

def plan376 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root376 : rootCheck plan376 ![1, 1] ![3, 2, 0] = true := by decide +kernel

def plan377 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root377 : rootCheck plan377 ![1, 1] ![3, 2, 1] = true := by decide +kernel

def plan378 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root378 : rootCheck plan378 ![1, 1] ![3, 2, 2] = true := by decide +kernel

def plan379 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(170, 111), (172, 111), (178, 245), (220, 248)])

theorem root379 : rootCheck plan379 ![1, 1] ![3, 2, 3] = true := by decide +kernel

def plan380 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 245), (170, 111), (172, 111), (178, 245)])

theorem root380 : rootCheck plan380 ![1, 1] ![3, 3, 0] = true := by decide +kernel

def plan381 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root381 : rootCheck plan381 ![1, 1] ![3, 3, 1] = true := by decide +kernel

def plan382 : Plan :=
  (.e1 [(122, 111), (164, 150), (178, 150), (213, 158), (220, 111)] [(164, 209), (170, 111), (172, 111), (178, 209)])

theorem root382 : rootCheck plan382 ![1, 1] ![3, 3, 2] = true := by decide +kernel

def plan383 : Plan :=
  (.e1 [(122, 111), (129, 158), (164, 150), (178, 150), (213, 158), (220, 111)] [(170, 111), (172, 111), (178, 245), (220, 253)])

theorem root383 : rootCheck plan383 ![1, 1] ![3, 3, 3] = true := by decide +kernel

def plan384 : Plan :=
  (.e1 [(122, 111), (164, 162), (172, 183), (178, 162), (220, 111)] [(122, 188), (164, 191), (165, 208), (170, 172), (172, 172), (177, 208), (178, 191), (220, 188)])

theorem root384 : rootCheck plan384 ![1, 2] ![0, 0, 0] = true := by decide +kernel

def plan385 : Plan :=
  (.e1 [(122, 95), (164, 151), (170, 148), (172, 148), (178, 151), (220, 95)] [(164, 143), (170, 146), (172, 146), (178, 143), (220, 200)])

theorem root385 : rootCheck plan385 ![1, 2] ![0, 0, 1] = true := by decide +kernel

def plan386 : Plan :=
  (.e1 [(122, 95), (164, 151), (170, 148), (172, 148), (178, 151), (220, 95)] [(164, 143), (170, 146), (172, 146), (178, 143), (220, 200)])

theorem root386 : rootCheck plan386 ![1, 2] ![0, 0, 2] = true := by decide +kernel

def plan387 : Plan :=
  (.e1 [(122, 106), (164, 152), (172, 184), (178, 152), (220, 106)] [(122, 187), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 187)])

theorem root387 : rootCheck plan387 ![1, 2] ![0, 0, 3] = true := by decide +kernel

def plan388 : Plan :=
  (.e1 [(122, 111), (164, 162), (170, 193), (172, 193), (178, 162), (220, 111)] [(122, 203), (164, 191), (165, 208), (170, 172), (172, 172), (177, 208), (178, 191), (220, 203)])

theorem root388 : rootCheck plan388 ![1, 2] ![0, 1, 0] = true := by decide +kernel

def plan389 : Plan :=
  (.e1 [(122, 95), (164, 151), (170, 155), (172, 155), (178, 151), (220, 95)] [(164, 143), (170, 146), (172, 146), (178, 143), (220, 208)])

theorem root389 : rootCheck plan389 ![1, 2] ![0, 1, 1] = true := by decide +kernel

def plan390 : Plan :=
  (.e1 [(122, 95), (164, 151), (170, 155), (172, 155), (178, 151), (220, 95)] [(164, 143), (170, 146), (172, 146), (178, 143), (220, 207)])

theorem root390 : rootCheck plan390 ![1, 2] ![0, 1, 2] = true := by decide +kernel

def plan391 : Plan :=
  (.e1 [(122, 106), (164, 150), (170, 195), (172, 195), (178, 150), (220, 106)] [(122, 195), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 195)])

theorem root391 : rootCheck plan391 ![1, 2] ![0, 1, 3] = true := by decide +kernel

def plan392 : Plan :=
  (.e1 [(122, 106), (163, 263), (164, 152), (170, 211), (172, 211), (178, 152), (179, 263), (212, 292), (220, 106)] [(121, 283), (122, 224), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 224), (221, 283)])

theorem root392 : rootCheck plan392 ![1, 2] ![0, 2, 0] = true := by decide +kernel

def plan393 : Plan :=
  (.e1 [(122, 95), (164, 151), (170, 169), (172, 169), (178, 151), (220, 95)] [(122, 224), (164, 143), (170, 146), (172, 146), (178, 143), (220, 224)])

theorem root393 : rootCheck plan393 ![1, 2] ![0, 2, 1] = true := by decide +kernel

def plan394 : Plan :=
  (.e1 [(122, 95), (164, 151), (170, 169), (172, 169), (178, 151), (220, 95)] [(122, 221), (164, 143), (170, 146), (172, 146), (178, 143), (220, 221)])

theorem root394 : rootCheck plan394 ![1, 2] ![0, 2, 2] = true := by decide +kernel

def plan395 : Plan :=
  (.e1 [(122, 106), (164, 150), (165, 241), (170, 211), (172, 211), (177, 241), (178, 150), (220, 106)] [(122, 212), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 212), (221, 299)])

theorem root395 : rootCheck plan395 ![1, 2] ![0, 2, 3] = true := by decide +kernel

def plan396 : Plan :=
  (.e1 [(122, 106), (130, 263), (164, 152), (170, 235), (172, 235), (178, 152), (179, 292), (212, 263), (219, 249), (220, 106)] [(121, 248), (122, 253), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 253), (221, 248)])

theorem root396 : rootCheck plan396 ![1, 2] ![0, 3, 0] = true := by decide +kernel

def plan397 : Plan :=
  (.e1 [(122, 95), (123, 217), (164, 151), (170, 190), (172, 190), (178, 151), (219, 217), (220, 95)] [(164, 143), (170, 146), (172, 146), (178, 143), (220, 247), (221, 273)])

theorem root397 : rootCheck plan397 ![1, 2] ![0, 3, 1] = true := by decide +kernel

def plan398 : Plan :=
  (.e1 [(122, 95), (123, 217), (164, 151), (170, 190), (172, 190), (178, 151), (219, 217), (220, 95)] [(122, 244), (164, 143), (170, 146), (172, 146), (178, 143), (220, 244)])

theorem root398 : rootCheck plan398 ![1, 2] ![0, 3, 2] = true := by decide +kernel

def plan399 : Plan :=
  (.e1 [(122, 106), (164, 152), (165, 251), (170, 235), (172, 235), (177, 251), (178, 152), (219, 249), (220, 106)] [(121, 270), (122, 233), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 233), (221, 270)])

theorem root399 : rootCheck plan399 ![1, 2] ![0, 3, 3] = true := by decide +kernel

def plan400 : Plan :=
  (.e1 [(122, 111), (164, 172), (170, 183), (172, 183), (178, 172), (220, 111)] [(122, 204), (164, 191), (165, 208), (170, 172), (172, 172), (177, 208), (178, 191), (220, 204)])

theorem root400 : rootCheck plan400 ![1, 2] ![1, 0, 0] = true := by decide +kernel

def plan401 : Plan :=
  (.e1 [(122, 95), (164, 158), (170, 148), (172, 148), (178, 158), (220, 95)] [(164, 143), (170, 146), (172, 146), (178, 143), (220, 208)])

theorem root401 : rootCheck plan401 ![1, 2] ![1, 0, 1] = true := by decide +kernel

def plan402 : Plan :=
  (.e1 [(122, 106), (170, 152), (172, 152), (178, 142), (220, 106)] [(122, 194), (164, 158), (170, 143), (172, 143), (178, 158), (220, 194)])

theorem root402 : rootCheck plan402 ![1, 2] ![1, 0, 2] = true := by decide +kernel

def plan403 : Plan :=
  (.e1 [(122, 111), (164, 172), (170, 180), (172, 180), (178, 172), (220, 111)] [(122, 193), (163, 208), (164, 191), (170, 172), (172, 172), (178, 191), (179, 208), (220, 193)])

theorem root403 : rootCheck plan403 ![1, 2] ![1, 0, 3] = true := by decide +kernel

def plan404 : Plan :=
  (.e1 [(122, 111), (164, 172), (170, 193), (172, 193), (178, 172), (179, 250), (212, 265), (220, 111)] [(122, 222), (164, 191), (165, 208), (170, 172), (172, 172), (177, 208), (178, 191), (220, 222), (227, 316)])

theorem root404 : rootCheck plan404 ![1, 2] ![1, 1, 0] = true := by decide +kernel

def plan405 : Plan :=
  (.e1 [(122, 95), (164, 158), (170, 155), (172, 155), (178, 158), (220, 95)] [(122, 217), (164, 143), (170, 146), (172, 146), (178, 143), (220, 217)])

theorem root405 : rootCheck plan405 ![1, 2] ![1, 1, 1] = true := by decide +kernel

def plan406 : Plan :=
  (.e1 [(122, 95), (164, 158), (170, 155), (172, 155), (178, 158), (220, 95)] [(122, 213), (164, 143), (170, 146), (172, 146), (178, 143), (220, 213)])

theorem root406 : rootCheck plan406 ![1, 2] ![1, 1, 2] = true := by decide +kernel

def plan407 : Plan :=
  (.e1 [(122, 106), (164, 161), (170, 195), (172, 195), (177, 218), (178, 161), (220, 106)] [(122, 200), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 200)])

theorem root407 : rootCheck plan407 ![1, 2] ![1, 1, 3] = true := by decide +kernel

def plan408 : Plan :=
  (.e1 [(122, 106), (130, 263), (164, 161), (170, 211), (172, 211), (178, 161), (212, 263), (219, 284), (220, 106)] [(115, 328), (121, 276), (122, 245), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 245), (221, 276), (227, 328)])

theorem root408 : rootCheck plan408 ![1, 2] ![1, 2, 0] = true := by decide +kernel

def plan409 : Plan :=
  (.e1 [(122, 95), (123, 252), (164, 158), (170, 169), (172, 169), (178, 158), (219, 252), (220, 95)] [(122, 234), (164, 143), (170, 146), (172, 146), (178, 143), (220, 234)])

theorem root409 : rootCheck plan409 ![1, 2] ![1, 2, 1] = true := by decide +kernel

def plan410 : Plan :=
  (.e1 [(122, 95), (164, 158), (170, 169), (172, 169), (178, 158), (219, 252), (220, 95)] [(122, 227), (164, 143), (170, 146), (172, 146), (178, 143), (220, 227)])

theorem root410 : rootCheck plan410 ![1, 2] ![1, 2, 2] = true := by decide +kernel

def plan411 : Plan :=
  (.e1 [(122, 106), (123, 284), (164, 161), (165, 222), (170, 211), (172, 211), (177, 222), (178, 161), (219, 284), (220, 106)] [(122, 211), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 211)])

theorem root411 : rootCheck plan411 ![1, 2] ![1, 2, 3] = true := by decide +kernel

def plan412 : Plan :=
  (.e1 [(122, 106), (123, 249), (130, 241), (164, 161), (170, 235), (172, 235), (178, 161), (212, 241), (219, 249), (220, 106)] [(121, 244), (122, 277), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 277), (221, 244), (227, 332)])

theorem root412 : rootCheck plan412 ![1, 2] ![1, 3, 0] = true := by decide +kernel

def plan413 : Plan :=
  (.e1 [(122, 106), (164, 161), (170, 191), (172, 191), (178, 161), (219, 206), (220, 106)] [(121, 257), (164, 149), (170, 158), (172, 158), (178, 149), (220, 262), (221, 257)])

theorem root413 : rootCheck plan413 ![1, 2] ![1, 3, 1] = true := by decide +kernel

def plan414 : Plan :=
  (.e1 [(122, 95), (123, 217), (164, 158), (170, 190), (172, 190), (178, 158), (219, 217), (220, 95)] [(122, 248), (164, 143), (170, 146), (172, 146), (178, 143), (220, 248), (221, 289)])

theorem root414 : rootCheck plan414 ![1, 2] ![1, 3, 2] = true := by decide +kernel

def plan415 : Plan :=
  (.e1 [(122, 106), (123, 249), (164, 161), (165, 233), (170, 235), (172, 235), (177, 233), (178, 161), (219, 249), (220, 106)] [(121, 296), (122, 231), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 231), (221, 296)])

theorem root415 : rootCheck plan415 ![1, 2] ![1, 3, 3] = true := by decide +kernel

def plan416 : Plan :=
  (.e1 [(122, 111), (164, 190), (170, 183), (172, 183), (178, 190), (179, 250), (213, 257), (220, 111)] [(115, 282), (122, 228), (164, 191), (165, 208), (170, 172), (172, 172), (177, 208), (178, 191), (220, 228), (227, 282)])

theorem root416 : rootCheck plan416 ![1, 2] ![2, 0, 0] = true := by decide +kernel

def plan417 : Plan :=
  (.e1 [(122, 106), (170, 152), (172, 152), (178, 156), (220, 106)] [(122, 211), (164, 158), (170, 143), (172, 143), (178, 158), (220, 211), (227, 303)])

theorem root417 : rootCheck plan417 ![1, 2] ![2, 0, 1] = true := by decide +kernel

def plan418 : Plan :=
  (.e1 [(122, 106), (170, 152), (172, 152), (178, 156), (220, 106)] [(122, 209), (164, 158), (170, 143), (172, 143), (178, 158), (220, 209)])

theorem root418 : rootCheck plan418 ![1, 2] ![2, 0, 2] = true := by decide +kernel

def plan419 : Plan :=
  (.e1 [(122, 106), (164, 178), (165, 241), (170, 184), (172, 184), (177, 241), (178, 178), (220, 106)] [(122, 216), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 216), (227, 312)])

theorem root419 : rootCheck plan419 ![1, 2] ![2, 0, 3] = true := by decide +kernel

def plan420 : Plan :=
  (.e1 [(122, 106), (130, 263), (164, 178), (170, 195), (172, 195), (178, 178), (212, 263), (213, 251), (220, 106)] [(115, 287), (121, 313), (122, 247), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 247), (221, 313), (227, 287)])

theorem root420 : rootCheck plan420 ![1, 2] ![2, 1, 0] = true := by decide +kernel

def plan421 : Plan :=
  (.e1 [(122, 106), (164, 156), (170, 159), (172, 159), (178, 156), (220, 106)] [(115, 305), (122, 221), (164, 158), (170, 143), (172, 143), (177, 337), (178, 158), (220, 221), (227, 305)])

theorem root421 : rootCheck plan421 ![1, 2] ![2, 1, 1] = true := by decide +kernel

def plan422 : Plan :=
  (.e1 [(122, 106), (164, 156), (170, 159), (172, 159), (178, 156), (220, 106)] [(122, 214), (164, 158), (170, 143), (172, 143), (178, 158), (179, 337), (220, 214)])

theorem root422 : rootCheck plan422 ![1, 2] ![2, 1, 2] = true := by decide +kernel

def plan423 : Plan :=
  (.e1 [(122, 106), (164, 178), (165, 222), (170, 195), (172, 195), (177, 222), (178, 178), (213, 251), (220, 106)] [(122, 214), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 214)])

theorem root423 : rootCheck plan423 ![1, 2] ![2, 1, 3] = true := by decide +kernel

def plan424 : Plan :=
  (.e1 [(122, 106), (130, 241), (164, 178), (170, 211), (172, 211), (178, 178), (212, 241), (213, 251), (219, 284), (220, 106)] [(115, 287), (121, 277), (122, 274), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 274), (221, 277), (227, 287)])

theorem root424 : rootCheck plan424 ![1, 2] ![2, 2, 0] = true := by decide +kernel

def plan425 : Plan :=
  (.e1 [(122, 106), (129, 251), (164, 178), (170, 168), (172, 168), (178, 178), (213, 251), (220, 106)] [(122, 255), (164, 149), (170, 158), (172, 158), (178, 149), (220, 255), (221, 301)])

theorem root425 : rootCheck plan425 ![1, 2] ![2, 2, 1] = true := by decide +kernel

def plan426 : Plan :=
  (.e1 [(122, 95), (129, 256), (164, 172), (170, 169), (172, 169), (178, 172), (213, 256), (219, 252), (220, 95)] [(122, 239), (164, 143), (170, 146), (172, 146), (178, 143), (220, 239)])

theorem root426 : rootCheck plan426 ![1, 2] ![2, 2, 2] = true := by decide +kernel

def plan427 : Plan :=
  (.e1 [(122, 106), (123, 284), (164, 178), (170, 211), (172, 211), (177, 218), (178, 178), (213, 251), (219, 284), (220, 106)] [(114, 321), (122, 222), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 222), (228, 321)])

theorem root427 : rootCheck plan427 ![1, 2] ![2, 2, 3] = true := by decide +kernel

def plan428 : Plan :=
  (.e1 [(122, 106), (123, 249), (130, 226), (164, 178), (170, 235), (172, 235), (178, 178), (212, 226), (213, 251), (219, 249), (220, 106)] [(115, 294), (121, 249), (122, 310), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 310), (221, 249), (227, 294)])

theorem root428 : rootCheck plan428 ![1, 2] ![2, 3, 0] = true := by decide +kernel

def plan429 : Plan :=
  (.e1 [(122, 106), (129, 251), (164, 178), (170, 191), (172, 191), (178, 178), (213, 251), (219, 206), (220, 106)] [(121, 268), (164, 149), (170, 158), (172, 158), (178, 149), (220, 285), (221, 268)])

theorem root429 : rootCheck plan429 ![1, 2] ![2, 3, 1] = true := by decide +kernel

def plan430 : Plan :=
  (.e1 [(122, 106), (129, 251), (164, 178), (170, 191), (172, 191), (178, 178), (213, 251), (219, 206), (220, 106)] [(122, 254), (164, 149), (170, 158), (172, 158), (178, 149), (220, 254)])

theorem root430 : rootCheck plan430 ![1, 2] ![2, 3, 2] = true := by decide +kernel

def plan431 : Plan :=
  (.e1 [(122, 106), (123, 249), (129, 251), (164, 178), (170, 235), (172, 235), (177, 222), (178, 178), (213, 251), (219, 249), (220, 106)] [(114, 301), (122, 238), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 238), (221, 330), (228, 301)])

theorem root431 : rootCheck plan431 ![1, 2] ![2, 3, 3] = true := by decide +kernel

def plan432 : Plan :=
  (.e1 [(122, 106), (130, 263), (164, 202), (170, 185), (172, 185), (178, 202), (179, 292), (212, 263), (213, 216), (220, 106)] [(115, 256), (122, 259), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 259), (227, 256)])

theorem root432 : rootCheck plan432 ![1, 2] ![3, 0, 0] = true := by decide +kernel

def plan433 : Plan :=
  (.e1 [(122, 106), (170, 152), (172, 152), (178, 178), (213, 207), (220, 106)] [(115, 264), (164, 158), (170, 143), (172, 143), (178, 158), (220, 236), (227, 264)])

theorem root433 : rootCheck plan433 ![1, 2] ![3, 0, 1] = true := by decide +kernel

def plan434 : Plan :=
  (.e1 [(122, 106), (170, 152), (172, 152), (178, 178), (213, 207), (220, 106)] [(122, 232), (164, 158), (170, 143), (172, 143), (178, 158), (220, 232), (227, 268)])

theorem root434 : rootCheck plan434 ![1, 2] ![3, 0, 2] = true := by decide +kernel

def plan435 : Plan :=
  (.e1 [(122, 106), (129, 216), (164, 202), (165, 263), (170, 184), (172, 184), (177, 263), (178, 202), (213, 216), (220, 106)] [(115, 269), (122, 244), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 244), (227, 269)])

theorem root435 : rootCheck plan435 ![1, 2] ![3, 0, 3] = true := by decide +kernel

def plan436 : Plan :=
  (.e1 [(122, 106), (130, 241), (164, 202), (170, 195), (172, 195), (178, 202), (179, 329), (212, 241), (213, 216), (220, 106)] [(115, 251), (122, 282), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 282), (221, 321), (227, 251)])

theorem root436 : rootCheck plan436 ![1, 2] ![3, 1, 0] = true := by decide +kernel

def plan437 : Plan :=
  (.e1 [(122, 106), (129, 207), (170, 159), (172, 159), (178, 178), (213, 207), (220, 106)] [(115, 267), (122, 246), (164, 158), (170, 143), (172, 143), (178, 158), (220, 246), (227, 267)])

theorem root437 : rootCheck plan437 ![1, 2] ![3, 1, 1] = true := by decide +kernel

def plan438 : Plan :=
  (.e1 [(122, 106), (170, 159), (172, 159), (178, 178), (213, 207), (220, 106)] [(115, 280), (122, 237), (164, 158), (170, 143), (172, 143), (178, 158), (220, 237), (227, 280)])

theorem root438 : rootCheck plan438 ![1, 2] ![3, 1, 2] = true := by decide +kernel

def plan439 : Plan :=
  (.e1 [(122, 106), (129, 216), (164, 202), (165, 233), (170, 195), (172, 195), (177, 233), (178, 202), (213, 216), (220, 106)] [(115, 303), (122, 236), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 236), (227, 303)])

theorem root439 : rootCheck plan439 ![1, 2] ![3, 1, 3] = true := by decide +kernel

def plan440 : Plan :=
  (.e1 [(122, 106), (123, 284), (129, 216), (130, 226), (164, 202), (170, 211), (172, 211), (178, 202), (212, 226), (213, 216), (219, 284), (220, 106)] [(115, 254), (122, 313), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 313), (221, 288), (227, 254)])

theorem root440 : rootCheck plan440 ![1, 2] ![3, 2, 0] = true := by decide +kernel

def plan441 : Plan :=
  (.e1 [(122, 100), (123, 254), (129, 210), (164, 189), (170, 176), (172, 176), (178, 189), (213, 210), (219, 254), (220, 100)] [(115, 278), (164, 153), (170, 145), (172, 145), (178, 153), (220, 279), (227, 278)])

theorem root441 : rootCheck plan441 ![1, 2] ![3, 2, 1] = true := by decide +kernel

def plan442 : Plan :=
  (.e1 [(122, 100), (123, 254), (129, 210), (164, 189), (170, 176), (172, 176), (178, 189), (213, 210), (219, 254), (220, 100)] [(122, 257), (164, 153), (170, 145), (172, 145), (178, 153), (179, 318), (220, 257)])

theorem root442 : rootCheck plan442 ![1, 2] ![3, 2, 2] = true := by decide +kernel

def plan443 : Plan :=
  (.e1 [(122, 106), (123, 284), (129, 216), (164, 202), (165, 222), (170, 211), (172, 211), (177, 222), (178, 202), (213, 216), (219, 284), (220, 106)] [(122, 241), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 241), (227, 335), (228, 297)])

theorem root443 : rootCheck plan443 ![1, 2] ![3, 2, 3] = true := by decide +kernel

def plan444 : Plan :=
  (.e1 [(122, 106), (123, 249), (129, 216), (130, 219), (164, 202), (170, 235), (172, 235), (178, 202), (212, 219), (213, 216), (219, 249), (220, 106)] [(115, 265), (121, 263), (122, 352), (164, 188), (165, 220), (170, 158), (172, 158), (177, 220), (178, 188), (220, 352), (221, 263), (227, 265)])

theorem root444 : rootCheck plan444 ![1, 2] ![3, 3, 0] = true := by decide +kernel

def plan445 : Plan :=
  (.e1 [(122, 106), (129, 216), (164, 202), (170, 191), (172, 191), (178, 202), (213, 216), (219, 206), (220, 106)] [(115, 286), (121, 286), (164, 149), (170, 158), (172, 158), (178, 149), (221, 286), (227, 286)])

theorem root445 : rootCheck plan445 ![1, 2] ![3, 3, 1] = true := by decide +kernel

def plan446 : Plan :=
  (.e1 [(122, 106), (129, 216), (164, 202), (170, 191), (172, 191), (178, 202), (213, 216), (219, 206), (220, 106)] [(114, 298), (122, 273), (164, 149), (170, 158), (172, 158), (178, 149), (220, 273), (228, 298)])

theorem root446 : rootCheck plan446 ![1, 2] ![3, 3, 2] = true := by decide +kernel

def plan447 : Plan :=
  (.e1 [(122, 106), (123, 249), (129, 216), (164, 202), (170, 235), (172, 235), (177, 218), (178, 202), (213, 216), (219, 249), (220, 106)] [(114, 274), (122, 254), (163, 220), (164, 188), (170, 158), (172, 158), (178, 188), (179, 220), (220, 254), (221, 374), (227, 376), (228, 274)])

theorem root447 : rootCheck plan447 ![1, 2] ![3, 3, 3] = true := by decide +kernel

def plan448 : Plan :=
  (.e1 [(122, 95), (164, 204), (170, 163), (172, 163), (178, 204), (179, 207), (220, 95)] [(122, 201), (164, 157), (165, 193), (170, 193), (172, 193), (177, 193), (178, 157), (220, 201)])

theorem root448 : rootCheck plan448 ![1, 3] ![0, 0, 0] = true := by decide +kernel

def plan449 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 200), (164, 118), (170, 177), (172, 177), (178, 118), (220, 200)])

theorem root449 : rootCheck plan449 ![1, 3] ![0, 0, 1] = true := by decide +kernel

def plan450 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 200), (164, 118), (170, 177), (172, 177), (178, 118), (220, 200)])

theorem root450 : rootCheck plan450 ![1, 3] ![0, 0, 2] = true := by decide +kernel

def plan451 : Plan :=
  (.e1 [(122, 95), (164, 204), (170, 163), (172, 163), (177, 204), (178, 204), (220, 95)] [(122, 199), (163, 193), (164, 157), (170, 193), (172, 193), (178, 157), (179, 193), (220, 199)])

theorem root451 : rootCheck plan451 ![1, 3] ![0, 0, 3] = true := by decide +kernel

def plan452 : Plan :=
  (.e1 [(122, 95), (130, 329), (163, 218), (164, 204), (170, 170), (172, 170), (178, 204), (179, 218), (212, 329), (220, 95)] [(122, 212), (164, 157), (165, 193), (170, 193), (172, 193), (177, 193), (178, 157), (220, 212)])

theorem root452 : rootCheck plan452 ![1, 3] ![0, 1, 0] = true := by decide +kernel

def plan453 : Plan :=
  (.e1 [(122, 95), (170, 125), (172, 125), (178, 186), (220, 95)] [(122, 209), (164, 118), (170, 177), (172, 177), (178, 118), (220, 209)])

theorem root453 : rootCheck plan453 ![1, 3] ![0, 1, 1] = true := by decide +kernel

def plan454 : Plan :=
  (.e1 [(122, 95), (170, 125), (172, 125), (220, 95)] [(122, 208), (164, 118), (170, 177), (172, 177), (178, 118), (220, 208)])

theorem root454 : rootCheck plan454 ![1, 3] ![0, 1, 2] = true := by decide +kernel

def plan455 : Plan :=
  (.e1 [(122, 106), (165, 209), (170, 172), (172, 172), (177, 209), (178, 185), (220, 106)] [(122, 197), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 197)])

theorem root455 : rootCheck plan455 ![1, 3] ![0, 1, 3] = true := by decide +kernel

def plan456 : Plan :=
  (.e1 [(122, 95), (123, 268), (130, 291), (163, 235), (164, 204), (170, 184), (172, 184), (178, 204), (179, 235), (212, 291), (219, 268), (220, 95)] [(121, 325), (122, 232), (164, 157), (165, 193), (170, 193), (172, 193), (177, 193), (178, 157), (220, 232), (221, 325), (227, 375)])

theorem root456 : rootCheck plan456 ![1, 3] ![0, 2, 0] = true := by decide +kernel

def plan457 : Plan :=
  (.e1 [(122, 95), (164, 186), (170, 139), (172, 139), (178, 186), (220, 95)] [(122, 227), (164, 118), (170, 177), (172, 177), (178, 118), (220, 227)])

theorem root457 : rootCheck plan457 ![1, 3] ![0, 2, 1] = true := by decide +kernel

def plan458 : Plan :=
  (.e1 [(122, 95), (164, 186), (170, 139), (172, 139), (178, 186), (220, 95)] [(122, 224), (164, 118), (170, 177), (172, 177), (178, 118), (220, 224)])

theorem root458 : rootCheck plan458 ![1, 3] ![0, 2, 2] = true := by decide +kernel

def plan459 : Plan :=
  (.e1 [(116, 329), (122, 95), (123, 268), (164, 204), (165, 218), (170, 184), (172, 184), (177, 218), (178, 204), (219, 268), (220, 95), (226, 329)] [(122, 222), (163, 193), (164, 157), (170, 193), (172, 193), (178, 157), (179, 193), (220, 222), (221, 346)])

theorem root459 : rootCheck plan459 ![1, 3] ![0, 2, 3] = true := by decide +kernel

def plan460 : Plan :=
  (.e1 [(122, 95), (123, 233), (130, 260), (163, 260), (164, 204), (170, 205), (172, 205), (178, 204), (179, 260), (212, 260), (219, 233), (220, 95)] [(115, 372), (121, 281), (122, 261), (128, 424), (164, 157), (165, 193), (170, 193), (172, 193), (177, 193), (178, 157), (214, 424), (220, 261), (221, 281), (227, 372)])

theorem root460 : rootCheck plan460 ![1, 3] ![0, 3, 0] = true := by decide +kernel

def plan461 : Plan :=
  (.e1 [(122, 95), (123, 188), (164, 186), (170, 160), (172, 160), (178, 186), (219, 188), (220, 95)] [(164, 118), (170, 177), (172, 177), (178, 118), (220, 253), (221, 283)])

theorem root461 : rootCheck plan461 ![1, 3] ![0, 3, 1] = true := by decide +kernel

def plan462 : Plan :=
  (.e1 [(122, 95), (123, 188), (164, 186), (170, 160), (172, 160), (178, 186), (219, 188), (220, 95)] [(164, 118), (170, 177), (172, 177), (178, 118), (220, 249)])

theorem root462 : rootCheck plan462 ![1, 3] ![0, 3, 2] = true := by decide +kernel

def plan463 : Plan :=
  (.e1 [(116, 291), (122, 95), (123, 233), (164, 204), (165, 235), (170, 205), (172, 205), (177, 235), (178, 204), (219, 233), (220, 95), (226, 291)] [(114, 379), (121, 299), (122, 247), (163, 193), (164, 157), (170, 193), (172, 193), (178, 157), (179, 193), (213, 421), (220, 247), (221, 299), (228, 379)])

theorem root463 : rootCheck plan463 ![1, 3] ![0, 3, 3] = true := by decide +kernel

def plan464 : Plan :=
  (.e1 [(122, 106), (163, 223), (170, 163), (172, 163), (178, 196), (179, 223), (220, 106)] [(122, 205), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 205), (227, 330)])

theorem root464 : rootCheck plan464 ![1, 3] ![1, 0, 0] = true := by decide +kernel

def plan465 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 207), (164, 118), (170, 177), (172, 177), (178, 118), (220, 207)])

theorem root465 : rootCheck plan465 ![1, 3] ![1, 0, 1] = true := by decide +kernel

def plan466 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 206), (164, 118), (170, 177), (172, 177), (178, 118), (220, 206)])

theorem root466 : rootCheck plan466 ![1, 3] ![1, 0, 2] = true := by decide +kernel

def plan467 : Plan :=
  (.e1 [(122, 95), (164, 211), (170, 163), (172, 163), (177, 207), (178, 211), (220, 95)] [(122, 205), (163, 193), (164, 157), (170, 193), (172, 193), (178, 157), (179, 193), (220, 205)])

theorem root467 : rootCheck plan467 ![1, 3] ![1, 0, 3] = true := by decide +kernel

def plan468 : Plan :=
  (.e1 [(122, 106), (130, 274), (163, 245), (170, 172), (172, 172), (178, 196), (179, 245), (212, 274), (220, 106)] [(115, 317), (121, 329), (122, 223), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 223), (221, 329), (227, 317)])

theorem root468 : rootCheck plan468 ![1, 3] ![1, 1, 0] = true := by decide +kernel

def plan469 : Plan :=
  (.e1 [(122, 95), (170, 125), (172, 125), (178, 193), (220, 95)] [(122, 218), (164, 118), (170, 177), (172, 177), (178, 118), (220, 218)])

theorem root469 : rootCheck plan469 ![1, 3] ![1, 1, 1] = true := by decide +kernel

def plan470 : Plan :=
  (.e1 [(122, 95), (170, 125), (172, 125), (178, 193), (220, 95)] [(122, 213), (164, 118), (170, 177), (172, 177), (178, 118), (220, 213)])

theorem root470 : rootCheck plan470 ![1, 3] ![1, 1, 2] = true := by decide +kernel

def plan471 : Plan :=
  (.e1 [(122, 106), (165, 200), (170, 172), (172, 172), (177, 200), (178, 196), (220, 106)] [(122, 199), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 199)])

theorem root471 : rootCheck plan471 ![1, 3] ![1, 1, 3] = true := by decide +kernel

def plan472 : Plan :=
  (.e1 [(122, 106), (123, 262), (130, 245), (163, 274), (170, 189), (172, 189), (178, 196), (179, 274), (212, 245), (219, 262), (220, 106)] [(115, 312), (121, 284), (122, 250), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 250), (221, 284), (227, 312)])

theorem root472 : rootCheck plan472 ![1, 3] ![1, 2, 0] = true := by decide +kernel

def plan473 : Plan :=
  (.e1 [(122, 95), (164, 193), (170, 139), (172, 139), (178, 193), (219, 223), (220, 95)] [(122, 236), (164, 118), (170, 177), (172, 177), (178, 118), (220, 236)])

theorem root473 : rootCheck plan473 ![1, 3] ![1, 2, 1] = true := by decide +kernel

def plan474 : Plan :=
  (.e1 [(122, 95), (164, 193), (170, 139), (172, 139), (178, 193), (220, 95)] [(122, 228), (164, 118), (170, 177), (172, 177), (178, 118), (220, 228)])

theorem root474 : rootCheck plan474 ![1, 3] ![1, 2, 2] = true := by decide +kernel

def plan475 : Plan :=
  (.e1 [(122, 95), (123, 268), (164, 211), (165, 207), (170, 184), (172, 184), (177, 207), (178, 211), (219, 268), (220, 95)] [(122, 220), (163, 193), (164, 157), (170, 193), (172, 193), (178, 157), (179, 193), (220, 220)])

theorem root475 : rootCheck plan475 ![1, 3] ![1, 2, 3] = true := by decide +kernel

def plan476 : Plan :=
  (.e1 [(122, 95), (123, 233), (130, 235), (163, 291), (164, 211), (170, 205), (172, 205), (178, 211), (179, 291), (212, 235), (219, 233), (220, 95)] [(115, 331), (121, 272), (122, 283), (164, 157), (165, 193), (170, 193), (172, 193), (177, 193), (178, 157), (220, 283), (221, 272), (227, 331)])

theorem root476 : rootCheck plan476 ![1, 3] ![1, 3, 0] = true := by decide +kernel

def plan477 : Plan :=
  (.e1 [(122, 95), (123, 188), (164, 193), (170, 160), (172, 160), (178, 193), (219, 188), (220, 95)] [(121, 285), (164, 118), (170, 177), (172, 177), (178, 118), (220, 263), (221, 285)])

theorem root477 : rootCheck plan477 ![1, 3] ![1, 3, 1] = true := by decide +kernel

def plan478 : Plan :=
  (.e1 [(122, 95), (123, 188), (164, 193), (170, 160), (172, 160), (178, 193), (219, 188), (220, 95)] [(122, 252), (164, 118), (170, 177), (172, 177), (178, 118), (220, 252)])

theorem root478 : rootCheck plan478 ![1, 3] ![1, 3, 2] = true := by decide +kernel

def plan479 : Plan :=
  (.e1 [(116, 329), (122, 95), (123, 233), (164, 211), (165, 218), (170, 205), (172, 205), (177, 218), (178, 211), (219, 233), (220, 95), (226, 329)] [(121, 325), (122, 241), (163, 193), (164, 157), (170, 193), (172, 193), (178, 157), (179, 193), (220, 241), (221, 325), (228, 341)])

theorem root479 : rootCheck plan479 ![1, 3] ![1, 3, 3] = true := by decide +kernel

def plan480 : Plan :=
  (.e1 [(122, 106), (163, 245), (164, 213), (170, 163), (172, 163), (178, 213), (179, 245), (212, 274), (220, 106)] [(115, 285), (122, 226), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 226), (227, 285)])

theorem root480 : rootCheck plan480 ![1, 3] ![2, 0, 0] = true := by decide +kernel

def plan481 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 221), (164, 118), (170, 177), (172, 177), (178, 118), (220, 221)])

theorem root481 : rootCheck plan481 ![1, 3] ![2, 0, 1] = true := by decide +kernel

def plan482 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 219), (164, 118), (170, 177), (172, 177), (178, 118), (220, 219)])

theorem root482 : rootCheck plan482 ![1, 3] ![2, 0, 2] = true := by decide +kernel

def plan483 : Plan :=
  (.e1 [(122, 106), (164, 213), (165, 223), (170, 161), (172, 161), (177, 223), (178, 213), (220, 106)] [(122, 213), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 213), (227, 304)])

theorem root483 : rootCheck plan483 ![1, 3] ![2, 0, 3] = true := by decide +kernel

def plan484 : Plan :=
  (.e1 [(122, 106), (130, 245), (163, 274), (164, 213), (170, 172), (172, 172), (178, 213), (179, 274), (212, 245), (220, 106)] [(115, 276), (121, 323), (122, 248), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 248), (221, 323), (227, 276)])

theorem root484 : rootCheck plan484 ![1, 3] ![2, 1, 0] = true := by decide +kernel

def plan485 : Plan :=
  (.e1 [(122, 95), (164, 207), (170, 125), (172, 125), (178, 207), (220, 95)] [(122, 232), (164, 118), (170, 177), (172, 177), (178, 118), (220, 232)])

theorem root485 : rootCheck plan485 ![1, 3] ![2, 1, 1] = true := by decide +kernel

def plan486 : Plan :=
  (.e1 [(122, 95), (170, 125), (172, 125), (178, 207), (220, 95)] [(122, 224), (164, 118), (170, 177), (172, 177), (178, 118), (220, 224)])

theorem root486 : rootCheck plan486 ![1, 3] ![2, 1, 2] = true := by decide +kernel

def plan487 : Plan :=
  (.e1 [(122, 106), (164, 213), (165, 204), (170, 172), (172, 172), (177, 204), (178, 213), (220, 106)] [(122, 211), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 211)])

theorem root487 : rootCheck plan487 ![1, 3] ![2, 1, 3] = true := by decide +kernel

def plan488 : Plan :=
  (.e1 [(122, 106), (130, 223), (163, 311), (164, 213), (170, 189), (172, 189), (178, 213), (179, 311), (212, 223), (219, 262), (220, 106)] [(115, 276), (121, 282), (122, 279), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 279), (221, 282), (227, 276)])

theorem root488 : rootCheck plan488 ![1, 3] ![2, 2, 0] = true := by decide +kernel

def plan489 : Plan :=
  (.e1 [(122, 95), (123, 223), (164, 207), (170, 139), (172, 139), (178, 207), (219, 223), (220, 95)] [(122, 252), (164, 118), (170, 177), (172, 177), (178, 118), (220, 252), (227, 311)])

theorem root489 : rootCheck plan489 ![1, 3] ![2, 2, 1] = true := by decide +kernel

def plan490 : Plan :=
  (.e1 [(122, 95), (123, 223), (164, 207), (170, 139), (172, 139), (178, 207), (219, 223), (220, 95)] [(122, 239), (164, 118), (170, 177), (172, 177), (178, 118), (220, 239)])

theorem root490 : rootCheck plan490 ![1, 3] ![2, 2, 2] = true := by decide +kernel

def plan491 : Plan :=
  (.e1 [(122, 106), (123, 262), (164, 213), (165, 200), (170, 189), (172, 189), (177, 200), (178, 213), (219, 262), (220, 106)] [(122, 220), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 220)])

theorem root491 : rootCheck plan491 ![1, 3] ![2, 2, 3] = true := by decide +kernel

def plan492 : Plan :=
  (.e1 [(122, 95), (123, 233), (130, 218), (163, 329), (164, 225), (170, 205), (172, 205), (178, 225), (179, 329), (212, 218), (213, 309), (219, 233), (220, 95)] [(115, 297), (121, 270), (122, 312), (164, 157), (165, 193), (170, 193), (172, 193), (177, 193), (178, 157), (220, 312), (221, 270), (227, 297)])

theorem root492 : rootCheck plan492 ![1, 3] ![2, 3, 0] = true := by decide +kernel

def plan493 : Plan :=
  (.e1 [(122, 95), (123, 188), (164, 207), (170, 160), (172, 160), (178, 207), (219, 188), (220, 95)] [(115, 331), (121, 293), (164, 118), (170, 177), (172, 177), (178, 118), (221, 293), (227, 331)])

theorem root493 : rootCheck plan493 ![1, 3] ![2, 3, 1] = true := by decide +kernel

def plan494 : Plan :=
  (.e1 [(122, 95), (123, 188), (164, 207), (170, 160), (172, 160), (178, 207), (219, 188), (220, 95)] [(122, 262), (164, 118), (170, 177), (172, 177), (178, 118), (179, 322), (220, 262)])

theorem root494 : rootCheck plan494 ![1, 3] ![2, 3, 2] = true := by decide +kernel

def plan495 : Plan :=
  (.e1 [(122, 95), (123, 233), (164, 225), (165, 207), (170, 205), (172, 205), (177, 207), (178, 225), (213, 309), (219, 233), (220, 95)] [(114, 311), (121, 358), (122, 243), (163, 193), (164, 157), (170, 193), (172, 193), (178, 157), (179, 193), (220, 243), (221, 358), (228, 311)])

theorem root495 : rootCheck plan495 ![1, 3] ![2, 3, 3] = true := by decide +kernel

def plan496 : Plan :=
  (.e1 [(122, 106), (130, 245), (163, 274), (164, 236), (170, 163), (172, 163), (178, 236), (179, 274), (212, 245), (220, 106)] [(115, 249), (122, 256), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 256), (227, 249)])

theorem root496 : rootCheck plan496 ![1, 3] ![3, 0, 0] = true := by decide +kernel

def plan497 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 242), (164, 118), (170, 177), (172, 177), (178, 118), (220, 242), (227, 264)])

theorem root497 : rootCheck plan497 ![1, 3] ![3, 0, 1] = true := by decide +kernel

def plan498 : Plan :=
  (.e1 [(122, 95), (170, 118), (172, 118), (220, 95)] [(122, 238), (164, 118), (170, 177), (172, 177), (178, 118), (220, 238), (227, 269)])

theorem root498 : rootCheck plan498 ![1, 3] ![3, 0, 2] = true := by decide +kernel

def plan499 : Plan :=
  (.e1 [(122, 106), (164, 236), (165, 245), (170, 161), (172, 161), (177, 245), (178, 236), (214, 274), (220, 106)] [(115, 263), (122, 239), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 239), (227, 263)])

theorem root499 : rootCheck plan499 ![1, 3] ![3, 0, 3] = true := by decide +kernel

def plan500 : Plan :=
  (.e1 [(122, 106), (130, 223), (164, 236), (170, 172), (172, 172), (178, 236), (179, 311), (212, 223), (220, 106)] [(115, 244), (121, 325), (122, 282), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 282), (221, 325), (227, 244)])

theorem root500 : rootCheck plan500 ![1, 3] ![3, 1, 0] = true := by decide +kernel

def plan501 : Plan :=
  (.e1 [(122, 95), (164, 228), (170, 125), (172, 125), (178, 228), (220, 95)] [(115, 268), (164, 118), (170, 177), (172, 177), (178, 118), (220, 254), (227, 268)])

theorem root501 : rootCheck plan501 ![1, 3] ![3, 1, 1] = true := by decide +kernel

def plan502 : Plan :=
  (.e1 [(122, 95), (164, 228), (170, 125), (172, 125), (178, 228), (220, 95)] [(122, 243), (164, 118), (170, 177), (172, 177), (178, 118), (220, 243), (227, 282)])

theorem root502 : rootCheck plan502 ![1, 3] ![3, 1, 2] = true := by decide +kernel

def plan503 : Plan :=
  (.e1 [(122, 106), (164, 236), (165, 215), (170, 172), (172, 172), (177, 215), (178, 236), (213, 251), (220, 106)] [(115, 302), (122, 231), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 231), (227, 302), (228, 330)])

theorem root503 : rootCheck plan503 ![1, 3] ![3, 1, 3] = true := by decide +kernel

def plan504 : Plan :=
  (.e1 [(122, 106), (130, 209), (164, 236), (170, 189), (172, 189), (178, 236), (212, 209), (219, 262), (220, 106)] [(115, 247), (121, 289), (122, 317), (164, 168), (165, 204), (170, 190), (172, 190), (177, 204), (178, 168), (220, 317), (221, 289), (227, 247)])

theorem root504 : rootCheck plan504 ![1, 3] ![3, 2, 0] = true := by decide +kernel

def plan505 : Plan :=
  (.e1 [(122, 95), (123, 223), (164, 228), (170, 139), (172, 139), (178, 228), (213, 256), (219, 223), (220, 95)] [(115, 280), (164, 118), (170, 177), (172, 177), (178, 118), (220, 275), (227, 280)])

theorem root505 : rootCheck plan505 ![1, 3] ![3, 2, 1] = true := by decide +kernel

def plan506 : Plan :=
  (.e1 [(122, 95), (123, 223), (129, 256), (164, 228), (170, 139), (172, 139), (178, 228), (213, 256), (219, 223), (220, 95)] [(122, 256), (164, 118), (170, 177), (172, 177), (178, 118), (220, 256)])

theorem root506 : rootCheck plan506 ![1, 3] ![3, 2, 2] = true := by decide +kernel

def plan507 : Plan :=
  (.e1 [(122, 106), (123, 262), (164, 236), (165, 204), (170, 189), (172, 189), (177, 204), (178, 236), (219, 262), (220, 106)] [(114, 295), (122, 236), (163, 204), (164, 168), (170, 190), (172, 190), (178, 168), (179, 204), (220, 236), (227, 338), (228, 295)])

theorem root507 : rootCheck plan507 ![1, 3] ![3, 2, 3] = true := by decide +kernel

def plan508 : Plan :=
  (.e1 [(122, 95), (123, 233), (129, 274), (130, 207), (164, 246), (170, 205), (172, 205), (178, 246), (212, 207), (213, 274), (219, 233), (220, 95)] [(115, 271), (121, 276), (122, 350), (164, 157), (165, 193), (170, 193), (172, 193), (177, 193), (178, 157), (220, 350), (221, 276), (227, 271)])

theorem root508 : rootCheck plan508 ![1, 3] ![3, 3, 0] = true := by decide +kernel

def plan509 : Plan :=
  (.e1 [(122, 95), (123, 188), (129, 256), (164, 228), (170, 160), (172, 160), (178, 228), (213, 256), (219, 188), (220, 95)] [(121, 308), (164, 118), (170, 177), (172, 177), (178, 118), (221, 308), (227, 301)])

theorem root509 : rootCheck plan509 ![1, 3] ![3, 3, 1] = true := by decide +kernel

def plan510 : Plan :=
  (.e1 [(122, 95), (123, 188), (129, 256), (164, 228), (170, 160), (172, 160), (178, 228), (213, 256), (219, 188), (220, 95)] [(122, 278), (164, 118), (170, 177), (172, 177), (178, 118), (220, 278), (228, 330)])

theorem root510 : rootCheck plan510 ![1, 3] ![3, 3, 2] = true := by decide +kernel

def plan511 : Plan :=
  (.e1 [(122, 100), (123, 222), (129, 271), (164, 235), (165, 214), (170, 200), (172, 200), (177, 214), (178, 235), (213, 271), (219, 222), (220, 100)] [(114, 287), (122, 250), (163, 209), (164, 155), (170, 191), (172, 191), (178, 155), (179, 209), (220, 250), (227, 395), (228, 287)])

theorem root511 : rootCheck plan511 ![1, 3] ![3, 3, 3] = true := by decide +kernel

def plan512 : Plan :=
  (.redFull 178)

theorem root512 : rootCheck plan512 ![2, 0] ![0, 0, 0] = true := by decide +kernel

def plan513 : Plan :=
  (.redFull 178)

theorem root513 : rootCheck plan513 ![2, 0] ![0, 0, 1] = true := by decide +kernel

def plan514 : Plan :=
  (.redFull 178)

theorem root514 : rootCheck plan514 ![2, 0] ![0, 0, 2] = true := by decide +kernel

def plan515 : Plan :=
  (.redFull 178)

theorem root515 : rootCheck plan515 ![2, 0] ![0, 0, 3] = true := by decide +kernel

def plan516 : Plan :=
  (.redFull 178)

theorem root516 : rootCheck plan516 ![2, 0] ![0, 1, 0] = true := by decide +kernel

def plan517 : Plan :=
  (.redFull 178)

theorem root517 : rootCheck plan517 ![2, 0] ![0, 1, 1] = true := by decide +kernel

def plan518 : Plan :=
  (.redFull 178)

theorem root518 : rootCheck plan518 ![2, 0] ![0, 1, 2] = true := by decide +kernel

def plan519 : Plan :=
  (.redFull 178)

theorem root519 : rootCheck plan519 ![2, 0] ![0, 1, 3] = true := by decide +kernel

def plan520 : Plan :=
  (.redFull 178)

theorem root520 : rootCheck plan520 ![2, 0] ![0, 2, 0] = true := by decide +kernel

def plan521 : Plan :=
  (.redFull 178)

theorem root521 : rootCheck plan521 ![2, 0] ![0, 2, 1] = true := by decide +kernel

def plan522 : Plan :=
  (.redFull 178)

theorem root522 : rootCheck plan522 ![2, 0] ![0, 2, 2] = true := by decide +kernel

def plan523 : Plan :=
  (.redFull 178)

theorem root523 : rootCheck plan523 ![2, 0] ![0, 2, 3] = true := by decide +kernel

def plan524 : Plan :=
  (.redFull 178)

theorem root524 : rootCheck plan524 ![2, 0] ![0, 3, 0] = true := by decide +kernel

def plan525 : Plan :=
  (.redFull 178)

theorem root525 : rootCheck plan525 ![2, 0] ![0, 3, 1] = true := by decide +kernel

def plan526 : Plan :=
  (.redFull 178)

theorem root526 : rootCheck plan526 ![2, 0] ![0, 3, 2] = true := by decide +kernel

def plan527 : Plan :=
  (.redFull 178)

theorem root527 : rootCheck plan527 ![2, 0] ![0, 3, 3] = true := by decide +kernel

def plan528 : Plan :=
  (.redFull 178)

theorem root528 : rootCheck plan528 ![2, 0] ![1, 0, 0] = true := by decide +kernel

def plan529 : Plan :=
  (.redFull 178)

theorem root529 : rootCheck plan529 ![2, 0] ![1, 0, 1] = true := by decide +kernel

def plan530 : Plan :=
  (.redFull 178)

theorem root530 : rootCheck plan530 ![2, 0] ![1, 0, 2] = true := by decide +kernel

def plan531 : Plan :=
  (.redFull 178)

theorem root531 : rootCheck plan531 ![2, 0] ![1, 0, 3] = true := by decide +kernel

def plan532 : Plan :=
  (.redFull 178)

theorem root532 : rootCheck plan532 ![2, 0] ![1, 1, 0] = true := by decide +kernel

def plan533 : Plan :=
  (.redFull 178)

theorem root533 : rootCheck plan533 ![2, 0] ![1, 1, 1] = true := by decide +kernel

def plan534 : Plan :=
  (.redFull 178)

theorem root534 : rootCheck plan534 ![2, 0] ![1, 1, 2] = true := by decide +kernel

def plan535 : Plan :=
  (.redFull 178)

theorem root535 : rootCheck plan535 ![2, 0] ![1, 1, 3] = true := by decide +kernel

def plan536 : Plan :=
  (.redFull 178)

theorem root536 : rootCheck plan536 ![2, 0] ![1, 2, 0] = true := by decide +kernel

def plan537 : Plan :=
  (.redFull 178)

theorem root537 : rootCheck plan537 ![2, 0] ![1, 2, 1] = true := by decide +kernel

def plan538 : Plan :=
  (.redFull 178)

theorem root538 : rootCheck plan538 ![2, 0] ![1, 2, 2] = true := by decide +kernel

def plan539 : Plan :=
  (.redFull 178)

theorem root539 : rootCheck plan539 ![2, 0] ![1, 2, 3] = true := by decide +kernel

def plan540 : Plan :=
  (.redFull 178)

theorem root540 : rootCheck plan540 ![2, 0] ![1, 3, 0] = true := by decide +kernel

def plan541 : Plan :=
  (.redFull 178)

theorem root541 : rootCheck plan541 ![2, 0] ![1, 3, 1] = true := by decide +kernel

def plan542 : Plan :=
  (.redFull 178)

theorem root542 : rootCheck plan542 ![2, 0] ![1, 3, 2] = true := by decide +kernel

def plan543 : Plan :=
  (.redFull 178)

theorem root543 : rootCheck plan543 ![2, 0] ![1, 3, 3] = true := by decide +kernel

def plan544 : Plan :=
  (.redFull 178)

theorem root544 : rootCheck plan544 ![2, 0] ![2, 0, 0] = true := by decide +kernel

def plan545 : Plan :=
  (.redFull 178)

theorem root545 : rootCheck plan545 ![2, 0] ![2, 0, 1] = true := by decide +kernel

def plan546 : Plan :=
  (.redFull 178)

theorem root546 : rootCheck plan546 ![2, 0] ![2, 0, 2] = true := by decide +kernel

def plan547 : Plan :=
  (.redFull 178)

theorem root547 : rootCheck plan547 ![2, 0] ![2, 0, 3] = true := by decide +kernel

def plan548 : Plan :=
  (.redFull 178)

theorem root548 : rootCheck plan548 ![2, 0] ![2, 1, 0] = true := by decide +kernel

def plan549 : Plan :=
  (.redFull 178)

theorem root549 : rootCheck plan549 ![2, 0] ![2, 1, 1] = true := by decide +kernel

def plan550 : Plan :=
  (.redFull 178)

theorem root550 : rootCheck plan550 ![2, 0] ![2, 1, 2] = true := by decide +kernel

def plan551 : Plan :=
  (.redFull 178)

theorem root551 : rootCheck plan551 ![2, 0] ![2, 1, 3] = true := by decide +kernel

def plan552 : Plan :=
  (.redFull 178)

theorem root552 : rootCheck plan552 ![2, 0] ![2, 2, 0] = true := by decide +kernel

def plan553 : Plan :=
  (.redFull 178)

theorem root553 : rootCheck plan553 ![2, 0] ![2, 2, 1] = true := by decide +kernel

def plan554 : Plan :=
  (.redFull 178)

theorem root554 : rootCheck plan554 ![2, 0] ![2, 2, 2] = true := by decide +kernel

def plan555 : Plan :=
  (.redFull 178)

theorem root555 : rootCheck plan555 ![2, 0] ![2, 2, 3] = true := by decide +kernel

def plan556 : Plan :=
  (.redFull 178)

theorem root556 : rootCheck plan556 ![2, 0] ![2, 3, 0] = true := by decide +kernel

def plan557 : Plan :=
  (.redFull 178)

theorem root557 : rootCheck plan557 ![2, 0] ![2, 3, 1] = true := by decide +kernel

def plan558 : Plan :=
  (.redFull 178)

theorem root558 : rootCheck plan558 ![2, 0] ![2, 3, 2] = true := by decide +kernel

def plan559 : Plan :=
  (.redFull 178)

theorem root559 : rootCheck plan559 ![2, 0] ![2, 3, 3] = true := by decide +kernel

def plan560 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root560 : rootCheck plan560 ![2, 0] ![3, 0, 0] = true := by decide +kernel

def plan561 : Plan :=
  (.e1 [(129, 116), (164, 82), (178, 82), (213, 116), (220, 139)] [(170, 70), (172, 70)])

theorem root561 : rootCheck plan561 ![2, 0] ![3, 0, 1] = true := by decide +kernel

def plan562 : Plan :=
  (.e1 [(129, 116), (164, 82), (178, 82), (213, 116), (220, 139)] [(170, 70), (172, 70)])

theorem root562 : rootCheck plan562 ![2, 0] ![3, 0, 2] = true := by decide +kernel

def plan563 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root563 : rootCheck plan563 ![2, 0] ![3, 0, 3] = true := by decide +kernel

def plan564 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root564 : rootCheck plan564 ![2, 0] ![3, 1, 0] = true := by decide +kernel

def plan565 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root565 : rootCheck plan565 ![2, 0] ![3, 1, 1] = true := by decide +kernel

def plan566 : Plan :=
  (.e1 [(129, 116), (164, 82), (178, 82), (213, 116), (220, 139)] [(170, 70), (172, 70)])

theorem root566 : rootCheck plan566 ![2, 0] ![3, 1, 2] = true := by decide +kernel

def plan567 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root567 : rootCheck plan567 ![2, 0] ![3, 1, 3] = true := by decide +kernel

def plan568 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root568 : rootCheck plan568 ![2, 0] ![3, 2, 0] = true := by decide +kernel

def plan569 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root569 : rootCheck plan569 ![2, 0] ![3, 2, 1] = true := by decide +kernel

def plan570 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root570 : rootCheck plan570 ![2, 0] ![3, 2, 2] = true := by decide +kernel

def plan571 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root571 : rootCheck plan571 ![2, 0] ![3, 2, 3] = true := by decide +kernel

def plan572 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root572 : rootCheck plan572 ![2, 0] ![3, 3, 0] = true := by decide +kernel

def plan573 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root573 : rootCheck plan573 ![2, 0] ![3, 3, 1] = true := by decide +kernel

def plan574 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root574 : rootCheck plan574 ![2, 0] ![3, 3, 2] = true := by decide +kernel

def plan575 : Plan :=
  (.e1 [(164, 104), (178, 104), (213, 113)] [(170, 88), (172, 88)])

theorem root575 : rootCheck plan575 ![2, 0] ![3, 3, 3] = true := by decide +kernel

def plan576 : Plan :=
  (.redFull 178)

theorem root576 : rootCheck plan576 ![2, 1] ![0, 0, 0] = true := by decide +kernel

def plan577 : Plan :=
  (.redFull 178)

theorem root577 : rootCheck plan577 ![2, 1] ![0, 0, 1] = true := by decide +kernel

def plan578 : Plan :=
  (.redFull 178)

theorem root578 : rootCheck plan578 ![2, 1] ![0, 0, 2] = true := by decide +kernel

def plan579 : Plan :=
  (.redFull 178)

theorem root579 : rootCheck plan579 ![2, 1] ![0, 0, 3] = true := by decide +kernel

def plan580 : Plan :=
  (.redFull 178)

theorem root580 : rootCheck plan580 ![2, 1] ![0, 1, 0] = true := by decide +kernel

def plan581 : Plan :=
  (.redFull 178)

theorem root581 : rootCheck plan581 ![2, 1] ![0, 1, 1] = true := by decide +kernel

def plan582 : Plan :=
  (.redFull 178)

theorem root582 : rootCheck plan582 ![2, 1] ![0, 1, 2] = true := by decide +kernel

def plan583 : Plan :=
  (.redFull 178)

theorem root583 : rootCheck plan583 ![2, 1] ![0, 1, 3] = true := by decide +kernel

def plan584 : Plan :=
  (.redFull 178)

theorem root584 : rootCheck plan584 ![2, 1] ![0, 2, 0] = true := by decide +kernel

def plan585 : Plan :=
  (.redFull 178)

theorem root585 : rootCheck plan585 ![2, 1] ![0, 2, 1] = true := by decide +kernel

def plan586 : Plan :=
  (.redFull 178)

theorem root586 : rootCheck plan586 ![2, 1] ![0, 2, 2] = true := by decide +kernel

def plan587 : Plan :=
  (.redFull 178)

theorem root587 : rootCheck plan587 ![2, 1] ![0, 2, 3] = true := by decide +kernel

def plan588 : Plan :=
  (.redFull 178)

theorem root588 : rootCheck plan588 ![2, 1] ![0, 3, 0] = true := by decide +kernel

def plan589 : Plan :=
  (.redFull 178)

theorem root589 : rootCheck plan589 ![2, 1] ![0, 3, 1] = true := by decide +kernel

def plan590 : Plan :=
  (.redFull 178)

theorem root590 : rootCheck plan590 ![2, 1] ![0, 3, 2] = true := by decide +kernel

def plan591 : Plan :=
  (.redFull 178)

theorem root591 : rootCheck plan591 ![2, 1] ![0, 3, 3] = true := by decide +kernel

def plan592 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 189), (172, 189), (178, 110), (220, 157)] [(122, 162), (164, 254), (165, 269), (170, 151), (172, 151), (177, 269), (178, 254), (220, 162)])

theorem root592 : rootCheck plan592 ![2, 1] ![1, 0, 0] = true := by decide +kernel

def plan593 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 151), (172, 151), (178, 110), (220, 157)] [(122, 157), (170, 151), (172, 151), (220, 157)])

theorem root593 : rootCheck plan593 ![2, 1] ![1, 0, 1] = true := by decide +kernel

def plan594 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 151), (172, 151), (178, 110), (220, 157)] [(122, 151), (170, 151), (172, 151), (220, 151)])

theorem root594 : rootCheck plan594 ![2, 1] ![1, 0, 2] = true := by decide +kernel

def plan595 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 186), (172, 186), (177, 214), (178, 110), (220, 157)] [(122, 152), (170, 151), (172, 151), (220, 152)])

theorem root595 : rootCheck plan595 ![2, 1] ![1, 0, 3] = true := by decide +kernel

def plan596 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 202), (172, 202), (178, 110), (220, 157)] [(121, 256), (122, 179), (164, 254), (165, 269), (170, 151), (172, 151), (177, 269), (178, 254), (220, 179), (221, 256)])

theorem root596 : rootCheck plan596 ![2, 1] ![1, 1, 0] = true := by decide +kernel

def plan597 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 164), (172, 164), (178, 110), (220, 157)] [(122, 170), (164, 211), (170, 151), (172, 151), (178, 211), (220, 170)])

theorem root597 : rootCheck plan597 ![2, 1] ![1, 1, 1] = true := by decide +kernel

def plan598 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 164), (172, 164), (178, 110), (220, 157)] [(122, 158), (170, 151), (172, 151), (178, 211), (220, 158)])

theorem root598 : rootCheck plan598 ![2, 1] ![1, 1, 2] = true := by decide +kernel

def plan599 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 202), (172, 202), (177, 200), (178, 110), (220, 157)] [(122, 154), (170, 151), (172, 151), (178, 254), (220, 154)])

theorem root599 : rootCheck plan599 ![2, 1] ![1, 1, 3] = true := by decide +kernel

def plan600 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 223), (172, 223), (178, 110), (212, 247), (220, 157)] [(121, 220), (122, 205), (164, 254), (165, 269), (170, 151), (172, 151), (177, 269), (178, 254), (220, 205), (221, 220), (227, 307)])

theorem root600 : rootCheck plan600 ![2, 1] ![1, 2, 0] = true := by decide +kernel

def plan601 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 185), (172, 185), (178, 110), (220, 157)] [(121, 236), (122, 192), (164, 211), (170, 151), (172, 151), (178, 211), (220, 192), (221, 236)])

theorem root601 : rootCheck plan601 ![2, 1] ![1, 2, 1] = true := by decide +kernel

def plan602 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 174), (172, 174), (178, 110), (220, 157)] [(122, 181), (164, 199), (170, 151), (172, 151), (178, 199), (220, 181)])

theorem root602 : rootCheck plan602 ![2, 1] ![1, 2, 2] = true := by decide +kernel

def plan603 : Plan :=
  (.e1 [(122, 157), (164, 110), (165, 256), (170, 192), (172, 192), (177, 256), (178, 110), (220, 157)] [(122, 171), (163, 327), (164, 219), (170, 151), (172, 151), (178, 219), (179, 327), (220, 171)])

theorem root603 : rootCheck plan603 ![2, 1] ![1, 2, 3] = true := by decide +kernel

def plan604 : Plan :=
  (.e1 [(122, 157), (123, 262), (164, 110), (170, 253), (172, 253), (178, 110), (213, 261), (219, 262), (220, 157)] [(115, 311), (121, 191), (122, 237), (164, 254), (165, 269), (170, 151), (172, 151), (177, 269), (178, 254), (220, 237), (221, 191), (227, 311)])

theorem root604 : rootCheck plan604 ![2, 1] ![1, 3, 0] = true := by decide +kernel

def plan605 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 215), (172, 215), (178, 110), (219, 224), (220, 157)] [(121, 203), (122, 221), (164, 211), (170, 151), (172, 151), (178, 211), (220, 221), (221, 203)])

theorem root605 : rootCheck plan605 ![2, 1] ![1, 3, 1] = true := by decide +kernel

def plan606 : Plan :=
  (.e1 [(122, 157), (164, 110), (170, 215), (172, 215), (178, 110), (219, 224), (220, 157)] [(121, 230), (122, 197), (164, 211), (170, 151), (172, 151), (178, 211), (220, 197), (221, 230)])

theorem root606 : rootCheck plan606 ![2, 1] ![1, 3, 2] = true := by decide +kernel

def plan607 : Plan :=
  (.e1 [(122, 157), (164, 110), (165, 270), (170, 222), (172, 222), (177, 270), (178, 110), (219, 231), (220, 157)] [(121, 234), (122, 193), (163, 327), (164, 219), (170, 151), (172, 151), (178, 219), (179, 327), (220, 193), (221, 234), (228, 329)])

theorem root607 : rootCheck plan607 ![2, 1] ![1, 3, 3] = true := by decide +kernel

def plan608 : Plan :=
  (.e1 [(122, 157), (129, 211), (163, 262), (164, 131), (170, 189), (172, 189), (178, 131), (179, 262), (213, 211), (220, 157)] [(115, 264), (122, 191), (164, 254), (165, 269), (170, 151), (172, 151), (177, 269), (178, 254), (220, 191), (227, 264)])

theorem root608 : rootCheck plan608 ![2, 1] ![2, 0, 0] = true := by decide +kernel

def plan609 : Plan :=
  (.e1 [(122, 157), (164, 131), (170, 151), (172, 151), (178, 131), (220, 157)] [(122, 181), (164, 211), (170, 151), (172, 151), (178, 211), (220, 181), (227, 255)])

theorem root609 : rootCheck plan609 ![2, 1] ![2, 0, 1] = true := by decide +kernel

def plan610 : Plan :=
  (.e1 [(122, 157), (164, 131), (170, 148), (172, 148), (178, 131), (220, 157)] [(122, 173), (164, 211), (170, 151), (172, 151), (178, 211), (220, 173)])

theorem root610 : rootCheck plan610 ![2, 1] ![2, 0, 2] = true := by decide +kernel

def plan611 : Plan :=
  (.e1 [(122, 157), (129, 211), (164, 131), (165, 234), (170, 186), (172, 186), (177, 234), (178, 131), (213, 211), (220, 157)] [(122, 178), (163, 269), (164, 254), (170, 151), (172, 151), (178, 254), (179, 269), (220, 178)])

theorem root611 : rootCheck plan611 ![2, 1] ![2, 0, 3] = true := by decide +kernel

def plan612 : Plan :=
  (.e1 [(122, 157), (129, 211), (164, 131), (170, 202), (172, 202), (178, 131), (212, 247), (213, 211), (220, 157)] [(115, 256), (121, 260), (122, 212), (164, 254), (165, 269), (170, 151), (172, 151), (177, 269), (178, 254), (220, 212), (221, 260), (227, 256)])

theorem root612 : rootCheck plan612 ![2, 1] ![2, 1, 0] = true := by decide +kernel

def plan613 : Plan :=
  (.e1 [(122, 157), (129, 211), (164, 131), (170, 164), (172, 164), (178, 131), (213, 211), (220, 157)] [(115, 257), (122, 196), (164, 211), (170, 151), (172, 151), (178, 211), (220, 196), (227, 257)])

theorem root613 : rootCheck plan613 ![2, 1] ![2, 1, 1] = true := by decide +kernel

def plan614 : Plan :=
  (.e1 [(122, 157), (129, 211), (164, 131), (170, 164), (172, 164), (178, 131), (213, 211), (220, 157)] [(122, 178), (164, 211), (170, 151), (172, 151), (178, 211), (220, 178)])

theorem root614 : rootCheck plan614 ![2, 1] ![2, 1, 2] = true := by decide +kernel

def plan615 : Plan :=
  (.e1 [(122, 157), (129, 211), (164, 131), (165, 214), (170, 192), (172, 192), (177, 214), (178, 131), (213, 211), (220, 157)] [(122, 172), (164, 254), (170, 151), (172, 151), (178, 254), (179, 269), (220, 172)])

theorem root615 : rootCheck plan615 ![2, 1] ![2, 1, 3] = true := by decide +kernel

def plan616 : Plan :=
  (.cut 1 (.redFull 178) (.e1 [(122, 151), (123, 306), (129, 214), (130, 240), (164, 127), (170, 218), (172, 218), (178, 127), (212, 240), (213, 214), (219, 306), (220, 151)] [(115, 267), (121, 236), (122, 233), (164, 246), (165, 276), (170, 146), (172, 146), (177, 276), (178, 246), (220, 233), (221, 236), (227, 267)]))

theorem root616 : rootCheck plan616 ![2, 1] ![2, 2, 0] = true := by decide +kernel

def plan617 : Plan :=
  (.e1 [(122, 157), (129, 211), (164, 131), (170, 185), (172, 185), (178, 131), (213, 211), (220, 157)] [(115, 267), (121, 250), (122, 219), (164, 211), (170, 151), (172, 151), (178, 211), (220, 219), (221, 250), (227, 267)])

theorem root617 : rootCheck plan617 ![2, 1] ![2, 2, 1] = true := by decide +kernel

def plan618 : Plan :=
  (.e1 [(122, 157), (123, 254), (129, 211), (164, 131), (170, 174), (172, 174), (178, 131), (213, 211), (219, 254), (220, 157)] [(114, 350), (122, 202), (164, 199), (170, 151), (172, 151), (178, 199), (220, 202), (221, 277), (228, 350)])

theorem root618 : rootCheck plan618 ![2, 1] ![2, 2, 2] = true := by decide +kernel

def plan619 : Plan :=
  (.e1 [(122, 157), (123, 272), (129, 211), (164, 131), (165, 252), (170, 192), (172, 192), (177, 252), (178, 131), (213, 211), (219, 272), (220, 157)] [(114, 308), (122, 189), (163, 327), (164, 219), (170, 151), (172, 151), (178, 219), (179, 327), (220, 189), (228, 308)])

theorem root619 : rootCheck plan619 ![2, 1] ![2, 2, 3] = true := by decide +kernel

def plan620 : Plan :=
  (.cut 1 (.redFull 178) (.cut 4 (.e1 [(122, 157), (123, 273), (129, 215), (130, 234), (164, 135), (170, 211), (172, 211), (178, 135), (212, 234), (213, 215), (219, 273), (220, 157)] [(115, 258), (121, 227), (164, 233), (165, 288), (170, 155), (172, 155), (177, 288), (178, 233), (220, 242), (221, 227), (227, 258)]) (.e1 [(122, 157), (123, 238), (129, 215), (130, 232), (164, 135), (170, 229), (172, 229), (178, 135), (212, 232), (213, 215), (219, 238), (220, 157)] [(115, 269), (121, 209), (122, 266), (164, 227), (170, 155), (172, 155), (178, 227), (220, 266), (221, 209), (227, 269)])))

theorem root620 : rootCheck plan620 ![2, 1] ![2, 3, 0] = true := by decide +kernel

def plan621 : Plan :=
  (.e1 [(122, 157), (123, 224), (129, 211), (164, 131), (170, 215), (172, 215), (178, 131), (213, 211), (219, 224), (220, 157)] [(115, 284), (121, 219), (122, 250), (164, 211), (170, 151), (172, 151), (178, 211), (220, 250), (221, 219), (227, 284)])

theorem root621 : rootCheck plan621 ![2, 1] ![2, 3, 1] = true := by decide +kernel

def plan622 : Plan :=
  (.e1 [(122, 157), (123, 224), (129, 211), (164, 131), (170, 215), (172, 215), (177, 277), (178, 131), (213, 211), (219, 224), (220, 157)] [(121, 259), (122, 213), (164, 211), (170, 151), (172, 151), (178, 211), (220, 213), (221, 259), (228, 290)])

theorem root622 : rootCheck plan622 ![2, 1] ![2, 3, 2] = true := by decide +kernel

def plan623 : Plan :=
  (.cut 1 (.redFull 178) (.e1 [(122, 151), (123, 243), (129, 214), (164, 127), (165, 252), (170, 226), (172, 226), (177, 252), (178, 127), (213, 214), (219, 243), (220, 151)] [(114, 292), (115, 376), (121, 272), (122, 205), (163, 314), (164, 223), (170, 146), (172, 146), (178, 223), (179, 314), (220, 205), (221, 272), (227, 376), (228, 292)]))

theorem root623 : rootCheck plan623 ![2, 1] ![2, 3, 3] = true := by decide +kernel

def plan624 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 223), (172, 223), (178, 111), (213, 146), (220, 151)] [(115, 255), (122, 217), (164, 285), (170, 106), (172, 106), (178, 285), (220, 217), (227, 255)]) (.e1 [(122, 151), (129, 173), (130, 267), (163, 301), (164, 155), (170, 188), (172, 188), (178, 155), (179, 301), (212, 267), (213, 173), (220, 151)] [(115, 227), (121, 323), (122, 225), (164, 246), (165, 276), (170, 146), (172, 146), (177, 276), (178, 246), (220, 225), (221, 323), (227, 227)]))

theorem root624 : rootCheck plan624 ![2, 1] ![3, 0, 0] = true := by decide +kernel

def plan625 : Plan :=
  (.e1 [(122, 157), (164, 161), (170, 151), (172, 151), (178, 161), (213, 170), (220, 157)] [(115, 212), (122, 215), (164, 211), (170, 151), (172, 151), (178, 211), (220, 215), (227, 212)])

theorem root625 : rootCheck plan625 ![2, 1] ![3, 0, 1] = true := by decide +kernel

def plan626 : Plan :=
  (.e1 [(122, 157), (129, 170), (164, 161), (170, 151), (172, 151), (178, 161), (213, 170), (220, 157)] [(122, 203), (164, 211), (170, 151), (172, 151), (178, 211), (220, 203), (227, 225)])

theorem root626 : rootCheck plan626 ![2, 1] ![3, 0, 2] = true := by decide +kernel

def plan627 : Plan :=
  (.e1 [(122, 157), (129, 170), (164, 161), (165, 262), (170, 186), (172, 186), (177, 262), (178, 161), (213, 170), (220, 157)] [(114, 349), (115, 229), (122, 214), (163, 269), (164, 254), (170, 151), (172, 151), (178, 254), (179, 269), (220, 214), (227, 229), (228, 349)])

theorem root627 : rootCheck plan627 ![2, 1] ![3, 0, 3] = true := by decide +kernel

def plan628 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 232), (172, 232), (178, 111), (213, 146), (220, 151)] [(115, 251), (121, 292), (122, 231), (170, 106), (172, 106), (178, 285), (220, 231), (221, 292), (227, 251)]) (.cut 4 (.cut 0 (.e1 [(122, 128), (129, 175), (130, 274), (164, 143), (170, 219), (172, 219), (178, 143), (212, 274), (213, 175), (220, 128)] [(115, 254), (164, 242), (165, 269), (170, 126), (172, 126), (177, 269), (178, 242), (220, 249), (227, 254)]) (.e1 [(122, 154), (129, 175), (130, 243), (163, 331), (164, 148), (170, 201), (172, 201), (178, 148), (179, 331), (212, 243), (213, 175), (219, 369), (220, 154)] [(115, 227), (121, 282), (122, 238), (164, 254), (165, 276), (170, 144), (172, 144), (177, 276), (178, 254), (220, 238), (221, 282), (227, 227)])) (.e1 [(122, 151), (129, 173), (164, 155), (170, 182), (172, 182), (178, 155), (212, 266), (213, 173), (220, 151)] [(115, 223), (121, 297), (122, 239), (164, 228), (165, 303), (170, 146), (172, 146), (177, 303), (178, 228), (220, 239), (221, 297), (227, 223)])))

theorem root628 : rootCheck plan628 ![2, 1] ![3, 1, 0] = true := by decide +kernel

def plan629 : Plan :=
  (.e1 [(122, 157), (129, 170), (164, 161), (170, 164), (172, 164), (178, 161), (213, 170), (220, 157)] [(115, 216), (122, 232), (164, 211), (170, 151), (172, 151), (178, 211), (220, 232), (221, 311), (227, 216)])

theorem root629 : rootCheck plan629 ![2, 1] ![3, 1, 1] = true := by decide +kernel

def plan630 : Plan :=
  (.e1 [(122, 157), (129, 170), (164, 161), (170, 164), (172, 164), (178, 161), (213, 170), (220, 157)] [(115, 242), (122, 207), (164, 211), (170, 151), (172, 151), (178, 211), (220, 207), (227, 242)])

theorem root630 : rootCheck plan630 ![2, 1] ![3, 1, 2] = true := by decide +kernel

def plan631 : Plan :=
  (.e1 [(122, 157), (129, 170), (164, 161), (165, 234), (170, 192), (172, 192), (177, 234), (178, 161), (213, 170), (220, 157)] [(115, 249), (122, 205), (163, 269), (164, 254), (170, 151), (172, 151), (178, 254), (179, 269), (220, 205), (227, 249), (228, 307)])

theorem root631 : rootCheck plan631 ![2, 1] ![3, 1, 3] = true := by decide +kernel

def plan632 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 249), (172, 249), (178, 111), (212, 286), (213, 146), (220, 151)] [(115, 253), (121, 262), (170, 106), (172, 106), (178, 285), (220, 252), (221, 262), (227, 253)]) (.cut 4 (.cut 0 (.e1 [(122, 128), (129, 175), (164, 143), (172, 235), (178, 143), (212, 254), (213, 175), (220, 128)] [(115, 255), (121, 271), (164, 242), (165, 269), (170, 126), (172, 126), (177, 269), (178, 242), (220, 273), (221, 271), (227, 255)]) (.e1 [(122, 154), (123, 317), (129, 175), (130, 223), (163, 382), (164, 148), (170, 220), (172, 220), (178, 148), (179, 382), (212, 223), (213, 175), (219, 317), (220, 154)] [(115, 228), (121, 250), (122, 266), (164, 254), (165, 276), (170, 144), (172, 144), (177, 276), (178, 254), (220, 266), (221, 250), (227, 228)])) (.e1 [(122, 151), (123, 289), (129, 173), (130, 248), (164, 155), (170, 202), (172, 202), (178, 155), (212, 248), (213, 173), (219, 289), (220, 151)] [(115, 228), (121, 263), (122, 265), (164, 228), (165, 303), (170, 146), (172, 146), (177, 303), (178, 228), (220, 265), (221, 263), (227, 228)])))

theorem root632 : rootCheck plan632 ![2, 1] ![3, 2, 0] = true := by decide +kernel

def plan633 : Plan :=
  (.e1 [(122, 157), (123, 265), (129, 170), (164, 161), (170, 185), (172, 185), (178, 161), (212, 280), (213, 170), (219, 265), (220, 157)] [(115, 227), (121, 274), (122, 257), (164, 211), (170, 151), (172, 151), (178, 211), (220, 257), (221, 274), (227, 227)])

theorem root633 : rootCheck plan633 ![2, 1] ![3, 2, 1] = true := by decide +kernel

def plan634 : Plan :=
  (.e1 [(122, 157), (123, 265), (129, 170), (164, 161), (165, 277), (170, 185), (172, 185), (177, 277), (178, 161), (213, 170), (219, 265), (220, 157)] [(115, 268), (122, 219), (164, 211), (170, 151), (172, 151), (178, 211), (220, 219), (221, 341), (227, 268), (228, 281)])

theorem root634 : rootCheck plan634 ![2, 1] ![3, 2, 2] = true := by decide +kernel

def plan635 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 249), (172, 249), (177, 273), (178, 111), (213, 146), (220, 151)] [(114, 296), (122, 211), (164, 285), (170, 106), (172, 106), (178, 285), (220, 211), (228, 296)]) (.cut 0 (.e1 [(122, 128), (129, 175), (164, 143), (170, 224), (172, 224), (177, 258), (178, 143), (213, 175), (220, 128)] [(114, 304), (122, 222), (163, 286), (164, 230), (170, 126), (172, 126), (178, 230), (179, 286), (220, 222), (228, 304)]) (.e1 [(122, 157), (123, 302), (128, 426), (129, 174), (164, 157), (165, 212), (170, 213), (172, 213), (177, 212), (178, 157), (213, 174), (214, 426), (219, 302), (220, 157)] [(114, 262), (115, 299), (121, 382), (122, 204), (163, 277), (164, 247), (170, 151), (172, 151), (178, 247), (179, 277), (220, 204), (221, 382), (227, 299), (228, 262)])))

theorem root635 : rootCheck plan635 ![2, 1] ![3, 2, 3] = true := by decide +kernel

def plan636 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 275), (172, 275), (178, 111), (212, 273), (213, 146), (220, 151)] [(115, 261), (121, 239), (164, 285), (170, 106), (172, 106), (178, 285), (220, 280), (221, 239), (227, 261)]) (.cut 0 (.e1 [(122, 128), (129, 175), (130, 258), (164, 143), (170, 248), (172, 248), (178, 143), (212, 258), (213, 175), (220, 128)] [(115, 265), (121, 252), (164, 230), (170, 126), (172, 126), (177, 286), (178, 230), (221, 252), (227, 265)]) (.cut 4 (.e1 [(122, 154), (123, 268), (129, 175), (130, 220), (164, 148), (170, 241), (172, 241), (178, 148), (179, 449), (212, 220), (213, 175), (219, 268), (220, 154)] [(114, 372), (115, 238), (121, 228), (122, 298), (164, 247), (165, 285), (170, 144), (172, 144), (177, 285), (178, 247), (220, 298), (221, 228), (227, 238), (228, 372)]) (.e1 [(122, 157), (123, 244), (129, 174), (130, 234), (164, 157), (170, 226), (172, 226), (178, 157), (212, 234), (213, 174), (219, 244), (220, 157)] [(115, 238), (121, 233), (122, 297), (164, 228), (165, 306), (170, 151), (172, 151), (177, 306), (178, 228), (220, 297), (221, 233), (227, 238)]))))

theorem root636 : rootCheck plan636 ![2, 1] ![3, 3, 0] = true := by decide +kernel

def plan637 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 252), (172, 252), (178, 111), (213, 146), (219, 287), (220, 151)] [(115, 278), (121, 259), (164, 260), (170, 106), (172, 106), (178, 260), (220, 255), (221, 259), (227, 278)]) (.e1 [(122, 151), (123, 229), (129, 173), (130, 291), (164, 155), (170, 212), (172, 212), (178, 155), (212, 291), (213, 173), (219, 229), (220, 151)] [(114, 318), (115, 255), (121, 251), (122, 279), (164, 208), (170, 146), (172, 146), (178, 208), (220, 279), (221, 251), (227, 255), (228, 318)]))

theorem root637 : rootCheck plan637 ![2, 1] ![3, 3, 1] = true := by decide +kernel

def plan638 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 252), (172, 252), (178, 111), (213, 146), (220, 151)] [(114, 300), (122, 236), (164, 260), (170, 106), (172, 106), (178, 260), (220, 236), (221, 284), (227, 303), (228, 300)]) (.e1 [(122, 151), (123, 229), (129, 173), (164, 155), (165, 289), (170, 212), (172, 212), (177, 289), (178, 155), (213, 173), (219, 229), (220, 151)] [(114, 267), (115, 300), (121, 296), (122, 239), (164, 208), (170, 146), (172, 146), (178, 208), (220, 239), (221, 296), (227, 300), (228, 267)]))

theorem root638 : rootCheck plan638 ![2, 1] ![3, 3, 2] = true := by decide +kernel

def plan639 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 146), (164, 111), (170, 275), (172, 275), (177, 268), (178, 111), (213, 146), (220, 151)] [(114, 276), (122, 222), (164, 285), (170, 106), (172, 106), (178, 285), (220, 222), (221, 313), (228, 276)]) (.cut 0 (.e1 [(122, 128), (129, 175), (164, 143), (165, 254), (170, 248), (172, 248), (177, 254), (178, 143), (213, 175), (219, 280), (220, 128)] [(114, 281), (122, 233), (164, 230), (170, 126), (172, 126), (178, 230), (179, 286), (220, 233), (228, 281)]) (.cut 4 (.e1 [(122, 157), (123, 244), (129, 174), (164, 157), (165, 233), (170, 226), (172, 226), (177, 233), (178, 157), (213, 174), (219, 244), (220, 157)] [(114, 247), (115, 322), (121, 317), (122, 222), (164, 228), (170, 151), (172, 151), (178, 228), (179, 306), (220, 222), (221, 317), (227, 322), (228, 247)]) (.e1 [(122, 157), (123, 254), (129, 174), (164, 157), (165, 215), (170, 236), (172, 236), (177, 215), (178, 157), (213, 174), (219, 254), (220, 157)] [(114, 242), (122, 218), (163, 286), (164, 240), (170, 151), (172, 151), (178, 240), (179, 286), (220, 218), (221, 328), (227, 333), (228, 242)]))))

theorem root639 : rootCheck plan639 ![2, 1] ![3, 3, 3] = true := by decide +kernel

def plan640 : Plan :=
  (.e1 [(122, 139), (163, 199), (164, 135), (170, 163), (172, 163), (178, 135), (179, 199), (220, 139)] [(122, 152), (164, 207), (165, 241), (170, 177), (172, 177), (177, 241), (178, 207), (220, 152)])

theorem root640 : rootCheck plan640 ![2, 2] ![0, 0, 0] = true := by decide +kernel

def plan641 : Plan :=
  (.e1 [(164, 134), (170, 128), (172, 128), (178, 134), (220, 128)] [(122, 162), (164, 159), (170, 165), (172, 165), (178, 159), (220, 162)])

theorem root641 : rootCheck plan641 ![2, 2] ![0, 0, 1] = true := by decide +kernel

def plan642 : Plan :=
  (.e1 [(164, 134), (170, 128), (172, 128), (178, 134), (220, 128)] [(122, 162), (164, 159), (170, 165), (172, 165), (178, 159), (220, 162)])

theorem root642 : rootCheck plan642 ![2, 2] ![0, 0, 2] = true := by decide +kernel

def plan643 : Plan :=
  (.e1 [(122, 139), (165, 195), (170, 163), (172, 163), (177, 195), (178, 135), (220, 139)] [(122, 150), (163, 241), (164, 207), (170, 177), (172, 177), (178, 207), (179, 241), (220, 150)])

theorem root643 : rootCheck plan643 ![2, 2] ![0, 0, 3] = true := by decide +kernel

def plan644 : Plan :=
  (.cut 1 (.e1 [(122, 151), (163, 230), (164, 118), (170, 161), (172, 161), (178, 118), (179, 230), (220, 151)] [(115, 381), (121, 306), (122, 152), (164, 209), (165, 276), (170, 171), (172, 171), (177, 276), (178, 209), (220, 152), (221, 306), (227, 381)]) (.e1 [(122, 139), (123, 327), (130, 336), (163, 202), (164, 151), (170, 160), (172, 160), (178, 151), (179, 202), (212, 336), (219, 327), (220, 139)] [(115, 371), (121, 329), (122, 163), (164, 195), (165, 231), (170, 194), (172, 194), (177, 231), (178, 195), (220, 163), (221, 329), (227, 371)]))

theorem root644 : rootCheck plan644 ![2, 2] ![0, 1, 0] = true := by decide +kernel

def plan645 : Plan :=
  (.e1 [(122, 139), (164, 135), (170, 131), (172, 131), (178, 135), (220, 139)] [(122, 161), (164, 164), (170, 177), (172, 177), (178, 164), (220, 161)])

theorem root645 : rootCheck plan645 ![2, 2] ![0, 1, 1] = true := by decide +kernel

def plan646 : Plan :=
  (.e1 [(122, 139), (164, 135), (170, 131), (172, 131), (178, 135), (220, 139)] [(122, 159), (164, 164), (170, 177), (172, 177), (178, 164), (220, 159)])

theorem root646 : rootCheck plan646 ![2, 2] ![0, 1, 2] = true := by decide +kernel

def plan647 : Plan :=
  (.e1 [(122, 145), (164, 142), (165, 201), (170, 155), (172, 155), (177, 201), (178, 142), (220, 145)] [(122, 154), (163, 248), (164, 194), (170, 192), (172, 192), (178, 194), (179, 248), (220, 154)])

theorem root647 : rootCheck plan647 ![2, 2] ![0, 1, 3] = true := by decide +kernel

def plan648 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 278), (130, 278), (163, 243), (164, 128), (170, 191), (172, 191), (178, 128), (179, 243), (212, 278), (219, 278), (220, 151)] [(121, 246), (122, 182), (164, 216), (165, 250), (170, 180), (172, 180), (177, 250), (178, 216), (220, 182), (221, 246)]) (.cut 4 (.cut 0 (.e1 [(122, 136), (123, 267), (130, 242), (163, 225), (164, 166), (170, 192), (172, 192), (178, 166), (179, 225), (212, 242), (219, 267), (220, 136)] [(121, 258), (122, 206), (164, 200), (165, 209), (170, 205), (172, 205), (177, 209), (178, 200), (220, 206), (221, 258)]) (.e1 [(122, 160), (123, 259), (130, 231), (163, 213), (164, 166), (170, 178), (172, 178), (178, 166), (179, 213), (212, 231), (219, 259), (220, 160)] [(115, 312), (121, 247), (122, 190), (164, 206), (165, 216), (170, 231), (172, 231), (177, 216), (178, 206), (220, 190), (221, 247), (227, 312)])) (.e1 [(122, 145), (123, 243), (163, 262), (164, 156), (170, 149), (172, 149), (178, 156), (179, 262), (219, 243), (220, 145)] [(115, 341), (121, 271), (122, 183), (164, 168), (165, 272), (170, 205), (172, 205), (177, 272), (178, 168), (220, 183), (221, 271), (227, 341)])))

theorem root648 : rootCheck plan648 ![2, 2] ![0, 2, 0] = true := by decide +kernel

def plan649 : Plan :=
  (.e1 [(122, 139), (123, 242), (164, 136), (170, 142), (172, 142), (178, 136), (219, 242), (220, 139)] [(115, 366), (121, 276), (122, 180), (164, 159), (170, 177), (172, 177), (178, 159), (220, 180), (221, 276), (227, 366)])

theorem root649 : rootCheck plan649 ![2, 2] ![0, 2, 1] = true := by decide +kernel

def plan650 : Plan :=
  (.e1 [(122, 139), (123, 248), (164, 135), (170, 147), (172, 147), (178, 135), (219, 248), (220, 139)] [(121, 284), (122, 175), (164, 164), (170, 177), (172, 177), (178, 164), (220, 175), (221, 284)])

theorem root650 : rootCheck plan650 ![2, 2] ![0, 2, 2] = true := by decide +kernel

def plan651 : Plan :=
  (.e1 [(116, 308), (122, 151), (123, 262), (164, 150), (165, 203), (170, 174), (172, 174), (177, 203), (178, 150), (219, 262), (220, 151), (226, 308)] [(114, 376), (121, 275), (122, 172), (163, 236), (164, 198), (170, 207), (172, 207), (178, 198), (179, 236), (220, 172), (221, 275), (228, 376)])

theorem root651 : rootCheck plan651 ![2, 2] ![0, 2, 3] = true := by decide +kernel

def plan652 : Plan :=
  (.cut 1 (.e1 [(115, 459), (122, 151), (123, 237), (130, 243), (163, 278), (164, 128), (170, 219), (172, 219), (178, 128), (179, 278), (212, 243), (213, 354), (219, 237), (220, 151), (227, 459)] [(115, 353), (121, 207), (122, 213), (128, 449), (164, 216), (165, 250), (170, 180), (172, 180), (177, 250), (178, 216), (214, 449), (220, 213), (221, 207), (227, 353)]) (.cut 4 (.cut 0 (.e1 [(122, 131), (123, 237), (130, 243), (163, 259), (164, 156), (170, 213), (172, 213), (178, 156), (179, 259), (212, 243), (213, 374), (219, 237), (220, 131)] [(115, 355), (121, 233), (122, 227), (164, 195), (165, 221), (170, 189), (172, 189), (177, 221), (178, 195), (214, 428), (220, 227), (221, 233), (227, 355)]) (.cut 3 (.cut 1 (.e1 [(122, 157), (123, 242), (130, 231), (163, 240), (164, 148), (170, 198), (172, 198), (178, 148), (179, 240), (212, 231), (219, 242), (220, 157)] [(115, 330), (121, 223), (122, 202), (164, 210), (165, 229), (170, 209), (172, 209), (177, 229), (178, 210), (220, 202), (221, 223), (227, 330)]) (.cut 4 (.e1 [(115, 504), (122, 157), (123, 238), (129, 397), (130, 219), (163, 227), (164, 166), (170, 193), (172, 193), (178, 166), (179, 227), (212, 219), (213, 397), (219, 238), (220, 157), (227, 504)] [(115, 319), (121, 228), (122, 207), (128, 404), (164, 205), (165, 215), (170, 228), (172, 228), (177, 215), (178, 205), (214, 404), (220, 207), (221, 228), (227, 319)]) (.e1 [(122, 157), (123, 221), (130, 238), (163, 247), (164, 166), (170, 177), (172, 177), (178, 166), (179, 247), (212, 238), (219, 221), (220, 157)] [(115, 319), (121, 230), (122, 205), (164, 187), (165, 237), (170, 228), (172, 228), (177, 237), (178, 187), (220, 205), (221, 230), (227, 319)]))) (.cut 1 (.e1 [(115, 472), (122, 154), (123, 224), (129, 384), (130, 228), (163, 259), (164, 146), (170, 211), (172, 211), (178, 146), (179, 259), (212, 228), (213, 384), (219, 224), (220, 154), (227, 472)] [(115, 342), (116, 677), (121, 209), (122, 216), (128, 417), (129, 696), (164, 207), (165, 235), (170, 203), (172, 203), (177, 235), (178, 207), (213, 696), (214, 417), (220, 216), (221, 209), (226, 677), (227, 342)]) (.cut 4 (.cut 2 (.cut 0 (.e1 [(122, 145), (123, 224), (130, 233), (163, 233), (164, 163), (170, 207), (172, 207), (178, 163), (179, 233), (212, 233), (219, 224), (220, 145)] [(115, 355), (121, 227), (122, 217), (164, 197), (165, 217), (170, 215), (172, 215), (177, 217), (178, 197), (220, 217), (221, 227), (227, 355)]) (.e1 [(122, 158), (123, 219), (130, 221), (163, 230), (164, 161), (170, 205), (172, 205), (178, 161), (179, 230), (212, 221), (219, 219), (220, 158), (227, 470)] [(115, 342), (121, 215), (122, 212), (128, 378), (164, 204), (165, 219), (170, 227), (172, 227), (177, 219), (178, 204), (214, 378), (220, 212), (221, 215), (227, 342)])) (.cut 0 (.e1 [(122, 145), (123, 231), (130, 215), (163, 249), (164, 161), (170, 214), (172, 214), (178, 161), (179, 249), (212, 215), (219, 231), (220, 145)] [(115, 332), (121, 218), (122, 227), (164, 204), (165, 214), (170, 210), (172, 210), (177, 214), (178, 204), (220, 227), (221, 218), (227, 332)]) (.e1 [(115, 500), (122, 157), (123, 225), (129, 393), (130, 208), (131, 694), (163, 244), (164, 161), (170, 207), (172, 207), (178, 161), (179, 244), (211, 694), (212, 208), (213, 393), (219, 225), (220, 157), (227, 500)] [(115, 322), (116, 660), (121, 211), (122, 220), (128, 407), (129, 726), (164, 207), (165, 217), (170, 223), (172, 223), (177, 217), (178, 207), (213, 726), (214, 407), (220, 220), (221, 211), (226, 660), (227, 322)]))) (.e1 [(122, 154), (123, 205), (130, 233), (163, 264), (164, 163), (170, 192), (172, 192), (178, 163), (179, 264), (212, 233), (219, 205), (220, 154)] [(115, 332), (121, 215), (122, 220), (128, 402), (164, 185), (165, 240), (170, 222), (172, 222), (177, 240), (178, 185), (214, 402), (220, 220), (221, 215), (227, 332)]))))) (.e1 [(122, 151), (123, 194), (130, 259), (163, 293), (164, 161), (170, 177), (172, 177), (178, 161), (179, 293), (212, 259), (219, 194), (220, 151)] [(121, 219), (122, 219), (164, 169), (165, 267), (170, 217), (172, 217), (177, 267), (178, 169), (220, 219), (221, 219), (227, 334)])))

theorem root652 : rootCheck plan652 ![2, 2] ![0, 3, 0] = true := by decide +kernel

def plan653 : Plan :=
  (.e1 [(122, 145), (123, 188), (164, 143), (170, 162), (172, 162), (178, 143), (219, 188), (220, 145)] [(121, 228), (122, 208), (164, 154), (165, 352), (170, 192), (172, 192), (177, 352), (178, 154), (220, 208), (221, 228)])

theorem root653 : rootCheck plan653 ![2, 2] ![0, 3, 1] = true := by decide +kernel

def plan654 : Plan :=
  (.e1 [(122, 151), (123, 194), (164, 135), (170, 159), (172, 159), (178, 135), (219, 194), (220, 151)] [(121, 233), (122, 192), (164, 159), (170, 189), (172, 189), (178, 159), (179, 373), (220, 192), (221, 233)])

theorem root654 : rootCheck plan654 ![2, 2] ![0, 3, 2] = true := by decide +kernel

def plan655 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 237), (164, 126), (165, 243), (170, 219), (172, 219), (177, 243), (178, 126), (219, 237), (220, 151), (226, 278)] [(114, 385), (121, 221), (122, 196), (163, 250), (164, 216), (170, 180), (172, 180), (178, 216), (179, 250), (220, 196), (221, 221), (228, 385)]) (.cut 4 (.e1 [(122, 151), (123, 194), (164, 159), (165, 259), (170, 177), (172, 177), (177, 259), (178, 159), (219, 194), (220, 151), (226, 293)] [(121, 231), (122, 205), (163, 267), (164, 169), (170, 217), (172, 217), (178, 169), (179, 267), (220, 205), (221, 231), (228, 366)]) (.cut 0 (.e1 [(116, 259), (122, 134), (123, 233), (164, 159), (165, 227), (170, 216), (172, 216), (177, 227), (178, 159), (219, 233), (220, 134), (226, 259)] [(121, 242), (122, 215), (163, 215), (164, 197), (170, 197), (172, 197), (178, 197), (179, 215), (220, 215), (221, 242), (228, 371)]) (.cut 3 (.e1 [(116, 264), (122, 157), (123, 236), (164, 159), (165, 202), (170, 191), (172, 191), (177, 202), (178, 159), (219, 236), (220, 157), (226, 264)] [(114, 353), (121, 246), (122, 187), (163, 223), (164, 203), (170, 223), (172, 223), (178, 203), (179, 223), (213, 378), (220, 187), (221, 246), (228, 353)]) (.cut 1 (.e1 [(116, 264), (122, 154), (123, 224), (164, 144), (165, 224), (170, 211), (172, 211), (177, 224), (178, 144), (219, 224), (220, 154), (226, 264)] [(114, 358), (121, 226), (122, 199), (129, 401), (163, 235), (164, 207), (170, 203), (172, 203), (178, 207), (179, 235), (213, 401), (220, 199), (221, 226), (228, 358)]) (.cut 4 (.e1 [(116, 269), (122, 154), (123, 205), (164, 162), (165, 229), (170, 192), (172, 192), (177, 229), (178, 162), (219, 205), (220, 154), (226, 269)] [(114, 348), (121, 231), (122, 203), (163, 240), (164, 185), (170, 222), (172, 222), (178, 185), (179, 240), (213, 386), (220, 203), (221, 231), (228, 348)]) (.cut 2 (.e1 [(116, 232), (122, 157), (123, 218), (164, 163), (165, 214), (170, 209), (172, 209), (177, 214), (178, 163), (219, 218), (220, 157), (226, 232)] [(114, 353), (121, 223), (122, 208), (129, 366), (163, 215), (164, 205), (170, 228), (172, 228), (178, 205), (179, 215), (213, 366), (220, 208), (221, 223), (228, 353)]) (.e1 [(116, 252), (122, 157), (123, 218), (164, 165), (165, 199), (170, 209), (172, 209), (177, 199), (178, 165), (219, 218), (220, 157), (226, 252)] [(114, 327), (121, 235), (122, 200), (163, 215), (164, 205), (170, 228), (172, 228), (178, 205), (179, 215), (213, 396), (220, 200), (221, 235), (228, 327)]))))))))

theorem root655 : rootCheck plan655 ![2, 2] ![0, 3, 3] = true := by decide +kernel

def plan656 : Plan :=
  (.cut 1 (.e1 [(122, 151), (163, 217), (164, 139), (170, 160), (172, 160), (178, 139), (179, 217), (220, 151)] [(115, 314), (122, 161), (164, 216), (165, 250), (170, 180), (172, 180), (177, 250), (178, 216), (220, 161), (227, 314)]) (.e1 [(122, 139), (130, 336), (163, 202), (164, 160), (170, 152), (172, 152), (178, 160), (179, 202), (212, 336), (220, 139)] [(115, 330), (121, 370), (122, 164), (164, 195), (165, 231), (170, 194), (172, 194), (177, 231), (178, 195), (220, 164), (221, 370), (227, 330)]))

theorem root656 : rootCheck plan656 ![2, 2] ![1, 0, 0] = true := by decide +kernel

def plan657 : Plan :=
  (.e1 [(122, 128), (164, 142), (170, 128), (172, 128), (178, 142), (220, 128)] [(122, 171), (164, 159), (170, 165), (172, 165), (178, 159), (220, 171)])

theorem root657 : rootCheck plan657 ![2, 2] ![1, 0, 1] = true := by decide +kernel

def plan658 : Plan :=
  (.e1 [(122, 128), (164, 142), (170, 128), (172, 128), (178, 142), (220, 128)] [(122, 169), (164, 159), (170, 165), (172, 165), (178, 159), (220, 169)])

theorem root658 : rootCheck plan658 ![2, 2] ![1, 0, 2] = true := by decide +kernel

def plan659 : Plan :=
  (.e1 [(122, 139), (129, 310), (164, 143), (165, 199), (170, 163), (172, 163), (177, 199), (178, 143), (213, 310), (214, 399), (220, 139)] [(115, 362), (122, 158), (163, 241), (164, 207), (170, 177), (172, 177), (178, 207), (179, 241), (220, 158), (227, 362)])

theorem root659 : rootCheck plan659 ![2, 2] ![1, 0, 3] = true := by decide +kernel

def plan660 : Plan :=
  (.cut 1 (.e1 [(122, 157), (130, 254), (163, 236), (164, 145), (170, 173), (172, 173), (178, 145), (179, 236), (212, 254), (220, 157)] [(115, 288), (121, 271), (122, 182), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (220, 182), (221, 271), (227, 288)]) (.cut 4 (.cut 2 (.e1 [(122, 145), (123, 321), (130, 283), (163, 211), (164, 162), (170, 159), (172, 159), (178, 162), (179, 211), (212, 283), (219, 321), (220, 145)] [(115, 315), (121, 308), (122, 173), (164, 198), (165, 226), (170, 205), (172, 205), (177, 226), (178, 198), (220, 173), (221, 308), (227, 315)]) (.cut 1 (.e1 [(122, 151), (123, 322), (130, 252), (163, 226), (164, 161), (170, 165), (172, 165), (178, 161), (179, 226), (212, 252), (219, 322), (220, 151)] [(115, 285), (121, 287), (122, 184), (164, 209), (165, 227), (170, 203), (172, 203), (177, 227), (178, 209), (220, 184), (221, 287), (227, 285)]) (.e1 [(122, 151), (123, 313), (129, 327), (130, 244), (163, 218), (164, 178), (170, 156), (172, 156), (178, 178), (179, 218), (212, 244), (213, 327), (219, 313), (220, 151)] [(115, 277), (121, 294), (122, 185), (164, 199), (165, 219), (170, 221), (172, 221), (177, 219), (178, 199), (220, 185), (221, 294), (227, 277)]))) (.e1 [(122, 139), (163, 273), (164, 163), (170, 134), (172, 134), (178, 163), (179, 273), (212, 323), (220, 139)] [(115, 294), (121, 321), (122, 179), (164, 168), (165, 277), (170, 194), (172, 194), (177, 277), (178, 168), (220, 179), (221, 321), (227, 294)])))

theorem root660 : rootCheck plan660 ![2, 2] ![1, 1, 0] = true := by decide +kernel

def plan661 : Plan :=
  (.e1 [(122, 139), (164, 143), (170, 131), (172, 131), (178, 143), (220, 139)] [(115, 315), (122, 172), (164, 164), (170, 177), (172, 177), (178, 164), (220, 172), (221, 323), (227, 315)])

theorem root661 : rootCheck plan661 ![2, 2] ![1, 1, 1] = true := by decide +kernel

def plan662 : Plan :=
  (.e1 [(122, 139), (164, 143), (170, 131), (172, 131), (178, 143), (220, 139)] [(122, 164), (164, 164), (170, 177), (172, 177), (178, 164), (220, 164)])

theorem root662 : rootCheck plan662 ![2, 2] ![1, 1, 2] = true := by decide +kernel

def plan663 : Plan :=
  (.e1 [(122, 145), (129, 315), (164, 153), (165, 195), (170, 155), (172, 155), (177, 195), (178, 153), (213, 315), (220, 145)] [(122, 158), (163, 248), (164, 194), (170, 192), (172, 192), (178, 194), (179, 248), (220, 158), (221, 377)])

theorem root663 : rootCheck plan663 ![2, 2] ![1, 1, 3] = true := by decide +kernel

def plan664 : Plan :=
  (.cut 1 (.cut 4 (.cut 0 (.e1 [(122, 136), (130, 231), (164, 144), (170, 213), (172, 213), (178, 144), (179, 280), (212, 231), (220, 136)] [(115, 301), (121, 240), (122, 225), (164, 221), (165, 229), (170, 170), (172, 170), (177, 229), (178, 221), (220, 225), (221, 240), (227, 301)]) (.e1 [(122, 157), (123, 283), (129, 299), (130, 230), (163, 266), (164, 139), (170, 194), (172, 194), (178, 139), (179, 266), (212, 230), (213, 299), (219, 283), (220, 157)] [(115, 292), (116, 561), (121, 233), (122, 203), (128, 520), (164, 225), (165, 242), (170, 186), (172, 186), (177, 242), (178, 225), (214, 520), (220, 203), (221, 233), (226, 561), (227, 292)])) (.e1 [(122, 157), (123, 251), (130, 253), (164, 145), (170, 171), (172, 171), (178, 145), (212, 253), (219, 251), (220, 157)] [(115, 285), (121, 237), (122, 204), (164, 196), (165, 276), (170, 191), (172, 191), (177, 276), (178, 196), (220, 204), (221, 237), (227, 285)])) (.cut 4 (.cut 2 (.cut 1 (.e1 [(122, 157), (123, 267), (130, 219), (163, 241), (164, 157), (170, 187), (172, 187), (178, 157), (179, 241), (212, 219), (213, 340), (219, 267), (220, 157)] [(115, 294), (121, 236), (122, 203), (164, 213), (165, 223), (170, 211), (172, 211), (177, 223), (178, 213), (220, 203), (221, 236), (227, 294)]) (.e1 [(115, 562), (122, 157), (123, 259), (129, 357), (130, 211), (163, 234), (164, 174), (170, 178), (172, 178), (178, 174), (179, 234), (212, 211), (213, 357), (219, 259), (220, 157), (221, 668), (227, 562)] [(114, 636), (115, 285), (121, 241), (122, 206), (128, 447), (129, 728), (164, 204), (165, 214), (170, 230), (172, 230), (177, 214), (178, 204), (213, 728), (214, 447), (220, 206), (221, 241), (227, 285), (228, 636)])) (.cut 0 (.e1 [(122, 134), (123, 271), (130, 223), (163, 264), (164, 173), (170, 190), (172, 190), (178, 173), (179, 264), (212, 223), (219, 271), (220, 134)] [(115, 289), (121, 255), (122, 227), (164, 197), (165, 215), (170, 197), (172, 197), (177, 215), (178, 197), (220, 227), (221, 255), (227, 289)]) (.cut 1 (.cut 3 (.e1 [(122, 160), (123, 287), (130, 216), (163, 243), (164, 165), (170, 175), (172, 175), (178, 165), (179, 243), (212, 216), (213, 313), (219, 287), (220, 160)] [(115, 269), (121, 249), (122, 201), (164, 214), (165, 224), (170, 215), (172, 215), (177, 224), (178, 214), (220, 201), (221, 249), (227, 269)]) (.cut 4 (.cut 0 (.e1 [(122, 150), (123, 269), (130, 205), (163, 265), (164, 164), (170, 195), (172, 195), (178, 164), (179, 265), (212, 205), (213, 307), (219, 269), (220, 150)] [(115, 276), (121, 233), (122, 225), (164, 214), (165, 219), (170, 203), (172, 203), (177, 219), (178, 214), (220, 225), (221, 233), (227, 276)]) (.e1 [(122, 160), (123, 267), (129, 315), (130, 205), (163, 259), (164, 162), (170, 186), (172, 186), (178, 162), (179, 259), (212, 205), (213, 315), (219, 267), (220, 160)] [(115, 272), (121, 230), (122, 214), (128, 497), (164, 216), (165, 225), (170, 212), (172, 212), (177, 225), (178, 216), (214, 497), (220, 214), (221, 230), (226, 573), (227, 272)])) (.e1 [(122, 160), (123, 249), (130, 217), (163, 280), (164, 165), (170, 173), (172, 173), (178, 165), (179, 280), (212, 217), (213, 313), (219, 249), (220, 160)] [(115, 268), (121, 232), (122, 214), (164, 199), (165, 242), (170, 215), (172, 215), (177, 242), (178, 199), (220, 214), (221, 232), (227, 268)]))) (.cut 3 (.e1 [(122, 160), (123, 279), (129, 331), (130, 208), (163, 235), (164, 182), (170, 166), (172, 166), (178, 182), (179, 235), (212, 208), (213, 331), (219, 279), (220, 160)] [(115, 261), (121, 255), (122, 203), (164, 205), (165, 215), (170, 234), (172, 234), (177, 215), (178, 205), (220, 203), (221, 255), (227, 261)]) (.cut 4 (.cut 1 (.cut 3 (.e1 [(122, 160), (123, 271), (129, 323), (130, 200), (163, 247), (164, 175), (170, 178), (172, 178), (178, 175), (179, 247), (212, 200), (213, 323), (219, 271), (220, 160)] [(115, 264), (121, 239), (122, 213), (164, 211), (165, 216), (170, 225), (172, 225), (177, 216), (178, 211), (220, 213), (221, 239), (227, 264)]) (.cut 0 (.e1 [(122, 145), (123, 268), (129, 321), (130, 213), (163, 256), (164, 168), (170, 191), (172, 191), (178, 168), (179, 256), (212, 213), (213, 321), (219, 268), (220, 145)] [(115, 286), (121, 241), (122, 220), (164, 207), (165, 216), (170, 205), (172, 205), (177, 216), (178, 207), (220, 220), (221, 241), (227, 286)]) (.e1 [(122, 160), (123, 259), (129, 325), (130, 198), (163, 257), (164, 172), (170, 182), (172, 182), (178, 172), (179, 257), (212, 198), (213, 325), (219, 259), (220, 160)] [(114, 589), (115, 267), (116, 584), (121, 231), (122, 218), (128, 483), (164, 209), (165, 219), (170, 224), (172, 224), (177, 219), (178, 209), (214, 483), (220, 218), (221, 231), (226, 584), (227, 267), (228, 589)]))) (.cut 3 (.e1 [(122, 160), (123, 267), (129, 332), (130, 196), (163, 243), (164, 183), (170, 175), (172, 175), (178, 183), (179, 243), (212, 196), (213, 332), (219, 267), (220, 160)] [(115, 260), (121, 242), (122, 214), (164, 207), (165, 212), (170, 235), (172, 235), (177, 212), (178, 207), (220, 214), (221, 242), (227, 260)]) (.cut 4 (.e1 [(122, 157), (123, 258), (129, 332), (130, 194), (163, 252), (164, 181), (170, 182), (172, 182), (178, 181), (179, 252), (212, 194), (213, 332), (219, 258), (220, 157)] [(115, 265), (116, 585), (121, 234), (122, 222), (128, 475), (164, 207), (165, 212), (170, 230), (172, 230), (177, 212), (178, 207), (214, 475), (220, 222), (221, 234), (226, 585), (227, 265), (228, 598)]) (.redProjected 0 1)))) (.e1 [(122, 160), (123, 240), (129, 331), (130, 210), (163, 273), (164, 182), (170, 164), (172, 164), (178, 182), (179, 273), (212, 210), (213, 331), (219, 240), (220, 160)] [(115, 260), (121, 237), (122, 218), (164, 188), (165, 235), (170, 234), (172, 234), (177, 235), (178, 188), (220, 218), (221, 237), (227, 260)])))))) (.cut 2 (.e1 [(122, 145), (123, 243), (130, 287), (163, 283), (164, 162), (170, 149), (172, 149), (178, 162), (179, 283), (212, 287), (219, 243), (220, 145)] [(115, 307), (121, 265), (122, 194), (164, 168), (165, 272), (170, 205), (172, 205), (177, 272), (178, 168), (220, 194), (221, 265), (227, 307)]) (.e1 [(115, 584), (121, 619), (122, 151), (123, 236), (129, 322), (130, 255), (163, 298), (164, 174), (170, 149), (172, 149), (178, 174), (179, 298), (212, 255), (213, 322), (219, 236), (220, 151), (221, 619), (227, 584)] [(114, 537), (115, 275), (116, 638), (121, 255), (122, 208), (163, 697), (164, 169), (165, 267), (170, 217), (172, 217), (177, 267), (178, 169), (179, 697), (220, 208), (221, 255), (226, 638), (227, 275), (228, 537)]))))

theorem root664 : rootCheck plan664 ![2, 2] ![1, 2, 0] = true := by decide +kernel

def plan665 : Plan :=
  (.e1 [(122, 139), (123, 242), (130, 371), (164, 146), (170, 142), (172, 142), (178, 146), (212, 371), (213, 297), (219, 242), (220, 139)] [(115, 315), (121, 280), (122, 193), (164, 159), (165, 364), (170, 177), (172, 177), (177, 364), (178, 159), (220, 193), (221, 280), (227, 315)])

theorem root665 : rootCheck plan665 ![2, 2] ![1, 2, 1] = true := by decide +kernel

def plan666 : Plan :=
  (.e1 [(122, 139), (123, 242), (164, 146), (165, 315), (170, 142), (172, 142), (177, 315), (178, 146), (219, 242), (220, 139)] [(121, 301), (122, 183), (164, 159), (170, 177), (172, 177), (178, 159), (220, 183), (221, 301)])

theorem root666 : rootCheck plan666 ![2, 2] ![1, 2, 2] = true := by decide +kernel

def plan667 : Plan :=
  (.cut 1 (.e1 [(122, 145), (123, 283), (164, 133), (165, 211), (170, 189), (172, 189), (177, 211), (178, 133), (219, 283), (220, 145)] [(114, 343), (121, 306), (122, 171), (163, 261), (164, 211), (170, 170), (172, 170), (178, 211), (179, 261), (220, 171), (221, 306), (228, 343)]) (.e1 [(122, 145), (123, 259), (164, 166), (165, 193), (170, 165), (172, 165), (177, 193), (178, 166), (219, 259), (220, 145)] [(114, 328), (121, 325), (122, 172), (163, 242), (164, 186), (170, 205), (172, 205), (178, 186), (179, 242), (220, 172), (221, 325), (228, 328)]))

theorem root667 : rootCheck plan667 ![2, 2] ![1, 2, 3] = true := by decide +kernel

def plan668_0 : Plan :=
  (.cut 4 (.cut 0 (.e1 [(122, 128), (123, 260), (130, 247), (164, 134), (170, 228), (172, 228), (178, 134), (212, 247), (213, 294), (219, 260), (220, 128)] [(115, 333), (121, 228), (122, 238), (164, 211), (165, 243), (170, 157), (172, 157), (177, 243), (178, 211), (220, 238), (221, 228), (227, 333)]) (.cut 2 (.e1 [(122, 154), (123, 246), (129, 318), (130, 227), (163, 293), (164, 129), (170, 220), (172, 220), (178, 129), (179, 293), (212, 227), (213, 318), (219, 246), (220, 154)] [(115, 322), (121, 205), (122, 220), (164, 223), (165, 249), (170, 179), (172, 179), (177, 249), (178, 223), (214, 493), (220, 220), (221, 205), (227, 322)]) (.cut 1 (.redFull 178) (.e1 [(115, 564), (122, 157), (123, 258), (129, 296), (130, 210), (163, 290), (164, 145), (170, 204), (172, 204), (178, 145), (179, 290), (212, 210), (213, 296), (219, 258), (220, 157), (227, 564)] [(114, 543), (115, 284), (121, 215), (122, 224), (128, 522), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (214, 522), (220, 224), (221, 215), (227, 284), (228, 543)])))) (.e1 [(122, 151), (123, 218), (129, 296), (130, 246), (163, 350), (164, 139), (170, 201), (172, 201), (178, 139), (179, 350), (212, 246), (213, 296), (219, 218), (220, 151)] [(115, 308), (121, 209), (122, 233), (164, 195), (165, 282), (170, 180), (172, 180), (177, 282), (178, 195), (220, 233), (221, 209), (227, 308)]))

theorem plan668_0_ok : plan668_0.checkAt
    ((rootAddress ![2, 2] ![1, 3, 0]).child false)
    (childBox (rootBox ![2, 2] ![1, 3, 0]) 1 false) = true := by decide +kernel

def plan668_1 : Plan :=
  (.cut 4 (.cut 2 (.cut 0 (.e1 [(122, 131), (123, 237), (129, 335), (130, 224), (163, 285), (164, 161), (170, 213), (172, 213), (178, 161), (179, 285), (212, 224), (213, 335), (219, 237), (220, 131)] [(115, 321), (121, 227), (122, 243), (164, 195), (165, 221), (170, 189), (172, 189), (177, 221), (178, 195), (214, 472), (220, 243), (221, 227), (227, 321)]) (.cut 4 (.cut 1 (.cut 3 (.e1 [(122, 157), (123, 246), (129, 341), (130, 207), (163, 260), (164, 154), (170, 202), (172, 202), (178, 154), (179, 260), (212, 207), (213, 341), (219, 246), (220, 157)] [(115, 298), (121, 216), (122, 219), (164, 215), (165, 224), (170, 209), (172, 209), (177, 224), (178, 215), (220, 219), (221, 216), (227, 298)]) (.e1 [(122, 157), (123, 236), (130, 200), (163, 271), (164, 154), (170, 210), (172, 210), (178, 154), (179, 271), (212, 200), (213, 341), (219, 236), (220, 157)] [(115, 299), (121, 207), (122, 229), (164, 215), (165, 224), (170, 209), (172, 209), (177, 224), (178, 215), (220, 229), (221, 207), (227, 299)])) (.cut 3 (.cut 2 (.e1 [(122, 157), (123, 238), (129, 370), (130, 204), (163, 244), (164, 169), (170, 193), (172, 193), (178, 169), (179, 244), (212, 204), (213, 370), (219, 238), (220, 157)] [(115, 297), (121, 222), (122, 218), (128, 431), (164, 205), (165, 215), (170, 228), (172, 228), (177, 215), (178, 205), (214, 431), (220, 218), (221, 222), (227, 297)]) (.cut 4 (.cut 0 (.e1 [(122, 145), (123, 248), (130, 209), (163, 252), (164, 171), (170, 196), (172, 196), (178, 171), (179, 252), (212, 209), (213, 350), (219, 248), (220, 145)] [(115, 298), (121, 232), (122, 225), (164, 202), (165, 212), (170, 215), (172, 215), (177, 212), (178, 202), (220, 225), (221, 232), (227, 298)]) (.e1 [(115, 557), (122, 158), (123, 242), (129, 356), (130, 199), (163, 250), (164, 170), (170, 193), (172, 193), (178, 170), (179, 250), (212, 199), (213, 356), (219, 242), (220, 158), (227, 557)] [(114, 603), (115, 287), (121, 221), (122, 221), (128, 446), (164, 208), (165, 216), (170, 227), (172, 227), (177, 216), (178, 208), (214, 446), (220, 221), (221, 221), (227, 287), (228, 603)])) (.e1 [(122, 157), (123, 231), (129, 355), (130, 204), (163, 262), (164, 172), (170, 187), (172, 187), (178, 172), (179, 262), (212, 204), (213, 355), (219, 231), (220, 157)] [(115, 286), (121, 221), (122, 224), (128, 448), (164, 198), (165, 223), (170, 228), (172, 228), (177, 223), (178, 198), (214, 448), (220, 224), (221, 221), (227, 286)]))) (.cut 2 (.e1 [(122, 157), (123, 228), (129, 377), (130, 201), (163, 249), (164, 168), (170, 201), (172, 201), (178, 168), (179, 249), (212, 201), (213, 377), (219, 228), (220, 157)] [(115, 304), (121, 213), (122, 225), (128, 423), (164, 205), (165, 215), (170, 228), (172, 228), (177, 215), (178, 205), (214, 423), (220, 225), (221, 213), (227, 304)]) (.e1 [(122, 157), (123, 228), (129, 362), (130, 193), (163, 260), (164, 171), (170, 201), (172, 201), (178, 171), (179, 260), (212, 193), (213, 362), (219, 228), (220, 157)] [(115, 292), (121, 211), (122, 232), (128, 439), (164, 205), (165, 215), (170, 228), (172, 228), (177, 215), (178, 205), (214, 439), (220, 232), (221, 211), (227, 292)])))) (.cut 1 (.e1 [(122, 154), (123, 222), (129, 341), (130, 226), (163, 292), (164, 151), (170, 195), (172, 195), (178, 151), (179, 292), (212, 226), (213, 341), (219, 222), (220, 154)] [(115, 308), (121, 212), (122, 224), (128, 464), (164, 196), (165, 248), (170, 203), (172, 203), (177, 248), (178, 196), (214, 464), (220, 224), (221, 212), (227, 308)]) (.cut 3 (.e1 [(122, 157), (123, 221), (130, 219), (163, 272), (164, 171), (170, 177), (172, 177), (178, 171), (179, 272), (212, 219), (213, 358), (219, 221), (220, 157)] [(115, 290), (121, 223), (122, 220), (164, 187), (165, 237), (170, 228), (172, 228), (177, 237), (178, 187), (220, 220), (221, 223), (227, 290)]) (.e1 [(122, 157), (123, 211), (130, 212), (163, 283), (164, 171), (170, 185), (172, 185), (178, 171), (179, 283), (212, 212), (213, 358), (219, 211), (220, 157)] [(115, 292), (121, 214), (122, 230), (164, 187), (165, 237), (170, 228), (172, 228), (177, 237), (178, 187), (220, 230), (221, 214), (227, 292)]))))) (.cut 0 (.cut 4 (.e1 [(122, 134), (123, 255), (130, 206), (164, 173), (170, 206), (172, 206), (178, 173), (179, 279), (212, 206), (213, 312), (219, 255), (220, 134)] [(115, 289), (121, 235), (122, 246), (164, 201), (165, 210), (170, 197), (172, 197), (177, 210), (178, 201), (220, 246), (221, 235), (227, 289)]) (.e1 [(122, 128), (123, 229), (130, 232), (164, 171), (170, 197), (172, 197), (178, 171), (179, 312), (212, 232), (213, 315), (219, 229), (220, 128)] [(115, 304), (121, 235), (122, 250), (164, 180), (165, 234), (170, 191), (172, 191), (177, 234), (178, 180), (220, 250), (221, 235), (227, 304)])) (.cut 4 (.cut 1 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 255), (129, 302), (130, 211), (163, 288), (164, 157), (170, 204), (172, 204), (178, 157), (179, 288), (212, 211), (213, 302), (219, 255), (220, 145)] [(115, 287), (121, 225), (122, 234), (164, 210), (165, 228), (170, 192), (172, 192), (177, 228), (178, 210), (220, 234), (221, 225), (227, 287)]) (.cut 2 (.e1 [(122, 158), (123, 248), (129, 324), (130, 203), (163, 272), (164, 156), (170, 198), (172, 198), (178, 156), (179, 272), (212, 203), (213, 324), (219, 248), (220, 158)] [(115, 285), (121, 215), (122, 223), (128, 484), (164, 214), (165, 228), (170, 208), (172, 208), (177, 228), (178, 214), (214, 484), (220, 223), (221, 215), (227, 285)]) (.cut 1 (.e1 [(122, 160), (123, 251), (129, 306), (130, 204), (163, 284), (164, 153), (170, 197), (172, 197), (178, 153), (179, 284), (212, 204), (213, 306), (219, 251), (220, 160)] [(115, 277), (121, 215), (122, 225), (164, 216), (165, 235), (170, 203), (172, 203), (177, 235), (178, 216), (220, 225), (221, 215), (227, 277)]) (.e1 [(81, 694), (115, 585), (122, 160), (123, 246), (129, 315), (130, 199), (163, 280), (164, 162), (170, 192), (172, 192), (178, 162), (179, 280), (212, 199), (213, 315), (219, 246), (220, 160), (227, 585), (261, 694)] [(114, 551), (115, 272), (116, 610), (121, 217), (122, 227), (128, 496), (164, 211), (165, 230), (170, 212), (172, 212), (177, 230), (178, 211), (214, 496), (220, 227), (221, 217), (226, 610), (227, 272), (228, 551)])))) (.e1 [(122, 157), (123, 236), (129, 313), (130, 188), (163, 294), (164, 162), (170, 210), (172, 210), (178, 162), (179, 294), (212, 188), (213, 313), (219, 236), (220, 157)] [(115, 276), (121, 204), (122, 245), (128, 499), (164, 215), (165, 224), (170, 209), (172, 209), (177, 224), (178, 215), (214, 499), (220, 245), (221, 204), (227, 276)])) (.cut 3 (.cut 0 (.e1 [(122, 147), (123, 243), (129, 325), (130, 198), (163, 275), (164, 175), (170, 196), (172, 196), (178, 175), (179, 275), (212, 198), (213, 325), (219, 243), (220, 147)] [(115, 279), (121, 225), (122, 239), (164, 201), (165, 216), (170, 214), (172, 214), (177, 216), (178, 201), (220, 239), (221, 225), (227, 279)]) (.cut 4 (.cut 2 (.cut 1 (.e1 [(122, 160), (123, 246), (129, 337), (130, 197), (163, 260), (164, 166), (170, 192), (172, 192), (178, 166), (179, 260), (212, 197), (213, 337), (219, 246), (220, 160)] [(114, 584), (115, 279), (121, 219), (122, 222), (128, 467), (164, 211), (165, 221), (170, 222), (172, 222), (177, 221), (178, 211), (214, 467), (220, 222), (221, 219), (227, 279), (228, 584)]) (.redProjected 0 1)) (.cut 1 (.e1 [(81, 685), (115, 595), (122, 158), (123, 250), (129, 322), (130, 191), (131, 699), (137, 731), (163, 269), (164, 172), (170, 192), (172, 192), (178, 172), (179, 269), (205, 731), (211, 699), (212, 191), (213, 322), (219, 250), (220, 158), (227, 595), (261, 685)] [(114, 568), (115, 267), (116, 601), (121, 221), (122, 230), (128, 487), (164, 211), (165, 218), (170, 221), (172, 221), (177, 218), (178, 211), (214, 487), (220, 230), (221, 221), (226, 601), (227, 267), (228, 568)]) (.redProjected 0 1))) (.cut 2 (.e1 [(122, 158), (123, 233), (129, 341), (130, 201), (163, 270), (164, 173), (170, 184), (172, 184), (178, 173), (179, 270), (212, 201), (213, 341), (219, 233), (220, 158)] [(115, 276), (121, 221), (122, 226), (128, 464), (164, 198), (165, 226), (170, 227), (172, 227), (177, 226), (178, 198), (214, 464), (220, 226), (221, 221), (227, 276)]) (.cut 1 (.e1 [(122, 160), (123, 238), (129, 323), (130, 200), (163, 281), (164, 170), (170, 184), (172, 184), (178, 170), (179, 281), (212, 200), (213, 323), (219, 238), (220, 160)] [(114, 549), (115, 269), (121, 220), (122, 228), (128, 485), (164, 201), (165, 231), (170, 222), (172, 222), (177, 231), (178, 201), (214, 485), (220, 228), (221, 220), (226, 624), (227, 269), (228, 549)]) (.redProjected 0 1))))) (.cut 0 (.e1 [(122, 145), (123, 224), (130, 192), (163, 294), (164, 176), (170, 207), (172, 207), (178, 176), (179, 294), (212, 192), (213, 330), (219, 224), (220, 145)] [(115, 285), (121, 212), (122, 256), (164, 197), (165, 217), (170, 215), (172, 215), (177, 217), (178, 197), (220, 256), (221, 212), (227, 285)]) (.e1 [(115, 581), (121, 752), (122, 158), (123, 224), (129, 339), (130, 185), (131, 689), (163, 283), (164, 174), (165, 722), (170, 201), (172, 201), (177, 722), (178, 174), (179, 283), (211, 689), (212, 185), (213, 339), (219, 224), (220, 158), (221, 752), (227, 581), (261, 659)] [(114, 545), (115, 276), (116, 655), (121, 205), (122, 245), (128, 466), (129, 814), (164, 204), (165, 219), (170, 227), (172, 227), (177, 219), (178, 204), (213, 814), (214, 466), (220, 245), (221, 205), (226, 655), (227, 276), (228, 545)])))) (.cut 1 (.cut 3 (.e1 [(122, 157), (123, 231), (129, 313), (130, 212), (163, 301), (164, 162), (170, 186), (172, 186), (178, 162), (179, 301), (212, 212), (213, 313), (219, 231), (220, 157)] [(115, 277), (121, 217), (122, 230), (164, 198), (165, 245), (170, 209), (172, 209), (177, 245), (178, 198), (220, 230), (221, 217), (227, 277)]) (.e1 [(122, 160), (123, 223), (130, 201), (163, 309), (164, 165), (170, 191), (172, 191), (178, 165), (179, 309), (212, 201), (213, 313), (219, 223), (220, 160)] [(115, 272), (121, 209), (122, 239), (164, 199), (165, 242), (170, 215), (172, 215), (177, 242), (178, 199), (220, 239), (221, 209), (227, 272)])) (.cut 3 (.e1 [(115, 597), (122, 157), (123, 221), (129, 330), (130, 205), (163, 294), (164, 179), (170, 177), (172, 177), (178, 179), (179, 294), (212, 205), (213, 330), (219, 221), (220, 157), (227, 597)] [(115, 269), (121, 221), (122, 234), (128, 478), (164, 187), (165, 237), (170, 228), (172, 228), (177, 237), (178, 187), (214, 478), (220, 234), (221, 221), (227, 269)]) (.e1 [(122, 157), (123, 211), (129, 330), (130, 199), (163, 306), (164, 179), (170, 185), (172, 185), (178, 179), (179, 306), (212, 199), (213, 330), (219, 211), (220, 157)] [(115, 271), (121, 211), (122, 245), (164, 187), (165, 237), (170, 228), (172, 228), (177, 237), (178, 187), (220, 245), (221, 211), (227, 271)])))))) (.cut 2 (.e1 [(122, 145), (123, 202), (129, 345), (130, 257), (163, 321), (164, 162), (170, 176), (172, 176), (178, 162), (179, 321), (212, 257), (213, 345), (219, 202), (220, 145)] [(115, 316), (121, 223), (122, 228), (164, 168), (165, 272), (170, 205), (172, 205), (177, 272), (178, 168), (214, 467), (220, 228), (221, 223), (227, 316)]) (.cut 0 (.e1 [(122, 134), (123, 213), (130, 265), (164, 163), (170, 180), (172, 180), (178, 163), (212, 265), (219, 213), (220, 134)] [(115, 309), (121, 235), (122, 239), (164, 167), (165, 274), (170, 188), (172, 188), (177, 274), (178, 167), (220, 239), (221, 235), (227, 309)]) (.e1 [(115, 579), (122, 154), (123, 197), (129, 323), (130, 239), (163, 340), (164, 169), (170, 171), (172, 171), (178, 169), (179, 340), (212, 239), (213, 323), (219, 197), (220, 154), (227, 579)] [(114, 475), (115, 288), (121, 218), (122, 235), (128, 492), (164, 170), (165, 276), (170, 215), (172, 215), (177, 276), (178, 170), (214, 492), (220, 235), (221, 218), (227, 288), (228, 475)]))))

theorem plan668_1_ok : plan668_1.checkAt
    ((rootAddress ![2, 2] ![1, 3, 0]).child true)
    (childBox (rootBox ![2, 2] ![1, 3, 0]) 1 true) = true := by decide +kernel

def plan668 : Plan := .cut 1 plan668_0 plan668_1

theorem plan668_ok : plan668.checkAt
    (rootAddress ![2, 2] ![1, 3, 0])
    (rootBox ![2, 2] ![1, 3, 0]) = true :=
  checkAt_cut 1 plan668_0 plan668_1
    (rootAddress ![2, 2] ![1, 3, 0])
    (rootBox ![2, 2] ![1, 3, 0])
    (by decide +kernel) plan668_0_ok plan668_1_ok

theorem root668 : rootCheck plan668 ![2, 2] ![1, 3, 0] = true := plan668_ok

def plan669 : Plan :=
  (.e1 [(122, 151), (123, 194), (129, 318), (130, 341), (164, 143), (170, 159), (172, 159), (178, 143), (212, 341), (213, 318), (219, 194), (220, 151)] [(115, 337), (121, 230), (122, 208), (164, 159), (165, 373), (170, 189), (172, 189), (177, 373), (178, 159), (220, 208), (221, 230), (227, 337), (228, 430)])

theorem root669 : rootCheck plan669 ![2, 2] ![1, 3, 1] = true := by decide +kernel

def plan670 : Plan :=
  (.e1 [(122, 151), (123, 194), (129, 318), (164, 143), (165, 320), (170, 159), (172, 159), (177, 320), (178, 143), (213, 318), (219, 194), (220, 151)] [(114, 365), (121, 246), (122, 197), (164, 159), (170, 189), (172, 189), (178, 159), (179, 373), (220, 197), (221, 246), (228, 365)])

theorem root670 : rootCheck plan670 ![2, 2] ![1, 3, 2] = true := by decide +kernel

def plan671 : Plan :=
  (.cut 1 (.cut 0 (.e1 [(122, 128), (123, 247), (164, 134), (165, 246), (170, 215), (172, 215), (177, 246), (178, 134), (213, 294), (219, 247), (220, 128)] [(114, 348), (121, 271), (122, 203), (163, 262), (164, 198), (170, 157), (172, 157), (178, 198), (179, 262), (220, 203), (221, 271), (228, 348)]) (.cut 4 (.e1 [(122, 160), (123, 208), (164, 145), (165, 222), (170, 199), (172, 199), (177, 222), (178, 145), (219, 208), (220, 160)] [(121, 250), (122, 192), (163, 277), (164, 196), (170, 194), (172, 194), (178, 196), (179, 277), (220, 192), (221, 250), (228, 298)]) (.e1 [(122, 157), (123, 227), (129, 299), (164, 139), (165, 212), (170, 209), (172, 209), (177, 212), (178, 139), (213, 299), (219, 227), (220, 157), (226, 354)] [(114, 305), (121, 255), (122, 187), (163, 262), (164, 209), (170, 186), (172, 186), (178, 209), (179, 262), (220, 187), (221, 255), (228, 305)]))) (.cut 4 (.e1 [(122, 151), (123, 194), (129, 329), (164, 172), (165, 223), (170, 177), (172, 177), (177, 223), (178, 172), (213, 329), (219, 194), (220, 151), (226, 362)] [(114, 300), (121, 265), (122, 198), (163, 267), (164, 169), (170, 217), (172, 217), (178, 169), (179, 267), (220, 198), (221, 265), (228, 300)]) (.cut 0 (.e1 [(116, 332), (122, 131), (123, 237), (164, 165), (165, 202), (170, 213), (172, 213), (177, 202), (178, 165), (219, 237), (220, 131), (226, 332)] [(114, 315), (121, 283), (122, 204), (163, 221), (164, 195), (170, 189), (172, 189), (178, 195), (179, 221), (220, 204), (221, 283), (228, 315)]) (.cut 3 (.e1 [(122, 151), (123, 235), (164, 169), (165, 186), (170, 183), (172, 183), (177, 186), (178, 169), (219, 235), (220, 151), (226, 343)] [(114, 308), (121, 290), (122, 180), (163, 231), (164, 192), (170, 217), (172, 217), (178, 192), (179, 231), (220, 180), (221, 290), (228, 308)]) (.cut 1 (.e1 [(116, 321), (122, 154), (123, 224), (129, 323), (164, 155), (165, 193), (170, 211), (172, 211), (177, 193), (178, 155), (213, 323), (219, 224), (220, 154), (226, 321)] [(114, 297), (121, 260), (122, 191), (163, 235), (164, 207), (170, 203), (172, 203), (178, 207), (179, 235), (220, 191), (221, 260), (228, 297)]) (.e1 [(115, 548), (116, 301), (117, 712), (122, 154), (123, 215), (129, 354), (164, 169), (165, 191), (170, 201), (172, 201), (177, 191), (178, 169), (213, 354), (219, 215), (220, 154), (225, 712), (226, 301), (227, 548)] [(113, 712), (114, 299), (115, 523), (121, 258), (122, 194), (129, 449), (163, 226), (164, 196), (170, 222), (172, 222), (178, 196), (179, 226), (212, 732), (213, 449), (220, 194), (221, 258), (227, 523), (228, 299), (229, 712)]))))))

theorem root671 : rootCheck plan671 ![2, 2] ![1, 3, 3] = true := by decide +kernel

def plan672 : Plan :=
  (.cut 1 (.e1 [(122, 157), (129, 246), (130, 254), (163, 236), (164, 166), (170, 161), (172, 161), (178, 166), (179, 236), (212, 254), (213, 246), (220, 157)] [(115, 249), (121, 316), (122, 189), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (220, 189), (221, 316), (227, 249)]) (.cut 4 (.cut 0 (.e1 [(122, 134), (129, 271), (130, 259), (163, 227), (164, 190), (170, 161), (172, 161), (178, 190), (179, 227), (212, 259), (213, 271), (220, 134)] [(115, 266), (122, 201), (164, 197), (165, 215), (170, 197), (172, 197), (177, 215), (178, 197), (220, 201), (227, 266)]) (.cut 4 (.e1 [(122, 151), (123, 395), (129, 270), (130, 265), (163, 213), (164, 183), (170, 150), (172, 150), (178, 183), (179, 213), (212, 265), (213, 270), (219, 395), (220, 151)] [(115, 259), (116, 413), (121, 349), (122, 182), (164, 206), (165, 225), (170, 207), (172, 207), (177, 225), (178, 206), (220, 182), (221, 349), (226, 413), (227, 259)]) (.e1 [(122, 145), (129, 279), (130, 298), (163, 229), (164, 177), (170, 140), (172, 140), (178, 177), (179, 229), (212, 298), (213, 279), (220, 145)] [(115, 269), (122, 178), (164, 189), (165, 244), (170, 201), (172, 201), (177, 244), (178, 189), (220, 178), (221, 362), (227, 269)]))) (.e1 [(122, 139), (129, 277), (163, 255), (164, 176), (170, 132), (172, 132), (178, 176), (179, 255), (213, 277), (220, 139)] [(115, 269), (122, 181), (164, 174), (165, 265), (170, 194), (172, 194), (177, 265), (178, 174), (220, 181), (227, 269)])))

theorem root672 : rootCheck plan672 ![2, 2] ![2, 0, 0] = true := by decide +kernel

def plan673 : Plan :=
  (.e1 [(122, 128), (129, 254), (164, 158), (170, 128), (172, 128), (178, 158), (213, 254), (220, 128)] [(115, 279), (122, 187), (164, 159), (170, 165), (172, 165), (178, 159), (220, 187), (227, 279)])

theorem root673 : rootCheck plan673 ![2, 2] ![2, 0, 1] = true := by decide +kernel

def plan674 : Plan :=
  (.e1 [(122, 128), (129, 254), (164, 158), (170, 128), (172, 128), (178, 158), (213, 254), (220, 128)] [(122, 185), (164, 159), (170, 165), (172, 165), (178, 159), (220, 185), (227, 284)])

theorem root674 : rootCheck plan674 ![2, 2] ![2, 0, 2] = true := by decide +kernel

def plan675 : Plan :=
  (.cut 1 (.e1 [(122, 151), (129, 245), (164, 158), (165, 217), (170, 158), (172, 158), (177, 217), (178, 158), (213, 245), (214, 321), (220, 151)] [(115, 278), (122, 173), (163, 250), (164, 216), (170, 180), (172, 180), (178, 216), (179, 250), (220, 173), (227, 278)]) (.e1 [(122, 139), (128, 336), (129, 277), (164, 176), (165, 202), (170, 152), (172, 152), (177, 202), (178, 176), (213, 277), (214, 336), (220, 139)] [(114, 378), (115, 299), (122, 174), (123, 421), (163, 231), (164, 195), (170, 194), (172, 194), (178, 195), (179, 231), (219, 421), (220, 174), (227, 299), (228, 378)]))

theorem root675 : rootCheck plan675 ![2, 2] ![2, 0, 3] = true := by decide +kernel

def plan676 : Plan :=
  (.cut 1 (.cut 4 (.cut 0 (.e1 [(122, 136), (129, 238), (130, 231), (164, 164), (170, 193), (172, 193), (178, 164), (179, 280), (212, 231), (213, 238), (220, 136)] [(115, 258), (122, 229), (164, 221), (165, 229), (170, 170), (172, 170), (177, 229), (178, 221), (220, 229), (221, 278), (227, 258)]) (.cut 1 (.e1 [(122, 160), (129, 233), (130, 224), (163, 278), (164, 152), (170, 184), (172, 184), (178, 152), (179, 278), (212, 224), (213, 233), (220, 160)] [(115, 244), (121, 262), (122, 212), (164, 238), (165, 246), (170, 178), (172, 178), (177, 246), (178, 238), (220, 212), (221, 262), (227, 244)]) (.cut 3 (.e1 [(122, 160), (129, 250), (130, 227), (163, 249), (164, 169), (170, 167), (172, 167), (178, 169), (179, 249), (212, 227), (213, 250), (220, 160)] [(115, 240), (121, 286), (122, 201), (164, 225), (165, 234), (170, 196), (172, 196), (177, 234), (178, 225), (220, 201), (221, 286), (227, 240)]) (.e1 [(122, 160), (123, 323), (129, 250), (130, 211), (163, 270), (164, 169), (170, 174), (172, 174), (178, 169), (179, 270), (212, 211), (213, 250), (219, 323), (220, 160)] [(115, 237), (116, 489), (121, 264), (122, 215), (164, 225), (165, 234), (170, 196), (172, 196), (177, 234), (178, 225), (220, 215), (221, 264), (226, 489), (227, 237)])))) (.e1 [(122, 151), (129, 245), (130, 272), (164, 158), (170, 153), (172, 153), (178, 158), (212, 272), (213, 245), (219, 310), (220, 151)] [(115, 250), (121, 291), (122, 201), (164, 195), (165, 282), (170, 180), (172, 180), (177, 282), (178, 195), (220, 201), (221, 291), (227, 250)])) (.cut 4 (.cut 1 (.cut 0 (.e1 [(122, 134), (129, 259), (130, 234), (163, 266), (164, 177), (170, 179), (172, 179), (178, 177), (179, 266), (212, 234), (213, 259), (220, 134)] [(115, 260), (121, 290), (122, 223), (164, 205), (165, 222), (170, 184), (172, 184), (177, 222), (178, 205), (220, 223), (221, 290), (227, 260)]) (.cut 3 (.e1 [(122, 157), (123, 343), (129, 269), (130, 231), (163, 240), (164, 180), (170, 156), (172, 156), (178, 180), (179, 240), (212, 231), (213, 269), (219, 343), (220, 157)] [(115, 243), (121, 298), (122, 196), (164, 210), (165, 229), (170, 209), (172, 209), (177, 229), (178, 210), (220, 196), (221, 298), (227, 243)]) (.cut 2 (.e1 [(122, 160), (129, 287), (130, 216), (163, 243), (164, 175), (170, 165), (172, 165), (178, 175), (179, 243), (212, 216), (213, 287), (219, 313), (220, 160)] [(115, 249), (121, 269), (122, 201), (164, 214), (165, 224), (170, 215), (172, 215), (177, 224), (178, 214), (220, 201), (221, 269), (227, 249)]) (.cut 4 (.e1 [(122, 157), (123, 318), (129, 263), (130, 207), (163, 260), (164, 183), (170, 167), (172, 167), (178, 183), (179, 260), (212, 207), (213, 263), (219, 318), (220, 157), (221, 585)] [(114, 585), (115, 234), (116, 493), (121, 272), (122, 216), (128, 580), (164, 215), (165, 224), (170, 209), (172, 209), (177, 224), (178, 215), (214, 580), (220, 216), (221, 272), (226, 493), (227, 234), (228, 585)]) (.e1 [(122, 157), (123, 309), (129, 264), (130, 240), (163, 276), (164, 175), (170, 148), (172, 148), (178, 175), (179, 276), (212, 240), (213, 264), (219, 309), (220, 157)] [(115, 239), (121, 286), (122, 201), (164, 197), (165, 253), (170, 204), (172, 204), (177, 253), (178, 197), (220, 201), (221, 286), (227, 239)]))))) (.cut 0 (.e1 [(122, 134), (129, 276), (130, 225), (163, 257), (164, 194), (170, 169), (172, 169), (178, 194), (179, 257), (212, 225), (213, 276), (220, 134)] [(115, 254), (121, 296), (122, 224), (164, 195), (165, 213), (170, 201), (172, 201), (177, 213), (178, 195), (220, 224), (221, 296), (227, 254)]) (.cut 3 (.e1 [(122, 160), (129, 270), (130, 216), (163, 238), (164, 189), (170, 155), (172, 155), (178, 189), (179, 238), (212, 216), (213, 270), (220, 160)] [(115, 233), (121, 293), (122, 201), (164, 212), (165, 222), (170, 219), (172, 219), (177, 222), (178, 212), (220, 201), (221, 293), (227, 233)]) (.cut 4 (.cut 2 (.e1 [(122, 157), (123, 310), (129, 304), (130, 214), (163, 232), (164, 188), (170, 158), (172, 158), (178, 188), (179, 232), (212, 214), (213, 304), (219, 310), (220, 157)] [(115, 249), (121, 279), (122, 200), (164, 205), (165, 215), (170, 228), (172, 228), (177, 215), (178, 205), (220, 200), (221, 279), (227, 249)]) (.e1 [(122, 160), (123, 313), (129, 268), (130, 196), (163, 259), (164, 191), (170, 165), (172, 165), (178, 191), (179, 259), (212, 196), (213, 268), (219, 313), (220, 160)] [(115, 227), (121, 268), (122, 219), (164, 214), (165, 219), (170, 219), (172, 219), (177, 219), (178, 214), (220, 219), (221, 268), (226, 498), (227, 227)])) (.e1 [(122, 157), (129, 277), (130, 226), (163, 270), (164, 188), (170, 146), (172, 146), (178, 188), (179, 270), (212, 226), (213, 277), (220, 157)] [(115, 234), (121, 282), (122, 207), (164, 192), (165, 241), (170, 218), (172, 218), (177, 241), (178, 192), (220, 207), (221, 282), (227, 234)]))))) (.e1 [(122, 157), (129, 255), (130, 250), (164, 174), (170, 144), (172, 144), (178, 174), (212, 250), (213, 255), (219, 295), (220, 157)] [(115, 235), (121, 286), (122, 205), (164, 189), (165, 272), (170, 200), (172, 200), (177, 272), (178, 189), (220, 205), (221, 286), (227, 235)])))

theorem root676 : rootCheck plan676 ![2, 2] ![2, 1, 0] = true := by decide +kernel

def plan677 : Plan :=
  (.e1 [(122, 139), (129, 260), (164, 160), (170, 131), (172, 131), (178, 160), (213, 260), (219, 298), (220, 139)] [(115, 269), (121, 329), (122, 190), (164, 164), (165, 335), (170, 177), (172, 177), (177, 335), (178, 164), (220, 190), (221, 329), (227, 269)])

theorem root677 : rootCheck plan677 ![2, 2] ![2, 1, 1] = true := by decide +kernel

def plan678 : Plan :=
  (.e1 [(122, 139), (129, 260), (164, 160), (170, 131), (172, 131), (177, 289), (178, 160), (213, 260), (220, 139)] [(115, 295), (122, 178), (164, 164), (170, 177), (172, 177), (178, 164), (179, 335), (220, 178), (227, 295)])

theorem root678 : rootCheck plan678 ![2, 2] ![2, 1, 2] = true := by decide +kernel

def plan679 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 328), (129, 245), (164, 158), (165, 194), (170, 171), (172, 171), (177, 194), (178, 158), (213, 245), (219, 328), (220, 151)] [(115, 321), (122, 171), (163, 250), (164, 216), (170, 180), (172, 180), (178, 216), (179, 250), (220, 171), (227, 321)]) (.e1 [(122, 139), (123, 327), (129, 277), (164, 176), (165, 190), (170, 160), (172, 160), (177, 190), (178, 176), (213, 277), (219, 327), (220, 139)] [(115, 330), (122, 173), (163, 231), (164, 195), (170, 194), (172, 194), (178, 195), (179, 231), (220, 173), (227, 330), (228, 337)]))

theorem root679 : rootCheck plan679 ![2, 2] ![2, 1, 3] = true := by decide +kernel

def plan680_0 : Plan :=
  (.cut 4 (.cut 0 (.e1 [(122, 134), (129, 238), (130, 222), (164, 156), (170, 212), (172, 212), (178, 156), (179, 320), (212, 222), (213, 238), (219, 294), (220, 134)] [(115, 266), (121, 249), (122, 251), (164, 220), (165, 236), (170, 163), (172, 163), (177, 236), (178, 220), (220, 251), (221, 249), (227, 266)]) (.cut 1 (.e1 [(122, 157), (123, 292), (129, 236), (130, 212), (163, 319), (164, 147), (170, 203), (172, 203), (178, 147), (179, 319), (212, 212), (213, 236), (219, 292), (220, 157)] [(114, 500), (115, 251), (116, 539), (121, 232), (122, 235), (164, 235), (165, 251), (170, 173), (172, 173), (177, 251), (178, 235), (220, 235), (221, 232), (226, 539), (227, 251), (228, 500)]) (.cut 2 (.cut 3 (.e1 [(122, 160), (123, 297), (129, 271), (130, 209), (163, 272), (164, 158), (170, 184), (172, 184), (178, 158), (179, 272), (212, 209), (213, 271), (219, 297), (220, 160)] [(115, 254), (121, 243), (122, 215), (164, 225), (165, 234), (170, 196), (172, 196), (177, 234), (178, 225), (220, 215), (221, 243), (227, 254)]) (.cut 4 (.e1 [(122, 157), (123, 278), (129, 270), (130, 203), (163, 292), (164, 154), (170, 198), (172, 198), (178, 154), (179, 292), (212, 203), (213, 270), (219, 278), (220, 157)] [(115, 260), (121, 227), (122, 229), (164, 226), (165, 235), (170, 191), (172, 191), (177, 235), (178, 226), (220, 229), (221, 227), (227, 260), (228, 536)]) (.e1 [(122, 160), (123, 260), (129, 271), (130, 212), (164, 158), (170, 183), (172, 183), (178, 158), (179, 311), (212, 212), (213, 271), (219, 260), (220, 160)] [(115, 255), (121, 229), (122, 227), (164, 211), (165, 252), (170, 196), (172, 196), (177, 252), (178, 211), (220, 227), (221, 229), (227, 255)]))) (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 145), (123, 308), (129, 247), (130, 222), (163, 290), (164, 162), (170, 189), (172, 189), (178, 162), (179, 290), (212, 222), (213, 247), (219, 308), (220, 145)] [(115, 254), (121, 259), (122, 228), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 228), (221, 259), (227, 254)]) (.e1 [(122, 160), (123, 301), (129, 248), (130, 201), (163, 291), (164, 167), (170, 184), (172, 184), (178, 167), (179, 291), (212, 201), (213, 248), (219, 301), (220, 160)] [(114, 533), (115, 236), (116, 518), (121, 245), (122, 229), (128, 603), (164, 227), (165, 236), (170, 194), (172, 194), (177, 236), (178, 227), (214, 603), (220, 229), (221, 245), (226, 518), (227, 236), (228, 533)])) (.e1 [(122, 160), (123, 284), (129, 247), (130, 212), (164, 170), (170, 171), (172, 171), (178, 170), (179, 311), (212, 212), (213, 247), (219, 284), (220, 160)] [(115, 233), (121, 250), (122, 228), (164, 211), (165, 252), (170, 196), (172, 196), (177, 252), (178, 211), (220, 228), (221, 250), (227, 233)])) (.cut 4 (.cut 0 (.e1 [(122, 145), (123, 285), (129, 247), (130, 210), (163, 312), (164, 162), (170, 199), (172, 199), (178, 162), (179, 312), (212, 210), (213, 247), (219, 285), (220, 145)] [(115, 254), (121, 241), (122, 244), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 244), (221, 241), (227, 254)]) (.cut 1 (.e1 [(122, 158), (123, 283), (129, 243), (130, 200), (163, 316), (164, 158), (170, 198), (172, 198), (178, 158), (179, 316), (212, 200), (213, 243), (219, 283), (220, 158)] [(115, 243), (121, 230), (122, 241), (164, 229), (165, 243), (170, 184), (172, 184), (177, 243), (178, 229), (220, 241), (221, 230), (227, 243)]) (.cut 3 (.cut 4 (.e1 [(122, 160), (123, 286), (129, 250), (130, 190), (163, 303), (164, 169), (170, 192), (172, 192), (178, 169), (179, 303), (212, 190), (213, 250), (219, 286), (220, 160)] [(114, 515), (115, 235), (116, 539), (121, 233), (122, 241), (128, 598), (164, 227), (165, 232), (170, 196), (172, 196), (177, 232), (178, 227), (214, 598), (220, 241), (221, 233), (226, 539), (227, 235), (228, 515)]) (.e1 [(122, 160), (123, 279), (129, 250), (130, 199), (163, 311), (164, 169), (170, 184), (172, 184), (178, 169), (179, 311), (212, 199), (213, 250), (219, 279), (220, 160)] [(115, 236), (121, 237), (122, 238), (164, 219), (165, 241), (170, 196), (172, 196), (177, 241), (178, 219), (220, 238), (221, 237), (227, 236)])) (.cut 4 (.e1 [(122, 158), (123, 274), (129, 251), (130, 192), (163, 315), (164, 166), (170, 196), (172, 196), (178, 166), (179, 315), (212, 192), (213, 251), (219, 274), (220, 158)] [(114, 499), (115, 240), (116, 559), (121, 227), (122, 246), (164, 224), (165, 236), (170, 193), (172, 193), (177, 236), (178, 224), (220, 246), (221, 227), (226, 559), (227, 240), (228, 499)]) (.e1 [(122, 160), (123, 267), (129, 250), (130, 193), (163, 324), (164, 169), (170, 191), (172, 191), (178, 169), (179, 324), (212, 193), (213, 250), (219, 267), (220, 160)] [(115, 237), (121, 228), (122, 247), (164, 219), (165, 241), (170, 196), (172, 196), (177, 241), (178, 219), (220, 247), (221, 228), (227, 237)]))))) (.e1 [(122, 157), (123, 264), (129, 246), (130, 209), (163, 334), (164, 166), (170, 183), (172, 183), (178, 166), (179, 334), (212, 209), (213, 246), (219, 264), (220, 157)] [(114, 476), (115, 241), (121, 235), (122, 242), (164, 210), (165, 254), (170, 191), (172, 191), (177, 254), (178, 210), (220, 242), (221, 235), (226, 578), (227, 241), (228, 476)])))))) (.e1 [(122, 157), (123, 251), (129, 246), (130, 229), (163, 354), (164, 166), (170, 171), (172, 171), (178, 166), (179, 354), (212, 229), (213, 246), (219, 251), (220, 157)] [(115, 243), (121, 242), (122, 235), (164, 196), (165, 276), (170, 191), (172, 191), (177, 276), (178, 196), (220, 235), (221, 242), (227, 243)]))

theorem plan680_0_ok : plan680_0.checkAt
    ((rootAddress ![2, 2] ![2, 2, 0]).child false)
    (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 false) = true := by decide +kernel

def plan680_1 : Plan :=
  (.cut 1 (.e1 [(122, 131), (123, 283), (129, 261), (130, 222), (163, 303), (164, 172), (170, 194), (172, 194), (178, 172), (179, 303), (212, 222), (213, 261), (219, 283), (220, 131)] [(114, 528), (115, 266), (121, 258), (122, 246), (164, 201), (165, 227), (170, 179), (172, 179), (177, 227), (178, 201), (220, 246), (221, 258), (227, 266), (228, 528)]) (.e1 [(122, 131), (123, 273), (129, 278), (130, 213), (163, 294), (164, 189), (170, 184), (172, 184), (178, 189), (179, 294), (212, 213), (213, 278), (219, 273), (220, 131)] [(114, 538), (115, 260), (116, 566), (121, 262), (122, 248), (128, 559), (164, 191), (165, 218), (170, 196), (172, 196), (177, 218), (178, 191), (214, 559), (220, 248), (221, 262), (226, 566), (227, 260), (228, 538)]))

theorem plan680_1_ok : plan680_1.checkAt
    ((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 false) = true := by decide +kernel

def plan680_2 : Plan :=
  (.cut 1 (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 289), (129, 287), (130, 198), (163, 261), (164, 175), (170, 177), (172, 177), (178, 175), (179, 261), (212, 198), (213, 287), (219, 289), (220, 160)] [(115, 247), (121, 246), (122, 218), (128, 537), (164, 217), (165, 221), (170, 215), (172, 215), (177, 221), (178, 217), (214, 537), (220, 218), (221, 246), (227, 247)]) (.cut 0 (.e1 [(122, 148), (123, 271), (129, 282), (130, 199), (163, 286), (164, 170), (170, 194), (172, 194), (178, 170), (179, 286), (212, 199), (213, 282), (219, 271), (220, 148)] [(115, 260), (121, 235), (122, 237), (164, 213), (165, 222), (170, 199), (172, 199), (177, 222), (178, 213), (220, 237), (221, 235), (227, 260)]) (.cut 1 (.cut 2 (.e1 [(122, 160), (123, 271), (129, 292), (130, 200), (163, 276), (164, 161), (170, 190), (172, 190), (178, 161), (179, 276), (212, 200), (213, 292), (219, 271), (220, 160)] [(115, 261), (121, 228), (122, 223), (164, 219), (165, 229), (170, 205), (172, 205), (177, 229), (178, 219), (220, 223), (221, 228), (227, 261)]) (.cut 4 (.cut 3 (.e1 [(122, 161), (123, 280), (129, 279), (130, 192), (163, 278), (164, 168), (170, 187), (172, 187), (178, 168), (179, 278), (212, 192), (213, 279), (219, 280), (220, 161)] [(115, 247), (121, 232), (122, 227), (164, 223), (165, 225), (170, 208), (172, 208), (177, 225), (178, 223), (220, 227), (221, 232), (227, 247)]) (.e1 [(122, 160), (123, 270), (129, 279), (130, 190), (163, 289), (164, 166), (170, 193), (172, 193), (178, 166), (179, 289), (212, 190), (213, 279), (219, 270), (220, 160)] [(114, 536), (115, 250), (121, 225), (122, 235), (164, 222), (165, 226), (170, 205), (172, 205), (177, 226), (178, 222), (214, 548), (220, 235), (221, 225), (227, 250), (228, 536)])) (.e1 [(122, 160), (123, 265), (129, 279), (130, 200), (163, 294), (164, 166), (170, 184), (172, 184), (178, 166), (179, 294), (212, 200), (213, 279), (219, 265), (220, 160)] [(115, 250), (121, 230), (122, 230), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (220, 230), (221, 230), (227, 250)]))) (.cut 2 (.e1 [(122, 160), (123, 266), (129, 300), (130, 195), (163, 272), (164, 170), (170, 185), (172, 185), (178, 170), (179, 272), (212, 195), (213, 300), (219, 266), (220, 160)] [(114, 563), (115, 257), (121, 230), (122, 224), (128, 517), (164, 214), (165, 224), (170, 215), (172, 215), (177, 224), (178, 214), (214, 517), (220, 224), (221, 230), (226, 572), (227, 257), (228, 563)]) (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 277), (129, 287), (130, 191), (163, 272), (164, 175), (170, 182), (172, 182), (178, 175), (179, 272), (212, 191), (213, 287), (219, 277), (220, 160)] [(115, 246), (116, 553), (121, 236), (122, 227), (128, 536), (164, 217), (165, 221), (170, 215), (172, 215), (177, 221), (178, 217), (214, 536), (220, 227), (221, 236), (226, 553), (227, 246), (228, 561)]) (.cut 0 (.e1 [(122, 154), (123, 269), (129, 282), (130, 194), (163, 286), (164, 172), (170, 190), (172, 190), (178, 172), (179, 286), (212, 194), (213, 282), (219, 269), (220, 154)] [(115, 252), (121, 232), (122, 236), (164, 214), (165, 223), (170, 206), (172, 206), (177, 223), (178, 214), (220, 236), (221, 232), (227, 252)]) (.e1 [(81, 671), (115, 636), (121, 685), (122, 161), (123, 266), (129, 288), (130, 188), (131, 718), (163, 283), (164, 173), (170, 187), (172, 187), (178, 173), (179, 283), (211, 718), (212, 188), (213, 288), (219, 266), (220, 161), (221, 685), (227, 636), (261, 671)] [(114, 544), (115, 248), (116, 571), (121, 227), (122, 233), (128, 534), (164, 216), (165, 224), (170, 214), (172, 214), (177, 224), (178, 216), (214, 534), (220, 233), (221, 227), (226, 571), (227, 248), (228, 544)]))) (.e1 [(122, 160), (123, 260), (129, 287), (130, 196), (163, 290), (164, 175), (170, 179), (172, 179), (178, 175), (179, 290), (212, 196), (213, 287), (219, 260), (220, 160)] [(115, 247), (121, 231), (122, 231), (128, 536), (164, 207), (165, 232), (170, 215), (172, 215), (177, 232), (178, 207), (214, 536), (220, 231), (221, 231), (226, 582), (227, 247), (228, 533)])))))) (.cut 3 (.e1 [(122, 160), (123, 273), (129, 287), (130, 217), (164, 175), (170, 161), (172, 161), (178, 175), (179, 280), (212, 217), (213, 287), (219, 273), (220, 160)] [(115, 246), (121, 253), (122, 213), (164, 199), (165, 242), (170, 215), (172, 215), (177, 242), (178, 199), (220, 213), (221, 253), (227, 246)]) (.e1 [(122, 160), (123, 249), (129, 287), (130, 204), (163, 303), (164, 175), (170, 173), (172, 173), (178, 175), (179, 303), (212, 204), (213, 287), (219, 249), (220, 160)] [(115, 248), (121, 232), (122, 231), (164, 199), (165, 242), (170, 215), (172, 215), (177, 242), (178, 199), (220, 231), (221, 232), (227, 248)]))) (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 148), (123, 286), (129, 300), (130, 204), (163, 256), (164, 187), (170, 173), (172, 173), (178, 187), (179, 256), (212, 204), (213, 300), (219, 286), (220, 148)] [(115, 253), (121, 259), (122, 222), (164, 203), (165, 213), (170, 218), (172, 218), (177, 213), (178, 203), (220, 222), (221, 259), (227, 253)]) (.cut 1 (.cut 3 (.e1 [(122, 161), (123, 295), (129, 298), (130, 199), (163, 247), (164, 185), (170, 166), (172, 166), (178, 185), (179, 247), (212, 199), (213, 298), (219, 295), (220, 161)] [(115, 243), (121, 258), (122, 211), (164, 212), (165, 217), (170, 227), (172, 227), (177, 217), (178, 212), (220, 211), (221, 258), (227, 243)]) (.e1 [(115, 650), (122, 161), (123, 282), (129, 298), (130, 192), (163, 257), (164, 185), (170, 172), (172, 172), (178, 185), (179, 257), (212, 192), (213, 298), (219, 282), (220, 161), (227, 650)] [(115, 242), (116, 543), (121, 246), (122, 220), (128, 522), (164, 212), (165, 217), (170, 227), (172, 227), (177, 217), (178, 212), (214, 522), (220, 220), (221, 246), (226, 543), (227, 242)])) (.redProjected 0 1))) (.cut 0 (.e1 [(122, 147), (123, 265), (129, 300), (130, 198), (163, 275), (164, 184), (170, 183), (172, 183), (178, 184), (179, 275), (212, 198), (213, 300), (219, 265), (220, 147)] [(115, 257), (121, 242), (122, 236), (164, 201), (165, 216), (170, 214), (172, 214), (177, 216), (178, 201), (220, 236), (221, 242), (227, 257)]) (.cut 4 (.cut 1 (.cut 3 (.cut 2 (.e1 [(122, 161), (123, 271), (129, 309), (130, 190), (163, 258), (164, 180), (170, 179), (172, 179), (178, 180), (179, 258), (212, 190), (213, 309), (219, 271), (220, 161)] [(115, 250), (121, 236), (122, 222), (164, 213), (165, 215), (170, 227), (172, 227), (177, 215), (178, 213), (214, 505), (220, 222), (221, 236), (227, 250)]) (.e1 [(122, 160), (123, 273), (129, 296), (130, 187), (163, 268), (164, 183), (170, 178), (172, 178), (178, 183), (179, 268), (212, 187), (213, 296), (219, 273), (220, 160), (227, 647)] [(114, 567), (115, 243), (116, 559), (121, 238), (122, 229), (128, 524), (164, 212), (165, 217), (170, 224), (172, 224), (177, 217), (178, 212), (214, 524), (220, 229), (221, 238), (226, 559), (227, 243), (228, 567)])) (.cut 2 (.e1 [(122, 160), (123, 261), (129, 309), (130, 187), (163, 268), (164, 178), (170, 184), (172, 184), (178, 178), (179, 268), (212, 187), (213, 309), (219, 261), (220, 160)] [(115, 253), (116, 579), (121, 228), (122, 229), (128, 505), (164, 212), (165, 217), (170, 224), (172, 224), (177, 217), (178, 212), (214, 505), (220, 229), (221, 228), (226, 579), (227, 253)]) (.cut 0 (.e1 [(122, 154), (123, 265), (129, 291), (130, 190), (163, 282), (164, 181), (170, 185), (172, 185), (178, 181), (179, 282), (212, 190), (213, 291), (219, 265), (220, 154)] [(115, 249), (121, 234), (122, 238), (164, 209), (165, 219), (170, 215), (172, 215), (177, 219), (178, 209), (220, 238), (221, 234), (227, 249)]) (.cut 4 (.e1 [(115, 641), (122, 160), (123, 264), (129, 299), (130, 184), (163, 274), (164, 182), (170, 183), (172, 183), (178, 182), (179, 274), (212, 184), (213, 299), (219, 264), (220, 160), (227, 641), (261, 670)] [(114, 557), (115, 245), (116, 574), (121, 230), (122, 234), (128, 519), (164, 212), (165, 217), (170, 224), (172, 224), (177, 217), (178, 212), (214, 519), (220, 234), (221, 230), (226, 574), (227, 245), (228, 557)]) (.e1 [(122, 161), (123, 259), (129, 297), (130, 187), (163, 281), (164, 182), (170, 180), (172, 180), (178, 182), (179, 281), (212, 187), (213, 297), (219, 259), (220, 161)] [(114, 546), (115, 244), (121, 230), (122, 234), (128, 522), (164, 208), (165, 222), (170, 224), (172, 224), (177, 222), (178, 208), (214, 522), (220, 234), (221, 230), (226, 582), (227, 244), (228, 546)]))))) (.redProjected 0 1)) (.cut 2 (.cut 1 (.e1 [(122, 160), (123, 255), (129, 309), (130, 198), (163, 275), (164, 178), (170, 174), (172, 174), (178, 178), (179, 275), (212, 198), (213, 309), (219, 255), (220, 160)] [(115, 253), (121, 234), (122, 224), (164, 202), (165, 227), (170, 224), (172, 224), (177, 227), (178, 202), (214, 506), (220, 224), (221, 234), (227, 253)]) (.redProjected 0 1)) (.cut 1 (.cut 3 (.e1 [(122, 161), (123, 263), (129, 296), (130, 192), (163, 278), (164, 185), (170, 170), (172, 170), (178, 185), (179, 278), (212, 192), (213, 296), (219, 263), (220, 161)] [(115, 240), (121, 238), (122, 228), (164, 203), (165, 226), (170, 227), (172, 227), (177, 226), (178, 203), (220, 228), (221, 238), (227, 240)]) (.e1 [(122, 160), (123, 253), (129, 296), (130, 190), (163, 289), (164, 183), (170, 176), (172, 176), (178, 183), (179, 289), (212, 190), (213, 296), (219, 253), (220, 160)] [(115, 244), (121, 231), (122, 235), (128, 524), (164, 202), (165, 227), (170, 224), (172, 224), (177, 227), (178, 202), (214, 524), (220, 235), (221, 231), (227, 244), (228, 534)])) (.redProjected 0 1)))))) (.cut 3 (.e1 [(122, 160), (123, 271), (130, 215), (163, 278), (164, 179), (170, 158), (172, 158), (178, 179), (179, 278), (212, 215), (213, 292), (219, 271), (220, 160)] [(115, 245), (121, 254), (122, 213), (164, 196), (165, 240), (170, 219), (172, 219), (177, 240), (178, 196), (220, 213), (221, 254), (227, 245)]) (.e1 [(122, 157), (123, 248), (129, 295), (130, 209), (163, 298), (164, 180), (170, 168), (172, 168), (178, 180), (179, 298), (212, 209), (213, 295), (219, 248), (220, 157)] [(114, 525), (115, 250), (121, 238), (122, 228), (128, 527), (164, 192), (165, 241), (170, 218), (172, 218), (177, 241), (178, 192), (214, 527), (220, 228), (221, 238), (227, 250), (228, 525)]))))

theorem plan680_2_ok : plan680_2.checkAt
    (((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 false) = true := by decide +kernel

def plan680_3 : Plan :=
  (.cut 3 (.cut 0 (.e1 [(122, 148), (123, 295), (129, 259), (130, 199), (163, 286), (164, 182), (170, 182), (172, 182), (178, 182), (179, 286), (212, 199), (213, 259), (219, 295), (220, 148)] [(115, 240), (121, 255), (122, 238), (164, 213), (165, 222), (170, 199), (172, 199), (177, 222), (178, 213), (220, 238), (221, 255), (227, 240)]) (.cut 1 (.cut 2 (.e1 [(122, 161), (123, 293), (129, 267), (130, 194), (163, 277), (164, 174), (170, 180), (172, 180), (178, 174), (179, 277), (212, 194), (213, 267), (219, 293), (220, 161)] [(115, 237), (116, 528), (121, 243), (122, 226), (128, 569), (164, 221), (165, 226), (170, 208), (172, 208), (177, 226), (178, 221), (214, 569), (220, 226), (221, 243), (226, 528), (227, 237), (228, 553)]) (.cut 4 (.cut 3 (.e1 [(122, 161), (123, 305), (129, 255), (130, 192), (163, 278), (164, 181), (170, 176), (172, 176), (178, 181), (179, 278), (212, 192), (213, 255), (219, 305), (220, 161)] [(115, 227), (121, 252), (122, 229), (164, 223), (165, 225), (170, 208), (172, 208), (177, 225), (178, 223), (220, 229), (221, 252), (226, 510), (227, 227)]) (.e1 [(122, 160), (123, 294), (129, 255), (130, 190), (163, 289), (164, 179), (170, 181), (172, 181), (178, 179), (179, 289), (212, 190), (213, 255), (219, 294), (220, 160)] [(114, 535), (115, 230), (116, 527), (121, 244), (122, 236), (128, 589), (164, 222), (165, 226), (170, 205), (172, 205), (177, 226), (178, 222), (214, 589), (220, 236), (221, 244), (226, 527), (227, 230), (228, 535)])) (.e1 [(122, 160), (123, 289), (129, 255), (130, 200), (163, 294), (164, 179), (170, 172), (172, 172), (178, 179), (179, 294), (212, 200), (213, 255), (219, 289), (220, 160)] [(115, 230), (121, 250), (122, 230), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (220, 230), (221, 250), (227, 230)]))) (.cut 2 (.cut 4 (.e1 [(81, 693), (115, 662), (121, 634), (122, 160), (123, 292), (129, 275), (130, 193), (131, 718), (163, 270), (164, 181), (170, 175), (172, 175), (178, 181), (179, 270), (211, 718), (212, 193), (213, 275), (219, 292), (220, 160), (221, 634), (227, 662), (261, 693)] [(114, 566), (115, 237), (116, 528), (121, 248), (122, 225), (128, 556), (164, 217), (165, 221), (170, 215), (172, 215), (177, 221), (178, 217), (214, 556), (220, 225), (221, 248), (226, 528), (227, 237), (228, 566)]) (.e1 [(122, 161), (123, 281), (129, 275), (130, 197), (163, 281), (164, 183), (170, 168), (172, 168), (178, 183), (179, 281), (212, 197), (213, 275), (219, 281), (220, 161)] [(115, 233), (121, 248), (122, 225), (164, 208), (165, 230), (170, 217), (172, 217), (177, 230), (178, 208), (220, 225), (221, 248), (227, 233)])) (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 302), (129, 263), (130, 191), (163, 272), (164, 187), (170, 171), (172, 171), (178, 187), (179, 272), (212, 191), (213, 263), (219, 302), (220, 160)] [(115, 227), (116, 514), (121, 256), (122, 228), (164, 217), (165, 221), (170, 215), (172, 215), (177, 221), (178, 217), (220, 228), (221, 256), (226, 514), (227, 227)]) (.e1 [(81, 668), (115, 679), (121, 635), (122, 158), (123, 291), (129, 263), (130, 189), (131, 724), (137, 714), (163, 283), (164, 185), (165, 695), (170, 176), (172, 176), (177, 695), (178, 185), (179, 283), (205, 714), (211, 724), (212, 189), (213, 263), (219, 291), (220, 158), (221, 635), (227, 679), (261, 668)] [(108, 848), (109, 849), (114, 543), (115, 229), (116, 531), (120, 877), (121, 248), (122, 235), (123, 837), (128, 576), (158, 857), (163, 824), (164, 216), (165, 223), (166, 846), (170, 212), (172, 212), (176, 846), (177, 223), (178, 216), (179, 824), (184, 857), (214, 576), (219, 837), (220, 235), (221, 248), (222, 877), (226, 531), (227, 229), (228, 543), (233, 849), (234, 848)])) (.e1 [(122, 160), (123, 284), (129, 263), (130, 196), (163, 290), (164, 187), (170, 167), (172, 167), (178, 187), (179, 290), (212, 196), (213, 263), (219, 284), (220, 160)] [(115, 227), (121, 252), (122, 231), (164, 207), (165, 232), (170, 215), (172, 215), (177, 232), (178, 207), (220, 231), (221, 252), (227, 227), (228, 534)]))))) (.cut 0 (.e1 [(122, 147), (123, 274), (129, 259), (130, 195), (163, 307), (164, 178), (170, 192), (172, 192), (178, 178), (179, 307), (212, 195), (213, 259), (219, 274), (220, 147)] [(115, 245), (121, 240), (122, 251), (164, 211), (165, 225), (170, 196), (172, 196), (177, 225), (178, 211), (220, 251), (221, 240), (227, 245)]) (.cut 1 (.cut 4 (.cut 3 (.cut 2 (.e1 [(122, 160), (123, 281), (129, 267), (130, 190), (163, 289), (164, 172), (170, 187), (172, 187), (178, 172), (179, 289), (212, 190), (213, 267), (219, 281), (220, 160)] [(114, 535), (115, 240), (116, 546), (121, 234), (122, 235), (164, 222), (165, 226), (170, 205), (172, 205), (177, 226), (178, 222), (214, 569), (220, 235), (221, 234), (226, 546), (227, 240), (228, 535)]) (.cut 0 (.e1 [(122, 154), (123, 286), (129, 251), (130, 193), (163, 303), (164, 176), (170, 189), (172, 189), (178, 176), (179, 303), (212, 193), (213, 251), (219, 286), (220, 154)] [(115, 235), (121, 241), (122, 245), (164, 219), (165, 229), (170, 197), (172, 197), (177, 229), (178, 219), (220, 245), (221, 241), (227, 235)]) (.e1 [(81, 651), (115, 675), (121, 666), (122, 161), (123, 282), (129, 256), (130, 187), (137, 700), (163, 299), (164, 177), (170, 185), (172, 185), (178, 177), (179, 299), (205, 700), (212, 187), (213, 256), (219, 282), (220, 161), (221, 666), (227, 675), (261, 651)] [(114, 519), (115, 231), (116, 544), (121, 236), (122, 241), (128, 588), (164, 221), (165, 229), (170, 205), (172, 205), (177, 229), (178, 221), (214, 588), (220, 241), (221, 236), (226, 544), (227, 231), (228, 519)]))) (.cut 2 (.cut 0 (.e1 [(122, 154), (123, 273), (129, 267), (130, 193), (163, 299), (164, 170), (170, 193), (172, 193), (178, 170), (179, 299), (212, 193), (213, 267), (219, 273), (220, 154)] [(115, 247), (121, 231), (122, 242), (164, 218), (165, 227), (170, 199), (172, 199), (177, 227), (178, 218), (220, 242), (221, 231), (227, 247)]) (.e1 [(122, 160), (123, 271), (129, 270), (130, 189), (163, 297), (164, 171), (170, 190), (172, 190), (178, 171), (179, 297), (212, 189), (213, 270), (219, 271), (220, 160)] [(114, 523), (115, 242), (121, 228), (122, 239), (128, 563), (164, 219), (165, 229), (170, 205), (172, 205), (177, 229), (178, 219), (214, 563), (220, 239), (221, 228), (226, 564), (227, 242), (228, 523)])) (.cut 0 (.e1 [(122, 154), (123, 273), (129, 255), (130, 188), (163, 311), (164, 176), (170, 193), (172, 193), (178, 176), (179, 311), (212, 188), (213, 255), (219, 273), (220, 154)] [(115, 238), (121, 232), (122, 252), (164, 218), (165, 227), (170, 199), (172, 199), (177, 227), (178, 218), (220, 252), (221, 232), (227, 238)]) (.e1 [(115, 672), (122, 160), (123, 271), (129, 258), (130, 184), (163, 310), (164, 177), (165, 679), (170, 190), (172, 190), (177, 679), (178, 177), (179, 310), (212, 184), (213, 258), (219, 271), (220, 160), (227, 672)] [(114, 504), (115, 233), (116, 563), (121, 229), (122, 249), (128, 584), (164, 219), (165, 229), (170, 205), (172, 205), (177, 229), (178, 219), (214, 584), (220, 249), (221, 229), (226, 563), (227, 233), (228, 504)])))) (.cut 3 (.cut 2 (.e1 [(122, 161), (123, 272), (129, 267), (130, 194), (163, 298), (164, 174), (170, 179), (172, 179), (178, 174), (179, 298), (212, 194), (213, 267), (219, 272), (220, 161)] [(115, 237), (121, 235), (122, 234), (164, 214), (165, 235), (170, 208), (172, 208), (177, 235), (178, 214), (220, 234), (221, 235), (227, 237)]) (.e1 [(122, 160), (123, 274), (129, 255), (130, 193), (163, 310), (164, 179), (170, 179), (172, 179), (178, 179), (179, 310), (212, 193), (213, 255), (219, 274), (220, 160)] [(115, 230), (121, 238), (122, 241), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (220, 241), (221, 238), (226, 558), (227, 230), (228, 505)])) (.cut 2 (.e1 [(122, 160), (123, 262), (129, 267), (130, 193), (163, 310), (164, 172), (170, 185), (172, 185), (178, 172), (179, 310), (212, 193), (213, 267), (219, 262), (220, 160)] [(114, 505), (115, 241), (121, 228), (122, 241), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (220, 241), (221, 228), (227, 241), (228, 505)]) (.e1 [(115, 678), (121, 685), (122, 160), (123, 262), (129, 255), (130, 188), (163, 323), (164, 179), (165, 661), (170, 185), (172, 185), (177, 661), (178, 179), (179, 323), (212, 188), (213, 255), (219, 262), (220, 160), (221, 685), (227, 678), (261, 629)] [(114, 487), (115, 231), (116, 578), (121, 229), (122, 251), (128, 589), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (214, 589), (220, 251), (221, 229), (226, 578), (227, 231), (228, 487)])))) (.cut 4 (.cut 3 (.cut 2 (.cut 0 (.e1 [(122, 154), (123, 281), (129, 270), (130, 194), (163, 286), (164, 178), (170, 184), (172, 184), (178, 178), (179, 286), (212, 194), (213, 270), (219, 281), (220, 154)] [(115, 242), (121, 242), (122, 236), (164, 214), (165, 223), (170, 206), (172, 206), (177, 223), (178, 214), (220, 236), (221, 242), (227, 242), (228, 540)]) (.cut 1 (.e1 [(81, 672), (115, 657), (121, 663), (122, 161), (123, 279), (129, 273), (130, 189), (131, 725), (137, 708), (163, 284), (164, 176), (165, 689), (170, 182), (172, 182), (177, 689), (178, 176), (179, 284), (205, 708), (211, 725), (212, 189), (213, 273), (219, 279), (220, 161), (221, 663), (227, 657), (261, 672)] [(114, 542), (115, 238), (116, 549), (121, 236), (122, 233), (128, 558), (164, 218), (165, 225), (170, 211), (172, 211), (177, 225), (178, 218), (214, 558), (220, 233), (221, 236), (226, 549), (227, 238), (228, 542)]) .sb)) (.cut 0 (.e1 [(122, 154), (123, 280), (129, 264), (130, 188), (163, 294), (164, 184), (170, 183), (172, 183), (178, 184), (179, 294), (212, 188), (213, 264), (219, 280), (220, 154)] [(115, 234), (121, 242), (122, 244), (164, 213), (165, 222), (170, 208), (172, 208), (177, 222), (178, 213), (220, 244), (221, 242), (227, 234)]) (.cut 1 (.e1 [(81, 652), (115, 676), (121, 660), (122, 160), (123, 282), (129, 262), (130, 185), (131, 729), (137, 705), (163, 293), (164, 181), (165, 692), (170, 183), (172, 183), (177, 692), (178, 181), (179, 293), (205, 705), (211, 729), (212, 185), (213, 262), (219, 282), (220, 160), (221, 660), (227, 676), (261, 652)] [(114, 529), (115, 231), (116, 544), (121, 238), (122, 241), (128, 577), (163, 826), (164, 219), (165, 224), (170, 210), (172, 210), (177, 224), (178, 219), (179, 826), (214, 577), (219, 855), (220, 241), (221, 238), (226, 544), (227, 231), (228, 529)]) (.e1 [(81, 654), (115, 683), (121, 657), (122, 161), (123, 277), (129, 267), (130, 184), (163, 292), (164, 185), (170, 178), (172, 178), (178, 185), (179, 292), (212, 184), (213, 267), (219, 277), (220, 161), (221, 657), (227, 683), (261, 654)] [(114, 529), (115, 228), (116, 551), (121, 238), (122, 240), (128, 569), (164, 215), (165, 224), (170, 216), (172, 216), (177, 224), (178, 215), (214, 569), (220, 240), (221, 238), (226, 551), (227, 228), (228, 529)])))) (.cut 2 (.cut 0 (.e1 [(122, 154), (123, 268), (129, 275), (130, 188), (163, 294), (164, 178), (170, 189), (172, 189), (178, 178), (179, 294), (212, 188), (213, 275), (219, 268), (220, 154)] [(115, 244), (121, 233), (122, 244), (164, 213), (165, 222), (170, 208), (172, 208), (177, 222), (178, 213), (220, 244), (221, 233), (227, 244)]) (.cut 1 (.e1 [(81, 654), (122, 160), (123, 268), (129, 275), (130, 186), (163, 294), (164, 176), (170, 187), (172, 187), (178, 176), (179, 294), (212, 186), (213, 275), (219, 268), (220, 160), (227, 653), (261, 654)] [(114, 526), (115, 240), (116, 568), (121, 229), (122, 240), (128, 555), (164, 216), (165, 226), (170, 211), (172, 211), (177, 226), (178, 216), (214, 555), (220, 240), (221, 229), (226, 568), (227, 240), (228, 526)]) (.e1 [(81, 654), (115, 659), (121, 682), (122, 161), (123, 266), (129, 279), (130, 184), (163, 292), (164, 179), (170, 184), (172, 184), (178, 179), (179, 292), (211, 713), (212, 184), (213, 279), (219, 266), (220, 161), (221, 682), (227, 659), (261, 654)] [(114, 529), (115, 238), (116, 571), (121, 228), (122, 240), (128, 549), (164, 215), (165, 224), (170, 216), (172, 216), (177, 224), (178, 215), (214, 549), (220, 240), (221, 228), (226, 571), (227, 238), (228, 529)]))) (.cut 0 (.e1 [(122, 154), (123, 272), (129, 262), (130, 186), (163, 305), (164, 182), (170, 188), (172, 188), (178, 182), (179, 305), (212, 186), (213, 262), (219, 272), (220, 154)] [(115, 235), (121, 235), (122, 251), (164, 214), (165, 223), (170, 206), (172, 206), (177, 223), (178, 214), (220, 251), (221, 235), (227, 235)]) (.e1 [(81, 637), (115, 677), (121, 677), (122, 161), (123, 267), (129, 267), (130, 182), (131, 719), (163, 303), (164, 183), (170, 183), (172, 183), (177, 686), (178, 183), (179, 303), (211, 719), (212, 182), (213, 267), (219, 267), (220, 161), (221, 677), (227, 677), (261, 637)] [(114, 512), (115, 231), (116, 569), (121, 231), (122, 247), (128, 569), (164, 214), (165, 226), (170, 214), (172, 214), (177, 226), (178, 214), (214, 569), (220, 247), (221, 231), (226, 569), (227, 231), (228, 512)])))) (.cut 3 (.cut 2 (.e1 [(122, 160), (123, 269), (129, 275), (130, 194), (163, 293), (164, 181), (170, 174), (172, 174), (178, 181), (179, 293), (212, 194), (213, 275), (219, 269), (220, 160)] [(114, 529), (115, 237), (121, 239), (122, 233), (164, 207), (165, 232), (170, 215), (172, 215), (177, 232), (178, 207), (220, 233), (221, 239), (227, 237), (228, 529)]) (.e1 [(122, 158), (123, 270), (129, 263), (130, 193), (163, 305), (164, 185), (170, 174), (172, 174), (178, 185), (179, 305), (212, 193), (213, 263), (219, 270), (220, 158)] [(114, 512), (115, 230), (116, 563), (121, 242), (122, 241), (164, 207), (165, 233), (170, 212), (172, 212), (177, 233), (178, 207), (214, 576), (220, 241), (221, 242), (226, 563), (227, 230), (228, 512)])) (.cut 2 (.e1 [(81, 648), (115, 662), (121, 680), (122, 160), (123, 257), (129, 275), (130, 189), (163, 306), (164, 181), (165, 673), (170, 181), (172, 181), (177, 673), (178, 181), (179, 306), (212, 189), (213, 275), (219, 257), (220, 160), (221, 680), (227, 662), (261, 648)] [(114, 510), (115, 237), (116, 586), (121, 229), (122, 243), (128, 555), (164, 207), (165, 232), (170, 215), (172, 215), (177, 232), (178, 207), (214, 555), (220, 243), (221, 229), (226, 586), (227, 237), (228, 510)]) (.e1 [(81, 639), (115, 678), (121, 673), (122, 160), (123, 259), (129, 264), (130, 189), (131, 727), (137, 742), (163, 315), (164, 183), (165, 663), (170, 178), (172, 178), (177, 663), (178, 183), (179, 315), (205, 742), (211, 727), (212, 189), (213, 264), (219, 259), (220, 160), (221, 673), (227, 678), (261, 639)] [(65, 885), (108, 821), (109, 892), (114, 497), (115, 231), (116, 582), (120, 835), (121, 233), (122, 247), (128, 574), (158, 864), (163, 794), (164, 206), (165, 235), (170, 212), (172, 212), (177, 235), (178, 206), (179, 794), (184, 864), (214, 574), (220, 247), (221, 233), (222, 835), (226, 582), (227, 231), (228, 497), (233, 892), (234, 821), (277, 885)])))))))

theorem plan680_3_ok : plan680_3.checkAt
    (((((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 true) 1 false) 4 false) = true := by decide +kernel

def plan680_4 : Plan :=
  (.cut 3 (.e1 [(122, 157), (123, 277), (129, 263), (130, 212), (163, 301), (164, 183), (170, 161), (172, 161), (178, 183), (179, 301), (212, 212), (213, 263), (219, 277), (220, 157)] [(115, 232), (121, 258), (122, 226), (164, 198), (165, 245), (170, 209), (172, 209), (177, 245), (178, 198), (220, 226), (221, 258), (227, 232)]) (.cut 0 (.e1 [(122, 148), (123, 256), (129, 259), (130, 207), (164, 182), (170, 178), (172, 178), (178, 182), (179, 328), (212, 207), (213, 259), (219, 256), (220, 148)] [(115, 242), (121, 243), (122, 249), (164, 196), (165, 242), (170, 199), (172, 199), (177, 242), (178, 196), (220, 249), (221, 243), (227, 242)]) (.cut 1 (.e1 [(122, 160), (123, 255), (129, 258), (130, 202), (163, 328), (164, 177), (170, 174), (172, 174), (178, 177), (179, 328), (212, 202), (213, 258), (219, 255), (220, 160)] [(114, 482), (115, 234), (121, 235), (122, 242), (164, 202), (165, 249), (170, 205), (172, 205), (177, 249), (178, 202), (214, 585), (220, 242), (221, 235), (227, 234), (228, 482)]) (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 261), (129, 266), (130, 200), (163, 312), (164, 185), (170, 167), (172, 167), (178, 185), (179, 312), (212, 200), (213, 266), (219, 261), (220, 160)] [(115, 230), (121, 243), (122, 237), (164, 199), (165, 242), (170, 215), (172, 215), (177, 242), (178, 199), (220, 237), (221, 243), (227, 230)]) (.e1 [(122, 158), (123, 251), (129, 267), (130, 199), (163, 322), (164, 182), (170, 173), (172, 173), (178, 182), (179, 322), (212, 199), (213, 267), (219, 251), (220, 158)] [(114, 489), (115, 235), (121, 235), (122, 243), (164, 198), (165, 244), (170, 212), (172, 212), (177, 244), (178, 198), (220, 243), (221, 235), (227, 235), (228, 489)])) (.redProjected 0 1)))))

theorem plan680_4_ok : plan680_4.checkAt
    (((((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 true) 1 false) 4 true) = true := by decide +kernel

def plan680_n0 : Plan := .cut 4 plan680_3 plan680_4

theorem plan680_n0_ok : plan680_n0.checkAt
    ((((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 true) 1 false) = true :=
  checkAt_cut 4 plan680_3 plan680_4
    ((((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 true) 1 false)
    (by decide +kernel) plan680_3_ok plan680_4_ok

def plan680_5 : Plan :=
  (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 147), (123, 288), (129, 276), (130, 198), (163, 275), (164, 195), (170, 172), (172, 172), (178, 195), (179, 275), (212, 198), (213, 276), (219, 288), (220, 147)] [(115, 238), (121, 262), (122, 235), (164, 201), (165, 216), (170, 214), (172, 214), (177, 216), (178, 201), (220, 235), (221, 262), (227, 238)]) (.cut 1 (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 300), (129, 270), (130, 191), (163, 267), (164, 189), (170, 169), (172, 169), (178, 189), (179, 267), (212, 191), (213, 270), (219, 300), (220, 160)] [(115, 228), (116, 517), (121, 257), (122, 226), (128, 565), (164, 214), (165, 219), (170, 219), (172, 219), (177, 219), (178, 214), (214, 565), (220, 226), (221, 257), (226, 517), (227, 228)]) (.cut 2 (.e1 [(122, 160), (123, 285), (129, 284), (130, 187), (163, 268), (164, 189), (170, 172), (172, 172), (178, 189), (179, 268), (212, 187), (213, 284), (219, 285), (220, 160)] [(114, 568), (115, 233), (116, 539), (121, 247), (122, 228), (128, 543), (164, 212), (165, 217), (170, 224), (172, 224), (177, 217), (178, 212), (214, 543), (220, 228), (221, 247), (226, 539), (227, 233), (228, 568)]) (.e1 [(122, 158), (123, 287), (129, 270), (130, 186), (163, 280), (164, 191), (170, 173), (172, 173), (178, 191), (179, 280), (212, 186), (213, 270), (219, 287), (220, 158), (221, 632)] [(114, 548), (115, 227), (116, 536), (121, 249), (122, 235), (128, 566), (164, 212), (165, 219), (170, 219), (172, 219), (177, 219), (178, 212), (214, 566), (220, 235), (221, 249), (226, 536), (227, 227), (228, 548)]))) (.e1 [(122, 160), (123, 282), (129, 270), (130, 195), (163, 285), (164, 189), (170, 165), (172, 165), (178, 189), (179, 285), (212, 195), (213, 270), (219, 282), (220, 160)] [(115, 228), (121, 253), (122, 229), (164, 205), (165, 229), (170, 219), (172, 219), (177, 229), (178, 205), (220, 229), (221, 253), (227, 228)])) (.redProjected 0 1))) (.cut 0 (.e1 [(122, 145), (123, 271), (129, 276), (130, 189), (163, 292), (164, 191), (170, 186), (172, 186), (178, 191), (179, 292), (212, 189), (213, 276), (219, 271), (220, 145)] [(115, 243), (121, 244), (122, 251), (164, 204), (165, 214), (170, 210), (172, 210), (177, 214), (178, 204), (220, 251), (221, 244), (227, 243)]) (.cut 4 (.cut 1 (.cut 3 (.cut 2 (.cut 0 (.e1 [(122, 154), (123, 278), (129, 282), (130, 189), (163, 277), (164, 185), (170, 181), (172, 181), (178, 185), (179, 277), (212, 189), (213, 282), (219, 278), (220, 154)] [(115, 241), (121, 242), (122, 236), (164, 211), (165, 216), (170, 215), (172, 215), (177, 216), (178, 211), (220, 236), (221, 242), (227, 241)]) (.e1 [(81, 667), (115, 666), (121, 658), (122, 161), (123, 274), (129, 282), (130, 185), (131, 698), (137, 722), (163, 280), (164, 185), (165, 702), (170, 177), (172, 177), (177, 702), (178, 185), (179, 280), (205, 722), (211, 698), (212, 185), (213, 282), (219, 274), (220, 161), (221, 658), (227, 666), (261, 667)] [(114, 549), (115, 235), (116, 556), (121, 238), (122, 234), (128, 544), (129, 851), (164, 213), (165, 220), (170, 221), (172, 221), (177, 220), (178, 213), (213, 851), (214, 544), (219, 865), (220, 234), (221, 238), (226, 556), (227, 235), (228, 549)])) (.cut 0 (.e1 [(122, 154), (123, 277), (129, 268), (130, 186), (163, 292), (164, 189), (170, 180), (172, 180), (178, 189), (179, 292), (212, 186), (213, 268), (219, 277), (220, 154)] [(115, 232), (121, 243), (122, 244), (164, 210), (165, 220), (170, 213), (172, 213), (177, 220), (178, 210), (220, 244), (221, 243), (227, 232)]) (.e1 [(122, 161), (123, 277), (129, 273), (130, 182), (163, 286), (164, 190), (170, 176), (172, 176), (178, 190), (179, 286), (212, 182), (213, 273), (219, 277), (220, 161), (261, 656)] [(114, 539), (115, 228), (116, 551), (121, 240), (122, 239), (128, 559), (164, 213), (165, 220), (170, 221), (172, 221), (177, 220), (178, 213), (214, 559), (220, 239), (221, 240), (226, 551), (227, 228), (228, 539)]))) (.cut 2 (.cut 0 (.e1 [(122, 155), (123, 264), (129, 282), (130, 184), (163, 291), (164, 185), (170, 184), (172, 184), (178, 185), (179, 291), (212, 184), (213, 282), (219, 264), (220, 155)] [(115, 240), (121, 233), (122, 244), (164, 209), (165, 219), (170, 217), (172, 217), (177, 219), (178, 209), (220, 244), (221, 233), (227, 240)]) (.e1 [(81, 656), (115, 660), (121, 676), (122, 161), (123, 266), (129, 285), (130, 182), (131, 699), (137, 722), (163, 286), (164, 184), (170, 182), (172, 182), (178, 184), (179, 286), (205, 722), (211, 699), (212, 182), (213, 285), (219, 266), (220, 161), (221, 676), (227, 660), (261, 656)] [(114, 539), (115, 238), (116, 571), (121, 230), (122, 239), (128, 539), (164, 213), (165, 220), (170, 221), (172, 221), (177, 220), (178, 213), (214, 539), (220, 239), (221, 230), (226, 571), (227, 238), (228, 539)])) (.cut 0 (.e1 [(122, 154), (123, 265), (129, 273), (130, 181), (163, 300), (164, 189), (170, 185), (172, 185), (178, 189), (179, 300), (212, 181), (213, 273), (219, 265), (220, 154)] [(115, 235), (121, 234), (122, 252), (164, 209), (165, 219), (170, 215), (172, 215), (177, 219), (178, 209), (220, 252), (221, 234), (227, 235)]) (.e1 [(81, 632), (122, 160), (123, 263), (129, 276), (130, 177), (163, 299), (164, 190), (170, 182), (172, 182), (178, 190), (179, 299), (212, 177), (213, 276), (219, 263), (220, 160), (261, 632)] [(114, 519), (115, 230), (116, 576), (121, 231), (122, 249), (128, 555), (164, 211), (165, 221), (170, 222), (172, 222), (177, 221), (178, 211), (214, 555), (220, 249), (221, 231), (226, 576), (227, 230), (228, 519)])))) (.redProjected 0 1)) (.cut 1 (.cut 3 (.cut 2 (.e1 [(122, 160), (123, 266), (129, 279), (130, 192), (163, 291), (164, 185), (170, 172), (172, 172), (178, 185), (179, 291), (212, 192), (213, 279), (219, 266), (220, 160)] [(115, 235), (121, 240), (122, 234), (164, 205), (165, 229), (170, 219), (172, 219), (177, 229), (178, 205), (220, 234), (221, 240), (227, 235), (228, 531)]) (.e1 [(122, 157), (123, 269), (129, 271), (130, 190), (163, 297), (164, 191), (170, 171), (172, 171), (178, 191), (179, 297), (212, 190), (213, 271), (219, 269), (220, 157)] [(114, 523), (115, 230), (121, 245), (122, 241), (164, 203), (165, 227), (170, 218), (172, 218), (177, 227), (178, 203), (214, 563), (220, 241), (221, 245), (226, 565), (227, 230), (228, 523)])) (.cut 2 (.e1 [(122, 158), (123, 255), (129, 281), (130, 190), (163, 302), (164, 185), (170, 177), (172, 177), (178, 185), (179, 302), (212, 190), (213, 281), (219, 255), (220, 158)] [(114, 516), (115, 238), (121, 232), (122, 242), (128, 546), (164, 203), (165, 230), (170, 219), (172, 219), (177, 230), (178, 203), (214, 546), (220, 242), (221, 232), (226, 589), (227, 238), (228, 516)]) (.e1 [(122, 157), (123, 257), (129, 271), (130, 185), (163, 310), (164, 191), (170, 177), (172, 177), (178, 191), (179, 310), (212, 185), (213, 271), (219, 257), (220, 157)] [(114, 505), (115, 230), (116, 585), (121, 235), (122, 251), (128, 563), (164, 203), (165, 227), (170, 218), (172, 218), (177, 227), (178, 203), (214, 563), (220, 251), (221, 235), (226, 585), (227, 230), (228, 505)]))) (.redProjected 0 1))))) (.cut 3 (.e1 [(122, 160), (123, 271), (129, 268), (130, 202), (163, 301), (164, 191), (170, 158), (172, 158), (178, 191), (179, 301), (212, 202), (213, 268), (219, 271), (220, 160)] [(115, 226), (121, 254), (122, 231), (164, 196), (165, 240), (170, 219), (172, 219), (177, 240), (178, 196), (220, 231), (221, 254), (227, 226)]) (.cut 0 (.e1 [(122, 145), (123, 255), (129, 276), (130, 209), (163, 311), (164, 191), (170, 170), (172, 170), (178, 191), (179, 311), (212, 209), (213, 276), (219, 255), (220, 145)] [(115, 244), (121, 251), (122, 244), (164, 187), (165, 235), (170, 210), (172, 210), (177, 235), (178, 187), (220, 244), (221, 251), (227, 244)]) (.redProjected 0 1))))

theorem plan680_5_ok : plan680_5.checkAt
    ((((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 true) 1 true) = true := by decide +kernel

def plan680_n1 : Plan := .cut 1 plan680_n0 plan680_5

theorem plan680_n1_ok : plan680_n1.checkAt
    (((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 true) = true :=
  checkAt_cut 1 plan680_n0 plan680_5
    (((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) 2 true)
    (by decide +kernel) plan680_n0_ok plan680_5_ok

def plan680_n2 : Plan := .cut 2 plan680_2 plan680_n1

theorem plan680_n2_ok : plan680_n2.checkAt
    ((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true) = true :=
  checkAt_cut 2 plan680_2 plan680_n1
    ((((rootAddress ![2, 2] ![2, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) 0 true)
    (by decide +kernel) plan680_2_ok plan680_n1_ok

def plan680_n3 : Plan := .cut 0 plan680_1 plan680_n2

theorem plan680_n3_ok : plan680_n3.checkAt
    (((rootAddress ![2, 2] ![2, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false) = true :=
  checkAt_cut 0 plan680_1 plan680_n2
    (((rootAddress ![2, 2] ![2, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 false)
    (by decide +kernel) plan680_1_ok plan680_n2_ok

def plan680_6 : Plan :=
  (.cut 0 (.e1 [(122, 128), (123, 256), (129, 260), (130, 269), (164, 180), (170, 160), (172, 160), (178, 180), (212, 269), (213, 260), (219, 256), (220, 128)] [(115, 265), (121, 282), (122, 237), (164, 167), (165, 271), (170, 182), (172, 182), (177, 271), (178, 167), (220, 237), (221, 282), (227, 265)]) (.cut 2 (.e1 [(122, 157), (123, 245), (129, 283), (130, 243), (163, 323), (164, 167), (170, 156), (172, 156), (178, 167), (179, 323), (212, 243), (213, 283), (219, 245), (220, 157)] [(115, 257), (121, 248), (122, 215), (164, 182), (165, 276), (170, 204), (172, 204), (177, 276), (178, 182), (220, 215), (221, 248), (227, 257), (228, 496)]) (.e1 [(122, 157), (123, 245), (129, 259), (130, 232), (163, 347), (164, 179), (170, 156), (172, 156), (178, 179), (179, 347), (212, 232), (213, 259), (219, 245), (220, 157)] [(115, 238), (121, 251), (122, 231), (164, 182), (165, 276), (170, 204), (172, 204), (177, 276), (178, 182), (220, 231), (221, 251), (227, 238), (228, 464)])))

theorem plan680_6_ok : plan680_6.checkAt
    (((rootAddress ![2, 2] ![2, 2, 0]).child true).child true)
    (childBox (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) 4 true) = true := by decide +kernel

def plan680_n4 : Plan := .cut 4 plan680_n3 plan680_6

theorem plan680_n4_ok : plan680_n4.checkAt
    ((rootAddress ![2, 2] ![2, 2, 0]).child true)
    (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true) = true :=
  checkAt_cut 4 plan680_n3 plan680_6
    ((rootAddress ![2, 2] ![2, 2, 0]).child true)
    (childBox (rootBox ![2, 2] ![2, 2, 0]) 1 true)
    (by decide +kernel) plan680_n3_ok plan680_6_ok

def plan680 : Plan := .cut 1 plan680_0 plan680_n4

theorem plan680_ok : plan680.checkAt
    (rootAddress ![2, 2] ![2, 2, 0])
    (rootBox ![2, 2] ![2, 2, 0]) = true :=
  checkAt_cut 1 plan680_0 plan680_n4
    (rootAddress ![2, 2] ![2, 2, 0])
    (rootBox ![2, 2] ![2, 2, 0])
    (by decide +kernel) plan680_0_ok plan680_n4_ok

theorem root680 : rootCheck plan680 ![2, 2] ![2, 2, 0] = true := plan680_ok

def plan681 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 238), (129, 245), (130, 304), (164, 158), (170, 151), (172, 151), (178, 158), (212, 304), (213, 245), (219, 238), (220, 151)] [(115, 264), (121, 266), (122, 215), (164, 172), (170, 180), (172, 180), (178, 172), (220, 215), (221, 266), (227, 264)]) (.e1 [(122, 157), (123, 223), (129, 255), (164, 174), (170, 143), (172, 143), (178, 174), (213, 255), (219, 223), (220, 157)] [(115, 249), (121, 259), (122, 223), (164, 165), (170, 200), (172, 200), (178, 165), (220, 223), (221, 259), (227, 249)]))

theorem root681 : rootCheck plan681 ![2, 2] ![2, 2, 1] = true := by decide +kernel

def plan682 : Plan :=
  (.e1 [(122, 139), (123, 248), (129, 260), (164, 160), (165, 285), (170, 147), (172, 147), (177, 285), (178, 160), (213, 260), (219, 248), (220, 139)] [(114, 353), (115, 321), (121, 326), (122, 191), (164, 164), (170, 177), (172, 177), (178, 164), (179, 335), (220, 191), (221, 326), (227, 321), (228, 353)])

theorem root682 : rootCheck plan682 ![2, 2] ![2, 2, 2] = true := by decide +kernel

def plan683 : Plan :=
  (.cut 1 (.cut 0 (.e1 [(122, 131), (123, 290), (129, 238), (164, 149), (165, 220), (170, 201), (172, 201), (177, 220), (178, 149), (213, 238), (219, 290), (220, 131)] [(114, 316), (122, 195), (163, 256), (164, 208), (170, 156), (172, 156), (178, 208), (179, 256), (220, 195), (221, 349), (228, 316)]) (.cut 4 (.e1 [(122, 157), (123, 257), (129, 248), (164, 159), (165, 214), (170, 168), (172, 168), (177, 214), (178, 159), (213, 248), (219, 257), (220, 157)] [(114, 298), (122, 179), (163, 284), (164, 196), (170, 186), (172, 186), (178, 196), (179, 284), (220, 179), (228, 298)]) (.e1 [(122, 157), (123, 269), (129, 248), (164, 159), (165, 194), (170, 180), (172, 180), (177, 194), (178, 159), (213, 248), (219, 269), (220, 157)] [(114, 288), (122, 176), (163, 262), (164, 209), (170, 186), (172, 186), (178, 209), (179, 262), (220, 176), (228, 288)]))) (.cut 0 (.e1 [(122, 131), (123, 265), (129, 271), (164, 182), (165, 201), (170, 176), (172, 176), (177, 201), (178, 182), (213, 271), (219, 265), (220, 131)] [(114, 308), (122, 193), (163, 237), (164, 183), (170, 189), (172, 189), (178, 183), (179, 237), (220, 193), (228, 308)]) (.cut 4 (.e1 [(122, 151), (123, 253), (129, 274), (164, 169), (165, 222), (170, 148), (172, 148), (177, 222), (178, 169), (213, 274), (219, 253), (220, 151)] [(114, 319), (115, 335), (122, 176), (163, 286), (164, 176), (170, 198), (172, 198), (178, 176), (179, 286), (220, 176), (227, 335), (228, 319)]) (.e1 [(122, 151), (123, 262), (129, 282), (164, 177), (165, 176), (170, 174), (172, 174), (177, 176), (178, 177), (213, 282), (219, 262), (220, 151)] [(114, 289), (122, 175), (163, 236), (164, 198), (170, 207), (172, 207), (178, 198), (179, 236), (220, 175), (228, 289)]))))

theorem root683 : rootCheck plan683 ![2, 2] ![2, 2, 3] = true := by decide +kernel

def plan684_0 : Plan :=
  (.cut 4 (.cut 0 (.e1 [(122, 128), (123, 260), (129, 246), (130, 227), (164, 150), (170, 228), (172, 228), (178, 150), (179, 355), (212, 227), (213, 246), (219, 260), (220, 128)] [(115, 287), (121, 231), (122, 269), (164, 211), (165, 243), (170, 157), (172, 157), (177, 243), (178, 211), (220, 269), (221, 231), (227, 287)]) (.cut 1 (.cut 2 (.e1 [(122, 157), (123, 256), (129, 257), (130, 218), (164, 132), (170, 220), (172, 220), (178, 132), (179, 342), (212, 218), (213, 257), (219, 256), (220, 157)] [(115, 281), (121, 207), (122, 239), (164, 231), (165, 264), (170, 168), (172, 168), (177, 264), (178, 231), (220, 239), (221, 207), (227, 281)]) (.cut 3 (.e1 [(122, 157), (123, 266), (129, 232), (130, 213), (163, 355), (164, 143), (170, 212), (172, 212), (178, 143), (179, 355), (212, 213), (213, 232), (219, 266), (220, 157)] [(115, 257), (121, 219), (122, 248), (164, 231), (165, 264), (170, 168), (172, 168), (177, 264), (178, 231), (220, 248), (221, 219), (227, 257), (228, 458)]) (.e1 [(122, 157), (123, 241), (129, 230), (130, 211), (164, 150), (170, 214), (172, 214), (178, 150), (212, 211), (213, 230), (219, 241), (220, 157)] [(115, 255), (121, 212), (122, 265), (164, 220), (165, 270), (170, 173), (172, 173), (177, 270), (178, 220), (220, 265), (221, 212), (227, 255)]))) (.cut 2 (.cut 3 (.cut 4 (.e1 [(122, 160), (123, 269), (129, 271), (130, 192), (163, 300), (164, 158), (170, 202), (172, 202), (178, 158), (179, 300), (212, 192), (213, 271), (219, 269), (220, 160)] [(115, 254), (121, 219), (122, 238), (164, 227), (165, 232), (170, 196), (172, 196), (177, 232), (178, 227), (220, 238), (221, 219), (227, 254)]) (.e1 [(122, 160), (123, 238), (129, 271), (130, 201), (163, 336), (164, 158), (170, 198), (172, 198), (178, 158), (179, 336), (212, 201), (213, 271), (219, 238), (220, 160)] [(115, 259), (121, 211), (122, 247), (164, 211), (165, 252), (170, 196), (172, 196), (177, 252), (178, 211), (220, 247), (221, 211), (227, 259)])) (.cut 4 (.e1 [(122, 160), (123, 237), (129, 271), (130, 194), (164, 158), (170, 205), (172, 205), (178, 158), (179, 338), (212, 194), (213, 271), (219, 237), (220, 160)] [(115, 259), (121, 206), (122, 254), (164, 215), (165, 246), (170, 196), (172, 196), (177, 246), (178, 215), (220, 254), (221, 206), (227, 259)]) (.e1 [(122, 160), (123, 233), (129, 271), (130, 199), (164, 158), (170, 202), (172, 202), (178, 158), (212, 199), (213, 271), (219, 233), (220, 160)] [(115, 260), (121, 207), (122, 252), (164, 211), (165, 252), (170, 196), (172, 196), (177, 252), (178, 211), (220, 252), (221, 207), (227, 260)]))) (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 145), (123, 264), (129, 247), (130, 200), (164, 162), (170, 212), (172, 212), (178, 162), (212, 200), (213, 247), (219, 264), (220, 145)] [(115, 256), (121, 225), (122, 262), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 262), (221, 225), (227, 256)]) (.cut 1 (.e1 [(122, 157), (123, 262), (129, 246), (130, 195), (163, 338), (164, 157), (170, 209), (172, 209), (178, 157), (179, 338), (212, 195), (213, 246), (219, 262), (220, 157)] [(115, 249), (121, 217), (122, 255), (164, 226), (165, 244), (170, 184), (172, 184), (177, 244), (178, 226), (220, 255), (221, 217), (227, 249)]) (.e1 [(81, 621), (115, 654), (121, 714), (122, 158), (123, 257), (129, 251), (130, 192), (131, 786), (137, 714), (163, 335), (164, 166), (165, 651), (170, 199), (172, 199), (177, 651), (178, 166), (179, 335), (205, 714), (211, 786), (212, 192), (213, 251), (219, 257), (220, 158), (221, 714), (227, 654), (261, 621)] [(108, 860), (114, 474), (115, 242), (116, 589), (120, 763), (121, 220), (122, 255), (128, 596), (164, 219), (165, 242), (166, 843), (170, 193), (172, 193), (176, 843), (177, 242), (178, 219), (179, 775), (214, 596), (220, 255), (221, 220), (222, 763), (226, 589), (227, 242), (228, 474), (234, 860)]))) (.cut 0 (.e1 [(122, 145), (123, 249), (129, 247), (130, 218), (164, 162), (170, 198), (172, 198), (178, 162), (212, 218), (213, 247), (219, 249), (220, 145)] [(115, 259), (121, 231), (122, 256), (164, 204), (165, 255), (170, 179), (172, 179), (177, 255), (178, 204), (220, 256), (221, 231), (227, 259)]) (.e1 [(122, 160), (123, 240), (129, 248), (130, 198), (163, 360), (164, 167), (170, 195), (172, 195), (178, 167), (179, 360), (212, 198), (213, 248), (219, 240), (220, 160)] [(114, 444), (115, 243), (116, 620), (121, 217), (122, 260), (164, 210), (165, 255), (170, 194), (172, 194), (177, 255), (178, 210), (214, 602), (220, 260), (221, 217), (226, 620), (227, 243), (228, 444)]))) (.cut 4 (.e1 [(122, 160), (123, 237), (129, 247), (130, 187), (164, 170), (170, 205), (172, 205), (178, 170), (179, 367), (212, 187), (213, 247), (219, 237), (220, 160)] [(115, 241), (121, 210), (122, 274), (164, 215), (165, 246), (170, 196), (172, 196), (177, 246), (178, 215), (220, 274), (221, 210), (227, 241)]) (.e1 [(122, 160), (123, 233), (129, 247), (130, 191), (164, 170), (170, 202), (172, 202), (178, 170), (179, 371), (212, 191), (213, 247), (219, 233), (220, 160)] [(114, 432), (115, 242), (121, 212), (122, 272), (164, 211), (165, 252), (170, 196), (172, 196), (177, 252), (178, 211), (220, 272), (221, 212), (227, 242), (228, 432)])))))) (.cut 0 (.e1 [(122, 134), (129, 238), (130, 244), (164, 156), (170, 213), (172, 213), (178, 156), (212, 244), (213, 238), (219, 229), (220, 134)] [(115, 281), (121, 229), (122, 274), (164, 193), (165, 274), (170, 163), (172, 163), (177, 274), (178, 193), (220, 274), (221, 229), (227, 281)]) (.cut 2 (.cut 1 (.e1 [(122, 157), (123, 233), (129, 257), (130, 255), (164, 132), (170, 198), (172, 198), (178, 132), (212, 255), (213, 257), (219, 233), (220, 157)] [(115, 289), (121, 215), (122, 229), (164, 206), (165, 305), (170, 168), (172, 168), (177, 305), (178, 206), (220, 229), (221, 215), (227, 289)]) (.e1 [(122, 154), (123, 217), (129, 270), (130, 239), (163, 376), (164, 151), (170, 190), (172, 190), (178, 151), (179, 376), (212, 239), (213, 270), (219, 217), (220, 154)] [(115, 280), (121, 215), (122, 242), (164, 191), (165, 288), (170, 185), (172, 185), (177, 288), (178, 191), (220, 242), (221, 215), (227, 280), (228, 437)])) (.cut 1 (.e1 [(122, 157), (123, 225), (129, 230), (130, 228), (164, 150), (170, 207), (172, 207), (178, 150), (212, 228), (213, 230), (219, 225), (220, 157)] [(115, 262), (121, 214), (122, 263), (164, 207), (165, 291), (170, 173), (172, 173), (177, 291), (178, 207), (220, 263), (221, 214), (227, 262)]) (.cut 3 (.e1 [(122, 160), (123, 224), (129, 247), (130, 215), (164, 170), (170, 183), (172, 183), (178, 170), (212, 215), (213, 247), (219, 224), (220, 160)] [(115, 245), (121, 222), (122, 258), (164, 194), (165, 276), (170, 196), (172, 196), (177, 276), (178, 194), (220, 258), (221, 222), (227, 245)]) (.e1 [(122, 160), (123, 219), (129, 247), (130, 213), (164, 170), (170, 187), (172, 187), (178, 170), (212, 213), (213, 247), (219, 219), (220, 160)] [(115, 247), (121, 218), (122, 263), (164, 194), (165, 276), (170, 196), (172, 196), (177, 276), (178, 194), (220, 263), (221, 218), (227, 247), (228, 411)]))))))

theorem plan684_0_ok : plan684_0.checkAt
    ((rootAddress ![2, 2] ![2, 3, 0]).child false)
    (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 false) = true := by decide +kernel

def plan684_1 : Plan :=
  (.cut 1 (.e1 [(122, 134), (123, 244), (129, 265), (130, 211), (163, 342), (164, 167), (170, 211), (172, 211), (178, 167), (179, 342), (212, 211), (213, 265), (219, 244), (220, 134)] [(115, 275), (121, 228), (122, 269), (164, 200), (165, 234), (170, 180), (172, 180), (177, 234), (178, 200), (220, 269), (221, 228), (227, 275), (228, 475)]) (.e1 [(122, 134), (123, 233), (129, 282), (130, 203), (163, 334), (164, 184), (170, 201), (172, 201), (178, 184), (179, 334), (212, 203), (213, 282), (219, 233), (220, 134)] [(115, 268), (116, 641), (121, 230), (122, 273), (128, 548), (164, 189), (165, 225), (170, 197), (172, 197), (177, 225), (178, 189), (214, 548), (220, 273), (221, 230), (226, 641), (227, 268), (228, 481)]))

theorem plan684_1_ok : plan684_1.checkAt
    ((((rootAddress ![2, 2] ![2, 3, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 false) 0 false) = true := by decide +kernel

def plan684_2 : Plan :=
  (.cut 4 (.cut 1 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 253), (129, 287), (130, 200), (163, 303), (164, 168), (170, 201), (172, 201), (178, 168), (179, 303), (212, 200), (213, 287), (219, 253), (220, 145)] [(115, 269), (121, 225), (122, 247), (164, 207), (165, 226), (170, 196), (172, 196), (177, 226), (178, 207), (220, 247), (221, 225), (227, 269)]) (.cut 2 (.cut 1 (.e1 [(122, 160), (123, 251), (129, 293), (130, 197), (163, 296), (164, 158), (170, 197), (172, 197), (178, 158), (179, 296), (212, 197), (213, 293), (219, 251), (220, 160)] [(115, 266), (121, 215), (122, 233), (164, 216), (165, 235), (170, 203), (172, 203), (177, 235), (178, 216), (214, 527), (220, 233), (221, 215), (227, 266)]) (.cut 4 (.e1 [(81, 667), (115, 609), (121, 709), (122, 158), (123, 252), (129, 300), (130, 191), (163, 287), (164, 168), (170, 194), (172, 194), (178, 168), (179, 287), (212, 191), (213, 300), (219, 252), (220, 158), (221, 709), (227, 609), (261, 667)] [(114, 539), (115, 261), (116, 598), (121, 219), (122, 236), (128, 517), (164, 213), (165, 225), (170, 212), (172, 212), (177, 225), (178, 213), (214, 517), (220, 236), (221, 219), (226, 598), (227, 261), (228, 539)]) (.e1 [(122, 160), (123, 242), (129, 301), (130, 198), (163, 297), (164, 166), (170, 188), (172, 188), (178, 166), (179, 297), (212, 198), (213, 301), (219, 242), (220, 160)] [(114, 525), (115, 262), (121, 218), (122, 234), (128, 515), (164, 206), (165, 235), (170, 212), (172, 212), (177, 235), (178, 206), (214, 515), (220, 234), (221, 218), (227, 262), (228, 525)]))) (.cut 1 (.cut 4 (.e1 [(122, 160), (123, 257), (129, 279), (130, 190), (163, 302), (164, 166), (170, 194), (172, 194), (178, 166), (179, 302), (212, 190), (213, 279), (219, 257), (220, 160)] [(115, 251), (121, 219), (122, 241), (164, 217), (165, 231), (170, 205), (172, 205), (177, 231), (178, 217), (220, 241), (221, 219), (227, 251), (228, 516)]) (.e1 [(122, 160), (123, 253), (129, 279), (130, 194), (163, 307), (164, 166), (170, 190), (172, 190), (178, 166), (179, 307), (212, 194), (213, 279), (219, 253), (220, 160)] [(115, 251), (121, 221), (122, 239), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (220, 239), (221, 221), (227, 251), (228, 510)])) (.cut 4 (.e1 [(81, 649), (115, 638), (122, 160), (123, 253), (129, 287), (130, 185), (163, 298), (164, 175), (170, 190), (172, 190), (178, 175), (179, 298), (212, 185), (213, 287), (219, 253), (220, 160), (227, 638), (261, 649)] [(114, 521), (115, 247), (116, 595), (121, 221), (122, 243), (128, 536), (164, 212), (165, 226), (170, 215), (172, 215), (177, 226), (178, 212), (214, 536), (220, 243), (221, 221), (226, 595), (227, 247), (228, 521)]) (.e1 [(81, 651), (115, 632), (122, 158), (123, 246), (129, 287), (130, 192), (163, 306), (164, 173), (170, 188), (172, 188), (178, 173), (179, 306), (212, 192), (213, 287), (219, 246), (220, 158), (227, 632), (261, 651)] [(114, 510), (115, 251), (116, 607), (121, 221), (122, 243), (128, 536), (164, 207), (165, 233), (170, 212), (172, 212), (177, 233), (178, 207), (214, 536), (220, 243), (221, 221), (226, 607), (227, 251), (228, 510)]))))) (.e1 [(81, 614), (115, 625), (121, 745), (122, 157), (123, 228), (129, 287), (130, 187), (131, 746), (137, 743), (163, 329), (164, 171), (165, 672), (170, 202), (172, 202), (177, 672), (178, 171), (179, 329), (205, 743), (211, 746), (212, 187), (213, 287), (219, 228), (220, 157), (221, 745), (227, 625), (261, 614)] [(114, 481), (115, 258), (116, 645), (120, 763), (121, 207), (122, 260), (127, 817), (128, 537), (164, 206), (165, 234), (170, 209), (172, 209), (177, 234), (178, 206), (184, 864), (214, 537), (215, 817), (220, 260), (221, 207), (222, 763), (226, 645), (227, 258), (228, 481)])) (.cut 3 (.cut 0 (.e1 [(122, 148), (123, 244), (129, 301), (130, 192), (163, 295), (164, 181), (170, 193), (172, 193), (178, 181), (179, 295), (212, 192), (213, 301), (219, 244), (220, 148)] [(115, 261), (121, 225), (122, 249), (164, 201), (165, 220), (170, 213), (172, 213), (177, 220), (178, 201), (220, 249), (221, 225), (227, 261)]) (.cut 4 (.cut 2 (.cut 1 (.cut 3 (.e1 [(122, 160), (123, 255), (129, 309), (130, 184), (163, 274), (164, 178), (170, 188), (172, 188), (178, 178), (179, 274), (212, 184), (213, 309), (219, 255), (220, 160)] [(114, 557), (115, 253), (121, 223), (122, 234), (128, 505), (164, 212), (165, 217), (170, 224), (172, 224), (177, 217), (178, 212), (214, 505), (220, 234), (221, 223), (227, 253), (228, 557)]) (.e1 [(122, 160), (123, 241), (129, 310), (130, 181), (163, 289), (164, 175), (170, 196), (172, 196), (178, 175), (179, 289), (212, 181), (213, 310), (219, 241), (220, 160)] [(115, 258), (121, 212), (122, 244), (128, 504), (164, 211), (165, 221), (170, 222), (172, 222), (177, 221), (178, 211), (214, 504), (220, 244), (221, 212), (227, 258)])) (.redProjected 0 1)) (.cut 1 (.cut 3 (.e1 [(115, 639), (122, 160), (123, 251), (129, 297), (130, 181), (131, 699), (163, 289), (164, 180), (170, 188), (172, 188), (178, 180), (179, 289), (211, 699), (212, 181), (213, 297), (219, 251), (220, 160), (227, 639)] [(114, 533), (115, 247), (116, 597), (121, 221), (122, 243), (128, 522), (164, 211), (165, 221), (170, 222), (172, 222), (177, 221), (178, 211), (214, 522), (220, 243), (221, 221), (226, 597), (227, 247), (228, 533)]) (.e1 [(122, 160), (123, 241), (129, 297), (130, 176), (163, 302), (164, 180), (170, 196), (172, 196), (178, 180), (179, 302), (212, 176), (213, 297), (219, 241), (220, 160)] [(115, 248), (121, 212), (122, 254), (128, 523), (164, 211), (165, 221), (170, 222), (172, 222), (177, 221), (178, 211), (214, 523), (220, 254), (221, 212), (227, 248), (228, 514)])) (.redProjected 0 1))) (.cut 2 (.cut 1 (.e1 [(122, 160), (123, 238), (129, 310), (130, 194), (163, 293), (164, 175), (170, 184), (172, 184), (178, 175), (179, 293), (212, 194), (213, 310), (219, 238), (220, 160)] [(114, 529), (115, 258), (116, 623), (121, 219), (122, 236), (128, 503), (164, 201), (165, 231), (170, 222), (172, 222), (177, 231), (178, 201), (214, 503), (220, 236), (221, 219), (226, 623), (227, 258), (228, 529)]) (.redProjected 0 1)) (.cut 1 (.cut 3 (.e1 [(122, 160), (123, 243), (129, 297), (130, 191), (163, 299), (164, 180), (170, 180), (172, 180), (178, 180), (179, 299), (212, 191), (213, 297), (219, 243), (220, 160)] [(114, 520), (115, 248), (121, 224), (122, 240), (128, 522), (164, 201), (165, 231), (170, 222), (172, 222), (177, 231), (178, 201), (214, 522), (220, 240), (221, 224), (227, 248), (228, 520)]) (.e1 [(122, 160), (123, 233), (129, 297), (130, 186), (163, 312), (164, 180), (170, 188), (172, 188), (178, 180), (179, 312), (212, 186), (213, 297), (219, 233), (220, 160)] [(115, 250), (121, 215), (122, 250), (164, 201), (165, 231), (170, 222), (172, 222), (177, 231), (178, 201), (220, 250), (221, 215), (227, 250)])) (.redProjected 0 1))))) (.cut 0 (.e1 [(122, 145), (123, 231), (130, 186), (163, 314), (164, 180), (170, 205), (172, 205), (178, 180), (179, 314), (212, 186), (213, 300), (219, 231), (220, 145)] [(115, 266), (121, 215), (122, 267), (164, 200), (165, 219), (170, 210), (172, 210), (177, 219), (178, 200), (220, 267), (221, 215), (227, 266)]) (.e1 [(122, 157), (123, 226), (129, 306), (130, 178), (163, 312), (164, 181), (170, 199), (172, 199), (178, 181), (179, 312), (212, 178), (213, 306), (219, 226), (220, 157)] [(114, 501), (115, 256), (121, 207), (122, 261), (128, 510), (164, 203), (165, 223), (170, 223), (172, 223), (177, 223), (178, 203), (214, 510), (220, 261), (221, 207), (227, 256), (228, 501)])))) (.cut 1 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 238), (129, 287), (130, 219), (163, 322), (164, 168), (170, 187), (172, 187), (178, 168), (179, 322), (212, 219), (213, 287), (219, 238), (220, 145)] [(115, 271), (121, 230), (122, 242), (164, 191), (165, 246), (170, 196), (172, 196), (177, 246), (178, 191), (220, 242), (221, 230), (227, 271)]) (.cut 2 (.e1 [(122, 160), (123, 230), (129, 298), (130, 203), (163, 315), (164, 167), (170, 185), (172, 185), (178, 167), (179, 315), (212, 203), (213, 298), (219, 230), (220, 160)] [(115, 262), (121, 215), (122, 238), (164, 198), (165, 246), (170, 212), (172, 212), (177, 246), (178, 198), (220, 238), (221, 215), (227, 262)]) (.e1 [(122, 160), (123, 230), (129, 285), (130, 198), (163, 328), (164, 173), (170, 185), (172, 185), (178, 173), (179, 328), (212, 198), (213, 285), (219, 230), (220, 160)] [(114, 481), (115, 252), (116, 640), (121, 216), (122, 247), (128, 539), (164, 198), (165, 246), (170, 212), (172, 212), (177, 246), (178, 198), (214, 539), (220, 247), (221, 216), (226, 640), (227, 252), (228, 481)]))) (.e1 [(122, 160), (123, 223), (129, 287), (130, 191), (163, 335), (164, 175), (170, 191), (172, 191), (178, 175), (179, 335), (212, 191), (213, 287), (219, 223), (220, 160)] [(115, 253), (121, 209), (122, 257), (164, 199), (165, 242), (170, 215), (172, 215), (177, 242), (178, 199), (220, 257), (221, 209), (227, 253)])) (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 230), (129, 294), (130, 211), (164, 183), (170, 179), (172, 179), (178, 183), (179, 322), (212, 211), (213, 294), (219, 230), (220, 145)] [(115, 261), (121, 233), (122, 249), (164, 183), (165, 240), (170, 210), (172, 210), (177, 240), (178, 183), (220, 249), (221, 233), (227, 261)]) (.redProjected 0 1)) (.e1 [(122, 154), (123, 209), (129, 303), (130, 195), (163, 336), (164, 184), (170, 187), (172, 187), (178, 184), (179, 336), (212, 195), (213, 303), (219, 209), (220, 154)] [(114, 472), (115, 260), (121, 211), (122, 263), (128, 513), (164, 185), (165, 240), (170, 222), (172, 222), (177, 240), (178, 185), (214, 513), (220, 263), (221, 211), (227, 260), (228, 472)]))))

theorem plan684_2_ok : plan684_2.checkAt
    (((((rootAddress ![2, 2] ![2, 3, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 false) 0 true) 2 false) = true := by decide +kernel

def plan684_3 : Plan :=
  (.cut 1 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 253), (129, 264), (130, 191), (163, 327), (164, 178), (170, 201), (172, 201), (178, 178), (179, 327), (212, 191), (213, 264), (219, 253), (220, 145)] [(115, 250), (121, 227), (122, 266), (164, 207), (165, 226), (170, 196), (172, 196), (177, 226), (178, 207), (220, 266), (221, 227), (227, 250)]) (.cut 1 (.cut 2 (.cut 4 (.e1 [(122, 160), (123, 257), (129, 267), (130, 185), (163, 315), (164, 172), (170, 194), (172, 194), (178, 172), (179, 315), (212, 185), (213, 267), (219, 257), (220, 160)] [(114, 498), (115, 241), (121, 220), (122, 251), (164, 217), (165, 231), (170, 205), (172, 205), (177, 231), (178, 217), (220, 251), (221, 220), (227, 241), (228, 498)]) (.e1 [(122, 160), (123, 253), (129, 267), (130, 189), (163, 319), (164, 172), (170, 190), (172, 190), (178, 172), (179, 319), (212, 189), (213, 267), (219, 253), (220, 160)] [(114, 492), (115, 242), (121, 221), (122, 249), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (220, 249), (221, 221), (227, 242), (228, 492)])) (.cut 4 (.e1 [(122, 160), (123, 257), (129, 261), (130, 182), (163, 322), (164, 175), (170, 194), (172, 194), (178, 175), (179, 322), (212, 182), (213, 261), (219, 257), (220, 160), (261, 619)] [(114, 488), (115, 237), (121, 221), (122, 256), (128, 579), (164, 217), (165, 231), (170, 205), (172, 205), (177, 231), (178, 217), (214, 579), (220, 256), (221, 221), (227, 237), (228, 488)]) (.e1 [(122, 160), (123, 253), (129, 255), (130, 184), (163, 333), (164, 179), (170, 190), (172, 190), (178, 179), (179, 333), (212, 184), (213, 255), (219, 253), (220, 160)] [(114, 474), (115, 233), (121, 223), (122, 259), (128, 589), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (214, 589), (220, 259), (221, 223), (226, 593), (227, 233), (228, 474)]))) (.cut 4 (.cut 2 (.cut 3 (.e1 [(74, 894), (81, 635), (115, 649), (121, 699), (122, 158), (123, 256), (129, 278), (130, 183), (131, 727), (137, 720), (163, 304), (164, 177), (165, 689), (170, 191), (172, 191), (177, 689), (178, 177), (179, 304), (205, 720), (211, 727), (212, 183), (213, 278), (219, 256), (220, 158), (221, 699), (227, 649), (260, 957), (261, 635), (268, 894)] [(65, 897), (66, 961), (72, 921), (108, 856), (109, 906), (114, 512), (115, 243), (116, 589), (120, 812), (121, 222), (122, 248), (123, 890), (127, 844), (128, 551), (129, 873), (158, 858), (163, 817), (164, 213), (165, 225), (166, 853), (170, 212), (172, 212), (176, 853), (177, 225), (178, 213), (179, 817), (184, 858), (213, 873), (214, 551), (215, 844), (219, 890), (220, 248), (221, 222), (222, 812), (226, 589), (227, 243), (228, 512), (233, 906), (234, 856), (270, 921), (276, 961), (277, 897)]) (.e1 [(122, 160), (123, 245), (129, 281), (130, 179), (163, 314), (164, 178), (170, 195), (172, 195), (178, 178), (179, 314), (212, 179), (213, 281), (219, 245), (220, 160)] [(115, 244), (121, 214), (122, 256), (164, 212), (165, 226), (170, 215), (172, 215), (177, 226), (178, 212), (220, 256), (221, 214), (227, 244)])) (.e1 [(122, 160), (123, 253), (129, 269), (130, 178), (163, 317), (164, 184), (170, 190), (172, 190), (178, 184), (179, 317), (212, 178), (213, 269), (219, 253), (220, 160)] [(114, 493), (115, 233), (121, 222), (122, 258), (164, 212), (165, 226), (170, 215), (172, 215), (177, 226), (178, 212), (214, 566), (220, 258), (221, 222), (227, 233), (228, 493)])) (.cut 2 (.cut 3 (.e1 [(122, 160), (123, 251), (129, 275), (130, 186), (163, 312), (164, 181), (170, 184), (172, 184), (178, 181), (179, 312), (212, 186), (213, 275), (219, 251), (220, 160)] [(114, 501), (115, 238), (121, 225), (122, 248), (164, 207), (165, 232), (170, 215), (172, 215), (177, 232), (178, 207), (220, 248), (221, 225), (227, 238), (228, 501)]) (.e1 [(122, 160), (123, 237), (129, 276), (130, 185), (163, 329), (164, 177), (170, 192), (172, 192), (178, 177), (179, 329), (212, 185), (213, 276), (219, 237), (220, 160)] [(114, 480), (115, 244), (121, 214), (122, 258), (164, 206), (165, 235), (170, 212), (172, 212), (177, 235), (178, 206), (220, 258), (221, 214), (227, 244), (228, 480)])) (.e1 [(81, 611), (115, 673), (121, 703), (122, 158), (123, 246), (129, 266), (130, 183), (131, 732), (137, 743), (163, 329), (164, 183), (165, 669), (170, 188), (172, 188), (177, 669), (178, 183), (179, 329), (205, 743), (211, 732), (212, 183), (213, 266), (219, 246), (220, 158), (221, 703), (227, 673), (261, 611)] [(114, 479), (115, 235), (116, 607), (121, 222), (122, 260), (128, 571), (164, 207), (165, 233), (170, 212), (172, 212), (177, 233), (178, 207), (214, 571), (220, 260), (221, 222), (226, 607), (227, 235), (228, 479), (234, 816)]))))) (.cut 0 (.e1 [(122, 145), (123, 233), (129, 264), (130, 183), (164, 178), (170, 216), (172, 216), (178, 178), (179, 354), (212, 183), (213, 264), (219, 233), (220, 145)] [(115, 255), (121, 212), (122, 288), (164, 207), (165, 226), (170, 196), (172, 196), (177, 226), (178, 207), (220, 288), (221, 212), (227, 255)]) (.e1 [(81, 573), (115, 678), (122, 160), (123, 227), (129, 264), (130, 177), (137, 749), (163, 357), (164, 183), (165, 666), (170, 200), (172, 200), (177, 666), (178, 183), (179, 357), (205, 749), (212, 177), (213, 264), (219, 227), (220, 160), (227, 678), (261, 573)] [(114, 446), (115, 238), (116, 646), (120, 753), (121, 208), (122, 279), (128, 575), (164, 206), (165, 235), (170, 212), (172, 212), (177, 235), (178, 206), (214, 575), (220, 279), (221, 208), (222, 753), (226, 646), (227, 238), (228, 446)]))) (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 238), (129, 264), (130, 210), (163, 346), (164, 178), (170, 187), (172, 187), (178, 178), (179, 346), (212, 210), (213, 264), (219, 238), (220, 145)] [(115, 253), (121, 232), (122, 259), (164, 191), (165, 246), (170, 196), (172, 196), (177, 246), (178, 191), (220, 259), (221, 232), (227, 253), (228, 463)]) (.cut 1 (.cut 2 (.e1 [(122, 160), (123, 234), (129, 267), (130, 196), (163, 344), (164, 172), (170, 189), (172, 189), (178, 172), (179, 344), (212, 196), (213, 267), (219, 234), (220, 160)] [(114, 461), (115, 246), (116, 632), (121, 217), (122, 255), (128, 569), (164, 202), (165, 249), (170, 205), (172, 205), (177, 249), (178, 202), (214, 569), (220, 255), (221, 217), (226, 632), (227, 246), (228, 461)]) (.cut 4 (.e1 [(122, 160), (123, 240), (129, 256), (130, 196), (163, 349), (164, 175), (170, 186), (172, 186), (178, 175), (179, 349), (212, 196), (213, 256), (219, 240), (220, 160)] [(114, 456), (115, 238), (121, 222), (122, 256), (128, 588), (164, 204), (165, 251), (170, 203), (172, 203), (177, 251), (178, 204), (214, 588), (220, 256), (221, 222), (227, 238), (228, 456)]) (.e1 [(122, 160), (123, 233), (129, 256), (130, 206), (163, 359), (164, 175), (170, 179), (172, 179), (178, 175), (179, 359), (212, 206), (213, 256), (219, 233), (220, 160)] [(115, 240), (121, 225), (122, 253), (164, 196), (165, 262), (170, 203), (172, 203), (177, 262), (178, 196), (220, 253), (221, 225), (227, 240), (228, 446)]))) (.cut 4 (.cut 2 (.e1 [(122, 160), (123, 235), (129, 276), (130, 197), (163, 332), (164, 177), (170, 181), (172, 181), (178, 177), (179, 332), (212, 197), (213, 276), (219, 235), (220, 160)] [(114, 477), (115, 244), (121, 221), (122, 249), (164, 198), (165, 246), (170, 212), (172, 212), (177, 246), (178, 198), (220, 249), (221, 221), (227, 244), (228, 477)]) (.e1 [(122, 160), (123, 235), (129, 264), (130, 192), (163, 345), (164, 183), (170, 181), (172, 181), (178, 183), (179, 345), (212, 192), (213, 264), (219, 235), (220, 160)] [(114, 460), (115, 235), (121, 223), (122, 258), (164, 198), (165, 246), (170, 212), (172, 212), (177, 246), (178, 198), (220, 258), (221, 223), (227, 235), (228, 460)])) (.redProjected 0 1)))) (.e1 [(122, 157), (123, 221), (129, 263), (130, 188), (163, 367), (164, 183), (170, 194), (172, 194), (178, 183), (179, 367), (212, 188), (213, 263), (219, 221), (220, 157)] [(115, 242), (121, 213), (122, 276), (164, 198), (165, 245), (170, 209), (172, 209), (177, 245), (178, 198), (220, 276), (221, 213), (227, 242), (228, 436)]))) (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 251), (129, 276), (130, 186), (163, 314), (164, 191), (170, 191), (172, 191), (178, 191), (179, 314), (212, 186), (213, 276), (219, 251), (220, 145)] [(115, 244), (121, 232), (122, 264), (164, 200), (165, 219), (170, 210), (172, 210), (177, 219), (178, 200), (220, 264), (221, 232), (227, 244)]) (.cut 4 (.cut 1 (.cut 2 (.cut 3 (.e1 [(115, 658), (122, 158), (123, 252), (129, 286), (130, 179), (163, 300), (164, 186), (170, 187), (172, 187), (178, 186), (179, 300), (212, 179), (213, 286), (219, 252), (220, 158), (227, 658), (261, 631)] [(114, 517), (115, 240), (116, 596), (121, 223), (122, 250), (128, 538), (164, 208), (165, 221), (170, 221), (172, 221), (177, 221), (178, 208), (214, 538), (220, 250), (221, 223), (226, 596), (227, 240), (228, 517)]) (.e1 [(122, 157), (123, 240), (129, 283), (130, 176), (163, 318), (164, 185), (170, 195), (172, 195), (178, 185), (179, 318), (212, 176), (213, 283), (219, 240), (220, 157)] [(114, 492), (115, 242), (121, 215), (122, 264), (164, 207), (165, 222), (170, 218), (172, 218), (177, 222), (178, 207), (220, 264), (221, 215), (227, 242), (228, 492)])) (.e1 [(122, 160), (123, 250), (129, 273), (130, 176), (163, 315), (164, 188), (170, 187), (172, 187), (178, 188), (179, 315), (212, 176), (213, 273), (219, 250), (220, 160)] [(114, 496), (115, 232), (121, 222), (122, 259), (164, 209), (165, 224), (170, 219), (172, 219), (177, 224), (178, 209), (220, 259), (221, 222), (227, 232), (228, 496)])) (.redProjected 0 1)) (.cut 1 (.cut 2 (.cut 3 (.e1 [(122, 160), (123, 243), (129, 284), (130, 186), (163, 312), (164, 185), (170, 180), (172, 180), (178, 185), (179, 312), (212, 186), (213, 284), (219, 243), (220, 160)] [(114, 502), (115, 239), (121, 224), (122, 249), (128, 541), (164, 201), (165, 231), (170, 222), (172, 222), (177, 231), (178, 201), (214, 541), (220, 249), (221, 224), (226, 611), (227, 239), (228, 502)]) (.e1 [(122, 160), (123, 233), (129, 284), (130, 181), (163, 325), (164, 185), (170, 188), (172, 188), (178, 185), (179, 325), (212, 181), (213, 284), (219, 233), (220, 160)] [(115, 241), (121, 215), (122, 260), (164, 201), (165, 231), (170, 222), (172, 222), (177, 231), (178, 201), (220, 260), (221, 215), (227, 241), (228, 484)])) (.e1 [(122, 158), (123, 243), (129, 272), (130, 180), (163, 326), (164, 190), (170, 184), (172, 184), (178, 190), (179, 326), (212, 180), (213, 272), (219, 243), (220, 158)] [(114, 482), (115, 233), (121, 223), (122, 261), (128, 561), (164, 203), (165, 230), (170, 219), (172, 219), (177, 230), (178, 203), (214, 561), (220, 261), (221, 223), (226, 613), (227, 233), (228, 482)])) (.redProjected 0 1)))) (.e1 [(122, 154), (123, 223), (129, 281), (130, 175), (163, 343), (164, 188), (170, 201), (172, 201), (178, 188), (179, 343), (212, 175), (213, 281), (219, 223), (220, 154), (261, 572)] [(114, 462), (115, 245), (116, 656), (121, 209), (122, 281), (128, 549), (164, 201), (165, 225), (170, 217), (172, 217), (177, 225), (178, 201), (214, 549), (220, 281), (221, 209), (226, 656), (227, 245), (228, 462)])) (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 234), (129, 276), (130, 199), (164, 191), (170, 182), (172, 182), (178, 191), (179, 336), (212, 199), (213, 276), (219, 234), (220, 145)] [(115, 247), (121, 233), (122, 264), (164, 187), (165, 235), (170, 210), (172, 210), (177, 235), (178, 187), (220, 264), (221, 233), (227, 247)]) (.redProjected 0 1)) (.e1 [(122, 157), (123, 216), (129, 283), (130, 188), (163, 349), (164, 185), (170, 189), (172, 189), (178, 185), (179, 349), (212, 188), (213, 283), (219, 216), (220, 157)] [(114, 455), (115, 248), (121, 211), (122, 269), (164, 192), (165, 241), (170, 218), (172, 218), (177, 241), (178, 192), (220, 269), (221, 211), (227, 248), (228, 455)]))))

theorem plan684_3_ok : plan684_3.checkAt
    (((((rootAddress ![2, 2] ![2, 3, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 false) 0 true) 2 true) = true := by decide +kernel

def plan684_n0 : Plan := .cut 2 plan684_2 plan684_3

theorem plan684_n0_ok : plan684_n0.checkAt
    ((((rootAddress ![2, 2] ![2, 3, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 false) 0 true) = true :=
  checkAt_cut 2 plan684_2 plan684_3
    ((((rootAddress ![2, 2] ![2, 3, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 false) 0 true)
    (by decide +kernel) plan684_2_ok plan684_3_ok

def plan684_n1 : Plan := .cut 0 plan684_1 plan684_n0

theorem plan684_n1_ok : plan684_n1.checkAt
    (((rootAddress ![2, 2] ![2, 3, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 false) = true :=
  checkAt_cut 0 plan684_1 plan684_n0
    (((rootAddress ![2, 2] ![2, 3, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 false)
    (by decide +kernel) plan684_1_ok plan684_n0_ok

def plan684_4 : Plan :=
  (.cut 0 (.e1 [(122, 134), (123, 213), (129, 274), (130, 250), (164, 176), (170, 180), (172, 180), (178, 176), (212, 250), (213, 274), (219, 213), (220, 134)] [(115, 280), (121, 239), (122, 259), (164, 167), (165, 274), (170, 188), (172, 188), (177, 274), (178, 167), (220, 259), (221, 239), (227, 280)]) (.cut 2 (.cut 4 (.cut 1 (.e1 [(122, 154), (123, 209), (129, 286), (130, 224), (163, 360), (164, 167), (170, 182), (172, 182), (178, 167), (179, 360), (212, 224), (213, 286), (219, 209), (220, 154)] [(115, 271), (121, 216), (122, 249), (164, 182), (165, 271), (170, 203), (172, 203), (177, 271), (178, 182), (220, 249), (221, 216), (227, 271), (228, 448)]) (.redProjected 0 1)) (.e1 [(122, 151), (123, 201), (129, 294), (130, 248), (164, 172), (170, 166), (172, 166), (178, 172), (212, 248), (213, 294), (219, 201), (220, 151)] [(115, 276), (121, 227), (122, 240), (164, 166), (165, 289), (170, 207), (172, 207), (177, 289), (178, 166), (220, 240), (221, 227), (227, 276)])) (.cut 1 (.cut 4 (.cut 3 (.e1 [(122, 157), (123, 218), (129, 263), (130, 213), (164, 183), (170, 173), (172, 173), (178, 183), (179, 373), (212, 213), (213, 263), (219, 218), (220, 157)] [(115, 243), (121, 226), (122, 257), (164, 183), (165, 268), (170, 209), (172, 209), (177, 268), (178, 183), (220, 257), (221, 226), (227, 243), (228, 431)]) (.e1 [(122, 154), (123, 206), (129, 262), (130, 215), (164, 179), (170, 184), (172, 184), (178, 179), (212, 215), (213, 262), (219, 206), (220, 154)] [(114, 414), (115, 254), (121, 218), (122, 269), (164, 182), (165, 271), (170, 203), (172, 203), (177, 271), (178, 182), (220, 269), (221, 218), (227, 254), (228, 414)])) (.e1 [(122, 151), (123, 207), (129, 262), (130, 242), (164, 175), (170, 172), (172, 172), (178, 175), (212, 242), (213, 262), (219, 207), (220, 151)] [(115, 261), (121, 230), (122, 253), (164, 173), (165, 292), (170, 198), (172, 198), (177, 292), (178, 173), (220, 253), (221, 230), (227, 261)])) (.redProjected 0 1))))

theorem plan684_4_ok : plan684_4.checkAt
    (((rootAddress ![2, 2] ![2, 3, 0]).child true).child true)
    (childBox (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) 4 true) = true := by decide +kernel

def plan684_n2 : Plan := .cut 4 plan684_n1 plan684_4

theorem plan684_n2_ok : plan684_n2.checkAt
    ((rootAddress ![2, 2] ![2, 3, 0]).child true)
    (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true) = true :=
  checkAt_cut 4 plan684_n1 plan684_4
    ((rootAddress ![2, 2] ![2, 3, 0]).child true)
    (childBox (rootBox ![2, 2] ![2, 3, 0]) 1 true)
    (by decide +kernel) plan684_n1_ok plan684_4_ok

def plan684 : Plan := .cut 1 plan684_0 plan684_n2

theorem plan684_ok : plan684.checkAt
    (rootAddress ![2, 2] ![2, 3, 0])
    (rootBox ![2, 2] ![2, 3, 0]) = true :=
  checkAt_cut 1 plan684_0 plan684_n2
    (rootAddress ![2, 2] ![2, 3, 0])
    (rootBox ![2, 2] ![2, 3, 0])
    (by decide +kernel) plan684_0_ok plan684_n2_ok

theorem root684 : rootCheck plan684 ![2, 2] ![2, 3, 0] = true := plan684_ok

def plan685 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 197), (129, 245), (130, 286), (164, 158), (170, 180), (172, 180), (178, 158), (212, 286), (213, 245), (219, 197), (220, 151)] [(115, 283), (121, 230), (122, 248), (164, 172), (170, 180), (172, 180), (177, 345), (178, 172), (220, 248), (221, 230), (227, 283)]) (.e1 [(122, 157), (123, 182), (129, 255), (130, 263), (164, 174), (170, 173), (172, 173), (178, 174), (212, 263), (213, 255), (219, 182), (220, 157)] [(115, 270), (121, 222), (122, 260), (164, 165), (170, 200), (172, 200), (178, 165), (220, 260), (221, 222), (227, 270)]))

theorem root685 : rootCheck plan685 ![2, 2] ![2, 3, 1] = true := by decide +kernel

def plan686 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 197), (129, 245), (164, 158), (165, 281), (170, 180), (172, 180), (177, 281), (178, 158), (213, 245), (219, 197), (220, 151)] [(114, 296), (121, 267), (122, 215), (164, 172), (170, 180), (172, 180), (178, 172), (220, 215), (221, 267), (227, 347), (228, 296)]) (.e1 [(122, 157), (123, 182), (129, 255), (164, 174), (165, 260), (170, 173), (172, 173), (177, 260), (178, 174), (213, 255), (219, 182), (220, 157)] [(114, 277), (121, 270), (122, 215), (164, 165), (170, 200), (172, 200), (178, 165), (220, 215), (221, 270), (228, 277)]))

theorem root686 : rootCheck plan686 ![2, 2] ![2, 3, 2] = true := by decide +kernel

def plan687 : Plan :=
  (.cut 1 (.cut 0 (.e1 [(122, 131), (123, 251), (129, 238), (164, 149), (165, 224), (170, 226), (172, 226), (177, 224), (178, 149), (213, 238), (219, 251), (220, 131)] [(114, 295), (121, 302), (122, 211), (163, 256), (164, 208), (170, 156), (172, 156), (178, 208), (179, 256), (220, 211), (221, 302), (227, 409), (228, 295)]) (.cut 4 (.e1 [(122, 160), (123, 208), (129, 248), (164, 167), (165, 208), (170, 199), (172, 199), (177, 208), (178, 167), (213, 248), (219, 208), (220, 160)] [(114, 260), (121, 285), (122, 201), (163, 277), (164, 196), (170, 194), (172, 194), (178, 196), (179, 277), (220, 201), (221, 285), (228, 260)]) (.cut 1 (.e1 [(122, 157), (123, 236), (129, 236), (164, 147), (165, 205), (170, 218), (172, 218), (177, 205), (178, 147), (213, 236), (219, 236), (220, 157)] [(114, 270), (121, 287), (122, 195), (163, 270), (164, 220), (170, 173), (172, 173), (178, 220), (179, 270), (220, 195), (221, 287), (228, 270)]) (.cut 0 (.e1 [(122, 145), (123, 246), (129, 258), (164, 156), (165, 196), (170, 212), (172, 212), (177, 196), (178, 156), (213, 258), (219, 246), (220, 145)] [(114, 283), (121, 303), (122, 194), (163, 246), (164, 211), (170, 179), (172, 179), (178, 211), (179, 246), (220, 194), (221, 303), (227, 414), (228, 283)]) (.cut 4 (.e1 [(122, 161), (123, 210), (129, 250), (164, 169), (165, 199), (170, 201), (172, 201), (177, 199), (178, 169), (213, 250), (219, 210), (220, 161)] [(114, 256), (121, 288), (122, 198), (163, 268), (164, 200), (170, 197), (172, 197), (178, 200), (179, 268), (220, 198), (221, 288), (227, 390), (228, 256)]) (.e1 [(122, 160), (123, 232), (129, 253), (164, 163), (165, 180), (170, 214), (172, 214), (177, 180), (178, 163), (213, 253), (219, 232), (220, 160)] [(114, 257), (121, 298), (122, 190), (163, 245), (164, 218), (170, 194), (172, 194), (178, 218), (179, 245), (220, 190), (221, 298), (228, 257)])))))) (.cut 4 (.cut 0 (.e1 [(122, 134), (123, 213), (129, 274), (164, 176), (165, 238), (170, 180), (172, 180), (177, 238), (178, 176), (213, 274), (219, 213), (220, 134)] [(114, 300), (121, 301), (122, 210), (163, 274), (164, 167), (170, 188), (172, 188), (178, 167), (179, 274), (220, 210), (221, 301), (228, 300)]) (.e1 [(116, 425), (122, 157), (123, 203), (129, 264), (164, 175), (165, 211), (170, 185), (172, 185), (177, 211), (178, 175), (213, 264), (219, 203), (220, 157), (226, 425)] [(114, 267), (115, 383), (121, 289), (122, 200), (129, 573), (163, 276), (164, 182), (170, 204), (172, 204), (178, 182), (179, 276), (213, 573), (220, 200), (221, 289), (227, 383), (228, 267)])) (.cut 0 (.e1 [(122, 131), (123, 237), (129, 271), (164, 182), (165, 190), (170, 213), (172, 213), (177, 190), (178, 182), (213, 271), (219, 237), (220, 131)] [(114, 279), (121, 320), (122, 209), (163, 221), (164, 195), (170, 189), (172, 189), (178, 195), (179, 221), (220, 209), (221, 320), (228, 279)]) (.cut 1 (.cut 0 (.e1 [(122, 145), (123, 235), (129, 275), (164, 173), (165, 187), (170, 201), (172, 201), (177, 187), (178, 173), (213, 275), (219, 235), (220, 145), (226, 392)] [(114, 277), (115, 416), (121, 310), (122, 194), (163, 236), (164, 199), (170, 196), (172, 196), (178, 199), (179, 236), (220, 194), (221, 310), (227, 416), (228, 277)]) (.cut 4 (.e1 [(122, 160), (123, 215), (129, 270), (164, 180), (165, 181), (170, 197), (172, 197), (177, 181), (178, 180), (213, 270), (219, 215), (220, 160), (226, 397)] [(114, 255), (121, 301), (122, 192), (163, 246), (164, 198), (170, 212), (172, 212), (178, 198), (179, 246), (220, 192), (221, 301), (227, 406), (228, 255)]) (.e1 [(116, 387), (122, 160), (123, 222), (129, 270), (164, 180), (165, 171), (170, 204), (172, 204), (177, 171), (178, 180), (213, 270), (219, 222), (220, 160), (226, 387)] [(114, 251), (121, 305), (122, 190), (163, 235), (164, 206), (170, 212), (172, 212), (178, 206), (179, 235), (220, 190), (221, 305), (228, 251)]))) (.cut 2 (.e1 [(116, 357), (122, 151), (123, 215), (129, 303), (164, 181), (165, 182), (170, 198), (172, 198), (177, 182), (178, 181), (213, 303), (219, 215), (220, 151), (226, 357)] [(114, 272), (121, 291), (122, 194), (163, 231), (164, 192), (170, 217), (172, 217), (178, 192), (179, 231), (213, 517), (220, 194), (221, 291), (227, 449), (228, 272)]) (.e1 [(116, 386), (122, 151), (123, 215), (129, 279), (164, 192), (165, 177), (170, 198), (172, 198), (177, 177), (178, 192), (213, 279), (219, 215), (220, 151), (226, 386)] [(114, 256), (121, 311), (122, 198), (163, 231), (164, 192), (170, 217), (172, 217), (178, 192), (179, 231), (220, 198), (221, 311), (227, 416), (228, 256)]))))))

theorem root687 : rootCheck plan687 ![2, 2] ![2, 3, 3] = true := by decide +kernel

def plan688 : Plan :=
  (.cut 0 (.cut 1 (.e1 [(122, 134), (129, 199), (130, 255), (163, 288), (164, 183), (170, 176), (172, 176), (178, 183), (179, 288), (212, 255), (213, 199), (220, 134)] [(115, 233), (121, 339), (122, 235), (164, 212), (165, 245), (170, 163), (172, 163), (177, 245), (178, 212), (220, 235), (221, 339), (227, 233)]) (.cut 4 (.e1 [(122, 131), (129, 232), (130, 243), (163, 259), (164, 208), (170, 161), (172, 161), (178, 208), (179, 259), (212, 243), (213, 232), (220, 131)] [(115, 235), (121, 352), (122, 228), (164, 195), (165, 221), (170, 189), (172, 189), (177, 221), (178, 195), (220, 228), (221, 352), (227, 235)]) (.e1 [(122, 128), (129, 231), (164, 199), (170, 142), (172, 142), (178, 199), (213, 231), (220, 128)] [(115, 239), (122, 218), (164, 172), (165, 259), (170, 182), (172, 182), (177, 259), (178, 172), (220, 218), (227, 239)]))) (.cut 4 (.cut 1 (.cut 1 (.cut 2 (.e1 [(122, 160), (129, 209), (130, 237), (163, 260), (164, 168), (170, 172), (172, 172), (178, 168), (179, 260), (212, 237), (213, 209), (220, 160)] [(115, 227), (122, 209), (164, 238), (165, 246), (170, 178), (172, 178), (177, 246), (178, 238), (220, 209), (221, 309), (227, 227)]) (.e1 [(122, 154), (129, 189), (130, 248), (163, 279), (164, 175), (170, 171), (172, 171), (178, 175), (179, 279), (212, 248), (213, 189), (220, 154)] [(115, 218), (121, 330), (122, 221), (164, 232), (165, 257), (170, 168), (172, 168), (177, 257), (178, 232), (220, 221), (221, 330), (226, 398), (227, 218)])) (.cut 2 (.e1 [(122, 157), (129, 225), (130, 240), (163, 249), (164, 180), (170, 160), (172, 160), (178, 180), (179, 249), (212, 240), (213, 225), (219, 391), (220, 157)] [(115, 228), (121, 323), (122, 204), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (220, 204), (221, 323), (227, 228)]) (.cut 3 (.e1 [(122, 157), (129, 205), (130, 236), (163, 254), (164, 196), (170, 158), (172, 158), (178, 196), (179, 254), (212, 236), (213, 205), (220, 157)] [(115, 213), (121, 345), (122, 215), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (220, 215), (221, 345), (226, 387), (227, 213)]) (.e1 [(122, 157), (129, 205), (130, 220), (163, 274), (164, 196), (170, 161), (172, 161), (178, 196), (179, 274), (212, 220), (213, 205), (220, 157)] [(115, 207), (116, 417), (121, 320), (122, 226), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (220, 226), (221, 320), (226, 417), (227, 207)])))) (.cut 4 (.cut 2 (.e1 [(121, 494), (122, 157), (123, 388), (129, 237), (130, 229), (163, 238), (164, 192), (170, 156), (172, 156), (178, 192), (179, 238), (212, 229), (213, 237), (219, 388), (220, 157), (221, 494)] [(115, 226), (116, 414), (121, 325), (122, 204), (128, 639), (164, 217), (165, 227), (170, 204), (172, 204), (177, 227), (178, 217), (214, 639), (220, 204), (221, 325), (226, 414), (227, 226)]) (.e1 [(121, 479), (122, 154), (123, 391), (129, 223), (130, 220), (163, 251), (164, 210), (170, 153), (172, 153), (178, 210), (179, 251), (212, 220), (213, 223), (219, 391), (220, 154), (221, 479)] [(115, 211), (116, 409), (121, 336), (122, 219), (164, 212), (165, 226), (170, 206), (172, 206), (177, 226), (178, 212), (219, 705), (220, 219), (221, 336), (226, 409), (227, 211)])) (.e1 [(122, 148), (129, 229), (130, 249), (163, 266), (164, 203), (170, 142), (172, 142), (178, 203), (179, 266), (212, 249), (213, 229), (220, 148)] [(115, 219), (121, 350), (122, 211), (164, 194), (165, 245), (170, 199), (172, 199), (177, 245), (178, 194), (220, 211), (221, 350), (227, 219)]))) (.e1 [(122, 145), (123, 373), (129, 220), (130, 299), (163, 299), (164, 186), (165, 596), (170, 134), (172, 134), (177, 596), (178, 186), (179, 299), (212, 299), (213, 220), (219, 373), (220, 145)] [(114, 569), (115, 227), (116, 443), (121, 371), (122, 203), (164, 182), (165, 287), (170, 183), (172, 183), (177, 287), (178, 182), (220, 203), (221, 371), (226, 443), (227, 227), (228, 569)])))

theorem root688 : rootCheck plan688 ![2, 2] ![3, 0, 0] = true := by decide +kernel

def plan689 : Plan :=
  (.e1 [(122, 134), (129, 204), (164, 179), (170, 133), (172, 133), (178, 179), (212, 363), (213, 204), (220, 134)] [(115, 232), (122, 213), (164, 169), (165, 347), (170, 163), (172, 163), (177, 347), (178, 169), (220, 213), (227, 232)])

theorem root689 : rootCheck plan689 ![2, 2] ![3, 0, 1] = true := by decide +kernel

def plan690 : Plan :=
  (.e1 [(122, 134), (129, 204), (164, 179), (170, 133), (172, 133), (178, 179), (213, 204), (220, 134)] [(115, 239), (122, 208), (163, 347), (164, 169), (170, 163), (172, 163), (178, 169), (179, 347), (220, 208), (227, 239)])

theorem root690 : rootCheck plan690 ![2, 2] ![3, 0, 2] = true := by decide +kernel

def plan691 : Plan :=
  (.cut 0 (.cut 1 (.e1 [(122, 134), (129, 199), (164, 183), (165, 255), (170, 174), (172, 174), (177, 255), (178, 183), (213, 199), (214, 288), (220, 134)] [(115, 246), (122, 219), (163, 245), (164, 212), (170, 163), (172, 163), (178, 212), (179, 245), (220, 219), (227, 246), (228, 368)]) (.cut 4 (.e1 [(122, 128), (129, 231), (164, 199), (170, 142), (172, 142), (178, 199), (213, 231), (220, 128)] [(115, 253), (122, 207), (163, 259), (164, 172), (170, 182), (172, 182), (178, 172), (179, 259), (220, 207), (227, 253)]) (.e1 [(122, 131), (128, 277), (129, 232), (164, 208), (165, 229), (170, 160), (172, 160), (177, 229), (178, 208), (213, 232), (214, 277), (220, 131)] [(115, 252), (122, 212), (163, 221), (164, 195), (170, 189), (172, 189), (178, 195), (179, 221), (220, 212), (227, 252), (228, 369)]))) (.cut 4 (.e1 [(122, 145), (128, 337), (129, 220), (164, 186), (165, 269), (170, 134), (172, 134), (177, 269), (178, 186), (213, 220), (214, 337), (220, 145)] [(114, 385), (115, 239), (122, 193), (163, 287), (164, 182), (170, 183), (172, 183), (178, 182), (179, 287), (220, 193), (227, 239), (228, 385)]) (.cut 2 (.cut 1 (.e1 [(122, 157), (128, 282), (129, 221), (164, 176), (165, 219), (170, 160), (172, 160), (177, 219), (178, 176), (213, 221), (214, 282), (220, 157)] [(115, 246), (122, 188), (163, 242), (164, 225), (170, 186), (172, 186), (178, 225), (179, 242), (220, 188), (227, 246), (228, 358)]) (.e1 [(122, 148), (128, 286), (129, 241), (164, 193), (165, 213), (170, 151), (172, 151), (177, 213), (178, 193), (213, 241), (214, 286), (220, 148)] [(114, 363), (115, 252), (122, 188), (123, 401), (163, 232), (164, 204), (170, 199), (172, 199), (178, 204), (179, 232), (219, 401), (220, 188), (227, 252), (228, 363)])) (.cut 1 (.e1 [(122, 157), (123, 428), (128, 261), (129, 201), (164, 192), (165, 234), (170, 160), (172, 160), (177, 234), (178, 192), (213, 201), (214, 261), (219, 428), (220, 157), (221, 463)] [(114, 352), (115, 224), (121, 598), (122, 205), (123, 377), (163, 242), (164, 225), (170, 186), (172, 186), (178, 225), (179, 242), (219, 377), (220, 205), (221, 598), (227, 224), (228, 352)]) (.cut 4 (.e1 [(122, 151), (128, 288), (129, 221), (164, 203), (165, 236), (170, 141), (172, 141), (177, 236), (178, 203), (213, 221), (214, 288), (220, 151)] [(115, 230), (122, 197), (163, 251), (164, 195), (170, 198), (172, 198), (178, 195), (179, 251), (220, 197), (227, 230)]) (.e1 [(122, 154), (128, 256), (129, 223), (164, 210), (165, 216), (170, 152), (172, 152), (177, 216), (178, 210), (213, 223), (214, 256), (220, 154)] [(114, 351), (115, 228), (122, 201), (163, 226), (164, 212), (170, 206), (172, 206), (178, 212), (179, 226), (219, 394), (220, 201), (227, 228), (228, 351)]))))))

theorem root691 : rootCheck plan691 ![2, 2] ![3, 0, 3] = true := by decide +kernel

def plan692 : Plan :=
  (.cut 1 (.cut 4 (.cut 0 (.e1 [(122, 131), (129, 199), (130, 237), (163, 318), (164, 174), (170, 194), (172, 194), (178, 174), (179, 318), (212, 237), (213, 199), (219, 348), (220, 131)] [(115, 236), (121, 299), (122, 253), (164, 219), (165, 242), (170, 156), (172, 156), (177, 242), (178, 219), (220, 253), (221, 299), (227, 236)]) (.cut 1 (.cut 3 (.e1 [(122, 154), (123, 367), (129, 196), (130, 233), (163, 300), (164, 169), (170, 177), (172, 177), (178, 169), (179, 300), (212, 233), (213, 196), (219, 367), (220, 154)] [(115, 220), (116, 440), (121, 297), (122, 229), (164, 232), (165, 257), (170, 168), (172, 168), (177, 257), (178, 232), (220, 229), (221, 297), (226, 440), (227, 220)]) (.cut 2 (.e1 [(122, 157), (129, 209), (130, 218), (163, 307), (164, 164), (170, 185), (172, 185), (178, 164), (179, 307), (212, 218), (213, 209), (220, 157)] [(115, 225), (121, 269), (122, 232), (164, 235), (165, 251), (170, 173), (172, 173), (177, 251), (178, 235), (220, 232), (221, 269), (227, 225)]) (.e1 [(122, 157), (129, 199), (130, 212), (164, 172), (170, 185), (172, 185), (178, 172), (179, 319), (212, 212), (213, 199), (219, 336), (220, 157)] [(115, 215), (121, 272), (122, 243), (164, 235), (165, 251), (170, 173), (172, 173), (177, 251), (178, 235), (220, 243), (221, 272), (227, 215)]))) (.cut 3 (.cut 2 (.e1 [(122, 157), (123, 353), (129, 225), (130, 220), (163, 274), (164, 180), (170, 166), (172, 166), (178, 180), (179, 274), (212, 220), (213, 225), (219, 353), (220, 157)] [(115, 222), (121, 293), (122, 218), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (220, 218), (221, 293), (227, 222)]) (.e1 [(122, 160), (129, 220), (130, 206), (163, 278), (164, 189), (170, 167), (172, 167), (178, 189), (179, 278), (212, 206), (213, 220), (219, 351), (220, 160)] [(115, 212), (121, 288), (122, 227), (164, 225), (165, 234), (170, 196), (172, 196), (177, 234), (178, 225), (220, 227), (221, 288), (227, 212)])) (.cut 2 (.cut 4 (.cut 0 (.e1 [(122, 145), (123, 334), (129, 226), (130, 222), (163, 290), (164, 174), (170, 180), (172, 180), (178, 174), (179, 290), (212, 222), (213, 226), (219, 334), (220, 145)] [(115, 235), (121, 282), (122, 232), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 232), (221, 282), (227, 235)]) (.cut 1 (.e1 [(122, 160), (123, 332), (129, 220), (130, 205), (163, 295), (164, 175), (170, 179), (172, 179), (178, 175), (179, 295), (212, 205), (213, 220), (219, 332), (220, 160)] [(115, 219), (121, 267), (122, 232), (164, 231), (165, 240), (170, 187), (172, 187), (177, 240), (178, 231), (220, 232), (221, 267), (227, 219)]) (.e1 [(122, 158), (123, 329), (129, 229), (130, 206), (163, 287), (164, 180), (170, 172), (172, 172), (178, 180), (179, 287), (212, 206), (213, 229), (219, 329), (220, 158)] [(114, 540), (115, 221), (116, 479), (121, 272), (122, 228), (164, 223), (165, 237), (170, 193), (172, 193), (177, 237), (178, 223), (214, 643), (220, 228), (221, 272), (226, 479), (227, 221), (228, 540)]))) (.e1 [(122, 157), (129, 225), (130, 220), (163, 309), (164, 180), (170, 162), (172, 162), (178, 180), (179, 309), (212, 220), (213, 225), (219, 314), (220, 157)] [(115, 219), (121, 278), (122, 228), (164, 210), (165, 254), (170, 191), (172, 191), (177, 254), (178, 210), (220, 228), (221, 278), (227, 219)])) (.e1 [(122, 157), (123, 324), (129, 215), (130, 201), (163, 308), (164, 188), (170, 173), (172, 173), (178, 188), (179, 308), (212, 201), (213, 215), (219, 324), (220, 157)] [(115, 210), (121, 274), (122, 243), (164, 222), (165, 239), (170, 191), (172, 191), (177, 239), (178, 222), (220, 243), (221, 274), (227, 210)]))))) (.e1 [(122, 151), (123, 310), (129, 204), (130, 246), (164, 187), (170, 153), (172, 153), (178, 187), (179, 350), (212, 246), (213, 204), (219, 310), (220, 151)] [(115, 212), (121, 302), (122, 236), (164, 195), (165, 282), (170, 180), (172, 180), (177, 282), (178, 195), (220, 236), (221, 302), (227, 212)])) (.cut 4 (.cut 0 (.cut 1 (.e1 [(122, 131), (123, 331), (129, 221), (130, 222), (163, 303), (164, 197), (170, 177), (172, 177), (178, 197), (179, 303), (212, 222), (213, 221), (219, 331), (220, 131)] [(115, 230), (121, 303), (122, 253), (164, 201), (165, 227), (170, 179), (172, 179), (177, 227), (178, 201), (220, 253), (221, 303), (227, 230)]) (.e1 [(122, 128), (123, 333), (129, 240), (130, 218), (163, 282), (164, 208), (170, 173), (172, 173), (178, 208), (179, 282), (212, 218), (213, 240), (219, 333), (220, 128)] [(115, 234), (121, 310), (122, 248), (164, 196), (165, 213), (170, 191), (172, 191), (177, 213), (178, 196), (220, 248), (221, 310), (227, 234)])) (.cut 1 (.cut 3 (.cut 2 (.e1 [(122, 157), (123, 343), (129, 241), (130, 211), (163, 265), (164, 197), (170, 156), (172, 156), (178, 197), (179, 265), (212, 211), (213, 241), (219, 343), (220, 157)] [(114, 582), (115, 217), (116, 461), (121, 298), (122, 218), (164, 210), (165, 229), (170, 209), (172, 209), (177, 229), (178, 210), (214, 626), (220, 218), (221, 298), (226, 461), (227, 217), (228, 582)]) (.e1 [(122, 157), (123, 343), (129, 231), (130, 204), (163, 276), (164, 204), (170, 156), (172, 156), (178, 204), (179, 276), (212, 204), (213, 231), (219, 343), (220, 157)] [(115, 208), (121, 299), (122, 228), (164, 210), (165, 229), (170, 209), (172, 209), (177, 229), (178, 210), (220, 228), (221, 299), (226, 461), (227, 208)])) (.cut 2 (.cut 4 (.cut 0 (.e1 [(122, 147), (129, 238), (130, 207), (163, 284), (164, 191), (170, 173), (172, 173), (178, 191), (179, 284), (212, 207), (213, 238), (219, 323), (220, 147)] [(115, 226), (121, 281), (122, 236), (164, 211), (165, 225), (170, 196), (172, 196), (177, 225), (178, 211), (220, 236), (221, 281), (227, 226)]) (.cut 1 (.cut 3 (.e1 [(122, 158), (123, 332), (129, 237), (130, 206), (163, 275), (164, 188), (170, 164), (172, 164), (178, 188), (179, 275), (212, 206), (213, 237), (219, 332), (220, 158)] [(115, 219), (121, 281), (122, 224), (164, 218), (165, 232), (170, 202), (172, 202), (177, 232), (178, 218), (220, 224), (221, 281), (227, 219)]) (.cut 4 (.e1 [(122, 160), (123, 322), (129, 239), (130, 199), (163, 280), (164, 185), (170, 169), (172, 169), (178, 185), (179, 280), (212, 199), (213, 239), (219, 322), (220, 160)] [(115, 219), (116, 486), (121, 269), (122, 228), (164, 221), (165, 230), (170, 203), (172, 203), (177, 230), (178, 221), (220, 228), (221, 269), (226, 486), (227, 219), (228, 550)]) (.e1 [(122, 160), (123, 315), (129, 239), (130, 208), (163, 289), (164, 185), (170, 162), (172, 162), (178, 185), (179, 289), (212, 208), (213, 239), (219, 315), (220, 160)] [(115, 219), (121, 273), (122, 225), (164, 212), (165, 240), (170, 203), (172, 203), (177, 240), (178, 212), (220, 225), (221, 273), (227, 219)]))) (.cut 4 (.e1 [(122, 157), (123, 318), (129, 246), (130, 197), (163, 277), (164, 193), (170, 167), (172, 167), (178, 193), (179, 277), (212, 197), (213, 246), (219, 318), (220, 157)] [(115, 219), (116, 492), (121, 272), (122, 230), (164, 215), (165, 224), (170, 209), (172, 209), (177, 224), (178, 215), (220, 230), (221, 272), (226, 492), (227, 219)]) (.e1 [(122, 157), (123, 310), (129, 246), (130, 206), (163, 286), (164, 193), (170, 159), (172, 159), (178, 193), (179, 286), (212, 206), (213, 246), (219, 310), (220, 157)] [(115, 219), (121, 277), (122, 227), (164, 206), (165, 234), (170, 209), (172, 209), (177, 234), (178, 206), (220, 227), (221, 277), (227, 219)])))) (.e1 [(122, 151), (123, 310), (129, 235), (130, 226), (163, 305), (164, 191), (170, 153), (172, 153), (178, 191), (179, 305), (212, 226), (213, 235), (219, 310), (220, 151)] [(115, 220), (121, 291), (122, 227), (164, 195), (165, 251), (170, 198), (172, 198), (177, 251), (178, 195), (220, 227), (221, 291), (227, 220)])) (.e1 [(121, 581), (122, 157), (123, 314), (129, 231), (130, 192), (163, 299), (164, 204), (170, 163), (172, 163), (178, 204), (179, 299), (212, 192), (213, 231), (219, 314), (220, 157), (221, 581), (261, 655)] [(114, 524), (115, 206), (116, 497), (121, 276), (122, 244), (128, 641), (164, 210), (165, 229), (170, 209), (172, 209), (177, 229), (178, 210), (214, 641), (220, 244), (221, 276), (226, 497), (227, 206), (228, 524)]))) (.cut 3 (.cut 4 (.e1 [(122, 151), (123, 348), (129, 247), (130, 204), (163, 256), (164, 212), (170, 156), (172, 156), (178, 212), (179, 256), (212, 204), (213, 247), (219, 348), (220, 151)] [(115, 215), (116, 455), (121, 307), (122, 225), (164, 206), (165, 216), (170, 217), (172, 217), (177, 216), (178, 206), (220, 225), (221, 307), (226, 455), (227, 215)]) (.e1 [(122, 151), (129, 247), (130, 224), (164, 212), (170, 140), (172, 140), (178, 212), (179, 276), (212, 224), (213, 247), (220, 151)] [(115, 213), (121, 318), (122, 219), (164, 188), (165, 237), (170, 217), (172, 217), (177, 237), (178, 188), (220, 219), (221, 318), (227, 213)])) (.cut 4 (.cut 2 (.cut 0 (.e1 [(122, 145), (129, 255), (130, 201), (163, 269), (164, 204), (170, 167), (172, 167), (178, 204), (179, 269), (212, 201), (213, 255), (219, 320), (220, 145)] [(115, 226), (121, 286), (122, 234), (164, 204), (165, 214), (170, 210), (172, 210), (177, 214), (178, 204), (220, 234), (221, 286), (227, 226)]) (.e1 [(121, 568), (122, 157), (123, 319), (129, 259), (130, 194), (163, 265), (164, 206), (170, 158), (172, 158), (178, 206), (179, 265), (212, 194), (213, 259), (219, 319), (220, 157), (221, 568)] [(114, 579), (115, 216), (116, 491), (121, 281), (122, 227), (128, 589), (164, 207), (165, 217), (170, 223), (172, 223), (177, 217), (178, 207), (214, 589), (220, 227), (221, 281), (226, 491), (227, 216), (228, 579)])) (.e1 [(122, 151), (123, 319), (129, 237), (130, 185), (163, 290), (164, 220), (170, 162), (172, 162), (178, 220), (179, 290), (212, 185), (213, 237), (219, 319), (220, 151)] [(115, 204), (121, 285), (122, 251), (164, 206), (165, 216), (170, 217), (172, 217), (177, 216), (178, 206), (220, 251), (221, 285), (227, 204)])) (.e1 [(122, 151), (129, 247), (130, 211), (163, 298), (164, 212), (170, 146), (172, 146), (178, 212), (179, 298), (212, 211), (213, 247), (219, 303), (220, 151)] [(115, 211), (121, 294), (122, 233), (164, 188), (165, 237), (170, 217), (172, 217), (177, 237), (178, 188), (220, 233), (221, 294), (227, 211)]))))) (.e1 [(122, 151), (123, 297), (129, 221), (130, 238), (164, 203), (170, 140), (172, 140), (178, 203), (212, 238), (213, 221), (219, 297), (220, 151)] [(115, 208), (121, 305), (122, 235), (164, 182), (165, 274), (170, 198), (172, 198), (177, 274), (178, 182), (220, 235), (221, 305), (227, 208)])))

theorem root692 : rootCheck plan692 ![2, 2] ![3, 1, 0] = true := by decide +kernel

def plan693 : Plan :=
  (.e1 [(122, 145), (129, 207), (130, 327), (164, 181), (170, 132), (172, 132), (178, 181), (212, 327), (213, 207), (220, 145)] [(115, 225), (121, 340), (122, 217), (164, 169), (170, 174), (172, 174), (177, 355), (178, 169), (220, 217), (221, 340), (227, 225)])

theorem root693 : rootCheck plan693 ![2, 2] ![3, 1, 1] = true := by decide +kernel

def plan694 : Plan :=
  (.e1 [(122, 145), (129, 207), (164, 181), (165, 312), (170, 132), (172, 132), (177, 312), (178, 181), (213, 207), (220, 145)] [(114, 358), (115, 244), (122, 202), (164, 169), (170, 174), (172, 174), (178, 169), (220, 202), (227, 244), (228, 358)])

theorem root694 : rootCheck plan694 ![2, 2] ![3, 1, 2] = true := by decide +kernel

def plan695 : Plan :=
  (.cut 0 (.cut 1 (.e1 [(122, 134), (129, 199), (164, 183), (165, 222), (170, 186), (172, 186), (177, 222), (178, 183), (213, 199), (220, 134)] [(114, 306), (115, 280), (122, 211), (163, 245), (164, 212), (170, 163), (172, 163), (178, 212), (179, 245), (220, 211), (227, 280), (228, 306)]) (.e1 [(122, 134), (128, 334), (129, 233), (164, 216), (165, 203), (170, 163), (172, 163), (177, 203), (178, 216), (213, 233), (214, 334), (219, 310), (220, 134)] [(114, 307), (115, 279), (122, 205), (163, 225), (164, 189), (170, 197), (172, 197), (178, 189), (179, 225), (220, 205), (227, 279), (228, 307)])) (.cut 4 (.cut 4 (.e1 [(122, 145), (123, 308), (129, 220), (164, 186), (165, 259), (170, 137), (172, 137), (177, 259), (178, 186), (213, 220), (219, 308), (220, 145)] [(114, 343), (115, 257), (122, 193), (163, 299), (164, 177), (170, 183), (172, 183), (178, 177), (179, 299), (220, 193), (227, 257), (228, 343)]) (.e1 [(122, 151), (123, 317), (128, 359), (129, 212), (164, 195), (165, 237), (170, 143), (172, 143), (177, 237), (178, 195), (213, 212), (214, 359), (219, 317), (220, 151)] [(114, 323), (115, 249), (121, 464), (122, 194), (163, 277), (164, 188), (170, 189), (172, 189), (178, 188), (179, 277), (220, 194), (221, 464), (227, 249), (228, 323)])) (.cut 1 (.e1 [(122, 157), (123, 363), (128, 311), (129, 206), (164, 188), (165, 204), (170, 167), (172, 167), (177, 204), (178, 188), (213, 206), (214, 311), (219, 363), (220, 157)] [(114, 307), (115, 253), (121, 510), (122, 192), (163, 242), (164, 225), (170, 186), (172, 186), (178, 225), (179, 242), (220, 192), (221, 510), (227, 253), (228, 307)]) (.cut 4 (.e1 [(122, 148), (129, 229), (164, 203), (165, 205), (170, 152), (172, 152), (177, 205), (178, 203), (213, 229), (214, 343), (219, 316), (220, 148)] [(114, 309), (115, 267), (122, 191), (163, 245), (164, 194), (170, 199), (172, 199), (178, 194), (179, 245), (220, 191), (227, 267), (228, 309)]) (.e1 [(122, 151), (123, 333), (128, 311), (129, 229), (164, 211), (165, 189), (170, 159), (172, 159), (177, 189), (178, 211), (213, 229), (214, 311), (219, 333), (220, 151)] [(114, 302), (115, 263), (122, 191), (123, 475), (163, 225), (164, 206), (170, 207), (172, 207), (178, 206), (179, 225), (219, 475), (220, 191), (227, 263), (228, 302)])))))

theorem root695 : rootCheck plan695 ![2, 2] ![3, 1, 3] = true := by decide +kernel

def plan696_0 : Plan :=
  (.cut 4 (.cut 0 (.e1 [(122, 131), (123, 300), (129, 199), (130, 219), (163, 365), (164, 174), (170, 211), (172, 211), (178, 174), (179, 365), (212, 219), (213, 199), (219, 300), (220, 131)] [(115, 238), (121, 266), (122, 283), (164, 219), (165, 242), (170, 156), (172, 156), (177, 242), (178, 219), (220, 283), (221, 266), (227, 238)]) (.cut 1 (.cut 2 (.cut 3 (.e1 [(122, 157), (123, 310), (129, 209), (130, 207), (163, 331), (164, 164), (170, 194), (172, 194), (178, 164), (179, 331), (212, 207), (213, 209), (219, 310), (220, 157)] [(115, 225), (121, 251), (122, 248), (164, 235), (165, 251), (170, 173), (172, 173), (177, 251), (178, 235), (220, 248), (221, 251), (227, 225)]) (.e1 [(81, 622), (122, 154), (123, 288), (129, 208), (130, 208), (163, 357), (164, 160), (165, 627), (170, 205), (172, 205), (177, 627), (178, 160), (179, 357), (212, 208), (213, 208), (219, 288), (220, 154), (261, 622)] [(114, 451), (115, 232), (116, 541), (121, 239), (122, 260), (164, 232), (165, 257), (170, 168), (172, 168), (177, 257), (178, 232), (220, 260), (221, 239), (226, 541), (227, 232), (228, 451)])) (.cut 3 (.e1 [(122, 157), (123, 310), (129, 199), (130, 202), (164, 172), (170, 194), (172, 194), (178, 172), (179, 344), (212, 202), (213, 199), (219, 310), (220, 157)] [(115, 216), (121, 254), (122, 259), (164, 235), (165, 251), (170, 173), (172, 173), (177, 251), (178, 235), (220, 259), (221, 254), (227, 216)]) (.e1 [(122, 157), (123, 288), (129, 190), (130, 205), (163, 383), (164, 172), (170, 199), (172, 199), (178, 172), (179, 383), (212, 205), (213, 190), (219, 288), (220, 157)] [(115, 215), (121, 248), (122, 274), (164, 231), (165, 264), (170, 168), (172, 168), (177, 264), (178, 231), (220, 274), (221, 248), (227, 215), (228, 421)]))) (.cut 2 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 308), (129, 226), (130, 210), (163, 312), (164, 174), (170, 189), (172, 189), (178, 174), (179, 312), (212, 210), (213, 226), (219, 308), (220, 145)] [(115, 234), (121, 263), (122, 247), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 247), (221, 263), (227, 234)]) (.cut 1 (.e1 [(122, 158), (123, 308), (129, 221), (130, 200), (163, 316), (164, 171), (170, 187), (172, 187), (178, 171), (179, 316), (212, 200), (213, 221), (219, 308), (220, 158)] [(115, 223), (121, 252), (122, 244), (164, 229), (165, 243), (170, 184), (172, 184), (177, 243), (178, 229), (220, 244), (221, 252), (227, 223)]) (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 314), (129, 231), (130, 198), (163, 297), (164, 177), (170, 179), (172, 179), (178, 177), (179, 297), (212, 198), (213, 231), (219, 314), (220, 160)] [(114, 524), (115, 221), (116, 498), (121, 257), (122, 236), (164, 227), (165, 236), (170, 194), (172, 194), (177, 236), (178, 227), (220, 236), (221, 257), (226, 498), (227, 221), (228, 524)]) (.e1 [(122, 160), (123, 301), (129, 231), (130, 192), (163, 309), (164, 177), (170, 184), (172, 184), (178, 177), (179, 309), (212, 192), (213, 231), (219, 301), (220, 160)] [(115, 221), (116, 516), (121, 248), (122, 244), (164, 227), (165, 236), (170, 194), (172, 194), (177, 236), (178, 227), (220, 244), (221, 248), (226, 516), (227, 221), (228, 506)])) (.e1 [(122, 158), (123, 297), (129, 229), (130, 200), (163, 316), (164, 180), (170, 177), (172, 177), (178, 180), (179, 316), (212, 200), (213, 229), (219, 297), (220, 158)] [(115, 220), (121, 255), (122, 242), (164, 218), (165, 243), (170, 193), (172, 193), (177, 243), (178, 218), (220, 242), (221, 255), (226, 521), (227, 220), (228, 497)])))) (.cut 0 (.e1 [(122, 145), (123, 285), (129, 226), (130, 200), (164, 174), (170, 199), (172, 199), (178, 174), (179, 337), (212, 200), (213, 226), (219, 285), (220, 145)] [(115, 235), (121, 246), (122, 264), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 264), (221, 246), (227, 235)]) (.cut 1 (.e1 [(122, 160), (123, 285), (129, 223), (130, 194), (163, 338), (164, 169), (170, 195), (172, 195), (178, 169), (179, 338), (212, 194), (213, 223), (219, 285), (220, 160)] [(115, 225), (121, 236), (122, 255), (164, 229), (165, 246), (170, 184), (172, 184), (177, 246), (178, 229), (220, 255), (221, 236), (227, 225), (228, 469)]) (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 289), (129, 231), (130, 187), (163, 322), (164, 177), (170, 190), (172, 190), (178, 177), (179, 322), (212, 187), (213, 231), (219, 289), (220, 160)] [(114, 488), (115, 222), (116, 535), (121, 239), (122, 253), (128, 635), (164, 227), (165, 236), (170, 194), (172, 194), (177, 236), (178, 227), (214, 635), (220, 253), (221, 239), (226, 535), (227, 222), (228, 488)]) (.e1 [(81, 613), (122, 158), (123, 277), (129, 234), (130, 186), (163, 331), (164, 176), (170, 194), (172, 194), (178, 176), (179, 331), (212, 186), (213, 234), (219, 277), (220, 158), (261, 613)] [(114, 477), (115, 226), (116, 553), (121, 232), (122, 260), (164, 224), (165, 236), (170, 193), (172, 193), (177, 236), (178, 224), (220, 260), (221, 232), (226, 553), (227, 226), (228, 477)])) (.cut 3 (.e1 [(122, 160), (123, 281), (129, 231), (130, 196), (163, 331), (164, 177), (170, 182), (172, 182), (178, 177), (179, 331), (212, 196), (213, 231), (219, 281), (220, 160)] [(114, 478), (115, 222), (121, 242), (122, 250), (164, 218), (165, 245), (170, 194), (172, 194), (177, 245), (178, 218), (220, 250), (221, 242), (226, 546), (227, 222), (228, 478)]) (.e1 [(122, 160), (123, 269), (129, 231), (130, 191), (163, 344), (164, 177), (170, 188), (172, 188), (178, 177), (179, 344), (212, 191), (213, 231), (219, 269), (220, 160)] [(114, 461), (115, 224), (121, 234), (122, 259), (164, 218), (165, 245), (170, 194), (172, 194), (177, 245), (178, 218), (220, 259), (221, 234), (227, 224), (228, 461)])))))) (.cut 3 (.e1 [(122, 157), (123, 287), (129, 225), (130, 209), (163, 334), (164, 180), (170, 172), (172, 172), (178, 180), (179, 334), (212, 209), (213, 225), (219, 287), (220, 157)] [(115, 220), (121, 258), (122, 244), (164, 210), (165, 254), (170, 191), (172, 191), (177, 254), (178, 210), (220, 244), (221, 258), (227, 220)]) (.cut 0 (.e1 [(122, 145), (123, 271), (129, 226), (130, 218), (164, 174), (170, 185), (172, 185), (178, 174), (179, 355), (212, 218), (213, 226), (219, 271), (220, 145)] [(115, 237), (121, 252), (122, 257), (164, 204), (165, 255), (170, 179), (172, 179), (177, 255), (178, 204), (220, 257), (221, 252), (227, 237)]) (.cut 1 (.e1 [(122, 160), (123, 267), (129, 220), (130, 202), (163, 364), (164, 175), (170, 186), (172, 186), (178, 175), (179, 364), (212, 202), (213, 220), (219, 267), (220, 160)] [(115, 223), (121, 238), (122, 260), (164, 215), (165, 259), (170, 187), (172, 187), (177, 259), (178, 215), (220, 260), (221, 238), (227, 223)]) (.e1 [(81, 624), (121, 666), (122, 158), (123, 263), (129, 229), (130, 203), (163, 355), (164, 180), (165, 616), (170, 178), (172, 178), (177, 616), (178, 180), (179, 355), (212, 203), (213, 229), (219, 263), (220, 158), (221, 666), (261, 624)] [(108, 798), (114, 449), (115, 223), (116, 575), (121, 242), (122, 255), (128, 641), (164, 207), (165, 257), (170, 193), (172, 193), (177, 257), (178, 207), (179, 736), (214, 641), (220, 255), (221, 242), (226, 575), (227, 223), (228, 449), (234, 798)]))))) (.cut 4 (.cut 3 (.e1 [(122, 157), (123, 315), (129, 215), (130, 192), (163, 316), (164, 188), (170, 181), (172, 181), (178, 188), (179, 316), (212, 192), (213, 215), (219, 315), (220, 157)] [(114, 496), (115, 210), (121, 262), (122, 254), (164, 226), (165, 235), (170, 191), (172, 191), (177, 235), (178, 226), (220, 254), (221, 262), (227, 210), (228, 496)]) (.cut 0 (.e1 [(122, 145), (123, 285), (129, 206), (130, 193), (164, 189), (170, 199), (172, 199), (178, 189), (212, 193), (213, 206), (219, 285), (220, 145)] [(115, 218), (121, 252), (122, 287), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 287), (221, 252), (227, 218)]) (.e1 [(81, 590), (115, 739), (121, 667), (122, 158), (123, 282), (129, 211), (130, 187), (137, 725), (163, 357), (164, 188), (165, 651), (170, 188), (172, 188), (177, 651), (178, 188), (179, 357), (205, 725), (211, 796), (212, 187), (213, 211), (219, 282), (220, 158), (221, 667), (227, 739), (261, 590)] [(108, 781), (114, 445), (115, 210), (116, 545), (120, 789), (121, 246), (122, 273), (128, 681), (164, 221), (165, 244), (170, 190), (172, 190), (177, 244), (178, 221), (214, 681), (220, 273), (221, 246), (222, 789), (226, 545), (227, 210), (228, 445), (234, 781)]))) (.cut 3 (.e1 [(122, 160), (123, 284), (129, 220), (130, 199), (164, 189), (170, 171), (172, 171), (178, 189), (212, 199), (213, 220), (219, 284), (220, 160)] [(115, 211), (121, 256), (122, 253), (164, 211), (165, 252), (170, 196), (172, 196), (177, 252), (178, 211), (220, 253), (221, 256), (227, 211)]) (.e1 [(122, 160), (123, 260), (129, 220), (130, 191), (163, 371), (164, 189), (170, 183), (172, 183), (178, 189), (179, 371), (212, 191), (213, 220), (219, 260), (220, 160)] [(115, 214), (121, 239), (122, 273), (164, 211), (165, 252), (170, 196), (172, 196), (177, 252), (178, 211), (220, 273), (221, 239), (227, 214), (228, 431)])))))) (.cut 0 (.e1 [(122, 134), (129, 199), (130, 244), (164, 183), (170, 186), (172, 186), (178, 183), (212, 244), (213, 199), (219, 268), (220, 134)] [(115, 234), (121, 275), (122, 277), (164, 193), (165, 274), (170, 163), (172, 163), (177, 274), (178, 193), (220, 277), (221, 275), (227, 234)]) (.cut 1 (.e1 [(122, 157), (123, 267), (129, 194), (130, 230), (163, 408), (164, 176), (170, 178), (172, 178), (178, 176), (179, 408), (212, 230), (213, 194), (219, 267), (220, 157)] [(115, 218), (121, 259), (122, 262), (164, 207), (165, 291), (170, 173), (172, 173), (177, 291), (178, 207), (220, 262), (221, 259), (227, 218), (228, 400)]) (.cut 2 (.e1 [(122, 157), (123, 254), (129, 225), (130, 227), (164, 180), (170, 165), (172, 165), (178, 180), (212, 227), (213, 225), (219, 254), (220, 157)] [(114, 429), (115, 225), (121, 254), (122, 248), (164, 192), (165, 282), (170, 191), (172, 191), (177, 282), (178, 192), (220, 248), (221, 254), (227, 225), (228, 429)]) (.e1 [(122, 157), (123, 254), (129, 205), (130, 220), (164, 196), (170, 165), (172, 165), (178, 196), (212, 220), (213, 205), (219, 254), (220, 157)] [(114, 401), (115, 210), (121, 262), (122, 268), (164, 192), (165, 282), (170, 191), (172, 191), (177, 282), (178, 192), (220, 268), (221, 262), (227, 210), (228, 401)])))))

theorem plan696_0_ok : plan696_0.checkAt
    ((rootAddress ![2, 2] ![3, 2, 0]).child false)
    (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 false) = true := by decide +kernel

def plan696_1 : Plan :=
  (.cut 1 (.e1 [(122, 134), (123, 285), (129, 225), (130, 211), (163, 342), (164, 192), (170, 187), (172, 187), (178, 192), (179, 342), (212, 211), (213, 225), (219, 285), (220, 134)] [(114, 472), (115, 233), (121, 269), (122, 271), (164, 200), (165, 234), (170, 180), (172, 180), (177, 234), (178, 200), (220, 271), (221, 269), (227, 233), (228, 472)]) (.e1 [(122, 134), (123, 274), (129, 241), (130, 203), (163, 334), (164, 209), (170, 176), (172, 176), (178, 209), (179, 334), (212, 203), (213, 241), (219, 274), (220, 134)] [(115, 228), (121, 270), (122, 273), (164, 189), (165, 225), (170, 197), (172, 197), (177, 225), (178, 189), (220, 273), (221, 270), (227, 228)]))

theorem plan696_1_ok : plan696_1.checkAt
    ((((rootAddress ![2, 2] ![3, 2, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 false) 0 false) = true := by decide +kernel

def plan696_2 : Plan :=
  (.cut 2 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 147), (123, 297), (129, 238), (130, 195), (163, 307), (164, 191), (170, 181), (172, 181), (178, 191), (179, 307), (212, 195), (213, 238), (219, 297), (220, 147)] [(115, 225), (121, 261), (122, 253), (164, 211), (165, 225), (170, 196), (172, 196), (177, 225), (178, 211), (220, 253), (221, 261), (227, 225)]) (.cut 1 (.cut 4 (.cut 3 (.e1 [(81, 670), (115, 707), (121, 615), (122, 160), (123, 309), (129, 239), (130, 193), (163, 292), (164, 185), (170, 174), (172, 174), (178, 185), (179, 292), (205, 703), (212, 193), (213, 239), (219, 309), (220, 160), (221, 615), (227, 707), (261, 670)] [(114, 531), (115, 219), (116, 504), (121, 259), (122, 236), (128, 620), (164, 221), (165, 230), (170, 203), (172, 203), (177, 230), (178, 221), (214, 620), (220, 236), (221, 259), (226, 504), (227, 219), (228, 531)]) (.cut 2 (.e1 [(81, 658), (122, 160), (123, 296), (129, 245), (130, 190), (163, 298), (164, 182), (170, 179), (172, 179), (178, 182), (179, 298), (212, 190), (213, 245), (219, 296), (220, 160), (221, 638), (261, 658)] [(114, 521), (115, 223), (116, 523), (121, 248), (122, 240), (128, 609), (164, 221), (165, 230), (170, 203), (172, 203), (177, 230), (178, 221), (214, 609), (220, 240), (221, 248), (226, 523), (227, 223), (228, 521)]) (.e1 [(122, 160), (123, 296), (129, 234), (130, 185), (163, 311), (164, 189), (170, 179), (172, 179), (178, 189), (179, 311), (212, 185), (213, 234), (219, 296), (220, 160)] [(115, 214), (121, 250), (122, 251), (164, 221), (165, 230), (170, 203), (172, 203), (177, 230), (178, 221), (220, 251), (221, 250), (226, 523), (227, 214)]))) (.cut 3 (.e1 [(122, 160), (123, 301), (129, 239), (130, 202), (163, 301), (164, 185), (170, 166), (172, 166), (178, 185), (179, 301), (212, 202), (213, 239), (219, 301), (220, 160)] [(115, 219), (121, 263), (122, 233), (164, 212), (165, 240), (170, 203), (172, 203), (177, 240), (178, 212), (220, 233), (221, 263), (227, 219)]) (.e1 [(122, 160), (123, 288), (129, 239), (130, 196), (163, 313), (164, 185), (170, 171), (172, 171), (178, 185), (179, 313), (212, 196), (213, 239), (219, 288), (220, 160)] [(114, 501), (115, 219), (121, 253), (122, 241), (164, 212), (165, 240), (170, 203), (172, 203), (177, 240), (178, 212), (220, 241), (221, 253), (226, 534), (227, 219), (228, 501)]))) (.cut 4 (.cut 3 (.e1 [(122, 158), (123, 305), (129, 249), (130, 190), (163, 286), (164, 190), (170, 172), (172, 172), (178, 190), (179, 286), (212, 190), (213, 249), (219, 305), (220, 158)] [(114, 540), (115, 220), (116, 510), (121, 259), (122, 237), (164, 217), (165, 224), (170, 209), (172, 209), (177, 224), (178, 217), (214, 603), (220, 237), (221, 259), (226, 510), (227, 220), (228, 540)]) (.cut 2 (.e1 [(122, 158), (123, 291), (129, 255), (130, 185), (163, 292), (164, 190), (170, 176), (172, 176), (178, 190), (179, 292), (212, 185), (213, 255), (219, 291), (220, 158)] [(114, 529), (115, 222), (116, 531), (121, 249), (122, 242), (164, 216), (165, 223), (170, 212), (172, 212), (177, 223), (178, 216), (220, 242), (221, 249), (226, 531), (227, 222), (228, 529)]) (.e1 [(122, 160), (123, 291), (129, 242), (130, 180), (163, 306), (164, 197), (170, 174), (172, 174), (178, 197), (179, 306), (212, 180), (213, 242), (219, 291), (220, 160)] [(115, 212), (121, 251), (122, 252), (164, 216), (165, 225), (170, 212), (172, 212), (177, 225), (178, 216), (220, 252), (221, 251), (227, 212)]))) (.e1 [(81, 661), (122, 160), (123, 286), (129, 251), (130, 193), (163, 301), (164, 188), (170, 169), (172, 169), (178, 188), (179, 301), (212, 193), (213, 251), (219, 286), (220, 160), (261, 661)] [(114, 517), (115, 221), (116, 537), (121, 252), (122, 238), (128, 599), (164, 210), (165, 234), (170, 210), (172, 210), (177, 234), (178, 210), (214, 599), (220, 238), (221, 252), (226, 537), (227, 221), (228, 517)])))) (.cut 0 (.e1 [(122, 145), (123, 274), (129, 242), (130, 191), (163, 327), (164, 191), (170, 189), (172, 189), (178, 191), (179, 327), (212, 191), (213, 242), (219, 274), (220, 145)] [(115, 230), (121, 247), (122, 267), (164, 207), (165, 226), (170, 196), (172, 196), (177, 226), (178, 207), (220, 267), (221, 247), (227, 230)]) (.cut 1 (.cut 4 (.cut 3 (.cut 2 (.e1 [(81, 635), (115, 695), (121, 662), (122, 160), (123, 284), (129, 245), (130, 185), (163, 311), (164, 182), (170, 185), (172, 185), (178, 182), (179, 311), (205, 705), (212, 185), (213, 245), (219, 284), (220, 160), (221, 662), (227, 695), (261, 635)] [(114, 503), (115, 224), (116, 542), (121, 239), (122, 249), (128, 609), (164, 221), (165, 230), (170, 203), (172, 203), (177, 230), (178, 221), (214, 609), (220, 249), (221, 239), (226, 542), (227, 224), (228, 503)]) (.e1 [(122, 160), (123, 284), (129, 234), (130, 180), (163, 324), (164, 189), (170, 185), (172, 185), (178, 189), (179, 324), (212, 180), (213, 234), (219, 284), (220, 160)] [(114, 485), (115, 215), (121, 241), (122, 260), (164, 221), (165, 230), (170, 203), (172, 203), (177, 230), (178, 221), (220, 260), (221, 241), (227, 215), (228, 485)])) (.cut 2 (.e1 [(122, 160), (123, 272), (129, 249), (130, 183), (163, 318), (164, 182), (170, 186), (172, 186), (178, 182), (179, 318), (212, 183), (213, 249), (219, 272), (220, 160)] [(114, 492), (115, 226), (116, 562), (121, 233), (122, 253), (128, 600), (164, 217), (165, 231), (170, 205), (172, 205), (177, 231), (178, 217), (214, 600), (220, 253), (221, 233), (226, 562), (227, 226), (228, 492)]) (.e1 [(122, 160), (123, 272), (129, 239), (130, 179), (163, 332), (164, 189), (170, 186), (172, 186), (178, 189), (179, 332), (212, 179), (213, 239), (219, 272), (220, 160)] [(115, 217), (121, 235), (122, 264), (164, 217), (165, 231), (170, 205), (172, 205), (177, 231), (178, 217), (220, 264), (221, 235), (227, 217)]))) (.cut 3 (.e1 [(81, 634), (122, 160), (123, 274), (129, 247), (130, 189), (163, 319), (164, 184), (170, 179), (172, 179), (178, 184), (179, 319), (212, 189), (213, 247), (219, 274), (220, 160), (261, 634)] [(114, 491), (115, 223), (116, 558), (121, 239), (122, 249), (128, 605), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (214, 605), (220, 249), (221, 239), (226, 558), (227, 223), (228, 491)]) (.cut 2 (.e1 [(122, 160), (123, 264), (129, 245), (130, 189), (163, 333), (164, 182), (170, 183), (172, 183), (178, 182), (179, 333), (212, 189), (213, 245), (219, 264), (220, 160)] [(114, 474), (115, 225), (116, 574), (121, 233), (122, 255), (164, 212), (165, 240), (170, 203), (172, 203), (177, 240), (178, 212), (220, 255), (221, 233), (226, 574), (227, 225), (228, 474)]) (.e1 [(122, 160), (123, 264), (129, 234), (130, 185), (163, 347), (164, 189), (170, 183), (172, 183), (178, 189), (179, 347), (212, 185), (213, 234), (219, 264), (220, 160)] [(115, 217), (121, 236), (122, 266), (164, 212), (165, 240), (170, 203), (172, 203), (177, 240), (178, 212), (220, 266), (221, 236), (227, 217), (228, 457)])))) (.cut 4 (.cut 3 (.cut 2 (.e1 [(122, 158), (123, 281), (129, 255), (130, 181), (163, 302), (164, 190), (170, 181), (172, 181), (178, 190), (179, 302), (212, 181), (213, 255), (219, 281), (220, 158)] [(114, 515), (115, 223), (116, 546), (121, 241), (122, 249), (164, 216), (165, 223), (170, 212), (172, 212), (177, 223), (178, 216), (214, 591), (220, 249), (221, 241), (226, 546), (227, 223), (228, 515)]) (.e1 [(122, 157), (123, 280), (129, 244), (130, 179), (163, 317), (164, 195), (170, 182), (172, 182), (178, 195), (179, 317), (212, 179), (213, 244), (219, 280), (220, 157)] [(115, 217), (121, 243), (122, 260), (164, 215), (165, 224), (170, 209), (172, 209), (177, 224), (178, 215), (220, 260), (221, 243), (227, 217)])) (.e1 [(81, 614), (115, 705), (121, 672), (122, 160), (123, 267), (129, 255), (130, 178), (131, 719), (137, 729), (163, 317), (164, 192), (165, 685), (170, 181), (172, 181), (177, 685), (178, 192), (179, 317), (205, 729), (211, 719), (212, 178), (213, 255), (219, 267), (220, 160), (221, 672), (227, 705), (261, 614)] [(108, 800), (109, 853), (114, 493), (115, 221), (116, 569), (120, 832), (121, 234), (122, 258), (128, 591), (163, 818), (164, 212), (165, 226), (166, 862), (170, 215), (172, 215), (176, 862), (177, 226), (178, 212), (179, 818), (214, 591), (220, 258), (221, 234), (222, 832), (226, 569), (227, 221), (228, 493), (233, 853), (234, 800)])) (.cut 3 (.e1 [(122, 160), (123, 271), (129, 251), (130, 187), (163, 317), (164, 188), (170, 177), (172, 177), (178, 188), (179, 317), (212, 187), (213, 251), (219, 271), (220, 160)] [(114, 494), (115, 222), (116, 562), (121, 240), (122, 250), (164, 210), (165, 234), (170, 210), (172, 210), (177, 234), (178, 210), (220, 250), (221, 240), (226, 562), (227, 222), (228, 494)]) (.e1 [(122, 158), (123, 263), (129, 249), (130, 184), (163, 330), (164, 190), (170, 180), (172, 180), (178, 190), (179, 330), (212, 184), (213, 249), (219, 263), (220, 158)] [(114, 478), (115, 222), (116, 576), (121, 236), (122, 259), (128, 602), (164, 208), (165, 234), (170, 209), (172, 209), (177, 234), (178, 208), (214, 602), (220, 259), (221, 236), (226, 576), (227, 222), (228, 478)])))))) (.cut 3 (.e1 [(81, 658), (115, 708), (121, 606), (122, 154), (123, 280), (129, 241), (130, 209), (131, 755), (137, 778), (163, 324), (164, 192), (165, 639), (170, 161), (172, 161), (177, 639), (178, 192), (179, 324), (205, 778), (211, 755), (212, 209), (213, 241), (219, 280), (220, 154), (221, 606), (227, 708), (261, 658)] [(114, 491), (115, 220), (116, 547), (121, 265), (122, 241), (123, 817), (128, 623), (129, 847), (163, 744), (164, 196), (165, 248), (170, 203), (172, 203), (177, 248), (178, 196), (179, 744), (213, 847), (214, 623), (219, 817), (220, 241), (221, 265), (226, 547), (227, 220), (228, 491)]) (.cut 0 (.e1 [(122, 145), (123, 259), (129, 242), (130, 210), (163, 346), (164, 191), (170, 174), (172, 174), (178, 191), (179, 346), (212, 210), (213, 242), (219, 259), (220, 145)] [(115, 231), (121, 254), (122, 259), (164, 191), (165, 246), (170, 196), (172, 196), (177, 246), (178, 191), (220, 259), (221, 254), (227, 231)]) (.cut 1 (.cut 4 (.e1 [(81, 616), (115, 711), (121, 663), (122, 158), (123, 260), (128, 885), (129, 237), (130, 195), (131, 760), (137, 762), (163, 347), (164, 188), (165, 635), (170, 175), (172, 175), (177, 635), (178, 188), (179, 347), (205, 762), (211, 760), (212, 195), (213, 237), (214, 885), (219, 260), (220, 158), (221, 663), (227, 711), (261, 616)] [(65, 867), (66, 945), (108, 782), (109, 887), (114, 458), (115, 220), (116, 580), (120, 822), (121, 241), (122, 258), (123, 871), (127, 951), (128, 625), (129, 896), (158, 894), (163, 756), (164, 204), (165, 248), (166, 889), (170, 202), (172, 202), (176, 889), (177, 248), (178, 204), (179, 756), (184, 894), (213, 896), (214, 625), (215, 951), (219, 871), (220, 258), (221, 241), (222, 822), (226, 580), (227, 220), (228, 458), (233, 887), (234, 782), (270, 989), (276, 945), (277, 867)]) (.e1 [(122, 157), (123, 251), (129, 238), (130, 208), (163, 359), (164, 185), (170, 171), (172, 171), (178, 185), (179, 359), (212, 208), (213, 238), (219, 251), (220, 157)] [(115, 226), (121, 243), (122, 254), (164, 196), (165, 261), (170, 200), (172, 200), (177, 261), (178, 196), (220, 254), (221, 243), (227, 226), (228, 446)])) (.cut 4 (.e1 [(122, 158), (123, 257), (129, 249), (130, 194), (163, 338), (164, 190), (170, 171), (172, 171), (178, 190), (179, 338), (212, 194), (213, 249), (219, 257), (220, 158), (261, 624)] [(114, 470), (115, 222), (116, 586), (121, 241), (122, 254), (164, 200), (165, 245), (170, 209), (172, 209), (177, 245), (178, 200), (220, 254), (221, 241), (226, 586), (227, 222), (228, 470)]) (.redProjected 0 1)))))) (.cut 4 (.cut 3 (.e1 [(121, 617), (122, 157), (123, 297), (129, 222), (130, 184), (163, 327), (164, 204), (170, 172), (172, 172), (178, 204), (179, 327), (212, 184), (213, 222), (219, 297), (220, 157), (221, 617), (261, 612)] [(114, 484), (115, 203), (116, 522), (121, 262), (122, 263), (128, 658), (164, 213), (165, 232), (170, 204), (172, 204), (177, 232), (178, 213), (214, 658), (220, 263), (221, 262), (226, 522), (227, 203), (228, 484)]) (.cut 0 (.e1 [(122, 145), (123, 274), (129, 223), (130, 183), (164, 206), (170, 189), (172, 189), (178, 206), (179, 354), (212, 183), (213, 223), (219, 274), (220, 145)] [(115, 214), (121, 252), (122, 289), (164, 207), (165, 226), (170, 196), (172, 196), (177, 226), (178, 207), (220, 289), (221, 252), (227, 214)]) (.e1 [(122, 157), (123, 272), (129, 227), (130, 178), (163, 347), (164, 200), (170, 183), (172, 183), (178, 200), (179, 347), (212, 178), (213, 227), (219, 272), (220, 157)] [(114, 457), (115, 209), (121, 243), (122, 277), (164, 213), (165, 232), (170, 204), (172, 204), (177, 232), (178, 213), (220, 277), (221, 243), (227, 209), (228, 457)]))) (.cut 3 (.e1 [(122, 151), (123, 287), (129, 221), (130, 202), (163, 342), (164, 203), (170, 165), (172, 165), (178, 203), (179, 342), (212, 202), (213, 221), (219, 287), (220, 151)] [(115, 208), (121, 272), (122, 260), (164, 199), (165, 245), (170, 198), (172, 198), (177, 245), (178, 199), (220, 260), (221, 272), (227, 208), (228, 469)]) (.e1 [(122, 157), (123, 253), (129, 231), (130, 188), (163, 367), (164, 204), (170, 172), (172, 172), (178, 204), (179, 367), (212, 188), (213, 231), (219, 253), (220, 157), (261, 580)] [(114, 437), (115, 211), (116, 594), (121, 245), (122, 276), (164, 198), (165, 245), (170, 209), (172, 209), (177, 245), (178, 198), (220, 276), (221, 245), (226, 594), (227, 211), (228, 437)]))))

theorem plan696_2_ok : plan696_2.checkAt
    (((((rootAddress ![2, 2] ![3, 2, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 false) 0 true) 1 false) = true := by decide +kernel

def plan696_3 : Plan :=
  (.cut 4 (.cut 2 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 295), (129, 255), (130, 189), (163, 292), (164, 204), (170, 175), (172, 175), (178, 204), (179, 292), (212, 189), (213, 255), (219, 295), (220, 145)] [(115, 225), (121, 265), (122, 252), (164, 204), (165, 214), (170, 210), (172, 210), (177, 214), (178, 204), (220, 252), (221, 265), (227, 225)]) (.cut 1 (.cut 4 (.cut 3 (.e1 [(122, 157), (123, 303), (129, 255), (130, 184), (163, 282), (164, 201), (170, 169), (172, 169), (178, 201), (179, 282), (212, 184), (213, 255), (219, 303), (220, 157)] [(115, 216), (116, 514), (121, 262), (122, 240), (164, 212), (165, 217), (170, 218), (172, 218), (177, 217), (178, 212), (220, 240), (221, 262), (226, 514), (227, 216), (228, 547)]) (.e1 [(122, 160), (123, 293), (129, 259), (130, 182), (163, 285), (164, 196), (170, 172), (172, 172), (178, 196), (179, 285), (212, 182), (213, 259), (219, 293), (220, 160)] [(114, 541), (115, 218), (121, 252), (122, 240), (164, 214), (165, 219), (170, 219), (172, 219), (177, 219), (178, 214), (220, 240), (221, 252), (227, 218), (228, 541)])) (.e1 [(122, 157), (123, 288), (129, 255), (130, 190), (163, 297), (164, 201), (170, 163), (172, 163), (178, 201), (179, 297), (212, 190), (213, 255), (219, 288), (220, 157)] [(114, 525), (115, 216), (121, 261), (122, 241), (164, 203), (165, 227), (170, 218), (172, 218), (177, 227), (178, 203), (220, 241), (221, 261), (227, 216), (228, 525)])) (.redProjected 0 1))) (.cut 0 (.e1 [(122, 145), (123, 267), (129, 260), (130, 186), (163, 314), (164, 200), (170, 182), (172, 182), (178, 200), (179, 314), (212, 186), (213, 260), (219, 267), (220, 145)] [(115, 230), (121, 247), (122, 264), (164, 200), (165, 219), (170, 210), (172, 210), (177, 219), (178, 200), (220, 264), (221, 247), (227, 230)]) (.cut 1 (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 281), (129, 259), (130, 176), (163, 298), (164, 196), (170, 177), (172, 177), (178, 196), (179, 298), (212, 176), (213, 259), (219, 281), (220, 160)] [(114, 521), (115, 219), (121, 242), (122, 250), (164, 214), (165, 219), (170, 219), (172, 219), (177, 219), (178, 214), (220, 250), (221, 242), (227, 219), (228, 521)]) (.e1 [(122, 160), (123, 265), (129, 259), (130, 176), (163, 315), (164, 196), (170, 179), (172, 179), (178, 196), (179, 315), (212, 176), (213, 259), (219, 265), (220, 160)] [(114, 496), (115, 220), (121, 235), (122, 258), (164, 209), (165, 224), (170, 219), (172, 219), (177, 224), (178, 209), (220, 258), (221, 235), (227, 220), (228, 496)])) (.cut 3 (.e1 [(122, 157), (123, 267), (129, 260), (130, 187), (163, 312), (164, 198), (170, 169), (172, 169), (178, 198), (179, 312), (212, 187), (213, 260), (219, 267), (220, 157)] [(114, 503), (115, 221), (121, 246), (122, 250), (164, 201), (165, 230), (170, 218), (172, 218), (177, 230), (178, 201), (220, 250), (221, 246), (227, 221), (228, 503)]) (.e1 [(122, 160), (123, 260), (129, 259), (130, 180), (163, 320), (164, 196), (170, 175), (172, 175), (178, 196), (179, 320), (212, 180), (213, 259), (219, 260), (220, 160)] [(115, 220), (121, 236), (122, 256), (164, 205), (165, 229), (170, 219), (172, 219), (177, 229), (178, 205), (220, 256), (221, 236), (227, 220), (228, 491)]))) (.redProjected 0 1)))) (.cut 3 (.e1 [(122, 151), (123, 293), (129, 237), (130, 175), (163, 315), (164, 220), (170, 171), (172, 171), (178, 220), (179, 315), (212, 175), (213, 237), (219, 293), (220, 151)] [(115, 204), (121, 265), (122, 270), (164, 206), (165, 216), (170, 217), (172, 217), (177, 216), (178, 206), (220, 270), (221, 265), (227, 204), (228, 501)]) (.e1 [(122, 151), (123, 265), (129, 242), (130, 174), (163, 340), (164, 216), (170, 178), (172, 178), (178, 216), (179, 340), (212, 174), (213, 242), (219, 265), (220, 151)] [(115, 210), (121, 247), (122, 282), (164, 201), (165, 221), (170, 217), (172, 217), (177, 221), (178, 201), (220, 282), (221, 247), (227, 210), (228, 468)]))) (.cut 2 (.cut 3 (.e1 [(122, 160), (123, 271), (129, 262), (130, 199), (164, 195), (170, 158), (172, 158), (178, 195), (179, 307), (212, 199), (213, 262), (219, 271), (220, 160)] [(115, 221), (121, 255), (122, 235), (164, 196), (165, 240), (170, 219), (172, 219), (177, 240), (178, 196), (220, 235), (221, 255), (227, 221)]) (.e1 [(122, 160), (123, 247), (129, 262), (130, 189), (163, 333), (164, 195), (170, 170), (172, 170), (178, 195), (179, 333), (212, 189), (213, 262), (219, 247), (220, 160)] [(115, 224), (121, 235), (122, 255), (164, 196), (165, 240), (170, 219), (172, 219), (177, 240), (178, 196), (220, 255), (221, 235), (227, 224), (228, 475)])) (.e1 [(122, 157), (123, 253), (129, 240), (130, 187), (163, 356), (164, 213), (170, 164), (172, 164), (178, 213), (179, 356), (212, 187), (213, 240), (219, 253), (220, 157)] [(115, 207), (121, 250), (122, 272), (164, 192), (165, 241), (170, 218), (172, 218), (177, 241), (178, 192), (220, 272), (221, 250), (227, 207)])))

theorem plan696_3_ok : plan696_3.checkAt
    (((((rootAddress ![2, 2] ![3, 2, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 false) 0 true) 1 true) = true := by decide +kernel

def plan696_n0 : Plan := .cut 1 plan696_2 plan696_3

theorem plan696_n0_ok : plan696_n0.checkAt
    ((((rootAddress ![2, 2] ![3, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 false) 0 true) = true :=
  checkAt_cut 1 plan696_2 plan696_3
    ((((rootAddress ![2, 2] ![3, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 false) 0 true)
    (by decide +kernel) plan696_2_ok plan696_3_ok

def plan696_n1 : Plan := .cut 0 plan696_1 plan696_n0

theorem plan696_n1_ok : plan696_n1.checkAt
    (((rootAddress ![2, 2] ![3, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 false) = true :=
  checkAt_cut 0 plan696_1 plan696_n0
    (((rootAddress ![2, 2] ![3, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 false)
    (by decide +kernel) plan696_1_ok plan696_n0_ok

def plan696_4 : Plan :=
  (.cut 0 (.e1 [(122, 128), (123, 262), (129, 231), (130, 244), (164, 199), (170, 166), (172, 166), (178, 199), (212, 244), (213, 231), (219, 262), (220, 128)] [(115, 239), (121, 285), (122, 265), (164, 172), (165, 259), (170, 182), (172, 182), (177, 259), (178, 172), (220, 265), (221, 285), (227, 239)]) (.cut 1 (.cut 2 (.e1 [(122, 157), (123, 248), (129, 233), (130, 224), (164, 188), (170, 159), (172, 159), (178, 188), (179, 375), (212, 224), (213, 233), (219, 248), (220, 157)] [(115, 223), (121, 255), (122, 249), (164, 186), (165, 278), (170, 200), (172, 200), (177, 278), (178, 186), (220, 249), (221, 255), (227, 223), (228, 433)]) (.e1 [(122, 160), (123, 245), (129, 210), (130, 208), (164, 205), (170, 164), (172, 164), (178, 205), (179, 410), (212, 208), (213, 210), (219, 245), (220, 160)] [(115, 205), (121, 256), (122, 277), (164, 191), (165, 274), (170, 200), (172, 200), (177, 274), (178, 191), (220, 277), (221, 256), (227, 205)])) (.redProjected 0 1)))

theorem plan696_4_ok : plan696_4.checkAt
    (((rootAddress ![2, 2] ![3, 2, 0]).child true).child true)
    (childBox (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) 4 true) = true := by decide +kernel

def plan696_n2 : Plan := .cut 4 plan696_n1 plan696_4

theorem plan696_n2_ok : plan696_n2.checkAt
    ((rootAddress ![2, 2] ![3, 2, 0]).child true)
    (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true) = true :=
  checkAt_cut 4 plan696_n1 plan696_4
    ((rootAddress ![2, 2] ![3, 2, 0]).child true)
    (childBox (rootBox ![2, 2] ![3, 2, 0]) 1 true)
    (by decide +kernel) plan696_n1_ok plan696_4_ok

def plan696 : Plan := .cut 1 plan696_0 plan696_n2

theorem plan696_ok : plan696.checkAt
    (rootAddress ![2, 2] ![3, 2, 0])
    (rootBox ![2, 2] ![3, 2, 0]) = true :=
  checkAt_cut 1 plan696_0 plan696_n2
    (rootAddress ![2, 2] ![3, 2, 0])
    (rootBox ![2, 2] ![3, 2, 0])
    (by decide +kernel) plan696_0_ok plan696_n2_ok

theorem root696 : rootCheck plan696 ![2, 2] ![3, 2, 0] = true := plan696_ok

def plan697 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 238), (129, 204), (130, 286), (164, 187), (170, 151), (172, 151), (178, 187), (212, 286), (213, 204), (219, 238), (220, 151)] [(114, 370), (115, 228), (121, 285), (122, 247), (164, 172), (165, 345), (170, 180), (172, 180), (177, 345), (178, 172), (220, 247), (221, 285), (227, 228), (228, 370)]) (.e1 [(122, 157), (123, 223), (129, 213), (164, 204), (170, 143), (172, 143), (178, 204), (212, 263), (213, 213), (219, 223), (220, 157)] [(115, 218), (121, 276), (122, 256), (164, 165), (170, 200), (172, 200), (177, 331), (178, 165), (220, 256), (221, 276), (227, 218)]))

theorem root697 : rootCheck plan697 ![2, 2] ![3, 2, 1] = true := by decide +kernel

def plan698 : Plan :=
  (.cut 1 (.e1 [(122, 151), (123, 238), (129, 204), (164, 187), (165, 281), (170, 151), (172, 151), (177, 281), (178, 187), (213, 204), (219, 238), (220, 151)] [(114, 297), (115, 266), (122, 214), (163, 345), (164, 172), (170, 180), (172, 180), (178, 172), (179, 345), (220, 214), (221, 349), (227, 266), (228, 297)]) (.e1 [(122, 157), (123, 223), (129, 213), (164, 204), (165, 260), (170, 143), (172, 143), (177, 260), (178, 204), (213, 213), (219, 223), (220, 157)] [(114, 282), (122, 211), (164, 165), (170, 200), (172, 200), (178, 165), (220, 211), (227, 265), (228, 282)]))

theorem root698 : rootCheck plan698 ![2, 2] ![3, 2, 2] = true := by decide +kernel

def plan699 : Plan :=
  (.cut 1 (.cut 0 (.e1 [(122, 131), (123, 290), (128, 418), (129, 199), (164, 174), (165, 224), (170, 201), (172, 201), (177, 224), (178, 174), (213, 199), (214, 418), (219, 290), (220, 131)] [(114, 287), (115, 312), (122, 217), (163, 256), (164, 208), (170, 156), (172, 156), (178, 208), (179, 256), (220, 217), (227, 312), (228, 287)]) (.cut 4 (.e1 [(122, 157), (123, 257), (129, 206), (164, 188), (165, 218), (170, 168), (172, 168), (177, 218), (178, 188), (213, 206), (219, 257), (220, 157)] [(114, 270), (115, 285), (122, 200), (163, 284), (164, 196), (170, 186), (172, 186), (178, 196), (179, 284), (220, 200), (221, 379), (227, 285), (228, 270)]) (.cut 1 (.e1 [(122, 157), (123, 279), (128, 419), (129, 194), (164, 176), (165, 205), (170, 189), (172, 189), (177, 205), (178, 176), (213, 194), (214, 419), (219, 279), (220, 157)] [(114, 263), (115, 295), (122, 200), (163, 270), (164, 220), (170, 173), (172, 173), (178, 220), (179, 270), (220, 200), (221, 386), (227, 295), (228, 263)]) (.cut 2 (.e1 [(122, 157), (123, 288), (129, 226), (164, 172), (165, 187), (170, 181), (172, 181), (177, 187), (178, 172), (213, 226), (219, 288), (220, 157)] [(114, 277), (115, 318), (122, 182), (163, 252), (164, 217), (170, 186), (172, 186), (178, 217), (179, 252), (220, 182), (221, 388), (227, 318), (228, 277)]) (.cut 0 (.e1 [(122, 145), (123, 289), (129, 206), (164, 189), (165, 199), (170, 187), (172, 187), (177, 199), (178, 189), (213, 206), (214, 387), (219, 289), (220, 145)] [(114, 273), (115, 297), (122, 203), (163, 246), (164, 211), (170, 179), (172, 179), (178, 211), (179, 246), (220, 203), (227, 297), (228, 273)]) (.cut 3 (.e1 [(122, 157), (123, 297), (128, 370), (129, 210), (164, 192), (165, 192), (170, 173), (172, 173), (177, 192), (178, 192), (213, 210), (214, 370), (219, 297), (220, 157)] [(114, 274), (115, 281), (122, 192), (163, 249), (164, 213), (170, 191), (172, 191), (178, 213), (179, 249), (220, 192), (227, 281), (228, 274)]) (.e1 [(122, 157), (123, 273), (129, 210), (164, 192), (165, 187), (170, 184), (172, 184), (177, 187), (178, 192), (213, 210), (214, 400), (219, 273), (220, 157)] [(114, 257), (115, 301), (121, 402), (122, 195), (163, 249), (164, 213), (170, 191), (172, 191), (178, 213), (179, 249), (220, 195), (221, 402), (227, 301), (228, 257)]))))))) (.cut 0 (.cut 4 (.e1 [(122, 128), (123, 262), (129, 231), (164, 199), (165, 232), (170, 166), (172, 166), (177, 232), (178, 199), (213, 231), (219, 262), (220, 128)] [(114, 303), (122, 213), (163, 259), (164, 172), (170, 182), (172, 182), (178, 172), (179, 259), (220, 213), (227, 306), (228, 303)]) (.e1 [(122, 131), (123, 276), (129, 232), (164, 208), (165, 190), (170, 187), (172, 187), (177, 190), (178, 208), (213, 232), (219, 276), (220, 131)] [(114, 278), (115, 321), (122, 209), (163, 221), (164, 195), (170, 189), (172, 189), (178, 195), (179, 221), (220, 209), (227, 321), (228, 278)])) (.cut 4 (.e1 [(122, 160), (123, 244), (129, 214), (164, 205), (165, 205), (170, 163), (172, 163), (177, 205), (178, 205), (213, 214), (219, 244), (220, 160)] [(114, 259), (115, 286), (122, 200), (163, 273), (164, 189), (170, 203), (172, 203), (178, 189), (179, 273), (220, 200), (227, 286), (228, 259)]) (.cut 1 (.cut 2 (.e1 [(122, 151), (123, 267), (129, 240), (164, 188), (165, 181), (170, 179), (172, 179), (177, 181), (178, 188), (213, 240), (219, 267), (220, 151)] [(114, 271), (115, 332), (122, 187), (163, 240), (164, 203), (170, 198), (172, 198), (178, 203), (179, 240), (220, 187), (227, 332), (228, 271)]) (.cut 0 (.e1 [(122, 148), (123, 279), (128, 379), (129, 220), (164, 202), (165, 189), (170, 176), (172, 176), (177, 189), (178, 202), (213, 220), (214, 379), (219, 279), (220, 148)] [(114, 270), (115, 296), (122, 198), (163, 239), (164, 203), (170, 195), (172, 195), (178, 203), (179, 239), (220, 198), (227, 296), (228, 270)]) (.e1 [(116, 549), (122, 158), (123, 275), (128, 379), (129, 218), (130, 667), (164, 205), (165, 177), (170, 177), (172, 177), (177, 177), (178, 205), (212, 667), (213, 218), (214, 379), (219, 275), (220, 158), (226, 549)] [(114, 256), (115, 296), (121, 424), (122, 192), (163, 238), (164, 210), (170, 204), (172, 204), (178, 210), (179, 238), (220, 192), (221, 424), (227, 296), (228, 256)]))) (.e1 [(122, 154), (123, 267), (128, 382), (129, 241), (164, 214), (165, 171), (170, 170), (172, 170), (177, 171), (178, 214), (213, 241), (214, 382), (219, 267), (220, 154)] [(114, 262), (115, 309), (121, 425), (122, 188), (163, 228), (164, 199), (170, 217), (172, 217), (178, 199), (179, 228), (220, 188), (221, 425), (227, 309), (228, 262)])))))

theorem root699 : rootCheck plan699 ![2, 2] ![3, 2, 3] = true := by decide +kernel

def plan700_0 : Plan :=
  (.cut 4 (.cut 0 (.e1 [(122, 128), (123, 260), (129, 206), (130, 215), (164, 174), (170, 228), (172, 228), (178, 174), (212, 215), (213, 206), (219, 260), (220, 128)] [(114, 408), (115, 251), (121, 245), (122, 310), (164, 211), (165, 243), (170, 157), (172, 157), (177, 243), (178, 211), (220, 310), (221, 245), (227, 251), (228, 408)]) (.cut 1 (.cut 2 (.cut 3 (.cut 4 (.e1 [(122, 160), (123, 269), (129, 209), (130, 196), (164, 168), (170, 202), (172, 202), (178, 168), (212, 196), (213, 209), (219, 269), (220, 160)] [(115, 224), (121, 231), (122, 272), (164, 228), (165, 258), (170, 178), (172, 178), (177, 258), (178, 228), (220, 272), (221, 231), (227, 224)]) (.e1 [(122, 157), (123, 254), (129, 209), (130, 204), (164, 164), (170, 210), (172, 210), (178, 164), (179, 400), (212, 204), (213, 209), (219, 254), (220, 157)] [(115, 233), (121, 225), (122, 279), (164, 223), (165, 265), (170, 173), (172, 173), (177, 265), (178, 223), (220, 279), (221, 225), (227, 233)])) (.e1 [(122, 154), (123, 245), (129, 208), (130, 205), (163, 416), (164, 160), (170, 223), (172, 223), (178, 160), (179, 416), (212, 205), (213, 208), (219, 245), (220, 154)] [(114, 393), (115, 242), (121, 218), (122, 290), (164, 225), (165, 266), (170, 168), (172, 168), (177, 266), (178, 225), (220, 290), (221, 218), (227, 242), (228, 393)])) (.cut 0 (.e1 [(122, 145), (123, 259), (129, 190), (130, 205), (164, 173), (170, 225), (172, 225), (178, 173), (212, 205), (213, 190), (219, 259), (220, 145)] [(115, 231), (121, 237), (122, 310), (164, 225), (165, 257), (170, 161), (172, 161), (177, 257), (178, 225), (220, 310), (221, 237), (227, 231)]) (.cut 4 (.e1 [(122, 157), (123, 259), (129, 194), (130, 187), (163, 418), (164, 176), (170, 224), (172, 224), (178, 176), (179, 418), (212, 187), (213, 194), (219, 259), (220, 157)] [(114, 388), (115, 220), (121, 225), (122, 310), (164, 235), (165, 251), (170, 173), (172, 173), (177, 251), (178, 235), (220, 310), (221, 225), (227, 220), (228, 388)]) (.e1 [(122, 157), (123, 246), (129, 194), (130, 204), (164, 176), (170, 210), (172, 210), (178, 176), (212, 204), (213, 194), (219, 246), (220, 157)] [(114, 373), (115, 224), (121, 231), (122, 300), (164, 220), (165, 270), (170, 173), (172, 173), (177, 270), (178, 220), (220, 300), (221, 231), (227, 224), (228, 373)])))) (.cut 2 (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 145), (123, 264), (129, 226), (130, 193), (164, 174), (170, 212), (172, 212), (178, 174), (212, 193), (213, 226), (219, 264), (220, 145)] [(115, 238), (121, 231), (122, 284), (164, 219), (165, 236), (170, 179), (172, 179), (177, 236), (178, 219), (220, 284), (221, 231), (227, 238)]) (.cut 1 (.e1 [(122, 160), (123, 262), (129, 223), (130, 186), (163, 366), (164, 169), (170, 208), (172, 208), (178, 169), (179, 366), (212, 186), (213, 223), (219, 262), (220, 160)] [(114, 438), (115, 229), (121, 221), (122, 275), (164, 229), (165, 246), (170, 184), (172, 184), (177, 246), (178, 229), (220, 275), (221, 221), (227, 229), (228, 438)]) (.cut 2 (.e1 [(122, 158), (123, 257), (129, 238), (130, 187), (163, 350), (164, 173), (170, 199), (172, 199), (178, 173), (179, 350), (212, 187), (213, 238), (219, 257), (220, 158)] [(114, 454), (115, 232), (116, 588), (121, 223), (122, 267), (164, 219), (165, 242), (170, 193), (172, 193), (177, 242), (178, 219), (220, 267), (221, 223), (226, 588), (227, 232), (228, 454)]) (.e1 [(122, 158), (123, 257), (129, 227), (130, 183), (163, 365), (164, 180), (170, 199), (172, 199), (178, 180), (179, 365), (212, 183), (213, 227), (219, 257), (220, 158)] [(114, 437), (115, 224), (121, 225), (122, 278), (164, 219), (165, 242), (170, 193), (172, 193), (177, 242), (178, 219), (220, 278), (221, 225), (226, 588), (227, 224), (228, 437)])))) (.cut 0 (.e1 [(122, 145), (123, 249), (129, 226), (130, 211), (164, 174), (170, 198), (172, 198), (178, 174), (212, 211), (213, 226), (219, 249), (220, 145)] [(115, 241), (121, 236), (122, 276), (164, 204), (165, 255), (170, 179), (172, 179), (177, 255), (178, 204), (220, 276), (221, 236), (227, 241), (228, 425)]) (.cut 1 (.e1 [(122, 158), (123, 247), (129, 221), (130, 200), (163, 388), (164, 171), (170, 198), (172, 198), (178, 171), (179, 388), (212, 200), (213, 221), (219, 247), (220, 158)] [(115, 231), (121, 226), (122, 274), (164, 214), (165, 262), (170, 184), (172, 184), (177, 262), (178, 214), (220, 274), (221, 226), (227, 231), (228, 415)]) (.cut 2 (.e1 [(122, 158), (123, 241), (129, 235), (130, 198), (163, 375), (164, 175), (170, 192), (172, 192), (178, 175), (179, 375), (212, 198), (213, 235), (219, 241), (220, 158)] [(114, 428), (115, 233), (116, 617), (121, 224), (122, 269), (164, 207), (165, 257), (170, 193), (172, 193), (177, 257), (178, 207), (214, 626), (220, 269), (221, 224), (226, 617), (227, 233), (228, 428)]) (.e1 [(81, 573), (122, 158), (123, 241), (129, 225), (130, 195), (163, 389), (164, 182), (170, 192), (172, 192), (178, 182), (179, 389), (212, 195), (213, 225), (219, 241), (220, 158), (261, 573)] [(114, 413), (115, 225), (116, 616), (121, 227), (122, 280), (128, 648), (164, 207), (165, 257), (170, 193), (172, 193), (177, 257), (178, 207), (214, 648), (220, 280), (221, 227), (226, 616), (227, 225), (228, 413)]))))) (.cut 0 (.e1 [(122, 145), (123, 237), (129, 226), (130, 196), (164, 174), (170, 220), (172, 220), (178, 174), (212, 196), (213, 226), (219, 237), (220, 145)] [(115, 246), (121, 220), (122, 301), (164, 211), (165, 246), (170, 179), (172, 179), (177, 246), (178, 211), (220, 301), (221, 220), (227, 246), (228, 406)]) (.cut 4 (.e1 [(122, 161), (123, 236), (129, 226), (130, 180), (163, 397), (164, 185), (170, 204), (172, 204), (178, 185), (179, 397), (212, 180), (213, 226), (219, 236), (220, 161)] [(114, 404), (115, 223), (121, 216), (122, 296), (164, 215), (165, 247), (170, 197), (172, 197), (177, 247), (178, 215), (220, 296), (221, 216), (227, 223), (228, 404)]) (.cut 0 (.e1 [(122, 154), (123, 225), (129, 229), (130, 198), (164, 176), (170, 208), (172, 208), (178, 176), (212, 198), (213, 229), (219, 225), (220, 154)] [(114, 395), (115, 241), (121, 216), (122, 292), (164, 205), (165, 259), (170, 188), (172, 188), (177, 259), (178, 205), (220, 292), (221, 216), (227, 241), (228, 395)]) (.e1 [(81, 553), (122, 161), (123, 227), (129, 226), (130, 192), (163, 408), (164, 177), (165, 611), (170, 205), (172, 205), (177, 611), (178, 177), (179, 408), (212, 192), (213, 226), (219, 227), (220, 161), (261, 553)] [(108, 788), (114, 395), (115, 233), (116, 647), (121, 214), (122, 290), (128, 645), (163, 737), (164, 210), (165, 260), (170, 192), (172, 192), (177, 260), (178, 210), (179, 737), (214, 645), (220, 290), (221, 214), (226, 647), (227, 233), (228, 395), (234, 788)]))))) (.cut 0 (.e1 [(122, 145), (123, 246), (129, 206), (130, 194), (163, 416), (164, 189), (170, 212), (172, 212), (178, 189), (179, 416), (212, 194), (213, 206), (219, 246), (220, 145)] [(114, 389), (115, 227), (121, 235), (122, 313), (164, 211), (165, 246), (170, 179), (172, 179), (177, 246), (178, 211), (220, 313), (221, 235), (227, 227), (228, 389)]) (.cut 4 (.cut 3 (.e1 [(81, 560), (121, 708), (122, 160), (123, 258), (129, 215), (130, 182), (163, 380), (164, 188), (165, 643), (170, 195), (172, 195), (177, 643), (178, 188), (179, 380), (212, 182), (213, 215), (219, 258), (220, 160), (221, 708), (261, 560)] [(65, 836), (108, 769), (114, 420), (115, 214), (116, 586), (120, 755), (121, 231), (122, 287), (128, 670), (163, 770), (164, 218), (165, 245), (170, 194), (172, 194), (177, 245), (178, 218), (179, 770), (214, 670), (220, 287), (221, 231), (222, 755), (226, 586), (227, 214), (228, 420), (234, 769), (277, 836)]) (.cut 1 (.e1 [(122, 157), (123, 240), (129, 202), (130, 184), (164, 184), (170, 222), (172, 222), (178, 184), (179, 433), (212, 184), (213, 202), (219, 240), (220, 157)] [(114, 374), (115, 223), (121, 220), (122, 320), (164, 224), (165, 250), (170, 181), (172, 181), (177, 250), (178, 224), (220, 320), (221, 220), (227, 223), (228, 374)]) (.e1 [(81, 507), (122, 158), (123, 237), (129, 214), (130, 175), (164, 191), (170, 214), (172, 214), (178, 191), (179, 417), (212, 175), (213, 214), (219, 237), (220, 158), (261, 507)] [(114, 386), (115, 220), (121, 217), (122, 318), (164, 219), (165, 242), (170, 193), (172, 193), (177, 242), (178, 219), (220, 318), (221, 217), (227, 220), (228, 386)]))) (.cut 3 (.cut 0 (.e1 [(122, 154), (123, 245), (129, 209), (130, 198), (164, 191), (170, 192), (172, 192), (178, 191), (212, 198), (213, 209), (219, 245), (220, 154)] [(114, 394), (115, 219), (121, 238), (122, 293), (164, 205), (165, 259), (170, 188), (172, 188), (177, 259), (178, 205), (220, 293), (221, 238), (227, 219), (228, 394)]) (.e1 [(122, 161), (123, 242), (129, 211), (130, 192), (163, 408), (164, 189), (170, 193), (172, 193), (178, 189), (179, 408), (212, 192), (213, 211), (219, 242), (220, 161)] [(114, 394), (115, 216), (121, 230), (122, 291), (164, 210), (165, 260), (170, 192), (172, 192), (177, 260), (178, 210), (220, 291), (221, 230), (226, 614), (227, 216), (228, 394)])) (.cut 0 (.e1 [(122, 154), (123, 225), (129, 209), (130, 195), (164, 191), (170, 208), (172, 208), (178, 191), (212, 195), (213, 209), (219, 225), (220, 154)] [(114, 366), (115, 226), (121, 225), (122, 316), (164, 205), (165, 259), (170, 188), (172, 188), (177, 259), (178, 205), (220, 316), (221, 225), (227, 226), (228, 366)]) (.e1 [(122, 160), (123, 222), (129, 211), (130, 190), (163, 442), (164, 193), (170, 204), (172, 204), (178, 193), (179, 442), (212, 190), (213, 211), (219, 222), (220, 160), (261, 514)] [(114, 365), (115, 222), (121, 221), (122, 313), (164, 206), (165, 261), (170, 194), (172, 194), (177, 261), (178, 206), (220, 313), (221, 221), (227, 222), (228, 365)])))))))) (.cut 0 (.e1 [(122, 134), (123, 229), (129, 199), (130, 235), (164, 183), (170, 213), (172, 213), (178, 183), (212, 235), (213, 199), (219, 229), (220, 134)] [(115, 249), (121, 247), (122, 314), (164, 193), (165, 274), (170, 163), (172, 163), (177, 274), (178, 193), (220, 314), (221, 247), (227, 249)]) (.cut 0 (.cut 1 (.e1 [(122, 145), (123, 240), (129, 186), (130, 245), (164, 169), (170, 206), (172, 206), (178, 169), (212, 245), (213, 186), (219, 240), (220, 145)] [(115, 241), (121, 248), (122, 291), (164, 205), (165, 300), (170, 157), (172, 157), (177, 300), (178, 205), (220, 291), (221, 248), (227, 241), (228, 356)]) (.e1 [(122, 147), (123, 221), (129, 209), (130, 229), (163, 452), (164, 184), (170, 195), (172, 195), (178, 184), (179, 452), (212, 229), (213, 209), (219, 221), (220, 147)] [(114, 364), (115, 240), (121, 239), (122, 295), (164, 190), (165, 284), (170, 178), (172, 178), (177, 284), (178, 190), (220, 295), (221, 239), (227, 240), (228, 364)])) (.cut 1 (.cut 4 (.cut 2 (.e1 [(122, 158), (123, 232), (129, 210), (130, 222), (164, 160), (170, 205), (172, 205), (178, 160), (212, 222), (213, 210), (219, 232), (220, 158)] [(114, 379), (115, 243), (121, 223), (122, 276), (164, 211), (165, 290), (170, 172), (172, 172), (177, 290), (178, 211), (220, 276), (221, 223), (227, 243), (228, 379)]) (.e1 [(122, 158), (123, 232), (129, 190), (130, 219), (164, 176), (170, 205), (172, 205), (178, 176), (179, 465), (212, 219), (213, 190), (219, 232), (220, 158)] [(114, 351), (115, 227), (121, 233), (122, 298), (164, 211), (165, 290), (170, 172), (172, 172), (177, 290), (178, 211), (220, 298), (221, 233), (227, 227), (228, 351)])) (.e1 [(122, 158), (123, 222), (129, 197), (130, 240), (164, 170), (170, 196), (172, 196), (178, 170), (212, 240), (213, 197), (219, 222), (220, 158)] [(114, 348), (115, 238), (121, 235), (122, 280), (164, 200), (165, 313), (170, 172), (172, 172), (177, 313), (178, 200), (220, 280), (221, 235), (227, 238), (228, 348)])) (.cut 4 (.cut 2 (.cut 3 (.e1 [(122, 160), (123, 228), (129, 226), (130, 211), (164, 181), (170, 183), (172, 183), (178, 181), (179, 409), (212, 211), (213, 226), (219, 228), (220, 160)] [(115, 230), (121, 230), (122, 272), (164, 196), (165, 277), (170, 194), (172, 194), (177, 277), (178, 196), (220, 272), (221, 230), (227, 230), (228, 395)]) (.e1 [(122, 160), (123, 208), (129, 226), (130, 207), (164, 181), (170, 199), (172, 199), (178, 181), (179, 441), (212, 207), (213, 226), (219, 208), (220, 160)] [(114, 368), (115, 239), (121, 215), (122, 294), (164, 196), (165, 277), (170, 194), (172, 194), (177, 277), (178, 196), (220, 294), (221, 215), (227, 239), (228, 368)])) (.cut 3 (.e1 [(122, 160), (123, 228), (129, 206), (130, 207), (164, 197), (170, 183), (172, 183), (178, 197), (179, 441), (212, 207), (213, 206), (219, 228), (220, 160)] [(114, 368), (115, 215), (121, 239), (122, 294), (164, 196), (165, 277), (170, 194), (172, 194), (177, 277), (178, 196), (220, 294), (221, 239), (227, 215), (228, 368)]) (.cut 0 (.e1 [(122, 154), (123, 213), (129, 209), (130, 215), (164, 191), (170, 196), (172, 196), (178, 191), (212, 215), (213, 209), (219, 213), (220, 154)] [(114, 353), (115, 231), (121, 231), (122, 305), (164, 192), (165, 281), (170, 188), (172, 188), (177, 281), (178, 192), (220, 305), (221, 231), (227, 231), (228, 353)]) (.e1 [(81, 534), (122, 160), (123, 210), (129, 211), (130, 210), (163, 462), (164, 193), (170, 192), (172, 192), (178, 193), (179, 462), (212, 210), (213, 211), (219, 210), (220, 160), (261, 534)] [(114, 351), (115, 227), (121, 227), (122, 302), (164, 193), (165, 283), (170, 194), (172, 194), (177, 283), (178, 193), (220, 302), (221, 227), (227, 227), (228, 351)])))) (.e1 [(122, 158), (123, 208), (129, 213), (130, 233), (164, 186), (170, 182), (172, 182), (178, 186), (179, 466), (212, 233), (213, 213), (219, 208), (220, 158)] [(114, 352), (115, 234), (121, 235), (122, 283), (164, 185), (165, 305), (170, 190), (172, 190), (177, 305), (178, 185), (220, 283), (221, 235), (227, 234), (228, 352)]))))))

theorem plan700_0_ok : plan700_0.checkAt
    ((rootAddress ![2, 2] ![3, 3, 0]).child false)
    (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 false) = true := by decide +kernel

def plan700_1 : Plan :=
  (.cut 1 (.e1 [(122, 134), (123, 244), (129, 225), (130, 199), (164, 192), (170, 211), (172, 211), (178, 192), (179, 395), (212, 199), (213, 225), (219, 244), (220, 134)] [(115, 242), (121, 239), (122, 310), (164, 200), (165, 234), (170, 180), (172, 180), (177, 234), (178, 200), (220, 310), (221, 239), (227, 242), (228, 412)]) (.e1 [(122, 131), (123, 242), (129, 247), (130, 189), (164, 207), (170, 202), (172, 202), (178, 207), (212, 189), (213, 247), (219, 242), (220, 131)] [(115, 241), (121, 241), (122, 307), (164, 191), (165, 218), (170, 196), (172, 196), (177, 218), (178, 191), (220, 307), (221, 241), (227, 241), (228, 439)]))

theorem plan700_1_ok : plan700_1.checkAt
    ((((rootAddress ![2, 2] ![3, 3, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 false) 0 false) = true := by decide +kernel

def plan700_2 : Plan :=
  (.cut 2 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 253), (129, 242), (130, 183), (163, 354), (164, 191), (170, 201), (172, 201), (178, 191), (179, 354), (212, 183), (213, 242), (219, 253), (220, 145)] [(115, 233), (121, 231), (122, 287), (164, 207), (165, 226), (170, 196), (172, 196), (177, 226), (178, 207), (220, 287), (221, 231), (227, 233)]) (.cut 1 (.cut 4 (.cut 2 (.e1 [(122, 160), (123, 257), (129, 249), (130, 178), (163, 335), (164, 182), (170, 194), (172, 194), (178, 182), (179, 335), (212, 178), (213, 249), (219, 257), (220, 160)] [(114, 471), (115, 228), (121, 222), (122, 266), (164, 217), (165, 231), (170, 205), (172, 205), (177, 231), (178, 217), (220, 266), (221, 222), (227, 228), (228, 471)]) (.e1 [(122, 160), (123, 257), (129, 239), (130, 174), (163, 349), (164, 189), (170, 194), (172, 194), (178, 189), (179, 349), (212, 174), (213, 239), (219, 257), (220, 160)] [(115, 219), (121, 225), (122, 278), (164, 217), (165, 231), (170, 205), (172, 205), (177, 231), (178, 217), (220, 278), (221, 225), (227, 219), (228, 453)])) (.cut 3 (.cut 2 (.e1 [(122, 160), (123, 256), (129, 249), (130, 183), (163, 336), (164, 182), (170, 189), (172, 189), (178, 182), (179, 336), (212, 183), (213, 249), (219, 256), (220, 160)] [(114, 470), (115, 228), (121, 226), (122, 262), (164, 213), (165, 236), (170, 205), (172, 205), (177, 236), (178, 213), (220, 262), (221, 226), (227, 228), (228, 470)]) (.e1 [(122, 160), (123, 253), (129, 234), (130, 181), (163, 361), (164, 189), (170, 190), (172, 190), (178, 189), (179, 361), (212, 181), (213, 234), (219, 253), (220, 160)] [(114, 441), (115, 219), (121, 228), (122, 277), (164, 212), (165, 240), (170, 203), (172, 203), (177, 240), (178, 212), (220, 277), (221, 228), (227, 219), (228, 441)])) (.e1 [(122, 158), (123, 242), (129, 242), (130, 182), (163, 363), (164, 184), (170, 195), (172, 195), (178, 184), (179, 363), (212, 182), (213, 242), (219, 242), (220, 158)] [(114, 438), (115, 228), (121, 220), (122, 278), (164, 210), (165, 240), (170, 202), (172, 202), (177, 240), (178, 210), (220, 278), (221, 220), (227, 228), (228, 438)]))) (.cut 4 (.e1 [(81, 586), (122, 160), (123, 253), (129, 255), (130, 172), (163, 334), (164, 192), (165, 685), (170, 190), (172, 190), (177, 685), (178, 192), (179, 334), (212, 172), (213, 255), (219, 253), (220, 160), (261, 586)] [(114, 471), (115, 223), (116, 596), (121, 223), (122, 271), (128, 592), (164, 212), (165, 226), (170, 215), (172, 215), (177, 226), (178, 212), (214, 592), (220, 271), (221, 223), (226, 596), (227, 223), (228, 471)]) (.cut 3 (.e1 [(122, 158), (123, 251), (129, 249), (130, 180), (163, 344), (164, 190), (170, 186), (172, 186), (178, 190), (179, 344), (212, 180), (213, 249), (219, 251), (220, 158)] [(114, 461), (115, 223), (116, 597), (121, 228), (122, 270), (128, 603), (164, 208), (165, 234), (170, 209), (172, 209), (177, 234), (178, 208), (214, 603), (220, 270), (221, 228), (226, 597), (227, 223), (228, 461)]) (.e1 [(122, 157), (123, 238), (129, 252), (130, 179), (163, 357), (164, 189), (170, 194), (172, 194), (178, 189), (179, 357), (212, 179), (213, 252), (219, 238), (220, 157)] [(114, 445), (115, 229), (121, 220), (122, 280), (164, 206), (165, 234), (170, 209), (172, 209), (177, 234), (178, 206), (220, 280), (221, 220), (227, 229), (228, 445)]))))) (.e1 [(81, 550), (122, 157), (123, 228), (129, 252), (130, 176), (163, 372), (164, 189), (165, 666), (170, 202), (172, 202), (177, 666), (178, 189), (179, 372), (212, 176), (213, 252), (219, 228), (220, 157), (261, 550)] [(114, 429), (115, 232), (116, 645), (120, 743), (121, 212), (122, 292), (128, 599), (164, 206), (165, 234), (170, 209), (172, 209), (177, 234), (178, 206), (214, 599), (220, 292), (221, 212), (222, 743), (226, 645), (227, 232), (228, 429), (234, 777)])) (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 238), (129, 242), (130, 202), (164, 191), (170, 187), (172, 187), (178, 191), (179, 373), (212, 202), (213, 242), (219, 238), (220, 145)] [(115, 236), (121, 237), (122, 279), (164, 191), (165, 246), (170, 196), (172, 196), (177, 246), (178, 191), (220, 279), (221, 237), (227, 236), (228, 432)]) (.cut 1 (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 246), (129, 239), (130, 192), (163, 363), (164, 185), (170, 183), (172, 183), (178, 185), (179, 363), (212, 192), (213, 239), (219, 246), (220, 160)] [(114, 439), (115, 224), (121, 230), (122, 267), (164, 204), (165, 251), (170, 203), (172, 203), (177, 251), (178, 204), (220, 267), (221, 230), (227, 224), (228, 439)]) (.e1 [(122, 160), (123, 235), (129, 239), (130, 189), (163, 378), (164, 185), (170, 190), (172, 190), (178, 185), (179, 378), (212, 189), (213, 239), (219, 235), (220, 160)] [(114, 424), (115, 227), (121, 222), (122, 277), (164, 204), (165, 251), (170, 203), (172, 203), (177, 251), (178, 204), (220, 277), (221, 222), (227, 227), (228, 424)])) (.e1 [(122, 158), (123, 231), (129, 237), (130, 198), (163, 386), (164, 188), (170, 182), (172, 182), (178, 188), (179, 386), (212, 198), (213, 237), (219, 231), (220, 158)] [(114, 416), (115, 227), (121, 228), (122, 274), (164, 196), (165, 259), (170, 202), (172, 202), (177, 259), (178, 196), (220, 274), (221, 228), (227, 227), (228, 416)])) (.cut 4 (.cut 3 (.e1 [(122, 160), (123, 240), (129, 247), (130, 188), (163, 359), (164, 193), (170, 177), (172, 177), (178, 193), (179, 359), (212, 188), (213, 247), (219, 240), (220, 160)] [(114, 444), (115, 222), (121, 230), (122, 268), (164, 198), (165, 246), (170, 212), (172, 212), (177, 246), (178, 198), (220, 268), (221, 230), (227, 222), (228, 444)]) (.e1 [(122, 160), (123, 230), (129, 247), (130, 185), (163, 374), (164, 193), (170, 185), (172, 185), (178, 193), (179, 374), (212, 185), (213, 247), (219, 230), (220, 160)] [(114, 428), (115, 225), (121, 222), (122, 280), (164, 198), (165, 246), (170, 212), (172, 212), (177, 246), (178, 198), (220, 280), (221, 222), (227, 225), (228, 428)])) (.redProjected 0 1)))) (.cut 0 (.e1 [(122, 145), (123, 219), (129, 242), (130, 197), (164, 191), (170, 201), (172, 201), (178, 191), (212, 197), (213, 242), (219, 219), (220, 145)] [(115, 243), (121, 223), (122, 301), (164, 191), (165, 246), (170, 196), (172, 196), (177, 246), (178, 191), (220, 301), (221, 223), (227, 243), (228, 403)]) (.cut 0 (.e1 [(122, 155), (123, 216), (129, 242), (130, 191), (164, 189), (170, 198), (172, 198), (178, 189), (179, 404), (212, 191), (213, 242), (219, 216), (220, 155)] [(114, 399), (115, 236), (121, 215), (122, 295), (164, 196), (165, 252), (170, 203), (172, 203), (177, 252), (178, 196), (220, 295), (221, 215), (227, 236), (228, 399)]) (.e1 [(81, 546), (122, 161), (123, 219), (129, 239), (130, 185), (163, 402), (164, 189), (165, 625), (170, 196), (172, 196), (177, 625), (178, 189), (179, 402), (212, 185), (213, 239), (219, 219), (220, 161), (261, 546)] [(114, 400), (115, 229), (121, 214), (122, 294), (128, 621), (164, 201), (165, 252), (170, 206), (172, 206), (177, 252), (178, 201), (214, 621), (220, 294), (221, 214), (227, 229), (228, 400)]))))) (.cut 0 (.cut 3 (.e1 [(122, 148), (123, 246), (129, 220), (130, 187), (163, 394), (164, 202), (170, 194), (172, 194), (178, 202), (179, 394), (212, 187), (213, 220), (219, 246), (220, 148)] [(115, 219), (121, 239), (122, 303), (164, 203), (165, 239), (170, 195), (172, 195), (177, 239), (178, 203), (220, 303), (221, 239), (227, 219), (228, 409)]) (.e1 [(122, 145), (123, 226), (129, 223), (130, 184), (164, 206), (170, 209), (172, 209), (178, 206), (212, 184), (213, 223), (219, 226), (220, 145)] [(114, 382), (115, 228), (121, 228), (122, 329), (164, 199), (165, 236), (170, 196), (172, 196), (177, 236), (178, 199), (220, 329), (221, 228), (227, 228), (228, 382)])) (.cut 3 (.cut 4 (.cut 1 (.e1 [(122, 160), (123, 252), (129, 226), (130, 177), (163, 375), (164, 199), (170, 189), (172, 189), (178, 199), (179, 375), (212, 177), (213, 226), (219, 252), (220, 160)] [(114, 426), (115, 211), (121, 231), (122, 289), (164, 211), (165, 239), (170, 205), (172, 205), (177, 239), (178, 211), (220, 289), (221, 231), (227, 211), (228, 426)]) (.e1 [(122, 158), (123, 248), (129, 228), (130, 172), (163, 377), (164, 206), (170, 190), (172, 190), (178, 206), (179, 377), (212, 172), (213, 228), (219, 248), (220, 158)] [(114, 423), (115, 209), (121, 230), (122, 298), (164, 209), (165, 233), (170, 209), (172, 209), (177, 233), (178, 209), (220, 298), (221, 230), (227, 209), (228, 423)])) (.e1 [(122, 158), (123, 235), (129, 223), (130, 187), (163, 402), (164, 201), (170, 186), (172, 186), (178, 201), (179, 402), (212, 187), (213, 223), (219, 235), (220, 158)] [(114, 400), (115, 215), (116, 629), (121, 232), (122, 294), (128, 655), (164, 200), (165, 252), (170, 204), (172, 204), (177, 252), (178, 200), (214, 655), (220, 294), (221, 232), (226, 629), (227, 215), (228, 400)])) (.cut 4 (.e1 [(81, 493), (122, 157), (123, 226), (129, 222), (130, 172), (163, 421), (164, 204), (170, 208), (172, 208), (178, 204), (179, 421), (212, 172), (213, 222), (219, 226), (220, 157), (261, 493)] [(114, 381), (115, 218), (121, 218), (122, 327), (128, 663), (164, 209), (165, 237), (170, 204), (172, 204), (177, 237), (178, 209), (214, 663), (220, 327), (221, 218), (227, 218), (228, 381)]) (.cut 0 (.e1 [(122, 154), (123, 217), (129, 221), (130, 189), (164, 204), (170, 199), (172, 199), (178, 204), (212, 189), (213, 221), (219, 217), (220, 154)] [(114, 371), (115, 224), (121, 224), (122, 319), (164, 196), (165, 252), (170, 201), (172, 201), (177, 252), (178, 196), (220, 319), (221, 224), (227, 224), (228, 371)]) (.cut 1 (.e1 [(122, 161), (123, 216), (129, 219), (130, 185), (163, 438), (164, 201), (170, 198), (172, 198), (178, 201), (179, 438), (212, 185), (213, 219), (219, 216), (220, 161), (261, 511)] [(114, 368), (115, 219), (121, 219), (122, 315), (164, 200), (165, 257), (170, 204), (172, 204), (177, 257), (178, 200), (220, 315), (221, 219), (227, 219), (228, 368)]) (.e1 [(122, 160), (123, 212), (129, 225), (130, 183), (163, 435), (164, 207), (170, 194), (172, 194), (178, 207), (179, 435), (212, 183), (213, 225), (219, 212), (220, 160)] [(114, 370), (115, 219), (121, 220), (122, 317), (164, 196), (165, 253), (170, 210), (172, 210), (177, 253), (178, 196), (220, 317), (221, 220), (227, 219), (228, 370)])))))))

theorem plan700_2_ok : plan700_2.checkAt
    (((((rootAddress ![2, 2] ![3, 3, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 false) 0 true) 1 false) = true := by decide +kernel

def plan700_3 : Plan :=
  (.cut 2 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 246), (129, 260), (130, 178), (163, 341), (164, 200), (170, 194), (172, 194), (178, 200), (179, 341), (212, 178), (213, 260), (219, 246), (220, 145)] [(115, 233), (121, 230), (122, 285), (164, 200), (165, 219), (170, 210), (172, 210), (177, 219), (178, 200), (220, 285), (221, 230), (227, 233)]) (.cut 1 (.cut 4 (.e1 [(122, 160), (123, 250), (129, 259), (130, 170), (163, 332), (164, 196), (170, 187), (172, 187), (178, 196), (179, 332), (212, 170), (213, 259), (219, 250), (220, 160)] [(115, 222), (121, 224), (122, 272), (164, 209), (165, 224), (170, 219), (172, 219), (177, 224), (178, 209), (220, 272), (221, 224), (227, 222), (228, 474)]) (.e1 [(122, 158), (123, 243), (129, 257), (130, 175), (163, 345), (164, 199), (170, 184), (172, 184), (178, 199), (179, 345), (212, 175), (213, 257), (219, 243), (220, 158)] [(114, 459), (115, 222), (121, 225), (122, 276), (128, 589), (164, 203), (165, 230), (170, 219), (172, 219), (177, 230), (178, 203), (214, 589), (220, 276), (221, 225), (226, 614), (227, 222), (228, 459)])) (.redProjected 0 1))) (.e1 [(122, 157), (123, 224), (129, 260), (130, 172), (164, 198), (170, 197), (172, 197), (178, 198), (179, 368), (212, 172), (213, 260), (219, 224), (220, 157)] [(115, 230), (121, 212), (122, 294), (164, 201), (165, 230), (170, 218), (172, 218), (177, 230), (178, 201), (220, 294), (221, 212), (227, 230), (228, 433)])) (.cut 3 (.cut 0 (.e1 [(122, 145), (123, 234), (129, 255), (130, 192), (164, 204), (170, 182), (172, 182), (178, 204), (179, 362), (212, 192), (213, 255), (219, 234), (220, 145)] [(115, 232), (121, 236), (122, 284), (164, 187), (165, 235), (170, 210), (172, 210), (177, 235), (178, 187), (220, 284), (221, 236), (227, 232)]) (.redProjected 0 1)) (.e1 [(122, 157), (123, 216), (129, 260), (130, 182), (164, 198), (170, 189), (172, 189), (178, 198), (179, 378), (212, 182), (213, 260), (219, 216), (220, 157)] [(114, 423), (115, 232), (121, 215), (122, 289), (164, 192), (165, 241), (170, 218), (172, 218), (177, 241), (178, 192), (220, 289), (221, 215), (227, 232), (228, 423)]))) (.cut 0 (.e1 [(81, 506), (122, 145), (123, 230), (129, 232), (130, 181), (163, 403), (164, 214), (170, 196), (172, 196), (178, 214), (179, 403), (212, 181), (213, 232), (219, 230), (220, 145), (221, 708), (261, 506)] [(114, 400), (115, 222), (116, 647), (121, 233), (122, 319), (128, 646), (164, 194), (165, 231), (170, 205), (172, 205), (177, 231), (178, 194), (214, 646), (220, 319), (221, 233), (226, 647), (227, 222), (228, 400)]) (.cut 3 (.cut 4 (.e1 [(122, 157), (123, 237), (129, 239), (130, 168), (163, 381), (164, 221), (170, 183), (172, 183), (178, 221), (179, 381), (212, 168), (213, 239), (219, 237), (220, 157)] [(115, 207), (121, 231), (122, 306), (164, 198), (165, 228), (170, 223), (172, 223), (177, 228), (178, 198), (220, 306), (221, 231), (227, 207), (228, 421)]) (.redProjected 0 1)) (.cut 4 (.e1 [(122, 157), (123, 217), (129, 239), (130, 164), (164, 221), (170, 199), (172, 199), (178, 221), (212, 164), (213, 239), (219, 217), (220, 157)] [(114, 389), (115, 215), (121, 217), (122, 332), (164, 198), (165, 228), (170, 223), (172, 223), (177, 228), (178, 198), (220, 332), (221, 217), (227, 215), (228, 389)]) (.redProjected 0 1)))))

theorem plan700_3_ok : plan700_3.checkAt
    (((((rootAddress ![2, 2] ![3, 3, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 false) 0 true) 1 true) = true := by decide +kernel

def plan700_n0 : Plan := .cut 1 plan700_2 plan700_3

theorem plan700_n0_ok : plan700_n0.checkAt
    ((((rootAddress ![2, 2] ![3, 3, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 false) 0 true) = true :=
  checkAt_cut 1 plan700_2 plan700_3
    ((((rootAddress ![2, 2] ![3, 3, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 false) 0 true)
    (by decide +kernel) plan700_2_ok plan700_3_ok

def plan700_n1 : Plan := .cut 0 plan700_1 plan700_n0

theorem plan700_n1_ok : plan700_n1.checkAt
    (((rootAddress ![2, 2] ![3, 3, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 false) = true :=
  checkAt_cut 0 plan700_1 plan700_n0
    (((rootAddress ![2, 2] ![3, 3, 0]).child true).child false)
    (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 false)
    (by decide +kernel) plan700_1_ok plan700_n0_ok

def plan700_4 : Plan :=
  (.cut 0 (.e1 [(122, 128), (123, 222), (129, 231), (130, 232), (164, 199), (170, 190), (172, 190), (178, 199), (212, 232), (213, 231), (219, 222), (220, 128)] [(115, 251), (121, 252), (122, 301), (164, 172), (165, 259), (170, 182), (172, 182), (177, 259), (178, 172), (220, 301), (221, 252), (227, 251), (228, 394)]) (.cut 0 (.cut 1 (.cut 4 (.e1 [(81, 556), (122, 145), (123, 221), (129, 228), (130, 215), (164, 194), (170, 187), (172, 187), (178, 194), (212, 215), (213, 228), (219, 221), (220, 145), (261, 556)] [(114, 389), (115, 237), (121, 238), (122, 292), (164, 184), (165, 265), (170, 192), (172, 192), (177, 265), (178, 184), (220, 292), (221, 238), (227, 237), (228, 389)]) (.e1 [(122, 145), (123, 198), (129, 228), (130, 241), (164, 194), (170, 181), (172, 181), (178, 194), (212, 241), (213, 228), (219, 198), (220, 145)] [(115, 249), (121, 238), (122, 291), (164, 170), (165, 296), (170, 192), (172, 192), (177, 296), (178, 170), (220, 291), (221, 238), (227, 249)])) (.redProjected 0 1)) (.cut 1 (.cut 4 (.cut 2 (.cut 3 (.e1 [(122, 160), (123, 222), (129, 234), (130, 207), (164, 189), (170, 177), (172, 177), (178, 189), (179, 405), (212, 207), (213, 234), (219, 222), (220, 160)] [(115, 228), (121, 230), (122, 274), (164, 189), (165, 273), (170, 203), (172, 203), (177, 273), (178, 189), (220, 274), (221, 230), (227, 228), (228, 399)]) (.e1 [(122, 157), (123, 206), (129, 242), (130, 205), (164, 189), (170, 188), (172, 188), (178, 189), (212, 205), (213, 242), (219, 206), (220, 157)] [(114, 386), (115, 239), (121, 219), (122, 288), (164, 186), (165, 270), (170, 204), (172, 204), (177, 270), (178, 186), (220, 288), (221, 219), (227, 239), (228, 386)])) (.cut 3 (.e1 [(122, 160), (123, 222), (129, 224), (130, 205), (164, 197), (170, 177), (172, 177), (178, 197), (212, 205), (213, 224), (219, 222), (220, 160)] [(114, 385), (115, 221), (121, 234), (122, 284), (164, 189), (165, 273), (170, 203), (172, 203), (177, 273), (178, 189), (220, 284), (221, 234), (227, 221), (228, 385)]) (.e1 [(81, 523), (122, 157), (123, 206), (129, 222), (130, 202), (164, 204), (170, 188), (172, 188), (178, 204), (179, 451), (212, 202), (213, 222), (219, 206), (220, 157), (261, 523)] [(114, 359), (115, 226), (121, 227), (122, 309), (164, 186), (165, 270), (170, 204), (172, 204), (177, 270), (178, 186), (220, 309), (221, 227), (227, 226), (228, 359)]))) (.redProjected 0 1)) (.redProjected 0 1))))

theorem plan700_4_ok : plan700_4.checkAt
    (((rootAddress ![2, 2] ![3, 3, 0]).child true).child true)
    (childBox (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) 4 true) = true := by decide +kernel

def plan700_n2 : Plan := .cut 4 plan700_n1 plan700_4

theorem plan700_n2_ok : plan700_n2.checkAt
    ((rootAddress ![2, 2] ![3, 3, 0]).child true)
    (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true) = true :=
  checkAt_cut 4 plan700_n1 plan700_4
    ((rootAddress ![2, 2] ![3, 3, 0]).child true)
    (childBox (rootBox ![2, 2] ![3, 3, 0]) 1 true)
    (by decide +kernel) plan700_n1_ok plan700_4_ok

def plan700 : Plan := .cut 1 plan700_0 plan700_n2

theorem plan700_ok : plan700.checkAt
    (rootAddress ![2, 2] ![3, 3, 0])
    (rootBox ![2, 2] ![3, 3, 0]) = true :=
  checkAt_cut 1 plan700_0 plan700_n2
    (rootAddress ![2, 2] ![3, 3, 0])
    (rootBox ![2, 2] ![3, 3, 0])
    (by decide +kernel) plan700_0_ok plan700_n2_ok

theorem root700 : rootCheck plan700 ![2, 2] ![3, 3, 0] = true := plan700_ok

def plan701 : Plan :=
  (.cut 1 (.cut 0 (.e1 [(122, 128), (123, 216), (129, 206), (130, 329), (164, 174), (170, 184), (172, 184), (178, 174), (212, 329), (213, 206), (219, 216), (220, 128)] [(115, 276), (121, 275), (164, 167), (165, 357), (170, 157), (172, 157), (177, 357), (178, 167), (220, 271), (221, 275), (227, 276)]) (.cut 4 (.e1 [(122, 154), (123, 205), (129, 206), (130, 271), (164, 179), (170, 179), (172, 179), (178, 179), (212, 271), (213, 206), (219, 205), (220, 154)] [(114, 334), (115, 247), (121, 247), (122, 272), (164, 178), (165, 341), (170, 179), (172, 179), (177, 341), (178, 178), (220, 272), (221, 247), (227, 247), (228, 334)]) (.e1 [(122, 151), (123, 206), (129, 196), (164, 179), (170, 172), (172, 172), (178, 179), (212, 335), (213, 196), (219, 206), (220, 151)] [(114, 309), (115, 258), (121, 274), (122, 256), (164, 172), (170, 171), (172, 171), (178, 172), (220, 256), (221, 274), (227, 258), (228, 309)]))) (.e1 [(122, 151), (123, 183), (129, 221), (130, 274), (164, 203), (170, 166), (172, 166), (178, 203), (212, 274), (213, 221), (219, 183), (220, 151)] [(115, 248), (121, 250), (122, 283), (164, 157), (165, 341), (170, 198), (172, 198), (177, 341), (178, 157), (220, 283), (221, 250), (227, 248), (228, 324)]))

theorem root701 : rootCheck plan701 ![2, 2] ![3, 3, 1] = true := by decide +kernel

def plan702 : Plan :=
  (.cut 1 (.cut 0 (.e1 [(122, 128), (123, 216), (129, 206), (164, 174), (165, 325), (170, 184), (172, 184), (177, 325), (178, 174), (213, 206), (219, 216), (220, 128)] [(114, 303), (115, 307), (122, 247), (164, 167), (170, 157), (172, 157), (178, 167), (220, 247), (221, 306), (227, 307), (228, 303)]) (.cut 4 (.e1 [(122, 157), (123, 203), (129, 207), (164, 172), (170, 168), (172, 168), (177, 328), (178, 172), (213, 207), (219, 203), (220, 157)] [(114, 294), (115, 280), (121, 280), (122, 231), (164, 172), (170, 177), (172, 177), (178, 172), (220, 231), (221, 280), (227, 280), (228, 294)]) (.e1 [(122, 154), (123, 205), (129, 206), (164, 179), (165, 269), (170, 179), (172, 179), (177, 269), (178, 179), (213, 206), (219, 205), (220, 154)] [(114, 267), (115, 302), (121, 302), (122, 226), (163, 341), (164, 178), (170, 179), (172, 179), (178, 178), (179, 341), (220, 226), (221, 302), (227, 302), (228, 267)]))) (.e1 [(122, 157), (123, 182), (129, 213), (164, 204), (165, 256), (170, 173), (172, 173), (177, 256), (178, 204), (213, 213), (219, 182), (220, 157)] [(114, 248), (115, 305), (121, 306), (122, 234), (164, 165), (170, 200), (172, 200), (178, 165), (179, 331), (220, 234), (221, 306), (227, 305), (228, 248)]))

theorem root702 : rootCheck plan702 ![2, 2] ![3, 3, 2] = true := by decide +kernel

def plan703 : Plan :=
  (.cut 1 (.cut 0 (.cut 4 (.e1 [(122, 136), (123, 222), (129, 200), (164, 191), (165, 224), (170, 214), (172, 214), (177, 224), (178, 191), (213, 200), (219, 222), (220, 136)] [(114, 249), (122, 237), (163, 268), (164, 193), (170, 170), (172, 170), (178, 193), (179, 268), (220, 237), (228, 249)]) (.e1 [(122, 134), (123, 241), (129, 199), (164, 183), (165, 215), (170, 225), (172, 225), (177, 215), (178, 183), (213, 199), (219, 241), (220, 134)] [(114, 253), (122, 231), (163, 254), (164, 205), (170, 163), (172, 163), (178, 205), (179, 254), (220, 231), (221, 346), (227, 349), (228, 253)])) (.cut 4 (.cut 1 (.e1 [(122, 157), (123, 225), (128, 505), (129, 194), (164, 176), (165, 220), (170, 207), (172, 207), (177, 220), (178, 176), (213, 194), (214, 505), (219, 225), (220, 157)] [(114, 243), (115, 325), (121, 322), (122, 219), (163, 291), (164, 207), (170, 173), (172, 173), (178, 207), (179, 291), (220, 219), (221, 322), (227, 325), (228, 243)]) (.cut 0 (.e1 [(122, 148), (123, 216), (129, 207), (164, 190), (165, 219), (170, 199), (172, 199), (177, 219), (178, 190), (213, 207), (219, 216), (220, 148)] [(114, 247), (115, 331), (121, 330), (122, 224), (163, 278), (164, 191), (170, 182), (172, 182), (178, 191), (179, 278), (220, 224), (221, 330), (227, 331), (228, 247)]) (.cut 2 (.e1 [(122, 160), (123, 210), (129, 226), (164, 181), (165, 210), (170, 192), (172, 192), (177, 210), (178, 181), (213, 226), (219, 210), (220, 160)] [(114, 249), (115, 346), (121, 309), (122, 207), (163, 283), (164, 193), (170, 194), (172, 194), (178, 193), (179, 283), (220, 207), (221, 309), (227, 346), (228, 249)]) (.cut 3 (.e1 [(122, 160), (123, 225), (129, 206), (164, 197), (165, 210), (170, 180), (172, 180), (177, 210), (178, 197), (213, 206), (219, 225), (220, 160)] [(114, 246), (115, 303), (121, 352), (122, 210), (163, 283), (164, 193), (170, 194), (172, 194), (178, 193), (179, 283), (220, 210), (221, 352), (227, 303), (228, 246)]) (.e1 [(122, 160), (123, 205), (129, 206), (164, 197), (165, 209), (170, 196), (172, 196), (177, 209), (178, 197), (213, 206), (219, 205), (220, 160)] [(114, 232), (115, 326), (121, 326), (122, 221), (163, 283), (164, 193), (170, 194), (172, 194), (178, 193), (179, 283), (220, 221), (221, 326), (227, 326), (228, 232)]))))) (.cut 1 (.cut 0 (.e1 [(122, 145), (123, 259), (129, 200), (164, 166), (165, 203), (170, 225), (172, 225), (177, 203), (178, 166), (213, 200), (219, 259), (220, 145)] [(114, 256), (121, 342), (122, 212), (163, 257), (164, 225), (170, 161), (172, 161), (178, 225), (179, 257), (220, 212), (221, 342), (227, 350), (228, 256)]) (.cut 2 (.e1 [(122, 160), (123, 235), (129, 210), (164, 165), (165, 199), (170, 217), (172, 217), (177, 199), (178, 165), (213, 210), (219, 235), (220, 160)] [(114, 246), (121, 314), (122, 204), (163, 271), (164, 220), (170, 175), (172, 175), (178, 220), (179, 271), (220, 204), (221, 314), (227, 357), (228, 246)]) (.e1 [(122, 158), (123, 245), (129, 190), (164, 176), (165, 197), (170, 218), (172, 218), (177, 197), (178, 176), (213, 190), (214, 470), (219, 245), (220, 158)] [(114, 236), (115, 329), (121, 345), (122, 212), (163, 267), (164, 225), (170, 172), (172, 172), (178, 225), (179, 267), (220, 212), (221, 345), (227, 329), (228, 236)]))) (.cut 0 (.e1 [(116, 471), (122, 147), (123, 239), (128, 471), (129, 209), (164, 184), (165, 197), (170, 213), (172, 213), (177, 197), (178, 184), (213, 209), (214, 471), (219, 239), (220, 147), (226, 471)] [(114, 247), (115, 347), (121, 345), (122, 214), (123, 632), (163, 252), (164, 209), (170, 178), (172, 178), (178, 209), (179, 252), (219, 632), (220, 214), (221, 345), (227, 347), (228, 247)]) (.cut 2 (.cut 3 (.e1 [(122, 158), (123, 245), (129, 226), (164, 176), (165, 187), (170, 196), (172, 196), (177, 187), (178, 176), (213, 226), (219, 245), (220, 158)] [(114, 254), (115, 346), (121, 342), (122, 193), (163, 256), (164, 212), (170, 190), (172, 190), (178, 212), (179, 256), (220, 193), (221, 342), (227, 346), (228, 254)]) (.cut 4 (.e1 [(122, 160), (123, 214), (129, 226), (164, 181), (165, 195), (170, 205), (172, 205), (177, 195), (178, 181), (213, 226), (219, 214), (220, 160)] [(114, 241), (115, 363), (121, 311), (122, 206), (163, 266), (164, 203), (170, 194), (172, 194), (178, 203), (179, 266), (220, 206), (221, 311), (227, 363), (228, 241)]) (.e1 [(122, 161), (123, 222), (129, 226), (164, 185), (165, 176), (170, 217), (172, 217), (177, 176), (178, 185), (213, 226), (219, 222), (220, 161)] [(114, 231), (121, 320), (122, 204), (163, 247), (164, 215), (170, 197), (172, 197), (178, 215), (179, 247), (220, 204), (221, 320), (228, 231)]))) (.cut 3 (.cut 4 (.e1 [(122, 160), (123, 240), (129, 206), (164, 197), (165, 186), (170, 195), (172, 195), (177, 186), (178, 197), (213, 206), (219, 240), (220, 160)] [(114, 237), (115, 318), (121, 369), (122, 205), (163, 255), (164, 210), (170, 194), (172, 194), (178, 210), (179, 255), (220, 205), (221, 369), (227, 318), (228, 237)]) (.e1 [(122, 161), (123, 241), (129, 206), (164, 202), (165, 176), (170, 200), (172, 200), (177, 176), (178, 202), (213, 206), (219, 241), (220, 161)] [(114, 230), (115, 322), (122, 205), (163, 247), (164, 215), (170, 197), (172, 197), (178, 215), (179, 247), (220, 205), (221, 374), (227, 322), (228, 230)])) (.cut 4 (.cut 1 (.e1 [(122, 157), (123, 228), (129, 204), (164, 186), (165, 195), (170, 210), (172, 210), (177, 195), (178, 186), (213, 204), (219, 228), (220, 157)] [(114, 235), (115, 339), (121, 337), (122, 213), (163, 263), (164, 211), (170, 184), (172, 184), (178, 211), (179, 263), (220, 213), (221, 337), (227, 339), (228, 235)]) (.e1 [(122, 158), (123, 218), (128, 479), (129, 209), (164, 195), (165, 192), (170, 205), (172, 205), (177, 192), (178, 195), (213, 209), (214, 479), (219, 218), (220, 158), (226, 479)] [(114, 231), (115, 338), (121, 337), (122, 214), (163, 262), (164, 204), (170, 193), (172, 193), (178, 204), (179, 262), (220, 214), (221, 337), (227, 338), (228, 231)])) (.e1 [(122, 161), (123, 222), (129, 206), (164, 202), (165, 175), (170, 217), (172, 217), (177, 175), (178, 202), (213, 206), (219, 222), (220, 161)] [(114, 219), (115, 347), (121, 347), (122, 213), (163, 247), (164, 215), (170, 197), (172, 197), (178, 215), (179, 247), (220, 213), (221, 347), (227, 347), (228, 219)])))))))) (.cut 0 (.cut 4 (.e1 [(122, 128), (123, 222), (129, 231), (164, 199), (165, 228), (170, 190), (172, 190), (177, 228), (178, 199), (213, 231), (219, 222), (220, 128)] [(114, 273), (121, 347), (122, 228), (163, 259), (164, 172), (170, 182), (172, 182), (178, 172), (179, 259), (220, 228), (221, 347), (227, 345), (228, 273)]) (.e1 [(122, 134), (123, 239), (129, 233), (164, 200), (165, 191), (170, 206), (172, 206), (177, 191), (178, 200), (213, 233), (219, 239), (220, 134)] [(114, 258), (115, 362), (121, 361), (122, 217), (163, 230), (164, 194), (170, 188), (172, 188), (178, 194), (179, 230), (220, 217), (221, 361), (227, 362), (228, 258)])) (.cut 4 (.cut 1 (.cut 0 (.e1 [(122, 148), (123, 210), (129, 216), (164, 198), (165, 215), (170, 193), (172, 193), (177, 215), (178, 198), (213, 216), (219, 210), (220, 148)] [(114, 246), (115, 333), (121, 333), (122, 223), (163, 274), (164, 185), (170, 190), (172, 190), (178, 185), (179, 274), (220, 223), (221, 333), (227, 333), (228, 246)]) (.cut 2 (.e1 [(122, 160), (123, 204), (129, 234), (164, 189), (165, 206), (170, 186), (172, 186), (177, 206), (178, 189), (213, 234), (219, 204), (220, 160)] [(114, 247), (115, 347), (121, 312), (122, 207), (163, 279), (164, 186), (170, 203), (172, 203), (178, 186), (179, 279), (220, 207), (221, 312), (227, 347), (228, 247)]) (.cut 3 (.e1 [(122, 161), (123, 220), (129, 210), (164, 206), (165, 201), (170, 179), (172, 179), (177, 201), (178, 206), (213, 210), (219, 220), (220, 161)] [(114, 239), (115, 306), (122, 210), (163, 275), (164, 191), (170, 202), (172, 202), (178, 191), (179, 275), (220, 210), (221, 357), (227, 306), (228, 239)]) (.e1 [(122, 160), (123, 199), (129, 214), (164, 205), (165, 206), (170, 190), (172, 190), (177, 206), (178, 205), (213, 214), (219, 199), (220, 160)] [(114, 231), (115, 328), (121, 328), (122, 220), (163, 279), (164, 186), (170, 203), (172, 203), (178, 186), (179, 279), (220, 220), (221, 328), (227, 328), (228, 231)])))) (.redProjected 0 1)) (.cut 1 (.cut 0 (.cut 2 (.e1 [(122, 145), (123, 228), (129, 238), (164, 187), (165, 186), (170, 211), (172, 211), (177, 186), (178, 187), (213, 238), (219, 228), (220, 145)] [(114, 251), (115, 382), (121, 329), (122, 208), (163, 238), (164, 202), (170, 192), (172, 192), (178, 202), (179, 238), (220, 208), (221, 329), (227, 382), (228, 251)]) (.e1 [(116, 473), (122, 145), (123, 235), (129, 223), (164, 206), (165, 183), (170, 201), (172, 201), (177, 183), (178, 206), (213, 223), (219, 235), (220, 145), (226, 473)] [(114, 243), (115, 343), (121, 369), (122, 212), (163, 236), (164, 199), (170, 196), (172, 196), (178, 199), (179, 236), (220, 212), (221, 369), (227, 343), (228, 243)])) (.cut 2 (.cut 3 (.e1 [(122, 157), (123, 242), (129, 237), (164, 192), (165, 176), (170, 189), (172, 189), (177, 176), (178, 192), (213, 237), (219, 242), (220, 157)] [(114, 250), (115, 346), (121, 359), (122, 192), (163, 242), (164, 204), (170, 204), (172, 204), (178, 204), (179, 242), (220, 192), (221, 359), (227, 346), (228, 250)]) (.cut 4 (.e1 [(122, 157), (123, 215), (129, 237), (164, 192), (165, 186), (170, 197), (172, 197), (177, 186), (178, 192), (213, 237), (219, 215), (220, 157)] [(114, 242), (115, 364), (121, 325), (122, 204), (163, 253), (164, 197), (170, 204), (172, 204), (178, 197), (179, 253), (220, 204), (221, 325), (227, 364), (228, 242)]) (.e1 [(122, 157), (123, 226), (129, 242), (164, 189), (165, 172), (170, 208), (172, 208), (177, 172), (178, 189), (213, 242), (219, 226), (220, 157)] [(114, 240), (115, 383), (121, 328), (122, 198), (163, 237), (164, 209), (170, 204), (172, 204), (178, 209), (179, 237), (220, 198), (221, 328), (227, 383), (228, 240)]))) (.cut 3 (.cut 4 (.e1 [(122, 157), (123, 230), (129, 222), (164, 204), (165, 186), (170, 185), (172, 185), (177, 186), (178, 204), (213, 222), (214, 444), (219, 230), (220, 157)] [(114, 242), (115, 325), (121, 365), (122, 203), (163, 253), (164, 197), (170, 204), (172, 204), (178, 197), (179, 253), (220, 203), (221, 365), (227, 325), (228, 242)]) (.e1 [(122, 157), (123, 246), (129, 222), (164, 204), (165, 172), (170, 193), (172, 193), (177, 172), (178, 204), (213, 222), (219, 246), (220, 157)] [(114, 240), (115, 328), (121, 383), (122, 199), (163, 237), (164, 209), (170, 204), (172, 204), (178, 209), (179, 237), (220, 199), (221, 383), (227, 328), (228, 240)])) (.cut 4 (.e1 [(116, 470), (122, 157), (123, 215), (128, 470), (129, 222), (130, 625), (164, 204), (165, 185), (170, 197), (172, 197), (177, 185), (178, 204), (212, 625), (213, 222), (214, 470), (219, 215), (220, 157), (226, 470)] [(114, 232), (115, 343), (121, 344), (122, 211), (163, 253), (164, 197), (170, 204), (172, 204), (178, 197), (179, 253), (219, 678), (220, 211), (221, 344), (227, 343), (228, 232)]) (.e1 [(122, 157), (123, 226), (129, 222), (164, 204), (165, 171), (170, 208), (172, 208), (177, 171), (178, 204), (213, 222), (219, 226), (220, 157)] [(114, 228), (115, 354), (121, 353), (122, 207), (163, 237), (164, 209), (170, 204), (172, 204), (178, 209), (179, 237), (220, 207), (221, 353), (227, 354), (228, 228)]))))) (.cut 0 (.cut 2 (.e1 [(122, 145), (123, 218), (129, 255), (164, 204), (165, 178), (170, 201), (172, 201), (177, 178), (178, 204), (213, 255), (219, 218), (220, 145)] [(114, 247), (121, 335), (122, 208), (163, 229), (164, 191), (170, 210), (172, 210), (178, 191), (179, 229), (220, 208), (221, 335), (227, 387), (228, 247)]) (.e1 [(122, 145), (123, 230), (129, 232), (164, 214), (165, 179), (170, 196), (172, 196), (177, 179), (178, 214), (213, 232), (219, 230), (220, 145)] [(114, 242), (115, 345), (121, 372), (122, 211), (163, 231), (164, 194), (170, 205), (172, 205), (178, 194), (179, 231), (220, 211), (221, 372), (227, 345), (228, 242)])) (.cut 2 (.e1 [(116, 419), (122, 157), (123, 213), (128, 490), (129, 259), (164, 206), (165, 169), (170, 195), (172, 195), (177, 169), (178, 206), (213, 259), (214, 490), (219, 213), (220, 157), (226, 419)] [(114, 238), (115, 384), (121, 332), (122, 199), (163, 234), (164, 194), (170, 223), (172, 223), (178, 194), (179, 234), (213, 593), (220, 199), (221, 332), (227, 384), (228, 238)]) (.cut 4 (.redProjected 0 1) (.e1 [(122, 157), (123, 226), (129, 239), (164, 221), (165, 163), (170, 191), (172, 191), (177, 163), (178, 221), (213, 239), (219, 226), (220, 157), (226, 466)] [(114, 232), (115, 345), (121, 376), (122, 200), (163, 228), (164, 198), (170, 223), (172, 223), (178, 198), (179, 228), (220, 200), (221, 376), (227, 345), (228, 232)]))))))))

theorem root703 : rootCheck plan703 ![2, 2] ![3, 3, 3] = true := by decide +kernel

def plan704 : Plan :=
  (.e1 [(122, 128), (163, 189), (164, 187), (170, 144), (172, 144), (178, 187), (179, 189), (220, 128)] [(122, 168), (164, 173), (165, 212), (172, 217), (177, 212), (178, 173), (220, 168)])

theorem root704 : rootCheck plan704 ![2, 3] ![0, 0, 0] = true := by decide +kernel

def plan705 : Plan :=
  (.redProjected 0 1)

theorem root705 : rootCheck plan705 ![2, 3] ![0, 0, 1] = true := by decide +kernel

def plan706 : Plan :=
  (.redProjected 0 1)

theorem root706 : rootCheck plan706 ![2, 3] ![0, 0, 2] = true := by decide +kernel

def plan707 : Plan :=
  (.e1 [(122, 128), (165, 181), (170, 144), (172, 144), (177, 181), (220, 128)] [(122, 162), (163, 212), (164, 173), (170, 217), (172, 217), (178, 173), (179, 212), (220, 162)])

theorem root707 : rootCheck plan707 ![2, 3] ![0, 0, 3] = true := by decide +kernel

def plan708 : Plan :=
  (.cut 4 (.e1 [(122, 134), (123, 303), (130, 303), (163, 188), (164, 196), (170, 148), (172, 148), (178, 196), (179, 188), (212, 303), (219, 303), (220, 134)] [(115, 343), (122, 175), (164, 175), (165, 206), (170, 233), (172, 233), (177, 206), (178, 175), (220, 175), (221, 347), (227, 343)]) (.redProjected 0 1))

theorem root708 : rootCheck plan708 ![2, 3] ![0, 1, 0] = true := by decide +kernel

def plan709 : Plan :=
  (.redProjected 0 1)

theorem root709 : rootCheck plan709 ![2, 3] ![0, 1, 1] = true := by decide +kernel

def plan710 : Plan :=
  (.redProjected 0 1)

theorem root710 : rootCheck plan710 ![2, 3] ![0, 1, 2] = true := by decide +kernel

def plan711 : Plan :=
  (.e1 [(116, 371), (122, 134), (123, 290), (164, 195), (165, 191), (170, 135), (172, 135), (177, 191), (178, 195), (219, 290), (220, 134), (226, 371)] [(121, 374), (122, 166), (163, 223), (164, 162), (170, 233), (172, 233), (178, 162), (179, 223), (220, 166), (221, 374)])

theorem root711 : rootCheck plan711 ![2, 3] ![0, 1, 3] = true := by decide +kernel

def plan712 : Plan :=
  (.cut 4 (.cut 4 (.cut 3 (.e1 [(122, 145), (123, 274), (130, 260), (163, 188), (164, 196), (170, 159), (172, 159), (178, 196), (179, 188), (212, 260), (219, 274), (220, 145)] [(115, 325), (121, 301), (122, 182), (164, 185), (165, 202), (170, 248), (172, 248), (177, 202), (178, 185), (214, 394), (220, 182), (221, 301), (227, 325)]) (.cut 1 (.cut 0 (.e1 [(122, 128), (123, 260), (130, 251), (163, 219), (164, 187), (170, 180), (172, 180), (178, 187), (179, 219), (212, 251), (219, 260), (220, 128)] [(115, 334), (121, 279), (122, 209), (164, 182), (165, 202), (170, 217), (172, 217), (177, 202), (178, 182), (220, 209), (221, 279), (227, 334)]) (.cut 2 (.e1 [(122, 151), (123, 258), (130, 256), (163, 187), (164, 185), (170, 170), (172, 170), (178, 185), (179, 187), (212, 256), (219, 258), (220, 151)] [(115, 341), (121, 279), (122, 183), (164, 193), (165, 204), (170, 245), (172, 245), (177, 204), (178, 193), (220, 183), (221, 279), (227, 341)]) (.cut 3 (.e1 [(122, 151), (123, 263), (130, 241), (163, 197), (164, 188), (170, 168), (172, 168), (178, 188), (179, 197), (212, 241), (219, 263), (220, 151)] [(115, 315), (121, 275), (122, 188), (164, 193), (165, 204), (170, 245), (172, 245), (177, 204), (178, 193), (220, 188), (221, 275), (227, 315)]) (.e1 [(122, 151), (123, 252), (130, 231), (163, 205), (164, 188), (170, 174), (172, 174), (178, 188), (179, 205), (212, 231), (213, 414), (219, 252), (220, 151)] [(115, 313), (121, 262), (122, 197), (128, 393), (164, 193), (165, 204), (170, 245), (172, 245), (177, 204), (178, 193), (214, 393), (220, 197), (221, 262), (227, 313)])))) (.redProjected 0 1))) (.e1 [(122, 151), (123, 240), (129, 414), (130, 257), (163, 222), (164, 188), (170, 153), (172, 153), (178, 188), (179, 222), (212, 257), (213, 414), (219, 240), (220, 151)] [(115, 311), (121, 271), (122, 191), (128, 402), (164, 174), (165, 227), (170, 245), (172, 245), (177, 227), (178, 174), (214, 402), (220, 191), (221, 271), (227, 311)])) (.redProjected 0 1))

theorem root712 : rootCheck plan712 ![2, 3] ![0, 2, 0] = true := by decide +kernel

def plan713 : Plan :=
  (.redProjected 0 1)

theorem root713 : rootCheck plan713 ![2, 3] ![0, 2, 1] = true := by decide +kernel

def plan714 : Plan :=
  (.redProjected 0 1)

theorem root714 : rootCheck plan714 ![2, 3] ![0, 2, 2] = true := by decide +kernel

def plan715 : Plan :=
  (.cut 4 (.redProjected 0 1) (.cut 4 (.e1 [(116, 317), (122, 134), (123, 244), (164, 195), (165, 202), (170, 154), (172, 154), (177, 202), (178, 195), (219, 244), (220, 134), (226, 317)] [(121, 312), (122, 186), (129, 381), (163, 220), (164, 164), (170, 233), (172, 233), (178, 164), (179, 220), (213, 381), (220, 186), (221, 312), (228, 365)]) (.e1 [(116, 292), (122, 145), (123, 259), (129, 442), (164, 195), (165, 173), (170, 165), (172, 165), (177, 173), (178, 195), (213, 442), (219, 259), (220, 145), (226, 292), (227, 494)] [(114, 345), (121, 310), (122, 177), (129, 377), (163, 202), (164, 185), (170, 248), (172, 248), (178, 185), (179, 202), (213, 377), (220, 177), (221, 310), (228, 345)])))

theorem root715 : rootCheck plan715 ![2, 3] ![0, 2, 3] = true := by decide +kernel

def plan716 : Plan :=
  (.cut 4 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 131), (123, 235), (130, 228), (163, 224), (164, 196), (170, 191), (172, 191), (178, 196), (179, 224), (212, 228), (219, 235), (220, 131)] [(115, 330), (121, 257), (122, 225), (128, 395), (164, 181), (165, 197), (170, 230), (172, 230), (177, 197), (178, 181), (214, 395), (220, 225), (221, 257), (227, 330)]) (.cut 1 (.cut 2 (.cut 0 (.e1 [(122, 145), (123, 228), (130, 238), (163, 213), (164, 185), (170, 186), (172, 186), (178, 185), (179, 213), (212, 238), (219, 228), (220, 145)] [(115, 341), (121, 250), (122, 208), (128, 369), (164, 187), (165, 208), (170, 238), (172, 238), (177, 208), (178, 187), (214, 369), (220, 208), (221, 250), (227, 341)]) (.redProjected 0 1)) (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 145), (123, 243), (130, 220), (163, 220), (164, 188), (170, 183), (172, 183), (178, 188), (179, 220), (212, 220), (219, 243), (220, 145)] [(115, 310), (121, 250), (122, 212), (164, 192), (165, 202), (170, 238), (172, 238), (177, 202), (178, 192), (220, 212), (221, 250), (227, 310)]) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.e1 [(122, 145), (123, 233), (130, 215), (163, 224), (164, 188), (170, 190), (172, 190), (178, 188), (179, 224), (212, 215), (219, 233), (220, 145)] [(115, 316), (121, 241), (122, 219), (164, 192), (165, 202), (170, 238), (172, 238), (177, 202), (178, 192), (214, 395), (220, 219), (221, 241), (227, 316)]) (.redProjected 0 1)))) (.redProjected 0 1))) (.cut 0 (.cut 1 (.e1 [(122, 134), (123, 219), (130, 223), (163, 239), (164, 186), (170, 203), (172, 203), (178, 186), (179, 239), (212, 223), (219, 219), (220, 134)] [(115, 339), (121, 236), (122, 235), (164, 184), (165, 204), (170, 224), (172, 224), (177, 204), (178, 184), (220, 235), (221, 236), (227, 339)]) (.redProjected 0 1)) (.cut 1 (.cut 0 (.e1 [(115, 494), (122, 145), (123, 219), (129, 425), (130, 211), (131, 657), (163, 228), (164, 186), (170, 202), (172, 202), (178, 186), (179, 228), (211, 657), (212, 211), (213, 425), (219, 219), (220, 145), (227, 494)] [(114, 652), (115, 328), (116, 672), (121, 229), (122, 228), (128, 380), (158, 741), (164, 192), (165, 202), (170, 238), (172, 238), (177, 202), (178, 192), (184, 741), (214, 380), (215, 725), (220, 228), (221, 229), (226, 672), (227, 328), (228, 652)]) (.redProjected 0 1)) (.redProjected 0 1)))) (.cut 1 (.cut 3 (.cut 0 (.e1 [(122, 128), (123, 227), (130, 258), (163, 242), (164, 186), (170, 179), (172, 179), (178, 186), (179, 242), (212, 258), (219, 227), (220, 128)] [(121, 262), (122, 220), (164, 169), (165, 218), (170, 217), (172, 217), (177, 218), (178, 169), (220, 220), (221, 262), (227, 344)]) (.redProjected 0 1)) (.cut 0 (.e1 [(122, 128), (123, 209), (130, 242), (163, 258), (164, 186), (170, 193), (172, 193), (178, 186), (179, 258), (212, 242), (219, 209), (220, 128)] [(121, 241), (122, 238), (164, 169), (165, 218), (170, 217), (172, 217), (177, 218), (178, 169), (220, 238), (221, 241), (227, 346)]) (.redProjected 0 1))) (.redProjected 0 1))) (.redProjected 0 1))

theorem root716 : rootCheck plan716 ![2, 3] ![0, 3, 0] = true := by decide +kernel

def plan717 : Plan :=
  (.redProjected 0 1)

theorem root717 : rootCheck plan717 ![2, 3] ![0, 3, 1] = true := by decide +kernel

def plan718 : Plan :=
  (.redProjected 0 1)

theorem root718 : rootCheck plan718 ![2, 3] ![0, 3, 2] = true := by decide +kernel

def plan719 : Plan :=
  (.cut 4 (.redProjected 0 1) (.cut 4 (.cut 1 (.cut 3 (.e1 [(116, 264), (122, 157), (123, 216), (164, 172), (165, 215), (170, 176), (172, 176), (177, 215), (178, 172), (219, 216), (220, 157), (226, 264)] [(114, 353), (121, 245), (122, 194), (163, 231), (164, 184), (170, 238), (172, 238), (178, 184), (179, 231), (213, 359), (220, 194), (221, 245), (228, 353)]) (.cut 0 (.e1 [(116, 276), (122, 128), (123, 209), (164, 186), (165, 228), (170, 193), (172, 193), (177, 228), (178, 186), (219, 209), (220, 128), (226, 276)] [(121, 258), (122, 222), (163, 218), (164, 169), (170, 217), (172, 217), (178, 169), (179, 218), (220, 222), (221, 258)]) (.redProjected 0 1))) (.redProjected 0 1)) (.cut 3 (.cut 1 (.cut 0 (.e1 [(116, 278), (122, 134), (123, 238), (164, 186), (165, 196), (170, 189), (172, 189), (177, 196), (178, 186), (219, 238), (220, 134), (226, 278)] [(121, 280), (122, 201), (163, 204), (164, 184), (170, 224), (172, 224), (178, 184), (179, 204), (220, 201), (221, 280), (228, 346)]) (.cut 2 (.e1 [(116, 251), (122, 154), (123, 228), (129, 459), (164, 190), (165, 189), (170, 180), (172, 180), (177, 189), (178, 190), (213, 459), (219, 228), (220, 154), (226, 251)] [(114, 338), (121, 261), (122, 193), (129, 354), (163, 206), (164, 190), (170, 254), (172, 254), (178, 190), (179, 206), (213, 354), (220, 193), (221, 261), (228, 338)]) (.e1 [(116, 278), (122, 151), (123, 226), (164, 188), (165, 182), (170, 182), (172, 182), (177, 182), (178, 188), (219, 226), (220, 151), (226, 278)] [(114, 319), (121, 273), (122, 189), (163, 210), (164, 188), (170, 245), (172, 245), (178, 188), (179, 210), (220, 189), (221, 273), (228, 319)]))) (.redProjected 0 1)) (.cut 1 (.cut 0 (.e1 [(116, 257), (122, 134), (123, 219), (164, 186), (165, 208), (170, 203), (172, 203), (177, 208), (178, 186), (219, 219), (220, 134), (226, 257)] [(114, 341), (121, 256), (122, 217), (163, 204), (164, 184), (170, 224), (172, 224), (178, 184), (179, 204), (220, 217), (221, 256), (228, 341)]) (.cut 2 (.cut 0 (.e1 [(116, 233), (122, 147), (123, 212), (164, 190), (165, 208), (170, 199), (172, 199), (177, 208), (178, 190), (219, 212), (220, 147), (226, 233)] [(114, 341), (121, 240), (122, 217), (129, 359), (163, 204), (164, 188), (170, 245), (172, 245), (178, 188), (179, 204), (213, 359), (220, 217), (221, 240), (228, 341)]) (.redProjected 0 1)) (.cut 4 (.redProjected 0 1) (.cut 3 (.e1 [(116, 260), (122, 157), (123, 219), (164, 188), (165, 180), (170, 192), (172, 192), (177, 180), (178, 188), (219, 219), (220, 157), (226, 260)] [(114, 310), (121, 258), (122, 194), (163, 206), (164, 195), (170, 253), (172, 253), (178, 195), (179, 206), (213, 386), (220, 194), (221, 258), (228, 310)]) (.cut 0 (.e1 [(116, 248), (122, 145), (123, 214), (164, 187), (165, 196), (170, 206), (172, 206), (177, 196), (178, 187), (219, 214), (220, 145), (226, 248)] [(114, 323), (121, 248), (122, 212), (163, 202), (164, 192), (170, 238), (172, 238), (178, 192), (179, 202), (220, 212), (221, 248), (228, 323)]) (.redProjected 0 1)))))) (.redProjected 0 1)))))

theorem root719 : rootCheck plan719 ![2, 3] ![0, 3, 3] = true := by decide +kernel

def plan720 : Plan :=
  (.cut 4 (.e1 [(122, 134), (130, 303), (163, 188), (164, 205), (170, 139), (172, 139), (178, 205), (179, 188), (212, 303), (220, 134)] [(115, 310), (122, 172), (164, 175), (165, 206), (170, 233), (172, 233), (177, 206), (178, 175), (220, 172), (227, 310)]) (.redProjected 0 1))

theorem root720 : rootCheck plan720 ![2, 3] ![1, 0, 0] = true := by decide +kernel

def plan721 : Plan :=
  (.redProjected 0 1)

theorem root721 : rootCheck plan721 ![2, 3] ![1, 0, 1] = true := by decide +kernel

def plan722 : Plan :=
  (.redProjected 0 1)

theorem root722 : rootCheck plan722 ![2, 3] ![1, 0, 2] = true := by decide +kernel

def plan723 : Plan :=
  (.e1 [(122, 128), (164, 197), (165, 189), (170, 142), (172, 142), (177, 189), (178, 197), (220, 128)] [(122, 171), (163, 212), (164, 173), (170, 217), (172, 217), (178, 173), (179, 212), (220, 171)])

theorem root723 : rootCheck plan723 ![2, 3] ![1, 0, 3] = true := by decide +kernel

def plan724 : Plan :=
  (.cut 4 (.cut 1 (.cut 2 (.e1 [(122, 139), (130, 276), (163, 192), (164, 192), (170, 151), (172, 151), (178, 192), (179, 192), (212, 276), (219, 318), (220, 139)] [(115, 312), (121, 333), (122, 177), (164, 185), (165, 206), (170, 231), (172, 231), (177, 206), (178, 185), (220, 177), (221, 333), (227, 312)]) (.e1 [(122, 151), (123, 307), (129, 340), (130, 239), (163, 213), (164, 192), (170, 150), (172, 150), (178, 192), (179, 213), (212, 239), (213, 340), (219, 307), (220, 151)] [(115, 272), (121, 300), (122, 187), (164, 192), (165, 213), (170, 236), (172, 236), (177, 213), (178, 192), (220, 187), (221, 300), (226, 510), (227, 272)])) (.redProjected 0 1)) (.redProjected 0 1))

theorem root724 : rootCheck plan724 ![2, 3] ![1, 1, 0] = true := by decide +kernel

def plan725 : Plan :=
  (.redProjected 0 1)

theorem root725 : rootCheck plan725 ![2, 3] ![1, 1, 1] = true := by decide +kernel

def plan726 : Plan :=
  (.redProjected 0 1)

theorem root726 : rootCheck plan726 ![2, 3] ![1, 1, 2] = true := by decide +kernel

def plan727 : Plan :=
  (.e1 [(122, 128), (123, 297), (164, 197), (165, 180), (170, 154), (172, 154), (177, 180), (178, 197), (219, 297), (220, 128)] [(122, 175), (163, 212), (164, 173), (170, 217), (172, 217), (178, 173), (179, 212), (220, 175)])

theorem root727 : rootCheck plan727 ![2, 3] ![1, 1, 3] = true := by decide +kernel

def plan728 : Plan :=
  (.cut 4 (.cut 1 (.cut 2 (.cut 4 (.cut 1 (.cut 3 (.e1 [(122, 151), (123, 277), (130, 228), (163, 210), (164, 189), (170, 164), (172, 164), (178, 189), (179, 210), (212, 228), (219, 277), (220, 151)] [(115, 288), (121, 274), (122, 194), (164, 195), (165, 206), (170, 240), (172, 240), (177, 206), (178, 195), (220, 194), (221, 274), (227, 288)]) (.cut 0 (.e1 [(122, 134), (123, 262), (130, 234), (163, 234), (164, 183), (170, 181), (172, 181), (178, 183), (179, 234), (212, 234), (219, 262), (220, 134)] [(115, 309), (121, 265), (122, 214), (164, 188), (165, 207), (170, 215), (172, 215), (177, 207), (178, 188), (220, 214), (221, 265), (227, 309)]) (.redProjected 0 1))) (.redProjected 0 1)) (.e1 [(122, 157), (123, 241), (130, 226), (163, 249), (164, 181), (170, 161), (172, 161), (178, 181), (179, 249), (212, 226), (219, 241), (220, 157)] [(115, 281), (121, 247), (122, 205), (164, 184), (165, 231), (170, 238), (172, 238), (177, 231), (178, 184), (220, 205), (221, 247), (227, 281)])) (.cut 4 (.cut 1 (.cut 0 (.e1 [(122, 128), (123, 265), (130, 222), (163, 254), (164, 188), (170, 185), (172, 185), (178, 188), (179, 254), (212, 222), (213, 332), (219, 265), (220, 128)] [(115, 292), (121, 264), (122, 231), (164, 186), (165, 205), (170, 208), (172, 208), (177, 205), (178, 186), (220, 231), (221, 264), (227, 292)]) (.redProjected 0 1)) (.redProjected 0 1)) (.e1 [(122, 157), (123, 241), (130, 211), (163, 269), (164, 189), (170, 161), (172, 161), (178, 189), (179, 269), (212, 211), (213, 335), (219, 241), (220, 157)] [(115, 260), (121, 243), (122, 218), (164, 184), (165, 231), (170, 238), (172, 238), (177, 231), (178, 184), (220, 218), (221, 243), (227, 260)]))) (.redProjected 0 1)) (.redProjected 0 1))

theorem root728 : rootCheck plan728 ![2, 3] ![1, 2, 0] = true := by decide +kernel

def plan729 : Plan :=
  (.redProjected 0 1)

theorem root729 : rootCheck plan729 ![2, 3] ![1, 2, 1] = true := by decide +kernel

def plan730 : Plan :=
  (.redProjected 0 1)

theorem root730 : rootCheck plan730 ![2, 3] ![1, 2, 2] = true := by decide +kernel

def plan731 : Plan :=
  (.cut 4 (.redProjected 0 1) (.e1 [(122, 134), (123, 255), (164, 202), (165, 174), (170, 165), (172, 165), (177, 174), (178, 202), (219, 255), (220, 134), (226, 354)] [(114, 323), (121, 346), (122, 181), (163, 206), (164, 175), (170, 233), (172, 233), (178, 175), (179, 206), (220, 181), (221, 346), (228, 323)]))

theorem root731 : rootCheck plan731 ![2, 3] ![1, 2, 3] = true := by decide +kernel

def plan732 : Plan :=
  (.cut 4 (.cut 1 (.cut 2 (.cut 4 (.cut 0 (.e1 [(122, 134), (123, 228), (130, 208), (163, 257), (164, 192), (170, 196), (172, 196), (178, 192), (179, 257), (212, 208), (219, 228), (220, 134)] [(115, 304), (121, 236), (122, 243), (164, 184), (165, 204), (170, 224), (172, 224), (177, 204), (178, 184), (220, 243), (221, 236), (227, 304)]) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))) (.cut 0 (.e1 [(122, 128), (123, 218), (130, 228), (164, 191), (170, 186), (172, 186), (178, 191), (179, 276), (212, 228), (219, 218), (220, 128)] [(115, 311), (121, 242), (122, 245), (164, 169), (165, 218), (170, 217), (172, 217), (177, 218), (178, 169), (220, 245), (221, 242), (227, 311)]) (.redProjected 0 1))) (.cut 4 (.cut 0 (.e1 [(122, 128), (123, 231), (130, 203), (163, 275), (164, 196), (170, 199), (172, 199), (178, 196), (179, 275), (212, 203), (213, 348), (219, 231), (220, 128)] [(115, 294), (121, 237), (122, 258), (164, 182), (165, 202), (170, 217), (172, 217), (177, 202), (178, 182), (220, 258), (221, 237), (227, 294)]) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))) (.cut 0 (.e1 [(122, 128), (123, 218), (130, 216), (163, 296), (164, 197), (170, 186), (172, 186), (178, 197), (179, 296), (212, 216), (219, 218), (220, 128)] [(115, 292), (121, 239), (122, 258), (164, 169), (165, 218), (170, 217), (172, 217), (177, 218), (178, 169), (220, 258), (221, 239), (227, 292)]) (.redProjected 0 1)))) (.redProjected 0 1)) (.redProjected 0 1))

theorem root732 : rootCheck plan732 ![2, 3] ![1, 3, 0] = true := by decide +kernel

def plan733 : Plan :=
  (.redProjected 0 1)

theorem root733 : rootCheck plan733 ![2, 3] ![1, 3, 1] = true := by decide +kernel

def plan734 : Plan :=
  (.redProjected 0 1)

theorem root734 : rootCheck plan734 ![2, 3] ![1, 3, 2] = true := by decide +kernel

def plan735 : Plan :=
  (.cut 4 (.redProjected 0 1) (.cut 1 (.cut 4 (.e1 [(116, 303), (122, 151), (123, 203), (164, 183), (165, 199), (170, 185), (172, 185), (177, 199), (178, 183), (213, 375), (219, 203), (220, 151), (226, 303)] [(114, 302), (121, 262), (122, 198), (163, 230), (164, 178), (170, 236), (172, 236), (178, 178), (179, 230), (213, 427), (220, 198), (221, 262), (228, 302)]) (.cut 0 (.e1 [(116, 302), (122, 128), (123, 222), (164, 194), (165, 190), (170, 206), (172, 206), (177, 190), (178, 194), (219, 222), (220, 128), (226, 302)] [(121, 287), (122, 213), (163, 202), (164, 182), (170, 217), (172, 217), (178, 182), (179, 202), (220, 213), (221, 287), (228, 305)]) (.cut 3 (.e1 [(122, 151), (123, 231), (164, 192), (165, 170), (170, 179), (172, 179), (177, 170), (178, 192), (219, 231), (220, 151), (226, 309)] [(114, 301), (121, 296), (122, 182), (163, 210), (164, 188), (170, 245), (172, 245), (178, 188), (179, 210), (220, 182), (221, 296), (228, 301)]) (.cut 2 (.e1 [(116, 277), (122, 154), (123, 212), (164, 187), (165, 180), (170, 199), (172, 199), (177, 180), (178, 187), (213, 385), (219, 212), (220, 154), (226, 277)] [(114, 295), (121, 261), (122, 197), (129, 418), (163, 209), (164, 194), (170, 244), (172, 244), (178, 194), (179, 209), (213, 418), (220, 197), (221, 261), (228, 295)]) (.e1 [(116, 303), (122, 151), (123, 212), (129, 362), (164, 197), (165, 172), (170, 194), (172, 194), (177, 172), (178, 197), (213, 362), (219, 212), (220, 151), (226, 303)] [(114, 280), (121, 281), (122, 195), (163, 210), (164, 188), (170, 245), (172, 245), (178, 188), (179, 210), (220, 195), (221, 281), (228, 280)]))))) (.redProjected 0 1)))

theorem root735 : rootCheck plan735 ![2, 3] ![1, 3, 3] = true := by decide +kernel

def plan736 : Plan :=
  (.cut 4 (.cut 1 (.cut 4 (.e1 [(122, 139), (123, 376), (129, 300), (130, 255), (163, 205), (164, 217), (170, 142), (172, 142), (178, 217), (179, 205), (212, 255), (213, 300), (219, 376), (220, 139)] [(115, 259), (121, 371), (122, 190), (164, 185), (165, 206), (170, 231), (172, 231), (177, 206), (178, 185), (220, 190), (221, 371), (227, 259)]) (.e1 [(122, 139), (129, 303), (130, 290), (163, 223), (164, 202), (170, 130), (172, 130), (178, 202), (179, 223), (212, 290), (213, 303), (220, 139)] [(115, 266), (122, 182), (164, 172), (165, 231), (170, 222), (172, 222), (177, 231), (178, 172), (220, 182), (227, 266)])) (.redProjected 0 1)) (.redProjected 0 1))

theorem root736 : rootCheck plan736 ![2, 3] ![2, 0, 0] = true := by decide +kernel

def plan737 : Plan :=
  (.redProjected 0 1)

theorem root737 : rootCheck plan737 ![2, 3] ![2, 0, 1] = true := by decide +kernel

def plan738 : Plan :=
  (.redProjected 0 1)

theorem root738 : rootCheck plan738 ![2, 3] ![2, 0, 2] = true := by decide +kernel

def plan739 : Plan :=
  (.e1 [(121, 413), (122, 128), (123, 381), (128, 301), (129, 295), (164, 215), (165, 205), (170, 142), (172, 142), (177, 205), (178, 215), (213, 295), (214, 301), (219, 381), (220, 128), (221, 413)] [(114, 396), (115, 282), (122, 189), (123, 428), (163, 212), (164, 173), (170, 217), (172, 217), (178, 173), (179, 212), (219, 428), (220, 189), (227, 282), (228, 396)])

theorem root739 : rootCheck plan739 ![2, 3] ![2, 0, 3] = true := by decide +kernel

def plan740 : Plan :=
  (.cut 4 (.cut 1 (.cut 1 (.cut 2 (.e1 [(122, 151), (123, 309), (129, 310), (130, 223), (163, 231), (164, 196), (170, 152), (172, 152), (178, 196), (179, 231), (212, 223), (213, 310), (219, 309), (220, 151)] [(115, 251), (121, 293), (122, 200), (164, 194), (165, 215), (170, 231), (172, 231), (177, 215), (178, 194), (220, 200), (221, 293), (227, 251)]) (.e1 [(122, 151), (123, 309), (129, 286), (130, 207), (163, 250), (164, 208), (170, 152), (172, 152), (178, 208), (179, 250), (212, 207), (213, 286), (219, 309), (220, 151)] [(115, 231), (116, 504), (121, 290), (122, 216), (128, 550), (164, 194), (165, 215), (170, 231), (172, 231), (177, 215), (178, 194), (214, 550), (220, 216), (221, 290), (226, 504), (227, 231), (228, 611)])) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))

theorem root740 : rootCheck plan740 ![2, 3] ![2, 1, 0] = true := by decide +kernel

def plan741 : Plan :=
  (.redProjected 0 1)

theorem root741 : rootCheck plan741 ![2, 3] ![2, 1, 1] = true := by decide +kernel

def plan742 : Plan :=
  (.redProjected 0 1)

theorem root742 : rootCheck plan742 ![2, 3] ![2, 1, 2] = true := by decide +kernel

def plan743 : Plan :=
  (.e1 [(122, 128), (123, 297), (164, 215), (165, 184), (170, 154), (172, 154), (177, 184), (178, 215), (213, 295), (214, 376), (219, 297), (220, 128)] [(114, 327), (115, 330), (122, 186), (163, 212), (164, 173), (170, 217), (172, 217), (178, 173), (179, 212), (220, 186), (227, 330), (228, 327)])

theorem root743 : rootCheck plan743 ![2, 3] ![2, 1, 3] = true := by decide +kernel

def plan744 : Plan :=
  (.cut 4 (.cut 1 (.cut 4 (.cut 0 (.e1 [(122, 131), (123, 269), (129, 297), (130, 197), (163, 278), (164, 209), (170, 180), (172, 180), (178, 209), (179, 278), (212, 197), (213, 297), (219, 269), (220, 131)] [(115, 253), (116, 570), (121, 263), (122, 253), (128, 532), (164, 187), (165, 202), (170, 216), (172, 216), (177, 202), (178, 187), (214, 532), (220, 253), (221, 263), (226, 570), (227, 253)]) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))) (.cut 0 (.e1 [(122, 131), (123, 252), (129, 297), (130, 219), (164, 209), (170, 163), (172, 163), (178, 209), (179, 299), (212, 219), (213, 297), (219, 252), (220, 131)] [(115, 254), (121, 270), (122, 247), (164, 170), (165, 223), (170, 216), (172, 216), (177, 223), (178, 170), (220, 247), (221, 270), (227, 254)]) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1))

theorem root744 : rootCheck plan744 ![2, 3] ![2, 2, 0] = true := by decide +kernel

def plan745 : Plan :=
  (.redProjected 0 1)

theorem root745 : rootCheck plan745 ![2, 3] ![2, 2, 1] = true := by decide +kernel

def plan746 : Plan :=
  (.redProjected 0 1)

theorem root746 : rootCheck plan746 ![2, 3] ![2, 2, 2] = true := by decide +kernel

def plan747 : Plan :=
  (.cut 1 (.cut 4 (.redProjected 0 1) (.e1 [(122, 139), (123, 247), (129, 312), (164, 211), (165, 172), (170, 164), (172, 164), (177, 172), (178, 211), (213, 312), (219, 247), (220, 139)] [(114, 289), (122, 184), (163, 217), (164, 176), (170, 231), (172, 231), (178, 176), (179, 217), (220, 184), (228, 289)])) (.redProjected 0 1))

theorem root747 : rootCheck plan747 ![2, 3] ![2, 2, 3] = true := by decide +kernel

def plan748 : Plan :=
  (.cut 4 (.cut 1 (.cut 0 (.cut 4 (.e1 [(122, 131), (123, 239), (129, 309), (130, 187), (163, 300), (164, 203), (170, 198), (172, 198), (178, 203), (179, 300), (212, 187), (213, 309), (219, 239), (220, 131)] [(115, 265), (121, 236), (122, 275), (164, 187), (165, 202), (170, 216), (172, 216), (177, 202), (178, 187), (220, 275), (221, 236), (227, 265)]) (.e1 [(122, 128), (123, 219), (129, 297), (130, 211), (164, 201), (170, 187), (172, 187), (178, 201), (179, 339), (212, 211), (213, 297), (219, 219), (220, 128)] [(115, 270), (121, 239), (122, 278), (164, 170), (165, 227), (170, 208), (172, 208), (177, 227), (178, 170), (220, 278), (221, 239), (227, 270)])) (.cut 4 (.cut 2 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1))

theorem root748 : rootCheck plan748 ![2, 3] ![2, 3, 0] = true := by decide +kernel

def plan749 : Plan :=
  (.redProjected 0 1)

theorem root749 : rootCheck plan749 ![2, 3] ![2, 3, 1] = true := by decide +kernel

def plan750 : Plan :=
  (.redProjected 0 1)

theorem root750 : rootCheck plan750 ![2, 3] ![2, 3, 2] = true := by decide +kernel

def plan751 : Plan :=
  (.cut 1 (.cut 4 (.redProjected 0 1) (.cut 0 (.e1 [(122, 128), (123, 214), (129, 306), (164, 210), (165, 187), (170, 198), (172, 198), (177, 187), (178, 210), (213, 306), (219, 214), (220, 128), (226, 363)] [(114, 276), (121, 320), (122, 215), (163, 212), (164, 173), (170, 217), (172, 217), (178, 173), (179, 212), (220, 215), (221, 320), (228, 276)]) (.cut 1 (.redProjected 0 1) (.redProjected 0 1)))) (.redProjected 0 1))

theorem root751 : rootCheck plan751 ![2, 3] ![2, 3, 3] = true := by decide +kernel

def plan752 : Plan :=
  (.cut 4 (.cut 1 (.cut 4 (.e1 [(121, 459), (122, 145), (129, 262), (130, 216), (163, 233), (164, 237), (170, 143), (172, 143), (178, 237), (179, 233), (212, 216), (213, 262), (219, 373), (220, 145), (221, 459)] [(115, 218), (116, 428), (121, 352), (122, 216), (164, 191), (165, 207), (170, 233), (172, 233), (177, 207), (178, 191), (220, 216), (221, 352), (226, 428), (227, 218)]) (.e1 [(122, 139), (129, 261), (130, 252), (163, 252), (164, 227), (170, 130), (172, 130), (178, 227), (179, 252), (212, 252), (213, 261), (220, 139)] [(115, 226), (122, 209), (164, 172), (165, 231), (170, 222), (172, 222), (177, 231), (178, 172), (220, 209), (227, 226)])) (.redProjected 0 1)) (.redProjected 0 1))

theorem root752 : rootCheck plan752 ![2, 3] ![3, 0, 0] = true := by decide +kernel

def plan753 : Plan :=
  (.redProjected 0 1)

theorem root753 : rootCheck plan753 ![2, 3] ![3, 0, 1] = true := by decide +kernel

def plan754 : Plan :=
  (.redProjected 0 1)

theorem root754 : rootCheck plan754 ![2, 3] ![3, 0, 2] = true := by decide +kernel

def plan755 : Plan :=
  (.cut 4 (.redProjected 0 1) (.cut 1 (.cut 4 (.e1 [(122, 139), (129, 261), (164, 227), (165, 223), (170, 130), (172, 130), (177, 223), (178, 227), (213, 261), (214, 290), (220, 139)] [(115, 244), (122, 195), (163, 231), (164, 172), (170, 222), (172, 222), (178, 172), (179, 231), (220, 195), (227, 244)]) (.e1 [(122, 139), (128, 255), (129, 261), (164, 244), (165, 205), (170, 142), (172, 142), (177, 205), (178, 244), (213, 261), (214, 255), (220, 139)] [(114, 363), (115, 240), (122, 203), (163, 206), (164, 185), (170, 231), (172, 231), (178, 185), (179, 206), (219, 427), (220, 203), (227, 240), (228, 363)])) (.redProjected 0 1)))

theorem root755 : rootCheck plan755 ![2, 3] ![3, 0, 3] = true := by decide +kernel

def plan756 : Plan :=
  (.cut 4 (.cut 1 (.cut 0 (.e1 [(122, 128), (129, 266), (130, 206), (163, 270), (164, 234), (170, 159), (172, 159), (178, 234), (179, 270), (212, 206), (213, 266), (219, 319), (220, 128)] [(115, 228), (121, 316), (122, 248), (164, 182), (165, 202), (170, 217), (172, 217), (177, 202), (178, 182), (220, 248), (221, 316), (227, 228)]) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1))

theorem root756 : rootCheck plan756 ![2, 3] ![3, 1, 0] = true := by decide +kernel

def plan757 : Plan :=
  (.redProjected 0 1)

theorem root757 : rootCheck plan757 ![2, 3] ![3, 1, 1] = true := by decide +kernel

def plan758 : Plan :=
  (.redProjected 0 1)

theorem root758 : rootCheck plan758 ![2, 3] ![3, 1, 2] = true := by decide +kernel

def plan759 : Plan :=
  (.cut 4 (.redProjected 0 1) (.cut 1 (.e1 [(122, 139), (123, 318), (128, 311), (129, 270), (164, 236), (165, 178), (170, 151), (172, 151), (177, 178), (178, 236), (213, 270), (214, 311), (219, 318), (220, 139)] [(114, 314), (115, 282), (122, 189), (163, 206), (164, 185), (170, 231), (172, 231), (178, 185), (179, 206), (220, 189), (227, 282), (228, 314)]) (.redProjected 0 1)))

theorem root759 : rootCheck plan759 ![2, 3] ![3, 1, 3] = true := by decide +kernel

def plan760 : Plan :=
  (.cut 4 (.cut 1 (.cut 0 (.e1 [(122, 134), (123, 262), (129, 268), (130, 185), (163, 316), (164, 219), (170, 181), (172, 181), (178, 219), (179, 316), (212, 185), (213, 268), (219, 262), (220, 134)] [(115, 232), (121, 258), (122, 279), (164, 188), (165, 207), (170, 215), (172, 215), (177, 207), (178, 188), (220, 279), (221, 258), (227, 232)]) (.cut 4 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1))

theorem root760 : rootCheck plan760 ![2, 3] ![3, 2, 0] = true := by decide +kernel

def plan761 : Plan :=
  (.redProjected 0 1)

theorem root761 : rootCheck plan761 ![2, 3] ![3, 2, 1] = true := by decide +kernel

def plan762 : Plan :=
  (.redProjected 0 1)

theorem root762 : rootCheck plan762 ![2, 3] ![3, 2, 2] = true := by decide +kernel

def plan763 : Plan :=
  (.cut 1 (.cut 4 (.redProjected 0 1) (.e1 [(122, 145), (123, 258), (129, 262), (164, 237), (165, 168), (170, 164), (172, 164), (177, 168), (178, 237), (213, 262), (214, 372), (219, 258), (220, 145)] [(114, 267), (115, 317), (122, 192), (163, 215), (164, 184), (170, 233), (172, 233), (178, 184), (179, 215), (220, 192), (227, 317), (228, 267)])) (.redProjected 0 1))

theorem root763 : rootCheck plan763 ![2, 3] ![3, 2, 3] = true := by decide +kernel

def plan764 : Plan :=
  (.cut 4 (.cut 1 (.cut 0 (.e1 [(122, 131), (123, 232), (129, 267), (130, 181), (164, 227), (170, 192), (172, 192), (178, 227), (179, 359), (212, 181), (213, 267), (219, 232), (220, 131)] [(115, 236), (121, 242), (122, 312), (164, 180), (165, 210), (170, 216), (172, 216), (177, 210), (178, 180), (220, 312), (221, 242), (227, 236)]) (.cut 4 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1))

theorem root764 : rootCheck plan764 ![2, 3] ![3, 3, 0] = true := by decide +kernel

def plan765 : Plan :=
  (.redProjected 0 1)

theorem root765 : rootCheck plan765 ![2, 3] ![3, 3, 1] = true := by decide +kernel

def plan766 : Plan :=
  (.redProjected 0 1)

theorem root766 : rootCheck plan766 ![2, 3] ![3, 3, 2] = true := by decide +kernel

def plan767 : Plan :=
  (.cut 1 (.cut 4 (.redProjected 0 1) (.cut 0 (.e1 [(122, 128), (123, 227), (129, 257), (164, 225), (165, 184), (170, 195), (172, 195), (177, 184), (178, 225), (213, 257), (219, 227), (220, 128)] [(114, 259), (122, 220), (163, 216), (164, 178), (170, 208), (172, 208), (178, 178), (179, 216), (220, 220), (221, 374), (227, 370), (228, 259)]) (.cut 1 (.redProjected 0 1) (.redProjected 0 1)))) (.redProjected 0 1))

theorem root767 : rootCheck plan767 ![2, 3] ![3, 3, 3] = true := by decide +kernel

def plan768 : Plan :=
  (.redFull 178)

theorem root768 : rootCheck plan768 ![3, 0] ![0, 0, 0] = true := by decide +kernel

def plan769 : Plan :=
  (.redFull 178)

theorem root769 : rootCheck plan769 ![3, 0] ![0, 0, 1] = true := by decide +kernel

def plan770 : Plan :=
  (.redFull 178)

theorem root770 : rootCheck plan770 ![3, 0] ![0, 0, 2] = true := by decide +kernel

def plan771 : Plan :=
  (.redFull 178)

theorem root771 : rootCheck plan771 ![3, 0] ![0, 0, 3] = true := by decide +kernel

def plan772 : Plan :=
  (.redFull 178)

theorem root772 : rootCheck plan772 ![3, 0] ![0, 1, 0] = true := by decide +kernel

def plan773 : Plan :=
  (.redFull 178)

theorem root773 : rootCheck plan773 ![3, 0] ![0, 1, 1] = true := by decide +kernel

def plan774 : Plan :=
  (.redFull 178)

theorem root774 : rootCheck plan774 ![3, 0] ![0, 1, 2] = true := by decide +kernel

def plan775 : Plan :=
  (.redFull 178)

theorem root775 : rootCheck plan775 ![3, 0] ![0, 1, 3] = true := by decide +kernel

def plan776 : Plan :=
  (.redFull 178)

theorem root776 : rootCheck plan776 ![3, 0] ![0, 2, 0] = true := by decide +kernel

def plan777 : Plan :=
  (.redFull 178)

theorem root777 : rootCheck plan777 ![3, 0] ![0, 2, 1] = true := by decide +kernel

def plan778 : Plan :=
  (.redFull 178)

theorem root778 : rootCheck plan778 ![3, 0] ![0, 2, 2] = true := by decide +kernel

def plan779 : Plan :=
  (.redFull 178)

theorem root779 : rootCheck plan779 ![3, 0] ![0, 2, 3] = true := by decide +kernel

def plan780 : Plan :=
  (.redFull 178)

theorem root780 : rootCheck plan780 ![3, 0] ![0, 3, 0] = true := by decide +kernel

def plan781 : Plan :=
  (.redFull 178)

theorem root781 : rootCheck plan781 ![3, 0] ![0, 3, 1] = true := by decide +kernel

def plan782 : Plan :=
  (.redFull 178)

theorem root782 : rootCheck plan782 ![3, 0] ![0, 3, 2] = true := by decide +kernel

def plan783 : Plan :=
  (.redFull 178)

theorem root783 : rootCheck plan783 ![3, 0] ![0, 3, 3] = true := by decide +kernel

def plan784 : Plan :=
  (.redFull 178)

theorem root784 : rootCheck plan784 ![3, 0] ![1, 0, 0] = true := by decide +kernel

def plan785 : Plan :=
  (.redFull 178)

theorem root785 : rootCheck plan785 ![3, 0] ![1, 0, 1] = true := by decide +kernel

def plan786 : Plan :=
  (.redFull 178)

theorem root786 : rootCheck plan786 ![3, 0] ![1, 0, 2] = true := by decide +kernel

def plan787 : Plan :=
  (.redFull 178)

theorem root787 : rootCheck plan787 ![3, 0] ![1, 0, 3] = true := by decide +kernel

def plan788 : Plan :=
  (.redFull 178)

theorem root788 : rootCheck plan788 ![3, 0] ![1, 1, 0] = true := by decide +kernel

def plan789 : Plan :=
  (.redFull 178)

theorem root789 : rootCheck plan789 ![3, 0] ![1, 1, 1] = true := by decide +kernel

def plan790 : Plan :=
  (.redFull 178)

theorem root790 : rootCheck plan790 ![3, 0] ![1, 1, 2] = true := by decide +kernel

def plan791 : Plan :=
  (.redFull 178)

theorem root791 : rootCheck plan791 ![3, 0] ![1, 1, 3] = true := by decide +kernel

def plan792 : Plan :=
  (.redFull 178)

theorem root792 : rootCheck plan792 ![3, 0] ![1, 2, 0] = true := by decide +kernel

def plan793 : Plan :=
  (.redFull 178)

theorem root793 : rootCheck plan793 ![3, 0] ![1, 2, 1] = true := by decide +kernel

def plan794 : Plan :=
  (.redFull 178)

theorem root794 : rootCheck plan794 ![3, 0] ![1, 2, 2] = true := by decide +kernel

def plan795 : Plan :=
  (.redFull 178)

theorem root795 : rootCheck plan795 ![3, 0] ![1, 2, 3] = true := by decide +kernel

def plan796 : Plan :=
  (.redFull 178)

theorem root796 : rootCheck plan796 ![3, 0] ![1, 3, 0] = true := by decide +kernel

def plan797 : Plan :=
  (.redFull 178)

theorem root797 : rootCheck plan797 ![3, 0] ![1, 3, 1] = true := by decide +kernel

def plan798 : Plan :=
  (.redFull 178)

theorem root798 : rootCheck plan798 ![3, 0] ![1, 3, 2] = true := by decide +kernel

def plan799 : Plan :=
  (.redFull 178)

theorem root799 : rootCheck plan799 ![3, 0] ![1, 3, 3] = true := by decide +kernel

def plan800 : Plan :=
  (.redFull 178)

theorem root800 : rootCheck plan800 ![3, 0] ![2, 0, 0] = true := by decide +kernel

def plan801 : Plan :=
  (.redFull 178)

theorem root801 : rootCheck plan801 ![3, 0] ![2, 0, 1] = true := by decide +kernel

def plan802 : Plan :=
  (.redFull 178)

theorem root802 : rootCheck plan802 ![3, 0] ![2, 0, 2] = true := by decide +kernel

def plan803 : Plan :=
  (.redFull 178)

theorem root803 : rootCheck plan803 ![3, 0] ![2, 0, 3] = true := by decide +kernel

def plan804 : Plan :=
  (.redFull 178)

theorem root804 : rootCheck plan804 ![3, 0] ![2, 1, 0] = true := by decide +kernel

def plan805 : Plan :=
  (.redFull 178)

theorem root805 : rootCheck plan805 ![3, 0] ![2, 1, 1] = true := by decide +kernel

def plan806 : Plan :=
  (.redFull 178)

theorem root806 : rootCheck plan806 ![3, 0] ![2, 1, 2] = true := by decide +kernel

def plan807 : Plan :=
  (.redFull 178)

theorem root807 : rootCheck plan807 ![3, 0] ![2, 1, 3] = true := by decide +kernel

def plan808 : Plan :=
  (.redFull 178)

theorem root808 : rootCheck plan808 ![3, 0] ![2, 2, 0] = true := by decide +kernel

def plan809 : Plan :=
  (.redFull 178)

theorem root809 : rootCheck plan809 ![3, 0] ![2, 2, 1] = true := by decide +kernel

def plan810 : Plan :=
  (.redFull 178)

theorem root810 : rootCheck plan810 ![3, 0] ![2, 2, 2] = true := by decide +kernel

def plan811 : Plan :=
  (.redFull 178)

theorem root811 : rootCheck plan811 ![3, 0] ![2, 2, 3] = true := by decide +kernel

def plan812 : Plan :=
  (.redFull 178)

theorem root812 : rootCheck plan812 ![3, 0] ![2, 3, 0] = true := by decide +kernel

def plan813 : Plan :=
  (.redFull 178)

theorem root813 : rootCheck plan813 ![3, 0] ![2, 3, 1] = true := by decide +kernel

def plan814 : Plan :=
  (.redFull 178)

theorem root814 : rootCheck plan814 ![3, 0] ![2, 3, 2] = true := by decide +kernel

def plan815 : Plan :=
  (.redFull 178)

theorem root815 : rootCheck plan815 ![3, 0] ![2, 3, 3] = true := by decide +kernel

def plan816 : Plan :=
  (.redFull 178)

theorem root816 : rootCheck plan816 ![3, 0] ![3, 0, 0] = true := by decide +kernel

def plan817 : Plan :=
  (.redFull 178)

theorem root817 : rootCheck plan817 ![3, 0] ![3, 0, 1] = true := by decide +kernel

def plan818 : Plan :=
  (.redFull 178)

theorem root818 : rootCheck plan818 ![3, 0] ![3, 0, 2] = true := by decide +kernel

def plan819 : Plan :=
  (.redFull 178)

theorem root819 : rootCheck plan819 ![3, 0] ![3, 0, 3] = true := by decide +kernel

def plan820 : Plan :=
  (.redFull 178)

theorem root820 : rootCheck plan820 ![3, 0] ![3, 1, 0] = true := by decide +kernel

def plan821 : Plan :=
  (.redFull 178)

theorem root821 : rootCheck plan821 ![3, 0] ![3, 1, 1] = true := by decide +kernel

def plan822 : Plan :=
  (.redFull 178)

theorem root822 : rootCheck plan822 ![3, 0] ![3, 1, 2] = true := by decide +kernel

def plan823 : Plan :=
  (.redFull 178)

theorem root823 : rootCheck plan823 ![3, 0] ![3, 1, 3] = true := by decide +kernel

def plan824 : Plan :=
  (.redFull 178)

theorem root824 : rootCheck plan824 ![3, 0] ![3, 2, 0] = true := by decide +kernel

def plan825 : Plan :=
  (.redFull 178)

theorem root825 : rootCheck plan825 ![3, 0] ![3, 2, 1] = true := by decide +kernel

def plan826 : Plan :=
  (.redFull 178)

theorem root826 : rootCheck plan826 ![3, 0] ![3, 2, 2] = true := by decide +kernel

def plan827 : Plan :=
  (.redFull 178)

theorem root827 : rootCheck plan827 ![3, 0] ![3, 2, 3] = true := by decide +kernel

def plan828 : Plan :=
  (.redFull 178)

theorem root828 : rootCheck plan828 ![3, 0] ![3, 3, 0] = true := by decide +kernel

def plan829 : Plan :=
  (.redFull 178)

theorem root829 : rootCheck plan829 ![3, 0] ![3, 3, 1] = true := by decide +kernel

def plan830 : Plan :=
  (.redFull 178)

theorem root830 : rootCheck plan830 ![3, 0] ![3, 3, 2] = true := by decide +kernel

def plan831 : Plan :=
  (.redFull 178)

theorem root831 : rootCheck plan831 ![3, 0] ![3, 3, 3] = true := by decide +kernel

def plan832 : Plan :=
  (.redFull 178)

theorem root832 : rootCheck plan832 ![3, 1] ![0, 0, 0] = true := by decide +kernel

def plan833 : Plan :=
  (.redFull 178)

theorem root833 : rootCheck plan833 ![3, 1] ![0, 0, 1] = true := by decide +kernel

def plan834 : Plan :=
  (.redFull 178)

theorem root834 : rootCheck plan834 ![3, 1] ![0, 0, 2] = true := by decide +kernel

def plan835 : Plan :=
  (.redFull 178)

theorem root835 : rootCheck plan835 ![3, 1] ![0, 0, 3] = true := by decide +kernel

def plan836 : Plan :=
  (.redFull 178)

theorem root836 : rootCheck plan836 ![3, 1] ![0, 1, 0] = true := by decide +kernel

def plan837 : Plan :=
  (.redFull 178)

theorem root837 : rootCheck plan837 ![3, 1] ![0, 1, 1] = true := by decide +kernel

def plan838 : Plan :=
  (.redFull 178)

theorem root838 : rootCheck plan838 ![3, 1] ![0, 1, 2] = true := by decide +kernel

def plan839 : Plan :=
  (.redFull 178)

theorem root839 : rootCheck plan839 ![3, 1] ![0, 1, 3] = true := by decide +kernel

def plan840 : Plan :=
  (.redFull 178)

theorem root840 : rootCheck plan840 ![3, 1] ![0, 2, 0] = true := by decide +kernel

def plan841 : Plan :=
  (.redFull 178)

theorem root841 : rootCheck plan841 ![3, 1] ![0, 2, 1] = true := by decide +kernel

def plan842 : Plan :=
  (.redFull 178)

theorem root842 : rootCheck plan842 ![3, 1] ![0, 2, 2] = true := by decide +kernel

def plan843 : Plan :=
  (.redFull 178)

theorem root843 : rootCheck plan843 ![3, 1] ![0, 2, 3] = true := by decide +kernel

def plan844 : Plan :=
  (.redFull 178)

theorem root844 : rootCheck plan844 ![3, 1] ![0, 3, 0] = true := by decide +kernel

def plan845 : Plan :=
  (.redFull 178)

theorem root845 : rootCheck plan845 ![3, 1] ![0, 3, 1] = true := by decide +kernel

def plan846 : Plan :=
  (.redFull 178)

theorem root846 : rootCheck plan846 ![3, 1] ![0, 3, 2] = true := by decide +kernel

def plan847 : Plan :=
  (.redFull 178)

theorem root847 : rootCheck plan847 ![3, 1] ![0, 3, 3] = true := by decide +kernel

def plan848 : Plan :=
  (.redFull 178)

theorem root848 : rootCheck plan848 ![3, 1] ![1, 0, 0] = true := by decide +kernel

def plan849 : Plan :=
  (.redFull 178)

theorem root849 : rootCheck plan849 ![3, 1] ![1, 0, 1] = true := by decide +kernel

def plan850 : Plan :=
  (.redFull 178)

theorem root850 : rootCheck plan850 ![3, 1] ![1, 0, 2] = true := by decide +kernel

def plan851 : Plan :=
  (.redFull 178)

theorem root851 : rootCheck plan851 ![3, 1] ![1, 0, 3] = true := by decide +kernel

def plan852 : Plan :=
  (.redFull 178)

theorem root852 : rootCheck plan852 ![3, 1] ![1, 1, 0] = true := by decide +kernel

def plan853 : Plan :=
  (.redFull 178)

theorem root853 : rootCheck plan853 ![3, 1] ![1, 1, 1] = true := by decide +kernel

def plan854 : Plan :=
  (.redFull 178)

theorem root854 : rootCheck plan854 ![3, 1] ![1, 1, 2] = true := by decide +kernel

def plan855 : Plan :=
  (.redFull 178)

theorem root855 : rootCheck plan855 ![3, 1] ![1, 1, 3] = true := by decide +kernel

def plan856 : Plan :=
  (.redFull 178)

theorem root856 : rootCheck plan856 ![3, 1] ![1, 2, 0] = true := by decide +kernel

def plan857 : Plan :=
  (.redFull 178)

theorem root857 : rootCheck plan857 ![3, 1] ![1, 2, 1] = true := by decide +kernel

def plan858 : Plan :=
  (.redFull 178)

theorem root858 : rootCheck plan858 ![3, 1] ![1, 2, 2] = true := by decide +kernel

def plan859 : Plan :=
  (.redFull 178)

theorem root859 : rootCheck plan859 ![3, 1] ![1, 2, 3] = true := by decide +kernel

def plan860 : Plan :=
  (.redFull 178)

theorem root860 : rootCheck plan860 ![3, 1] ![1, 3, 0] = true := by decide +kernel

def plan861 : Plan :=
  (.redFull 178)

theorem root861 : rootCheck plan861 ![3, 1] ![1, 3, 1] = true := by decide +kernel

def plan862 : Plan :=
  (.redFull 178)

theorem root862 : rootCheck plan862 ![3, 1] ![1, 3, 2] = true := by decide +kernel

def plan863 : Plan :=
  (.redFull 178)

theorem root863 : rootCheck plan863 ![3, 1] ![1, 3, 3] = true := by decide +kernel

def plan864 : Plan :=
  (.redFull 178)

theorem root864 : rootCheck plan864 ![3, 1] ![2, 0, 0] = true := by decide +kernel

def plan865 : Plan :=
  (.redFull 178)

theorem root865 : rootCheck plan865 ![3, 1] ![2, 0, 1] = true := by decide +kernel

def plan866 : Plan :=
  (.redFull 178)

theorem root866 : rootCheck plan866 ![3, 1] ![2, 0, 2] = true := by decide +kernel

def plan867 : Plan :=
  (.redFull 178)

theorem root867 : rootCheck plan867 ![3, 1] ![2, 0, 3] = true := by decide +kernel

def plan868 : Plan :=
  (.redFull 178)

theorem root868 : rootCheck plan868 ![3, 1] ![2, 1, 0] = true := by decide +kernel

def plan869 : Plan :=
  (.redFull 178)

theorem root869 : rootCheck plan869 ![3, 1] ![2, 1, 1] = true := by decide +kernel

def plan870 : Plan :=
  (.redFull 178)

theorem root870 : rootCheck plan870 ![3, 1] ![2, 1, 2] = true := by decide +kernel

def plan871 : Plan :=
  (.redFull 178)

theorem root871 : rootCheck plan871 ![3, 1] ![2, 1, 3] = true := by decide +kernel

def plan872 : Plan :=
  (.redFull 178)

theorem root872 : rootCheck plan872 ![3, 1] ![2, 2, 0] = true := by decide +kernel

def plan873 : Plan :=
  (.redFull 178)

theorem root873 : rootCheck plan873 ![3, 1] ![2, 2, 1] = true := by decide +kernel

def plan874 : Plan :=
  (.redFull 178)

theorem root874 : rootCheck plan874 ![3, 1] ![2, 2, 2] = true := by decide +kernel

def plan875 : Plan :=
  (.redFull 178)

theorem root875 : rootCheck plan875 ![3, 1] ![2, 2, 3] = true := by decide +kernel

def plan876 : Plan :=
  (.redFull 178)

theorem root876 : rootCheck plan876 ![3, 1] ![2, 3, 0] = true := by decide +kernel

def plan877 : Plan :=
  (.redFull 178)

theorem root877 : rootCheck plan877 ![3, 1] ![2, 3, 1] = true := by decide +kernel

def plan878 : Plan :=
  (.redFull 178)

theorem root878 : rootCheck plan878 ![3, 1] ![2, 3, 2] = true := by decide +kernel

def plan879 : Plan :=
  (.redFull 178)

theorem root879 : rootCheck plan879 ![3, 1] ![2, 3, 3] = true := by decide +kernel

def plan880 : Plan :=
  (.cut 1 (.redFull 178) (.cut 2 (.cut 1 (.redFull 178) (.cut 4 (.cut 0 (.redFull 178) (.redFull 172)) (.e1 [(122, 188), (129, 205), (130, 295), (164, 146), (170, 136), (172, 136), (178, 146), (212, 295), (213, 205), (220, 188)] [(115, 218), (122, 174), (164, 226), (165, 329), (170, 178), (172, 178), (177, 329), (178, 226), (220, 174), (227, 218)]))) (.cut 1 (.e1 [(122, 201), (129, 170), (130, 239), (163, 291), (164, 160), (170, 158), (172, 158), (178, 160), (179, 291), (212, 239), (213, 170), (220, 201)] [(115, 191), (121, 307), (122, 202), (164, 267), (165, 301), (170, 174), (172, 174), (177, 301), (178, 267), (220, 202), (221, 307), (227, 191)]) (.cut 4 (.e1 [(122, 194), (129, 184), (130, 236), (163, 271), (164, 169), (170, 153), (172, 153), (178, 169), (179, 271), (212, 236), (213, 184), (219, 424), (220, 194)] [(115, 195), (116, 387), (121, 314), (122, 198), (164, 255), (165, 281), (170, 186), (172, 186), (177, 281), (178, 255), (220, 198), (221, 314), (226, 387), (227, 195)]) (.e1 [(122, 188), (129, 183), (130, 277), (164, 163), (170, 136), (172, 136), (178, 163), (212, 277), (213, 183), (220, 188)] [(115, 196), (122, 192), (164, 226), (165, 329), (170, 178), (172, 178), (177, 329), (178, 226), (220, 192), (227, 196)])))))

theorem root880 : rootCheck plan880 ![3, 1] ![3, 0, 0] = true := by decide +kernel

def plan881 : Plan :=
  (.e1 [(122, 194), (129, 175), (164, 145), (170, 131), (172, 131), (178, 145), (213, 175), (220, 194)] [(115, 202), (122, 178), (164, 227), (170, 165), (172, 165), (178, 227), (220, 178), (227, 202)])

theorem root881 : rootCheck plan881 ![3, 1] ![3, 0, 1] = true := by decide +kernel

def plan882 : Plan :=
  (.e1 [(122, 194), (129, 175), (164, 145), (170, 131), (172, 131), (178, 145), (213, 175), (220, 194)] [(115, 209), (122, 172), (164, 227), (170, 165), (172, 165), (178, 227), (220, 172), (227, 209)])

theorem root882 : rootCheck plan882 ![3, 1] ![3, 0, 2] = true := by decide +kernel

def plan883 : Plan :=
  (.cut 1 (.redFull 178) (.cut 1 (.e1 [(122, 201), (128, 285), (129, 175), (164, 155), (165, 244), (170, 155), (172, 155), (177, 244), (178, 155), (213, 175), (214, 285), (220, 201)] [(115, 210), (122, 180), (163, 301), (164, 267), (170, 174), (172, 174), (178, 267), (179, 301), (220, 180), (227, 210), (228, 338)]) (.cut 2 (.e1 [(122, 188), (128, 318), (129, 205), (164, 146), (165, 219), (170, 155), (172, 155), (177, 219), (178, 146), (213, 205), (214, 318), (220, 188)] [(115, 244), (122, 164), (163, 286), (164, 252), (170, 178), (172, 178), (178, 252), (179, 286), (219, 375), (220, 164), (227, 244), (228, 341)]) (.cut 4 (.e1 [(122, 188), (129, 183), (164, 163), (165, 259), (170, 139), (172, 139), (177, 259), (178, 163), (213, 183), (220, 188)] [(115, 211), (122, 179), (164, 232), (170, 178), (172, 178), (178, 232), (179, 317), (220, 179), (227, 211)]) (.e1 [(122, 194), (128, 276), (129, 184), (164, 169), (165, 231), (170, 151), (172, 151), (177, 231), (178, 169), (213, 184), (214, 276), (219, 443), (220, 194)] [(114, 332), (115, 210), (122, 182), (123, 368), (163, 281), (164, 255), (170, 186), (172, 186), (178, 255), (179, 281), (219, 368), (220, 182), (227, 210), (228, 332)])))))

theorem root883 : rootCheck plan883 ![3, 1] ![3, 0, 3] = true := by decide +kernel

def plan884 : Plan :=
  (.cut 1 (.redFull 178) (.cut 4 (.cut 0 (.cut 1 (.e1 [(122, 178), (129, 173), (130, 233), (164, 144), (170, 190), (172, 190), (178, 144), (212, 233), (213, 173), (220, 178)] [(115, 212), (121, 270), (122, 224), (164, 269), (165, 292), (170, 154), (172, 154), (177, 292), (178, 269), (220, 224), (221, 270), (227, 212)]) (.cut 3 (.e1 [(122, 178), (123, 377), (129, 187), (130, 228), (163, 300), (164, 159), (170, 171), (172, 171), (178, 159), (179, 300), (212, 228), (213, 187), (219, 377), (220, 178)] [(115, 207), (121, 285), (122, 215), (164, 252), (165, 277), (170, 172), (172, 172), (177, 277), (178, 252), (220, 215), (221, 285), (226, 430), (227, 207)]) (.cut 2 (.redFull 178) (.e1 [(122, 185), (129, 196), (130, 199), (164, 162), (170, 179), (172, 179), (178, 162), (179, 316), (212, 199), (213, 196), (220, 185)] [(115, 202), (121, 252), (122, 229), (164, 257), (165, 266), (170, 182), (172, 182), (177, 266), (178, 257), (220, 229), (221, 252), (227, 202)])))) (.redFull 178)) (.e1 [(122, 194), (123, 339), (129, 187), (130, 247), (163, 348), (164, 156), (170, 148), (172, 148), (178, 156), (179, 348), (212, 247), (213, 187), (219, 339), (220, 194)] [(114, 459), (115, 197), (121, 284), (122, 203), (164, 234), (165, 328), (170, 179), (172, 179), (177, 328), (178, 234), (220, 203), (221, 284), (227, 197), (228, 459)])))

theorem root884 : rootCheck plan884 ![3, 1] ![3, 1, 0] = true := by decide +kernel

def plan885 : Plan :=
  (.cut 1 (.redFull 178) (.e1 [(122, 188), (123, 332), (129, 176), (130, 321), (164, 156), (170, 134), (172, 134), (178, 156), (212, 321), (213, 176), (219, 332), (220, 188)] [(115, 202), (121, 329), (122, 195), (164, 214), (170, 169), (172, 169), (178, 214), (220, 195), (221, 329), (227, 202)]))

theorem root885 : rootCheck plan885 ![3, 1] ![3, 1, 1] = true := by decide +kernel

def plan886 : Plan :=
  (.e1 [(122, 194), (123, 333), (129, 175), (164, 145), (165, 291), (170, 142), (172, 142), (177, 291), (178, 145), (213, 175), (219, 333), (220, 194)] [(114, 334), (115, 224), (122, 177), (163, 406), (164, 227), (170, 165), (172, 165), (178, 227), (179, 406), (220, 177), (227, 224), (228, 334)])

theorem root886 : rootCheck plan886 ![3, 1] ![3, 1, 2] = true := by decide +kernel

def plan887 : Plan :=
  (.cut 1 (.redFull 178) (.cut 1 (.e1 [(122, 201), (129, 175), (164, 155), (165, 202), (170, 170), (172, 170), (177, 202), (178, 155), (213, 175), (220, 201)] [(114, 273), (115, 246), (122, 172), (163, 301), (164, 267), (170, 174), (172, 174), (178, 267), (179, 301), (220, 172), (227, 246), (228, 273)]) (.cut 4 (.e1 [(122, 188), (129, 183), (164, 163), (165, 241), (170, 144), (172, 144), (177, 241), (178, 163), (213, 183), (219, 342), (220, 188)] [(114, 309), (115, 229), (122, 177), (163, 329), (164, 226), (170, 178), (172, 178), (178, 226), (179, 329), (220, 177), (227, 229), (228, 309)]) (.cut 2 (.e1 [(122, 188), (129, 205), (164, 146), (165, 189), (170, 171), (172, 171), (177, 189), (178, 146), (213, 205), (220, 188)] [(115, 275), (122, 160), (163, 277), (164, 259), (170, 178), (172, 178), (178, 259), (179, 277), (220, 160), (227, 275), (228, 294)]) (.e1 [(122, 194), (128, 342), (129, 184), (164, 169), (165, 196), (170, 164), (172, 164), (177, 196), (178, 169), (213, 184), (214, 342), (219, 355), (220, 194)] [(114, 276), (115, 242), (122, 174), (163, 281), (164, 255), (170, 186), (172, 186), (178, 255), (179, 281), (219, 448), (220, 174), (227, 242), (228, 276)])))))

theorem root887 : rootCheck plan887 ![3, 1] ![3, 1, 3] = true := by decide +kernel

def plan888 : Plan :=
  (.cut 1 (.redFull 178) (.cut 4 (.cut 0 (.cut 1 (.e1 [(122, 178), (129, 173), (130, 211), (164, 144), (170, 210), (172, 210), (178, 144), (212, 211), (213, 173), (219, 315), (220, 178)] [(115, 213), (121, 237), (122, 253), (164, 269), (165, 292), (170, 154), (172, 154), (177, 292), (178, 269), (220, 253), (221, 237), (227, 213)]) (.cut 2 (.redFull 178) (.cut 3 (.e1 [(122, 178), (123, 317), (129, 185), (130, 203), (163, 356), (164, 161), (170, 188), (172, 188), (178, 161), (179, 356), (212, 203), (213, 185), (219, 317), (220, 178)] [(115, 204), (121, 248), (122, 247), (164, 252), (165, 277), (170, 172), (172, 172), (177, 277), (178, 252), (220, 247), (221, 248), (227, 204)]) (.e1 [(81, 623), (122, 181), (123, 292), (129, 181), (130, 197), (163, 391), (164, 162), (165, 580), (170, 195), (172, 195), (177, 580), (178, 162), (179, 391), (212, 197), (213, 181), (219, 292), (220, 181), (221, 718), (261, 623)] [(65, 783), (114, 411), (115, 202), (116, 530), (121, 235), (122, 261), (128, 753), (163, 754), (164, 251), (165, 284), (170, 172), (172, 172), (177, 284), (178, 251), (179, 754), (214, 753), (220, 261), (221, 235), (226, 530), (227, 202), (228, 411), (277, 783)])))) (.redFull 178)) (.cut 0 (.cut 2 (.redFull 178) (.e1 [(122, 181), (123, 276), (129, 176), (130, 221), (163, 424), (164, 167), (165, 523), (170, 179), (172, 179), (177, 523), (178, 167), (179, 424), (212, 221), (213, 176), (219, 276), (220, 181)] [(114, 381), (115, 202), (121, 249), (122, 255), (164, 231), (165, 315), (170, 172), (172, 172), (177, 315), (178, 231), (179, 684), (220, 255), (221, 249), (226, 559), (227, 202), (228, 381)])) (.redFull 178))))

theorem root888 : rootCheck plan888 ![3, 1] ![3, 2, 0] = true := by decide +kernel

def plan889 : Plan :=
  (.cut 0 (.cut 1 (.redFull 178) (.e1 [(122, 181), (123, 257), (129, 181), (130, 274), (164, 162), (165, 434), (170, 161), (172, 161), (177, 434), (178, 162), (212, 274), (213, 181), (219, 257), (220, 181)] [(114, 352), (115, 215), (121, 267), (122, 231), (164, 209), (170, 172), (172, 172), (177, 376), (178, 209), (220, 231), (221, 267), (227, 215), (228, 352)])) (.redFull 178))

theorem root889 : rootCheck plan889 ![3, 1] ![3, 2, 1] = true := by decide +kernel

def plan890 : Plan :=
  (.cut 1 (.redFull 178) (.cut 0 (.e1 [(122, 181), (123, 257), (129, 181), (164, 162), (165, 268), (170, 161), (172, 161), (177, 268), (178, 162), (213, 181), (219, 257), (220, 181)] [(114, 282), (115, 252), (121, 329), (122, 198), (164, 209), (170, 172), (172, 172), (178, 209), (220, 198), (221, 329), (227, 252), (228, 282)]) (.redFull 178)))

theorem root890 : rootCheck plan890 ![3, 1] ![3, 2, 2] = true := by decide +kernel

def plan891 : Plan :=
  (.cut 1 (.redFull 178) (.cut 0 (.cut 4 (.e1 [(122, 185), (123, 267), (129, 181), (164, 171), (165, 207), (170, 179), (172, 179), (177, 207), (178, 171), (213, 181), (219, 267), (220, 185)] [(114, 248), (115, 273), (121, 365), (122, 191), (164, 230), (170, 180), (172, 180), (178, 230), (179, 307), (220, 191), (221, 365), (227, 273), (228, 248)]) (.e1 [(122, 185), (123, 272), (129, 181), (164, 171), (165, 198), (170, 185), (172, 185), (177, 198), (178, 171), (213, 181), (214, 433), (219, 272), (220, 185)] [(114, 244), (115, 278), (122, 190), (163, 297), (164, 236), (170, 180), (172, 180), (178, 236), (179, 297), (220, 190), (221, 372), (227, 278), (228, 244)])) (.redFull 178)))

theorem root891 : rootCheck plan891 ![3, 1] ![3, 2, 3] = true := by decide +kernel

def plan892 : Plan :=
  (.cut 1 (.redFull 178) (.cut 0 (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.cut 4 (.e1 [(122, 169), (123, 266), (129, 192), (130, 190), (164, 155), (170, 229), (172, 229), (178, 155), (212, 190), (213, 192), (219, 266), (220, 169)] [(114, 395), (115, 224), (121, 214), (122, 288), (164, 252), (165, 268), (170, 166), (172, 166), (177, 268), (178, 252), (220, 288), (221, 214), (227, 224), (228, 395)]) (.cut 2 (.redFull 178) (.e1 [(122, 169), (123, 253), (129, 182), (130, 204), (164, 163), (170, 216), (172, 216), (178, 163), (212, 204), (213, 182), (219, 253), (220, 169)] [(114, 365), (115, 219), (121, 225), (122, 292), (164, 238), (165, 287), (170, 166), (172, 166), (177, 287), (178, 238), (220, 292), (221, 225), (227, 219), (228, 365)])))) (.cut 1 (.redFull 178) (.cut 4 (.cut 2 (.redFull 178) (.e1 [(122, 181), (123, 260), (129, 185), (130, 179), (163, 430), (164, 166), (170, 221), (172, 221), (177, 599), (178, 166), (179, 430), (212, 179), (213, 185), (219, 260), (220, 181)] [(114, 377), (115, 207), (116, 583), (121, 212), (122, 297), (164, 254), (165, 271), (170, 177), (172, 177), (177, 271), (178, 254), (220, 297), (221, 212), (226, 583), (227, 207), (228, 377)])) (.cut 2 (.redFull 178) (.cut 3 (.e1 [(122, 181), (123, 258), (129, 185), (130, 197), (164, 166), (170, 200), (172, 200), (178, 166), (212, 197), (213, 185), (219, 258), (220, 181)] [(114, 377), (115, 208), (121, 224), (122, 277), (164, 239), (165, 290), (170, 177), (172, 177), (177, 290), (178, 239), (220, 277), (221, 224), (227, 208), (228, 377)]) (.e1 [(81, 541), (122, 181), (123, 237), (129, 185), (130, 193), (163, 464), (164, 166), (170, 217), (172, 217), (177, 559), (178, 166), (179, 464), (212, 193), (213, 185), (219, 237), (220, 181), (261, 541)] [(114, 350), (115, 215), (121, 211), (122, 298), (164, 239), (165, 290), (170, 177), (172, 177), (177, 290), (178, 239), (220, 298), (221, 211), (227, 215), (228, 350)])))))) (.cut 0 (.cut 1 (.redFull 178) (.e1 [(81, 581), (122, 171), (123, 236), (129, 185), (130, 227), (163, 469), (164, 157), (170, 208), (172, 208), (177, 518), (178, 157), (179, 469), (212, 227), (213, 185), (219, 236), (220, 171), (261, 581)] [(114, 349), (115, 231), (121, 225), (122, 278), (164, 225), (165, 315), (170, 165), (172, 165), (177, 315), (178, 225), (220, 278), (221, 225), (227, 231), (228, 349)])) (.cut 1 (.redFull 178) (.cut 4 (.cut 2 (.redFull 178) (.cut 3 (.e1 [(122, 183), (123, 247), (129, 181), (130, 211), (163, 454), (164, 166), (170, 194), (172, 194), (178, 166), (179, 454), (212, 211), (213, 181), (219, 247), (220, 183)] [(114, 356), (115, 209), (121, 229), (122, 273), (164, 230), (165, 311), (170, 176), (172, 176), (177, 311), (178, 230), (220, 273), (221, 229), (227, 209), (228, 356)]) (.cut 0 (.e1 [(122, 178), (123, 228), (129, 184), (130, 213), (164, 165), (170, 209), (172, 209), (178, 165), (212, 213), (213, 184), (219, 228), (220, 178)] [(114, 338), (115, 222), (121, 219), (122, 289), (164, 226), (165, 311), (170, 174), (172, 174), (177, 311), (178, 226), (220, 289), (221, 219), (227, 222), (228, 338)]) (.redFull 178)))) (.cut 2 (.redFull 178) (.cut 3 (.e1 [(122, 185), (123, 234), (129, 181), (130, 224), (164, 171), (170, 185), (172, 185), (178, 171), (212, 224), (213, 181), (219, 234), (220, 185)] [(114, 338), (115, 211), (121, 234), (122, 270), (164, 219), (165, 331), (170, 180), (172, 180), (177, 331), (178, 219), (220, 270), (221, 234), (227, 211), (228, 338)]) (.cut 0 (.e1 [(122, 178), (123, 219), (129, 184), (130, 232), (164, 165), (170, 200), (172, 200), (178, 165), (212, 232), (213, 184), (219, 219), (220, 178)] [(114, 325), (115, 227), (121, 225), (122, 279), (164, 216), (165, 334), (170, 174), (172, 174), (177, 334), (178, 216), (220, 279), (221, 225), (227, 227), (228, 325)]) (.redFull 178)))))))) (.redFull 178)))

theorem root892 : rootCheck plan892 ![3, 1] ![3, 3, 0] = true := by decide +kernel

def plan893 : Plan :=
  (.cut 0 (.cut 1 (.redFull 178) (.cut 4 (.cut 0 (.e1 [(122, 172), (123, 219), (129, 179), (130, 260), (164, 160), (170, 200), (172, 200), (178, 160), (212, 260), (213, 179), (219, 219), (220, 172)] [(114, 315), (115, 238), (121, 235), (122, 272), (164, 212), (165, 358), (170, 164), (172, 164), (177, 358), (178, 212), (220, 272), (221, 235), (227, 238), (228, 315)]) (.cut 1 (.redFull 178) (.cut 2 (.redFull 178) (.cut 3 (.e1 [(122, 185), (123, 225), (129, 181), (130, 250), (164, 171), (170, 176), (172, 176), (178, 171), (212, 250), (213, 181), (219, 225), (220, 185)] [(114, 322), (115, 217), (121, 243), (122, 259), (164, 207), (170, 180), (172, 180), (177, 363), (178, 207), (220, 259), (221, 243), (227, 217), (228, 322)]) (.e1 [(122, 185), (123, 204), (129, 181), (130, 248), (164, 171), (170, 194), (172, 194), (178, 171), (212, 248), (213, 181), (219, 204), (220, 185)] [(114, 300), (115, 229), (121, 228), (122, 278), (164, 207), (165, 363), (170, 180), (172, 180), (177, 363), (178, 207), (220, 278), (221, 228), (227, 229), (228, 300)]))))) (.e1 [(122, 181), (123, 206), (129, 181), (130, 300), (164, 162), (165, 382), (170, 186), (172, 186), (177, 382), (178, 162), (212, 300), (213, 181), (219, 206), (220, 181)] [(114, 290), (115, 246), (121, 244), (122, 251), (164, 202), (170, 172), (172, 172), (177, 420), (178, 202), (220, 251), (221, 244), (227, 246), (228, 290)]))) (.redFull 178))

theorem root893 : rootCheck plan893 ![3, 1] ![3, 3, 1] = true := by decide +kernel

def plan894 : Plan :=
  (.cut 1 (.redFull 178) (.cut 0 (.cut 4 (.cut 1 (.e1 [(122, 181), (123, 217), (129, 170), (164, 151), (170, 197), (172, 197), (178, 151), (213, 170), (219, 217), (220, 181)] [(114, 271), (115, 264), (121, 260), (122, 237), (164, 215), (170, 159), (172, 159), (178, 215), (220, 237), (221, 260), (227, 264), (228, 271)]) (.e1 [(122, 181), (123, 201), (129, 185), (164, 166), (165, 298), (170, 182), (172, 182), (177, 298), (178, 166), (212, 383), (213, 185), (219, 201), (220, 181)] [(114, 261), (115, 271), (121, 270), (122, 229), (164, 197), (170, 177), (172, 177), (178, 197), (220, 229), (221, 270), (227, 271), (228, 261)])) (.cut 1 (.e1 [(122, 181), (123, 227), (129, 170), (164, 151), (165, 258), (170, 207), (172, 207), (177, 258), (178, 151), (213, 170), (219, 227), (220, 181)] [(114, 247), (115, 291), (121, 286), (122, 218), (164, 227), (170, 159), (172, 159), (178, 227), (220, 218), (221, 286), (227, 291), (228, 247)]) (.cut 3 (.e1 [(122, 181), (123, 226), (129, 185), (164, 166), (165, 251), (170, 178), (172, 178), (177, 251), (178, 166), (213, 185), (219, 226), (220, 181)] [(114, 256), (115, 277), (121, 306), (122, 207), (164, 207), (170, 177), (172, 177), (178, 207), (179, 361), (220, 207), (221, 306), (227, 277), (228, 256)]) (.e1 [(122, 181), (123, 205), (129, 185), (130, 448), (164, 166), (165, 250), (170, 196), (172, 196), (177, 250), (178, 166), (212, 448), (213, 185), (219, 205), (220, 181)] [(114, 241), (115, 296), (121, 284), (122, 219), (163, 361), (164, 207), (170, 177), (172, 177), (178, 207), (179, 361), (220, 219), (221, 284), (227, 296), (228, 241)])))) (.redFull 178)))

theorem root894 : rootCheck plan894 ![3, 1] ![3, 3, 2] = true := by decide +kernel

def plan895 : Plan :=
  (.cut 1 (.redFull 178) (.cut 0 (.cut 4 (.cut 1 (.e1 [(122, 181), (123, 233), (129, 170), (164, 151), (165, 238), (170, 214), (172, 214), (177, 238), (178, 151), (213, 170), (219, 233), (220, 181)] [(114, 241), (115, 301), (121, 296), (122, 213), (164, 235), (170, 159), (172, 159), (178, 235), (179, 347), (220, 213), (221, 296), (227, 301), (228, 241)]) (.cut 2 (.redFull 178) (.cut 0 (.e1 [(122, 171), (123, 236), (129, 178), (164, 164), (165, 224), (170, 208), (172, 208), (177, 224), (178, 164), (213, 178), (219, 236), (220, 171)] [(114, 240), (115, 306), (121, 319), (122, 213), (163, 315), (164, 225), (170, 165), (172, 165), (178, 225), (179, 315), (220, 213), (221, 319), (227, 306), (228, 240)]) (.cut 4 (.cut 3 (.e1 [(122, 186), (123, 230), (129, 181), (164, 176), (165, 218), (170, 186), (172, 186), (177, 218), (178, 176), (213, 181), (219, 230), (220, 186)] [(114, 235), (115, 282), (121, 327), (122, 204), (164, 218), (170, 183), (172, 183), (178, 218), (179, 327), (220, 204), (221, 327), (227, 282), (228, 235)]) (.e1 [(122, 185), (123, 213), (129, 181), (164, 171), (165, 221), (170, 203), (172, 203), (177, 221), (178, 171), (213, 181), (219, 213), (220, 185)] [(114, 227), (115, 303), (121, 302), (122, 214), (163, 331), (164, 219), (170, 180), (172, 180), (178, 219), (179, 331), (220, 214), (221, 302), (227, 303), (228, 227)])) (.cut 3 (.e1 [(122, 186), (123, 232), (129, 181), (164, 176), (165, 213), (170, 188), (172, 188), (177, 213), (178, 176), (213, 181), (219, 232), (220, 186)] [(114, 233), (115, 285), (121, 330), (122, 203), (163, 321), (164, 221), (170, 183), (172, 183), (178, 221), (179, 321), (220, 203), (221, 330), (227, 285), (228, 233)]) (.e1 [(122, 185), (123, 217), (129, 181), (164, 171), (165, 212), (170, 207), (172, 207), (177, 212), (178, 171), (213, 181), (219, 217), (220, 185)] [(114, 224), (115, 309), (121, 307), (122, 211), (163, 319), (164, 224), (170, 180), (172, 180), (178, 224), (179, 319), (220, 211), (221, 307), (227, 309), (228, 224)])))))) (.cut 1 (.e1 [(122, 181), (123, 251), (129, 170), (164, 151), (165, 204), (170, 232), (172, 232), (177, 204), (178, 151), (213, 170), (219, 251), (220, 181)] [(114, 229), (122, 204), (163, 305), (164, 257), (170, 159), (172, 159), (178, 257), (179, 305), (220, 204), (221, 317), (227, 323), (228, 229)]) (.cut 0 (.e1 [(122, 172), (123, 242), (129, 182), (164, 164), (165, 199), (170, 223), (172, 223), (177, 199), (178, 164), (213, 182), (219, 242), (220, 172)] [(114, 231), (115, 328), (121, 324), (122, 207), (163, 288), (164, 238), (170, 169), (172, 169), (178, 238), (179, 288), (220, 207), (221, 324), (227, 328), (228, 231)]) (.cut 2 (.redFull 178) (.cut 3 (.e1 [(122, 186), (123, 243), (129, 181), (164, 176), (165, 192), (170, 199), (172, 199), (177, 192), (178, 176), (213, 181), (219, 243), (220, 186)] [(114, 225), (115, 297), (122, 198), (163, 296), (164, 234), (170, 183), (172, 183), (178, 234), (179, 296), (220, 198), (221, 345), (227, 297), (228, 225)]) (.e1 [(122, 186), (123, 222), (129, 181), (164, 176), (165, 191), (170, 217), (172, 217), (177, 191), (178, 176), (213, 181), (219, 222), (220, 186)] [(114, 214), (115, 320), (121, 319), (122, 207), (163, 296), (164, 234), (170, 183), (172, 183), (178, 234), (179, 296), (220, 207), (221, 319), (227, 320), (228, 214)])))))) (.redFull 178)))

theorem root895 : rootCheck plan895 ![3, 1] ![3, 3, 3] = true := by decide +kernel

def plan896 : Plan :=
  (.e1 [(122, 175), (163, 190), (164, 135), (170, 122), (172, 122), (178, 135), (179, 190), (220, 175)] [(122, 123), (164, 198), (165, 276), (170, 214), (172, 214), (177, 276), (178, 198), (220, 123)])

theorem root896 : rootCheck plan896 ![3, 2] ![0, 0, 0] = true := by decide +kernel

def plan897 : Plan :=
  (.redFull 172)

theorem root897 : rootCheck plan897 ![3, 2] ![0, 0, 1] = true := by decide +kernel

def plan898 : Plan :=
  (.redFull 172)

theorem root898 : rootCheck plan898 ![3, 2] ![0, 0, 2] = true := by decide +kernel

def plan899 : Plan :=
  (.e1 [(122, 175), (164, 135), (165, 186), (170, 122), (172, 122), (177, 186), (178, 135), (220, 175)] [(122, 122), (164, 198), (170, 214), (172, 214), (178, 198), (220, 122)])

theorem root899 : rootCheck plan899 ![3, 2] ![0, 0, 3] = true := by decide +kernel

def plan900 : Plan :=
  (.e1 [(122, 175), (123, 309), (129, 399), (130, 302), (163, 189), (164, 153), (170, 139), (172, 139), (178, 153), (179, 189), (212, 302), (213, 399), (219, 309), (220, 175)] [(115, 324), (121, 303), (122, 144), (164, 203), (165, 244), (170, 234), (172, 234), (177, 244), (178, 203), (220, 144), (221, 303), (227, 324)])

theorem root900 : rootCheck plan900 ![3, 2] ![0, 1, 0] = true := by decide +kernel

def plan901 : Plan :=
  (.e1 [(122, 175), (164, 120), (170, 121), (172, 121), (178, 120), (220, 175)] [(122, 139), (164, 181), (172, 195), (178, 181), (220, 139)])

theorem root901 : rootCheck plan901 ![3, 2] ![0, 1, 1] = true := by decide +kernel

def plan902 : Plan :=
  (.e1 [(122, 175), (164, 120), (170, 121), (172, 121), (178, 120), (220, 175)] [(122, 134), (164, 181), (172, 195), (178, 181), (220, 134)])

theorem root902 : rootCheck plan902 ![3, 2] ![0, 1, 2] = true := by decide +kernel

def plan903 : Plan :=
  (.e1 [(122, 188), (164, 135), (165, 163), (170, 136), (172, 136), (177, 163), (178, 135), (220, 188)] [(121, 340), (122, 121), (163, 257), (164, 216), (170, 226), (172, 226), (178, 216), (179, 257), (220, 121), (221, 340)])

theorem root903 : rootCheck plan903 ![3, 2] ![0, 1, 3] = true := by decide +kernel

def plan904 : Plan :=
  (.cut 4 (.cut 3 (.e1 [(122, 175), (123, 282), (130, 262), (163, 196), (164, 153), (170, 159), (172, 159), (178, 153), (179, 196), (212, 262), (219, 282), (220, 175)] [(115, 319), (121, 265), (122, 160), (164, 212), (165, 233), (170, 234), (172, 234), (177, 233), (178, 212), (220, 160), (221, 265), (227, 319)]) (.cut 1 (.redFull 178) (.cut 2 (.e1 [(122, 175), (123, 252), (130, 253), (163, 196), (164, 159), (170, 167), (172, 167), (178, 159), (179, 196), (212, 253), (219, 252), (220, 175)] [(115, 330), (121, 251), (122, 170), (164, 207), (165, 228), (170, 244), (172, 244), (177, 228), (178, 207), (214, 378), (220, 170), (221, 251), (227, 330)]) (.cut 4 (.cut 0 (.e1 [(115, 540), (122, 181), (123, 255), (129, 404), (130, 225), (131, 638), (163, 205), (164, 162), (170, 168), (172, 168), (178, 162), (179, 205), (211, 638), (212, 225), (213, 404), (219, 255), (220, 181), (227, 540)] [(114, 695), (115, 299), (116, 596), (121, 238), (122, 177), (128, 401), (164, 214), (165, 225), (170, 251), (172, 251), (177, 225), (178, 214), (213, 676), (214, 401), (220, 177), (221, 238), (226, 596), (227, 299), (228, 695)]) (.redFull 178)) (.e1 [(122, 175), (123, 240), (130, 246), (163, 227), (164, 162), (170, 155), (172, 155), (178, 162), (179, 227), (212, 246), (219, 240), (220, 175)] [(115, 302), (121, 243), (122, 179), (164, 193), (165, 246), (170, 244), (172, 244), (177, 246), (178, 193), (214, 412), (220, 179), (221, 243), (227, 302)]))))) (.cut 3 (.e1 [(122, 175), (123, 266), (163, 243), (164, 135), (170, 133), (172, 133), (178, 135), (179, 243), (219, 266), (220, 175)] [(115, 340), (121, 273), (122, 149), (164, 185), (165, 301), (170, 214), (172, 214), (177, 301), (178, 185), (220, 149), (221, 273), (227, 340)]) (.e1 [(122, 181), (123, 232), (129, 405), (130, 295), (163, 252), (164, 144), (170, 140), (172, 140), (178, 144), (179, 252), (212, 295), (213, 405), (219, 232), (220, 181), (227, 501)] [(115, 323), (121, 244), (122, 164), (164, 182), (165, 294), (170, 230), (172, 230), (177, 294), (178, 182), (220, 164), (221, 244), (227, 323)])))

theorem root904 : rootCheck plan904 ![3, 2] ![0, 2, 0] = true := by decide +kernel

def plan905 : Plan :=
  (.e1 [(122, 181), (123, 232), (164, 127), (170, 126), (172, 126), (178, 127), (219, 232), (220, 181)] [(121, 251), (122, 153), (164, 170), (170, 210), (172, 210), (178, 170), (220, 153), (221, 251)])

theorem root905 : rootCheck plan905 ![3, 2] ![0, 2, 1] = true := by decide +kernel

def plan906 : Plan :=
  (.e1 [(122, 181), (123, 232), (164, 127), (170, 126), (172, 126), (178, 127), (219, 232), (220, 181)] [(122, 148), (164, 170), (170, 210), (172, 210), (178, 170), (220, 148), (221, 261)])

theorem root906 : rootCheck plan906 ![3, 2] ![0, 2, 2] = true := by decide +kernel

def plan907 : Plan :=
  (.e1 [(116, 302), (122, 175), (123, 255), (164, 150), (165, 189), (170, 160), (172, 160), (177, 189), (178, 150), (219, 255), (220, 175), (226, 302)] [(114, 359), (121, 268), (122, 156), (163, 244), (164, 203), (170, 234), (172, 234), (178, 203), (179, 244), (213, 374), (220, 156), (221, 268), (228, 359)])

theorem root907 : rootCheck plan907 ![3, 2] ![0, 2, 3] = true := by decide +kernel

def plan908 : Plan :=
  (.cut 4 (.cut 1 (.redFull 178) (.cut 3 (.cut 2 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 181), (123, 240), (130, 233), (163, 199), (164, 159), (170, 177), (172, 177), (178, 159), (179, 199), (212, 233), (219, 240), (220, 181)] [(115, 325), (121, 232), (122, 178), (128, 369), (164, 214), (165, 225), (170, 251), (172, 251), (177, 225), (178, 214), (214, 369), (220, 178), (221, 232), (227, 325)]) (.redFull 178)) (.cut 1 (.redFull 178) (.cut 0 (.e1 [(122, 181), (123, 227), (129, 444), (130, 220), (163, 206), (164, 164), (170, 184), (172, 184), (178, 164), (179, 206), (212, 220), (213, 444), (219, 227), (220, 181)] [(115, 321), (121, 222), (122, 188), (128, 364), (164, 212), (165, 223), (170, 256), (172, 256), (177, 223), (178, 212), (214, 364), (220, 188), (221, 222), (227, 321)]) (.redFull 178)))) (.cut 3 (.e1 [(122, 181), (123, 226), (130, 260), (163, 219), (164, 155), (170, 161), (172, 161), (178, 155), (179, 219), (212, 260), (219, 226), (220, 181)] [(115, 330), (121, 235), (122, 174), (164, 195), (165, 253), (170, 245), (172, 245), (177, 253), (178, 195), (214, 377), (220, 174), (221, 235), (227, 330)]) (.cut 0 (.e1 [(122, 181), (123, 213), (130, 242), (163, 227), (164, 159), (170, 169), (172, 169), (178, 159), (179, 227), (212, 242), (219, 213), (220, 181)] [(115, 324), (121, 221), (122, 186), (164, 194), (165, 248), (170, 251), (172, 251), (177, 248), (178, 194), (220, 186), (221, 221), (227, 324)]) (.redFull 178)))) (.cut 4 (.cut 1 (.redFull 178) (.cut 3 (.cut 0 (.cut 4 (.cut 0 (.e1 [(122, 174), (123, 242), (130, 206), (163, 218), (164, 169), (170, 183), (172, 183), (178, 169), (179, 218), (212, 206), (219, 242), (220, 174)] [(115, 296), (121, 225), (122, 198), (128, 401), (164, 213), (165, 215), (170, 250), (172, 250), (177, 215), (178, 213), (214, 401), (220, 198), (221, 225), (227, 296)]) (.redFull 178)) (.redProjected 0 1)) (.redFull 178)) (.cut 0 (.cut 2 (.e1 [(81, 818), (114, 847), (115, 528), (121, 759), (122, 181), (123, 227), (129, 422), (130, 208), (131, 618), (137, 776), (163, 218), (164, 165), (165, 736), (170, 184), (172, 184), (177, 736), (178, 165), (179, 218), (205, 776), (211, 618), (212, 208), (213, 422), (219, 227), (220, 181), (221, 759), (227, 528), (228, 847), (261, 818)] [(72, 759), (114, 665), (115, 304), (116, 647), (121, 216), (122, 196), (127, 765), (128, 382), (129, 703), (158, 805), (164, 212), (165, 223), (170, 256), (172, 256), (177, 223), (178, 212), (184, 805), (213, 703), (214, 382), (215, 765), (220, 196), (221, 216), (226, 647), (227, 304), (228, 665), (270, 759)]) (.cut 0 (.e1 [(122, 172), (123, 230), (129, 397), (130, 203), (163, 231), (164, 167), (170, 188), (172, 188), (178, 167), (179, 231), (212, 203), (213, 397), (219, 230), (220, 172), (227, 538)] [(115, 298), (121, 215), (122, 206), (128, 404), (164, 209), (165, 220), (170, 245), (172, 245), (177, 220), (178, 209), (214, 404), (220, 206), (221, 215), (227, 298)]) (.redFull 178))) (.redFull 178)))) (.cut 3 (.cut 0 (.e1 [(122, 178), (123, 227), (130, 241), (163, 238), (164, 158), (170, 162), (172, 162), (178, 158), (179, 238), (212, 241), (219, 227), (220, 178)] [(115, 305), (121, 228), (122, 185), (164, 194), (165, 252), (170, 242), (172, 242), (177, 252), (178, 194), (214, 407), (220, 185), (221, 228), (227, 305)]) (.redFull 178)) (.cut 1 (.redFull 178) (.redProjected 0 1))))) (.cut 4 (.cut 1 (.redFull 178) (.cut 2 (.cut 0 (.cut 3 (.e1 [(81, 825), (115, 502), (121, 787), (122, 181), (123, 216), (129, 444), (130, 211), (131, 618), (137, 788), (163, 215), (164, 164), (170, 192), (172, 192), (177, 753), (178, 164), (179, 215), (205, 788), (211, 618), (212, 211), (213, 444), (219, 216), (220, 181), (221, 787), (227, 502), (261, 825)] [(114, 673), (115, 320), (116, 672), (121, 210), (122, 199), (127, 737), (128, 363), (129, 692), (158, 805), (164, 212), (165, 223), (170, 256), (172, 256), (177, 223), (178, 212), (184, 805), (213, 692), (214, 363), (215, 737), (220, 199), (221, 210), (226, 672), (227, 320), (228, 673)]) (.cut 0 (.cut 4 (.e1 [(115, 479), (122, 169), (123, 213), (129, 442), (130, 213), (131, 648), (163, 222), (164, 163), (170, 204), (172, 204), (178, 163), (179, 222), (211, 648), (212, 213), (213, 442), (219, 213), (220, 169), (227, 479)] [(72, 787), (114, 664), (115, 336), (116, 684), (121, 209), (122, 209), (127, 713), (128, 364), (164, 208), (165, 219), (170, 242), (172, 242), (177, 219), (178, 208), (213, 691), (214, 364), (215, 713), (220, 209), (221, 209), (226, 684), (227, 336), (228, 664), (270, 787)]) (.redProjected 0 1)) (.redFull 178))) (.redFull 178)) (.cut 0 (.cut 0 (.cut 1 (.e1 [(122, 169), (123, 222), (129, 398), (130, 204), (163, 241), (164, 157), (170, 203), (172, 203), (178, 157), (179, 241), (212, 204), (213, 398), (219, 222), (220, 169)] [(115, 315), (121, 204), (122, 213), (128, 402), (164, 213), (165, 223), (170, 232), (172, 232), (177, 223), (178, 213), (214, 402), (220, 213), (221, 204), (227, 315)]) (.redProjected 0 1)) (.redFull 178)) (.redFull 178)))) (.cut 1 (.redFull 178) (.redProjected 0 1))))) (.cut 1 (.redFull 178) (.cut 4 (.e1 [(122, 188), (123, 185), (130, 252), (163, 272), (164, 151), (170, 165), (172, 165), (178, 151), (179, 272), (212, 252), (213, 428), (219, 185), (220, 188)] [(115, 326), (121, 202), (122, 195), (128, 387), (164, 180), (165, 287), (170, 247), (172, 247), (177, 287), (178, 180), (214, 387), (220, 195), (221, 202), (227, 326)]) (.redProjected 0 1))))

theorem root908 : rootCheck plan908 ![3, 2] ![0, 3, 0] = true := by decide +kernel

def plan909 : Plan :=
  (.e1 [(122, 175), (123, 184), (129, 400), (130, 360), (164, 135), (170, 146), (172, 146), (178, 135), (179, 360), (212, 360), (213, 400), (219, 184), (220, 175)] [(115, 372), (121, 216), (122, 183), (164, 159), (165, 392), (170, 214), (172, 214), (177, 392), (178, 159), (220, 183), (221, 216), (227, 372)])

theorem root909 : rootCheck plan909 ![3, 2] ![0, 3, 1] = true := by decide +kernel

def plan910 : Plan :=
  (.e1 [(122, 175), (123, 184), (164, 135), (165, 326), (170, 146), (172, 146), (177, 326), (178, 135), (219, 184), (220, 175)] [(121, 222), (122, 178), (163, 392), (164, 159), (170, 214), (172, 214), (178, 159), (179, 392), (220, 178), (221, 222), (228, 402)])

theorem root910 : rootCheck plan910 ![3, 2] ![0, 3, 2] = true := by decide +kernel

def plan911 : Plan :=
  (.cut 4 (.cut 1 (.redFull 178) (.cut 3 (.e1 [(116, 317), (122, 181), (123, 206), (164, 147), (165, 235), (170, 152), (172, 152), (177, 235), (178, 147), (219, 206), (220, 181), (226, 317)] [(121, 236), (122, 169), (163, 293), (164, 179), (170, 235), (172, 235), (178, 179), (179, 293), (220, 169), (221, 236), (228, 358)]) (.e1 [(116, 294), (122, 188), (123, 185), (164, 151), (165, 235), (170, 165), (172, 165), (177, 235), (178, 151), (219, 185), (220, 188), (226, 294)] [(114, 334), (121, 217), (122, 181), (163, 287), (164, 180), (170, 247), (172, 247), (178, 180), (179, 287), (213, 381), (220, 181), (221, 217), (228, 334)]))) (.cut 1 (.redFull 178) (.cut 3 (.cut 3 (.e1 [(116, 267), (122, 175), (123, 238), (164, 159), (165, 187), (170, 176), (172, 176), (177, 187), (178, 159), (219, 238), (220, 175), (226, 267)] [(114, 342), (121, 249), (122, 170), (163, 228), (164, 207), (170, 244), (172, 244), (178, 207), (179, 228), (213, 366), (220, 170), (221, 249), (228, 342)]) (.cut 0 (.e1 [(116, 254), (122, 181), (123, 225), (164, 159), (165, 191), (170, 181), (172, 181), (177, 191), (178, 159), (219, 225), (220, 181), (226, 254)] [(114, 335), (121, 235), (122, 176), (129, 360), (163, 230), (164, 209), (170, 251), (172, 251), (178, 209), (179, 230), (213, 360), (220, 176), (221, 235), (228, 335)]) (.redFull 178))) (.cut 4 (.cut 2 (.cut 1 (.redFull 178) (.redProjected 0 1)) (.cut 3 (.e1 [(116, 288), (122, 188), (123, 201), (164, 153), (165, 204), (170, 176), (172, 176), (177, 204), (178, 153), (213, 409), (219, 201), (220, 188), (226, 288)] [(114, 315), (121, 228), (122, 175), (129, 393), (163, 261), (164, 196), (170, 247), (172, 247), (178, 196), (179, 261), (213, 393), (220, 175), (221, 228), (228, 315)]) (.cut 1 (.redFull 178) (.redProjected 0 1)))) (.cut 2 (.cut 1 (.redFull 178) (.cut 3 (.cut 0 (.e1 [(116, 231), (122, 181), (123, 216), (164, 163), (165, 197), (170, 192), (172, 192), (177, 197), (178, 163), (213, 463), (219, 216), (220, 181), (226, 231)] [(114, 335), (121, 221), (122, 188), (129, 348), (163, 223), (164, 212), (170, 256), (172, 256), (178, 212), (179, 223), (213, 348), (220, 188), (221, 221), (228, 335)]) (.redFull 178)) (.cut 0 (.cut 0 (.e1 [(116, 224), (122, 172), (123, 210), (129, 454), (164, 163), (165, 210), (170, 205), (172, 205), (177, 210), (178, 163), (213, 454), (219, 210), (220, 172), (226, 224)] [(114, 341), (121, 213), (122, 203), (129, 355), (163, 220), (164, 209), (170, 245), (172, 245), (178, 209), (179, 220), (213, 355), (220, 203), (221, 213), (228, 341)]) (.redFull 178)) (.redFull 178)))) (.cut 3 (.cut 0 (.e1 [(116, 264), (122, 178), (123, 220), (164, 157), (165, 185), (170, 194), (172, 194), (177, 185), (178, 157), (219, 220), (220, 178), (226, 264)] [(114, 316), (121, 235), (122, 178), (129, 393), (163, 229), (164, 213), (170, 242), (172, 242), (178, 213), (179, 229), (213, 393), (220, 178), (221, 235), (228, 316)]) (.redFull 178)) (.cut 1 (.redFull 178) (.cut 0 (.e1 [(116, 242), (122, 181), (123, 206), (129, 426), (164, 165), (165, 189), (170, 202), (172, 202), (177, 189), (178, 165), (213, 426), (219, 206), (220, 181), (226, 242), (227, 523)] [(114, 308), (121, 222), (122, 190), (129, 378), (163, 223), (164, 212), (170, 256), (172, 256), (178, 212), (179, 223), (213, 378), (220, 190), (221, 222), (228, 308)]) (.redFull 178)))))))))

theorem root911 : rootCheck plan911 ![3, 2] ![0, 3, 3] = true := by decide +kernel

def plan912 : Plan :=
  (.cut 4 (.e1 [(122, 175), (123, 400), (129, 334), (130, 337), (163, 185), (164, 144), (170, 135), (172, 135), (178, 144), (179, 185), (212, 337), (213, 334), (219, 400), (220, 175)] [(115, 312), (116, 440), (121, 356), (122, 135), (128, 528), (164, 214), (165, 253), (170, 214), (172, 214), (177, 253), (178, 214), (214, 528), (220, 135), (221, 356), (226, 440), (227, 312)]) (.e1 [(122, 175), (163, 233), (164, 132), (170, 129), (172, 129), (178, 132), (179, 233), (220, 175)] [(122, 141), (164, 206), (165, 296), (170, 195), (172, 195), (177, 296), (178, 206), (220, 141), (227, 292)]))

theorem root912 : rootCheck plan912 ![3, 2] ![1, 0, 0] = true := by decide +kernel

def plan913 : Plan :=
  (.redFull 172)

theorem root913 : rootCheck plan913 ![3, 2] ![1, 0, 1] = true := by decide +kernel

def plan914 : Plan :=
  (.redFull 172)

theorem root914 : rootCheck plan914 ![3, 2] ![1, 0, 2] = true := by decide +kernel

def plan915 : Plan :=
  (.e1 [(122, 181), (164, 138), (165, 183), (170, 129), (172, 129), (177, 183), (178, 138), (220, 181)] [(122, 127), (163, 271), (164, 213), (170, 210), (172, 210), (178, 213), (179, 271), (220, 127), (227, 322)])

theorem root915 : rootCheck plan915 ![3, 2] ![1, 0, 3] = true := by decide +kernel

def plan916 : Plan :=
  (.cut 1 (.redFull 178) (.cut 4 (.cut 2 (.e1 [(122, 175), (130, 266), (163, 199), (164, 151), (170, 151), (172, 151), (178, 151), (179, 199), (212, 266), (219, 321), (220, 175)] [(115, 296), (121, 284), (122, 156), (164, 217), (165, 237), (170, 224), (172, 224), (177, 237), (178, 217), (220, 156), (221, 284), (227, 296)]) (.cut 3 (.e1 [(122, 175), (130, 260), (163, 203), (164, 158), (170, 145), (172, 145), (178, 158), (179, 203), (212, 260), (220, 175)] [(115, 274), (121, 298), (122, 159), (164, 217), (165, 237), (170, 224), (172, 224), (177, 237), (178, 217), (220, 159), (221, 298), (227, 274)]) (.cut 1 (.e1 [(122, 175), (123, 316), (129, 315), (130, 241), (163, 222), (164, 154), (170, 155), (172, 155), (178, 154), (179, 222), (212, 241), (213, 315), (219, 316), (220, 175)] [(115, 270), (121, 269), (122, 171), (164, 220), (165, 240), (170, 219), (172, 219), (177, 240), (178, 220), (220, 171), (221, 269), (227, 270)]) (.e1 [(122, 175), (123, 308), (130, 233), (163, 214), (164, 171), (170, 147), (172, 147), (178, 171), (179, 214), (212, 233), (213, 332), (219, 308), (220, 175)] [(115, 261), (121, 277), (122, 173), (164, 210), (165, 230), (170, 239), (172, 239), (177, 230), (178, 210), (220, 173), (221, 277), (227, 261)])))) (.redFull 172)))

theorem root916 : rootCheck plan916 ![3, 2] ![1, 1, 0] = true := by decide +kernel

def plan917 : Plan :=
  (.e1 [(122, 175), (164, 132), (170, 121), (172, 121), (178, 132), (220, 175)] [(115, 285), (122, 153), (164, 181), (170, 195), (172, 195), (178, 181), (220, 153), (227, 285)])

theorem root917 : rootCheck plan917 ![3, 2] ![1, 1, 1] = true := by decide +kernel

def plan918 : Plan :=
  (.e1 [(122, 175), (164, 132), (170, 121), (172, 121), (178, 132), (220, 175)] [(122, 142), (164, 181), (170, 195), (172, 195), (178, 181), (220, 142)])

theorem root918 : rootCheck plan918 ![3, 2] ![1, 1, 2] = true := by decide +kernel

def plan919 : Plan :=
  (.e1 [(122, 181), (164, 138), (165, 175), (170, 141), (172, 141), (177, 175), (178, 138), (219, 324), (220, 181)] [(122, 131), (163, 271), (164, 213), (170, 210), (172, 210), (178, 213), (179, 271), (220, 131)])

theorem root919 : rootCheck plan919 ![3, 2] ![1, 1, 3] = true := by decide +kernel

def plan920_0 : Plan :=
  (.redFull 178)

theorem plan920_0_ok : plan920_0.checkAt
    ((rootAddress ![3, 2] ![1, 2, 0]).child false)
    (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 false) = true := by decide +kernel

def plan920_1 : Plan :=
  (.cut 3 (.cut 1 (.redFull 178) (.cut 4 (.cut 0 (.e1 [(122, 169), (123, 281), (130, 227), (163, 209), (164, 172), (170, 160), (172, 160), (178, 172), (179, 209), (212, 227), (219, 281), (220, 169)] [(115, 283), (121, 261), (122, 180), (164, 208), (165, 219), (170, 242), (172, 242), (177, 219), (178, 208), (220, 180), (221, 261), (227, 283)]) (.redFull 172)) (.redProjected 0 1))) (.cut 1 (.redFull 178) (.cut 0 (.cut 4 (.cut 3 (.cut 2 (.e1 [(122, 175), (123, 269), (130, 227), (163, 208), (164, 165), (170, 165), (172, 165), (178, 165), (179, 208), (212, 227), (213, 383), (219, 269), (220, 175)] [(115, 292), (121, 248), (122, 178), (164, 212), (165, 223), (170, 244), (172, 244), (177, 223), (178, 212), (220, 178), (221, 248), (227, 292)]) (.e1 [(122, 175), (123, 269), (129, 367), (130, 217), (163, 217), (164, 168), (170, 165), (172, 165), (178, 168), (179, 217), (212, 217), (213, 367), (219, 269), (220, 175)] [(115, 279), (121, 245), (122, 184), (128, 438), (164, 212), (165, 223), (170, 244), (172, 244), (177, 223), (178, 212), (214, 438), (220, 184), (221, 245), (227, 279)])) (.cut 2 (.cut 4 (.e1 [(122, 178), (123, 255), (129, 385), (130, 211), (163, 216), (164, 167), (170, 171), (172, 171), (178, 167), (179, 216), (212, 211), (213, 385), (219, 255), (220, 178)] [(115, 285), (121, 233), (122, 188), (128, 417), (164, 213), (165, 221), (170, 250), (172, 250), (177, 221), (178, 213), (214, 417), (220, 188), (221, 233), (227, 285)]) (.redProjected 0 1)) (.cut 4 (.cut 1 (.e1 [(115, 579), (122, 178), (123, 257), (129, 364), (130, 204), (163, 228), (164, 165), (170, 173), (172, 173), (178, 165), (179, 228), (212, 204), (213, 364), (219, 257), (220, 178), (227, 579)] [(115, 275), (116, 588), (121, 228), (122, 194), (128, 439), (164, 216), (165, 224), (170, 243), (172, 243), (177, 224), (178, 216), (214, 439), (220, 194), (221, 228), (226, 588), (227, 275), (228, 641)]) (.redProjected 0 1)) (.redProjected 0 1)))) (.redProjected 0 1)) (.redFull 172))))

theorem plan920_1_ok : plan920_1.checkAt
    ((((rootAddress ![3, 2] ![1, 2, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 false) 2 false) = true := by decide +kernel

def plan920_2 : Plan :=
  (.cut 1 (.cut 0 (.cut 4 (.cut 3 (.e1 [(122, 175), (123, 300), (129, 320), (130, 229), (163, 229), (164, 158), (170, 158), (172, 158), (178, 158), (179, 229), (212, 229), (213, 320), (219, 300), (220, 175)] [(115, 265), (121, 258), (122, 179), (164, 217), (165, 237), (170, 224), (172, 224), (177, 237), (178, 217), (220, 179), (221, 258), (227, 265)]) (.cut 2 (.e1 [(122, 175), (123, 290), (129, 334), (130, 225), (163, 225), (164, 154), (170, 167), (172, 167), (178, 154), (179, 225), (212, 225), (213, 334), (219, 290), (220, 175)] [(115, 277), (121, 247), (122, 180), (164, 222), (165, 232), (170, 224), (172, 224), (177, 232), (178, 222), (220, 180), (221, 247), (227, 277)]) (.cut 1 (.redFull 178) (.e1 [(122, 175), (123, 288), (129, 324), (130, 213), (163, 232), (164, 163), (170, 165), (172, 165), (178, 163), (179, 232), (212, 213), (213, 324), (219, 288), (220, 175)] [(115, 262), (121, 246), (122, 188), (128, 488), (164, 219), (165, 230), (170, 229), (172, 229), (177, 230), (178, 219), (214, 488), (220, 188), (221, 246), (226, 539), (227, 262)])))) (.e1 [(122, 175), (123, 272), (130, 243), (163, 253), (164, 156), (170, 148), (172, 148), (178, 156), (179, 253), (212, 243), (213, 327), (219, 272), (220, 175)] [(115, 269), (121, 252), (122, 179), (164, 200), (165, 260), (170, 224), (172, 224), (177, 260), (178, 200), (220, 179), (221, 252), (227, 269)])) (.redFull 172)) (.cut 0 (.cut 4 (.cut 3 (.e1 [(122, 172), (123, 293), (129, 336), (130, 223), (163, 220), (164, 172), (170, 155), (172, 155), (178, 172), (179, 220), (212, 223), (213, 336), (219, 293), (220, 172)] [(115, 263), (121, 263), (122, 182), (164, 210), (165, 226), (170, 238), (172, 238), (177, 226), (178, 210), (220, 182), (221, 263), (227, 263)]) (.cut 2 (.e1 [(122, 175), (123, 282), (129, 351), (130, 217), (163, 217), (164, 171), (170, 159), (172, 159), (178, 171), (179, 217), (212, 217), (213, 351), (219, 282), (220, 175)] [(115, 268), (121, 254), (122, 183), (164, 212), (165, 223), (170, 244), (172, 244), (177, 223), (178, 212), (220, 183), (221, 254), (227, 268)]) (.cut 1 (.cut 0 (.e1 [(122, 172), (123, 280), (129, 329), (130, 206), (163, 234), (164, 174), (170, 163), (172, 163), (178, 174), (179, 234), (212, 206), (213, 329), (219, 280), (220, 172)] [(115, 256), (121, 247), (122, 195), (164, 213), (165, 223), (170, 238), (172, 238), (177, 223), (178, 213), (220, 195), (221, 247), (227, 256)]) (.redFull 172)) (.redProjected 0 1)))) (.redProjected 0 1)) (.redFull 172)))

theorem plan920_2_ok : plan920_2.checkAt
    (((((rootAddress ![3, 2] ![1, 2, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 false) 2 true) 3 false) = true := by decide +kernel

def plan920_3 : Plan :=
  (.cut 0 (.cut 1 (.cut 4 (.cut 3 (.cut 2 (.e1 [(122, 181), (123, 271), (129, 339), (130, 206), (163, 235), (164, 160), (170, 169), (172, 169), (178, 160), (179, 235), (212, 206), (213, 339), (219, 271), (220, 181)] [(114, 627), (115, 265), (116, 566), (121, 231), (122, 190), (128, 469), (164, 221), (165, 231), (170, 235), (172, 235), (177, 231), (178, 221), (214, 469), (220, 190), (221, 231), (226, 566), (227, 265), (228, 627)]) (.cut 0 (.e1 [(122, 174), (123, 272), (129, 320), (130, 196), (163, 248), (164, 166), (170, 175), (172, 175), (178, 166), (179, 248), (212, 196), (213, 320), (219, 272), (220, 174)] [(115, 256), (121, 230), (122, 205), (164, 220), (165, 225), (170, 229), (172, 229), (177, 225), (178, 220), (214, 491), (220, 205), (221, 230), (227, 256)]) (.redFull 178))) (.cut 2 (.cut 0 (.e1 [(122, 174), (123, 260), (129, 334), (130, 196), (163, 248), (164, 162), (170, 182), (172, 182), (178, 162), (179, 248), (212, 196), (213, 334), (219, 260), (220, 174)] [(115, 268), (121, 221), (122, 206), (164, 220), (165, 225), (170, 229), (172, 229), (177, 225), (178, 220), (220, 206), (221, 221), (227, 268)]) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) (.cut 4 (.e1 [(115, 618), (122, 174), (123, 260), (129, 321), (130, 187), (131, 675), (163, 258), (164, 167), (170, 182), (172, 182), (178, 167), (179, 258), (211, 675), (212, 187), (213, 321), (219, 260), (220, 174), (227, 618)] [(114, 584), (115, 256), (116, 580), (121, 219), (122, 215), (128, 488), (164, 221), (165, 223), (170, 231), (172, 231), (177, 223), (178, 221), (214, 488), (220, 215), (221, 219), (226, 580), (227, 256), (228, 584)]) (.e1 [(122, 174), (123, 252), (129, 321), (130, 196), (163, 267), (164, 167), (170, 174), (172, 174), (178, 167), (179, 267), (212, 196), (213, 321), (219, 252), (220, 174)] [(115, 256), (121, 222), (122, 213), (164, 211), (165, 234), (170, 231), (172, 231), (177, 234), (178, 211), (220, 213), (221, 222), (227, 256)]))) (.redFull 178)))) (.cut 2 (.e1 [(122, 181), (123, 246), (129, 339), (130, 219), (163, 262), (164, 160), (170, 159), (172, 159), (178, 160), (179, 262), (212, 219), (213, 339), (219, 246), (220, 181)] [(115, 265), (121, 227), (122, 193), (164, 202), (165, 254), (170, 235), (172, 235), (177, 254), (178, 202), (220, 193), (221, 227), (227, 265)]) (.cut 0 (.e1 [(122, 174), (123, 245), (129, 320), (130, 208), (163, 277), (164, 166), (170, 165), (172, 165), (178, 166), (179, 277), (212, 208), (213, 320), (219, 245), (220, 174)] [(115, 257), (121, 226), (122, 208), (164, 201), (165, 247), (170, 229), (172, 229), (177, 247), (178, 201), (220, 208), (221, 226), (227, 257)]) (.redFull 178)))) (.cut 4 (.cut 3 (.cut 2 (.cut 1 (.cut 4 (.cut 0 (.e1 [(122, 169), (123, 272), (129, 339), (130, 210), (163, 233), (164, 168), (170, 170), (172, 170), (178, 168), (179, 233), (212, 210), (213, 339), (219, 272), (220, 169)] [(115, 270), (121, 241), (122, 196), (128, 467), (164, 213), (165, 223), (170, 232), (172, 232), (177, 223), (178, 213), (214, 467), (220, 196), (221, 241), (227, 270)]) (.redFull 178)) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 1 (.cut 0 (.cut 4 (.e1 [(122, 172), (123, 270), (129, 329), (130, 195), (163, 242), (164, 174), (170, 171), (172, 171), (178, 174), (179, 242), (212, 195), (213, 329), (219, 270), (220, 172)] [(115, 255), (116, 564), (121, 235), (122, 205), (128, 479), (164, 215), (165, 220), (170, 238), (172, 238), (177, 220), (178, 215), (214, 479), (220, 205), (221, 235), (226, 564), (227, 255), (228, 613)]) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))) (.cut 2 (.cut 1 (.cut 0 (.e1 [(122, 174), (123, 255), (129, 344), (130, 192), (163, 244), (164, 172), (170, 177), (172, 177), (178, 172), (179, 244), (212, 192), (213, 344), (219, 255), (220, 174)] [(115, 263), (121, 224), (122, 208), (128, 460), (164, 215), (165, 220), (170, 241), (172, 241), (177, 220), (178, 215), (214, 460), (220, 208), (221, 224), (227, 263), (228, 610)]) (.redFull 178)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 263), (129, 326), (130, 189), (163, 250), (164, 176), (170, 179), (172, 179), (178, 176), (179, 250), (212, 189), (213, 326), (219, 263), (220, 168)] [(115, 256), (121, 228), (122, 215), (128, 482), (164, 215), (165, 217), (170, 235), (172, 235), (177, 217), (178, 215), (214, 482), (220, 215), (221, 228), (227, 256)]) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 258), (129, 326), (130, 185), (163, 256), (164, 176), (170, 182), (172, 182), (178, 176), (179, 256), (212, 185), (213, 326), (219, 258), (220, 168)] [(115, 256), (121, 223), (122, 220), (128, 481), (164, 215), (165, 217), (170, 235), (172, 235), (177, 217), (178, 215), (214, 481), (220, 220), (221, 223), (226, 585), (227, 256)]) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1)))) (.redProjected 0 1))) (.cut 1 (.redFull 178) (.redFull 172)))

theorem plan920_3_ok : plan920_3.checkAt
    (((((rootAddress ![3, 2] ![1, 2, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 false) 2 true) 3 true) = true := by decide +kernel

def plan920_n0 : Plan := .cut 3 plan920_2 plan920_3

theorem plan920_n0_ok : plan920_n0.checkAt
    ((((rootAddress ![3, 2] ![1, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 false) 2 true) = true :=
  checkAt_cut 3 plan920_2 plan920_3
    ((((rootAddress ![3, 2] ![1, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 false) 2 true)
    (by decide +kernel) plan920_2_ok plan920_3_ok

def plan920_n1 : Plan := .cut 2 plan920_1 plan920_n0

theorem plan920_n1_ok : plan920_n1.checkAt
    (((rootAddress ![3, 2] ![1, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 false) = true :=
  checkAt_cut 2 plan920_1 plan920_n0
    (((rootAddress ![3, 2] ![1, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 false)
    (by decide +kernel) plan920_1_ok plan920_n0_ok

def plan920_4 : Plan :=
  (.cut 2 (.cut 3 (.e1 [(122, 175), (163, 260), (164, 151), (170, 136), (172, 136), (178, 151), (179, 260), (219, 259), (220, 175)] [(115, 287), (121, 260), (122, 168), (164, 185), (165, 285), (170, 224), (172, 224), (177, 285), (178, 185), (220, 168), (221, 260), (227, 287)]) (.e1 [(122, 181), (123, 230), (130, 266), (163, 276), (164, 154), (170, 138), (172, 138), (178, 154), (179, 276), (212, 266), (219, 230), (220, 181)] [(115, 285), (121, 239), (122, 177), (164, 179), (165, 293), (170, 235), (172, 235), (177, 293), (178, 179), (220, 177), (221, 239), (227, 285)])) (.cut 0 (.cut 4 (.e1 [(122, 172), (123, 245), (129, 326), (130, 251), (163, 284), (164, 161), (170, 142), (172, 142), (178, 161), (179, 284), (212, 251), (213, 326), (219, 245), (220, 172)] [(115, 266), (121, 247), (122, 188), (164, 183), (165, 278), (170, 225), (172, 225), (177, 278), (178, 183), (220, 188), (221, 247), (227, 266)]) (.redProjected 0 1)) (.redFull 172)))

theorem plan920_4_ok : plan920_4.checkAt
    (((rootAddress ![3, 2] ![1, 2, 0]).child true).child true)
    (childBox (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) 4 true) = true := by decide +kernel

def plan920_n2 : Plan := .cut 4 plan920_n1 plan920_4

theorem plan920_n2_ok : plan920_n2.checkAt
    ((rootAddress ![3, 2] ![1, 2, 0]).child true)
    (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true) = true :=
  checkAt_cut 4 plan920_n1 plan920_4
    ((rootAddress ![3, 2] ![1, 2, 0]).child true)
    (childBox (rootBox ![3, 2] ![1, 2, 0]) 1 true)
    (by decide +kernel) plan920_n1_ok plan920_4_ok

def plan920 : Plan := .cut 1 plan920_0 plan920_n2

theorem plan920_ok : plan920.checkAt
    (rootAddress ![3, 2] ![1, 2, 0])
    (rootBox ![3, 2] ![1, 2, 0]) = true :=
  checkAt_cut 1 plan920_0 plan920_n2
    (rootAddress ![3, 2] ![1, 2, 0])
    (rootBox ![3, 2] ![1, 2, 0])
    (by decide +kernel) plan920_0_ok plan920_n2_ok

theorem root920 : rootCheck plan920 ![3, 2] ![1, 2, 0] = true := plan920_ok

def plan921 : Plan :=
  (.cut 4 (.e1 [(122, 181), (123, 236), (129, 322), (130, 315), (164, 138), (170, 130), (172, 130), (178, 138), (212, 315), (213, 322), (219, 236), (220, 181)] [(115, 289), (121, 248), (122, 168), (164, 175), (170, 210), (172, 210), (177, 357), (178, 175), (220, 168), (221, 248), (227, 289)]) (.e1 [(122, 175), (123, 230), (164, 132), (170, 136), (172, 136), (178, 132), (219, 230), (220, 175)] [(115, 304), (121, 250), (122, 171), (164, 174), (170, 195), (172, 195), (178, 174), (220, 171), (221, 250), (227, 304)]))

theorem root921 : rootCheck plan921 ![3, 2] ![1, 2, 1] = true := by decide +kernel

def plan922 : Plan :=
  (.e1 [(122, 181), (123, 232), (129, 322), (164, 138), (165, 271), (170, 126), (172, 126), (177, 271), (178, 138), (213, 322), (219, 232), (220, 181)] [(121, 278), (122, 153), (164, 170), (170, 210), (172, 210), (178, 170), (220, 153), (221, 278), (228, 372)])

theorem root922 : rootCheck plan922 ![3, 2] ![1, 2, 2] = true := by decide +kernel

def plan923 : Plan :=
  (.cut 0 (.e1 [(122, 172), (123, 259), (129, 332), (164, 154), (165, 179), (170, 156), (172, 156), (177, 179), (178, 154), (213, 332), (219, 259), (220, 172)] [(114, 315), (121, 312), (122, 151), (163, 258), (164, 199), (170, 220), (172, 220), (178, 199), (179, 258), (220, 151), (221, 312), (227, 411), (228, 315)]) (.e1 [(122, 201), (123, 246), (164, 145), (165, 177), (170, 143), (172, 143), (177, 177), (178, 145), (219, 246), (220, 201)] [(114, 310), (121, 289), (122, 137), (163, 286), (164, 202), (170, 240), (172, 240), (178, 202), (179, 286), (220, 137), (221, 289), (228, 310)]))

theorem root923 : rootCheck plan923 ![3, 2] ![1, 2, 3] = true := by decide +kernel

def plan924_0 : Plan :=
  (.redFull 178)

theorem plan924_0_ok : plan924_0.checkAt
    ((rootAddress ![3, 2] ![1, 3, 0]).child false)
    (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 false) = true := by decide +kernel

def plan924_1 : Plan :=
  (.cut 3 (.cut 0 (.cut 4 (.cut 1 (.redFull 178) (.cut 2 (.cut 3 (.cut 0 (.e1 [(122, 174), (123, 240), (129, 382), (130, 197), (163, 230), (164, 172), (170, 182), (172, 182), (178, 172), (179, 230), (212, 197), (213, 382), (219, 240), (220, 174)] [(115, 282), (121, 221), (122, 205), (128, 418), (164, 211), (165, 217), (170, 250), (172, 250), (177, 217), (178, 211), (214, 418), (220, 205), (221, 221), (227, 282)]) (.redFull 178)) (.cut 0 (.cut 4 (.e1 [(115, 559), (121, 748), (122, 172), (123, 232), (129, 381), (130, 193), (131, 640), (163, 239), (164, 170), (165, 736), (170, 190), (172, 190), (177, 736), (178, 170), (179, 239), (211, 640), (212, 193), (213, 381), (219, 232), (220, 172), (221, 748), (227, 559)] [(114, 620), (115, 286), (116, 634), (121, 212), (122, 214), (127, 764), (128, 419), (129, 757), (164, 212), (165, 217), (170, 245), (172, 245), (177, 217), (178, 212), (213, 757), (214, 419), (215, 764), (220, 214), (221, 212), (226, 634), (227, 286), (228, 620), (270, 797)]) (.redProjected 0 1)) (.redFull 178))) (.cut 4 (.cut 3 (.cut 1 (.cut 0 (.e1 [(122, 174), (123, 245), (129, 359), (130, 191), (163, 243), (164, 168), (170, 186), (172, 186), (178, 168), (179, 243), (212, 191), (213, 359), (219, 245), (220, 174)] [(115, 274), (121, 215), (122, 211), (128, 443), (164, 216), (165, 219), (170, 241), (172, 241), (177, 219), (178, 216), (214, 443), (220, 211), (221, 215), (227, 274)]) (.redFull 178)) (.redProjected 0 1)) (.cut 0 (.cut 1 (.e1 [(122, 171), (123, 236), (129, 358), (130, 192), (163, 252), (164, 165), (170, 192), (172, 192), (178, 165), (179, 252), (212, 192), (213, 358), (219, 236), (220, 171)] [(115, 281), (116, 627), (121, 209), (122, 217), (128, 443), (164, 214), (165, 222), (170, 235), (172, 235), (177, 222), (178, 214), (214, 443), (220, 217), (221, 209), (226, 627), (227, 281), (228, 596)]) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)))) (.cut 1 (.redFull 178) (.redProjected 0 1))) (.redFull 178)) (.cut 0 (.cut 4 (.cut 1 (.redFull 178) (.cut 2 (.cut 0 (.cut 3 (.e1 [(115, 559), (122, 172), (123, 225), (129, 381), (130, 191), (131, 641), (163, 247), (164, 170), (170, 192), (172, 192), (178, 170), (179, 247), (211, 641), (212, 191), (213, 381), (219, 225), (220, 172), (227, 559)] [(114, 605), (115, 286), (121, 207), (122, 219), (128, 419), (164, 209), (165, 220), (170, 245), (172, 245), (177, 220), (178, 209), (214, 419), (220, 219), (221, 207), (226, 650), (227, 286), (228, 605)]) (.e1 [(122, 172), (123, 215), (129, 389), (130, 187), (163, 253), (164, 168), (170, 200), (172, 200), (178, 168), (179, 253), (212, 187), (213, 389), (219, 215), (220, 172)] [(115, 293), (121, 198), (122, 226), (128, 412), (164, 209), (165, 220), (170, 245), (172, 245), (177, 220), (178, 209), (214, 412), (220, 226), (221, 198), (227, 293)])) (.redFull 178)) (.cut 0 (.cut 4 (.cut 3 (.e1 [(115, 570), (122, 172), (123, 227), (129, 373), (130, 185), (163, 251), (164, 171), (170, 194), (172, 194), (178, 171), (179, 251), (212, 185), (213, 373), (219, 227), (220, 172), (227, 570)] [(114, 598), (115, 280), (121, 205), (122, 223), (128, 428), (164, 212), (165, 217), (170, 245), (172, 245), (177, 217), (178, 212), (214, 428), (220, 223), (221, 205), (226, 644), (227, 280), (228, 598)]) (.e1 [(122, 169), (123, 213), (130, 179), (163, 271), (164, 172), (170, 204), (172, 204), (178, 172), (179, 271), (212, 179), (213, 367), (219, 213), (220, 169)] [(115, 281), (121, 194), (122, 240), (128, 435), (164, 208), (165, 219), (170, 242), (172, 242), (177, 219), (178, 208), (214, 435), (220, 240), (221, 194), (227, 281)])) (.redProjected 0 1)) (.redProjected 0 1)))) (.cut 1 (.redFull 178) (.redProjected 0 1))) (.redFull 178)))

theorem plan924_1_ok : plan924_1.checkAt
    ((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 false) = true := by decide +kernel

def plan924_2 : Plan :=
  (.cut 1 (.cut 2 (.cut 0 (.cut 1 (.redFull 178) (.cut 3 (.e1 [(122, 172), (123, 248), (129, 335), (130, 194), (163, 259), (164, 161), (170, 187), (172, 187), (178, 161), (179, 259), (212, 194), (213, 335), (219, 248), (220, 172)] [(115, 270), (121, 214), (122, 214), (128, 471), (164, 217), (165, 227), (170, 228), (172, 228), (177, 227), (178, 217), (214, 471), (220, 214), (221, 214), (227, 270)]) (.e1 [(122, 172), (123, 242), (129, 335), (130, 190), (163, 265), (164, 161), (170, 191), (172, 191), (178, 161), (179, 265), (212, 190), (213, 335), (219, 242), (220, 172)] [(115, 270), (121, 209), (122, 219), (128, 470), (164, 217), (165, 227), (170, 228), (172, 228), (177, 227), (178, 217), (214, 470), (220, 219), (221, 209), (227, 270)]))) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 167), (123, 253), (129, 318), (130, 191), (163, 269), (164, 164), (170, 190), (172, 190), (178, 164), (179, 269), (212, 191), (213, 318), (219, 253), (220, 167)] [(115, 265), (121, 216), (122, 222), (128, 492), (164, 218), (165, 225), (170, 221), (172, 221), (177, 225), (178, 218), (214, 492), (220, 222), (221, 216), (227, 265), (228, 567)]) (.cut 2 (.redFull 178) (.cut 4 (.e1 [(115, 617), (122, 174), (123, 256), (129, 320), (130, 185), (163, 263), (164, 166), (170, 186), (172, 186), (178, 166), (179, 263), (212, 185), (213, 320), (219, 256), (220, 174), (227, 617)] [(114, 576), (115, 256), (116, 587), (121, 215), (122, 219), (128, 490), (164, 221), (165, 224), (170, 229), (172, 229), (177, 224), (178, 221), (214, 490), (220, 219), (221, 215), (226, 587), (227, 256), (228, 576)]) (.e1 [(81, 711), (115, 611), (122, 172), (123, 249), (129, 320), (130, 191), (131, 683), (137, 720), (163, 270), (164, 166), (165, 683), (170, 183), (172, 183), (177, 683), (178, 166), (179, 270), (205, 720), (211, 683), (212, 191), (213, 320), (219, 249), (220, 172), (221, 718), (227, 611), (261, 711)] [(114, 564), (115, 259), (116, 602), (121, 215), (122, 219), (128, 489), (164, 215), (165, 230), (170, 228), (172, 228), (177, 230), (178, 215), (214, 489), (220, 219), (221, 215), (226, 602), (227, 259), (228, 564)])))) (.e1 [(122, 172), (123, 242), (129, 320), (130, 193), (163, 278), (164, 166), (170, 181), (172, 181), (178, 166), (179, 278), (212, 193), (213, 320), (219, 242), (220, 172)] [(115, 259), (121, 214), (122, 220), (128, 489), (164, 210), (165, 235), (170, 228), (172, 228), (177, 235), (178, 210), (214, 489), (220, 220), (221, 214), (227, 259)])) (.cut 4 (.e1 [(122, 172), (123, 240), (129, 320), (130, 186), (163, 279), (164, 166), (170, 189), (172, 189), (178, 166), (179, 279), (212, 186), (213, 320), (219, 240), (220, 172)] [(114, 549), (115, 260), (116, 618), (121, 208), (122, 227), (128, 489), (164, 215), (165, 230), (170, 228), (172, 228), (177, 230), (178, 215), (214, 489), (220, 227), (221, 208), (226, 618), (227, 260), (228, 549)]) (.e1 [(122, 174), (123, 238), (129, 321), (130, 188), (163, 282), (164, 167), (170, 183), (172, 183), (178, 167), (179, 282), (212, 188), (213, 321), (219, 238), (220, 174)] [(115, 257), (121, 209), (122, 225), (164, 211), (165, 234), (170, 231), (172, 231), (177, 234), (178, 211), (220, 225), (221, 209), (227, 257)])))) (.redFull 178))) (.cut 2 (.cut 4 (.cut 0 (.cut 3 (.cut 1 (.cut 2 (.e1 [(122, 172), (123, 246), (129, 349), (130, 190), (163, 249), (164, 168), (170, 185), (172, 185), (178, 168), (179, 249), (212, 190), (213, 349), (219, 246), (220, 172)] [(115, 270), (121, 216), (122, 214), (128, 454), (164, 215), (165, 220), (170, 238), (172, 238), (177, 220), (178, 215), (214, 454), (220, 214), (221, 216), (227, 270)]) (.cut 4 (.cut 0 (.e1 [(122, 166), (123, 249), (129, 338), (130, 192), (163, 256), (164, 168), (170, 189), (172, 189), (178, 168), (179, 256), (212, 192), (213, 338), (219, 249), (220, 166)] [(115, 271), (116, 602), (121, 218), (122, 219), (128, 467), (164, 215), (165, 220), (170, 228), (172, 228), (177, 220), (178, 215), (214, 467), (220, 219), (221, 218), (226, 602), (227, 271), (228, 589)]) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)) (.cut 1 (.e1 [(115, 597), (122, 172), (123, 240), (129, 343), (130, 184), (131, 658), (163, 259), (164, 170), (170, 189), (172, 189), (177, 714), (178, 170), (179, 259), (211, 658), (212, 184), (213, 343), (219, 240), (220, 172), (227, 597)] [(114, 582), (115, 266), (116, 617), (121, 210), (122, 222), (128, 460), (164, 215), (165, 220), (170, 238), (172, 238), (177, 220), (178, 215), (214, 460), (220, 222), (221, 210), (226, 617), (227, 266), (228, 582)]) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.cut 3 (.cut 2 (.cut 4 (.cut 0 (.e1 [(122, 167), (123, 250), (129, 331), (130, 187), (163, 260), (164, 171), (170, 188), (172, 188), (178, 171), (179, 260), (212, 187), (213, 331), (219, 250), (220, 167)] [(114, 582), (115, 264), (116, 599), (121, 218), (122, 222), (128, 475), (164, 215), (165, 219), (170, 230), (172, 230), (177, 219), (178, 215), (214, 475), (220, 222), (221, 218), (226, 599), (227, 264), (228, 582)]) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.e1 [(115, 616), (122, 168), (123, 254), (129, 325), (130, 184), (163, 261), (164, 174), (170, 185), (172, 185), (178, 174), (179, 261), (211, 670), (212, 184), (213, 325), (219, 254), (220, 168), (227, 616)] [(114, 579), (115, 257), (116, 591), (121, 220), (122, 223), (128, 483), (164, 215), (165, 218), (170, 233), (172, 233), (177, 218), (178, 215), (214, 483), (220, 223), (221, 220), (226, 591), (227, 257), (228, 579)]) (.redProjected 0 1)) (.redProjected 0 1))) (.cut 0 (.e1 [(122, 166), (123, 238), (129, 329), (130, 183), (163, 275), (164, 173), (170, 192), (172, 192), (178, 173), (179, 275), (212, 183), (213, 329), (219, 238), (220, 166)] [(114, 556), (115, 263), (121, 210), (122, 233), (128, 478), (164, 211), (165, 221), (170, 231), (172, 231), (177, 221), (178, 211), (214, 478), (220, 233), (221, 210), (227, 263), (228, 556)]) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))))

theorem plan924_2_ok : plan924_2.checkAt
    (((((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 3 false) = true := by decide +kernel

def plan924_3 : Plan :=
  (.cut 1 (.cut 2 (.cut 0 (.e1 [(122, 169), (123, 222), (129, 335), (130, 187), (163, 290), (164, 158), (170, 204), (172, 204), (178, 158), (179, 290), (212, 187), (213, 335), (219, 222), (220, 169)] [(114, 537), (115, 279), (121, 195), (122, 236), (128, 471), (164, 213), (165, 233), (170, 222), (172, 222), (177, 233), (178, 213), (214, 471), (220, 236), (221, 195), (227, 279), (228, 537)]) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) (.e1 [(122, 169), (123, 227), (129, 320), (130, 184), (163, 296), (164, 162), (170, 199), (172, 199), (178, 162), (179, 296), (212, 184), (213, 320), (219, 227), (220, 169)] [(115, 268), (121, 198), (122, 239), (128, 489), (164, 213), (165, 233), (170, 222), (172, 222), (177, 233), (178, 213), (214, 489), (220, 239), (221, 198), (227, 268), (228, 526)])) (.redFull 178))) (.cut 2 (.cut 0 (.cut 4 (.e1 [(115, 592), (122, 172), (123, 220), (129, 357), (130, 181), (163, 270), (164, 175), (170, 192), (172, 192), (178, 175), (179, 270), (211, 644), (212, 181), (213, 357), (219, 220), (220, 172), (227, 592), (261, 692)] [(114, 564), (115, 270), (116, 659), (121, 201), (122, 233), (128, 444), (164, 207), (165, 223), (170, 245), (172, 245), (177, 223), (178, 207), (214, 444), (220, 233), (221, 201), (226, 659), (227, 270), (228, 564)]) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.e1 [(122, 172), (123, 223), (129, 336), (130, 177), (163, 285), (164, 172), (170, 195), (172, 195), (178, 172), (179, 285), (212, 177), (213, 336), (219, 223), (220, 172)] [(115, 262), (121, 198), (122, 239), (164, 210), (165, 226), (170, 238), (172, 238), (177, 226), (178, 210), (214, 469), (220, 239), (221, 198), (227, 262)]) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))))

theorem plan924_3_ok : plan924_3.checkAt
    (((((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 3 true) = true := by decide +kernel

def plan924_n0 : Plan := .cut 3 plan924_2 plan924_3

theorem plan924_n0_ok : plan924_n0.checkAt
    ((((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) = true :=
  checkAt_cut 3 plan924_2 plan924_3
    ((((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 false)
    (by decide +kernel) plan924_2_ok plan924_3_ok

def plan924_4 : Plan :=
  (.cut 3 (.cut 1 (.cut 2 (.e1 [(122, 181), (123, 222), (129, 339), (130, 203), (163, 285), (164, 160), (170, 174), (172, 174), (178, 160), (179, 285), (212, 203), (213, 339), (219, 222), (220, 181)] [(115, 267), (121, 206), (122, 213), (164, 202), (165, 254), (170, 235), (172, 235), (177, 254), (178, 202), (220, 213), (221, 206), (227, 267)]) (.cut 0 (.e1 [(122, 172), (123, 225), (129, 318), (130, 201), (163, 300), (164, 164), (170, 178), (172, 178), (178, 164), (179, 300), (212, 201), (213, 318), (219, 225), (220, 172)] [(115, 263), (121, 209), (122, 225), (128, 492), (164, 200), (165, 251), (170, 225), (172, 225), (177, 251), (178, 200), (214, 492), (220, 225), (221, 209), (227, 263), (228, 519)]) (.redFull 178))) (.redProjected 0 1)) (.cut 1 (.e1 [(122, 178), (123, 209), (129, 327), (130, 197), (163, 312), (164, 160), (170, 185), (172, 185), (178, 160), (179, 312), (212, 197), (213, 327), (219, 209), (220, 178)] [(114, 502), (115, 269), (121, 195), (122, 230), (128, 481), (164, 201), (165, 257), (170, 229), (172, 229), (177, 257), (178, 201), (214, 481), (220, 230), (221, 195), (227, 269), (228, 502)]) (.redProjected 0 1)))

theorem plan924_4_ok : plan924_4.checkAt
    ((((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 true) = true := by decide +kernel

def plan924_n1 : Plan := .cut 4 plan924_n0 plan924_4

theorem plan924_n1_ok : plan924_n1.checkAt
    (((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 false) = true :=
  checkAt_cut 4 plan924_n0 plan924_4
    (((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 false)
    (by decide +kernel) plan924_n0_ok plan924_4_ok

def plan924_5 : Plan :=
  (.cut 3 (.cut 4 (.cut 1 (.redFull 178) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 4 (.cut 1 (.redFull 178) (.redProjected 0 1)) (.redProjected 0 1)))

theorem plan924_5_ok : plan924_5.checkAt
    (((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) 0 true) = true := by decide +kernel

def plan924_n2 : Plan := .cut 0 plan924_n1 plan924_5

theorem plan924_n2_ok : plan924_n2.checkAt
    ((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true) = true :=
  checkAt_cut 0 plan924_n1 plan924_5
    ((((rootAddress ![3, 2] ![1, 3, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) 2 true)
    (by decide +kernel) plan924_n1_ok plan924_5_ok

def plan924_n3 : Plan := .cut 2 plan924_1 plan924_n2

theorem plan924_n3_ok : plan924_n3.checkAt
    (((rootAddress ![3, 2] ![1, 3, 0]).child true).child false)
    (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false) = true :=
  checkAt_cut 2 plan924_1 plan924_n2
    (((rootAddress ![3, 2] ![1, 3, 0]).child true).child false)
    (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 false)
    (by decide +kernel) plan924_1_ok plan924_n2_ok

def plan924_6 : Plan :=
  (.cut 2 (.cut 3 (.cut 0 (.e1 [(122, 175), (123, 211), (130, 249), (163, 287), (164, 158), (170, 154), (172, 154), (178, 158), (179, 287), (212, 249), (219, 211), (220, 175)] [(115, 292), (121, 222), (122, 196), (164, 179), (165, 282), (170, 234), (172, 234), (177, 282), (178, 179), (220, 196), (221, 222), (227, 292)]) (.redFull 172)) (.e1 [(122, 188), (123, 185), (129, 375), (130, 227), (163, 306), (164, 158), (170, 165), (172, 165), (178, 158), (179, 306), (212, 227), (213, 375), (219, 185), (220, 188)] [(114, 511), (115, 290), (121, 196), (122, 211), (164, 180), (165, 287), (170, 247), (172, 247), (177, 287), (178, 180), (214, 433), (220, 211), (221, 196), (227, 290), (228, 511)])) (.cut 0 (.cut 3 (.cut 4 (.e1 [(122, 175), (123, 205), (129, 335), (130, 230), (163, 315), (164, 165), (170, 158), (172, 158), (178, 165), (179, 315), (212, 230), (213, 335), (219, 205), (220, 175)] [(115, 272), (121, 215), (122, 213), (164, 179), (165, 282), (170, 234), (172, 234), (177, 282), (178, 179), (220, 213), (221, 215), (227, 272), (228, 500)]) (.redProjected 0 1)) (.e1 [(122, 175), (123, 189), (129, 335), (130, 220), (163, 334), (164, 165), (170, 170), (172, 170), (178, 165), (179, 334), (212, 220), (213, 335), (219, 189), (220, 175)] [(115, 277), (121, 200), (122, 229), (164, 179), (165, 282), (170, 234), (172, 234), (177, 282), (178, 179), (220, 229), (221, 200), (227, 277)])) (.redProjected 0 1)))

theorem plan924_6_ok : plan924_6.checkAt
    (((rootAddress ![3, 2] ![1, 3, 0]).child true).child true)
    (childBox (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) 4 true) = true := by decide +kernel

def plan924_n4 : Plan := .cut 4 plan924_n3 plan924_6

theorem plan924_n4_ok : plan924_n4.checkAt
    ((rootAddress ![3, 2] ![1, 3, 0]).child true)
    (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true) = true :=
  checkAt_cut 4 plan924_n3 plan924_6
    ((rootAddress ![3, 2] ![1, 3, 0]).child true)
    (childBox (rootBox ![3, 2] ![1, 3, 0]) 1 true)
    (by decide +kernel) plan924_n3_ok plan924_6_ok

def plan924 : Plan := .cut 1 plan924_0 plan924_n4

theorem plan924_ok : plan924.checkAt
    (rootAddress ![3, 2] ![1, 3, 0])
    (rootBox ![3, 2] ![1, 3, 0]) = true :=
  checkAt_cut 1 plan924_0 plan924_n4
    (rootAddress ![3, 2] ![1, 3, 0])
    (rootBox ![3, 2] ![1, 3, 0])
    (by decide +kernel) plan924_0_ok plan924_n4_ok

theorem root924 : rootCheck plan924 ![3, 2] ![1, 3, 0] = true := plan924_ok

def plan925 : Plan :=
  (.cut 4 (.cut 1 (.redFull 178) (.redProjected 0 1)) (.e1 [(122, 181), (123, 180), (164, 138), (170, 151), (172, 151), (178, 138), (213, 322), (219, 180), (220, 181)] [(121, 213), (122, 194), (164, 165), (170, 210), (172, 210), (178, 165), (220, 194), (221, 213), (227, 327)]))

theorem root925 : rootCheck plan925 ![3, 2] ![1, 3, 1] = true := by decide +kernel

def plan926 : Plan :=
  (.cut 4 (.e1 [(122, 181), (123, 180), (164, 138), (170, 151), (172, 151), (178, 138), (213, 322), (219, 180), (220, 181)] [(121, 223), (122, 185), (164, 165), (170, 210), (172, 210), (178, 165), (220, 185), (221, 223)]) (.cut 1 (.redFull 178) (.redProjected 0 1)))

theorem root926 : rootCheck plan926 ![3, 2] ![1, 3, 2] = true := by decide +kernel

def plan927 : Plan :=
  (.cut 4 (.cut 3 (.e1 [(116, 381), (122, 188), (123, 217), (129, 342), (164, 145), (165, 203), (170, 158), (172, 158), (177, 203), (178, 145), (213, 342), (219, 217), (220, 188), (226, 381)] [(114, 309), (115, 429), (121, 260), (122, 158), (129, 465), (163, 294), (164, 193), (170, 226), (172, 226), (178, 193), (179, 294), (213, 465), (220, 158), (221, 260), (227, 429), (228, 309)]) (.cut 2 (.cut 1 (.redFull 178) (.e1 [(116, 340), (122, 181), (123, 184), (164, 154), (165, 224), (170, 170), (172, 170), (177, 224), (178, 154), (219, 184), (220, 181), (226, 340)] [(114, 303), (121, 233), (122, 181), (129, 443), (163, 293), (164, 179), (170, 235), (172, 235), (178, 179), (179, 293), (213, 443), (220, 181), (221, 233), (228, 303)])) (.cut 4 (.cut 0 (.e1 [(122, 175), (123, 190), (164, 150), (165, 235), (170, 171), (172, 171), (177, 235), (178, 150), (213, 311), (219, 190), (220, 175)] [(114, 298), (121, 244), (122, 184), (163, 315), (164, 179), (170, 214), (172, 214), (178, 179), (179, 315), (220, 184), (221, 244), (228, 298)]) (.e1 [(122, 194), (123, 183), (129, 330), (164, 149), (165, 226), (170, 163), (172, 163), (177, 226), (178, 149), (213, 330), (219, 183), (220, 194)] [(114, 292), (121, 235), (122, 174), (163, 325), (164, 181), (170, 233), (172, 233), (178, 181), (179, 325), (220, 174), (221, 235), (228, 292)])) (.cut 1 (.redFull 178) (.e1 [(116, 359), (122, 181), (123, 189), (164, 162), (165, 204), (170, 174), (172, 174), (177, 204), (178, 162), (213, 331), (219, 189), (220, 181), (226, 359)] [(114, 280), (121, 249), (122, 180), (163, 282), (164, 184), (170, 235), (172, 235), (178, 184), (179, 282), (220, 180), (221, 249), (228, 280)]))))) (.cut 1 (.redFull 178) (.cut 3 (.e1 [(116, 344), (122, 175), (123, 231), (164, 161), (165, 173), (170, 174), (172, 174), (177, 173), (178, 161), (219, 231), (220, 175), (226, 344)] [(114, 294), (121, 279), (122, 163), (163, 244), (164, 203), (170, 234), (172, 234), (178, 203), (179, 244), (220, 163), (221, 279), (228, 294)]) (.cut 0 (.cut 4 (.cut 1 (.e1 [(116, 327), (122, 175), (123, 205), (164, 157), (165, 195), (170, 186), (172, 186), (177, 195), (178, 157), (213, 346), (219, 205), (220, 175), (226, 327)] [(114, 291), (121, 248), (122, 179), (163, 258), (164, 197), (170, 229), (172, 229), (178, 197), (179, 258), (220, 179), (221, 248), (228, 291)]) (.redProjected 0 1)) (.cut 1 (.e1 [(116, 303), (122, 175), (123, 217), (129, 342), (164, 152), (165, 180), (170, 208), (172, 208), (177, 180), (178, 152), (213, 342), (219, 217), (220, 175), (226, 303)] [(114, 286), (121, 245), (122, 179), (163, 237), (164, 217), (170, 224), (172, 224), (178, 217), (179, 237), (220, 179), (221, 245), (228, 286)]) (.cut 2 (.e1 [(116, 283), (122, 175), (123, 209), (164, 166), (165, 179), (170, 199), (172, 199), (177, 179), (178, 166), (213, 375), (219, 209), (220, 175), (226, 283)] [(114, 288), (121, 243), (122, 183), (129, 427), (163, 228), (164, 207), (170, 244), (172, 244), (178, 207), (179, 228), (213, 427), (220, 183), (221, 243), (228, 288)]) (.e1 [(116, 309), (122, 175), (123, 209), (129, 344), (164, 173), (165, 167), (170, 199), (172, 199), (177, 167), (178, 173), (213, 344), (219, 209), (220, 175), (226, 309)] [(114, 267), (121, 261), (122, 181), (163, 228), (164, 207), (170, 244), (172, 244), (178, 207), (179, 228), (220, 181), (221, 261), (228, 267)])))) (.cut 3 (.e1 [(116, 321), (122, 194), (123, 209), (164, 162), (165, 170), (170, 179), (172, 179), (177, 170), (178, 162), (219, 209), (220, 194), (226, 321)] [(114, 276), (121, 254), (122, 164), (163, 250), (164, 207), (170, 254), (172, 254), (178, 207), (179, 250), (213, 441), (220, 164), (221, 254), (228, 276)]) (.cut 2 (.redFull 178) (.e1 [(116, 321), (122, 194), (123, 198), (164, 166), (165, 170), (170, 188), (172, 188), (177, 170), (178, 166), (213, 347), (219, 198), (220, 194), (226, 321)] [(114, 262), (121, 250), (122, 172), (163, 250), (164, 207), (170, 254), (172, 254), (178, 207), (179, 250), (220, 172), (221, 250), (228, 262)])))))))

theorem root927 : rootCheck plan927 ![3, 2] ![1, 3, 3] = true := by decide +kernel

def plan928 : Plan :=
  (.cut 4 (.cut 0 (.cut 2 (.cut 4 (.e1 [(122, 175), (129, 290), (130, 276), (163, 200), (164, 157), (170, 144), (172, 144), (178, 157), (179, 200), (212, 276), (213, 290), (219, 390), (220, 175)] [(115, 268), (121, 326), (122, 156), (164, 223), (165, 242), (170, 214), (172, 214), (177, 242), (178, 223), (220, 156), (221, 326), (226, 427), (227, 268)]) (.e1 [(122, 172), (130, 300), (163, 220), (164, 150), (170, 138), (172, 138), (178, 150), (179, 220), (212, 300), (220, 172)] [(115, 267), (121, 335), (122, 156), (164, 214), (165, 265), (170, 201), (172, 201), (177, 265), (178, 214), (220, 156), (221, 335), (227, 267)])) (.cut 4 (.cut 3 (.e1 [(115, 670), (121, 461), (122, 169), (123, 424), (129, 261), (130, 278), (163, 204), (164, 169), (170, 146), (172, 146), (178, 169), (179, 204), (212, 278), (213, 261), (219, 424), (220, 169), (221, 461), (227, 670)] [(114, 727), (115, 256), (116, 391), (121, 352), (122, 165), (123, 586), (164, 221), (165, 240), (170, 207), (172, 207), (177, 240), (178, 221), (219, 586), (220, 165), (221, 352), (226, 391), (227, 256), (228, 727)]) (.cut 1 (.e1 [(122, 178), (129, 250), (130, 252), (163, 223), (164, 159), (170, 151), (172, 151), (178, 159), (179, 223), (212, 252), (213, 250), (219, 396), (220, 178)] [(115, 241), (121, 310), (122, 172), (164, 235), (165, 249), (170, 202), (172, 202), (177, 249), (178, 235), (220, 172), (221, 310), (227, 241)]) (.e1 [(122, 169), (129, 264), (130, 237), (163, 218), (164, 180), (170, 148), (172, 148), (178, 180), (179, 218), (212, 237), (213, 264), (220, 169)] [(115, 237), (121, 317), (122, 181), (164, 220), (165, 230), (170, 217), (172, 217), (177, 230), (178, 220), (220, 181), (221, 317), (227, 237)]))) (.e1 [(122, 172), (123, 391), (129, 252), (130, 277), (163, 235), (164, 162), (170, 138), (172, 138), (178, 162), (179, 235), (212, 277), (213, 252), (219, 391), (220, 172)] [(115, 242), (121, 333), (122, 169), (164, 214), (165, 265), (170, 201), (172, 201), (177, 265), (178, 214), (220, 169), (221, 333), (226, 426), (227, 242)]))) (.redFull 172)) (.e1 [(122, 175), (130, 299), (163, 261), (164, 153), (170, 129), (172, 129), (178, 153), (179, 261), (212, 299), (213, 248), (220, 175)] [(115, 240), (121, 332), (122, 165), (164, 206), (165, 296), (170, 195), (172, 195), (177, 296), (178, 206), (220, 165), (221, 332), (227, 240)]))

theorem root928 : rootCheck plan928 ![3, 2] ![2, 0, 0] = true := by decide +kernel

def plan929 : Plan :=
  (.redFull 172)

theorem root929 : rootCheck plan929 ![3, 2] ![2, 0, 1] = true := by decide +kernel

def plan930 : Plan :=
  (.redFull 172)

theorem root930 : rootCheck plan930 ![3, 2] ![2, 0, 2] = true := by decide +kernel

def plan931 : Plan :=
  (.cut 4 (.e1 [(122, 175), (164, 153), (165, 233), (170, 127), (172, 127), (177, 233), (178, 153), (213, 248), (220, 175)] [(115, 254), (122, 154), (164, 206), (170, 195), (172, 195), (178, 206), (179, 296), (220, 154), (227, 254)]) (.cut 0 (.cut 1 (.e1 [(122, 175), (128, 332), (129, 248), (164, 153), (165, 199), (170, 146), (172, 146), (177, 199), (178, 153), (213, 248), (214, 332), (220, 175)] [(115, 271), (122, 154), (163, 263), (164, 227), (170, 195), (172, 195), (178, 227), (179, 263), (220, 154), (227, 271)]) (.e1 [(122, 166), (164, 176), (165, 192), (170, 149), (172, 149), (177, 192), (178, 176), (213, 258), (214, 284), (220, 166)] [(115, 261), (122, 166), (163, 232), (164, 222), (170, 209), (172, 209), (178, 222), (179, 232), (220, 166), (227, 261)])) (.redFull 172)))

theorem root931 : rootCheck plan931 ![3, 2] ![2, 0, 3] = true := by decide +kernel

def plan932_0 : Plan :=
  (.cut 4 (.cut 2 (.cut 0 (.cut 1 (.redFull 178) (.cut 3 (.e1 [(122, 169), (130, 248), (163, 229), (164, 156), (170, 157), (172, 157), (178, 156), (179, 229), (212, 248), (213, 276), (220, 169)] [(115, 258), (121, 289), (122, 176), (164, 224), (165, 243), (170, 203), (172, 203), (177, 243), (178, 224), (220, 176), (221, 289), (227, 258)]) (.cut 4 (.e1 [(122, 181), (123, 324), (129, 282), (130, 219), (163, 238), (164, 157), (170, 160), (172, 160), (178, 157), (179, 238), (212, 219), (213, 282), (219, 324), (220, 181)] [(115, 245), (121, 259), (122, 183), (164, 232), (165, 241), (170, 215), (172, 215), (177, 241), (178, 232), (220, 183), (221, 259), (226, 490), (227, 245)]) (.e1 [(122, 175), (129, 275), (130, 251), (163, 260), (164, 152), (170, 147), (172, 147), (178, 152), (179, 260), (212, 251), (213, 275), (220, 175)] [(115, 249), (121, 274), (122, 177), (164, 212), (165, 269), (170, 204), (172, 204), (177, 269), (178, 212), (220, 177), (221, 274), (227, 249)])))) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 172), (129, 253), (130, 224), (163, 242), (164, 168), (170, 158), (172, 158), (178, 168), (179, 242), (212, 224), (213, 253), (219, 355), (220, 172)] [(115, 233), (121, 284), (122, 191), (164, 229), (165, 239), (170, 206), (172, 206), (177, 239), (178, 229), (220, 191), (221, 284), (227, 233)]) (.redFull 172)) (.e1 [(122, 175), (129, 256), (130, 251), (163, 260), (164, 161), (170, 141), (172, 141), (178, 161), (179, 260), (212, 251), (213, 256), (220, 175)] [(115, 234), (121, 293), (122, 180), (164, 212), (165, 269), (170, 204), (172, 204), (177, 269), (178, 212), (220, 180), (221, 293), (227, 234)])) (.cut 4 (.cut 0 (.e1 [(122, 174), (123, 322), (129, 252), (130, 199), (163, 265), (164, 172), (170, 167), (172, 167), (178, 172), (179, 265), (212, 199), (213, 252), (219, 322), (220, 174)] [(115, 224), (116, 487), (121, 257), (122, 210), (164, 231), (165, 235), (170, 210), (172, 210), (177, 235), (178, 231), (220, 210), (221, 257), (226, 487), (227, 224)]) (.cut 1 (.redFull 178) (.e1 [(122, 177), (123, 321), (129, 254), (130, 197), (163, 264), (164, 174), (170, 164), (172, 164), (178, 174), (179, 264), (212, 197), (213, 254), (219, 321), (220, 177)] [(114, 574), (115, 221), (116, 488), (121, 256), (122, 208), (128, 592), (164, 231), (165, 236), (170, 214), (172, 214), (177, 236), (178, 231), (214, 592), (220, 208), (221, 256), (226, 488), (227, 221), (228, 574)]))) (.e1 [(122, 175), (123, 317), (129, 250), (130, 234), (163, 281), (164, 164), (170, 147), (172, 147), (178, 164), (179, 281), (212, 234), (213, 250), (219, 317), (220, 175)] [(115, 227), (121, 275), (122, 193), (164, 212), (165, 269), (170, 204), (172, 204), (177, 269), (178, 212), (220, 193), (221, 275), (227, 227)])))) (.redFull 178))) (.cut 2 (.e1 [(122, 181), (129, 270), (130, 285), (163, 281), (164, 139), (170, 135), (172, 135), (178, 139), (179, 281), (212, 285), (213, 270), (220, 181)] [(115, 253), (121, 282), (122, 164), (164, 207), (165, 307), (170, 196), (172, 196), (177, 307), (178, 207), (220, 164), (221, 282), (227, 253)]) (.e1 [(122, 181), (123, 319), (129, 243), (130, 267), (163, 301), (164, 152), (165, 529), (170, 135), (172, 135), (177, 529), (178, 152), (179, 301), (212, 267), (213, 243), (219, 319), (220, 181)] [(114, 527), (115, 230), (116, 516), (121, 285), (122, 179), (164, 207), (165, 307), (170, 196), (172, 196), (177, 307), (178, 207), (220, 179), (221, 285), (226, 516), (227, 230), (228, 527)])))

theorem plan932_0_ok : plan932_0.checkAt
    ((rootAddress ![3, 2] ![2, 1, 0]).child false)
    (childBox (rootBox ![3, 2] ![2, 1, 0]) 1 false) = true := by decide +kernel

def plan932_1 : Plan :=
  (.cut 4 (.cut 2 (.cut 3 (.e1 [(122, 175), (123, 344), (129, 292), (130, 239), (163, 220), (164, 168), (170, 145), (172, 145), (178, 168), (179, 220), (212, 239), (213, 292), (219, 344), (220, 175)] [(115, 248), (121, 293), (122, 172), (164, 217), (165, 237), (170, 224), (172, 224), (177, 237), (178, 217), (220, 172), (221, 293), (227, 248)]) (.cut 1 (.cut 0 (.cut 4 (.cut 3 (.e1 [(122, 172), (123, 330), (129, 291), (130, 230), (163, 228), (164, 165), (170, 154), (172, 154), (178, 165), (179, 228), (212, 230), (213, 291), (219, 330), (220, 172)] [(115, 252), (121, 278), (122, 180), (164, 220), (165, 235), (170, 218), (172, 218), (177, 235), (178, 220), (220, 180), (221, 278), (227, 252)]) (.e1 [(122, 169), (123, 313), (129, 293), (130, 214), (163, 237), (164, 172), (170, 160), (172, 160), (178, 172), (179, 237), (212, 214), (213, 293), (219, 313), (220, 169)] [(114, 626), (115, 246), (116, 501), (121, 266), (122, 193), (128, 532), (164, 218), (165, 228), (170, 222), (172, 222), (177, 228), (178, 218), (214, 532), (220, 193), (221, 266), (226, 501), (227, 246), (228, 626)])) (.e1 [(122, 169), (129, 295), (130, 251), (163, 251), (164, 165), (170, 140), (172, 140), (178, 165), (179, 251), (212, 251), (213, 295), (219, 307), (220, 169)] [(115, 252), (121, 283), (122, 179), (164, 199), (165, 257), (170, 217), (172, 217), (177, 257), (178, 199), (220, 179), (221, 283), (227, 252)])) (.redFull 172)) (.cut 0 (.cut 4 (.e1 [(122, 169), (123, 312), (129, 301), (130, 212), (163, 231), (164, 181), (170, 155), (172, 155), (178, 181), (179, 231), (212, 212), (213, 301), (219, 312), (220, 169)] [(115, 243), (121, 272), (122, 192), (128, 521), (164, 213), (165, 223), (170, 232), (172, 232), (177, 223), (178, 213), (214, 521), (220, 192), (221, 272), (226, 501), (227, 243)]) (.redFull 172)) (.redFull 172)))) (.cut 3 (.cut 1 (.cut 0 (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 351), (129, 264), (130, 227), (163, 236), (164, 176), (170, 153), (172, 153), (178, 176), (179, 236), (212, 227), (213, 264), (219, 351), (220, 168)] [(115, 235), (116, 455), (121, 294), (122, 190), (164, 219), (165, 234), (170, 213), (172, 213), (177, 234), (178, 219), (214, 584), (220, 190), (221, 294), (226, 455), (227, 235)]) (.redFull 172)) (.redFull 172)) (.redFull 172)) (.cut 0 (.e1 [(122, 166), (129, 270), (130, 210), (163, 238), (164, 192), (170, 151), (172, 151), (178, 192), (179, 238), (212, 210), (213, 270), (219, 339), (220, 166)] [(115, 226), (121, 291), (122, 200), (164, 213), (165, 223), (170, 226), (172, 226), (177, 223), (178, 213), (220, 200), (221, 291), (227, 226)]) (.redFull 172))) (.cut 0 (.cut 1 (.cut 4 (.cut 0 (.cut 1 (.cut 2 (.e1 [(122, 172), (123, 320), (129, 272), (130, 207), (163, 250), (164, 174), (170, 160), (172, 160), (178, 174), (179, 250), (212, 207), (213, 272), (219, 320), (220, 172)] [(115, 233), (116, 492), (121, 264), (122, 199), (164, 222), (165, 232), (170, 218), (172, 218), (177, 232), (178, 222), (220, 199), (221, 264), (226, 492), (227, 233)]) (.cut 3 (.e1 [(122, 172), (123, 331), (129, 260), (130, 205), (163, 252), (164, 180), (170, 157), (172, 157), (178, 180), (179, 252), (212, 205), (213, 260), (219, 331), (220, 172)] [(115, 223), (116, 477), (121, 273), (122, 203), (164, 222), (165, 232), (170, 218), (172, 218), (177, 232), (178, 222), (220, 203), (221, 273), (226, 477), (227, 223)]) (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 317), (129, 258), (130, 194), (163, 264), (164, 182), (170, 167), (172, 167), (178, 182), (179, 264), (212, 194), (213, 258), (219, 317), (220, 168)] [(115, 223), (121, 260), (122, 216), (164, 224), (165, 227), (170, 215), (172, 215), (177, 227), (178, 224), (220, 216), (221, 260), (227, 223)]) (.e1 [(122, 174), (123, 318), (129, 260), (130, 195), (163, 261), (164, 180), (170, 162), (172, 162), (178, 180), (179, 261), (212, 195), (213, 260), (219, 318), (220, 174)] [(114, 580), (115, 221), (116, 493), (121, 259), (122, 211), (164, 225), (165, 230), (170, 219), (172, 219), (177, 230), (178, 225), (214, 581), (220, 211), (221, 259), (226, 493), (227, 221), (228, 580)])) (.e1 [(122, 169), (123, 313), (129, 257), (130, 211), (163, 272), (164, 178), (170, 155), (172, 155), (178, 178), (179, 272), (212, 211), (213, 257), (219, 313), (220, 169)] [(115, 224), (121, 269), (122, 207), (164, 214), (165, 243), (170, 212), (172, 212), (177, 243), (178, 214), (220, 207), (221, 269), (227, 224)])))) (.cut 2 (.cut 3 (.e1 [(122, 169), (123, 331), (129, 280), (130, 216), (163, 235), (164, 178), (170, 155), (172, 155), (178, 178), (179, 235), (212, 216), (213, 280), (219, 331), (220, 169)] [(115, 237), (121, 280), (122, 192), (164, 218), (165, 228), (170, 222), (172, 222), (177, 228), (178, 218), (220, 192), (221, 280), (227, 237)]) (.e1 [(122, 169), (123, 317), (129, 280), (130, 208), (163, 245), (164, 178), (170, 159), (172, 159), (178, 178), (179, 245), (212, 208), (213, 280), (219, 317), (220, 169)] [(115, 235), (116, 495), (121, 267), (122, 200), (128, 551), (164, 218), (165, 228), (170, 222), (172, 222), (177, 228), (178, 218), (214, 551), (220, 200), (221, 267), (226, 495), (227, 235)])) (.cut 4 (.cut 3 (.e1 [(122, 169), (123, 327), (129, 268), (130, 206), (163, 248), (164, 184), (170, 156), (172, 156), (178, 184), (179, 248), (212, 206), (213, 268), (219, 327), (220, 169)] [(115, 226), (121, 276), (122, 203), (164, 218), (165, 228), (170, 222), (172, 222), (177, 228), (178, 218), (220, 203), (221, 276), (227, 226)]) (.e1 [(122, 172), (123, 316), (129, 264), (130, 194), (163, 259), (164, 184), (170, 161), (172, 161), (178, 184), (179, 259), (212, 194), (213, 264), (219, 316), (220, 172)] [(114, 583), (115, 220), (116, 495), (121, 261), (122, 212), (164, 222), (165, 227), (170, 223), (172, 223), (177, 227), (178, 222), (214, 575), (220, 212), (221, 261), (226, 495), (227, 220), (228, 583)])) (.e1 [(122, 169), (123, 309), (129, 268), (130, 209), (163, 265), (164, 184), (170, 151), (172, 151), (178, 184), (179, 265), (212, 209), (213, 268), (219, 309), (220, 169)] [(115, 224), (121, 271), (122, 206), (164, 209), (165, 238), (170, 222), (172, 222), (177, 238), (178, 209), (220, 206), (221, 271), (227, 224)])))) (.redFull 172)) (.e1 [(122, 169), (123, 306), (129, 260), (130, 222), (163, 278), (164, 176), (170, 148), (172, 148), (178, 176), (179, 278), (212, 222), (213, 260), (219, 306), (220, 169)] [(115, 226), (121, 273), (122, 202), (164, 206), (165, 254), (170, 212), (172, 212), (177, 254), (178, 206), (220, 202), (221, 273), (227, 226)])) (.cut 4 (.cut 3 (.e1 [(122, 169), (123, 323), (129, 276), (130, 202), (163, 244), (164, 193), (170, 151), (172, 151), (178, 193), (179, 244), (212, 202), (213, 276), (219, 323), (220, 169)] [(115, 223), (121, 279), (122, 203), (164, 213), (165, 223), (170, 232), (172, 232), (177, 223), (178, 213), (220, 203), (221, 279), (227, 223)]) (.e1 [(122, 169), (123, 309), (129, 276), (130, 194), (163, 255), (164, 193), (170, 156), (172, 156), (178, 193), (179, 255), (212, 194), (213, 276), (219, 309), (220, 169)] [(115, 221), (116, 504), (121, 266), (122, 211), (128, 557), (164, 213), (165, 223), (170, 232), (172, 232), (177, 223), (178, 213), (214, 557), (220, 211), (221, 266), (226, 504), (227, 221)])) (.redFull 172))) (.redFull 172)))) (.redFull 172))

theorem plan932_1_ok : plan932_1.checkAt
    ((rootAddress ![3, 2] ![2, 1, 0]).child true)
    (childBox (rootBox ![3, 2] ![2, 1, 0]) 1 true) = true := by decide +kernel

def plan932 : Plan := .cut 1 plan932_0 plan932_1

theorem plan932_ok : plan932.checkAt
    (rootAddress ![3, 2] ![2, 1, 0])
    (rootBox ![3, 2] ![2, 1, 0]) = true :=
  checkAt_cut 1 plan932_0 plan932_1
    (rootAddress ![3, 2] ![2, 1, 0])
    (rootBox ![3, 2] ![2, 1, 0])
    (by decide +kernel) plan932_0_ok plan932_1_ok

theorem root932 : rootCheck plan932 ![3, 2] ![2, 1, 0] = true := plan932_ok

def plan933 : Plan :=
  (.e1 [(122, 175), (129, 248), (130, 318), (164, 153), (170, 121), (172, 121), (178, 153), (212, 318), (213, 248), (220, 175)] [(115, 238), (121, 301), (122, 175), (164, 181), (170, 195), (172, 195), (178, 181), (220, 175), (221, 301), (227, 238)])

theorem root933 : rootCheck plan933 ![3, 2] ![2, 1, 1] = true := by decide +kernel

def plan934 : Plan :=
  (.e1 [(122, 175), (129, 248), (164, 153), (170, 121), (172, 121), (177, 264), (178, 153), (213, 248), (220, 175)] [(115, 269), (122, 159), (164, 181), (170, 195), (172, 195), (178, 181), (220, 159), (227, 269)])

theorem root934 : rootCheck plan934 ![3, 2] ![2, 1, 2] = true := by decide +kernel

def plan935 : Plan :=
  (.cut 0 (.e1 [(122, 172), (123, 325), (129, 261), (164, 158), (165, 187), (170, 147), (172, 147), (177, 187), (178, 158), (213, 261), (219, 325), (220, 172)] [(114, 321), (115, 306), (122, 152), (163, 267), (164, 212), (170, 201), (172, 201), (178, 212), (179, 267), (220, 152), (227, 306), (228, 321)]) (.e1 [(122, 197), (129, 272), (164, 160), (165, 170), (170, 131), (172, 131), (177, 170), (178, 160), (213, 272), (219, 324), (220, 197)] [(114, 311), (115, 295), (122, 135), (163, 276), (164, 216), (170, 226), (172, 226), (178, 216), (179, 276), (220, 135), (227, 295), (228, 311)]))

theorem root935 : rootCheck plan935 ![3, 2] ![2, 1, 3] = true := by decide +kernel

def plan936_0 : Plan :=
  (.cut 0 (.cut 1 (.redFull 178) (.cut 3 (.cut 4 (.cut 3 (.cut 0 (.e1 [(122, 174), (123, 307), (129, 277), (130, 206), (163, 255), (164, 159), (170, 172), (172, 172), (178, 159), (179, 255), (212, 206), (213, 277), (219, 307), (220, 174)] [(115, 245), (121, 245), (122, 200), (164, 231), (165, 235), (170, 210), (172, 210), (177, 235), (178, 231), (220, 200), (221, 245), (227, 245)]) (.redFull 178)) (.cut 0 (.e1 [(122, 174), (123, 293), (129, 277), (130, 198), (163, 267), (164, 159), (170, 178), (172, 178), (178, 159), (179, 267), (212, 198), (213, 277), (219, 293), (220, 174)] [(115, 244), (121, 234), (122, 209), (164, 231), (165, 235), (170, 210), (172, 210), (177, 235), (178, 231), (220, 209), (221, 234), (227, 244)]) (.redFull 178))) (.e1 [(122, 181), (123, 281), (129, 282), (130, 220), (163, 278), (164, 157), (170, 156), (172, 156), (178, 157), (179, 278), (212, 220), (213, 282), (219, 281), (220, 181)] [(115, 242), (121, 242), (122, 194), (164, 214), (165, 263), (170, 215), (172, 215), (177, 263), (178, 214), (220, 194), (221, 242), (227, 242)])) (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.cut 2 (.redFull 178) (.cut 3 (.e1 [(115, 642), (122, 172), (123, 281), (129, 277), (130, 195), (163, 280), (164, 159), (170, 182), (172, 182), (178, 159), (179, 280), (205, 684), (212, 195), (213, 277), (219, 281), (220, 172), (227, 642)] [(114, 549), (115, 244), (116, 548), (121, 227), (122, 217), (128, 553), (164, 228), (165, 237), (170, 208), (172, 208), (177, 237), (178, 228), (214, 553), (220, 217), (221, 227), (226, 548), (227, 244), (228, 549)]) (.cut 4 (.cut 0 (.redFull 178) (.redFull 178)) (.e1 [(122, 174), (123, 261), (129, 277), (130, 191), (163, 299), (164, 161), (170, 183), (172, 183), (178, 161), (179, 299), (212, 191), (213, 277), (219, 261), (220, 174)] [(115, 242), (121, 218), (122, 226), (164, 222), (165, 244), (170, 211), (172, 211), (177, 244), (178, 222), (220, 226), (221, 218), (227, 242)]))))) (.redFull 178)) (.cut 0 (.e1 [(122, 174), (123, 255), (129, 277), (130, 203), (163, 307), (164, 159), (170, 175), (172, 175), (178, 159), (179, 307), (212, 203), (213, 277), (219, 255), (220, 174)] [(115, 245), (121, 222), (122, 221), (164, 213), (165, 256), (170, 210), (172, 210), (177, 256), (178, 213), (220, 221), (221, 222), (227, 245)]) (.redFull 178))))) (.redFull 178))

theorem plan936_0_ok : plan936_0.checkAt
    ((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child false)
    (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 false) = true := by decide +kernel

def plan936_1 : Plan :=
  (.redFull 178)

theorem plan936_1_ok : plan936_1.checkAt
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 false) = true := by decide +kernel

def plan936_2 : Plan :=
  (.cut 4 (.cut 0 (.cut 1 (.cut 2 (.redFull 178) (.cut 3 (.e1 [(122, 174), (123, 311), (129, 244), (130, 195), (163, 284), (164, 166), (170, 177), (172, 177), (178, 166), (179, 284), (212, 195), (213, 244), (219, 311), (220, 174)] [(115, 224), (121, 244), (122, 220), (164, 236), (165, 240), (170, 201), (172, 201), (177, 240), (178, 236), (220, 220), (221, 244), (227, 224)]) (.e1 [(122, 172), (123, 299), (129, 243), (130, 194), (163, 297), (164, 164), (170, 181), (172, 181), (178, 164), (179, 297), (212, 194), (213, 243), (219, 299), (220, 172)] [(114, 522), (115, 227), (116, 520), (121, 236), (122, 226), (164, 234), (165, 243), (170, 199), (172, 199), (177, 243), (178, 234), (214, 610), (220, 226), (221, 236), (226, 520), (227, 227), (228, 522)]))) (.cut 2 (.cut 3 (.e1 [(122, 174), (123, 306), (129, 264), (130, 197), (163, 268), (164, 167), (170, 172), (172, 172), (178, 167), (179, 268), (212, 197), (213, 264), (219, 306), (220, 174)] [(115, 232), (121, 245), (122, 211), (164, 230), (165, 235), (170, 211), (172, 211), (177, 235), (178, 230), (220, 211), (221, 245), (226, 509), (227, 232)]) (.e1 [(81, 704), (115, 674), (121, 665), (122, 174), (123, 293), (129, 264), (130, 190), (131, 727), (137, 678), (163, 280), (164, 167), (165, 666), (170, 177), (172, 177), (177, 666), (178, 167), (179, 280), (205, 678), (211, 727), (212, 190), (213, 264), (219, 293), (220, 174), (221, 665), (227, 674), (261, 704)] [(65, 888), (66, 864), (72, 890), (108, 894), (109, 889), (114, 548), (115, 231), (116, 528), (120, 863), (121, 235), (122, 220), (123, 819), (127, 900), (128, 573), (129, 861), (163, 839), (164, 230), (165, 235), (166, 853), (170, 211), (172, 211), (176, 853), (177, 235), (178, 230), (179, 839), (213, 861), (214, 573), (215, 900), (219, 819), (220, 220), (221, 235), (222, 863), (226, 528), (227, 231), (228, 548), (233, 889), (234, 894), (270, 890), (276, 864), (277, 888)])) (.cut 3 (.e1 [(121, 641), (122, 174), (123, 306), (129, 252), (130, 190), (137, 678), (163, 280), (164, 174), (170, 172), (172, 172), (177, 668), (178, 174), (179, 280), (205, 678), (212, 190), (213, 252), (219, 306), (220, 174), (221, 641)] [(114, 548), (115, 221), (116, 508), (121, 245), (122, 221), (128, 595), (164, 230), (165, 235), (170, 211), (172, 211), (177, 235), (178, 230), (214, 595), (220, 221), (221, 245), (226, 508), (227, 221), (228, 548)]) (.cut 4 (.cut 0 (.e1 [(121, 657), (122, 168), (123, 297), (129, 250), (130, 190), (163, 291), (164, 171), (170, 181), (172, 181), (178, 171), (179, 291), (212, 190), (213, 250), (219, 297), (220, 168), (221, 657), (261, 679)] [(114, 530), (115, 227), (116, 522), (121, 239), (122, 230), (128, 598), (164, 229), (165, 234), (170, 204), (172, 204), (177, 234), (178, 229), (214, 598), (220, 230), (221, 239), (226, 522), (227, 227), (228, 530)]) (.cut 1 (.cut 2 (.redFull 178) (.e1 [(121, 665), (122, 174), (123, 297), (129, 248), (130, 187), (137, 672), (163, 293), (164, 170), (165, 661), (170, 179), (172, 179), (177, 661), (178, 170), (179, 293), (205, 672), (212, 187), (213, 248), (219, 297), (220, 174), (221, 665)] [(114, 527), (115, 222), (116, 522), (121, 236), (122, 228), (128, 602), (164, 233), (165, 238), (170, 206), (172, 206), (177, 238), (178, 233), (214, 602), (220, 228), (221, 236), (226, 522), (227, 222), (228, 527)])) (.cut 2 .sb .sb))) (.e1 [(122, 174), (123, 286), (129, 252), (130, 191), (163, 299), (164, 174), (170, 171), (172, 171), (178, 174), (179, 299), (212, 191), (213, 252), (219, 286), (220, 174)] [(114, 518), (115, 221), (116, 538), (121, 239), (122, 227), (164, 222), (165, 244), (170, 211), (172, 211), (177, 244), (178, 222), (220, 227), (221, 239), (226, 538), (227, 221), (228, 518)]))))) (.cut 2 (.redFull 178) (.cut 1 (.redFull 178) (.cut 3 (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.cut 2 (.redFull 178) .sb)) (.redFull 172)) (.redFull 172)) (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.cut 2 (.redFull 178) .sb)) (.redFull 178)) (.cut 0 (.e1 [(81, 701), (115, 707), (121, 661), (122, 180), (123, 286), (129, 255), (130, 191), (131, 714), (137, 697), (163, 296), (164, 173), (165, 637), (170, 166), (172, 166), (177, 637), (178, 173), (179, 296), (205, 697), (211, 714), (212, 191), (213, 255), (219, 286), (220, 180), (221, 661), (227, 707), (261, 701)] [(114, 522), (115, 218), (116, 538), (121, 237), (122, 221), (128, 590), (164, 223), (165, 247), (170, 216), (172, 216), (177, 247), (178, 223), (179, 823), (214, 590), (220, 221), (221, 237), (226, 538), (227, 218), (228, 522)]) (.redFull 172))))))) (.cut 0 (.e1 [(122, 174), (123, 280), (129, 252), (130, 203), (163, 307), (164, 172), (170, 162), (172, 162), (178, 172), (179, 307), (212, 203), (213, 252), (219, 280), (220, 174)] [(115, 223), (121, 244), (122, 221), (164, 213), (165, 256), (170, 210), (172, 210), (177, 256), (178, 213), (220, 221), (221, 244), (227, 223), (228, 508)]) (.cut 1 (.redFull 178) (.redFull 172))))

theorem plan936_2_ok : plan936_2.checkAt
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 false) = true := by decide +kernel

def plan936_3 : Plan :=
  (.cut 3 (.cut 2 (.redFull 178) (.cut 4 (.e1 [(74, 986), (80, 924), (81, 664), (115, 684), (116, 973), (121, 691), (122, 172), (123, 288), (128, 936), (129, 243), (130, 186), (131, 762), (136, 898), (137, 667), (156, 1010), (163, 308), (164, 164), (165, 654), (170, 189), (172, 189), (177, 654), (178, 164), (179, 308), (186, 1010), (205, 667), (206, 898), (211, 762), (212, 186), (213, 243), (214, 936), (219, 288), (220, 172), (221, 691), (226, 973), (227, 684), (261, 664), (262, 924), (268, 986)] [(65, 858), (66, 882), (72, 918), (108, 882), (109, 901), (114, 507), (115, 227), (116, 536), (120, 806), (121, 226), (122, 236), (123, 835), (127, 899), (128, 610), (129, 910), (158, 947), (163, 821), (164, 236), (165, 241), (166, 835), (170, 199), (172, 199), (176, 835), (177, 241), (178, 236), (179, 821), (184, 947), (213, 910), (214, 610), (215, 899), (219, 835), (220, 236), (221, 226), (222, 806), (226, 536), (227, 227), (228, 507), (233, 901), (234, 882), (270, 918), (276, 882), (277, 858)]) (.e1 [(122, 174), (123, 278), (129, 244), (130, 190), (163, 317), (164, 166), (170, 182), (172, 182), (178, 166), (179, 317), (212, 190), (213, 244), (219, 278), (220, 174)] [(115, 225), (121, 228), (122, 235), (164, 228), (165, 249), (170, 201), (172, 201), (177, 249), (178, 228), (220, 235), (221, 228), (226, 550), (227, 225)]))) (.cut 2 (.redFull 178) (.cut 4 (.e1 [(122, 172), (123, 278), (129, 243), (130, 187), (163, 318), (164, 164), (170, 189), (172, 189), (178, 164), (179, 318), (212, 187), (213, 243), (219, 278), (220, 172)] [(114, 493), (115, 228), (116, 552), (121, 224), (122, 239), (164, 232), (165, 246), (170, 199), (172, 199), (177, 246), (178, 232), (214, 610), (220, 239), (221, 224), (226, 552), (227, 228), (228, 493)]) (.e1 [(122, 172), (123, 268), (129, 243), (130, 189), (163, 329), (164, 164), (170, 188), (172, 188), (178, 164), (179, 329), (212, 189), (213, 243), (219, 268), (220, 172)] [(114, 479), (115, 228), (121, 221), (122, 242), (164, 227), (165, 250), (170, 199), (172, 199), (177, 250), (178, 227), (220, 242), (221, 221), (226, 568), (227, 228), (228, 479)]))))

theorem plan936_3_ok : plan936_3.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 false) 0 false) 1 false) = true := by decide +kernel

def plan936_4 : Plan :=
  (.cut 3 (.cut 4 (.cut 2 (.cut 0 (.e1 [(122, 168), (123, 284), (129, 262), (130, 190), (163, 291), (164, 165), (170, 187), (172, 187), (178, 165), (179, 291), (212, 190), (213, 262), (219, 284), (220, 168)] [(114, 531), (115, 237), (121, 229), (122, 230), (164, 229), (165, 234), (170, 204), (172, 204), (177, 234), (178, 229), (220, 230), (221, 229), (226, 542), (227, 237), (228, 531)]) (.cut 1 (.redFull 178) .sb)) (.cut 0 (.cut 1 (.e1 [(122, 167), (123, 287), (129, 247), (130, 189), (163, 304), (164, 167), (170, 188), (172, 188), (178, 167), (179, 304), (212, 189), (213, 247), (219, 287), (220, 167)] [(114, 512), (115, 230), (121, 231), (122, 237), (164, 230), (165, 237), (170, 199), (172, 199), (177, 237), (178, 230), (220, 237), (221, 231), (227, 230), (228, 512)]) (.cut 4 .sb (.e1 [(74, 971), (80, 922), (81, 663), (88, 954), (115, 680), (121, 674), (122, 167), (123, 282), (128, 936), (129, 251), (130, 189), (131, 749), (136, 934), (137, 694), (163, 304), (164, 171), (165, 659), (170, 183), (172, 183), (177, 659), (178, 171), (179, 304), (205, 694), (206, 934), (211, 749), (212, 189), (213, 251), (214, 936), (219, 282), (220, 167), (221, 674), (227, 680), (254, 954), (261, 663), (262, 922), (268, 971)] [(65, 877), (66, 897), (72, 926), (108, 863), (109, 892), (114, 512), (115, 229), (116, 544), (120, 828), (121, 233), (122, 236), (123, 838), (127, 904), (128, 595), (129, 885), (158, 913), (163, 810), (164, 225), (165, 238), (166, 849), (170, 203), (172, 203), (176, 849), (177, 238), (178, 225), (179, 810), (184, 913), (213, 885), (214, 595), (215, 904), (219, 838), (220, 236), (221, 233), (222, 828), (226, 544), (227, 229), (228, 512), (233, 892), (234, 863), (270, 926), (276, 897), (277, 877)]))) (.cut 1 (.cut 3 .sb .sb) (.cut 3 .sb .sb)))) (.cut 2 (.e1 [(122, 174), (123, 273), (129, 264), (130, 191), (163, 299), (164, 167), (170, 177), (172, 177), (178, 167), (179, 299), (212, 191), (213, 264), (219, 273), (220, 174)] [(114, 518), (115, 231), (116, 558), (121, 228), (122, 226), (164, 222), (165, 244), (170, 211), (172, 211), (177, 244), (178, 222), (214, 573), (220, 226), (221, 228), (226, 558), (227, 231), (228, 518)]) (.cut 0 (.e1 [(122, 168), (123, 276), (129, 250), (130, 192), (163, 312), (164, 171), (170, 179), (172, 179), (178, 171), (179, 312), (212, 192), (213, 250), (219, 276), (220, 168)] [(114, 500), (115, 227), (116, 553), (121, 233), (122, 236), (164, 220), (165, 244), (170, 204), (172, 204), (177, 244), (178, 220), (220, 236), (221, 233), (226, 553), (227, 227), (228, 500)]) (.cut 1 (.e1 [(122, 174), (123, 276), (129, 249), (130, 190), (163, 313), (164, 169), (165, 636), (170, 177), (172, 177), (177, 636), (178, 169), (179, 313), (212, 190), (213, 249), (219, 276), (220, 174), (261, 671)] [(114, 500), (115, 224), (116, 553), (121, 230), (122, 233), (128, 599), (164, 224), (165, 247), (170, 206), (172, 206), (177, 247), (178, 224), (214, 599), (220, 233), (221, 230), (226, 553), (227, 224), (228, 500)]) (.cut 3 .sb .sb))))) (.cut 2 (.cut 4 (.cut 0 (.e1 [(122, 166), (123, 273), (129, 264), (130, 190), (163, 300), (164, 163), (170, 191), (172, 191), (178, 163), (179, 300), (212, 190), (213, 264), (219, 273), (220, 166), (261, 667)] [(114, 519), (115, 241), (116, 559), (121, 223), (122, 234), (128, 573), (164, 227), (165, 236), (170, 202), (172, 202), (177, 236), (178, 227), (214, 573), (220, 234), (221, 223), (226, 559), (227, 241), (228, 519)]) (.cut 1 (.redFull 178) (.cut 3 .sb .sb))) (.cut 0 (.e1 [(122, 168), (123, 264), (129, 262), (130, 192), (163, 312), (164, 165), (170, 186), (172, 186), (178, 165), (179, 312), (212, 192), (213, 262), (219, 264), (220, 168)] [(114, 501), (115, 238), (121, 223), (122, 236), (164, 220), (165, 244), (170, 204), (172, 204), (177, 244), (178, 220), (220, 236), (221, 223), (227, 238), (228, 501)]) (.cut 1 (.redFull 178) (.cut 3 (.e1 [(122, 174), (123, 266), (129, 265), (130, 187), (163, 306), (164, 168), (170, 180), (172, 180), (178, 168), (179, 306), (212, 187), (213, 265), (219, 266), (220, 174)] [(114, 508), (115, 231), (116, 570), (121, 222), (122, 232), (128, 572), (164, 222), (165, 243), (170, 212), (172, 212), (177, 243), (178, 222), (214, 572), (220, 232), (221, 222), (226, 570), (227, 231), (228, 508)]) (.e1 [(81, 666), (122, 174), (123, 260), (129, 265), (130, 187), (163, 312), (164, 166), (165, 642), (170, 182), (172, 182), (177, 642), (178, 166), (179, 312), (212, 187), (213, 265), (219, 260), (220, 174), (261, 666)] [(114, 501), (115, 233), (116, 580), (121, 219), (122, 235), (128, 570), (164, 221), (165, 245), (170, 211), (172, 211), (177, 245), (178, 221), (214, 570), (220, 235), (221, 219), (226, 580), (227, 233), (228, 501)]))))) (.cut 4 (.cut 0 (.cut 1 (.e1 [(122, 168), (123, 276), (129, 249), (130, 186), (163, 315), (164, 166), (170, 192), (172, 192), (178, 166), (179, 315), (212, 186), (213, 249), (219, 276), (220, 168)] [(114, 498), (115, 232), (121, 223), (122, 243), (164, 230), (165, 239), (170, 199), (172, 199), (177, 239), (178, 230), (220, 243), (221, 223), (227, 232), (228, 498)]) (.e1 [(81, 645), (122, 167), (123, 273), (129, 251), (130, 184), (163, 313), (164, 171), (170, 188), (172, 188), (178, 171), (179, 313), (212, 184), (213, 251), (219, 273), (220, 167), (227, 680), (261, 645)] [(114, 499), (115, 229), (116, 558), (121, 226), (122, 244), (128, 595), (164, 225), (165, 237), (170, 203), (172, 203), (177, 237), (178, 225), (214, 595), (220, 244), (221, 226), (226, 558), (227, 229), (228, 499)])) (.cut 1 (.cut 3 .sb (.e1 [(122, 174), (123, 269), (129, 249), (130, 181), (163, 320), (164, 169), (170, 187), (172, 187), (178, 169), (179, 320), (212, 181), (213, 249), (219, 269), (220, 174)] [(114, 490), (115, 225), (116, 564), (121, 220), (122, 243), (164, 228), (165, 242), (170, 206), (172, 206), (177, 242), (178, 228), (214, 599), (220, 243), (221, 220), (226, 564), (227, 225), (228, 490)])) (.cut 3 .sb .sb))) (.cut 0 (.cut 1 (.e1 [(122, 166), (123, 269), (129, 245), (130, 194), (163, 327), (164, 167), (170, 186), (172, 186), (178, 167), (179, 327), (212, 194), (213, 245), (219, 269), (220, 166)] [(114, 482), (115, 231), (121, 227), (122, 243), (164, 221), (165, 248), (170, 197), (172, 197), (177, 248), (178, 221), (220, 243), (221, 227), (227, 231), (228, 482)]) (.e1 [(81, 646), (122, 167), (123, 265), (129, 251), (130, 190), (163, 323), (164, 171), (165, 643), (170, 184), (172, 184), (177, 643), (178, 171), (179, 323), (212, 190), (213, 251), (219, 265), (220, 167), (261, 646)] [(114, 486), (115, 230), (116, 573), (121, 226), (122, 243), (128, 595), (164, 219), (165, 244), (170, 203), (172, 203), (177, 244), (178, 219), (214, 595), (220, 243), (221, 226), (226, 573), (227, 230), (228, 486)])) (.cut 1 (.cut 3 (.e1 [(122, 174), (123, 269), (129, 249), (130, 187), (163, 321), (164, 169), (170, 182), (172, 182), (178, 169), (179, 321), (212, 187), (213, 249), (219, 269), (220, 174)] [(114, 488), (115, 225), (116, 565), (121, 224), (122, 239), (128, 599), (164, 224), (165, 247), (170, 206), (172, 206), (177, 247), (178, 224), (214, 599), (220, 239), (221, 224), (226, 565), (227, 225), (228, 488)]) (.e1 [(81, 649), (115, 687), (122, 173), (123, 263), (129, 250), (130, 187), (137, 702), (163, 327), (164, 168), (165, 633), (170, 184), (172, 184), (177, 633), (178, 168), (179, 327), (205, 702), (212, 187), (213, 250), (219, 263), (220, 173), (227, 687), (261, 649)] [(114, 481), (115, 227), (116, 575), (121, 221), (122, 242), (128, 598), (164, 223), (165, 249), (170, 205), (172, 205), (177, 249), (178, 223), (214, 598), (220, 242), (221, 221), (226, 575), (227, 227), (228, 481)])) (.cut 3 .sb (.cut 4 .sb .sb)))))))

theorem plan936_4_ok : plan936_4.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 false) 0 false) 1 true) = true := by decide +kernel

def plan936_n0 : Plan := .cut 1 plan936_3 plan936_4

theorem plan936_n0_ok : plan936_n0.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 false) 0 false) = true :=
  checkAt_cut 1 plan936_3 plan936_4
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 false) 0 false)
    (by decide +kernel) plan936_3_ok plan936_4_ok

def plan936_5 : Plan :=
  (.cut 1 (.redFull 178) (.cut 3 (.cut 2 (.redFull 178) (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.cut 3 .sb .sb)) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) (.cut 3 .sb .sb)) (.redFull 172)))) (.cut 2 (.redFull 178) (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.cut 3 .sb .sb)) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) (.cut 3 .sb (.cut 4 .sb .sb))) (.redFull 178))))))

theorem plan936_5_ok : plan936_5.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 false) 0 true) = true := by decide +kernel

def plan936_n1 : Plan := .cut 0 plan936_n0 plan936_5

theorem plan936_n1_ok : plan936_n1.checkAt
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 false) = true :=
  checkAt_cut 0 plan936_n0 plan936_5
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 false)
    (by decide +kernel) plan936_n0_ok plan936_5_ok

def plan936_6 : Plan :=
  (.cut 0 (.cut 1 (.e1 [(81, 671), (122, 172), (123, 262), (129, 246), (130, 202), (163, 333), (164, 162), (165, 602), (170, 178), (172, 178), (177, 602), (178, 162), (179, 333), (212, 202), (213, 246), (219, 262), (220, 172), (227, 678), (261, 671)] [(114, 474), (115, 232), (116, 579), (121, 226), (122, 233), (128, 606), (164, 217), (165, 263), (170, 199), (172, 199), (177, 263), (178, 217), (214, 606), (220, 233), (221, 226), (226, 579), (227, 232), (228, 474)]) (.cut 3 (.e1 [(122, 174), (123, 265), (129, 253), (130, 196), (163, 321), (164, 173), (170, 168), (172, 168), (178, 173), (179, 321), (212, 196), (213, 253), (219, 265), (220, 174)] [(114, 489), (115, 223), (116, 572), (121, 233), (122, 231), (128, 593), (164, 212), (165, 255), (170, 211), (172, 211), (177, 255), (178, 212), (214, 593), (220, 231), (221, 233), (226, 572), (227, 223), (228, 489)]) (.cut 2 (.e1 [(122, 174), (123, 253), (129, 264), (130, 195), (163, 323), (164, 167), (170, 175), (172, 175), (178, 167), (179, 323), (212, 195), (213, 264), (219, 253), (220, 174)] [(115, 233), (121, 222), (122, 232), (164, 212), (165, 255), (170, 211), (172, 211), (177, 255), (178, 212), (220, 232), (221, 222), (227, 233), (228, 486)]) (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 256), (129, 250), (130, 193), (163, 336), (164, 173), (170, 179), (172, 179), (178, 173), (179, 336), (212, 193), (213, 250), (219, 256), (220, 168)] [(115, 228), (121, 226), (122, 245), (164, 212), (165, 252), (170, 205), (172, 205), (177, 252), (178, 212), (220, 245), (221, 226), (227, 228), (228, 470)]) (.e1 [(81, 654), (122, 174), (123, 255), (129, 252), (130, 192), (163, 333), (164, 172), (165, 617), (170, 175), (172, 175), (177, 617), (178, 172), (179, 333), (212, 192), (213, 252), (219, 255), (220, 174), (261, 654)] [(114, 473), (115, 225), (116, 589), (121, 224), (122, 240), (128, 594), (164, 213), (165, 256), (170, 210), (172, 210), (177, 256), (178, 213), (214, 594), (220, 240), (221, 224), (226, 589), (227, 225), (228, 473)])) (.e1 [(122, 174), (123, 247), (129, 252), (130, 199), (163, 345), (164, 174), (170, 169), (172, 169), (178, 174), (179, 345), (212, 199), (213, 252), (219, 247), (220, 174)] [(115, 225), (121, 226), (122, 239), (164, 205), (165, 265), (170, 211), (172, 211), (177, 265), (178, 205), (220, 239), (221, 226), (227, 225)]))))) (.cut 1 (.redFull 178) (.cut 3 (.cut 2 (.redFull 178) (.cut 4 (.cut 0 (.e1 [(122, 180), (123, 266), (129, 255), (130, 194), (163, 319), (164, 173), (170, 165), (172, 165), (178, 173), (179, 319), (212, 194), (213, 255), (219, 266), (220, 180)] [(114, 491), (115, 219), (116, 571), (121, 231), (122, 227), (164, 214), (165, 258), (170, 216), (172, 216), (177, 258), (178, 214), (220, 227), (221, 231), (226, 571), (227, 219), (228, 491)]) (.redFull 172)) (.redFull 172))) (.cut 2 (.redFull 178) (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.cut 3 (.e1 [(122, 180), (123, 257), (129, 256), (130, 190), (163, 327), (164, 174), (170, 168), (172, 168), (178, 174), (179, 327), (212, 190), (213, 256), (219, 257), (220, 180)] [(114, 481), (115, 220), (116, 585), (121, 225), (122, 233), (128, 588), (164, 213), (165, 258), (170, 217), (172, 217), (177, 258), (178, 213), (214, 588), (220, 233), (221, 225), (226, 585), (227, 220), (228, 481)]) (.e1 [(81, 656), (115, 708), (122, 180), (123, 251), (129, 256), (130, 187), (163, 334), (164, 174), (165, 614), (170, 172), (172, 172), (177, 614), (178, 174), (179, 334), (212, 187), (213, 256), (219, 251), (220, 180), (227, 708), (261, 656)] [(114, 472), (115, 221), (116, 596), (121, 220), (122, 238), (128, 588), (164, 213), (165, 258), (170, 217), (172, 217), (177, 258), (178, 213), (214, 588), (220, 238), (221, 220), (226, 596), (227, 221), (228, 472)]))) (.redFull 172)) (.e1 [(122, 181), (123, 249), (129, 253), (130, 201), (163, 342), (164, 171), (170, 162), (172, 162), (177, 580), (178, 171), (179, 342), (212, 201), (213, 253), (219, 249), (220, 181)] [(114, 463), (115, 222), (116, 603), (121, 227), (122, 229), (128, 595), (164, 206), (165, 274), (170, 215), (172, 215), (177, 274), (178, 206), (214, 595), (220, 229), (221, 227), (226, 603), (227, 222), (228, 463)]))))))

theorem plan936_6_ok : plan936_6.checkAt
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) 4 true) = true := by decide +kernel

def plan936_n2 : Plan := .cut 4 plan936_n1 plan936_6

theorem plan936_n2_ok : plan936_n2.checkAt
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true) = true :=
  checkAt_cut 4 plan936_n1 plan936_6
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) 3 true)
    (by decide +kernel) plan936_n1_ok plan936_6_ok

def plan936_n3 : Plan := .cut 3 plan936_2 plan936_n2

theorem plan936_n3_ok : plan936_n3.checkAt
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true) = true :=
  checkAt_cut 3 plan936_2 plan936_n2
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) 1 true)
    (by decide +kernel) plan936_2_ok plan936_n2_ok

def plan936_n4 : Plan := .cut 1 plan936_1 plan936_n3

theorem plan936_n4_ok : plan936_n4.checkAt
    (((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false) = true :=
  checkAt_cut 1 plan936_1 plan936_n3
    (((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 false)
    (by decide +kernel) plan936_1_ok plan936_n3_ok

def plan936_7 : Plan :=
  (.redFull 178)

theorem plan936_7_ok : plan936_7.checkAt
    (((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) 0 true) = true := by decide +kernel

def plan936_n5 : Plan := .cut 0 plan936_n4 plan936_7

theorem plan936_n5_ok : plan936_n5.checkAt
    ((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true) = true :=
  checkAt_cut 0 plan936_n4 plan936_7
    ((((rootAddress ![3, 2] ![2, 2, 0]).child false).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) 2 true)
    (by decide +kernel) plan936_n4_ok plan936_7_ok

def plan936_n6 : Plan := .cut 2 plan936_0 plan936_n5

theorem plan936_n6_ok : plan936_n6.checkAt
    (((rootAddress ![3, 2] ![2, 2, 0]).child false).child false)
    (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false) = true :=
  checkAt_cut 2 plan936_0 plan936_n5
    (((rootAddress ![3, 2] ![2, 2, 0]).child false).child false)
    (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 false)
    (by decide +kernel) plan936_0_ok plan936_n5_ok

def plan936_8 : Plan :=
  (.cut 0 (.cut 2 (.cut 1 (.redFull 178) (.cut 3 (.e1 [(122, 175), (123, 277), (129, 282), (130, 258), (164, 149), (170, 144), (172, 144), (178, 149), (212, 258), (213, 282), (219, 277), (220, 175)] [(115, 254), (121, 257), (122, 183), (164, 198), (165, 292), (170, 204), (172, 204), (177, 292), (178, 198), (220, 183), (221, 257), (227, 254)]) (.e1 [(122, 181), (123, 240), (129, 282), (130, 230), (163, 327), (164, 157), (170, 153), (172, 153), (178, 157), (179, 327), (212, 230), (213, 282), (219, 240), (220, 181)] [(115, 246), (121, 228), (122, 204), (164, 195), (165, 293), (170, 215), (172, 215), (177, 293), (178, 195), (220, 204), (221, 228), (227, 246)]))) (.cut 1 (.redFull 178) (.cut 3 (.e1 [(122, 175), (123, 277), (129, 256), (130, 242), (163, 318), (164, 161), (170, 144), (172, 144), (178, 161), (179, 318), (212, 242), (213, 256), (219, 277), (220, 175)] [(115, 232), (121, 259), (122, 199), (164, 198), (165, 292), (170, 204), (172, 204), (177, 292), (178, 198), (220, 199), (221, 259), (227, 232)]) (.cut 4 (.cut 0 (.e1 [(122, 172), (123, 246), (129, 253), (130, 219), (164, 168), (170, 161), (172, 161), (178, 168), (179, 350), (212, 219), (213, 253), (219, 246), (220, 172)] [(115, 232), (121, 234), (122, 227), (164, 198), (165, 282), (170, 206), (172, 206), (177, 282), (178, 198), (220, 227), (221, 234), (227, 232)]) (.cut 1 (.redFull 178) (.redFull 172))) (.e1 [(122, 175), (123, 235), (129, 256), (130, 248), (164, 161), (170, 150), (172, 150), (178, 161), (212, 248), (213, 256), (219, 235), (220, 175)] [(115, 241), (121, 239), (122, 213), (164, 186), (165, 318), (170, 204), (172, 204), (177, 318), (178, 186), (220, 213), (221, 239), (227, 241)]))))) (.redFull 178))

theorem plan936_8_ok : plan936_8.checkAt
    (((rootAddress ![3, 2] ![2, 2, 0]).child false).child true)
    (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) 4 true) = true := by decide +kernel

def plan936_n7 : Plan := .cut 4 plan936_n6 plan936_8

theorem plan936_n7_ok : plan936_n7.checkAt
    ((rootAddress ![3, 2] ![2, 2, 0]).child false)
    (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false) = true :=
  checkAt_cut 4 plan936_n6 plan936_8
    ((rootAddress ![3, 2] ![2, 2, 0]).child false)
    (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 false)
    (by decide +kernel) plan936_n6_ok plan936_8_ok

def plan936_9 : Plan :=
  (.cut 4 (.cut 3 (.cut 0 (.cut 1 (.e1 [(122, 174), (123, 302), (129, 287), (130, 201), (163, 250), (164, 169), (170, 167), (172, 167), (178, 169), (179, 250), (212, 201), (213, 287), (219, 302), (220, 174)] [(115, 240), (121, 248), (122, 202), (164, 225), (165, 230), (170, 221), (172, 221), (177, 230), (178, 225), (220, 202), (221, 248), (227, 240)]) (.cut 4 (.e1 [(122, 172), (123, 300), (129, 296), (130, 201), (163, 243), (164, 175), (170, 164), (172, 164), (178, 175), (179, 243), (212, 201), (213, 296), (219, 300), (220, 172)] [(114, 612), (115, 241), (116, 518), (121, 252), (122, 200), (128, 524), (164, 220), (165, 225), (170, 228), (172, 228), (177, 225), (178, 220), (214, 524), (220, 200), (221, 252), (226, 518), (227, 241), (228, 612)]) (.e1 [(122, 169), (123, 295), (129, 293), (130, 217), (163, 254), (164, 172), (170, 155), (172, 155), (178, 172), (179, 254), (212, 217), (213, 293), (219, 295), (220, 169)] [(115, 244), (121, 260), (122, 197), (164, 209), (165, 238), (170, 222), (172, 222), (177, 238), (178, 209), (220, 197), (221, 260), (227, 244)]))) (.cut 1 (.redFull 178) (.redFull 172))) (.cut 0 (.cut 1 (.e1 [(81, 728), (115, 654), (121, 661), (122, 174), (123, 288), (129, 287), (130, 193), (131, 702), (137, 692), (163, 262), (164, 169), (165, 677), (170, 173), (172, 173), (177, 677), (178, 169), (179, 262), (205, 692), (211, 702), (212, 193), (213, 287), (219, 288), (220, 174), (221, 661), (227, 654), (228, 933), (261, 728)] [(65, 915), (66, 867), (72, 866), (108, 910), (109, 893), (114, 577), (115, 239), (116, 535), (120, 896), (121, 237), (122, 210), (123, 818), (127, 885), (128, 537), (129, 823), (158, 880), (163, 853), (164, 225), (165, 230), (166, 868), (170, 221), (172, 221), (176, 868), (177, 230), (178, 225), (179, 853), (184, 880), (213, 823), (214, 537), (215, 885), (219, 818), (220, 210), (221, 237), (222, 896), (226, 535), (227, 239), (228, 577), (233, 893), (234, 910), (270, 866), (276, 867), (277, 915)]) (.cut 4 (.cut 2 (.e1 [(122, 172), (123, 286), (129, 307), (130, 199), (163, 246), (164, 171), (170, 169), (172, 169), (178, 171), (179, 246), (212, 199), (213, 307), (219, 286), (220, 172)] [(115, 249), (121, 242), (122, 203), (128, 509), (164, 220), (165, 225), (170, 228), (172, 228), (177, 225), (178, 220), (214, 509), (220, 203), (221, 242), (227, 249)]) (.cut 0 (.e1 [(115, 657), (122, 168), (123, 286), (129, 291), (130, 190), (163, 260), (164, 177), (170, 173), (172, 173), (178, 177), (179, 260), (212, 190), (213, 291), (219, 286), (220, 168), (227, 657)] [(114, 581), (115, 239), (116, 537), (121, 241), (122, 216), (128, 531), (164, 219), (165, 222), (170, 225), (172, 225), (177, 222), (178, 219), (214, 531), (220, 216), (221, 241), (226, 537), (227, 239), (228, 581)]) (.cut 1 (.cut 3 (.e1 [(122, 174), (123, 293), (129, 290), (130, 192), (163, 254), (164, 174), (170, 168), (172, 168), (178, 174), (179, 254), (212, 192), (213, 290), (219, 293), (220, 174)] [(115, 236), (116, 528), (121, 242), (122, 208), (164, 223), (165, 226), (170, 227), (172, 227), (177, 226), (178, 223), (214, 532), (220, 208), (221, 242), (226, 528), (227, 236)]) (.e1 [(81, 721), (115, 663), (121, 662), (122, 174), (123, 286), (129, 290), (130, 188), (131, 685), (137, 695), (163, 260), (164, 174), (165, 687), (170, 171), (172, 171), (177, 687), (178, 174), (179, 260), (205, 695), (211, 685), (212, 188), (213, 290), (219, 286), (220, 174), (221, 662), (227, 663), (261, 721)] [(114, 580), (115, 236), (116, 538), (121, 236), (122, 213), (128, 532), (164, 223), (165, 226), (170, 227), (172, 227), (177, 226), (178, 223), (213, 829), (214, 532), (220, 213), (221, 236), (226, 538), (227, 236), (228, 580)])) (.cut 3 (.e1 [(122, 174), (123, 290), (129, 294), (130, 190), (163, 252), (164, 178), (170, 166), (172, 166), (178, 178), (179, 252), (212, 190), (213, 294), (219, 290), (220, 174)] [(115, 234), (116, 531), (121, 243), (122, 209), (128, 526), (164, 221), (165, 223), (170, 232), (172, 232), (177, 223), (178, 221), (214, 526), (220, 209), (221, 243), (226, 531), (227, 234), (228, 594)]) .sb)))) (.e1 [(122, 172), (123, 278), (129, 296), (130, 202), (163, 263), (164, 175), (170, 161), (172, 161), (178, 175), (179, 263), (212, 202), (213, 296), (219, 278), (220, 172)] [(114, 576), (115, 240), (116, 551), (121, 244), (122, 206), (128, 525), (164, 210), (165, 235), (170, 228), (172, 228), (177, 235), (178, 210), (214, 525), (220, 206), (221, 244), (226, 551), (227, 240), (228, 576)]))) (.cut 1 (.redFull 178) (.cut 2 (.redFull 178) (.cut 4 (.cut 0 (.cut 1 (.cut 3 (.redFull 172) .sb) (.redFull 172)) (.redFull 172)) (.redFull 172)))))) (.cut 3 (.e1 [(122, 175), (123, 289), (129, 298), (130, 230), (163, 258), (164, 166), (170, 147), (172, 147), (178, 166), (179, 258), (212, 230), (213, 298), (219, 289), (220, 175)] [(115, 246), (121, 260), (122, 187), (164, 204), (165, 254), (170, 224), (172, 224), (177, 254), (178, 204), (220, 187), (221, 260), (227, 246)]) (.e1 [(122, 175), (123, 275), (129, 298), (130, 221), (163, 269), (164, 166), (170, 152), (172, 152), (178, 166), (179, 269), (212, 221), (213, 298), (219, 275), (220, 175)] [(114, 569), (115, 246), (116, 561), (121, 248), (122, 195), (128, 527), (164, 204), (165, 254), (170, 224), (172, 224), (177, 254), (178, 204), (214, 527), (220, 195), (221, 248), (226, 561), (227, 246), (228, 569)])))

theorem plan936_9_ok : plan936_9.checkAt
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 false) = true := by decide +kernel

def plan936_10 : Plan :=
  (.cut 1 (.cut 3 (.e1 [(122, 174), (123, 276), (129, 298), (130, 192), (163, 263), (164, 164), (170, 179), (172, 179), (178, 164), (179, 263), (212, 192), (213, 298), (219, 276), (220, 174)] [(115, 249), (121, 227), (122, 212), (128, 519), (164, 225), (165, 230), (170, 221), (172, 221), (177, 230), (178, 225), (214, 519), (220, 212), (221, 227), (227, 249), (228, 575)]) (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 267), (129, 296), (130, 191), (163, 274), (164, 162), (170, 189), (172, 189), (178, 162), (179, 274), (212, 191), (213, 296), (219, 267), (220, 168)] [(115, 255), (121, 221), (122, 222), (164, 224), (165, 229), (170, 213), (172, 213), (177, 229), (178, 224), (214, 523), (220, 222), (221, 221), (227, 255)]) (.redFull 178)) (.e1 [(122, 174), (123, 256), (129, 298), (130, 193), (163, 283), (164, 164), (170, 179), (172, 179), (178, 164), (179, 283), (212, 193), (213, 298), (219, 256), (220, 174)] [(115, 249), (121, 219), (122, 219), (164, 216), (165, 239), (170, 221), (172, 221), (177, 239), (178, 216), (220, 219), (221, 219), (227, 249)]))) (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 274), (129, 304), (130, 190), (163, 260), (164, 172), (170, 179), (172, 179), (178, 172), (179, 260), (212, 190), (213, 304), (219, 274), (220, 168)] [(115, 249), (116, 558), (121, 231), (122, 216), (128, 511), (164, 219), (165, 222), (170, 225), (172, 225), (177, 222), (178, 219), (214, 511), (220, 216), (221, 231), (226, 558), (227, 249)]) (.cut 1 (.e1 [(122, 174), (123, 274), (129, 303), (130, 189), (163, 260), (164, 169), (170, 177), (172, 177), (178, 169), (179, 260), (212, 189), (213, 303), (219, 274), (220, 174), (227, 639)] [(114, 581), (115, 246), (116, 557), (121, 227), (122, 213), (128, 512), (164, 223), (165, 226), (170, 227), (172, 227), (177, 226), (178, 223), (214, 512), (220, 213), (221, 227), (226, 557), (227, 246), (228, 581)]) (.cut 3 (.e1 [(122, 174), (123, 277), (129, 308), (130, 190), (163, 252), (164, 173), (170, 172), (172, 172), (178, 173), (179, 252), (212, 190), (213, 308), (219, 277), (220, 174)] [(115, 244), (116, 551), (121, 233), (122, 209), (128, 506), (164, 221), (165, 223), (170, 232), (172, 232), (177, 223), (178, 221), (214, 506), (220, 209), (221, 233), (226, 551), (227, 244)]) .sb))) (.e1 [(122, 172), (123, 265), (129, 307), (130, 200), (163, 266), (164, 171), (170, 167), (172, 167), (178, 171), (179, 266), (212, 200), (213, 307), (219, 265), (220, 172)] [(115, 248), (121, 234), (122, 209), (128, 509), (164, 210), (165, 235), (170, 228), (172, 228), (177, 235), (178, 210), (214, 509), (220, 209), (221, 234), (227, 248)])) (.cut 4 (.cut 0 (.cut 1 (.e1 [(122, 168), (123, 264), (129, 301), (130, 189), (163, 272), (164, 167), (170, 186), (172, 186), (178, 167), (179, 272), (212, 189), (213, 301), (219, 264), (220, 168)] [(114, 562), (115, 253), (121, 222), (122, 223), (128, 515), (164, 220), (165, 225), (170, 219), (172, 219), (177, 225), (178, 220), (214, 515), (220, 223), (221, 222), (226, 574), (227, 253), (228, 562)]) (.cut 4 .sb (.e1 [(115, 628), (122, 168), (123, 259), (129, 305), (130, 190), (163, 273), (164, 171), (170, 181), (172, 181), (178, 171), (179, 273), (212, 190), (213, 305), (219, 259), (220, 168), (227, 628)] [(114, 559), (115, 251), (116, 582), (121, 224), (122, 223), (128, 509), (164, 214), (165, 227), (170, 224), (172, 224), (177, 227), (178, 214), (214, 509), (220, 223), (221, 224), (226, 582), (227, 251), (228, 559)]))) (.cut 4 (.cut 3 .sb .sb) (.cut 2 (.e1 [(115, 632), (122, 174), (123, 256), (129, 313), (130, 187), (163, 268), (164, 170), (170, 178), (172, 178), (178, 170), (179, 268), (211, 673), (212, 187), (213, 313), (219, 256), (220, 174), (227, 632)] [(114, 566), (115, 249), (116, 587), (121, 220), (122, 218), (128, 498), (164, 217), (165, 228), (170, 231), (172, 231), (177, 228), (178, 217), (214, 498), (220, 218), (221, 220), (226, 587), (227, 249), (228, 566)]) .sb))) (.cut 0 (.e1 [(122, 168), (123, 253), (129, 304), (130, 192), (163, 280), (164, 172), (170, 177), (172, 177), (178, 172), (179, 280), (212, 192), (213, 304), (219, 253), (220, 168)] [(115, 249), (121, 224), (122, 224), (164, 210), (165, 232), (170, 225), (172, 225), (177, 232), (178, 210), (214, 511), (220, 224), (221, 224), (227, 249)]) (.e1 [(122, 174), (123, 252), (129, 307), (130, 189), (163, 279), (164, 172), (170, 174), (172, 174), (178, 172), (179, 279), (212, 189), (213, 307), (219, 252), (220, 174)] [(114, 549), (115, 245), (116, 595), (121, 221), (122, 221), (128, 507), (164, 211), (165, 234), (170, 231), (172, 231), (177, 234), (178, 211), (214, 507), (220, 221), (221, 221), (226, 595), (227, 245), (228, 549)])))))

theorem plan936_10_ok : plan936_10.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 false) 0 false) 2 false) = true := by decide +kernel

def plan936_11 : Plan :=
  (.cut 1 (.cut 3 (.cut 4 (.cut 0 (.e1 [(115, 648), (121, 681), (122, 168), (123, 278), (129, 282), (130, 188), (131, 715), (137, 691), (163, 276), (164, 169), (165, 684), (170, 183), (172, 183), (177, 684), (178, 169), (179, 276), (205, 691), (211, 715), (212, 188), (213, 282), (219, 278), (220, 168), (221, 681), (227, 648)] [(114, 555), (115, 242), (116, 551), (121, 228), (122, 224), (128, 543), (164, 224), (165, 227), (170, 215), (172, 215), (177, 227), (178, 224), (214, 543), (220, 224), (221, 228), (226, 551), (227, 242), (228, 555)]) (.cut 1 (.redFull 178) .sb)) (.e1 [(122, 174), (123, 268), (129, 285), (130, 193), (163, 283), (164, 169), (170, 172), (172, 172), (178, 169), (179, 283), (212, 193), (213, 285), (219, 268), (220, 174)] [(114, 543), (115, 238), (121, 229), (122, 218), (128, 540), (164, 216), (165, 239), (170, 221), (172, 221), (177, 239), (178, 216), (214, 540), (220, 218), (221, 229), (226, 566), (227, 238), (228, 543)])) (.cut 4 (.cut 0 (.cut 1 (.e1 [(122, 167), (123, 270), (129, 280), (130, 190), (163, 287), (164, 163), (170, 189), (172, 189), (178, 163), (179, 287), (212, 190), (213, 280), (219, 270), (220, 167)] [(114, 539), (115, 248), (121, 222), (122, 228), (128, 546), (164, 225), (165, 232), (170, 208), (172, 208), (177, 232), (178, 225), (214, 546), (220, 228), (221, 222), (227, 248), (228, 539)]) .sb) (.cut 1 (.redFull 178) .sb)) (.cut 0 (.e1 [(122, 168), (123, 258), (129, 282), (130, 190), (163, 297), (164, 169), (170, 182), (172, 182), (178, 169), (179, 297), (212, 190), (213, 282), (219, 258), (220, 168)] [(114, 523), (115, 243), (121, 222), (122, 231), (128, 543), (164, 215), (165, 237), (170, 215), (172, 215), (177, 237), (178, 215), (214, 543), (220, 231), (221, 222), (226, 584), (227, 243), (228, 523)]) (.cut 2 (.redFull 178) .sb)))) (.cut 4 (.cut 3 (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb (.cut 3 .sb .sb))) (.cut 0 (.cut 1 .sb (.cut 4 .sb .sb)) (.cut 1 (.cut 2 .sb .sb) (.cut 2 .sb .sb)))) (.cut 3 (.cut 0 (.e1 [(122, 168), (123, 265), (129, 291), (130, 192), (163, 280), (164, 177), (170, 170), (172, 170), (178, 177), (179, 280), (212, 192), (213, 291), (219, 265), (220, 168)] [(114, 547), (115, 238), (121, 233), (122, 223), (128, 531), (164, 210), (165, 232), (170, 225), (172, 225), (177, 232), (178, 210), (214, 531), (220, 223), (221, 233), (226, 571), (227, 238), (228, 547)]) (.cut 4 .sb (.redProjected 0 1))) (.cut 0 (.cut 1 (.e1 [(81, 681), (115, 648), (122, 168), (123, 256), (129, 288), (130, 191), (131, 706), (163, 293), (164, 172), (165, 664), (170, 178), (172, 178), (177, 664), (178, 172), (179, 293), (211, 706), (212, 191), (213, 288), (219, 256), (220, 168), (227, 648), (261, 681)] [(114, 528), (115, 243), (116, 587), (121, 224), (122, 229), (128, 535), (164, 211), (165, 236), (170, 219), (172, 219), (177, 236), (178, 211), (214, 535), (220, 229), (221, 224), (226, 587), (227, 243), (228, 528)]) (.redProjected 0 1)) (.cut 2 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.cut 1 (.redProjected 0 1) (.redProjected 0 1)))))))

theorem plan936_11_ok : plan936_11.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 false) 0 false) 2 true) = true := by decide +kernel

def plan936_n8 : Plan := .cut 2 plan936_10 plan936_11

theorem plan936_n8_ok : plan936_n8.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 false) 0 false) = true :=
  checkAt_cut 2 plan936_10 plan936_11
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 false) 0 false)
    (by decide +kernel) plan936_10_ok plan936_11_ok

def plan936_12 : Plan :=
  (.cut 2 (.redFull 178) (.cut 1 (.redFull 178) (.cut 3 (.cut 4 (.cut 0 (.cut 3 (.cut 1 .sb (.redProjected 0 1)) (.cut 1 .sb (.redProjected 0 1))) (.redFull 172)) (.redProjected 0 1)) (.cut 4 (.cut 0 (.cut 2 (.cut 1 (.redFull 178) (.redProjected 0 1)) (.cut 1 .sb (.redProjected 0 1))) (.redFull 178)) (.redProjected 0 1)))))

theorem plan936_12_ok : plan936_12.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 false) 0 true) = true := by decide +kernel

def plan936_n9 : Plan := .cut 0 plan936_n8 plan936_12

theorem plan936_n9_ok : plan936_n9.checkAt
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 false) = true :=
  checkAt_cut 0 plan936_n8 plan936_12
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 false)
    (by decide +kernel) plan936_n8_ok plan936_12_ok

def plan936_13 : Plan :=
  (.cut 0 (.cut 2 (.e1 [(122, 172), (123, 248), (129, 304), (130, 208), (163, 288), (164, 168), (170, 164), (172, 164), (178, 168), (179, 288), (212, 208), (213, 304), (219, 248), (220, 172)] [(115, 250), (121, 229), (122, 213), (164, 200), (165, 251), (170, 225), (172, 225), (177, 251), (178, 200), (214, 514), (220, 213), (221, 229), (227, 250)]) (.cut 4 (.cut 1 (.e1 [(122, 174), (123, 250), (129, 285), (130, 197), (163, 303), (164, 169), (170, 170), (172, 170), (178, 169), (179, 303), (212, 197), (213, 285), (219, 250), (220, 174)] [(115, 239), (121, 223), (122, 224), (164, 207), (165, 249), (170, 221), (172, 221), (177, 249), (178, 207), (220, 224), (221, 223), (227, 239)]) (.redProjected 0 1)) (.e1 [(122, 169), (123, 244), (129, 289), (130, 217), (163, 309), (164, 168), (170, 161), (172, 161), (178, 168), (179, 309), (212, 217), (213, 289), (219, 244), (220, 169)] [(115, 247), (121, 232), (122, 217), (164, 195), (165, 263), (170, 217), (172, 217), (177, 263), (178, 195), (220, 217), (221, 232), (227, 247)]))) (.cut 2 (.redFull 178) (.cut 4 (.cut 3 (.redFull 172) (.cut 1 (.redFull 178) (.redFull 172))) (.redFull 172))))

theorem plan936_13_ok : plan936_13.checkAt
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) 4 true) = true := by decide +kernel

def plan936_n10 : Plan := .cut 4 plan936_n9 plan936_13

theorem plan936_n10_ok : plan936_n10.checkAt
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true) = true :=
  checkAt_cut 4 plan936_n9 plan936_13
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) 3 true)
    (by decide +kernel) plan936_n9_ok plan936_13_ok

def plan936_n11 : Plan := .cut 3 plan936_9 plan936_n10

theorem plan936_n11_ok : plan936_n11.checkAt
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false) = true :=
  checkAt_cut 3 plan936_9 plan936_n10
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 false)
    (by decide +kernel) plan936_9_ok plan936_n10_ok

def plan936_14 : Plan :=
  (.cut 3 (.cut 4 (.cut 3 (.cut 1 (.cut 0 (.cut 4 (.cut 2 (.e1 [(122, 169), (123, 298), (129, 311), (130, 210), (163, 233), (164, 177), (170, 159), (172, 159), (178, 177), (179, 233), (212, 210), (213, 311), (219, 298), (220, 169)] [(115, 250), (121, 261), (122, 194), (164, 213), (165, 223), (170, 232), (172, 232), (177, 223), (178, 213), (220, 194), (221, 261), (227, 250)]) (.e1 [(122, 169), (123, 295), (129, 301), (130, 202), (163, 244), (164, 181), (170, 160), (172, 160), (178, 181), (179, 244), (212, 202), (213, 301), (219, 295), (220, 169)] [(115, 241), (116, 525), (121, 256), (122, 202), (128, 518), (164, 213), (165, 223), (170, 232), (172, 232), (177, 223), (178, 213), (214, 518), (220, 202), (221, 256), (226, 525), (227, 241)])) (.redProjected 0 1)) (.redFull 172)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.cut 2 (.e1 [(81, 755), (115, 637), (121, 643), (122, 171), (123, 284), (129, 315), (130, 200), (131, 670), (137, 726), (163, 242), (164, 177), (165, 698), (170, 165), (172, 165), (177, 698), (178, 177), (179, 242), (205, 726), (211, 670), (212, 200), (213, 315), (219, 284), (220, 171), (221, 643), (227, 637), (261, 755)] [(114, 616), (115, 248), (116, 542), (121, 247), (122, 202), (128, 498), (129, 776), (164, 214), (165, 222), (170, 235), (172, 235), (177, 222), (178, 214), (213, 776), (214, 498), (220, 202), (221, 247), (226, 542), (227, 248), (228, 616)]) (.cut 0 (.e1 [(81, 712), (115, 659), (121, 651), (122, 168), (123, 285), (129, 293), (130, 189), (131, 685), (137, 708), (163, 259), (164, 179), (170, 172), (172, 172), (177, 700), (178, 179), (179, 259), (205, 708), (211, 685), (212, 189), (213, 293), (219, 285), (220, 168), (221, 651), (227, 659), (261, 712)] [(114, 583), (115, 238), (116, 539), (121, 241), (122, 216), (128, 528), (164, 218), (165, 221), (170, 227), (172, 227), (177, 221), (178, 218), (214, 528), (220, 216), (221, 241), (226, 539), (227, 238), (228, 583)]) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)) (.cut 4 (.cut 2 (.cut 0 (.cut 4 (.cut 1 (.cut 3 (.cut 0 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.cut 3 (.cut 0 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1)))

theorem plan936_14_ok : plan936_14.checkAt
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) 1 true) = true := by decide +kernel

def plan936_n12 : Plan := .cut 1 plan936_n11 plan936_14

theorem plan936_n12_ok : plan936_n12.checkAt
    (((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false) = true :=
  checkAt_cut 1 plan936_n11 plan936_14
    (((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 false)
    (by decide +kernel) plan936_n11_ok plan936_14_ok

def plan936_15 : Plan :=
  (.cut 3 (.redFull 172) (.cut 4 (.cut 1 (.redFull 178) (.redFull 172)) (.redFull 172)))

theorem plan936_15_ok : plan936_15.checkAt
    (((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false).child true)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) 0 true) = true := by decide +kernel

def plan936_n13 : Plan := .cut 0 plan936_n12 plan936_15

theorem plan936_n13_ok : plan936_n13.checkAt
    ((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false) = true :=
  checkAt_cut 0 plan936_n12 plan936_15
    ((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child false)
    (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 false)
    (by decide +kernel) plan936_n12_ok plan936_15_ok

def plan936_16 : Plan :=
  (.cut 2 (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 304), (129, 270), (130, 194), (163, 264), (164, 175), (170, 172), (172, 172), (178, 175), (179, 264), (212, 194), (213, 270), (219, 304), (220, 168)] [(115, 232), (116, 512), (121, 249), (122, 215), (164, 224), (165, 227), (170, 215), (172, 215), (177, 227), (178, 224), (220, 215), (221, 249), (226, 512), (227, 232)]) (.e1 [(115, 684), (121, 638), (122, 174), (123, 303), (129, 273), (130, 191), (137, 687), (163, 262), (164, 176), (170, 168), (172, 168), (178, 176), (179, 262), (205, 687), (212, 191), (213, 273), (219, 303), (220, 174), (221, 638), (227, 684)] [(114, 577), (115, 228), (116, 513), (121, 246), (122, 212), (128, 560), (164, 226), (165, 229), (170, 221), (172, 221), (177, 229), (178, 226), (214, 560), (220, 212), (221, 246), (226, 513), (227, 228), (228, 577)])) (.e1 [(122, 172), (123, 299), (129, 273), (130, 211), (163, 268), (164, 170), (170, 158), (172, 158), (178, 170), (179, 268), (212, 211), (213, 273), (219, 299), (220, 172)] [(115, 234), (116, 521), (121, 256), (122, 202), (164, 215), (165, 244), (170, 215), (172, 215), (177, 244), (178, 215), (214, 563), (220, 202), (221, 256), (226, 521), (227, 234)])) (.cut 4 (.cut 0 (.cut 1 (.e1 [(122, 168), (123, 292), (129, 266), (130, 190), (163, 277), (164, 171), (170, 179), (172, 179), (178, 171), (179, 277), (212, 190), (213, 266), (219, 292), (220, 168)] [(114, 551), (115, 233), (116, 528), (121, 238), (122, 224), (164, 227), (165, 229), (170, 211), (172, 211), (177, 229), (178, 227), (214, 569), (220, 224), (221, 238), (226, 528), (227, 233), (228, 551)]) .sb) (.cut 1 .sb .sb)) (.e1 [(122, 172), (123, 283), (129, 272), (130, 197), (163, 282), (164, 174), (170, 166), (172, 166), (178, 174), (179, 282), (212, 197), (213, 272), (219, 283), (220, 172), (221, 649)] [(114, 545), (115, 230), (116, 543), (121, 242), (122, 216), (128, 561), (164, 216), (165, 240), (170, 218), (172, 218), (177, 240), (178, 216), (214, 561), (220, 216), (221, 242), (226, 543), (227, 230), (228, 545)]))) (.cut 3 (.cut 4 (.cut 0 (.e1 [(81, 699), (121, 628), (122, 168), (123, 305), (129, 258), (130, 191), (137, 693), (163, 274), (164, 180), (165, 683), (170, 171), (172, 171), (177, 683), (178, 180), (179, 274), (205, 693), (212, 191), (213, 258), (219, 305), (220, 168), (221, 628), (227, 692), (261, 699)] [(114, 557), (115, 224), (116, 510), (121, 251), (122, 222), (128, 584), (164, 224), (165, 229), (170, 213), (172, 213), (177, 229), (178, 224), (214, 584), (220, 222), (221, 251), (226, 510), (227, 224), (228, 557)]) (.cut 1 (.cut 2 (.e1 [(122, 174), (123, 304), (129, 262), (130, 189), (163, 270), (164, 176), (170, 170), (172, 170), (178, 176), (179, 270), (212, 189), (213, 262), (219, 304), (220, 174)] [(114, 562), (115, 223), (116, 511), (121, 245), (122, 217), (128, 577), (164, 228), (165, 231), (170, 217), (172, 217), (177, 231), (178, 228), (214, 577), (220, 217), (221, 245), (226, 511), (227, 223), (228, 562)]) (.e1 [(80, 938), (81, 699), (115, 707), (121, 640), (122, 174), (123, 304), (128, 922), (129, 256), (130, 186), (131, 711), (136, 952), (137, 681), (163, 277), (164, 179), (165, 677), (170, 170), (172, 170), (177, 677), (178, 179), (179, 277), (205, 681), (206, 952), (211, 711), (212, 186), (213, 256), (214, 922), (219, 304), (220, 174), (221, 640), (227, 707), (261, 699), (262, 938)] [(65, 889), (66, 844), (72, 910), (108, 863), (109, 844), (114, 553), (115, 218), (116, 510), (120, 896), (121, 246), (122, 222), (123, 825), (127, 926), (128, 587), (129, 875), (158, 893), (163, 852), (164, 228), (165, 231), (166, 860), (170, 217), (172, 217), (176, 860), (177, 231), (178, 228), (179, 852), (184, 893), (213, 875), (214, 587), (215, 926), (219, 825), (220, 222), (221, 246), (222, 896), (226, 510), (227, 218), (228, 553), (233, 844), (234, 863), (270, 910), (276, 844), (277, 889)])) (.cut 2 .sb .sb))) (.e1 [(122, 171), (123, 298), (129, 260), (130, 202), (163, 281), (164, 178), (170, 160), (172, 160), (178, 178), (179, 281), (212, 202), (213, 260), (219, 298), (220, 171)] [(115, 223), (116, 521), (121, 255), (122, 215), (164, 215), (165, 241), (170, 215), (172, 215), (177, 241), (178, 215), (220, 215), (221, 255), (226, 521), (227, 223), (228, 548)])) (.cut 4 (.cut 0 (.cut 1 (.cut 2 .sb .sb) .sb) (.cut 1 (.cut 2 .sb .sb) .sb)) (.cut 0 (.e1 [(122, 168), (123, 284), (129, 258), (130, 194), (163, 295), (164, 180), (170, 168), (172, 168), (178, 180), (179, 295), (212, 194), (213, 258), (219, 284), (220, 168)] [(114, 525), (115, 224), (116, 541), (121, 244), (122, 228), (164, 214), (165, 239), (170, 213), (172, 213), (177, 239), (178, 214), (220, 228), (221, 244), (226, 541), (227, 224), (228, 525)]) (.cut 1 (.e1 [(121, 652), (122, 174), (123, 284), (129, 257), (130, 192), (163, 295), (164, 177), (165, 648), (170, 166), (172, 166), (177, 648), (178, 177), (179, 295), (212, 192), (213, 257), (219, 284), (220, 174), (221, 652)] [(114, 524), (115, 220), (116, 540), (121, 241), (122, 225), (128, 586), (164, 218), (165, 242), (170, 216), (172, 216), (177, 242), (178, 218), (214, 586), (220, 225), (221, 241), (226, 540), (227, 220), (228, 524)]) .sb)))))

theorem plan936_16_ok : plan936_16.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 false) 1 false) = true := by decide +kernel

def plan936_17 : Plan :=
  (.cut 2 (.cut 3 (.cut 4 (.cut 0 (.e1 [(122, 168), (123, 301), (129, 278), (130, 194), (163, 259), (164, 181), (170, 167), (172, 167), (178, 181), (179, 259), (212, 194), (213, 278), (219, 301), (220, 168)] [(114, 584), (115, 231), (116, 516), (121, 253), (122, 214), (128, 551), (164, 219), (165, 224), (170, 223), (172, 223), (177, 224), (178, 219), (214, 551), (220, 214), (221, 253), (226, 516), (227, 231), (228, 584)]) (.cut 1 .sb (.e1 [(121, 627), (122, 171), (123, 301), (129, 279), (130, 193), (131, 693), (163, 258), (164, 181), (170, 165), (172, 165), (178, 181), (179, 258), (205, 702), (211, 693), (212, 193), (213, 279), (219, 301), (220, 171), (221, 627)] [(114, 585), (115, 229), (116, 516), (121, 251), (122, 212), (128, 550), (164, 220), (165, 225), (170, 225), (172, 225), (177, 225), (178, 220), (214, 550), (220, 212), (221, 251), (226, 516), (227, 229), (228, 585)]))) (.e1 [(122, 169), (123, 291), (129, 280), (130, 207), (163, 268), (164, 178), (170, 157), (172, 157), (178, 178), (179, 268), (212, 207), (213, 280), (219, 291), (220, 169)] [(115, 233), (121, 257), (122, 207), (164, 209), (165, 238), (170, 222), (172, 222), (177, 238), (178, 209), (220, 207), (221, 257), (227, 233)])) (.cut 4 (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb .sb)) (.cut 0 (.e1 [(122, 168), (123, 279), (129, 278), (130, 196), (163, 279), (164, 181), (170, 164), (172, 164), (178, 181), (179, 279), (212, 196), (213, 278), (219, 279), (220, 168)] [(114, 550), (115, 230), (116, 548), (121, 246), (122, 220), (164, 209), (165, 234), (170, 223), (172, 223), (177, 234), (178, 209), (220, 220), (221, 246), (226, 548), (227, 230), (228, 550)]) (.e1 [(122, 174), (123, 280), (129, 275), (130, 192), (163, 282), (164, 178), (170, 164), (172, 164), (178, 178), (179, 282), (212, 192), (213, 275), (219, 280), (220, 174)] [(114, 545), (115, 226), (121, 240), (122, 218), (128, 557), (164, 215), (165, 238), (170, 224), (172, 224), (177, 238), (178, 215), (214, 557), (220, 218), (221, 240), (227, 226), (228, 545)])))) (.cut 4 (.cut 3 (.cut 0 (.e1 [(121, 626), (122, 168), (123, 303), (129, 262), (130, 189), (163, 272), (164, 184), (170, 169), (172, 169), (178, 184), (179, 272), (212, 189), (213, 262), (219, 303), (220, 168), (221, 626)] [(114, 560), (115, 223), (116, 513), (121, 252), (122, 223), (128, 577), (164, 221), (165, 226), (170, 218), (172, 218), (177, 226), (178, 221), (214, 577), (220, 223), (221, 252), (226, 513), (227, 223), (228, 560)]) (.cut 1 (.cut 2 (.e1 [(121, 637), (122, 174), (123, 302), (129, 267), (130, 186), (137, 689), (163, 268), (164, 181), (165, 684), (170, 167), (172, 167), (177, 684), (178, 181), (179, 268), (205, 689), (212, 186), (213, 267), (219, 302), (220, 174), (221, 637)] [(114, 567), (115, 221), (116, 514), (121, 247), (122, 218), (128, 568), (164, 225), (165, 228), (170, 223), (172, 223), (177, 228), (178, 225), (214, 568), (220, 218), (221, 247), (226, 514), (227, 221), (228, 567)]) .sb) .sb)) (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb .sb))) (.cut 3 (.e1 [(122, 169), (123, 291), (129, 268), (130, 200), (163, 279), (164, 184), (170, 157), (172, 157), (178, 184), (179, 279), (212, 200), (213, 268), (219, 291), (220, 169)] [(115, 223), (116, 530), (121, 257), (122, 216), (164, 209), (165, 238), (170, 222), (172, 222), (177, 238), (178, 209), (220, 216), (221, 257), (226, 530), (227, 223)]) (.cut 0 (.e1 [(122, 168), (123, 281), (129, 262), (130, 192), (163, 293), (164, 184), (170, 166), (172, 166), (178, 184), (179, 293), (212, 192), (213, 262), (219, 281), (220, 168)] [(114, 528), (115, 222), (116, 544), (121, 245), (122, 229), (164, 212), (165, 236), (170, 218), (172, 218), (177, 236), (178, 212), (220, 229), (221, 245), (226, 544), (227, 222), (228, 528)]) (.cut 1 (.redProjected 0 1) (.redFull 172))))))

theorem plan936_17_ok : plan936_17.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 false) 1 true) = true := by decide +kernel

def plan936_n14 : Plan := .cut 1 plan936_16 plan936_17

theorem plan936_n14_ok : plan936_n14.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 false) = true :=
  checkAt_cut 1 plan936_16 plan936_17
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 false)
    (by decide +kernel) plan936_16_ok plan936_17_ok

def plan936_18 : Plan :=
  (.cut 2 (.cut 1 (.cut 3 (.cut 4 (.cut 0 (.e1 [(121, 640), (122, 176), (123, 302), (129, 273), (130, 190), (137, 686), (163, 261), (164, 176), (170, 167), (172, 167), (178, 176), (179, 261), (205, 686), (212, 190), (213, 273), (219, 302), (220, 176), (221, 640)] [(114, 578), (115, 227), (116, 514), (121, 246), (122, 211), (128, 558), (164, 226), (165, 229), (170, 223), (172, 223), (177, 229), (178, 226), (214, 558), (220, 211), (221, 246), (226, 514), (227, 227), (228, 578)]) (.redFull 172)) (.redFull 172)) (.cut 4 (.cut 0 (.cut 1 (.redFull 178) .sb) (.redFull 172)) (.redFull 172))) (.cut 3 (.redFull 172) (.cut 4 (.cut 0 (.cut 1 .sb (.redFull 172)) (.redFull 172)) (.redFull 172)))) (.cut 1 (.cut 3 (.cut 4 (.cut 0 (.cut 1 (.redFull 172) (.redFull 172)) (.redFull 172)) (.redFull 172)) (.cut 4 (.cut 0 (.cut 1 .sb .sb) (.redFull 172)) (.redFull 172))) (.cut 3 (.redFull 172) (.cut 4 (.cut 0 (.cut 1 .sb (.redFull 172)) (.redFull 172)) (.redFull 172)))))

theorem plan936_18_ok : plan936_18.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 true) = true := by decide +kernel

def plan936_n15 : Plan := .cut 0 plan936_n14 plan936_18

theorem plan936_n15_ok : plan936_n15.checkAt
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) = true :=
  checkAt_cut 0 plan936_n14 plan936_18
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false)
    (by decide +kernel) plan936_n14_ok plan936_18_ok

def plan936_19 : Plan :=
  (.cut 4 (.cut 2 (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb .sb)) (.cut 0 (.cut 1 (.cut 4 .sb .sb) .sb) (.cut 1 (.cut 3 .sb .sb) .sb))) (.cut 2 (.cut 0 (.e1 [(115, 673), (121, 673), (122, 168), (123, 270), (129, 270), (130, 190), (163, 297), (164, 175), (170, 175), (172, 175), (178, 175), (179, 297), (212, 190), (213, 270), (219, 270), (220, 168), (221, 673), (227, 673)] [(114, 522), (115, 232), (116, 563), (121, 232), (122, 230), (128, 563), (164, 215), (165, 237), (170, 215), (172, 215), (177, 237), (178, 215), (214, 563), (220, 230), (221, 232), (226, 563), (227, 232), (228, 522)]) (.cut 1 .sb .sb)) (.cut 0 (.cut 1 (.cut 4 .sb (.e1 [(122, 168), (123, 270), (129, 255), (130, 193), (163, 313), (164, 176), (170, 173), (172, 173), (178, 176), (179, 313), (212, 193), (213, 255), (219, 270), (220, 168)] [(114, 500), (115, 226), (121, 235), (122, 236), (164, 213), (165, 244), (170, 209), (172, 209), (177, 244), (178, 213), (220, 236), (221, 235), (227, 226), (228, 500)])) (.cut 4 .sb (.e1 [(122, 168), (123, 268), (129, 259), (130, 191), (163, 311), (164, 181), (170, 171), (172, 171), (178, 181), (179, 311), (212, 191), (213, 259), (219, 268), (220, 168)] [(114, 502), (115, 224), (121, 236), (122, 236), (164, 210), (165, 242), (170, 214), (172, 214), (177, 242), (178, 210), (220, 236), (221, 236), (226, 567), (227, 224), (228, 502)]))) (.cut 1 (.cut 3 .sb .sb) (.cut 4 .sb .sb)))))

theorem plan936_19_ok : plan936_19.checkAt
    (((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 false) 1 false) 3 false) = true := by decide +kernel

def plan936_20 : Plan :=
  (.cut 4 (.cut 2 (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb .sb)) (.cut 0 (.cut 1 (.cut 4 .sb .sb) (.cut 4 .sb .sb)) (.cut 1 (.cut 3 .sb .sb) (.cut 4 .sb .sb)))) (.cut 2 (.cut 0 (.cut 1 (.e1 [(81, 661), (122, 168), (123, 261), (129, 267), (130, 189), (163, 310), (164, 170), (165, 652), (170, 183), (172, 183), (177, 652), (178, 170), (179, 310), (212, 189), (213, 267), (219, 261), (220, 168), (261, 661)] [(114, 504), (115, 236), (116, 579), (121, 223), (122, 237), (128, 568), (164, 217), (165, 240), (170, 209), (172, 209), (177, 240), (178, 217), (214, 568), (220, 237), (221, 223), (226, 579), (227, 236), (228, 504)]) (.cut 4 .sb (.e1 [(122, 168), (123, 256), (129, 271), (130, 191), (163, 311), (164, 174), (170, 177), (172, 177), (178, 174), (179, 311), (212, 191), (213, 271), (219, 256), (220, 168)] [(114, 502), (115, 235), (121, 225), (122, 237), (128, 561), (164, 210), (165, 242), (170, 214), (172, 214), (177, 242), (178, 210), (214, 561), (220, 237), (221, 225), (227, 235), (228, 502)]))) (.cut 1 (.cut 3 .sb .sb) (.cut 3 .sb .sb))) (.cut 0 (.cut 1 (.cut 4 .sb (.e1 [(81, 646), (115, 684), (121, 688), (122, 167), (123, 260), (129, 256), (130, 190), (131, 739), (137, 727), (163, 324), (164, 175), (165, 641), (170, 179), (172, 179), (177, 641), (178, 175), (179, 324), (205, 727), (211, 739), (212, 190), (213, 256), (219, 260), (220, 167), (221, 688), (227, 684), (261, 646)] [(114, 485), (115, 229), (116, 581), (121, 227), (122, 243), (128, 588), (163, 789), (164, 213), (165, 245), (170, 208), (172, 208), (177, 245), (178, 213), (179, 789), (214, 588), (220, 243), (221, 227), (226, 581), (227, 229), (228, 485)])) (.cut 4 .sb .sb)) (.cut 1 (.cut 3 .sb (.cut 4 .sb .sb)) (.cut 4 .sb .sb)))))

theorem plan936_20_ok : plan936_20.checkAt
    (((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 false) 1 false) 3 true) = true := by decide +kernel

def plan936_n16 : Plan := .cut 3 plan936_19 plan936_20

theorem plan936_n16_ok : plan936_n16.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 false) 1 false) = true :=
  checkAt_cut 3 plan936_19 plan936_20
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 false) 1 false)
    (by decide +kernel) plan936_19_ok plan936_20_ok

def plan936_21 : Plan :=
  (.cut 4 (.cut 3 (.cut 2 (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb .sb)) (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb .sb))) (.cut 2 (.cut 0 (.cut 1 .sb .sb) (.cut 1 .sb .sb)) (.cut 0 (.cut 1 (.cut 4 .sb .sb) (.cut 4 .sb .sb)) (.cut 1 (.cut 4 .sb .sb) (.cut 4 .sb (.redProjected 0 1)))))) (.cut 3 (.cut 2 (.cut 0 (.cut 1 .sb (.redProjected 0 1)) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))) (.cut 0 (.cut 1 (.cut 4 .sb (.e1 [(122, 168), (123, 267), (129, 261), (130, 190), (163, 310), (164, 183), (170, 170), (172, 170), (178, 183), (179, 310), (212, 190), (213, 261), (219, 267), (220, 168)] [(114, 504), (115, 223), (121, 236), (122, 237), (164, 209), (165, 241), (170, 217), (172, 217), (177, 241), (178, 209), (214, 579), (220, 237), (221, 236), (227, 223), (228, 504)])) (.redProjected 0 1)) (.cut 1 (.redProjected 0 1) (.redProjected 0 1)))) (.cut 2 (.cut 0 (.cut 1 .sb (.redProjected 0 1)) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))) (.cut 0 (.cut 1 (.cut 4 .sb .sb) (.redProjected 0 1)) (.cut 1 (.redProjected 0 1) (.redProjected 0 1))))))

theorem plan936_21_ok : plan936_21.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 false) 1 true) = true := by decide +kernel

def plan936_n17 : Plan := .cut 1 plan936_n16 plan936_21

theorem plan936_n17_ok : plan936_n17.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 false) = true :=
  checkAt_cut 1 plan936_n16 plan936_21
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 false)
    (by decide +kernel) plan936_n16_ok plan936_21_ok

def plan936_22 : Plan :=
  (.cut 3 (.cut 2 (.cut 4 (.cut 0 (.cut 1 (.redFull 178) .sb) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) .sb) (.redFull 172))) (.cut 4 (.cut 0 (.cut 1 (.cut 3 .sb .sb) .sb) (.cut 1 (.cut 3 (.redFull 172) .sb) (.redFull 172))) (.cut 0 (.cut 1 (.cut 3 .sb .sb) (.cut 3 (.redFull 172) .sb)) (.redFull 172)))) (.cut 2 (.cut 4 (.cut 0 (.cut 1 (.redFull 178) .sb) (.redFull 178)) (.cut 0 (.cut 1 (.redFull 178) .sb) (.redFull 178))) (.cut 4 (.cut 0 (.cut 1 (.cut 3 .sb .sb) (.cut 3 .sb .sb)) (.cut 1 (.cut 3 .sb .sb) (.cut 3 .sb (.redFull 212)))) (.cut 0 (.cut 1 (.cut 3 .sb (.cut 4 .sb .sb)) (.cut 3 .sb .sb)) (.cut 1 (.cut 3 (.redFull 172) .sb) (.redFull 172))))))

theorem plan936_22_ok : plan936_22.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 true) 1 false) = true := by decide +kernel

def plan936_23 : Plan :=
  (.cut 2 (.cut 3 (.cut 4 (.cut 0 (.cut 1 .sb (.redProjected 0 1)) (.redFull 172)) (.redProjected 0 1)) (.cut 4 (.cut 0 (.cut 1 .sb (.redProjected 0 1)) (.cut 2 (.cut 1 (.redFull 178) (.redProjected 0 1)) (.cut 1 (.redProjected 0 1) (.redProjected 0 1)))) (.redProjected 0 1))) (.cut 4 (.cut 3 (.cut 0 (.cut 1 .sb (.redProjected 0 1)) (.redFull 172)) (.cut 0 (.cut 1 (.cut 4 .sb (.redProjected 0 1)) (.redProjected 0 1)) (.cut 1 (.redFull 212) (.redFull 212)))) (.redProjected 0 1)))

theorem plan936_23_ok : plan936_23.checkAt
    ((((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 true) 1 true) = true := by decide +kernel

def plan936_n18 : Plan := .cut 1 plan936_22 plan936_23

theorem plan936_n18_ok : plan936_n18.checkAt
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 true) = true :=
  checkAt_cut 1 plan936_22 plan936_23
    (((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) 0 true)
    (by decide +kernel) plan936_22_ok plan936_23_ok

def plan936_n19 : Plan := .cut 0 plan936_n17 plan936_n18

theorem plan936_n19_ok : plan936_n19.checkAt
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true) = true :=
  checkAt_cut 0 plan936_n17 plan936_n18
    ((((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 true)
    (by decide +kernel) plan936_n17_ok plan936_n18_ok

def plan936_n20 : Plan := .cut 3 plan936_n15 plan936_n19

theorem plan936_n20_ok : plan936_n20.checkAt
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) = true :=
  checkAt_cut 3 plan936_n15 plan936_n19
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false)
    (by decide +kernel) plan936_n15_ok plan936_n19_ok

def plan936_24 : Plan :=
  (.cut 3 (.cut 0 (.cut 1 (.cut 3 (.cut 4 (.cut 2 (.cut 0 (.e1 [(122, 168), (123, 298), (129, 280), (130, 189), (163, 259), (164, 185), (170, 166), (172, 166), (178, 185), (179, 259), (212, 189), (213, 280), (219, 298), (220, 168)] [(115, 228), (121, 251), (122, 217), (164, 218), (165, 221), (170, 227), (172, 227), (177, 221), (178, 218), (220, 217), (221, 251), (227, 228)]) (.redProjected 0 1)) (.cut 0 (.e1 [(122, 168), (123, 298), (129, 271), (130, 185), (163, 268), (164, 192), (170, 165), (172, 165), (178, 192), (179, 268), (212, 185), (213, 271), (219, 298), (220, 168)] [(115, 220), (116, 519), (121, 254), (122, 224), (128, 564), (164, 216), (165, 221), (170, 228), (172, 228), (177, 221), (178, 216), (214, 564), (220, 224), (221, 254), (226, 519), (227, 220)]) (.redProjected 0 1))) (.redProjected 0 1)) (.cut 4 (.cut 2 (.cut 0 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1))) (.redProjected 0 1))) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 4 (.cut 1 (.cut 2 (.cut 3 (.cut 0 (.cut 4 .sb (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1))) (.cut 3 (.cut 0 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)) (.cut 0 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)))) (.redProjected 0 1)) (.redProjected 0 1)) (.redProjected 0 1)))

theorem plan936_24_ok : plan936_24.checkAt
    (((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 true) = true := by decide +kernel

def plan936_n21 : Plan := .cut 1 plan936_n20 plan936_24

theorem plan936_n21_ok : plan936_n21.checkAt
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) = true :=
  checkAt_cut 1 plan936_n20 plan936_24
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 false)
    (by decide +kernel) plan936_n20_ok plan936_24_ok

def plan936_25 : Plan :=
  (.cut 1 (.cut 3 (.cut 0 (.cut 1 (.e1 [(81, 712), (121, 633), (122, 172), (123, 277), (129, 263), (130, 206), (163, 300), (164, 178), (165, 623), (170, 155), (172, 155), (177, 623), (178, 178), (179, 300), (212, 206), (213, 263), (219, 277), (220, 172), (221, 633), (261, 712)] [(114, 520), (115, 223), (116, 554), (121, 249), (122, 217), (128, 580), (164, 205), (165, 254), (170, 218), (172, 218), (177, 254), (178, 205), (214, 580), (220, 217), (221, 249), (226, 554), (227, 223), (228, 520)]) (.redProjected 0 1)) (.redFull 172)) (.cut 0 (.cut 1 (.cut 3 (.cut 4 (.e1 [(81, 679), (121, 666), (122, 172), (123, 263), (129, 263), (130, 196), (163, 313), (164, 178), (165, 628), (170, 164), (172, 164), (177, 628), (178, 178), (179, 313), (212, 196), (213, 263), (219, 263), (220, 172), (221, 666), (261, 679)] [(114, 500), (115, 224), (116, 576), (121, 235), (122, 229), (128, 577), (164, 207), (165, 251), (170, 218), (172, 218), (177, 251), (178, 207), (214, 577), (220, 229), (221, 235), (226, 576), (227, 224), (228, 500)]) (.e1 [(122, 169), (123, 259), (129, 260), (130, 212), (163, 324), (164, 176), (170, 157), (172, 157), (178, 176), (179, 324), (212, 212), (213, 260), (219, 259), (220, 169)] [(115, 228), (121, 244), (122, 224), (164, 198), (165, 265), (170, 212), (172, 212), (177, 265), (178, 198), (220, 224), (221, 244), (227, 228)])) (.cut 4 (.cut 2 (.e1 [(122, 172), (123, 250), (129, 272), (130, 194), (163, 316), (164, 174), (170, 171), (172, 171), (178, 174), (179, 316), (212, 194), (213, 272), (219, 250), (220, 172)] [(114, 495), (115, 232), (116, 598), (121, 225), (122, 232), (128, 560), (164, 207), (165, 251), (170, 218), (172, 218), (177, 251), (178, 207), (214, 560), (220, 232), (221, 225), (226, 598), (227, 232), (228, 495)]) (.cut 0 (.e1 [(122, 168), (123, 252), (129, 258), (130, 192), (163, 331), (164, 180), (170, 173), (172, 173), (178, 180), (179, 331), (212, 192), (213, 258), (219, 252), (220, 168)] [(114, 477), (115, 227), (121, 228), (122, 244), (164, 206), (165, 249), (170, 213), (172, 213), (177, 249), (178, 206), (220, 244), (221, 228), (226, 595), (227, 227), (228, 477)]) (.cut 1 (.e1 [(115, 700), (121, 695), (122, 174), (123, 252), (129, 257), (130, 190), (163, 331), (164, 177), (165, 623), (170, 172), (172, 172), (177, 623), (178, 177), (179, 331), (212, 190), (213, 257), (219, 252), (220, 174), (221, 695), (227, 700), (261, 652)] [(114, 476), (115, 223), (116, 594), (121, 225), (122, 241), (128, 585), (164, 209), (165, 253), (170, 216), (172, 216), (177, 253), (178, 209), (214, 585), (220, 241), (221, 225), (226, 594), (227, 223), (228, 476)]) (.redProjected 0 1)))) (.e1 [(122, 172), (123, 244), (129, 263), (130, 200), (163, 336), (164, 178), (170, 164), (172, 164), (178, 178), (179, 336), (212, 200), (213, 263), (219, 244), (220, 172)] [(115, 227), (121, 229), (122, 236), (164, 199), (165, 262), (170, 218), (172, 218), (177, 262), (178, 199), (220, 236), (221, 229), (227, 227), (228, 470)]))) (.redProjected 0 1)) (.cut 1 (.cut 3 (.redFull 172) (.cut 2 (.cut 4 (.cut 0 (.cut 1 (.redFull 178) (.redProjected 0 1)) (.redFull 172)) (.redFull 172)) (.cut 4 (.cut 0 (.cut 1 (.cut 3 (.redFull 172) (.cut 4 (.e1 [(81, 656), (82, 956), (115, 708), (121, 701), (122, 178), (123, 251), (124, 920), (129, 258), (130, 187), (131, 712), (137, 733), (163, 331), (164, 177), (165, 618), (170, 170), (172, 170), (177, 618), (178, 177), (179, 331), (205, 733), (211, 712), (212, 187), (213, 258), (214, 925), (218, 920), (219, 251), (220, 178), (221, 701), (226, 925), (227, 708), (260, 956), (261, 656)] [(65, 823), (66, 899), (72, 895), (108, 816), (109, 921), (114, 476), (115, 220), (116, 596), (120, 838), (121, 223), (122, 238), (123, 885), (127, 927), (128, 583), (129, 870), (158, 905), (163, 797), (164, 211), (165, 255), (166, 930), (170, 219), (172, 219), (176, 930), (177, 255), (178, 211), (179, 797), (184, 905), (213, 870), (214, 583), (215, 927), (219, 885), (220, 238), (221, 223), (222, 838), (226, 596), (227, 220), (228, 476), (233, 921), (234, 816), (270, 895), (276, 899), (277, 823)]) (.redFull 172))) (.redProjected 0 1)) (.redFull 172)) (.redFull 172)))) (.redFull 172)))) (.redProjected 0 1))

theorem plan936_25_ok : plan936_25.checkAt
    ((((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false).child true)
    (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) 4 true) = true := by decide +kernel

def plan936_n22 : Plan := .cut 4 plan936_n21 plan936_25

theorem plan936_n22_ok : plan936_n22.checkAt
    (((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false) = true :=
  checkAt_cut 4 plan936_n21 plan936_25
    (((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child false)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 false)
    (by decide +kernel) plan936_n21_ok plan936_25_ok

def plan936_26 : Plan :=
  (.cut 3 (.redFull 172) (.cut 4 (.cut 1 (.cut 2 (.cut 0 (.cut 3 (.redFull 172) (.cut 1 (.redFull 178) (.redFull 172))) (.redFull 172)) (.cut 0 (.cut 1 (.cut 3 (.redFull 172) (.cut 4 (.redFull 212) (.redFull 172))) (.redFull 172)) (.redFull 172))) (.redFull 172)) (.redFull 172)))

theorem plan936_26_ok : plan936_26.checkAt
    (((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true).child true)
    (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) 0 true) = true := by decide +kernel

def plan936_n23 : Plan := .cut 0 plan936_n22 plan936_26

theorem plan936_n23_ok : plan936_n23.checkAt
    ((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true) = true :=
  checkAt_cut 0 plan936_n22 plan936_26
    ((((rootAddress ![3, 2] ![2, 2, 0]).child true).child false).child true)
    (childBox (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) 2 true)
    (by decide +kernel) plan936_n22_ok plan936_26_ok

def plan936_n24 : Plan := .cut 2 plan936_n13 plan936_n23

theorem plan936_n24_ok : plan936_n24.checkAt
    (((rootAddress ![3, 2] ![2, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false) = true :=
  checkAt_cut 2 plan936_n13 plan936_n23
    (((rootAddress ![3, 2] ![2, 2, 0]).child true).child false)
    (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 false)
    (by decide +kernel) plan936_n13_ok plan936_n23_ok

def plan936_27 : Plan :=
  (.cut 2 (.cut 0 (.cut 4 (.cut 3 (.e1 [(122, 169), (123, 263), (130, 241), (164, 168), (170, 142), (172, 142), (178, 168), (179, 297), (212, 241), (219, 263), (220, 169)] [(115, 245), (121, 257), (122, 197), (164, 187), (165, 275), (170, 217), (172, 217), (177, 275), (178, 187), (220, 197), (221, 257), (227, 245)]) (.e1 [(122, 172), (123, 236), (129, 298), (130, 230), (163, 314), (164, 171), (170, 147), (172, 147), (178, 171), (179, 314), (212, 230), (213, 298), (219, 236), (220, 172)] [(115, 247), (121, 238), (122, 208), (164, 183), (165, 278), (170, 225), (172, 225), (177, 278), (178, 183), (220, 208), (221, 238), (227, 247), (228, 502)])) (.redProjected 0 1)) (.redFull 172)) (.cut 0 (.cut 4 (.cut 1 (.redProjected 0 1) (.redProjected 0 1)) (.redProjected 0 1)) (.redFull 172)))

theorem plan936_27_ok : plan936_27.checkAt
    (((rootAddress ![3, 2] ![2, 2, 0]).child true).child true)
    (childBox (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) 4 true) = true := by decide +kernel

def plan936_n25 : Plan := .cut 4 plan936_n24 plan936_27

theorem plan936_n25_ok : plan936_n25.checkAt
    ((rootAddress ![3, 2] ![2, 2, 0]).child true)
    (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true) = true :=
  checkAt_cut 4 plan936_n24 plan936_27
    ((rootAddress ![3, 2] ![2, 2, 0]).child true)
    (childBox (rootBox ![3, 2] ![2, 2, 0]) 1 true)
    (by decide +kernel) plan936_n24_ok plan936_27_ok

def plan936 : Plan := .cut 1 plan936_n7 plan936_n25

theorem plan936_ok : plan936.checkAt
    (rootAddress ![3, 2] ![2, 2, 0])
    (rootBox ![3, 2] ![2, 2, 0]) = true :=
  checkAt_cut 1 plan936_n7 plan936_n25
    (rootAddress ![3, 2] ![2, 2, 0])
    (rootBox ![3, 2] ![2, 2, 0])
    (by decide +kernel) plan936_n7_ok plan936_n25_ok

theorem root936 : rootCheck plan936 ![3, 2] ![2, 2, 0] = true := plan936_ok

def plan937 : Plan :=
  (.cut 0 (.cut 1 (.cut 4 (.e1 [(122, 175), (123, 237), (129, 261), (130, 295), (164, 147), (170, 142), (172, 142), (178, 147), (212, 295), (213, 261), (219, 237), (220, 175)] [(115, 260), (121, 250), (122, 193), (164, 181), (165, 363), (170, 195), (172, 195), (177, 363), (178, 181), (220, 193), (221, 250), (227, 260), (228, 426)]) (.e1 [(122, 175), (123, 229), (129, 261), (164, 147), (170, 134), (172, 134), (178, 147), (213, 261), (219, 229), (220, 175)] [(115, 273), (121, 264), (122, 185), (164, 172), (170, 195), (172, 195), (178, 172), (220, 185), (221, 264), (227, 273)])) (.redFull 172)) (.redFull 172))

theorem root937 : rootCheck plan937 ![3, 2] ![2, 2, 1] = true := by decide +kernel

def plan938 : Plan :=
  (.cut 1 (.e1 [(122, 181), (123, 242), (129, 253), (164, 147), (165, 268), (170, 136), (172, 136), (177, 268), (178, 147), (213, 253), (219, 242), (220, 181)] [(114, 332), (115, 293), (121, 298), (122, 167), (164, 183), (170, 196), (172, 196), (178, 183), (220, 167), (221, 298), (227, 293), (228, 332)]) (.redFull 172))

theorem root938 : rootCheck plan938 ![3, 2] ![2, 2, 2] = true := by decide +kernel

def plan939 : Plan :=
  (.cut 1 (.cut 0 (.cut 4 (.e1 [(122, 175), (123, 265), (129, 248), (164, 153), (165, 214), (170, 151), (172, 151), (177, 214), (178, 153), (213, 248), (219, 265), (220, 175)] [(114, 303), (122, 164), (163, 309), (164, 200), (170, 195), (172, 195), (178, 200), (179, 309), (220, 164), (221, 335), (227, 313), (228, 303)]) (.e1 [(122, 175), (123, 288), (129, 248), (164, 153), (165, 175), (170, 174), (172, 174), (177, 175), (178, 153), (213, 248), (219, 288), (220, 175)] [(114, 282), (115, 340), (122, 159), (163, 263), (164, 227), (170, 195), (172, 195), (178, 227), (179, 263), (220, 159), (221, 356), (227, 340), (228, 282)])) (.redFull 178)) (.cut 4 (.e1 [(122, 175), (123, 240), (129, 272), (164, 178), (165, 193), (170, 145), (172, 145), (177, 193), (178, 178), (213, 272), (219, 240), (220, 175)] [(114, 284), (122, 165), (163, 285), (164, 185), (170, 224), (172, 224), (178, 185), (179, 285), (220, 165), (227, 328), (228, 284)]) (.e1 [(122, 175), (123, 252), (129, 272), (164, 178), (165, 172), (170, 157), (172, 157), (177, 172), (178, 178), (213, 272), (219, 252), (220, 175)] [(114, 273), (115, 344), (121, 351), (122, 162), (163, 260), (164, 200), (170, 224), (172, 224), (178, 200), (179, 260), (220, 162), (221, 351), (227, 344), (228, 273)])))

theorem root939 : rootCheck plan939 ![3, 2] ![2, 2, 3] = true := by decide +kernel

end BccSharp.Coulomb.BravaisCover.TangentCover.Forest
