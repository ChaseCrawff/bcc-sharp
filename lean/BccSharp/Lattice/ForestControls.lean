import BccSharp.Lattice.ForestBase

set_option autoImplicit false

/-! Negative controls of the Lattice forest check: corrupted plans that `Plan.checkAt` must reject.
Each states its reason, the kernel
confirms the rejection. Generated. -/

noncomputable section

namespace BccSharp.Coulomb.BravaisCover.TangentCover.Forest.Controls
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.TangentCover
open BccSharp.Coulomb.BravaisCover.TangentCover.Forest

theorem control_e1Parent : Plan.checkAt (.e1 [(81, 638), (115, 684), (121, 748), (122, 179), (123, 235), (129, 276), (130, 177), (131, 703), (137, 720), (163, 331), (164, 172), (165, 639), (170, 184), (172, 184), (177, 639), (178, 172), (179, 331), (205, 720), (211, 703), (212, 177), (213, 276), (219, 235), (220, 179), (221, 748), (227, 684), (261, 638)] [(65, 817), (114, 476), (115, 231), (116, 627), (120, 801), (121, 204), (122, 247), (127, 863), (128, 554), (163, 822), (164, 214), (165, 247), (170, 224), (172, 224), (177, 247), (178, 214), (179, 822), (214, 554), (215, 863), (220, 247), (221, 204), (222, 801), (226, 627), (227, 231), (228, 476), (234, 836), (277, 817)])
    (((((((((((((rootAddress ![3, 2] ![2, 3, 0]).child true).child false).child true).child false).child false).child false).child false).child true).child false).child false).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 true) 1 false) 2 false) 3 true) 4 true) = false := by decide +kernel

theorem control_e1Drop : Plan.checkAt (.e1 [(81, 638), (115, 684), (121, 748), (122, 179), (123, 235), (129, 276), (130, 177), (131, 703), (137, 720), (163, 331), (165, 639), (170, 184), (172, 184), (177, 639), (178, 172), (179, 331), (205, 720), (211, 703), (212, 177), (213, 276), (219, 235), (220, 179), (221, 748), (227, 684), (261, 638)] [(65, 817), (114, 476), (115, 231), (116, 627), (120, 801), (121, 204), (122, 247), (127, 863), (128, 554), (163, 822), (164, 214), (165, 247), (170, 224), (172, 224), (177, 247), (178, 214), (179, 822), (214, 554), (215, 863), (220, 247), (221, 204), (222, 801), (226, 627), (227, 231), (228, 476), (234, 836), (277, 817)])
    ((((((((((((((rootAddress ![3, 2] ![2, 3, 0]).child true).child false).child true).child false).child false).child false).child false).child true).child false).child false).child true).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 true) 1 false) 2 false) 3 true) 4 true) 0 false) = false := by decide +kernel

theorem control_e1Shift : Plan.checkAt (.e1 [(81, 654), (115, 700), (121, 764), (122, 195), (123, 251), (129, 292), (130, 193), (131, 719), (137, 736), (163, 347), (164, 188), (165, 655), (170, 200), (172, 200), (177, 655), (178, 188), (179, 347), (205, 736), (211, 719), (212, 193), (213, 292), (219, 251), (220, 195), (221, 764), (227, 700), (261, 654)] [(65, 833), (114, 492), (115, 247), (116, 643), (120, 817), (121, 220), (122, 263), (127, 879), (128, 570), (163, 838), (164, 230), (165, 263), (170, 240), (172, 240), (177, 263), (178, 230), (179, 838), (214, 570), (215, 879), (220, 263), (221, 220), (222, 817), (226, 643), (227, 247), (228, 492), (234, 852), (277, 833)])
    ((((((((((((((rootAddress ![3, 2] ![2, 3, 0]).child true).child false).child true).child false).child false).child false).child false).child true).child false).child false).child true).child true).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![2, 3, 0]) 1 true) 4 false) 2 true) 0 false) 4 false) 1 false) 3 false) 0 true) 1 false) 2 false) 3 true) 4 true) 0 false) = false := by decide +kernel

theorem control_sbParent : Plan.checkAt .sb
    (((((((((((((((((rootAddress ![3, 2] ![3, 2, 0]).child false).child false).child false).child false).child true).child true).child false).child false).child true).child true).child true).child false).child true).child true).child true).child true)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![3, 2, 0]) 1 false) 4 false) 0 false) 2 false) 1 true) 3 true) 4 false) 0 false) 1 true) 3 true) 4 true) 2 false) 0 true) 1 true) 3 true) 4 true) = false := by decide +kernel

theorem control_sfAsSb : Plan.checkAt .sb
    ((((((((((((((((rootAddress ![3, 2] ![3, 3, 0]).child false).child false).child false).child true).child true).child false).child true).child true).child true).child true).child true).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![3, 3, 0]) 0 false) 1 false) 4 false) 2 true) 0 true) 1 false) 4 true) 3 true) 0 true) 1 true) 4 true) 0 false) 1 true) 2 false) 3 false) = false := by decide +kernel

theorem control_rWrong : Plan.checkAt (.redFull 172)
    ((((((((((((((((((rootAddress ![3, 2] ![3, 2, 0]).child false).child false).child false).child false).child true).child true).child false).child true).child true).child true).child false).child true).child true).child false).child true).child false).child false)
    (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (childBox (rootBox ![3, 2] ![3, 2, 0]) 1 false) 4 false) 0 false) 2 false) 1 true) 3 true) 4 false) 0 true) 1 true) 3 true) 2 false) 4 true) 0 true) 1 false) 3 true) 4 false) 2 false) = false := by decide +kernel

theorem control_fccCellE1 : Plan.checkAt (.e1 [(74, 883), (80, 904), (81, 577), (82, 850), (88, 915), (115, 786), (116, 885), (121, 764), (122, 188), (123, 212), (124, 837), (128, 885), (129, 233), (130, 182), (131, 732), (136, 923), (137, 796), (163, 419), (164, 194), (165, 570), (170, 172), (172, 172), (177, 570), (178, 194), (179, 419), (205, 796), (206, 923), (211, 732), (212, 182), (213, 233), (214, 885), (218, 837), (219, 212), (220, 188), (221, 764), (226, 885), (227, 786), (254, 915), (260, 850), (261, 577), (262, 904), (268, 883)] [(65, 748), (66, 959), (72, 939), (108, 731), (109, 957), (114, 384), (115, 207), (116, 676), (120, 790), (121, 211), (122, 276), (123, 987), (127, 967), (128, 630), (129, 937), (158, 927), (163, 764), (164, 200), (165, 281), (166, 1006), (170, 226), (172, 226), (176, 1006), (177, 281), (178, 200), (179, 764), (184, 927), (213, 937), (214, 630), (215, 967), (219, 987), (220, 276), (221, 211), (222, 790), (226, 676), (227, 207), (228, 384), (233, 957), (234, 731), (270, 939), (276, 959), (277, 748)])
    (rootAddress ![3, 2] ![3, 3, 0])
    (rootBox ![3, 2] ![3, 3, 0]) = false := by decide +kernel

theorem control_fccCellSf : Plan.checkAt .sf
    (rootAddress ![3, 2] ![3, 3, 0])
    (rootBox ![3, 2] ![3, 3, 0]) = false := by decide +kernel

end BccSharp.Coulomb.BravaisCover.TangentCover.Forest.Controls
