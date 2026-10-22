/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Lower.MatrixBridge.Data

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge

@[simp] theorem lookup_case_gammaLower : caseData.gammaLower = (17 / 10) := rfl
@[simp] theorem lookup_case_gammaUpper : caseData.gammaUpper = (187 / 100) := rfl
@[simp] theorem lookup_case_omega : caseData.omega = (41353 / 5000000) := rfl
@[simp] theorem lookup_case_epsilon : caseData.epsilon = (1 / 10000) := rfl
@[simp] theorem lookup_case_zeta : caseData.zeta = (1 / 10000) := rfl
@[simp] theorem lookup_case_endpoint : endpointGamma caseData .lower = (17 / 10) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_0 : lagMinusValue caseData .F 0 = (0 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_1 : lagMinusValue caseData .F 1 = (11119415 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_2 : lagMinusValue caseData .F 2 = (0 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_3 : lagMinusValue caseData .F 3 = (1179711 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_4 : lagMinusValue caseData .F 4 = (0 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_5 : lagMinusValue caseData .F 5 = (567145 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_0 : lagPlusValue caseData .F 0 = (0 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_1 : lagPlusValue caseData .F 1 = (10385658 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_2 : lagPlusValue caseData .F 2 = (1351203 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_3 : lagPlusValue caseData .F 3 = (6 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_4 : lagPlusValue caseData .F 4 = (587810 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_5 : lagPlusValue caseData .F 5 = (454524 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_0_0 : packedMuValue caseData .F none 0 = (1166696 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_0_1 : packedMuValue caseData .F none 1 = (1469578 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_0_2 : packedMuValue caseData .F none 2 = (515588 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_0_3 : packedMuValue caseData .F none 3 = (263253 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_0_4 : packedMuValue caseData .F none 4 = (173915 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_0_5 : packedMuValue caseData .F none 5 = (67871 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_1_0 : packedMuValue caseData .F (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_F_1_1 : packedMuValue caseData .F (some 0) 1 = (2480238 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_1_2 : packedMuValue caseData .F (some 0) 2 = (462638 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_1_3 : packedMuValue caseData .F (some 0) 3 = (114990 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_1_4 : packedMuValue caseData .F (some 0) 4 = (158126 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_1_5 : packedMuValue caseData .F (some 0) 5 = (36459 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_2_0 : packedMuValue caseData .F (some 1) 0 = (2051439 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_2_1 : packedMuValue caseData .F (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_packed_F_2_2 : packedMuValue caseData .F (some 1) 2 = (1394126 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_2_3 : packedMuValue caseData .F (some 1) 3 = (609677 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_2_4 : packedMuValue caseData .F (some 1) 4 = (356593 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_2_5 : packedMuValue caseData .F (some 1) 5 = (121628 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_3_0 : packedMuValue caseData .F (some 2) 0 = (939438 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_3_1 : packedMuValue caseData .F (some 2) 1 = (238363 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_3_2 : packedMuValue caseData .F (some 2) 2 = 0 := rfl
@[simp] theorem lookup_case_packed_F_3_3 : packedMuValue caseData .F (some 2) 3 = (201305 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_3_4 : packedMuValue caseData .F (some 2) 4 = (335842 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_3_5 : packedMuValue caseData .F (some 2) 5 = (73210 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_4_0 : packedMuValue caseData .F (some 3) 0 = (214949 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_4_1 : packedMuValue caseData .F (some 3) 1 = (1357108 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_4_2 : packedMuValue caseData .F (some 3) 2 = (48985 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_4_3 : packedMuValue caseData .F (some 3) 3 = 0 := rfl
@[simp] theorem lookup_case_packed_F_4_4 : packedMuValue caseData .F (some 3) 4 = (69447 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_4_5 : packedMuValue caseData .F (some 3) 5 = (133500 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_5_0 : packedMuValue caseData .F (some 4) 0 = (146383 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_5_1 : packedMuValue caseData .F (some 4) 1 = (72615 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_5_2 : packedMuValue caseData .F (some 4) 2 = (248094 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_5_3 : packedMuValue caseData .F (some 4) 3 = (18991 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_5_4 : packedMuValue caseData .F (some 4) 4 = 0 := rfl
@[simp] theorem lookup_case_packed_F_5_5 : packedMuValue caseData .F (some 4) 5 = (16445 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_6_0 : packedMuValue caseData .F (some 5) 0 = (106919 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_6_1 : packedMuValue caseData .F (some 5) 1 = (165149 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_6_2 : packedMuValue caseData .F (some 5) 2 = (23055 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_6_3 : packedMuValue caseData .F (some 5) 3 = (148111 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_6_4 : packedMuValue caseData .F (some 5) 4 = (10943 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_6_5 : packedMuValue caseData .F (some 5) 5 = 0 := rfl
@[simp] theorem lookup_case_lagMinusValue_J_0 : lagMinusValue caseData .J 0 = (2603736 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_1 : lagMinusValue caseData .J 1 = (23912606 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_2 : lagMinusValue caseData .J 2 = (1 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_3 : lagMinusValue caseData .J 3 = (0 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_4 : lagMinusValue caseData .J 4 = (0 / 100000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_5 : lagMinusValue caseData .J 5 = (0 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_0 : lagPlusValue caseData .J 0 = (46268369 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_1 : lagPlusValue caseData .J 1 = (1 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_2 : lagPlusValue caseData .J 2 = (2 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_3 : lagPlusValue caseData .J 3 = (1 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_4 : lagPlusValue caseData .J 4 = (165343 / 100000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_5 : lagPlusValue caseData .J 5 = (577409 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_0_0 : packedMuValue caseData .J none 0 = (2619308 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_0_1 : packedMuValue caseData .J none 1 = (595937 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_0_2 : packedMuValue caseData .J none 2 = (245913 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_0_3 : packedMuValue caseData .J none 3 = (134964 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_0_4 : packedMuValue caseData .J none 4 = (102400 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_0_5 : packedMuValue caseData .J none 5 = (78919 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_1_0 : packedMuValue caseData .J (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_J_1_1 : packedMuValue caseData .J (some 0) 1 = (1372118 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_1_2 : packedMuValue caseData .J (some 0) 2 = (668847 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_1_3 : packedMuValue caseData .J (some 0) 3 = (247838 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_1_4 : packedMuValue caseData .J (some 0) 4 = (147529 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_1_5 : packedMuValue caseData .J (some 0) 5 = (112453 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_2_0 : packedMuValue caseData .J (some 1) 0 = (22186028 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_2_1 : packedMuValue caseData .J (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_packed_J_2_2 : packedMuValue caseData .J (some 1) 2 = (1435357 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_2_3 : packedMuValue caseData .J (some 1) 3 = (464203 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_2_4 : packedMuValue caseData .J (some 1) 4 = (230672 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_2_5 : packedMuValue caseData .J (some 1) 5 = (126632 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_3_0 : packedMuValue caseData .J (some 2) 0 = (255224 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_3_1 : packedMuValue caseData .J (some 2) 1 = (299843 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_3_2 : packedMuValue caseData .J (some 2) 2 = 0 := rfl
@[simp] theorem lookup_case_packed_J_3_3 : packedMuValue caseData .J (some 2) 3 = (647878 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_3_4 : packedMuValue caseData .J (some 2) 4 = (359011 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_3_5 : packedMuValue caseData .J (some 2) 5 = (165175 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_4_0 : packedMuValue caseData .J (some 3) 0 = (91667 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_4_1 : packedMuValue caseData .J (some 3) 1 = (101875 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_4_2 : packedMuValue caseData .J (some 3) 2 = (153361 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_4_3 : packedMuValue caseData .J (some 3) 3 = 0 := rfl
@[simp] theorem lookup_case_packed_J_4_4 : packedMuValue caseData .J (some 3) 4 = (336375 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_4_5 : packedMuValue caseData .J (some 3) 5 = (222755 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_5_0 : packedMuValue caseData .J (some 4) 0 = (46034 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_5_1 : packedMuValue caseData .J (some 4) 1 = (51560 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_5_2 : packedMuValue caseData .J (some 4) 2 = (102178 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_5_3 : packedMuValue caseData .J (some 4) 3 = (136665 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_5_4 : packedMuValue caseData .J (some 4) 4 = 0 := rfl
@[simp] theorem lookup_case_packed_J_5_5 : packedMuValue caseData .J (some 4) 5 = (134963 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_6_0 : packedMuValue caseData .J (some 5) 0 = (22901 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_6_1 : packedMuValue caseData .J (some 5) 1 = (23830 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_6_2 : packedMuValue caseData .J (some 5) 2 = (32714 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_6_3 : packedMuValue caseData .J (some 5) 3 = (86818 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_6_4 : packedMuValue caseData .J (some 5) 4 = (77509 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_6_5 : packedMuValue caseData .J (some 5) 5 = 0 := rfl
@[simp] theorem lookup_case_A_0_0 : upperTriangleMatrix caseData .lower (0, 0) (0, 0) = (254526940 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_1 : upperTriangleMatrix caseData .lower (0, 0) (0, 1) = (-1773300 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_2 : upperTriangleMatrix caseData .lower (0, 0) (1, 0) = (-115651940 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_3 : upperTriangleMatrix caseData .lower (0, 0) (1, 1) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_4 : upperTriangleMatrix caseData .lower (0, 0) (2, 0) = (-206761880 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_5 : upperTriangleMatrix caseData .lower (0, 0) (2, 1) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_6 : upperTriangleMatrix caseData .lower (0, 0) (3, 0) = (80119360 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_7 : upperTriangleMatrix caseData .lower (0, 0) (3, 1) = (22397480 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_8 : upperTriangleMatrix caseData .lower (0, 0) (4, 0) = (1429780 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_9 : upperTriangleMatrix caseData .lower (0, 0) (4, 1) = (-19274240 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_10 : upperTriangleMatrix caseData .lower (0, 0) (5, 0) = (-3390940 / 2000000000) := rfl
@[simp] theorem lookup_case_A_0_11 : upperTriangleMatrix caseData .lower (0, 0) (5, 1) = (8666820 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_0 : upperTriangleMatrix caseData .lower (0, 1) (0, 0) = (-1773300 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_1 : upperTriangleMatrix caseData .lower (0, 1) (0, 1) = (267615550 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_2 : upperTriangleMatrix caseData .lower (0, 1) (1, 0) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_3 : upperTriangleMatrix caseData .lower (0, 1) (1, 1) = (-34160840 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_4 : upperTriangleMatrix caseData .lower (0, 1) (2, 0) = (24380920 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_5 : upperTriangleMatrix caseData .lower (0, 1) (2, 1) = (-211999700 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_6 : upperTriangleMatrix caseData .lower (0, 1) (3, 0) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_7 : upperTriangleMatrix caseData .lower (0, 1) (3, 1) = (21758560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_8 : upperTriangleMatrix caseData .lower (0, 1) (4, 0) = (686560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_9 : upperTriangleMatrix caseData .lower (0, 1) (4, 1) = (-22396340 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_10 : upperTriangleMatrix caseData .lower (0, 1) (5, 0) = (-441240 / 2000000000) := rfl
@[simp] theorem lookup_case_A_1_11 : upperTriangleMatrix caseData .lower (0, 1) (5, 1) = (5546720 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_0 : upperTriangleMatrix caseData .lower (1, 0) (0, 0) = (-115651940 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_1 : upperTriangleMatrix caseData .lower (1, 0) (0, 1) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_2 : upperTriangleMatrix caseData .lower (1, 0) (1, 0) = (210460900 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_3 : upperTriangleMatrix caseData .lower (1, 0) (1, 1) = (-317196584 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_4 : upperTriangleMatrix caseData .lower (1, 0) (2, 0) = (6992160 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_5 : upperTriangleMatrix caseData .lower (1, 0) (2, 1) = (23016720 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_6 : upperTriangleMatrix caseData .lower (1, 0) (3, 0) = (-180910100 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_7 : upperTriangleMatrix caseData .lower (1, 0) (3, 1) = (-1359880 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_8 : upperTriangleMatrix caseData .lower (1, 0) (4, 0) = (77233260 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_9 : upperTriangleMatrix caseData .lower (1, 0) (4, 1) = (28317080 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_10 : upperTriangleMatrix caseData .lower (1, 0) (5, 0) = (1860140 / 2000000000) := rfl
@[simp] theorem lookup_case_A_2_11 : upperTriangleMatrix caseData .lower (1, 0) (5, 1) = (-23460860 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_0 : upperTriangleMatrix caseData .lower (1, 1) (0, 0) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_1 : upperTriangleMatrix caseData .lower (1, 1) (0, 1) = (-34160840 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_2 : upperTriangleMatrix caseData .lower (1, 1) (1, 0) = (-317196584 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_3 : upperTriangleMatrix caseData .lower (1, 1) (1, 1) = (62340840 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_4 : upperTriangleMatrix caseData .lower (1, 1) (2, 0) = (92380500 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_5 : upperTriangleMatrix caseData .lower (1, 1) (2, 1) = (-4948140 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_6 : upperTriangleMatrix caseData .lower (1, 1) (3, 0) = (-56995260 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_7 : upperTriangleMatrix caseData .lower (1, 1) (3, 1) = (-41273200 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_8 : upperTriangleMatrix caseData .lower (1, 1) (4, 0) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_9 : upperTriangleMatrix caseData .lower (1, 1) (4, 1) = (20695420 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_10 : upperTriangleMatrix caseData .lower (1, 1) (5, 0) = (2848580 / 2000000000) := rfl
@[simp] theorem lookup_case_A_3_11 : upperTriangleMatrix caseData .lower (1, 1) (5, 1) = (-6319160 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_0 : upperTriangleMatrix caseData .lower (2, 0) (0, 0) = (-206761880 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_1 : upperTriangleMatrix caseData .lower (2, 0) (0, 1) = (24380920 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_2 : upperTriangleMatrix caseData .lower (2, 0) (1, 0) = (6992160 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_3 : upperTriangleMatrix caseData .lower (2, 0) (1, 1) = (92380500 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_4 : upperTriangleMatrix caseData .lower (2, 0) (2, 0) = (367497500 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_5 : upperTriangleMatrix caseData .lower (2, 0) (2, 1) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_6 : upperTriangleMatrix caseData .lower (2, 0) (3, 0) = (-78694560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_7 : upperTriangleMatrix caseData .lower (2, 0) (3, 1) = (-4591880 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_8 : upperTriangleMatrix caseData .lower (2, 0) (4, 0) = (-150829580 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_9 : upperTriangleMatrix caseData .lower (2, 0) (4, 1) = (-1358280 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_10 : upperTriangleMatrix caseData .lower (2, 0) (5, 0) = (58242960 / 2000000000) := rfl
@[simp] theorem lookup_case_A_4_11 : upperTriangleMatrix caseData .lower (2, 0) (5, 1) = (18281840 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_0 : upperTriangleMatrix caseData .lower (2, 1) (0, 0) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_1 : upperTriangleMatrix caseData .lower (2, 1) (0, 1) = (-211999700 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_2 : upperTriangleMatrix caseData .lower (2, 1) (1, 0) = (23016720 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_3 : upperTriangleMatrix caseData .lower (2, 1) (1, 1) = (-4948140 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_4 : upperTriangleMatrix caseData .lower (2, 1) (2, 0) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_5 : upperTriangleMatrix caseData .lower (2, 1) (2, 1) = (253737411 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_6 : upperTriangleMatrix caseData .lower (2, 1) (3, 0) = (-2453280 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_7 : upperTriangleMatrix caseData .lower (2, 1) (3, 1) = (-30931720 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_8 : upperTriangleMatrix caseData .lower (2, 1) (4, 0) = (-43982680 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_9 : upperTriangleMatrix caseData .lower (2, 1) (4, 1) = (-32853620 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_10 : upperTriangleMatrix caseData .lower (2, 1) (5, 0) = (35386110 / 2000000000) := rfl
@[simp] theorem lookup_case_A_5_11 : upperTriangleMatrix caseData .lower (2, 1) (5, 1) = (15542660 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_0 : upperTriangleMatrix caseData .lower (3, 0) (0, 0) = (80119360 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_1 : upperTriangleMatrix caseData .lower (3, 0) (0, 1) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_2 : upperTriangleMatrix caseData .lower (3, 0) (1, 0) = (-180910100 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_3 : upperTriangleMatrix caseData .lower (3, 0) (1, 1) = (-56995260 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_4 : upperTriangleMatrix caseData .lower (3, 0) (2, 0) = (-78694560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_5 : upperTriangleMatrix caseData .lower (3, 0) (2, 1) = (-2453280 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_6 : upperTriangleMatrix caseData .lower (3, 0) (3, 0) = (319380380 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_7 : upperTriangleMatrix caseData .lower (3, 0) (3, 1) = (1200900 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_8 : upperTriangleMatrix caseData .lower (3, 0) (4, 0) = (-73531000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_9 : upperTriangleMatrix caseData .lower (3, 0) (4, 1) = (-872000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_10 : upperTriangleMatrix caseData .lower (3, 0) (5, 0) = (-107123120 / 2000000000) := rfl
@[simp] theorem lookup_case_A_6_11 : upperTriangleMatrix caseData .lower (3, 0) (5, 1) = (-3171700 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_0 : upperTriangleMatrix caseData .lower (3, 1) (0, 0) = (22397480 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_1 : upperTriangleMatrix caseData .lower (3, 1) (0, 1) = (21758560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_2 : upperTriangleMatrix caseData .lower (3, 1) (1, 0) = (-1359880 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_3 : upperTriangleMatrix caseData .lower (3, 1) (1, 1) = (-41273200 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_4 : upperTriangleMatrix caseData .lower (3, 1) (2, 0) = (-4591880 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_5 : upperTriangleMatrix caseData .lower (3, 1) (2, 1) = (-30931720 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_6 : upperTriangleMatrix caseData .lower (3, 1) (3, 0) = (1200900 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_7 : upperTriangleMatrix caseData .lower (3, 1) (3, 1) = (116489531 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_8 : upperTriangleMatrix caseData .lower (3, 1) (4, 0) = (-8015640 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_9 : upperTriangleMatrix caseData .lower (3, 1) (4, 1) = (-28196560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_10 : upperTriangleMatrix caseData .lower (3, 1) (5, 0) = (-31569320 / 2000000000) := rfl
@[simp] theorem lookup_case_A_7_11 : upperTriangleMatrix caseData .lower (3, 1) (5, 1) = (-24046680 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_0 : upperTriangleMatrix caseData .lower (4, 0) (0, 0) = (1429780 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_1 : upperTriangleMatrix caseData .lower (4, 0) (0, 1) = (686560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_2 : upperTriangleMatrix caseData .lower (4, 0) (1, 0) = (77233260 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_3 : upperTriangleMatrix caseData .lower (4, 0) (1, 1) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_4 : upperTriangleMatrix caseData .lower (4, 0) (2, 0) = (-150829580 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_5 : upperTriangleMatrix caseData .lower (4, 0) (2, 1) = (-43982680 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_6 : upperTriangleMatrix caseData .lower (4, 0) (3, 0) = (-73531000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_7 : upperTriangleMatrix caseData .lower (4, 0) (3, 1) = (-8015640 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_8 : upperTriangleMatrix caseData .lower (4, 0) (4, 0) = (232208080 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_9 : upperTriangleMatrix caseData .lower (4, 0) (4, 1) = (-5733040 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_10 : upperTriangleMatrix caseData .lower (4, 0) (5, 0) = (-41518000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_8_11 : upperTriangleMatrix caseData .lower (4, 0) (5, 1) = (5807920 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_0 : upperTriangleMatrix caseData .lower (4, 1) (0, 0) = (-19274240 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_1 : upperTriangleMatrix caseData .lower (4, 1) (0, 1) = (-22396340 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_2 : upperTriangleMatrix caseData .lower (4, 1) (1, 0) = (28317080 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_3 : upperTriangleMatrix caseData .lower (4, 1) (1, 1) = (20695420 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_4 : upperTriangleMatrix caseData .lower (4, 1) (2, 0) = (-1358280 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_5 : upperTriangleMatrix caseData .lower (4, 1) (2, 1) = (-32853620 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_6 : upperTriangleMatrix caseData .lower (4, 1) (3, 0) = (-872000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_7 : upperTriangleMatrix caseData .lower (4, 1) (3, 1) = (-28196560 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_8 : upperTriangleMatrix caseData .lower (4, 1) (4, 0) = (-5733040 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_9 : upperTriangleMatrix caseData .lower (4, 1) (4, 1) = (70325555 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_10 : upperTriangleMatrix caseData .lower (4, 1) (5, 0) = (4798740 / 2000000000) := rfl
@[simp] theorem lookup_case_A_9_11 : upperTriangleMatrix caseData .lower (4, 1) (5, 1) = (-19629160 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_0 : upperTriangleMatrix caseData .lower (5, 0) (0, 0) = (-3390940 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_1 : upperTriangleMatrix caseData .lower (5, 0) (0, 1) = (-441240 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_2 : upperTriangleMatrix caseData .lower (5, 0) (1, 0) = (1860140 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_3 : upperTriangleMatrix caseData .lower (5, 0) (1, 1) = (2848580 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_4 : upperTriangleMatrix caseData .lower (5, 0) (2, 0) = (58242960 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_5 : upperTriangleMatrix caseData .lower (5, 0) (2, 1) = (35386110 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_6 : upperTriangleMatrix caseData .lower (5, 0) (3, 0) = (-107123120 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_7 : upperTriangleMatrix caseData .lower (5, 0) (3, 1) = (-31569320 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_8 : upperTriangleMatrix caseData .lower (5, 0) (4, 0) = (-41518000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_9 : upperTriangleMatrix caseData .lower (5, 0) (4, 1) = (4798740 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_10 : upperTriangleMatrix caseData .lower (5, 0) (5, 0) = (153689580 / 2000000000) := rfl
@[simp] theorem lookup_case_A_10_11 : upperTriangleMatrix caseData .lower (5, 0) (5, 1) = (-2006000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_0 : upperTriangleMatrix caseData .lower (5, 1) (0, 0) = (8666820 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_1 : upperTriangleMatrix caseData .lower (5, 1) (0, 1) = (5546720 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_2 : upperTriangleMatrix caseData .lower (5, 1) (1, 0) = (-23460860 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_3 : upperTriangleMatrix caseData .lower (5, 1) (1, 1) = (-6319160 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_4 : upperTriangleMatrix caseData .lower (5, 1) (2, 0) = (18281840 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_5 : upperTriangleMatrix caseData .lower (5, 1) (2, 1) = (15542660 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_6 : upperTriangleMatrix caseData .lower (5, 1) (3, 0) = (-3171700 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_7 : upperTriangleMatrix caseData .lower (5, 1) (3, 1) = (-24046680 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_8 : upperTriangleMatrix caseData .lower (5, 1) (4, 0) = (5807920 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_9 : upperTriangleMatrix caseData .lower (5, 1) (4, 1) = (-19629160 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_10 : upperTriangleMatrix caseData .lower (5, 1) (5, 0) = (-2006000 / 2000000000) := rfl
@[simp] theorem lookup_case_A_11_11 : upperTriangleMatrix caseData .lower (5, 1) (5, 1) = (59936690 / 2000000000) := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge
