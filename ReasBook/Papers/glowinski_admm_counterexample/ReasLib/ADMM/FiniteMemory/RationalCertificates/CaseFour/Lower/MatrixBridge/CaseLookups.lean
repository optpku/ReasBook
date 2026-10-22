/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.Data

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge

@[simp] theorem lookup_case_gammaLower : caseData.gammaLower = (47 / 25) := rfl
@[simp] theorem lookup_case_gammaUpper : caseData.gammaUpper = (377 / 200) := rfl
@[simp] theorem lookup_case_omega : caseData.omega = (283707 / 500000000) := rfl
@[simp] theorem lookup_case_epsilon : caseData.epsilon = (1 / 50000) := rfl
@[simp] theorem lookup_case_zeta : caseData.zeta = (1 / 50000) := rfl
@[simp] theorem lookup_case_endpoint : endpointGamma caseData .lower = (47 / 25) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_0 : lagMinusValue caseData .F 0 = (41 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_1 : lagMinusValue caseData .F 1 = (1146317252 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_2 : lagMinusValue caseData .F 2 = (39 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_3 : lagMinusValue caseData .F 3 = (141594734 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_4 : lagMinusValue caseData .F 4 = (67 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_5 : lagMinusValue caseData .F 5 = (22702006 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_6 : lagMinusValue caseData .F 6 = (114 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_7 : lagMinusValue caseData .F 7 = (14787442 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_0 : lagPlusValue caseData .F 0 = (96 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_1 : lagPlusValue caseData .F 1 = (1083402730 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_2 : lagPlusValue caseData .F 2 = (161226617 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_3 : lagPlusValue caseData .F 3 = (28646686 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_4 : lagPlusValue caseData .F 4 = (25827187 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_5 : lagPlusValue caseData .F 5 = (32239 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_6 : lagPlusValue caseData .F 6 = (9866220 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_7 : lagPlusValue caseData .F 7 = (18875370 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_0 : packedMuValue caseData .F none 0 = (29435905 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_1 : packedMuValue caseData .F none 1 = (41790871 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_2 : packedMuValue caseData .F none 2 = (19345827 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_3 : packedMuValue caseData .F none 3 = (12316666 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_4 : packedMuValue caseData .F none 4 = (7163305 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_5 : packedMuValue caseData .F none 5 = (3264942 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_6 : packedMuValue caseData .F none 6 = (2733050 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_7 : packedMuValue caseData .F none 7 = (2316424 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_0 : packedMuValue caseData .F (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_F_1_1 : packedMuValue caseData .F (some 0) 1 = (258506318 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_2 : packedMuValue caseData .F (some 0) 2 = (28284670 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_3 : packedMuValue caseData .F (some 0) 3 = (8282814 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_4 : packedMuValue caseData .F (some 0) 4 = (7346803 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_5 : packedMuValue caseData .F (some 0) 5 = (2231146 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_6 : packedMuValue caseData .F (some 0) 6 = (2316783 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_7 : packedMuValue caseData .F (some 0) 7 = (1319290 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_0 : packedMuValue caseData .F (some 1) 0 = (183359378 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_1 : packedMuValue caseData .F (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_packed_F_2_2 : packedMuValue caseData .F (some 1) 2 = (185857970 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_3 : packedMuValue caseData .F (some 1) 3 = (41481194 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_4 : packedMuValue caseData .F (some 1) 4 = (17482186 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_5 : packedMuValue caseData .F (some 1) 5 = (6949018 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_6 : packedMuValue caseData .F (some 1) 6 = (3054029 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_7 : packedMuValue caseData .F (some 1) 7 = (5134342 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_0 : packedMuValue caseData .F (some 2) 0 = (99476008 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_1 : packedMuValue caseData .F (some 2) 1 = (21713506 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_2 : packedMuValue caseData .F (some 2) 2 = 0 := rfl
@[simp] theorem lookup_case_packed_F_3_3 : packedMuValue caseData .F (some 2) 3 = (21734036 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_4 : packedMuValue caseData .F (some 2) 4 = (26851158 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_5 : packedMuValue caseData .F (some 2) 5 = (4408902 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_6 : packedMuValue caseData .F (some 2) 6 = (2593142 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_7 : packedMuValue caseData .F (some 2) 7 = (1709154 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_0 : packedMuValue caseData .F (some 3) 0 = (19957831 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_1 : packedMuValue caseData .F (some 3) 1 = (135010903 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_2 : packedMuValue caseData .F (some 3) 2 = (3450112 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_3 : packedMuValue caseData .F (some 3) 3 = 0 := rfl
@[simp] theorem lookup_case_packed_F_4_4 : packedMuValue caseData .F (some 3) 4 = (3702403 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_5 : packedMuValue caseData .F (some 3) 5 = (13508803 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_6 : packedMuValue caseData .F (some 3) 6 = (7298518 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_7 : packedMuValue caseData .F (some 3) 7 = (2317552 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_0 : packedMuValue caseData .F (some 4) 0 = (11886793 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_1 : packedMuValue caseData .F (some 4) 1 = (6102910 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_2 : packedMuValue caseData .F (some 4) 2 = (13074810 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_3 : packedMuValue caseData .F (some 4) 3 = (1600753 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_4 : packedMuValue caseData .F (some 4) 4 = 0 := rfl
@[simp] theorem lookup_case_packed_F_5_5 : packedMuValue caseData .F (some 4) 5 = (1555613 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_6 : packedMuValue caseData .F (some 4) 6 = (10993327 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_7 : packedMuValue caseData .F (some 4) 7 = (2115736 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_0 : packedMuValue caseData .F (some 5) 0 = (8966716 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_1 : packedMuValue caseData .F (some 5) 1 = (16622485 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_2 : packedMuValue caseData .F (some 5) 2 = (1475718 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_3 : packedMuValue caseData .F (some 5) 3 = (10089504 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_4 : packedMuValue caseData .F (some 5) 4 = (709911 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_5 : packedMuValue caseData .F (some 5) 5 = 0 := rfl
@[simp] theorem lookup_case_packed_F_6_6 : packedMuValue caseData .F (some 5) 6 = (914465 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_7 : packedMuValue caseData .F (some 5) 7 = (3012491 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_0 : packedMuValue caseData .F (some 6) 0 = (2695082 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_1 : packedMuValue caseData .F (some 6) 1 = (2974350 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_2 : packedMuValue caseData .F (some 6) 2 = (2636849 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_3 : packedMuValue caseData .F (some 6) 3 = (731270 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_4 : packedMuValue caseData .F (some 6) 4 = (4074595 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_5 : packedMuValue caseData .F (some 6) 5 = (393903 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_6 : packedMuValue caseData .F (some 6) 6 = 0 := rfl
@[simp] theorem lookup_case_packed_F_7_7 : packedMuValue caseData .F (some 6) 7 = (426857 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_0 : packedMuValue caseData .F (some 7) 0 = (2575766 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_1 : packedMuValue caseData .F (some 7) 1 = (2322076 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_2 : packedMuValue caseData .F (some 7) 2 = (1279041 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_3 : packedMuValue caseData .F (some 7) 3 = (2142808 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_4 : packedMuValue caseData .F (some 7) 4 = (424170 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_5 : packedMuValue caseData .F (some 7) 5 = (3569687 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_6 : packedMuValue caseData .F (some 7) 6 = (295731 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_7 : packedMuValue caseData .F (some 7) 7 = 0 := rfl
@[simp] theorem lookup_case_lagMinusValue_J_0 : lagMinusValue caseData .J 0 = (13169 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_1 : lagMinusValue caseData .J 1 = (2540052618 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_2 : lagMinusValue caseData .J 2 = (348 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_3 : lagMinusValue caseData .J 3 = (224 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_4 : lagMinusValue caseData .J 4 = (131 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_5 : lagMinusValue caseData .J 5 = (103 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_6 : lagMinusValue caseData .J 6 = (90 / 10000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_7 : lagMinusValue caseData .J 7 = (96 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_0 : lagPlusValue caseData .J 0 = (4754293604 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_1 : lagPlusValue caseData .J 1 = (463 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_2 : lagPlusValue caseData .J 2 = (2036 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_3 : lagPlusValue caseData .J 3 = (466 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_4 : lagPlusValue caseData .J 4 = (11641 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_5 : lagPlusValue caseData .J 5 = (1903 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_6 : lagPlusValue caseData .J 6 = (46668416 / 10000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_7 : lagPlusValue caseData .J 7 = (1712 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_0 : packedMuValue caseData .J none 0 = (72755567 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_1 : packedMuValue caseData .J none 1 = (17197383 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_2 : packedMuValue caseData .J none 2 = (9594052 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_3 : packedMuValue caseData .J none 3 = (6894662 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_4 : packedMuValue caseData .J none 4 = (5285776 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_5 : packedMuValue caseData .J none 5 = (4257908 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_6 : packedMuValue caseData .J none 6 = (2970625 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_7 : packedMuValue caseData .J none 7 = (782528 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_0 : packedMuValue caseData .J (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_J_1_1 : packedMuValue caseData .J (some 0) 1 = (93755336 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_2 : packedMuValue caseData .J (some 0) 2 = (43893080 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_3 : packedMuValue caseData .J (some 0) 3 = (18645401 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_4 : packedMuValue caseData .J (some 0) 4 = (9381941 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_5 : packedMuValue caseData .J (some 0) 5 = (6851531 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_6 : packedMuValue caseData .J (some 0) 6 = (4270586 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_7 : packedMuValue caseData .J (some 0) 7 = (889883 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_0 : packedMuValue caseData .J (some 1) 0 = (2409863310 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_1 : packedMuValue caseData .J (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_packed_J_2_2 : packedMuValue caseData .J (some 1) 2 = (123753901 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_3 : packedMuValue caseData .J (some 1) 3 = (35015491 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_4 : packedMuValue caseData .J (some 1) 4 = (13526587 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_5 : packedMuValue caseData .J (some 1) 5 = (7809059 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_6 : packedMuValue caseData .J (some 1) 6 = (5802388 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_7 : packedMuValue caseData .J (some 1) 7 = (960592 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_0 : packedMuValue caseData .J (some 2) 0 = (14117083 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_1 : packedMuValue caseData .J (some 2) 1 = (17188544 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_2 : packedMuValue caseData .J (some 2) 2 = 0 := rfl
@[simp] theorem lookup_case_packed_J_3_3 : packedMuValue caseData .J (some 2) 3 = (61237089 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_4 : packedMuValue caseData .J (some 2) 4 = (32647446 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_5 : packedMuValue caseData .J (some 2) 5 = (13344619 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_6 : packedMuValue caseData .J (some 2) 6 = (6040881 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_7 : packedMuValue caseData .J (some 2) 7 = (1100816 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_0 : packedMuValue caseData .J (some 3) 0 = (6259387 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_1 : packedMuValue caseData .J (some 3) 1 = (7112635 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_2 : packedMuValue caseData .J (some 3) 2 = (12735220 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_3 : packedMuValue caseData .J (some 3) 3 = 0 := rfl
@[simp] theorem lookup_case_packed_J_4_4 : packedMuValue caseData .J (some 3) 4 = (27963709 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_5 : packedMuValue caseData .J (some 3) 5 = (18410862 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_6 : packedMuValue caseData .J (some 3) 6 = (9999797 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_7 : packedMuValue caseData .J (some 3) 7 = (1151709 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_0 : packedMuValue caseData .J (some 4) 0 = (2314622 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_1 : packedMuValue caseData .J (some 4) 1 = (2551774 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_2 : packedMuValue caseData .J (some 4) 2 = (4928690 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_3 : packedMuValue caseData .J (some 4) 3 = (6663458 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_4 : packedMuValue caseData .J (some 4) 4 = 0 := rfl
@[simp] theorem lookup_case_packed_J_5_5 : packedMuValue caseData .J (some 4) 5 = (18562552 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_6 : packedMuValue caseData .J (some 4) 6 = (12193966 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_7 : packedMuValue caseData .J (some 4) 7 = (1612829 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_0 : packedMuValue caseData .J (some 5) 0 = (1268532 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_1 : packedMuValue caseData .J (some 5) 1 = (1307076 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_2 : packedMuValue caseData .J (some 5) 2 = (1729225 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_3 : packedMuValue caseData .J (some 5) 3 = (3262485 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_4 : packedMuValue caseData .J (some 5) 4 = (4223954 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_5 : packedMuValue caseData .J (some 5) 5 = 0 := rfl
@[simp] theorem lookup_case_packed_J_6_6 : packedMuValue caseData .J (some 5) 6 = (14604877 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_7 : packedMuValue caseData .J (some 5) 7 = (1751954 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_0 : packedMuValue caseData .J (some 6) 0 = (808445 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_1 : packedMuValue caseData .J (some 6) 1 = (835887 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_2 : packedMuValue caseData .J (some 6) 2 = (1044690 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_3 : packedMuValue caseData .J (some 6) 3 = (1336162 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_4 : packedMuValue caseData .J (some 6) 4 = (3113434 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_5 : packedMuValue caseData .J (some 6) 5 = (3804238 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_6 : packedMuValue caseData .J (some 6) 6 = 0 := rfl
@[simp] theorem lookup_case_packed_J_7_7 : packedMuValue caseData .J (some 6) 7 = (2255898 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_0 : packedMuValue caseData .J (some 7) 0 = (445426 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_1 : packedMuValue caseData .J (some 7) 1 = (448951 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_2 : packedMuValue caseData .J (some 7) 2 = (522271 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_3 : packedMuValue caseData .J (some 7) 3 = (661626 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_4 : packedMuValue caseData .J (some 7) 4 = (887334 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_5 : packedMuValue caseData .J (some 7) 5 = (2651329 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_6 : packedMuValue caseData .J (some 7) 6 = (4573049 / 10000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_7 : packedMuValue caseData .J (some 7) 7 = 0 := rfl
@[simp] theorem lookup_case_A_0_0 : upperTriangleMatrix caseData .lower (0, 0) (0, 0) = (65206814050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_1 : upperTriangleMatrix caseData .lower (0, 0) (0, 1) = (2587478050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_2 : upperTriangleMatrix caseData .lower (0, 0) (1, 0) = (-30608114600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_3 : upperTriangleMatrix caseData .lower (0, 0) (1, 1) = (59542480030 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_4 : upperTriangleMatrix caseData .lower (0, 0) (2, 0) = (-55737942850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_5 : upperTriangleMatrix caseData .lower (0, 0) (2, 1) = (48361660984 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_6 : upperTriangleMatrix caseData .lower (0, 0) (3, 0) = (20311063200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_7 : upperTriangleMatrix caseData .lower (0, 0) (3, 1) = (965373650 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_8 : upperTriangleMatrix caseData .lower (0, 0) (4, 0) = (624052450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_9 : upperTriangleMatrix caseData .lower (0, 0) (4, 1) = (-7239502250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_10 : upperTriangleMatrix caseData .lower (0, 0) (5, 0) = (76883950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_11 : upperTriangleMatrix caseData .lower (0, 0) (5, 1) = (1527734000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_12 : upperTriangleMatrix caseData .lower (0, 0) (6, 0) = (804871500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_13 : upperTriangleMatrix caseData .lower (0, 0) (6, 1) = (-1138533000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_14 : upperTriangleMatrix caseData .lower (0, 0) (7, 0) = (188541450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_0_15 : upperTriangleMatrix caseData .lower (0, 0) (7, 1) = (1358457600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_0 : upperTriangleMatrix caseData .lower (0, 1) (0, 0) = (2587478050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_1 : upperTriangleMatrix caseData .lower (0, 1) (0, 1) = (66177729380 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_2 : upperTriangleMatrix caseData .lower (0, 1) (1, 0) = (-32170915485 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_3 : upperTriangleMatrix caseData .lower (0, 1) (1, 1) = (-3642879400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_4 : upperTriangleMatrix caseData .lower (0, 1) (2, 0) = (7968655050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_5 : upperTriangleMatrix caseData .lower (0, 1) (2, 1) = (-55578678200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_6 : upperTriangleMatrix caseData .lower (0, 1) (3, 0) = (21209639585 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_7 : upperTriangleMatrix caseData .lower (0, 1) (3, 1) = (740503800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_8 : upperTriangleMatrix caseData .lower (0, 1) (4, 0) = (189892150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_9 : upperTriangleMatrix caseData .lower (0, 1) (4, 1) = (-7479945700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_10 : upperTriangleMatrix caseData .lower (0, 1) (5, 0) = (112121850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_11 : upperTriangleMatrix caseData .lower (0, 1) (5, 1) = (1908296350 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_12 : upperTriangleMatrix caseData .lower (0, 1) (6, 0) = (75107600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_13 : upperTriangleMatrix caseData .lower (0, 1) (6, 1) = (-1264161450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_14 : upperTriangleMatrix caseData .lower (0, 1) (7, 0) = (305059550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_1_15 : upperTriangleMatrix caseData .lower (0, 1) (7, 1) = (211345700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_0 : upperTriangleMatrix caseData .lower (1, 0) (0, 0) = (-30608114600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_1 : upperTriangleMatrix caseData .lower (1, 0) (0, 1) = (-32170915485 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_2 : upperTriangleMatrix caseData .lower (1, 0) (1, 0) = (57688332400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_3 : upperTriangleMatrix caseData .lower (1, 0) (1, 1) = (-84909358135 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_4 : upperTriangleMatrix caseData .lower (1, 0) (2, 0) = (487927250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_5 : upperTriangleMatrix caseData .lower (1, 0) (2, 1) = (-15183773100 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_6 : upperTriangleMatrix caseData .lower (1, 0) (3, 0) = (-48413630400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_7 : upperTriangleMatrix caseData .lower (1, 0) (3, 1) = (18906003874 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_8 : upperTriangleMatrix caseData .lower (1, 0) (4, 0) = (19411299800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_9 : upperTriangleMatrix caseData .lower (1, 0) (4, 1) = (3429743700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_10 : upperTriangleMatrix caseData .lower (1, 0) (5, 0) = (727600750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_11 : upperTriangleMatrix caseData .lower (1, 0) (5, 1) = (-8709351350 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_12 : upperTriangleMatrix caseData .lower (1, 0) (6, 0) = (-522377900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_13 : upperTriangleMatrix caseData .lower (1, 0) (6, 1) = (1580395250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_14 : upperTriangleMatrix caseData .lower (1, 0) (7, 0) = (1337245350 / 500000000000) := rfl
@[simp] theorem lookup_case_A_2_15 : upperTriangleMatrix caseData .lower (1, 0) (7, 1) = (-1096653500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_0 : upperTriangleMatrix caseData .lower (1, 1) (0, 0) = (59542480030 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_1 : upperTriangleMatrix caseData .lower (1, 1) (0, 1) = (-3642879400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_2 : upperTriangleMatrix caseData .lower (1, 1) (1, 0) = (-84909358135 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_3 : upperTriangleMatrix caseData .lower (1, 1) (1, 1) = (6765683735 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_4 : upperTriangleMatrix caseData .lower (1, 1) (2, 0) = (26628205000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_5 : upperTriangleMatrix caseData .lower (1, 1) (2, 1) = (-1420471250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_6 : upperTriangleMatrix caseData .lower (1, 1) (3, 0) = (-12743516450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_7 : upperTriangleMatrix caseData .lower (1, 1) (3, 1) = (-2386185900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_8 : upperTriangleMatrix caseData .lower (1, 1) (4, 0) = (12529532155 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_9 : upperTriangleMatrix caseData .lower (1, 1) (4, 1) = (1553600750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_10 : upperTriangleMatrix caseData .lower (1, 1) (5, 0) = (53767900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_11 : upperTriangleMatrix caseData .lower (1, 1) (5, 1) = (-2384374200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_12 : upperTriangleMatrix caseData .lower (1, 1) (6, 0) = (-1114526000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_13 : upperTriangleMatrix caseData .lower (1, 1) (6, 1) = (1864217300 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_14 : upperTriangleMatrix caseData .lower (1, 1) (7, 0) = (349651300 / 500000000000) := rfl
@[simp] theorem lookup_case_A_3_15 : upperTriangleMatrix caseData .lower (1, 1) (7, 1) = (-446040750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_0 : upperTriangleMatrix caseData .lower (2, 0) (0, 0) = (-55737942850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_1 : upperTriangleMatrix caseData .lower (2, 0) (0, 1) = (7968655050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_2 : upperTriangleMatrix caseData .lower (2, 0) (1, 0) = (487927250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_3 : upperTriangleMatrix caseData .lower (2, 0) (1, 1) = (26628205000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_4 : upperTriangleMatrix caseData .lower (2, 0) (2, 0) = (103769583100 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_5 : upperTriangleMatrix caseData .lower (2, 0) (2, 1) = (-32780792409 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_6 : upperTriangleMatrix caseData .lower (2, 0) (3, 0) = (-23525389400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_7 : upperTriangleMatrix caseData .lower (2, 0) (3, 1) = (-17028426550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_8 : upperTriangleMatrix caseData .lower (2, 0) (4, 0) = (-41602514050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_9 : upperTriangleMatrix caseData .lower (2, 0) (4, 1) = (17613889314 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_10 : upperTriangleMatrix caseData .lower (2, 0) (5, 0) = (15947964200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_11 : upperTriangleMatrix caseData .lower (2, 0) (5, 1) = (2501215950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_12 : upperTriangleMatrix caseData .lower (2, 0) (6, 0) = (1865366700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_13 : upperTriangleMatrix caseData .lower (2, 0) (6, 1) = (-6695896050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_14 : upperTriangleMatrix caseData .lower (2, 0) (7, 0) = (-3477177800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_4_15 : upperTriangleMatrix caseData .lower (2, 0) (7, 1) = (839859700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_0 : upperTriangleMatrix caseData .lower (2, 1) (0, 0) = (48361660984 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_1 : upperTriangleMatrix caseData .lower (2, 1) (0, 1) = (-55578678200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_2 : upperTriangleMatrix caseData .lower (2, 1) (1, 0) = (-15183773100 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_3 : upperTriangleMatrix caseData .lower (2, 1) (1, 1) = (-1420471250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_4 : upperTriangleMatrix caseData .lower (2, 1) (2, 0) = (-32780792409 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_5 : upperTriangleMatrix caseData .lower (2, 1) (2, 1) = (59727290016 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_6 : upperTriangleMatrix caseData .lower (2, 1) (3, 0) = (701190850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_7 : upperTriangleMatrix caseData .lower (2, 1) (3, 1) = (-4087046750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_8 : upperTriangleMatrix caseData .lower (2, 1) (4, 0) = (-10699130700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_9 : upperTriangleMatrix caseData .lower (2, 1) (4, 1) = (-2255173600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_10 : upperTriangleMatrix caseData .lower (2, 1) (5, 0) = (10261253375 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_11 : upperTriangleMatrix caseData .lower (2, 1) (5, 1) = (1231553050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_12 : upperTriangleMatrix caseData .lower (2, 1) (6, 0) = (749392450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_13 : upperTriangleMatrix caseData .lower (2, 1) (6, 1) = (-1688171750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_14 : upperTriangleMatrix caseData .lower (2, 1) (7, 0) = (-1636444450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_5_15 : upperTriangleMatrix caseData .lower (2, 1) (7, 1) = (1339860000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_0 : upperTriangleMatrix caseData .lower (3, 0) (0, 0) = (20311063200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_1 : upperTriangleMatrix caseData .lower (3, 0) (0, 1) = (21209639585 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_2 : upperTriangleMatrix caseData .lower (3, 0) (1, 0) = (-48413630400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_3 : upperTriangleMatrix caseData .lower (3, 0) (1, 1) = (-12743516450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_4 : upperTriangleMatrix caseData .lower (3, 0) (2, 0) = (-23525389400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_5 : upperTriangleMatrix caseData .lower (3, 0) (2, 1) = (701190850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_6 : upperTriangleMatrix caseData .lower (3, 0) (3, 0) = (93421805450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_7 : upperTriangleMatrix caseData .lower (3, 0) (3, 1) = (272163900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_8 : upperTriangleMatrix caseData .lower (3, 0) (4, 0) = (-21484594150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_9 : upperTriangleMatrix caseData .lower (3, 0) (4, 1) = (-14492864450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_10 : upperTriangleMatrix caseData .lower (3, 0) (5, 0) = (-32669578500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_11 : upperTriangleMatrix caseData .lower (3, 0) (5, 1) = (14552540550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_12 : upperTriangleMatrix caseData .lower (3, 0) (6, 0) = (10707859000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_13 : upperTriangleMatrix caseData .lower (3, 0) (6, 1) = (892644200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_14 : upperTriangleMatrix caseData .lower (3, 0) (7, 0) = (3279035850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_6_15 : upperTriangleMatrix caseData .lower (3, 0) (7, 1) = (-4562502650 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_0 : upperTriangleMatrix caseData .lower (3, 1) (0, 0) = (965373650 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_1 : upperTriangleMatrix caseData .lower (3, 1) (0, 1) = (740503800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_2 : upperTriangleMatrix caseData .lower (3, 1) (1, 0) = (18906003874 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_3 : upperTriangleMatrix caseData .lower (3, 1) (1, 1) = (-2386185900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_4 : upperTriangleMatrix caseData .lower (3, 1) (2, 0) = (-17028426550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_5 : upperTriangleMatrix caseData .lower (3, 1) (2, 1) = (-4087046750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_6 : upperTriangleMatrix caseData .lower (3, 1) (3, 0) = (272163900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_7 : upperTriangleMatrix caseData .lower (3, 1) (3, 1) = (18781415416 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_8 : upperTriangleMatrix caseData .lower (3, 1) (4, 0) = (-2125348950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_9 : upperTriangleMatrix caseData .lower (3, 1) (4, 1) = (-3966687150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_10 : upperTriangleMatrix caseData .lower (3, 1) (5, 0) = (-8478767400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_11 : upperTriangleMatrix caseData .lower (3, 1) (5, 1) = (-1963747400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_12 : upperTriangleMatrix caseData .lower (3, 1) (6, 0) = (7061695826 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_13 : upperTriangleMatrix caseData .lower (3, 1) (6, 1) = (769115150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_14 : upperTriangleMatrix caseData .lower (3, 1) (7, 0) = (1678912200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_7_15 : upperTriangleMatrix caseData .lower (3, 1) (7, 1) = (-983873450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_0 : upperTriangleMatrix caseData .lower (4, 0) (0, 0) = (624052450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_1 : upperTriangleMatrix caseData .lower (4, 0) (0, 1) = (189892150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_2 : upperTriangleMatrix caseData .lower (4, 0) (1, 0) = (19411299800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_3 : upperTriangleMatrix caseData .lower (4, 0) (1, 1) = (12529532155 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_4 : upperTriangleMatrix caseData .lower (4, 0) (2, 0) = (-41602514050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_5 : upperTriangleMatrix caseData .lower (4, 0) (2, 1) = (-10699130700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_6 : upperTriangleMatrix caseData .lower (4, 0) (3, 0) = (-21484594150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_7 : upperTriangleMatrix caseData .lower (4, 0) (3, 1) = (-2125348950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_8 : upperTriangleMatrix caseData .lower (4, 0) (4, 0) = (75532456550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_9 : upperTriangleMatrix caseData .lower (4, 0) (4, 1) = (3020305550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_10 : upperTriangleMatrix caseData .lower (4, 0) (5, 0) = (-16412301000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_11 : upperTriangleMatrix caseData .lower (4, 0) (5, 1) = (-11149735650 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_12 : upperTriangleMatrix caseData .lower (4, 0) (6, 0) = (-21904482900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_13 : upperTriangleMatrix caseData .lower (4, 0) (6, 1) = (11985143300 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_14 : upperTriangleMatrix caseData .lower (4, 0) (7, 0) = (3780545050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_8_15 : upperTriangleMatrix caseData .lower (4, 0) (7, 1) = (-129349900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_0 : upperTriangleMatrix caseData .lower (4, 1) (0, 0) = (-7239502250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_1 : upperTriangleMatrix caseData .lower (4, 1) (0, 1) = (-7479945700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_2 : upperTriangleMatrix caseData .lower (4, 1) (1, 0) = (3429743700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_3 : upperTriangleMatrix caseData .lower (4, 1) (1, 1) = (1553600750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_4 : upperTriangleMatrix caseData .lower (4, 1) (2, 0) = (17613889314 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_5 : upperTriangleMatrix caseData .lower (4, 1) (2, 1) = (-2255173600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_6 : upperTriangleMatrix caseData .lower (4, 1) (3, 0) = (-14492864450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_7 : upperTriangleMatrix caseData .lower (4, 1) (3, 1) = (-3966687150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_8 : upperTriangleMatrix caseData .lower (4, 1) (4, 0) = (3020305550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_9 : upperTriangleMatrix caseData .lower (4, 1) (4, 1) = (11111442194 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_10 : upperTriangleMatrix caseData .lower (4, 1) (5, 0) = (-1021519450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_11 : upperTriangleMatrix caseData .lower (4, 1) (5, 1) = (-3224618700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_12 : upperTriangleMatrix caseData .lower (4, 1) (6, 0) = (-4957998400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_13 : upperTriangleMatrix caseData .lower (4, 1) (6, 1) = (-1378401500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_14 : upperTriangleMatrix caseData .lower (4, 1) (7, 0) = (2348956286 / 500000000000) := rfl
@[simp] theorem lookup_case_A_9_15 : upperTriangleMatrix caseData .lower (4, 1) (7, 1) = (428162100 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_0 : upperTriangleMatrix caseData .lower (5, 0) (0, 0) = (76883950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_1 : upperTriangleMatrix caseData .lower (5, 0) (0, 1) = (112121850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_2 : upperTriangleMatrix caseData .lower (5, 0) (1, 0) = (727600750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_3 : upperTriangleMatrix caseData .lower (5, 0) (1, 1) = (53767900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_4 : upperTriangleMatrix caseData .lower (5, 0) (2, 0) = (15947964200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_5 : upperTriangleMatrix caseData .lower (5, 0) (2, 1) = (10261253375 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_6 : upperTriangleMatrix caseData .lower (5, 0) (3, 0) = (-32669578500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_7 : upperTriangleMatrix caseData .lower (5, 0) (3, 1) = (-8478767400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_8 : upperTriangleMatrix caseData .lower (5, 0) (4, 0) = (-16412301000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_9 : upperTriangleMatrix caseData .lower (5, 0) (4, 1) = (-1021519450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_10 : upperTriangleMatrix caseData .lower (5, 0) (5, 0) = (54684731750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_11 : upperTriangleMatrix caseData .lower (5, 0) (5, 1) = (3324655950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_12 : upperTriangleMatrix caseData .lower (5, 0) (6, 0) = (-15464713850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_13 : upperTriangleMatrix caseData .lower (5, 0) (6, 1) = (-8216298800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_14 : upperTriangleMatrix caseData .lower (5, 0) (7, 0) = (-8547546100 / 500000000000) := rfl
@[simp] theorem lookup_case_A_10_15 : upperTriangleMatrix caseData .lower (5, 0) (7, 1) = (8649833050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_0 : upperTriangleMatrix caseData .lower (5, 1) (0, 0) = (1527734000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_1 : upperTriangleMatrix caseData .lower (5, 1) (0, 1) = (1908296350 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_2 : upperTriangleMatrix caseData .lower (5, 1) (1, 0) = (-8709351350 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_3 : upperTriangleMatrix caseData .lower (5, 1) (1, 1) = (-2384374200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_4 : upperTriangleMatrix caseData .lower (5, 1) (2, 0) = (2501215950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_5 : upperTriangleMatrix caseData .lower (5, 1) (2, 1) = (1231553050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_6 : upperTriangleMatrix caseData .lower (5, 1) (3, 0) = (14552540550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_7 : upperTriangleMatrix caseData .lower (5, 1) (3, 1) = (-1963747400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_8 : upperTriangleMatrix caseData .lower (5, 1) (4, 0) = (-11149735650 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_9 : upperTriangleMatrix caseData .lower (5, 1) (4, 1) = (-3224618700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_10 : upperTriangleMatrix caseData .lower (5, 1) (5, 0) = (3324655950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_11 : upperTriangleMatrix caseData .lower (5, 1) (5, 1) = (9138083090 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_12 : upperTriangleMatrix caseData .lower (5, 1) (6, 0) = (-1873606050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_13 : upperTriangleMatrix caseData .lower (5, 1) (6, 1) = (-2978417950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_14 : upperTriangleMatrix caseData .lower (5, 1) (7, 0) = (-2170408400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_11_15 : upperTriangleMatrix caseData .lower (5, 1) (7, 1) = (-836523700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_0 : upperTriangleMatrix caseData .lower (6, 0) (0, 0) = (804871500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_1 : upperTriangleMatrix caseData .lower (6, 0) (0, 1) = (75107600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_2 : upperTriangleMatrix caseData .lower (6, 0) (1, 0) = (-522377900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_3 : upperTriangleMatrix caseData .lower (6, 0) (1, 1) = (-1114526000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_4 : upperTriangleMatrix caseData .lower (6, 0) (2, 0) = (1865366700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_5 : upperTriangleMatrix caseData .lower (6, 0) (2, 1) = (749392450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_6 : upperTriangleMatrix caseData .lower (6, 0) (3, 0) = (10707859000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_7 : upperTriangleMatrix caseData .lower (6, 0) (3, 1) = (7061695826 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_8 : upperTriangleMatrix caseData .lower (6, 0) (4, 0) = (-21904482900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_9 : upperTriangleMatrix caseData .lower (6, 0) (4, 1) = (-4957998400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_10 : upperTriangleMatrix caseData .lower (6, 0) (5, 0) = (-15464713850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_11 : upperTriangleMatrix caseData .lower (6, 0) (5, 1) = (-1873606050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_12 : upperTriangleMatrix caseData .lower (6, 0) (6, 0) = (34926337000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_13 : upperTriangleMatrix caseData .lower (6, 0) (6, 1) = (2789421200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_14 : upperTriangleMatrix caseData .lower (6, 0) (7, 0) = (-3724291050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_12_15 : upperTriangleMatrix caseData .lower (6, 0) (7, 1) = (-4821283550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_0 : upperTriangleMatrix caseData .lower (6, 1) (0, 0) = (-1138533000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_1 : upperTriangleMatrix caseData .lower (6, 1) (0, 1) = (-1264161450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_2 : upperTriangleMatrix caseData .lower (6, 1) (1, 0) = (1580395250 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_3 : upperTriangleMatrix caseData .lower (6, 1) (1, 1) = (1864217300 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_4 : upperTriangleMatrix caseData .lower (6, 1) (2, 0) = (-6695896050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_5 : upperTriangleMatrix caseData .lower (6, 1) (2, 1) = (-1688171750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_6 : upperTriangleMatrix caseData .lower (6, 1) (3, 0) = (892644200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_7 : upperTriangleMatrix caseData .lower (6, 1) (3, 1) = (769115150 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_8 : upperTriangleMatrix caseData .lower (6, 1) (4, 0) = (11985143300 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_9 : upperTriangleMatrix caseData .lower (6, 1) (4, 1) = (-1378401500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_10 : upperTriangleMatrix caseData .lower (6, 1) (5, 0) = (-8216298800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_11 : upperTriangleMatrix caseData .lower (6, 1) (5, 1) = (-2978417950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_12 : upperTriangleMatrix caseData .lower (6, 1) (6, 0) = (2789421200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_13 : upperTriangleMatrix caseData .lower (6, 1) (6, 1) = (5749595801 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_14 : upperTriangleMatrix caseData .lower (6, 1) (7, 0) = (-684549050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_13_15 : upperTriangleMatrix caseData .lower (6, 1) (7, 1) = (-2153081950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_0 : upperTriangleMatrix caseData .lower (7, 0) (0, 0) = (188541450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_1 : upperTriangleMatrix caseData .lower (7, 0) (0, 1) = (305059550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_2 : upperTriangleMatrix caseData .lower (7, 0) (1, 0) = (1337245350 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_3 : upperTriangleMatrix caseData .lower (7, 0) (1, 1) = (349651300 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_4 : upperTriangleMatrix caseData .lower (7, 0) (2, 0) = (-3477177800 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_5 : upperTriangleMatrix caseData .lower (7, 0) (2, 1) = (-1636444450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_6 : upperTriangleMatrix caseData .lower (7, 0) (3, 0) = (3279035850 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_7 : upperTriangleMatrix caseData .lower (7, 0) (3, 1) = (1678912200 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_8 : upperTriangleMatrix caseData .lower (7, 0) (4, 0) = (3780545050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_9 : upperTriangleMatrix caseData .lower (7, 0) (4, 1) = (2348956286 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_10 : upperTriangleMatrix caseData .lower (7, 0) (5, 0) = (-8547546100 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_11 : upperTriangleMatrix caseData .lower (7, 0) (5, 1) = (-2170408400 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_12 : upperTriangleMatrix caseData .lower (7, 0) (6, 0) = (-3724291050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_13 : upperTriangleMatrix caseData .lower (7, 0) (6, 1) = (-684549050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_14 : upperTriangleMatrix caseData .lower (7, 0) (7, 0) = (9721595500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_14_15 : upperTriangleMatrix caseData .lower (7, 0) (7, 1) = (469227500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_0 : upperTriangleMatrix caseData .lower (7, 1) (0, 0) = (1358457600 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_1 : upperTriangleMatrix caseData .lower (7, 1) (0, 1) = (211345700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_2 : upperTriangleMatrix caseData .lower (7, 1) (1, 0) = (-1096653500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_3 : upperTriangleMatrix caseData .lower (7, 1) (1, 1) = (-446040750 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_4 : upperTriangleMatrix caseData .lower (7, 1) (2, 0) = (839859700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_5 : upperTriangleMatrix caseData .lower (7, 1) (2, 1) = (1339860000 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_6 : upperTriangleMatrix caseData .lower (7, 1) (3, 0) = (-4562502650 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_7 : upperTriangleMatrix caseData .lower (7, 1) (3, 1) = (-983873450 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_8 : upperTriangleMatrix caseData .lower (7, 1) (4, 0) = (-129349900 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_9 : upperTriangleMatrix caseData .lower (7, 1) (4, 1) = (428162100 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_10 : upperTriangleMatrix caseData .lower (7, 1) (5, 0) = (8649833050 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_11 : upperTriangleMatrix caseData .lower (7, 1) (5, 1) = (-836523700 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_12 : upperTriangleMatrix caseData .lower (7, 1) (6, 0) = (-4821283550 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_13 : upperTriangleMatrix caseData .lower (7, 1) (6, 1) = (-2153081950 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_14 : upperTriangleMatrix caseData .lower (7, 1) (7, 0) = (469227500 / 500000000000) := rfl
@[simp] theorem lookup_case_A_15_15 : upperTriangleMatrix caseData .lower (7, 1) (7, 1) = (4305483132 / 500000000000) := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
