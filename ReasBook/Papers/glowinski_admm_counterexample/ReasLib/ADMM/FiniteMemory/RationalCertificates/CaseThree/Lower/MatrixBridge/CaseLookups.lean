/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.Data

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge

@[simp] theorem lookup_case_gammaLower : caseData.gammaLower = (187 / 100) := rfl
@[simp] theorem lookup_case_gammaUpper : caseData.gammaUpper = (47 / 25) := rfl
@[simp] theorem lookup_case_omega : caseData.omega = (2907189 / 1000000000) := rfl
@[simp] theorem lookup_case_epsilon : caseData.epsilon = (1 / 5000) := rfl
@[simp] theorem lookup_case_zeta : caseData.zeta = (1 / 5000) := rfl
@[simp] theorem lookup_case_endpoint : endpointGamma caseData .lower = (187 / 100) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_0 : lagMinusValue caseData .F 0 = (96 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_1 : lagMinusValue caseData .F 1 = (3245626857 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_2 : lagMinusValue caseData .F 2 = (93 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_3 : lagMinusValue caseData .F 3 = (530203728 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_4 : lagMinusValue caseData .F 4 = (165 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_5 : lagMinusValue caseData .F 5 = (49669905 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_6 : lagMinusValue caseData .F 6 = (306 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_7 : lagMinusValue caseData .F 7 = (42995103 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_0 : lagPlusValue caseData .F 0 = (225 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_1 : lagPlusValue caseData .F 1 = (3101627889 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_2 : lagPlusValue caseData .F 2 = (462267435 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_3 : lagPlusValue caseData .F 3 = (149196462 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_4 : lagPlusValue caseData .F 4 = (89994132 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_5 : lagPlusValue caseData .F 5 = (11529 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_6 : lagPlusValue caseData .F 6 = (27642477 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_7 : lagPlusValue caseData .F 7 = (54885078 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_0 : packedMuValue caseData .F none 0 = (230305839 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_1 : packedMuValue caseData .F none 1 = (306966930 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_2 : packedMuValue caseData .F none 2 = (121284624 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_3 : packedMuValue caseData .F none 3 = (62426331 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_4 : packedMuValue caseData .F none 4 = (30303063 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_5 : packedMuValue caseData .F none 5 = (11748927 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_6 : packedMuValue caseData .F none 6 = (9065097 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_0_7 : packedMuValue caseData .F none 7 = (9060918 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_0 : packedMuValue caseData .F (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_F_1_1 : packedMuValue caseData .F (some 0) 1 = (695081670 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_2 : packedMuValue caseData .F (some 0) 2 = (116261280 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_3 : packedMuValue caseData .F (some 0) 3 = (27613503 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_4 : packedMuValue caseData .F (some 0) 4 = (22239273 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_5 : packedMuValue caseData .F (some 0) 5 = (6479907 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_6 : packedMuValue caseData .F (some 0) 6 = (6887172 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_1_7 : packedMuValue caseData .F (some 0) 7 = (3881157 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_0 : packedMuValue caseData .F (some 1) 0 = (491429085 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_1 : packedMuValue caseData .F (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_packed_F_2_2 : packedMuValue caseData .F (some 1) 2 = (530796618 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_3 : packedMuValue caseData .F (some 1) 3 = (163592337 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_4 : packedMuValue caseData .F (some 1) 4 = (50561448 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_5 : packedMuValue caseData .F (some 1) 5 = (19506627 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_6 : packedMuValue caseData .F (some 1) 6 = (9450891 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_2_7 : packedMuValue caseData .F (some 1) 7 = (14488767 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_0 : packedMuValue caseData .F (some 2) 0 = (358759662 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_1 : packedMuValue caseData .F (some 2) 1 = (65531268 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_2 : packedMuValue caseData .F (some 2) 2 = 0 := rfl
@[simp] theorem lookup_case_packed_F_3_3 : packedMuValue caseData .F (some 2) 3 = (62752836 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_4 : packedMuValue caseData .F (some 2) 4 = (82165251 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_5 : packedMuValue caseData .F (some 2) 5 = (12345129 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_6 : packedMuValue caseData .F (some 2) 6 = (8384724 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_3_7 : packedMuValue caseData .F (some 2) 7 = (5056458 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_0 : packedMuValue caseData .F (some 3) 0 = (71546571 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_1 : packedMuValue caseData .F (some 3) 1 = (444435096 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_2 : packedMuValue caseData .F (some 3) 2 = (10412952 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_3 : packedMuValue caseData .F (some 3) 3 = 0 := rfl
@[simp] theorem lookup_case_packed_F_4_4 : packedMuValue caseData .F (some 3) 4 = (10659036 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_5 : packedMuValue caseData .F (some 3) 5 = (39394851 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_6 : packedMuValue caseData .F (some 3) 6 = (22115715 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_4_7 : packedMuValue caseData .F (some 3) 7 = (7462611 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_0 : packedMuValue caseData .F (some 4) 0 = (23380131 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_1 : packedMuValue caseData .F (some 4) 1 = (15095010 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_2 : packedMuValue caseData .F (some 4) 2 = (30885900 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_3 : packedMuValue caseData .F (some 4) 3 = (4689765 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_4 : packedMuValue caseData .F (some 4) 4 = 0 := rfl
@[simp] theorem lookup_case_packed_F_5_5 : packedMuValue caseData .F (some 4) 5 = (4548951 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_6 : packedMuValue caseData .F (some 4) 6 = (32011050 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_5_7 : packedMuValue caseData .F (some 4) 7 = (5620644 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_0 : packedMuValue caseData .F (some 5) 0 = (21530091 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_1 : packedMuValue caseData .F (some 5) 1 = (29445003 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_2 : packedMuValue caseData .F (some 5) 2 = (4272000 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_3 : packedMuValue caseData .F (some 5) 3 = (32416227 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_4 : packedMuValue caseData .F (some 5) 4 = (2073834 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_5 : packedMuValue caseData .F (some 5) 5 = 0 := rfl
@[simp] theorem lookup_case_packed_F_6_6 : packedMuValue caseData .F (some 5) 6 = (2438376 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_6_7 : packedMuValue caseData .F (some 5) 7 = (8871891 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_0 : packedMuValue caseData .F (some 6) 0 = (6966636 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_1 : packedMuValue caseData .F (some 6) 1 = (8167869 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_2 : packedMuValue caseData .F (some 6) 2 = (7470744 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_3 : packedMuValue caseData .F (some 6) 3 = (2226153 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_4 : packedMuValue caseData .F (some 6) 4 = (15464208 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_5 : packedMuValue caseData .F (some 6) 5 = (1137645 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_7_6 : packedMuValue caseData .F (some 6) 6 = 0 := rfl
@[simp] theorem lookup_case_packed_F_7_7 : packedMuValue caseData .F (some 6) 7 = (1070697 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_0 : packedMuValue caseData .F (some 7) 0 = (6671124 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_1 : packedMuValue caseData .F (some 7) 1 = (5827404 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_2 : packedMuValue caseData .F (some 7) 2 = (3508026 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_3 : packedMuValue caseData .F (some 7) 3 = (6167592 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_4 : packedMuValue caseData .F (some 7) 4 = (1178478 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_5 : packedMuValue caseData .F (some 7) 5 = (12887502 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_6 : packedMuValue caseData .F (some 7) 6 = (784089 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_F_8_7 : packedMuValue caseData .F (some 7) 7 = 0 := rfl
@[simp] theorem lookup_case_lagMinusValue_J_0 : lagMinusValue caseData .J 0 = (64389 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_1 : lagMinusValue caseData .J 1 = (7672453198 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_2 : lagMinusValue caseData .J 2 = (825 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_3 : lagMinusValue caseData .J 3 = (531 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_4 : lagMinusValue caseData .J 4 = (309 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_5 : lagMinusValue caseData .J 5 = (243 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_6 : lagMinusValue caseData .J 6 = (219 / 30000000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_7 : lagMinusValue caseData .J 7 = (501 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_0 : lagPlusValue caseData .J 0 = (14340426911 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_1 : lagPlusValue caseData .J 1 = (1026 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_2 : lagPlusValue caseData .J 2 = (3753 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_3 : lagPlusValue caseData .J 3 = (984 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_4 : lagPlusValue caseData .J 4 = (10041 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_5 : lagPlusValue caseData .J 5 = (3375 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_6 : lagPlusValue caseData .J 6 = (145693314 / 30000000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_7 : lagPlusValue caseData .J 7 = (3231 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_0 : packedMuValue caseData .J none 0 = (543264441 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_1 : packedMuValue caseData .J none 1 = (118564074 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_2 : packedMuValue caseData .J none 2 = (51054735 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_3 : packedMuValue caseData .J none 3 = (31456008 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_4 : packedMuValue caseData .J none 4 = (21472431 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_5 : packedMuValue caseData .J none 5 = (16054335 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_6 : packedMuValue caseData .J none 6 = (11308782 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_0_7 : packedMuValue caseData .J none 7 = (2636139 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_0 : packedMuValue caseData .J (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_J_1_1 : packedMuValue caseData .J (some 0) 1 = (282612162 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_2 : packedMuValue caseData .J (some 0) 2 = (130154991 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_3 : packedMuValue caseData .J (some 0) 3 = (61735254 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_4 : packedMuValue caseData .J (some 0) 4 = (33097461 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_5 : packedMuValue caseData .J (some 0) 5 = (25724397 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_6 : packedMuValue caseData .J (some 0) 6 = (16553337 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_1_7 : packedMuValue caseData .J (some 0) 7 = (3122136 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_0 : packedMuValue caseData .J (some 1) 0 = (7215811393 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_1 : packedMuValue caseData .J (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_packed_J_2_2 : packedMuValue caseData .J (some 1) 2 = (345493818 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_3 : packedMuValue caseData .J (some 1) 3 = (106425447 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_4 : packedMuValue caseData .J (some 1) 4 = (47691729 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_5 : packedMuValue caseData .J (some 1) 5 = (28372536 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_6 : packedMuValue caseData .J (some 1) 6 = (23345706 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_2_7 : packedMuValue caseData .J (some 1) 7 = (3383931 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_0 : packedMuValue caseData .J (some 2) 0 = (43434084 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_1 : packedMuValue caseData .J (some 2) 1 = (54618543 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_2 : packedMuValue caseData .J (some 2) 2 = 0 := rfl
@[simp] theorem lookup_case_packed_J_3_3 : packedMuValue caseData .J (some 2) 3 = (158055912 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_4 : packedMuValue caseData .J (some 2) 4 = (94030335 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_5 : packedMuValue caseData .J (some 2) 5 = (45141342 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_6 : packedMuValue caseData .J (some 2) 6 = (20914788 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_3_7 : packedMuValue caseData .J (some 2) 7 = (3825306 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_0 : packedMuValue caseData .J (some 3) 0 = (19965546 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_1 : packedMuValue caseData .J (some 3) 1 = (23051637 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_2 : packedMuValue caseData .J (some 3) 2 = (43101795 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_3 : packedMuValue caseData .J (some 3) 3 = 0 := rfl
@[simp] theorem lookup_case_packed_J_4_4 : packedMuValue caseData .J (some 3) 4 = (68476938 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_5 : packedMuValue caseData .J (some 3) 5 = (45646575 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_6 : packedMuValue caseData .J (some 3) 6 = (30166563 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_4_7 : packedMuValue caseData .J (some 3) 7 = (3865485 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_0 : packedMuValue caseData .J (some 4) 0 = (7181043 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_1 : packedMuValue caseData .J (some 4) 1 = (8075490 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_2 : packedMuValue caseData .J (some 4) 2 = (15209445 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_3 : packedMuValue caseData .J (some 4) 3 = (20939430 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_4 : packedMuValue caseData .J (some 4) 4 = 0 := rfl
@[simp] theorem lookup_case_packed_J_5_5 : packedMuValue caseData .J (some 4) 5 = (47876541 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_6 : packedMuValue caseData .J (some 4) 6 = (33874026 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_5_7 : packedMuValue caseData .J (some 4) 7 = (5207127 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_0 : packedMuValue caseData .J (some 5) 0 = (4041483 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_1 : packedMuValue caseData .J (some 5) 1 = (4202823 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_2 : packedMuValue caseData .J (some 5) 2 = (5608878 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_3 : packedMuValue caseData .J (some 5) 3 = (10118616 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_4 : packedMuValue caseData .J (some 5) 4 = (12775608 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_5 : packedMuValue caseData .J (some 5) 5 = 0 := rfl
@[simp] theorem lookup_case_packed_J_6_6 : packedMuValue caseData .J (some 5) 6 = (38208855 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_6_7 : packedMuValue caseData .J (some 5) 7 = (5851314 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_0 : packedMuValue caseData .J (some 6) 0 = (2504190 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_1 : packedMuValue caseData .J (some 6) 1 = (2613930 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_2 : packedMuValue caseData .J (some 6) 2 = (3286329 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_3 : packedMuValue caseData .J (some 6) 3 = (4208574 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_4 : packedMuValue caseData .J (some 6) 4 = (9856644 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_5 : packedMuValue caseData .J (some 6) 5 = (11382849 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_7_6 : packedMuValue caseData .J (some 6) 6 = 0 := rfl
@[simp] theorem lookup_case_packed_J_7_7 : packedMuValue caseData .J (some 6) 7 = (6123543 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_0 : packedMuValue caseData .J (some 7) 0 = (1393464 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_1 : packedMuValue caseData .J (some 7) 1 = (1410573 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_2 : packedMuValue caseData .J (some 7) 2 = (1647783 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_3 : packedMuValue caseData .J (some 7) 3 = (2090292 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_4 : packedMuValue caseData .J (some 7) 4 = (2818596 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_5 : packedMuValue caseData .J (some 7) 5 = (9834501 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_6 : packedMuValue caseData .J (some 7) 6 = (13548357 / 30000000000) := rfl
@[simp] theorem lookup_case_packed_J_8_7 : packedMuValue caseData .J (some 7) 7 = 0 := rfl
@[simp] theorem lookup_case_A_0_0 : upperTriangleMatrix caseData .lower (0, 0) (0, 0) = (772295477400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_1 : upperTriangleMatrix caseData .lower (0, 0) (0, 1) = (12694638600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_2 : upperTriangleMatrix caseData .lower (0, 0) (1, 0) = (-363005567400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_3 : upperTriangleMatrix caseData .lower (0, 0) (1, 1) = (714575807215 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_4 : upperTriangleMatrix caseData .lower (0, 0) (2, 0) = (-633586894200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_5 : upperTriangleMatrix caseData .lower (0, 0) (2, 1) = (604755181587 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_6 : upperTriangleMatrix caseData .lower (0, 0) (3, 0) = (236174983200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_7 : upperTriangleMatrix caseData .lower (0, 0) (3, 1) = (11843548800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_8 : upperTriangleMatrix caseData .lower (0, 0) (4, 0) = (-13752265200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_9 : upperTriangleMatrix caseData .lower (0, 0) (4, 1) = (-100888978200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_10 : upperTriangleMatrix caseData .lower (0, 0) (5, 0) = (4602519000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_11 : upperTriangleMatrix caseData .lower (0, 0) (5, 1) = (23006980800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_12 : upperTriangleMatrix caseData .lower (0, 0) (6, 0) = (11621706000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_13 : upperTriangleMatrix caseData .lower (0, 0) (6, 1) = (-13248870000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_14 : upperTriangleMatrix caseData .lower (0, 0) (7, 0) = (3243203400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_0_15 : upperTriangleMatrix caseData .lower (0, 0) (7, 1) = (15571258800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_0 : upperTriangleMatrix caseData .lower (0, 1) (0, 0) = (12694638600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_1 : upperTriangleMatrix caseData .lower (0, 1) (0, 1) = (785575989552 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_2 : upperTriangleMatrix caseData .lower (0, 1) (1, 0) = (-382549245501 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_3 : upperTriangleMatrix caseData .lower (0, 1) (1, 1) = (-46267972200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_4 : upperTriangleMatrix caseData .lower (0, 1) (2, 0) = (130963502400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_5 : upperTriangleMatrix caseData .lower (0, 1) (2, 1) = (-633179071800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_6 : upperTriangleMatrix caseData .lower (0, 1) (3, 0) = (244520039301 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_7 : upperTriangleMatrix caseData .lower (0, 1) (3, 1) = (9247297200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_8 : upperTriangleMatrix caseData .lower (0, 1) (4, 0) = (-15502293600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_9 : upperTriangleMatrix caseData .lower (0, 1) (4, 1) = (-105177669600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_10 : upperTriangleMatrix caseData .lower (0, 1) (5, 0) = (6058514400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_11 : upperTriangleMatrix caseData .lower (0, 1) (5, 1) = (26395256400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_12 : upperTriangleMatrix caseData .lower (0, 1) (6, 0) = (3407652000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_13 : upperTriangleMatrix caseData .lower (0, 1) (6, 1) = (-14039725200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_14 : upperTriangleMatrix caseData .lower (0, 1) (7, 0) = (2823515400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_1_15 : upperTriangleMatrix caseData .lower (0, 1) (7, 1) = (1157683800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_0 : upperTriangleMatrix caseData .lower (1, 0) (0, 0) = (-363005567400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_1 : upperTriangleMatrix caseData .lower (1, 0) (0, 1) = (-382549245501 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_2 : upperTriangleMatrix caseData .lower (1, 0) (1, 0) = (676595824200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_3 : upperTriangleMatrix caseData .lower (1, 0) (1, 1) = (-1046572457215 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_4 : upperTriangleMatrix caseData .lower (1, 0) (2, 0) = (-2931998400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_5 : upperTriangleMatrix caseData .lower (1, 0) (2, 1) = (-192854888400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_6 : upperTriangleMatrix caseData .lower (1, 0) (3, 0) = (-550191128400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_7 : upperTriangleMatrix caseData .lower (1, 0) (3, 1) = (264205395627 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_8 : upperTriangleMatrix caseData .lower (1, 0) (4, 0) = (239739066600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_9 : upperTriangleMatrix caseData .lower (1, 0) (4, 1) = (52912050000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_10 : upperTriangleMatrix caseData .lower (1, 0) (5, 0) = (-10576156200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_11 : upperTriangleMatrix caseData .lower (1, 0) (5, 1) = (-126587997000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_12 : upperTriangleMatrix caseData .lower (1, 0) (6, 0) = (-2724828000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_13 : upperTriangleMatrix caseData .lower (1, 0) (6, 1) = (22927739400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_14 : upperTriangleMatrix caseData .lower (1, 0) (7, 0) = (12605697600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_2_15 : upperTriangleMatrix caseData .lower (1, 0) (7, 1) = (-12810752400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_0 : upperTriangleMatrix caseData .lower (1, 1) (0, 0) = (714575807215 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_1 : upperTriangleMatrix caseData .lower (1, 1) (0, 1) = (-46267972200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_2 : upperTriangleMatrix caseData .lower (1, 1) (1, 0) = (-1046572457215 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_3 : upperTriangleMatrix caseData .lower (1, 1) (1, 1) = (86664550323 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_4 : upperTriangleMatrix caseData .lower (1, 1) (2, 0) = (327782340000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_5 : upperTriangleMatrix caseData .lower (1, 1) (2, 1) = (-13917958800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_6 : upperTriangleMatrix caseData .lower (1, 1) (3, 0) = (-112429629000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_7 : upperTriangleMatrix caseData .lower (1, 1) (3, 1) = (-35088864000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_8 : upperTriangleMatrix caseData .lower (1, 1) (4, 0) = (142048728000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_9 : upperTriangleMatrix caseData .lower (1, 1) (4, 1) = (16145995800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_10 : upperTriangleMatrix caseData .lower (1, 1) (5, 0) = (-19332423600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_11 : upperTriangleMatrix caseData .lower (1, 1) (5, 1) = (-29215544400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_12 : upperTriangleMatrix caseData .lower (1, 1) (6, 0) = (-8218059000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_13 : upperTriangleMatrix caseData .lower (1, 1) (6, 1) = (27262288200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_14 : upperTriangleMatrix caseData .lower (1, 1) (7, 0) = (6128242800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_3_15 : upperTriangleMatrix caseData .lower (1, 1) (7, 1) = (-6159186600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_0 : upperTriangleMatrix caseData .lower (2, 0) (0, 0) = (-633586894200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_1 : upperTriangleMatrix caseData .lower (2, 0) (0, 1) = (130963502400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_2 : upperTriangleMatrix caseData .lower (2, 0) (1, 0) = (-2931998400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_3 : upperTriangleMatrix caseData .lower (2, 0) (1, 1) = (327782340000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_4 : upperTriangleMatrix caseData .lower (2, 0) (2, 0) = (1193412346200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_5 : upperTriangleMatrix caseData .lower (2, 0) (2, 1) = (-445113171756 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_6 : upperTriangleMatrix caseData .lower (2, 0) (3, 0) = (-283355539200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_7 : upperTriangleMatrix caseData .lower (2, 0) (3, 1) = (-215571129600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_8 : upperTriangleMatrix caseData .lower (2, 0) (4, 0) = (-467698994400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_9 : upperTriangleMatrix caseData .lower (2, 0) (4, 1) = (243563776815 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_10 : upperTriangleMatrix caseData .lower (2, 0) (5, 0) = (203045545800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_11 : upperTriangleMatrix caseData .lower (2, 0) (5, 1) = (39456931800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_12 : upperTriangleMatrix caseData .lower (2, 0) (6, 0) = (2484614400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_13 : upperTriangleMatrix caseData .lower (2, 0) (6, 1) = (-100491954000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_14 : upperTriangleMatrix caseData .lower (2, 0) (7, 0) = (-34618832400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_4_15 : upperTriangleMatrix caseData .lower (2, 0) (7, 1) = (15577231800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_0 : upperTriangleMatrix caseData .lower (2, 1) (0, 0) = (604755181587 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_1 : upperTriangleMatrix caseData .lower (2, 1) (0, 1) = (-633179071800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_2 : upperTriangleMatrix caseData .lower (2, 1) (1, 0) = (-192854888400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_3 : upperTriangleMatrix caseData .lower (2, 1) (1, 1) = (-13917958800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_4 : upperTriangleMatrix caseData .lower (2, 1) (2, 0) = (-445113171756 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_5 : upperTriangleMatrix caseData .lower (2, 1) (2, 1) = (692940273984 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_6 : upperTriangleMatrix caseData .lower (2, 1) (3, 0) = (30169648200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_7 : upperTriangleMatrix caseData .lower (2, 1) (3, 1) = (-47567164200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_8 : upperTriangleMatrix caseData .lower (2, 1) (4, 0) = (-94988528400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_9 : upperTriangleMatrix caseData .lower (2, 1) (4, 1) = (-33519187800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_10 : upperTriangleMatrix caseData .lower (2, 1) (5, 0) = (115435098969 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_11 : upperTriangleMatrix caseData .lower (2, 1) (5, 1) = (12987981000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_12 : upperTriangleMatrix caseData .lower (2, 1) (6, 0) = (-7377188400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_13 : upperTriangleMatrix caseData .lower (2, 1) (6, 1) = (-21235099800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_14 : upperTriangleMatrix caseData .lower (2, 1) (7, 0) = (-11897491800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_5_15 : upperTriangleMatrix caseData .lower (2, 1) (7, 1) = (20450531400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_0 : upperTriangleMatrix caseData .lower (3, 0) (0, 0) = (236174983200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_1 : upperTriangleMatrix caseData .lower (3, 0) (0, 1) = (244520039301 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_2 : upperTriangleMatrix caseData .lower (3, 0) (1, 0) = (-550191128400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_3 : upperTriangleMatrix caseData .lower (3, 0) (1, 1) = (-112429629000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_4 : upperTriangleMatrix caseData .lower (3, 0) (2, 0) = (-283355539200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_5 : upperTriangleMatrix caseData .lower (3, 0) (2, 1) = (30169648200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_6 : upperTriangleMatrix caseData .lower (3, 0) (3, 0) = (1081047348000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_7 : upperTriangleMatrix caseData .lower (3, 0) (3, 1) = (-55854317400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_8 : upperTriangleMatrix caseData .lower (3, 0) (4, 0) = (-263830927800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_9 : upperTriangleMatrix caseData .lower (3, 0) (4, 1) = (-188258061000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_10 : upperTriangleMatrix caseData .lower (3, 0) (5, 0) = (-365485949400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_11 : upperTriangleMatrix caseData .lower (3, 0) (5, 1) = (202766111976 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_12 : upperTriangleMatrix caseData .lower (3, 0) (6, 0) = (140523968400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_13 : upperTriangleMatrix caseData .lower (3, 0) (6, 1) = (20191525800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_14 : upperTriangleMatrix caseData .lower (3, 0) (7, 0) = (18422599800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_6_15 : upperTriangleMatrix caseData .lower (3, 0) (7, 1) = (-70948158600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_0 : upperTriangleMatrix caseData .lower (3, 1) (0, 0) = (11843548800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_1 : upperTriangleMatrix caseData .lower (3, 1) (0, 1) = (9247297200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_2 : upperTriangleMatrix caseData .lower (3, 1) (1, 0) = (264205395627 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_3 : upperTriangleMatrix caseData .lower (3, 1) (1, 1) = (-35088864000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_4 : upperTriangleMatrix caseData .lower (3, 1) (2, 0) = (-215571129600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_5 : upperTriangleMatrix caseData .lower (3, 1) (2, 1) = (-47567164200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_6 : upperTriangleMatrix caseData .lower (3, 1) (3, 0) = (-55854317400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_7 : upperTriangleMatrix caseData .lower (3, 1) (3, 1) = (229807388154 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_8 : upperTriangleMatrix caseData .lower (3, 1) (4, 0) = (-3152664000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_9 : upperTriangleMatrix caseData .lower (3, 1) (4, 1) = (-47290980000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_10 : upperTriangleMatrix caseData .lower (3, 1) (5, 0) = (-78374014200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_11 : upperTriangleMatrix caseData .lower (3, 1) (5, 1) = (-29294031000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_12 : upperTriangleMatrix caseData .lower (3, 1) (6, 0) = (79080094173 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_13 : upperTriangleMatrix caseData .lower (3, 1) (6, 1) = (9889998000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_14 : upperTriangleMatrix caseData .lower (3, 1) (7, 0) = (8271760800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_7_15 : upperTriangleMatrix caseData .lower (3, 1) (7, 1) = (-13200676200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_0 : upperTriangleMatrix caseData .lower (4, 0) (0, 0) = (-13752265200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_1 : upperTriangleMatrix caseData .lower (4, 0) (0, 1) = (-15502293600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_2 : upperTriangleMatrix caseData .lower (4, 0) (1, 0) = (239739066600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_3 : upperTriangleMatrix caseData .lower (4, 0) (1, 1) = (142048728000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_4 : upperTriangleMatrix caseData .lower (4, 0) (2, 0) = (-467698994400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_5 : upperTriangleMatrix caseData .lower (4, 0) (2, 1) = (-94988528400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_6 : upperTriangleMatrix caseData .lower (4, 0) (3, 0) = (-263830927800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_7 : upperTriangleMatrix caseData .lower (4, 0) (3, 1) = (-3152664000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_8 : upperTriangleMatrix caseData .lower (4, 0) (4, 0) = (885642386400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_9 : upperTriangleMatrix caseData .lower (4, 0) (4, 1) = (-924378600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_10 : upperTriangleMatrix caseData .lower (4, 0) (5, 0) = (-208893979800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_11 : upperTriangleMatrix caseData .lower (4, 0) (5, 1) = (-149120438976 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_12 : upperTriangleMatrix caseData .lower (4, 0) (6, 0) = (-242201998200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_13 : upperTriangleMatrix caseData .lower (4, 0) (6, 1) = (161690158200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_14 : upperTriangleMatrix caseData .lower (4, 0) (7, 0) = (57363383400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_8_15 : upperTriangleMatrix caseData .lower (4, 0) (7, 1) = (6643966800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_0 : upperTriangleMatrix caseData .lower (4, 1) (0, 0) = (-100888978200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_1 : upperTriangleMatrix caseData .lower (4, 1) (0, 1) = (-105177669600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_2 : upperTriangleMatrix caseData .lower (4, 1) (1, 0) = (52912050000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_3 : upperTriangleMatrix caseData .lower (4, 1) (1, 1) = (16145995800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_4 : upperTriangleMatrix caseData .lower (4, 1) (2, 0) = (243563776815 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_5 : upperTriangleMatrix caseData .lower (4, 1) (2, 1) = (-33519187800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_6 : upperTriangleMatrix caseData .lower (4, 1) (3, 0) = (-188258061000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_7 : upperTriangleMatrix caseData .lower (4, 1) (3, 1) = (-47290980000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_8 : upperTriangleMatrix caseData .lower (4, 1) (4, 0) = (-924378600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_9 : upperTriangleMatrix caseData .lower (4, 1) (4, 1) = (155957759658 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_10 : upperTriangleMatrix caseData .lower (4, 1) (5, 0) = (2592091200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_11 : upperTriangleMatrix caseData .lower (4, 1) (5, 1) = (-41268416400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_12 : upperTriangleMatrix caseData .lower (4, 1) (6, 0) = (-44438099400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_13 : upperTriangleMatrix caseData .lower (4, 1) (6, 1) = (-23593984800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_14 : upperTriangleMatrix caseData .lower (4, 1) (7, 0) = (27018132585 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_9_15 : upperTriangleMatrix caseData .lower (4, 1) (7, 1) = (7796208600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_0 : upperTriangleMatrix caseData .lower (5, 0) (0, 0) = (4602519000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_1 : upperTriangleMatrix caseData .lower (5, 0) (0, 1) = (6058514400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_2 : upperTriangleMatrix caseData .lower (5, 0) (1, 0) = (-10576156200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_3 : upperTriangleMatrix caseData .lower (5, 0) (1, 1) = (-19332423600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_4 : upperTriangleMatrix caseData .lower (5, 0) (2, 0) = (203045545800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_5 : upperTriangleMatrix caseData .lower (5, 0) (2, 1) = (115435098969 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_6 : upperTriangleMatrix caseData .lower (5, 0) (3, 0) = (-365485949400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_7 : upperTriangleMatrix caseData .lower (5, 0) (3, 1) = (-78374014200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_8 : upperTriangleMatrix caseData .lower (5, 0) (4, 0) = (-208893979800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_9 : upperTriangleMatrix caseData .lower (5, 0) (4, 1) = (2592091200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_10 : upperTriangleMatrix caseData .lower (5, 0) (5, 0) = (641726451600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_11 : upperTriangleMatrix caseData .lower (5, 0) (5, 1) = (23189260200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_12 : upperTriangleMatrix caseData .lower (5, 0) (6, 0) = (-200487352200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_13 : upperTriangleMatrix caseData .lower (5, 0) (6, 1) = (-106504162200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_14 : upperTriangleMatrix caseData .lower (5, 0) (7, 0) = (-87141025200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_10_15 : upperTriangleMatrix caseData .lower (5, 0) (7, 1) = (112813249200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_0 : upperTriangleMatrix caseData .lower (5, 1) (0, 0) = (23006980800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_1 : upperTriangleMatrix caseData .lower (5, 1) (0, 1) = (26395256400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_2 : upperTriangleMatrix caseData .lower (5, 1) (1, 0) = (-126587997000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_3 : upperTriangleMatrix caseData .lower (5, 1) (1, 1) = (-29215544400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_4 : upperTriangleMatrix caseData .lower (5, 1) (2, 0) = (39456931800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_5 : upperTriangleMatrix caseData .lower (5, 1) (2, 1) = (12987981000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_6 : upperTriangleMatrix caseData .lower (5, 1) (3, 0) = (202766111976 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_7 : upperTriangleMatrix caseData .lower (5, 1) (3, 1) = (-29294031000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_8 : upperTriangleMatrix caseData .lower (5, 1) (4, 0) = (-149120438976 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_9 : upperTriangleMatrix caseData .lower (5, 1) (4, 1) = (-41268416400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_10 : upperTriangleMatrix caseData .lower (5, 1) (5, 0) = (23189260200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_11 : upperTriangleMatrix caseData .lower (5, 1) (5, 1) = (124539961029 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_12 : upperTriangleMatrix caseData .lower (5, 1) (6, 0) = (-10794052200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_13 : upperTriangleMatrix caseData .lower (5, 1) (6, 1) = (-36771580200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_14 : upperTriangleMatrix caseData .lower (5, 1) (7, 0) = (-24257770200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_11_15 : upperTriangleMatrix caseData .lower (5, 1) (7, 1) = (-16232482200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_0 : upperTriangleMatrix caseData .lower (6, 0) (0, 0) = (11621706000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_1 : upperTriangleMatrix caseData .lower (6, 0) (0, 1) = (3407652000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_2 : upperTriangleMatrix caseData .lower (6, 0) (1, 0) = (-2724828000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_3 : upperTriangleMatrix caseData .lower (6, 0) (1, 1) = (-8218059000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_4 : upperTriangleMatrix caseData .lower (6, 0) (2, 0) = (2484614400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_5 : upperTriangleMatrix caseData .lower (6, 0) (2, 1) = (-7377188400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_6 : upperTriangleMatrix caseData .lower (6, 0) (3, 0) = (140523968400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_7 : upperTriangleMatrix caseData .lower (6, 0) (3, 1) = (79080094173 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_8 : upperTriangleMatrix caseData .lower (6, 0) (4, 0) = (-242201998200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_9 : upperTriangleMatrix caseData .lower (6, 0) (4, 1) = (-44438099400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_10 : upperTriangleMatrix caseData .lower (6, 0) (5, 0) = (-200487352200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_11 : upperTriangleMatrix caseData .lower (6, 0) (5, 1) = (-10794052200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_12 : upperTriangleMatrix caseData .lower (6, 0) (6, 0) = (418837240800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_13 : upperTriangleMatrix caseData .lower (6, 0) (6, 1) = (25896662400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_14 : upperTriangleMatrix caseData .lower (6, 0) (7, 0) = (-63765351000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_12_15 : upperTriangleMatrix caseData .lower (6, 0) (7, 1) = (-68068691400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_0 : upperTriangleMatrix caseData .lower (6, 1) (0, 0) = (-13248870000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_1 : upperTriangleMatrix caseData .lower (6, 1) (0, 1) = (-14039725200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_2 : upperTriangleMatrix caseData .lower (6, 1) (1, 0) = (22927739400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_3 : upperTriangleMatrix caseData .lower (6, 1) (1, 1) = (27262288200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_4 : upperTriangleMatrix caseData .lower (6, 1) (2, 0) = (-100491954000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_5 : upperTriangleMatrix caseData .lower (6, 1) (2, 1) = (-21235099800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_6 : upperTriangleMatrix caseData .lower (6, 1) (3, 0) = (20191525800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_7 : upperTriangleMatrix caseData .lower (6, 1) (3, 1) = (9889998000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_8 : upperTriangleMatrix caseData .lower (6, 1) (4, 0) = (161690158200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_9 : upperTriangleMatrix caseData .lower (6, 1) (4, 1) = (-23593984800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_10 : upperTriangleMatrix caseData .lower (6, 1) (5, 0) = (-106504162200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_11 : upperTriangleMatrix caseData .lower (6, 1) (5, 1) = (-36771580200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_12 : upperTriangleMatrix caseData .lower (6, 1) (6, 0) = (25896662400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_13 : upperTriangleMatrix caseData .lower (6, 1) (6, 1) = (79737122088 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_14 : upperTriangleMatrix caseData .lower (6, 1) (7, 0) = (-8931791400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_13_15 : upperTriangleMatrix caseData .lower (6, 1) (7, 1) = (-28030803600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_0 : upperTriangleMatrix caseData .lower (7, 0) (0, 0) = (3243203400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_1 : upperTriangleMatrix caseData .lower (7, 0) (0, 1) = (2823515400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_2 : upperTriangleMatrix caseData .lower (7, 0) (1, 0) = (12605697600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_3 : upperTriangleMatrix caseData .lower (7, 0) (1, 1) = (6128242800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_4 : upperTriangleMatrix caseData .lower (7, 0) (2, 0) = (-34618832400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_5 : upperTriangleMatrix caseData .lower (7, 0) (2, 1) = (-11897491800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_6 : upperTriangleMatrix caseData .lower (7, 0) (3, 0) = (18422599800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_7 : upperTriangleMatrix caseData .lower (7, 0) (3, 1) = (8271760800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_8 : upperTriangleMatrix caseData .lower (7, 0) (4, 0) = (57363383400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_9 : upperTriangleMatrix caseData .lower (7, 0) (4, 1) = (27018132585 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_10 : upperTriangleMatrix caseData .lower (7, 0) (5, 0) = (-87141025200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_11 : upperTriangleMatrix caseData .lower (7, 0) (5, 1) = (-24257770200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_12 : upperTriangleMatrix caseData .lower (7, 0) (6, 0) = (-63765351000 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_13 : upperTriangleMatrix caseData .lower (7, 0) (6, 1) = (-8931791400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_14 : upperTriangleMatrix caseData .lower (7, 0) (7, 0) = (139606532400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_14_15 : upperTriangleMatrix caseData .lower (7, 0) (7, 1) = (10457240400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_0 : upperTriangleMatrix caseData .lower (7, 1) (0, 0) = (15571258800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_1 : upperTriangleMatrix caseData .lower (7, 1) (0, 1) = (1157683800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_2 : upperTriangleMatrix caseData .lower (7, 1) (1, 0) = (-12810752400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_3 : upperTriangleMatrix caseData .lower (7, 1) (1, 1) = (-6159186600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_4 : upperTriangleMatrix caseData .lower (7, 1) (2, 0) = (15577231800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_5 : upperTriangleMatrix caseData .lower (7, 1) (2, 1) = (20450531400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_6 : upperTriangleMatrix caseData .lower (7, 1) (3, 0) = (-70948158600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_7 : upperTriangleMatrix caseData .lower (7, 1) (3, 1) = (-13200676200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_8 : upperTriangleMatrix caseData .lower (7, 1) (4, 0) = (6643966800 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_9 : upperTriangleMatrix caseData .lower (7, 1) (4, 1) = (7796208600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_10 : upperTriangleMatrix caseData .lower (7, 1) (5, 0) = (112813249200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_11 : upperTriangleMatrix caseData .lower (7, 1) (5, 1) = (-16232482200 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_12 : upperTriangleMatrix caseData .lower (7, 1) (6, 0) = (-68068691400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_13 : upperTriangleMatrix caseData .lower (7, 1) (6, 1) = (-28030803600 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_14 : upperTriangleMatrix caseData .lower (7, 1) (7, 0) = (10457240400 / 6000000000000) := rfl
@[simp] theorem lookup_case_A_15_15 : upperTriangleMatrix caseData .lower (7, 1) (7, 1) = (59967181377 / 6000000000000) := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
