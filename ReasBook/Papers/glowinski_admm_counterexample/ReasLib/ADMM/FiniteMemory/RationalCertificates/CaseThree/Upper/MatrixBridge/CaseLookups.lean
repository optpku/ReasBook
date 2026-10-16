module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.Data

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge

@[simp] theorem lookup_case_gammaLower : caseData.gammaLower = (187 / 100) := rfl
@[simp] theorem lookup_case_gammaUpper : caseData.gammaUpper = (47 / 25) := rfl
@[simp] theorem lookup_case_omega : caseData.omega = (2907189 / 1000000000) := rfl
@[simp] theorem lookup_case_epsilon : caseData.epsilon = (1 / 5000) := rfl
@[simp] theorem lookup_case_zeta : caseData.zeta = (1 / 5000) := rfl
@[simp] theorem lookup_case_endpoint : endpointGamma caseData .upper = (47 / 25) := rfl
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
@[simp] theorem lookup_case_A_0_0 : upperTriangleMatrix caseData .upper (0, 0) (0, 0) = (195032291250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_1 : upperTriangleMatrix caseData .upper (0, 0) (0, 1) = (3040240800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_2 : upperTriangleMatrix caseData .upper (0, 0) (1, 0) = (-93976427100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_3 : upperTriangleMatrix caseData .upper (0, 0) (1, 1) = (177460931291 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_4 : upperTriangleMatrix caseData .upper (0, 0) (2, 0) = (-157107010200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_5 : upperTriangleMatrix caseData .upper (0, 0) (2, 1) = (156018054471 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_6 : upperTriangleMatrix caseData .upper (0, 0) (3, 0) = (58134814650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_7 : upperTriangleMatrix caseData .upper (0, 0) (3, 1) = (1109074500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_8 : upperTriangleMatrix caseData .upper (0, 0) (4, 0) = (-2311407600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_9 : upperTriangleMatrix caseData .upper (0, 0) (4, 1) = (-24984188250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_10 : upperTriangleMatrix caseData .upper (0, 0) (5, 0) = (941234400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_11 : upperTriangleMatrix caseData .upper (0, 0) (5, 1) = (5226392700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_12 : upperTriangleMatrix caseData .upper (0, 0) (6, 0) = (2526766050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_13 : upperTriangleMatrix caseData .upper (0, 0) (6, 1) = (-3259164900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_14 : upperTriangleMatrix caseData .upper (0, 0) (7, 0) = (1474975200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_0_15 : upperTriangleMatrix caseData .upper (0, 0) (7, 1) = (4377027600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_0 : upperTriangleMatrix caseData .upper (0, 1) (0, 0) = (3040240800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_1 : upperTriangleMatrix caseData .upper (0, 1) (0, 1) = (196524304512 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_2 : upperTriangleMatrix caseData .upper (0, 1) (1, 0) = (-95972251833 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_3 : upperTriangleMatrix caseData .upper (0, 1) (1, 1) = (-10636530750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_4 : upperTriangleMatrix caseData .upper (0, 1) (2, 0) = (33721362300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_5 : upperTriangleMatrix caseData .upper (0, 1) (2, 1) = (-158311675350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_6 : upperTriangleMatrix caseData .upper (0, 1) (3, 0) = (59921569233 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_7 : upperTriangleMatrix caseData .upper (0, 1) (3, 1) = (1084542600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_8 : upperTriangleMatrix caseData .upper (0, 1) (4, 0) = (-2319690150 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_9 : upperTriangleMatrix caseData .upper (0, 1) (4, 1) = (-25667550300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_10 : upperTriangleMatrix caseData .upper (0, 1) (5, 0) = (277821900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_11 : upperTriangleMatrix caseData .upper (0, 1) (5, 1) = (5966956800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_12 : upperTriangleMatrix caseData .upper (0, 1) (6, 0) = (998953200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_13 : upperTriangleMatrix caseData .upper (0, 1) (6, 1) = (-3295827000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_14 : upperTriangleMatrix caseData .upper (0, 1) (7, 0) = (1506985200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_1_15 : upperTriangleMatrix caseData .upper (0, 1) (7, 1) = (345869850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_0 : upperTriangleMatrix caseData .upper (1, 0) (0, 0) = (-93976427100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_1 : upperTriangleMatrix caseData .upper (1, 0) (0, 1) = (-95972251833 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_2 : upperTriangleMatrix caseData .upper (1, 0) (1, 0) = (179045450250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_3 : upperTriangleMatrix caseData .upper (1, 0) (1, 1) = (-260812432391 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_4 : upperTriangleMatrix caseData .upper (1, 0) (2, 0) = (-10101601050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_5 : upperTriangleMatrix caseData .upper (1, 0) (2, 1) = (-55363079400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_6 : upperTriangleMatrix caseData .upper (1, 0) (3, 0) = (-132867226050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_7 : upperTriangleMatrix caseData .upper (1, 0) (3, 1) = (74041553115 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_8 : upperTriangleMatrix caseData .upper (1, 0) (4, 0) = (56339298300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_9 : upperTriangleMatrix caseData .upper (1, 0) (4, 1) = (9512797050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_10 : upperTriangleMatrix caseData .upper (1, 0) (5, 0) = (-1260746850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_11 : upperTriangleMatrix caseData .upper (1, 0) (5, 1) = (-30490422000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_12 : upperTriangleMatrix caseData .upper (1, 0) (6, 0) = (-829650750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_13 : upperTriangleMatrix caseData .upper (1, 0) (6, 1) = (5182886400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_14 : upperTriangleMatrix caseData .upper (1, 0) (7, 0) = (2995780350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_2_15 : upperTriangleMatrix caseData .upper (1, 0) (7, 1) = (-3731532900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_0 : upperTriangleMatrix caseData .upper (1, 1) (0, 0) = (177460931291 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_1 : upperTriangleMatrix caseData .upper (1, 1) (0, 1) = (-10636530750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_2 : upperTriangleMatrix caseData .upper (1, 1) (1, 0) = (-260812432391 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_3 : upperTriangleMatrix caseData .upper (1, 1) (1, 1) = (20005963413 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_4 : upperTriangleMatrix caseData .upper (1, 1) (2, 0) = (81281590200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_5 : upperTriangleMatrix caseData .upper (1, 1) (2, 1) = (-3900846600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_6 : upperTriangleMatrix caseData .upper (1, 1) (3, 0) = (-24791017800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_7 : upperTriangleMatrix caseData .upper (1, 1) (3, 1) = (-6430787700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_8 : upperTriangleMatrix caseData .upper (1, 1) (4, 0) = (31670559600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_9 : upperTriangleMatrix caseData .upper (1, 1) (4, 1) = (1688791500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_10 : upperTriangleMatrix caseData .upper (1, 1) (5, 0) = (-1961704500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_11 : upperTriangleMatrix caseData .upper (1, 1) (5, 1) = (-5422926900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_12 : upperTriangleMatrix caseData .upper (1, 1) (6, 0) = (-3420343350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_13 : upperTriangleMatrix caseData .upper (1, 1) (6, 1) = (6169540950 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_14 : upperTriangleMatrix caseData .upper (1, 1) (7, 0) = (545930250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_3_15 : upperTriangleMatrix caseData .upper (1, 1) (7, 1) = (-1495288500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_0 : upperTriangleMatrix caseData .upper (2, 0) (0, 0) = (-157107010200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_1 : upperTriangleMatrix caseData .upper (2, 0) (0, 1) = (33721362300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_2 : upperTriangleMatrix caseData .upper (2, 0) (1, 0) = (-10101601050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_3 : upperTriangleMatrix caseData .upper (2, 0) (1, 1) = (81281590200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_4 : upperTriangleMatrix caseData .upper (2, 0) (2, 0) = (313760979600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_5 : upperTriangleMatrix caseData .upper (2, 0) (2, 1) = (-109247311371 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_6 : upperTriangleMatrix caseData .upper (2, 0) (3, 0) = (-80336715450 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_7 : upperTriangleMatrix caseData .upper (2, 0) (3, 1) = (-61967640000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_8 : upperTriangleMatrix caseData .upper (2, 0) (4, 0) = (-112973188500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_9 : upperTriangleMatrix caseData .upper (2, 0) (4, 1) = (69846508500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_10 : upperTriangleMatrix caseData .upper (2, 0) (5, 0) = (47734785150 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_11 : upperTriangleMatrix caseData .upper (2, 0) (5, 1) = (6380743650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_12 : upperTriangleMatrix caseData .upper (2, 0) (6, 0) = (4199451000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_13 : upperTriangleMatrix caseData .upper (2, 0) (6, 1) = (-24373934550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_14 : upperTriangleMatrix caseData .upper (2, 0) (7, 0) = (-12393692550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_4_15 : upperTriangleMatrix caseData .upper (2, 0) (7, 1) = (2790529800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_0 : upperTriangleMatrix caseData .upper (2, 1) (0, 0) = (156018054471 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_1 : upperTriangleMatrix caseData .upper (2, 1) (0, 1) = (-158311675350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_2 : upperTriangleMatrix caseData .upper (2, 1) (1, 0) = (-55363079400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_3 : upperTriangleMatrix caseData .upper (2, 1) (1, 1) = (-3900846600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_4 : upperTriangleMatrix caseData .upper (2, 1) (2, 0) = (-109247311371 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_5 : upperTriangleMatrix caseData .upper (2, 1) (2, 1) = (172936649154 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_6 : upperTriangleMatrix caseData .upper (2, 1) (3, 0) = (6575555400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_7 : upperTriangleMatrix caseData .upper (2, 1) (3, 1) = (-12456455700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_8 : upperTriangleMatrix caseData .upper (2, 1) (4, 0) = (-20241259800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_9 : upperTriangleMatrix caseData .upper (2, 1) (4, 1) = (-5917044000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_10 : upperTriangleMatrix caseData .upper (2, 1) (5, 0) = (25677525000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_11 : upperTriangleMatrix caseData .upper (2, 1) (5, 1) = (1133220600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_12 : upperTriangleMatrix caseData .upper (2, 1) (6, 0) = (-928667100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_13 : upperTriangleMatrix caseData .upper (2, 1) (6, 1) = (-4022836950 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_14 : upperTriangleMatrix caseData .upper (2, 1) (7, 0) = (-3166504050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_5_15 : upperTriangleMatrix caseData .upper (2, 1) (7, 1) = (4939271100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_0 : upperTriangleMatrix caseData .upper (3, 0) (0, 0) = (58134814650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_1 : upperTriangleMatrix caseData .upper (3, 0) (0, 1) = (59921569233 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_2 : upperTriangleMatrix caseData .upper (3, 0) (1, 0) = (-132867226050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_3 : upperTriangleMatrix caseData .upper (3, 0) (1, 1) = (-24791017800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_4 : upperTriangleMatrix caseData .upper (3, 0) (2, 0) = (-80336715450 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_5 : upperTriangleMatrix caseData .upper (3, 0) (2, 1) = (6575555400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_6 : upperTriangleMatrix caseData .upper (3, 0) (3, 0) = (274736381100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_7 : upperTriangleMatrix caseData .upper (3, 0) (3, 1) = (-13379004750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_8 : upperTriangleMatrix caseData .upper (3, 0) (4, 0) = (-65271426750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_9 : upperTriangleMatrix caseData .upper (3, 0) (4, 1) = (-51517675650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_10 : upperTriangleMatrix caseData .upper (3, 0) (5, 0) = (-90796928400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_11 : upperTriangleMatrix caseData .upper (3, 0) (5, 1) = (55006517004 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_12 : upperTriangleMatrix caseData .upper (3, 0) (6, 0) = (34424047650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_13 : upperTriangleMatrix caseData .upper (3, 0) (6, 1) = (2243843850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_14 : upperTriangleMatrix caseData .upper (3, 0) (7, 0) = (10689057600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_6_15 : upperTriangleMatrix caseData .upper (3, 0) (7, 1) = (-16824568800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_0 : upperTriangleMatrix caseData .upper (3, 1) (0, 0) = (1109074500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_1 : upperTriangleMatrix caseData .upper (3, 1) (0, 1) = (1084542600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_2 : upperTriangleMatrix caseData .upper (3, 1) (1, 0) = (74041553115 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_3 : upperTriangleMatrix caseData .upper (3, 1) (1, 1) = (-6430787700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_4 : upperTriangleMatrix caseData .upper (3, 1) (2, 0) = (-61967640000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_5 : upperTriangleMatrix caseData .upper (3, 1) (2, 1) = (-12456455700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_6 : upperTriangleMatrix caseData .upper (3, 1) (3, 0) = (-13379004750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_7 : upperTriangleMatrix caseData .upper (3, 1) (3, 1) = (56452444974 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_8 : upperTriangleMatrix caseData .upper (3, 1) (4, 0) = (755879400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_9 : upperTriangleMatrix caseData .upper (3, 1) (4, 1) = (-11848643700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_10 : upperTriangleMatrix caseData .upper (3, 1) (5, 0) = (-18703629300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_11 : upperTriangleMatrix caseData .upper (3, 1) (5, 1) = (-5701919250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_12 : upperTriangleMatrix caseData .upper (3, 1) (6, 0) = (16303220400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_13 : upperTriangleMatrix caseData .upper (3, 1) (6, 1) = (865365300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_14 : upperTriangleMatrix caseData .upper (3, 1) (7, 0) = (5096972085 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_7_15 : upperTriangleMatrix caseData .upper (3, 1) (7, 1) = (-2546317200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_0 : upperTriangleMatrix caseData .upper (4, 0) (0, 0) = (-2311407600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_1 : upperTriangleMatrix caseData .upper (4, 0) (0, 1) = (-2319690150 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_2 : upperTriangleMatrix caseData .upper (4, 0) (1, 0) = (56339298300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_3 : upperTriangleMatrix caseData .upper (4, 0) (1, 1) = (31670559600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_4 : upperTriangleMatrix caseData .upper (4, 0) (2, 0) = (-112973188500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_5 : upperTriangleMatrix caseData .upper (4, 0) (2, 1) = (-20241259800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_6 : upperTriangleMatrix caseData .upper (4, 0) (3, 0) = (-65271426750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_7 : upperTriangleMatrix caseData .upper (4, 0) (3, 1) = (755879400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_8 : upperTriangleMatrix caseData .upper (4, 0) (4, 0) = (208661386800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_9 : upperTriangleMatrix caseData .upper (4, 0) (4, 1) = (-5378743800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_10 : upperTriangleMatrix caseData .upper (4, 0) (5, 0) = (-38124335700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_11 : upperTriangleMatrix caseData .upper (4, 0) (5, 1) = (-37042149204 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_12 : upperTriangleMatrix caseData .upper (4, 0) (6, 0) = (-55125987300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_13 : upperTriangleMatrix caseData .upper (4, 0) (6, 1) = (44158742148 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_14 : upperTriangleMatrix caseData .upper (4, 0) (7, 0) = (1136796900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_8_15 : upperTriangleMatrix caseData .upper (4, 0) (7, 1) = (27595350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_0 : upperTriangleMatrix caseData .upper (4, 1) (0, 0) = (-24984188250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_1 : upperTriangleMatrix caseData .upper (4, 1) (0, 1) = (-25667550300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_2 : upperTriangleMatrix caseData .upper (4, 1) (1, 0) = (9512797050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_3 : upperTriangleMatrix caseData .upper (4, 1) (1, 1) = (1688791500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_4 : upperTriangleMatrix caseData .upper (4, 1) (2, 0) = (69846508500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_5 : upperTriangleMatrix caseData .upper (4, 1) (2, 1) = (-5917044000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_6 : upperTriangleMatrix caseData .upper (4, 1) (3, 0) = (-51517675650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_7 : upperTriangleMatrix caseData .upper (4, 1) (3, 1) = (-11848643700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_8 : upperTriangleMatrix caseData .upper (4, 1) (4, 0) = (-5378743800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_9 : upperTriangleMatrix caseData .upper (4, 1) (4, 1) = (36765709698 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_10 : upperTriangleMatrix caseData .upper (4, 1) (5, 0) = (5581646550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_11 : upperTriangleMatrix caseData .upper (4, 1) (5, 1) = (-8738504400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_12 : upperTriangleMatrix caseData .upper (4, 1) (6, 0) = (-8658798150 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_13 : upperTriangleMatrix caseData .upper (4, 1) (6, 1) = (-4973523450 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_14 : upperTriangleMatrix caseData .upper (4, 1) (7, 0) = (348485250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_9_15 : upperTriangleMatrix caseData .upper (4, 1) (7, 1) = (199232100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_0 : upperTriangleMatrix caseData .upper (5, 0) (0, 0) = (941234400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_1 : upperTriangleMatrix caseData .upper (5, 0) (0, 1) = (277821900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_2 : upperTriangleMatrix caseData .upper (5, 0) (1, 0) = (-1260746850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_3 : upperTriangleMatrix caseData .upper (5, 0) (1, 1) = (-1961704500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_4 : upperTriangleMatrix caseData .upper (5, 0) (2, 0) = (47734785150 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_5 : upperTriangleMatrix caseData .upper (5, 0) (2, 1) = (25677525000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_6 : upperTriangleMatrix caseData .upper (5, 0) (3, 0) = (-90796928400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_7 : upperTriangleMatrix caseData .upper (5, 0) (3, 1) = (-18703629300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_8 : upperTriangleMatrix caseData .upper (5, 0) (4, 0) = (-38124335700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_9 : upperTriangleMatrix caseData .upper (5, 0) (4, 1) = (5581646550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_10 : upperTriangleMatrix caseData .upper (5, 0) (5, 0) = (136812338700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_11 : upperTriangleMatrix caseData .upper (5, 0) (5, 1) = (-1047710250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_12 : upperTriangleMatrix caseData .upper (5, 0) (6, 0) = (-47548807500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_13 : upperTriangleMatrix caseData .upper (5, 0) (6, 1) = (-26158569348 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_14 : upperTriangleMatrix caseData .upper (5, 0) (7, 0) = (-4977030000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_10_15 : upperTriangleMatrix caseData .upper (5, 0) (7, 1) = (32622004287 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_0 : upperTriangleMatrix caseData .upper (5, 1) (0, 0) = (5226392700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_1 : upperTriangleMatrix caseData .upper (5, 1) (0, 1) = (5966956800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_2 : upperTriangleMatrix caseData .upper (5, 1) (1, 0) = (-30490422000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_3 : upperTriangleMatrix caseData .upper (5, 1) (1, 1) = (-5422926900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_4 : upperTriangleMatrix caseData .upper (5, 1) (2, 0) = (6380743650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_5 : upperTriangleMatrix caseData .upper (5, 1) (2, 1) = (1133220600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_6 : upperTriangleMatrix caseData .upper (5, 1) (3, 0) = (55006517004 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_7 : upperTriangleMatrix caseData .upper (5, 1) (3, 1) = (-5701919250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_8 : upperTriangleMatrix caseData .upper (5, 1) (4, 0) = (-37042149204 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_9 : upperTriangleMatrix caseData .upper (5, 1) (4, 1) = (-8738504400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_10 : upperTriangleMatrix caseData .upper (5, 1) (5, 0) = (-1047710250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_11 : upperTriangleMatrix caseData .upper (5, 1) (5, 1) = (27028899999 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_12 : upperTriangleMatrix caseData .upper (5, 1) (6, 0) = (2647702950 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_13 : upperTriangleMatrix caseData .upper (5, 1) (6, 1) = (-8425934550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_14 : upperTriangleMatrix caseData .upper (5, 1) (7, 0) = (-1739389050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_11_15 : upperTriangleMatrix caseData .upper (5, 1) (7, 1) = (-3067008000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_0 : upperTriangleMatrix caseData .upper (6, 0) (0, 0) = (2526766050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_1 : upperTriangleMatrix caseData .upper (6, 0) (0, 1) = (998953200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_2 : upperTriangleMatrix caseData .upper (6, 0) (1, 0) = (-829650750 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_3 : upperTriangleMatrix caseData .upper (6, 0) (1, 1) = (-3420343350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_4 : upperTriangleMatrix caseData .upper (6, 0) (2, 0) = (4199451000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_5 : upperTriangleMatrix caseData .upper (6, 0) (2, 1) = (-928667100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_6 : upperTriangleMatrix caseData .upper (6, 0) (3, 0) = (34424047650 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_7 : upperTriangleMatrix caseData .upper (6, 0) (3, 1) = (16303220400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_8 : upperTriangleMatrix caseData .upper (6, 0) (4, 0) = (-55125987300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_9 : upperTriangleMatrix caseData .upper (6, 0) (4, 1) = (-8658798150 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_10 : upperTriangleMatrix caseData .upper (6, 0) (5, 0) = (-47548807500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_11 : upperTriangleMatrix caseData .upper (6, 0) (5, 1) = (2647702950 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_12 : upperTriangleMatrix caseData .upper (6, 0) (6, 0) = (79281987900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_13 : upperTriangleMatrix caseData .upper (6, 0) (6, 1) = (4408604850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_14 : upperTriangleMatrix caseData .upper (6, 0) (7, 0) = (-8134679700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_12_15 : upperTriangleMatrix caseData .upper (6, 0) (7, 1) = (-18520417287 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_0 : upperTriangleMatrix caseData .upper (6, 1) (0, 0) = (-3259164900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_1 : upperTriangleMatrix caseData .upper (6, 1) (0, 1) = (-3295827000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_2 : upperTriangleMatrix caseData .upper (6, 1) (1, 0) = (5182886400 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_3 : upperTriangleMatrix caseData .upper (6, 1) (1, 1) = (6169540950 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_4 : upperTriangleMatrix caseData .upper (6, 1) (2, 0) = (-24373934550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_5 : upperTriangleMatrix caseData .upper (6, 1) (2, 1) = (-4022836950 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_6 : upperTriangleMatrix caseData .upper (6, 1) (3, 0) = (2243843850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_7 : upperTriangleMatrix caseData .upper (6, 1) (3, 1) = (865365300 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_8 : upperTriangleMatrix caseData .upper (6, 1) (4, 0) = (44158742148 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_9 : upperTriangleMatrix caseData .upper (6, 1) (4, 1) = (-4973523450 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_10 : upperTriangleMatrix caseData .upper (6, 1) (5, 0) = (-26158569348 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_11 : upperTriangleMatrix caseData .upper (6, 1) (5, 1) = (-8425934550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_12 : upperTriangleMatrix caseData .upper (6, 1) (6, 0) = (4408604850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_13 : upperTriangleMatrix caseData .upper (6, 1) (6, 1) = (18178748478 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_14 : upperTriangleMatrix caseData .upper (6, 1) (7, 0) = (-1607852700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_13_15 : upperTriangleMatrix caseData .upper (6, 1) (7, 1) = (-6456411450 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_0 : upperTriangleMatrix caseData .upper (7, 0) (0, 0) = (1474975200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_1 : upperTriangleMatrix caseData .upper (7, 0) (0, 1) = (1506985200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_2 : upperTriangleMatrix caseData .upper (7, 0) (1, 0) = (2995780350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_3 : upperTriangleMatrix caseData .upper (7, 0) (1, 1) = (545930250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_4 : upperTriangleMatrix caseData .upper (7, 0) (2, 0) = (-12393692550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_5 : upperTriangleMatrix caseData .upper (7, 0) (2, 1) = (-3166504050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_6 : upperTriangleMatrix caseData .upper (7, 0) (3, 0) = (10689057600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_7 : upperTriangleMatrix caseData .upper (7, 0) (3, 1) = (5096972085 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_8 : upperTriangleMatrix caseData .upper (7, 0) (4, 0) = (1136796900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_9 : upperTriangleMatrix caseData .upper (7, 0) (4, 1) = (348485250 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_10 : upperTriangleMatrix caseData .upper (7, 0) (5, 0) = (-4977030000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_11 : upperTriangleMatrix caseData .upper (7, 0) (5, 1) = (-1739389050 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_12 : upperTriangleMatrix caseData .upper (7, 0) (6, 0) = (-8134679700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_13 : upperTriangleMatrix caseData .upper (7, 0) (6, 1) = (-1607852700 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_14 : upperTriangleMatrix caseData .upper (7, 0) (7, 0) = (9300907350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_14_15 : upperTriangleMatrix caseData .upper (7, 0) (7, 1) = (699860550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_0 : upperTriangleMatrix caseData .upper (7, 1) (0, 0) = (4377027600 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_1 : upperTriangleMatrix caseData .upper (7, 1) (0, 1) = (345869850 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_2 : upperTriangleMatrix caseData .upper (7, 1) (1, 0) = (-3731532900 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_3 : upperTriangleMatrix caseData .upper (7, 1) (1, 1) = (-1495288500 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_4 : upperTriangleMatrix caseData .upper (7, 1) (2, 0) = (2790529800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_5 : upperTriangleMatrix caseData .upper (7, 1) (2, 1) = (4939271100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_6 : upperTriangleMatrix caseData .upper (7, 1) (3, 0) = (-16824568800 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_7 : upperTriangleMatrix caseData .upper (7, 1) (3, 1) = (-2546317200 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_8 : upperTriangleMatrix caseData .upper (7, 1) (4, 0) = (27595350 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_9 : upperTriangleMatrix caseData .upper (7, 1) (4, 1) = (199232100 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_10 : upperTriangleMatrix caseData .upper (7, 1) (5, 0) = (32622004287 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_11 : upperTriangleMatrix caseData .upper (7, 1) (5, 1) = (-3067008000 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_12 : upperTriangleMatrix caseData .upper (7, 1) (6, 0) = (-18520417287 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_13 : upperTriangleMatrix caseData .upper (7, 1) (6, 1) = (-6456411450 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_14 : upperTriangleMatrix caseData .upper (7, 1) (7, 0) = (699860550 / 1500000000000) := rfl
@[simp] theorem lookup_case_A_15_15 : upperTriangleMatrix caseData .upper (7, 1) (7, 1) = (14440024737 / 1500000000000) := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
