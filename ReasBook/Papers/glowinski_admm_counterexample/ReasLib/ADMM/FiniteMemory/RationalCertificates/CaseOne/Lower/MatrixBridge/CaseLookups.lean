module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.Data

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge

@[simp] theorem lookup_case_gammaLower : caseData.gammaLower = (3 / 2) := rfl
@[simp] theorem lookup_case_gammaUpper : caseData.gammaUpper = (17 / 10) := rfl
@[simp] theorem lookup_case_omega : caseData.omega = (7009 / 500000) := rfl
@[simp] theorem lookup_case_epsilon : caseData.epsilon = (1 / 1000) := rfl
@[simp] theorem lookup_case_zeta : caseData.zeta = (1 / 1000) := rfl
@[simp] theorem lookup_case_endpoint : endpointGamma caseData .lower = (3 / 2) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_0 : lagMinusValue caseData .F 0 = (0 / 1000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_F_1 : lagMinusValue caseData .F 1 = (109315 / 1000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_0 : lagPlusValue caseData .F 0 = (62972 / 1000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_F_1 : lagPlusValue caseData .F 1 = (81293 / 1000000) := rfl
@[simp] theorem lookup_case_packed_F_0_0 : packedMuValue caseData .F none 0 = (394093 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_0_1 : packedMuValue caseData .F none 1 = (301545 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_1_0 : packedMuValue caseData .F (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_F_1_1 : packedMuValue caseData .F (some 0) 1 = (2091255 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_2_0 : packedMuValue caseData .F (some 1) 0 = (5193879 / 100000000) := rfl
@[simp] theorem lookup_case_packed_F_2_1 : packedMuValue caseData .F (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_lagMinusValue_J_0 : lagMinusValue caseData .J 0 = (307870 / 1000000) := rfl
@[simp] theorem lookup_case_lagMinusValue_J_1 : lagMinusValue caseData .J 1 = (36578 / 1000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_0 : lagPlusValue caseData .J 0 = (387954 / 1000000) := rfl
@[simp] theorem lookup_case_lagPlusValue_J_1 : lagPlusValue caseData .J 1 = (0 / 1000000) := rfl
@[simp] theorem lookup_case_packed_J_0_0 : packedMuValue caseData .J none 0 = (375556 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_0_1 : packedMuValue caseData .J none 1 = (319968 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_1_0 : packedMuValue caseData .J (some 0) 0 = 0 := rfl
@[simp] theorem lookup_case_packed_J_1_1 : packedMuValue caseData .J (some 0) 1 = (2742418 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_2_0 : packedMuValue caseData .J (some 1) 0 = (6719495 / 100000000) := rfl
@[simp] theorem lookup_case_packed_J_2_1 : packedMuValue caseData .J (some 1) 1 = 0 := rfl
@[simp] theorem lookup_case_A_0_0 : upperTriangleMatrix caseData .lower (0, 0) (0, 0) = (8350767 / 100000000) := rfl
@[simp] theorem lookup_case_A_0_1 : upperTriangleMatrix caseData .lower (0, 0) (0, 1) = (-8831839 / 100000000) := rfl
@[simp] theorem lookup_case_A_0_2 : upperTriangleMatrix caseData .lower (0, 0) (1, 0) = (-5429368 / 100000000) := rfl
@[simp] theorem lookup_case_A_0_3 : upperTriangleMatrix caseData .lower (0, 0) (1, 1) = (7013879 / 100000000) := rfl
@[simp] theorem lookup_case_A_1_0 : upperTriangleMatrix caseData .lower (0, 1) (0, 0) = (-8831839 / 100000000) := rfl
@[simp] theorem lookup_case_A_1_1 : upperTriangleMatrix caseData .lower (0, 1) (0, 1) = (8422643 / 100000000) := rfl
@[simp] theorem lookup_case_A_1_2 : upperTriangleMatrix caseData .lower (0, 1) (1, 0) = (8469609 / 100000000) := rfl
@[simp] theorem lookup_case_A_1_3 : upperTriangleMatrix caseData .lower (0, 1) (1, 1) = (-2429443 / 100000000) := rfl
@[simp] theorem lookup_case_A_2_0 : upperTriangleMatrix caseData .lower (1, 0) (0, 0) = (-5429368 / 100000000) := rfl
@[simp] theorem lookup_case_A_2_1 : upperTriangleMatrix caseData .lower (1, 0) (0, 1) = (8469609 / 100000000) := rfl
@[simp] theorem lookup_case_A_2_2 : upperTriangleMatrix caseData .lower (1, 0) (1, 0) = (9089044 / 100000000) := rfl
@[simp] theorem lookup_case_A_2_3 : upperTriangleMatrix caseData .lower (1, 0) (1, 1) = (-6820664 / 100000000) := rfl
@[simp] theorem lookup_case_A_3_0 : upperTriangleMatrix caseData .lower (1, 1) (0, 0) = (7013879 / 100000000) := rfl
@[simp] theorem lookup_case_A_3_1 : upperTriangleMatrix caseData .lower (1, 1) (0, 1) = (-2429443 / 100000000) := rfl
@[simp] theorem lookup_case_A_3_2 : upperTriangleMatrix caseData .lower (1, 1) (1, 0) = (-6820664 / 100000000) := rfl
@[simp] theorem lookup_case_A_3_3 : upperTriangleMatrix caseData .lower (1, 1) (1, 1) = (10436193 / 100000000) := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
