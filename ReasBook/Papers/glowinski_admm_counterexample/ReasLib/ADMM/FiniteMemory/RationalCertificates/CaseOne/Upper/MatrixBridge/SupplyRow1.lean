module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.SupplyRow0
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096
-- Each theorem checks a finite rational entry after symbolic sparse expansion.
set_option maxHeartbeats 2000000

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
open MatrixAssembly

theorem supply_1_0 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (0, 0) = literalQ (0, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_1, lookup_literalQ_1_0] using supply_0_1

theorem supply_1_1 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (0, 1) = literalQ (0, 1) (0, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_1_2 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (1, 0) = literalQ (0, 1) (1, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_1_3 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (1, 1) = literalQ (0, 1) (1, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_1_4 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (2, 0) = literalQ (0, 1) (2, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_1_5 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (2, 1) = literalQ (0, 1) (2, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_1_6 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (3, 0) = literalQ (0, 1) (3, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_1_7 : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) (3, 1) = literalQ (0, 1) (3, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_1 (j : Fin 4 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (0, 1) j = literalQ (0, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_1_0
  · exact supply_1_1
  · exact supply_1_2
  · exact supply_1_3
  · exact supply_1_4
  · exact supply_1_5
  · exact supply_1_6
  · exact supply_1_7

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
