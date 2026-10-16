module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Upper.MatrixBridge.SupplyRow5
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096
-- Each theorem checks a finite rational entry after symbolic sparse expansion.
set_option maxHeartbeats 2000000

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Upper.MatrixBridge
open MatrixAssembly

theorem supply_6_0 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (0, 0) = literalQ (3, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_6, lookup_literalQ_6_0] using supply_0_6

theorem supply_6_1 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (0, 1) = literalQ (3, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_6, lookup_literalQ_6_1] using supply_1_6

theorem supply_6_2 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (1, 0) = literalQ (3, 0) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_6, lookup_literalQ_6_2] using supply_2_6

theorem supply_6_3 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (1, 1) = literalQ (3, 0) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_6, lookup_literalQ_6_3] using supply_3_6

theorem supply_6_4 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (2, 0) = literalQ (3, 0) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_6, lookup_literalQ_6_4] using supply_4_6

theorem supply_6_5 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (2, 1) = literalQ (3, 0) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_6, lookup_literalQ_6_5] using supply_5_6

theorem supply_6_6 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (3, 0) = literalQ (3, 0) (3, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_7 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (3, 1) = literalQ (3, 0) (3, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_8 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (4, 0) = literalQ (3, 0) (4, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_9 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (4, 1) = literalQ (3, 0) (4, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_10 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (5, 0) = literalQ (3, 0) (5, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_11 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (5, 1) = literalQ (3, 0) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_12 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (6, 0) = literalQ (3, 0) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_13 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (6, 1) = literalQ (3, 0) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_14 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (7, 0) = literalQ (3, 0) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_6_15 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) (7, 1) = literalQ (3, 0) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_6 (j : Fin 8 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (3, 0) j = literalQ (3, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_6_0
  · exact supply_6_1
  · exact supply_6_2
  · exact supply_6_3
  · exact supply_6_4
  · exact supply_6_5
  · exact supply_6_6
  · exact supply_6_7
  · exact supply_6_8
  · exact supply_6_9
  · exact supply_6_10
  · exact supply_6_11
  · exact supply_6_12
  · exact supply_6_13
  · exact supply_6_14
  · exact supply_6_15

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Upper.MatrixBridge
