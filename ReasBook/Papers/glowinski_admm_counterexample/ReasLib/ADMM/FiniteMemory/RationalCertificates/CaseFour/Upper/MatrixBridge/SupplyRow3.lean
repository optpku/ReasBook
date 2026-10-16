module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.SupplyRow2
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096
-- Each theorem checks a finite rational entry after symbolic sparse expansion.
set_option maxHeartbeats 2000000

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
open MatrixAssembly

theorem supply_3_0 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (0, 0) = literalQ (1, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_3, lookup_literalQ_3_0] using supply_0_3

theorem supply_3_1 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (0, 1) = literalQ (1, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_3, lookup_literalQ_3_1] using supply_1_3

theorem supply_3_2 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (1, 0) = literalQ (1, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_3, lookup_literalQ_3_2] using supply_2_3

theorem supply_3_3 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (1, 1) = literalQ (1, 1) (1, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_4 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (2, 0) = literalQ (1, 1) (2, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_5 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (2, 1) = literalQ (1, 1) (2, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_6 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (3, 0) = literalQ (1, 1) (3, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_7 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (3, 1) = literalQ (1, 1) (3, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_8 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (4, 0) = literalQ (1, 1) (4, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_9 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (4, 1) = literalQ (1, 1) (4, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_10 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (5, 0) = literalQ (1, 1) (5, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_11 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (5, 1) = literalQ (1, 1) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_12 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (6, 0) = literalQ (1, 1) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_13 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (6, 1) = literalQ (1, 1) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_14 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (7, 0) = literalQ (1, 1) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_15 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (7, 1) = literalQ (1, 1) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_16 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (8, 0) = literalQ (1, 1) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_17 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (8, 1) = literalQ (1, 1) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_18 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (9, 0) = literalQ (1, 1) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_3_19 : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) (9, 1) = literalQ (1, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_3 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (1, 1) j = literalQ (1, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_3_0
  · exact supply_3_1
  · exact supply_3_2
  · exact supply_3_3
  · exact supply_3_4
  · exact supply_3_5
  · exact supply_3_6
  · exact supply_3_7
  · exact supply_3_8
  · exact supply_3_9
  · exact supply_3_10
  · exact supply_3_11
  · exact supply_3_12
  · exact supply_3_13
  · exact supply_3_14
  · exact supply_3_15
  · exact supply_3_16
  · exact supply_3_17
  · exact supply_3_18
  · exact supply_3_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
