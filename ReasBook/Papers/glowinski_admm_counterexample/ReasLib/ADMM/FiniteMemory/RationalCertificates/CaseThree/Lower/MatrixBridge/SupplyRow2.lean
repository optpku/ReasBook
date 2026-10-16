module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.SupplyRow1
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096
-- Each theorem checks a finite rational entry after symbolic sparse expansion.
set_option maxHeartbeats 2000000

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
open MatrixAssembly

theorem supply_2_0 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (0, 0) = literalQ (1, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_2, lookup_literalQ_2_0] using supply_0_2

theorem supply_2_1 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (0, 1) = literalQ (1, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_2, lookup_literalQ_2_1] using supply_1_2

theorem supply_2_2 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (1, 0) = literalQ (1, 0) (1, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_3 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (1, 1) = literalQ (1, 0) (1, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_4 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (2, 0) = literalQ (1, 0) (2, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_5 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (2, 1) = literalQ (1, 0) (2, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_6 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (3, 0) = literalQ (1, 0) (3, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_7 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (3, 1) = literalQ (1, 0) (3, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_8 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (4, 0) = literalQ (1, 0) (4, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_9 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (4, 1) = literalQ (1, 0) (4, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_10 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (5, 0) = literalQ (1, 0) (5, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_11 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (5, 1) = literalQ (1, 0) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_12 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (6, 0) = literalQ (1, 0) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_13 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (6, 1) = literalQ (1, 0) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_14 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (7, 0) = literalQ (1, 0) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_15 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (7, 1) = literalQ (1, 0) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_16 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (8, 0) = literalQ (1, 0) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_17 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (8, 1) = literalQ (1, 0) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_18 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (9, 0) = literalQ (1, 0) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_2_19 : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) (9, 1) = literalQ (1, 0) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_2 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (1, 0) j = literalQ (1, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_2_0
  · exact supply_2_1
  · exact supply_2_2
  · exact supply_2_3
  · exact supply_2_4
  · exact supply_2_5
  · exact supply_2_6
  · exact supply_2_7
  · exact supply_2_8
  · exact supply_2_9
  · exact supply_2_10
  · exact supply_2_11
  · exact supply_2_12
  · exact supply_2_13
  · exact supply_2_14
  · exact supply_2_15
  · exact supply_2_16
  · exact supply_2_17
  · exact supply_2_18
  · exact supply_2_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
