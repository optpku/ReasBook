module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.SupplyRow7
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096
-- Each theorem checks a finite rational entry after symbolic sparse expansion.
set_option maxHeartbeats 2000000

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
open MatrixAssembly

theorem supply_8_0 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (0, 0) = literalQ (4, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_8, lookup_literalQ_8_0] using supply_0_8

theorem supply_8_1 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (0, 1) = literalQ (4, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_8, lookup_literalQ_8_1] using supply_1_8

theorem supply_8_2 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (1, 0) = literalQ (4, 0) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_8, lookup_literalQ_8_2] using supply_2_8

theorem supply_8_3 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (1, 1) = literalQ (4, 0) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_8, lookup_literalQ_8_3] using supply_3_8

theorem supply_8_4 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (2, 0) = literalQ (4, 0) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_8, lookup_literalQ_8_4] using supply_4_8

theorem supply_8_5 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (2, 1) = literalQ (4, 0) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_8, lookup_literalQ_8_5] using supply_5_8

theorem supply_8_6 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (3, 0) = literalQ (4, 0) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_8, lookup_literalQ_8_6] using supply_6_8

theorem supply_8_7 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (3, 1) = literalQ (4, 0) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_8, lookup_literalQ_8_7] using supply_7_8

theorem supply_8_8 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (4, 0) = literalQ (4, 0) (4, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_9 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (4, 1) = literalQ (4, 0) (4, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_10 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (5, 0) = literalQ (4, 0) (5, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_11 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (5, 1) = literalQ (4, 0) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_12 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (6, 0) = literalQ (4, 0) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_13 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (6, 1) = literalQ (4, 0) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_14 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (7, 0) = literalQ (4, 0) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_15 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (7, 1) = literalQ (4, 0) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_16 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (8, 0) = literalQ (4, 0) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_17 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (8, 1) = literalQ (4, 0) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_18 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (9, 0) = literalQ (4, 0) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_8_19 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) (9, 1) = literalQ (4, 0) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_8 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (4, 0) j = literalQ (4, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_8_0
  · exact supply_8_1
  · exact supply_8_2
  · exact supply_8_3
  · exact supply_8_4
  · exact supply_8_5
  · exact supply_8_6
  · exact supply_8_7
  · exact supply_8_8
  · exact supply_8_9
  · exact supply_8_10
  · exact supply_8_11
  · exact supply_8_12
  · exact supply_8_13
  · exact supply_8_14
  · exact supply_8_15
  · exact supply_8_16
  · exact supply_8_17
  · exact supply_8_18
  · exact supply_8_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
