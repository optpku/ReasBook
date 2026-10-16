module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.SupplyRow14
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

theorem supply_15_0 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (0, 0) = literalQ (7, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_15, lookup_literalQ_15_0] using supply_0_15

theorem supply_15_1 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (0, 1) = literalQ (7, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_15, lookup_literalQ_15_1] using supply_1_15

theorem supply_15_2 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (1, 0) = literalQ (7, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_15, lookup_literalQ_15_2] using supply_2_15

theorem supply_15_3 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (1, 1) = literalQ (7, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_15, lookup_literalQ_15_3] using supply_3_15

theorem supply_15_4 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (2, 0) = literalQ (7, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_15, lookup_literalQ_15_4] using supply_4_15

theorem supply_15_5 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (2, 1) = literalQ (7, 1) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_15, lookup_literalQ_15_5] using supply_5_15

theorem supply_15_6 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (3, 0) = literalQ (7, 1) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_15, lookup_literalQ_15_6] using supply_6_15

theorem supply_15_7 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (3, 1) = literalQ (7, 1) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_15, lookup_literalQ_15_7] using supply_7_15

theorem supply_15_8 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (4, 0) = literalQ (7, 1) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_15, lookup_literalQ_15_8] using supply_8_15

theorem supply_15_9 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (4, 1) = literalQ (7, 1) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_15, lookup_literalQ_15_9] using supply_9_15

theorem supply_15_10 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (5, 0) = literalQ (7, 1) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_15, lookup_literalQ_15_10] using supply_10_15

theorem supply_15_11 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (5, 1) = literalQ (7, 1) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_15, lookup_literalQ_15_11] using supply_11_15

theorem supply_15_12 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (6, 0) = literalQ (7, 1) (6, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_12_15, lookup_literalQ_15_12] using supply_12_15

theorem supply_15_13 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (6, 1) = literalQ (7, 1) (6, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_13_15, lookup_literalQ_15_13] using supply_13_15

theorem supply_15_14 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (7, 0) = literalQ (7, 1) (7, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_14_15, lookup_literalQ_15_14] using supply_14_15

theorem supply_15_15 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (7, 1) = literalQ (7, 1) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_15_16 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (8, 0) = literalQ (7, 1) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_15_17 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (8, 1) = literalQ (7, 1) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_15_18 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (9, 0) = literalQ (7, 1) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_15_19 : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) (9, 1) = literalQ (7, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_15 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (7, 1) j = literalQ (7, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_15_0
  · exact supply_15_1
  · exact supply_15_2
  · exact supply_15_3
  · exact supply_15_4
  · exact supply_15_5
  · exact supply_15_6
  · exact supply_15_7
  · exact supply_15_8
  · exact supply_15_9
  · exact supply_15_10
  · exact supply_15_11
  · exact supply_15_12
  · exact supply_15_13
  · exact supply_15_14
  · exact supply_15_15
  · exact supply_15_16
  · exact supply_15_17
  · exact supply_15_18
  · exact supply_15_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
