module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.SupplyRow16
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

theorem supply_17_0 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (0, 0) = literalQ (8, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_17, lookup_literalQ_17_0] using supply_0_17

theorem supply_17_1 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (0, 1) = literalQ (8, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_17, lookup_literalQ_17_1] using supply_1_17

theorem supply_17_2 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (1, 0) = literalQ (8, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_17, lookup_literalQ_17_2] using supply_2_17

theorem supply_17_3 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (1, 1) = literalQ (8, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_17, lookup_literalQ_17_3] using supply_3_17

theorem supply_17_4 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (2, 0) = literalQ (8, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_17, lookup_literalQ_17_4] using supply_4_17

theorem supply_17_5 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (2, 1) = literalQ (8, 1) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_17, lookup_literalQ_17_5] using supply_5_17

theorem supply_17_6 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (3, 0) = literalQ (8, 1) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_17, lookup_literalQ_17_6] using supply_6_17

theorem supply_17_7 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (3, 1) = literalQ (8, 1) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_17, lookup_literalQ_17_7] using supply_7_17

theorem supply_17_8 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (4, 0) = literalQ (8, 1) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_17, lookup_literalQ_17_8] using supply_8_17

theorem supply_17_9 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (4, 1) = literalQ (8, 1) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_17, lookup_literalQ_17_9] using supply_9_17

theorem supply_17_10 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (5, 0) = literalQ (8, 1) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_17, lookup_literalQ_17_10] using supply_10_17

theorem supply_17_11 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (5, 1) = literalQ (8, 1) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_17, lookup_literalQ_17_11] using supply_11_17

theorem supply_17_12 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (6, 0) = literalQ (8, 1) (6, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_12_17, lookup_literalQ_17_12] using supply_12_17

theorem supply_17_13 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (6, 1) = literalQ (8, 1) (6, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_13_17, lookup_literalQ_17_13] using supply_13_17

theorem supply_17_14 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (7, 0) = literalQ (8, 1) (7, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_14_17, lookup_literalQ_17_14] using supply_14_17

theorem supply_17_15 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (7, 1) = literalQ (8, 1) (7, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_15_17, lookup_literalQ_17_15] using supply_15_17

theorem supply_17_16 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (8, 0) = literalQ (8, 1) (8, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_16_17, lookup_literalQ_17_16] using supply_16_17

theorem supply_17_17 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (8, 1) = literalQ (8, 1) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_17_18 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (9, 0) = literalQ (8, 1) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_17_19 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) (9, 1) = literalQ (8, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_17 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (8, 1) j = literalQ (8, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_17_0
  · exact supply_17_1
  · exact supply_17_2
  · exact supply_17_3
  · exact supply_17_4
  · exact supply_17_5
  · exact supply_17_6
  · exact supply_17_7
  · exact supply_17_8
  · exact supply_17_9
  · exact supply_17_10
  · exact supply_17_11
  · exact supply_17_12
  · exact supply_17_13
  · exact supply_17_14
  · exact supply_17_15
  · exact supply_17_16
  · exact supply_17_17
  · exact supply_17_18
  · exact supply_17_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
