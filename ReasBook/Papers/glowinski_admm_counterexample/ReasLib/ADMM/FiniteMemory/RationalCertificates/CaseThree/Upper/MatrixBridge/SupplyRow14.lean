module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.SupplyRow13
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096
-- Each theorem checks a finite rational entry after symbolic sparse expansion.
set_option maxHeartbeats 2000000

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
open MatrixAssembly

theorem supply_14_0 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (0, 0) = literalQ (7, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_14, lookup_literalQ_14_0] using supply_0_14

theorem supply_14_1 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (0, 1) = literalQ (7, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_14, lookup_literalQ_14_1] using supply_1_14

theorem supply_14_2 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (1, 0) = literalQ (7, 0) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_14, lookup_literalQ_14_2] using supply_2_14

theorem supply_14_3 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (1, 1) = literalQ (7, 0) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_14, lookup_literalQ_14_3] using supply_3_14

theorem supply_14_4 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (2, 0) = literalQ (7, 0) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_14, lookup_literalQ_14_4] using supply_4_14

theorem supply_14_5 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (2, 1) = literalQ (7, 0) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_14, lookup_literalQ_14_5] using supply_5_14

theorem supply_14_6 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (3, 0) = literalQ (7, 0) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_14, lookup_literalQ_14_6] using supply_6_14

theorem supply_14_7 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (3, 1) = literalQ (7, 0) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_14, lookup_literalQ_14_7] using supply_7_14

theorem supply_14_8 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (4, 0) = literalQ (7, 0) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_14, lookup_literalQ_14_8] using supply_8_14

theorem supply_14_9 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (4, 1) = literalQ (7, 0) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_14, lookup_literalQ_14_9] using supply_9_14

theorem supply_14_10 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (5, 0) = literalQ (7, 0) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_14, lookup_literalQ_14_10] using supply_10_14

theorem supply_14_11 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (5, 1) = literalQ (7, 0) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_14, lookup_literalQ_14_11] using supply_11_14

theorem supply_14_12 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (6, 0) = literalQ (7, 0) (6, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_12_14, lookup_literalQ_14_12] using supply_12_14

theorem supply_14_13 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (6, 1) = literalQ (7, 0) (6, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_13_14, lookup_literalQ_14_13] using supply_13_14

theorem supply_14_14 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (7, 0) = literalQ (7, 0) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_14_15 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (7, 1) = literalQ (7, 0) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_14_16 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (8, 0) = literalQ (7, 0) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_14_17 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (8, 1) = literalQ (7, 0) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_14_18 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (9, 0) = literalQ (7, 0) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_14_19 : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) (9, 1) = literalQ (7, 0) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_14 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (7, 0) j = literalQ (7, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_14_0
  · exact supply_14_1
  · exact supply_14_2
  · exact supply_14_3
  · exact supply_14_4
  · exact supply_14_5
  · exact supply_14_6
  · exact supply_14_7
  · exact supply_14_8
  · exact supply_14_9
  · exact supply_14_10
  · exact supply_14_11
  · exact supply_14_12
  · exact supply_14_13
  · exact supply_14_14
  · exact supply_14_15
  · exact supply_14_16
  · exact supply_14_17
  · exact supply_14_18
  · exact supply_14_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
