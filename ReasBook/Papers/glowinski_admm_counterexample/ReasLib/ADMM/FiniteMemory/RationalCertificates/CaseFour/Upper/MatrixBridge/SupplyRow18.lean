module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.SupplyRow17
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

theorem supply_18_0 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (0, 0) = literalQ (9, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_18, lookup_literalQ_18_0] using supply_0_18

theorem supply_18_1 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (0, 1) = literalQ (9, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_18, lookup_literalQ_18_1] using supply_1_18

theorem supply_18_2 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (1, 0) = literalQ (9, 0) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_18, lookup_literalQ_18_2] using supply_2_18

theorem supply_18_3 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (1, 1) = literalQ (9, 0) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_18, lookup_literalQ_18_3] using supply_3_18

theorem supply_18_4 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (2, 0) = literalQ (9, 0) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_18, lookup_literalQ_18_4] using supply_4_18

theorem supply_18_5 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (2, 1) = literalQ (9, 0) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_18, lookup_literalQ_18_5] using supply_5_18

theorem supply_18_6 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (3, 0) = literalQ (9, 0) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_18, lookup_literalQ_18_6] using supply_6_18

theorem supply_18_7 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (3, 1) = literalQ (9, 0) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_18, lookup_literalQ_18_7] using supply_7_18

theorem supply_18_8 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (4, 0) = literalQ (9, 0) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_18, lookup_literalQ_18_8] using supply_8_18

theorem supply_18_9 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (4, 1) = literalQ (9, 0) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_18, lookup_literalQ_18_9] using supply_9_18

theorem supply_18_10 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (5, 0) = literalQ (9, 0) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_18, lookup_literalQ_18_10] using supply_10_18

theorem supply_18_11 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (5, 1) = literalQ (9, 0) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_18, lookup_literalQ_18_11] using supply_11_18

theorem supply_18_12 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (6, 0) = literalQ (9, 0) (6, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_12_18, lookup_literalQ_18_12] using supply_12_18

theorem supply_18_13 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (6, 1) = literalQ (9, 0) (6, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_13_18, lookup_literalQ_18_13] using supply_13_18

theorem supply_18_14 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (7, 0) = literalQ (9, 0) (7, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_14_18, lookup_literalQ_18_14] using supply_14_18

theorem supply_18_15 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (7, 1) = literalQ (9, 0) (7, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_15_18, lookup_literalQ_18_15] using supply_15_18

theorem supply_18_16 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (8, 0) = literalQ (9, 0) (8, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_16_18, lookup_literalQ_18_16] using supply_16_18

theorem supply_18_17 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (8, 1) = literalQ (9, 0) (8, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_17_18, lookup_literalQ_18_17] using supply_17_18

theorem supply_18_18 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (9, 0) = literalQ (9, 0) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_18_19 : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) (9, 1) = literalQ (9, 0) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_18 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (9, 0) j = literalQ (9, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_18_0
  · exact supply_18_1
  · exact supply_18_2
  · exact supply_18_3
  · exact supply_18_4
  · exact supply_18_5
  · exact supply_18_6
  · exact supply_18_7
  · exact supply_18_8
  · exact supply_18_9
  · exact supply_18_10
  · exact supply_18_11
  · exact supply_18_12
  · exact supply_18_13
  · exact supply_18_14
  · exact supply_18_15
  · exact supply_18_16
  · exact supply_18_17
  · exact supply_18_18
  · exact supply_18_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
