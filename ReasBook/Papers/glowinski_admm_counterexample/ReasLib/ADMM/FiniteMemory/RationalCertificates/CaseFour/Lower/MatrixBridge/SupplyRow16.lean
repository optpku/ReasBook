module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.SupplyRow15
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

theorem supply_16_0 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (0, 0) = literalQ (8, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_16, lookup_literalQ_16_0] using supply_0_16

theorem supply_16_1 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (0, 1) = literalQ (8, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_16, lookup_literalQ_16_1] using supply_1_16

theorem supply_16_2 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (1, 0) = literalQ (8, 0) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_16, lookup_literalQ_16_2] using supply_2_16

theorem supply_16_3 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (1, 1) = literalQ (8, 0) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_16, lookup_literalQ_16_3] using supply_3_16

theorem supply_16_4 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (2, 0) = literalQ (8, 0) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_16, lookup_literalQ_16_4] using supply_4_16

theorem supply_16_5 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (2, 1) = literalQ (8, 0) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_16, lookup_literalQ_16_5] using supply_5_16

theorem supply_16_6 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (3, 0) = literalQ (8, 0) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_16, lookup_literalQ_16_6] using supply_6_16

theorem supply_16_7 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (3, 1) = literalQ (8, 0) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_16, lookup_literalQ_16_7] using supply_7_16

theorem supply_16_8 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (4, 0) = literalQ (8, 0) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_16, lookup_literalQ_16_8] using supply_8_16

theorem supply_16_9 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (4, 1) = literalQ (8, 0) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_16, lookup_literalQ_16_9] using supply_9_16

theorem supply_16_10 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (5, 0) = literalQ (8, 0) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_16, lookup_literalQ_16_10] using supply_10_16

theorem supply_16_11 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (5, 1) = literalQ (8, 0) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_16, lookup_literalQ_16_11] using supply_11_16

theorem supply_16_12 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (6, 0) = literalQ (8, 0) (6, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_12_16, lookup_literalQ_16_12] using supply_12_16

theorem supply_16_13 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (6, 1) = literalQ (8, 0) (6, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_13_16, lookup_literalQ_16_13] using supply_13_16

theorem supply_16_14 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (7, 0) = literalQ (8, 0) (7, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_14_16, lookup_literalQ_16_14] using supply_14_16

theorem supply_16_15 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (7, 1) = literalQ (8, 0) (7, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_15_16, lookup_literalQ_16_15] using supply_15_16

theorem supply_16_16 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (8, 0) = literalQ (8, 0) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_16_17 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (8, 1) = literalQ (8, 0) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_16_18 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (9, 0) = literalQ (8, 0) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_16_19 : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) (9, 1) = literalQ (8, 0) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_16 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (8, 0) j = literalQ (8, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_16_0
  · exact supply_16_1
  · exact supply_16_2
  · exact supply_16_3
  · exact supply_16_4
  · exact supply_16_5
  · exact supply_16_6
  · exact supply_16_7
  · exact supply_16_8
  · exact supply_16_9
  · exact supply_16_10
  · exact supply_16_11
  · exact supply_16_12
  · exact supply_16_13
  · exact supply_16_14
  · exact supply_16_15
  · exact supply_16_16
  · exact supply_16_17
  · exact supply_16_18
  · exact supply_16_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
