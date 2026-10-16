module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.SupplyRow18
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

theorem supply_19_0 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (0, 0) = literalQ (9, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_19, lookup_literalQ_19_0] using supply_0_19

theorem supply_19_1 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (0, 1) = literalQ (9, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_19, lookup_literalQ_19_1] using supply_1_19

theorem supply_19_2 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (1, 0) = literalQ (9, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_19, lookup_literalQ_19_2] using supply_2_19

theorem supply_19_3 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (1, 1) = literalQ (9, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_19, lookup_literalQ_19_3] using supply_3_19

theorem supply_19_4 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (2, 0) = literalQ (9, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_19, lookup_literalQ_19_4] using supply_4_19

theorem supply_19_5 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (2, 1) = literalQ (9, 1) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_19, lookup_literalQ_19_5] using supply_5_19

theorem supply_19_6 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (3, 0) = literalQ (9, 1) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_19, lookup_literalQ_19_6] using supply_6_19

theorem supply_19_7 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (3, 1) = literalQ (9, 1) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_19, lookup_literalQ_19_7] using supply_7_19

theorem supply_19_8 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (4, 0) = literalQ (9, 1) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_19, lookup_literalQ_19_8] using supply_8_19

theorem supply_19_9 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (4, 1) = literalQ (9, 1) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_19, lookup_literalQ_19_9] using supply_9_19

theorem supply_19_10 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (5, 0) = literalQ (9, 1) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_19, lookup_literalQ_19_10] using supply_10_19

theorem supply_19_11 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (5, 1) = literalQ (9, 1) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_19, lookup_literalQ_19_11] using supply_11_19

theorem supply_19_12 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (6, 0) = literalQ (9, 1) (6, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_12_19, lookup_literalQ_19_12] using supply_12_19

theorem supply_19_13 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (6, 1) = literalQ (9, 1) (6, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_13_19, lookup_literalQ_19_13] using supply_13_19

theorem supply_19_14 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (7, 0) = literalQ (9, 1) (7, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_14_19, lookup_literalQ_19_14] using supply_14_19

theorem supply_19_15 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (7, 1) = literalQ (9, 1) (7, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_15_19, lookup_literalQ_19_15] using supply_15_19

theorem supply_19_16 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (8, 0) = literalQ (9, 1) (8, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_16_19, lookup_literalQ_19_16] using supply_16_19

theorem supply_19_17 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (8, 1) = literalQ (9, 1) (8, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_17_19, lookup_literalQ_19_17] using supply_17_19

theorem supply_19_18 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (9, 0) = literalQ (9, 1) (9, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_18_19, lookup_literalQ_19_18] using supply_18_19

theorem supply_19_19 : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) (9, 1) = literalQ (9, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_19 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (9, 1) j = literalQ (9, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_19_0
  · exact supply_19_1
  · exact supply_19_2
  · exact supply_19_3
  · exact supply_19_4
  · exact supply_19_5
  · exact supply_19_6
  · exact supply_19_7
  · exact supply_19_8
  · exact supply_19_9
  · exact supply_19_10
  · exact supply_19_11
  · exact supply_19_12
  · exact supply_19_13
  · exact supply_19_14
  · exact supply_19_15
  · exact supply_19_16
  · exact supply_19_17
  · exact supply_19_18
  · exact supply_19_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
