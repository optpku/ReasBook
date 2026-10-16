module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.SupplyRow9
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

theorem supply_10_0 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (0, 0) = literalQ (5, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_10, lookup_literalQ_10_0] using supply_0_10

theorem supply_10_1 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (0, 1) = literalQ (5, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_10, lookup_literalQ_10_1] using supply_1_10

theorem supply_10_2 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (1, 0) = literalQ (5, 0) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_10, lookup_literalQ_10_2] using supply_2_10

theorem supply_10_3 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (1, 1) = literalQ (5, 0) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_10, lookup_literalQ_10_3] using supply_3_10

theorem supply_10_4 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (2, 0) = literalQ (5, 0) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_10, lookup_literalQ_10_4] using supply_4_10

theorem supply_10_5 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (2, 1) = literalQ (5, 0) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_10, lookup_literalQ_10_5] using supply_5_10

theorem supply_10_6 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (3, 0) = literalQ (5, 0) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_10, lookup_literalQ_10_6] using supply_6_10

theorem supply_10_7 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (3, 1) = literalQ (5, 0) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_10, lookup_literalQ_10_7] using supply_7_10

theorem supply_10_8 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (4, 0) = literalQ (5, 0) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_10, lookup_literalQ_10_8] using supply_8_10

theorem supply_10_9 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (4, 1) = literalQ (5, 0) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_10, lookup_literalQ_10_9] using supply_9_10

theorem supply_10_10 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (5, 0) = literalQ (5, 0) (5, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_11 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (5, 1) = literalQ (5, 0) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_12 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (6, 0) = literalQ (5, 0) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_13 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (6, 1) = literalQ (5, 0) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_14 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (7, 0) = literalQ (5, 0) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_15 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (7, 1) = literalQ (5, 0) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_16 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (8, 0) = literalQ (5, 0) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_17 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (8, 1) = literalQ (5, 0) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_18 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (9, 0) = literalQ (5, 0) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_10_19 : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) (9, 1) = literalQ (5, 0) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_10 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (5, 0) j = literalQ (5, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_10_0
  · exact supply_10_1
  · exact supply_10_2
  · exact supply_10_3
  · exact supply_10_4
  · exact supply_10_5
  · exact supply_10_6
  · exact supply_10_7
  · exact supply_10_8
  · exact supply_10_9
  · exact supply_10_10
  · exact supply_10_11
  · exact supply_10_12
  · exact supply_10_13
  · exact supply_10_14
  · exact supply_10_15
  · exact supply_10_16
  · exact supply_10_17
  · exact supply_10_18
  · exact supply_10_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
