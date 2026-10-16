module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.SupplyRow10
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

theorem supply_11_0 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (0, 0) = literalQ (5, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_11, lookup_literalQ_11_0] using supply_0_11

theorem supply_11_1 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (0, 1) = literalQ (5, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_11, lookup_literalQ_11_1] using supply_1_11

theorem supply_11_2 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (1, 0) = literalQ (5, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_11, lookup_literalQ_11_2] using supply_2_11

theorem supply_11_3 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (1, 1) = literalQ (5, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_11, lookup_literalQ_11_3] using supply_3_11

theorem supply_11_4 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (2, 0) = literalQ (5, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_11, lookup_literalQ_11_4] using supply_4_11

theorem supply_11_5 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (2, 1) = literalQ (5, 1) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_11, lookup_literalQ_11_5] using supply_5_11

theorem supply_11_6 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (3, 0) = literalQ (5, 1) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_11, lookup_literalQ_11_6] using supply_6_11

theorem supply_11_7 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (3, 1) = literalQ (5, 1) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_11, lookup_literalQ_11_7] using supply_7_11

theorem supply_11_8 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (4, 0) = literalQ (5, 1) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_11, lookup_literalQ_11_8] using supply_8_11

theorem supply_11_9 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (4, 1) = literalQ (5, 1) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_11, lookup_literalQ_11_9] using supply_9_11

theorem supply_11_10 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (5, 0) = literalQ (5, 1) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_11, lookup_literalQ_11_10] using supply_10_11

theorem supply_11_11 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (5, 1) = literalQ (5, 1) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_12 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (6, 0) = literalQ (5, 1) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_13 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (6, 1) = literalQ (5, 1) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_14 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (7, 0) = literalQ (5, 1) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_15 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (7, 1) = literalQ (5, 1) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_16 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (8, 0) = literalQ (5, 1) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_17 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (8, 1) = literalQ (5, 1) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_18 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (9, 0) = literalQ (5, 1) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_11_19 : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) (9, 1) = literalQ (5, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_11 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (5, 1) j = literalQ (5, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_11_0
  · exact supply_11_1
  · exact supply_11_2
  · exact supply_11_3
  · exact supply_11_4
  · exact supply_11_5
  · exact supply_11_6
  · exact supply_11_7
  · exact supply_11_8
  · exact supply_11_9
  · exact supply_11_10
  · exact supply_11_11
  · exact supply_11_12
  · exact supply_11_13
  · exact supply_11_14
  · exact supply_11_15
  · exact supply_11_16
  · exact supply_11_17
  · exact supply_11_18
  · exact supply_11_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
