/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.SupplyRow12
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

theorem supply_13_0 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (0, 0) = literalQ (6, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_13, lookup_literalQ_13_0] using supply_0_13

theorem supply_13_1 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (0, 1) = literalQ (6, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_13, lookup_literalQ_13_1] using supply_1_13

theorem supply_13_2 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (1, 0) = literalQ (6, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_13, lookup_literalQ_13_2] using supply_2_13

theorem supply_13_3 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (1, 1) = literalQ (6, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_13, lookup_literalQ_13_3] using supply_3_13

theorem supply_13_4 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (2, 0) = literalQ (6, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_13, lookup_literalQ_13_4] using supply_4_13

theorem supply_13_5 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (2, 1) = literalQ (6, 1) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_13, lookup_literalQ_13_5] using supply_5_13

theorem supply_13_6 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (3, 0) = literalQ (6, 1) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_13, lookup_literalQ_13_6] using supply_6_13

theorem supply_13_7 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (3, 1) = literalQ (6, 1) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_13, lookup_literalQ_13_7] using supply_7_13

theorem supply_13_8 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (4, 0) = literalQ (6, 1) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_13, lookup_literalQ_13_8] using supply_8_13

theorem supply_13_9 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (4, 1) = literalQ (6, 1) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_13, lookup_literalQ_13_9] using supply_9_13

theorem supply_13_10 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (5, 0) = literalQ (6, 1) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_13, lookup_literalQ_13_10] using supply_10_13

theorem supply_13_11 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (5, 1) = literalQ (6, 1) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_13, lookup_literalQ_13_11] using supply_11_13

theorem supply_13_12 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (6, 0) = literalQ (6, 1) (6, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_12_13, lookup_literalQ_13_12] using supply_12_13

theorem supply_13_13 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (6, 1) = literalQ (6, 1) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_13_14 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (7, 0) = literalQ (6, 1) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_13_15 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (7, 1) = literalQ (6, 1) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_13_16 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (8, 0) = literalQ (6, 1) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_13_17 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (8, 1) = literalQ (6, 1) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_13_18 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (9, 0) = literalQ (6, 1) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_13_19 : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) (9, 1) = literalQ (6, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_13 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (6, 1) j = literalQ (6, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_13_0
  · exact supply_13_1
  · exact supply_13_2
  · exact supply_13_3
  · exact supply_13_4
  · exact supply_13_5
  · exact supply_13_6
  · exact supply_13_7
  · exact supply_13_8
  · exact supply_13_9
  · exact supply_13_10
  · exact supply_13_11
  · exact supply_13_12
  · exact supply_13_13
  · exact supply_13_14
  · exact supply_13_15
  · exact supply_13_16
  · exact supply_13_17
  · exact supply_13_18
  · exact supply_13_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
