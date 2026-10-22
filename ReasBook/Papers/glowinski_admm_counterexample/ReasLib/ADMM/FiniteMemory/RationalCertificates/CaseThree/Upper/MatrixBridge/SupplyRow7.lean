/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.SupplyRow6
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

theorem supply_7_0 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (0, 0) = literalQ (3, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_7, lookup_literalQ_7_0] using supply_0_7

theorem supply_7_1 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (0, 1) = literalQ (3, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_7, lookup_literalQ_7_1] using supply_1_7

theorem supply_7_2 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (1, 0) = literalQ (3, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_7, lookup_literalQ_7_2] using supply_2_7

theorem supply_7_3 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (1, 1) = literalQ (3, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_7, lookup_literalQ_7_3] using supply_3_7

theorem supply_7_4 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (2, 0) = literalQ (3, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_7, lookup_literalQ_7_4] using supply_4_7

theorem supply_7_5 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (2, 1) = literalQ (3, 1) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_7, lookup_literalQ_7_5] using supply_5_7

theorem supply_7_6 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (3, 0) = literalQ (3, 1) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_7, lookup_literalQ_7_6] using supply_6_7

theorem supply_7_7 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (3, 1) = literalQ (3, 1) (3, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_8 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (4, 0) = literalQ (3, 1) (4, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_9 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (4, 1) = literalQ (3, 1) (4, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_10 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (5, 0) = literalQ (3, 1) (5, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_11 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (5, 1) = literalQ (3, 1) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_12 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (6, 0) = literalQ (3, 1) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_13 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (6, 1) = literalQ (3, 1) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_14 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (7, 0) = literalQ (3, 1) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_15 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (7, 1) = literalQ (3, 1) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_16 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (8, 0) = literalQ (3, 1) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_17 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (8, 1) = literalQ (3, 1) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_18 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (9, 0) = literalQ (3, 1) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_7_19 : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) (9, 1) = literalQ (3, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_7 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (3, 1) j = literalQ (3, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_7_0
  · exact supply_7_1
  · exact supply_7_2
  · exact supply_7_3
  · exact supply_7_4
  · exact supply_7_5
  · exact supply_7_6
  · exact supply_7_7
  · exact supply_7_8
  · exact supply_7_9
  · exact supply_7_10
  · exact supply_7_11
  · exact supply_7_12
  · exact supply_7_13
  · exact supply_7_14
  · exact supply_7_15
  · exact supply_7_16
  · exact supply_7_17
  · exact supply_7_18
  · exact supply_7_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
