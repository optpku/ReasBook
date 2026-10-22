/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.SupplyRow8
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

theorem supply_9_0 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (0, 0) = literalQ (4, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_9, lookup_literalQ_9_0] using supply_0_9

theorem supply_9_1 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (0, 1) = literalQ (4, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_9, lookup_literalQ_9_1] using supply_1_9

theorem supply_9_2 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (1, 0) = literalQ (4, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_9, lookup_literalQ_9_2] using supply_2_9

theorem supply_9_3 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (1, 1) = literalQ (4, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_9, lookup_literalQ_9_3] using supply_3_9

theorem supply_9_4 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (2, 0) = literalQ (4, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_9, lookup_literalQ_9_4] using supply_4_9

theorem supply_9_5 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (2, 1) = literalQ (4, 1) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_9, lookup_literalQ_9_5] using supply_5_9

theorem supply_9_6 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (3, 0) = literalQ (4, 1) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_9, lookup_literalQ_9_6] using supply_6_9

theorem supply_9_7 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (3, 1) = literalQ (4, 1) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_9, lookup_literalQ_9_7] using supply_7_9

theorem supply_9_8 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (4, 0) = literalQ (4, 1) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_9, lookup_literalQ_9_8] using supply_8_9

theorem supply_9_9 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (4, 1) = literalQ (4, 1) (4, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_10 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (5, 0) = literalQ (4, 1) (5, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_11 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (5, 1) = literalQ (4, 1) (5, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_12 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (6, 0) = literalQ (4, 1) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_13 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (6, 1) = literalQ (4, 1) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_14 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (7, 0) = literalQ (4, 1) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_15 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (7, 1) = literalQ (4, 1) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_16 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (8, 0) = literalQ (4, 1) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_17 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (8, 1) = literalQ (4, 1) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_18 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (9, 0) = literalQ (4, 1) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_9_19 : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) (9, 1) = literalQ (4, 1) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_9 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (4, 1) j = literalQ (4, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_9_0
  · exact supply_9_1
  · exact supply_9_2
  · exact supply_9_3
  · exact supply_9_4
  · exact supply_9_5
  · exact supply_9_6
  · exact supply_9_7
  · exact supply_9_8
  · exact supply_9_9
  · exact supply_9_10
  · exact supply_9_11
  · exact supply_9_12
  · exact supply_9_13
  · exact supply_9_14
  · exact supply_9_15
  · exact supply_9_16
  · exact supply_9_17
  · exact supply_9_18
  · exact supply_9_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
