/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.SupplyRow11
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

theorem supply_12_0 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (0, 0) = literalQ (6, 0) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_12, lookup_literalQ_12_0] using supply_0_12

theorem supply_12_1 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (0, 1) = literalQ (6, 0) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_12, lookup_literalQ_12_1] using supply_1_12

theorem supply_12_2 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (1, 0) = literalQ (6, 0) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_12, lookup_literalQ_12_2] using supply_2_12

theorem supply_12_3 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (1, 1) = literalQ (6, 0) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_12, lookup_literalQ_12_3] using supply_3_12

theorem supply_12_4 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (2, 0) = literalQ (6, 0) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_12, lookup_literalQ_12_4] using supply_4_12

theorem supply_12_5 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (2, 1) = literalQ (6, 0) (2, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_5_12, lookup_literalQ_12_5] using supply_5_12

theorem supply_12_6 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (3, 0) = literalQ (6, 0) (3, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_6_12, lookup_literalQ_12_6] using supply_6_12

theorem supply_12_7 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (3, 1) = literalQ (6, 0) (3, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_7_12, lookup_literalQ_12_7] using supply_7_12

theorem supply_12_8 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (4, 0) = literalQ (6, 0) (4, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_8_12, lookup_literalQ_12_8] using supply_8_12

theorem supply_12_9 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (4, 1) = literalQ (6, 0) (4, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_9_12, lookup_literalQ_12_9] using supply_9_12

theorem supply_12_10 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (5, 0) = literalQ (6, 0) (5, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_10_12, lookup_literalQ_12_10] using supply_10_12

theorem supply_12_11 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (5, 1) = literalQ (6, 0) (5, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_11_12, lookup_literalQ_12_11] using supply_11_12

theorem supply_12_12 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (6, 0) = literalQ (6, 0) (6, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_12_13 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (6, 1) = literalQ (6, 0) (6, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_12_14 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (7, 0) = literalQ (6, 0) (7, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_12_15 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (7, 1) = literalQ (6, 0) (7, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_12_16 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (8, 0) = literalQ (6, 0) (8, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_12_17 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (8, 1) = literalQ (6, 0) (8, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_12_18 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (9, 0) = literalQ (6, 0) (9, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_12_19 : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) (9, 1) = literalQ (6, 0) (9, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_12 (j : Fin 10 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .lower) (6, 0) j = literalQ (6, 0) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_12_0
  · exact supply_12_1
  · exact supply_12_2
  · exact supply_12_3
  · exact supply_12_4
  · exact supply_12_5
  · exact supply_12_6
  · exact supply_12_7
  · exact supply_12_8
  · exact supply_12_9
  · exact supply_12_10
  · exact supply_12_11
  · exact supply_12_12
  · exact supply_12_13
  · exact supply_12_14
  · exact supply_12_15
  · exact supply_12_16
  · exact supply_12_17
  · exact supply_12_18
  · exact supply_12_19

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
