/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.SupplyRow4
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096
-- Each theorem checks a finite rational entry after symbolic sparse expansion.
set_option maxHeartbeats 2000000

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
open MatrixAssembly

theorem supply_5_0 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (0, 0) = literalQ (2, 1) (0, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_0_5, lookup_literalQ_5_0] using supply_0_5

theorem supply_5_1 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (0, 1) = literalQ (2, 1) (0, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_1_5, lookup_literalQ_5_1] using supply_1_5

theorem supply_5_2 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (1, 0) = literalQ (2, 1) (1, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_2_5, lookup_literalQ_5_2] using supply_2_5

theorem supply_5_3 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (1, 1) = literalQ (2, 1) (1, 1) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_3_5, lookup_literalQ_5_3] using supply_3_5

theorem supply_5_4 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (2, 0) = literalQ (2, 1) (2, 0) := by
  rw [supplyMatrix_comm]
  simpa only [lookup_literalQ_4_5, lookup_literalQ_5_4] using supply_4_5

theorem supply_5_5 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (2, 1) = literalQ (2, 1) (2, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_5_6 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (3, 0) = literalQ (2, 1) (3, 0) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_5_7 : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) (3, 1) = literalQ (2, 1) (3, 1) := by
  rw [supplyMatrix_factored]
  simp only [supplyEntry, sum_block, Fin.sum_univ_succ]
  simp [productEntry, ADMM.FiniteMemory.Reconstruction.graphNormal,
    ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  all_goals norm_num

theorem supply_row_5 (j : Fin 4 × Fin 2) : supplyMatrix caseData (endpointGamma caseData .upper) (2, 1) j = literalQ (2, 1) j := by
  rcases j with ⟨j, b⟩
  fin_cases j <;> fin_cases b
  · exact supply_5_0
  · exact supply_5_1
  · exact supply_5_2
  · exact supply_5_3
  · exact supply_5_4
  · exact supply_5_5
  · exact supply_5_6
  · exact supply_5_7

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
