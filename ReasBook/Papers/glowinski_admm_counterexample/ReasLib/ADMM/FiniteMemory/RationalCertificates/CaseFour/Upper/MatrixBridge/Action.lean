/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAction
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.CaseLookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
open MatrixAssembly

/-- Exact source-to-candidate comparison for all forty constant-mode entries. -/
theorem action_eq :
    supplyConstantModes caseData (endpointGamma caseData .upper) = literalAction := by
  ext ⟨i, a⟩ b
  fin_cases b
  · change supplyConstantModes caseData (endpointGamma caseData .upper) (i, a) 0 = literalAction (i, a) 0
    rw [supplyConstantModes_zero]
    fin_cases i <;> fin_cases a <;> simp <;> norm_num
  · change supplyConstantModes caseData (endpointGamma caseData .upper) (i, a) 1 = literalAction (i, a) 1
    rw [supplyConstantModes_one]
    fin_cases i <;> fin_cases a <;>
      simp [sum_block, Fin.sum_univ_succ, actionLag,
        ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual] <;> norm_num

#print axioms action_eq
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
