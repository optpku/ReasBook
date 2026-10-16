module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.Storage
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.Moments
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.LowerNumeric
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.Lower.Local
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
open MatrixAssembly

/-- The exact original lower matrix is the one checked by the local LDL certificate. -/
theorem lowerMatrix_eq : lowerMatrix caseData .lower = ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.Lower.candidateK := by
  ext i j
  rw [lowerMatrix_factored, storage_eq]
  simp_rw [mu_eq]
  rw [interpolation_gap_factored]
  simp_rw [moment_eq]
  exact lowerNumeric i j

/-- Positivity transferred from the checked LDL recurrence to the original lower matrix. -/
theorem lowerPositive : PositivePivots (1 / 10000000) (lowerMatrix caseData .lower) := by
  rw [lowerMatrix_eq]
  exact ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.Lower.candidatePositive

#print axioms lowerMatrix_eq
#print axioms lowerPositive

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
