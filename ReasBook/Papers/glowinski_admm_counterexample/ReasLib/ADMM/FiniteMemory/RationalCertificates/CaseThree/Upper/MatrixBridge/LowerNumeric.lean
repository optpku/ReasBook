module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.CaseLookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.MomentData
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixGap
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.Lower.Local
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
open MatrixAssembly

/-- The final lower-matrix arithmetic after independently checking storage and moments. -/
theorem lowerNumeric (i j : Fin 9 × Fin 2) :
    (literalP i j + literalP j i) / 2 -
      (∑ b : Block, ∑ d : Option (Fin 8),
        -(interpolationNormal (endpointGamma caseData .upper) b d (unitVector i) * literalMoment b d j +
          interpolationNormal (endpointGamma caseData .upper) b d (unitVector j) * literalMoment b d i) / 2) -
      caseData.zeta * currentPairMatrix 8 i j = ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.Lower.candidateK i j := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, d⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases d <;>
    simp [sum_block, Fintype.sum_option, Fin.sum_univ_succ, interpolationNormal,
      interpolationPosition, currentPairMatrix_apply] <;> norm_num

#print axioms lowerNumeric

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
