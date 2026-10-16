module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Lower.MatrixBridge.DescentData
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Lower.Descent.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAction

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge
open MatrixAssembly

-- Check the finite arithmetic after every table entry has a definitional lookup proof.
set_option maxHeartbeats 16000000
theorem cachedDescent (i j : Fin 8 × Fin 2) :
  (previousPadding literalP i j + previousPadding literalP j i) / 2 -
  (currentPadding literalP i j + currentPadding literalP j i) / 2 - literalQ i j = literalDescent i j := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;> norm_num

theorem cachedDescentKernel : literalDescent * constantModes 8 = 0 := by
  ext ⟨i, a⟩ b
  rw [mul_constantModes]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [Fin.sum_univ_succ]

theorem cachedDescentPrincipal (i j : Fin 7 × Fin 2) :
  literalDescent (i.1.castSucc, i.2) (j.1.castSucc, j.2) = ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.Descent.candidateK i j := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;> norm_num

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge
