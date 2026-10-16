module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.CaseLookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
open MatrixAssembly

/-- All reconstructed weights equal their exact rational candidates. -/
theorem mu_eq (b : Block) (a d : Option (Fin 8)) :
    reconstructMu caseData b a d = literalMu b a d := by
  cases b <;> fin_cases a <;> fin_cases d <;>
    norm_num [reconstructMu, lagCoefficient, Fin.sum_univ_succ] <;>
    simp only [Fin.le_iff_val_le_val, Fin.ext_iff, Fin.val_natCast] <;> norm_num

/-- Nonnegativity is checked against every original reconstructed weight. -/
theorem mu_nonneg (b : Block) (a d : Option (Fin 8)) :
    0 ≤ reconstructMu caseData b a d := by
  rw [mu_eq]
  cases b <;> fin_cases a <;> fin_cases d <;> norm_num

#print axioms mu_eq
#print axioms mu_nonneg

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
