/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.Mu
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.MomentData
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixGap
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.BasisLookups
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
open MatrixAssembly

/-- The small moment table is obtained by finite summation of checked weights. -/
theorem moment_eq (b : Block) (d : Option (Fin 2)) (i : Fin 3 × Fin 2) :
    interpolationMoment literalMu b d i = literalMoment b d i := by
  rcases i with ⟨i, a⟩
  cases b <;> fin_cases d <;> fin_cases i <;> fin_cases a <;>
    simp [interpolationMoment, Fintype.sum_option, Fin.sum_univ_succ,
      interpolationPosition] <;> norm_num

#print axioms moment_eq

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
