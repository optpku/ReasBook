/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.Lower.Data
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.Local
@[expose] public section
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.Lower
theorem candidatePositive : PositivePivots (1 / 10000000) candidateK :=
  Pilot.candidatePositive
#print axioms candidatePositive
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.Lower
