module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.Lower.Data
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.Local
@[expose] public section
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.Lower
theorem candidatePositive : PositivePivots (1 / 10000000) candidateK :=
  Pilot.candidatePositive
#print axioms candidatePositive
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.Lower
