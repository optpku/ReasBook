/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.TargetContext

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

set_option maxHeartbeats 5000000 in
-- Exact source-to-polynomial coefficient equality, checked in the kernel.
theorem startCoefficientZero : startLeftCoefficient 0 = startRightCoefficient 0 := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
