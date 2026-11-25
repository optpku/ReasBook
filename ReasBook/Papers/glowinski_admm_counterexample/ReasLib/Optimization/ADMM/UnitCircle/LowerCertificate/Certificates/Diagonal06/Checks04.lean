/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal06.Data

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal06

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk32 : ∀ i : Fin 1,
    leftCoefficient (i.val + 256) = rightCoefficient (i.val + 256) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal06
