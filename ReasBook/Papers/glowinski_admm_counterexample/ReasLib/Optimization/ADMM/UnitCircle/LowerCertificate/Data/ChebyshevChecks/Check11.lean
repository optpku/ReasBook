/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.ChebyshevContext

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.UnitCircle.LowerCertificate.Data

theorem chebyshevRecurrence11 : ∀ i : Fin 16,
    chebyshevTree.get (i.val + 176 + 2) = IntegerCoefficients.add
      (0 :: IntegerCoefficients.scale 2 (chebyshevTree.get (i.val + 176 + 1)))
      (IntegerCoefficients.scale (-1) (chebyshevTree.get (i.val + 176))) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Data
