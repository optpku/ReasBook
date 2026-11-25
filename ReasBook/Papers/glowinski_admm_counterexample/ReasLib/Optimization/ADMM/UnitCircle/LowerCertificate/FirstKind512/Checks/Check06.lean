/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Context

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.FirstKind512

set_option maxHeartbeats 5000000 in
-- A small batch checks the defining integer Chebyshev recurrence in the kernel.
theorem recurrence06 : ∀ i : Fin 16,
    tree.get (i.val + 351 + 2) = IntegerCoefficients.add
      (0 :: IntegerCoefficients.scale 2 (tree.get (i.val + 351 + 1)))
      (IntegerCoefficients.scale (-1) (tree.get (i.val + 351))) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.FirstKind512
