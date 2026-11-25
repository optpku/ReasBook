/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevContext

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.UnitCircle.LowerCertificate.Data

set_option maxHeartbeats 5000000 in
-- Each finite batch checks exact integer Chebyshev power coefficients in the kernel.
theorem diagonalChebChunk14 : ∀ i : Fin 8,
    diagonalChebPolynomial.getD (i.val + 112) 0 = Leaves.diagonalTree.get (i.val + 112) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Data
