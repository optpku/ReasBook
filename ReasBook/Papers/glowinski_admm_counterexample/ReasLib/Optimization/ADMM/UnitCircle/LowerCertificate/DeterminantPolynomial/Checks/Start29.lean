/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CachedContext

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

set_option maxHeartbeats 5000000 in
/-- Exact integer computation through the certified two-level Chebyshev cache. -/
theorem startChunk29Cached : ∀ i : Fin 8,
    startCachedLeftCoefficient (i.val + 232) =
      startRightCoefficient (i.val + 232) := by
  decide +kernel

/-- Transport the cached computation back to the original source coefficients. -/
theorem startChunk29 : ∀ i : Fin 8,
    startLeftCoefficient (i.val + 232) = startRightCoefficient (i.val + 232) := by
  intro i
  rw [← startCachedLeftCoefficient_eq]
  exact startChunk29Cached i

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
