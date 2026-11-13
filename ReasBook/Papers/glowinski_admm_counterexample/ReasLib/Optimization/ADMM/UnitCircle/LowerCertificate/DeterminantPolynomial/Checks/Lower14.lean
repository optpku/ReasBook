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
theorem lowerChunk14Cached : ∀ i : Fin 8,
    lowerCachedLeftCoefficient (i.val + 112) =
      lowerRightCoefficient (i.val + 112) := by
  decide +kernel

/-- Transport the cached computation back to the original source coefficients. -/
theorem lowerChunk14 : ∀ i : Fin 8,
    lowerLeftCoefficient (i.val + 112) = lowerRightCoefficient (i.val + 112) := by
  intro i
  rw [← lowerCachedLeftCoefficient_eq]
  exact lowerChunk14Cached i

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
