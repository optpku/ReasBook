/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheData

@[expose] public section

set_option maxRecDepth 16384

namespace ConsensusADMM.RefinedEndpoint.Certificate

/-- All 1024 first-block comparisons, including the origin, have positive lower numerators. -/
theorem cached_first_supports_positive : ∀ j : Fin 1024,
    0 < (cachedPairNumerator firstNormalNumerator (firstTarget j)).lower := by
  decide +kernel

/-- All 1024 second-block comparisons have positive lower numerators. -/
theorem cached_second_supports_positive : ∀ j : Fin 1024,
    0 < (cachedPairNumerator secondNormalNumerator (secondTarget j)).lower := by
  decide +kernel

/-- The residual's squared norm has a positive lower numerator. -/
theorem cached_residual_positive :
    0 < (cachedPairNumerator residualVector residualVector).lower := by
  decide +kernel

end ConsensusADMM.RefinedEndpoint.Certificate
