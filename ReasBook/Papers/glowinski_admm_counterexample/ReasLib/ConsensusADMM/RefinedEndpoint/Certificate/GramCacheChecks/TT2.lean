/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheData

@[expose] public section

set_option maxRecDepth 8192

namespace ConsensusADMM.RefinedEndpoint.Certificate

/-- Kernel equality for one bounded cache block; the generating Python is untrusted. -/
theorem gramCacheTT2 : ∀ i : Fin 64,
    cachedGramNumerator true true (128 + i) =
      gramNumerator true true (128 + i) := by
  decide +kernel

end ConsensusADMM.RefinedEndpoint.Certificate
