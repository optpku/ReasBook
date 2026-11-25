/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCache
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.SupportChecks

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

/-- Positivity is transported from the checked cache to the faithful integer evaluator. -/
theorem first_supports_positive (j : Fin 1024) : 0 < (firstSupportNumerator j).lower := by
  unfold firstSupportNumerator
  rw [← cachedPairNumerator_correct]
  exact cached_first_supports_positive j

theorem second_supports_positive (j : Fin 1024) : 0 < (secondSupportNumerator j).lower := by
  unfold secondSupportNumerator
  rw [← cachedPairNumerator_correct]
  exact cached_second_supports_positive j

theorem residual_positive : 0 < residualNormNumerator.lower := by
  unfold residualNormNumerator
  rw [← cachedPairNumerator_correct]
  exact cached_residual_positive

end ConsensusADMM.RefinedEndpoint.Certificate
