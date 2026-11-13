/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.RefinedLowerCertificate
public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedAssembly

@[expose] public section

/-!
# Complete results for the updated manuscript

The analytic unit-circle implication, the concrete lower certificate, and
the 1024-phase counterexample discharge all three updated obligations.
-/

namespace ADMM.UpdatedTargets

/-- Theorem 2.1 on the full updated multiplier range. -/
theorem mainConvergence : MainConvergenceClaim :=
  mainConvergence_of_lower_certificate lowerCircleCertificate

/-- The uniform convergence endpoint lies strictly above the displayed `L`. -/
theorem refinedLowerBound : RefinedLowerBoundClaim :=
  refinedLowerBound_of_lower_certificate lowerCircleCertificate

/-- Corollary 2.3: both strict endpoint bounds and the exact enclosure width. -/
theorem endpointBounds : EndpointBoundsClaim :=
  endpointBounds_of_lower_certificate lowerCircleCertificate

end ADMM.UpdatedTargets
