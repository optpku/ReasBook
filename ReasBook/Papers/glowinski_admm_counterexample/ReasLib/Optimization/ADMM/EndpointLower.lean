module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.Certificate
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.EndpointBounds
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.CertificateUniform

@[expose] public section

namespace ADMM.EndpointLower

open FiniteMemory.Reconstruction.EndpointLower

/-- Assemble the original interval convergence theorem into the uniform interface. -/
theorem uniformConvergenceAt_original {t : ℝ} (ht : 0 < t)
    (hUpper : t ≤ (377 : ℝ) / 200) : UniformConvergenceAt t := by
  intro n₁ n₂ m P hf hg hKKT β hβ z
  constructor
  · exact ⟨primalResidual_tendsto_zero P hf hg hKKT hβ ht hUpper z,
      secondIncrement_tendsto_zero P hf hg hKKT hβ ht hUpper z,
      objective_tendsto P hf hg hKKT hβ ht hUpper z,
      multiplier_tendsto_optimal P hf hg hKKT hβ ht hUpper z⟩
  · exact trajectory_tendsto_kkt_of_injective P hf hg hKKT hβ ht hUpper z

/-- The new certified endpoint extends every positive parameter in the prefix. -/
theorem uniformConvergenceAt_extended {t : ℝ} (ht : 0 < t)
    (hUpper : t ≤ gamma) : UniformConvergenceAt t := by
  by_cases hOld : t ≤ (377 : ℝ) / 200
  · exact uniformConvergenceAt_original ht hOld
  · exact ConvergenceProof.uniformConvergenceAt_of_certificate
      (certificateOnExtension t (le_of_not_ge hOld) hUpper)

/-- A fully checked positive gap beyond the displayed rational lower bound. -/
theorem gamma_le_endpoint : gamma ≤ uniformConvergenceEndpoint := by
  rw [uniformConvergenceEndpoint_def]
  apply le_csSup EndpointBounds.prefix_bounded_and_endpoint_lt.1
  exact ⟨by norm_num [gamma], fun t ht hUpper ↦
    uniformConvergenceAt_extended ht hUpper.le⟩

/-- Strict lower endpoint bound, using the original affine certificate family. -/
theorem endpoint_gt : (377 : ℝ) / 200 < uniformConvergenceEndpoint := by
  have hgap : (377 : ℝ) / 200 < gamma := by norm_num [gamma]
  exact hgap.trans_le gamma_le_endpoint

end ADMM.EndpointLower
