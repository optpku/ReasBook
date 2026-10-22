/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_6_5_Positive_limiting_gradient_norm_at_every_endpoint.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit

public section

open Filter
open scoped Asymptotics Topology

/- Lemma 6.5 (Positive limiting gradient norm at every endpoint): for every
sufficiently small canonical slow-curve orbit, the norms of the gradients along
the full endpoint sequence converge to a strictly positive limit. -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointGradientNormTendsto :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∃ Glim > 0,
        Tendsto (fun k : ℕ ↦ ‖orbit.endpointGradient k‖) atTop (𝓝 Glim))
