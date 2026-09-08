module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_21_Uniform_all_pairs_endpoint_separation

open Filter
open scoped Topology

/- Lemma (Uniform separation): after restricting the initial scale, every endpoint
is uniformly separated from the other endpoints and the limiting circle. -/
#check (DFP.TwoPhaseOrbit.slowCurveUniformEndpointSeparation :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cStar > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ,
                  cStar * (orbit.state (k / 2)).ε ^ 2 ≤
                    Metric.infDist (orbit.endpoint k)
                      (orbit.closedSetCandidate Clim Glim \ {orbit.endpoint k}))
