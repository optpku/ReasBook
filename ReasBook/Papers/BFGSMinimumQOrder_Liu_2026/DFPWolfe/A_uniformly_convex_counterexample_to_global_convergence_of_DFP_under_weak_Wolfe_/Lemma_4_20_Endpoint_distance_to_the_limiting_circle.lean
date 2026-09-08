module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointDistance
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map

public section

open Filter
open scoped Asymptotics Topology

/- Lemma 4.20 (Endpoint distance to the limiting circle) (1): the distance from
each flattened endpoint to the limiting circle is asymptotic to
`(13 / 3) * Glim * ε` at its cycle index. -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointLimitCircleDistanceEquivalent :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
                (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) ~[atTop]
                (fun k : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state (k / 2)).ε))

/- Lemma 4.20 (Endpoint distance to the limiting circle) (2): the squared
cycle scale is little-o of the distance from a flattened endpoint to the
limiting circle. -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointRadiusIsLittleODistance :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              (fun k : ℕ ↦ (orbit.state (k / 2)).ε ^ 2) =o[atTop]
                (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim)))
