module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointClusterSet

public section

export DFP.TwoPhaseOrbit (slowCurveEndpointClusterSet_eq_limitCircle)

open Filter
open scoped Asymptotics Topology

/- Lemma 4.9 (Full limiting circle as the endpoint accumulation set): for every
sufficiently small slow-curve orbit whose centers and positive amplitudes converge,
the cluster set of the flattened endpoint sequence is exactly its limiting circle. -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointClusterSet_eq_limitCircle :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
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
              {x : EuclideanSpace ℝ (Fin 2) | MapClusterPt x atTop orbit.endpoint} =
                DFP.TwoPhaseOrbit.limitCircle Clim Glim)
