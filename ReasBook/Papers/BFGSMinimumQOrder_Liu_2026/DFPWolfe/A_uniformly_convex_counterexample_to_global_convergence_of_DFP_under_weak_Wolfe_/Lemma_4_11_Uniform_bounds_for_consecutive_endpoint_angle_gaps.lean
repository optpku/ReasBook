module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleGap

public section

open Filter
open scoped Topology

/- Lemma 4.11 (Uniform bounds for consecutive endpoint angle gaps): for all sufficiently
small slow-curve orbits, the lifted physical endpoint angles decrease strictly and both
gaps in cycle `j` are uniformly comparable to `ε_j ^ 2`. -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointPolarAngleGapUniformBounds :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cθ > 0, ∃ Cθ > cθ,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            StrictAnti (orbit.endpointPolarAngleLift Clim) ∧
              ∀ j : ℕ, ∀ i : Fin 2,
                let k := 2 * j + i.val
                orbit.endpointPolarAngleLift Clim k -
                    orbit.endpointPolarAngleLift Clim (k + 1) ∈
                  Set.Icc (cθ * (orbit.state j).ε ^ 2)
                    (Cθ * (orbit.state j).ε ^ 2))
