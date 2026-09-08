module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.NearReturnEndpointSeparation

public section

open Filter
open scoped Topology

/- Lemma 4.19 (Near-return endpoint separation after phase-radius errors): after
the two phase-radius errors are absorbed into the main radial gap, comparable-scale
positive-winding near returns have uniform endpoint separation at the earlier
squared scale. -/
#check (DFP.TwoPhaseOrbit.slowCurveNearReturnEndpointSeparation :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∀ (κ : ℝ), κ ∈ Set.Ioo (1 / Real.sqrt 2) 1 →
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ c > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
              ∀ j ℓ : ℕ, ∀ σ τ : Fin 2,
                j < ℓ →
                  κ * (orbit.state j).ε < (orbit.state ℓ).ε →
                    ∀ (m : ℤ) (ζ : ℝ),
                      1 ≤ m →
                        orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                            orbit.endpointPolarAngleLift Clim (2 * ℓ + τ.val) =
                          2 * Real.pi * (m : ℝ) + ζ →
                            |ζ| < (orbit.state j).ε ^ 2 / 4 →
                              c * (orbit.state j).ε ^ 2 ≤
                                dist (orbit.endpoint (2 * j + σ.val))
                                  (orbit.endpoint (2 * ℓ + τ.val)))
