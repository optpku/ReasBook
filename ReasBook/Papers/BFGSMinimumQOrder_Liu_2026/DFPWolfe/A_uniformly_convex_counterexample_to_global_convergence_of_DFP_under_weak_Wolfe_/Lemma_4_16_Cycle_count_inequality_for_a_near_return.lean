module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.NearReturnCycleCount

public section

open Filter
open scoped Topology

/- Lemma 4.16 (Cycle-count inequality for a near return): if a later endpoint is
`N` cycles after an earlier endpoint at a comparable scale and their lifted angular
difference is `2 * Real.pi * m + ζ`, then that angular displacement is bounded by
`N` times the uniform per-cycle upper bound at the earlier scale. -/
#check (DFP.TwoPhaseOrbit.slowCurveNearReturnCycleCountBound :
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
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Cθ > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
              ∀ j N : ℕ, ∀ σ τ : Fin 2,
                0 < N →
                  κ * (orbit.state j).ε < (orbit.state (j + N)).ε →
                    ∀ (m : ℤ) (ζ : ℝ),
                      orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                          orbit.endpointPolarAngleLift Clim (2 * (j + N) + τ.val) =
                        2 * Real.pi * (m : ℝ) + ζ →
                          |ζ| < (orbit.state j).ε ^ 2 / 4 →
                            2 * Real.pi * (m : ℝ) - (orbit.state j).ε ^ 2 / 4 ≤
                              (N : ℝ) * Cθ * (orbit.state j).ε ^ 2)
