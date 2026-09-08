module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AngularGapSeparation
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map

public section

open Filter
open scoped Topology

/- Lemma 4.14 (Separation from a definite circular angular gap) (1) -/
#check ((fun p h h_invariant h_pJet h_hJet κ _hκ ↦
    DFP.TwoPhaseOrbit.slowCurveAngularGapEndpointSeparation
      p h h_invariant h_pJet h_hJet κ) :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∀ κ : ℝ, κ ∈ Set.Ioo (1 / Real.sqrt 2) 1 →
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ c > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
              ∀ Glim > 0,
                Tendsto (fun i : ℕ ↦ (orbit.state i).amplitude) atTop (𝓝 Glim) →
                  ∀ j ℓ : ℕ, ∀ σ τ : Fin 2,
                    2 * j + σ.val < 2 * ℓ + τ.val →
                      κ * (orbit.state j).ε < (orbit.state ℓ).ε →
                        (orbit.state j).ε ^ 2 / 4 ≤
                            |(orbit.endpointPolarAngle Clim (2 * j + σ.val) -
                              orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal| →
                          c * (orbit.state j).ε ^ 2 ≤
                            dist (orbit.endpoint (2 * j + σ.val))
                              (orbit.endpoint (2 * ℓ + τ.val)))

/- Lemma 4.14 (Separation from a definite circular angular gap) (2) -/
#check (DFP.TwoPhaseOrbit.slowCurveAdjacentEndpointSeparation :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cAdj > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun k : ℕ ↦ (orbit.state k).center) atTop (𝓝 Clim) →
              ∀ Glim > 0,
                Tendsto (fun k : ℕ ↦ (orbit.state k).amplitude) atTop (𝓝 Glim) →
                  ∀ j : ℕ, ∀ i : Fin 2,
                    cAdj * (orbit.state j).ε ^ 2 ≤
                      dist (orbit.endpoint (2 * j + i.val))
                        (orbit.endpoint (2 * j + i.val + 1)))
