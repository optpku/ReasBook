module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_4_8b_Limiting_circle_and_endpoint_closed_set_candidate_EndpointSet
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_4b_Uniform_endpoint_gradient_norm_bounds_in_both_phases
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_7a_Uniform_center_tail_bounds_over_all_sufficiently_small_initial_scales
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation

public section

open Filter
open scoped Asymptotics Topology

/- Lemma 4.12 (Uniform phase-radius approximation) -/
#check (DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorIsBigO :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ σ : Fin 2,
            (fun j : ℕ ↦
                ‖orbit.endpoint (2 * j + σ.val) - Clim‖ - (orbit.state j).amplitude) =O[atTop]
              (fun j : ℕ ↦ (orbit.state j).ε ^ 3))

/- Lemma 4.12 (Uniform phase-radius approximation) -/
#check (DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorIsLittleO :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ σ : Fin 2,
            (fun j : ℕ ↦
                ‖orbit.endpoint (2 * j + σ.val) - Clim‖ - (orbit.state j).amplitude) =o[atTop]
              (fun j : ℕ ↦ (orbit.state j).ε ^ 2))

/- Lemma 4.12 (Uniform phase-radius approximation) -/
#check (DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorUniform :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ ωR : ℝ → ℝ,
      ((∀ η ∈ Set.Ioc 0 εbar, 0 ≤ ωR η) ∧
          MonotoneOn ωR (Set.Ioc 0 εbar) ∧ Tendsto ωR (𝓝[>] 0) (𝓝 0)) ∧
        ∀ η ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 η,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
              ∀ j : ℕ, ∀ σ : Fin 2,
                |‖orbit.endpoint (2 * j + σ.val) - Clim‖ - (orbit.state j).amplitude| ≤
                  ωR η * (orbit.state j).ε ^ 2)
