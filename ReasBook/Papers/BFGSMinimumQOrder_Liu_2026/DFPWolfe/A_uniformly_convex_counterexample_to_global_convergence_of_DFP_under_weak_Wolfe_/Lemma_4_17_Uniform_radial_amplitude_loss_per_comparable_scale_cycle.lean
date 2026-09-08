module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_4a_Uniform_amplitude_bounds_over_all_sufficiently_small_initial_scales
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ComparableScaleAmplitudeLoss

public section

open Filter
open scoped Topology

/- Lemma 4.17 (Uniform radial amplitude loss per comparable-scale cycle). -/
#check (DFP.TwoPhaseOrbit.slowCurveComparableScaleAmplitudeLoss :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∀ (κ : ℝ), κ ∈ Set.Ioo (1 / Real.sqrt 2) 1 →
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cG > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ j ℓ t : ℕ, j ≤ t → t < ℓ →
            κ * (orbit.state j).ε < (orbit.state ℓ).ε →
              cG * (orbit.state j).ε ^ 4 ≤
                (orbit.state t).amplitude - (orbit.state (t + 1)).amplitude)
