module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_7a_Uniform_center_tail_bounds_over_all_sufficiently_small_initial_scales
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.BoundaryPolarExpansion

public section

open Filter
open scoped Asymptotics Matrix Topology

export DFP.TwoPhaseOrbit (slowCurveBoundaryPolarExpansion)

/- Lemma 4.10 (Cycle-boundary polar expansion) -/
#check (DFP.TwoPhaseOrbit.slowCurveBoundaryPolarExpansion :
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
          (fun j : ℕ ↦
              let s := orbit.state j
              s.point - Clim -
                s.amplitude • WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 2 * s.ε ^ 2])) =o[atTop]
            (fun j : ℕ ↦
              let s := orbit.state j
              s.amplitude * s.ε ^ 2))
