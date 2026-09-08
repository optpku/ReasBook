module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTailUniform

public section

open Filter
open scoped Topology

/- Lemma 4.12a (Uniform first-order amplitude tail on all sufficiently small orbits):
the canonical owner controls the first-order amplitude-tail error uniformly over all
sufficiently small invariant slow-curve orbits. -/
#check (DFP.TwoPhaseOrbit.slowCurveAmplitudeTailUniform :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ ωG : ℝ → ℝ,
      ((∀ η ∈ Set.Ioc 0 εbar, 0 ≤ ωG η) ∧
          MonotoneOn ωG (Set.Ioc 0 εbar) ∧ Tendsto ωG (𝓝[>] 0) (𝓝 0)) ∧
        ∀ η ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 η,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ j : ℕ,
                |(orbit.state j).amplitude - Glim -
                    (13 / 3 : ℝ) * Glim * (orbit.state j).ε| ≤
                  ωG η * (orbit.state j).ε)
