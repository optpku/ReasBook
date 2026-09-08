module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit

public section

open Filter
open scoped Asymptotics Topology

export DFP.TwoPhaseOrbit (slowCurveAmplitudeExistsPositiveLimit)

/- Lemma 4.4 (Positive limiting gradient amplitude): for every sufficiently small
positive initial scale, the amplitude of the canonical slow-curve orbit converges to a
strictly positive limit. -/
#check (DFP.TwoPhaseOrbit.slowCurveAmplitudeExistsPositiveLimit :
  ∀ (p h : ℝ → ℝ),
    (
      (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
          (ε', p ε', h ε'))) →
    (
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∃ Glim > 0,
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim))
