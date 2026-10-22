/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_5_2_Decay_of_the_endpoint_correction_vectors.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map

public section

open Filter
open scoped Topology

/- Lemma 5.2 (Decay of the endpoint correction vectors) -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionUniformBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorrection > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, ‖orbit.endpointCorrection Clim k‖ ≤
              Kcorrection * (orbit.state (k / 2)).ε ^ 3)

#check (DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionRadiusUniformBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorrection > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, ‖orbit.endpointCorrection Clim k‖ ≤
              Kcorrection * (orbit.state (k / 2)).ε * orbit.endpointRadius k)
