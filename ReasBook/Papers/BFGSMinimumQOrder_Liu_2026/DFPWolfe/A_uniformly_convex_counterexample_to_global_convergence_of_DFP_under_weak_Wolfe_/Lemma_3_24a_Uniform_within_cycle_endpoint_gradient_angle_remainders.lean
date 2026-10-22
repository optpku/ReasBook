/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_24a_Uniform_within_cycle_endpoint_gradient_angle_remainders.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleRemainder

public section

open Filter
open scoped Topology

/- Lemma 3.24a (Uniform within-cycle endpoint-gradient angle remainders): The canonical order-two modulus uniformly controls both real endpoint-gradient angle
remainders along every sufficiently small invariant slow-curve orbit. -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointAngleRemainderModulus :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    let R : Unit → ℝ → ℝ × ℝ := fun _ ε ↦
      ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal -
          (-2 * ε ^ 2),
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal -
          (-ε ^ 2))
    let ωθ := Asymptotics.uniformRemainderModulus R Set.univ 2
    ∃ η₀ ∈ Set.Ioo 0 (1 / 4),
      Asymptotics.IsUniformRemainderModulusOn R Set.univ 2 η₀ ωθ ∧
        ∀ η ∈ Set.Ioc 0 η₀, ∀ ε₀ ∈ Set.Ioc 0 η, ∀ j : ℕ,
          let state := (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j
          let observable := DFP.TwoLeg.observableMap state.coordinates
          |observable.firstEndpointAngleIncrement.toReal - (-2 * state.ε ^ 2)| ≤
              ωθ η * state.ε ^ 2 ∧
            |observable.secondEndpointAngleIncrement.toReal - (-state.ε ^ 2)| ≤
              ωθ η * state.ε ^ 2)
