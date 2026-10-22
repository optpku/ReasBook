/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_18a_Uniform_parabolic_recurrence_remainder.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.RadiusJet

public section

open Filter
open scoped Topology

/- Lemma 3.18a (Uniform parabolic recurrence remainder): for a slow graph with
the fixed cubic and quartic jets, one common positive threshold and coefficient
bound the signed two-leg recurrence remainder at every smaller positive scale. -/
#check (DFP.TwoLeg.slowGraphSignedRecurrenceBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
    ∃ η₀ > 0, ∃ Cε > 0, ∀ η ∈ Set.Ioc 0 η₀, ∀ ε ∈ Set.Ioc 0 η,
      |DFP.TwoLeg.signedEpsilon ε (p ε) (h ε) - ε +
          (3 / 2) * ε ^ 4 - (5 / 4) * ε ^ 5| ≤ Cε * ε ^ 6)

/- The normalized signed recurrence remainder has the canonical order-five
tail-supremum modulus, uniformly controlled at a linear rate. -/
#check (DFP.TwoLeg.slowGraphSignedRecurrenceModulus :
  ∀ (p h : ℝ → ℝ),
    (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
    let R : Unit → ℝ → ℝ := fun _ ε ↦
      DFP.TwoLeg.signedEpsilon ε (p ε) (h ε) -
        (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)
    ∃ η₀ > 0, ∃ Cε > 0,
      Asymptotics.IsUniformRemainderModulusOn R Set.univ 5 η₀
          (Asymptotics.uniformRemainderModulus R Set.univ 5) ∧
        ∀ η ∈ Set.Ioc 0 η₀,
          Asymptotics.uniformRemainderModulus R Set.univ 5 η ≤ Cε * η)
