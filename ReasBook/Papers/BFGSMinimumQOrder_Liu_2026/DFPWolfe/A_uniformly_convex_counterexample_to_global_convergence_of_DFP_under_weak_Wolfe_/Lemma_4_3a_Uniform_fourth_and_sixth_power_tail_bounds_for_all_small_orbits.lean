/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_3a_Uniform_fourth_and_sixth_power_tail_bounds_for_all_small_orbits.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail

public section

open Filter
open scoped BigOperators Topology

/- Lemma 4.3a (Uniform fourth- and sixth-power tail bounds for all small orbits):
all sufficiently small positive orbits on the invariant slow graph have uniformly
bounded fourth- and sixth-power tails. -/
#check (DFP.TwoLeg.slowCurvePowerTailBounds :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∃ C₄ > 0, ∃ C₆ > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let ε n := (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
      ∀ j : ℕ,
        (Summable (fun k : ℕ ↦ ε (j + k) ^ 4) ∧
            (∑' k : ℕ, ε (j + k) ^ 4) ≤ C₄ * ε j) ∧
          (Summable (fun k : ℕ ↦ ε (j + k) ^ 6) ∧
            (∑' k : ℕ, ε (j + k) ^ 6) ≤ C₆ * ε j ^ 3))
