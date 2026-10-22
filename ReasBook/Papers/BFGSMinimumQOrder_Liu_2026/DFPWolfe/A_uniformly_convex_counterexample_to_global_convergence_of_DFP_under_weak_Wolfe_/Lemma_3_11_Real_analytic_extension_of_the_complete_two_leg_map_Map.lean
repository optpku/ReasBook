/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

noncomputable section

namespace DFP.TwoLeg

/-- The complete two-leg coordinate map after removing the singular powers of `ε`. -/
abbrev extendedMap : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
  stateMap

/-- The analytically extended complete map fixes the factored base point. -/
theorem extendedMap_base :
    extendedMap ((0, 2, 1) : ℝ × ℝ × ℝ) = (0, 2, 1) :=
  stateMap_base

end DFP.TwoLeg
