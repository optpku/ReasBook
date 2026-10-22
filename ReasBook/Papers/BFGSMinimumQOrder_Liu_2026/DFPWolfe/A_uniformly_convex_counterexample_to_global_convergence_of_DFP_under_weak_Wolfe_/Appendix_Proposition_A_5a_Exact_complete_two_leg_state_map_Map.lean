/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_5a_Exact_complete_two_leg_state_map_Map.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

/- Appendix Proposition A.5a (Exact complete two-leg state map): the explicit
signed factored map on the common two-leg state space. -/
#check (DFP.TwoLeg.stateMap :
  (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ))
