/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_6_0_The_selected_weak_Wolfe_constants_are_admissible.lean
-/

module

public import ReasLib.Optimization.LineSearch

public section

/- Lemma 6.0 (The selected weak Wolfe constants are admissible): the constants
`c₁ = 1 / 4` and `c₂ = 3 / 4` satisfy the weak Wolfe coefficient bounds. -/
#check (LineSearch.IsWeakWolfe.selectedConstantsAdmissible :
  0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) < 1)
