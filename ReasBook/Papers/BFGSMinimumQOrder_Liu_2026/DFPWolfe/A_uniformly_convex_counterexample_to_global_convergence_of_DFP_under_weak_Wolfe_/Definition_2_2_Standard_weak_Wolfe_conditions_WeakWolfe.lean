/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_2_2_Standard_weak_Wolfe_conditions_WeakWolfe.lean
-/

module

public import ReasLib.Optimization.LineSearch

universe u

/- Compatibility bridge for the former weak-Wolfe owner. -/
#check (LineSearch.IsWeakWolfe :
  {E : Type u} → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] → [CompleteSpace E] →
    ℝ → ℝ → (E → ℝ) → E → E → Prop)
