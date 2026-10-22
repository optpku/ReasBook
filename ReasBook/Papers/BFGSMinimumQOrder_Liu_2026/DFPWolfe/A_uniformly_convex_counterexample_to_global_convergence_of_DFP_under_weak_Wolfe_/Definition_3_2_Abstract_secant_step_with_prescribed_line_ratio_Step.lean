/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_3_2_Abstract_secant_step_with_prescribed_line_ratio_Step.lean
-/

module

public import ReasLib.Optimization.DFP.AbstractSecantStep

public section

open scoped Matrix

section

variable {n : Type u} [Fintype n]

/- This forwarding bridge exposes the shared abstract secant-step constructor
to existing importers. -/
#check (DFP.AbstractSecantStep.ofMatrices :
  (H : Matrix n n ℝ) → (g : n → ℝ) → (A : Matrix n n ℝ) → (τ : ℝ) →
    H.PosDef → A.PosDef → 0 < τ → g ≠ 0 → DFP.AbstractSecantStep n)

end
