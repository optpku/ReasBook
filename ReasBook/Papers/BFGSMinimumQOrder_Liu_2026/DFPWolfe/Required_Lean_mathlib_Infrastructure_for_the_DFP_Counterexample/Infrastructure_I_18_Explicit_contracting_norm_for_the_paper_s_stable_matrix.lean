/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_18_Explicit_contracting_norm_for_the_paper_s_stable_matrix.lean
-/

module

public import ReasLib.Optimization.DFP.StableMatrix

public section

/- Infrastructure I.18 (Explicit contracting norm for the paper's stable matrix) (1):
the explicit weighted sum seminorm is equivalent to the standard norm on `Fin 2 → ℝ`. -/
#check (DFPStable.weightedSum_isEquivalent :
  DFPStable.weightedSum.IsEquivalent (normSeminorm ℝ (Fin 2 → ℝ)))

/- Infrastructure I.18 (Explicit contracting norm for the paper's stable matrix) (2):
the stable matrix contracts the explicit weighted sum seminorm by the rational rate `1 / 3 < 1`. -/
#check (DFPStable.weightedSum_contracts :
  (∀ x, DFPStable.weightedSum (DFPStable.map x) ≤
    (1 / 3 : ℝ) * DFPStable.weightedSum x) ∧
  (1 / 3 : ℝ) < 1)
