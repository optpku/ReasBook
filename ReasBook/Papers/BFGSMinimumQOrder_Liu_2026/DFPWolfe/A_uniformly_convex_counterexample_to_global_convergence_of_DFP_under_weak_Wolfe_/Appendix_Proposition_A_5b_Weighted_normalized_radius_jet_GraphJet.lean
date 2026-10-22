/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_5b_Weighted_normalized_radius_jet_GraphJet.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet

public section

/- The polynomial graph path is shared DFP two-leg data. -/
#check (DFP.TwoLeg.graphJetPath :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℝ)

/- Its computation theorem gives all three path coordinates. -/
#check (DFP.TwoLeg.graphJetPath_apply :
  ∀ P₃ H₃ P₄ H₄ ε : ℝ,
    DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε =
      (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4, 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4))

/- The slow-graph polynomial is the specialized shared path. -/
#check (DFP.TwoLeg.slowGraphJetPath : ℝ → ℝ × ℝ × ℝ)

/- Its computation theorem records the exact slow-graph coefficients. -/
#check (DFP.TwoLeg.slowGraphJetPath_apply :
  ∀ ε : ℝ,
    DFP.TwoLeg.slowGraphJetPath ε =
      (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3))
