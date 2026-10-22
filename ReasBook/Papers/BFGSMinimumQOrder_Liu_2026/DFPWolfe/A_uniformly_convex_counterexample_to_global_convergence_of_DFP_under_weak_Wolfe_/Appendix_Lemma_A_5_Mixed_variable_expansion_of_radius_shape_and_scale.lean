/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Lemma_A_5_Mixed_variable_expansion_of_radius_shape_and_scale.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion

public section

/- Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale) (1):
uniformly for bounded `(b, P, J)`, the independent-radius update has the stated
quadratic term and an order-three remainder. -/
#check (DFP.TwoLeg.Mixed.radiusExpansion :
  ∀ (β B : ℝ), 0 < β → β < 1 / 4 → 0 ≤ B →
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let y := DFP.TwoLeg.Mixed.map θ.1 (DFP.TwoLeg.Mixed.input θ r)
        y.1 - r - (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2)
      (DFP.TwoLeg.Mixed.parameterSet β B) C 3)

/- Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale) (2):
uniformly for bounded `(b, P, J)`, the recovered shape has the stated linear term
and an order-two remainder. -/
#check (DFP.TwoLeg.Mixed.shapeExpansion :
  ∀ (β B : ℝ), 0 < β → β < 1 / 4 → 0 ≤ B →
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let y := DFP.TwoLeg.Mixed.map θ.1 (DFP.TwoLeg.Mixed.input θ r)
        y.2.1 - 2 - (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r)
      (DFP.TwoLeg.Mixed.parameterSet β B) C 2)

/- Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale) (3):
uniformly for bounded `(b, P, J)`, the recovered high scale has linear term
`8 * b * r` and an order-two remainder. -/
#check (DFP.TwoLeg.Mixed.scaleExpansion :
  ∀ (β B : ℝ), 0 < β → β < 1 / 4 → 0 ≤ B →
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let y := DFP.TwoLeg.Mixed.map θ.1 (DFP.TwoLeg.Mixed.input θ r)
        y.2.2 - 1 - 8 * θ.1 * r)
      (DFP.TwoLeg.Mixed.parameterSet β B) C 2)
