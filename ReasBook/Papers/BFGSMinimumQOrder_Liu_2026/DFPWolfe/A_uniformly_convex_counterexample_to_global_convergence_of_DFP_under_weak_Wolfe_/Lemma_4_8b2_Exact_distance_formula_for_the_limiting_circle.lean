/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_8b2_Exact_distance_formula_for_the_limiting_circle.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Distance

public section

/- Lemma 4.8b2 (Exact distance formula for the limiting circle) -/
#check (DFP.TwoPhaseOrbit.infDist_limitCircle :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ), 0 < G →
    ∀ (x : EuclideanSpace ℝ (Fin 2)),
      Metric.infDist x (DFP.TwoPhaseOrbit.limitCircle C G) = |‖x - C‖ - G|)
