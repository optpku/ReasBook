/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_5_11_Global_realized_objective.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective

/- Definition 5.11 (Global realized objective):
`DFP.TwoPhaseOrbit.realizedObjective orbit C G` is the function
`fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z`. -/
#check (DFP.TwoPhaseOrbit.realizedObjective :
  DFP.TwoPhaseOrbit → EuclideanSpace ℝ (Fin 2) → ℝ →
    EuclideanSpace ℝ (Fin 2) → ℝ)

#check (DFP.TwoPhaseOrbit.realizedObjective_apply :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
      (z : EuclideanSpace ℝ (Fin 2)),
    orbit.realizedObjective C G z =
      (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z)
