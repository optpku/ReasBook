/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_3_Exact_line_ratio_identity.lean
-/

module

public import ReasLib.Optimization.DFP.AbstractSecantStep

universe u

/- Lemma 3.3 (Exact line-ratio identity): for
`q = z.predictedDecrease = -(z.gradient ⬝ᵥ z.displacement)` and
`t = z.secantCurvature = z.displacement ⬝ᵥ z.gradientChange`, the abstract
secant step has `t / q = z.tau`. -/
#check (DFP.AbstractSecantStep.lineRatio :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    z.secantCurvature / z.predictedDecrease = z.tau)
