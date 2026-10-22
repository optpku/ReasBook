/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_6_6_Positive_definiteness_of_every_DFP_matrix.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Iteration

public section

namespace DFP.TwoPhaseOrbit

/- Lemma 6.6 (Positive definiteness of every DFP matrix): every inverse-Hessian
matrix in the flattened endpoint sequence is positive definite; `Matrix.PosDef`
also includes symmetry. -/
#check (endpointMetric_posDef :
  ∀ (orbit : DFP.TwoPhaseOrbit),
    (∀ j, State.ExactCycle (orbit.state j)) →
      ∀ k : ℕ, (orbit.endpointMetric k).PosDef)

end DFP.TwoPhaseOrbit
