/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_6_1_Exact_Armijo_decrease_ratio_identity.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective.DecreaseRatio

public section

/- Lemma 6.1 (Exact Armijo decrease-ratio identity): for every two-phase
orbit satisfying the endpoint interpolation hypotheses, the exact normalized
decrease ratio has the translated quadratic and endpoint-correction form. -/
#check (DFP.TwoPhaseOrbit.realizedObjective_decreaseRatio :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ,
      let s := orbit.endpoint (k + 1) - orbit.endpoint k
      let q := -inner ℝ (orbit.endpointGradient k) s
      0 < q →
        (orbit.realizedObjective C G (orbit.endpoint k) -
            orbit.realizedObjective C G (orbit.endpoint (k + 1))) / q =
          1 - ‖s‖ ^ 2 / (2 * q) +
            inner ℝ (orbit.endpointCorrection C k) s / q)
