/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Proposition 6.11 lies in the zero-model smoothing / primal-dual gap complexity domain.

Sampled owner declarations in this domain:
* `explicitModelSmoothingParameter` in `Chap06/Theorem_6_3`, the chapter owner for the chosen
  smoothing scale `μ(N)`;
* `optimized_primal_dual_gap_bound_for_explicit_model_smoothing` in `Chap06/Theorem_6_3`, the
  source-facing owner for the explicit-model gap estimate before fixing `ε`;
* `primal_dual_gap_le_epsilon_of_iteration_bound` in `Chap06/Theorem_6_3`, the stronger chapter
  corollary using the simpler but more restrictive hypothesis `(4 ‖A‖ √(D₁ D₂)) / ε ≤ N`;
* `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn` in
  `Chap06/Example_6_1_3`, the example-level recall showing that the displayed `L_μ` formula is a
  derived bound rather than a second public owner to be repackaged here.

Best owner abstraction:
* source-facing: the zero-model `ε`-accuracy bridge under the displayed threshold
  `√(N (N + 1)) ≥ 4 ‖A‖ √(D₁ D₂) / ε`;
* core/canonical: `optimized_primal_dual_gap_bound_for_explicit_model_smoothing`;
* bridge/view: the scalar inequality converting that optimized bound to the final `≤ ε`
  conclusion when `M = 0`.

Primitive data:
* the explicit-model smoothing hypotheses from Theorem 6.3;
* the zero-model specialization `M = 0`;
* the displayed lower bound on `√(N (N + 1))`.

Derived API:
* the final bound `f x_N - φ(\hat u_N) ≤ ε`.

Source/core/bridge triage:
* source-facing: the zero-model complexity consequence stated in Proposition 6.11;
* core/canonical: `optimized_primal_dual_gap_bound_for_explicit_model_smoothing`;
* bridge/view: the final scalar comparison between
  `4 ‖A‖ √(D₁ D₂) / √(N (N + 1))` and `ε`.

The previous version introduced a tautological wrapper that merely returned its own threshold
hypothesis together with definitional equalities for `μ` and `L_μ`. This refinement deletes that
parallel packaging and states Proposition 6.11 as the actual zero-model specialization of the
chapter smoothing-gap owner.
-/

-- Proof sketch: specialize
-- `optimized_primal_dual_gap_bound_for_explicit_model_smoothing` at `M = 0`, so the upper bound
-- becomes `4 ‖A‖ √(D₁ D₂) / √(N (N + 1))`. Then use the displayed threshold
-- `4 ‖A‖ √(D₁ D₂) / ε ≤ √(N (N + 1))` to bound that quantity by `ε`.
/-- Proposition 6.11: in the case `M = 0`, if the explicit-model smoothing hypotheses from
Theorem 6.3 hold and
`√(N (N + 1)) ≥ 4 ‖A‖ √(D₁ D₂) / ε`, then the primal-dual gap at `(x_N, \hat u_N)` is at most
`ε`. -/
theorem zero_model_smoothing_complexity_relation
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ ε : ℝ) (hε : 0 < ε) (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
          (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))))
    (hiter :
      (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ε ≤
        Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ ε := by
  have hgap :=
    optimized_primal_dual_gap_bound_for_explicit_model_smoothing
      A f fμ φ N xN u D₁ D₂ 0 hD₁ hD₂ hxN_approx hφ_le hfμ_le (by
        simpa using hsmoothed_gap)
  have hupper :
      f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) := by
    simpa using hgap.2
  have hsqrt_pos : 0 < Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
    positivity
  have hiter' :
      4 * ‖A‖ * Real.sqrt (D₁ * D₂) ≤
        ε * Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
    have hiter'' := (div_le_iff₀ hε).mp hiter
    simpa [mul_comm] using hiter''
  have hε_bound :
      (4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) ≤ ε := by
    have :
        (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) ≤ ε :=
      (div_le_iff₀ hsqrt_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hiter')
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact le_trans hupper hε_bound

end
