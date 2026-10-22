/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_5_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient
open Matrix

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 1)
local notation "Mat" => Matrix (Fin 1) (Fin 1) ℝ

/- Primary domain: one-dimensional quadratic counterexamples for the weighted sampled point built
from an actual optimal-method trajectory.

Sampled owner declarations before refining this file:
* `GeneralOptimalMethodScheme` in `Algorithm_2_2`, the chapter's owner for genuine Algorithm 2.2
  trajectories, including the step-`(c)` descent axiom;
* `OptimalMethodRecurrence.weightedAverage` in `Algorithm_2_2`, the canonical owner of the
  weighted sampled point attached to the underlying recurrence data;
* `constantStepSchemeIToGeneralOptimalMethodScheme` in `Algorithm_2_3`, the canonical bridge from
  the recursive exact-step trajectory to an actual optimal-method scheme;
* `quadraticObjective` and `quadraticObjective_gradient_eq` in Chapter 1, the canonical Euclidean
  quadratic owner and its gradient formula.

Source/core/bridge triage:
* source-facing: the counterexample theorem for the weighted sampled point at stage `k`;
* core/canonical: an actual `GeneralOptimalMethodScheme` witness together with the owner weighted
  sampled point inherited from its underlying recurrence;
* bridge/view: `constantStepSchemeIToGeneralOptimalMethodScheme`, used only to realize a genuine
  Algorithm 2.2 trajectory from the recursive exact-step construction.

Primitive data:
* the linear coefficient `linearCoeff` of the degenerate quadratic objective
  `quadraticObjective 0 linearCoeff 0`;
* the actual scheme witness `method`.

Derived API:
* the weighted sampled point
  `\hat y_k = (λ_k / (1 - λ_k)) ∑_{i < k} (α_i / λ_{i+1}) y_i`,
  owned by `OptimalMethodRecurrence.weightedAverage`;
* the constant-gradient evaluation
  `∇ (quadraticObjective 0 linearCoeff 0) x = linearCoeff`.
-/

/-- Theorem 2.23: for every stage `k` and threshold `M`, there is a one-dimensional quadratic
objective together with an actual optimal-method scheme whose weighted sampled point
`\hat y_k = (λ_k / (1 - λ_k)) ∑_{i < k} (α_i / λ_{i+1}) y_i`,
formed from the owner data `λ_k = method.weight k`, `α_i = method.alpha i`, and `y_i = method.y i`,
has gradient norm at least `M`. -/
-- Proof sketch: fix `k` and `M`. Use the degenerate quadratic owner
-- `quadraticObjective 0 linearCoeff 0` with `linearCoeff = M e₀`. Its gradient is constant,
-- `∇ f x = linearCoeff` for every `x`. Realize an actual Algorithm 2.2 trajectory for this
-- objective by the canonical bridge
-- `constantStepSchemeIToGeneralOptimalMethodScheme`. Since the gradient is constant, the weighted
-- sampled point `\hat y_k` can be arbitrary and still satisfies
-- `‖∇ f \hat y_k‖ = ‖linearCoeff‖ = |M| ≥ M`.
theorem exists_estimatingSequence_counterexample_with_large_gradient_norm
    (k : ℕ) (M : ℝ) :
    ∃ (linearCoeff : E)
      (method : GeneralOptimalMethodScheme (quadraticObjective 0 linearCoeff (0 : Mat))
        1 0 0 1),
      let yHat := method.weightedAverage method.y k
      M ≤ ‖∇ (quadraticObjective 0 linearCoeff (0 : Mat)) yHat‖ := by
  let linearCoeff : E :=
    EuclideanSpace.single 0 M
  let f : E → ℝ := quadraticObjective 0 linearCoeff (0 : Mat)
  have hgrad_eq : ∇ f = fun _ ↦ linearCoeff := by
    simpa [f] using quadraticObjective_gradient_eq 0 linearCoeff (0 : Mat) (by simp)
  have hDiff : Differentiable ℝ f := by
    exact
      (symmetric_quadratic_contDiff_and_gradient_lipschitz
        0 linearCoeff (0 : Mat) (by simp)).1.differentiable one_ne_zero
  have hGrad : LipschitzWith 1 (∇ f) := by
    rw [hgrad_eq]
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simp
  let method :
      GeneralOptimalMethodScheme f 1 0 0 1 :=
    constantStepSchemeIToGeneralOptimalMethodScheme
      f 1 0 0 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hDiff hGrad
  have hmethod :
      GeneralOptimalMethodScheme (quadraticObjective 0 linearCoeff (0 : Mat))
        1 0 0 1 := by
    simpa [f] using method
  have hlinearCoeff_norm : ‖linearCoeff‖ = |M| := by
    simp [linearCoeff]
  refine ⟨linearCoeff, hmethod, ?_⟩
  change M ≤
    ‖∇ (quadraticObjective 0 linearCoeff (0 : Mat)) (hmethod.weightedAverage hmethod.y k)‖
  rw [show
      ∇ (quadraticObjective 0 linearCoeff (0 : Mat))
        (hmethod.weightedAverage hmethod.y k) = linearCoeff by
      simpa [f] using congrFun hgrad_eq (hmethod.weightedAverage hmethod.y k)]
  rw [hlinearCoeff_norm]
  exact le_abs_self M
