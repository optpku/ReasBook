/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open HasGeometricRateOfConvergence

universe u v

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-
Primary domain:
* norm decay for linear iterations on normed spaces

Sampled owner-style declarations:
* `HasGeometricRateOfConvergence` and
  `HasGeometricRateOfConvergence.of_step_bound` in `Definition_1_2_6.lean`
* `ContinuousLinearMap.le_opNorm` in mathlib
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`

Source/core/bridge triage:
* source-facing: the linear recurrence `a (k + 1) = A k (a k)` together with the operator-norm
  bound `‖A k‖ ≤ 1 - q`
* core/canonical: the owner statement `HasGeometricRateOfConvergence`
* bridge/view: the scalar one-step estimate obtained from `ContinuousLinearMap.le_opNorm`

Owner abstraction:
* `HasGeometricRateOfConvergence`; the linear-algebra hypotheses only serve to produce its
  one-step bound

Primitive data:
* the trajectory `a`
* the step maps `A`
* the recurrence `a (k + 1) = A k (a k)`
* the operator-norm bound `‖A k‖ ≤ 1 - q`

Derived API:
* the scalar inequality `‖a (k + 1)‖ ≤ (1 - q) * ‖a k‖`
* the resulting owner geometric-rate statement
* under the extra textbook hypothesis `0 < q < 1`, the corollary
  `HasGeometricRateOfConvergence.tendsto_zero`
-/

/-- Proposition 1.6.13: if `a_{k+1} = A_k a_k` and each step operator has operator norm at most
`1 - q`, then the norm sequence satisfies the owner geometric-rate statement with constant
`‖a_0‖`. The textbook positivity hypothesis `0 < q < 1` is only needed later for the convergence
corollary `HasGeometricRateOfConvergence.tendsto_zero`.

The source specializes this to `ℝⁿ`; the proof only uses the normed-space operator estimate
`ContinuousLinearMap.le_opNorm`. -/
-- Proof sketch: use the recurrence together with the submultiplicative estimate
-- `‖A_k a_k‖ ≤ ‖A_k‖ ‖a_k‖` to get `‖a (k + 1)‖ ≤ (1 - q) ‖a_k‖`. Iterating yields the
-- geometric bound recorded by `HasGeometricRateOfConvergence`.
theorem linear_iteration_contraction_estimate
    (q : ℝ) (A : ℕ → E →L[𝕜] E) (a : ℕ → E)
    (ha : ∀ k : ℕ, a (k + 1) = A k (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    HasGeometricRateOfConvergence (fun k : ℕ ↦ ‖a k‖) q ‖a 0‖ := by
  have hq₁ : q ≤ 1 := by
    have hnorm_nonneg : 0 ≤ ‖A 0‖ := norm_nonneg _
    linarith [hA 0, hnorm_nonneg]
  refine of_step_bound hq₁ le_rfl ?_
  intro k
  calc
    ‖a (k + 1)‖ = ‖A k (a k)‖ := by rw [ha k]
    _ ≤ ‖A k‖ * ‖a k‖ := (A k).le_opNorm (a k)
    _ ≤ (1 - q) * ‖a k‖ := by
      exact mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _)

end
