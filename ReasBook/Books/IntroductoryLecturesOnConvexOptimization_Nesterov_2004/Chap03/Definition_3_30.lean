/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_26

-- Declarations for this item will be appended below by the statement pipeline.

universe uE uι

variable {E : Type uE} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.30 is a recall-only item in the chapter's sampled affine-model aggregation domain.

Primary domain:
- convex optimization models obtained by averaging sampled affine minorants.

Sampled owner-style declarations:
- `StdSimplex.Strict` in `Nesterov.Chap03.Definition_3_4`, the earlier chapter owner for
  the textbook's strict-positivity side condition on simplex coefficients
- `sampledAffineMinorant` in `Nesterov.Chap03.Proposition_3_26`, the chapter owner for one
  sampled affine oracle model
- the mathlib affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ`,
  the canonical owner for the aggregated model
- `sum_smul_sampledAffineMinorant_apply` in `Nesterov.Chap03.Proposition_3_26`, the evaluation
  bridge for that canonical affine-map sum

Best owner abstraction:
- `source-facing`: the textbook aggregated linear model built from sampled points
  `y₀, …, y_N`, weights, and the sampled slopes `g (y k)`
- `core/canonical`: the affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i))`
- `bridge/view`: the simplex specialization `α = weights.weights` together with the sampled slope
  family `g ∘ y`; `StdSimplex.Strict` records the source's redundant strict-positivity side
  condition when needed, while the later affine-map owner in
  `Nesterov.Chap03.Proposition_3_27` is the corresponding packaged affine view of the same
  finite averaging construction

Primitive data:
- `weights : StdSimplex ℝ (Fin (N + 1))`
- `y : Fin (N + 1) → E`
- `f : E → ℝ`
- `g : E → E`

Derived API:
- the owner specialization
  `∑ i, weights.weights i • sampledAffineMinorant (y i) (g (y i)) (f (y i))`
- the pointwise sum formula obtained by unfolding that owner definition

Source/core/bridge triage:
- `source-facing`: the sampled aggregated linear model itself
- `core/canonical`: the affine-map sum above
- `bridge/view`: evaluation of the simplex specialization by
  `sum_smul_sampledAffineMinorant_apply`

Definition 3.30 adds no new mathematical data beyond this owner specialization, so this file
checks the canonical owner expression directly and introduces no parallel public alias such as
`aggregatedLinearModel`.
-/

section

variable {N : ℕ}

variable (weights : StdSimplex ℝ (Fin (N + 1))) (y : Fin (N + 1) → E)
variable (f : E → ℝ) (g : E → E) (x : E)

/- Definition 3.30: the aggregated linear model attached to sample points `y₀, …, y_N` and a
normalized coefficient vector is the direct simplex specialization of the canonical affine-map
sum of the sampled affine minorants. The textbook additionally assumes these weights are strictly
positive, but the defining expression depends only on the normalized simplex data. -/
#check (∑ i, weights.weights i • sampledAffineMinorant (y i) (g (y i)) (f (y i)) : E →ᵃ[ℝ] ℝ)

/- Evaluating the canonical affine-map sum for Definition 3.30 recovers the weighted sum of the
sampled affine oracle models. -/
#check (sum_smul_sampledAffineMinorant_apply weights.weights y (g ∘ y) f x)

end
