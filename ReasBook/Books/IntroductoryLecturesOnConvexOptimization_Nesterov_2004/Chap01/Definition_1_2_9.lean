/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

universe u

/- Definition 1.2.9 lies in the black-box optimization-oracle / differential-answer-map domain.

Source/core/bridge triage:
* source-facing: the textbook zero-, first-, and second-order oracle replies attached to an
  objective function;
* core/canonical: the Chapter 1 owner abstraction `Query → Answer` from Definition 1.2.2, with
  first- and second-order replies constrained by the pointwise owners `HasGradientAt` and
  `HasFDerivAt (∇ f)`;
* bridge/view: the Hessian matrix view from `Definition_1_4_16.lean`, which presents the owner
  Hessian operator `hessian f x` in coordinates.

Relevant owner-style declarations sampled before refining:
* `#check (Query → Answer)` in `Definition_1_2_2.lean`;
* `HasGradientAt` in `Definition_1_4_6.lean`, the pointwise owner for genuine first-order data;
* `SatisfiesExactLineSearch` in `Definition_1_6_3.lean`, which keeps `HasGradientAt` explicit
  rather than trusting the totalized gradient alone;
* `HasWeightedGradientSecondOrderExpansionAt` in `Definition_1_8_4.lean`, whose canonical bridge
  target is `HasGradientAt f g x ∧ HasFDerivAt (∇ f) H x`.

Owner abstraction:
* the oracle answer-map type `Query → Answer`

Primitive data:
* the objective function itself

Derived API:
* the zero-order value map `f`
* the first-order value-gradient map `x ↦ (f x, ∇ f x)` under the genuine-gradient owner
  `∀ x, HasGradientAt f (∇ f x) x`
* the second-order value-gradient-Hessian map `x ↦ (f x, ∇ f x, hessian f x)` under the genuine
  first- and second-order owners `HasGradientAt` and `HasFDerivAt (∇ f)`

Accordingly, this file recalls the canonical answer maps directly and introduces no parallel
public wrapper names for them. The zero-order clause stays at the bare function level, while the
first- and second-order clauses make the needed regularity assumptions explicit so that the
displayed answers are genuine differential data rather than totalized placeholders. -/

variable {E : Type u}
variable (f : E → ℝ)

/- Definition 1.2.9 (1): a zero-order oracle for the objective function `f` returns the value
`f x` at the query point `x`. -/
#check (f : E → ℝ)

section HigherOrder

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.2.9 (2): for an objective whose displayed gradient answers are genuine, a
first-order oracle returns both the value and the gradient at the query point. -/
#check
  ((fun _ x ↦ (f x, ∇ f x)) :
    (∀ x : E, HasGradientAt f (∇ f x) x) → E → ℝ × E)

/- Definition 1.2.9 (3): for an objective whose displayed gradient and Hessian answers are
genuine, a second-order oracle returns the value, the gradient, and the Hessian operator at the
query point. -/
#check
  ((fun _ _ x ↦ (f x, ∇ f x, hessian f x)) :
    (∀ x : E, HasGradientAt f (∇ f x) x) →
      (∀ x : E, HasFDerivAt (∇ f) (hessian f x) x) →
        E → ℝ × E × (E →L[ℝ] E))

end HigherOrder
