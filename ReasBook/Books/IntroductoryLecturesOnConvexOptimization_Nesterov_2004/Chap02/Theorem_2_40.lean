/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

/- Primary domain: constrained strong convexity and quadratic growth on complete real
inner-product spaces.

Sampled owner-style declarations:
* `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` in `Definition_2_14`
* `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`
* `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Definition_2_14`
* `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem` in `Theorem_2_30`

Best owner abstraction:
* source-facing/core: `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`
* bridge/view: the ambient-norm specialization `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem`

Primitive data:
* the seminorm `p`
* the feasible set `Q`
* the objective `f`
* the strong-convexity hypothesis `hf : StrongConvexOnWith p μ Q f`
* the feasible minimizer data `hxStar_mem : xStar ∈ Q` and `hxStar : IsMinOn f Q xStar`

Derived API:
* the constrained owner quadratic-growth theorem on a feasible set
* the whole-space ambient-norm specialization from `Theorem_2_30`

This file therefore introduces no second proof surface: Theorem 2.40 is recalled directly from
the weaker owner theorem in `Definition_2_14`, without keeping a redundant differentiable
specialization. -/

/- Theorem 2.40 is the direct owner recall of constrained quadratic growth at a feasible
minimizer. -/
recall StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem
