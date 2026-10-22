/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_45
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Theorem 3.46 lies in the constrained strong-convexity domain on real normed spaces.

Sampled owner-style declarations:
- project `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Theorem_2_30`
- project `StrongConvexOn.eq_of_isMinOn` in `Chap03/Theorem_3_45`
- mathlib `StrongConvexOn`
- mathlib `StrongConvexOn.strictConvexOn`

Best owner abstraction:
- source-facing: the constrained quadratic-growth and uniqueness consequences for a positive
  strongly convex objective on a convex feasible set
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: passing from strong convexity to strict convexity via
  `StrongConvexOn.strictConvexOn`

Primitive data:
- a feasible set `Q`, an objective `f`, a modulus `μ`, and feasible minimizers of `f` on `Q`

Derived API:
- the constrained quadratic-growth estimate
- uniqueness of feasible minimizers for `μ > 0`

This item is a direct recall of the chapter's owner-level constrained strong-convexity API, so it
keeps the canonical declarations central instead of restating them under parallel local names. -/

namespace StrongConvexOn

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.46 (quadratic-growth part): this is exactly the owner theorem
`StrongConvexOn.quadratic_growth_of_isMinOn_of_mem`. -/
recall StrongConvexOn.quadratic_growth_of_isMinOn_of_mem

/- Theorem 3.46 (uniqueness part): positive strong convexity gives strict convexity, so the
canonical constrained uniqueness theorem is `StrongConvexOn.eq_of_isMinOn`. -/
recall StrongConvexOn.eq_of_isMinOn

end StrongConvexOn

end
