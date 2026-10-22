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

/-
Corollary 3.2.3 lies in the constrained strong-convexity domain for real normed spaces.

Sampled owner-style declarations:
- project `StrongConvexOn.quadratic_growth_of_isMinOn` in `Theorem_2_30`
- mathlib `StrongConvexOn`
- mathlib `StrongConvexOn.strictConvexOn`
- project `StrongConvexOn.eq_of_isMinOn` in `Theorem_3_45`

Best owner abstraction:
- `StrongConvexOn Q μ f`

Primitive data:
- a feasible set `Q`, an objective `f`, a strong-convexity modulus `μ`, and feasible minimizers
  of `f` on `Q`

Derived API:
- the constrained quadratic-growth bound at a feasible minimizer
- uniqueness of the feasible minimizer when `μ > 0`

Source/core/bridge triage:
- source-facing: Corollary 3.2.3, the constrained quadratic-growth estimate and uniqueness
  consequence
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: `StrongConvexOn.strictConvexOn` together with
  `StrictConvexOn.eq_of_isMinOn`
-/

namespace StrongConvexOn

variable {E : Type u} [NormedAddCommGroup E]
variable [NormedSpace ℝ E]

/- Corollary 3.2.3 (quadratic-growth part): this is the direct constrained owner theorem already
exposed in Chapter 2. -/
recall StrongConvexOn.quadratic_growth_of_isMinOn_of_mem

/- Corollary 3.2.3 (uniqueness part): this is the direct chapter owner theorem already exposed in
`Theorem_3_45`. -/
recall StrongConvexOn.eq_of_isMinOn

end StrongConvexOn

end
