/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped ConvexAnalysis

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → EReal)

/- Theorem 3.1.3 is a recall-only item in the chapter's extended-real convex-analysis domain.

Primary domain:
- convex sublevel sets for `EReal`-valued convex functions on an `ℝ`-module.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn.convex_le`
- project `mem_levelSet_iff`
- chapter `extendedRealRealPart`

Best owner abstraction:
- the owner theorem `ConvexOn.convex_le`

Primitive data:
- `dom f`
- `extendedRealRealPart f`
- the owner sublevel set `{x ∈ dom f | extendedRealRealPart f x ≤ β}`

Derived API:
- the convexity conclusion for that owner sublevel set

The previous file recalled a chapter-local wrapper around the owner theorem. Since
`Theorem_3_1_1_3` now keeps only direct owner reuse and no parallel sublevel-set alias, this file
checks the specialized owner theorem itself at the canonical owner surface. -/

#check
  (show ConvexOn ℝ (dom f) (extendedRealRealPart f) →
      ∀ β : ℝ, Convex ℝ {x | x ∈ dom f ∧ extendedRealRealPart f x ≤ β} from
    ConvexOn.convex_le)

end
