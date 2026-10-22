/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_1_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.12 is a recall-only item in the chapter's convex-analysis/minimax-linearization
domain.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `maxTypeObjective`
- `constrainedSublevelSet`
- `exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets`

Best owner abstraction:
- source-facing: the bounded-level-set minimax-linearization statement of Theorem 3.12
- core/canonical: `maxTypeObjective fs`, the bounded feasible sublevel owner
  `constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α`, and the
  simplex coefficient owner `StdSimplex ℝ ι`
- bridge/view: the weighted-sum expression `∑ i, coeffs.weights i * fs i x`, derived from the
  canonical simplex data

Primitive data:
- a nonempty finite family `fs : ι → E → ℝ`
- closed convexity of each component on `Q`
- boundedness of the constrained sublevel sets of `maxTypeObjective fs`

Derived API:
- the simplex coefficient vector `coeffs : StdSimplex ℝ ι`
- the equality of constrained `EReal` infima between `maxTypeObjective fs` and the simplex-weighted
  objective

The previous version introduced a second public theorem name with exactly the same interface as the
upstream source-facing theorem
`exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets`. Since that theorem
already has the correct statement and owner-level data, this file now recalls it directly instead
of keeping a duplicate wrapper. In particular, the old file-level `[FiniteDimensional ℝ E]`
assumption was redundant and is removed here because the canonical theorem does not use it.
-/

recall exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets
