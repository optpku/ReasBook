/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_1_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Corollary 3.1.3 is a recall-only item in the chapter's convex-analysis/minimax-linearization
domain.

Primary domain:
- finite pointwise maxima of closed convex functions and bounded constrained sublevel sets.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `maxTypeObjective`
- `constrainedSublevelSet`
- `exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets`

Best owner abstraction:
- source-facing: the bounded-level-set minimax-linearization corollary
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
- the equality of constrained `EReal` infima between the finite maximum and the weighted sum

The upstream max-sublevel-set theorem already has the exact interface needed here. This file
therefore imports that owner theorem directly and recalls its canonical name rather than routing
through a later recall surface or keeping a duplicate local wrapper. The textbook `Fin m`
specialization is recovered by instantiating the recalled theorem at `ι = Fin m`; it does not
need a separate local declaration here.
-/

recall exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets
