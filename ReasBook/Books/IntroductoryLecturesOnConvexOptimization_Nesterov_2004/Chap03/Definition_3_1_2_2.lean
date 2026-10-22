/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped SupportFunction

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.1.2.2 is a recall-only item in the chapter's support-function domain.

Primary domain:
- support functions of subsets of a real inner-product space.

Sampled owner-style declarations:
- `supportFunction` from `Nesterov.Chap03.Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_eq`

Best owner abstraction:
- the chapter source-facing owner declaration `supportFunction`.

Primitive data:
- none; this is a recall-only item.

Derived API:
- the owner declaration `supportFunction`
- the defining bridge `supportFunction_apply`

Source/core/bridge triage:
- source-facing: the textbook support function of a set
- core/canonical: the owner declaration `supportFunction`
- bridge/view: the defining evaluation lemma `supportFunction_apply`

No exact mathlib owner for this `EReal`-valued support function was found in the sampled domain,
so this file recalls the chapter owner declarations directly instead of keeping a parallel local
copy of the same supremum construction. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

recall supportFunction

/- The defining evaluation formula is recalled through the canonical companion theorem. -/
recall supportFunction_apply
