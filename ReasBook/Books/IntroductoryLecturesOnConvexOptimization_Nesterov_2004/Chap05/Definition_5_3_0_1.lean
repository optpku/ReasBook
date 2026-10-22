/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 5.3.0.1 is a recall-only item in the chapter's self-concordance domain.

Primary domain:
- self-concordant functions on an open convex domain in a real inner-product space.

Sampled owner-style declarations:
- `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative owner carrying the constant
  `M_f`;
- `IsSelfConcordantOn` from `Definition_5_1_1`, the existential source-facing relaxation;
- `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the canonical owner for the case
  `M_f = 1`;
- the definitional equality
  `IsStandardSelfConcordantOn dom f = IsSelfConcordantOnWith dom 1 f`.

Best owner abstraction:
- source-facing: standard self-concordance on `dom`;
- core/canonical: `IsStandardSelfConcordantOn dom f`;
- bridge/view: the definitional equality with `IsSelfConcordantOnWith dom 1 f`.

Primitive data:
- none; this item only recalls an existing owner.

Derived API:
- the owner predicate `IsStandardSelfConcordantOn`;
- the definitional equality with `IsSelfConcordantOnWith dom 1 f`.

This file therefore keeps no parallel local predicate for “self-concordant with constant `1`”.
It recalls the upstream owner from `Definition_5_1_1` directly, and the textbook specification is
checked by definitional equality instead of a redundant wrapper theorem. -/

/- Definition 5.3.0.1 recalls the canonical owner for standard self-concordance. -/
recall IsStandardSelfConcordantOn

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (dom : Set E) (f : E → ℝ)

/- The textbook phrase “exactly a self-concordant function with constant `M_f = 1`” is
definitionally the Chapter 5 owner specialized to `1`. -/
#check (Iff.rfl : IsStandardSelfConcordantOn dom f ↔ IsSelfConcordantOnWith dom 1 f)

end
