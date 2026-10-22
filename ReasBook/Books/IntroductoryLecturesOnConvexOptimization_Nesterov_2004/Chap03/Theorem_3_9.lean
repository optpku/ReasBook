/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped WithTopConvexAnalysis

universe u v

variable {ι : Type u} {X : Type v}

/- Theorem 3.9 is a recall-only `Set.univ` specialization in the chapter's closed-convex
pointwise-supremum domain.

Primary domain:
- subset-indexed pointwise suprema of `WithTop ℝ`-valued functions and their closed-convex
  stability.

Sampled owner-style declarations:
- `pointwiseSupremumOn`
- `pointwiseSupremumOnEffectiveDomain`
- `ClosedConvexOn`
- `ClosedConvexOn.pointwise_sSup`

Best owner abstraction:
- the core owner theorem `ClosedConvexOn.pointwise_sSup`;
- the source-facing surface in this numbered item is only the `Δ = Set.univ` specialization.

Primitive data:
- none in this file; the owner object and theorem already live upstream.

Derived API:
- this recall-only `Set.univ` specialization.

Source/core/bridge triage:
- source-facing: the pointwise-supremum closed-convex stability theorem over all indices;
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`, and
  `ClosedConvexOn.pointwise_sSup`;
- bridge/view: the `Set.univ` specialization.

This file now recalls the canonical subset-indexed owner theorem directly instead of depending on
the former bridge theorem name `ClosedConvexOn.pointwise_iSup`. The nonemptiness hypothesis
remains essential because the `Set.univ` specialization needs a nonempty index set.
-/

section

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] [Nonempty ι]
variable {Q : Set X} {φ : X → ι → WithTop ℝ}

/- Theorem 3.9: for a nonempty index type, if each slice `x ↦ φ x y` is closed and convex on
`Q`, then the pointwise supremum over all indices is closed and convex on its canonical effective
domain. -/
#check
  (show (∀ y : ι, ClosedConvexOn Q (fun x ↦ φ x y)) →
      ClosedConvexOn (pointwiseSupremumOnEffectiveDomain Q univ φ)
        (pointwiseSupremumOn univ φ) from
    fun hφ ↦ ClosedConvexOn.pointwise_sSup univ_nonempty (fun y _ ↦ hφ y))

end

end
