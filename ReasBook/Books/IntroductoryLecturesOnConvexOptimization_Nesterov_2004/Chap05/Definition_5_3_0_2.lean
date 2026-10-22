/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 5.3.0.2 lies in the chapter's `WithTop ℝ` convex-analysis domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` / `dom` from `Chap03/Definition_3_3`
- `extendedRealEffectiveDomain` / `dom` from `Chap03/Definition_3_1_1_2`
- mathlib `closure`

Best owner abstraction:
- source-facing: the textbook notation `Dom f`
- core/canonical: `closure (dom f)`
- bridge/view: the scoped notation declaration below

Primitive data:
- the effective domain owner `dom f`
- the topological closure operator

Derived API:
- `mem_Dom_iff`
- `dom_subset_Dom`

This item is only a source-facing notation bridge. Since `closure (dom f)` is already the exact
canonical owner, the refinement keeps no parallel alias for it and exposes only the notation and
its atomic bridge lemmas. -/

/-- Textbook notation for the closed effective domain of an `ℝ ∪ {+∞}`-valued function. -/
scoped[WithTopConvexAnalysis] notation "Dom " f:arg => closure (withTopEffectiveDomain f)

open scoped WithTopConvexAnalysis

/-- Membership in `Dom f` means membership in the closure of the effective domain. -/
@[simp] theorem mem_Dom_iff {X : Type u} [TopologicalSpace X]
    {f : X → WithTop ℝ} {x : X} :
    x ∈ Dom f ↔ x ∈ closure (dom f) :=
  Iff.rfl

/-- The effective domain is contained in its closed effective domain. -/
theorem dom_subset_Dom {X : Type u}
    [TopologicalSpace X] (f : X → WithTop ℝ) :
    dom f ⊆ Dom f := by
  simpa using (subset_closure : dom f ⊆ closure (dom f))
