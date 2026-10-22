/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Lemma 3.1.2 is a source-facing recall in the chapter's `WithTop`-valued convex-analysis
domain.

Primary domain:
- restriction of a closed convex extended-real-valued function to a closed convex subset.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.restrict` from `Definition_3_1_1_5`
- `ClosedConvexOn.subset_withTopEffectiveDomain`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- `ClosedConvexOn.convex_constrainedEpigraph`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witness `hf : ClosedConvexOn Q f`
- the subset, closedness, and convexity data for `Q₁ ⊆ Q`

Derived API:
- the canonical owner theorem `ClosedConvexOn.restrict`

Source/core/bridge triage:
- source-facing: `ClosedConvexOn.restrict`
- core/canonical: `ClosedConvexOn`
- bridge/view: `constrainedEpigraph`, together with the closed/convex cylinder intersection proof
  internalized in the owner theorem

This file is recall-only: the owner theorem now lives where `ClosedConvexOn` itself is defined,
so the later chapter item reuses that exact owner theorem instead of introducing a duplicate
specialized copy.
-/

recall ClosedConvexOn.restrict
    {f : X → WithTop ℝ} {Q Q₁ : Set X}
    (hf : ClosedConvexOn Q f)
    (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁)
    (hQ₁Q : Q₁ ⊆ Q) :
    ClosedConvexOn Q₁ f

end
