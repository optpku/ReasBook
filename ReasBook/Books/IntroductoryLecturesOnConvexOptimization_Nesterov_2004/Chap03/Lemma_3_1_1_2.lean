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

/- Lemma 3.1.1.2 is a source-facing recall in the chapter's closed-convex `WithTop`-valued
convex-analysis domain.

Primary domain:
- restriction of a closed convex extended-real-valued function to a closed convex subset.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `ClosedConvexOn.restrict`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- mathlib `ConvexOn.subset`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- a witness `hf : ClosedConvexOn Q f`
- the subset, closedness, and convexity data for `Q₁ ⊆ Q`

Derived API:
- the canonical owner theorem `ClosedConvexOn.restrict`

Source/core/bridge triage:
- source-facing: the restriction lemma for closed convex functions on a closed convex subset
- core/canonical: `ClosedConvexOn`
- bridge/view: `constrainedEpigraph` together with mathlib `ConvexOn.subset`

The main entry now reuses the owner theorem at the same ambient abstraction level as
`ClosedConvexOn` itself, instead of recalling a later `ℝⁿ`-specialized duplicate. -/

recall ClosedConvexOn.restrict
    {f : X → WithTop ℝ} {Q Q₁ : Set X}
    (hf : ClosedConvexOn Q f)
    (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁)
    (hQ₁Q : Q₁ ⊆ Q) :
    ClosedConvexOn Q₁ f

end
