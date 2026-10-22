/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

universe u

/- Definition 3.16 is a recall-only item in the chapter's common-subdifferential domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `subdifferential`, the pointwise owner for subgradients;
- `commonRegularSubdifferential`, the canonical owner for the intersection of pointwise
  subdifferentials over a set;
- `mem_commonRegularSubdifferential_iff`, the membership bridge for that owner.

Best owner abstraction:
- `commonRegularSubdifferential`

Primitive data:
- an extended-real-valued function `f`;
- a set `X`.

Derived API:
- the textbook notation `∂̂ f(X)`;
- the membership expansion `g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, g ∈ ∂ f(x)`.

Source/core/bridge triage:
- source-facing: the epigraph facet of `X` with respect to `f`;
- core/canonical: `commonRegularSubdifferential f X`;
- bridge/view: `mem_commonRegularSubdifferential_iff`.

The textbook defines the epigraph facet for a nonempty closed convex set `X ⊆ dom f`, but those
extra hypotheses are not primitive data for the underlying owner. This file therefore reuses the
existing common-subdifferential owner directly rather than introducing a new synonym or keeping a
Euclidean-coordinate wrapper.
-/

section

/- Definition 3.16: for a nonempty closed convex set `X ⊆ dom f`, the epigraph facet of `X` with
respect to `f` is the common regular subdifferential `∂̂ f(X) = ⋂ x ∈ X, ∂ f(x)`. -/
recall commonRegularSubdifferential
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → WithTop ℝ) (X : Set V) : Set V

/- Membership in the recalled epigraph facet means belonging to every pointwise subdifferential
`∂ f(x)` for `x ∈ X`. -/
recall mem_commonRegularSubdifferential_iff
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → WithTop ℝ} {X : Set V} {g : V} :
    g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, g ∈ ∂ f(x)

end
