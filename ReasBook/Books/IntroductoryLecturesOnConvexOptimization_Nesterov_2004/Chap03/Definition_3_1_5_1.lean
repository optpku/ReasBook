/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

universe u

/- This item is a source-facing recall in the chapter's extended-valued constrained
subdifferential domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`, the upstream source-facing owner for affine lower-support inequalities on the
  effective domain;
- `subdifferential`, the unconstrained set-valued owner derived from `IsSubgradientAt`;
- `constrainedSubdifferential`, the canonical owner for the textbook constrained subdifferential;
- `mem_constrainedSubdifferential_iff`, the defining membership expansion for that owner.

Best owner abstraction:
- `constrainedSubdifferential`

Primitive data:
- a feasible set `Q`
- an extended-real-valued function `f`
- a base point `x0`

Derived API:
- the source-facing notation `∂[Q] f(x0)`
- `mem_constrainedSubdifferential_iff`

Source/core/bridge triage:
- source-facing: the textbook constrained subdifferential `∂_Q f(x₀)`
- core/canonical: `constrainedSubdifferential`
- bridge/view: `mem_constrainedSubdifferential_iff`

This file therefore reuses the existing chapter owner directly instead of introducing a Euclidean
wrapper, a theorem-shaped alias, or a second local notation shell. The recall signatures below
match the upstream binder surface exactly. -/

/- Definition 3.1.5.1: the constrained subdifferential of an extended-real-valued function `f`
at a point `x₀` relative to a set `Q` is the canonical set `constrainedSubdifferential Q f x₀`,
written `∂[Q] f(x₀)`, consisting of all vectors whose affine support inequality holds for every
`y ∈ Q`, with `x₀` itself lying in `Q ∩ dom f`. -/
recall constrainedSubdifferential
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : Set V) (f : V → WithTop ℝ) (x0 : V) : Set V

/-- Membership in the constrained subdifferential unfolds to the feasibility condition
`x₀ ∈ Q ∩ dom f` together with the affine lower-support inequality on `Q`. -/
recall mem_constrainedSubdifferential_iff
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Q : Set V} {f : V → WithTop ℝ} {x0 g : V} :
    g ∈ ∂[Q] f(x0) ↔
      x0 ∈ Q ∧
        x0 ∈ dom f ∧
        ∀ ⦃y : V⦄, y ∈ Q →
          f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ)
