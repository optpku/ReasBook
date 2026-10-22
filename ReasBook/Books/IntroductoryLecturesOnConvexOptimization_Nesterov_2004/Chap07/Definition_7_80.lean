/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Definition 7.80 lies in the chapter's extended-valued subdifferential domain.

Mandatory domain-style sampling before refinement:
- `IsSubgradientAt`, `subdifferential`, and the notation `∂ f(x)` in
  `Chap03/Definition_3_1_5`, the chapter owner for extended-valued subdifferentials;
- `commonRegularSubdifferential` in `Chap03/Definition_3_1_5_4`, which packages the stronger
  common-subgradient condition and confirms that Chapter 3 already treats pointwise
  subdifferentials as the primitive owner data;
- `closedConvexFunction_of_subdifferential_nonempty` in `Chap03/Proposition_3_24`, whose
  hypothesis is the same owner-level pointwise nonemptiness condition on a set.

Best owner abstraction:
- the pointwise chapter owner `∂ f(x)`.

Primitive data:
- the function `f`;
- the set `Q`;
- the owner-level pointwise nonemptiness condition `∀ x ∈ Q, (∂ f(x)).Nonempty`.

Derived API:
- the named source-facing predicate
  `EverywhereNonemptySubdifferentialCondition`;
- the pointwise elimination lemma
  `EverywhereNonemptySubdifferentialCondition.subdifferential_nonempty`.

Source/core/bridge triage:
- source-facing: Definition 7.80's condition that every point of `Q` has a nonempty
  subdifferential;
- core/canonical: the Chapter 3 owner `subdifferential` and its notation `∂ f(x)`;
- bridge/view: the elimination theorem exposing the pointwise owner-level consequence.

The textbook states this on a closed convex function over `ℝⁿ`, but the mathematical content of
the condition itself only depends on the existing chapter owner `∂ f(x)` on a real inner-product
space. This file therefore keeps the source-facing named condition while removing the duplicate
Euclidean wrapper layer and writing the public API directly on the canonical owner surface.
-/

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Definition 7.80: `f` satisfies the everywhere nonempty subdifferential condition on `Q` when
every point `x ∈ Q` has a nonempty subdifferential `∂ f(x)`. -/
def EverywhereNonemptySubdifferentialCondition
    (f : V → WithTop ℝ) (Q : Set V) : Prop :=
  ∀ ⦃x : V⦄, x ∈ Q → (∂ f(x)).Nonempty

-- Proof sketch: apply the defining predicate of
-- `EverywhereNonemptySubdifferentialCondition` at the chosen point `x ∈ Q`.
/-- Under the everywhere nonempty subdifferential condition, each point of `Q` admits a
subgradient of `f`. -/
theorem EverywhereNonemptySubdifferentialCondition.subdifferential_nonempty
    {f : V → WithTop ℝ} {Q : Set V}
    (h : EverywhereNonemptySubdifferentialCondition f Q) {x : V} (hx : x ∈ Q) :
    (∂ f(x)).Nonempty :=
  h hx

end
