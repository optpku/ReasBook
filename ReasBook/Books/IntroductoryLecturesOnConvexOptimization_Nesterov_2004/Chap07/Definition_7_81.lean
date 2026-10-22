/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 7.81 lies in the chapter's real-valued whole-space subdifferential domain.

Mandatory domain-style sampling before refinement:
- `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in
  `Nesterov.Chap03.Theorem_3_44`, the chapter owner for real-valued relative
  subdifferentials;
- `∂[Set.univ] (Ψ u)(x)` in `Nesterov.Chap07.Definition_7_51`,
  the nearby Chapter 7 whole-space specialization of that owner;
- the owner-level pointwise nonemptiness condition
  `EverywhereNonemptySubdifferentialCondition` in
  `Nesterov.Chap07.Definition_7_80`, which already treats `∂ f(x)` as primitive and
  source-facing conditions as derived API.

Best owner abstraction:
- source-facing: Definition 7.81's predicate `StrictlyPositiveOn`;
- core/canonical: the Chapter 3 whole-space real-valued subdifferential `∂[Set.univ] f(x)`;
- bridge/view: `mem_subdifferentialWithin_iff` specialized to `Set.univ`.

Primitive data:
- the set `Q`;
- the real-valued objective `f`;
- the owner-level whole-space subgradient input `g ∈ ∂[Set.univ] f(x)`.

Derived API:
- the source-facing predicate `StrictlyPositiveOn`;
- the projection lemma `StrictlyPositiveOn.inequality`.

The earlier version rebuilt a local real-valued whole-space `subdifferential` even though Chapter 3
already owns that notion and Chapter 7 already reuses it elsewhere. This refinement keeps the
source-facing Definition 7.81 predicate but writes it directly on the canonical owner surface
`∂[Set.univ] f(x)`. -/

/-- The source-facing predicate from Definition 7.81: a real-valued function is strictly positive
on `Q` when for every
`x, y ∈ Q` and every subgradient `g ∈ ∂f(x)`, one has
`f y + f x + ⟪g, y - x⟫ ≥ 0`. -/
def StrictlyPositiveOn (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x y g : E⦄, x ∈ Q → y ∈ Q → g ∈ ∂[Set.univ] f(x) →
    0 ≤ f y + f x + inner ℝ g (y - x)

/-- Definition 7.81: a function that is strictly positive on `Q` satisfies the defining
subgradient inequality at every pair of points of `Q`. -/
-- Proof sketch: apply the defining quantified condition in `StrictlyPositiveOn Q f` to the chosen
-- `x`, `y`, and `g`.
theorem StrictlyPositiveOn.inequality
    {Q : Set E} {f : E → ℝ} (hf : StrictlyPositiveOn Q f)
    {x y g : E} (hx : x ∈ Q) (hy : y ∈ Q) (hg : g ∈ ∂[Set.univ] f(x)) :
    0 ≤ f y + f x + inner ℝ g (y - x) := by
  -- Apply the defining quantified inequality to the chosen `x`, `y`, and `g`.
  simpa [StrictlyPositiveOn] using hf hx hy hg
