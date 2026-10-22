/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin WithTopConvexAnalysis

/- This item is a recall-only surface in the chapter's extended-valued
convex-analysis minimizer/common-subdifferential domain.

Primary domain:
- effective-domain minimizers of `WithTop ℝ`-valued convex functions and their
  common-subdifferential optimality criterion.

Relevant owner-style declarations sampled before refinement:
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizer predicate on a set;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for extended-valued subgradients;
- `commonRegularSubdifferential` in `Definition_3_1_5_4`, the chapter owner for common
  subdifferentials;
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  minimizer-set owner on a feasible set;
- `subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential` in
  `Theorem_3_1_20`, the upstream chapter theorem for this exact source-facing optimality
  statement.

Best owner abstraction:
- `argmin[dom f] f` together with
  `subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential`.

Primitive data:
- an extended-valued function `f`;
- a set `XStar`.

Derived API:
- the minimizer-set owner `argmin[dom f] f`;
- its atomic membership theorem `mem_constrainedArgmin_iff`;
- the zero-common-subgradient optimality criterion.

Source/core/bridge triage:
- source-facing: the textbook optimality criterion for a set of global minimizers;
- core/canonical: `argmin[dom f] f` together with the theorem in `Theorem_3_1_20`;
- bridge/view: this numbered recall surface.

The previous file duplicated a local owner `globalMinimizers` for the canonical minimizer set
`argmin[dom f] f`, together with a parallel membership theorem and the same
zero-common-subgradient criterion. Chapter 3 already has the canonical theorem surface in
`Theorem_3_1_20`, so this file now reuses that owner directly instead of maintaining a parallel
Euclidean-only wrapper API. -/

universe u

section MinimizersRecall

variable {V : Type u} (f : V → WithTop ℝ) (x : V)

/- The set `arg min_{x ∈ dom f} f(x)` is the canonical owner `argmin[dom f] f`. -/
set_option linter.hashCommand false in
#check (argmin[dom f] f : Set V)

/- Membership in `argmin[dom f] f` is exactly effective-domain membership together
with minimizing on that domain. -/
set_option linter.hashCommand false in
#check (show x ∈ argmin[dom f] f ↔ x ∈ dom f ∧ IsMinOn f (dom f) x from
  mem_constrainedArgmin_iff)

end MinimizersRecall

section CommonSubdifferentialRecall

variable {V : Type u}
variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.1.5.8: if `X^* := argmin[dom f] f`, then `XStar ⊆ X^*` if and only if the zero
vector lies in the common regular subdifferential `∂̂ f(XStar)`. The source-side assumptions that
`XStar` is nonempty, closed, convex, and contained in `dom f` are redundant for this equivalence,
so the canonical recall surface states the exact owner theorem without them. -/
recall subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential
    {f : V → WithTop ℝ} {XStar : Set V} :
    XStar ⊆ argmin[dom f] f ↔ (0 : V) ∈ ∂̂ f(XStar)

end CommonSubdifferentialRecall
