/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin WithTopConvexAnalysis

universe u

/- Theorem 3.25 is a `bridge/view` recall in the chapter's extended-valued convex-analysis
minimizer/common-subdifferential domain.

Primary mathematical domain:
- effective-domain minimizers of `WithTop ℝ`-valued convex functions and their
  common-subdifferential optimality criterion.

Relevant owner-style declarations sampled before refinement:
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizer predicate on a set;
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  minimizer-set owner on a feasible set;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the chapter owner API for common subdifferentials;
- `subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential` in
  `Theorem_3_1_20`, the upstream chapter theorem for this exact optimality statement.

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
- source-facing: the textbook criterion identifying sets of global minimizers by the common
  regular subdifferential;
- core/canonical: `argmin[dom f] f` together with the theorem in `Theorem_3_1_20`;
- bridge/view: this numbered recall surface.

The previous file duplicated a local owner `globalMinimizers` for the canonical minimizer set
`argmin[dom f] f`, together with a parallel membership theorem. The chapter theorem in
`Theorem_3_1_20` now lives directly on the canonical owner surface, so this file reuses that
surface instead of preserving the redundant wrapper vocabulary. -/

section MinimizersRecall

variable {X : Type u} (f : X → WithTop ℝ) (x : X)

/- The set `arg min_{x ∈ dom f} f(x)` is the canonical owner `argmin[dom f] f`. -/
set_option linter.hashCommand false in
#check (argmin[dom f] f : Set X)

/- Membership in `argmin[dom f] f` is exactly effective-domain membership together
with minimizing on that domain. -/
set_option linter.hashCommand false in
#check (show x ∈ argmin[dom f] f ↔ x ∈ dom f ∧ IsMinOn f (dom f) x from
  mem_constrainedArgmin_iff)

end MinimizersRecall

section CommonSubdifferentialRecall

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.25: a set is contained in `arg min_{x ∈ dom f} f(x)` if and only if the zero vector
lies in the common regular subdifferential on that set. -/
recall subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential
    {f : V → WithTop ℝ} {XStar : Set V} :
    XStar ⊆ argmin[dom f] f ↔ (0 : V) ∈ ∂̂ f(XStar)

end CommonSubdifferentialRecall
