/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ConstrainedArgmin

variable {E : Type u} [TopologicalSpace E]

/- Definition 7.52 lies in the chapter's constrained analytic-center domain.

Sampled owner-style declarations:
* `IsMinOn` in mathlib, the canonical minimizer predicate on a set;
* `constrainedArgmin` in `Chap01/Definition_1_3_3`, the project owner for constrained minimizers;
* `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the atomic feasibility-plus-`IsMinOn`
  expansion of that owner;
* `Chap05/Definition_5_3_3`, where analytic-center language is already refined to direct use of
  the canonical minimizer owner rather than a parallel wrapper.

Best owner abstraction:
* source-facing: the constrained analytic center of `P = hatP ∩ Q` with respect to `F`;
* core/canonical: `x0 ∈ argmin[hatP ∩ interior Q] F`;
* bridge/view: `mem_constrainedArgmin_iff`, which expands that canonical owner to the textbook
  statement `x0 ∈ hatP ∩ interior Q ∧ IsMinOn F (hatP ∩ interior Q) x0`.

Primitive data:
* the sets `hatP`, `Q : Set E`;
* the objective `F : E → ℝ`;
* the candidate point `x0 : E`.

Derived API:
* the strict feasible set `hatP ∩ interior Q`;
* the constrained analytic-center condition, canonically as membership in
  `argmin[hatP ∩ interior Q] F`;
* the textbook expansion, derived from `mem_constrainedArgmin_iff`.

Source/core/bridge triage:
* source-facing: the constrained analytic center from Definition 7.52;
* core/canonical: the Chapter 1 constrained-argmin owner on the strict feasible set;
* bridge/view: the expansion lemma `mem_constrainedArgmin_iff`.

The textbook assumptions that `P = hatP ∩ Q` is bounded, that `P₀ = hatP ∩ interior Q` is
nonempty, and that `F` is a barrier on `Q` are existence/uniqueness hypotheses for later results,
not part of the owner introduced here. This item therefore adds no new public wrapper for the
feasible region, strict feasible region, or analytic-center predicate: all of them are already
expressed canonically by the intersection `hatP ∩ interior Q` and the owner
`argmin[hatP ∩ interior Q] F`. -/

section

variable (hatP Q : Set E) (F : E → ℝ) (x0 : E)

local notation "P₀" => hatP ∩ interior Q

set_option linter.hashCommand false

/- Definition 7.52: a constrained analytic center of `P = hatP ∩ Q` with respect to `F` is
exactly a point of the canonical constrained argmin set of `F` on the strict feasible region
`P₀ = hatP ∩ interior Q`. -/
#check x0 ∈ argmin[P₀] F

end
