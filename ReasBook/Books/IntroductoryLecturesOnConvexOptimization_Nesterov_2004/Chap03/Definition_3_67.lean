/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u v

variable {X : Type u} {E : Type v}

/-
Definition 3.67 lies in the chapter's constrained model-minimization domain.

Sampled owner declarations:
* `SetConstrainedMinimizationProblem` and `argmin[Q] f` in `Chap01/Definition_1_3_3`, the Chapter 1
  owner of a feasible set and objective together with its canonical minimizer set;
* `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the atomic membership expansion for
  the constrained argmin owner;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the Chapter 1
  owner optimal value in `EReal`;
* `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in `Chap01/Definition_1_3_7`,
  the attained-minimum bridge for the owner optimal value.

Best owner abstraction:
* source-facing: the model optimal set `Z_k^*` and value `\hat f_k^*` for the model
  `z ↦ hatf Z z` on `Q`;
* core/canonical: `argmin[Q] (hatf Z)` and `(.mk Q (hatf Z) : SetConstrainedMinimizationProblem E)`;
* bridge/view: `mem_constrainedArgmin_iff` and `optimalValue_eq_of_isMinOn`.

Primitive data:
* the feasible set `Q`;
* the model family `hatf`;
* the parameter `Z`.

Derived API:
* the canonical minimizer set `argmin[Q] (hatf Z)`;
* the owner optimal value of the constrained model problem;
* the membership and attained-minimum bridge formulas below.

This file is therefore recall-only: it should expose the Chapter 1 owners directly and avoid any
parallel public wrapper for the model problem.
-/

section

variable (Q : Set E) (hatf : X → E → ℝ) (Z : X) (z : E)

local notation "modelProblem" => (SetConstrainedMinimizationProblem.mk Q (hatf Z) :
  SetConstrainedMinimizationProblem E)

/- Definition 3.67: the model optimal set `Z_k^*` is the canonical constrained argmin
`argmin[Q] (hatf Z)`. -/
#check (argmin[Q] (hatf Z) : Set E)

/- The model optimal value `\hat f_k^*` is the Chapter 1 constrained optimal value of the model
problem with feasible set `Q` and objective `hatf Z`. -/
#check ((modelProblem).optimalValue : EReal)

/- Membership in the model optimal set means feasibility together with exact minimization of the
model on `Q`. -/
#check
  (show z ∈ argmin[Q] (hatf Z) ↔ z ∈ Q ∧ IsMinOn (hatf Z) Q z from
    mem_constrainedArgmin_iff)

end

section

variable (Q : Set E) (hatf : X → E → ℝ) (Z : X) {z : E}
variable (hz_mem : z ∈ Q) (hz_min : IsMinOn (hatf Z) Q z)

local notation "modelProblem" => (SetConstrainedMinimizationProblem.mk Q (hatf Z) :
  SetConstrainedMinimizationProblem E)

/- If `z` minimizes the model on `Q`, then the Chapter 1 owner optimal value is exactly the model
value at `z`, matching the textbook identity `\hat f_k^* = \hat f_k(Z; z)`. -/
#check
  (show ((modelProblem).optimalValue : EReal) = hatf Z z from
    (modelProblem).optimalValue_eq_of_isMinOn hz_mem hz_min)

end
