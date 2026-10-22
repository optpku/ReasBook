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

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.77 is a recall-only item in the chapter's constrained convex-analysis /
relative-subdifferential domain.

Primary domain:
- relative subgradients on a feasible set and the maximum attained by their norms across the two
  functions `f` and `\bar f`.

Relevant owner declarations sampled before refining:
- `subdifferentialWithin` in `Theorem_3_44`, the chapter owner for relative subgradients;
- `mem_subdifferentialWithin_iff` in `Theorem_3_44`, the canonical pointwise membership bridge for
  that owner;
- `Definition_3_70`, where the nearby single-function maximum statement is already written as a
  direct `IsGreatest` proposition on an inlined set of attainable norms;
- `IsGreatest.csSup_eq` in mathlib, the generic bridge from an explicit maximum statement to the
  corresponding `sSup` equality.

Best owner abstraction:
- source-facing: the textbook maximum-attainment statement for `M_f`;
- core/canonical: the pointwise owners `∂[Q] f(x)` and `∂[Q] fBar(x)` together with the ambient
  order owner `IsGreatest`;
- bridge/view: none; the one-off set of attainable joint relative-subgradient norms is inlined
  directly into the `IsGreatest` statement.

Primitive data:
- the pointwise relative subdifferentials `∂[Q] f(x)` and `∂[Q] fBar(x)`.

Public derived API:
- none in this recall file.

Source/core/bridge triage:
- source-facing: the textbook maximum-attainment statement for the constant `M_f`;
- core/canonical: `subdifferentialWithin` together with `IsGreatest`;
- bridge/view: the inlined set of attainable norms inside the checked statement.

There is no earlier chapter owner for the whole textbook constant `M_f`, but there is also no
downstream use that justifies a separate public wrapper for the joint norm set. This file
therefore follows the nearby recall-only pattern of `Definition_3_70`: it keeps the source-facing
maximum statement directly as a checked `IsGreatest` proposition on the inlined set of attainable
relative-subgradient norms, and leaves the supremum reformulation to the canonical generic
companion `hM_f.csSup_eq`. Because the checked statement only uses the relative-subdifferential
owner `∂[Q] f(x)` from `Theorem_3_44` and the ambient norm `‖g‖`, its public ambient assumptions
stay on the same seminormed inner-product layer as that owner bridge.
-/

section

variable (Q : Set E) (f fBar : E → ℝ) (M_f : ℝ)

/- Definition 3.77: the textbook constant `M_f` is the maximum of the norms `‖g‖` of all relative
subgradients `g ∈ ∂_Q f(x) ∪ ∂_Q \bar f(x)` at feasible base points `x`; in Lean this is the
canonical maximum-attainment predicate on the direct set of attainable relative-subgradient norms,
with feasibility carried by `subdifferentialWithin`. -/
#check
  IsGreatest
    ({r | ∃ x g, g ∈ ∂[Q] f(x) ∪ ∂[Q] fBar(x) ∧ ‖g‖ = r} : Set ℝ)
    M_f

end

section

variable {Q : Set E} {f fBar : E → ℝ} {M_f : ℝ}
variable
  (hM_f :
    IsGreatest
      ({r | ∃ x g, g ∈ ∂[Q] f(x) ∪ ∂[Q] fBar(x) ∧ ‖g‖ = r} : Set ℝ)
      M_f)

/- The supremum reformulation is not a second source-facing definition: it is the generic
order-theoretic companion view `hM_f.csSup_eq`. -/
#check hM_f.csSup_eq

end

end
