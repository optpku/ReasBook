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

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.70 is a recall-only item in the chapter's real-valued convex-analysis /
subdifferential domain.

Sampled owner-style declarations:
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`
- `isGreatest_inner_image_spdEllipsoid` in `Lemma_3_20`
- `IsGreatest.csSup_eq` in mathlib, the canonical bridge from explicit maximum attainment to the
  corresponding supremum equality

Best owner abstraction in this file:
- source-facing: the textbook maximum-attainment statement for `M_f`
- core/canonical: the pointwise owner `∂ (fun y ↦ (f y : WithTop ℝ))(x)` together with the
  ambient order owner `IsGreatest`
- bridge/view: none; the one-off norm-set comprehension is inlined directly into the
  `IsGreatest` statement

Primitive data:
- the pointwise subdifferentials `subdifferential (fun y ↦ (f y : WithTop ℝ)) x`

Public derived API:
- none in this recall file

Source/core/bridge triage:
- source-facing: the textbook maximum-attainment statement for `M_f`
- core/canonical: `subdifferential` and `IsGreatest`
- bridge/view: the inlined set of attainable subgradient norms inside the checked statement

There is no earlier chapter owner for the whole textbook constant `M_f`. This file therefore keeps
the source-facing maximum statement directly as a checked `IsGreatest` proposition, deletes the
one-off public norm-set wrapper, and leaves the supremum reformulation to the canonical generic
companion `hM_f.csSup_eq`. Because the checked statement only uses the subdifferential owner
`∂ (fun y ↦ (f y : WithTop ℝ))(x)` from `Definition_3_1_5` and the ambient norm `‖g‖`, its
public ambient assumptions stay on the same seminormed inner-product layer as that owner.
-/

section

variable (Q : Set E) (f : E → ℝ) (M_f : ℝ)

/- Definition 3.70: the textbook constant `M_f` is the maximum of the norms `‖g‖` of all
subgradients `g ∈ ∂f(x)` with `x ∈ Q`; in Lean this is the canonical maximum-attainment predicate
on the direct set of attainable subgradient norms. -/
#check
  IsGreatest
    ({r | ∃ x ∈ Q, ∃ g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x), ‖g‖ = r} : Set ℝ)
    M_f

end

section

variable {Q : Set E} {f : E → ℝ} {M_f : ℝ}
variable
  (hM_f :
    IsGreatest
      ({r | ∃ x ∈ Q, ∃ g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x), ‖g‖ = r} : Set ℝ)
      M_f)

/- The supremum reformulation is not a second source-facing definition: it is the generic
order-theoretic companion view `hM_f.csSup_eq`. -/
#check hM_f.csSup_eq

end

end
