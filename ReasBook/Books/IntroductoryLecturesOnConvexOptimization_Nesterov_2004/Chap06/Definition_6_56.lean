/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Definition 6.56 lies in the chapter's scaled restricted-duality / `WithTop`-valued
convex-analysis domain.

Sampled owner-style declarations:
- `dom` in `Chap03/Definition_3_3`, the chapter owner for the finite-value domain of a
  `WithTop ℝ`-valued function;
- `restrictedDualFunction` in `Chap06/Definition_6_55`, the Chapter 6 owner of the restricted
  dual supremum with a feasible base point;
- `AffineMap.lineMap`, the canonical affine owner for textbook contractions
  `(1 - τ) • xBar + τ • x`.

Best owner abstraction:
- source-facing: `scaledRestrictedDualFunction`;
- core/canonical: `restrictedDualFunction` on the contracted feasible set;
- bridge/view: the evaluation theorem `scaledRestrictedDualFunction_apply`.

Primitive data:
- the feasible set `Q : Set E`;
- the extended-real-valued function `F : E → WithTop ℝ`;
- the feasible base point `xBar : ↥(Q ∩ dom F)`;
- the scaling parameter `τ : ℝ`.

Derived API:
- `scaledRestrictedDualFunction`;
- the atomic evaluation theorem for that owner.

This refinement removes the duplicate local `sSup` assembly from the public surface. The scaled
restricted dual function is now defined as the Chapter 6 owner `restrictedDualFunction` applied to
the contracted feasible set `((fun y ↦ AffineMap.lineMap xBar y τ) '' Q)`, so the feasible
base-point data `xBar ∈ Q ∩ dom F` remains primitive in the main source-facing API.
-/

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

variable [TopologicalSpace E]

/-- Definition 6.56: the scaled restricted dual function of `F` with respect to `(τ, xBar, Q)` is
the restricted dual function of `F` over the contracted feasible set
`{(1 - τ) • xBar + τ • x | x ∈ Q}`, with the same feasible base point `xBar ∈ Q ∩ dom F`.
Equivalently, it is the supremum over contracted feasible points `y ∈ dom F` of the affine gap
`s (xBar - y) + F(xBar) - F(y)`. In textbook settings with compactness or attainment hypotheses,
this supremum is the displayed maximum. -/
def scaledRestrictedDualFunction
    (Q : Set E) (F : E → WithTop ℝ) (xBar : ↥(Q ∩ dom F)) (τ : ℝ) :
    StrongDual ℝ E → WithTop ℝ :=
  restrictedDualFunction ((fun y ↦ AffineMap.lineMap (xBar : E) y τ) '' Q) F
    ⟨xBar, by
      refine ⟨?_, xBar.2.2⟩
      exact ⟨xBar, xBar.2.1, by simp⟩⟩

/-- Evaluating the scaled restricted dual function recovers the defining supremum over the
contracted feasible set. -/
theorem scaledRestrictedDualFunction_apply
    (Q : Set E) (F : E → WithTop ℝ) (xBar : ↥(Q ∩ dom F)) (τ : ℝ) (s : StrongDual ℝ E) :
    scaledRestrictedDualFunction Q F xBar τ s =
      sSup (Set.range fun y : ↥(((fun z ↦ AffineMap.lineMap (xBar : E) z τ) '' Q) ∩ dom F) ↦
        ((restrictedDualMaximand F ⟨xBar, xBar.2.2⟩ s ⟨y, y.2.2⟩ : ℝ) : WithTop ℝ)) :=
  rfl

end
