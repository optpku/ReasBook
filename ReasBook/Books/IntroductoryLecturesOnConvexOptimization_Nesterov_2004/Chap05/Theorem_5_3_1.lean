/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Theorem 5.3.1 lies in the chapter's self-concordance / affine-perturbation domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantOnWith` and `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter
  owners for self-concordance;
* `quadraticAffineObjective` and `quadraticAffineObjective_zero_operator` from `Example_5_1_2`,
  the source-facing affine-quadratic owner and its zero-quadratic bridge to a linear term;
* `IsSelfConcordantOnWith.add_quadraticAffineObjective` from `Corollary_5_1_2`, the owner-level
  perturbation theorem for preserving self-concordance.

Source/core/bridge triage:
* source-facing: the linear perturbation `x ↦ ⟪c, x⟫ + F x`;
* core/canonical: `IsStandardSelfConcordantOn dom F`;
* bridge/view: `quadraticAffineObjective_zero_operator`, identifying the linear term with the
  zero-quadratic specialization of `quadraticAffineObjective`.

Primitive data:
* the domain `dom`;
* the standard self-concordant objective `F`;
* the perturbation vector `c`.

Derived API:
* positivity of the zero operator;
* the zero-operator bridge
  `quadraticAffineObjective 0 c (0 : E →L[ℝ] E) = fun x ↦ inner ℝ c x`;
* the specialization of `IsSelfConcordantOnWith.add_quadraticAffineObjective` to
  `quadraticAffineObjective 0 c 0`.

The target statement is therefore kept source-facing, while its implementation is refined to the
chapter owner theorem and the owner zero-operator bridge instead of a parallel local proof
route. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: apply Corollary 5.1.2 to the standard self-concordant function `F` with
-- quadratic-affine perturbation data `α = 0`, `a = c`, and `A = 0`. The zero operator is
-- positive semidefinite, and `quadraticAffineObjective_zero_operator` identifies this
-- specialization with the linear term `x ↦ inner ℝ c x`.
/-- Theorem 5.3.1: if `F` is standard self-concordant on `dom`, then the linear perturbation
`x ↦ ⟪c, x⟫ + F(x)` is standard self-concordant on `dom`. This is the self-concordance part of
the textbook statement for a self-concordant barrier. -/
theorem selfConcordantBarrier_add_linear_isStandardSelfConcordantOn
    (dom : Set E) (F : E → ℝ) (c : E) (hF : IsStandardSelfConcordantOn dom F) :
    IsStandardSelfConcordantOn dom (fun x ↦ inner ℝ c x + F x) := by
  simpa [quadraticAffineObjective_zero_operator, add_comm, add_left_comm, add_assoc] using
    hF.add_quadraticAffineObjective 0 c (0 : E →L[ℝ] E) ContinuousLinearMap.isPositive_zero

end
