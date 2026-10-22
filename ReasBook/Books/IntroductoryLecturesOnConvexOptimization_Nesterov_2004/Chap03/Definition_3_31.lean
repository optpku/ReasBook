/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

/- Definition 3.31 is a recall-only item in the chapter's weighted primal-dual certificate
domain.

Primary domain:
- finite weighted inner-product certificates attached to sampled primal points.

Sampled owner-style declarations:
- mathlib `dotProduct`, the canonical finite weighted-sum owner behind the certificate formula
- `gapFunctionCertificate` in `Chap03/Lemma_3_24`, the chapter owner for the sampled certificate
- `gapFunctionCertificate_apply` in `Chap03/Lemma_3_24`, the defining finite-sum expansion

Best owner abstraction:
- source-facing: the certificate `δ_N`
- core/canonical: `gapFunctionCertificate y α g`
- bridge/view: `gapFunctionCertificate_apply`

Primitive data:
- the horizon `N`
- the sample points `y : Fin (N + 1) → E`
- the coefficients `α : Fin (N + 1) → ℝ`
- the field `g : E → E`

Derived API:
- the certificate function `gapFunctionCertificate y α g`
- its pointwise weighted-sum expansion

Source/core/bridge triage:
- source-facing: the textbook gap certificate
- core/canonical: the owner in `Lemma_3_24`
- bridge/view: this recall surface

The owner already lives in `Lemma_3_24`, so this file remains a pure recall layer and introduces
no parallel local wrapper or alias. -/

/- Definition 3.31: the gap function certificate attached to test points `y_k`, scaling
coefficients `α_k`, and a map `g` is the function
`δ_N(x) = ∑_{k=0}^N α_k ⟪g(y_k), y_k - x⟫`. -/
recall gapFunctionCertificate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ}
    (y : Fin (N + 1) → E) (α : Fin (N + 1) → ℝ) (g : E → E) :
    E → ℝ

/- Evaluating the gap function certificate expands to its defining weighted inner-product sum. -/
recall gapFunctionCertificate_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ}
    (y : Fin (N + 1) → E) (α : Fin (N + 1) → ℝ) (g : E → E) (x : E) :
    gapFunctionCertificate y α g x =
      ∑ k, α k * inner ℝ (g (y k)) (y k - x)

end
