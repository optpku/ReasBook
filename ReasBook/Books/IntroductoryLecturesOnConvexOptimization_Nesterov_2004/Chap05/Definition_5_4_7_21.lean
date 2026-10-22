/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

/- Definition 5.4.7.21 lies in the Chapter 5 posynomial / positive-orthant domain.

Primary domain:
- finite positive linear combinations of simplex monomials on the strict positive orthant.

Relevant owner declarations sampled before refinement:
- `monomialXi` and `monomialXi_apply` in `Definition_5_4_7_17`, the chapter owner and evaluation
  bridge for the simplex monomials `ξ_[a]`;
- `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the ambient owner for the
  strict positive orthant `ℝⁿ₊₊`;
- `posynomialXi` in `Theorem_5_4_7_14`, the existing Chapter 5 owner for the same posynomial
  construction;
- `posynomialXi_apply` in `Theorem_5_4_7_14`, the canonical evaluation lemma on that owner.

Best owner abstraction:
- `posynomialXi`.

Primitive data:
- the positive coefficients `α : Fin m → Set.Ioi (0 : ℝ)`;
- the simplex exponents `a : Fin m → Δ[n]`.

Derived API:
- the owner declaration `posynomialXi`;
- the evaluation lemma `posynomialXi_apply`.

Source/core/bridge triage:
- source-facing: the posynomial `ξ(x) = ∑ₖ αₖ x^{aₖ}` on `ℝⁿ₊₊`;
- core/canonical: the Chapter 5 owner `posynomialXi`;
- bridge/view: the monomial notation `ξ_[(a k)]` used in the canonical evaluation formula.

The previous version rebuilt the same owner and its apply lemma locally. This file now reuses the
existing Chapter 5 declaration directly instead of keeping a parallel duplicate API.
-/

recall posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    positiveOrthant n → ℝ

/- Evaluating the recalled owner keeps the Chapter 5 monomial surface `ξ_[(a k)]`, which is the
canonical source-facing notation for the monomials `x ↦ x^{aₖ}` introduced earlier in the same
subsection. -/
recall posynomialXi_apply
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    posynomialXi n m α a x =
      ∑ k : Fin m, (α k : ℝ) * ξ_[(a k)] x

end
