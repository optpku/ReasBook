/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ConvexAnalysis SupportFunction

/- Corollary 3.1.5 belongs to the chapter's support-function comparison domain.

Primary domain:
- support functions of subsets of a real inner-product space and the extended-real effective
  domain.

Sampled owner declarations:
- `extendedRealEffectiveDomain` / `dom`
- `supportFunction`
- `subset_of_supportFunction_le_on_domain`
- `supportFunction_eq_on_common_domain_implies_eq`

Best owner abstraction:
- the support-function comparison theorem pair from `Theorem_3_17`, organized over the primitive
  data `supportFunction Q` and `dom ξ[Q]`

Source-facing layer:
- the textbook inclusion and equality criteria for closed convex sets stated via support-function
  comparison on the finite-value domain.

Core/canonical layer:
- `subset_of_supportFunction_le_on_domain`
- `supportFunction_eq_on_common_domain_implies_eq`

Bridge/view:
- none; this file only recalls the owner theorems.

Primitive data:
- `supportFunction Q`
- `dom ξ[Q]`

Derived API:
- inclusion from support-function comparison on the finite-value domain
- equality from agreement on the common finite-value domain

This file therefore keeps no parallel local support-function or effective-domain wrapper, and
recalls the chapter owner theorems directly at the intrinsic real Hilbert-space layer rather than
only at the concrete `ℝⁿ` specialization. -/

/- Corollary 3.1.5 (1) recalls the canonical support-function comparison theorem from
`Theorem_3_17`. -/
recall subset_of_supportFunction_le_on_domain
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q₁ Q₂ : Set E) (hQ₂_nonempty : Q₂.Nonempty)
    (hQ₂_closed : IsClosed Q₂) (hQ₂_convex : Convex ℝ Q₂)
    (hξ : ∀ g ∈ dom ξ[Q₂], ξ[Q₁] g ≤ ξ[Q₂] g) :
    Q₁ ⊆ Q₂

/- Corollary 3.1.5 (2) recalls the canonical equality criterion obtained by comparing support
functions on their common finite-value domain; the shared-domain hypothesis already handles the
empty/nonempty bookkeeping. -/
recall supportFunction_eq_on_common_domain_implies_eq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q₁ Q₂ : Set E) (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdom : dom ξ[Q₁] = dom ξ[Q₂])
    (hξ : Set.EqOn ξ[Q₁] ξ[Q₂] (dom ξ[Q₁])) :
    Q₁ = Q₂
