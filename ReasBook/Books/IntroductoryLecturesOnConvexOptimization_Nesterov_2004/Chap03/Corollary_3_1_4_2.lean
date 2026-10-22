/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped ConvexAnalysis SupportFunction

/- Corollary 3.1.4.2 belongs to the chapter's support-function comparison domain.

Primary domain:
- support functions of subsets of a real Hilbert space and the extended-real effective domain.

Sampled owner declarations:
- `extendedRealEffectiveDomain` / `dom` from `Definition_3_1_1_2`
- `supportFunction` from `Definition_3_9`
- `subset_of_supportFunction_le_on_domain` from `Theorem_3_17`
- `supportFunction_eq_on_common_domain_implies_eq` from `Theorem_3_17`

Source-facing layer:
- equality of closed convex sets from agreement of their support functions on the common
  finite-value domain, with empty/nonempty status already encoded by the shared effective domain.

Core/canonical layer:
- the owner constructions `extendedRealEffectiveDomain` and `supportFunction`, together with the
  exact comparison theorem `supportFunction_eq_on_common_domain_implies_eq`.

Bridge/view:
- the companion inclusion theorem `subset_of_supportFunction_le_on_domain`.

Primitive data:
- the sets `Q₁`, `Q₂` and the canonical support-function/effective-domain constructions.

Derived API:
- the inclusion and equality comparison theorems for those owner constructions.

This file therefore reuses the exact owner theorem from `Theorem_3_17` instead of keeping a
parallel local copy of `supportFunction`, `extendedRealEffectiveDomain`, and the same comparison
statement under a second name.
-/

recall supportFunction_eq_on_common_domain_implies_eq
    (Q₁ Q₂ : Set E) (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdom : dom ξ[Q₁] = dom ξ[Q₂])
    (hξ : Set.EqOn ξ[Q₁] ξ[Q₂] (dom ξ[Q₁])) :
    Q₁ = Q₂
