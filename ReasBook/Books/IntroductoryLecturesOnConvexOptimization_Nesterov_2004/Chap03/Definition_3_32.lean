/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {X : Type u}

/-
Definition 3.32 is a recall-only item in the chapter's finite weighted-sum domain.

Primary domain:
- finite weighted sums of sampled scalar values.

Sampled owner-style declarations:
- mathlib `dotProduct`, the canonical owner for finite sums of entrywise products;
- mathlib notation `α ⬝ᵥ fy`, the idiomatic display form of that owner;
- `hatf` in `Chap03/Lemma_3_24`, the local weighted-sum notation built from `dotProduct` for the
  chapter's sampled primal values;
- project `gapFunctionCertificate_apply` in `Chap03/Lemma_3_24`, the nearby textbook-style
  expansion from the `dotProduct` owner back to an explicit finite sum.

Best owner abstraction:
- `dotProduct α (f ∘ y)`, equivalently `α ⬝ᵥ (f ∘ y)`.

Primitive data:
- a horizon `N : ℕ`;
- sample points `y : Fin (N + 1) → X`;
- coefficients `α : Fin (N + 1) → ℝ`;
- the sampled scalar family `f ∘ y : Fin (N + 1) → ℝ`.

Derived API:
- the textbook display `α ⬝ᵥ (f ∘ y) = ∑ k, α k * f (y k)`, which is just the defining expansion
  of `dotProduct`;
- nearby sampled weighted-gap owners built from the same `dotProduct` abstraction.

Source/core/bridge triage:
- source-facing: the textbook quantity `\hat f_N = ∑_{k=0}^N α_k f(y_k)`;
- core/canonical: `dotProduct α (f ∘ y)`;
- bridge/view: the explicit finite-sum display of that dot product.

This file therefore recalls the mathlib owner directly instead of keeping a parallel local
weighted-sum wrapper.
-/

recall dotProduct

section

variable {N : ℕ} (y : Fin (N + 1) → X) (α : Fin (N + 1) → ℝ) (f : X → ℝ)

#check α ⬝ᵥ (f ∘ y)

#check
  (show α ⬝ᵥ (f ∘ y) = ∑ k, α k * f (y k) from by
    simp [dotProduct])

end

end
