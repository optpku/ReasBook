/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

/- Theorem 3.20 is a recall-only Euclidean specialization in the chapter's Fenchel-biconjugacy
domain.

Primary domain:
- Fenchel conjugates, biduals, and subdifferentials of `ℝ ∪ {+∞}`-valued functions on `ℝⁿ`.

Sampled owner-style declarations:
- `fenchelConjugate` in `Definition_6_1`, the core owner;
- the source-facing Fenchel-dual notation `f⋆` in `Definition_3_1_2_1`;
- the source-facing Fenchel-bidual notation `f⋆⋆` in `Theorem_3_1_5_2`;
- the intrinsic theorem declarations `fenchelBidual_le_of_mem_dom`,
  `subdifferential_subset_dom_fenchelDual`, and
  `fenchelBidual_eq_of_subdifferential_nonempty` in `Theorem_3_1_5_2`.

Best owner abstraction:
- the intrinsic theorem surface in `Theorem_3_1_5_2`, stated on the chapter's source-facing
  notation `f⋆` and `f⋆⋆`.

Primitive data:
- none in this file; the notation and theorem owners already live upstream.

Derived API:
- this Euclidean recall surface.

Source/core/bridge triage:
- source-facing: Theorem 3.20's Euclidean `ℝⁿ` specialization of the textbook Fenchel-biconjugacy
  statements;
- core/canonical: the intrinsic theorem declarations from `Theorem_3_1_5_2`;
- bridge/view: this finite-dimensional specialization by recall.

The previous refinement rebuilt a parallel Euclidean `f⋆` / `f⋆⋆` surface locally and then only
`#check`ed the theorem propositions. This file now consumes the owner-level notation and theorem
API from `Definition_3_1_2_1` and `Theorem_3_1_5_2` directly, so the Euclidean item is only the
specialization layer and does not maintain a second bridge surface. The explicit specialized
checks below expose the actual `E = EuclideanSpace ℝ (Fin n)` signatures instead of only
rechecking the generic owner names.
-/

section

variable {n : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
variable {x : EuclideanSpace ℝ (Fin n)}

/- Theorem 3.20 (1): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, the
Fenchel bidual is bounded above by the original value at every point of `dom f`. -/
#check
  (fenchelBidual_le_of_mem_dom :
    x ∈ dom f → (f⋆⋆) x ≤ withTopToEReal (f x))

/- Theorem 3.20 (2): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, every
subgradient belongs to the effective domain of the Fenchel dual. -/
#check
  (subdifferential_subset_dom_fenchelDual :
    ∂ f(x) ⊆ dom (f⋆))

/- Theorem 3.20 (3): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, nonempty
subdifferential implies Fenchel-bidual equality at `x`. -/
#check
  (fenchelBidual_eq_of_subdifferential_nonempty :
    (∂ f(x)).Nonempty → (f⋆⋆) x = withTopToEReal (f x))

end

end
