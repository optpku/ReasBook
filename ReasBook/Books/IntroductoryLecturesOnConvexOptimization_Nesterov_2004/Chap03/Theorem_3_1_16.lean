/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

/- Theorem 3.1.16 is a recall-only Euclidean specialization in the chapter's
Fenchel-biconjugacy domain.

Primary domain:
- Fenchel conjugates, biduals, and subdifferentials of `ℝ ∪ {+∞}`-valued
  functions on `ℝⁿ`.

Relevant sampled declarations in this domain:
- `dom` and `withTopToEReal` in `Definition_3_3`, the chapter owners for the
  effective-domain / `EReal` bridge;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the
  chapter owner for extended-valued subgradients;
- `fenchelDual` and the notation `f⋆` in `Definition_3_1_2_1`, the
  source-facing Fenchel-dual owner;
- `fenchelBidual`, `fenchelBidual_le_of_mem_dom`,
  `subdifferential_subset_dom_fenchelDual`, and
  `fenchelBidual_eq_of_subdifferential_nonempty` in `Theorem_3_1_5_2`, the
  owner-level bidual surface.

Best owner abstraction:
- the existing source-facing owner surface `f⋆`, `f⋆⋆`, `dom f`, and `∂ f(x)`.

Primitive data:
- none in this file; the primitive domain, subdifferential, Fenchel-dual, and
  Fenchel-bidual data already live upstream.

Derived API:
- only the Euclidean `ℝⁿ` specialization of the three theorem clauses.

Source/core/bridge triage:
- source-facing: Theorem 3.1.16 as the textbook Euclidean specialization;
- core/canonical: `dom`, `subdifferential`, `fenchelDual`, and `fenchelBidual`;
- bridge/view: this recall-only specialization from the intrinsic owner layer
  to `EuclideanSpace ℝ (Fin n)`.

The previous file rebuilt local copies of the effective domain, finite real
part, subgradient predicate, subdifferential, Fenchel dual, and Fenchel bidual.
All of those notions are already owned upstream in the chapter. This refinement
deletes the duplicate wheels and recalls only the Euclidean specialization of
the canonical owner-level theorem surface.
-/

section

variable {n : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
variable {x : EuclideanSpace ℝ (Fin n)}

/- Theorem 3.1.16 (1): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, the
Fenchel bidual is bounded above by the original value at every point of `dom f`. -/
#check
  (fenchelBidual_le_of_mem_dom :
    x ∈ dom f → (f⋆⋆) x ≤ withTopToEReal (f x))

/- Theorem 3.1.16 (2): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, every
subgradient belongs to the effective domain of the Fenchel dual. -/
#check
  (subdifferential_subset_dom_fenchelDual :
    ∂ f(x) ⊆ dom (f⋆))

/- Theorem 3.1.16 (3): in the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)`, nonempty
subdifferential implies Fenchel-bidual equality at `x`. -/
#check
  (fenchelBidual_eq_of_subdifferential_nonempty :
    (∂ f(x)).Nonempty → (f⋆⋆) x = withTopToEReal (f x))

end

end
