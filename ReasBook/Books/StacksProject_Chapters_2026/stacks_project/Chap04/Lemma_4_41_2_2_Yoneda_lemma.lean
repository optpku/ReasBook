module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Lemma_4_41_1_2_Yoneda_lemma_for_fibred_categories

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)

variable {C : Type u} [Category.{v} C]
variable {S : Type (max u v)} [Category.{v} S]

/- Domain-style sampling for Lemma 4.41.2 (2):
- primary domain: the `2`-Yoneda evaluation functor for categories fibred over a fixed base.
- sampled owner API:
  `FibredCategoryOver.yonedaEvaluationFunctor`,
  `ofFunctor`,
  `FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence`,
  the inherited owner method call on `ofFunctor p`.
- best owner abstraction: `FibredCategoryOver`.
- primitive data: a fibred category over `C` together with `U : C`; in the fibred-in-groupoids
  specialization, the only extra primitive datum is the canonical bundling `ofFunctor p`.
- derived API: the specialization of the owner evaluation functor and of the owner equivalence
  instance to `p : S ⥤ C`.

Source/core/bridge triage:
- source-facing: Lemma 4.41.2 (2), the fibred-in-groupoids specialization of the `2`-Yoneda
  lemma.
- core/canonical: `FibredCategoryOver.yonedaEvaluationFunctor`.
- bridge/view: `ofFunctor p`, used through the coercion
  `FibredInGroupoidsOver C ↪ FibredCategoryOver C`.

This file therefore lives at the bridge/view layer: the source statement adds no new owner-level
mathematics beyond the fibred-category Yoneda owner, but the public artifact should expose the
groupoid specialization itself rather than stopping at a bare owner recall.
-/

variable (p : S ⥤ C) [IsFibredInGroupoids p]
variable (U : C)

/- Lemma 4.41.2 (2-Yoneda lemma), owner recall: the underlying `2`-Yoneda evaluation functor for
fibred categories is already the canonical owner declaration
`FibredCategoryOver.yonedaEvaluationFunctor`. -/
recall FibredCategoryOver.yonedaEvaluationFunctor

/- Lemma 4.41.2 (2-Yoneda lemma): for a functor `p : S ⥤ C` fibred in groupoids, evaluation at
`𝟙 U` is the canonical owner functor specialized to the bundled fibred-in-groupoids object
`ofFunctor p`, via the canonical bridge `toFibredCategoryOver`. -/
#check (ofFunctor p).toFibredCategoryOver.yonedaEvaluationFunctor U

/- Companion owner recall: the equivalence statement is already owned by
`FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence`. -/
recall FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence

/- Companion bridge: the same specialization yields the equivalence instance for the fibred-in-
groupoids evaluation functor itself. -/
#check
  FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence (ofFunctor p).toFibredCategoryOver U

end CategoryTheory
