module

import Mathlib.Tactic.Recall
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open IsStronglyCartesian

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/- Domain-style sampling for Lemma 4.33.2:
- primary domain: strongly cartesian morphisms for a functor and their canonical closure
  properties;
- inspected owner-level declarations:
  `Functor.IsStronglyCartesian.comp`,
  `Functor.IsStronglyCartesian.of_isIso`,
  `Functor.IsStronglyCartesian.isIso_of_base_isIso`;
- best owner abstraction: `Functor.IsStronglyCartesian`;
- primitive data: a functor `p : 𝒮 ⥤ 𝒞`, a base morphism `f`, and a morphism `φ` lying over `f`;
- derived API: closure under composition, stability under isomorphism, and recovery of an
  isomorphism from an isomorphic base arrow.

Source/core/bridge triage:
- `source-facing`: the three textbook closure properties listed in Lemma 4.33.2;
- `core/canonical`: the owner namespace `CategoryTheory.Functor.IsStronglyCartesian`;
- `bridge/view`: this file is a direct canonical recall, so no wrapper theorem or alias is needed.
-/

/- Lemma 4.33.2 (1): the composite of strongly cartesian morphisms is the canonical instance
`comp`. -/
recall comp

/- Lemma 4.33.2 (2): an isomorphism is strongly cartesian over its image in the base category by
the canonical instance `of_isIso`. -/
recall of_isIso

/- Lemma 4.33.2 (3): a strongly cartesian morphism whose image in the base category is an
isomorphism is itself an isomorphism by the canonical theorem
`isIso_of_base_isIso`. -/
recall isIso_of_base_isIso

end CategoryTheory.Functor
