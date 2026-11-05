module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_43_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain-style sampling for Lemma 4.43.6:
- Primary domain: rigid monoidal category theory for a fixed exact pairing.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `tensorLeftHomEquiv`
  - `tensorRightHomEquiv`
  - `tensorLeftAdjunction`
- Owner abstraction first: `ExactPairing Y X`, already recalled in Definition `4.43.5`.
- Layer triage:
  - `source-facing`: the two textbook bijections associated to a fixed left dual `Y` of `X`;
  - `core/canonical`: the exact pairing `ExactPairing Y X`;
  - `bridge/view`: `tensorRightHomEquiv` and `tensorLeftHomEquiv`, functorially derived from the
    owner exact pairing, with naturality as companion theorem API.
- Primitive vs. derived:
  - primitive data: the exact pairing `ExactPairing Y X`;
  - derived API: `tensorRightHomEquiv`, `tensorLeftHomEquiv`, and their naturality theorems.
-/

/- Lemma 4.43.6: if `Y` is a left dual of `X`, then for every `Z` and `Z'` there is a canonical
bijection `Mor (X ⊗ Z', Z) ≃ Mor (Z', Y ⊗ Z)`. This is the specialization
`tensorLeftHomEquiv Z' Y X Z`. -/
recall tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)

/- The first bijection of Lemma 4.43.6 is natural in the target object `Z`. -/
recall tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y']
    (f : Y' ⊗ X ⟶ Z) (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g

/- The inverse of the first bijection of Lemma 4.43.6 is natural in the source object `Z'`. -/
recall tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y']
    (f : X ⟶ X') (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      Y' ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g

/- Lemma 4.43.6 also gives the canonical bijection
`Mor (Z' ⊗ Y, Z) ≃ Mor (Z', Z ⊗ X)`. This is the specialization
`tensorRightHomEquiv Z' Y X Z`. -/
recall tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')

/- The second bijection of Lemma 4.43.6 is natural in the target object `Z`. -/
recall tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y']
    (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y'

/- The inverse of the second bijection of Lemma 4.43.6 is natural in the source object `Z'`. -/
recall tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y']
    (f : X ⟶ X') (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g

end CategoryTheory
