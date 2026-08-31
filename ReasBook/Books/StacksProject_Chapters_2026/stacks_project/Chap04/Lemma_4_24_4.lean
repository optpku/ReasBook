module

public import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.4:
- primary domain: adjunction criteria for fully faithful functors;
- sampled owner API:
  `Adjunction.unit_isIso_of_L_fully_faithful`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`,
  `Adjunction.counit_isIso_of_R_fully_faithful`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`;
- sampled bridge API:
  `Adjunction.isIso_unit_of_iso`,
  `Adjunction.fullyFaithfulLOfCompIsoId`,
  `Adjunction.isIso_counit_of_iso`,
  `Adjunction.fullyFaithfulROfCompIsoId`;
- source-facing layer: the Stacks criterion that, for an adjunction `u ⊣ v`, full faithfulness of
  `u` is equivalent to invertibility of the unit, and full faithfulness of `v` is equivalent to
  invertibility of the counit;
- core/canonical owner: `CategoryTheory.Adjunction`;
- bridge/view: passage between the natural-transformation isomorphism criteria and the explicit
  functor isomorphisms `𝟭 C ≅ u ⋙ v` and `v ⋙ u ≅ 𝟭 D`.

Primitive data are just the adjunction `u ⊣ v`. The full-faithfulness criteria, the `IsIso`
structures on the unit and counit, and the functor-isomorphism reformulations are all derived API
already owned upstream by `CategoryTheory.Adjunction`, so this file should remain a pure canonical
recall rather than introducing local wrappers.
-/

/- Lemma 4.24.4: for an adjunction `u ⊣ v`, the fully faithful criterion is already owned by the
canonical mathlib adjunction API. The source-facing equivalence

* `u` fully faithful `↔` the unit `𝟭 C ⟶ u ⋙ v` is an isomorphism, and
* `v` fully faithful `↔` the counit `v ⋙ u ⟶ 𝟭 D` is an isomorphism

is exactly the pair of owner constructions below. -/
recall Adjunction.unit_isIso_of_L_fully_faithful
recall Adjunction.fullyFaithfulLOfIsIsoUnit
recall Adjunction.counit_isIso_of_R_fully_faithful
recall Adjunction.fullyFaithfulROfIsIsoCounit

/- The source restatement using explicit isomorphisms `𝟭 C ≅ u ⋙ v` and `v ⋙ u ≅ 𝟭 D` is the
canonical bridge between those owner theorems and abstract functor isomorphisms. -/
recall Adjunction.isIso_unit_of_iso
recall Adjunction.fullyFaithfulLOfCompIsoId
recall Adjunction.isIso_counit_of_iso
recall Adjunction.fullyFaithfulROfCompIsoId

end CategoryTheory
