module

public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Recall
@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X : C}

/- Domain-style sampling for Remark 4.2.3:
- primary domain: identity morphisms in an arbitrary category and their uniqueness
- sampled canonical declarations:
  `Category.id_comp`,
  `Category.comp_id`,
  `CategoryTheory.id_of_comp_left_id`,
  `CategoryTheory.id_of_comp_right_id`
- best owner abstraction: the canonical identity morphism `𝟙 X`, with uniqueness expressed by the
  owner lemmas `id_of_comp_left_id` and `id_of_comp_right_id`
- primitive data: the ambient category structure and the canonical identity morphism on `X`
- derived API: the source-facing uniqueness bridge for a left identity and a right identity on `X`

Source/core/bridge triage for Remark 4.2.3:
- source-facing: the Stacks remark that identity morphisms are unique
- core/canonical: `𝟙 X`, `id_of_comp_left_id`, `id_of_comp_right_id`
- bridge/view: `identity_morphism_unique`, which packages the source wording as the canonical
  consequence of those owner lemmas
-/

/- Companion recall: a morphism out of `X` acting as a left identity on all maps with source `X`
is the canonical identity `𝟙 X`; this is the owner lemma `id_of_comp_left_id`. -/
recall id_of_comp_left_id

/- Companion recall: a morphism into `X` acting as a right identity on all maps with target `X`
is the canonical identity `𝟙 X`; this is the owner lemma `id_of_comp_right_id`. -/
recall id_of_comp_right_id

/-- Remark 4.2.3: any two identity morphisms of an object `X` are equal. Concretely, if `e` acts
as a left identity on all morphisms out of `X` and `e'` acts as a right identity on all morphisms
into `X`, then `e = e'`; hence one may speak of the identity morphism `𝟙 X`. -/
-- Proof sketch: apply `id_of_comp_left_id` to identify `e` with `𝟙 X`, apply
-- `id_of_comp_right_id` to identify `e'` with `𝟙 X`, and compare the two equalities.
theorem identity_morphism_unique {e e' : X ⟶ X}
    (hleft : ∀ {Y : C} (f : X ⟶ Y), e ≫ f = f)
    (hright : ∀ {Y : C} (f : Y ⟶ X), f ≫ e' = f) :
    e = e' := by
  -- First identify the left-identity candidate with the canonical identity morphism.
  have he : e = 𝟙 X := id_of_comp_left_id e hleft
  -- Then identify the right-identity candidate with the same canonical identity morphism.
  have he' : e' = 𝟙 X := id_of_comp_right_id e' hright
  -- Comparing both morphisms through `𝟙 X` gives the desired uniqueness.
  calc
    e = 𝟙 X := he
    _ = e' := he'.symm

end CategoryTheory
