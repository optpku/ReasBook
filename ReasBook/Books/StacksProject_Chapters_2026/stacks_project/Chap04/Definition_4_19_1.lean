module

public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u vC uC

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]
variable {C : Type uC} [Category.{vC} C]

/-- Definition 4.19.1, diagram form: a diagram is filtered when its indexing category is
nonempty, any two objects admit a common successor, and any two parallel arrows become equal
after postcomposition with some arrow and applying the diagram. -/
structure IsFilteredDiagram (M : I ⥤ C) : Prop where
  /-- The indexing category has at least one object. -/
  nonempty : Nonempty I
  /-- Any two objects in the indexing category admit a common successor. -/
  cocone_objs : ∀ x y : I, ∃ (z : I) (_ : x ⟶ z) (_ : y ⟶ z), True
  /-- Parallel morphisms can be equalized after postcomposition and applying the diagram. -/
  cocone_maps : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
    ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c)

namespace IsFilteredDiagram

/-- A functor indexed by a filtered category is a filtered diagram in the source sense. -/
theorem of_isFiltered (M : I ⥤ C) [IsFiltered I] : IsFilteredDiagram M where
  nonempty := IsFiltered.nonempty
  cocone_objs := IsFilteredOrEmpty.cocone_objs
  cocone_maps := by
    intro x y a b
    obtain ⟨z, c, hc⟩ := IsFilteredOrEmpty.cocone_maps a b
    exact ⟨z, c, by simpa using congrArg M.map hc⟩

/-- The identity diagram is filtered exactly when the indexing category is filtered. -/
theorem isFiltered_of_id (h : IsFilteredDiagram (𝟭 I)) : IsFiltered I where
  nonempty := h.nonempty
  cocone_objs := h.cocone_objs
  cocone_maps := by
    intro x y a b
    obtain ⟨z, c, hc⟩ := h.cocone_maps a b
    exact ⟨z, c, by simpa using hc⟩

/-- Definition 4.19.1, index-category clause: `I` is filtered iff its identity diagram is
filtered. -/
theorem id_iff_isFiltered : IsFilteredDiagram (𝟭 I) ↔ IsFiltered I :=
  ⟨isFiltered_of_id, fun _ => of_isFiltered (𝟭 I)⟩

end IsFilteredDiagram

/- Definition 4.19.1: the canonical mathlib notion of a filtered index category is
`CategoryTheory.IsFiltered I`. -/
recall IsFiltered

/-
Domain-style sampling for Definition 4.19.1:
- primary domain: filtered index categories in category theory;
- relevant owner declarations inspected:
  - `CategoryTheory.IsFiltered`,
  - `CategoryTheory.IsFilteredOrEmpty`,
  - `CategoryTheory.IsFiltered.max`,
  - `CategoryTheory.IsFiltered.coeq_condition`;
- best owner abstraction:
  - `source-facing`: `IsFilteredDiagram`, with the textbook nonemptiness,
    common-successor, and diagram-level postcomposition-equalizer conditions;
  - `core/canonical`: `IsFiltered`, with primitive owner data in `IsFilteredOrEmpty`;
  - `bridge/view`: direct downstream existential uses of `IsFilteredOrEmpty.cocone_objs` and
    local equalizer constructions when only the source-facing witnesses are needed;
- primitive data: `IsFiltered.nonempty`, `IsFilteredOrEmpty.cocone_objs`, and
  `IsFilteredOrEmpty.cocone_maps`.

Source/core/bridge triage for Definition 4.19.1:
- `source-facing`: `IsFilteredDiagram`, including the diagram-level
  postcomposition-equalizer condition, and its identity-diagram bridge to `IsFiltered`.
- `core/canonical`: `IsFiltered` and `IsFilteredOrEmpty`.
- `bridge/view`: downstream existential uses of `IsFilteredOrEmpty.cocone_objs` together with
  direct equalizer witnesses on opposite categories.
-/

end CategoryTheory
