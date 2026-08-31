module

public import Mathlib.CategoryTheory.Filtered.Basic
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe vI vC uI uC

namespace CategoryTheory
namespace Functor

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/- Domain-style sampling for Definition 4.20.1:
- primary domain: cofiltered diagrams and the passage from a source-facing diagram condition to the
  canonical cofilteredness of the indexing category.
- relevant owner declarations inspected:
  - `CategoryTheory.IsCofiltered` and `CategoryTheory.IsCofilteredOrEmpty` in
    `Mathlib/CategoryTheory/Filtered/Basic.lean`,
  - `nonempty_sections_of_finite_cofiltered_system` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`,
  - the chapter owner recall `CategoryTheory.IsFiltered` in `Definition_4_19_1`,
  - the source-facing system owner `I ⥤ C` in `Definition_4_21_2`.
- best owner abstraction:
  - `source-facing`: `Functor.IsCofiltered M` for a diagram `M : I ⥤ C`,
  - `core/canonical`: `CategoryTheory.IsCofiltered I` for the identity diagram special case,
  - `bridge/view`: a cofiltered index category makes every diagram cofiltered, and the identity
    diagram recovers the canonical owner exactly.
- primitive data: nonemptiness of `I`, common predecessors in `I`, and eventual equalization of
  parallel arrows after applying `M`.
- derived API: `Functor.IsCofiltered.of_index` and `id_isCofiltered_iff`. -/

/- Source/core/bridge triage for Definition 4.20.1:
- `source-facing`: the Stacks definition of a cofiltered diagram `M : I ⥤ C`, where equalization
  is only required after applying `M`.
- `core/canonical`: `CategoryTheory.IsCofiltered I`, recovered when `M = 𝟭 I`.
- `bridge/view`: theorems comparing `M.IsCofiltered` with category-level cofilteredness. -/

/-- Definition 4.20.1: a diagram `M : I ⥤ C` is cofiltered if `I` is nonempty, every pair of
indices admits a common predecessor, and every parallel pair in `I` becomes equal after
precomposition and then applying `M`. -/
def IsCofiltered (M : I ⥤ C) : Prop :=
  Nonempty I ∧
    (∀ i j : I, ∃ k : I, Nonempty (k ⟶ i) ∧ Nonempty (k ⟶ j)) ∧
    (∀ ⦃i j : I⦄ (a b : i ⟶ j), ∃ (k : I) (c : k ⟶ i), M.map c ≫ M.map a = M.map c ≫ M.map b)

namespace IsCofiltered

/-- A diagram indexed by a cofiltered category is cofiltered in the source sense. -/
theorem of_index [CategoryTheory.IsCofiltered I] (M : I ⥤ C) :
    M.IsCofiltered := by
  refine ⟨CategoryTheory.IsCofiltered.nonempty, ?_, ?_⟩
  · intro i j
    rcases IsCofilteredOrEmpty.cone_objs i j with ⟨k, f, g, _⟩
    exact ⟨k, ⟨f⟩, ⟨g⟩⟩
  · intro i j a b
    rcases IsCofilteredOrEmpty.cone_maps a b with ⟨k, c, hc⟩
    exact ⟨k, c, by simpa [Functor.map_comp] using congrArg (M.map) hc⟩

end IsCofiltered

/-- The identity diagram is cofiltered exactly when its index category is cofiltered. -/
theorem id_isCofiltered_iff :
    (𝟭 I : I ⥤ I).IsCofiltered ↔ CategoryTheory.IsCofiltered I := by
  constructor
  · rintro ⟨hI, hObj, hMap⟩
    refine { nonempty := hI, cone_objs := ?_, cone_maps := ?_ }
    · intro i j
      rcases hObj i j with ⟨k, ⟨f⟩, ⟨g⟩⟩
      exact ⟨k, f, g, trivial⟩
    · intro i j a b
      rcases hMap a b with ⟨k, c, hc⟩
      exact ⟨k, c, hc⟩
  · intro hI
    let _ : CategoryTheory.IsCofiltered I := hI
    simpa using IsCofiltered.of_index (𝟭 I : I ⥤ I)

end Functor
end CategoryTheory
