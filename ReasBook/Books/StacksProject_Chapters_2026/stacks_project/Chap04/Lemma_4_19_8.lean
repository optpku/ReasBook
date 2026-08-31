module

public import stacks_project.Chap04.Definition_4_19_1
public import stacks_project.Chap04.Lemma_4_19_6
public import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe vI uI

namespace CategoryTheory

open ConnectedComponents

variable {I : Type uI} [Category.{vI} I]

/-
Source/core/bridge triage for Lemma 4.19.8:
- `source-facing`: the span-cocone hypothesis `HasSpanCocones I` together with the explicit
  postcomposition-equalizer condition on parallel pairs in `I`.
- `core/canonical`: the canonical connected-component decomposition `decomposedEquiv` and the
  owner predicate `IsFiltered`.
- `bridge/view`: the source-facing conclusion is expressed by proving that every connected
  component in the canonical decomposition is filtered.
-/

/- Companion recall: `CategoryTheory.decomposedEquiv` is the canonical equivalence expressing any
category as the disjoint union of its connected components. -/
recall CategoryTheory.decomposedEquiv

/-- Helper for Lemma 4.19.8: any two objects in one connected component admit a common successor
inside that same component. -/
lemma component_common_successor
    [HasSpanCocones I] (j : ConnectedComponents I) (X Y : j.Component) :
    ∃ (Z : j.Component), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := by
  -- The connectedness of `j.Component` lets us reuse the ambient common-successor theorem
  -- directly inside the full subcategory.
  simpa using exists_common_successor_of_isPreconnected X Y

/-- Helper for Lemma 4.19.8: a morphism out of an object in component `j` lands back in the same
connected component. -/
lemma ambient_target_mem_component
    {j : ConnectedComponents I} {Y : j.Component} {Z : I} (h : Y.obj ⟶ Z) :
    ConnectedComponents.mk Z = j := by
  -- A single morphism already gives the zigzag witnessing equality of connected components.
  calc
    ConnectedComponents.mk Z = ConnectedComponents.mk Y.obj := (ConnectedComponents.mk_eq_of_hom h).symm
    _ = j := Y.property

/-- Helper for Lemma 4.19.8: a parallel pair inside one connected component becomes equal after
postcomposition with a morphism that still lies in that component. -/
lemma component_parallel_pair_equalizer
    [HasSpanCocones I]
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    {j : ConnectedComponents I} {X Y : j.Component} (f g : X ⟶ Y) :
    ∃ (Z : j.Component) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
  -- Apply the ambient equalizer hypothesis to the underlying morphisms.
  obtain ⟨Z, h, hh⟩ := hMap f.hom g.hom
  let Z' : j.Component := ⟨Z, ambient_target_mem_component h⟩
  let h' : Y ⟶ Z' := ObjectProperty.homMk h
  -- Lift the ambient equalizing morphism back into the full subcategory.
  refine ⟨Z', h', ?_⟩
  apply ObjectProperty.hom_ext j.objectProperty
  simpa [h'] using hh

-- Proof sketch: use `decomposedEquiv` to write `I` as the disjoint union of its connected
-- components; Lemma 4.19.6 supplies common successors inside each component from
-- `HasSpanCocones I`, and the postcomposition-equalizer hypothesis descends to the componentwise
-- full subcategories, giving the remaining filteredness axiom.
/-- Lemma 4.19.8: if every span in `I` admits a commuting cocone and every parallel pair in `I`
is equalized after postcomposition, then each connected component in the canonical decomposition
of `I` is a filtered index category. Together with `CategoryTheory.decomposedEquiv`, this is the
library-facing form of the statement that `I` is a possibly empty disjoint union of filtered
index categories. -/
theorem connected_components_are_filtered
    [HasSpanCocones I]
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    (j : ConnectedComponents I) :
    IsFiltered j.Component := by
  -- Build the two `IsFilteredOrEmpty` witness fields componentwise, following the source proof's
  -- equivalence-class decomposition into connected components.
  letI : IsFilteredOrEmpty j.Component :=
    { cocone_objs := by
        intro X Y
        -- Connectedness inside the component provides a common successor for the object pair.
        obtain ⟨Z, hX, hY⟩ := component_common_successor j X Y
        obtain ⟨f⟩ := hX
        obtain ⟨g⟩ := hY
        exact ⟨Z, f, g, trivial⟩
      cocone_maps := by
        intro X Y f g
        -- The ambient postcomposition equalizer lifts back to the same component.
        exact component_parallel_pair_equalizer hMap f g }
  -- Each connected component is already nonempty, so the `IsFiltered` structure is complete.
  exact IsFiltered.mk

end CategoryTheory
