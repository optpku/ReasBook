module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open ConnectedComponents ObjectProperty

universe v u

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]

/-
Source/core/bridge triage for Lemma 4.19.6:
- `source-facing`: `HasSpanCocones`, the span-completion hypothesis appearing in the text.
- `core/canonical`: `IsFilteredOrEmpty` via `IsFiltered.span`, and `HasPushouts` via
  `pushout.inl`, `pushout.inr`, and `pushout.condition`.
- `bridge/view`: `hasSpanCocones_of_isFilteredOrEmpty`, `hasSpanCocones_of_hasPushouts`, and
  `ConnectedComponents.mk_eq_of_hom` together with
  `exists_common_successor_of_isPreconnected`.
- primitive data: the owner field `HasSpanCocones.span`; no separate exact-interface wrapper is
  kept for this field.
-/

class HasSpanCocones (I : Type u) [Category.{v} I] : Prop where
  span {x y z : I} (f : x ⟶ y) (g : x ⟶ z) :
    ∃ (w : I) (fy : y ⟶ w) (gz : z ⟶ w), f ≫ fy = g ≫ gz

instance hasSpanCocones_of_isFilteredOrEmpty [IsFilteredOrEmpty I] :
    HasSpanCocones I where
  span := IsFiltered.span

attribute [instance 100] hasSpanCocones_of_isFilteredOrEmpty

instance hasSpanCocones_of_hasPushouts [HasPushouts I] : HasSpanCocones I where
  span f g := ⟨pushout f g, pushout.inl f g, pushout.inr f g, pushout.condition⟩

attribute [instance 100] hasSpanCocones_of_hasPushouts

namespace ConnectedComponents

/-- A morphism stays inside a single connected component. -/
theorem mk_eq_of_hom {X Y : I} (f : X ⟶ Y) :
    mk X = mk Y := by
  change Quotient.mk'' X = Quotient.mk'' Y
  exact Quotient.sound' (Zigzag.of_hom f)

end ConnectedComponents

/-- Helper for Lemma 4.19.6: a morphism out of an object already lying in a connected
component `j` forces its target to lie in the same component. -/
theorem mk_eq_component_of_target_hom {j : ConnectedComponents I} {Y W : I}
    (hY : mk Y = j) (f : Y ⟶ W) : mk W = j := by
  -- Move the target back to the known source component using the canonical quotient equality.
  calc
    mk W = mk Y := (ConnectedComponents.mk_eq_of_hom f).symm
    _ = j := hY

/- Companion recall: `CategoryTheory.decomposedEquiv` is the canonical equivalence expressing any
category as the disjoint union of its connected components. -/
recall CategoryTheory.decomposedEquiv

section

variable [HasSpanCocones I]

/-- In a preconnected category satisfying the span-cocone hypothesis, any two objects admit a
common successor. -/
theorem exists_common_successor_of_isPreconnected [IsPreconnected I] (X Y : I) :
    ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := by
  let r : I → I → Prop := fun X Y ↦ ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z)
  have hr : _root_.Equivalence r := by
    refine ⟨?_, ?_, ?_⟩
    · intro X
      exact ⟨X, ⟨𝟙 X⟩, ⟨𝟙 X⟩⟩
    · intro X Y
      rintro ⟨Z, hX, hY⟩
      exact ⟨Z, hY, hX⟩
    · intro X Y Z
      rintro ⟨W₁, hX, hY₁⟩ ⟨W₂, hY₂, hZ⟩
      obtain ⟨f⟩ := hY₁
      obtain ⟨g⟩ := hY₂
      obtain ⟨hXW₁⟩ := hX
      obtain ⟨hZW₂⟩ := hZ
      obtain ⟨W, k₁, k₂, _⟩ := HasSpanCocones.span f g
      exact ⟨W, ⟨hXW₁ ≫ k₁⟩, ⟨hZW₂ ≫ k₂⟩⟩
  exact equiv_relation r hr (fun {_ Y} f ↦ ⟨Y, ⟨f⟩, ⟨𝟙 Y⟩⟩) X Y

-- Proof sketch: a span inside a connected component is still a span in the ambient category, so
-- choose an ambient square completion; then show its cocone point lies in the same connected
-- component because it receives morphisms from objects already in that component.
/-- Lemma 4.19.6: in the canonical decomposition `CategoryTheory.decomposedEquiv`, each connected
component again satisfies the source-text span-completion condition. -/
theorem connected_components_have_span_cocones (j : ConnectedComponents I) : HasSpanCocones j.Component where
  span := by
    intro x y z f g
    -- Forget the componentwise span to the ambient category and complete it there.
    obtain ⟨w, fy, gz, hfg⟩ := HasSpanCocones.span f.hom g.hom
    -- Pull the ambient apex back into the same component using the map from `y`.
    have hw : mk w = j := mk_eq_component_of_target_hom y.property fy
    let w' : j.Component := ⟨w, hw⟩
    let fy' : y ⟶ w' := homMk fy
    let gz' : z ⟶ w' := homMk gz
    -- The lifted maps commute because equality in the full subcategory is detected ambiently.
    have hfg' : f ≫ fy' = g ≫ gz' := by
      apply hom_ext
      simpa [fy', gz'] using hfg
    exact ⟨w', fy', gz', hfg'⟩

/-- Each connected component inherits span cocones from the ambient category. -/
instance (j : ConnectedComponents I) : HasSpanCocones j.Component :=
  connected_components_have_span_cocones j

/-- Corollary form of Lemma 4.19.6: either `I` is empty, or its canonical indexing type of
connected components is nonempty and every component inherits span cocones. -/
theorem isEmpty_or_nonempty_connected_components_have_span_cocones
    : IsEmpty I ∨
        Nonempty (ConnectedComponents I) ∧
          ∀ j : ConnectedComponents I, HasSpanCocones j.Component := by
  rcases isEmpty_or_nonempty I with hI | hI
  · exact Or.inl hI
  · exact Or.inr ⟨hI.map mk, fun j ↦ inferInstance⟩

end

end CategoryTheory
