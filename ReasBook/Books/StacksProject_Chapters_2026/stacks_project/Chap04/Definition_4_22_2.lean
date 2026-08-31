module

public import stacks_project.Chap04.Definition_4_22_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe uI vI uC vC uD vD

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/- Source/core/bridge triage for Definition 4.22.2:
- `source-facing`: the filtered-diagram notion `IsEssentiallyConstantFilteredDiagram`, which says
  that the diagram admits an essentially constant cocone in the sense of Definition 4.22.1, and
  the dual cofiltered-diagram notion defined by existence of an essentially constant cone.
- `core/canonical`: the earlier cocone/cone owners `IsEssentiallyConstantFilteredCocone` and
  `IsEssentiallyConstantCofilteredCone`; the diagram-level predicates here are their canonical
  existence forms.
- `bridge/view`: passage between the cofiltered notion and the filtered notion on the opposite
  diagram.

Primitive-vs-derived split:
- primitive data: only the ambient diagram and an essentially constant cocone/cone witness.
- derived API: the opposite-category bridge and postcomposition invariance. These owner-level
  functoriality statements do not require filteredness assumptions in their public interface.
-/

/-- Definition 4.22.2 (1): a filtered diagram is essentially constant when it admits an essentially
constant cocone in the sense of Definition 4.22.1. For a directed system, this is the same
condition applied to its associated functor. -/
def IsEssentiallyConstantFilteredDiagram (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, IsEssentiallyConstantFilteredCocone c

/-- Definition 4.22.2 (2): a cofiltered diagram is essentially constant when it admits an essentially
constant cone in the sense of Definition 4.22.1. For a directed inverse system, this is the same
condition applied to its associated functor. -/
def IsEssentiallyConstantCofilteredDiagram (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, IsEssentiallyConstantCofilteredCone c

/-- Unfolds Definition 4.22.2 for cofiltered diagrams. -/
theorem isEssentiallyConstantCofilteredDiagram_iff_exists_essentiallyConstantCone
    (M : I ⥤ C) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      ∃ c : Cone M, IsEssentiallyConstantCofilteredCone c :=
  Iff.rfl

/-- Bridge/view reformulation of the cofiltered notion through the opposite filtered diagram. -/
theorem isEssentiallyConstantCofilteredDiagram_iff_op (M : I ⥤ C) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      IsEssentiallyConstantFilteredDiagram M.op := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.op, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.unop, hc⟩

/-- Postcomposition with a functor preserves essential constancy of diagrams. -/
theorem essentiallyConstantFilteredDiagram_compFunctor
    {D : Type uD} [Category.{vD} D] {M : I ⥤ C} (F : C ⥤ D)
    (hM : IsEssentiallyConstantFilteredDiagram M) :
    IsEssentiallyConstantFilteredDiagram (M ⋙ F) := by
  rcases hM with ⟨c, hc⟩
  exact ⟨F.mapCocone c, hc.mapCocone F⟩

/-- The cofiltered variant of `essentiallyConstantFilteredDiagram_compFunctor`. -/
theorem essentiallyConstantCofilteredDiagram_compFunctor
    {D : Type uD} [Category.{vD} D] {M : I ⥤ C} (F : C ⥤ D)
    (hM : IsEssentiallyConstantCofilteredDiagram M) :
    IsEssentiallyConstantCofilteredDiagram (M ⋙ F) := by
  rcases hM with ⟨c, hc⟩
  refine ⟨F.mapCone c, ?_⟩
  change IsEssentiallyConstantFilteredCocone ((F.mapCone c).op)
  simpa using (show IsEssentiallyConstantFilteredCocone c.op from hc).mapCocone F.op
