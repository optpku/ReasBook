module

public import stacks_project.Chap04.Lemma_4_22_11
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe uI vI uJ vJ uC vC

/- Domain-style sampling for Lemma 4.22.13:
- primary domain: essentially constant cofiltered diagrams and their behavior under initial
  pullback.
- inspected owner-level declarations:
  `IsEssentiallyConstantCofilteredDiagram` in `Definition_4_22_2`,
  `isEssentiallyConstantCofilteredDiagram_iff_op` in `Definition_4_22_2`,
  `essentiallyConstantFilteredDiagram_iff_comp_final` in `Lemma_4_22_11`.
- inspected mathlib duality declaration:
  `CategoryTheory.final_op_of_initial` / instance `CategoryTheory.final_op_of_initial`,
  used through the canonical finality of `H.op`.
- best owner abstraction for the main proposition: `IsEssentiallyConstantCofilteredDiagram M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cone on the cofiltered diagram, equivalently the
  opposite filtered diagram being essentially constant.
- derived API: the initial-pullback invariance statement below, obtained by transporting the
  filtered result across the canonical opposite-category bridge.

Source/core/bridge triage:
- `source-facing`: the textbook claim that essential constancy is preserved and reflected by
  pullback along an initial functor.
- `core/canonical`: `IsEssentiallyConstantCofilteredDiagram`.
- `bridge/view`: passage to the opposite filtered diagram via
  the definition of `IsEssentiallyConstantCofilteredDiagram`, and then to the filtered
  invariance theorem `essentiallyConstantFilteredDiagram_iff_comp_final`. -/

-- Proof sketch: pass to the opposite diagram `M.op : Jᵒᵖ ⥤ Cᵒᵖ`, where `H.op` is final, apply
-- Lemma 4.22.11, and translate back through the canonical cone/cocone duality.
/-- Lemma 4.22.13: for an initial functor `H : I ⥤ J` from a cofiltered index category, a
diagram `M : J ⥤ C` is essentially constant if and only if its pullback `H ⋙ M` is essentially
constant. -/
theorem essentiallyConstantCofilteredDiagram_iff_comp_initial
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      IsEssentiallyConstantCofilteredDiagram (H ⋙ M) := by
  simpa [isEssentiallyConstantCofilteredDiagram_iff_op] using
    (essentiallyConstantFilteredDiagram_iff_comp_final (H.op) M.op)
