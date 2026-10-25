module

public import Mathlib.CategoryTheory.Filtered.Final
public import stacks_project.Chap04.Lemma_4_22_11
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe uI vI uJ vJ uC vC

namespace CategoryTheory

variable {I : Type uI} {J : Type uJ} {C : Type uC}
variable [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]

/- Source/core/bridge triage for Lemma 4.22.12:
- `source-facing`: the product of filtered categories is filtered, and essential constancy is
  unchanged after pulling a diagram back along the second projection.
- `core/canonical`: the mathlib instance `IsFiltered (I × J)` and the chapter owner theorem
  `essentiallyConstantFilteredDiagram_iff_comp_final`.
- `bridge/view`: the final functor `Prod.snd I J : I × J ⥤ J`, whose finality is supplied by the
  filtered-domain instance `CategoryTheory.final_snd`.

Primary domain-style sampling:
- project owner recall: `IsFiltered` in `Definition_4_19_1`;
- mathlib owner instance: `IsFiltered (C × D)` in
  `Mathlib/CategoryTheory/Filtered/Basic.lean`;
- mathlib bridge/view instance: `final_snd` in
  `Mathlib/CategoryTheory/Filtered/Final.lean`;
- project final-functor invariance theorem:
  `essentiallyConstantFilteredDiagram_iff_comp_final` in `Lemma_4_22_11`.

Primitive-vs-derived split:
- primitive source data: filteredness of `I` and `J`, and the diagram `M : J ⥤ C`;
- derived API: filteredness of `I × J`, finality of `Prod.snd I J`, and the pullback invariance of
  `IsEssentiallyConstantFilteredDiagram`. -/

section

variable [IsFiltered I] [IsFiltered J]
variable (M : J ⥤ C)

/- Companion recall: if `I` and `J` are filtered, then the product category `I × J` is filtered.
This is exactly the canonical mathlib instance `IsFiltered (I × J)`. -/
#synth IsFiltered (I × J)

-- Proof sketch: the first clause is the canonical instance `IsFiltered (I × J)`, and the second
-- clause is the specialization of Lemma 4.22.11 to the final projection functor `Prod.snd I J`.
/-- Lemma 4.22.12: if `I` and `J` are filtered, then a diagram `M : J ⥤ C` is essentially
constant if and only if its pullback along the projection `Prod.snd I J : I × J ⥤ J` is
essentially constant. -/
theorem essentiallyConstantFilteredDiagram_iff_comp_snd :
    IsEssentiallyConstantFilteredDiagram M ↔
      IsEssentiallyConstantFilteredDiagram (Prod.snd I J ⋙ M) := by
  simpa using
    (essentiallyConstantFilteredDiagram_iff_comp_final (Prod.snd I J) M)

end

end CategoryTheory
