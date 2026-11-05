module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_22_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 4.22.8:
- primary domain: essentially constant filtered/cofiltered diagrams and their behavior under
  postcomposition by a functor.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredDiagram`,
  `IsEssentiallyConstantCofilteredDiagram`,
  `essentiallyConstantFilteredDiagram_compFunctor`,
  `essentiallyConstantCofilteredDiagram_compFunctor`.
- best owner abstraction for the main statements: the chapter owners
  `IsEssentiallyConstantFilteredDiagram M` and `IsEssentiallyConstantCofilteredDiagram M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cocone/cone from Definitions 4.22.1 and 4.22.2.
- derived API: the postcomposition invariance theorems now owned directly by
  `Definition_4_22_2`, so this numbered file should recall them rather than re-prove a parallel
  copy.

Source/core/bridge triage:
- `source-facing`: postcomposition preserves essential constancy for filtered and cofiltered
  diagrams.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram M` and
  `IsEssentiallyConstantCofilteredDiagram M`.
- `bridge/view`: owner-level functoriality in `Definition_4_22_2`, itself derived from the
  cocone-level theorem `IsEssentiallyConstantFilteredCocone.mapCocone` and the opposite-category
  definition of `IsEssentiallyConstantCofilteredDiagram`. -/

/- Lemma 4.22.8: postcomposition with a functor preserves essential constancy of filtered
diagrams. The canonical owner theorem lives in `Definition_4_22_2`. -/
recall essentiallyConstantFilteredDiagram_compFunctor

/- Lemma 4.22.8, dual form: postcomposition with a functor preserves essential constancy of
cofiltered diagrams. The canonical owner theorem lives in `Definition_4_22_2`. -/
recall essentiallyConstantCofilteredDiagram_compFunctor
