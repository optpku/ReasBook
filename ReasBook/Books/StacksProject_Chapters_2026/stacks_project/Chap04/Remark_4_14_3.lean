module

public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/-
Domain-style sampling for Remark 4.14.3:
- primary domain: category-theoretic size conventions for diagram shapes in limits and colimits
- sampled canonical declarations:
  `SmallCategory`,
  `HasLimitsOfShape`,
  `HasColimitsOfShape`
- best owner abstraction: `SmallCategory`; the limit/colimit classes consume the small indexing
  category rather than replacing it with a new owner
- primitive data: the small category structure on the indexing type
- derived API: the shape-indexed limit and colimit classes

Source/core/bridge triage:
- source-facing: the textbook convention that the indexing category for a limit or colimit is
  small
- core/canonical: `SmallCategory`
- bridge/view: `HasLimitsOfShape` and `HasColimitsOfShape` as downstream users of the size
  convention, not new abstractions for it
-/
/- Remark 4.14.3: the size convention on indexing categories for limits and colimits is the
canonical category structure abbreviation `SmallCategory`. -/
recall SmallCategory

end CategoryTheory
