module

public import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace ObjectProperty

variable {I : Type u} [Category.{v} I]
variable (P : ObjectProperty I)
variable [IsFiltered I]
variable (h : ∀ X : I, ∃ Y : P.FullSubcategory, Nonempty (X ⟶ Y.obj))

/- Domain sampling:
- Primary domain: filtered categories and full subcategories cut out by an object property.
- Core/canonical declarations inspected:
  - `FullSubcategory`
  - `ι`
  - `fullyFaithfulι`
  - `IsFiltered.of_exists_of_isFiltered_of_fullyFaithful`
  - `Functor.final_of_exists_of_isFiltered_of_fullyFaithful`
- Owner abstraction: the inclusion functor `P.ι : P.FullSubcategory ⥤ I`.
- Layer triage:
  - `source-facing`: the existence hypothesis that every `X : I` maps to an object satisfying `P`;
  - `core/canonical`: the fully faithful inclusion `P.ι`;
  - `bridge/view`: the two source-level consequences obtained by specializing the owner theorems to
    `P.ι`.
- Since the canonical owners are generic theorems rather than named declarations specialized to
  `P.ι`, this file records the specialized bridge layer with `#check` instead of introducing local
  wrapper theorems.
- Primitive vs. derived:
  - primitive data: the object property `P` and the hypothesis `h`;
  - derived API: filteredness of `P.FullSubcategory` and finality of `P.ι`.
-/

/- Owner recall: the full-subcategory inclusion `P.ι` is the canonical owner abstraction from which
the source-facing consequences in Lemma 4.19.3 are derived. -/
recall ι (P : ObjectProperty I) : P.FullSubcategory ⥤ I

/- Lemma 4.19.3, filteredness part: under the source hypothesis `h`, the filteredness of
`P.FullSubcategory` is exactly the canonical owner theorem applied to the inclusion `P.ι`. -/
#check
  (IsFiltered.of_exists_of_isFiltered_of_fullyFaithful P.ι h :
    IsFiltered P.FullSubcategory)

/- Lemma 4.19.3, cofinality part: under the same source hypothesis `h`, the finality of `P.ι` is
exactly the canonical owner theorem specialized to that inclusion. -/
#check
  (Functor.final_of_exists_of_isFiltered_of_fullyFaithful P.ι h :
    P.ι.Final)

end ObjectProperty
end CategoryTheory
