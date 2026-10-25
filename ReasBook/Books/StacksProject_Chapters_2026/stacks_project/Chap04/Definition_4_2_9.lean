module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-
Domain-style sampling for Definition 4.2.9:
- primary domain: categorical functor properties detected on hom-sets and essential image;
- sampled owner-level declarations:
  `Functor.Faithful`,
  `Functor.FullyFaithful`,
  `Functor.FullyFaithful.nonempty_iff_map_bijective`,
  `Functor.EssSurj`;
- best owner abstraction: a functor `F : C ⥤ D` equipped with the canonical owner predicates
  `F.Faithful` and `F.EssSurj`, together with the canonical owner structure `F.FullyFaithful`
  whose nonemptiness expresses the source-level fully faithful condition;
- primitive data: none locally, since these notions are already owned by mathlib;
- derived API: the field-level formulation `Faithful.map_injective`, the essential-image accessor
  `EssSurj.mem_essImage`, and the source-facing fully faithful criterion
  `Functor.FullyFaithful.nonempty_iff_map_bijective`.

Source/core/bridge triage:
- `source-facing`: faithful functors, the hom-set-bijective fully faithful condition, and
  essentially surjective functors;
- `core/canonical`: `Faithful`, `FullyFaithful`, `EssSurj`;
- `bridge/view`: `Faithful.map_injective`, `FullyFaithful.nonempty_iff_map_bijective`, and
  `EssSurj.mem_essImage`. -/

/- Definition 4.2.9: the Stacks notions of faithful, fully faithful, and essentially surjective
functors are the canonical mathlib owner predicates/structures `Functor.Faithful`,
`Functor.FullyFaithful`, and `Functor.EssSurj`; the source-level hom-set bijectivity criterion for
full faithfulness is expressed by `Functor.FullyFaithful.nonempty_iff_map_bijective`. -/
recall Faithful

/- Companion recall: the source fully faithful condition is bijectivity of each induced map on
hom-sets, and mathlib expresses that exact source-facing criterion by the canonical theorem
`Functor.FullyFaithful.nonempty_iff_map_bijective`. -/
recall FullyFaithful.nonempty_iff_map_bijective

/- Companion owner recall: mathlib packages chosen inverse maps on hom-sets in the canonical
structure `Functor.FullyFaithful`; its `Nonempty` is exactly the source-level fully faithful
property by the preceding recall. -/
recall FullyFaithful

/- Companion recall: the Stacks notion of essentially surjective functor is the canonical mathlib
class
`Functor.EssSurj`; its field `mem_essImage` says every target object lies in the essential image,
and `Functor.essImage` is defined by `∃ X : C, Nonempty (F.obj X ≅ Y)`. -/
recall EssSurj

end Functor
end CategoryTheory
