module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 4.6.5:
- primary domain: morphism properties in `CategoryTheory`, specialized to representable morphisms.
- inspected owner declarations:
  `MorphismProperty.comp_mem`,
  `MorphismProperty.IsStableUnderComposition`,
  `Functor.relativelyRepresentable`,
  `Functor.relativelyRepresentable.isMultiplicative`.
- best owner abstraction: the morphism property `(𝟭 C).relativelyRepresentable`, whose
  composition stability is inherited from the generic owner theorem `MorphismProperty.comp_mem`.
- primitive-vs-derived split:
  primitive data: only the morphisms `f`, `g` and their representability hypotheses.
  derived API: closure under composition, supplied canonically by the `IsMultiplicative` instance
    on `Functor.relativelyRepresentable`. -/

/- Source/core/bridge triage for Lemma 4.6.5:
- `source-facing`: the composite of two representable morphisms is representable.
- `core/canonical`: `MorphismProperty.comp_mem` for the morphism property
  `(𝟭 C).relativelyRepresentable`.
- `bridge/view`: the specialization from relative representability with respect to a general
  functor to the identity functor on `C`.
-/

/- Core owner recall: the multiplicative structure on relatively representable morphisms is the
upstream instance `Functor.relativelyRepresentable.isMultiplicative`. -/
recall Functor.relativelyRepresentable.isMultiplicative

/- Lemma 4.6.5: the composite of representable morphisms in a category is exactly the canonical
composition theorem for the morphism property `(𝟭 C).relativelyRepresentable`, derived from that
owner instance through `MorphismProperty.comp_mem`. -/
#check ((𝟭 C).relativelyRepresentable).comp_mem

end CategoryTheory
