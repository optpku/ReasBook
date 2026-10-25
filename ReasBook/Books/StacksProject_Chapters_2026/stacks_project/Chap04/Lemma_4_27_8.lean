module

import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MorphismProperty.LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]

/- Companion recall: the canonical functor from `C` to the left-fraction localization of `W` is
`Q W : C ⥤ LeftFraction.Localization W`. -/
recall Q

/- Companion recall: if `s : X ⟶ Y` lies in `W`, then its image under `Q W` is canonically an
isomorphism, namely `Qiso s hs`. -/
recall Qiso

/- Companion recall: the strict universal property for the left-fraction model is packaged by
`strictUniversalPropertyFixedTarget`. -/
recall strictUniversalPropertyFixedTarget

/- Domain-style sampling in the left-fraction localization owner API:
- source-facing model: `LeftFraction.Localization W`
- core/canonical owner predicate: `Functor.IsLocalization`
- canonical localization functor: `Q W`
- canonical inverted isomorphisms: `Qiso`
- universal property owner: `strictUniversalPropertyFixedTarget`
- owner instance for the left-fraction model: `instIsLocalizationQ`

Primitive data: the morphism property `W` together with its left-calculus-of-fractions structure.
Derived API: the localized category, the functor `Q W`, the inverted morphisms `Qiso`, and the
strict universal property.

The main labeled entry below should therefore be a direct recall of the canonical localization
owner instance, rather than a new wrapper theorem restating the same universal property. -/
/- Lemma 4.27.8: for a left multiplicative system `W`, the rules `X ↦ X` and
`f : X ⟶ Y ↦ (f, 𝟙 Y)` define the canonical functor `Q W : C ⥤ LeftFraction.Localization W`;
every `s ∈ W` becomes an isomorphism under `Q W`; and `Q W` satisfies the universal property that
any functor out of `C` inverting `W` factors uniquely through `LeftFraction.Localization W`.
This is the owner-level localization statement `Functor.IsLocalization` for `Q W`. -/
recall instIsLocalizationQ : (Q W).IsLocalization W

end CategoryTheory
