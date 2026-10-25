module

public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {U₁ U₂ : C ⥤ D} {V₁ V₂ : D ⥤ C}
variable (adj₁ : U₁ ⊣ V₁) (adj₂ : U₂ ⊣ V₂)

/- Domain-style sampling for Lemma 4.24.8:
- primary domain: adjunction mates/conjugation in category theory;
- sampled owner API:
  `Adjunction`,
  `conjugateEquiv`,
  `conjugateEquiv_counit`,
  `unit_conjugateEquiv`;
- best owner abstraction: the adjunction-mates API in
  `Mathlib.CategoryTheory.Adjunction.Mates`.

Primitive-vs-derived split:
- primitive data: the two adjunctions `adj₁ : U₁ ⊣ V₁` and `adj₂ : U₂ ⊣ V₂`;
- derived API: the conjugation equivalence between natural transformations of left and right
  adjoints, and its unit/counit compatibility lemmas. This item is purely derived API, so it
  should be a direct recall of the owner theorem rather than a parallel local wrapper.
-/

/- Source/core/bridge triage for Lemma 4.24.8:
- source-facing: the textbook counit square comparing a natural transformation of left adjoints
  with its conjugate transformation of right adjoints;
- core/canonical: `conjugateEquiv_counit`;
- bridge/view: `conjugateEquiv` supplies the corresponding mate on right adjoints, but no extra
  local bridge declaration is needed here.
-/

/- Lemma 4.24.8: if `β : U₂ ⟶ U₁` is a natural transformation between left adjoints and
`conjugateEquiv adj₁ adj₂ β : V₁ ⟶ V₂` is the corresponding transformation of right adjoints,
then for each `d : D` the counit square commutes. This is exactly the canonical mathlib theorem
`conjugateEquiv_counit`. -/
recall conjugateEquiv_counit

end CategoryTheory
