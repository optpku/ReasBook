module

public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {u : B ⥤ A} {v : A ⥤ B}
variable {u' : C ⥤ B} {v' : B ⥤ C}

/- Domain-style sampling for Lemma 4.24.9:
- primary domain: adjunctions in category theory;
- sampled owner API:
  `Adjunction`,
  `Adjunction.comp`,
  `Adjunction.comp_unit_app`,
  `Adjunction.comp_counit_app`;
- best owner abstraction: `CategoryTheory.Adjunction`.

Primitive-vs-derived split:
- primitive data: the chosen adjunctions `u ⊣ v` and `u' ⊣ v'`;
- derived API: their composite adjunction `u' ⋙ u ⊣ v ⋙ v'` and the corresponding unit/counit
  formulas. Since this item is just the composite adjunction itself, it should be a direct recall
  of the owner construction rather than a parallel local wrapper.
-/

/- Source/core/bridge triage for Lemma 4.24.9:
- source-facing: the textbook composes two chosen adjunctions `u ⊣ v` and `u' ⊣ v'`.
- core/canonical: mathlib already owns this construction as `Adjunction.comp`.
- bridge/view: the explicit counit formula is the separate companion recall `4_24_9_1`. -/

/- Lemma 4.24.9 (1): if `v : A ⥤ B` and `v' : B ⥤ C` have left adjoints `u` and `u'`
respectively, then the composite `v ⋙ v'` has left adjoint `u' ⋙ u`. This is exactly the canonical
mathlib construction `Adjunction.comp`. The counit formula in part (2) is the separate item
`4.24.9.1`. -/
recall Adjunction.comp

end CategoryTheory
