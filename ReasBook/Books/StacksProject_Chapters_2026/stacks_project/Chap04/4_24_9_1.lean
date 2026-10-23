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
variable (adj : u ⊣ v) (adj' : u' ⊣ v')

/- Domain-style sampling for Equation 4.24.9.1:
- primary domain: composition of adjunctions in category theory;
- sampled owner API:
  `Adjunction.comp`,
  `Adjunction.comp_unit_app`,
  `Adjunction.comp_counit_app`,
  `Adjunction.comp_homEquiv`;
- best owner abstraction: `CategoryTheory.Adjunction`;
- primitive data: two adjunctions `u ⊣ v` and `u' ⊣ v'`;
- derived API: the induced composite adjunction and its explicit unit/counit formulas.

Source/core/bridge triage:
- `source-facing`: the explicit formula for the counit of the composite adjunction from Lemma
  `4.24.9`;
- `core/canonical`: `Adjunction.comp`;
- `bridge/view`: the owner theorem `Adjunction.comp_counit_app`, which already states exactly this
  counit formula without introducing any local wrapper.
-/
/- 4.24.9.1: for adjunctions `adj : u ⊣ v` and `adj' : u' ⊣ v'`, the counit of the composite
adjunction `adj'.comp adj : u' ⋙ u ⊣ v ⋙ v'` satisfies
`(adj'.comp adj).counit.app X = u.map (adj'.counit.app (v.obj X)) ≫ adj.counit.app X`,
which is the source formula
`ε_X^v ≫ u.map (ε_{v(X)}^{v'}) = ε_X^{v''}`. This is exactly the canonical owner theorem
`Adjunction.comp_counit_app`. -/
recall Adjunction.comp_counit_app

end CategoryTheory
