module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {X Y Z : RingedSpace.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Domain-style sampling for Definition 6.25.3:
- primary domain: categorical composition of morphisms in `RingedSpace` and the resulting formulas
  on the underlying `SheafedSpace` and topological-space components;
- sampled owner declarations:
  `CategoryStruct.comp`,
  `InducedCategory.comp_hom`,
  `SheafedSpace.comp_hom_base`,
  `SheafedSpace.comp_hom_c_app'`;
- owner abstraction: categorical composition in `RingedSpace`;
- primitive data: composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the formulas for the underlying `SheafedSpace` morphism, the underlying continuous
  map, and the sectionwise structure-sheaf map of `f ≫ g`.

Source/core/bridge triage:
- `source-facing`: the Stacks formula
  `(g, g^\sharp) \circ (f, f^\sharp) = (g \circ f, f^\sharp \circ g^\sharp)`;
- `core/canonical`: categorical composition in `RingedSpace`;
- `bridge/view`: the induced component formulas
  `InducedCategory.comp_hom`, `SheafedSpace.comp_hom_base`, and
  `SheafedSpace.comp_hom_c_app'`.

This item only recalls canonical owner data already present upstream, so the refined file should
stay recall-shaped and avoid any parallel local wrapper for composition. -/

/- Definition 6.25.3: the composition of morphisms of ringed spaces is the canonical categorical
composition `f ≫ g : X ⟶ Z`. This matches the Stacks Project formula
`(g, g^\sharp) ∘ (f, f^\sharp) = (g ∘ f, f^\sharp ∘ g^\sharp)`. -/
#check (f ≫ g : X ⟶ Z)

/- Companion recall: on the underlying `SheafedSpace`, composition is exactly the canonical
induced-category composition theorem. -/
recall InducedCategory.comp_hom

#check (InducedCategory.comp_hom f g : (f ≫ g).hom = f.hom ≫ g.hom)

/- Companion recall: on underlying continuous maps, the same formula is the standard
`SheafedSpace` component lemma. -/
recall SheafedSpace.comp_hom_base

#check (SheafedSpace.comp_hom_base f g :
  (f ≫ g).hom.base = f.hom.base ≫ g.hom.base)

/- Companion recall: on sections over an open `U ⊆ Z`, the structure-sheaf component of the
composite is the composite `g^\sharp(U) ≫ f^\sharp(g^{-1}U)`. -/
recall SheafedSpace.comp_hom_c_app'

variable (U : Opens Z)

#check (SheafedSpace.comp_hom_c_app' f g U)

end AlgebraicGeometry
