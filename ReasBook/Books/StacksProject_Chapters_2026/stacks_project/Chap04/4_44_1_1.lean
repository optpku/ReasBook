module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_31_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T X Y : B}
variable (j : S ⟶ T) (x : S ⟶ X) (f : X ⟶ Y) (y : T ⟶ Y)

/- Domain-style sampling for 4.44.1.1:
- primary domain: bicategorical `2`-commutative squares;
- sampled owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Limits.CategoricalPullback.CatCommSqOver.toBicategoricalSquare`,
  `BicategoricalTwoCommutativeSquare.toLeftLift`;
- best owner abstraction: `BicategoricalTwoCommutativeSquare y f`;
- primitive data: the apex object `S`, the boundary morphisms `j`, `x`, and the chosen
  `2`-isomorphism `γ : j ≫ y ≅ x ≫ f`;
- derived API: the packaged square `⟨S, j, x, γ⟩ : BicategoricalTwoCommutativeSquare y f` and its
  canonical left-lift view.

Source/core/bridge triage:
- `source-facing`: the solid square and its chosen witness `γ`;
- `core/canonical`: `BicategoricalTwoCommutativeSquare`;
- `bridge/view`: packaging the source-facing boundary data as an object of
  `BicategoricalTwoCommutativeSquare y f`. -/

variable (γ : j ≫ y ≅ x ≫ f)

/- 4.44.1.1: the displayed solid square with boundary maps `j`, `x`, `f`, and `y`, together with
the chosen `2`-commutativity witness `γ : j ≫ y ≅ x ≫ f`, is recorded by the chapter owner
`BicategoricalTwoCommutativeSquare`. -/
recall BicategoricalTwoCommutativeSquare

/- Companion check: the chosen `2`-commutativity witness has the canonical type
`j ≫ y ≅ x ≫ f`, matching the Stacks notation `γ : y ∘ j → f ∘ x`. -/
#check (γ : j ≫ y ≅ x ≫ f)

/- Companion check: the solid boundary data determine an object of the canonical owner type
`BicategoricalTwoCommutativeSquare y f`. -/
#check (⟨S, j, x, γ⟩ : BicategoricalTwoCommutativeSquare y f)

end CategoryTheory
