module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling:
- primary domain: presheaf left Kan extensions and their units;
- sampled owner API:
  `Functor.leftKanExtensionUnit`,
  `HasLeftKanExtension`,
  `Functor.lanAdjunction`,
  nearby chapter analogue `Lemma_7_19_1` for the right Kan extension counit;
- source-facing: Lemma 7.5.3 records the canonical evaluation map and its compatibility with
  restriction maps;
- core/canonical: `Functor.leftKanExtensionUnit`;
- bridge/view: the component at `U` and the naturality equation for `f : U' ⟶ U`.

Primitive data are `u`, `ℱ`, and the existence of the left Kan extension along `u.op`. The
component map and its restriction compatibility are derived API from the unit natural
transformation, so this file should expose that owner projection directly rather than a parallel
local definition.
-/

/- Lemma 7.5.3: for a presheaf `ℱ` on `C` and `u : C ⥤ D`, the canonical map
`ℱ(U) ⟶ {}_p u \mathcal F (u(U))` is the component at `U` of the left Kan extension unit
`u.op.leftKanExtensionUnit ℱ`. -/
recall Functor.leftKanExtensionUnit

variable (u : C ⥤ D) (ℱ : Cᵒᵖ ⥤ Type w) [HasLeftKanExtension u.op ℱ]
variable {U U' : C} (f : U' ⟶ U)

/- The source-facing map of Lemma 7.5.3 is the `U`-component of that unit. -/
#check ((u.op.leftKanExtensionUnit ℱ).app (op U) :
    ℱ.obj (op U) ⟶ (u.op.leftKanExtension ℱ).obj (op (u.obj U)))

/- The restriction-map compatibility in Lemma 7.5.3 is exactly the naturality of the unit:
for `f : U' ⟶ U`, this is `(u.op.leftKanExtensionUnit ℱ).naturality f.op`. -/
#check ((u.op.leftKanExtensionUnit ℱ).naturality f.op :
    ℱ.map f.op ≫ (u.op.leftKanExtensionUnit ℱ).app (op U') =
      (u.op.leftKanExtensionUnit ℱ).app (op U) ≫
        (u.op.leftKanExtension ℱ).map (u.map f).op)

end CategoryTheory
