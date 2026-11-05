module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)

/- Domain-style sampling:
- primary domain: presheaf right Kan extensions into `Type` and the adjunction they induce;
- sampled owner API:
  `Functor.HasPointwiseRightKanExtension`,
  `Functor.pointwiseRightKanExtension`,
  `Functor.ran`,
  `Functor.ranAdjunction`,
- source/core/bridge triage:
  `source-facing`: Lemma 7.19.2 records the pullback/pushforward adjunction on set-valued
    presheaves;
  `core/canonical`: `Functor.ranAdjunction`;
  `bridge/view`: the canonical passage from pointwise right Kan extensions of `Type`-valued
    presheaves along `u.op` to the chosen right Kan extension functor `u.op.ran`.

Primitive data are only the functor `u`; for `Type`-valued presheaves, the needed right Kan
extensions are derived canonically from pointwise limits in `Type`. The adjunction itself is then
derived API from `Functor.ranAdjunction`, so this file should expose that owner after supplying
the canonical presheaf specialization directly rather than add a parallel local wrapper or extra
existence hypotheses to the public API.
-/

section

/- Lemma 7.19.2: for a functor `u : C ⥤ D`, pullback of set-valued presheaves along `u.op`,
realized as precomposition with `u.op`, has as right adjoint the presheaf pushforward realized by
right Kan extension along `u.op`. This is exactly the canonical presheaf specialization of
`Functor.ranAdjunction`. -/
#check (u.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂ w)) :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂ w))).obj u.op ⊣ u.op.ran)

variable (ℱ : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w))
variable (𝒢 : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w))

/- The source-facing hom-set bijection is the `Adjunction.homEquiv` of the presheaf right
Kan-extension adjunction. -/
#check (((u.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂ w))).homEquiv 𝒢 ℱ) :
    ((u.op ⋙ 𝒢) ⟶ ℱ) ≃ (𝒢 ⟶ u.op.ran.obj ℱ))

end

end CategoryTheory
