module

public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Lemma_4_42_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsMor

open CategoryOver
open FibredInGroupoidsOver (ofFunctor)

variable {X Y : FibredInGroupoidsOver C}

/- Domain-style sampling for Definition 4.42.3:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.ofFunctor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductLeftProjection`,
  `FibredInGroupoidsMor.toBasedFunctor`,
  `FibredInGroupoidsOver.IsRepresentable`;
- best owner abstraction: the ambient owner hom `F : X ⟶ Y` in `FibredInGroupoidsOver C`. The
  source-facing test object is the slice base-change owner
  `twoFibreProductLeftProjection G F` over `C/U`, viewed through the existing owner
  `twoFibreProduct G F` instead of rebuilding the explicit pullback model locally; the
  representability owner itself remains the ambient hom `F : X ⟶ Y`;
- primitive data: only the owner morphism `F : X ⟶ Y`;
- derived API: the canonical slice base-change owner `sliceTwoFibreProduct F G` over `C/U`. -/

/- Source/core/bridge triage for Definition 4.42.3:
- `source-facing`: `FibredInGroupoidsMor.IsRepresentable` as a property of an owner hom `X ⟶ Y`;
- `core/canonical`: the absolute owner `FibredInGroupoidsOver.IsRepresentable` applied to the
  slice base-change projection over `C/U`;
- `bridge/view`: the representable test objects `ofFunctor (Over.forget U)` and the owner-level
  slice pullback `sliceTwoFibreProduct F G`. -/

noncomputable abbrev sliceTwoFibreProductProjection
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    (FibredInGroupoidsOver.twoFibreProduct G F).S ⥤ Over U :=
  (FibredInGroupoidsMor.toBasedFunctor
    (FibredInGroupoidsOver.twoFibreProductLeftProjection G F)).toFunctor

instance sliceTwoFibreProductProjection_isFibredInGroupoids
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    IsFibredInGroupoids (sliceTwoFibreProductProjection F G) := by
  change IsFibredInGroupoids
    (explicitTwoFibreProductLeftProjection (toBasedFunctor G) (toBasedFunctor F)).toFunctor
  exact explicitTwoFibreProductLeftProjection_isFibredInGroupoids
    (toBasedFunctor F) (toBasedFunctor G)

/-- The canonical slice base change of `F : X ⟶ Y` along `G : C/U ⟶ Y`, regarded as a category
fibred in groupoids over the slice category `C/U`. -/
noncomputable def sliceTwoFibreProduct
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    FibredInGroupoidsOver (Over U) :=
  ofFunctor (sliceTwoFibreProductProjection F G)

instance sliceTwoFibreProduct_isFibredInGroupoids
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    IsFibredInGroupoids (sliceTwoFibreProduct F G).p := by
  unfold sliceTwoFibreProduct
  change IsFibredInGroupoids (sliceTwoFibreProductProjection F G)
  infer_instance

instance sliceTwoFibreProduct_isFibered
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    (sliceTwoFibreProduct F G).p.IsFibered := by
  unfold sliceTwoFibreProduct
  change (sliceTwoFibreProductProjection F G).IsFibered
  infer_instance

/-- Definition 4.42.3: a `1`-morphism `F : X ⟶ Y` of categories fibred in groupoids over `C` is
representable, or relatively representable over `Y`, if for every object `U : C` and every
`1`-morphism `G : C/U ⟶ Y`, the induced slice base change `(C/U) ×[Y] X → C/U` is
representable. -/
def IsRepresentable (F : FibredInGroupoidsMor X Y) : Prop :=
  ∀ ⦃U : C⦄ (G : ofFunctor (Over.forget U) ⟶ Y),
    (sliceTwoFibreProduct F G).IsRepresentable

-- Proof sketch: unfold `FibredInGroupoidsMor.IsRepresentable`; the statement is exactly the
-- defining universal representability condition on all slice base changes.
/-- Companion specification for Definition 4.42.3: a morphism of categories fibred in groupoids is
representable exactly when every canonical slice base change `sliceTwoFibreProduct F G` is a
representable fibred category over the slice base. -/
theorem isRepresentable_iff_forall_sliceTwoFibreProduct_isRepresentable
    (F : FibredInGroupoidsMor X Y) :
    F.IsRepresentable ↔
      ∀ ⦃U : C⦄ (G : ofFunctor (Over.forget U) ⟶ Y),
        (sliceTwoFibreProduct F G).IsRepresentable := by
  -- Unfold the definition: the theorem states exactly the defining condition of representability.
  rfl

end FibredInGroupoidsMor

end CategoryTheory
