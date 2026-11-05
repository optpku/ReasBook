module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for the current item:
- primary domain: sheaves of modules on ringed spaces and their direct/inverse image functors;
- sampled owner declarations:
  `AlgebraicGeometry.Scheme.Modules`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `Mathlib.AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`,
  `Mathlib.AlgebraicGeometry.Scheme.Hom.pullback`;
- owner abstraction: following the surrounding `X.Modules` ecosystem for schemes, the ambient
  owner category here should be `RingedSpace.Modules`, defined directly from
  `RingedSpace.ringCatSheaf`, while the primitive bridge data are the forgotten structure-sheaf
  morphism attached to `f`, surfaced as `RingedSpace.Hom.toRingCatSheafHom`; the current item
  itself is the source-facing specialization of `SheafOfModules.pushforward` and
  `SheafOfModules.pullback` along that owner;
- primitive data: the underlying structure-sheaf morphism of `f` after forgetting
  commutativity, together with the canonical adjoint inverse-image map
  `f^{-1} \mathcal O_Y ⟶ \mathcal O_X`;
- derived API: the ringed-space owner `RingedSpace.Modules`, the canonical functors
  `RingedSpace.Hom.pushforward` and `RingedSpace.Hom.pullback`, together with the notation
  `f _*` and `f^*`.

Source/core/bridge triage:
- `source-facing`: the notation `f _*` and `f^*`;
- `core/canonical`: `SheafOfModules.pushforward` and `SheafOfModules.pullback`;
- `bridge/view`: `RingedSpace.ringCatSheaf` and `RingedSpace.Hom.toRingCatSheafHom`.
-/

namespace RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf of not-necessarily-commutative
rings. -/
abbrev ringCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space `X`. -/
abbrev Modules (X : RingedSpace.{u}) :=
  SheafOfModules.{u} X.ringCatSheaf

section

variable {X : RingedSpace.{u}}

public abbrev asCommModulePresheaf (ℱ : X.Modules) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  ℱ.val

public instance instModuleStalkVal (ℱ : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) := by
  change Module (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (asCommModulePresheaf ℱ).presheaf x)
  infer_instance

/-- The stalk of an `\mathcal O_X`-module sheaf at `x`, bundled as an
`\mathcal O_{X, x}`-module. -/
noncomputable abbrev stalkModuleCat (ℱ : X.Modules) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)

end

end RingedSpace

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The structure-sheaf morphism `𝒪_Y ⟶ f_* 𝒪_X` attached to a morphism of ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a morphism of ringed spaces after forgetting commutativity. -/
noncomputable abbrev toRingCatSheafHom :
    Y.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj X.ringCatSheaf :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).map (commRingSheafPushforwardMap f)

/-- The adjoint structure-sheaf morphism `f^{-1}\mathcal O_Y \to \mathcal O_X`. -/
noncomputable abbrev inverseImageStructureSheafHomComm :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _).symm
    (commRingSheafPushforwardMap f)

/-- Definition 6.26.1: the pushforward of an `\mathcal O_X`-module sheaf along a morphism of
ringed spaces `f : X ⟶ Y` is the canonical direct-image functor
`f_* : X.Modules ⥤ Y.Modules`, obtained by restricting scalars along the structure-sheaf morphism
`\mathcal O_Y \to f_* \mathcal O_X`. -/
noncomputable abbrev pushforward :
    X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward (toRingCatSheafHom f)

-- Proof sketch: unfold `pushforward`; it is defined to be the canonical
-- `SheafOfModules.pushforward` functor along `toRingCatSheafHom f`.
/-- Unfolding `pushforward` identifies it with the canonical direct-image functor on sheaves of
modules. -/
theorem pushforward_def :
    pushforward f = SheafOfModules.pushforward (toRingCatSheafHom f) := by
  -- The local abbreviation was defined using the owner direct-image functor.
  rfl

/-- The pullback functor on sheaves of modules along a morphism of ringed spaces. -/
noncomputable abbrev pullback :
    Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback (toRingCatSheafHom f)

end RingedSpace.Hom

/- Source-facing notation for direct and inverse image of module sheaves on ringed spaces. -/
scoped notation:max f:max " _*" => RingedSpace.Hom.pushforward f
scoped notation:max f:max "^*" => RingedSpace.Hom.pullback f

end AlgebraicGeometry
