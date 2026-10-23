module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
public import stacks_project.Chap06.Definition_6_21_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopCat.Presheaf TopCat.Sheaf
open AlgebraicGeometry

universe v u

noncomputable section

namespace TopCat.Sheaf

variable {A : Type u} [Category.{v} A] [HasColimits A]

/-- Helper for Lemma 6.21.10: package a sheaf on `X` as the corresponding sheafed space. -/
public abbrev toSheafedSpace {X : TopCat.{v}} (ℱ : X.Sheaf A) : SheafedSpace A :=
  { carrier := X
    presheaf := ℱ.presheaf
    IsSheaf := ℱ.2 }

/-- Helper for Lemma 6.21.10: turn an `f`-map of sheaves into the corresponding morphism of
sheafed spaces over `f`. -/
public abbrev toSheafedSpaceHom {X Y : TopCat.{v}} (f : X ⟶ Y) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) :
    ℱ.toSheafedSpace ⟶ 𝒢.toSheafedSpace :=
  InducedCategory.homMk { base := f, c := φ.1 }

/-- Helper for Lemma 6.21.10: the induced stalk map of an `f`-map of sheaves. -/
abbrev stalkMap {X Y : TopCat.{v}} (f : X ⟶ Y) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) (x : X) :
    𝒢.presheaf.stalk (f x) ⟶ ℱ.presheaf.stalk x :=
  (toSheafedSpaceHom f φ).hom.stalkMap x

end TopCat.Sheaf

/- Domain-style sampling for Lemma 6.21.10:
- primary domain: stalk functoriality for morphisms of sheafed spaces, specialized to sheaf
  morphisms into a pushforward along a continuous map, at the generic coefficient-category level;
- inspected owner declarations:
  `PresheafedSpace.Hom.stalkMap`,
  `PresheafedSpace.stalkMap.comp`,
  `RingedSpace.Hom.stalkMap`,
  `TopCat.Sheaf.pushforward`,
  `SheafedSpace`;
- owner abstraction: an `f`-map `φ : 𝒢 ⟶ f_* ℱ` is exactly the sheaf component of a morphism
  between the sheafed spaces attached to `ℱ` and `𝒢`; the internal bridge to
  `PresheafedSpace.Hom.stalkMap` is proof support only, while the public source-facing bridge
  owner is `TopCat.Sheaf.stalkMap`; its correct ambient level is the same generic coefficient
  category `A` used by the canonical owners, and the set-valued textbook statement is recovered by
  specializing `A := Type u`; composition is therefore derived from the canonical theorem
  `PresheafedSpace.stalkMap.comp`;
- primitive data: a continuous map `f : X ⟶ Y`, a sheaf morphism `φ : 𝒢 ⟶ f_* ℱ`, and a point
  `x : X`, with coefficients in a category `A` carrying the colimits needed for stalks;
- derived API: the source-facing owner `TopCat.Sheaf.stalkMap`, internally implemented via the
  bridge from an `f`-map to a morphism of sheafed spaces.

Source/core/bridge triage:
- `source-facing`: the induced stalk map `TopCat.Sheaf.stalkMap` and its compatibility with
  composition of `f`-maps;
- `core/canonical`: `PresheafedSpace.Hom.stalkMap` and
  `PresheafedSpace.stalkMap.comp`;
- `bridge/view`: the private conversion sending a sheaf `ℱ` on `X` to the sheafed space `(X, ℱ)`
  and an `f`-map `φ : 𝒢 ⟶ f_* ℱ` to the corresponding sheafed-space morphism with base `f`. -/

namespace TopCat.Sheaf

variable {A : Type u} [Category.{v} A] [HasColimits A]

/-- Lemma 6.21.10: for composable continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, a coefficient
category `A` with the colimits needed for stalks, and `f`- and `g`-maps of `A`-valued sheaves,
the map on stalks of the composite `(φ ∘ ψ)` is the composition `ψ_{f(x)} ≫ φ_x`. The Stacks
Project statement is the specialization `A := Type u`. -/
theorem stalkMap_comp {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A} {ℋ : Z.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) (ψ : ℋ ⟶ (pushforward A g).obj 𝒢) (x : X) :
    stalkMap (f ≫ g) (ψ ≫ (pushforward A g).map φ) x =
      stalkMap g ψ (f x) ≫ stalkMap f φ x := by
  -- Rewrite the textbook stalk maps through the sheafed-space bridge and apply the canonical
  -- composition theorem for stalk maps of morphisms of presheafed spaces.
  simpa only [stalkMap, toSheafedSpaceHom] using
    (PresheafedSpace.stalkMap.comp (toSheafedSpaceHom f φ).hom (toSheafedSpaceHom g ψ).hom x)

end TopCat.Sheaf
