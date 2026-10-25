module

public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp_
public import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Monoidal MonoidalCategory CartesianMonoidalCategory MonObj

/- Domain-style sampling for topological groups:
- primary domain: category-theoretic limits of topological groups, organized canonically as group
  objects in `TopCat`.
- sampled owner declarations:
  `Grp TopCat`,
  `Grp.forget TopCat`,
  `Functor.mapGrp`,
  `grpTypeEquivalenceGrp`.
- best owner abstraction: `Grp TopCat` is the core/canonical owner. The only extra data this file
  needs is the bridge from `Grp TopCat` to `GrpCat`, obtained by forgetting `TopCat` to `Type` and
  then using `grpTypeEquivalenceGrp`.

Layer triage:
- `source-facing`: Lemma 5.30.3, asserting that the category of topological groups has limits and
  that the forgetful functors to `TopCat` and `GrpCat` preserve them.
- `core/canonical`: `Grp TopCat` together with the generic `Grp`-limits machinery.
- `bridge/view`: the concrete-category bridge via `ContinuousMonoidHom` and the forgetful functor
  `forget₂ (Grp TopCat) GrpCat`.

Primitive data already lives in the owner `Grp TopCat`. The `GrpCat` bridge and the preservation
results are derived API and should not force an extra public wrapper category; only the concrete
morphism realization by `ContinuousMonoidHom` is needed to build the canonical forgetful functor to
`GrpCat`.
-/

instance (X : Grp TopCat.{u}) : Group X.X where
  one := (TopCat.Hom.hom η[X.X]) PUnit.unit
  mul x y := (TopCat.Hom.hom μ[X.X]) (x, y)
  inv x := (TopCat.Hom.hom ι[X.X]) x
  one_mul x := by
    change (ConcreteCategory.hom (η[X.X] ▷ X.X ≫ μ[X.X])) (PUnit.unit, x) =
      (ConcreteCategory.hom (λ_ X.X).hom) (PUnit.unit, x)
    exact ConcreteCategory.congr_hom (MonObj.one_mul X.X) (PUnit.unit, x)
  mul_one x := by
    change (ConcreteCategory.hom (X.X ◁ η[X.X] ≫ μ[X.X])) (x, PUnit.unit) =
      (ConcreteCategory.hom (ρ_ X.X).hom) (x, PUnit.unit)
    exact ConcreteCategory.congr_hom (MonObj.mul_one X.X) (x, PUnit.unit)
  mul_assoc x y z := by
    change (ConcreteCategory.hom (μ[X.X] ▷ X.X ≫ μ[X.X])) ((x, y), z) =
      (ConcreteCategory.hom ((α_ X.X X.X X.X).hom ≫ X.X ◁ μ[X.X] ≫ μ[X.X])) ((x, y), z)
    exact ConcreteCategory.congr_hom (MonObj.mul_assoc X.X) ((x, y), z)
  inv_mul_cancel x := by
    change (ConcreteCategory.hom (lift ι[X.X] (𝟙 X.X) ≫ μ[X.X])) x =
      (ConcreteCategory.hom (toUnit X.X ≫ η[X.X])) x
    exact ConcreteCategory.congr_hom (GrpObj.left_inv X.X) x

instance instIsMonHomOfContinuousMonoidHom {X Y : Grp TopCat.{u}} (f : X.X →ₜ* Y.X) :
    IsMonHom (show X.X ⟶ Y.X from TopCat.ofHom f.toContinuousMap) where
  one_hom := by
    ext x
    change f 1 = (1 : Y.X)
    simp
  mul_hom := by
    ext x
    change f (x.1 * x.2) = f x.1 * f x.2
    simp

/-- The underlying continuous group homomorphism of a morphism in `Grp TopCat`. -/
abbrev homToContinuousMonoidHom {X Y : Grp TopCat.{u}} (f : X ⟶ Y) :
    X.X →ₜ* Y.X where
  toFun := f.hom.hom
  map_one' := by
    change (ConcreteCategory.hom (η[X.X] ≫ f.hom.hom)) PUnit.unit =
      (ConcreteCategory.hom η[Y.X]) PUnit.unit
    exact ConcreteCategory.congr_hom (IsMonHom.one_hom f.hom.hom) PUnit.unit
  map_mul' x y := by
    change (ConcreteCategory.hom (μ[X.X] ≫ f.hom.hom)) (x, y) =
      (ConcreteCategory.hom ((f.hom.hom ⊗ₘ f.hom.hom) ≫ μ[Y.X])) (x, y)
    exact ConcreteCategory.congr_hom (IsMonHom.mul_hom f.hom.hom) (x, y)
  continuous_toFun := (TopCat.Hom.hom f.hom.hom).continuous

instance : ConcreteCategory (Grp TopCat.{u}) (fun X Y ↦ X.X →ₜ* Y.X) where
  hom := homToContinuousMonoidHom
  ofHom := by
    intro X Y f
    exact Grp.homMk (show X.X ⟶ Y.X from TopCat.ofHom f.toContinuousMap)
  hom_ofHom := by
    intro X Y f
    ext x
    rfl
  ofHom_hom := by
    intro X Y f
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    rfl

noncomputable instance : HasForget₂ (Grp TopCat.{u}) GrpCat.{u} :=
  { forget₂ := by
      let _ : (forget TopCat.{u}).Monoidal :=
        Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
      exact (forget TopCat.{u}).mapGrp ⋙ grpTypeEquivalenceGrp.functor
    forget_comp := rfl }

/- The proof of preservation to `GrpCat` factors through the internal-group forgetful functor to
`Grp (Type u)`. This helper is implementation-only; the public surface should use
`forget₂ (Grp TopCat) GrpCat`. -/
private noncomputable abbrev topologicalGroupToGrpType : Grp TopCat.{u} ⥤ Grp (Type u) := by
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  exact (forget TopCat.{u}).mapGrp

private noncomputable def topologicalGroupToGrpType_mapConeIsLimit
    {J : Type v} [Category.{w} J] [Small.{u} J]
    (F : J ⥤ Grp TopCat.{u}) :
    IsLimit (topologicalGroupToGrpType.mapCone (limit.cone F)) := by
  dsimp [topologicalGroupToGrpType]
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  apply isLimitOfReflects (Grp.forget (Type u))
  change IsLimit ((forget TopCat.{u}).mapCone ((Grp.forget TopCat.{u}).mapCone (limit.cone F)))
  exact isLimitOfPreserves (forget TopCat.{u})
    (isLimitOfPreserves (Grp.forget TopCat.{u}) (limit.isLimit F))

/-- Lemma 5.30.3 (1): the canonical category `Grp TopCat` of topological groups has limits. -/
instance topologicalGroupCat_hasLimits : HasLimits (Grp TopCat.{u}) :=
  { has_limits_of_shape := fun J _ ↦ by
      let _ : Small.{u} J := inferInstance
      infer_instance }

/-- Lemma 5.30.3 (2): the forgetful functor from topological groups to `TopCat` preserves
limits. -/
instance topologicalGroupCat_forgetToTopCat_preservesLimits :
    PreservesLimits (Grp.forget TopCat.{u}) :=
  { preservesLimitsOfShape := fun {J} _ ↦ by
      simpa using (inferInstance : PreservesLimitsOfShape J (Grp.forget TopCat.{u})) }

/-- Lemma 5.30.3 (3): the forgetful functor to `GrpCat` preserves limits. -/
instance topologicalGroupCat_forgetToGrpCat_preservesLimits :
    PreservesLimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesLimitsOfShape := by
    intro J _
    let _ : Small.{u} J := inferInstance
    exact
      { preservesLimit := fun {F} ↦ by
          exact preservesLimit_of_preserves_limit_cone (limit.isLimit F) <| by
            let _ : (grpTypeEquivalenceGrp.{u}.functor).IsEquivalence := inferInstance
            simpa [topologicalGroupToGrpType] using
              (isLimitOfPreserves grpTypeEquivalenceGrp.functor
                (topologicalGroupToGrpType_mapConeIsLimit F)) }
