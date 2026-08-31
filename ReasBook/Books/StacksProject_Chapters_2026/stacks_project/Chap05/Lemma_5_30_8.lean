module

public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Category.TopCat.Limits.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace

-- In the Stacks Project convention, a “ring” is commutative. The canonical bundled mathlib
-- owner abstraction for topological rings is therefore `TopCommRingCat`.

/- Domain-style sampling for topological rings:
- primary domain: category-theoretic limits in `TopCommRingCat` and preservation by the canonical
  forgetful functors to `TopCat` and `CommRingCat`.
- sampled canonical declarations:
  `TopCommRingCat`,
  `CommRingCat.limitCone`,
  `CommRingCat.limitConeIsLimit`,
  `TopCat.isLimitConeOfForget`,
  `TopModuleCat.ofCone`,
  `TopModuleCat.isLimit`.
- best owner abstraction: `TopCommRingCat` for the source-facing result, with the underlying
  `CommRingCat` limit cone as primitive data and the induced topology as derived owner data.

Primitive-vs-derived split:
- primitive data: the underlying `CommRingCat` limit cone and the induced topology on its cone
  point;
- derived API: the resulting `HasLimitsOfSize` / `HasLimits` and `PreservesLimitsOfSize` /
  `PreservesLimits` instances for `TopCommRingCat` and its forgetful functors.

Layer triage:
- `source-facing`: Lemma 5.30.8, asserting existence of limits in `TopCommRingCat` and
  preservation by the two forgetful functors.
- `core/canonical`: the canonical owner instances `HasLimits` / `HasLimitsOfSize` for
  `TopCommRingCat` and `PreservesLimits` / `PreservesLimitsOfSize` for the forgetful functors.
- `bridge/view`: the induced topology on the underlying `CommRingCat` limit cone and its
  comparison with the corresponding `TopCat` limit cone.
-/

namespace TopCommRingCat

noncomputable section

universe v u w

variable {J : Type v} [Category.{w} J]

private abbrev underlyingDiagram (F : J ⥤ TopCommRingCat.{u}) :=
  F ⋙ forget₂ TopCommRingCat CommRingCat

private instance objTopologicalSpace (F : J ⥤ TopCommRingCat.{u}) (j : J) :
    TopologicalSpace ((underlyingDiagram F).obj j) :=
  TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)

private def induced {F : J ⥤ TopCommRingCat.{u}} (c : Cone (underlyingDiagram F)) :
    TopCommRingCat.{u} :=
  letI : TopologicalSpace c.pt := ⨅ j,
    TopologicalSpace.induced (show c.pt → F.obj j from (c.π.app j).hom) inferInstance
  letI : ContinuousAdd c.pt := continuousAdd_iInf fun j ↦
    continuousAdd_induced (show c.pt →+* F.obj j from (c.π.app j).hom)
  letI : ContinuousMul c.pt := continuousMul_iInf fun j ↦
    continuousMul_induced (show c.pt →+* F.obj j from (c.π.app j).hom)
  letI : IsTopologicalSemiring c.pt :=
    { toContinuousAdd := inferInstance, toContinuousMul := inferInstance }
  letI : IsTopologicalRing c.pt := IsTopologicalSemiring.toIsTopologicalRing inferInstance
  TopCommRingCat.of c.pt

private def fromInduced {F : J ⥤ TopCommRingCat.{u}} (c : Cone (underlyingDiagram F)) (j : J) :
    induced c ⟶ F.obj j :=
  ⟨show induced c →+* F.obj j from (c.π.app j).hom,
    continuous_iff_le_induced.mpr (iInf_le _ j)⟩

private def ofCone {F : J ⥤ TopCommRingCat.{u}} (c : Cone (underlyingDiagram F)) : Cone F where
  pt := induced c
  π :=
    { app := fromInduced c
      naturality := by
        intro i j f
        apply Subtype.ext
        change
          CommRingCat.Hom.hom (((Functor.const J).obj c.pt).map f ≫ c.π.app j) =
            CommRingCat.Hom.hom (c.π.app i ≫ (underlyingDiagram F).map f)
        simpa using congrArg CommRingCat.Hom.hom (c.π.naturality f) }

private def isLimit {F : J ⥤ TopCommRingCat.{u}} {c : Cone (underlyingDiagram F)}
    (hc : IsLimit c) : IsLimit (ofCone c) :=
  IsLimit.ofFaithful (forget₂ TopCommRingCat CommRingCat)
    (by
      simpa [ofCone, fromInduced] using hc)
    (fun s ↦
      ⟨show s.pt →+* induced c from (hc.lift ((forget₂ TopCommRingCat CommRingCat).mapCone s)).hom,
        by
          rw [continuous_iff_coinduced_le]
          refine le_iInf fun j ↦ ?_
          exact (coinduced_le_iff_le_induced).2 <| by
            rw [← continuous_iff_le_induced]
            refine (continuous_induced_rng).2 ?_
            let g : s.pt →+* F.obj j :=
              ((hc.lift ((forget₂ TopCommRingCat CommRingCat).mapCone s)) ≫ c.π.app j).hom
            change Continuous g
            have hg : g = (s.π.app j).1 := by
              ext x
              exact congrArg (fun f ↦ f x)
                (congrArg CommRingCat.Hom.hom
                  (hc.fac ((forget₂ TopCommRingCat CommRingCat).mapCone s) j))
            simpa [hg] using (s.π.app j).2⟩)
    fun _ ↦ rfl

private instance hasLimit (F : J ⥤ TopCommRingCat.{u}) [HasLimit (underlyingDiagram F)] :
    HasLimit F :=
  ⟨_, isLimit (limit.isLimit (underlyingDiagram F))⟩

/-- `TopCommRingCat` has limits of all small shapes. -/
instance hasLimitsOfShape (J : Type v) [Category.{w} J] [Small.{u} J] :
    HasLimitsOfShape J TopCommRingCat.{u} where
  has_limit F := by infer_instance

/-- `TopCommRingCat` has all small limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} TopCommRingCat.{u} where
  has_limits_of_shape K _ := by
    let _ : Small.{u} K := inferInstance
    infer_instance

/-- Lemma 5.30.8 (1): the category of topological rings has all small limits. -/
instance hasLimits : HasLimits TopCommRingCat.{u} where
  has_limits_of_shape K _ := by
    let _ : Small.{u} K := inferInstance
    infer_instance

/-- Auxiliary preservation of a fixed limit cone by the forgetful functor to `TopCat`. -/
private instance forgetToTopCat_preservesLimit {F : J ⥤ TopCommRingCat.{u}}
    [HasLimit (underlyingDiagram F)] [PreservesLimit (underlyingDiagram F) (forget CommRingCat)] :
    PreservesLimit F (forget₂ TopCommRingCat.{u} TopCat.{u}) :=
  preservesLimit_of_preserves_limit_cone (isLimit (limit.isLimit (underlyingDiagram F))) <| by
    let cTop : Cone ((F ⋙ forget₂ TopCommRingCat TopCat) ⋙ forget TopCat) :=
      (forget CommRingCat).mapCone (limit.cone (underlyingDiagram F))
    have hcTop : IsLimit cTop := by
      simpa [cTop] using
        (isLimitOfPreserves (forget CommRingCat) (limit.isLimit (underlyingDiagram F)))
    simpa [ofCone, fromInduced, induced, cTop] using TopCat.isLimitConeOfForget cTop hcTop

instance forgetToTopCat_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ TopCommRingCat.{u} TopCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    exact { preservesLimit := fun {F} ↦ inferInstance }

/-- Lemma 5.30.8 (2): the forgetful functor from topological rings to topological spaces preserves
all small limits. -/
instance forgetToTopCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    infer_instance

private instance forgetToCommRingCat_preservesLimit {F : J ⥤ TopCommRingCat.{u}}
    [HasLimit (underlyingDiagram F)] :
    PreservesLimit F (forget₂ TopCommRingCat.{u} CommRingCat.{u}) :=
  preservesLimit_of_preserves_limit_cone (isLimit (limit.isLimit (underlyingDiagram F))) <| by
    simpa [ofCone, fromInduced, induced] using (limit.isLimit (underlyingDiagram F))

instance forgetToCommRingCat_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    exact { preservesLimit := fun {F} ↦ inferInstance }

/-- Lemma 5.30.8 (3): the forgetful functor from topological rings to commutative rings preserves
all small limits. -/
instance forgetToCommRingCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    infer_instance

end

end TopCommRingCat
