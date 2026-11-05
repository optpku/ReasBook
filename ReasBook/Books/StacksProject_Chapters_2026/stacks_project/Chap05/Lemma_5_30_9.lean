module

public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Combinatorics.Quiver.ReflQuiver

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

/- Domain-style sampling for topological rings:
- primary domain: category-theoretic colimits in `TopCommRingCat`, built from the canonical
  `CommRingCat` colimit and the lattice of ring topologies.
- sampled canonical declarations:
  `CommRingCat.Colimits.colimitCocone`,
  `CommRingCat.Colimits.colimitIsColimit`,
  `RingTopology.coinduced`,
  `continuous_induced_rng`,
  `preservesColimit_of_preserves_colimit_cocone`.
- best owner abstraction: the `CommRingCat` colimit cocone is the primitive algebraic data; the
  topological-ring structure on its cocone point is derived from the canonical `RingTopology`
  lattice by taking the infimum of the admissible ring topologies making all cocone maps
  continuous.

Layer triage:
- `source-facing`: Lemma 5.30.9, asserting colimits in `TopCommRingCat` and preservation by the
  forgetful functor to `CommRingCat`.
- `core/canonical`: `HasColimitsOfShape` / `HasColimitsOfSize` for `TopCommRingCat` and
  `PreservesColimitsOfShape` / `PreservesColimitsOfSize` for
  `forget₂ TopCommRingCat CommRingCat`.
- `bridge/view`: the infimum of the admissible ring topologies on the `CommRingCat` colimit.
-/

namespace TopCommRingCat

noncomputable section

variable {J : Type u} [Category.{u} J]

private abbrev underlyingDiagram (F : J ⥤ TopCommRingCat.{u}) :=
  F ⋙ forget₂ TopCommRingCat CommRingCat

private def admissibleRingTopologies {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : Set (RingTopology c.pt) :=
  { t | ∀ j,
      letI : TopologicalSpace ((underlyingDiagram F).obj j) :=
        TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)
      RingTopology.coinduced (c.ι.app j).hom ≤ t }

private def coinducedRingTopology {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : RingTopology c.pt :=
  sInf (admissibleRingTopologies c)

private def coinduced {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : TopCommRingCat.{u} :=
  let t := coinducedRingTopology c
  letI : TopologicalSpace c.pt := t.toTopologicalSpace
  letI : IsTopologicalRing c.pt := t.toIsTopologicalRing
  TopCommRingCat.of c.pt

private def toCoinduced {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) (j : J) : F.obj j ⟶ coinduced c :=
  ⟨(c.ι.app j).hom, by
    letI : TopologicalSpace ((underlyingDiagram F).obj j) :=
      TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)
    change @Continuous (F.obj j) c.pt (F.obj j).isTopologicalSpace
      (coinducedRingTopology c).toTopologicalSpace (c.ι.app j).hom
    refine continuous_sInf_rng.2 fun _ ht ↦ ?_
    rcases ht with ⟨t, ht, rfl⟩
    exact continuous_iff_coinduced_le.2 <|
      (continuous_iff_coinduced_le.1 (RingTopology.coinduced_continuous (c.ι.app j).hom)).trans
        (ht j)⟩

private def ofCocone {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : Cocone F where
  pt := coinduced c
  ι :=
    { app := toCoinduced c
      naturality := by
        intro i j f
        apply Subtype.ext
        simpa using congrArg CommRingCat.Hom.hom (c.ι.naturality f) }

private def inducedRingTopology {F : J ⥤ TopCommRingCat.{u}}
    {c : Cocone (underlyingDiagram F)} {R : TopCommRingCat.{u}} (h : c.pt →+* R) :
    RingTopology c.pt :=
  let t : TopologicalSpace c.pt := TopologicalSpace.induced h inferInstance
  letI : TopologicalSpace c.pt := t
  letI : IsTopologicalSemiring c.pt :=
    { toContinuousAdd := continuousAdd_induced h, toContinuousMul := continuousMul_induced h }
  RingTopology.mk t (IsTopologicalSemiring.toIsTopologicalRing inferInstance)

private theorem inducedRingTopology_mem {F : J ⥤ TopCommRingCat.{u}}
    {c : Cocone (underlyingDiagram F)} {R : TopCommRingCat.{u}} (h : c.pt →+* R)
    (hh : ∀ j, Continuous (fun x : F.obj j ↦ h ((c.ι.app j).hom x))) :
    inducedRingTopology h ∈ admissibleRingTopologies c := by
  intro j
  letI : TopologicalSpace ((underlyingDiagram F).obj j) :=
    TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)
  change RingTopology.coinduced (c.ι.app j).hom ≤ inducedRingTopology h
  change sInf { t : RingTopology c.pt |
      TopologicalSpace.coinduced (c.ι.app j).hom (F.obj j).isTopologicalSpace ≤
        t.toTopologicalSpace } ≤ inducedRingTopology h
  refine sInf_le ?_
  change TopologicalSpace.coinduced (c.ι.app j).hom (F.obj j).isTopologicalSpace ≤
    TopologicalSpace.induced h inferInstance
  exact continuous_iff_coinduced_le.1 (continuous_induced_rng.2 (hh j))

private def isColimit {F : J ⥤ TopCommRingCat.{u}} {c : Cocone (underlyingDiagram F)}
    (hc : IsColimit c) : IsColimit (ofCocone c) :=
  IsColimit.ofFaithful (forget₂ TopCommRingCat CommRingCat)
    (by
      simpa [ofCocone, toCoinduced, coinduced] using hc)
    (fun s ↦
      let h := hc.desc ((forget₂ TopCommRingCat CommRingCat).mapCocone s)
      ⟨h.hom, by
        rw [continuous_iff_le_induced]
        exact sInf_le ⟨inducedRingTopology h.hom, inducedRingTopology_mem h.hom <| by
          intro j
          change Continuous (show F.obj j → s.pt from (c.ι.app j ≫ h).hom)
          rw [hc.fac ((forget₂ TopCommRingCat CommRingCat).mapCocone s) j]
          exact (s.ι.app j).2, rfl⟩⟩)
    fun _ ↦ rfl

private instance hasColimit (F : J ⥤ TopCommRingCat.{u}) : HasColimit F :=
  ⟨⟨ofCocone (colimit.cocone (underlyingDiagram F)), isColimit (colimit.isColimit _)⟩⟩

/-- `TopCommRingCat` has colimits of all small shapes. -/
instance hasColimitsOfShape (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J TopCommRingCat.{u} where
  has_colimit F := by infer_instance

/-- Lemma 5.30.9 (1): the category of topological rings has all colimits. -/
instance hasColimits : HasColimits TopCommRingCat.{u} where
  has_colimits_of_shape K _ := by infer_instance

instance forgetToCommRingCat_preservesColimitsOfShape (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesColimit := fun {F} ↦
    preservesColimit_of_preserves_colimit_cocone
      (isColimit (colimit.isColimit (underlyingDiagram F))) <| by
        simpa [ofCocone, toCoinduced, coinduced] using (colimit.isColimit (underlyingDiagram F))

/-- Lemma 5.30.9 (2): the forgetful functor from topological rings to commutative rings preserves
colimits. -/
instance forgetToCommRingCat_preservesColimits :
    PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesColimitsOfShape {J} := by infer_instance

end

end TopCommRingCat

/-- Summary theorem collecting the colimit existence and preservation instances for
`TopCommRingCat`. -/
theorem topologicalRingCat_has_colimits_and_forget_to_commRing_preserves_colimits :
    HasColimits TopCommRingCat.{u} ∧
      PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) :=
  ⟨inferInstance, inferInstance⟩
