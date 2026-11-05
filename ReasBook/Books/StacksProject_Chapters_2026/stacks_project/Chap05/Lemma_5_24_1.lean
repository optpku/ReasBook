module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.Topology.Connected.Separation
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v w

noncomputable section

/-
Domain-style sampling for Lemma 5.24.1:
- inspected owner declarations:
  `WithConstructibleTopology`,
  `constructibleTopology_compactSpace_of_spectralSpace`,
  `constructibleTopology_t2Space_of_spectralSpace`,
  `compactSpace_limit_of_compactSpace_t2Space`,
  `Types.limitEquivSections`
- primary domain: inverse limits of spectral spaces and constructible-topology closed subspaces
- `source-facing`: the restricted inverse system obtained from a diagram `F` and stable subsets
  `Z i`
- `core/canonical`: patch-topology compactness is owned by the constructible-topology package, and
  limit compactness is owned by the compact-Hausdorff limit theorem
- `bridge/view`: a second restricted diagram built from the same subsets with the patch subspace
  topologies, together with the comparison map from that compact limit to the original limit

Primitive data is only the ambient diagram `F`, the subsets `Z`, and the stability proofs. The
patch-subspace diagram is the faithful translation of the source proof; compactness is then
transported back to the original inverse limit through the identity-on-points comparison map.
-/

section

variable {I : Type v} [Category.{w} I]
variable {F : I ⥤ TopCat.{max u v}}
variable (Z : ∀ i, Set (F.obj i))
variable (hZ : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))

namespace CategoryTheory.Functor

/-- The morphism on subspaces induced by a map of the ambient diagram that preserves the chosen
subsets. -/
def stableSubsetDiagramMap {i j : I} (a : i ⟶ j) : TopCat.of (Z i) ⟶ TopCat.of (Z j) :=
  TopCat.ofHom
    ⟨Set.MapsTo.restrict (F.map a) (Z i) (Z j) (hZ a),
      Continuous.restrict (hZ a) (F.map a).hom.continuous⟩

-- This is just the restricted identity map on the subtype `Z i`.
/-- Restricting the identity morphism of the ambient diagram gives the identity on the stable
subset. -/
theorem stableSubsetDiagramMap_id (i : I) :
    stableSubsetDiagramMap Z hZ (𝟙 i) = 𝟙 (TopCat.of (Z i)) := by
  apply ConcreteCategory.ext
  ext x
  simp [stableSubsetDiagramMap]

-- Both sides act by the same composite function on points of `Z i`.
/-- Restricting a composite morphism agrees with composing the restricted morphisms on the stable
subspaces. -/
theorem stableSubsetDiagramMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    stableSubsetDiagramMap Z hZ (a ≫ b) =
      stableSubsetDiagramMap Z hZ a ≫
        stableSubsetDiagramMap Z hZ b := by
  apply ConcreteCategory.ext
  ext x
  simp [stableSubsetDiagramMap]

/-- The diagram of subspaces cut out by a family of subsets stable under the transition maps. -/
def stableSubsetDiagram : I ⥤ TopCat.{max u v} where
  obj i := TopCat.of (Z i)
  map a := stableSubsetDiagramMap Z hZ a
  map_id i := stableSubsetDiagramMap_id Z hZ i
  map_comp a b := stableSubsetDiagramMap_comp Z hZ a b

end CategoryTheory.Functor

end

section

variable {I : Type v} [Category.{w} I]
variable (F : I ⥤ TopCat.{max u v})
variable [∀ i, SpectralSpace ↥(F.obj i)]

/-- Helper for Lemma 5.24.1: every open subset of a spectral space is open for the constructible
topology. -/
theorem isOpen_constructibleTopology_of_isOpen_spectralSpaceDiagram {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] {s : Set X} (hs : IsOpen s) : IsOpen[constructibleTopology X] s := by
  -- The compact-open basis of a spectral space consists of constructible opens.
  refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hs
  · intro U hU
    exact hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  · intro S hS
    let _ : TopologicalSpace X := constructibleTopology X
    exact isOpen_sUnion fun U hU ↦ hS U hU

section ConstructibleDiagram

/-- Helper for Lemma 5.24.1: the same subset `Z i`, but endowed with the subspace topology coming
from the constructible topology on `F.obj i`. -/
abbrev PatchSubtype (Z : ∀ i, Set (F.obj i)) (i : I) : Type (max u v) :=
  { x : WithConstructibleTopology (F.obj i) | (x : F.obj i) ∈ Z i }

/-- Helper for Lemma 5.24.1: the restricted transition map is continuous for the patch subspace
topologies. -/
theorem patchSubsetDiagramMap_continuous
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    Continuous
      (fun x : PatchSubtype (F := F) Z i ↦
        (⟨F.map a x.1, hZ_maps a x.2⟩ : PatchSubtype (F := F) Z j)) := by
  -- The ambient spectral map is continuous for the constructible topologies on the wrapper types.
  have hAmbient :
      @Continuous (WithConstructibleTopology (F.obj i)) (WithConstructibleTopology (F.obj j))
        _ _
        (fun x ↦ ((F.map a : F.obj i → F.obj j) x : F.obj j)) := by
    simpa [WithConstructibleTopology] using (hF a).continuous_constructibleTopology
  -- Restrict that continuous ambient map to the chosen stable subsets.
  exact (hAmbient.comp continuous_subtype_val).subtype_mk fun x ↦ hZ_maps a x.2

/-- Helper for Lemma 5.24.1: the transition map on the patch subspace diagram. -/
def patchSubsetDiagramMap
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    TopCat.of (PatchSubtype (F := F) Z i) ⟶
      TopCat.of (PatchSubtype (F := F) Z j) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨F.map a x.1, hZ_maps a x.2⟩,
      patchSubsetDiagramMap_continuous (F := F) Z hF hZ_maps a⟩

/-- Helper for Lemma 5.24.1: restricting the identity map on the patch subspaces gives the
identity morphism. -/
theorem patchSubsetDiagramMap_id
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (i : I) :
    patchSubsetDiagramMap (F := F) Z hF hZ_maps (𝟙 i) =
      𝟙 (TopCat.of (PatchSubtype (F := F) Z i)) := by
  -- Both morphisms are the identity on the underlying subtype points.
  apply ConcreteCategory.ext
  ext x
  change (F.map (𝟙 i)) x.1 = x.1
  simpa using congrArg (fun f : F.obj i ⟶ F.obj i ↦ f x.1) (F.map_id i)

/-- Helper for Lemma 5.24.1: the patch restricted maps compose exactly as the ambient diagram
maps do. -/
theorem patchSubsetDiagramMap_comp
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    patchSubsetDiagramMap (F := F) Z hF hZ_maps (a ≫ b) =
      patchSubsetDiagramMap (F := F) Z hF hZ_maps a ≫
        patchSubsetDiagramMap (F := F) Z hF hZ_maps b := by
  -- Both sides evaluate to the same composite restricted map on each point.
  apply ConcreteCategory.ext
  ext x
  change (F.map (a ≫ b)) x.1 = (F.map b) ((F.map a) x.1)
  simpa using congrArg (fun f : F.obj i ⟶ F.obj k ↦ f x.1) (F.map_comp a b)

/-- Helper for Lemma 5.24.1: the inverse system obtained from the stable subsets equipped with the
subspace topologies coming from the constructible topologies on the ambient spaces. -/
def constructibleClosedStableSubsetDiagram
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    I ⥤ TopCat.{max u v} where
  obj i := TopCat.of (PatchSubtype (F := F) Z i)
  map a := patchSubsetDiagramMap (F := F) Z hF hZ_maps a
  map_id i := patchSubsetDiagramMap_id (F := F) Z hF hZ_maps i
  map_comp a b := patchSubsetDiagramMap_comp (F := F) Z hF hZ_maps a b

/-- Helper for Lemma 5.24.1: each patch subspace `Z i` is compact because it is closed in the
compact constructible topology on `F.obj i`. -/
theorem patchSubtype_compactSpace
    (Z : ∀ i, Set (F.obj i))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (i : I) : CompactSpace (PatchSubtype (F := F) Z i) := by
  -- The ambient constructible-topology space is compact by spectrality.
  have hPatchCompact : @CompactSpace (F.obj i) (constructibleTopology (F.obj i)) :=
    constructibleTopology_compactSpace_of_spectralSpace
  let _ : TopologicalSpace (F.obj i) := constructibleTopology (F.obj i)
  let _ : CompactSpace (F.obj i) := hPatchCompact
  -- A closed subset of that compact patch space is compact.
  have hClosed : IsClosed (Z i) := by
    simpa using hZ_closed i
  have hCompact : IsCompact (Z i) := hClosed.isCompact
  -- Rewrite the subtype in the owner topology back to the wrapper notation used here.
  simpa [PatchSubtype, WithConstructibleTopology] using
    (isCompact_iff_compactSpace.mp hCompact : CompactSpace (Z i))

/-- Helper for Lemma 5.24.1: each patch subspace `Z i` is Hausdorff because it is a subspace of
the Hausdorff constructible topology on `F.obj i`. -/
theorem patchSubtype_t2Space
    (Z : ∀ i, Set (F.obj i))
    (i : I) : T2Space (PatchSubtype (F := F) Z i) := by
  -- A subtype of a Hausdorff space is Hausdorff, so it is enough to switch the ambient topology
  -- to the constructible topology on `F.obj i`.
  letI : T2Space (WithConstructibleTopology (F.obj i)) := inferInstance
  simpa [PatchSubtype, WithConstructibleTopology] using
    (inferInstance : T2Space { x : WithConstructibleTopology (F.obj i) | (x : F.obj i) ∈ Z i })

/-- Helper for Lemma 5.24.1: the identity on `Z i` is continuous from the patch subspace topology
to the original subspace topology. -/
theorem patchToOriginalComponent_continuous
    (Z : ∀ i, Set (F.obj i)) (i : I) :
    Continuous
      (fun x : PatchSubtype (F := F) Z i ↦
        ((⟨x.1, x.2⟩ : Z i) : Z i)) := by
  -- Every original open is constructible-open, so the identity from the patch topology is
  -- continuous to the original topology.
  have hContToOriginal :
      @Continuous (WithConstructibleTopology (F.obj i)) (F.obj i) _ _
        (fun x ↦ (x : F.obj i)) := by
    simpa [WithConstructibleTopology] using
      (continuous_id_of_le
        (fun U hU ↦ isOpen_constructibleTopology_of_isOpen_spectralSpaceDiagram (X := F.obj i) hU) :
          @Continuous (F.obj i) (F.obj i) (constructibleTopology (F.obj i)) _ id)
  -- Restrict that identity map to the stable subset.
  exact (hContToOriginal.comp continuous_subtype_val).subtype_mk fun x ↦ x.2

/-- Helper for Lemma 5.24.1: the stagewise identity maps from the patch subspace diagram to the
original subspace diagram. -/
def patchToOriginalComponent
    (Z : ∀ i, Set (F.obj i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (i : I) :
    TopCat.of (PatchSubtype (F := F) Z i) ⟶ (F.stableSubsetDiagram Z hZ_maps).obj i :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, x.2⟩,
      patchToOriginalComponent_continuous (F := F) Z i⟩

/-- Helper for Lemma 5.24.1: the stagewise identity maps commute with the restricted transition
maps after forgetting the auxiliary constructible topologies. -/
theorem patchToOriginalComponent_naturality
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    patchToOriginalComponent (F := F) Z hZ_maps i ≫
        (F.stableSubsetDiagram Z hZ_maps).map a =
      patchSubsetDiagramMap (F := F) Z hF hZ_maps a ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
  -- Both sides are the same restricted ambient map, viewed with different source topologies.
  apply ConcreteCategory.ext
  ext x
  rfl

/-- Helper for Lemma 5.24.1: the stagewise identity maps from the patch limit point satisfy the
cone compatibility relations for the original stable-subset diagram. -/
theorem patchLimitConeToOriginalCone_naturality
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    ((TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        patchToOriginalComponent (F := F) Z hZ_maps i) ≫
        (F.stableSubsetDiagram Z hZ_maps).map a =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app j ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
  -- First move the stagewise identity map across the restricted transition map.
  calc
    ((TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        patchToOriginalComponent (F := F) Z hZ_maps i) ≫
        (F.stableSubsetDiagram Z hZ_maps).map a
        =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        (patchToOriginalComponent (F := F) Z hZ_maps i ≫
          (F.stableSubsetDiagram Z hZ_maps).map a) := by
          rw [Category.assoc]
    _ =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        (patchSubsetDiagramMap (F := F) Z hF hZ_maps a ≫
          patchToOriginalComponent (F := F) Z hZ_maps j) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦
                (TopCat.limitCone
                    (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫ f)
              (patchToOriginalComponent_naturality (F := F) Z hF hZ_maps a)
    _ =
      ((TopCat.limitCone
            (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
          patchSubsetDiagramMap (F := F) Z hF hZ_maps a) ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
          rw [← Category.assoc]
    _ =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app j ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ f ≫ patchToOriginalComponent (F := F) Z hZ_maps j)
              ((TopCat.limitCone
                (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).w a)

/-- Helper for Lemma 5.24.1: the stagewise identity maps assemble to a cone from the explicit
patch limit cone point to the original stable-subset diagram. -/
def patchLimitConeToOriginalCone
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    Cone (F.stableSubsetDiagram Z hZ_maps) where
  pt := (TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt
  π :=
    { app := fun i ↦
        (TopCat.limitCone
            (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
          patchToOriginalComponent (F := F) Z hZ_maps i
      naturality := fun {i j} a ↦
        (patchLimitConeToOriginalCone_naturality (F := F) Z hF hZ_maps a).symm }

/-- Helper for Lemma 5.24.1: a compatible family in the original stable-subset diagram is also a
compatible family in the patch diagram, since only the topology changes. -/
theorem original_limitCone_point_to_patch_limitCone_point_compatible
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (x : (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :
    ∀ {i j : I} (a : i ⟶ j),
      patchSubsetDiagramMap (F := F) Z hF hZ_maps a ⟨(x.1 i).1, (x.1 i).2⟩ =
        ⟨(x.1 j).1, (x.1 j).2⟩ := by
  -- The patch and original diagrams have the same underlying pointwise compatibility relation.
  intro i j a
  apply Subtype.ext
  simpa [patchSubsetDiagramMap, CategoryTheory.Functor.stableSubsetDiagram,
    CategoryTheory.Functor.stableSubsetDiagramMap] using congrArg Subtype.val (x.2 a)

/-- Helper for Lemma 5.24.1: a compatible family in the original stable-subset diagram is also a
compatible family in the patch diagram, since only the topology changes. -/
def original_limitCone_point_to_patch_limitCone_point
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (x : (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :
    (TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt :=
  ⟨fun i ↦ ⟨(x.1 i).1, (x.1 i).2⟩,
    original_limitCone_point_to_patch_limitCone_point_compatible
      (F := F) Z hF hZ_maps x⟩

/-- Helper for Lemma 5.24.1: the stagewise identity maps assemble to a morphism from the explicit
patch limit cone point to the explicit original limit cone point. -/
def patchLimitConeToOriginalLimitCone
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    (TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt ⟶
      (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt :=
  (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps)).lift
    (patchLimitConeToOriginalCone (F := F) Z hF hZ_maps)

/-- Helper for Lemma 5.24.1: the map between the explicit limit cone points evaluates
coordinatewise by the stagewise identity maps. -/
theorem patchLimitConeToOriginalLimitCone_π
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (i : I) :
    patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps ≫
        (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).π.app i =
      (TopCat.limitCone
        (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        patchToOriginalComponent (F := F) Z hZ_maps i := by
  -- This is exactly the defining `fac` equation of the lifted cone morphism.
  simpa [patchLimitConeToOriginalLimitCone, patchLimitConeToOriginalCone] using
    (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps)).fac
      (patchLimitConeToOriginalCone (F := F) Z hF hZ_maps) i

/-- Helper for Lemma 5.24.1: the comparison map from the patch limit to the original limit is
surjective because both limits classify the same compatible families of points. -/
theorem patchLimitConeToOriginalLimitCone_surjective
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    Function.Surjective
      (patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps) := by
  -- Use the explicit pointwise reinterpretation of a compatible family as the right inverse.
  intro x
  refine ⟨original_limitCone_point_to_patch_limitCone_point (F := F) Z hF hZ_maps x, ?_⟩
  apply Subtype.ext
  funext i
  have hπ :=
    congrArg
      (fun f ↦ f (original_limitCone_point_to_patch_limitCone_point (F := F) Z hF hZ_maps x))
      (patchLimitConeToOriginalLimitCone_π (F := F) Z hF hZ_maps i)
  simpa [patchToOriginalComponent, original_limitCone_point_to_patch_limitCone_point,
    Category.assoc] using hπ

/-- Helper for Lemma 5.24.1: for `Z i = univ`, the stable-subset diagram is naturally isomorphic
to the original diagram. -/
theorem stableSubsetDiagram_mapsTo_univ_subset :
    ∀ ⦃i j : I⦄ (a : i ⟶ j),
      Set.MapsTo (F.map a)
        ((fun i ↦ (Set.univ : Set (F.obj i))) i)
        ((fun j ↦ (Set.univ : Set (F.obj j))) j) := by
  intro i j a x hx
  simp

/-- Helper for Lemma 5.24.1: the stagewise identifications for the universal-subset diagram are
natural in the diagram index. -/
theorem stable_subset_diagram_univ_iso_naturality
    {i j : I} (a : i ⟶ j) :
    (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
          (stableSubsetDiagram_mapsTo_univ_subset (F := F))).map a ≫
        (TopCat.isoOfHomeo (Homeomorph.Set.univ (F.obj j))).hom =
      (TopCat.isoOfHomeo (Homeomorph.Set.univ (F.obj i))).hom ≫
        F.map a := by
  -- For the universal subset, every restricted transition map is just the original map on points.
  apply ConcreteCategory.ext
  ext x
  rfl

/-- Helper for Lemma 5.24.1: for `Z i = univ`, the stable-subset diagram is naturally isomorphic
to the original diagram. -/
def stable_subset_diagram_univ_iso :
    F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
        (stableSubsetDiagram_mapsTo_univ_subset (F := F)) ≅
      F :=
  NatIso.ofComponents (fun i ↦ TopCat.isoOfHomeo (Homeomorph.Set.univ (F.obj i)))
    (fun {i j} a ↦ stable_subset_diagram_univ_iso_naturality (F := F) a)

end ConstructibleDiagram

section

attribute [local instance] uliftCategory

/-- Helper for Lemma 5.24.1: Lemma 5.14.5 extends to arbitrary index-universe categories after
lifting the codomain to `CompHaus` without changing the index category. -/
theorem compactSpace_limit_of_compactSpace_t2Space_large
    {J : Type v} [Category.{w} J] (G : J ⥤ TopCat.{max u v})
    [∀ j, CompactSpace ↥(G.obj j)] [∀ j, T2Space ↥(G.obj j)] :
    CompactSpace ↥(limit G) := by
  -- Route correction: enlarge only the codomain universe, using `uliftFunctor` so the index
  -- category stays fixed while the compact-Hausdorff owner can supply a limit of this shape.
  let H : J ⥤ TopCat.{max u v w} := G ⋙ TopCat.uliftFunctor.{w, max u v}
  haveI : ∀ j, CompactSpace ↥(H.obj j) := by
    intro j
    change CompactSpace (ULift.{w} (G.obj j))
    infer_instance
  haveI : ∀ j, T2Space ↥(H.obj j) := by
    intro j
    change T2Space (ULift.{w} (G.obj j))
    infer_instance
  -- Transfer `CompHaus` limits from a same-universe shape equivalent to `J`.
  haveI : HasLimitsOfShape J CompHaus.{max u v w} := by
    haveI :
        HasLimitsOfShape (ULiftHom.{max u v w} (ULift.{max u v w} J))
          CompHaus.{max u v w} := by
      let _ : HasLimits CompHaus.{max u v w} := inferInstance
      exact HasLimits.has_limits_of_shape
        (J := ULiftHom.{max u v w} (ULift.{max u v w} J))
        (C := CompHaus.{max u v w})
    exact hasLimitsOfShape_of_equivalence
      (ULiftHomULiftCategory.equiv.{max u v w, max u v w, w, v} J).symm
  let Gc : J ⥤ CompHaus.{max u v w} := {
    obj := fun j ↦ CompHaus.of ↥(H.obj j)
    map := fun f ↦ CompHausLike.ofHom (fun _ ↦ True) (H.map f).hom
    map_id := by
      intro j
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (H.map_id j)
    map_comp := by
      intro i j k f g
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (H.map_comp f g) }
  -- The forgotten `CompHaus` limit computes the `TopCat` limit of the lifted diagram `H`.
  have hCompactLifted : CompactSpace ↥(limit H) := by
    let hGc : IsLimit (compHausToTop.mapCone (limit.cone Gc)) := by
      simpa using isLimitOfPreserves compHausToTop (limit.isLimit Gc)
    have hCompactCone : CompactSpace ↥(compHausToTop.mapCone (limit.cone Gc)).pt := by
      change CompactSpace ↥(limit Gc)
      infer_instance
    letI : CompactSpace ↥(compHausToTop.mapCone (limit.cone Gc)).pt := hCompactCone
    simpa [H, Gc] using
      (TopCat.homeoOfIso
        (IsLimit.conePointUniqueUpToIso hGc (limit.isLimit (Gc ⋙ compHausToTop)))).compactSpace
  letI : CompactSpace ↥(limit H) := hCompactLifted
  -- Since `uliftFunctor` preserves limits, compactness descends from `limit H` to the lifted
  -- copy of `limit G`, and then across the explicit `ULift` homeomorphism back to `limit G`.
  have hCompactUliftedLimit :
      CompactSpace ↥(TopCat.uliftFunctor.{w, max u v}.obj (limit G)) := by
    simpa [H] using
      (TopCat.homeoOfIso
        (preservesLimitIso (TopCat.uliftFunctor.{w, max u v}) G)).symm.compactSpace
  letI : CompactSpace ↥(TopCat.uliftFunctor.{w, max u v}.obj (limit G)) :=
    hCompactUliftedLimit
  simpa using (TopCat.uliftFunctorObjHomeo.{w, max u v} (limit G)).symm.compactSpace

end

/-- Helper for Lemma 5.24.1: the explicit patch-topology limit cone point is compact because it
is homeomorphic to the limit of a diagram of compact Hausdorff patch subspaces. -/
theorem patch_limitCone_compactSpace
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace
      ↥((TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt) := by
  haveI : ∀ i,
      CompactSpace
        ↥((constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps).obj i) := by
    -- Each stage is a closed subspace of the compact constructible topology on `F.obj i`.
    intro i
    simpa [constructibleClosedStableSubsetDiagram] using
      patchSubtype_compactSpace (F := F) Z hZ_closed i
  haveI : ∀ i,
      T2Space ↥((constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps).obj i) := by
    -- The constructible topology is Hausdorff, and subspaces preserve Hausdorffness.
    intro i
    simpa [constructibleClosedStableSubsetDiagram] using patchSubtype_t2Space (F := F) Z i
  haveI :
      CompactSpace
        ↥(limit (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)) :=
    compactSpace_limit_of_compactSpace_t2Space_large
      (G := constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)
  -- The explicit `TopCat.limitCone` point is the same limit space up to the canonical isomorphism.
  let e :=
    (TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso
        (TopCat.limitConeIsLimit
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps))
        (limit.isLimit
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)))).symm
  letI :
      CompactSpace
        ↥((limit.cone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt) := by
    change CompactSpace ↥(limit (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps))
    infer_instance
  exact e.compactSpace

/-- Helper for Lemma 5.24.1: the explicit original limit cone point is compact as the continuous
surjective image of the compact patch-topology limit cone point. -/
theorem original_limitCone_compactSpace_of_patch_surjective
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) := by
  let f := patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps
  letI :
      CompactSpace
        ↥((TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt) :=
    patch_limitCone_compactSpace (F := F) Z hF hZ_closed hZ_maps
  have hCompactUniv :
      IsCompact (Set.univ : Set ((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt)) := by
    -- The image of the compact patch limit is all of the original limit because the comparison
    -- map is surjective on the underlying compatible families.
    simpa [f, Set.image_univ,
      Set.range_eq_univ.2 (patchLimitConeToOriginalLimitCone_surjective (F := F) Z hF hZ_maps)] using
      (isCompact_univ.image
        (patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps).hom.continuous)
  letI :
      CompactSpace
        (Set.univ : Set ((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt)) :=
    isCompact_iff_compactSpace.mp hCompactUniv
  -- Passing from the compact subtype `univ` back to the ambient space is just the universal-set
  -- homeomorphism.
  simpa using
    (Homeomorph.Set.univ
      ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt)).compactSpace

-- Proof sketch: endow each `F.obj i` with its constructible topology, restrict to the closed
-- subsets `Z i`, and apply the compact-Hausdorff limit theorem to that patch-topology diagram.
-- The resulting limit maps continuously and surjectively onto the original inverse limit because
-- both limits classify the same compatible families of points.
/-- Lemma 5.24.1: for a diagram of spectral spaces with spectral transition maps, any inverse limit
of subsets that are closed in the constructible topology and stable under the transition maps is
quasi-compact. -/
theorem compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace ↥(limit (F.stableSubsetDiagram Z hZ_maps)) := by
  -- Route correction: the only missing step was the large-universe compact-Hausdorff limit
  -- wrapper. With that in place, the source proof now runs exactly through the patch diagram.
  have hCompactOriginalCone :
      CompactSpace ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :=
    original_limitCone_compactSpace_of_patch_surjective (F := F) Z hF hZ_closed hZ_maps
  letI : CompactSpace ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :=
    hCompactOriginalCone
  -- The explicit original cone point is canonically homeomorphic to `limit (F.stableSubsetDiagram
  -- Z hZ_maps)`, so compactness transports back to the abstract limit.
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso
        (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps))
        (limit.isLimit (F.stableSubsetDiagram Z hZ_maps)))
  simpa using e.compactSpace

-- Proof sketch: specialize the previous theorem to the family `Z i = univ`, then transport the
-- resulting compactness across the natural isomorphism from the stable-subset diagram back to the
-- original diagram.
/-- The inverse limit of a diagram of spectral spaces is quasi-compact. -/
theorem compactSpace_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a)) :
    CompactSpace ↥(limit F) := by
  have hUnivClosed :
      ∀ i, IsClosed[constructibleTopology (F.obj i)]
        ((fun i ↦ (Set.univ : Set (F.obj i))) i) := by
    intro i
    simp
  have hCompactStable :
      CompactSpace ↥(limit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
          (stableSubsetDiagram_mapsTo_univ_subset (F := F)))) :=
    compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
      (F := F)
      (Z := fun i ↦ (Set.univ : Set (F.obj i)))
      (hF := hF)
      (hZ_closed := hUnivClosed)
      (hZ_maps := stableSubsetDiagram_mapsTo_univ_subset (F := F))
  -- For the universal family, the restricted diagram is naturally isomorphic to the original one.
  letI :
      CompactSpace ↥(limit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
          (stableSubsetDiagram_mapsTo_univ_subset (F := F)))) := hCompactStable
  let e :=
    TopCat.homeoOfIso
      (HasLimit.isoOfNatIso (stable_subset_diagram_univ_iso (F := F)))
  simpa using e.compactSpace

end
