module

public import stacks_project.Chap05.Lemma_5_24_1
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v w

noncomputable section

section

variable {I : Type v} [Category.{w} I] [IsCofiltered I]
variable (F : I ⥤ TopCat.{max u v})
variable [∀ i : I, SpectralSpace (F.obj i)]
variable (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
variable (Z : ∀ i, Set (F.obj i))
variable (hZ_nonempty : ∀ i, (Z i).Nonempty)
variable (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
variable (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))

/- Domain-style sampling for nonempty cofiltered limits of spectral spaces:
- primary domain: inverse limits of spectral spaces, constructible-topology closed subspaces, and
  the induced stable subdiagram on chosen subsets;
- sampled owner-level declarations:
  `CategoryTheory.Functor.stableSubsetDiagram`,
  `compactSpace_limit_of_constructibleClosed_stableSubsetDiagram`,
  `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`;
- best owner abstraction: the source-facing restricted diagram `F.stableSubsetDiagram Z hZ_maps`,
  with nonemptiness obtained from the canonical `TopCat` cofiltered-limit theorem after upgrading
  each stage to the constructible-topology compact Hausdorff owner.
-/

-- Proof sketch: the source proof passes to the constructible-topology subdiagram `Z'_i`,
-- reindexes along `AsSmall.down`, applies the compact-Hausdorff cofiltered-limit nonemptiness
-- theorem there, and then forgets the auxiliary topology stagewise to obtain a point of the
-- original stable-subset inverse limit.
omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: the family `Z i = univ` is stable under every transition map. -/
theorem mapsTo_univ_subset :
    ∀ ⦃i j : I⦄ (a : i ⟶ j),
      Set.MapsTo (F.map a)
        ((fun i ↦ (Set.univ : Set (F.obj i))) i)
        ((fun j ↦ (Set.univ : Set (F.obj j))) j) := by
  intro i j a x hx
  simp

/-- Helper for Lemma 5.24.2: the subset `Z i` with the subspace topology induced from the
constructible topology on `F.obj i`. -/
abbrev ConstructibleStableSubtype (i : I) : Type (max u v) :=
  { x : WithConstructibleTopology (F.obj i) | (x : F.obj i) ∈ Z i }

/-- Helper for Lemma 5.24.2: a small cofinal reindexing of the original cofiltered category. -/
abbrev ConstructibleSmallIndex :=
  AsSmall.{max w v} I

omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: every stage of the constructible-topology subdiagram is nonempty. -/
theorem constructible_stage_nonempty
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (i : ConstructibleSmallIndex (I := I)) :
    Nonempty (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) := by
  -- The witness is the same point of `Z i`, now regarded inside the constructible-topology owner.
  rcases hZ_nonempty (AsSmall.down.obj i) with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

omit [IsCofiltered I] in
/-- Helper for Lemma 5.24.2: every stage of the constructible-topology subdiagram is compact. -/
theorem constructible_stage_compactSpace
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (i : ConstructibleSmallIndex (I := I)) :
    CompactSpace (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) := by
  -- A constructibly closed subset of a compact constructible topology is compact.
  let _ : CompactSpace (WithConstructibleTopology (F.obj (AsSmall.down.obj i))) := inferInstance
  have hClosed :
      IsClosed { x : WithConstructibleTopology (F.obj (AsSmall.down.obj i)) |
        (x : F.obj (AsSmall.down.obj i)) ∈ Z (AsSmall.down.obj i) } := by
    simpa [WithConstructibleTopology] using hZ_closed (AsSmall.down.obj i)
  exact isCompact_iff_compactSpace.mp hClosed.isCompact

omit [IsCofiltered I] in
/-- Helper for Lemma 5.24.2: every stage of the constructible-topology subdiagram is Hausdorff. -/
theorem constructible_stage_t2Space
    (i : ConstructibleSmallIndex (I := I)) :
    T2Space (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) := by
  -- The ambient constructible topology is Hausdorff, and subspaces of Hausdorff spaces are
  -- Hausdorff.
  let _ : T2Space (WithConstructibleTopology (F.obj (AsSmall.down.obj i))) := inferInstance
  infer_instance

omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: the restricted transition maps are continuous for the constructible
subspace topologies. -/
theorem constructible_reindexed_stableSubsetDiagramMap_continuous
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : ConstructibleSmallIndex (I := I)} (a : i ⟶ j) :
    Continuous (fun x : ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i) ↦
      (⟨(F.map a.down) x.1, hZ_maps a.down x.2⟩ :
        ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj j))) := by
  -- The ambient map is constructibly continuous, so it restricts continuously to the closed
  -- subspaces `Z i`.
  let g : ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i) →
      WithConstructibleTopology (F.obj (AsSmall.down.obj j)) :=
    fun x ↦ (F.map a.down) x.1
  have hg : Continuous g := by
    let g' : WithConstructibleTopology (F.obj (AsSmall.down.obj i)) →
        WithConstructibleTopology (F.obj (AsSmall.down.obj j)) := F.map a.down
    have hg' : Continuous g' := by
      simpa [g', WithConstructibleTopology] using (hF a.down).continuous_constructibleTopology
    simpa [g, g'] using hg'.comp continuous_subtype_val
  simpa [g] using hg.subtype_mk
    (fun x : ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i) ↦ hZ_maps a.down x.2)

/-- Helper for Lemma 5.24.2: the constructible-topology restricted diagram, reindexed on
`AsSmall I`. -/
def constructible_reindexed_stableSubsetDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    ConstructibleSmallIndex (I := I) ⥤ TopCat.{max u v} where
  obj i := TopCat.of (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i))
  map a := TopCat.ofHom
    ⟨fun x ↦ ⟨(F.map a.down) x.1, hZ_maps a.down x.2⟩,
      constructible_reindexed_stableSubsetDiagramMap_continuous (F := F) (Z := Z) hF hZ_maps a⟩
  map_id i := by
    apply ConcreteCategory.ext
    ext x
    -- After restricting to the subtype, the identity map is still pointwise the identity.
    change
      ((ConcreteCategory.hom (F.map (𝟙 (AsSmall.down.obj i)))) x.1 :
        WithConstructibleTopology (F.obj (AsSmall.down.obj i))) = x.1
    simp
    rfl
  map_comp a b := by
    rename_i X Y Z' a b
    apply ConcreteCategory.ext
    ext x
    -- The restricted maps compose exactly as the ambient diagram maps do.
    change
      (ConcreteCategory.hom (F.map (a.down ≫ b.down))) x.1 =
        (ConcreteCategory.hom (F.map b.down)) ((ConcreteCategory.hom (F.map a.down)) x.1)
    simp

omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: the transition maps of the lifted small constructible diagram are
continuous. -/
theorem constructible_reindexed_stableSubsetDiagram_liftedMap_continuous
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    ∀ {i j : ConstructibleSmallIndex (I := I)} (a : i ⟶ j),
      Continuous (fun x : ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) ↦
        (ULift.up
          (⟨(F.map a.down) x.down.1, hZ_maps a.down x.down.2⟩ :
            ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj j)))) := by
  intro i j a
  -- The lifted map is `ULift.up` after the already constructed continuous restricted map.
  exact
    continuous_uliftUp.comp
      ((constructible_reindexed_stableSubsetDiagramMap_continuous (F := F) (Z := Z) hF hZ_maps a).comp
        continuous_uliftDown)

/-- Helper for Lemma 5.24.2: the lifted small constructible-topology diagram used to apply
Kőnig's lemma in the required universe. -/
def constructible_reindexed_stableSubsetDiagram_lifted
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    ConstructibleSmallIndex (I := I) ⥤ TopCat.{max u v w} :=
  { obj := fun i ↦ TopCat.of (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    map := fun a ↦
      TopCat.ofHom
        ⟨fun x ↦
          ULift.up
            (⟨(F.map a.down) x.down.1, hZ_maps a.down x.down.2⟩ :
              ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj _)),
          constructible_reindexed_stableSubsetDiagram_liftedMap_continuous
            (F := F) (Z := Z) hF hZ_maps a⟩
    map_id := by
      intro i
      apply ConcreteCategory.ext
      ext x
      change
        ((ConcreteCategory.hom (F.map (𝟙 (AsSmall.down.obj i)))) x.down.1 :
          WithConstructibleTopology (F.obj (AsSmall.down.obj i))) = x.down.1
      simp
      rfl
    map_comp := by
      intro X Y Z' a b
      apply ConcreteCategory.ext
      ext x
      change
        (ConcreteCategory.hom (F.map (a.down ≫ b.down))) x.down.1 =
          (ConcreteCategory.hom (F.map b.down)) ((ConcreteCategory.hom (F.map a.down)) x.down.1)
      simp }

/-- Helper for Lemma 5.24.2: forget the auxiliary constructible topology on a stagewise point. -/
def forget_constructible_point {i : I} :
    ConstructibleStableSubtype (F := F) Z i → Z i :=
  fun x ↦ ⟨(x.1 : F.obj i), x.2⟩

/-- Helper for Lemma 5.24.2: a point of the lifted constructible chosen limit cone gives a point
of the original stable-subset chosen limit cone. -/
def constructible_reindexed_limitCone_point_to_stableSubset_limitCone_point
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (x : (TopCat.limitCone
      (constructible_reindexed_stableSubsetDiagram_lifted (F := F) (Z := Z) hF hZ_maps)).pt) :
    (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt := by
  -- A limit point is a compatible family, so we simply evaluate it at `⟨i⟩` and forget the
  -- auxiliary topology.
  let D := constructible_reindexed_stableSubsetDiagram (F := F) (Z := Z) hF hZ_maps
  refine ⟨fun i ↦ forget_constructible_point (F := F) (Z := Z) ((x.1 ⟨i⟩).down), ?_⟩
  intro i j a
  apply Subtype.ext
  -- The compatibility relation is exactly the same after removing `ULift` and the constructible
  -- topology wrapper.
  have hx : D.map ⟨a⟩ ((x.1 ⟨i⟩).down) = (x.1 ⟨j⟩).down := by
    exact congrArg ULift.down (x.2 ⟨a⟩)
  simpa [D, forget_constructible_point, CategoryTheory.Functor.stableSubsetDiagram] using
    congrArg Subtype.val hx

/-- Helper for Lemma 5.24.2: the chosen limit cone of the original stable-subset diagram is
nonempty. -/
theorem nonempty_limitCone_of_constructibleClosed_stableSubsetDiagram_aux
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i)) :
    Nonempty (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt := by
  -- We apply Kőnig's lemma to the small lifted constructible-topology diagram.
  let Dlift : ConstructibleSmallIndex (I := I) ⥤ TopCat.{max u v w} :=
    constructible_reindexed_stableSubsetDiagram_lifted (F := F) (Z := Z) hF hZ_maps
  let _ : ∀ i : ConstructibleSmallIndex (I := I), Nonempty (Dlift.obj i) := by
    intro i
    haveI : Nonempty (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) :=
      constructible_stage_nonempty (F := F) (Z := Z) hZ_nonempty i
    change Nonempty (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    infer_instance
  let _ : ∀ i : ConstructibleSmallIndex (I := I), CompactSpace (Dlift.obj i) := by
    intro i
    haveI : CompactSpace (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) :=
      constructible_stage_compactSpace (F := F) (Z := Z) hZ_closed i
    change CompactSpace (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    infer_instance
  let _ : ∀ i : ConstructibleSmallIndex (I := I), T2Space (Dlift.obj i) := by
    intro i
    haveI : T2Space (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) :=
      constructible_stage_t2Space (F := F) (Z := Z) i
    change T2Space (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    infer_instance
  obtain ⟨x⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} Dlift
  exact
    ⟨constructible_reindexed_limitCone_point_to_stableSubset_limitCone_point
      (F := F) (Z := Z) hF hZ_maps x⟩

/-- Lemma 5.24.2 (1): for a cofiltered diagram of spectral spaces with spectral transition maps,
nonempty subsets that are closed in the constructible topology and stable under the transition maps
have a nonempty inverse limit. -/
theorem nonempty_limit_of_constructibleClosed_stableSubsetDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i)) :
    Nonempty ↥(limit (F.stableSubsetDiagram Z hZ_maps)) := by
  -- Route correction: the intended proof is to pass to the constructible-topology subdiagram,
  -- apply Kőnig there after an `AsSmall` reindex, and then forget the auxiliary topology.
  obtain ⟨x⟩ :=
    nonempty_limitCone_of_constructibleClosed_stableSubsetDiagram_aux
      (F := F) (Z := Z) (hZ_maps := hZ_maps) hF hZ_nonempty hZ_closed
  -- The chosen `TopCat.limitCone` point maps to the categorical limit point via the universal
  -- comparison isomorphism.
  exact
    ⟨(IsLimit.conePointUniqueUpToIso
      (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps))
      (limit.isLimit (F.stableSubsetDiagram Z hZ_maps))).hom x⟩

-- Proof sketch: apply part `(1)` to the constant family `Z i = Set.univ`; these subsets are
-- nonempty by assumption, closed in every topology, and stable under all transition maps.
/-- Lemma 5.24.2 (2): if every space in a cofiltered diagram of spectral spaces is nonempty, then
the inverse limit space is nonempty. -/
theorem nonempty_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    [∀ i : I, Nonempty (F.obj i)] :
    Nonempty ↥(limit F) := by
  classical
  have hUnivNonempty :
      ∀ i, ((fun i ↦ (Set.univ : Set (F.obj i))) i).Nonempty := by
    intro i
    exact ⟨Classical.choice inferInstance, by simp⟩
  have hUnivClosed :
      ∀ i, IsClosed[constructibleTopology (F.obj i)]
        ((fun i ↦ (Set.univ : Set (F.obj i))) i) := by
    intro i
    simp
  -- Apply part `(1)` to the stable family `Z i = univ`.
  obtain ⟨x⟩ :=
    nonempty_limit_of_constructibleClosed_stableSubsetDiagram
      (F := F)
      (Z := fun i ↦ (Set.univ : Set (F.obj i)))
      (hZ_maps := mapsTo_univ_subset (F := F)) hF hUnivNonempty hUnivClosed
  let e :
      (TopCat.limitCone
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F)))).pt ≅
        limit (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F))) :=
    IsLimit.conePointUniqueUpToIso
      (TopCat.limitConeIsLimit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F))))
      (limit.isLimit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F))))
  let x' : (TopCat.limitCone
      (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F)))).pt :=
    e.inv x
  let y : (TopCat.limitCone F).pt := by
    refine ⟨fun i ↦ (x'.1 i).1, ?_⟩
    intro i j a
    -- For `Z i = univ`, forgetting the subtype proof recovers the original compatibility.
    simpa [CategoryTheory.Functor.stableSubsetDiagram] using
      congrArg (fun z : ((fun j ↦ (Set.univ : Set (F.obj j))) j) ↦ (z : F.obj j)) (x'.2 a)
  -- Transport the compatible family from the chosen limit cone to the categorical limit.
  exact
    ⟨(IsLimit.conePointUniqueUpToIso
      (TopCat.limitConeIsLimit F)
      (limit.isLimit F)).hom y⟩

end
