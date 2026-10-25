module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_3
import stacks_project.Chap05.Lemma_5_24_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v

noncomputable section

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable {F : I ⥤ TopCat.{max u v}} [∀ i : I, SpectralSpace ↥(F.obj i)]
variable {C : Cone F}

/- Domain-style sampling for cofiltered limits of spectral spaces:
- primary domain: inverse limits in `TopCat` of spectral spaces with spectral transition maps;
- sampled owner declarations:
  `SpectralSpace`,
  `IsSpectralMap`,
  `TopCat.isTopologicalBasis_cofiltered_limit`,
  `compact_open_eq_preimage_of_isLimit`;
- best owner abstraction: the cone-level spectrality theorem for an arbitrary limiting cone, with
  the chosen categorical limit treated only as derived inference support;
- primitive data: a cofiltered diagram `F`, spectral structures on the stages, a limiting cone
  `C`, and spectrality of the transition maps;
- derived API: spectrality of the limiting cone point and spectrality of its projection maps.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that an inverse limit of spectral spaces with spectral
  transition maps is spectral, together with the projection-map corollary;
- `core/canonical`: `SpectralSpace` and `IsSpectralMap` on the limiting cone data;
- `bridge/view`: the chosen-limit specialization, which should remain only an instance and not a
  second named owner theorem.
-/

/-- Helper for Lemma 5.24.5: at stage `j`, keep only the points whose image in the fixed stage `i`
lies in the chosen compact open along every arrow `j ⟶ i`. -/
private def stagewise_pullback_family (i : I) (U : CompactOpens (F.obj i)) (j : I) :
    Set (F.obj j) :=
  ⋂ a : j ⟶ i, (F.map a) ⁻¹' (U : Set (F.obj i))

/-- Helper for Lemma 5.24.5: the stagewise pullback family is constructibly closed because each
member is the pullback of a compact open along a spectral map. -/
private theorem stagewise_pullback_family_closed
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (U : CompactOpens (F.obj i)) (j : I) :
    IsClosed[constructibleTopology (F.obj j)] (stagewise_pullback_family (F := F) i U j) := by
  -- Compact opens are clopen for the constructible topology on a spectral space.
  have hU_closed : IsClosed[constructibleTopology (F.obj i)] (U : Set (F.obj i)) := by
    exact (isClopen_constructibleTopology_of_isConstructible
      (U.isCompact.isConstructible U.isOpen)).1
  -- Intersect the constructibly closed pullbacks over all arrows `j ⟶ i`.
  dsimp [stagewise_pullback_family]
  refine @isClosed_iInter (F.obj j) (j ⟶ i) (constructibleTopology (F.obj j))
    (fun a ↦ (F.map a) ⁻¹' (U : Set (F.obj i))) ?_
  intro a
  exact @IsClosed.preimage (F.obj j) (F.obj i)
    (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i))
    (F.map a) (hF a).continuous_constructibleTopology _ hU_closed

/-- Helper for Lemma 5.24.5: the stagewise pullback family is stable under the transition maps. -/
private theorem stagewise_pullback_family_mapsTo
    (i : I) (U : CompactOpens (F.obj i)) {j k : I} (a : j ⟶ k) :
    Set.MapsTo (F.map a)
      (stagewise_pullback_family (F := F) i U j)
      (stagewise_pullback_family (F := F) i U k) := by
  -- A point satisfying all arrows out of `j` still satisfies all arrows out of `k` after
  -- precomposing with `a`.
  intro x hx
  refine mem_iInter.2 fun b ↦ ?_
  have hx' :
      x ∈ (F.map (a ≫ b)) ⁻¹' (U : Set (F.obj i)) := by
    exact mem_iInter.1 hx (a ≫ b)
  change F.map b (F.map a x) ∈ (U : Set (F.obj i))
  simpa [stagewise_pullback_family, Functor.map_comp] using hx'

/-- Helper for Lemma 5.24.5: forgetting the subtype coordinate gives a natural transformation from
the stable-subset diagram back to the ambient diagram. -/
private def stagewise_pullback_forget_hom
    (i : I) (U : CompactOpens (F.obj i))
    (hZ_maps :
      ∀ ⦃j k : I⦄ (a : j ⟶ k), Set.MapsTo (F.map a)
        (stagewise_pullback_family (F := F) i U j)
        (stagewise_pullback_family (F := F) i U k)) :
    (F.stableSubsetDiagram (stagewise_pullback_family (F := F) i U) hZ_maps) ⟶ F where
  app j := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  naturality {X Y} f := by
    -- Both sides are the same restricted ambient map on points.
    ext x
    rfl

/-- Helper for Lemma 5.24.5: the pullback of a stage compact open to the explicit limit cone is
compact, by realizing it as the image of a compact limit of a stable-subset diagram. -/
private theorem projection_preimage_isCompact_of_compact_open
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (U : CompactOpens (F.obj i)) :
    IsCompact (((TopCat.limitCone F).π.app i) ⁻¹' (U : Set (F.obj i))) := by
  let Z := stagewise_pullback_family (F := F) i U
  have hZ_closed : ∀ j : I, IsClosed[constructibleTopology (F.obj j)] (Z j) := by
    intro j
    exact stagewise_pullback_family_closed (F := F) hF i U j
  have hZ_maps :
      ∀ ⦃j k : I⦄ (a : j ⟶ k), Set.MapsTo (F.map a) (Z j) (Z k) := by
    intro j k a
    exact stagewise_pullback_family_mapsTo (F := F) i U a
  let D := F.stableSubsetDiagram Z hZ_maps
  have hCompactLimit : CompactSpace ↥(limit D) :=
    compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
      (F := F) (Z := Z) (hF := hF) (hZ_closed := hZ_closed) (hZ_maps := hZ_maps)
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit D) (TopCat.limitConeIsLimit D))
  letI : CompactSpace ↥((limit.cone D).pt) := by
    simpa using hCompactLimit
  letI : CompactSpace ↥((TopCat.limitCone D).pt) := by
    exact e.compactSpace
  let α := stagewise_pullback_forget_hom (F := F) i U hZ_maps
  let c : Cone F := (Cone.postcompose α).obj (TopCat.limitCone D)
  let f : (TopCat.limitCone D).pt ⟶ (TopCat.limitCone F).pt :=
    (TopCat.limitConeIsLimit F).lift c
  have hImage :
      f '' (Set.univ : Set (TopCat.limitCone D).pt) =
        ((TopCat.limitCone F).π.app i) ⁻¹' (U : Set (F.obj i)) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      refine mem_preimage.2 ?_
      have hfπ :
          (TopCat.limitCone F).π.app i (f y) = c.π.app i y := by
        simpa [f] using
          congrArg
            (fun g : (TopCat.limitCone D).pt ⟶ F.obj i ↦ g y)
            ((TopCat.limitConeIsLimit F).fac c i)
      have hyi : c.π.app i y ∈ (U : Set (F.obj i)) := by
        change (((TopCat.limitCone D).π.app i y).1 : F.obj i) ∈ (U : Set (F.obj i))
        have hyi' :
            ((TopCat.limitCone D).π.app i y).1 ∈ Z i :=
          ((TopCat.limitCone D).π.app i y).2
        simpa [Z, stagewise_pullback_family, Functor.map_id] using
          (mem_iInter.1 hyi' (𝟙 i))
      rw [hfπ]
      exact hyi
    · intro hx
      let yComp : ∀ j : I, D.obj j := fun j ↦
        ⟨(TopCat.limitCone F).π.app j x, by
          refine mem_iInter.2 fun a ↦ ?_
          change F.map a ((TopCat.limitCone F).π.app j x) ∈ (U : Set (F.obj i))
          have hπ :
              (TopCat.limitCone F).π.app i x =
                F.map a ((TopCat.limitCone F).π.app j x) := by
            rw [← CategoryTheory.comp_apply]
            exact congrArg
              (fun g : (TopCat.limitCone F).pt ⟶ F.obj i ↦ g x)
              ((TopCat.limitCone F).w a).symm
          exact hπ ▸ mem_preimage.1 hx⟩
      have hyCompat :
          ∀ ⦃j k : I⦄ (a : j ⟶ k), D.map a (yComp j) = yComp k := by
        intro j k a
        apply Subtype.ext
        change F.map a ((TopCat.limitCone F).π.app j x) = (TopCat.limitCone F).π.app k x
        rw [← CategoryTheory.comp_apply]
        exact congrArg
          (fun g : (TopCat.limitCone F).pt ⟶ F.obj k ↦ g x)
          ((TopCat.limitCone F).w a)
      let y : (TopCat.limitCone D).pt := ⟨yComp, fun {_ _} a ↦ hyCompat a⟩
      refine ⟨y, trivial, ?_⟩
      apply Subtype.ext
      funext j
      have hfπ :
          (TopCat.limitCone F).π.app j (f y) = c.π.app j y := by
        simpa [f] using
          congrArg
            (fun g : (TopCat.limitCone D).pt ⟶ F.obj j ↦ g y)
            ((TopCat.limitConeIsLimit F).fac c j)
      change (TopCat.limitCone F).π.app j (f y) = (TopCat.limitCone F).π.app j x
      rw [hfπ]
      rfl
  -- The stable-subset limit is compact, and its image is exactly the desired pullback subset.
  rw [← hImage]
  exact isCompact_univ.image f.hom.continuous

/-- Helper for Lemma 5.24.5: index the compact-open basic neighborhoods on the explicit limit cone
by a stage together with a stage compact open. -/
private def projection_preimage_basis :
    (Σ i : I, CompactOpens (F.obj i)) → Set (TopCat.limitCone F).pt :=
  fun p ↦ (TopCat.limitCone F).π.app p.1 ⁻¹' (p.2 : Set (F.obj p.1))

/-- Helper for Lemma 5.24.5: projection pullbacks of stage compact opens form a topological basis
on the explicit limit cone. -/
private theorem projection_preimage_compact_open_basis
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    IsTopologicalBasis (Set.range (projection_preimage_basis (F := F))) := by
  let C := TopCat.limitCone F
  let T : ∀ j : I, Set (Set (F.obj j)) := fun j ↦ {U : Set (F.obj j) | IsOpen U ∧ IsCompact U}
  have hT_basis : ∀ j : I, IsTopologicalBasis (T j) := by
    intro j
    simpa [T] using (PrespectralSpace.isTopologicalBasis (X := F.obj j))
  have hT_univ : ∀ j : I, Set.univ ∈ T j := by
    intro j
    exact ⟨isOpen_univ, isCompact_univ⟩
  have hT_inter :
      ∀ j : I, ∀ U V : Set (F.obj j), U ∈ T j → V ∈ T j → U ∩ V ∈ T j := by
    intro j U V hU hV
    exact ⟨hU.1.inter hV.1, hU.2.inter_of_isOpen hV.2 hU.1 hV.1⟩
  have hBasisAux :
      IsTopologicalBasis {W : Set C.pt | ∃ j, ∃ V ∈ T j, W = C.π.app j ⁻¹' V} :=
    TopCat.isTopologicalBasis_cofiltered_limit.{max u v, u, v} F C (TopCat.limitConeIsLimit F)
      T
      hT_basis hT_univ hT_inter
      (fun _ _ a U hU ↦ by
        change IsOpen ((F.map a) ⁻¹' U) ∧ IsCompact ((F.map a) ⁻¹' U)
        exact ⟨hU.1.preimage (hF a).continuous, (hF a).isCompact_preimage_of_isOpen hU.1 hU.2⟩)
  have hRange :
      Set.range (projection_preimage_basis (F := F)) =
        {W : Set C.pt | ∃ (j : I) (U : Set (F.obj j)),
          IsOpen U ∧ IsCompact U ∧ W = C.π.app j ⁻¹' U} := by
    ext W
    constructor
    · rintro ⟨⟨j, U⟩, rfl⟩
      exact ⟨j, (U : Set (F.obj j)), U.isOpen, U.isCompact, rfl⟩
    · rintro ⟨j, U, hU_open, hU_compact, rfl⟩
      exact ⟨⟨j, ⟨⟨U, hU_compact⟩, hU_open⟩⟩, rfl⟩
  -- Rewrite the existential basis returned by the owner theorem into the sigma-indexed family.
  rw [hRange]
  simpa [T, and_assoc] using hBasisAux

/-- Helper for Lemma 5.24.5: a basis intersection is again a single projection pullback on a
common refinement stage. -/
private theorem projection_preimage_inter_eq
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    (i j : I) (Ui : CompactOpens (F.obj i)) (Uj : CompactOpens (F.obj j)) :
    ∃ (k : I) (_ : k ⟶ i) (_ : k ⟶ j) (Uk : CompactOpens (F.obj k)),
      (((TopCat.limitCone F).π.app i) ⁻¹' (Ui : Set (F.obj i))) ∩
          (((TopCat.limitCone F).π.app j) ⁻¹' (Uj : Set (F.obj j))) =
        ((TopCat.limitCone F).π.app k) ⁻¹' (Uk : Set (F.obj k)) := by
  let C := TopCat.limitCone F
  have hπ {a b : I} (f : a ⟶ b) (x : C.pt) :
      C.π.app b x = F.map f (C.π.app a x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun m : C.pt ⟶ F.obj b ↦ m x) (C.w f).symm
  obtain ⟨k, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  have hUk_open :
      IsOpen (((F.map a) ⁻¹' (Ui : Set (F.obj i))) ∩
        ((F.map b) ⁻¹' (Uj : Set (F.obj j))) : Set (F.obj k)) := by
    exact (Ui.isOpen.preimage (hF a).continuous).inter (Uj.isOpen.preimage (hF b).continuous)
  have hUk_compact :
      IsCompact (((F.map a) ⁻¹' (Ui : Set (F.obj i))) ∩
        ((F.map b) ⁻¹' (Uj : Set (F.obj j))) : Set (F.obj k)) := by
    exact ((hF a).isCompact_preimage_of_isOpen Ui.isOpen Ui.isCompact).inter_of_isOpen
      ((hF b).isCompact_preimage_of_isOpen Uj.isOpen Uj.isCompact)
      (Ui.isOpen.preimage (hF a).continuous) (Uj.isOpen.preimage (hF b).continuous)
  let Uk : CompactOpens (F.obj k) := ⟨⟨_, hUk_compact⟩, hUk_open⟩
  refine ⟨k, a, b, Uk, ?_⟩
  ext x
  constructor
  · intro hx
    refine mem_preimage.2 ?_
    constructor
    · have hleft : C.π.app i x ∈ (Ui : Set (F.obj i)) := mem_preimage.1 hx.1
      change F.map a (C.π.app k x) ∈ (Ui : Set (F.obj i))
      exact (hπ a x).symm ▸ hleft
    · have hright : C.π.app j x ∈ (Uj : Set (F.obj j)) := mem_preimage.1 hx.2
      change F.map b (C.π.app k x) ∈ (Uj : Set (F.obj j))
      exact (hπ b x).symm ▸ hright
  · intro hx
    constructor
    · refine mem_preimage.2 ?_
      have hleft : F.map a (C.π.app k x) ∈ (Ui : Set (F.obj i)) := (mem_preimage.1 hx).1
      exact hπ a x ▸ hleft
    · refine mem_preimage.2 ?_
      have hright : F.map b (C.π.app k x) ∈ (Uj : Set (F.obj j)) := (mem_preimage.1 hx).2
      exact hπ b x ▸ hright

/-- Helper for Lemma 5.24.5: an irreducible closed subset of the explicit limit cone has a
generic point obtained from the compatible family of the stage generic points. -/
private theorem generic_point_of_irreducible_closed_limit
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    {Z : Set (TopCat.limitCone F).pt}
    (hZ_irred : IsIrreducible Z) (hZ_closed : IsClosed Z) :
    ∃ ξ : (TopCat.limitCone F).pt, IsGenericPoint ξ Z := by
  let C := TopCat.limitCone F
  have hπ {i j : I} (f : i ⟶ j) (x : C.pt) :
      C.π.app j x = F.map f (C.π.app i x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun g : C.pt ⟶ F.obj j ↦ g x) (C.w f).symm
  have hBasis : IsTopologicalBasis (Set.range (projection_preimage_basis (F := F))) :=
    projection_preimage_compact_open_basis (F := F) hF
  have hImage_irred (i : I) : IsIrreducible (C.π.app i '' Z) :=
    hZ_irred.image (C.π.app i) (C.π.app i).hom.continuous.continuousOn
  let ξi : ∀ i : I, F.obj i := fun i ↦ (hImage_irred i).genericPoint
  have hξi :
      ∀ i : I, IsGenericPoint (ξi i) (closure (C.π.app i '' Z)) := by
    intro i
    simpa [ξi] using (hImage_irred i).isGenericPoint_genericPoint_closure
  have hmap_image {i j : I} (f : i ⟶ j) :
      F.map f '' (C.π.app i '' Z) = C.π.app j '' Z := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, hπ f z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨C.π.app i z, ⟨z, hz, rfl⟩, (hπ f z).symm⟩
  have hξ_compatible : ∀ {i j : I} (f : i ⟶ j), F.map f (ξi i) = ξi j := by
    intro i j f
    have hImageGeneric :
        IsGenericPoint (F.map f (ξi i)) (closure (C.π.app j '' Z)) := by
      have htmp := (hξi i).image (F.map f).hom.continuous
      have hclosure :
          closure (F.map f '' closure (C.π.app i '' Z)) = closure (C.π.app j '' Z) := by
        rw [closure_image_closure (F.map f).hom.continuous]
        simpa using congrArg closure (hmap_image (f := f))
      exact hclosure ▸ htmp
    exact IsGenericPoint.eq hImageGeneric (hξi j)
  let ξ : C.pt :=
    ⟨ξi, fun {_ _} f ↦ hξ_compatible f⟩
  have hξ_mem_closure : ξ ∈ closure Z := by
    -- Any open neighborhood of `ξ` contains a basis neighborhood of the form `π_i ⁻¹(Ui)`.
    rw [mem_closure_iff]
    intro U hU hξU
    obtain ⟨B, hB, hξB, hBU⟩ := hBasis.exists_subset_of_mem_open hξU hU
    rcases hB with ⟨⟨i, Ui⟩, rfl⟩
    have hξiUi : ξi i ∈ (Ui : Set (F.obj i)) := by
      simpa [ξ, projection_preimage_basis] using hξB
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (Ui : Set (F.obj i))).Nonempty :=
      ((hξi i).mem_open_set_iff Ui.isOpen).1 hξiUi
    rcases hStageMeet with ⟨y, hyClosure, hyUi⟩
    rcases mem_closure_iff.1 hyClosure (Ui : Set (F.obj i)) Ui.isOpen hyUi with
      ⟨w, hwUi, hwImage⟩
    rcases hwImage with ⟨z, hz, rfl⟩
    refine ⟨z, ?_, hz⟩
    exact hBU (by simpa [projection_preimage_basis] using hwUi)
  have hξ_mem : ξ ∈ Z := by
    simpa [hZ_closed.closure_eq] using hξ_mem_closure
  have hξ_specializes : ∀ ⦃z : C.pt⦄, z ∈ Z → ξ ⤳ z := by
    intro z hz
    -- Basis neighborhoods of `z` already meet the stage image of `Z`, hence they contain `ξ`.
    rw [specializes_iff_forall_open]
    intro U hU hzU
    obtain ⟨B, hB, hzB, hBU⟩ := hBasis.exists_subset_of_mem_open hzU hU
    rcases hB with ⟨⟨i, Ui⟩, rfl⟩
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (Ui : Set (F.obj i))).Nonempty := by
      exact ⟨C.π.app i z, subset_closure ⟨z, hz, rfl⟩, by
        simpa [projection_preimage_basis] using hzB⟩
    have hξiUi : ξi i ∈ (Ui : Set (F.obj i)) :=
      ((hξi i).mem_open_set_iff Ui.isOpen).2 hStageMeet
    have hξB : ξ ∈ C.π.app i ⁻¹' (Ui : Set (F.obj i)) := by
      simpa [ξ, projection_preimage_basis] using hξiUi
    exact hBU hξB
  have hclosure_subset : closure ({ξ} : Set C.pt) ⊆ Z :=
    hZ_closed.closure_subset_iff.mpr (by simpa using (singleton_subset_iff.mpr hξ_mem))
  refine ⟨ξ, ?_⟩
  -- The specialization criterion identifies `Z` with the closure of the singleton `{ξ}`.
  rw [isGenericPoint_iff_specializes]
  intro z
  constructor
  · intro hz
    exact hclosure_subset (specializes_iff_mem_closure.mp hz)
  · intro hz
    exact hξ_specializes hz

/-- Helper for Lemma 5.24.5: the explicit limit cone of the diagram is spectral. -/
private theorem explicit_spectralSpace_of_cofiltered_spectral_diagram
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥((TopCat.limitCone F).pt) := by
  classical
  let C := TopCat.limitCone F
  have hCompactLimit : CompactSpace ↥(limit F) :=
    compactSpace_limit_of_spectralSpaceDiagram (F := F) hF
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (TopCat.limitConeIsLimit F))
  letI : CompactSpace ↥((limit.cone F).pt) := by
    simpa using hCompactLimit
  letI : T0Space C.pt := by
    change T0Space { u : ∀ j : I, F.obj j |
      ∀ {i j : I} (f : i ⟶ j), F.map f (u i) = u j }
    infer_instance
  letI : CompactSpace C.pt := by
    exact e.compactSpace
  letI : QuasiSober C.pt :=
    { sober := fun {Z} hZ_irred hZ_closed ↦
        generic_point_of_irreducible_closed_limit (F := F) hF hZ_irred hZ_closed }
  let b := projection_preimage_basis (F := F)
  have hBasis : IsTopologicalBasis (Set.range b) :=
    projection_preimage_compact_open_basis (F := F) hF
  have hCompactBasis : ∀ p : Σ i : I, CompactOpens (F.obj i), IsCompact (b p) := by
    rintro ⟨i, U⟩
    -- Each basis element is compact by the stable-subset limit comparison above.
    simpa [b, projection_preimage_basis] using
      projection_preimage_isCompact_of_compact_open (F := F) hF i U
  have hCompactInter :
      ∀ p q : Σ i : I, CompactOpens (F.obj i), IsCompact (b p ∩ b q) := by
    rintro ⟨i, Ui⟩ ⟨j, Uj⟩
    obtain ⟨k, _, _, Uk, hEq⟩ :=
      projection_preimage_inter_eq (F := F) hF i j Ui Uj
    have hbEq : b ⟨i, Ui⟩ ∩ b ⟨j, Uj⟩ = b ⟨k, Uk⟩ := by
      simpa [b, projection_preimage_basis] using hEq
    rw [hbEq]
    simpa [b, projection_preimage_basis] using
      projection_preimage_isCompact_of_compact_open (F := F) hF k Uk
  letI : PrespectralSpace C.pt :=
    PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis
  letI : QuasiSeparatedSpace C.pt :=
    QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
  exact
    { toT0Space := inferInstance
      toCompactSpace := inferInstance
      toQuasiSober := inferInstance
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }

/-- Helper for Lemma 5.24.5: a homeomorphism is spectral because preimages of compact sets are
images under the continuous inverse. -/
private theorem isSpectralMap_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : IsSpectralMap e := by
  refine ⟨e.continuous, fun s _ hs_compact ↦ ?_⟩
  have hpreimage : e ⁻¹' s = e.symm '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hpreimage]
  exact hs_compact.image e.symm.continuous

/-- Helper for Lemma 5.24.5: each projection from the explicit limit cone is spectral. -/
private theorem isSpectralMap_explicit_projection_of_cofiltered_spectral_diagram
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) (i : I) :
    IsSpectralMap ((TopCat.limitCone F).π.app i) := by
  let C := TopCat.limitCone F
  letI : SpectralSpace C.pt :=
    explicit_spectralSpace_of_cofiltered_spectral_diagram (F := F) hF
  refine ⟨(C.π.app i).hom.continuous, fun s hs_open hs_compact ↦ ?_⟩
  let U : CompactOpens (F.obj i) := ⟨⟨s, hs_compact⟩, hs_open⟩
  simpa [U] using projection_preimage_isCompact_of_compact_open (F := F) hF i U

-- Proof sketch: first prove spectrality for the explicit limit cone `TopCat.limitCone F` by
-- combining the compactness theorem of Lemma `5.24.1` with the compact-open basis and the
-- compatible-family generic-point construction; then transport the resulting spectral structure to
-- the arbitrary limiting cone point `C.pt`.
/-- Lemma 5.24.5: the inverse limit of a cofiltered diagram of spectral spaces with spectral
transition maps is a spectral topological space. -/
theorem spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (hC : IsLimit C)
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥C.pt := by
  let C₀ := TopCat.limitCone F
  letI : SpectralSpace ↥C₀.pt :=
    explicit_spectralSpace_of_cofiltered_spectral_diagram (F := F) hF
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit F) hC)
  -- Transport the spectral ingredients across the canonical homeomorphism from the explicit limit
  -- cone to the chosen limiting cone.
  letI : T0Space C.pt := e.t0Space
  letI : CompactSpace C.pt := e.compactSpace
  letI : QuasiSober C.pt := e.symm.isOpenEmbedding.quasiSober
  letI : QuasiSeparatedSpace C.pt := e.symm.isOpenEmbedding.quasiSeparatedSpace
  letI : PrespectralSpace C.pt := e.symm.isOpenEmbedding.prespectralSpace
  exact SpectralSpace.mk

-- Proof sketch: compare the chosen limiting cone to the explicit limit cone, note that the
-- comparison homeomorphism is spectral, and compose it with the already-proved spectral
-- projection on the explicit cone.
/-- Each projection from a limiting cone of a cofiltered diagram of spectral spaces is a spectral
map. -/
theorem isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
    (hC : IsLimit C) (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) (i : I) :
    IsSpectralMap (C.π.app i) := by
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso hC (TopCat.limitConeIsLimit F))
  have hHomeo : IsSpectralMap e :=
    isSpectralMap_homeomorph e
  have hExplicit : IsSpectralMap ((TopCat.limitCone F).π.app i) :=
    isSpectralMap_explicit_projection_of_cofiltered_spectral_diagram (F := F) hF i
  have hComp : IsSpectralMap (((TopCat.limitCone F).π.app i) ∘ e) :=
    hExplicit.comp hHomeo
  have hEq : (C.π.app i : C.pt → F.obj i) = ((TopCat.limitCone F).π.app i) ∘ e := by
    funext x
    simpa [Function.comp] using
      congrArg (fun g : C.pt ⟶ F.obj i ↦ g x)
        (IsLimit.conePointUniqueUpToIso_hom_comp hC (TopCat.limitConeIsLimit F) i)
  simpa [hEq, Function.comp] using hComp

instance
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥(limit F) :=
  spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (limit.isLimit F) hF

end
