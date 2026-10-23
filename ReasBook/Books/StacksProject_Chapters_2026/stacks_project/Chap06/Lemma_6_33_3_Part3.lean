module

public import stacks_project.Chap06.Lemma_6_33_3_Part2

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}}

local instance : HasLimits (Type w) := inferInstance
local instance : HasColimits (Type w) := inferInstance
local instance : PreservesLimits (forget (Type w)) := inferInstance
local instance : PreservesFilteredColimits (forget (Type w)) :=
  PreservesColimits.preservesFilteredColimits (forget (Type w))
local instance : (forget (Type w)).ReflectsIsomorphisms := inferInstance

variable {C : Type (w + 1)} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

variable {ι : Type u} {U : ι → Opens X}

local notation "algRestrictToOpen" => algebraicRestrictToOpen
local notation "algRestrictToPairLeft" => algebraicRestrictToPairLeft
local notation "algRestrictToPairRight" => algebraicRestrictToPairRight
local notation "algRestrictToTripleFirst" => algebraicRestrictToTripleFirst
local notation "algRestrictToTripleSecond" => algebraicRestrictToTripleSecond
local notation "algRestrictToTripleThird" => algebraicRestrictToTripleThird
local notation "algRestrictOverlapToTripleLeft" => algebraicRestrictOverlapToTripleLeft
local notation "algRestrictOverlapToTripleCenter" =>
  algebraicRestrictOverlapToTripleCenter
local notation "algRestrictOverlapToTripleOuter" =>
  algebraicRestrictOverlapToTripleOuter

/-- Helper for Lemma 6.33.3: the object assigned to a subordinate basis open by the
chosen-chart algebraic basis presheaf. -/
abbrev algebraicOpenCoverBasisPresheafObj
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (W : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ) : C :=
  (localSheaf (chosen_chart W.unop)).1.obj
    (op (subspaceOpenOfLE (chosen_chart_le W.unop)))

/-- Helper for Lemma 6.33.3: the restriction morphism of the chosen-chart algebraic basis
presheaf. It first restricts inside the chart of the larger open and then changes charts over the
smaller open. -/
noncomputable def algebraicOpenCoverBasisPresheafMap
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    {V W : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ} (f : V ⟶ W) :
    algebraicOpenCoverBasisPresheafObj localSheaf V ⟶
      algebraicOpenCoverBasisPresheafObj localSheaf W :=
  let hWV : W.unop.obj ≤ V.unop.obj := f.unop.hom.le
  let hWcV : W.unop.obj ≤ U (chosen_chart V.unop) :=
    hWV.trans (chosen_chart_le V.unop)
  (localSheaf (chosen_chart V.unop)).1.map
      (subspaceOpenHom hWcV (chosen_chart_le V.unop) hWV).op ≫
    (algebraicSubsetChartIso localSheaf overlapIso hWcV (chosen_chart_le W.unop)).hom

/-
Domain-style sampling for Lemma 6.33.3:
- primary domain: sheaf descent on an open cover, specialized to sheaves valued in a category of
  algebraic structures;
- sampled owner declarations:
  `IsAlgebraicStructure`,
  `CategoryTheory.sheafCompose`,
  `SheafOpenCoverGlueing`,
  `SheafOpenCoverGlueing.Realizes`,
  `exists_sheaf_realizing_open_cover_glueing`;
- owner abstraction: the chapter owner remains `SheafOpenCoverGlueing U`, and the algebraic input
  data should only appear through a thin bridge to that owner;
- primitive data: the local `C`-valued sheaves, the pairwise overlap isomorphisms, the cocycle
  condition, and the covering hypothesis;
- derived API: the realization predicate and the existence theorem for a global realizing sheaf.

Source/core/bridge triage:
- `source-facing`: the primitive local sheaves, overlap isomorphisms, cocycle, and cover;
- `core/canonical`: `SheafOpenCoverGlueing U`;
  `bridge/view`: the helper below that forgets along `F` and packages the resulting
  set-valued descent datum in the existing owner. -/
abbrev algebraicToTypes (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf (Type w) (openSubsetSpace U) :=
  letI : PreservesLimits F := inferInstance
  letI : (Opens.grothendieckTopology (openSubsetSpace U)).HasSheafCompose F :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
      (Opens.grothendieckTopology (openSubsetSpace U))
  sheafCompose (Opens.grothendieckTopology (openSubsetSpace U)) F

theorem algebraicOpenSubsetRestrictionCompIso_toTypes_inv
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {T W U : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U) (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (algebraicToTypes F T).map
        ((algebraicOpenSubsetRestrictionCompIso (C := C) hTW hWU).inv.app ℱ) =
      (typeOpenSubsetRestrictionCompIso hTW hWU).inv.app
        ((algebraicToTypes F U).obj ℱ) := by
  apply ObjectProperty.hom_ext
  ext V x
  simp [algebraicToTypes, algebraicOpenSubsetRestrictionCompIso,
    typeOpenSubsetRestrictionCompIso, Topology.IsOpenEmbedding.sheafPullback,
    Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]

theorem algebraicOpenSubsetRestrictionCompIso_toTypes_hom
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {T W U : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U) (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (algebraicToTypes F T).map
        ((algebraicOpenSubsetRestrictionCompIso (C := C) hTW hWU).hom.app ℱ) =
      (typeOpenSubsetRestrictionCompIso hTW hWU).hom.app
        ((algebraicToTypes F U).obj ℱ) := by
  apply ObjectProperty.hom_ext
  ext V x
  simp [algebraicToTypes, algebraicOpenSubsetRestrictionCompIso,
    typeOpenSubsetRestrictionCompIso, Topology.IsOpenEmbedding.sheafPullback,
    Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]

noncomputable def algebraicPairLeftToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    ((algRestrictToPairLeft U V ⋙ algebraicToTypes F (U ⊓ V)).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
        (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  eqToIso rfl

noncomputable def algebraicPairRightToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algRestrictToPairRight U V ⋙ algebraicToTypes F (U ⊓ V)).obj ℱ) ≅
      ((algebraicToTypes F V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  eqToIso rfl

noncomputable def algebraicLeftOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetIntersectionLeftInclusion U V)).obj
        ((algebraicToTypes F U).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  (openEmbeddingSheafPullbackIso (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V)).app
    ((algebraicToTypes F U).obj ℱ)

noncomputable def algebraicRightOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algebraicToTypes F V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
      ℱ) ≅
      (TopCat.Sheaf.pullback (Type w) (openSubsetIntersectionRightInclusion U V)).obj
        ((algebraicToTypes F V).obj ℱ) :=
  ((openEmbeddingSheafPullbackIso (openSubsetIntersectionRightInclusion_isOpenEmbedding U V)).app
    ((algebraicToTypes F V).obj ℱ)).symm

/-- Helper for Lemma 6.33.3: forgetting a direct triple restriction agrees definitionally with
forgetting first and then applying the open-embedding pullback on the triple overlap. -/
noncomputable def algebraicTripleFirstToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    ((algRestrictToTripleFirst U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
        (openSubsetTripleFirstInclusion_isOpenEmbedding U V W).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: forgetting the second direct triple restriction agrees
definitionally with the corresponding open-embedding pullback after forgetting. -/
noncomputable def algebraicTripleSecondToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algRestrictToTripleSecond U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) ≅
      ((algebraicToTypes F V ⋙
        (openSubsetTripleSecondInclusion_isOpenEmbedding U V W).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: forgetting the third direct triple restriction agrees definitionally
with the corresponding open-embedding pullback after forgetting. -/
noncomputable def algebraicTripleThirdToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace W)) :
    ((algRestrictToTripleThird U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) ≅
      ((algebraicToTypes F W ⋙
        (openSubsetTripleThirdInclusion_isOpenEmbedding U V W).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: the direct triple restriction of the first local sheaf has the same
underlying sheaf as the actual pullback along the first triple-overlap inclusion. -/
noncomputable def algebraicTripleFirstOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetTripleFirstInclusion U V W)).obj
        ((algebraicToTypes F U).obj ℱ) ≅
      ((algRestrictToTripleFirst U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) :=
  (openEmbeddingSheafPullbackIso (openSubsetTripleFirstInclusion_isOpenEmbedding U V W)).app
      ((algebraicToTypes F U).obj ℱ) ≪≫
    (algebraicTripleFirstToTypesIso F U V W ℱ).symm

/-- Helper for Lemma 6.33.3: the direct triple restriction of the second local sheaf has the same
underlying sheaf as the actual pullback along the second triple-overlap inclusion. -/
noncomputable def algebraicTripleSecondOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetTripleSecondInclusion U V W)).obj
        ((algebraicToTypes F V).obj ℱ) ≅
      ((algRestrictToTripleSecond U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) :=
  (openEmbeddingSheafPullbackIso (openSubsetTripleSecondInclusion_isOpenEmbedding U V W)).app
      ((algebraicToTypes F V).obj ℱ) ≪≫
    (algebraicTripleSecondToTypesIso F U V W ℱ).symm

/-- Helper for Lemma 6.33.3: the direct triple restriction of the third local sheaf has the same
underlying sheaf as the actual pullback along the third triple-overlap inclusion. -/
noncomputable def algebraicTripleThirdOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace W)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetTripleThirdInclusion U V W)).obj
        ((algebraicToTypes F W).obj ℱ) ≅
      ((algRestrictToTripleThird U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) :=
  (openEmbeddingSheafPullbackIso (openSubsetTripleThirdInclusion_isOpenEmbedding U V W)).app
      ((algebraicToTypes F W).obj ℱ) ≪≫
    (algebraicTripleThirdToTypesIso F U V W ℱ).symm

/-- Helper for Lemma 6.33.3: forgetting an arbitrary internal restriction agrees definitionally
with first restricting in `C` and then forgetting to `Type`. -/
noncomputable def algebraicRestrictionToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {W U : Opens X} (h : W ≤ U)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    ((((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) ⋙ algebraicToTypes F W).obj ℱ) ≅
      (((algebraicToTypes F U) ⋙
        (openSubsetHomOfLE_isOpenEmbedding h).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: the actual pullback of the forgotten sheaf along an internal open
inclusion matches the forgotten `C`-valued restriction. -/
noncomputable def algebraicRestrictionOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {W U : Opens X} (h : W ≤ U)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE h)).obj
        ((algebraicToTypes F U).obj ℱ) ≅
      ((((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) ⋙
          algebraicToTypes F W).obj ℱ) :=
  (openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding h)).app
      ((algebraicToTypes F U).obj ℱ) ≪≫
    (algebraicRestrictionToTypesIso F h ℱ).symm

/-- Helper for Lemma 6.33.3: transporting a forgotten morphism through an internal restriction is
exactly the naturality square of the owner comparison. -/
theorem algebraicRestrictionOwnerIso_naturality
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {W U : Opens X} (h : W ≤ U)
    {ℱ 𝒢 : TopCat.Sheaf C (openSubsetSpace U)} (φ : ℱ ⟶ 𝒢) :
    (algebraicRestrictionOwnerIso F h ℱ).inv ≫
      (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE h)).map
        ((algebraicToTypes F U).map φ) =
    (algebraicToTypes F W).map
      (((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C).map φ) ≫
      (algebraicRestrictionOwnerIso F h 𝒢).inv := by
  -- Route correction: the middle overlap factor should be handled as one naturality square for
  -- the generic owner comparison, not as another path-specific transport chase.
  let e := openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding h)
  -- Peel off the definitional `eqToIso rfl` layer so the goal becomes the naturality square for
  -- the open-embedding pullback comparison itself.
  rw [show (algebraicRestrictionOwnerIso F h ℱ).inv =
      eqToHom rfl ≫ (e.app ((algebraicToTypes F U).obj ℱ)).inv by
        rfl]
  rw [show (algebraicRestrictionOwnerIso F h 𝒢).inv =
      eqToHom rfl ≫ (e.app ((algebraicToTypes F U).obj 𝒢)).inv by
        rfl]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc]
  have hnat := CategoryTheory.NatIso.naturality_1 e ((algebraicToTypes F U).map φ)
  -- Postcompose by the inverse comparison to isolate the imported middle factor.
  have hpost := congrArg
      (fun t ↦ t ≫ (e.app ((algebraicToTypes F U).obj 𝒢)).inv)
      hnat
  change (e.app ((algebraicToTypes F U).obj ℱ)).inv ≫
        (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE h)).map
          ((algebraicToTypes F U).map φ) =
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback (Type w)).map
          ((algebraicToTypes F U).map φ) ≫
        (e.app ((algebraicToTypes F U).obj 𝒢)).inv
  simpa [Category.assoc] using hpost

/-- Helper for Lemma 6.33.3: the imported forward endpoint of a composite internal restriction can
be rewritten to the direct forgotten composite, while keeping the remaining imported owner bridge
to the middle factor explicit. -/
theorem algebraicRestrictionCompToTypes_forwardImportedEndpoint
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {T W U : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U) (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullbackComp (A := Type w) (openSubsetHomOfLE hTW)
        (openSubsetHomOfLE hWU)).inv.app
        ((algebraicToTypes F U).obj ℱ) ≫
      (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
        (algebraicRestrictionOwnerIso F hWU ℱ).hom =
    (algebraicRestrictionOwnerIso F (hTW.trans hWU) ℱ).hom ≫
      (algebraicToTypes F T).map
        ((algebraicOpenSubsetRestrictionCompIso (C := C) hTW hWU).inv.app ℱ) ≫
      (algebraicRestrictionOwnerIso F hTW
        (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ)).inv := by
  -- Route correction: this bridge is stated in the imported-owner spelling that actually survives
  -- after normalizing the triple-overlap path.
  let eWU := algebraicRestrictionOwnerIso F hWU ℱ
  let eTW := algebraicRestrictionOwnerIso F hTW
    (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ)
  let eComp := algebraicRestrictionOwnerIso F (hTW.trans hWU) ℱ
  -- Peel off the definitional `eqToIso rfl` factors so only the genuine pullback comparisons and
  -- the composed internal restriction isomorphism remain.
  rw [show eWU.hom =
      ((openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hWU)).app
          ((algebraicToTypes F U).obj ℱ)).hom ≫
        eqToHom rfl by
        rfl]
  rw [show eTW.inv =
      eqToHom rfl ≫
        ((openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hTW)).app
          ((algebraicToTypes F W).obj
            (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ))).inv by
        rfl]
  rw [show eComp.hom =
      ((openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))).app
          ((algebraicToTypes F U).obj ℱ)).hom ≫
        eqToHom rfl by
        rfl]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]
  have hforward := sheaf_pullback_forward_endpoint
      (openSubsetHomOfLE hTW) (openSubsetHomOfLE hWU) (𝟙 (openSubsetSpace U))
      ((algebraicToTypes F U).obj ℱ)
  rw [algebraicOpenSubsetRestrictionCompIso_toTypes_inv F hTW hWU ℱ]
  let P := TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetHomOfLE hTW) (openSubsetHomOfLE hWU)
  let eWU' :=
    openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hWU)
  let eTW' :=
    openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hTW)
  let eComp' :=
    openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))
  let tComp := typeOpenSubsetRestrictionCompIso hTW hWU
  let G := (algebraicToTypes F U).obj ℱ
  let A :=
    (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
      ((eWU'.app G).hom)
  let B :=
    (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).hom
  let C := (tComp.hom.app G)
  let D := (eComp'.app G).hom
  have hcomp :
      P.hom.app G ≫ D = A ≫ B ≫ C := by
    simpa [P, eWU', eTW', eComp', tComp, G, A, B, C, D] using
      openSubsetHomOfLE_openEmbeddingSheafPullbackIso_comp_hom hTW hWU G
  have hcancel_A :
      A ≫ B ≫ C ≫ (tComp.inv.app G) ≫
          (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv =
        A := by
    calc
      A ≫ B ≫ C ≫ (tComp.inv.app G) ≫
            (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv =
          A ≫ B ≫ (C ≫ (tComp.inv.app G)) ≫
            (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv := by
          simp [Category.assoc]
      _ = A ≫ B ≫ 𝟙 _ ≫
            (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv := by
          simpa only [Category.assoc] using
            congrArg
              (fun k ↦ A ≫ B ≫ k ≫
                (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback
                  (Type w)).obj G)).inv)
              (show C ≫ (tComp.inv.app G) = 𝟙 _ by
                simpa [C] using Iso.hom_inv_id_app tComp G)
      _ = A ≫
            (B ≫
              (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv) := by
          simp [Category.assoc]
      _ = A ≫ 𝟙 _ := by
          rw [show
            B ≫
              (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv =
                𝟙 _ by
            simpa [B] using
              Iso.hom_inv_id_app eTW'
                (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)]
      _ = A := by simp
  have hA : A = P.hom.app G ≫ D ≫ (tComp.inv.app G) ≫
      (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv := by
    calc
      A =
          A ≫ B ≫ C ≫ (tComp.inv.app G) ≫
            (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv := by
            exact hcancel_A.symm
      _ =
          (P.hom.app G ≫ D) ≫ (tComp.inv.app G) ≫
            (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫ (tComp.inv.app G) ≫
                  (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback
                    (Type w)).obj G)).inv)
                hcomp.symm
      _ =
          P.hom.app G ≫ D ≫ (tComp.inv.app G) ≫
            (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv := by
            simp [Category.assoc]
  have hcancel_P :
      P.inv.app G ≫ P.hom.app G = 𝟙 _ := by
    simpa using Iso.inv_hom_id_app P G
  calc
    P.inv.app G ≫ A =
        P.inv.app G ≫
          (P.hom.app G ≫ D ≫ (tComp.inv.app G) ≫
            (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv) := by
          rw [hA]
    _ =
        D ≫ (tComp.inv.app G) ≫
          (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv := by
          simpa [P, openSubsetHomOfLE_comp, Category.assoc] using
            congrArg
              (fun k ↦ k ≫ D ≫ (tComp.inv.app G) ≫
                (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback
                  (Type w)).obj G)).inv)
              hcancel_P

/-- Helper for Lemma 6.33.3: the imported inverse endpoint of a composite internal restriction
rewrites to the inverse of the direct forgotten composite, again keeping the middle imported owner
transport explicit. -/
theorem algebraicRestrictionCompToTypes_inverseImportedEndpoint
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {T W U : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U) (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (algebraicRestrictionOwnerIso F hTW
        (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ)).inv ≫
      (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
        (algebraicRestrictionOwnerIso F hWU ℱ).inv ≫
      (TopCat.Sheaf.pullbackComp (A := Type w) (openSubsetHomOfLE hTW)
          (openSubsetHomOfLE hWU)).hom.app
        ((algebraicToTypes F U).obj ℱ) =
    (algebraicToTypes F T).map
      ((algebraicOpenSubsetRestrictionCompIso (C := C) hTW hWU).hom.app ℱ) ≫
      (algebraicRestrictionOwnerIso F (hTW.trans hWU) ℱ).inv := by
  -- Route correction: the same imported-owner transport appears on the right endpoint, so it is
  -- isolated once here instead of being re-expanded in each overlap leg.
  let eWU := algebraicRestrictionOwnerIso F hWU ℱ
  let eTW := algebraicRestrictionOwnerIso F hTW
    (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ)
  let eComp := algebraicRestrictionOwnerIso F (hTW.trans hWU) ℱ
  rw [show eWU.inv =
      eqToHom rfl ≫
        ((openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hWU)).app
          ((algebraicToTypes F U).obj ℱ)).inv by
        rfl]
  rw [show eTW.inv =
      eqToHom rfl ≫
        ((openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hTW)).app
          ((algebraicToTypes F W).obj
            (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ))).inv by
        rfl]
  rw [show eComp.inv =
      eqToHom rfl ≫
        ((openEmbeddingSheafPullbackIso
          (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))).app
          ((algebraicToTypes F U).obj ℱ)).inv by
        rfl]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]
  rw [algebraicOpenSubsetRestrictionCompIso_toTypes_hom F hTW hWU ℱ]
  let P := TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetHomOfLE hTW) (openSubsetHomOfLE hWU)
  let eWU' :=
    openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hWU)
  let eTW' :=
    openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding hTW)
  let eComp' :=
    openEmbeddingSheafPullbackIso (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))
  let tComp := typeOpenSubsetRestrictionCompIso hTW hWU
  let G := (algebraicToTypes F U).obj ℱ
  let A :=
    (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
      ((eWU'.app G).hom)
  let Ainv :=
    (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
      ((eWU'.app G).inv)
  let B :=
    (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).hom
  let Binv :=
    (eTW'.app (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)).inv
  let C := (tComp.hom.app G)
  let D := (eComp'.app G).hom
  let Dinv := (eComp'.app G).inv
  have hcomp :
      P.hom.app G ≫ D = A ≫ B ≫ C := by
    simpa [P, eWU', eTW', eComp', tComp, G, A, B, C, D] using
      openSubsetHomOfLE_openEmbeddingSheafPullbackIso_comp_hom hTW hWU G
  have hD_cancel : D ≫ Dinv = 𝟙 _ := by
    simpa [D, Dinv] using Iso.hom_inv_id_app eComp' G
  have hPD : P.hom.app G = (P.hom.app G ≫ D) ≫ Dinv := by
    simpa [P, openSubsetHomOfLE_comp, Category.assoc] using
      congrArg (fun k ↦ P.hom.app G ≫ k) hD_cancel.symm
  have hP : P.hom.app G = A ≫ B ≫ C ≫ Dinv := by
    have hP' : (P.hom.app G ≫ D) ≫ Dinv = (A ≫ B ≫ C) ≫ Dinv := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ Dinv) hcomp
    have hAssoc : (A ≫ B ≫ C) ≫ Dinv = A ≫ B ≫ C ≫ Dinv := by
      simp [Category.assoc]
    exact hPD.trans (hP'.trans hAssoc)
  have hA_cancel : Ainv ≫ A = 𝟙 _ := by
    simpa [Ainv, A, Functor.map_comp] using
      congrArg
        (fun k ↦ (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map k)
        (Iso.inv_hom_id_app eWU' G)
  have hB_cancel : Binv ≫ B = 𝟙 _ := by
    simpa [Binv, B] using
      Iso.inv_hom_id_app eTW'
        (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G)
  have h0 :
      Binv ≫ Ainv ≫ P.hom.app G =
        Binv ≫ Ainv ≫ (A ≫ B ≫ C ≫ Dinv) := by
    rw [hP]
    rfl
  have h1 :
      Binv ≫ Ainv ≫ (A ≫ B ≫ C ≫ Dinv) =
        Binv ≫ (Ainv ≫ A) ≫ B ≫ C ≫ Dinv := by
    simp [Category.assoc]
  have h2 :
      Binv ≫ (Ainv ≫ A) ≫ B ≫ C ≫ Dinv =
        Binv ≫ B ≫ C ≫ Dinv := by
    rw [hA_cancel]
    simp [Category.assoc]
  have h3 : Binv ≫ B ≫ C ≫ Dinv = C ≫ Dinv := by
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ C ≫ Dinv) hB_cancel
  exact h0.trans (h1.trans (h2.trans h3))

/-- Helper for Lemma 6.33.3: the explicit forgotten `12` overlap path is the direct triple-owner
transport of the forgotten algebraic `12` comparison. -/
theorem algebraicTripleOverlapHom12_middle_toTypes
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullback (Type w)
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom =
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) := by
  -- The pair-to-Types comparisons are definitional, so the pulled-back middle transport reduces
  -- to the forgotten overlap morphism on the pair restriction.
  have hLeft :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv =
      𝟙 _ := by
    rw [show (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map_id
        ((algebraicToTypes F (U i) ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U j)).sheafPullback
            (Type w)).obj (localSheaf i)))
  have hRight :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom =
      𝟙 _ := by
    rw [show (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map_id
        ((algRestrictToPairRight (U i) (U j) ⋙ algebraicToTypes F (U i ⊓ U j)).obj
          (localSheaf j)))
  -- After rewriting both pulled-back comparison maps to identities, only the central overlap map
  -- remains.
  rw [hLeft]
  simpa [Category.assoc] using
    congrArg
      (fun t ↦
        𝟙 _ ≫
          (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
            ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) ≫
          t)
      hRight

/-- Helper for Lemma 6.33.3: forgetting the algebraic `12` overlap comparison preserves its
three-factor decomposition before any owner transport is inserted. -/
theorem algebraicTripleOverlapHom12_mappedPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
        (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).mapIso
            (overlapIso i j)).hom) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app (localSheaf j)) := by
  -- Expand the mapped algebraic path once so later transport lemmas only have to compare owner
  -- spellings, not refactor the algebraic composite again.
  rw [algebraicTripleOverlapHom12, Functor.map_comp, Functor.map_comp]

theorem algebraicTripleOverlapHom12_toTypesPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type w)
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U j))).inv.app
        ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicLeftOwnerIso F (U i) (U j) (localSheaf i)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicRightOwnerIso F (U i) (U j) (localSheaf j)).hom ≫
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U j))).hom.app
        ((algebraicToTypes F (U j)).obj (localSheaf j)) =
      (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) ≫
        (algebraicTripleSecondOwnerIso F (U i) (U j) (U k) (localSheaf j)).inv := by
  -- Expand the mapped algebraic `12` path first, so the only remaining work is the two owner
  -- endpoint comparisons against the imported `pullbackComp` spelling.
  rw [algebraicTripleOverlapHom12_mappedPath]
  -- TODO: assemble the rewritten path by first normalizing the two adjacent imported owner maps
  -- to `algebraicRestrictionOwnerIso`, then apply the three generic bridge lemmas
  -- `algebraicRestrictionCompToTypes_forwardImportedEndpoint`,
  -- `algebraicRestrictionOwnerIso_naturality`, and
  -- `algebraicRestrictionCompToTypes_inverseImportedEndpoint` with `congrArg`-based association
  -- wrappers. The remaining blocker is rewrite targeting, not a new mathematical identity.
  have hLeftOwner :
      (algebraicLeftOwnerIso F (U i) (U j) (localSheaf i)).hom =
        (algebraicRestrictionOwnerIso F
          (show U i ⊓ U j ≤ U i from inf_le_left) (localSheaf i)).hom := by
    rfl
  have hRightOwner :
      (algebraicRightOwnerIso F (U i) (U j) (localSheaf j)).hom =
        (algebraicRestrictionOwnerIso F
          (show U i ⊓ U j ≤ U j from inf_le_right) (localSheaf j)).inv := by
    rfl
  have hTripleFirstOwner :
      (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom =
        (algebraicRestrictionOwnerIso F
          ((show U i ⊓ U j ⊓ U k ≤ U i ⊓ U j from inf_le_left).trans
            (show U i ⊓ U j ≤ U i from inf_le_left))
          (localSheaf i)).hom := by
    rfl
  have hTripleSecondOwner :
      (algebraicTripleSecondOwnerIso F (U i) (U j) (U k) (localSheaf j)).inv =
        (algebraicRestrictionOwnerIso F
          ((show U i ⊓ U j ⊓ U k ≤ U i ⊓ U j from inf_le_left).trans
            (show U i ⊓ U j ≤ U j from inf_le_right))
          (localSheaf j)).inv := by
    rfl
  let hTij : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  let hIij : U i ⊓ U j ≤ U i := inf_le_left
  let hJij : U i ⊓ U j ≤ U j := inf_le_right
  have hTripleToPairLeft :
      openSubsetTripleToPairLeftInclusion (U i) (U j) (U k) =
        openSubsetHomOfLE hTij := by
    rfl
  have hPairLeft :
      openSubsetIntersectionLeftInclusion (U i) (U j) =
        openSubsetHomOfLE hIij := by
    rfl
  have hPairRight :
      openSubsetIntersectionRightInclusion (U i) (U j) =
        openSubsetHomOfLE hJij := by
    rfl
  have hForward12 :
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U i) (U j))).inv.app
          ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
        (TopCat.Sheaf.pullback (Type w)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
          (algebraicRestrictionOwnerIso F hIij (localSheaf i)).hom =
      (algebraicRestrictionOwnerIso F (hTij.trans hIij) (localSheaf i)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
            (localSheaf i)) ≫
        (algebraicRestrictionOwnerIso F hTij
          (((openSubsetHomOfLE_isOpenEmbedding hIij).sheafPullback C).obj
            (localSheaf i))).inv := by
    simpa [hTij, hIij, openSubsetTripleToPairLeftInclusion,
      openSubsetIntersectionLeftInclusion, openSubsetTripleFirstInclusion,
      algebraicRestrictToTripleFirstViaIJIso, Category.assoc] using
      algebraicRestrictionCompToTypes_forwardImportedEndpoint F hTij hIij (localSheaf i)
  have hNat12 :
      (algebraicRestrictionOwnerIso F hTij
          (((openSubsetHomOfLE_isOpenEmbedding hIij).sheafPullback C).obj
            (localSheaf i))).inv ≫
        (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
          ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).map
            (overlapIso i j).hom) ≫
        (algebraicRestrictionOwnerIso F hTij
          (((openSubsetHomOfLE_isOpenEmbedding hJij).sheafPullback C).obj
            (localSheaf j))).inv := by
    simpa only [hTij, hIij, hJij, openSubsetTripleToPairLeftInclusion,
      algebraicRestrictOverlapToTripleLeft] using
      algebraicRestrictionOwnerIso_naturality F hTij (overlapIso i j).hom
  have hInverse12 :
      (algebraicRestrictionOwnerIso F hTij
          (((openSubsetHomOfLE_isOpenEmbedding hJij).sheafPullback C).obj
            (localSheaf j))).inv ≫
        (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
          (algebraicRestrictionOwnerIso F hJij (localSheaf j)).inv ≫
        (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U j))).hom.app
          ((algebraicToTypes F (U j)).obj (localSheaf j)) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app
            (localSheaf j)) ≫
        (algebraicRestrictionOwnerIso F (hTij.trans hJij) (localSheaf j)).inv := by
    simpa [hTij, hJij, openSubsetTripleToPairLeftInclusion,
      openSubsetIntersectionRightInclusion, openSubsetTripleSecondInclusion,
      algebraicRestrictToTripleSecondViaIJIso, Category.assoc] using
      algebraicRestrictionCompToTypes_inverseImportedEndpoint F hTij hJij (localSheaf j)
  have hMiddle12 :=
    algebraicTripleOverlapHom12_middle_toTypes F localSheaf overlapIso i j k
  let midI :=
    (algebraicRestrictionOwnerIso F hTij
      (((openSubsetHomOfLE_isOpenEmbedding hIij).sheafPullback C).obj
        (localSheaf i))).inv
  let midJ :=
    (algebraicRestrictionOwnerIso F hTij
      (((openSubsetHomOfLE_isOpenEmbedding hJij).sheafPullback C).obj
        (localSheaf j))).inv
  let pairL :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv
  let overlapPair :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
      ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom)
  let pairR :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
      (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom
  let rightOwner :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
      (algebraicRestrictionOwnerIso F hJij (localSheaf j)).inv
  let rightComp :=
    (TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U j))).hom.app
      ((algebraicToTypes F (U j)).obj (localSheaf j))
  let overlapTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).map
        (overlapIso i j).hom)
  let secondTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app
        (localSheaf j))
  let directJ := (algebraicRestrictionOwnerIso F (hTij.trans hJij) (localSheaf j)).inv
  let forwardStart :=
    (TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U j))).inv.app
      ((algebraicToTypes F (U i)).obj (localSheaf i))
  let forwardOwner :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
      (algebraicRestrictionOwnerIso F hIij (localSheaf i)).hom
  let directI := (algebraicRestrictionOwnerIso F (hTij.trans hIij) (localSheaf i)).hom
  let firstTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
        (localSheaf i))
  have hForwardWrapped :
      forwardStart ≫ forwardOwner = directI ≫ firstTriple ≫ midI := by
    dsimp [forwardStart, forwardOwner, directI, firstTriple, midI]
    simpa only [Category.assoc] using hForward12
  have hMiddleWrapped :
      midI ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp =
        midI ≫ overlapPair ≫ rightOwner ≫ rightComp := by
    dsimp [midI, pairL, overlapPair, pairR, rightOwner, rightComp]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          (algebraicRestrictionOwnerIso F hTij
            (((openSubsetHomOfLE_isOpenEmbedding hIij).sheafPullback C).obj
              (localSheaf i))).inv ≫ t ≫
            (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
              (algebraicRestrictionOwnerIso F hJij (localSheaf j)).inv ≫
            (TopCat.Sheaf.pullbackComp (A := Type w)
              (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
              (openSubsetIntersectionRightInclusion (U i) (U j))).hom.app
              ((algebraicToTypes F (U j)).obj (localSheaf j)))
        hMiddle12
  have hNatWrapped :
      midI ≫ overlapPair ≫ rightOwner ≫ rightComp =
        overlapTriple ≫ midJ ≫ rightOwner ≫ rightComp := by
    dsimp [midI, overlapPair, overlapTriple, midJ, rightOwner, rightComp]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦ t ≫
          (TopCat.Sheaf.pullback (Type w)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
            (algebraicRestrictionOwnerIso F hJij (localSheaf j)).inv ≫
          (TopCat.Sheaf.pullbackComp (A := Type w)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetIntersectionRightInclusion (U i) (U j))).hom.app
            ((algebraicToTypes F (U j)).obj (localSheaf j)))
        hNat12
  have hInverseWrapped :
      overlapTriple ≫ midJ ≫ rightOwner ≫ rightComp =
        overlapTriple ≫ secondTriple ≫ directJ := by
    dsimp [overlapTriple, midJ, rightOwner, rightComp, secondTriple, directJ]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            ((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).map
              (overlapIso i j).hom) ≫ t)
        hInverse12
  have hAssembled :
      forwardStart ≫ forwardOwner ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫
          rightComp =
        directI ≫ firstTriple ≫ overlapTriple ≫ secondTriple ≫ directJ := by
    have h0 :
        forwardStart ≫ forwardOwner ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫
            rightComp =
          (directI ≫ firstTriple ≫ midI) ≫ pairL ≫ overlapPair ≫ pairR ≫
            rightOwner ≫ rightComp := by
      simpa only [Category.assoc] using
        congrArg
          (fun t ↦ t ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp)
          hForwardWrapped
    have h1 :
        (directI ≫ firstTriple ≫ midI) ≫ pairL ≫ overlapPair ≫ pairR ≫
            rightOwner ≫ rightComp =
          directI ≫ firstTriple ≫
            (midI ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp) := by
      simp only [Category.assoc]
    have h2 :
        directI ≫ firstTriple ≫
            (midI ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp) =
          directI ≫ firstTriple ≫
            (midI ≫ overlapPair ≫ rightOwner ≫ rightComp) := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ directI ≫ firstTriple ≫ t) hMiddleWrapped
    have h3 :
        directI ≫ firstTriple ≫
            (midI ≫ overlapPair ≫ rightOwner ≫ rightComp) =
          directI ≫ firstTriple ≫
            (overlapTriple ≫ secondTriple ≫ directJ) := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ directI ≫ firstTriple ≫ t)
          (hNatWrapped.trans hInverseWrapped)
    have h4 :
        directI ≫ firstTriple ≫ (overlapTriple ≫ secondTriple ≫ directJ) =
          directI ≫ firstTriple ≫ overlapTriple ≫ secondTriple ≫ directJ := by
      simp only [Category.assoc]
    exact h0.trans (h1.trans (h2.trans (h3.trans h4)))
  rw [hLeftOwner, hRightOwner, hTripleFirstOwner, hTripleSecondOwner]
  simpa only [forwardStart, forwardOwner, directI, firstTriple, midI, pairL, overlapPair,
    pairR, rightOwner, rightComp, overlapTriple, secondTriple, directJ,
    Functor.mapIso_hom, Category.assoc] using hAssembled

end
