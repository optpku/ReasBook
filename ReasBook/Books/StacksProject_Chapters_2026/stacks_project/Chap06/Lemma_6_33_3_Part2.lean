module

public import stacks_project.Chap06.Lemma_6_33_3_RingPullbackAux

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

variable {C : Type (w + 1)} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

variable {ι : Type u} {U : ι → Opens X}

instance algebraicBasisExtension_hasLimitsOfShape
    (B : Set (Opens X)) [HasLimitsOfSize.{w, w} C] :
    ∀ U₀ : (Opens X)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow U₀ (basisOpenInclusion B).op) C := by
  intro U₀
  exact HasLimitsOfSize.has_limits_of_shape
    (C := C) (StructuredArrow U₀ (basisOpenInclusion B).op)

noncomputable abbrev algebraicBasisSiteSheafComparisonEquiv
    {Y : TopCat.{w}} {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    [HasLimitsOfSize.{w, w} C] :
    BasisSiteSheaf C B hB ≌ TopCat.Sheaf C Y := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hB
  exact
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology Y) C

noncomputable def algebraicBasisSiteRestrictFromSheaf
    {Y : TopCat.{w}} {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    [HasLimitsOfSize.{w, w} C]
    (Fext : TopCat.Sheaf C Y) : BasisSiteSheaf C B hB where
  obj := (basisOpenInclusion B).op ⋙ Fext.1
  property := by
    simpa [algebraicBasisSiteSheafComparisonEquiv] using
      ((algebraicBasisSiteSheafComparisonEquiv (C := C) hB).inverse.obj Fext).property

noncomputable abbrev algebraicBasisSiteIsoExtendOfRestrictIso
    {Y : TopCat.{w}} {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    [HasLimitsOfSize.{w, w} C]
    (F : BasisSiteSheaf C B hB)
    (Fext : TopCat.Sheaf C Y)
    (e : algebraicBasisSiteRestrictFromSheaf (C := C) hB Fext ≅ F) :
    Fext ≅ F.extend :=
  let e' : (algebraicBasisSiteSheafComparisonEquiv (C := C) hB).inverse.obj Fext ≅ F := by
    simpa [algebraicBasisSiteRestrictFromSheaf, algebraicBasisSiteSheafComparisonEquiv] using e
  ((algebraicBasisSiteSheafComparisonEquiv (C := C) hB).counitIso.app Fext).symm ≪≫
    (algebraicBasisSiteSheafComparisonEquiv (C := C) hB).functor.mapIso e'

/-- Helper for Lemma 6.33.3: the basis of opens contained in one member of the cover. -/
def coverSubordinateOpens : Set (Opens X) :=
  { W | ∃ i, W ≤ U i }

/-- Helper for Lemma 6.33.3: the subordinate opens form a topological basis. -/
theorem cover_subordinate_opens_isBasis (hU : IsOpenCover U) :
    Opens.IsBasis (coverSubordinateOpens (U := U)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  refine ⟨V ⊓ U i, ?_, ?_, inf_le_left⟩
  · exact ⟨i, inf_le_right⟩
  · exact ⟨hx, hxi⟩

/-- Helper for Lemma 6.33.3: choose one chart containing a subordinate basis open. -/
noncomputable abbrev chosen_chart
    (W : BasisOpen (coverSubordinateOpens (U := U))) : ι :=
  Classical.choose W.property

/-- Helper for Lemma 6.33.3: the chosen chart indeed contains the subordinate basis open. -/
theorem chosen_chart_le
    (W : BasisOpen (coverSubordinateOpens (U := U))) :
    W.obj ≤ U (chosen_chart W) :=
  Classical.choose_spec W.property

/-- Helper for Lemma 6.33.3: if `W` is contained in two cover members, it is contained in their
overlap. -/
def subset_overlap_le
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j) :
    W ≤ U i ⊓ U j := fun _ hx ↦ ⟨hWi hx, hWj hx⟩

/-- Helper for Lemma 6.33.3: if `W` is contained in three cover members, it is contained in their
triple overlap. -/
theorem subset_triple_overlap_le
    {W : Opens X} {i j k : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) (hWk : W ≤ U k) :
    W ≤ U i ⊓ U j ⊓ U k := by
  intro x hx
  exact ⟨⟨hWi hx, hWj hx⟩, hWk hx⟩

abbrev algebraicRestrictToOpen (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace U) :=
  U.isOpenEmbedding.sheafPullback C

abbrev algebraicRestrictToPairLeft (U V : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) :=
  (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback C

abbrev algebraicRestrictToPairRight (U V : Opens X) :
    TopCat.Sheaf C (openSubsetSpace V) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) :=
  (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback C

abbrev algebraicRestrictToTripleFirst (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleFirstInclusion_isOpenEmbedding U V W).sheafPullback C

abbrev algebraicRestrictToTripleSecond (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace V) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleSecondInclusion_isOpenEmbedding U V W).sheafPullback C

abbrev algebraicRestrictToTripleThird (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace W) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleThirdInclusion_isOpenEmbedding U V W).sheafPullback C

abbrev algebraicRestrictOverlapToTripleLeft (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairLeftInclusion_isOpenEmbedding U V W).sheafPullback C

abbrev algebraicRestrictOverlapToTripleCenter (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairCenterInclusion_isOpenEmbedding U V W).sheafPullback C

abbrev algebraicRestrictOverlapToTripleOuter (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairOuterInclusion_isOpenEmbedding U V W).sheafPullback C

noncomputable def openSubsetHomOfLEFunctorCompIso
    {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    (openSubsetHomOfLE_isOpenEmbedding hTW).functor ⋙
        (openSubsetHomOfLE_isOpenEmbedding hWU).functor ≅
      (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor :=
  NatIso.ofComponents
    (fun V ↦ eqToIso (by
      ext x
      change x ∈
          (((openSubsetHomOfLE_isOpenEmbedding hWU).functor.obj
              ((openSubsetHomOfLE_isOpenEmbedding hTW).functor.obj V)) : Set _) ↔
        x ∈ (((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor.obj V) : Set _)
      constructor
      · rintro ⟨x₁, hx₁, hx⟩
        rcases (by
          simpa [Topology.IsOpenEmbedding.functor] using hx₁) with ⟨t, htV, rfl⟩
        exact ⟨t, htV, by simpa using hx⟩
      · rintro ⟨t, htV, hx⟩
        refine ⟨(openSubsetHomOfLE hTW) t, ?_, by simpa using hx⟩
        simpa [Topology.IsOpenEmbedding.functor] using ⟨t, htV, rfl⟩))
    (fun {_ _} _ ↦ by apply Subsingleton.elim)

/-- Helper for Lemma 6.33.3: the functors on opens attached to nested open inclusions compose
to the functor for the composite inclusion. -/
theorem openSubsetHomOfLEFunctorCompEq
    {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    (openSubsetHomOfLE_isOpenEmbedding hTW).functor ⋙
        (openSubsetHomOfLE_isOpenEmbedding hWU).functor =
      (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro V
    ext x
    change x ∈
        (((openSubsetHomOfLE_isOpenEmbedding hWU).functor.obj
            ((openSubsetHomOfLE_isOpenEmbedding hTW).functor.obj V)) : Set _) ↔
      x ∈ (((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor.obj V) : Set _)
    constructor
    · rintro ⟨x₁, hx₁, hx⟩
      rcases (by
        simpa [Topology.IsOpenEmbedding.functor] using hx₁) with ⟨t, htV, rfl⟩
      exact ⟨t, htV, by simpa using hx⟩
    · rintro ⟨t, htV, hx⟩
      refine ⟨(openSubsetHomOfLE hTW) t, ?_, by simpa using hx⟩
      simpa [Topology.IsOpenEmbedding.functor] using ⟨t, htV, rfl⟩
  · intro V W i
    apply Subsingleton.elim

/-- Helper for Lemma 6.33.3: for composable open embeddings, the image-open functor for the
composite is the composite of the two image-open functors. -/
theorem openEmbeddingFunctorCompEq
    {Y Z T : TopCat.{w}} {f : Y ⟶ Z} {g : Z ⟶ T}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (hfg : IsOpenEmbedding (f ≫ g)) :
    hf.functor ⋙ hg.functor = hfg.functor := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro V
    ext t
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  · intro V W i
    apply Subsingleton.elim

/-- Helper for Lemma 6.33.3: the naive sheaf pullback for a composite open embedding is the
composition of the naive sheaf pullbacks for the two open embeddings. -/
noncomputable def openEmbeddingSheafPullbackCompIso
    {Y Z T : TopCat.{w}} {f : Y ⟶ Z} {g : Z ⟶ T}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (hfg : IsOpenEmbedding (f ≫ g)) :
    hg.sheafPullback (Type w) ⋙ hf.sheafPullback (Type w) ≅
      hfg.sheafPullback (Type w) :=
  haveI := hf.functor_isContinuous
  haveI := hg.functor_isContinuous
  haveI := hfg.functor_isContinuous
  Functor.sheafPushforwardContinuousComp'
    (eFG := eqToIso (openEmbeddingFunctorCompEq hf hg hfg))
    (Type w)
    (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology Z)
    (Opens.grothendieckTopology T)

noncomputable def algebraicOpenSubsetRestrictionCompIso
    {C : Type (w + 1)} [Category.{w} C] {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    ((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding hTW).sheafPullback C) ≅
      ((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).sheafPullback C) := by
  -- Normalize the composite open-embedding pullback to the pullback along the composite map.
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding hTW)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding hWU)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))
  simpa [Topology.IsOpenEmbedding.sheafPullback] using
    (CategoryTheory.Functor.sheafPushforwardContinuousComp'
      (F := (openSubsetHomOfLE_isOpenEmbedding hTW).functor)
      (G := (openSubsetHomOfLE_isOpenEmbedding hWU).functor)
      (FG := (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor)
      (eFG := eqToIso (openSubsetHomOfLEFunctorCompEq hTW hWU))
      C
      (Opens.grothendieckTopology (openSubsetSpace T))
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U)))

/-- Helper for Lemma 6.33.3: the direct section comparison for `A ⊆ B ⊆ D ⊆ E` factors
through the left endpoint of the open-subspace pullback-composition comparison. -/
theorem openSubsetHomOfLEOpenEmbeddingSectionIso_forward_endpoint_compare
    {C : Type (w + 1)} [Category.{w} C]
    {A B D E : Opens X} (hAB : A ≤ B) (hBD : B ≤ D) (hDE : D ≤ E)
    (ℱ : TopCat.Sheaf C (openSubsetSpace E)) :
    (openSubsetHomOfLEOpenEmbeddingSectionIso hAB (hBD.trans hDE) ℱ).hom ≫
      (openSubsetHomOfLEOpenEmbeddingSectionIso (hAB.trans hBD) hDE ℱ).inv =
    (((algebraicOpenSubsetRestrictionCompIso (C := C) hBD hDE).symm.hom.app ℱ).hom.app
        (op (subspaceOpenOfLE hAB))) ≫
      (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD
        (((openSubsetHomOfLE_isOpenEmbedding hDE).sheafPullback C).obj ℱ)).hom := by
  simp [openSubsetHomOfLEOpenEmbeddingSectionIso, algebraicOpenSubsetRestrictionCompIso,
    Topology.IsOpenEmbedding.sheafPullback, eqToHom_map]

/-- Helper for Lemma 6.33.3: the inverse endpoint of the open-subspace pullback-composition
comparison recovers the right-hand section comparison. -/
theorem openSubsetHomOfLEOpenEmbeddingSectionIso_inverse_endpoint_compare
    {C : Type (w + 1)} [Category.{w} C]
    {A B D E : Opens X} (hAB : A ≤ B) (hBD : B ≤ D) (hDE : D ≤ E)
    (ℱ : TopCat.Sheaf C (openSubsetSpace E)) :
    (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD
        (((openSubsetHomOfLE_isOpenEmbedding hDE).sheafPullback C).obj ℱ)).inv ≫
      (((algebraicOpenSubsetRestrictionCompIso (C := C) hBD hDE).symm.inv.app ℱ).hom.app
        (op (subspaceOpenOfLE hAB))) =
    (openSubsetHomOfLEOpenEmbeddingSectionIso (hAB.trans hBD) hDE ℱ).hom ≫
      (openSubsetHomOfLEOpenEmbeddingSectionIso hAB (hBD.trans hDE) ℱ).inv := by
  simp [openSubsetHomOfLEOpenEmbeddingSectionIso, algebraicOpenSubsetRestrictionCompIso,
    Topology.IsOpenEmbedding.sheafPullback, eqToHom_map]

noncomputable def typeOpenSubsetRestrictionCompIso
    {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    ((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding hTW).sheafPullback (Type w)) ≅
      ((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).sheafPullback (Type w)) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding hTW)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding hWU)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))
  simpa [Topology.IsOpenEmbedding.sheafPullback] using
    (CategoryTheory.Functor.sheafPushforwardContinuousComp'
      (F := (openSubsetHomOfLE_isOpenEmbedding hTW).functor)
      (G := (openSubsetHomOfLE_isOpenEmbedding hWU).functor)
      (FG := (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor)
      (eFG := eqToIso (openSubsetHomOfLEFunctorCompEq hTW hWU))
      (Type w)
      (Opens.grothendieckTopology (openSubsetSpace T))
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U)))

theorem typeOpenSubsetRestrictionCompIso_hom_eq_generic
    {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U)
    (G : TopCat.Sheaf (Type w) (openSubsetSpace U)) :
    (typeOpenSubsetRestrictionCompIso hTW hWU).hom.app G =
      (openEmbeddingSheafPullbackCompIso
        (openSubsetHomOfLE_isOpenEmbedding hTW)
        (openSubsetHomOfLE_isOpenEmbedding hWU)
        (by
          simpa [openSubsetHomOfLE_comp] using
            (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)))).hom.app G := by
  apply ObjectProperty.hom_ext
  ext V x
  simp [typeOpenSubsetRestrictionCompIso, openEmbeddingSheafPullbackCompIso,
    Topology.IsOpenEmbedding.sheafPullback,
    Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]
  congr 1

/-- Helper for Lemma 6.33.3: the open-embedding pullback comparison chosen by uniqueness of
left adjoints. This avoids expanding the concrete sheafification model of mathlib's
`IsOpenEmbedding.sheafPullbackIso` in the algebraic descent transport proofs. -/
noncomputable def openEmbeddingSheafPullbackIso
    {Y Z : TopCat.{w}} {f : Y ⟶ Z} (hf : IsOpenEmbedding f) :
    TopCat.Sheaf.pullback (Type w) f ≅ hf.sheafPullback (Type w) := by
  haveI := hf.functor_isContinuous
  exact
    Adjunction.leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
      (hf.isOpenMap.adjunction.sheafPushforwardContinuous
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Z))

/-- The uniqueness-based open-embedding pullback comparison for ring-valued sheaves. This is the
ring-valued analogue of `openEmbeddingSheafPullbackIso`, chosen so adjunction units and counits
normalize by the generic `leftAdjointUniq` API. -/
noncomputable def openEmbeddingSheafPullbackIsoRing
    {Y Z : TopCat.{w}} {f : Y ⟶ Z} (hf : IsOpenEmbedding f) :
    TopCat.Sheaf.pullback RingCat f ≅ hf.sheafPullback RingCat := by
  haveI := hf.functor_isContinuous
  exact
    Adjunction.leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f)
      (hf.isOpenMap.adjunction.sheafPushforwardContinuous
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Z))

/-- Helper for Lemma 6.33.3: the uniqueness-based open-embedding pullback comparison is
compatible with composition of open embeddings. -/
theorem openEmbeddingSheafPullbackIso_comp_hom
    {Y Z T : TopCat.{w}} {f : Y ⟶ Z} {g : Z ⟶ T}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (hfg : IsOpenEmbedding (f ≫ g))
    (G : T.Sheaf (Type w)) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app G ≫
      (openEmbeddingSheafPullbackIso hfg).hom.app G =
    (TopCat.Sheaf.pullback (Type w) f).map
        ((openEmbeddingSheafPullbackIso hg).hom.app G) ≫
      (openEmbeddingSheafPullbackIso hf).hom.app
        (((hg.sheafPullback (Type w)).obj G)) ≫
        (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G := by
  haveI := hf.functor_isContinuous
  haveI := hg.functor_isContinuous
  haveI := hfg.functor_isContinuous
  let adjActualG := TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g
  let adjActualF := TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f
  let adjActualDirect := TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g)
  let adjNaiveG :
      hg.sheafPullback (Type w) ⊣ TopCat.Sheaf.pushforward (Type w) g :=
    hg.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Z)
      (Opens.grothendieckTopology T)
  let adjNaiveF :
      hf.sheafPullback (Type w) ⊣ TopCat.Sheaf.pushforward (Type w) f :=
    hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z)
  let adjNaiveDirect :
      hfg.sheafPullback (Type w) ⊣ TopCat.Sheaf.pushforward (Type w) (f ≫ g) :=
    hfg.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology T)
  let adjActualComp := adjActualG.comp adjActualF
  let adjMixedComp := adjNaiveG.comp adjActualF
  let adjNaiveComp := adjNaiveG.comp adjNaiveF
  have hleft :
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app G ≫
        (openEmbeddingSheafPullbackIso hfg).hom.app G =
      (Adjunction.leftAdjointUniq adjActualComp adjNaiveDirect).hom.app G := by
    simpa [adjActualComp, adjActualG, adjActualF, adjActualDirect, adjNaiveDirect,
      openEmbeddingSheafPullbackIso, sheafPullbackComp_def, Category.assoc] using
      (Adjunction.leftAdjointUniq_trans_app
        adjActualComp adjActualDirect adjNaiveDirect G)
  have hgreplace :
      (TopCat.Sheaf.pullback (Type w) f).map
          ((openEmbeddingSheafPullbackIso hg).hom.app G) =
      (Adjunction.leftAdjointUniq adjActualComp adjMixedComp).hom.app G := by
    simpa [adjActualComp, adjMixedComp, adjActualG, adjActualF, adjNaiveG,
      openEmbeddingSheafPullbackIso] using
      (leftAdjointUniq_comp_first_app adjActualG adjNaiveG adjActualF G).symm
  have hfreplace :
      (openEmbeddingSheafPullbackIso hf).hom.app
          (((hg.sheafPullback (Type w)).obj G)) =
      (Adjunction.leftAdjointUniq adjMixedComp adjNaiveComp).hom.app G := by
    simpa [adjMixedComp, adjNaiveComp, adjNaiveG, adjActualF, adjNaiveF,
      openEmbeddingSheafPullbackIso] using
      (leftAdjointUniq_comp_second_app adjNaiveG adjActualF adjNaiveF G).symm
  have hreplace :
      (TopCat.Sheaf.pullback (Type w) f).map
          ((openEmbeddingSheafPullbackIso hg).hom.app G) ≫
        (openEmbeddingSheafPullbackIso hf).hom.app
          (((hg.sheafPullback (Type w)).obj G)) =
      (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app G := by
    calc
      (TopCat.Sheaf.pullback (Type w) f).map
            ((openEmbeddingSheafPullbackIso hg).hom.app G) ≫
          (openEmbeddingSheafPullbackIso hf).hom.app
            (((hg.sheafPullback (Type w)).obj G))
          =
        (Adjunction.leftAdjointUniq adjActualComp adjMixedComp).hom.app G ≫
          (Adjunction.leftAdjointUniq adjMixedComp adjNaiveComp).hom.app G := by
            simpa [hgreplace, hfreplace]
      _ =
        (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app G := by
          simpa using
            (Adjunction.leftAdjointUniq_trans_app
              adjActualComp adjMixedComp adjNaiveComp G)
  have hcomp :
      (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G =
      (Adjunction.leftAdjointUniq adjNaiveComp adjNaiveDirect).hom.app G := by
    apply (adjNaiveComp.homEquiv G
      ((hfg.sheafPullback (Type w)).obj G)).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app adjNaiveComp adjNaiveDirect G]
    rw [Adjunction.homEquiv_unit]
    apply ObjectProperty.hom_ext
    ext V x
    repeat erw [ObjectProperty.FullSubcategory.comp_hom]
    simp [adjNaiveComp, adjNaiveG, adjNaiveF, adjNaiveDirect,
      openEmbeddingSheafPullbackCompIso,
      Adjunction.comp, Adjunction.sheafPushforwardContinuous,
      Topology.IsOpenEmbedding.sheafPullback,
      IsOpenMap.adjunction,
      ObjectProperty.FullSubcategory.id_hom,
      Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
      Category.assoc]
    rw [← FunctorToTypes.map_comp_apply]
    rw [← FunctorToTypes.map_comp_apply]
    congr 1
  have hright :
      (TopCat.Sheaf.pullback (Type w) f).map
          ((openEmbeddingSheafPullbackIso hg).hom.app G) ≫
        (openEmbeddingSheafPullbackIso hf).hom.app
          (((hg.sheafPullback (Type w)).obj G)) ≫
        (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G =
      (Adjunction.leftAdjointUniq adjActualComp adjNaiveDirect).hom.app G := by
    calc
      (TopCat.Sheaf.pullback (Type w) f).map
            ((openEmbeddingSheafPullbackIso hg).hom.app G) ≫
          (openEmbeddingSheafPullbackIso hf).hom.app
            (((hg.sheafPullback (Type w)).obj G)) ≫
          (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G
          =
        (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app G ≫
          (Adjunction.leftAdjointUniq adjNaiveComp adjNaiveDirect).hom.app G := by
            calc
              (TopCat.Sheaf.pullback (Type w) f).map
                    ((openEmbeddingSheafPullbackIso hg).hom.app G) ≫
                  (openEmbeddingSheafPullbackIso hf).hom.app
                    (((hg.sheafPullback (Type w)).obj G)) ≫
                  (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G
                  =
                ((TopCat.Sheaf.pullback (Type w) f).map
                    ((openEmbeddingSheafPullbackIso hg).hom.app G) ≫
                  (openEmbeddingSheafPullbackIso hf).hom.app
                    (((hg.sheafPullback (Type w)).obj G))) ≫
                  (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G := by
                    rfl
              _ =
                (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app G ≫
                  (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G := by
                    simpa using congrArg
                      (fun k ↦ k ≫ (openEmbeddingSheafPullbackCompIso hf hg hfg).hom.app G)
                      hreplace
              _ =
                (Adjunction.leftAdjointUniq adjActualComp adjNaiveComp).hom.app G ≫
                  (Adjunction.leftAdjointUniq adjNaiveComp adjNaiveDirect).hom.app G := by
                    rw [hcomp]
      _ =
        (Adjunction.leftAdjointUniq adjActualComp adjNaiveDirect).hom.app G := by
          simpa using
            (Adjunction.leftAdjointUniq_trans_app
              adjActualComp adjNaiveComp adjNaiveDirect G)
  exact hleft.trans hright.symm

/-- Helper for Lemma 6.33.3: the uniqueness-based open-embedding pullback comparison is
compatible with composition of nested open-subset inclusions. -/
theorem openSubsetHomOfLE_openEmbeddingSheafPullbackIso_comp_hom
    {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U)
    (G : TopCat.Sheaf (Type w) (openSubsetSpace U)) :
    (TopCat.Sheaf.pullbackComp (A := Type w)
        (openSubsetHomOfLE hTW) (openSubsetHomOfLE hWU)).hom.app G ≫
      (openEmbeddingSheafPullbackIso
        (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))).hom.app G =
    (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
        ((openEmbeddingSheafPullbackIso
          (openSubsetHomOfLE_isOpenEmbedding hWU)).hom.app G) ≫
      (openEmbeddingSheafPullbackIso
        (openSubsetHomOfLE_isOpenEmbedding hTW)).hom.app
          (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback (Type w)).obj G) ≫
        (typeOpenSubsetRestrictionCompIso hTW hWU).hom.app G := by
  let hfg : IsOpenEmbedding (openSubsetHomOfLE hTW ≫ openSubsetHomOfLE hWU) := by
    simpa [openSubsetHomOfLE_comp] using
      (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))
  have h := openEmbeddingSheafPullbackIso_comp_hom
    (hf := openSubsetHomOfLE_isOpenEmbedding hTW)
    (hg := openSubsetHomOfLE_isOpenEmbedding hWU)
    (hfg := hfg) G
  rw [← typeOpenSubsetRestrictionCompIso_hom_eq_generic hTW hWU G] at h
  simpa [hfg, openSubsetHomOfLE_comp, Category.assoc] using h

noncomputable def algebraicGlobalRestrictionCompIso
    {C : Type (w + 1)} [Category.{w} C] {W U : Opens X} (h : W ≤ U) :
    (U.isOpenEmbedding.sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) ≅
      (W.isOpenEmbedding.sheafPullback C) := by
  -- The ambient restriction followed by the internal restriction is the direct pullback along
  -- the inclusion `W ↪ X`.
  let eComp :
      (openSubsetHomOfLE_isOpenEmbedding h).functor ⋙ U.isOpenEmbedding.functor ≅
        W.isOpenEmbedding.functor :=
    NatIso.ofComponents
      (fun V ↦ eqToIso (by
        ext x
        change x ∈
            ((U.isOpenEmbedding.functor.obj
                ((openSubsetHomOfLE_isOpenEmbedding h).functor.obj V)) : Set _) ↔
          x ∈ ((W.isOpenEmbedding.functor.obj V) : Set _)
        constructor
        · rintro ⟨x₁, hx₁, hx⟩
          rcases (by
            simpa [Topology.IsOpenEmbedding.functor] using hx₁) with ⟨w, hwV, rfl⟩
          exact ⟨w, hwV, by simpa using hx⟩
        · rintro ⟨w, hwV, hx⟩
          refine ⟨(openSubsetHomOfLE h) w, ?_, by simpa using hx⟩
          simpa [Topology.IsOpenEmbedding.functor] using ⟨w, hwV, rfl⟩))
      (fun {_ _} _ ↦ by apply Subsingleton.elim)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding h)
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  letI := Topology.IsOpenEmbedding.functor_isContinuous W.isOpenEmbedding
  simpa [Topology.IsOpenEmbedding.sheafPullback, openSubsetHomOfLE_comp_inclusion] using
    (CategoryTheory.Functor.sheafPushforwardContinuousComp'
      (F := (openSubsetHomOfLE_isOpenEmbedding h).functor)
      (G := U.isOpenEmbedding.functor)
      (FG := W.isOpenEmbedding.functor)
      (eFG := eComp)
      C
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U))
      (Opens.grothendieckTopology X))

noncomputable def algebraicRestrictToTripleFirstViaIJIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleFirst U V W :
      TopCat.Sheaf C (openSubsetSpace U) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft U V :
        TopCat.Sheaf C (openSubsetSpace U) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ⋙
        (algebraicRestrictOverlapToTripleLeft U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ U from inf_le_left)).symm

noncomputable def algebraicRestrictToTripleSecondViaIJIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleSecond U V W :
      TopCat.Sheaf C (openSubsetSpace V) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight U V :
        TopCat.Sheaf C (openSubsetSpace V) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ⋙
        (algebraicRestrictOverlapToTripleLeft U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ V from inf_le_right)).symm

noncomputable def algebraicRestrictToTripleSecondViaJKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleSecond U V W :
      TopCat.Sheaf C (openSubsetSpace V) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft V W :
        TopCat.Sheaf C (openSubsetSpace V) ⥤
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleCenter U V W :
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ V from inf_le_left)).symm

noncomputable def algebraicRestrictToTripleThirdViaJKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleThird U V W :
      TopCat.Sheaf C (openSubsetSpace W) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight V W :
        TopCat.Sheaf C (openSubsetSpace W) ⥤
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleCenter U V W :
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ W from inf_le_right)).symm

noncomputable def algebraicRestrictToTripleFirstViaIKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleFirst U V W :
      TopCat.Sheaf C (openSubsetSpace U) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft U W :
        TopCat.Sheaf C (openSubsetSpace U) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleOuter U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ U from inf_le_left)).symm

noncomputable def algebraicRestrictToTripleThirdViaIKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleThird U V W :
      TopCat.Sheaf C (openSubsetSpace W) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight U W :
        TopCat.Sheaf C (openSubsetSpace W) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleOuter U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ W from inf_le_right)).symm

noncomputable def algebraicGlobalRestrictionToPairViaLeftIso
    (U V : Opens X) :
    (algebraicRestrictToOpen (U ⊓ V) :
      TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ≅
      (algebraicRestrictToOpen U :
        TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace U)) ⋙
        (algebraicRestrictToPairLeft U V :
          TopCat.Sheaf C (openSubsetSpace U) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) :=
  (algebraicGlobalRestrictionCompIso
    (show U ⊓ V ≤ U from inf_le_left)).symm

noncomputable def algebraicGlobalRestrictionToPairViaRightIso
    (U V : Opens X) :
    (algebraicRestrictToOpen (U ⊓ V) :
      TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ≅
      (algebraicRestrictToOpen V :
        TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace V)) ⋙
        (algebraicRestrictToPairRight U V :
          TopCat.Sheaf C (openSubsetSpace V) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) :=
  (algebraicGlobalRestrictionCompIso
    (show U ⊓ V ≤ V from inf_le_right)).symm

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

abbrev algebraicTripleOverlapHom12
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleFirst (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (algRestrictToTripleSecond (U i) (U j) (U k)).obj (localSheaf j) :=
  ((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).mapIso (overlapIso i j)).hom ≫
    ((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app (localSheaf j))

abbrev algebraicTripleOverlapHom23
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleSecond (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (algRestrictToTripleThird (U i) (U j) (U k)).obj (localSheaf k) :=
  ((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
    ((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app (localSheaf k))

abbrev algebraicTripleOverlapHom13
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleFirst (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (algRestrictToTripleThird (U i) (U j) (U k)).obj (localSheaf k) :=
  ((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).mapIso (overlapIso i k)).hom ≫
    ((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app (localSheaf k))

/-- Helper for Lemma 6.33.3: compare the two chart descriptions of a `C`-valued sheaf over a
subordinate open `W`. -/
noncomputable def algebraicSubsetChartIso
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (localSheaf i).1.obj (op (subspaceOpenOfLE hWi)) ≅
      (localSheaf j).1.obj (op (subspaceOpenOfLE hWj)) := by
  let hWij := subset_overlap_le (U := U) hWi hWj
  let eLi := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_left (localSheaf i)
  let eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right (localSheaf j)
  exact
    eLi.symm ≪≫
      (((TopCat.Sheaf.forget C (openSubsetSpace (U i ⊓ U j))).mapIso
        (overlapIso i j)).app (op (subspaceOpenOfLE hWij))) ≪≫
      eRj

theorem algebraicSubsetChartIso_hom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom =
      (openSubsetHomOfLEOpenEmbeddingSectionIso
          (subset_overlap_le (U := U) hWi hWj) inf_le_left (localSheaf i)).inv ≫
        (((TopCat.Sheaf.forget C (openSubsetSpace (U i ⊓ U j))).mapIso
          (overlapIso i j)).hom.app
            (op (subspaceOpenOfLE (subset_overlap_le (U := U) hWi hWj)))) ≫
        (openSubsetHomOfLEOpenEmbeddingSectionIso
          (subset_overlap_le (U := U) hWi hWj) inf_le_right (localSheaf j)).hom := by
  simp only [algebraicSubsetChartIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom]

/-- Helper for Lemma 6.33.3: the chart-change isomorphisms commute with restriction to a smaller
subordinate open. -/
theorem algebraicSubsetChartIso_naturality
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    {V W : Opens X} {i j : ι}
    (hVW : V ≤ W) (hVi : V ≤ U i) (hVj : V ≤ U j)
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (localSheaf i).1.map (subspaceOpenHom hVi hWi hVW).op ≫
      (algebraicSubsetChartIso localSheaf overlapIso hVi hVj).hom =
    (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom ≫
      (localSheaf j).1.map (subspaceOpenHom hVj hWj hVW).op := by
  let hVij := subset_overlap_le (U := U) hVi hVj
  let hWij := subset_overlap_le (U := U) hWi hWj
  let eLiV := openSubsetHomOfLEOpenEmbeddingSectionIso hVij inf_le_left (localSheaf i)
  let eLiW := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_left (localSheaf i)
  let eRjV := openSubsetHomOfLEOpenEmbeddingSectionIso hVij inf_le_right (localSheaf j)
  let eRjW := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right (localSheaf j)
  let pairHom : subspaceOpenOfLE hVij ⟶ subspaceOpenOfLE hWij :=
    subspaceOpenHom hVij hWij hVW
  let overlapIsoSections :
      ((algRestrictToPairLeft (U i) (U j)).obj (localSheaf i)).1 ≅
        ((algRestrictToPairRight (U i) (U j)).obj (localSheaf j)).1 :=
    (TopCat.Sheaf.forget C (openSubsetSpace (U i ⊓ U j))).mapIso (overlapIso i j)
  have hmapi :
      subspaceOpenHom (hVij.trans inf_le_left) (hWij.trans inf_le_left) hVW =
        subspaceOpenHom hVi hWi hVW := by
    apply Subsingleton.elim
  have hmapj :
      subspaceOpenHom (hVij.trans inf_le_right) (hWij.trans inf_le_right) hVW =
        subspaceOpenHom hVj hWj hVW := by
    apply Subsingleton.elim
  have hleft :=
    openSubsetHomOfLEOpenEmbeddingSectionIso_naturality
      (hA₁ := hVij) (hA₂ := hWij) (h12 := hVW) (hBD := inf_le_left)
      (ℱ := localSheaf i)
  have hright :=
    openSubsetHomOfLEOpenEmbeddingSectionIso_naturality
      (hA₁ := hVij) (hA₂ := hWij) (h12 := hVW) (hBD := inf_le_right)
      (ℱ := localSheaf j)
  have hleft_aux :
      (localSheaf i).1.map (subspaceOpenHom hVi hWi hVW).op ≫ eLiV.inv =
        eLiW.inv ≫
          (((openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U j)).sheafPullback
            C).obj (localSheaf i)).1.map pairHom.op := by
    rw [← cancel_mono eLiV.hom]
    simp [Category.assoc, eLiV, eLiW, pairHom, hleft, hmapi]
  have hnat := overlapIsoSections.hom.naturality pairHom.op
  calc
    (localSheaf i).1.map (subspaceOpenHom hVi hWi hVW).op ≫
        (algebraicSubsetChartIso localSheaf overlapIso hVi hVj).hom
        =
      (localSheaf i).1.map (subspaceOpenHom hVi hWi hVW).op ≫ eLiV.inv ≫
        overlapIsoSections.hom.app (op (subspaceOpenOfLE hVij)) ≫ eRjV.hom := by
          rfl
    _ = eLiW.inv ≫
        (((openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U j)).sheafPullback
          C).obj (localSheaf i)).1.map pairHom.op ≫
        overlapIsoSections.hom.app (op (subspaceOpenOfLE hVij)) ≫ eRjV.hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ overlapIsoSections.hom.app (op (subspaceOpenOfLE hVij)) ≫
                eRjV.hom)
              hleft_aux
    _ = eLiW.inv ≫
        overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
        (((openSubsetIntersectionRightInclusion_isOpenEmbedding (U i) (U j)).sheafPullback
          C).obj (localSheaf j)).1.map pairHom.op ≫ eRjV.hom := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ eLiW.inv ≫ k ≫ eRjV.hom) hnat
    _ = eLiW.inv ≫
        overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫ eRjW.hom ≫
          (localSheaf j).1.map (subspaceOpenHom hVj hWj hVW).op := by
          simpa [Category.assoc, hmapj] using
            congrArg
              (fun k ↦ eLiW.inv ≫ overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫ k)
              hright
    _ = (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom ≫
        (localSheaf j).1.map (subspaceOpenHom hVj hWj hVW).op := by
          show
            eLiW.inv ≫ overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
                eRjW.hom ≫
                  (localSheaf j).1.map (subspaceOpenHom hVj hWj hVW).op =
              (eLiW.inv ≫ overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
                  eRjW.hom) ≫
                (localSheaf j).1.map (subspaceOpenHom hVj hWj hVW).op
          simp [Category.assoc]

end
