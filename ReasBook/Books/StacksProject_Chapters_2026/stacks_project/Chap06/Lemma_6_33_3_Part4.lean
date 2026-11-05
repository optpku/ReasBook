module

public import stacks_project.Chap06.Lemma_6_33_3_Part3

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

/-- Helper for Lemma 6.33.3: the explicit forgotten `23` overlap path is the direct triple-owner
transport of the forgotten algebraic `23` comparison. -/
theorem algebraicTripleOverlapHom23_mappedPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
        (algebraicTripleOverlapHom23 localSheaf overlapIso i j k) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).mapIso
            (overlapIso j k)).hom) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app (localSheaf k)) := by
  -- Expand the mapped algebraic `23` comparison once so the later bridge proof can focus only
  -- on owner transports.
  rw [algebraicTripleOverlapHom23, Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 6.33.3: the pair-to-Types comparisons in the `23` overlap leg are
definitionally trivial after pulling back to the triple overlap. -/
theorem algebraicTripleOverlapHom23_middle_toTypes
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullback (Type w)
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom =
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) := by
  -- The pair-to-Types comparisons are definitional, so pulling them back to the triple overlap
  -- leaves only the central forgotten overlap morphism.
  have hLeft :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv =
      𝟙 _ := by
    rw [show (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map_id
        ((algebraicToTypes F (U j) ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding (U j) (U k)).sheafPullback
            (Type w)).obj (localSheaf j)))
  have hRight :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom =
      𝟙 _ := by
    rw [show (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map_id
        ((algRestrictToPairRight (U j) (U k) ⋙ algebraicToTypes F (U j ⊓ U k)).obj
          (localSheaf k)))
  -- Rewriting both pulled-back comparison maps to identities leaves exactly the overlap map.
  rw [hLeft]
  simpa [Category.assoc] using
    congrArg
      (fun t ↦
        𝟙 _ ≫
          (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
            ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) ≫
          t)
      hRight

theorem algebraicTripleOverlapHom23_toTypesPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type w)
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U j) (U k))).inv.app
        ((algebraicToTypes F (U j)).obj (localSheaf j)) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicLeftOwnerIso F (U j) (U k) (localSheaf j)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicRightOwnerIso F (U j) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U j) (U k))).hom.app
        ((algebraicToTypes F (U k)).obj (localSheaf k)) =
      (algebraicTripleSecondOwnerIso F (U i) (U j) (U k) (localSheaf j)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (algebraicTripleOverlapHom23 localSheaf overlapIso i j k) ≫
        (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
  -- Expand the mapped algebraic `23` path first; the remaining work is again only the two owner
  -- endpoint comparisons and the center pulled-back overlap map.
  rw [algebraicTripleOverlapHom23_mappedPath]
  have hLeftOwner :
      (algebraicLeftOwnerIso F (U j) (U k) (localSheaf j)).hom =
        (algebraicRestrictionOwnerIso F
          (show U j ⊓ U k ≤ U j from inf_le_left) (localSheaf j)).hom := by
    rfl
  have hRightOwner :
      (algebraicRightOwnerIso F (U j) (U k) (localSheaf k)).hom =
        (algebraicRestrictionOwnerIso F
          (show U j ⊓ U k ≤ U k from inf_le_right) (localSheaf k)).inv := by
    rfl
  have hTripleSecondOwner :
      (algebraicTripleSecondOwnerIso F (U i) (U j) (U k) (localSheaf j)).hom =
        (algebraicRestrictionOwnerIso F
          ((show U i ⊓ U j ⊓ U k ≤ U j ⊓ U k from
              inf_le_inf inf_le_right le_rfl).trans
            (show U j ⊓ U k ≤ U j from inf_le_left))
          (localSheaf j)).hom := by
    rfl
  have hTripleThirdOwner :
      (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv =
        (algebraicRestrictionOwnerIso F
          ((show U i ⊓ U j ⊓ U k ≤ U j ⊓ U k from
              inf_le_inf inf_le_right le_rfl).trans
            (show U j ⊓ U k ≤ U k from inf_le_right))
          (localSheaf k)).inv := by
    rfl
  let hTjk : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := inf_le_inf inf_le_right le_rfl
  let hJjk : U j ⊓ U k ≤ U j := inf_le_left
  let hKjk : U j ⊓ U k ≤ U k := inf_le_right
  have hForward23 :
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U j) (U k))).inv.app
          ((algebraicToTypes F (U j)).obj (localSheaf j)) ≫
        (TopCat.Sheaf.pullback (Type w)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
          (algebraicRestrictionOwnerIso F hJjk (localSheaf j)).hom =
      (algebraicRestrictionOwnerIso F (hTjk.trans hJjk) (localSheaf j)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
            (localSheaf j)) ≫
        (algebraicRestrictionOwnerIso F hTjk
          (((openSubsetHomOfLE_isOpenEmbedding hJjk).sheafPullback C).obj
            (localSheaf j))).inv := by
    simpa [hTjk, hJjk, openSubsetTripleToPairCenterInclusion,
      openSubsetIntersectionLeftInclusion, openSubsetTripleSecondInclusion,
      algebraicRestrictToTripleSecondViaJKIso, Category.assoc] using
      algebraicRestrictionCompToTypes_forwardImportedEndpoint F hTjk hJjk (localSheaf j)
  have hNat23 :
      (algebraicRestrictionOwnerIso F hTjk
          (((openSubsetHomOfLE_isOpenEmbedding hJjk).sheafPullback C).obj
            (localSheaf j))).inv ≫
        (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
          ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).map
            (overlapIso j k).hom) ≫
        (algebraicRestrictionOwnerIso F hTjk
          (((openSubsetHomOfLE_isOpenEmbedding hKjk).sheafPullback C).obj
            (localSheaf k))).inv := by
    simpa only [hTjk, hJjk, hKjk, openSubsetTripleToPairCenterInclusion,
      algebraicRestrictOverlapToTripleCenter] using
      algebraicRestrictionOwnerIso_naturality F hTjk (overlapIso j k).hom
  have hInverse23 :
      (algebraicRestrictionOwnerIso F hTjk
          (((openSubsetHomOfLE_isOpenEmbedding hKjk).sheafPullback C).obj
            (localSheaf k))).inv ≫
        (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
          (algebraicRestrictionOwnerIso F hKjk (localSheaf k)).inv ≫
        (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U j) (U k))).hom.app
          ((algebraicToTypes F (U k)).obj (localSheaf k)) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app
            (localSheaf k)) ≫
        (algebraicRestrictionOwnerIso F (hTjk.trans hKjk) (localSheaf k)).inv := by
    simpa [hTjk, hKjk, openSubsetTripleToPairCenterInclusion,
      openSubsetIntersectionRightInclusion, openSubsetTripleThirdInclusion,
      algebraicRestrictToTripleThirdViaJKIso, Category.assoc] using
      algebraicRestrictionCompToTypes_inverseImportedEndpoint F hTjk hKjk (localSheaf k)
  have hMiddle23 :=
    algebraicTripleOverlapHom23_middle_toTypes F localSheaf overlapIso i j k
  let midJ :=
    (algebraicRestrictionOwnerIso F hTjk
      (((openSubsetHomOfLE_isOpenEmbedding hJjk).sheafPullback C).obj
        (localSheaf j))).inv
  let midK :=
    (algebraicRestrictionOwnerIso F hTjk
      (((openSubsetHomOfLE_isOpenEmbedding hKjk).sheafPullback C).obj
        (localSheaf k))).inv
  let pairL :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv
  let overlapPair :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
      ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom)
  let pairR :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
      (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom
  let rightOwner :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
      (algebraicRestrictionOwnerIso F hKjk (localSheaf k)).inv
  let rightComp :=
    (TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U j) (U k))).hom.app
      ((algebraicToTypes F (U k)).obj (localSheaf k))
  let overlapTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).map
        (overlapIso j k).hom)
  let thirdTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app
        (localSheaf k))
  let directK := (algebraicRestrictionOwnerIso F (hTjk.trans hKjk) (localSheaf k)).inv
  let forwardStart :=
    (TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U j) (U k))).inv.app
      ((algebraicToTypes F (U j)).obj (localSheaf j))
  let forwardOwner :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
      (algebraicRestrictionOwnerIso F hJjk (localSheaf j)).hom
  let directJ := (algebraicRestrictionOwnerIso F (hTjk.trans hJjk) (localSheaf j)).hom
  let secondTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
        (localSheaf j))
  have hForwardWrapped :
      forwardStart ≫ forwardOwner = directJ ≫ secondTriple ≫ midJ := by
    dsimp [forwardStart, forwardOwner, directJ, secondTriple, midJ]
    simpa only [Category.assoc] using hForward23
  have hMiddleWrapped :
      midJ ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp =
        midJ ≫ overlapPair ≫ rightOwner ≫ rightComp := by
    dsimp [midJ, pairL, overlapPair, pairR, rightOwner, rightComp]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          (algebraicRestrictionOwnerIso F hTjk
            (((openSubsetHomOfLE_isOpenEmbedding hJjk).sheafPullback C).obj
              (localSheaf j))).inv ≫ t ≫
            (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
              (algebraicRestrictionOwnerIso F hKjk (localSheaf k)).inv ≫
            (TopCat.Sheaf.pullbackComp (A := Type w)
              (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
              (openSubsetIntersectionRightInclusion (U j) (U k))).hom.app
              ((algebraicToTypes F (U k)).obj (localSheaf k)))
        hMiddle23
  have hNatWrapped :
      midJ ≫ overlapPair ≫ rightOwner ≫ rightComp =
        overlapTriple ≫ midK ≫ rightOwner ≫ rightComp := by
    dsimp [midJ, overlapPair, overlapTriple, midK, rightOwner, rightComp]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦ t ≫
          (TopCat.Sheaf.pullback (Type w)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
            (algebraicRestrictionOwnerIso F hKjk (localSheaf k)).inv ≫
          (TopCat.Sheaf.pullbackComp (A := Type w)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetIntersectionRightInclusion (U j) (U k))).hom.app
            ((algebraicToTypes F (U k)).obj (localSheaf k)))
        hNat23
  have hInverseWrapped :
      overlapTriple ≫ midK ≫ rightOwner ≫ rightComp =
        overlapTriple ≫ thirdTriple ≫ directK := by
    dsimp [overlapTriple, midK, rightOwner, rightComp, thirdTriple, directK]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            ((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).map
              (overlapIso j k).hom) ≫ t)
        hInverse23
  have hAssembled :
      forwardStart ≫ forwardOwner ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫
          rightComp =
        directJ ≫ secondTriple ≫ overlapTriple ≫ thirdTriple ≫ directK := by
    have h0 :
        forwardStart ≫ forwardOwner ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫
            rightComp =
          (directJ ≫ secondTriple ≫ midJ) ≫ pairL ≫ overlapPair ≫ pairR ≫
            rightOwner ≫ rightComp := by
      simpa only [Category.assoc] using
        congrArg
          (fun t ↦ t ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp)
          hForwardWrapped
    have h1 :
        (directJ ≫ secondTriple ≫ midJ) ≫ pairL ≫ overlapPair ≫ pairR ≫
            rightOwner ≫ rightComp =
          directJ ≫ secondTriple ≫
            (midJ ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp) := by
      simp only [Category.assoc]
    have h2 :
        directJ ≫ secondTriple ≫
            (midJ ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp) =
          directJ ≫ secondTriple ≫
            (midJ ≫ overlapPair ≫ rightOwner ≫ rightComp) := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ directJ ≫ secondTriple ≫ t) hMiddleWrapped
    have h3 :
        directJ ≫ secondTriple ≫
            (midJ ≫ overlapPair ≫ rightOwner ≫ rightComp) =
          directJ ≫ secondTriple ≫
            (overlapTriple ≫ thirdTriple ≫ directK) := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ directJ ≫ secondTriple ≫ t)
          (hNatWrapped.trans hInverseWrapped)
    have h4 :
        directJ ≫ secondTriple ≫ (overlapTriple ≫ thirdTriple ≫ directK) =
          directJ ≫ secondTriple ≫ overlapTriple ≫ thirdTriple ≫ directK := by
      simp only [Category.assoc]
    exact h0.trans (h1.trans (h2.trans (h3.trans h4)))
  rw [hLeftOwner, hRightOwner, hTripleSecondOwner, hTripleThirdOwner]
  simpa only [forwardStart, forwardOwner, directJ, secondTriple, midJ, pairL, overlapPair,
    pairR, rightOwner, rightComp, overlapTriple, thirdTriple, directK,
    Functor.mapIso_hom, Category.assoc] using hAssembled

/-- Helper for Lemma 6.33.3: the explicit forgotten `13` overlap path is the direct triple-owner
transport of the forgotten algebraic `13` comparison. -/
theorem algebraicTripleOverlapHom13_mappedPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
        (algebraicTripleOverlapHom13 localSheaf overlapIso i j k) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).mapIso
            (overlapIso i k)).hom) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app (localSheaf k)) := by
  -- Expand the mapped algebraic `13` comparison once so the last bridge theorem has the same
  -- normal form as the other two.
  rw [algebraicTripleOverlapHom13, Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 6.33.3: the pair-to-Types comparisons in the `13` overlap leg are
definitionally trivial after pulling back to the triple overlap. -/
theorem algebraicTripleOverlapHom13_middle_toTypes
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullback (Type w)
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom =
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) := by
  -- The pair-to-Types comparisons are again definitional, so pulling them back to the triple
  -- overlap leaves only the outer forgotten overlap morphism.
  have hLeft :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv =
      𝟙 _ := by
    rw [show (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map_id
        ((algebraicToTypes F (U i) ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U k)).sheafPullback
            (Type w)).obj (localSheaf i)))
  have hRight :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom =
      𝟙 _ := by
    rw [show (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map_id
        ((algRestrictToPairRight (U i) (U k) ⋙ algebraicToTypes F (U i ⊓ U k)).obj
          (localSheaf k)))
  -- Rewriting both pulled-back comparison maps to identities leaves exactly the overlap map.
  rw [hLeft]
  simpa [Category.assoc] using
    congrArg
      (fun t ↦
        𝟙 _ ≫
          (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
            ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) ≫
          t)
      hRight

theorem algebraicTripleOverlapHom13_toTypesPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type w)
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U k))).inv.app
        ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicLeftOwnerIso F (U i) (U k) (localSheaf i)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicRightOwnerIso F (U i) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U k))).hom.app
        ((algebraicToTypes F (U k)).obj (localSheaf k)) =
      (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (algebraicTripleOverlapHom13 localSheaf overlapIso i j k) ≫
        (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
  -- Expand the mapped algebraic `13` path first; as above, only the owner transports remain.
  rw [algebraicTripleOverlapHom13_mappedPath]
  have hLeftOwner :
      (algebraicLeftOwnerIso F (U i) (U k) (localSheaf i)).hom =
        (algebraicRestrictionOwnerIso F
          (show U i ⊓ U k ≤ U i from inf_le_left) (localSheaf i)).hom := by
    rfl
  have hRightOwner :
      (algebraicRightOwnerIso F (U i) (U k) (localSheaf k)).hom =
        (algebraicRestrictionOwnerIso F
          (show U i ⊓ U k ≤ U k from inf_le_right) (localSheaf k)).inv := by
    rfl
  have hTripleFirstOwner :
      (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom =
        (algebraicRestrictionOwnerIso F
          ((show U i ⊓ U j ⊓ U k ≤ U i ⊓ U k from
              inf_le_inf (show U i ⊓ U j ≤ U i from inf_le_left) le_rfl).trans
            (show U i ⊓ U k ≤ U i from inf_le_left))
          (localSheaf i)).hom := by
    rfl
  have hTripleThirdOwner :
      (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv =
        (algebraicRestrictionOwnerIso F
          ((show U i ⊓ U j ⊓ U k ≤ U i ⊓ U k from
              inf_le_inf (show U i ⊓ U j ≤ U i from inf_le_left) le_rfl).trans
            (show U i ⊓ U k ≤ U k from inf_le_right))
          (localSheaf k)).inv := by
    rfl
  let hTik : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k :=
    inf_le_inf (show U i ⊓ U j ≤ U i from inf_le_left) le_rfl
  let hIik : U i ⊓ U k ≤ U i := inf_le_left
  let hKik : U i ⊓ U k ≤ U k := inf_le_right
  have hForward13 :
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U i) (U k))).inv.app
          ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
        (TopCat.Sheaf.pullback (Type w)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
          (algebraicRestrictionOwnerIso F hIik (localSheaf i)).hom =
      (algebraicRestrictionOwnerIso F (hTik.trans hIik) (localSheaf i)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
            (localSheaf i)) ≫
        (algebraicRestrictionOwnerIso F hTik
          (((openSubsetHomOfLE_isOpenEmbedding hIik).sheafPullback C).obj
            (localSheaf i))).inv := by
    simpa [hTik, hIik, openSubsetTripleToPairOuterInclusion,
      openSubsetIntersectionLeftInclusion, openSubsetTripleFirstInclusion,
      algebraicRestrictToTripleFirstViaIKIso, Category.assoc] using
      algebraicRestrictionCompToTypes_forwardImportedEndpoint F hTik hIik (localSheaf i)
  have hNat13 :
      (algebraicRestrictionOwnerIso F hTik
          (((openSubsetHomOfLE_isOpenEmbedding hIik).sheafPullback C).obj
            (localSheaf i))).inv ≫
        (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
          ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).map
            (overlapIso i k).hom) ≫
        (algebraicRestrictionOwnerIso F hTik
          (((openSubsetHomOfLE_isOpenEmbedding hKik).sheafPullback C).obj
            (localSheaf k))).inv := by
    simpa only [hTik, hIik, hKik, openSubsetTripleToPairOuterInclusion,
      algebraicRestrictOverlapToTripleOuter] using
      algebraicRestrictionOwnerIso_naturality F hTik (overlapIso i k).hom
  have hInverse13 :
      (algebraicRestrictionOwnerIso F hTik
          (((openSubsetHomOfLE_isOpenEmbedding hKik).sheafPullback C).obj
            (localSheaf k))).inv ≫
        (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
          (algebraicRestrictionOwnerIso F hKik (localSheaf k)).inv ≫
        (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U k))).hom.app
          ((algebraicToTypes F (U k)).obj (localSheaf k)) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app
            (localSheaf k)) ≫
        (algebraicRestrictionOwnerIso F (hTik.trans hKik) (localSheaf k)).inv := by
    simpa [hTik, hKik, openSubsetTripleToPairOuterInclusion,
      openSubsetIntersectionRightInclusion, openSubsetTripleThirdInclusion,
      algebraicRestrictToTripleThirdViaIKIso, Category.assoc] using
      algebraicRestrictionCompToTypes_inverseImportedEndpoint F hTik hKik (localSheaf k)
  have hMiddle13 :=
    algebraicTripleOverlapHom13_middle_toTypes F localSheaf overlapIso i j k
  let midI :=
    (algebraicRestrictionOwnerIso F hTik
      (((openSubsetHomOfLE_isOpenEmbedding hIik).sheafPullback C).obj
        (localSheaf i))).inv
  let midK :=
    (algebraicRestrictionOwnerIso F hTik
      (((openSubsetHomOfLE_isOpenEmbedding hKik).sheafPullback C).obj
        (localSheaf k))).inv
  let pairL :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv
  let overlapPair :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
      ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom)
  let pairR :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
      (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom
  let rightOwner :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
      (algebraicRestrictionOwnerIso F hKik (localSheaf k)).inv
  let rightComp :=
    (TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U k))).hom.app
      ((algebraicToTypes F (U k)).obj (localSheaf k))
  let overlapTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).map
        (overlapIso i k).hom)
  let thirdTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app
        (localSheaf k))
  let directK := (algebraicRestrictionOwnerIso F (hTik.trans hKik) (localSheaf k)).inv
  let forwardStart :=
    (TopCat.Sheaf.pullbackComp (A := Type w)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U k))).inv.app
      ((algebraicToTypes F (U i)).obj (localSheaf i))
  let forwardOwner :=
    (TopCat.Sheaf.pullback (Type w)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
      (algebraicRestrictionOwnerIso F hIik (localSheaf i)).hom
  let directI := (algebraicRestrictionOwnerIso F (hTik.trans hIik) (localSheaf i)).hom
  let firstTriple :=
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
      ((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
        (localSheaf i))
  have hForwardWrapped :
      forwardStart ≫ forwardOwner = directI ≫ firstTriple ≫ midI := by
    dsimp [forwardStart, forwardOwner, directI, firstTriple, midI]
    simpa only [Category.assoc] using hForward13
  have hMiddleWrapped :
      midI ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫ rightComp =
        midI ≫ overlapPair ≫ rightOwner ≫ rightComp := by
    dsimp [midI, pairL, overlapPair, pairR, rightOwner, rightComp]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          (algebraicRestrictionOwnerIso F hTik
            (((openSubsetHomOfLE_isOpenEmbedding hIik).sheafPullback C).obj
              (localSheaf i))).inv ≫ t ≫
            (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
              (algebraicRestrictionOwnerIso F hKik (localSheaf k)).inv ≫
            (TopCat.Sheaf.pullbackComp (A := Type w)
              (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
              (openSubsetIntersectionRightInclusion (U i) (U k))).hom.app
              ((algebraicToTypes F (U k)).obj (localSheaf k)))
        hMiddle13
  have hNatWrapped :
      midI ≫ overlapPair ≫ rightOwner ≫ rightComp =
        overlapTriple ≫ midK ≫ rightOwner ≫ rightComp := by
    dsimp [midI, overlapPair, overlapTriple, midK, rightOwner, rightComp]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦ t ≫
          (TopCat.Sheaf.pullback (Type w)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
            (algebraicRestrictionOwnerIso F hKik (localSheaf k)).inv ≫
          (TopCat.Sheaf.pullbackComp (A := Type w)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetIntersectionRightInclusion (U i) (U k))).hom.app
            ((algebraicToTypes F (U k)).obj (localSheaf k)))
        hNat13
  have hInverseWrapped :
      overlapTriple ≫ midK ≫ rightOwner ≫ rightComp =
        overlapTriple ≫ thirdTriple ≫ directK := by
    dsimp [overlapTriple, midK, rightOwner, rightComp, thirdTriple, directK]
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            ((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).map
              (overlapIso i k).hom) ≫ t)
        hInverse13
  have hAssembled :
      forwardStart ≫ forwardOwner ≫ pairL ≫ overlapPair ≫ pairR ≫ rightOwner ≫
          rightComp =
        directI ≫ firstTriple ≫ overlapTriple ≫ thirdTriple ≫ directK := by
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
            (overlapTriple ≫ thirdTriple ≫ directK) := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ directI ≫ firstTriple ≫ t)
          (hNatWrapped.trans hInverseWrapped)
    have h4 :
        directI ≫ firstTriple ≫ (overlapTriple ≫ thirdTriple ≫ directK) =
          directI ≫ firstTriple ≫ overlapTriple ≫ thirdTriple ≫ directK := by
      simp only [Category.assoc]
    exact h0.trans (h1.trans (h2.trans (h3.trans h4)))
  rw [hLeftOwner, hRightOwner, hTripleFirstOwner, hTripleThirdOwner]
  simpa only [forwardStart, forwardOwner, directI, firstTriple, midI, pairL, overlapPair,
    pairR, rightOwner, rightComp, overlapTriple, thirdTriple, directK,
    Functor.mapIso_hom, Category.assoc] using hAssembled

namespace AlgebraicSheafOpenCover

/-- The cocycle condition for pairwise overlap isomorphisms in a gluing datum of sheaves valued in
a category of algebraic structures on an open cover. -/
def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j)) :
    Prop :=
  ∀ i j k : ι,
    algebraicTripleOverlapHom12 localSheaf overlapIso i j k ≫
      algebraicTripleOverlapHom23 localSheaf overlapIso i j k =
    algebraicTripleOverlapHom13 localSheaf overlapIso i j k

variable {F : C ⥤ Type w} [IsAlgebraicStructure C F] {U : ι → Opens X}

noncomputable def toSheafOpenCoverGlueing
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    SheafOpenCoverGlueing U where
  localSheaf i := (algebraicToTypes F (U i)).obj (localSheaf i)
  overlapIso i j :=
    (algebraicLeftOwnerIso F (U i) (U j) (localSheaf i) ≪≫
      (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).symm) ≪≫
      ((algebraicToTypes F (U i ⊓ U j)).mapIso (overlapIso i j)) ≪≫
      (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j) ≪≫
        algebraicRightOwnerIso F (U i) (U j) (localSheaf j))
  cocycle := by
    intro i j k
    have h12 :=
      algebraicTripleOverlapHom12_toTypesPath F localSheaf overlapIso i j k
    have h23 :=
      algebraicTripleOverlapHom23_toTypesPath F localSheaf overlapIso i j k
    have h13 :=
      algebraicTripleOverlapHom13_toTypesPath F localSheaf overlapIso i j k
    have hAlg :
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) ≫
          (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            (algebraicTripleOverlapHom23 localSheaf overlapIso i j k) =
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            (algebraicTripleOverlapHom13 localSheaf overlapIso i j k) := by
      simpa only [Functor.map_comp] using
        congrArg
          (fun f ↦ (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map f)
          (cocycle i j k)
    let leg12 :
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj
            ((algebraicToTypes F (U i)).obj (localSheaf i))) ⟶
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj
            ((algebraicToTypes F (U j)).obj (localSheaf j))) :=
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app
          ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).mapIso
          ((algebraicLeftOwnerIso F (U i) (U j) (localSheaf i) ≪≫
              (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).symm) ≪≫
            ((algebraicToTypes F (U i ⊓ U j)).mapIso (overlapIso i j)) ≪≫
            (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j) ≪≫
              algebraicRightOwnerIso F (U i) (U j) (localSheaf j)))).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app
          ((algebraicToTypes F (U j)).obj (localSheaf j))
    let leg23 :
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj
            ((algebraicToTypes F (U j)).obj (localSheaf j))) ⟶
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj
            ((algebraicToTypes F (U k)).obj (localSheaf k))) :=
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app
          ((algebraicToTypes F (U j)).obj (localSheaf j)) ≫
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).mapIso
          ((algebraicLeftOwnerIso F (U j) (U k) (localSheaf j) ≪≫
              (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).symm) ≪≫
            ((algebraicToTypes F (U j ⊓ U k)).mapIso (overlapIso j k)) ≪≫
            (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k) ≪≫
              algebraicRightOwnerIso F (U j) (U k) (localSheaf k)))).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app
          ((algebraicToTypes F (U k)).obj (localSheaf k))
    let leg13 :
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj
            ((algebraicToTypes F (U i)).obj (localSheaf i))) ⟶
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj
            ((algebraicToTypes F (U k)).obj (localSheaf k))) :=
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app
          ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
        ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).mapIso
          ((algebraicLeftOwnerIso F (U i) (U k) (localSheaf i) ≪≫
              (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).symm) ≪≫
            ((algebraicToTypes F (U i ⊓ U k)).mapIso (overlapIso i k)) ≪≫
            (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k) ≪≫
              algebraicRightOwnerIso F (U i) (U k) (localSheaf k)))).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app
          ((algebraicToTypes F (U k)).obj (localSheaf k))
    change leg12 ≫ leg23 = leg13
    let mid := algebraicTripleSecondOwnerIso F (U i) (U j) (U k) (localSheaf j)
    have h12' :
        leg12 =
          (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
            (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
              (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) ≫
            mid.inv := by
      simpa only [leg12, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc] using h12
    have h23' :
        leg23 =
          mid.hom ≫
            (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
              (algebraicTripleOverlapHom23 localSheaf overlapIso i j k) ≫
            (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
      simpa only [leg23, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc] using h23
    calc
      leg12 ≫ leg23 =
          ((algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
            (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
              (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) ≫
            mid.inv) ≫ leg23 := by
        rw [h12']
      _ =
          ((algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
            (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
              (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) ≫
            mid.inv) ≫
          (mid.hom ≫
            (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
              (algebraicTripleOverlapHom23 localSheaf overlapIso i j k) ≫
            (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv) := by
        rw [h23']
      _ =
          (((algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
              (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
                (algebraicTripleOverlapHom12 localSheaf overlapIso i j k)) ≫
            (mid.inv ≫ mid.hom) ≫
            (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
              (algebraicTripleOverlapHom23 localSheaf overlapIso i j k)) ≫
            (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
        simp only [Category.assoc]
      _ =
          (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
            ((algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
                (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) ≫
              (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
                (algebraicTripleOverlapHom23 localSheaf overlapIso i j k)) ≫
            (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
        let m12 :=
          (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            (algebraicTripleOverlapHom12 localSheaf overlapIso i j k)
        let m23 :=
          (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
            (algebraicTripleOverlapHom23 localSheaf overlapIso i j k)
        let last :=
          (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv
        have htail : mid.inv ≫ (mid.hom ≫ (m23 ≫ last)) = m23 ≫ last := by
          simpa only [m23, last, Category.assoc] using
            Iso.inv_hom_id_assoc mid (m23 ≫ last)
        simpa only [m12, m23, last, Category.assoc] using
          congrArg
            (fun t ↦
              (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
                m12 ≫ t)
            htail
      _ =
          (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
            (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
              (algebraicTripleOverlapHom13 localSheaf overlapIso i j k) ≫
            (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
        simpa only [Category.assoc] using
          congrArg
            (fun t ↦
              (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
                t ≫
            (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv)
            hAlg
      _ = leg13 := by
        simpa only [leg13, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
          Functor.mapIso_hom, Functor.map_comp, Category.assoc] using h13.symm
  isCover := hU

abbrev realizationLeftHom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (ℱ : TopCat.Sheaf C X) (φ : ∀ i : ι, (algRestrictToOpen (U i)).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (algRestrictToOpen (U i ⊓ U j)).obj ℱ ⟶
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) :=
  ((algebraicGlobalRestrictionToPairViaLeftIso (U i) (U j)).hom.app ℱ) ≫
    ((algRestrictToPairLeft (U i) (U j)).mapIso (φ i)).hom

abbrev realizationRightHom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (ℱ : TopCat.Sheaf C X) (φ : ∀ i : ι, (algRestrictToOpen (U i)).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (algRestrictToOpen (U i ⊓ U j)).obj ℱ ⟶
      (algRestrictToPairRight (U i) (U j)).obj (localSheaf j) :=
  ((algebraicGlobalRestrictionToPairViaRightIso (U i) (U j)).hom.app ℱ) ≫
    ((algRestrictToPairRight (U i) (U j)).mapIso (φ j)).hom

/-- A `C`-valued sheaf realizes an algebraic gluing datum if its restrictions recover the given
local sheaves and the induced overlap comparisons agree with the prescribed overlap
isomorphisms in `TopCat.Sheaf C`. -/
def Realizes
    (U : ι → Opens X)
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (ℱ : TopCat.Sheaf C X) : Prop :=
  ∃ φ : ∀ i : ι,
      ((U i).isOpenEmbedding.sheafPullback C).obj ℱ ≅ localSheaf i,
    ∀ i j : ι,
      realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
        realizationRightHom localSheaf ℱ φ i j

end AlgebraicSheafOpenCover


end
