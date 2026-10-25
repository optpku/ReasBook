module

public import stacks_project.Chap06.Lemma_6_33_3_Part5

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

theorem algebraicFixedChartGluing_recoversBasisSection
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    {W0 : BasisOpen (coverSubordinateOpens (U := U))}
    (𝒰 : BasisCover (coverSubordinateOpens (U := U)) W0)
    (s : FamilyOfElementsOnObjects
      ((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F) 𝒰.obj)
    {t0 : F.obj
      ((localSheaf (chosen_chart W0)).1.obj
        (op (subspaceOpenOfLE (chosen_chart_le W0))))}
    (ht0 :
      ∀ i : 𝒰.ι,
        F.map
            ((localSheaf (chosen_chart W0)).1.map
              (subspaceOpenHom
                ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
                (chosen_chart_le W0)
                (𝒰.hom i).hom.le).op)
            t0 =
          F.map
            (algebraicSubsetChartIso localSheaf overlapIso
              (chosen_chart_le (𝒰.obj i))
              ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom
            (s i)) :
    ∀ i : 𝒰.ι,
      ((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F).map
        (𝒰.hom i).op t0 = s i := by
  intro i
  let hIc0 : (𝒰.obj i).obj ≤ U (chosen_chart W0) :=
    (𝒰.hom i).hom.le.trans (chosen_chart_le W0)
  let toFixed :=
    algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le (𝒰.obj i)) hIc0
  let fromFixed :=
    algebraicSubsetChartIso localSheaf overlapIso hIc0 (chosen_chart_le (𝒰.obj i))
  have hround :
      toFixed.hom ≫ fromFixed.hom = 𝟙 _ := by
    calc
      toFixed.hom ≫ fromFixed.hom =
          (algebraicSubsetChartIso localSheaf overlapIso
            (chosen_chart_le (𝒰.obj i))
            (chosen_chart_le (𝒰.obj i))).hom := by
              simpa [toFixed, fromFixed, hIc0] using
                algebraicSubsetChartIso_trans localSheaf overlapIso cocycle
                  (chosen_chart_le (𝒰.obj i)) hIc0 (chosen_chart_le (𝒰.obj i))
      _ = 𝟙 _ := by
            simpa [toFixed, fromFixed] using
              algebraicSubsetChartIso_self_hom localSheaf overlapIso cocycle
                (hWi := chosen_chart_le (𝒰.obj i))
  calc
    ((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F).map
        (𝒰.hom i).op t0 =
      F.map fromFixed.hom
        (F.map
          ((localSheaf (chosen_chart W0)).1.map
            (subspaceOpenHom hIc0 (chosen_chart_le W0) (𝒰.hom i).hom.le).op)
          t0) := by
          simp [algebraicOpenCoverBasisPresheaf, algebraicOpenCoverBasisPresheafMap,
            hIc0, fromFixed, Functor.map_comp, Function.comp_apply]
    _ = F.map fromFixed.hom (F.map toFixed.hom (s i)) := by
          rw [ht0 i]
    _ =
      (show F.obj
          ((localSheaf (chosen_chart (𝒰.obj i))).1.obj
            (op (subspaceOpenOfLE (chosen_chart_le (𝒰.obj i))))) from s i) := by
          change
            (F.map toFixed.hom ≫ F.map fromFixed.hom) (s i) =
              (show F.obj
                ((localSheaf (chosen_chart (𝒰.obj i))).1.obj
                  (op (subspaceOpenOfLE (chosen_chart_le (𝒰.obj i))))) from s i)
          rw [← Functor.map_comp, hround]
          simp

theorem algebraicOpenCoverBasisPresheaf_toTypes_isSheaf
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    Presheaf.IsSheaf
      (basisGrothendieckTopology
        (coverSubordinateOpens (U := U)) (cover_subordinate_opens_isBasis hU))
      ((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F) := by
  refine (basisPresheaf_isSheaf_iff_uniqueGluing_on_cofinal_basis_covers_local
    (X := X)
    (B := coverSubordinateOpens (U := U))
    (hB := cover_subordinate_opens_isBasis hU)
    (Covers := fun _ ↦ Set.univ)
    (hC := ?_)
    (hInterC := ?_)
    (F := ((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F))).2 ?_
  · intro W0 𝒰 _ i j
    refine ⟨chosen_chart (𝒰.obj i), ?_⟩
    intro x hx
    exact (chosen_chart_le (𝒰.obj i)) hx.1
  · intro W0 𝒰
    refine ⟨𝒰, Set.mem_univ _, ?_⟩
    refine ⟨fun i ↦ i, ?_⟩
    intro i
    exact ⟨𝟙 _, by simp⟩
  · intro W0 𝒰 _ s hs
    let c0 := chosen_chart W0
    let cover : 𝒰.ι → Opens (openSubsetSpace (U c0)) :=
      fun i ↦ subspaceOpenOfLE ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
    let iUV : ∀ i : 𝒰.ι, cover i ⟶ subspaceOpenOfLE (chosen_chart_le W0) :=
      fun i ↦
        subspaceOpenHom
          ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))
          (chosen_chart_le W0)
          (𝒰.hom i).hom.le
    have hcover : subspaceOpenOfLE (chosen_chart_le W0) ≤ iSup cover := by
      intro x hx
      rw [Opens.mem_iSup]
      have hxW0 : x.1 ∈ W0.obj := by
        simpa [cover, c0, subspaceOpenOfLEImageEq] using
          (memSubspaceOpenIff (subspaceOpenOfLE (chosen_chart_le W0)) x).1 hx
      have hxW0' : x.1 ∈ ((W0.obj : Opens X) : Set X) := hxW0
      rw [𝒰.iUnion_eq] at hxW0'
      rcases Set.mem_iUnion.mp hxW0' with ⟨i, hxi⟩
      refine ⟨i, ?_⟩
      exact
        (memSubspaceOpenIff (cover i) x).2
          (by simpa [cover, c0, subspaceOpenOfLEImageEq] using hxi)
    have hcompat :=
      algebraicBasisCoverTransportToFixedChart_compatible
        (F := F) (localSheaf := localSheaf) (overlapIso := overlapIso)
        (cocycle := cocycle)
        (𝒰 := 𝒰)
        (hInter := fun i j ↦ by
          refine ⟨chosen_chart (𝒰.obj i), ?_⟩
          intro x hx
          exact (chosen_chart_le (𝒰.obj i)) hx.1)
        (s := s)
        hs
    obtain ⟨t0, ht0, ht0uniq⟩ :=
      (((algebraicToTypes F (U c0)).obj (localSheaf c0))).existsUnique_gluing'
        (V := subspaceOpenOfLE (chosen_chart_le W0))
        (U := cover)
        iUV
        hcover
        (fun i ↦
          F.map
            (algebraicSubsetChartIso localSheaf overlapIso
              (chosen_chart_le (𝒰.obj i))
              ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom
            (s i))
        hcompat
    refine ⟨t0, ?_, ?_⟩
    · exact
        algebraicFixedChartGluing_recoversBasisSection
          (F := F) (localSheaf := localSheaf) (overlapIso := overlapIso)
          (cocycle := cocycle) (𝒰 := 𝒰) (s := s) ht0
    · intro t' ht'
      apply ht0uniq
      intro i
      let hIc0 : (𝒰.obj i).obj ≤ U c0 :=
        (𝒰.hom i).hom.le.trans (chosen_chart_le W0)
      let toFixed :=
        algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le (𝒰.obj i)) hIc0
      let fromFixed :=
        algebraicSubsetChartIso localSheaf overlapIso hIc0 (chosen_chart_le (𝒰.obj i))
      have hround :
          fromFixed.hom ≫ toFixed.hom = 𝟙 _ := by
        calc
          fromFixed.hom ≫ toFixed.hom =
              (algebraicSubsetChartIso localSheaf overlapIso hIc0 hIc0).hom := by
                simpa [toFixed, fromFixed, hIc0] using
                  algebraicSubsetChartIso_trans localSheaf overlapIso cocycle
                    hIc0 (chosen_chart_le (𝒰.obj i)) hIc0
          _ = 𝟙 _ := by
                simpa [toFixed, fromFixed] using
                  algebraicSubsetChartIso_self_hom localSheaf overlapIso cocycle
                    (hWi := hIc0)
      have hmap :
          F.map toFixed.hom
              (((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F).map
                (𝒰.hom i).op t') =
            F.map
              ((localSheaf c0).1.map
                (subspaceOpenHom hIc0 (chosen_chart_le W0) (𝒰.hom i).hom.le).op)
              t' := by
        have h := congrArg (fun f ↦ F.map f) hround
        have h' :=
          congrFun h
            (F.map
              ((localSheaf c0).1.map
                (subspaceOpenHom hIc0 (chosen_chart_le W0) (𝒰.hom i).hom.le).op)
              t')
        simpa [algebraicOpenCoverBasisPresheaf, algebraicOpenCoverBasisPresheafMap,
          toFixed, fromFixed, c0, hIc0, Functor.map_comp, Function.comp_apply] using h'
      calc
        (ConcreteCategory.hom
            (((algebraicToTypes F (U c0)).obj (localSheaf c0)).obj.map (iUV i).op)) t' =
          F.map
            ((localSheaf c0).1.map
              (subspaceOpenHom hIc0 (chosen_chart_le W0) (𝒰.hom i).hom.le).op)
            t' := by
            rfl
        _ =
          F.map toFixed.hom
              (((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F).map
                (𝒰.hom i).op t') := hmap.symm
        _ = F.map toFixed.hom (s i) := by
            rw [ht' i]

theorem algebraicOpenCoverBasisPresheaf_isSheaf
    (F : C ⥤ Type w) [IsAlgebraicStructure C F]
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    Presheaf.IsSheaf
      (basisGrothendieckTopology
        (coverSubordinateOpens (U := U)) (cover_subordinate_opens_isBasis hU))
      (algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) := by
  letI : HasLimitsOfSize.{w, w} C := inferInstance
  letI : PreservesLimitsOfSize.{w, w} F := inferInstance
  exact
    (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp
      (basisGrothendieckTopology
        (coverSubordinateOpens (U := U)) (cover_subordinate_opens_isBasis hU))
      (algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) F).2
      (algebraicOpenCoverBasisPresheaf_toTypes_isSheaf
        (F := F) localSheaf overlapIso cocycle hU)

noncomputable def algebraicOpenCoverBasisSheaf
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    BasisSiteSheaf C (coverSubordinateOpens (U := U)) (cover_subordinate_opens_isBasis hU) where
  obj := algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle
  property := algebraicOpenCoverBasisPresheaf_isSheaf
    (F := F) localSheaf overlapIso cocycle hU

def algebraicMemberSubordinateOpens (i : ι) :
    Set (Opens (openSubsetSpace (U i))) :=
  { V | ∃ W : Opens X, ∃ hWi : W ≤ U i, subspaceOpenOfLE hWi = V }

theorem algebraicMemberSubordinateOpenRepresentation
    (i : ι) (V : Opens (openSubsetSpace (U i))) :
    ∃ W : Opens X, ∃ hWi : W ≤ U i, subspaceOpenOfLE hWi = V :=
  openSubsetOpenRepresentation V

theorem algebraicMemberSubordinateOpens_isBasis
    (i : ι) :
    Opens.IsBasis (algebraicMemberSubordinateOpens (U := U) i) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨W, hWi, rfl⟩ := algebraicMemberSubordinateOpenRepresentation (U := U) i V
  refine ⟨subspaceOpenOfLE hWi, ?_, hx, le_rfl⟩
  exact ⟨W, hWi, rfl⟩

theorem algebraicMemberSubordinateOpenHomRepresentation
    (i : ι)
    {V W : (BasisOpen (algebraicMemberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W)
    {V₀ : Opens X}
    (hVi : V₀ ≤ U i)
    (hV : subspaceOpenOfLE hVi = V.unop.obj) :
    ∃ (W₀ : Opens X) (hWi : W₀ ≤ U i)
      (hW : subspaceOpenOfLE hWi = W.unop.obj) (hWV : W₀ ≤ V₀),
      eqToHom hW ≫ f.unop.hom =
        subspaceOpenHom hWi hVi hWV ≫ eqToHom hV := by
  obtain ⟨W₀, hWi, hW⟩ :=
    algebraicMemberSubordinateOpenRepresentation (U := U) i W.unop.obj
  have hWV : W₀ ≤ V₀ := by
    intro x hx
    have hxWsub : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ W.unop.obj := by
      have hxWbase : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ subspaceOpenOfLE hWi := by
        exact (memSubspaceOpenIff (subspaceOpenOfLE hWi) ⟨x, hWi hx⟩).2
          (by simpa [subspaceOpenOfLEImageEq] using hx)
      simpa [hW] using hxWbase
    have hxVsub : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ V.unop.obj :=
      f.unop.hom.down.down hxWsub
    have hxVbase : (⟨x, hWi hx⟩ : openSubsetSpace (U i)) ∈ subspaceOpenOfLE hVi := by
      simpa [hV] using hxVsub
    exact
      by
        simpa [subspaceOpenOfLEImageEq] using
          (memSubspaceOpenIff (subspaceOpenOfLE hVi) ⟨x, hWi hx⟩).1 hxVbase
  refine ⟨W₀, hWi, hW, hWV, ?_⟩
  apply Subsingleton.elim

theorem algebraicMemberSubordinateOpenRepresentationUnique
    (i : ι) {V : Opens (openSubsetSpace (U i))}
    {W₁ W₂ : Opens X}
    (h₁ : W₁ ≤ U i) (h₂ : W₂ ≤ U i)
    (e₁ : subspaceOpenOfLE h₁ = V) (e₂ : subspaceOpenOfLE h₂ = V) :
    W₁ = W₂ := by
  have h :=
    congrArg (fun A ↦ (subspaceInclusionFunctor (U i)).obj A) (e₁.trans e₂.symm)
  simpa [subspaceOpenOfLEImageEq] using h

theorem subspaceInclusionFunctorMapEqHomOfLE
    (i : ι) {W V : Opens X}
    (hWi : W ≤ U i) (hVi : V ≤ U i) (hWV : W ≤ V) :
    eqToHom (subspaceOpenOfLEImageEq hWi).symm ≫
        (subspaceInclusionFunctor (U i)).map (subspaceOpenHom hWi hVi hWV) =
      homOfLE hWV ≫ eqToHom (subspaceOpenOfLEImageEq hVi).symm := by
  apply Subsingleton.elim

noncomputable def algebraicGlobalMemberSectionIso
    (ℱ : TopCat.Sheaf C X) {W : Opens X} {i : ι} (hWi : W ≤ U i) :
    (((algRestrictToOpen (U i)).obj ℱ)).1.obj
        (op (subspaceOpenOfLE hWi)) ≅
      ℱ.1.obj (op W) :=
  eqToIso (by
    change
      ℱ.1.obj (op ((subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hWi))) =
        ℱ.1.obj (op W)
    simpa [subspaceOpenOfLEImageEq])

theorem algebraicGlobalMemberSectionIso_naturality
    (ℱ : TopCat.Sheaf C X) (i : ι)
    {W V : Opens X} (hWi : W ≤ U i) (hVi : V ≤ U i) (hWV : W ≤ V) :
    ((((algRestrictToOpen (U i)).obj ℱ)).1.map
        (subspaceOpenHom hWi hVi hWV).op) ≫
      (algebraicGlobalMemberSectionIso (U := U) ℱ (i := i) hWi).hom =
    (algebraicGlobalMemberSectionIso (U := U) ℱ (i := i) hVi).hom ≫
      ℱ.1.map (homOfLE hWV).op := by
  let pW :
      ℱ.1.obj (op ((subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hWi))) =
        ℱ.1.obj (op W) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V)) (subspaceOpenOfLEImageEq hWi)
  let pV :
      ℱ.1.obj (op ((subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hVi))) =
        ℱ.1.obj (op V) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V)) (subspaceOpenOfLEImageEq hVi)
  have hw :
      ℱ.1.map (eqToHom (subspaceOpenOfLEImageEq hWi).symm).op = eqToHom pW := by
    have hw' :
        ℱ.1.map (eqToHom (subspaceOpenOfLEImageEq hWi).symm).op =
          eqToHom (congrArg (fun V ↦ ℱ.1.obj (op V)) (subspaceOpenOfLEImageEq hWi)) := by
      simpa using
        (CategoryTheory.eqToHom_map ℱ.1
          (congrArg Opposite.op (subspaceOpenOfLEImageEq hWi)))
    simpa [pW] using hw'
  have hv :
      ℱ.1.map (eqToHom (subspaceOpenOfLEImageEq hVi).symm).op = eqToHom pV := by
    have hv' :
        ℱ.1.map (eqToHom (subspaceOpenOfLEImageEq hVi).symm).op =
          eqToHom (congrArg (fun V ↦ ℱ.1.obj (op V)) (subspaceOpenOfLEImageEq hVi)) := by
      simpa using
        (CategoryTheory.eqToHom_map ℱ.1
          (congrArg Opposite.op (subspaceOpenOfLEImageEq hVi)))
    simpa [pV] using hv'
  have hmap' := congrArg (fun k ↦ ℱ.1.map k.op)
    (subspaceInclusionFunctorMapEqHomOfLE (U := U) i hWi hVi hWV)
  have hmap :
      ℱ.1.map (((subspaceInclusionFunctor (U i)).map
          (subspaceOpenHom hWi hVi hWV)).op) ≫
        eqToHom pW =
      eqToHom pV ≫ ℱ.1.map (homOfLE hWV).op := by
    rw [← hw, ← hv, ← Functor.map_comp, ← Functor.map_comp]
    exact hmap'
  simpa [algebraicGlobalMemberSectionIso, Topology.IsOpenEmbedding.sheafPullback,
    pW, pV, Category.assoc] using hmap

noncomputable def algebraicCoverBasisRestrictExtendComponentIso
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (W : BasisOpen (coverSubordinateOpens (U := U))) :
    ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend).1.obj
        (op W.obj) ≅
      (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).presheaf.obj
        (op W) where
  hom :=
    BasisSiteSheaf.restrictExtendComponentInv
      (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU) (op W)
  inv :=
    BasisSiteSheaf.restrictExtendComponentHom
      (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU) (op W)
  hom_inv_id := by
    exact
      BasisSiteSheaf.restrictExtend_component_inv_hom_id
        (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU) (op W)
  inv_hom_id := by
    exact
      BasisSiteSheaf.restrictExtend_component_hom_inv_id
        (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU) (op W)

theorem algebraicCoverBasisRestrictExtendComponent_naturality
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    {W V : BasisOpen (coverSubordinateOpens (U := U))}
    (k : W ⟶ V) :
    (((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend).1.map
        k.hom.op) ≫
      (algebraicCoverBasisRestrictExtendComponentIso
        F localSheaf overlapIso cocycle hU W).hom =
    (algebraicCoverBasisRestrictExtendComponentIso
        F localSheaf overlapIso cocycle hU V).hom ≫
      (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).presheaf.map
        k.op := by
  simpa [algebraicCoverBasisRestrictExtendComponentIso, BasisSiteSheaf.presheaf] using
    BasisSiteSheaf.restrictExtendInv_naturality
      (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU)
      (i := k.op)

noncomputable abbrev algebraicMemberSpaceBasisComponentIsoOfRep
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    (((algRestrictToOpen (U i)).obj
      ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend))).1.obj
        (op (subspaceOpenOfLE hWi)) ≅
      (localSheaf i).1.obj (op (subspaceOpenOfLE hWi)) :=
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  (algebraicGlobalMemberSectionIso (U := U) ℱ hWi) ≪≫
    (algebraicCoverBasisRestrictExtendComponentIso
      F localSheaf overlapIso cocycle hU ambientW) ≪≫
    (algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le ambientW) hWi)

theorem algebraicMemberSpaceBasisComponentIsoOfRep_congr
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W : Opens X}
    {hWi₁ hWi₂ : W ≤ U i} :
    algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi₁ =
      algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi₂ := by
  cases Subsingleton.elim hWi₁ hWi₂
  rfl

theorem algebraicMemberSpaceBasisComponentIso_eq_of_rep_transport
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W W' : Opens X}
    (hWi : W ≤ U i) (hW'i : W' ≤ U i)
    (hV : subspaceOpenOfLE hW'i = subspaceOpenOfLE hWi)
    (hWW' : W' = W) :
    let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
    let pLeft :
        (((algRestrictToOpen (U i)).obj ℱ)).1.obj
            (op (subspaceOpenOfLE hWi)) =
          (((algRestrictToOpen (U i)).obj ℱ)).1.obj
            (op (subspaceOpenOfLE hW'i)) := by
      simpa [hV] using
        congrArg
          (fun A ↦ (((algRestrictToOpen (U i)).obj ℱ)).1.obj (op A))
          hV.symm
    let pRight :
        (localSheaf i).1.obj (op (subspaceOpenOfLE hW'i)) =
          (localSheaf i).1.obj (op (subspaceOpenOfLE hWi)) := by
      simpa [hV] using congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hV
    (eqToIso pLeft) ≪≫
        algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hW'i ≪≫
        (eqToIso pRight) =
      algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi := by
  subst hWW'
  have hhWi : hW'i = hWi := Subsingleton.elim _ _
  subst hhWi
  have hhV : hV = rfl := Subsingleton.elim _ _
  subst hhV
  simp

noncomputable def algebraicMemberSpaceBasisComponentIso
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    (V : BasisOpen (algebraicMemberSubordinateOpens (U := U) i)) :
    (((algRestrictToOpen (U i)).obj
      ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend))).1.obj
        (op V.obj) ≅
      (localSheaf i).1.obj (op V.obj) := by
  classical
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let hVrep := algebraicMemberSubordinateOpenRepresentation (U := U) i V.obj
  let W : Opens X := Classical.choose hVrep
  let hWrep : ∃ hWi : W ≤ U i, subspaceOpenOfLE hWi = V.obj :=
    Classical.choose_spec hVrep
  let hWi : W ≤ U i := Classical.choose hWrep
  let hV : subspaceOpenOfLE hWi = V.obj := Classical.choose_spec hWrep
  let pLeft :
      (((algRestrictToOpen (U i)).obj ℱ)).1.obj (op V.obj) =
        (((algRestrictToOpen (U i)).obj ℱ)).1.obj (op (subspaceOpenOfLE hWi)) := by
    simpa [hV] using
      congrArg
        (fun A ↦ (((algRestrictToOpen (U i)).obj ℱ)).1.obj (op A))
        hV.symm
  let pRight :
      (localSheaf i).1.obj (op (subspaceOpenOfLE hWi)) =
        (localSheaf i).1.obj (op V.obj) := by
    simpa [hV] using congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hV
  exact
    (eqToIso pLeft) ≪≫
      algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi ≪≫
      (eqToIso pRight)

theorem algebraicMemberSpaceBasisComponentIso_eq_of_rep
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    algebraicMemberSpaceBasisComponentIso
        F localSheaf overlapIso cocycle hU i
        ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩ =
      algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi := by
  classical
  let V : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
    ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
  let hVrep := algebraicMemberSubordinateOpenRepresentation (U := U) i V.obj
  let W' : Opens X := Classical.choose hVrep
  let hWrep : ∃ hW'i : W' ≤ U i, subspaceOpenOfLE hW'i = V.obj :=
    Classical.choose_spec hVrep
  let hW'i : W' ≤ U i := Classical.choose hWrep
  let hV : subspaceOpenOfLE hW'i = V.obj := Classical.choose_spec hWrep
  have hWW' : W' = W := by
    simpa [V] using
      algebraicMemberSubordinateOpenRepresentationUnique (U := U) i hW'i hWi hV rfl
  simpa [algebraicMemberSpaceBasisComponentIso, V, hVrep, W', hWrep, hW'i, hV] using
    algebraicMemberSpaceBasisComponentIso_eq_of_rep_transport
      F localSheaf overlapIso cocycle hU i hWi hW'i (by simpa [V] using hV) hWW'

theorem algebraicMemberSpaceBasisComponent_naturality_of_rep
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W V : Opens X}
    (hWi : W ≤ U i) (hVi : V ≤ U i) (hWV : W ≤ V) :
    ((((algRestrictToOpen (U i)).obj
        ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend))).1.map
        (subspaceOpenHom hWi hVi hWV).op) ≫
      (algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi).hom =
    (algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hVi).hom ≫
      (localSheaf i).1.map (subspaceOpenHom hWi hVi hWV).op := by
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  let ambientV : BasisOpen (coverSubordinateOpens (U := U)) := ⟨V, ⟨i, hVi⟩⟩
  let subsetW := algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le ambientW) hWi
  let subsetV := algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le ambientV) hVi
  let k : ambientW ⟶ ambientV := ⟨homOfLE hWV⟩
  have hglobal :=
    algebraicGlobalMemberSectionIso_naturality (U := U) ℱ i hWi hVi hWV
  have hcover :=
    algebraicCoverBasisRestrictExtendComponent_naturality
      (F := F) localSheaf overlapIso cocycle hU k
  have hbasis :
      ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).presheaf.map
          k.op) ≫ subsetW.hom =
        subsetV.hom ≫ (localSheaf i).1.map (subspaceOpenHom hWi hVi hWV).op := by
    let hVcV : V ≤ U (chosen_chart ambientV) := chosen_chart_le ambientV
    let hWcV : W ≤ U (chosen_chart ambientV) := hWV.trans hVcV
    let hWcW : W ≤ U (chosen_chart ambientW) := chosen_chart_le ambientW
    have htrans :
        (algebraicSubsetChartIso localSheaf overlapIso hWcV hWcW).hom ≫
          subsetW.hom =
        (algebraicSubsetChartIso localSheaf overlapIso hWcV hWi).hom := by
      simpa [subsetW, ambientW, Category.assoc] using
        algebraicSubsetChartIso_trans localSheaf overlapIso cocycle hWcV hWcW hWi
    have hnat :=
      algebraicSubsetChartIso_naturality localSheaf overlapIso
        (hVW := hWV) (hVi := hWcV) (hVj := hWi)
        (hWi := hVcV) (hWj := hVi)
    calc
      ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).presheaf.map
          k.op) ≫ subsetW.hom =
          ((localSheaf (chosen_chart ambientV)).1.map
              (subspaceOpenHom hWcV hVcV hWV).op ≫
            (algebraicSubsetChartIso localSheaf overlapIso hWcV hWcW).hom) ≫
              subsetW.hom := by
            rfl
      _ =
          (localSheaf (chosen_chart ambientV)).1.map
              (subspaceOpenHom hWcV hVcV hWV).op ≫
            (algebraicSubsetChartIso localSheaf overlapIso hWcV hWi).hom := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  (localSheaf (chosen_chart ambientV)).1.map
                    (subspaceOpenHom hWcV hVcV hWV).op ≫ t)
                htrans
      _ =
          subsetV.hom ≫ (localSheaf i).1.map (subspaceOpenHom hWi hVi hWV).op := by
            simpa [subsetV, hWcV] using hnat
  calc
    ((((algRestrictToOpen (U i)).obj ℱ)).1.map
          (subspaceOpenHom hWi hVi hWV).op) ≫
        (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hWi).hom
        =
      ((((algRestrictToOpen (U i)).obj ℱ)).1.map
            (subspaceOpenHom hWi hVi hWV).op) ≫
          (algebraicGlobalMemberSectionIso (U := U) ℱ hWi).hom ≫
          (algebraicCoverBasisRestrictExtendComponentIso
            F localSheaf overlapIso cocycle hU ambientW).hom ≫
          subsetW.hom := by
            rfl
    _ =
      (algebraicGlobalMemberSectionIso (U := U) ℱ hVi).hom ≫
          ℱ.1.map (homOfLE hWV).op ≫
          (algebraicCoverBasisRestrictExtendComponentIso
            F localSheaf overlapIso cocycle hU ambientW).hom ≫
          subsetW.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  t ≫
                    (algebraicCoverBasisRestrictExtendComponentIso
                      F localSheaf overlapIso cocycle hU ambientW).hom ≫
                      subsetW.hom)
                hglobal
    _ =
      (algebraicGlobalMemberSectionIso (U := U) ℱ hVi).hom ≫
          (algebraicCoverBasisRestrictExtendComponentIso
            F localSheaf overlapIso cocycle hU ambientV).hom ≫
          ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).presheaf.map
            k.op) ≫
          subsetW.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  (algebraicGlobalMemberSectionIso (U := U) ℱ hVi).hom ≫ t ≫ subsetW.hom)
                hcover
    _ =
      (algebraicGlobalMemberSectionIso (U := U) ℱ hVi).hom ≫
          (algebraicCoverBasisRestrictExtendComponentIso
            F localSheaf overlapIso cocycle hU ambientV).hom ≫
          subsetV.hom ≫
          (localSheaf i).1.map (subspaceOpenHom hWi hVi hWV).op := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  (algebraicGlobalMemberSectionIso (U := U) ℱ hVi).hom ≫
                    (algebraicCoverBasisRestrictExtendComponentIso
                      F localSheaf overlapIso cocycle hU ambientV).hom ≫ t)
                hbasis
    _ =
      (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hVi).hom ≫
        (localSheaf i).1.map (subspaceOpenHom hWi hVi hWV).op := by
            simp [algebraicMemberSpaceBasisComponentIsoOfRep, ℱ, ambientV, subsetV,
              Category.assoc]

theorem algebraicMemberBasisRestrictFromSheafMapTransport
    (i : ι)
    {Fext : TopCat.Sheaf C (openSubsetSpace (U i))}
    {V W : (BasisOpen (algebraicMemberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W)
    {V₀ W₀ : Opens X}
    (hVi : V₀ ≤ U i) (hWi : W₀ ≤ U i)
    (hV : subspaceOpenOfLE hVi = V.unop.obj)
    (hW : subspaceOpenOfLE hWi = W.unop.obj)
    (hWV : W₀ ≤ V₀)
    (hcomp : eqToHom hW ≫ f.unop.hom = subspaceOpenHom hWi hVi hWV ≫ eqToHom hV) :
    (algebraicBasisSiteRestrictFromSheaf
        (algebraicMemberSubordinateOpens_isBasis (U := U) i) Fext).presheaf.map f ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW.symm) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV.symm) ≫
      Fext.1.map (subspaceOpenHom hWi hVi hWV).op := by
  change Fext.1.map f.unop.hom.op ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW.symm) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV.symm) ≫
      Fext.1.map (subspaceOpenHom hWi hVi hWV).op
  have hcomp' :
      f.unop.hom =
        eqToHom hW.symm ≫ subspaceOpenHom hWi hVi hWV ≫ eqToHom hV := by
    simpa [Category.assoc] using congrArg (fun t ↦ eqToHom hW.symm ≫ t) hcomp
  have hmap := congrArg (fun k ↦ Fext.1.map k.op) hcomp'
  have hmap' :=
    congrArg
      (fun t ↦ t ≫ eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW.symm))
      hmap
  simpa [Functor.map_comp, Category.assoc, eqToHom_map] using hmap'

theorem algebraicMemberBasisRestrictTargetMapTransport
    (i : ι)
    {Fext : TopCat.Sheaf C (openSubsetSpace (U i))}
    {V W : (BasisOpen (algebraicMemberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W)
    {V₀ W₀ : Opens X}
    (hVi : V₀ ≤ U i) (hWi : W₀ ≤ U i)
    (hV : subspaceOpenOfLE hVi = V.unop.obj)
    (hW : subspaceOpenOfLE hWi = W.unop.obj)
    (hWV : W₀ ≤ V₀)
    (hcomp : eqToHom hW ≫ f.unop.hom = subspaceOpenHom hWi hVi hWV ≫ eqToHom hV) :
    Fext.1.map (subspaceOpenHom hWi hVi hWV).op ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV) ≫
      (algebraicBasisSiteRestrictFromSheaf
        (algebraicMemberSubordinateOpens_isBasis (U := U) i) Fext).presheaf.map f := by
  change Fext.1.map (subspaceOpenHom hWi hVi hWV).op ≫
      eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW) =
    eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hV) ≫
      Fext.1.map f.unop.hom.op
  have hcomp' :
      subspaceOpenHom hWi hVi hWV =
        eqToHom hW ≫ f.unop.hom ≫ eqToHom hV.symm := by
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ eqToHom hV.symm) hcomp.symm
  have hmap := congrArg (fun k ↦ Fext.1.map k.op) hcomp'
  have hmap' :=
    congrArg
      (fun t ↦ t ≫ eqToHom (congrArg (fun A ↦ Fext.1.obj (op A)) hW))
      hmap
  simpa [Functor.map_comp, Category.assoc, eqToHom_map] using hmap'

theorem algebraicMemberSpaceBasisComponent_naturality
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {V W : (BasisOpen (algebraicMemberSubordinateOpens (U := U) i))ᵒᵖ}
    (f : V ⟶ W) :
    (algebraicBasisSiteRestrictFromSheaf
      (algebraicMemberSubordinateOpens_isBasis (U := U) i)
      (((algRestrictToOpen (U i)).obj
        ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend)))).presheaf.map
      f ≫
      (algebraicMemberSpaceBasisComponentIso
        F localSheaf overlapIso cocycle hU i W.unop).hom =
    (algebraicMemberSpaceBasisComponentIso
        F localSheaf overlapIso cocycle hU i V.unop).hom ≫
      (algebraicBasisSiteRestrictFromSheaf
        (algebraicMemberSubordinateOpens_isBasis (U := U) i)
        (localSheaf i)).presheaf.map f := by
  classical
  let hVrep := algebraicMemberSubordinateOpenRepresentation (U := U) i V.unop.obj
  let V₀ : Opens X := Classical.choose hVrep
  let hVrep' : ∃ hVi : V₀ ≤ U i, subspaceOpenOfLE hVi = V.unop.obj :=
    Classical.choose_spec hVrep
  let hVi : V₀ ≤ U i := Classical.choose hVrep'
  let hV : subspaceOpenOfLE hVi = V.unop.obj := Classical.choose_spec hVrep'
  let hWrep := algebraicMemberSubordinateOpenRepresentation (U := U) i W.unop.obj
  let W₀ : Opens X := Classical.choose hWrep
  let hWrep' : ∃ hWi : W₀ ≤ U i, subspaceOpenOfLE hWi = W.unop.obj :=
    Classical.choose_spec hWrep
  let hWi : W₀ ≤ U i := Classical.choose hWrep'
  let hW : subspaceOpenOfLE hWi = W.unop.obj := Classical.choose_spec hWrep'
  obtain ⟨W₁, hWi₁, hW₁, hW₁V, hf₁⟩ :=
    algebraicMemberSubordinateOpenHomRepresentation (U := U) i f hVi hV
  have hWeq : W₁ = W₀ :=
    algebraicMemberSubordinateOpenRepresentationUnique (U := U) i hWi₁ hWi hW₁ hW
  subst hWeq
  have hhWi : hWi₁ = hWi := Subsingleton.elim _ _
  subst hhWi
  have hcomp :
      eqToHom hW ≫ f.unop.hom =
        subspaceOpenHom hWi hVi hW₁V ≫ eqToHom hV := by
    simpa using hf₁
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let Fsource := ((algRestrictToOpen (U i)).obj ℱ)
  have hsource :=
    algebraicMemberBasisRestrictFromSheafMapTransport
      (F := F) (U := U) (i := i) (Fext := Fsource) (V := V) (W := W) (f := f)
      (hVi := hVi) (hWi := hWi) (hV := hV) (hW := hW)
      (hWV := hW₁V) hcomp
  have hrep :=
    algebraicMemberSpaceBasisComponent_naturality_of_rep
      (F := F) localSheaf overlapIso cocycle hU i hWi hVi hW₁V
  have htarget :=
    algebraicMemberBasisRestrictTargetMapTransport
      (F := F) (U := U) (i := i) (Fext := localSheaf i) (V := V) (W := W) (f := f)
      (hVi := hVi) (hWi := hWi) (hV := hV) (hW := hW)
      (hWV := hW₁V) hcomp
  have hstep₁ :
      (algebraicBasisSiteRestrictFromSheaf
          (algebraicMemberSubordinateOpens_isBasis (U := U) i) Fsource).presheaf.map f ≫
        eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hW.symm) ≫
        (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hWi).hom ≫
        eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hW) =
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        Fsource.1.map (subspaceOpenHom hWi hVi hW₁V).op ≫
        (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hWi).hom ≫
        eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hW) := by
    let c :=
      (algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi).hom
    let d := eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hW)
    have h :=
      congrArg (fun k ↦ k ≫ c ≫ d) hsource
    calc
      (algebraicBasisSiteRestrictFromSheaf
          (algebraicMemberSubordinateOpens_isBasis (U := U) i) Fsource).presheaf.map f ≫
        eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hW.symm) ≫ c ≫ d
          =
        ((algebraicBasisSiteRestrictFromSheaf
          (algebraicMemberSubordinateOpens_isBasis (U := U) i) Fsource).presheaf.map f ≫
            eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hW.symm)) ≫ c ≫ d := by
            simp [Category.assoc]
      _ =
        (eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
          Fsource.1.map (subspaceOpenHom hWi hVi hW₁V).op) ≫ c ≫ d := by
            simpa only [] using h
      _ =
        eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
          Fsource.1.map (subspaceOpenHom hWi hVi hW₁V).op ≫ c ≫ d := by
            simp [Category.assoc]
  have hstep₂ :
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        Fsource.1.map (subspaceOpenHom hWi hVi hW₁V).op ≫
        (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hWi).hom ≫
        eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hW) =
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hVi).hom ≫
        (localSheaf i).1.map (subspaceOpenHom hWi hVi hW₁V).op ≫
        eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hW) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
            k ≫ eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hW))
        hrep
  have hstep₃ :
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hVi).hom ≫
        (localSheaf i).1.map (subspaceOpenHom hWi hVi hW₁V).op ≫
        eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hW) =
      eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
        (algebraicMemberSpaceBasisComponentIsoOfRep
          F localSheaf overlapIso cocycle hU i hVi).hom ≫
        eqToHom (congrArg (fun A ↦ (localSheaf i).1.obj (op A)) hV) ≫
        (algebraicBasisSiteRestrictFromSheaf
          (algebraicMemberSubordinateOpens_isBasis (U := U) i) (localSheaf i)).presheaf.map f := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          eqToHom (congrArg (fun A ↦ Fsource.1.obj (op A)) hV.symm) ≫
            (algebraicMemberSpaceBasisComponentIsoOfRep
              F localSheaf overlapIso cocycle hU i hVi).hom ≫ k)
        htarget
  exact
    (by
      simpa [algebraicMemberSpaceBasisComponentIso, Fsource, ℱ, Category.assoc] using
        hstep₁.trans (hstep₂.trans hstep₃))


end
