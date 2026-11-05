module

public import stacks_project.Chap06.Glueing_data_for_sheaves_on_an_open_cover
public import stacks_project.Chap06.Definition_6_30_2
public import stacks_project.Chap06.Lemma_6_30_6

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w

namespace Lemma_6_33_3_OpenEmbeddingAux

@[simp] theorem sheaf_id_hom_app {Y : TopCat.{w}} (G : Y.Sheaf (Type w)) (V) :
    ((𝟙 G : G ⟶ G).hom.app V) = 𝟙 _ := rfl

theorem leftAdjointUniq_comp_second_app
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ F₁₂' : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₁₂' : F₁₂' ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂')).hom.app X =
      (Adjunction.leftAdjointUniq adj₁₂ adj₁₂').hom.app (F₀₁.obj X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂'.obj (F₀₁.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁.comp adj₁₂')).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        ((adj₁₂.leftAdjointUniq adj₁₂').hom.app (F₀₁.obj X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂') X]
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj₁₂ adj₁₂' (F₀₁.obj X)
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h.symm

theorem leftAdjointUniq_comp_first_app
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ F₀₁' : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₀₁' : F₀₁' ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂)).hom.app X =
      F₁₂.map ((Adjunction.leftAdjointUniq adj₀₁ adj₀₁').hom.app X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂.obj (F₀₁'.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁'.comp adj₁₂)).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (F₁₂.map ((adj₀₁.leftAdjointUniq adj₀₁').hom.app X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂) X]
  let α := (adj₀₁.leftAdjointUniq adj₀₁').hom.app X
  have h₁ : adj₀₁.unit.app X ≫ G₁₀.map α = adj₀₁'.unit.app X := by
    simpa [α] using Adjunction.unit_leftAdjointUniq_hom_app adj₀₁ adj₀₁' X
  have h₂ :
      α ≫ adj₁₂.unit.app (F₀₁'.obj X) =
        adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α) := by
    simpa [α] using adj₁₂.unit.naturality α
  have hcalc :
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) =
        adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
          G₁₀.map (G₂₁.map (F₁₂.map α)) := by
    calc
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))
          =
        (adj₀₁.unit.app X ≫ G₁₀.map α) ≫
          G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))) h₁.symm
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map (α ≫ adj₁₂.unit.app (F₀₁'.obj X)) := by
            simp [Functor.map_comp, Category.assoc]
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map
            (adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α)) := by
            simpa using congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h₂
      _ =
      adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
        G₁₀.map (G₂₁.map (F₁₂.map α)) := by
          simp [Functor.map_comp]
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp,
    Category.assoc, α] using hcalc

theorem sheafPullbackComp_def {W Y Z : TopCat.{w}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp (A := Type w) f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
            TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl)) := by
  rfl

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

noncomputable def openEmbeddingSheafPullbackIso
    {Y Z : TopCat.{w}} {f : Y ⟶ Z} (hf : IsOpenEmbedding f) :
    TopCat.Sheaf.pullback (Type w) f ≅ hf.sheafPullback (Type w) :=
  haveI := hf.functor_isContinuous
  Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
    (hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z))

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

end Lemma_6_33_3_OpenEmbeddingAux
