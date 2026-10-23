module

public import stacks_project.Chap06.Lemma_6_33_3_Part1

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w

section

/-- Helper for Lemma 6.33.3: identify sheaf pullback composition for `RingCat` with the
adjunction comparison used to prove associativity. -/
theorem sheafPullbackComp_def_ring {W Y Z : TopCat.{w}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp (A := RingCat) f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward RingCat f ⋙ TopCat.Sheaf.pushforward RingCat g =
            TopCat.Sheaf.pushforward RingCat (f ≫ g) from rfl)) := by
  rfl

/-- Helper for Lemma 6.33.3: associativity of pushforwards of `RingCat`-valued sheaves. -/
theorem sheaf_pushforward_assoc_ring {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward RingCat f)
        (eqToIso
          (show TopCat.Sheaf.pushforward RingCat g ⋙ TopCat.Sheaf.pushforward RingCat h =
            TopCat.Sheaf.pushforward RingCat (g ≫ h) from rfl)) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward RingCat f ⋙
            TopCat.Sheaf.pushforward RingCat (g ≫ h) =
          TopCat.Sheaf.pushforward RingCat (f ≫ g ≫ h) from rfl) =
    (Functor.associator
      (TopCat.Sheaf.pushforward RingCat f)
      (TopCat.Sheaf.pushforward RingCat g)
      (TopCat.Sheaf.pushforward RingCat h)).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso
          (show TopCat.Sheaf.pushforward RingCat f ⋙ TopCat.Sheaf.pushforward RingCat g =
            TopCat.Sheaf.pushforward RingCat (f ≫ g) from rfl))
        (TopCat.Sheaf.pushforward RingCat h) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward RingCat (f ≫ g) ⋙ TopCat.Sheaf.pushforward RingCat h =
          TopCat.Sheaf.pushforward RingCat (f ≫ g ≫ h) from rfl) := by
  ext ℱ
  rfl

/-- Helper for Lemma 6.33.3: associativity of pullbacks of `RingCat`-valued sheaves. -/
theorem sheaf_pullback_comp_assoc_ring {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackComp (A := RingCat) f g) ≪≫
      TopCat.Sheaf.pullbackComp (A := RingCat) (f ≫ g) h =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (TopCat.Sheaf.pullbackComp (A := RingCat) g h) _ ≪≫
        TopCat.Sheaf.pullbackComp (A := RingCat) f (g ≫ h) := by
  simpa [sheafPullbackComp_def_ring] using
    (Adjunction.leftAdjointCompIso_assoc
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat h)
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (g ≫ h))
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (f ≫ g))
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (f ≫ g ≫ h))
      (eqToIso
        (show TopCat.Sheaf.pushforward RingCat g ⋙ TopCat.Sheaf.pushforward RingCat h =
          TopCat.Sheaf.pushforward RingCat (g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward RingCat f ⋙ TopCat.Sheaf.pushforward RingCat g =
          TopCat.Sheaf.pushforward RingCat (f ≫ g) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward RingCat (f ≫ g) ⋙ TopCat.Sheaf.pushforward RingCat h =
          TopCat.Sheaf.pushforward RingCat (f ≫ g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward RingCat f ⋙
            TopCat.Sheaf.pushforward RingCat (g ≫ h) =
          TopCat.Sheaf.pushforward RingCat (f ≫ g ≫ h) from rfl))
      (sheaf_pushforward_assoc_ring f g h))

/-- Helper for Lemma 6.33.3: hom-component form of pullback associativity for
`RingCat`-valued sheaves. -/
theorem sheaf_pullback_comp_assoc_hom_ring {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (F : T.Sheaf RingCat) :
    (TopCat.Sheaf.pullback RingCat f).map
          ((TopCat.Sheaf.pullbackComp (A := RingCat) g h).hom.app F) ≫
        (TopCat.Sheaf.pullbackComp (A := RingCat) f (g ≫ h)).hom.app F =
      (TopCat.Sheaf.pullbackComp (A := RingCat) f g).hom.app
          ((TopCat.Sheaf.pullback RingCat h).obj F) ≫
        (TopCat.Sheaf.pullbackComp (A := RingCat) (f ≫ g) h).hom.app F := by
  simpa only [Category.assoc] using
    (congrArg (fun α ↦ α.hom.app F)
      (sheaf_pullback_comp_assoc_ring f g h)).symm

end
