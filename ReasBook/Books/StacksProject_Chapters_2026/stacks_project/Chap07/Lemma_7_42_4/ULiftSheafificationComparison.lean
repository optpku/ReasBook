module

public import stacks_project.Chap07.Lemma_7_28_5.TypeSheafification
public import stacks_project.Chap07.Lemma_7_42_4.TypeLocalBijectivity

@[expose] public section

open CategoryTheory Opposite CategoryTheory.GrothendieckTopology.Plus

universe u₁ u₂ u₃ v₁ v₂ v₃ w r

namespace CategoryTheory.Functor

/-- Helper for Lemma 7.42.4: if the small universe `Type w` carried the extra multicospan-limit
and cover-colimit owners used by the concrete sheafification theorem, then the relevant `ULift`
functor would preserve sheafification by the generic concrete-category criterion. -/
theorem uliftFunctor_preservesSheafification_type_of_small_owners
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan J') (Type w)]
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  -- Supply the small-owner hypotheses explicitly so the generic concrete-category theorem applies
  -- without the global instance-search timeout seen in the unconditional goal.
  let _ :
      ∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
        Limits.HasLimitsOfShape (Limits.WalkingMulticospan J') Ts := by
    intro J'
    infer_instance
  let _ : ∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ Ts := by
    intro X
    infer_instance
  let _ : ∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ F := by
    intro X
    infer_instance
  let _ :
      ∀ (X : E) (S : L.Cover X) (P : Eᵒᵖ ⥤ Type w),
        Limits.PreservesLimit (S.index P).multicospan F := by
    intro X S P
    infer_instance
  let _ : Limits.PreservesLimitsOfSize.{max v₃ u₃, max v₃ u₃} (forget (Type w)) := by
    infer_instance
  let _ : Limits.PreservesLimitsOfSize.{max v₃ u₃, max v₃ u₃} (forget Ts) := by
    infer_instance
  let _ : (forget (Type w)).ReflectsIsomorphisms := by
    infer_instance
  let _ : (forget Ts).ReflectsIsomorphisms := by
    infer_instance
  simpa [F] using
    (CategoryTheory.GrothendieckTopology.instPreservesSheafification
      (J := L) (F := F))

/-- Helper for Lemma 7.42.4: the owner comparison against `plusPlusAdjunction` factors through
the `plusPlusSheafIsoPresheafToSheaf` isomorphism and the large sheafification comparison. -/
theorem ulift_plus_plus_comparison_component_fac
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    (((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))).hom ≫
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P) =
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let α :
      (plusPlusSheaf L Ts).obj (P ⋙ F) ⟶
        (sheafCompose L F).obj ((presheafToSheaf L (Type w)).obj P) :=
    ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫
      (sheafComposeNatTrans L F
        (sheafificationAdjunction L (Type w))
        (sheafificationAdjunction L Ts)).app P
  apply sheafComposeNatTrans_app_uniq
  -- First rewrite the `plus-plus` unit through the comparison with abstract sheafification.
  change
    (plusPlusAdjunction L Ts).unit.app (P ⋙ F) ≫
        (sheafToPresheaf L Ts).map α =
      Functor.whiskerRight ((sheafificationAdjunction L (Type w)).unit.app P) F
  simp only [α, Functor.map_comp]
  change
    L.toSheafify (P ⋙ F) ≫
        (sheafToPresheaf L Ts).map ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫
          (sheafToPresheaf L Ts).map
            ((sheafComposeNatTrans L F
              (sheafificationAdjunction L (Type w))
              (sheafificationAdjunction L Ts)).app P) =
      Functor.whiskerRight ((sheafificationAdjunction L (Type w)).unit.app P) F
  have hplus :
      L.toSheafify (P ⋙ F) ≫
          (sheafToPresheaf L Ts).map ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom =
        toSheafify L (P ⋙ F) := by
    simpa [plusPlusIsoSheafify] using
      (toSheafify_plusPlusIsoSheafify_hom (J := L) (D := Ts) (P := P ⋙ F))
  have hplus' :
      L.toSheafify (P ⋙ F) ≫
          (sheafToPresheaf L Ts).map ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫
            (sheafToPresheaf L Ts).map
              ((sheafComposeNatTrans L F
                (sheafificationAdjunction L (Type w))
                (sheafificationAdjunction L Ts)).app P) =
        toSheafify L (P ⋙ F) ≫
          (sheafToPresheaf L Ts).map
            ((sheafComposeNatTrans L F
              (sheafificationAdjunction L (Type w))
              (sheafificationAdjunction L Ts)).app P) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ (sheafToPresheaf L Ts).map
            ((sheafComposeNatTrans L F
              (sheafificationAdjunction L (Type w))
              (sheafificationAdjunction L Ts)).app P))
        hplus
  rw [hplus']
  -- The remaining identity is exactly the defining factorization of `sheafComposeNatTrans`.
  simpa [Ts, F] using
    sheafComposeNatTrans_fac L F
      (sheafificationAdjunction L (Type w))
      (sheafificationAdjunction L Ts) P

/-- Helper for Lemma 7.42.4: after cancelling the `plusPlusSheafIsoPresheafToSheaf`
comparison on the left, the owner comparison against `plusPlusAdjunction` is exactly the large
sheafification comparison. -/
theorem ulift_plus_plus_comparison_component_cancel_left
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    (((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))).inv ≫
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P) =
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let e := (plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)
  have h :=
    ulift_plus_plus_comparison_component_fac (L := L) (P := P)
  have h' := congrArg (fun k ↦ e.inv ≫ k) h
  -- Cancel the left comparison isomorphism to isolate the large sheafification comparison.
  simpa [e, Ts, F, Category.assoc] using h'.symm

/-- Helper for Lemma 7.42.4: re-expanding the cancelled comparison shows that the owner
comparison against `plusPlusAdjunction` is the `plusPlusSheafIsoPresheafToSheaf` isomorphism
followed by the large sheafification comparison. -/
theorem ulift_plus_plus_comparison_component_eq_large_comparison
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    (sheafComposeNatTrans L
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃)))
      (sheafificationAdjunction L (Type w))
      (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P =
      ((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))).hom ≫
        (sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))
          (sheafificationAdjunction L (Type w))
          (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  have hcancel :=
    ulift_plus_plus_comparison_component_cancel_left (L := L) (P := P)
  have h' := congrArg
    (fun k ↦
      ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫ k)
    hcancel
  -- Reinsert the cancelled isomorphism to recover the original owner comparison.
  simpa [Ts, F, Category.assoc] using h'

/-- Helper for Lemma 7.42.4: once the large sheafification comparison is invertible at `P`, the
owner comparison against `plusPlusAdjunction` is invertible as well. -/
theorem ulift_plus_plus_comparison_component_isIso_of_large_comparison
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w)
    [IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))
          (sheafificationAdjunction L (Type w))
          (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P)] :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))
          (sheafificationAdjunction L (Type w))
          (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P) := by
  -- Reduce the `plus-plus` comparison to the large comparison and compose the two isomorphisms.
  rw [ulift_plus_plus_comparison_component_eq_large_comparison (L := L) (P := P)]
  let _ :
      IsIso
        (((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
            (P ⋙
              (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
                Type w ⥤ Type (max w (max u₃ v₃))))).hom) := by
    infer_instance
  let hLarge :
      IsIso
        ((sheafComposeNatTrans L
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃)))
            (sheafificationAdjunction L (Type w))
            (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P) :=
    inferInstance
  exact IsIso.comp_isIso' inferInstance hLarge

/-- Helper for Lemma 7.42.4: once `W` is identified with local bijectivity in both the small and
large type universes, the relevant `ULift` functor preserves sheafification. -/
theorem uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [L.WEqualsLocallyBijective (Type w)]
    [L.WEqualsLocallyBijective (Type (max w (max u₃ v₃)))] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max w (max u₃ v₃))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  refine ⟨?_⟩
  intro P Q f hf
  let _ : Presheaf.IsLocallyInjective L f := (L.W_iff_isLocallyBijective f).1 hf |>.1
  let _ : Presheaf.IsLocallySurjective L f := (L.W_iff_isLocallyBijective f).1 hf |>.2
  -- `ULift` leaves the local equalizer and image sieves unchanged, so local bijectivity
  -- transports directly across whiskering.
  let _ : Presheaf.IsLocallyInjective L (Functor.whiskerRight f F) :=
    isLocallyInjective_whisker_ulift (L := L) (η := f)
  let _ : Presheaf.IsLocallySurjective L (Functor.whiskerRight f F) :=
    isLocallySurjective_whisker_ulift (L := L) (η := f)
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight f F))

/-- Helper for Lemma 7.42.4: once the small `Type w` sheafification unit is locally bijective on
every presheaf, the relevant `ULift` functor preserves sheafification by comparing `W` with local
bijectivity in both universes. -/
theorem uliftFunctor_preservesSheafification_type_of_small_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (hInj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective L (toSheafify L P))
    (hSurj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallySurjective L (toSheafify L P)) :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃))) := by
  let _ : L.WEqualsLocallyBijective (Type w) :=
    @small_type_WEqualsLocallyBijective_of_unit_local_bijectivity.{u₃, v₃, w}
      E _ L inferInstance hInj hSurj
  let _ : L.WEqualsLocallyBijective (Type (max w (max u₃ v₃))) :=
    large_type_WEqualsLocallyBijective (L := L)
  -- Once `W` agrees with local bijectivity in both universes, the abstract `ULift` comparison
  -- theorem supplies sheafification preservation.
  exact
    @uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective.{u₃, v₃, w}
      E _ L inferInstance inferInstance inferInstance inferInstance

/-- Helper for Lemma 7.42.4: if the walking multicospans and cover categories used by the
concrete `plus-plus` model already shrink to `Type w`, then the generic small-owner criterion
proves that the relevant `ULift` functor preserves sheafification. -/
theorem uliftFunctor_preservesSheafification_type_of_small_shapes
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
      Small.{w} (Limits.WalkingMulticospan J')]
    [∀ X : E, Small.{w} (L.Cover X)ᵒᵖ] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max w (max u₃ v₃))) := by
  let _ :
      ∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
        Limits.HasLimitsOfShape (Limits.WalkingMulticospan J') (Type w) := by
    intro J'
    infer_instance
  let _ : ∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w) := by
    intro X
    infer_instance
  -- Once the indexing shapes are genuinely `w`-small, the concrete small-owner theorem applies.
  exact
    @uliftFunctor_preservesSheafification_type_of_small_owners.{u₃, v₃, w}
      E _ L inferInstance inferInstance inferInstance inferInstance

/-- Helper for Lemma 7.42.4: when the shape universe of the site already embeds into `w`, the
concrete `plus-plus` model gives local injectivity of the small sheafification unit directly. -/
theorem small_type_toSheafify_isLocallyInjective_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{max u₃ v₃, w}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  exact CategoryTheory.toSheafify_isLocallyInjective_type_of_univLE (L := L) P

/-- Helper for Lemma 7.42.4: when the shape universe of the site already embeds into `w`, the
concrete `plus-plus` model gives local surjectivity of the small sheafification unit directly. -/
theorem small_type_toSheafify_isLocallySurjective_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{max u₃ v₃, w}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  exact CategoryTheory.toSheafify_isLocallySurjective_type_of_hasWeakSheafify (L := L) P

/-- Helper for Lemma 7.42.4: in the easy universe branch `UnivLE.{max u₃ v₃, w}`, both local
injectivity and local surjectivity of the small sheafification unit are already available from the
concrete `plus-plus` model. -/
theorem small_type_toSheafify_isLocallyBijective_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{max u₃ v₃, w}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) ∧
      Presheaf.IsLocallySurjective L (toSheafify L P) := by
  constructor
  · -- The concrete `plus-plus` comparison gives the injective half in this branch.
    exact small_type_toSheafify_isLocallyInjective_of_univLE (L := L) P
  · -- The same comparison gives the surjective half in the same branch.
    exact small_type_toSheafify_isLocallySurjective_of_univLE (L := L) P

end CategoryTheory.Functor
