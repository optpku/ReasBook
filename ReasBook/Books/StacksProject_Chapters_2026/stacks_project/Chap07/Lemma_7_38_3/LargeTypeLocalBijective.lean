module

public import stacks_project.Chap07.Lemma_7_38_3.SieveFiberLifting

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory

namespace GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 7.38.3: stalkwise isomorphisms on a small set-valued sheaf morphism stay
stalkwise isomorphisms after composing with the relevant `ULift` functor. -/
lemma point_sheafFiber_ulift_map_isIso
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢)
    (hφ : IsIso (q.sheafFiber.map φ)) :
    IsIso
      (q.sheafFiber.map
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).map φ)) := by
  let Fup :
      Sheaf J (Type w') ⥤ Sheaf J (Type (max u v w')) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u v, w'} :
        Type w' ⥤ Type (max u v w'))
  let ψ : q.sheafFiber.obj ℱ ⟶ q.sheafFiber.obj 𝒢 := q.sheafFiber.map φ
  let ψup : q.sheafFiber.obj (Fup.obj ℱ) ⟶ q.sheafFiber.obj (Fup.obj 𝒢) :=
    q.sheafFiber.map (Fup.map φ)
  have hψ : Function.Bijective ψ := (isIso_iff_bijective ψ).1 hφ
  refine (isIso_iff_bijective ψup).2 ?_
  constructor
  · intro a₁ a₂ hEq
    -- Represent both source stalk elements on a common stage of the filtered colimit.
    obtain ⟨X, x, z₁, z₂, rfl, rfl⟩ :=
      point_presheafFiber_jointly_surjective₂_of_type
        (q := q) (P := (Fup.obj ℱ).obj) a₁ a₂
    rcases z₁ with ⟨s₁⟩
    rcases z₂ with ⟨s₂⟩
    have hmap₁ :
        ψup (q.toPresheafFiber X x (Fup.obj ℱ).obj (ULift.up s₁)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₁)) := by
      -- Naturality computes the lifted stalk map on a chosen representative.
      simpa [Fup, ψup, CategoryTheory.uliftFunctor_map] using
        congrFun (q.toPresheafFiber_naturality (Fup.map φ).hom X x) (ULift.up s₁)
    have hmap₂ :
        ψup (q.toPresheafFiber X x (Fup.obj ℱ).obj (ULift.up s₂)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₂)) := by
      -- The same computation holds for the second representative.
      simpa [Fup, ψup, CategoryTheory.uliftFunctor_map] using
        congrFun (q.toPresheafFiber_naturality (Fup.map φ).hom X x) (ULift.up s₂)
    have hEqUp :
        q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₁)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₂)) := by
      exact hmap₁.symm.trans (hEq.trans hmap₂)
    have hEqSmallMapped :
        q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₁) =
          q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₂) :=
      (point_ulift_presheafFiber_eq_iff (q := q) X x _ _).1 hEqUp
    have hsmall₁ :
        ψ (q.toPresheafFiber X x ℱ.obj s₁) =
          q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₁) := by
      -- Compare the original stalk map with the germ of the image section.
      simpa [ψ] using congrFun (q.toPresheafFiber_naturality φ.hom X x) s₁
    have hsmall₂ :
        ψ (q.toPresheafFiber X x ℱ.obj s₂) =
          q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₂) := by
      -- The same comparison for the second section.
      simpa [ψ] using congrFun (q.toPresheafFiber_naturality φ.hom X x) s₂
    have hEqSmall :
        q.toPresheafFiber X x ℱ.obj s₁ =
          q.toPresheafFiber X x ℱ.obj s₂ := by
      -- Injectivity of the original stalk map identifies the two source germs.
      exact hψ.injective (hsmall₁.trans (hEqSmallMapped.trans hsmall₂.symm))
    exact (point_ulift_presheafFiber_eq_iff (q := q) X x s₁ s₂).2 hEqSmall
  · intro b
    -- Represent the target stalk element by an actual section of the lifted target sheaf.
    obtain ⟨X, x, z, rfl⟩ :=
      point_presheafFiber_jointly_surjective_of_type
        (q := q) (P := (Fup.obj 𝒢).obj) b
    rcases z with ⟨t⟩
    obtain ⟨a, ha⟩ := hψ.surjective (q.toPresheafFiber X x 𝒢.obj t)
    obtain ⟨Y, y, s, hs⟩ :=
      point_presheafFiber_jointly_surjective_of_type (q := q) (P := ℱ.obj) a
    refine ⟨q.toPresheafFiber Y y (Fup.obj ℱ).obj (ULift.up s), ?_⟩
    have hsmall :
        q.toPresheafFiber Y y 𝒢.obj ((φ.hom.app (op Y)) s) =
          q.toPresheafFiber X x 𝒢.obj t := by
      have hmapSmall :
          ψ a = q.toPresheafFiber Y y 𝒢.obj ((φ.hom.app (op Y)) s) := by
        -- Rewrite the chosen preimage `a` by its representing germ and compute the stalk map.
        rw [← hs]
        simpa [ψ] using congrFun (q.toPresheafFiber_naturality φ.hom Y y) s
      exact hmapSmall.symm.trans ha
    have hlarge :
        q.toPresheafFiber Y y (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op Y)) s)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj (ULift.up t) := by
      obtain ⟨Z, f, g, hfg⟩ :=
        (Limits.Types.FilteredColimit.isColimit_eq_iff
          (ht := q.isColimitPresheafFiberCocone 𝒢.obj)
          (i := op ⟨Y, y⟩) (j := op ⟨X, x⟩)
          (xi := (φ.hom.app (op Y)) s) (xj := t)).1 hsmall
      exact
        (Limits.Types.FilteredColimit.isColimit_eq_iff
          (ht := q.isColimitPresheafFiberCocone (Fup.obj 𝒢).obj)
          (i := op ⟨Y, y⟩) (j := op ⟨X, x⟩)
          (xi := ULift.up ((φ.hom.app (op Y)) s)) (xj := ULift.up t)).2
          ⟨Z, f, g, by
            simpa [Fup, CategoryTheory.uliftFunctor_map] using hfg⟩
    have hmap :
        ψup (q.toPresheafFiber Y y (Fup.obj ℱ).obj (ULift.up s)) =
          q.toPresheafFiber Y y (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op Y)) s)) := by
      -- Naturality computes the lifted stalk map on the chosen preimage representative.
      simpa [Fup, ψup, CategoryTheory.uliftFunctor_map] using
        congrFun (q.toPresheafFiber_naturality (Fup.map φ).hom Y y) (ULift.up s)
    exact hmap.trans hlarge

/-- Helper for Lemma 7.38.3: pointwise equality of germs makes the lifted equalizer-sieve
inclusion bijective on every point fiber. -/
lemma pointwise_germ_eq_uliftFunctorInclusion_presheafFiber_bijective
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ i,
      Function.Bijective
        ((p i).presheafFiber.map
          (Sieve.uliftFunctorInclusion.{max u v w'}
            (Presheaf.equalizerSieve (F := ℱ.obj) s s'))) := by
  intro i
  -- Each point-fiber generator already lifts through the equalizer sieve, so the induced map is
  -- bijective by the earlier point-fiber lifting package.
  refine point_uliftFunctorInclusion_presheafFiber_bijective_of_lifts
    (q := p i) (S := Presheaf.equalizerSieve (F := ℱ.obj) s s') ?_
  intro x
  exact pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x)

/-- Helper for Lemma 7.38.3: bijectivity on a point fiber upgrades to an isomorphism on the
corresponding stalk map after sheafification. -/
lemma point_sheafify_map_isIso_of_presheafFiber_bijective
    [HasWeakSheafify J (Type (max u v w'))]
    (q : Point.{w'} J) {P Q : Cᵒᵖ ⥤ Type (max u v w')} (η : P ⟶ Q)
    (hη : Function.Bijective (q.presheafFiber.map η)) :
    IsIso (q.sheafFiber.map ((presheafToSheaf J (Type (max u v w'))).map η)) := by
  -- Conjugate the stalk map across the canonical identification between presheaf fibers and the
  -- fibers of the sheafification.
  let _ : IsIso (q.presheafFiber.map η) := (isIso_iff_bijective _).2 hη
  exact
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (q.presheafToSheafCompSheafFiberIso (Type (max u v w')))).app
          (Arrow.mk η))).2
      (inferInstanceAs (IsIso (q.presheafFiber.map η)))

/-- Helper for Lemma 7.38.3: the concrete `Plus` map is locally injective in the ambient large
type universe. -/
theorem toPlus_isLocallyInjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallyInjective J (J.toPlus P) := by
  -- The concrete `Plus` quotient identifies two representatives only after passing to a common
  -- covering sieve, so that covering sieve witnesses local injectivity directly.
  letI : Presheaf.IsLocallyInjective J (J.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      open GrothendieckTopology.Plus in
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, h₁, h₂, eq⟩ := h
      exact J.superset_covering (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Lemma 7.38.3: the concrete `Plus` map is locally surjective in the ambient large
type universe. -/
theorem toPlus_isLocallySurjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallySurjective J (J.toPlus P) := by
  -- Every `Plus` section is represented on some covering sieve, and that representative gives
  -- the desired local preimage.
  letI : Presheaf.IsLocallySurjective J (J.toPlus P) := {
    imageSieve_mem := by
      intro X x
      open GrothendieckTopology.Plus in
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine J.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. } }
  infer_instance

/-- Helper for Lemma 7.38.3: the concrete `plus-plus` model of sheafification is locally
injective in the ambient large type universe. -/
theorem concrete_toSheafify_isLocallyInjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallyInjective J (J.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective J (J.toPlus P) :=
    toPlus_isLocallyInjective_type (J := J) P
  letI : Presheaf.IsLocallyInjective J (J.toPlus (J.plusObj P)) :=
    toPlus_isLocallyInjective_type (J := J) (J.plusObj P)
  -- The concrete sheafification unit is the composite of the two concrete `Plus` maps.
  change Presheaf.IsLocallyInjective J (J.toPlus P ≫ J.plusMap (J.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.38.3: the concrete `plus-plus` model of sheafification is locally
surjective in the ambient large type universe. -/
theorem concrete_toSheafify_isLocallySurjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallySurjective J (J.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective J (J.toPlus P) :=
    toPlus_isLocallySurjective_type (J := J) P
  letI : Presheaf.IsLocallySurjective J (J.toPlus (J.plusObj P)) :=
    toPlus_isLocallySurjective_type (J := J) (J.plusObj P)
  -- The same concrete factorization reduces surjectivity to the two `Plus` steps.
  change Presheaf.IsLocallySurjective J (J.toPlus P ≫ J.plusMap (J.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.38.3: in the ambient large `Type` universe used for the sheafified
representable, `J.W` still agrees with local bijectivity. -/
theorem large_type_WEqualsLocallyBijective
    [HasWeakSheafify J (Type (max u v w'))] :
    J.WEqualsLocallyBijective (Type (max u v w')) := by
  let T := Type (max u v w')
  let _ :
      ∀ P : Cᵒᵖ ⥤ T,
        Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) := by
    intro P
    let _ : Presheaf.IsLocallyInjective J (J.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallyInjective_type (J := J) (P := P ⋙ forget T)
    -- Rewrite the abstract large-universe unit as the concrete one followed by comparison
    -- isomorphisms that preserve local injectivity.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify J T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso J (forget T) P).hom) := by
      infer_instance
    infer_instance
  let _ :
      ∀ P : Cᵒᵖ ⥤ T,
        Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
    intro P
    let _ : Presheaf.IsLocallySurjective J (J.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallySurjective_type (J := J) (P := P ⋙ forget T)
    -- The same large-universe comparison transports local surjectivity to the abstract unit.
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify J T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso J (forget T) P).hom) := by
      infer_instance
    infer_instance
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' (J := J) (A := T)

/-- Helper for Lemma 7.38.3: once the lifted sieve inclusion lies in `J.W`, local surjectivity at
the lifted identity section shows that the original sieve is covering. -/
lemma covering_of_W_uliftFunctorInclusion
    [HasWeakSheafify J (Type (max u v w'))]
    {U : C} (S : Sieve U)
    (hW :
      J.W
        (Sieve.uliftFunctorInclusion.{max u v w'} S :
          Sieve.uliftFunctor.{max u v w'} S ⟶
            CategoryTheory.uliftYoneda.obj.{max u v w'} U)) :
    S ∈ J U := by
  let _ : J.WEqualsLocallyBijective (Type (max u v w')) :=
    large_type_WEqualsLocallyBijective (J := J)
  let f :
      Sieve.uliftFunctor.{max u v w'} S ⟶
        CategoryTheory.uliftYoneda.obj.{max u v w'} U :=
    Sieve.uliftFunctorInclusion.{max u v w'} S
  have hSurj : Presheaf.IsLocallySurjective J f := hW.isLocallySurjective
  let s : (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op U) := ULift.up (𝟙 U)
  -- Evaluate local surjectivity on the lifted identity section and identify its image sieve.
  have hmem : Presheaf.imageSieve f s ∈ J U := hSurj.imageSieve_mem s
  rw [imageSieve_uliftFunctorInclusion_eq_pullback (S := S) (𝟙 U), Sieve.pullback_id] at hmem
  exact hmem

end GrothendieckTopology

end CategoryTheory
