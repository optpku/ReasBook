module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.UnivLE
public import Mathlib.Logic.Small.Basic
public import stacks_project.Chap07.Definition_7_42_3

@[expose] public section

open CategoryTheory Opposite CategoryTheory.GrothendieckTopology.Plus

universe u₁ u₂ u₃ v₁ v₂ v₃ w r

namespace CategoryTheory.Functor

/-- Helper for Lemma 7.42.4: composing a sheaf of `Type w`-valued presheaves with the relevant
`ULift` functor preserves the sheaf condition. -/
instance uliftFunctor_hasSheafCompose_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max u₃ v₃ w)) where
  isSheaf P hP := by
    -- Rewrite the sheaf condition into the concrete type-valued form where `ULift` is stable.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := L)
      ((isSheaf_iff_isSheaf_of_type L P).1 hP)

/-- Helper for Lemma 7.42.4: the identity functor on `Type w` preserves sheafification
tautologically. -/
instance preservesSheafification_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (𝟭 (Type w)) where
  le P Q f hf := by
    -- Whiskering by the identity functor leaves the `W`-morphism unchanged.
    simpa using hf

/-- Helper for Lemma 7.42.4: the forgetful functor on the large `Type` universe used below is
definitionally the identity, so it preserves sheafification tautologically. -/
instance preservesSheafification_forget_large_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (forget (Type (max u₃ v₃ w))) where
  le P Q f hf := by
    simpa using hf

/-- Helper for Lemma 7.42.4: the concrete `Plus` map is locally injective in any universe of
types. -/
theorem toPlus_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (L.toPlus P) := by
  -- Compare representatives of equal `Plus` sections on a covering sieve.
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      open GrothendieckTopology.Plus in
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, h₁, h₂, eq⟩ := h
      exact L.superset_covering (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Lemma 7.42.4: the concrete `Plus` map is locally surjective in any universe of
types. -/
theorem toPlus_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (L.toPlus P) := by
  -- Every `Plus` section is locally represented by an actual presheaf section.
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) := {
    imageSieve_mem := by
      intro X x
      open GrothendieckTopology.Plus in
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine L.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. } }
  infer_instance

/-- Helper for Lemma 7.42.4: the concrete `plus-plus` model of sheafification is locally
injective in any universe of types. -/
theorem concrete_toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) :=
    toPlus_isLocallyInjective_type (L := L) P
  letI : Presheaf.IsLocallyInjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallyInjective_type (L := L) (L.plusObj P)
  -- Rewrite the concrete sheafification unit as the composite of the two `Plus` maps.
  change Presheaf.IsLocallyInjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.42.4: the concrete `plus-plus` model of sheafification is locally
surjective in any universe of types. -/
theorem concrete_toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) :=
    toPlus_isLocallySurjective_type (L := L) P
  letI : Presheaf.IsLocallySurjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallySurjective_type (L := L) (L.plusObj P)
  -- Rewrite the concrete sheafification unit as the composite of the two `Plus` maps.
  change Presheaf.IsLocallySurjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.42.4: local injectivity reflects across whiskering by the relevant
`ULift` functor. -/
theorem locallyInjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w)))] :
    Presheaf.IsLocallyInjective L η where
  equalizerSieve_mem {X} x y h := by
    let x' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))).obj X := ULift.up x
    let y' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))).obj X := ULift.up y
    -- Lift the equal pair, use local injectivity upstairs, then descend with `ULift.down`.
    have hUp :
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))).app X x' =
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max u₃ v₃ w))).app X y' := by
      change ULift.up (η.app X x) = ULift.up (η.app X y)
      exact congrArg ULift.up h
    let S : Sieve X.unop :=
      Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w)))
        x' y'
    have hS : S ∈ L X.unop := by
      exact
        Presheaf.equalizerSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max u₃ v₃ w)))
          x' y' hUp
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ULift.up ((P.map f.op) x) = ULift.up ((P.map f.op) y) at hf
    change (P.map f.op) x = (P.map f.op) y
    exact ULift.up.inj hf

/-- Helper for Lemma 7.42.4: local injectivity of type-valued presheaf maps is preserved by
whiskering with the ambient `ULift` functor. -/
theorem isLocallyInjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L η] :
    Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w))) where
  equalizerSieve_mem {X} x y h := by
    -- The `ULift` whiskering only repackages sections, so the equalizer sieve is unchanged.
    have hDown : η.app X x.down = η.app X y.down := by
      change ULift.up (η.app X x.down) = ULift.up (η.app X y.down) at h
      exact ULift.up.inj h
    have hSieve :
        Presheaf.equalizerSieve
            (F := P ⋙
              (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
                Type w ⥤ Type (max u₃ v₃ w)))
            x y =
          Presheaf.equalizerSieve (F := P) x.down y.down := by
      ext Y f
      constructor
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down) at hEq
        exact ULift.up.inj hEq
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down)
        exact congrArg ULift.up hEq
    rw [hSieve]
    exact Presheaf.equalizerSieve_mem L η x.down y.down hDown

/-- Helper for Lemma 7.42.4: whiskering a type-valued presheaf morphism by `ULift` does not
change its image sieve. -/
theorem imageSieve_whisker_ulift
    {E : Type u₃} [Category.{v₃} E]
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q) {X : E}
    (x :
      (Q ⋙
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w))).obj (op X)) :
    Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))) x =
      Presheaf.imageSieve η x.down := by
  ext Y f
  constructor
  · rintro ⟨y, hy⟩
    -- Any lifted local preimage descends by `ULift.down`.
    refine ⟨y.down, ?_⟩
    exact congrArg ULift.down hy
  · rintro ⟨y, hy⟩
    -- Conversely, any ordinary local preimage lifts back via `ULift.up`.
    refine ⟨ULift.up y, ?_⟩
    change ULift.up (η.app (op Y) y) = ULift.up (Q.map f.op x.down)
    exact congrArg ULift.up hy

/-- Helper for Lemma 7.42.4: local surjectivity of type-valued presheaf maps is preserved by
whiskering with the ambient `ULift` functor. -/
theorem isLocallySurjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L η] :
    Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w))) where
  imageSieve_mem {X} x := by
    -- After identifying the image sieve with the unlifted one, reuse local surjectivity of `η`.
    simpa [imageSieve_whisker_ulift (η := η) x] using
      (Presheaf.imageSieve_mem L η x.down)

/-- Helper for Lemma 7.42.4: local surjectivity reflects across whiskering by the relevant
`ULift` functor. -/
theorem locallySurjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w)))] :
    Presheaf.IsLocallySurjective L η where
  imageSieve_mem {X} x := by
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))).obj (op X) := ULift.up x
    let S : Sieve X :=
      Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w)))
        x'
    -- Lift the target section to the ambient universe, then descend a local preimage.
    have hS : S ∈ L X := by
      exact
        Presheaf.imageSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max u₃ v₃ w)))
          x'
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ∃ t : (P ⋙
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w))).obj (op Y),
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w))).app (op Y) t =
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))).map f.op x' at hf
    rcases hf with ⟨y, hy⟩
    refine ⟨y.down, ?_⟩
    change ULift.up (η.app (op Y) y.down) = ULift.up (Q.map f.op x) at hy
    exact ULift.up.inj hy

/-- Helper for Lemma 7.42.4: after enlarging the target universe so that the concrete
`plus-plus` model is available, the abstract sheafification unit is locally injective. -/
theorem large_toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max u₃ v₃ w))]
    (P : Eᵒᵖ ⥤ Type (max u₃ v₃ w)) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  let _ : Presheaf.IsLocallyInjective L
      (L.toSheafify (P ⋙ forget (Type (max u₃ v₃ w)))) :=
    concrete_toSheafify_isLocallyInjective_type
      (L := L) (P := P ⋙ forget (Type (max u₃ v₃ w)))
  -- Compare the abstract unit with the concrete `plus-plus` unit and transfer local injectivity.
  rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso
      ((plusPlusIsoSheafify L (Type (max u₃ v₃ w))
        (P ⋙ forget (Type (max u₃ v₃ w)))).hom) := by
    infer_instance
  let _ : IsIso
      ((sheafifyComposeIso L (forget (Type (max u₃ v₃ w))) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.42.4: after enlarging the target universe so that the concrete
`plus-plus` model is available, the abstract sheafification unit is locally surjective. -/
theorem large_toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max u₃ v₃ w))]
    (P : Eᵒᵖ ⥤ Type (max u₃ v₃ w)) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let _ : Presheaf.IsLocallySurjective L
      (L.toSheafify (P ⋙ forget (Type (max u₃ v₃ w)))) :=
    concrete_toSheafify_isLocallySurjective_type
      (L := L) (P := P ⋙ forget (Type (max u₃ v₃ w)))
  -- Compare the abstract unit with the concrete `plus-plus` unit and transfer local surjectivity.
  rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso
      ((plusPlusIsoSheafify L (Type (max u₃ v₃ w))
        (P ⋙ forget (Type (max u₃ v₃ w)))).hom) := by
    infer_instance
  let _ : IsIso
      ((sheafifyComposeIso L (forget (Type (max u₃ v₃ w))) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.42.4: for type-valued presheaves, the abstract sheafification unit is
locally surjective from the weak reflector alone. -/
theorem toSheafify_isLocallySurjective_type_of_hasWeakSheafify
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let η : P ⟶ sheafify L P := toSheafify L P
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  let Rsub : Subfunctor (sheafify L P) := (Subfunctor.range η).sheafify L
  change Rsub = ⊤
  rw [Subfunctor.eq_top_iff_isIso]
  let hS : Presheaf.IsSheaf L (sheafify L P) :=
    ((presheafToSheaf L (Type w)).obj P).property
  have hR : Presheaf.IsSheaf L Rsub.toFunctor := by
    -- The sheafified image is a subsheaf of the sheafification target.
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact hS
  let r : sheafify L P ⟶ Rsub.toFunctor :=
    sheafifyLift L (Subfunctor.toRangeSheafify L η) hR
  have hfac : Subfunctor.toRangeSheafify L η ≫ Rsub.ι = η := by
    -- The sheafified range inclusion still factors the original unit.
    dsimp [Subfunctor.toRangeSheafify, Rsub]
    rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
  have hret : r ≫ Rsub.ι = 𝟙 (sheafify L P) := by
    -- The universal property of sheafification makes the range inclusion split.
    apply sheafify_hom_ext L
    · exact hS
    · change (toSheafify L P ≫ r) ≫ Rsub.ι =
        toSheafify L P ≫ 𝟙 (sheafify L P)
      dsimp [r]
      rw [toSheafify_sheafifyLift, hfac]
      simp [η]
  -- A split monomorphism onto the sheafified image is an isomorphism, so the image covers locally.
  refine ⟨r, ?_, hret⟩
  apply (cancel_mono Rsub.ι).1
  simp [Category.assoc, hret]

/-- Helper for Lemma 7.42.4: preserving sheafification for the relevant `ULift` functor is
equivalent to invertibility of the canonical sheaf-composition comparison. -/
theorem uliftFunctor_preservesSheafification_type_iff
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max u₃ v₃ w)) ↔
      IsIso (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max u₃ v₃ w))
        (sheafificationAdjunction L (Type w))
        (plusPlusAdjunction L (Type (max u₃ v₃ w)))) := by
  let Ts := Type (max u₃ v₃ w)
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  -- Rewrite preservation into the owner comparison for the chosen adjunctions.
  change L.PreservesSheafification F ↔
    IsIso (sheafComposeNatTrans L F
      (sheafificationAdjunction L (Type w))
      (plusPlusAdjunction L Ts))
  rw [GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
    (J := L) (F := F)
    (adj₁ := sheafificationAdjunction L (Type w))
    (adj₂ := plusPlusAdjunction L Ts)]

/-- Helper for Lemma 7.42.4: the specialized `ULift` sheafification comparison is an isomorphism
exactly when the whiskered small-universe unit is a `W`-morphism upstairs. -/
theorem uliftFunctor_comparison_app_isIso_iff_whiskered_toSheafify_W
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max u₃ v₃ w))]
    (P : Eᵒᵖ ⥤ Type w) :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))
          (sheafificationAdjunction L (Type w))
          (sheafificationAdjunction L (Type (max u₃ v₃ w)))).app P) ↔
      L.W
        (Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w))) := by
  let Ts := Type (max u₃ v₃ w)
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let adj₁ := sheafificationAdjunction L (Type w)
  let adj₂ := sheafificationAdjunction L Ts
  let η := (sheafComposeNatTrans L F adj₁ adj₂).app P
  have hW :
      L.W ((sheafToPresheaf L Ts).map η) ↔ IsIso η := by
    -- Passing to underlying presheaves detects isomorphisms for sheaf morphisms.
    simpa [η] using (L.W_sheafToPresheaf_map_iff_isIso η)
  have hfac :
      toSheafify L (P ⋙ F) ≫ (sheafToPresheaf L Ts).map η =
        Functor.whiskerRight (toSheafify L P) F := by
    -- This is the defining factorization of `sheafComposeNatTrans`.
    simpa [η, adj₁, adj₂, F] using
      (sheafComposeNatTrans_fac L F adj₁ adj₂ P)
  -- Normalize the componentwise isomorphism question to a `W`-statement and peel off the
  -- large-universe sheafification unit.
  change IsIso η ↔ L.W (Functor.whiskerRight (toSheafify L P) F)
  rw [← hW, ← hfac]
  exact
    (((GrothendieckTopology.W (J := L) (A := Ts)).precomp_iff
      (W' := GrothendieckTopology.W (J := L) (A := Ts))
      (toSheafify L (P ⋙ F))
      ((sheafToPresheaf L Ts).map η)
      (L.W_toSheafify (P ⋙ F))).symm)

/-- Helper for Lemma 7.42.4: in the large universe of types used for `ULift`, the class `W`
coincides with local bijectivity because the large-universe sheafification unit is already
locally bijective. -/
theorem large_type_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max u₃ v₃ w))] :
    L.WEqualsLocallyBijective (Type (max u₃ v₃ w)) := by
  let T := Type (max u₃ v₃ w)
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallyInjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallyInjective L (L.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallyInjective_type (L := L) (P := P ⋙ forget T)
    -- Rewrite the abstract large-universe unit as the concrete one followed by comparison
    -- isomorphisms that preserve local injectivity.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallySurjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallySurjective L (L.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallySurjective_type (L := L) (P := P ⋙ forget T)
    -- The same large-universe comparison transports local surjectivity to the abstract unit.
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := T)

/-- Helper for Lemma 7.42.4: once the small-universe sheafification unit is known to be locally
injective and locally surjective on every `Type w`-valued presheaf, `W` agrees with local
bijectivity on `Type w`. -/
theorem small_type_WEqualsLocallyBijective_of_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    (hInj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective L (toSheafify L P))
    (hSurj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallySurjective L (toSheafify L P)) :
    L.WEqualsLocallyBijective (Type w) := by
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective L (toSheafify L P) := hInj
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallySurjective L (toSheafify L P) := hSurj
  let _ : L.PreservesSheafification (forget (Type w)) := by
    -- The forgetful functor on `Type w` is the identity, so it preserves sheafification
    -- tautologically.
    simpa using
      (preservesSheafification_id_type (L := L) :
        L.PreservesSheafification (𝟭 (Type w)))
  let _ : L.HasSheafCompose (forget (Type w)) := by
    -- Sheaf composition with the identity-on-types forgetful functor is available by instance
    -- search.
    infer_instance
  -- Package the two local-bijectivity hypotheses into the canonical `WEqualsLocallyBijective`
  -- structure.
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := Type w)

/-- Helper for Lemma 7.42.4: once the small-universe sheafification unit is locally bijective,
its `ULift`-whiskering already lies in `W` in the large target universe. -/
theorem whiskered_toSheafify_W_of_small_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max u₃ v₃ w))]
    (P : Eᵒᵖ ⥤ Type w)
    [Presheaf.IsLocallyInjective L (toSheafify L P)]
    [Presheaf.IsLocallySurjective L (toSheafify L P)] :
    L.W
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max u₃ v₃ w))) := by
  let Ts := Type (max u₃ v₃ w)
  let F : Type w ⥤ Ts :=
    CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let _ : L.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (L := L)
  let _ : Presheaf.IsLocallyInjective L (Functor.whiskerRight (toSheafify L P) F) :=
    isLocallyInjective_whisker_ulift (L := L) (η := toSheafify L P)
  let _ : Presheaf.IsLocallySurjective L (Functor.whiskerRight (toSheafify L P) F) :=
    isLocallySurjective_whisker_ulift (L := L) (η := toSheafify L P)
  -- Once the whiskered unit is locally bijective in the large universe, `W` follows directly.
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight (toSheafify L P) F))

/-- Helper for Lemma 7.42.4: after enlarging the target universe, the sheafification unit itself
is already a `W`-morphism. -/
theorem ulifted_toSheafify_W
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max u₃ v₃ w))]
    (P : Eᵒᵖ ⥤ Type w) :
    L.W
      (toSheafify L
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max u₃ v₃ w)))) := by
  let Ts := Type (max u₃ v₃ w)
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let _ : L.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (L := L)
  -- Once `W` is identified with local bijectivity in the large universe, the large sheafification
  -- unit lies in `W` automatically.
  simpa [F] using (L.W_toSheafify (P ⋙ F))

end CategoryTheory.Functor
