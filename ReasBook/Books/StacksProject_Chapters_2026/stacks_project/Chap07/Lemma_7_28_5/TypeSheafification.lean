module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.UnivLE
public import stacks_project.Chap07.Lemma_7_20_3

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
universe u₁ u₂ u₃ v₁ v₂ v₃ t w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (V : D)

/-- Helper for Lemma 7.28.5: composing type-valued sheaves with any ambient `ULift` functor
preserves the sheaf condition on the site in use. -/
instance uliftFunctor_hasSheafCompose_type_generic
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) where
  isSheaf P hP := by
    -- Reduce to the concrete type-valued sheaf condition where `ULift` is stable.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := L)
      ((isSheaf_iff_isSheaf_of_type L P).1 hP)

/-- Helper for Lemma 7.28.5: a type-valued presheaf morphism is an isomorphism if its
`ULift`-whiskering is an isomorphism. -/
theorem isIso_of_whiskerRight_ulift
    {E : Type u₃} [Category.{v₃} E] {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [IsIso (Functor.whiskerRight η
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)))] :
    IsIso η := by
  let R :=
    (Functor.whiskeringRight Eᵒᵖ (Type t) (Type (max t w))).obj
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))
  have hR : IsIso (R.map η) := by
    -- The functor-category spelling of whiskering is the one expected by reflection.
    simpa [R] using
      (inferInstance :
        IsIso (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))))
  -- `ULift` reflects isomorphisms, hence so does right whiskering by it.
  exact isIso_of_reflects_iso η R

/-- Helper for Lemma 7.28.5: a sheaf morphism is an isomorphism if its image under the
`ULift` sheaf-composition functor is an isomorphism. -/
theorem isIso_of_sheafCompose_ulift_map
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {A B : Sheaf L (Type t)} (α : A ⟶ B)
    [IsIso ((sheafCompose L
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))).map α)] :
    IsIso α := by
  -- The sheaf-composition functor reflects isomorphisms because `ULift` does.
  exact isIso_of_reflects_iso α
    (sheafCompose L
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)))

/-- Helper for Lemma 7.28.5: whiskering a locally injective morphism of `Type`-valued presheaves
by `ULift` does not change the equalizer sieves. -/
theorem locallyInjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w)))] :
    Presheaf.IsLocallyInjective L η where
  equalizerSieve_mem {X} x y h := by
    let x' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).obj X := ULift.up x
    let y' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).obj X := ULift.up y
    -- Lift the equal pair to the larger universe, use local injectivity there, and descend.
    have hUp :
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).app X x' =
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w))).app X y' := by
      change ULift.up (η.app X x) = ULift.up (η.app X y)
      exact congrArg ULift.up h
    let S : Sieve X.unop :=
      Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w)))
        x' y'
    have hS : S ∈ L X.unop := by
      exact
        Presheaf.equalizerSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w)))
          x' y' hUp
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ULift.up ((P.map f.op) x) = ULift.up ((P.map f.op) y) at hf
    change (P.map f.op) x = (P.map f.op) y
    exact ULift.up.inj hf

/-- Helper for Lemma 7.28.5: whiskering a locally injective morphism of `Type`-valued presheaves
by `ULift` does not change the equalizer sieves. -/
theorem isLocallyInjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L η] :
    Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  refine ⟨?_⟩
  intro X x y h
  -- The `ULift` whiskering only repackages sections, so the equalizer sieve is unchanged.
  have hDown : η.app X x.down = η.app X y.down := by
    change ULift.up (η.app X x.down) = ULift.up (η.app X y.down) at h
    exact ULift.up.inj h
  have hSieve :
      Presheaf.equalizerSieve
          (F := P ⋙
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w)))
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

/-- Helper for Lemma 7.28.5: whiskering a type-valued presheaf morphism by `ULift` does not
change its image sieve. -/
theorem imageSieve_whisker_ulift
    {E : Type u₃} [Category.{v₃} E]
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q) {X : E}
    (x :
      (Q ⋙
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w))).obj (Opposite.op X)) :
    Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))) x =
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
    change ULift.up (η.app (Opposite.op Y) y) = ULift.up (Q.map f.op x.down)
    exact congrArg ULift.up hy

/-- Helper for Lemma 7.28.5: whiskering a locally surjective morphism of `Type`-valued presheaves
by `ULift` does not change the image sieves. -/
theorem locallySurjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w)))] :
    Presheaf.IsLocallySurjective L η where
  imageSieve_mem {X} x := by
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).obj (Opposite.op X) := ULift.up x
    let S : Sieve X :=
      Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w)))
        x'
    -- Lift the target section upstairs, obtain a local preimage there, and descend it.
    have hS : S ∈ L X := by
      exact
        Presheaf.imageSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{w, t} :
              Type t ⥤ Type (max t w)))
          x'
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ∃ t : (P ⋙
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w))).obj (Opposite.op Y),
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} :
          Type t ⥤ Type (max t w))).app (Opposite.op Y) t =
        (Q ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))).map f.op x' at hf
    rcases hf with ⟨y, hy⟩
    refine ⟨y.down, ?_⟩
    change ULift.up (η.app (Opposite.op Y) y.down) = ULift.up (Q.map f.op x) at hy
    exact ULift.up.inj hy

/-- Helper for Lemma 7.28.5: whiskering a locally surjective morphism of `Type`-valued presheaves
by `ULift` does not change the image sieves. -/
theorem isLocallySurjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L η] :
    Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  refine ⟨?_⟩
  intro X x
  -- After identifying the image sieve with the unlifted one, reuse local surjectivity of `η`.
  rw [imageSieve_whisker_ulift (η := η) (x := x)]
  exact Presheaf.imageSieve_mem L η x.down

/-- Helper for Lemma 7.28.5: the identity functor on any `Type` universe preserves
sheafification tautologically. -/
instance preservesSheafification_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (𝟭 (Type t)) where
  le P Q f hf := by
    -- Whiskering by the identity functor leaves the `W`-morphism unchanged.
    simpa using hf

/-- Helper for Lemma 7.28.5: the forgetful functor on any `Type` universe is the identity, so it
preserves sheafification tautologically as well. -/
instance preservesSheafification_forget_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (forget (Type t)) where
  le P Q f hf := by
    -- For `Type`, the forgetful functor is definitionally the identity functor.
    simpa using hf

/-- Helper for Lemma 7.28.5: the concrete `Plus` map is locally injective for type-valued
presheaves in any universe. -/
theorem toPlus_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
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

/-- Helper for Lemma 7.28.5: the concrete `Plus` map is locally surjective for type-valued
presheaves in any universe. -/
theorem toPlus_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
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
      simpa using
        x.2
          { fst.hf := hf
            snd.hf := S.1.downward_closed hf g
            r.g₁ := g
            r.g₂ := 𝟙 Z
            .. } }
  infer_instance

/-- Helper for Lemma 7.28.5: the concrete `plus-plus` model of sheafification is locally
injective for type-valued presheaves in any universe. -/
theorem concrete_toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) :=
    toPlus_isLocallyInjective_type (L := L) P
  letI : Presheaf.IsLocallyInjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallyInjective_type (L := L) (L.plusObj P)
  -- Rewrite the concrete sheafification unit as a composite of two `Plus` maps.
  change Presheaf.IsLocallyInjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.28.5: the concrete `plus-plus` model of sheafification is locally
surjective for type-valued presheaves in any universe. -/
theorem concrete_toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Eᵒᵖ ⥤ Type t, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type t))]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) :=
    toPlus_isLocallySurjective_type (L := L) P
  letI : Presheaf.IsLocallySurjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallySurjective_type (L := L) (L.plusObj P)
  -- The same concrete `Plus` factorization gives local surjectivity of `L.toSheafify`.
  change Presheaf.IsLocallySurjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.28.5: in a universe containing the site shapes, equality after the
abstract Type-valued sheafification unit forces the original sections to agree locally. -/
theorem equalizerSieve_mem_of_toSheafify_eq_type_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] [UnivLE.{max u₃ v₃, t}]
    {P : Eᵒᵖ ⥤ Type t} {X : Eᵒᵖ}
    (x y : P.obj X)
    (h : (toSheafify L P).app X x = (toSheafify L P).app X y) :
    Presheaf.equalizerSieve (F := P) x y ∈ L X.unop := by
  let T := Type t
  haveI : Presheaf.IsLocallyInjective L (toSheafify L P) := by
    let _ : Presheaf.IsLocallyInjective L (L.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallyInjective_type (L := L) (P := P ⋙ forget T)
    -- Compare the concrete plus-plus sheafification unit with the abstract reflector unit.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  exact Presheaf.equalizerSieve_mem L (toSheafify L P) x y h

/-- Helper for Lemma 7.28.5: the abstract Type-valued sheafification unit is locally injective
once equality in the sheafification is known to imply covering of equalizer sieves. -/
theorem toSheafify_isLocallyInjective_type_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] [UnivLE.{max u₃ v₃, t}]
    (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective L (toSheafify L P) where
  equalizerSieve_mem {X} x y h := by
    -- Reduce local injectivity of the unit to the pointwise equalizer-sieve bridge.
    exact equalizerSieve_mem_of_toSheafify_eq_type_of_univLE (L := L) x y h

/-- Helper for Lemma 7.28.5: for type-valued presheaves, the abstract sheafification unit is
locally surjective by the reflector universal property. -/
theorem toSheafify_isLocallySurjective_type_of_hasWeakSheafify
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] (P : Eᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let η : P ⟶ sheafify L P := toSheafify L P
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  let Rsub : Subfunctor (sheafify L P) := (Subfunctor.range η).sheafify L
  change Rsub = ⊤
  rw [Subfunctor.eq_top_iff_isIso]
  let hS : Presheaf.IsSheaf L (sheafify L P) :=
    ((presheafToSheaf L (Type t)).obj P).property
  have hR : Presheaf.IsSheaf L Rsub.toFunctor := by
    -- The sheafified image is a sheaf because it is a subsheaf of the sheafification target.
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

/-- Helper for Lemma 7.28.5: if the small `Type`-valued sheafification unit is locally bijective
for every presheaf, then `W` agrees with local bijectivity in the small universe as well. -/
theorem small_type_WEqualsLocallyBijective_of_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    (hInj :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallyInjective L (toSheafify L P))
    (hSurj :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallySurjective L (toSheafify L P)) :
    L.WEqualsLocallyBijective (Type t) := by
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallyInjective L (toSheafify L P) := hInj
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type t,
        Presheaf.IsLocallySurjective L (toSheafify L P) := hSurj
  let _ : L.PreservesSheafification (forget (Type t)) := by
    -- The forgetful functor on `Type t` is the identity, so it preserves sheafification.
    simpa using
      (preservesSheafification_id_type (L := L) :
        L.PreservesSheafification (𝟭 (Type t)))
  let _ : L.HasSheafCompose (forget (Type t)) := by
    infer_instance
  -- Package the unitwise local bijectivity data into the canonical `WEqualsLocallyBijective`
  -- structure.
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := Type t)

/-- Helper for Lemma 7.28.5: in a universe containing the site shapes, Type-valued weak
sheafification gives the local-bijective description of `W`. -/
theorem type_WEqualsLocallyBijective_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] [UnivLE.{max u₃ v₃, t}] :
    L.WEqualsLocallyBijective (Type t) := by
  -- Package the two unitwise local properties into the standard `W = locally bijective` API.
  exact
    small_type_WEqualsLocallyBijective_of_unit_local_bijectivity (L := L)
      (fun P ↦ toSheafify_isLocallyInjective_type_of_univLE (L := L) P)
      (fun P ↦ toSheafify_isLocallySurjective_type_of_hasWeakSheafify (L := L) P)

/-- Helper for Lemma 7.28.5: compatibility name for the valid large-enough Type-valued
`W =` local-bijectivity criterion. -/
theorem type_WEqualsLocallyBijective_of_hasWeakSheafify
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)] [UnivLE.{max u₃ v₃, t}] :
    L.WEqualsLocallyBijective (Type t) :=
  type_WEqualsLocallyBijective_of_univLE (L := L)

/-- Helper for Lemma 7.28.5: once `W` agrees with local bijectivity in both `Type` universes,
whiskering by the fixed `ULift` functor preserves sheafification. -/
theorem uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    [L.WEqualsLocallyBijective (Type t)]
    [L.WEqualsLocallyBijective (Type (max t w))] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  refine ⟨?_⟩
  intro P Q f hf
  let _ : Presheaf.IsLocallyInjective L f :=
    (L.W_iff_isLocallyBijective f).1 hf |>.1
  let _ : Presheaf.IsLocallySurjective L f :=
    (L.W_iff_isLocallyBijective f).1 hf |>.2
  -- `ULift` leaves equalizer and image sieves unchanged, so local bijectivity transports
  -- directly across whiskering.
  let _ : Presheaf.IsLocallyInjective L (Functor.whiskerRight f F) :=
    isLocallyInjective_whisker_ulift (L := L) (η := f)
  let _ : Presheaf.IsLocallySurjective L (Functor.whiskerRight f F) :=
    isLocallySurjective_whisker_ulift (L := L) (η := f)
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight f F))

/-- Helper for Lemma 7.28.5: the fixed `ULift` functor on types preserves sheafification for any
site once the small and large sheafification units are known to be locally bijective. -/

noncomputable def ulift_sheafCompose_comparison_hom
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    sheafify L (P ⋙ (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) ⟶
      sheafify L P ⋙ (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)) :=
  (sheafToPresheaf L (Type (max t w))).map
    ((sheafComposeNatTrans L
      (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))
      (sheafificationAdjunction L (Type t))
      (sheafificationAdjunction L (Type (max t w)))).app P)

/-- Helper for Lemma 7.28.5: the underlying `ULift` comparison satisfies the standard
`toSheafify` factorization. -/
theorem ulift_sheafCompose_comparison_hom_fac
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    toSheafify L
        (P ⋙
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))) ≫
      ulift_sheafCompose_comparison_hom (L := L) P =
        Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w)) := by
  -- Unfold the named comparison back to the standard sheafification comparison component.
  simpa [ulift_sheafCompose_comparison_hom] using
    sheafComposeNatTrans_fac L
      (CategoryTheory.uliftFunctor.{w, t} :
        Type t ⥤ Type (max t w))
      (sheafificationAdjunction L (Type t))
      (sheafificationAdjunction L (Type (max t w))) P

/-- Helper for Lemma 7.28.5: the `ULift` comparison component is an isomorphism exactly when the
whiskered small sheafification unit is a `W`-morphism in the large target universe. -/
theorem ulift_sheafComposeNatTrans_app_isIso_iff_whiskered_toSheafify_W
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t) :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))
          (sheafificationAdjunction L (Type t))
          (sheafificationAdjunction L (Type (max t w)))).app P) ↔
      L.W
        (Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{w, t} :
            Type t ⥤ Type (max t w))) := by
  let Tl := Type (max t w)
  let U : Type t ⥤ Tl := CategoryTheory.uliftFunctor.{w, t}
  let η :=
    (sheafComposeNatTrans L U
      (sheafificationAdjunction L (Type t))
      (sheafificationAdjunction L Tl)).app P
  have hW :
      L.W (ulift_sheafCompose_comparison_hom (L := L) P) ↔ IsIso η := by
    -- Forgetting to presheaves identifies the comparison with the corresponding `W`-statement.
    simpa [ulift_sheafCompose_comparison_hom, η] using
      (L.W_sheafToPresheaf_map_iff_isIso η)
  -- Reduce the componentwise isomorphism to a `W`-statement for its underlying presheaf map.
  change IsIso η ↔ L.W (Functor.whiskerRight (toSheafify L P) U)
  rw [← hW, ← ulift_sheafCompose_comparison_hom_fac (L := L) (P := P)]
  -- Precomposition by the large-universe sheafification unit does not change membership in `W`.
  exact
    (((GrothendieckTopology.W (J := L) (A := Tl)).precomp_iff
      (W' := GrothendieckTopology.W (J := L) (A := Tl))
      (toSheafify L (P ⋙ U))
      (ulift_sheafCompose_comparison_hom (L := L) P)
      (L.W_toSheafify (P ⋙ U))).symm)

/-- Helper for Lemma 7.28.5: if the small sheafification unit is locally bijective, then its
`ULift`-whiskering is locally bijective as well. -/
theorem whiskered_toSheafify_isLocallyBijective_for_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    (P : Eᵒᵖ ⥤ Type t)
    [HasWeakSheafify L (Type t)]
    [Presheaf.IsLocallyInjective L (toSheafify L P)]
    [Presheaf.IsLocallySurjective L (toSheafify L P)] :
    Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) ∧
      Presheaf.IsLocallySurjective L
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  let F : Type t ⥤ Type (max t w) :=
    CategoryTheory.uliftFunctor.{w, t}
  constructor
  · -- `ULift` leaves the equalizer sieves unchanged, so local injectivity transports directly.
    exact isLocallyInjective_whisker_ulift (L := L) (η := toSheafify L P)
  · -- The same argument on image sieves transports local surjectivity across `ULift`.
    exact isLocallySurjective_whisker_ulift (L := L) (η := toSheafify L P)

/-- Helper for Lemma 7.28.5: the small `Type`-valued sheafification unit is locally bijective
once the same site admits weak sheafification in the larger `ULift` target universe. -/
theorem small_type_toSheafify_isLocallyBijective_for_site
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    [HasWeakSheafify L (Type (max t w))]
    (P : Eᵒᵖ ⥤ Type t)
    (hPres :
      L.PreservesSheafification
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)))
    (hInj :
      Presheaf.IsLocallyInjective L
        (toSheafify L
          (P ⋙
            (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w)))))
    (hSurj :
      Presheaf.IsLocallySurjective L
        (toSheafify L
          (P ⋙
            (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))))) :
    Presheaf.IsLocallyInjective L (toSheafify L P) ∧
      Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  have hWhiskerInj :
      Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P) F) := by
    let _ : L.PreservesSheafification F := hPres
    let _ : Presheaf.IsLocallyInjective L (toSheafify L (P ⋙ F)) := hInj
    -- Rewrite the whiskered small unit to the large unit before reflecting injectivity back.
    rw [← sheafComposeIso_hom_fac (J := L) (F := F) (P := P)]
    infer_instance
  have hWhiskerSurj :
      Presheaf.IsLocallySurjective L
        (Functor.whiskerRight (toSheafify L P) F) := by
    let _ : L.PreservesSheafification F := hPres
    let _ : Presheaf.IsLocallySurjective L (toSheafify L (P ⋙ F)) := hSurj
    -- The same comparison identifies the whiskered small unit with the large unit upstairs.
    rw [← sheafComposeIso_hom_fac (J := L) (F := F) (P := P)]
    infer_instance
  constructor
  · letI :
        Presheaf.IsLocallyInjective L
          (Functor.whiskerRight (toSheafify L P) F) := hWhiskerInj
    -- Reflect local injectivity back down through `ULift`.
    simpa [F] using
      (locallyInjective_of_whisker_ulift (L := L) (η := toSheafify L P) :
        Presheaf.IsLocallyInjective L (toSheafify L P))
  · letI :
        Presheaf.IsLocallySurjective L
          (Functor.whiskerRight (toSheafify L P) F) := hWhiskerSurj
    -- Reflect local surjectivity back down through `ULift`.
    simpa [F] using
      (locallySurjective_of_whisker_ulift (L := L) (η := toSheafify L P) :
        Presheaf.IsLocallySurjective L (toSheafify L P))

/-- Helper for Lemma 7.28.5: once the small sheafification unit is locally bijective and `W`
agrees with local bijectivity in the target universe, the whiskered unit is already in `W`. -/
theorem whiskered_toSheafify_W_of_small_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type t)]
    (P : Eᵒᵖ ⥤ Type t)
    [Presheaf.IsLocallyInjective L (toSheafify L P)]
    [Presheaf.IsLocallySurjective L (toSheafify L P)]
    (hW : L.WEqualsLocallyBijective (Type (max t w))) :
    L.W
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{w, t} : Type t ⥤ Type (max t w))) := by
  let Ts := Type (max t w)
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{w, t}
  let _ : L.WEqualsLocallyBijective Ts := hW
  rcases whiskered_toSheafify_isLocallyBijective_for_ulift (L := L) P with ⟨hWhiskerInj, hWhiskerSurj⟩
  letI :
      Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P) F) := hWhiskerInj
  letI :
      Presheaf.IsLocallySurjective L
        (Functor.whiskerRight (toSheafify L P) F) := hWhiskerSurj
  -- Once the whiskered unit is locally bijective in the target universe, `W` follows formally.
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight (toSheafify L P) F))

end CategoryTheory
