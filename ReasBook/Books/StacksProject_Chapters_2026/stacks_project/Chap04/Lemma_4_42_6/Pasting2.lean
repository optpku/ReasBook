module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Lemma_4_42_6.SliceRepresentable
public import stacks_project.Chap04.Lemma_4_42_6.Core
public import stacks_project.Chap04.Lemma_4_42_6.Pasting
public import stacks_project.Chap04.Lemma_4_40_3
public import stacks_project.Chap04.Lemma_4_35_7
public import stacks_project.Chap04.Remark_4_35_8
public import stacks_project.Chap04.Lemma_4_31_13

@[expose] public section

/-!
# Pasting support II for Lemma 4.42.6 — the diagonal collapse at the `⊡` level

This module adds the categorical-pullback (`⊡`) infrastructure needed to identify, *up to
equivalence over `C`*, the slice product `2`-fibre product `C/V ×_X C/U` with the base change of
the diagonal `C/(U⨯V) ×_{X×_C X} X`.  Everything is phrased so that the heavy terminal-lift
comparison morphisms `H` and `Dg` are kept opaque (via `set`/`let`); only their cheap leg-cell
projections `.left`/`.right` and the Remark-4.35.8 bridge `twoFibreProductEquivCatPullback` are
forced.

The decisive structural fact is the *strict* `2`-functor "forget a `2`-cell to its underlying
natural transformation": `ownerTwoCellFunctor`.  All the `coh` compatibilities below are images
of the square-morphism compatibility field `comm` under this `2`-functor.
-/

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

/-! ### Two further congruences for the categorical pullback `⊡` -/

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- The explicit functor `Z ⥤ F ⊡ G` assembled from two leg functors and a structural natural
isomorphism. This is definitionally `(functorEquiv F G Z).inverse.obj ⟨L, R, e⟩`, but stated as a
plain `@[simps]` functor so that it behaves well as the *source* of a comparison
(`CategoricalPullback.mkNatIso` overflows `whnf` when applied to a functor in
`functorEquiv.inverse.obj` form). -/
@[simps]
noncomputable def mkCatPullbackFunctor {Z : Type*} [Category Z]
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (L : Z ⥤ A₀) (R : Z ⥤ B₀) (e : L ⋙ F ≅ R ⋙ G) :
    Z ⥤ F ⊡ G where
  obj z := { fst := L.obj z, snd := R.obj z, iso := e.app z }
  map {z z'} f := { fst := L.map f, snd := R.map f, w := e.hom.naturality f }

/-- Swap the two legs of a categorical pullback. -/
@[simps]
noncomputable def catPullbackSwapFunctor (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ G ⥤ G ⊡ F where
  obj x := { fst := x.snd, snd := x.fst, iso := x.iso.symm }
  map {x y} f := { fst := f.snd, snd := f.fst, w := f.w' }

/-- The categorical pullback is invariant under swapping the two legs. -/
noncomputable def catPullbackSwap (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ G ≌ G ⊡ F where
  functor := catPullbackSwapFunctor F G
  inverse := catPullbackSwapFunctor G F
  unitIso := NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by simp [catPullbackSwapFunctor]))
    (by intro x y f; apply CategoricalPullback.hom_ext <;> simp [catPullbackSwapFunctor])
  counitIso := NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by simp [catPullbackSwapFunctor]))
    (by intro x y f; apply CategoricalPullback.hom_ext <;> simp [catPullbackSwapFunctor])

/-- Precompose the left leg with a functor `E` on its domain. -/
@[simps obj_fst obj_snd map_fst map_snd]
noncomputable def catPullbackMapLeftDom {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (E ⋙ F) ⊡ G ⥤ F ⊡ G where
  obj x := { fst := E.obj x.fst, snd := x.snd, iso := x.iso }
  map {x y} f := { fst := E.map f.fst, snd := f.snd, w := f.w }

instance {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀) [E.Faithful] (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapLeftDom E F G).Faithful where
  map_injective h := by
    apply CategoricalPullback.hom_ext
    · apply E.map_injective; exact congrArg (fun t => t.fst) h
    · exact congrArg (fun t => t.snd) h

instance {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀) [E.Full] [E.Faithful]
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapLeftDom E F G).Full where
  map_surjective {x y} g := by
    refine ⟨{ fst := E.preimage g.fst, snd := g.snd, w := ?_ }, ?_⟩
    · have hg := g.w
      simpa [Functor.comp_map, E.map_preimage] using hg
    · apply CategoricalPullback.hom_ext
      · simp
      · simp

instance {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀) [E.EssSurj] [E.Full] [E.Faithful]
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapLeftDom E F G).EssSurj where
  mem_essImage y := by
    refine ⟨{ fst := E.objPreimage y.fst, snd := y.snd,
              iso := F.mapIso (E.objObjPreimageIso y.fst) ≪≫ y.iso }, ⟨?_⟩⟩
    refine CategoricalPullback.mkIso (E.objObjPreimageIso y.fst) (Iso.refl _) ?_
    dsimp [catPullbackMapLeftDom]
    simp

instance {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀) [E.EssSurj] [E.Full] [E.Faithful]
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapLeftDom E F G).IsEquivalence where

/-- The categorical pullback is invariant under precomposing the left leg with an equivalence of
its domain. -/
noncomputable def catPullbackCongrLeftDom {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (E.functor ⋙ F) ⊡ G ≌ F ⊡ G :=
  (catPullbackMapLeftDom E.functor F G).asEquivalence

/-- The forward functor of `catPullbackCongrLeftDom` is compatible with the left projection, after
composing the left projection with base functors compatible under the domain equivalence. -/
noncomputable def catPullbackCongrLeftDom_functor_fst_baseIso
    {A₀' E₀ : Type*} [Category A₀'] [Category E₀]
    (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pA : A₀ ⥤ E₀) (pA' : A₀' ⥤ E₀)
    (α : E.functor ⋙ pA ≅ pA') :
    (catPullbackCongrLeftDom E F G).functor ⋙ (π₁ F G ⋙ pA) ≅
      π₁ (E.functor ⋙ F) G ⋙ pA' := by
  simpa [Functor.assoc] using
    (Functor.isoWhiskerLeft (π₁ (E.functor ⋙ F) G) α)

/-- The inverse functor of `catPullbackCongrLeftDom` is compatible with the left projection, after
composing the left projection with base functors compatible under the domain equivalence. -/
noncomputable def catPullbackCongrLeftDom_inverse_fst_baseIso
    {A₀' E₀ : Type*} [Category A₀'] [Category E₀]
    (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pA : A₀ ⥤ E₀) (pA' : A₀' ⥤ E₀)
    (α : E.functor ⋙ pA ≅ pA') :
    (catPullbackCongrLeftDom E F G).inverse ⋙
        (π₁ (E.functor ⋙ F) G ⋙ pA') ≅
      π₁ F G ⋙ pA :=
  equivalence_inverse_baseIso (catPullbackCongrLeftDom E F G)
    (π₁ (E.functor ⋙ F) G ⋙ pA') (π₁ F G ⋙ pA)
    (catPullbackCongrLeftDom_functor_fst_baseIso E F G pA pA' α)

/-- Precompose the right leg with a functor `E` on its domain. -/
@[simps obj_fst obj_snd map_fst map_snd]
noncomputable def catPullbackMapRightDom {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ (E ⋙ G) ⥤ F ⊡ G where
  obj x := { fst := x.fst, snd := E.obj x.snd, iso := x.iso }
  map {x y} f := { fst := f.fst, snd := E.map f.snd, w := f.w }

instance {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀) [E.Faithful]
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapRightDom E F G).Faithful where
  map_injective h := by
    apply CategoricalPullback.hom_ext
    · exact congrArg (fun t => t.fst) h
    · apply E.map_injective
      exact congrArg (fun t => t.snd) h

instance {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀) [E.Full] [E.Faithful]
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapRightDom E F G).Full where
  map_surjective {x y} g := by
    refine ⟨{ fst := g.fst, snd := E.preimage g.snd, w := ?_ }, ?_⟩
    · have hg := g.w
      simpa [Functor.comp_map, E.map_preimage] using hg
    · apply CategoricalPullback.hom_ext
      · simp
      · simp

instance {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀) [E.EssSurj] [E.Full]
    [E.Faithful] (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapRightDom E F G).EssSurj where
  mem_essImage y := by
    refine ⟨{ fst := y.fst, snd := E.objPreimage y.snd,
              iso := y.iso ≪≫ (G.mapIso (E.objObjPreimageIso y.snd)).symm }, ⟨?_⟩⟩
    refine CategoricalPullback.mkIso (Iso.refl _) (E.objObjPreimageIso y.snd) ?_
    dsimp [catPullbackMapRightDom]
    simp

instance {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀) [E.EssSurj] [E.Full]
    [E.Faithful] (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackMapRightDom E F G).IsEquivalence where

/-- The categorical pullback is invariant under precomposing the right leg with an equivalence of
its domain. -/
noncomputable def catPullbackCongrRightDom {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ (E.functor ⋙ G) ≌ F ⊡ G :=
  (catPullbackMapRightDom E.functor F G).asEquivalence

/-- The forward functor of `catPullbackCongrRightDom` is compatible with the right projection,
after composing the right projection with base functors compatible under the domain equivalence. -/
noncomputable def catPullbackCongrRightDom_functor_snd_baseIso
    {B₀' E₀ : Type*} [Category B₀'] [Category E₀]
    (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pB : B₀ ⥤ E₀) (pB' : B₀' ⥤ E₀)
    (α : E.functor ⋙ pB ≅ pB') :
    (catPullbackCongrRightDom E F G).functor ⋙ (π₂ F G ⋙ pB) ≅
      π₂ F (E.functor ⋙ G) ⋙ pB' := by
  simpa [Functor.assoc] using
    (Functor.isoWhiskerLeft (π₂ F (E.functor ⋙ G)) α)

/-- The inverse functor of `catPullbackCongrRightDom` is compatible with the right projection,
after composing the right projection with base functors compatible under the domain equivalence. -/
noncomputable def catPullbackCongrRightDom_inverse_snd_baseIso
    {B₀' E₀ : Type*} [Category B₀'] [Category E₀]
    (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pB : B₀ ⥤ E₀) (pB' : B₀' ⥤ E₀)
    (α : E.functor ⋙ pB ≅ pB') :
    (catPullbackCongrRightDom E F G).inverse ⋙
        (π₂ F (E.functor ⋙ G) ⋙ pB') ≅
      π₂ F G ⋙ pB :=
  equivalence_inverse_baseIso (catPullbackCongrRightDom E F G)
    (π₂ F (E.functor ⋙ G) ⋙ pB') (π₂ F G ⋙ pB)
    (catPullbackCongrRightDom_functor_snd_baseIso E F G pB pB' α)

end CatPullbackMore

section CatPullbackAssocLeftProjection

variable {A₀' A₀ B₀ D₀ : Type*} [Category A₀'] [Category A₀] [Category B₀]
  [Category D₀]

/-- Reassociate `A' ×_A (A ×_D B)` with `A' ×_D B`, using the left projection of the inner
pullback. -/
@[simps obj_fst obj_snd map_fst map_snd]
noncomputable def catPullbackAssocLeftProjectionFunctor
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    K ⊡ (π₁ F G) ⥤ (K ⋙ F) ⊡ G where
  obj x := { fst := x.fst, snd := x.snd.snd, iso := F.mapIso x.iso ≪≫ x.snd.iso }
  map {x y} φ :=
    { fst := φ.fst
      snd := φ.snd.snd
      w := by
        dsimp
        have houter0 := congrArg (fun t => F.map t) φ.w
        simp only [Functor.map_comp] at houter0
        have houter : F.map (K.map φ.fst) ≫ F.map y.iso.hom =
            F.map x.iso.hom ≫ F.map φ.snd.fst := by
          simpa using houter0
        have hinner : F.map φ.snd.fst ≫ y.snd.iso.hom =
            x.snd.iso.hom ≫ G.map φ.snd.snd := φ.snd.w
        calc
          F.map (K.map φ.fst) ≫ (F.map y.iso.hom ≫ y.snd.iso.hom)
              = (F.map (K.map φ.fst) ≫ F.map y.iso.hom) ≫ y.snd.iso.hom := by
                simp [Category.assoc]
          _ = (F.map x.iso.hom ≫ F.map φ.snd.fst) ≫ y.snd.iso.hom := by
                simpa using congrArg (fun t => t ≫ y.snd.iso.hom) houter
          _ = F.map x.iso.hom ≫ (F.map φ.snd.fst ≫ y.snd.iso.hom) := by
                simp [Category.assoc]
          _ = F.map x.iso.hom ≫ (x.snd.iso.hom ≫ G.map φ.snd.snd) := by
                simpa [Category.assoc] using congrArg (fun t => F.map x.iso.hom ≫ t) hinner
          _ = (F.map x.iso.hom ≫ x.snd.iso.hom) ≫ G.map φ.snd.snd := by
                simp [Category.assoc] }

/-- Inverse reassociation functor for `catPullbackAssocLeftProjectionFunctor`. -/
@[simps obj_fst obj_snd map_fst map_snd]
noncomputable def catPullbackAssocLeftProjectionInverse
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (K ⋙ F) ⊡ G ⥤ K ⊡ (π₁ F G) where
  obj x :=
    { fst := x.fst
      snd :=
        { fst := K.obj x.fst
          snd := x.snd
          iso := x.iso }
      iso := Iso.refl _ }
  map {x y} φ :=
    { fst := φ.fst
      snd :=
        { fst := K.map φ.fst
          snd := φ.snd
          w := φ.w }
      w := by simp }

/-- Unit isomorphism for `catPullbackAssocLeftProjectionFunctor`. -/
noncomputable def catPullbackAssocLeftProjectionUnitIso
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    𝟭 (K ⊡ (π₁ F G)) ≅
      catPullbackAssocLeftProjectionFunctor K F G ⋙
        catPullbackAssocLeftProjectionInverse K F G :=
  NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (Iso.refl _)
      (CategoricalPullback.mkIso x.iso.symm (Iso.refl _) (by
        simp [catPullbackAssocLeftProjectionFunctor, catPullbackAssocLeftProjectionInverse]))
      (by simp [catPullbackAssocLeftProjectionFunctor, catPullbackAssocLeftProjectionInverse]))
    (by
      intro x y φ
      apply CategoricalPullback.hom_ext
      · simp [catPullbackAssocLeftProjectionFunctor, catPullbackAssocLeftProjectionInverse]
      · apply CategoricalPullback.hom_ext
        · simpa using φ.w'
        · simp [catPullbackAssocLeftProjectionFunctor, catPullbackAssocLeftProjectionInverse])

/-- Counit isomorphism for `catPullbackAssocLeftProjectionFunctor`. -/
noncomputable def catPullbackAssocLeftProjectionCounitIso
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    catPullbackAssocLeftProjectionInverse K F G ⋙
        catPullbackAssocLeftProjectionFunctor K F G ≅
      𝟭 ((K ⋙ F) ⊡ G) :=
  NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      simp [catPullbackAssocLeftProjectionFunctor, catPullbackAssocLeftProjectionInverse]))
    (by
      intro x y φ
      apply CategoricalPullback.hom_ext <;>
        simp [catPullbackAssocLeftProjectionFunctor, catPullbackAssocLeftProjectionInverse])

noncomputable instance catPullbackAssocLeftProjectionFunctor_isEquivalence
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackAssocLeftProjectionFunctor K F G).IsEquivalence :=
  Functor.IsEquivalence.mk' (catPullbackAssocLeftProjectionInverse K F G)
    (catPullbackAssocLeftProjectionUnitIso K F G)
    (catPullbackAssocLeftProjectionCounitIso K F G)

noncomputable instance catPullbackAssocLeftProjectionInverse_isEquivalence
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (catPullbackAssocLeftProjectionInverse K F G).IsEquivalence :=
  Functor.IsEquivalence.mk' (catPullbackAssocLeftProjectionFunctor K F G)
    (catPullbackAssocLeftProjectionCounitIso K F G).symm
    (catPullbackAssocLeftProjectionUnitIso K F G).symm

/-- The inverse reassociation keeps the left projection to `A'`. -/
noncomputable def catPullbackAssocLeftProjection_inverse_fst_baseIso
    {E₀ : Type*} [Category E₀]
    (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (pA : A₀' ⥤ E₀) :
    catPullbackAssocLeftProjectionInverse K F G ⋙
        (π₁ K (π₁ F G) ⋙ pA) ≅
      π₁ (K ⋙ F) G ⋙ pA :=
  NatIso.ofComponents (fun _ => Iso.refl _)

end CatPullbackAssocLeftProjection

variable {C : Type (max u v)} [Category.{v} C]

/-! ### Ordinary slice pullbacks -/

section OverMapPullback

variable [Limits.HasPullbacks C]

/-- The categorical pullback of two slice-postcomposition functors is the slice over the ordinary
pullback of their base arrows. -/
noncomputable def overMapPullbackToOverPullback {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    (Over.map f) ⊡ (Over.map a) ⥤ Over (Limits.pullback f a) where
  obj x := Over.mk (Limits.pullback.lift x.fst.hom (x.iso.hom.left ≫ x.snd.hom) (by
    have hw := Over.w x.iso.hom
    simpa [Over.map_obj_hom, Category.assoc] using hw.symm))
  map {x y} φ := Over.homMk φ.fst.left (by
    apply Limits.pullback.hom_ext
    · simpa [Limits.pullback.lift_fst] using Over.w φ.fst
    · have hw : φ.fst.left ≫ y.iso.hom.left = x.iso.hom.left ≫ φ.snd.left := by
        simpa using congrArg (fun m => m.left) φ.w
      have hsnd :
          φ.fst.left ≫ (y.iso.hom.left ≫ y.snd.hom) =
            x.iso.hom.left ≫ x.snd.hom := by
        have h₁ :
            (φ.fst.left ≫ y.iso.hom.left) ≫ y.snd.hom =
              (x.iso.hom.left ≫ φ.snd.left) ≫ y.snd.hom :=
          congrArg (fun t => t ≫ y.snd.hom) hw
        have h₂ :
            x.iso.hom.left ≫ (φ.snd.left ≫ y.snd.hom) =
              x.iso.hom.left ≫ x.snd.hom :=
          congrArg (fun t => x.iso.hom.left ≫ t) (Over.w φ.snd)
        simpa [Category.assoc] using h₁.trans (by simpa [Category.assoc] using h₂)
      simpa [Limits.pullback.lift_snd, Category.assoc] using hsnd)
  map_id x := by
    apply Over.OverMorphism.ext
    simp
  map_comp φ ψ := by
    apply Over.OverMorphism.ext
    simp

/-- The inverse functor from the slice over the ordinary pullback to the categorical pullback of
slice-postcomposition functors. -/
noncomputable def overPullbackToOverMapPullback {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    Over (Limits.pullback f a) ⥤ (Over.map f) ⊡ (Over.map a) where
  obj c :=
    { fst := Over.mk (c.hom ≫ Limits.pullback.fst f a)
      snd := Over.mk (c.hom ≫ Limits.pullback.snd f a)
      iso := Over.isoMk (Iso.refl c.left) (by
        dsimp
        rw [Category.id_comp]
        simp [Category.assoc, Limits.pullback.condition]) }
  map {c d} g :=
    { fst := Over.homMk g.left (by
        simpa [Category.assoc] using
          congrArg (fun t => t ≫ Limits.pullback.fst f a) (Over.w g))
      snd := Over.homMk g.left (by
        simpa [Category.assoc] using
          congrArg (fun t => t ≫ Limits.pullback.snd f a) (Over.w g))
      w := by
        apply Over.OverMorphism.ext
        simp }
  map_id c := by
    apply CategoricalPullback.hom_ext <;> apply Over.OverMorphism.ext <;> simp
  map_comp g h := by
    apply CategoricalPullback.hom_ext <;> apply Over.OverMorphism.ext <;> simp

/-- Unit isomorphism for `overMapPullbackToOverPullback`. -/
noncomputable def overMapPullbackUnitIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    𝟭 ((Over.map f) ⊡ (Over.map a)) ≅
      overMapPullbackToOverPullback f a ⋙ overPullbackToOverMapPullback f a :=
  NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso
      (Over.isoMk (Iso.refl x.fst.left) (by
        dsimp [overMapPullbackToOverPullback, overPullbackToOverMapPullback]
        change 𝟙 x.fst.left ≫
            (Limits.pullback.lift x.fst.hom (x.iso.hom.left ≫ x.snd.hom) _ ≫
              Limits.pullback.fst f a) =
          x.fst.hom
        simp [Limits.pullback.lift_fst]))
      (Over.isoMk ((Over.forget U).mapIso x.iso.symm) (by
        dsimp [overMapPullbackToOverPullback, overPullbackToOverMapPullback]
        have hs : x.iso.inv.left ≫ (x.iso.hom.left ≫ x.snd.hom) = x.snd.hom := by
          have hleft : x.iso.inv.left ≫ x.iso.hom.left = 𝟙 x.snd.left := by
            exact congrArg (fun k => k.left) x.iso.inv_hom_id
          simpa [Category.assoc] using congrArg (fun t => t ≫ x.snd.hom) hleft
        simpa [Limits.pullback.lift_snd, Category.assoc] using hs))
      (by
        apply Over.OverMorphism.ext
        dsimp [overMapPullbackToOverPullback, overPullbackToOverMapPullback]
        change 𝟙 x.fst.left ≫ 𝟙 x.fst.left = x.iso.hom.left ≫ x.iso.inv.left
        rw [Category.id_comp]
        exact (congrArg (fun k => k.left) x.iso.hom_inv_id).symm))
    (by
      intro x y φ
      apply CategoricalPullback.hom_ext
      · apply Over.OverMorphism.ext
        simp [overMapPullbackToOverPullback, overPullbackToOverMapPullback]
      · apply Over.OverMorphism.ext
        dsimp [overMapPullbackToOverPullback, overPullbackToOverMapPullback]
        change φ.snd.left ≫ (y.iso.inv).left = (x.iso.inv).left ≫ φ.fst.left
        simpa using congrArg (fun m => m.left) φ.w')

/-- Counit isomorphism for `overMapPullbackToOverPullback`. -/
noncomputable def overMapPullbackCounitIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    overPullbackToOverMapPullback f a ⋙ overMapPullbackToOverPullback f a ≅
      𝟭 (Over (Limits.pullback f a)) :=
  NatIso.ofComponents
    (fun c => Over.isoMk (Iso.refl c.left) (by
      dsimp [overPullbackToOverMapPullback, overMapPullbackToOverPullback]
      apply Limits.pullback.hom_ext <;> simp [Limits.pullback.lift_fst, Limits.pullback.lift_snd]))
    (by
      intro c d g
      apply Over.OverMorphism.ext
      simp [overPullbackToOverMapPullback, overMapPullbackToOverPullback])

noncomputable instance overMapPullbackToOverPullback_isEquivalence {A W U : C}
    (f : W ⟶ U) (a : A ⟶ U) :
    (overMapPullbackToOverPullback f a).IsEquivalence := by
  exact Functor.IsEquivalence.mk'
    (overPullbackToOverMapPullback f a)
    (overMapPullbackUnitIso f a)
    (overMapPullbackCounitIso f a)

@[simp] theorem overMapPullbackToOverPullback_comp_forget {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    overMapPullbackToOverPullback f a ⋙ Over.forget (Limits.pullback f a) =
      π₁ (Over.map f) (Over.map a) ⋙ Over.forget W :=
  rfl

end OverMapPullback

/-- Package a four-step chain of equivalence functors together with its composite compatibility
with base projections. -/
noncomputable def functorCompBaseIso4_transportData
    {P Q : FibredInGroupoidsOver C}
    {A₁ A₂ A₃ : Type*} [Category A₁] [Category A₂] [Category A₃]
    (F₁ : P.S ⥤ A₁) (F₂ : A₁ ⥤ A₂) (F₃ : A₂ ⥤ A₃) (F₄ : A₃ ⥤ Q.S)
    [F₁.IsEquivalence] [F₂.IsEquivalence] [F₃.IsEquivalence] [F₄.IsEquivalence]
    (q₃ : A₃ ⥤ C) (q₂ : A₂ ⥤ C) (q₁ : A₁ ⥤ C)
    (h₄ : F₄ ⋙ Q.p ≅ q₃) (h₃ : F₃ ⋙ q₃ ≅ q₂)
    (h₂ : F₂ ⋙ q₂ ≅ q₁) (h₁ : F₁ ⋙ q₁ ≅ P.p) :
    Σ' (e : P.S ⥤ Q.S), Σ' (_ : e.IsEquivalence), e ⋙ Q.p ≅ P.p := by
  let F := F₁ ⋙ (F₂ ⋙ (F₃ ⋙ F₄))
  haveI : F.IsEquivalence := by
    dsimp [F]
    infer_instance
  have h₃₄ : (F₃ ⋙ F₄) ⋙ Q.p ≅ q₂ :=
    functorCompBaseIso F₃ F₄ Q.p q₃ q₂ h₄ h₃
  have h₂₃₄ : (F₂ ⋙ (F₃ ⋙ F₄)) ⋙ Q.p ≅ q₁ :=
    functorCompBaseIso F₂ (F₃ ⋙ F₄) Q.p q₂ q₁ h₃₄ h₂
  have h₁₂₃₄ : F ⋙ Q.p ≅ P.p :=
    functorCompBaseIso F₁ (F₂ ⋙ (F₃ ⋙ F₄)) Q.p q₁ P.p h₂₃₄ h₁
  exact ⟨F, inferInstance, h₁₂₃₄⟩

/-- Explicit-instance variant of `functorCompBaseIso4_transportData`. -/
noncomputable def functorCompBaseIso4_transportData_explicit
    {P Q : FibredInGroupoidsOver C}
    {A₁ A₂ A₃ : Type*} [Category A₁] [Category A₂] [Category A₃]
    (F₁ : P.S ⥤ A₁) (F₂ : A₁ ⥤ A₂) (F₃ : A₂ ⥤ A₃) (F₄ : A₃ ⥤ Q.S)
    (hF₁ : F₁.IsEquivalence) (hF₂ : F₂.IsEquivalence)
    (hF₃ : F₃.IsEquivalence) (hF₄ : F₄.IsEquivalence)
    (q₃ : A₃ ⥤ C) (q₂ : A₂ ⥤ C) (q₁ : A₁ ⥤ C)
    (h₄ : F₄ ⋙ Q.p ≅ q₃) (h₃ : F₃ ⋙ q₃ ≅ q₂)
    (h₂ : F₂ ⋙ q₂ ≅ q₁) (h₁ : F₁ ⋙ q₁ ≅ P.p) :
    Σ' (e : P.S ⥤ Q.S), Σ' (_ : e.IsEquivalence), e ⋙ Q.p ≅ P.p := by
  haveI : F₁.IsEquivalence := hF₁
  haveI : F₂.IsEquivalence := hF₂
  haveI : F₃.IsEquivalence := hF₃
  haveI : F₄.IsEquivalence := hF₄
  exact functorCompBaseIso4_transportData F₁ F₂ F₃ F₄ q₃ q₂ q₁ h₄ h₃ h₂ h₁

/-- The forward Remark-4.35.8 comparison preserves the left projection functor itself, not only
the composite with the base projection. -/
noncomputable def twoFibreProductEquivCatPullback_functor_fstIso
    {X Y S : FibredInGroupoidsOver C} (F : X ⟶ S) (G : Y ⟶ S) :
    (twoFibreProductEquivCatPullback F G).functor ⋙
        π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ≅
      FibredInGroupoidsMor.G (FibredInGroupoidsOver.twoFibreProductLeftProjection F G) :=
  Iso.refl _

/-- The inverse Remark-4.35.8 comparison preserves the left projection functor itself. -/
noncomputable def twoFibreProductEquivCatPullback_inverse_fstIso
    {X Y S : FibredInGroupoidsOver C} (F : X ⟶ S) (G : Y ⟶ S) :
    (twoFibreProductEquivCatPullback F G).inverse ⋙
        FibredInGroupoidsMor.G (FibredInGroupoidsOver.twoFibreProductLeftProjection F G) ≅
      π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) :=
  equivalence_inverse_baseIso (twoFibreProductEquivCatPullback F G)
    (FibredInGroupoidsMor.G (FibredInGroupoidsOver.twoFibreProductLeftProjection F G))
    (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G))
    (twoFibreProductEquivCatPullback_functor_fstIso F G)

/-- The forward functor of `catPullbackCongrRightDom` does not change the left projection. -/
noncomputable def catPullbackCongrRightDom_functor_fst_baseIso
    {A₀ B₀ B₀' D₀ E₀ : Type*} [Category A₀] [Category B₀] [Category B₀']
    [Category D₀] [Category E₀]
    (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (pA : A₀ ⥤ E₀) :
    (catPullbackCongrRightDom E F G).functor ⋙ (π₁ F G ⋙ pA) ≅
      π₁ F (E.functor ⋙ G) ⋙ pA :=
  Iso.refl _

/-- The inverse functor of `catPullbackCongrRightDom` does not change the left projection. -/
noncomputable def catPullbackCongrRightDom_inverse_fst_baseIso
    {A₀ B₀ B₀' D₀ E₀ : Type*} [Category A₀] [Category B₀] [Category B₀']
    [Category D₀] [Category E₀]
    (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (pA : A₀ ⥤ E₀) :
    (catPullbackCongrRightDom E F G).inverse ⋙
        (π₁ F (E.functor ⋙ G) ⋙ pA) ≅
      π₁ F G ⋙ pA :=
  equivalence_inverse_baseIso (catPullbackCongrRightDom E F G)
    (π₁ F (E.functor ⋙ G) ⋙ pA) (π₁ F G ⋙ pA)
    (catPullbackCongrRightDom_functor_fst_baseIso E F G pA)

/-- Base-changing a representable category fibred in groupoids along a slice map remains
representable.  This is the concrete `C/W ×_{C/U} C/A ≃ C/(W ×_U A)` step used in the Stacks
proof of Lemma 4.42.6. -/
theorem twoFibreProduct_overMap_representable_of_representable
    [Limits.HasPullbacks C]
    {Q : FibredInGroupoidsOver C} {U W : C}
    (j : Q ⟶ ofFunctor (Over.forget U)) (f : W ⟶ U)
    (hQ : Q.IsRepresentable) :
    (FibredInGroupoidsOver.twoFibreProduct (FibredInGroupoidsOver.overMap f) j).IsRepresentable := by
  rw [FibredInGroupoidsOver.isRepresentable_iff_exists_presentation] at hQ
  rcases hQ with ⟨A, e, he⟩
  let hid : FibredInGroupoidsMor.IsEquivalenceOverBase
      (𝟙 (ofFunctor (Over.forget U)) : ofFunctor (Over.forget U) ⟶ ofFunctor (Over.forget U)) :=
    FibredInGroupoidsOver.hom_isEquivalenceOverBase (Bicategory.Equivalence.id _)
  let a : A ⟶ U :=
    FibredInGroupoidsOver.mor_isoClasses_equiv_hom e
      (𝟙 (ofFunctor (Over.forget U))) he hid (Quotient.mk'' j)
  have ha : FibredInGroupoidsMor.InducesHom j e
      (𝟙 (ofFunctor (Over.forget U))) a := by
    exact (FibredInGroupoidsOver.inducesHom_iff_mor_isoClasses_equiv_hom_eq
      e (𝟙 (ofFunctor (Over.forget U))) he hid j a).2 rfl
  rcases ha with ⟨τ0⟩
  let τ : j ≅ e ≫ FibredInGroupoidsOver.overMap a := by
    simpa [FibredInGroupoidsMor.InducesHom] using τ0
  let Fm := FibredInGroupoidsOver.overMap f
  let Ja := e ≫ FibredInGroupoidsOver.overMap a
  let source := FibredInGroupoidsOver.twoFibreProduct Fm j
  let target : FibredInGroupoidsOver C := ofFunctor (Over.forget (Limits.pullback f a))
  haveI heTot : (FibredInGroupoidsMor.G e).IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase _ he
  let eSource : source.S ≌ (FibredInGroupoidsMor.G Fm) ⊡ (FibredInGroupoidsMor.G j) :=
    twoFibreProductEquivCatPullback Fm j
  let eLegs : (FibredInGroupoidsMor.G Fm) ⊡ (FibredInGroupoidsMor.G j) ≌
      (FibredInGroupoidsMor.G Fm) ⊡ (FibredInGroupoidsMor.G Ja) :=
    catPullbackCongrLegs (Iso.refl _) (ownerIsoToFunctorIso τ)
  let eRight : (FibredInGroupoidsMor.G Fm) ⊡ (FibredInGroupoidsMor.G Ja) ≌
      (Over.map f) ⊡ (Over.map a) := by
    change (Over.map f) ⊡ ((FibredInGroupoidsMor.G e) ⋙ Over.map a) ≌
      (Over.map f) ⊡ (Over.map a)
    exact catPullbackCongrRightDom (FibredInGroupoidsMor.G e).asEquivalence
      (Over.map f) (Over.map a)
  let q1 := π₁ (FibredInGroupoidsMor.G Fm) (FibredInGroupoidsMor.G j) ⋙ Over.forget W
  let q2 := π₁ (FibredInGroupoidsMor.G Fm) (FibredInGroupoidsMor.G Ja) ⋙ Over.forget W
  let q3 := π₁ (Over.map f) (Over.map a) ⋙ Over.forget W
  let q4 := Over.forget (Limits.pullback f a)
  have h1 : eSource.functor ⋙ q1 ≅ source.p := by
    simpa [eSource, source, Fm, q1] using
      (twoFibreProductEquivCatPullback_functor_baseIso_left Fm j)
  have h2 : eLegs.functor ⋙ q2 ≅ q1 := by
    simpa [eLegs, q1, q2] using
      (catPullbackCongrLegs_functor_fst_baseIso (Iso.refl _)
        (ownerIsoToFunctorIso τ) (Over.forget W))
  have h3 : eRight.functor ⋙ q3 ≅ q2 := by
    change eRight.functor ⋙ (π₁ (Over.map f) (Over.map a) ⋙ Over.forget W) ≅
      π₁ (FibredInGroupoidsMor.G Fm) (FibredInGroupoidsMor.G Ja) ⋙ Over.forget W
    simpa [eRight, Fm, Ja] using
      (catPullbackCongrRightDom_functor_fst_baseIso
        (FibredInGroupoidsMor.G e).asEquivalence (Over.map f) (Over.map a) (Over.forget W))
  have h4 : overMapPullbackToOverPullback f a ⋙ q4 ≅ q3 := by
    exact eqToIso (by simp [q3, q4])
  exact isRepresentable_of_total_equivalence_transportData
    (functorCompBaseIso4_transportData_explicit (P := source) (Q := target)
      eSource.functor eLegs.functor eRight.functor (overMapPullbackToOverPullback f a)
      (inferInstance : eSource.functor.IsEquivalence)
      (inferInstance : eLegs.functor.IsEquivalence)
      (inferInstance : eRight.functor.IsEquivalence)
      (overMapPullbackToOverPullback_isEquivalence f a)
      q3 q2 q1 h4 h3 h2 h1)
    (FibredInGroupoidsOver.over_forget_isRepresentable (Limits.pullback f a))

/-- Package a five-step chain of equivalence functors together with its composite compatibility with
base projections.  The concrete projection formulae supply the five `hᵢ`; this API performs only the
formal associator bookkeeping. -/
noncomputable def functorCompBaseIso5_transportData
    {P Q : FibredInGroupoidsOver C}
    {A₁ A₂ A₃ A₄ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    (F₁ : P.S ⥤ A₁) (F₂ : A₁ ⥤ A₂) (F₃ : A₂ ⥤ A₃) (F₄ : A₃ ⥤ A₄)
    (F₅ : A₄ ⥤ Q.S)
    [F₁.IsEquivalence] [F₂.IsEquivalence] [F₃.IsEquivalence] [F₄.IsEquivalence]
    [F₅.IsEquivalence]
    (q₄ : A₄ ⥤ C) (q₃ : A₃ ⥤ C) (q₂ : A₂ ⥤ C) (q₁ : A₁ ⥤ C)
    (h₅ : F₅ ⋙ Q.p ≅ q₄) (h₄ : F₄ ⋙ q₄ ≅ q₃) (h₃ : F₃ ⋙ q₃ ≅ q₂)
    (h₂ : F₂ ⋙ q₂ ≅ q₁) (h₁ : F₁ ⋙ q₁ ≅ P.p) :
    Σ' (e : P.S ⥤ Q.S), Σ' (_ : e.IsEquivalence), e ⋙ Q.p ≅ P.p := by
  let F := F₁ ⋙ (F₂ ⋙ (F₃ ⋙ (F₄ ⋙ F₅)))
  haveI : F.IsEquivalence := by
    dsimp [F]
    infer_instance
  exact ⟨F, inferInstance,
    functorCompBaseIso5 F₁ F₂ F₃ F₄ F₅ Q.p q₄ q₃ q₂ q₁ P.p h₅ h₄ h₃ h₂ h₁⟩

/-- Explicit-instance variant of `functorCompBaseIso5_transportData`. -/
noncomputable def functorCompBaseIso5_transportData_explicit
    {P Q : FibredInGroupoidsOver C}
    {A₁ A₂ A₃ A₄ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    (F₁ : P.S ⥤ A₁) (F₂ : A₁ ⥤ A₂) (F₃ : A₂ ⥤ A₃) (F₄ : A₃ ⥤ A₄)
    (F₅ : A₄ ⥤ Q.S)
    (hF₁ : F₁.IsEquivalence) (hF₂ : F₂.IsEquivalence)
    (hF₃ : F₃.IsEquivalence) (hF₄ : F₄.IsEquivalence) (hF₅ : F₅.IsEquivalence)
    (q₄ : A₄ ⥤ C) (q₃ : A₃ ⥤ C) (q₂ : A₂ ⥤ C) (q₁ : A₁ ⥤ C)
    (h₅ : F₅ ⋙ Q.p ≅ q₄) (h₄ : F₄ ⋙ q₄ ≅ q₃) (h₃ : F₃ ⋙ q₃ ≅ q₂)
    (h₂ : F₂ ⋙ q₂ ≅ q₁) (h₁ : F₁ ⋙ q₁ ≅ P.p) :
    Σ' (e : P.S ⥤ Q.S), Σ' (_ : e.IsEquivalence), e ⋙ Q.p ≅ P.p := by
  haveI : F₁.IsEquivalence := hF₁
  haveI : F₂.IsEquivalence := hF₂
  haveI : F₃.IsEquivalence := hF₃
  haveI : F₄.IsEquivalence := hF₄
  haveI : F₅.IsEquivalence := hF₅
  exact functorCompBaseIso5_transportData F₁ F₂ F₃ F₄ F₅ q₄ q₃ q₂ q₁ h₅ h₄ h₃ h₂ h₁

/-- Reassociation of a two-fibre product: pulling back the left projection
`A ×_T B -> A` along `K : A' -> A` is representability-equivalent to the direct pullback of
`K ≫ F` and `G`. -/
theorem twoFibreProduct_leftProjection_representable_transport
    {A' A B T : FibredInGroupoidsOver C}
    (K : A' ⟶ A) (F : A ⟶ T) (G : B ⟶ T) :
    (FibredInGroupoidsOver.twoFibreProduct K
      (FibredInGroupoidsOver.twoFibreProductLeftProjection F G)).IsRepresentable →
    (FibredInGroupoidsOver.twoFibreProduct (K ≫ F) G).IsRepresentable := by
  intro hRep
  let leftProj := FibredInGroupoidsOver.twoFibreProductLeftProjection F G
  let source := FibredInGroupoidsOver.twoFibreProduct (K ≫ F) G
  let target := FibredInGroupoidsOver.twoFibreProduct K leftProj
  let eSource := twoFibreProductEquivCatPullback (K ≫ F) G
  let eInner := twoFibreProductEquivCatPullback F G
  let eKnown := twoFibreProductEquivCatPullback K leftProj
  let FAssoc := catPullbackAssocLeftProjectionInverse
    (FibredInGroupoidsMor.G K) (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G)
  let eRight : (FibredInGroupoidsMor.G K) ⊡
        ((twoFibreProductEquivCatPullback F G).functor ⋙
          (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G))) ≌
      (FibredInGroupoidsMor.G K) ⊡
        (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G)) :=
    catPullbackCongrRightDom eInner (FibredInGroupoidsMor.G K)
      (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G))
  let eLegs : (FibredInGroupoidsMor.G K) ⊡ (FibredInGroupoidsMor.G leftProj) ≌
      (FibredInGroupoidsMor.G K) ⊡
        ((twoFibreProductEquivCatPullback F G).functor ⋙
          (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G))) :=
    catPullbackCongrLegs (Iso.refl _) (twoFibreProductEquivCatPullback_functor_fstIso F G).symm
  let q₄ := π₁ (FibredInGroupoidsMor.G K) (FibredInGroupoidsMor.G leftProj) ⋙ A'.p
  let q₃ := π₁ (FibredInGroupoidsMor.G K)
      ((twoFibreProductEquivCatPullback F G).functor ⋙
        π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G)) ⋙ A'.p
  let q₂ := π₁ (FibredInGroupoidsMor.G K)
      (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G)) ⋙ A'.p
  let q₁ := π₁ ((FibredInGroupoidsMor.G K) ⋙ (FibredInGroupoidsMor.G F))
      (FibredInGroupoidsMor.G G) ⋙ A'.p
  have h₅ : eKnown.inverse ⋙ target.p ≅ q₄ := by
    change (twoFibreProductEquivCatPullback K leftProj).inverse ⋙
        (FibredInGroupoidsOver.twoFibreProduct K leftProj).p ≅
      π₁ (FibredInGroupoidsMor.G K) (FibredInGroupoidsMor.G leftProj) ⋙ A'.p
    exact twoFibreProductEquivCatPullback_inverse_baseIso_left K leftProj
  have h₄ : eLegs.inverse ⋙ q₄ ≅ q₃ :=
    catPullbackCongrLegs_inverse_fst_baseIso (Iso.refl _)
      (twoFibreProductEquivCatPullback_functor_fstIso F G).symm A'.p
  have h₃ : eRight.inverse ⋙ q₃ ≅ q₂ := by
    simpa [eRight, q₃, q₂] using
      (catPullbackCongrRightDom_inverse_fst_baseIso eInner (FibredInGroupoidsMor.G K)
        (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G)) A'.p)
  have h₂ : FAssoc ⋙ q₂ ≅ q₁ := by
    simpa [FAssoc, q₂, q₁] using
      (catPullbackAssocLeftProjection_inverse_fst_baseIso
        (FibredInGroupoidsMor.G K) (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) A'.p)
  have h₁ : eSource.functor ⋙ q₁ ≅ source.p := by
    simpa [eSource, source, q₁] using
      (twoFibreProductEquivCatPullback_functor_baseIso_left (K ≫ F) G)
  exact isRepresentable_of_total_equivalence_transportData
    (functorCompBaseIso5_transportData_explicit (P := source) (Q := target)
      eSource.functor (catPullbackAssocLeftProjectionInverse
        (FibredInGroupoidsMor.G K) (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G))
      eRight.inverse eLegs.inverse eKnown.inverse
      (inferInstance : eSource.functor.IsEquivalence)
      (catPullbackAssocLeftProjectionInverse_isEquivalence
        (FibredInGroupoidsMor.G K) (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G))
      (inferInstance : eRight.inverse.IsEquivalence)
      (inferInstance : eLegs.inverse.IsEquivalence)
      (inferInstance : eKnown.inverse.IsEquivalence)
      q₄ q₃ q₂ q₁ h₅ h₄ h₃ h₂ h₁) hRep

/-- Representability of a two-fibre product is invariant under replacing both legs by isomorphic
legs. -/
theorem twoFibreProduct_representable_transport_iso
    {A B T : FibredInGroupoidsOver C}
    {F F' : A ⟶ T} {G G' : B ⟶ T}
    (α : F ≅ F') (β : G ≅ G') :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct F' G').IsRepresentable := by
  intro hRep
  let source := FibredInGroupoidsOver.twoFibreProduct F' G'
  let target := FibredInGroupoidsOver.twoFibreProduct F G
  let eSource := twoFibreProductEquivCatPullback F' G'
  let eLegs := catPullbackCongrLegs (ownerIsoToFunctorIso α) (ownerIsoToFunctorIso β)
  let eTarget := twoFibreProductEquivCatPullback F G
  let q₂ := π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ⋙ A.p
  let q₁ := π₁ (FibredInGroupoidsMor.G F') (FibredInGroupoidsMor.G G') ⋙ A.p
  have h₃ : eTarget.inverse ⋙ target.p ≅ q₂ := by
    simpa [eTarget, target, q₂] using
      (twoFibreProductEquivCatPullback_inverse_baseIso_left F G)
  have h₂ : eLegs.inverse ⋙ q₂ ≅ q₁ := by
    simpa [eLegs, q₁, q₂] using
      (catPullbackCongrLegs_inverse_fst_baseIso
        (ownerIsoToFunctorIso α) (ownerIsoToFunctorIso β) A.p)
  have h₁ : eSource.functor ⋙ q₁ ≅ source.p := by
    simpa [eSource, source, q₁] using
      (twoFibreProductEquivCatPullback_functor_baseIso_left F' G')
  let E := eSource.functor ⋙ (eLegs.inverse ⋙ eTarget.inverse)
  haveI : E.IsEquivalence := by
    dsimp [E]
    infer_instance
  have h₂₃ : (eLegs.inverse ⋙ eTarget.inverse) ⋙ target.p ≅ q₁ :=
    functorCompBaseIso eLegs.inverse eTarget.inverse target.p q₂ q₁ h₃ h₂
  have h₁₂₃ : E ⋙ target.p ≅ source.p :=
    functorCompBaseIso eSource.functor (eLegs.inverse ⋙ eTarget.inverse)
      target.p q₁ source.p h₂₃ h₁
  exact isRepresentable_of_total_equivalence_transportData
    ⟨E, inferInstance, h₁₂₃⟩ hRep

/-- Representability of a two-fibre product is invariant under replacing both legs by morphisms
whose underlying total-category functors are isomorphic. -/
theorem twoFibreProduct_representable_transport_functor_iso
    {A B T : FibredInGroupoidsOver C}
    {F F' : A ⟶ T} {G G' : B ⟶ T}
    (α : FibredInGroupoidsMor.G F ≅ FibredInGroupoidsMor.G F')
    (β : FibredInGroupoidsMor.G G ≅ FibredInGroupoidsMor.G G') :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct F' G').IsRepresentable := by
  intro hRep
  let source := FibredInGroupoidsOver.twoFibreProduct F' G'
  let target := FibredInGroupoidsOver.twoFibreProduct F G
  let eSource := twoFibreProductEquivCatPullback F' G'
  let eLegs := catPullbackCongrLegs α β
  let eTarget := twoFibreProductEquivCatPullback F G
  let q₂ := π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ⋙ A.p
  let q₁ := π₁ (FibredInGroupoidsMor.G F') (FibredInGroupoidsMor.G G') ⋙ A.p
  have h₃ : eTarget.inverse ⋙ target.p ≅ q₂ := by
    simpa [eTarget, target, q₂] using
      (twoFibreProductEquivCatPullback_inverse_baseIso_left F G)
  have h₂ : eLegs.inverse ⋙ q₂ ≅ q₁ := by
    simpa [eLegs, q₁, q₂] using
      (catPullbackCongrLegs_inverse_fst_baseIso α β A.p)
  have h₁ : eSource.functor ⋙ q₁ ≅ source.p := by
    simpa [eSource, source, q₁] using
      (twoFibreProductEquivCatPullback_functor_baseIso_left F' G')
  let E := eSource.functor ⋙ (eLegs.inverse ⋙ eTarget.inverse)
  haveI : E.IsEquivalence := by
    dsimp [E]
    infer_instance
  have h₂₃ : (eLegs.inverse ⋙ eTarget.inverse) ⋙ target.p ≅ q₁ :=
    functorCompBaseIso eLegs.inverse eTarget.inverse target.p q₂ q₁ h₃ h₂
  have h₁₂₃ : E ⋙ target.p ≅ source.p :=
    functorCompBaseIso eSource.functor (eLegs.inverse ⋙ eTarget.inverse)
      target.p q₁ source.p h₂₃ h₁
  exact isRepresentable_of_total_equivalence_transportData
    ⟨E, inferInstance, h₁₂₃⟩ hRep

/-- Representability of a two-fibre product is invariant under replacing both legs by morphisms
whose underlying total-category functors become isomorphic after postcomposing with an equivalence
of the common target. -/
opaque twoFibreProduct_representable_transport_postcompose_functor_iso
    {A B T : FibredInGroupoidsOver C} {E : Type*} [Category E]
    {F F' : A ⟶ T} {G G' : B ⟶ T}
    (eT : T.S ≌ E)
    (α : FibredInGroupoidsMor.G F ⋙ eT.functor ≅
      FibredInGroupoidsMor.G F' ⋙ eT.functor)
    (β : FibredInGroupoidsMor.G G ⋙ eT.functor ≅
      FibredInGroupoidsMor.G G' ⋙ eT.functor) :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct F' G').IsRepresentable := by
  intro hRep
  let source := FibredInGroupoidsOver.twoFibreProduct F' G'
  let target := FibredInGroupoidsOver.twoFibreProduct F G
  let eSource := twoFibreProductEquivCatPullback F' G'
  let eBaseSource := catPullbackCongrBase
    (FibredInGroupoidsMor.G F') (FibredInGroupoidsMor.G G') eT
  let eLegs := catPullbackCongrLegs α β
  let eBaseTarget := catPullbackCongrBase
    (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) eT
  let eTarget := twoFibreProductEquivCatPullback F G
  let q₄ := π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ⋙ A.p
  let q₃ := π₁ (FibredInGroupoidsMor.G F ⋙ eT.functor)
      (FibredInGroupoidsMor.G G ⋙ eT.functor) ⋙ A.p
  let q₂ := π₁ (FibredInGroupoidsMor.G F' ⋙ eT.functor)
      (FibredInGroupoidsMor.G G' ⋙ eT.functor) ⋙ A.p
  let q₁ := π₁ (FibredInGroupoidsMor.G F') (FibredInGroupoidsMor.G G') ⋙ A.p
  have h₅ : eTarget.inverse ⋙ target.p ≅ q₄ := by
    simpa [eTarget, target, q₄] using
      (twoFibreProductEquivCatPullback_inverse_baseIso_left F G)
  have h₄ : eBaseTarget.inverse ⋙ q₄ ≅ q₃ := by
    simpa [eBaseTarget, q₄, q₃] using
      (catPullbackCongrBase_inverse_fst_baseIso
        (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) eT A.p)
  have h₃ : eLegs.inverse ⋙ q₃ ≅ q₂ := by
    simpa [eLegs, q₃, q₂] using
      (catPullbackCongrLegs_inverse_fst_baseIso α β A.p)
  have h₂ : eBaseSource.functor ⋙ q₂ ≅ q₁ := by
    simpa [eBaseSource, q₂, q₁] using
      (catPullbackCongrBase_functor_fst_baseIso
        (FibredInGroupoidsMor.G F') (FibredInGroupoidsMor.G G') eT A.p)
  have h₁ : eSource.functor ⋙ q₁ ≅ source.p := by
    simpa [eSource, source, q₁] using
      (twoFibreProductEquivCatPullback_functor_baseIso_left F' G')
  exact isRepresentable_of_total_equivalence_transportData
    (functorCompBaseIso5_transportData_explicit (P := source) (Q := target)
      eSource.functor eBaseSource.functor eLegs.inverse eBaseTarget.inverse eTarget.inverse
      (inferInstance : eSource.functor.IsEquivalence)
      (inferInstance : eBaseSource.functor.IsEquivalence)
      (inferInstance : eLegs.inverse.IsEquivalence)
      (inferInstance : eBaseTarget.inverse.IsEquivalence)
      (inferInstance : eTarget.inverse.IsEquivalence)
      q₄ q₃ q₂ q₁ h₅ h₄ h₃ h₂ h₁) hRep

/-- Variant of `twoFibreProduct_representable_transport_postcompose_functor_iso` where the two
left-leg comparisons are supplied as isomorphisms to a common postcomposed target. -/
opaque twoFibreProduct_representable_transport_postcompose_common_left
    {A B T : FibredInGroupoidsOver C} {E : Type*} [Category E]
    {F F' : A ⟶ T} {G G' : B ⟶ T}
    (eT : T.S ≌ E) {Q : A.S ⥤ E}
    (α : FibredInGroupoidsMor.G F ⋙ eT.functor ≅ Q)
    (α' : FibredInGroupoidsMor.G F' ⋙ eT.functor ≅ Q)
    (β : FibredInGroupoidsMor.G G ⋙ eT.functor ≅
      FibredInGroupoidsMor.G G' ⋙ eT.functor) :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct F' G').IsRepresentable :=
  twoFibreProduct_representable_transport_postcompose_functor_iso eT (α ≪≫ α'.symm) β

/-! ### Small slice-map comparison isomorphisms -/

/-- Composition of the canonical slice maps `Over.map` is naturally isomorphic to the slice map of
the composite. -/
noncomputable def overMapCompFunctorIso {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    Over.map f ⋙ Over.map g ≅ Over.map (f ≫ g) := by
  refine NatIso.ofComponents (fun a => ?_) ?_
  · refine Over.isoMk (Iso.refl a.left) ?_
    simp [Category.assoc]
  · intro a b h
    apply Over.OverMorphism.ext
    simp

/-- The canonical slice map attached to an identity is naturally isomorphic to the identity
functor. -/
noncomputable def overMapIdFunctorIso {U : C} :
    Over.map (𝟙 U) ≅ 𝟭 (Over U) := by
  refine NatIso.ofComponents (fun a => ?_) ?_
  · refine Over.isoMk (Iso.refl a.left) ?_
    simp
  · intro a b h
    apply Over.OverMorphism.ext
    simp

/-- Owner-level form of `overMapCompFunctorIso`. -/
noncomputable def overMapCompIso {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    (FibredInGroupoidsOver.overMap f ≫ FibredInGroupoidsOver.overMap g) ≅
      FibredInGroupoidsOver.overMap (f ≫ g) := by
  refine FibredInGroupoidsMor.ownerIsoOfBasedFunctorIso ?_
  refine BasedNatIso.mkNatIso (overMapCompFunctorIso f g) ?_
  intro a
  refine IsHomLift.of_fac' (Over.forget W) (𝟙 a.left)
    ((overMapCompFunctorIso f g).hom.app a) ?_ ?_ ?_
  · rfl
  · rfl
  · simp [overMapCompFunctorIso]

/-- Owner-level form of `overMapIdFunctorIso`. -/
noncomputable def overMapIdIso {U : C} :
    FibredInGroupoidsOver.overMap (𝟙 U) ≅
      (𝟙 (ofFunctor (Over.forget U)) : ofFunctor (Over.forget U) ⟶
        ofFunctor (Over.forget U)) := by
  refine FibredInGroupoidsMor.ownerIsoOfBasedFunctorIso ?_
  refine BasedNatIso.mkNatIso overMapIdFunctorIso ?_
  intro a
  refine IsHomLift.of_fac' (Over.forget U) (𝟙 a.left)
    (overMapIdFunctorIso.hom.app a) ?_ ?_ ?_
  · rfl
  · rfl
  · simp [overMapIdFunctorIso]

/-- Pulling a slice morphism back along the diagonal `W ⟶ W × W` and then along the first
projection recovers the original slice morphism, up to the canonical owner isomorphism. -/
noncomputable def diagonalOverMapFstIso [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (L : ofFunctor (Over.forget W) ⟶ X) :
    (FibredInGroupoidsOver.overMap (Limits.prod.lift (𝟙 W) (𝟙 W) : W ⟶ Limits.prod W W) ≫
      slice_morphism_pullback X (Limits.prod.fst : Limits.prod W W ⟶ W) L) ≅ L := by
  let δ : W ⟶ Limits.prod W W := Limits.prod.lift (𝟙 W) (𝟙 W)
  let ecomp := overMapCompIso δ (Limits.prod.fst : Limits.prod W W ⟶ W)
  let eproj : FibredInGroupoidsOver.overMap (δ ≫ Limits.prod.fst) ≅
      (𝟙 (ofFunctor (Over.forget W)) : ofFunctor (Over.forget W) ⟶
        ofFunctor (Over.forget W)) :=
    eqToIso (by rw [Limits.prod.lift_fst]) ≪≫ overMapIdIso
  exact (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso ecomp L ≪≫
    Bicategory.whiskerRightIso eproj L ≪≫ Bicategory.leftUnitor L

/-- Pulling a slice morphism back along the diagonal `W ⟶ W × W` and then along the second
projection recovers the original slice morphism, up to the canonical owner isomorphism. -/
noncomputable def diagonalOverMapSndIso [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (R : ofFunctor (Over.forget W) ⟶ X) :
    (FibredInGroupoidsOver.overMap (Limits.prod.lift (𝟙 W) (𝟙 W) : W ⟶ Limits.prod W W) ≫
      slice_morphism_pullback X (Limits.prod.snd : Limits.prod W W ⟶ W) R) ≅ R := by
  let δ : W ⟶ Limits.prod W W := Limits.prod.lift (𝟙 W) (𝟙 W)
  let ecomp := overMapCompIso δ (Limits.prod.snd : Limits.prod W W ⟶ W)
  let eproj : FibredInGroupoidsOver.overMap (δ ≫ Limits.prod.snd) ≅
      (𝟙 (ofFunctor (Over.forget W)) : ofFunctor (Over.forget W) ⟶
        ofFunctor (Over.forget W)) :=
    eqToIso (by rw [Limits.prod.lift_snd]) ≪≫ overMapIdIso
  exact (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso ecomp R ≪≫
    Bicategory.whiskerRightIso eproj R ≪≫ Bicategory.leftUnitor R

/-- A `2`-isomorphism between morphisms of `2`-commutative squares induces a `2`-isomorphism
between their apex maps. -/
noncomputable def apexIsoOfSquareHomIso
    {B : Type*} [Bicategory B]
    {x y z : B} {f : x ⟶ z} {g : y ⟶ z}
    {P Q : BicategoricalTwoCommutativeSquare f g}
    {u v : P ⟶ Q} (e : u ≅ v) : u.hom ≅ v.hom where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := by
    exact congrArg BicategoricalTwoCommutativeSquare.TwoHom.hom e.hom_inv_id
  inv_hom_id := by
    exact congrArg BicategoricalTwoCommutativeSquare.TwoHom.hom e.inv_hom_id

/-- Any two parallel `2`-morphisms into the identity fibration `C -> C` are equal.  Components
lie over identity arrows for the identity functor, hence are themselves the same identity after
the harmless equality transports. -/
theorem twoCell_to_identity_unique
    {A : FibredInGroupoidsOver C}
    {F G : A ⟶ ofFunctor (𝟭 C)} (α β : F ⟶ G) : α = β := by
  repeat first | apply WideSubcategory.hom_ext | apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  change α.hom.hom.hom.hom.app a = β.hom.hom.hom.hom.app a
  let φ := α.hom.hom.hom.hom.app a
  let ψ := β.hom.hom.hom.hom.app a
  have hφ : (𝟭 C).map φ =
      eqToHom (IsHomLift.domain_eq (ofFunctor (𝟭 C)).toBasedCategory.p
          (𝟙 (A.p.obj a)) φ) ≫
        𝟙 (A.p.obj a) ≫
        eqToHom (IsHomLift.codomain_eq (ofFunctor (𝟭 C)).toBasedCategory.p
          (𝟙 (A.p.obj a)) φ).symm :=
    IsHomLift.fac' (ofFunctor (𝟭 C)).toBasedCategory.p (𝟙 (A.p.obj a)) φ
  have hψ : (𝟭 C).map ψ =
      eqToHom (IsHomLift.domain_eq (ofFunctor (𝟭 C)).toBasedCategory.p
          (𝟙 (A.p.obj a)) ψ) ≫
        𝟙 (A.p.obj a) ≫
        eqToHom (IsHomLift.codomain_eq (ofFunctor (𝟭 C)).toBasedCategory.p
          (𝟙 (A.p.obj a)) ψ).symm :=
    IsHomLift.fac' (ofFunctor (𝟭 C)).toBasedCategory.p (𝟙 (A.p.obj a)) ψ
  change φ = ψ
  rw [← Functor.id_map (C := C) φ, hφ]
  rw [← Functor.id_map (C := C) ψ, hψ]

section SquareHomCommUnique

open scoped Bicategory

/-- Any candidate morphism between squares over `X -> C` satisfies the square-compatibility
condition automatically: both sides are parallel `2`-cells into the identity fibration. -/
theorem square_hom_comm_unique_to_identity
    (X : FibredInGroupoidsOver C)
    {P Q : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    (hom : P.obj ⟶ Q.obj)
    (left : hom ≫ Q.p ⟶ P.p)
    (right : hom ≫ Q.q ⟶ P.q) :
    (left ▷ X.baseProjection) ≫ P.ψ.hom =
      (α_ hom Q.p X.baseProjection).hom ≫ hom ◁ Q.ψ.hom ≫
        (α_ hom Q.q X.baseProjection).inv ≫ (right ▷ X.baseProjection) := by
  exact twoCell_to_identity_unique _ _

end SquareHomCommUnique

/-- Build a morphism of squares over `X -> C` from its apex map and two leg comparison cells.
The compatibility condition is automatic because both sides are parallel `2`-cells into the
identity fibration.  This direct constructor is intentionally separate from
`square_hom_comm_unique_to_identity`: applying that theorem through a structure field can force a
large dependent-conversion check in the diagonal comparison. -/
noncomputable def squareHomMkToIdentity
    (X : FibredInGroupoidsOver C)
    {P Q : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    (hom : P.obj ⟶ Q.obj)
    (left : hom ≫ Q.p ⟶ P.p)
    (right : hom ≫ Q.q ⟶ P.q) :
    P ⟶ Q where
  hom := hom
  left := left
  right := right
  comm := by
    exact twoCell_to_identity_unique _ _

/-! ### The diagonal comparison equivalence (Lemma 4.31.13, bundled as an equivalence) -/

/-- The canonical comparison from `A ×[C] B` to the diagonal base change is an equivalence
(Lemma 4.31.13). -/
theorem diagComparison_isEquiv {A B D : Type (max u v)} [Category.{v} A] [Category.{v} B]
    [Category.{v} D] (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (Limits.two_fibre_product_diagonal_comparison F G H).IsEquivalence := by
  let G' := Limits.twoFibreProductDiagonalInverse F G H
  let η := Limits.twoFibreProductDiagonalUnitIso F G H
  let ε := Limits.twoFibreProductDiagonalCounitIso F G H
  exact Functor.IsEquivalence.mk' G' η ε

/-- Instance form of Lemma 4.31.13.  The proof is deliberately duplicated from
`diagComparison_isEquiv` rather than reusing that theorem: applying the theorem as an instance
forces a large definitional-equality check in later products-of-slices comparisons. -/
instance diagComparison_isEquiv_inst {A B D : Type (max u v)} [Category.{v} A] [Category.{v} B]
    [Category.{v} D] (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (Limits.two_fibre_product_diagonal_comparison F G H).IsEquivalence := by
  let G' := Limits.twoFibreProductDiagonalInverse F G H
  let η := Limits.twoFibreProductDiagonalUnitIso F G H
  let ε := Limits.twoFibreProductDiagonalCounitIso F G H
  exact Functor.IsEquivalence.mk' G' η ε

/-! ### The "forget a `2`-cell to a natural transformation" strict `2`-functor -/

/-- The underlying-natural-transformation functor on each hom-category of
`FibredInGroupoidsOver C`: forget through the two sub-`2`-category inclusions and the
based-natural-transformation forgetful functor.  This is the strict `2`-functor underlying
`ownerIsoToFunctorIso`. -/
noncomputable def ownerTwoCellFunctor (A B : FibredInGroupoidsOver C) :
    (A ⟶ B) ⥤ (A.S ⥤ B.S) :=
  ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
    ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
      B.toFibredCategoryOver).inclusion ⋙
    BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory

/-- `ownerIsoToFunctorIso` is the action of `ownerTwoCellFunctor` on isomorphisms. -/
theorem ownerIsoToFunctorIso_hom {X Y : FibredInGroupoidsOver C} {f g : X ⟶ Y} (α : f ≅ g) :
    (ownerIsoToFunctorIso α).hom = (ownerTwoCellFunctor X Y).map α.hom := rfl

/-- The underlying functor of the identity `2`-cell is the identity natural transformation. -/
theorem ownerIsoToFunctorIso_refl {X Y : FibredInGroupoidsOver C} (f : X ⟶ Y) :
    ownerIsoToFunctorIso (Iso.refl f) = Iso.refl (FibredInGroupoidsMor.G f) := by
  apply Iso.ext
  rw [ownerIsoToFunctorIso_hom]
  exact (ownerTwoCellFunctor X Y).map_id f

/-- `ownerIsoToFunctorIso` sends equality isomorphisms of owner morphisms to equality
isomorphisms of underlying functors. -/
theorem ownerIsoToFunctorIso_eqToIso {X Y : FibredInGroupoidsOver C} {f g : X ⟶ Y}
    (h : f = g) :
    ownerIsoToFunctorIso (eqToIso h) =
      eqToIso (congrArg FibredInGroupoidsMor.G h) := by
  cases h
  simpa using ownerIsoToFunctorIso_refl f

/-- Component formula for the natural transformation induced by an equality of functors. -/
@[simp] theorem eqToHom_functor_app {A : Type*} {B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (h : F = G) (a : A) :
    (eqToHom h : F ⟶ G).app a = eqToHom (congrFun (congrArg Functor.obj h) a) := by
  cases h
  rfl

/-- Morphisms `eqToHom h` are independent of the particular equality proof `h`. -/
theorem eqToHom_eq_of_proof_irrel {D : Type*} [Category D] {X Y : D} (h h' : X = Y) :
    eqToHom h = eqToHom h' := by
  cases h
  simp

/-- Composites of equality morphisms are independent of the particular equality proofs. -/
theorem eqToHom_comp_eq_of_proof_irrel {D : Type*} [Category D] {X Y Z : D}
    (h1 h1' : X = Y) (h2 h2' : Y = Z) :
    eqToHom h1 ≫ eqToHom h2 = eqToHom h1' ≫ eqToHom h2' := by
  cases h1
  cases h2
  simp

/-- The explicit categorical-pullback functor is definitionally the `functorEquiv`-inverse image of
the corresponding `CatCommSqOver`. -/
theorem mkCatPullbackFunctor_eq_functorEquiv_inverse {A₀ B₀ D₀ Z : Type*} [Category A₀]
    [Category B₀] [Category D₀] [Category Z]
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (L : Z ⥤ A₀) (R : Z ⥤ B₀) (e : L ⋙ F ≅ R ⋙ G) :
    mkCatPullbackFunctor F G L R e =
      (CategoricalPullback.functorEquiv F G Z).inverse.obj { fst := L, snd := R, iso := e } :=
  rfl

/-- The explicit categorical-pullback target associated to two chosen components of a map into
`X ×_C X`.  Naming this target keeps downstream comparison lemmas from repeatedly normalizing the
large `mkCatPullbackFunctor` expression. -/
noncomputable def actualTwoFibreProductMapComparisonTarget
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (L R : A ⟶ X)
    (ψ : L ≫ X.baseProjection ≅ R ≫ X.baseProjection) :
    A.S ⥤ (FibredInGroupoidsMor.G X.baseProjection) ⊡
      (FibredInGroupoidsMor.G X.baseProjection) :=
  mkCatPullbackFunctor (FibredInGroupoidsMor.G X.baseProjection)
    (FibredInGroupoidsMor.G X.baseProjection)
    (FibredInGroupoidsMor.G L) (FibredInGroupoidsMor.G R)
    (ownerIsoToFunctorIso ψ)

/-- Direct comparison for an actual map into the canonical explicit two-fibre product, with the
two projection comparison cells supplied separately.  Unlike `squareComparisonIsoOfLegs`, the
target is named by `actualTwoFibreProductMapComparisonTarget` and the square compatibility is
discharged by uniqueness of `2`-cells into the identity fibration. -/
noncomputable opaque actualTwoFibreProductMapComparisonIso
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (M : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (L R : A ⟶ X)
    (ψ : L ≫ X.baseProjection ≅ R ≫ X.baseProjection)
    (left : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).p ⟶ L)
    (right : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).q ⟶ R) :
    FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      actualTwoFibreProductMapComparisonTarget X L R ψ := by
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso left := fibredInGroupoidsMor_twoCell_isIso left
  haveI : IsIso right := fibredInGroupoidsMor_twoCell_isIso right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅
      FibredInGroupoidsMor.G L :=
      ownerIsoToFunctorIso (asIso left)
  let e2 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅
      FibredInGroupoidsMor.G R :=
    ownerIsoToFunctorIso (asIso right)
  exact CategoricalPullback.mkNatIso e1 e2 (by
    ext z
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp, NatTrans.comp_app]
    dsimp [actualTwoFibreProductMapComparisonTarget, mkCatPullbackFunctor]
    change Xp.map (e1.hom.app z) ≫ (ownerIsoToFunctorIso ψ).hom.app z =
      (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M).obj z) ≫
        Xp.map (e2.hom.app z)
    let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
      ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
        ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
          B.toFibredCategoryOver).inclusion ⋙
        BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
    let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
        (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
      fun {A B f g} t => (Ψ A B).map t
    have hWR : Φ (Bicategory.whiskerRight left X.baseProjection)
        = Functor.whiskerRight (Φ left) Xp := rfl
    have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
        (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
      fun {A B _ _ _} s t => (Ψ A B).map_comp s t
    have hΦψ : (ownerIsoToFunctorIso ψ).hom = Φ ψ.hom := rfl
    have hΦDT : (ownerIsoToFunctorIso DTsq.ψ).hom = Φ DTsq.ψ.hom := rfl
    have hΦe1 : e1.hom = Φ left := rfl
    have hΦe2 : e2.hom = Φ right := rfl
    have hc2 : Bicategory.whiskerRight left X.baseProjection ≫ ψ.hom =
        Bicategory.whiskerLeft M DTsq.ψ.hom ≫
          Bicategory.whiskerRight right X.baseProjection := by
      exact twoCell_to_identity_unique _ _
    have hcomm := congrArg Φ hc2
    simp only [hΦcomp, hWR] at hcomm
    have hx := congrArg
      (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
    rw [hΦψ, hΦDT, hΦe1, hΦe2]
    exact hx)

/-- Two maps into the canonical `X ×_C X` are identified after the Remark-4.35.8 comparison as
soon as their two projections are identified.  This is the comparison API used by downstream
representability transports; it avoids exposing the auxiliary explicit pullback target. -/
noncomputable opaque actualTwoFibreProductMapsComparisonIso
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (M M' : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (left : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).p ≅
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).p)
    (right : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).q ≅
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).q) :
    FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G M' ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor := by
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso left
  let e2 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso right
  exact CategoricalPullback.mkNatIso e1 e2 (by
    ext z
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp, NatTrans.comp_app]
    change Xp.map (e1.hom.app z) ≫
        (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M').obj z) =
      (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M).obj z) ≫
        Xp.map (e2.hom.app z)
    let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
      ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
        ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
          B.toFibredCategoryOver).inclusion ⋙
        BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
    let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
        (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
      fun {A B f g} t => (Ψ A B).map t
    have hWR_left : Φ (Bicategory.whiskerRight left.hom X.baseProjection)
        = Functor.whiskerRight (Φ left.hom) Xp := rfl
    have hWR_right : Φ (Bicategory.whiskerRight right.hom X.baseProjection)
        = Functor.whiskerRight (Φ right.hom) Xp := rfl
    have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
        (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
      fun {A B _ _ _} s t => (Ψ A B).map_comp s t
    have hΦDT : (ownerIsoToFunctorIso DTsq.ψ).hom = Φ DTsq.ψ.hom := rfl
    have hΦe1 : e1.hom = Φ left.hom := rfl
    have hΦe2 : e2.hom = Φ right.hom := rfl
    have hc2 : Bicategory.whiskerRight left.hom X.baseProjection ≫
        Bicategory.whiskerLeft M' DTsq.ψ.hom =
      Bicategory.whiskerLeft M DTsq.ψ.hom ≫
        Bicategory.whiskerRight right.hom X.baseProjection := by
      exact twoCell_to_identity_unique _ _
    have hcomm := congrArg Φ hc2
    simp only [hΦcomp, hWR_left] at hcomm
    have hx := congrArg
      (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
    rw [hΦDT, hΦe1, hΦe2]
    exact hx)

/-- Two-cell version of `actualTwoFibreProductMapsComparisonIso`: two maps into the canonical
`X ×_C X` are identified after the Remark-4.35.8 comparison as soon as their two projections are
connected by `2`-cells.  The cells are automatically isomorphisms because the target is fibred in
groupoids. -/
noncomputable opaque actualTwoFibreProductMapsComparisonIsoOfTwoCells
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (M M' : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (left : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).p ⟶
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).p)
    (right : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).q ⟶
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).q) :
    FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G M' ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor := by
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso left := fibredInGroupoidsMor_twoCell_isIso left
  haveI : IsIso right := fibredInGroupoidsMor_twoCell_isIso right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso (asIso left)
  let e2 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso (asIso right)
  exact CategoricalPullback.mkNatIso e1 e2 (by
    ext z
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp, NatTrans.comp_app]
    change Xp.map (e1.hom.app z) ≫
        (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M').obj z) =
      (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M).obj z) ≫
        Xp.map (e2.hom.app z)
    let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
      ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
        ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
          B.toFibredCategoryOver).inclusion ⋙
        BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
    let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
        (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
      fun {A B f g} t => (Ψ A B).map t
    have hWR_left : Φ (Bicategory.whiskerRight left X.baseProjection)
        = Functor.whiskerRight (Φ left) Xp := rfl
    have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
        (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
      fun {A B _ _ _} s t => (Ψ A B).map_comp s t
    have hΦDT : (ownerIsoToFunctorIso DTsq.ψ).hom = Φ DTsq.ψ.hom := rfl
    have hΦe1 : e1.hom = Φ left := rfl
    have hΦe2 : e2.hom = Φ right := rfl
    have hc2 : Bicategory.whiskerRight left X.baseProjection ≫
        Bicategory.whiskerLeft M' DTsq.ψ.hom =
      Bicategory.whiskerLeft M DTsq.ψ.hom ≫
        Bicategory.whiskerRight right X.baseProjection := by
      exact twoCell_to_identity_unique _ _
    have hcomm := congrArg Φ hc2
    simp only [hΦcomp, hWR_left] at hcomm
    have hx := congrArg
      (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
    rw [hΦDT, hΦe1, hΦe2]
    exact hx)

/-- Representability transport when the left maps become isomorphic after postcomposition with the
canonical Remark-4.35.8 comparison and the right map is unchanged. -/
opaque twoFibreProduct_representable_transport_postcompose_left
    {A B T : FibredInGroupoidsOver C} {E : Type*} [Category E]
    {F F' : A ⟶ T} {G : B ⟶ T}
    (eT : T.S ≌ E)
    (α : FibredInGroupoidsMor.G F ⋙ eT.functor ≅
      FibredInGroupoidsMor.G F' ⋙ eT.functor) :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct F' G).IsRepresentable :=
  twoFibreProduct_representable_transport_postcompose_functor_iso eT α (Iso.refl _)

/-- Projection-cell comparison for two maps into the canonical self two-fibre product, stated only
as the postcomposed functor isomorphism needed by representability transport. -/
noncomputable opaque twoFibreProduct_postcomposeAlpha_of_projection_cells
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (M H : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (left : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).p ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).p)
    (right : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).q ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).q) :
    FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G H ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor := by
  let T := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso left := fibredInGroupoidsMor_twoCell_isIso left
  haveI : IsIso right := fibredInGroupoidsMor_twoCell_isIso right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅
      (FibredInGroupoidsMor.G H ⋙ eDT.functor) ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso (asIso left)
  let e2 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅
      (FibredInGroupoidsMor.G H ⋙ eDT.functor) ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso (asIso right)
  exact CategoricalPullback.mkNatIso e1 e2 (by
    ext z
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp, NatTrans.comp_app]
    change Xp.map (e1.hom.app z) ≫
        (ownerIsoToFunctorIso T.ψ).hom.app ((FibredInGroupoidsMor.G H).obj z) =
      (ownerIsoToFunctorIso T.ψ).hom.app ((FibredInGroupoidsMor.G M).obj z) ≫
        Xp.map (e2.hom.app z)
    let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
      ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
        ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
          B.toFibredCategoryOver).inclusion ⋙
        BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
    let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
        (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
      fun {A B f g} t => (Ψ A B).map t
    have hWR_left : Φ (Bicategory.whiskerRight left X.baseProjection)
        = Functor.whiskerRight (Φ left) Xp := rfl
    have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
        (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
      fun {A B _ _ _} s t => (Ψ A B).map_comp s t
    have hΦT : (ownerIsoToFunctorIso T.ψ).hom = Φ T.ψ.hom := rfl
    have hΦe1 : e1.hom = Φ left := rfl
    have hΦe2 : e2.hom = Φ right := rfl
    have hc2 : Bicategory.whiskerRight left X.baseProjection ≫
        Bicategory.whiskerLeft H T.ψ.hom =
      Bicategory.whiskerLeft M T.ψ.hom ≫
        Bicategory.whiskerRight right X.baseProjection := by
      exact twoCell_to_identity_unique _ _
    have hcomm := congrArg Φ hc2
    simp only [hΦcomp, hWR_left] at hcomm
    have hx := congrArg
      (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
    rw [hΦT, hΦe1, hΦe2]
    exact hx)

/-- Projection-cell comparison for two maps into the canonical self two-fibre product.  This
variant keeps the proof generic and callers only instantiate an already compiled opaque constant,
avoiding local `whnf` expansion of concrete diagonal maps. -/
noncomputable opaque twoFibreProduct_postcomposeAlpha_from_cells
    (X : FibredInGroupoidsOver C) {A : FibredInGroupoidsOver C}
    (M H : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (left : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).p ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).p)
    (right : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).q ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).q) :
    FibredInGroupoidsMor.G M ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G H ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor := by
  let T := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso left := fibredInGroupoidsMor_twoCell_isIso left
  haveI : IsIso right := fibredInGroupoidsMor_twoCell_isIso right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅
      (FibredInGroupoidsMor.G H ⋙ eDT.functor) ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso (asIso left)
  let e2 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅
      (FibredInGroupoidsMor.G H ⋙ eDT.functor) ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso (asIso right)
  exact CategoricalPullback.mkNatIso e1 e2 (by
    ext z
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp, NatTrans.comp_app]
    change Xp.map (e1.hom.app z) ≫
        (ownerIsoToFunctorIso T.ψ).hom.app ((FibredInGroupoidsMor.G H).obj z) =
      (ownerIsoToFunctorIso T.ψ).hom.app ((FibredInGroupoidsMor.G M).obj z) ≫
        Xp.map (e2.hom.app z)
    let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
      ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
        ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
          B.toFibredCategoryOver).inclusion ⋙
        BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
    let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
        (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
      fun {A B f g} t => (Ψ A B).map t
    have hWR_left : Φ (Bicategory.whiskerRight left X.baseProjection)
        = Functor.whiskerRight (Φ left) Xp := rfl
    have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
        (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
      fun {A B _ _ _} s t => (Ψ A B).map_comp s t
    have hΦT : (ownerIsoToFunctorIso T.ψ).hom = Φ T.ψ.hom := rfl
    have hΦe1 : e1.hom = Φ left := rfl
    have hΦe2 : e2.hom = Φ right := rfl
    have hc2 : Bicategory.whiskerRight left X.baseProjection ≫
        Bicategory.whiskerLeft H T.ψ.hom =
      Bicategory.whiskerLeft M T.ψ.hom ≫
        Bicategory.whiskerRight right X.baseProjection := by
      exact twoCell_to_identity_unique _ _
    have hcomm := congrArg Φ hc2
    simp only [hΦcomp, hWR_left] at hcomm
    have hx := congrArg
      (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
    rw [hΦT, hΦe1, hΦe2]
    exact hx)

/-- Total-category transport data for replacing the left leg of a two-fibre product over the
canonical self product, supplied by projection `2`-cells.  The intermediate postcomposed
categorical-pullback comparison is built inside this compiled API, so callers do not expose its
large type. -/
noncomputable opaque twoFibreProduct_transportData_postcompose_left_of_cells
    (X : FibredInGroupoidsOver C)
    {A B : FibredInGroupoidsOver C}
    (M H : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (G : B ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (left : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).p ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).p)
    (right : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).q ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).q) :
    Σ' (e : (FibredInGroupoidsOver.twoFibreProduct H G).S ⥤
        (FibredInGroupoidsOver.twoFibreProduct M G).S),
      Σ' (_ : e.IsEquivalence),
        e ⋙ (FibredInGroupoidsOver.twoFibreProduct M G).p ≅
          (FibredInGroupoidsOver.twoFibreProduct H G).p := by
  let T := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let source := FibredInGroupoidsOver.twoFibreProduct H G
  let target := FibredInGroupoidsOver.twoFibreProduct M G
  let eT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso left := fibredInGroupoidsMor_twoCell_isIso left
  haveI : IsIso right := fibredInGroupoidsMor_twoCell_isIso right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G M ⋙ eT.functor) ⋙ π₁ Xp Xp ≅
      (FibredInGroupoidsMor.G H ⋙ eT.functor) ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso (asIso left)
  let e2 : (FibredInGroupoidsMor.G M ⋙ eT.functor) ⋙ π₂ Xp Xp ≅
      (FibredInGroupoidsMor.G H ⋙ eT.functor) ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso (asIso right)
  let alpha : FibredInGroupoidsMor.G M ⋙ eT.functor ≅
      FibredInGroupoidsMor.G H ⋙ eT.functor :=
    CategoricalPullback.mkNatIso e1 e2 (by
      ext z
      simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
        Category.id_comp, NatTrans.comp_app]
      change Xp.map (e1.hom.app z) ≫
          (ownerIsoToFunctorIso T.ψ).hom.app ((FibredInGroupoidsMor.G H).obj z) =
        (ownerIsoToFunctorIso T.ψ).hom.app ((FibredInGroupoidsMor.G M).obj z) ≫
          Xp.map (e2.hom.app z)
      let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
        ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
          ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
            B.toFibredCategoryOver).inclusion ⋙
          BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
      let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
          (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
        fun {A B f g} t => (Ψ A B).map t
      have hWR_left : Φ (Bicategory.whiskerRight left X.baseProjection)
          = Functor.whiskerRight (Φ left) Xp := rfl
      have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
          (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
        fun {A B _ _ _} s t => (Ψ A B).map_comp s t
      have hΦT : (ownerIsoToFunctorIso T.ψ).hom = Φ T.ψ.hom := rfl
      have hΦe1 : e1.hom = Φ left := rfl
      have hΦe2 : e2.hom = Φ right := rfl
      have hc2 : Bicategory.whiskerRight left X.baseProjection ≫
          Bicategory.whiskerLeft H T.ψ.hom =
        Bicategory.whiskerLeft M T.ψ.hom ≫
          Bicategory.whiskerRight right X.baseProjection := by
        exact twoCell_to_identity_unique _ _
      have hcomm := congrArg Φ hc2
      simp only [hΦcomp, hWR_left] at hcomm
      have hx := congrArg
        (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
      simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
      rw [hΦT, hΦe1, hΦe2]
      exact hx)
  let eSource := twoFibreProductEquivCatPullback H G
  let eBaseSource := catPullbackCongrBase
    (FibredInGroupoidsMor.G H) (FibredInGroupoidsMor.G G) eT
  let eLegs := catPullbackCongrLegs alpha
    (Iso.refl (FibredInGroupoidsMor.G G ⋙ eT.functor))
  let eBaseTarget := catPullbackCongrBase
    (FibredInGroupoidsMor.G M) (FibredInGroupoidsMor.G G) eT
  let eTarget := twoFibreProductEquivCatPullback M G
  let q₄ := π₁ (FibredInGroupoidsMor.G M) (FibredInGroupoidsMor.G G) ⋙ A.p
  let q₃ := π₁ (FibredInGroupoidsMor.G M ⋙ eT.functor)
      (FibredInGroupoidsMor.G G ⋙ eT.functor) ⋙ A.p
  let q₂ := π₁ (FibredInGroupoidsMor.G H ⋙ eT.functor)
      (FibredInGroupoidsMor.G G ⋙ eT.functor) ⋙ A.p
  let q₁ := π₁ (FibredInGroupoidsMor.G H) (FibredInGroupoidsMor.G G) ⋙ A.p
  have h₅ : eTarget.inverse ⋙ target.p ≅ q₄ := by
    simpa [eTarget, target, q₄] using
      (twoFibreProductEquivCatPullback_inverse_baseIso_left M G)
  have h₄ : eBaseTarget.inverse ⋙ q₄ ≅ q₃ := by
    simpa [eBaseTarget, eT, q₄, q₃] using
      (catPullbackCongrBase_inverse_fst_baseIso
        (FibredInGroupoidsMor.G M) (FibredInGroupoidsMor.G G) eT A.p)
  have h₃ : eLegs.inverse ⋙ q₃ ≅ q₂ := by
    simpa [eLegs, q₃, q₂] using
      (catPullbackCongrLegs_inverse_fst_baseIso alpha
        (Iso.refl (FibredInGroupoidsMor.G G ⋙ eT.functor)) A.p)
  have h₂ : eBaseSource.functor ⋙ q₂ ≅ q₁ := by
    simpa [eBaseSource, eT, q₂, q₁] using
      (catPullbackCongrBase_functor_fst_baseIso
        (FibredInGroupoidsMor.G H) (FibredInGroupoidsMor.G G) eT A.p)
  have h₁ : eSource.functor ⋙ q₁ ≅ source.p := by
    simpa [eSource, source, q₁] using
      (twoFibreProductEquivCatPullback_functor_baseIso_left H G)
  exact functorCompBaseIso5_transportData_explicit (P := source) (Q := target)
    eSource.functor eBaseSource.functor eLegs.inverse eBaseTarget.inverse eTarget.inverse
    (inferInstance : eSource.functor.IsEquivalence)
    (inferInstance : eBaseSource.functor.IsEquivalence)
    (inferInstance : eLegs.inverse.IsEquivalence)
    (inferInstance : eBaseTarget.inverse.IsEquivalence)
    (inferInstance : eTarget.inverse.IsEquivalence)
    q₄ q₃ q₂ q₁ h₅ h₄ h₃ h₂ h₁

/-- Transport representability when the left maps into the canonical self two-fibre product have
projection `2`-cells.  The postcomposed comparison is built directly here so downstream files do
not have to elaborate the large comparison isomorphism. -/
opaque twoFibreProduct_representable_transport_postcompose_left_of_two_cells
    (X : FibredInGroupoidsOver C) {A B : FibredInGroupoidsOver C}
    {M M' : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection}
    {G : B ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection}
    (left : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).p ⟶
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).p)
    (right : M ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).q ⟶
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).q) :
    (FibredInGroupoidsOver.twoFibreProduct M G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct M' G).IsRepresentable := by
  intro hRep
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso left := fibredInGroupoidsMor_twoCell_isIso left
  haveI : IsIso right := fibredInGroupoidsMor_twoCell_isIso right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso (asIso left)
  let e2 : (FibredInGroupoidsMor.G M ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso (asIso right)
  let α : FibredInGroupoidsMor.G M ⋙ eDT.functor ≅
      FibredInGroupoidsMor.G M' ⋙ eDT.functor :=
    CategoricalPullback.mkNatIso e1 e2 (by
      ext z
      simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
        Category.id_comp, NatTrans.comp_app]
      change Xp.map (e1.hom.app z) ≫
          (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M').obj z) =
        (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M).obj z) ≫
          Xp.map (e2.hom.app z)
      let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
        ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
          ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
            B.toFibredCategoryOver).inclusion ⋙
          BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
      let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
          (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
        fun {A B f g} t => (Ψ A B).map t
      have hWR_left : Φ (Bicategory.whiskerRight left X.baseProjection)
          = Functor.whiskerRight (Φ left) Xp := rfl
      have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
          (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
        fun {A B _ _ _} s t => (Ψ A B).map_comp s t
      have hΦDT : (ownerIsoToFunctorIso DTsq.ψ).hom = Φ DTsq.ψ.hom := rfl
      have hΦe1 : e1.hom = Φ left := rfl
      have hΦe2 : e2.hom = Φ right := rfl
      have hc2 : Bicategory.whiskerRight left X.baseProjection ≫
          Bicategory.whiskerLeft M' DTsq.ψ.hom =
        Bicategory.whiskerLeft M DTsq.ψ.hom ≫
          Bicategory.whiskerRight right X.baseProjection := by
        exact twoCell_to_identity_unique _ _
      have hcomm := congrArg Φ hc2
      simp only [hΦcomp, hWR_left] at hcomm
      have hx := congrArg
        (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
      simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
      rw [hΦDT, hΦe1, hΦe2]
      exact hx)
  exact twoFibreProduct_representable_transport_postcompose_left eDT α hRep

/-- Variant of `twoFibreProduct_representable_transport_postcompose_left_of_two_cells` for a
left map written as `K ≫ u.hom`.  Keeping this composite in the statement avoids a costly
definitional-equality check in downstream diagonal arguments. -/
opaque twoFibreProduct_representable_transport_postcompose_left_of_composed_two_cells
    (X : FibredInGroupoidsOver C)
    {P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    {A B : FibredInGroupoidsOver C}
    (K : A ⟶ P.obj)
    (u : P ⟶ FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    {M' : A ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection}
    {G : B ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection}
    (left : (K ≫ u.hom) ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).p ⟶
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).p)
    (right : (K ≫ u.hom) ≫ (FibredInGroupoidsOver.twoFibreProductSquare
      X.baseProjection X.baseProjection).q ⟶
      M' ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).q) :
    (FibredInGroupoidsOver.twoFibreProduct (K ≫ u.hom) G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct M' G).IsRepresentable := by
  intro hRep
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso left := fibredInGroupoidsMor_twoCell_isIso left
  haveI : IsIso right := fibredInGroupoidsMor_twoCell_isIso right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let e1 : (FibredInGroupoidsMor.G (K ≫ u.hom) ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso (asIso left)
  let e2 : (FibredInGroupoidsMor.G (K ≫ u.hom) ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅
      (FibredInGroupoidsMor.G M' ⋙ eDT.functor) ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso (asIso right)
  let α : FibredInGroupoidsMor.G (K ≫ u.hom) ⋙ eDT.functor ≅
      FibredInGroupoidsMor.G M' ⋙ eDT.functor :=
    CategoricalPullback.mkNatIso e1 e2 (by
      ext z
      simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
        Category.id_comp, NatTrans.comp_app]
      change Xp.map (e1.hom.app z) ≫
          (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G M').obj z) =
        (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G (K ≫ u.hom)).obj z) ≫
          Xp.map (e2.hom.app z)
      let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
        ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
          ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
            B.toFibredCategoryOver).inclusion ⋙
          BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
      let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
          (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) :=
        fun {A B f g} t => (Ψ A B).map t
      have hWR_left : Φ (Bicategory.whiskerRight left X.baseProjection)
          = Functor.whiskerRight (Φ left) Xp := rfl
      have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B}
          (s : f ⟶ g) (t : g ⟶ h), Φ (s ≫ t) = Φ s ≫ Φ t :=
        fun {A B _ _ _} s t => (Ψ A B).map_comp s t
      have hΦDT : (ownerIsoToFunctorIso DTsq.ψ).hom = Φ DTsq.ψ.hom := rfl
      have hΦe1 : e1.hom = Φ left := rfl
      have hΦe2 : e2.hom = Φ right := rfl
      have hc2 : Bicategory.whiskerRight left X.baseProjection ≫
          Bicategory.whiskerLeft M' DTsq.ψ.hom =
        Bicategory.whiskerLeft (K ≫ u.hom) DTsq.ψ.hom ≫
          Bicategory.whiskerRight right X.baseProjection := by
        exact twoCell_to_identity_unique _ _
      have hcomm := congrArg Φ hc2
      simp only [hΦcomp, hWR_left] at hcomm
      have hx := congrArg
        (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
      simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
      rw [hΦDT, hΦe1, hΦe2]
      exact hx)
  exact twoFibreProduct_representable_transport_postcompose_left eDT α hRep

/-- The square-comparison isomorphism (kept opaque in `u.hom`): the underlying functor of `u.hom`
composed with the Remark-4.35.8 comparison `eDT.functor` is the explicit categorical-pullback
functor of `P`'s legs `P.p.G, P.q.G` with structural iso `ownerIsoToFunctorIso P.ψ`.  The target is
phrased through `functorEquiv.inverse.obj` (definitionally `mkCatPullbackFunctor …`, see
`mkCatPullbackFunctor_eq_functorEquiv_inverse`).

The single non-formal ingredient is the `coh`: the image of the square-morphism compatibility field
`u.comm` under the strict `2`-functor "forget a `2`-cell to its underlying natural transformation"
(`Φ` below).  The Remark-4.35.8 comparison stores, on each object, exactly the underlying-functor
image of the target square's `2`-commutativity witness, so the `coh` reduces *definitionally* to a
`2`-cell equation that is `Φ`-image of `u.comm`. -/
noncomputable opaque squareComparisonIso (X : FibredInGroupoidsOver C)
    (P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    (u : P ⟶ FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    (FibredInGroupoidsMor.G u.hom ⋙
      (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor) ≅
    (CategoricalPullback.functorEquiv (FibredInGroupoidsMor.G X.baseProjection)
        (FibredInGroupoidsMor.G X.baseProjection) P.obj.S).inverse.obj
      { fst := FibredInGroupoidsMor.G P.p
        snd := FibredInGroupoidsMor.G P.q
        iso := ownerIsoToFunctorIso P.ψ } := by
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  haveI : IsIso u.left := fibredInGroupoidsMor_twoCell_isIso u.left
  haveI : IsIso u.right := fibredInGroupoidsMor_twoCell_isIso u.right
  let Xp := FibredInGroupoidsMor.G X.baseProjection
  let Q : CatCommSqOver Xp Xp P.obj.S :=
    { fst := FibredInGroupoidsMor.G P.p, snd := FibredInGroupoidsMor.G P.q,
      iso := ownerIsoToFunctorIso P.ψ }
  let targetFun : P.obj.S ⥤ Xp ⊡ Xp :=
    (CategoricalPullback.functorEquiv Xp Xp P.obj.S).inverse.obj Q
  let e1 : (FibredInGroupoidsMor.G u.hom ⋙ eDT.functor) ⋙ π₁ Xp Xp ≅ targetFun ⋙ π₁ Xp Xp :=
    ownerIsoToFunctorIso (asIso u.left)
  let e2 : (FibredInGroupoidsMor.G u.hom ⋙ eDT.functor) ⋙ π₂ Xp Xp ≅ targetFun ⋙ π₂ Xp Xp :=
    ownerIsoToFunctorIso (asIso u.right)
  exact CategoricalPullback.mkNatIso e1 e2 (by
      ext z
      simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
        Category.id_comp, NatTrans.comp_app]
      simp only [CatCommSq.iso, NatIso.ofComponents_hom_app]
      simp only [CategoricalPullback.functorEquiv_inverse_obj_obj_iso_hom]
      change Xp.map (e1.hom.app z) ≫ (ownerIsoToFunctorIso P.ψ).hom.app z =
        (ownerIsoToFunctorIso DTsq.ψ).hom.app ((FibredInGroupoidsMor.G u.hom).obj z) ≫
          Xp.map (e2.hom.app z)
      let Ψ : (A B : FibredInGroupoidsOver C) → (A ⟶ B) ⥤ (A.S ⥤ B.S) := fun A B =>
        ((fibredInGroupoidsOverSubTwoCategory C).hom A B).inclusion ⋙
          ((fibredCategoryOverSubTwoCategory C).hom A.toFibredCategoryOver
            B.toFibredCategoryOver).inclusion ⋙
          BasedNatTrans.forgetful A.toBasedCategory B.toBasedCategory
      let Φ : {A B : FibredInGroupoidsOver C} → {f g : A ⟶ B} → (f ⟶ g) →
          (FibredInGroupoidsMor.G f ⟶ FibredInGroupoidsMor.G g) := fun {A B f g} t => (Ψ A B).map t
      have hWR : Φ (Bicategory.whiskerRight u.left X.baseProjection)
          = Functor.whiskerRight (Φ u.left) Xp := rfl
      have hΦcomp : ∀ {A B : FibredInGroupoidsOver C} {f g h : A ⟶ B} (s : f ⟶ g) (t : g ⟶ h),
          Φ (s ≫ t) = Φ s ≫ Φ t := fun {A B _ _ _} s t => (Ψ A B).map_comp s t
      have hΦ1 : (ownerIsoToFunctorIso P.ψ).hom = Φ P.ψ.hom := rfl
      have hΦDT : (ownerIsoToFunctorIso DTsq.ψ).hom = Φ DTsq.ψ.hom := rfl
      have hΦe1 : e1.hom = Φ u.left := rfl
      have hΦe2 : e2.hom = Φ u.right := rfl
      have hAref : (Bicategory.associator u.hom DTsq.p X.baseProjection) = Iso.refl _ := rfl
      have hAref2 : (Bicategory.associator u.hom DTsq.q X.baseProjection) = Iso.refl _ := rfl
      have hc2 : Bicategory.whiskerRight u.left X.baseProjection ≫ P.ψ.hom
          = Bicategory.whiskerLeft u.hom DTsq.ψ.hom ≫
            Bicategory.whiskerRight u.right X.baseProjection := by
        have h := u.comm
        rw [hAref, hAref2] at h
        simp only [Iso.refl_hom, Iso.refl_inv] at h
        erw [Category.id_comp, Category.id_comp] at h
        exact h
      have hcomm := congrArg Φ hc2
      simp only [hΦcomp, hWR] at hcomm
      have hx := congrArg
        (fun (τ : FibredInGroupoidsMor.G _ ⟶ FibredInGroupoidsMor.G _) => τ.app z) hcomm
      simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hx
      rw [hΦ1, hΦDT, hΦe1, hΦe2]
      exact hx)



/-- Any two morphisms from the same square into the canonical two-fibre-product square have
isomorphic underlying total-category functors.  After composing with the canonical equivalence to the
ordinary categorical pullback, both are identified by `squareComparisonIso` with the same explicit
categorical-pullback functor. -/
noncomputable opaque squareHomFunctorIsoOfComparison
    (X : FibredInGroupoidsOver C)
    {P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    {u v : P ⟶ FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection} :
    FibredInGroupoidsMor.G u.hom ≅ FibredInGroupoidsMor.G v.hom := by
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  let α : FibredInGroupoidsMor.G u.hom ⋙ eDT.functor ≅
      FibredInGroupoidsMor.G v.hom ⋙ eDT.functor :=
    (squareComparisonIso X P u) ≪≫ (squareComparisonIso X P v).symm
  exact ((Functor.FullyFaithful.ofFullyFaithful eDT.functor).whiskeringRight P.obj.S).preimageIso α

/-- Two morphisms from the same source square into the canonical two-fibre-product square agree
after postcomposing with the Remark-4.35.8 comparison.  This is the postcomposed form of
`squareHomFunctorIsoOfComparison`, kept as a separate API so callers do not have to build the
common categorical-pullback target locally. -/
noncomputable opaque squareComparisonPostcomposeIso
    (X : FibredInGroupoidsOver C)
    {P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    (u v : P ⟶ FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    FibredInGroupoidsMor.G u.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G v.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor :=
  (squareComparisonIso X P u) ≪≫ (squareComparisonIso X P v).symm

/-- Leg-cell form of `squareComparisonIso`, avoiding explicit local construction of the square
morphism in callers. -/
noncomputable opaque squareComparisonIsoOfLegs
    (X : FibredInGroupoidsOver C)
    {P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    (hom : P.obj ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (left : hom ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).p ⟶
      P.p)
    (right : hom ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).q ⟶
      P.q) :
    FibredInGroupoidsMor.G hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      (Limits.CategoricalPullback.functorEquiv (FibredInGroupoidsMor.G X.baseProjection)
        (FibredInGroupoidsMor.G X.baseProjection) P.obj.S).inverse.obj
      { fst := FibredInGroupoidsMor.G P.p
        snd := FibredInGroupoidsMor.G P.q
        iso := ownerIsoToFunctorIso P.ψ } :=
  squareComparisonIso X P (squareHomMkToIdentity X (P := P)
    (Q := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    hom left right)

/-- Transport representability across replacing the left leg by another morphism from the same
source square into the canonical two-fibre-product square, and replacing the right leg by a
functor-isomorphic morphism. -/
opaque twoFibreProduct_representable_transport_square_left
    (X : FibredInGroupoidsOver C)
    {P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection}
    {u v : P ⟶ FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection}
    {B : FibredInGroupoidsOver C}
    {D D' : B ⟶ FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection}
    (β : FibredInGroupoidsMor.G D ≅ FibredInGroupoidsMor.G D') :
    (FibredInGroupoidsOver.twoFibreProduct u.hom D).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct v.hom D').IsRepresentable := by
  intro hRep
  let α : FibredInGroupoidsMor.G u.hom ≅ FibredInGroupoidsMor.G v.hom :=
    squareHomFunctorIsoOfComparison X (P := P) (u := u) (v := v)
  exact twoFibreProduct_representable_transport_functor_iso α β hRep

/-! ### The product-slice map carried by an explicit two-fibre product -/

section ExplicitTwoFibreProductProductSlice

variable [Limits.HasBinaryProducts C]
variable {U V : C}
variable {S : BasedCategory C}
variable (F : (ofFunctor (Over.forget V)).toBasedCategory ⥤ᵇ S)
variable (G : (ofFunctor (Over.forget U)).toBasedCategory ⥤ᵇ S)
omit [HasBinaryProducts C] in
/-- The `U`-slice component of a morphism in the explicit two-fibre product is compatible with
its stored base arrow. -/
theorem explicitTwoFibreProductHom_snd_base_comp
    {P Q : (CategoryOver.explicitTwoFibreProduct F G).obj}
    (φ : P ⟶ Q) :
    φ.base ≫ (eqToHom Q.obj.snd.2.symm ≫ Q.obj.snd.1.hom) =
      eqToHom P.obj.snd.2.symm ≫ P.obj.snd.1.hom := by
  cases P with
  | mk PU Pobj =>
    cases Q with
    | mk QU Qobj =>
      cases Pobj with
      | mk Pfst Psnd Piso =>
        cases Qobj with
        | mk Qfst Qsnd Qiso =>
          cases Psnd with
          | mk PsndObj hPsnd =>
            cases Qsnd with
            | mk QsndObj hQsnd =>
              cases hPsnd
              cases hQsnd
              have hb : φ.base = φ.b.left := by
                simpa only [Over.forget_map] using
                  (@IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget U) _ _ φ.base φ.b
                    φ.b_over)
              rw [hb]
              simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using Over.w φ.b
omit [HasBinaryProducts C] in
/-- The `V`-slice component of a morphism in the explicit two-fibre product is compatible with
its stored base arrow. -/
theorem explicitTwoFibreProductHom_fst_base_comp
    {P Q : (CategoryOver.explicitTwoFibreProduct F G).obj}
    (φ : P ⟶ Q) :
    φ.base ≫ (eqToHom Q.obj.fst.2.symm ≫ Q.obj.fst.1.hom) =
      eqToHom P.obj.fst.2.symm ≫ P.obj.fst.1.hom := by
  cases P with
  | mk PU Pobj =>
    cases Q with
    | mk QU Qobj =>
      cases Pobj with
      | mk Pfst Psnd Piso =>
        cases Qobj with
        | mk Qfst Qsnd Qiso =>
          cases Pfst with
          | mk PfstObj hPfst =>
            cases Qfst with
            | mk QfstObj hQfst =>
              cases hPfst
              cases hQfst
              have hb : φ.base = φ.a.left := by
                simpa only [Over.forget_map] using
                  (@IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget V) _ _ φ.base φ.a
                    φ.a_over)
              rw [hb]
              simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using Over.w φ.a

/-- The explicit two-fibre product of two slice morphisms has a canonical map to the product
slice: an object over `T` with components `T -> U` and `T -> V` is sent to the induced
`T -> U x V`. -/
noncomputable def explicitTwoFibreProductToProductSliceFunctor :
    (CategoryOver.explicitTwoFibreProduct F G).obj ⥤ Over (Limits.prod U V) where
  obj P := Over.mk (Limits.prod.lift
    (eqToHom P.obj.snd.2.symm ≫ P.obj.snd.1.hom)
    (eqToHom P.obj.fst.2.symm ≫ P.obj.fst.1.hom))
  map {P Q} φ := Over.homMk φ.base (by
    apply Limits.prod.hom_ext
    · simpa [Over.mk_hom, Category.assoc, Limits.prod.lift_fst] using
        explicitTwoFibreProductHom_snd_base_comp (F := F) (G := G) φ
    · simpa [Over.mk_hom, Category.assoc, Limits.prod.lift_snd] using
        explicitTwoFibreProductHom_fst_base_comp (F := F) (G := G) φ)
  map_id P := by
    ext
    rfl
  map_comp {P Q R} φ ψ := by
    ext
    rfl

/-- Forgetting the product-slice map recovers the base projection of the explicit two-fibre
product, strictly. -/
@[simp] theorem explicitTwoFibreProductToProductSliceFunctor_comp_forget :
    explicitTwoFibreProductToProductSliceFunctor F G ⋙ Over.forget (Limits.prod U V) =
      (CategoryOver.explicitTwoFibreProduct F G).p :=
  rfl

/-- The same product-slice functor for the fibred-in-groupoids two-fibre product. -/
noncomputable def twoFibreProductToProductSliceFunctor
    (X : FibredInGroupoidsOver C) {U V : C}
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    (FibredInGroupoidsOver.twoFibreProduct G' G).S ⥤ Over (Limits.prod U V) :=
  explicitTwoFibreProductToProductSliceFunctor
    (F := FibredInGroupoidsMor.toBasedFunctor G')
    (G := FibredInGroupoidsMor.toBasedFunctor G)

/-- The fibred-in-groupoids product-slice functor is strictly over `C`. -/
@[simp] theorem twoFibreProductToProductSliceFunctor_comp_forget
    (X : FibredInGroupoidsOver C) {U V : C}
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    twoFibreProductToProductSliceFunctor X G G' ⋙ Over.forget (Limits.prod U V) =
      (FibredInGroupoidsOver.twoFibreProduct G' G).p :=
  rfl

/-- The product-slice functor bundled as a morphism of categories fibred in groupoids over C. -/
noncomputable def twoFibreProductToProductSliceMor
    (X : FibredInGroupoidsOver C) {U V : C}
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    FibredInGroupoidsOver.twoFibreProduct G' G ⟶
      ofFunctor (Over.forget (Limits.prod U V)) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := twoFibreProductToProductSliceFunctor X G G'
      w := twoFibreProductToProductSliceFunctor_comp_forget X G G' }

end ExplicitTwoFibreProductProductSlice

/-! ### Product-slice comparison with the right vertical functor of Lemma 4.31.13 -/

section ProductSliceRightVertical

variable [Limits.HasBinaryProducts C]
variable {XS : Type (max u v)} [Category.{v} XS]
variable {U V : C} {gU : Over U ⥤ XS} {gV : Over V ⥤ XS} {xp : XS ⥤ C}

/-- The base isomorphism showing that the two product-slice legs into `C` agree after applying the
representing isomorphisms `gU ⋙ xp ≅ C/U` and `gV ⋙ xp ≅ C/V`. -/
noncomputable def productSliceRightVerticalBaseIso
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp) :=
  NatIso.ofComponents
    (fun c => eU.app ((Over.map Limits.prod.fst).obj c) ≪≫
      (eV.app ((Over.map Limits.prod.snd).obj c)).symm)
    (by
      intro c d f
      dsimp
      have hU := eU.hom.naturality
        ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U)).map f)
      have hV := eV.inv.naturality
        ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V)).map f)
      have hU' :
          xp.map (gU.map ((Over.map Limits.prod.fst).map f)) ≫
              eU.hom.app ((Over.map Limits.prod.fst).obj d) ≫
                eV.inv.app ((Over.map Limits.prod.snd).obj d) =
            eU.hom.app ((Over.map Limits.prod.fst).obj c) ≫ f.left ≫
                eV.inv.app ((Over.map Limits.prod.snd).obj d) := by
        simpa [Functor.comp_map, Category.assoc] using
          congrArg (fun t => t ≫ eV.inv.app ((Over.map Limits.prod.snd).obj d)) hU
      have hV' :
          eU.hom.app ((Over.map Limits.prod.fst).obj c) ≫ f.left ≫
                eV.inv.app ((Over.map Limits.prod.snd).obj d) =
            eU.hom.app ((Over.map Limits.prod.fst).obj c) ≫
              eV.inv.app ((Over.map Limits.prod.snd).obj c) ≫
                xp.map (gV.map ((Over.map Limits.prod.snd).map f)) := by
        simpa [Functor.comp_map, Category.assoc] using
          congrArg (fun t => eU.hom.app ((Over.map Limits.prod.fst).obj c) ≫ t) hV
      simpa [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Iso.symm_hom, Category.assoc]
        using hU'.trans hV')

@[simp] theorem productSliceRightVerticalBaseIso_hom_app
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    (productSliceRightVerticalBaseIso (gU := gU) (gV := gV) (xp := xp) eU eV).hom.app c =
      eU.hom.app ((Over.map Limits.prod.fst).obj c) ≫
        eV.inv.app ((Over.map Limits.prod.snd).obj c) :=
  rfl

end ProductSliceRightVertical

/-! ### Product-slice source square with explicit base projection isomorphism -/

section ProductSliceSourceSquare

variable [Limits.HasBinaryProducts C]
variable {U V : C}

/-- The left pulled-back base projection agrees with the product-slice projection. -/
theorem product_slice_left_base_obj_eq
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (a : Over (Limits.prod U V)) :
    (ofFunctor (𝟭 C)).toBasedCategory.p.obj
        ((FibredInGroupoidsMor.G
          ((slice_morphism_pullback X (Limits.prod.fst (X := U) (Y := V)) G) ≫
            X.baseProjection)).obj a) =
      (ofFunctor (Over.forget (Limits.prod U V))).toBasedCategory.p.obj a := by
  let aU := (Over.map (Limits.prod.fst (X := U) (Y := V))).obj a
  change (FibredInGroupoidsMor.G G ⋙ X.p).obj aU = (Over.forget U).obj aU
  exact congrFun (congrArg Functor.obj (FibredInGroupoidsMor.comm G)) aU

/-- The right pulled-back base projection agrees with the product-slice projection. -/
theorem product_slice_right_base_obj_eq
    (X : FibredInGroupoidsOver C)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (a : Over (Limits.prod U V)) :
    (ofFunctor (𝟭 C)).toBasedCategory.p.obj
        ((FibredInGroupoidsMor.G
          ((slice_morphism_pullback X (Limits.prod.snd (X := U) (Y := V)) G') ≫
            X.baseProjection)).obj a) =
      (ofFunctor (Over.forget (Limits.prod U V))).toBasedCategory.p.obj a := by
  let aV := (Over.map (Limits.prod.snd (X := U) (Y := V))).obj a
  change (FibredInGroupoidsMor.G G' ⋙ X.p).obj aV = (Over.forget V).obj aV
  exact congrFun (congrArg Functor.obj (FibredInGroupoidsMor.comm G')) aV

/-- The explicit product-slice base isomorphism has components lying over identities for the target
`C -> C`. -/
theorem product_slice_pullbacks_base_projection_hom_isHomLift
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (a : Over (Limits.prod U V)) :
    (ofFunctor (𝟭 C)).toBasedCategory.p.IsHomLift
      (𝟙 ((ofFunctor (Over.forget (Limits.prod U V))).toBasedCategory.p.obj a))
      ((productSliceRightVerticalBaseIso
          (gU := FibredInGroupoidsMor.G G)
          (gV := FibredInGroupoidsMor.G G')
          (xp := X.p)
          (eqToIso (FibredInGroupoidsMor.comm G))
          (eqToIso (FibredInGroupoidsMor.comm G'))).hom.app a) := by
  have hUapp :
      (eqToHom (FibredInGroupoidsMor.comm G) :
          (FibredInGroupoidsMor.G G ⋙ X.p) ⟶ Over.forget U).app
          ((Over.map (Limits.prod.fst (X := U) (Y := V))).obj a) =
        eqToHom (product_slice_left_base_obj_eq X G a) := by
    rw [eqToHom_functor_app]
    apply eqToHom_eq_of_proof_irrel
  have hVapp :
      (eqToHom (FibredInGroupoidsMor.comm G').symm :
          Over.forget V ⟶ (FibredInGroupoidsMor.G G' ⋙ X.p)).app
          ((Over.map (Limits.prod.snd (X := U) (Y := V))).obj a) =
        eqToHom (product_slice_right_base_obj_eq X G' a).symm := by
    rw [eqToHom_functor_app]
    apply eqToHom_eq_of_proof_irrel
  refine IsHomLift.of_fac' (ofFunctor (𝟭 C)).toBasedCategory.p
    (𝟙 ((ofFunctor (Over.forget (Limits.prod U V))).toBasedCategory.p.obj a))
    ((productSliceRightVerticalBaseIso
        (gU := FibredInGroupoidsMor.G G)
        (gV := FibredInGroupoidsMor.G G')
        (xp := X.p)
        (eqToIso (FibredInGroupoidsMor.comm G))
        (eqToIso (FibredInGroupoidsMor.comm G'))).hom.app a)
    (product_slice_left_base_obj_eq X G a)
    (product_slice_right_base_obj_eq X G' a) ?_
  dsimp [productSliceRightVerticalBaseIso, slice_morphism_pullback, over_map_morphism]
  change (𝟭 C).map
      ((eqToHom (FibredInGroupoidsMor.comm G) :
          (FibredInGroupoidsMor.G G ⋙ X.p) ⟶ Over.forget U).app
          ((Over.map (Limits.prod.fst (X := U) (Y := V))).obj a) ≫
        (eqToHom (FibredInGroupoidsMor.comm G').symm :
          Over.forget V ⟶ (FibredInGroupoidsMor.G G' ⋙ X.p)).app
          ((Over.map (Limits.prod.snd (X := U) (Y := V))).obj a)) =
    eqToHom (product_slice_left_base_obj_eq X G a) ≫ 𝟙 _ ≫
      eqToHom (product_slice_right_base_obj_eq X G' a).symm
  rw [hUapp, hVapp]
  simp only [Functor.id_map, Category.id_comp]
  change eqToHom (product_slice_left_base_obj_eq X G a) ≫
      eqToHom (product_slice_right_base_obj_eq X G' a).symm =
    eqToHom (product_slice_left_base_obj_eq X G a) ≫
      eqToHom (product_slice_right_base_obj_eq X G' a).symm
  apply eqToHom_comp_eq_of_proof_irrel

/-- The product-slice base projection isomorphism, constructed with an explicit underlying natural
isomorphism. This avoids later recovering the right vertical functor from a large equality proof. -/
noncomputable def product_slice_pullbacks_base_projection_iso_explicit
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    ((slice_morphism_pullback X Limits.prod.fst G) ≫ X.baseProjection) ≅
      ((slice_morphism_pullback X Limits.prod.snd G') ≫ X.baseProjection) :=
  FibredInGroupoidsMor.ownerIsoOfBasedFunctorIso
    (BasedNatIso.mkNatIso
      (productSliceRightVerticalBaseIso
        (gU := FibredInGroupoidsMor.G G)
        (gV := FibredInGroupoidsMor.G G')
        (xp := X.p)
        (eqToIso (FibredInGroupoidsMor.comm G))
        (eqToIso (FibredInGroupoidsMor.comm G')))
      (product_slice_pullbacks_base_projection_hom_isHomLift X G G'))

@[simp] theorem ownerIsoToFunctorIso_product_slice_pullbacks_base_projection_iso_explicit
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    ownerIsoToFunctorIso (product_slice_pullbacks_base_projection_iso_explicit X G G') =
      productSliceRightVerticalBaseIso
        (gU := FibredInGroupoidsMor.G G)
        (gV := FibredInGroupoidsMor.G G')
        (xp := X.p)
        (eqToIso (FibredInGroupoidsMor.comm G))
        (eqToIso (FibredInGroupoidsMor.comm G')) := by
  rfl

/-- The product-slice source square for the comparison with the diagonal target, using the explicit
base-projection isomorphism above. -/
noncomputable def productSliceSourceSquare
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection where
  obj := ofFunctor (Over.forget (Limits.prod U V))
  p := slice_morphism_pullback X Limits.prod.fst G
  q := slice_morphism_pullback X Limits.prod.snd G'
  ψ := product_slice_pullbacks_base_projection_iso_explicit X G G'

/-- The apex projection of the product-slice source square is the product-slice forgetful functor. -/
@[simp] theorem productSliceSourceSquare_obj_p
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    (productSliceSourceSquare X G G').obj.p = Over.forget (Limits.prod U V) :=
  rfl

/-- The inverse Remark-4.35.8 projection formula specialized to a two-fibre product whose left leg
starts at the product-slice source square. -/
noncomputable def productSliceSource_twoFibreProductEquiv_inverse_baseIso_left
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    {T Y : FibredInGroupoidsOver C}
    (H : (productSliceSourceSquare X G G').obj ⟶ T) (Dg : Y ⟶ T) :
    (twoFibreProductEquivCatPullback H Dg).inverse ⋙
        (FibredInGroupoidsOver.twoFibreProduct H Dg).p ≅
      π₁ (FibredInGroupoidsMor.G H) (FibredInGroupoidsMor.G Dg) ⋙
        Over.forget (Limits.prod U V) :=
  (twoFibreProductEquivCatPullback_inverse_baseIso_left H Dg) ≪≫
    Functor.isoWhiskerLeft (π₁ (FibredInGroupoidsMor.G H) (FibredInGroupoidsMor.G Dg))
      (eqToIso (productSliceSourceSquare_obj_p X G G'))


/-- The identity source square whose terminal factorization is the diagonal. -/
noncomputable def diagonalSourceSquare (X : FibredInGroupoidsOver C) :
    BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection where
  obj := X
  p := 𝟙 X
  q := 𝟙 X
  ψ := Iso.refl X.baseProjection

/-- The identity source square comparison is the ordinary categorical diagonal after the
Remark 4.35.8 equivalence.  The square morphism is kept opaque; this avoids unfolding the terminal
factorization defining the diagonal morphism. -/
noncomputable def diagonalSourceSquareComparisonIso
    (X : FibredInGroupoidsOver C)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    FibredInGroupoidsMor.G uDg.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      Limits.categorical_pullback_diagonal X.p := by
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  let Δ := Limits.categorical_pullback_diagonal X.p
  let isoD₀ : (FibredInGroupoidsMor.G uDg.hom ⋙ eDT.functor) ≅
      (CategoricalPullback.functorEquiv (FibredInGroupoidsMor.G X.baseProjection)
        (FibredInGroupoidsMor.G X.baseProjection) X.S).inverse.obj
        { fst := FibredInGroupoidsMor.G (𝟙 X)
          snd := FibredInGroupoidsMor.G (𝟙 X)
          iso := ownerIsoToFunctorIso (Iso.refl X.baseProjection) } :=
    squareComparisonIso X (diagonalSourceSquare X) uDg
  have hDiagTarget :
      (CategoricalPullback.functorEquiv (FibredInGroupoidsMor.G X.baseProjection)
          (FibredInGroupoidsMor.G X.baseProjection) X.S).inverse.obj
        { fst := FibredInGroupoidsMor.G (𝟙 X)
          snd := FibredInGroupoidsMor.G (𝟙 X)
          iso := ownerIsoToFunctorIso (Iso.refl X.baseProjection) } = Δ := by
    dsimp [Δ, Limits.categorical_pullback_diagonal]
    rfl
  exact isoD₀ ≪≫ eqToIso hDiagTarget

-- The diagonal owner `twoFibreProductDiagonalMor` is `@[irreducible]` (its terminal-factorization
-- body is whnf-heavy).  Here we only need its definitional identification with the terminal map
-- `uDg.hom` out of `diagonalSourceSquare X`, so locally restore default unfolding.
attribute [local semireducible] FibredInGroupoidsMor.twoFibreProductDiagonalMor

/-- The concrete diagonal morphism of the canonical two-fibre product becomes the ordinary
categorical diagonal after the Remark 4.35.8 equivalence. -/
noncomputable def diagonalMorComparisonIso
    (X : FibredInGroupoidsOver C) :
    FibredInGroupoidsMor.G (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      Limits.categorical_pullback_diagonal X.p := by
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  haveI hDTsq : Bicategory.IsFinal DTsq :=
    FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct X.baseProjection X.baseProjection
  let PDg := diagonalSourceSquare X
  haveI : Limits.HasTerminal (PDg ⟶ DTsq) :=
    Bicategory.IsFinal.hasTerminal (x := DTsq) PDg
  let uDg : PDg ⟶ DTsq := ⊤_ (PDg ⟶ DTsq)
  change FibredInGroupoidsMor.G uDg.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      Limits.categorical_pullback_diagonal X.p
  exact diagonalSourceSquareComparisonIso X uDg


end ProductSliceSourceSquare

section ProductSliceRightVertical

variable [Limits.HasBinaryProducts C]
variable {XS : Type (max u v)} [Category.{v} XS]
variable {U V : C} {gU : Over U ⥤ XS} {gV : Over V ⥤ XS} {xp : XS ⥤ C}

/-- The explicit functor from the product slice `C/(U × V)` into `xp ⊡ xp` induced by the two
slice legs over `U` and `V`.  This is the categorical-pullback functor which the Stacks proof uses
after identifying `C/U × C/V` with `C/(U × V)`. -/
@[simps]
noncomputable def productSliceRightVerticalFunctor
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp)) :
    Over (Limits.prod U V) ⥤ xp ⊡ xp where
  obj c :=
    { fst := gU.obj ((Over.map Limits.prod.fst).obj c)
      snd := gV.obj ((Over.map Limits.prod.snd).obj c)
      iso := eH.app c }
  map {c d} f :=
    { fst := gU.map ((Over.map Limits.prod.fst).map f)
      snd := gV.map ((Over.map Limits.prod.snd).map f)
      w := eH.hom.naturality f }
  map_id := by
    intro c
    apply CategoricalPullback.hom_ext
    · simpa using congrArg (fun q => gU.map q)
        ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U)).map_id c)
    · simpa using congrArg (fun q => gV.map q)
        ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V)).map_id c)
  map_comp := by
    intro c d e f g
    apply CategoricalPullback.hom_ext
    · simpa using congrArg (fun q => gU.map q)
        ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U)).map_comp f g)
    · simpa using congrArg (fun q => gV.map q)
        ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V)).map_comp f g)


/-- After the product-of-slices equivalence and the leg-congruence by `eU,eV`, the right vertical
functor of Lemma 4.31.13 is the explicit product-slice functor above. -/
noncomputable def productSliceRightVerticalIso
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    prodSliceToSliceProd U V ⋙
        (catPullbackCongrLegs eU.symm eV.symm).functor ⋙
          Limits.two_fibre_product_right_vertical gU gV xp ≅
      productSliceRightVerticalFunctor
        (productSliceRightVerticalBaseIso (gU := gU) (gV := gV) (xp := xp) eU eV) := by
  refine NatIso.ofComponents (fun c => ?_) ?_
  · refine CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) ?_
    simp only [Functor.comp_obj, Iso.refl_hom]
    rw [Limits.twoFibreProductRightVertical_obj_iso_hom]
    simp [productSliceRightVerticalFunctor, prodSliceToSliceProd, catPullbackCongrLegs]
  · intro c d f
    apply CategoricalPullback.hom_ext
    · simp [productSliceRightVerticalFunctor, prodSliceToSliceProd, catPullbackCongrLegs]
    · simp [productSliceRightVerticalFunctor, prodSliceToSliceProd, catPullbackCongrLegs]


/-- The comparison functor from the slice product `gV ⊡ gU` to the diagonal base change built from
`C/(U × V)`.  It is the Stacks Lemma 4.31.13 comparison, transported through the product-of-slices
identification and the two leg isomorphisms `eU,eV`; the final swap gives the `G',G` order used in
Lemma 4.42.6. -/
noncomputable def productSliceDiagonalComparisonFunctor
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    gV ⊡ gU ⥤
      (productSliceRightVerticalFunctor
          (productSliceRightVerticalBaseIso (gU := gU) (gV := gV) (xp := xp) eU eV)) ⊡
        (Limits.categorical_pullback_diagonal xp) :=
  let RV := Limits.two_fibre_product_right_vertical gU gV xp
  let Δ := Limits.categorical_pullback_diagonal xp
  let Elegs := catPullbackCongrLegs eU.symm eV.symm
  let Eprod := sliceProdEquiv U V
  let eH := productSliceRightVerticalIso (gU := gU) (gV := gV) (xp := xp) eU eV
  (catPullbackSwap gV gU).functor ⋙
    Limits.two_fibre_product_diagonal_comparison gU gV xp ⋙
      (catPullbackCongrLeftDom Elegs RV Δ).inverse ⋙
        (catPullbackCongrLeftDom Eprod.symm (Elegs.functor ⋙ RV) Δ).inverse ⋙
          (catPullbackCongrLegs eH.symm (Iso.refl Δ)).inverse

instance productSliceDiagonalComparisonFunctor_isEquivalence
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (productSliceDiagonalComparisonFunctor (gU := gU) (gV := gV) (xp := xp) eU eV).IsEquivalence := by
  dsimp [productSliceDiagonalComparisonFunctor]
  infer_instance

/-- The product-slice diagonal comparison is compatible with the base projection to `C`: after
projecting to the product slice and forgetting `U × V`, one recovers the base projection from the
`U`-leg of the source pullback.  This packages the product formula and the domain/leg congruence
compatibilities explicitly, so later proofs do not ask definitional equality to infer it. -/
noncomputable def productSliceDiagonalComparisonFunctor_leftBaseIso
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    productSliceDiagonalComparisonFunctor (gU := gU) (gV := gV) (xp := xp) eU eV ⋙
        (π₁ (productSliceRightVerticalFunctor
            (productSliceRightVerticalBaseIso (gU := gU) (gV := gV) (xp := xp) eU eV))
          (Limits.categorical_pullback_diagonal xp) ⋙ Over.forget (Limits.prod U V)) ≅
      π₂ gV gU ⋙ Over.forget U := by
  dsimp only [productSliceDiagonalComparisonFunctor]
  let RV := Limits.two_fibre_product_right_vertical gU gV xp
  let Δ := Limits.categorical_pullback_diagonal xp
  let Elegs := catPullbackCongrLegs eU.symm eV.symm
  let Eprod := sliceProdEquiv U V
  let eH := productSliceRightVerticalIso (gU := gU) (gV := gV) (xp := xp) eU eV
  let RVps := productSliceRightVerticalFunctor
    (productSliceRightVerticalBaseIso (gU := gU) (gV := gV) (xp := xp) eU eV)
  let K1 := catPullbackCongrLeftDom Elegs RV Δ
  let K2 := catPullbackCongrLeftDom Eprod.symm (Elegs.functor ⋙ RV) Δ
  let K3 := catPullbackCongrLegs eH.symm (Iso.refl Δ)
  let pProd := Over.forget (Limits.prod U V)
  let pMid := π₁ (gU ⋙ xp) (gV ⋙ xp) ⋙ Over.forget U
  let F0 := (catPullbackSwap gV gU).functor
  let F1 := Limits.two_fibre_product_diagonal_comparison gU gV xp
  have h3 : K3.inverse ⋙ (π₁ RVps Δ ⋙ pProd) ≅
      π₁ (Eprod.symm.functor ⋙ (Elegs.functor ⋙ RV)) Δ ⋙ pProd := by
    simpa [K3, RVps, eH, Eprod, Elegs, RV, Δ, pProd, Functor.assoc] using
      (catPullbackCongrLegs_inverse_fst_baseIso eH.symm (Iso.refl Δ) pProd)
  have h2 : K2.inverse ⋙ (π₁ (Eprod.symm.functor ⋙ (Elegs.functor ⋙ RV)) Δ ⋙ pProd) ≅
      π₁ (Elegs.functor ⋙ RV) Δ ⋙ (Eprod.functor ⋙ pProd) := by
    simpa [K2, Eprod, Elegs, RV, Δ, pProd, Functor.assoc] using
      (catPullbackCongrLeftDom_inverse_fst_baseIso Eprod.symm (Elegs.functor ⋙ RV) Δ
        (Eprod.functor ⋙ pProd) pProd
        (equivalence_functor_inverse_baseIso Eprod.symm pProd))
  have hElegBase : Elegs.functor ⋙ pMid ≅ Eprod.functor ⋙ pProd := eqToIso (by rfl)
  have h1 : K1.inverse ⋙ (π₁ (Elegs.functor ⋙ RV) Δ ⋙ (Eprod.functor ⋙ pProd)) ≅
      π₁ RV Δ ⋙ pMid :=
    catPullbackCongrLeftDom_inverse_fst_baseIso Elegs RV Δ pMid (Eprod.functor ⋙ pProd)
      hElegBase
  have hdiag : F1 ⋙ (π₁ RV Δ ⋙ pMid) ≅ π₁ gU gV ⋙ Over.forget U := Iso.refl _
  have hswap : F0 ⋙ (π₁ gU gV ⋙ Over.forget U) ≅ π₂ gV gU ⋙ Over.forget U := Iso.refl _
  calc
    ((F0 ⋙ F1 ⋙ K1.inverse ⋙ K2.inverse ⋙ K3.inverse) ⋙ (π₁ RVps Δ ⋙ pProd))
        ≅ (F0 ⋙ F1 ⋙ K1.inverse ⋙ K2.inverse) ⋙
            (K3.inverse ⋙ (π₁ RVps Δ ⋙ pProd)) :=
          Functor.associator (F0 ⋙ F1 ⋙ K1.inverse ⋙ K2.inverse) K3.inverse (π₁ RVps Δ ⋙ pProd)
    _ ≅ (F0 ⋙ F1 ⋙ K1.inverse ⋙ K2.inverse) ⋙
            (π₁ (Eprod.symm.functor ⋙ (Elegs.functor ⋙ RV)) Δ ⋙ pProd) :=
          Functor.isoWhiskerLeft (F0 ⋙ F1 ⋙ K1.inverse ⋙ K2.inverse) h3
    _ ≅ (F0 ⋙ F1 ⋙ K1.inverse) ⋙
            (K2.inverse ⋙ (π₁ (Eprod.symm.functor ⋙ (Elegs.functor ⋙ RV)) Δ ⋙ pProd)) :=
          (Functor.associator (F0 ⋙ F1 ⋙ K1.inverse) K2.inverse
            (π₁ (Eprod.symm.functor ⋙ (Elegs.functor ⋙ RV)) Δ ⋙ pProd)).symm
    _ ≅ (F0 ⋙ F1 ⋙ K1.inverse) ⋙
            (π₁ (Elegs.functor ⋙ RV) Δ ⋙ (Eprod.functor ⋙ pProd)) :=
          Functor.isoWhiskerLeft (F0 ⋙ F1 ⋙ K1.inverse) h2
    _ ≅ (F0 ⋙ F1) ⋙ (K1.inverse ⋙
            (π₁ (Elegs.functor ⋙ RV) Δ ⋙ (Eprod.functor ⋙ pProd))) :=
          (Functor.associator (F0 ⋙ F1) K1.inverse
            (π₁ (Elegs.functor ⋙ RV) Δ ⋙ (Eprod.functor ⋙ pProd))).symm
    _ ≅ (F0 ⋙ F1) ⋙ (π₁ RV Δ ⋙ pMid) :=
          Functor.isoWhiskerLeft (F0 ⋙ F1) h1
    _ ≅ F0 ⋙ (F1 ⋙ (π₁ RV Δ ⋙ pMid)) :=
          Functor.associator F0 F1 (π₁ RV Δ ⋙ pMid)
    _ ≅ F0 ⋙ (π₁ gU gV ⋙ Over.forget U) :=
          Functor.isoWhiskerLeft F0 hdiag
    _ ≅ π₂ gV gU ⋙ Over.forget U := hswap

end ProductSliceRightVertical

section ProductSliceSourceRightVertical

variable [Limits.HasBinaryProducts C]
variable {U V : C}

/-- The right vertical functor associated to the product-slice source square.  This is the
`C/(U × V) -> X ×_C X` map in the Stacks proof. -/
noncomputable def productSliceSourceRightVerticalFunctor
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    Over (Limits.prod U V) ⥤ X.p ⊡ X.p :=
  productSliceRightVerticalFunctor
    (productSliceRightVerticalBaseIso
      (gU := FibredInGroupoidsMor.G G)
      (gV := FibredInGroupoidsMor.G G')
      (xp := X.p)
      (eqToIso (FibredInGroupoidsMor.comm G))
      (eqToIso (FibredInGroupoidsMor.comm G')))

/-- The raw target of `squareComparisonIso` for the product-slice source square.  Kept named so that
later projection-formula proofs do not unfold the square comparison target. -/
noncomputable def productSliceSourceSquareComparisonTarget
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    Over (Limits.prod U V) ⥤ X.p ⊡ X.p :=
  (CategoricalPullback.functorEquiv (FibredInGroupoidsMor.G X.baseProjection)
    (FibredInGroupoidsMor.G X.baseProjection)
    (ofFunctor (Over.forget (Limits.prod U V))).S).inverse.obj
    { fst := FibredInGroupoidsMor.G (slice_morphism_pullback X Limits.prod.fst G)
      snd := FibredInGroupoidsMor.G (slice_morphism_pullback X Limits.prod.snd G')
      iso := ownerIsoToFunctorIso (product_slice_pullbacks_base_projection_iso_explicit X G G') }

/-- The raw square-comparison target is the explicit right vertical functor. -/
noncomputable def productSliceSourceSquareComparisonTargetIso
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    productSliceSourceSquareComparisonTarget X G G' ≅
      productSliceSourceRightVerticalFunctor X G G' := by
  dsimp [productSliceSourceSquareComparisonTarget, productSliceSourceRightVerticalFunctor,
    productSliceRightVerticalFunctor, productSliceSourceSquare, slice_morphism_pullback, over_map_morphism]
  rw [ownerIsoToFunctorIso_product_slice_pullbacks_base_projection_iso_explicit]
  rfl

/-- The product-slice source square comparison after the Remark 4.35.8 equivalence.  This packages the
over-base compatibility needed in Lemma 4.42.6 `(1) -> (2)`. -/
noncomputable def productSliceSourceSquareComparisonIsoRaw
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (uH : productSliceSourceSquare X G G' ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    FibredInGroupoidsMor.G uH.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      productSliceSourceSquareComparisonTarget X G G' :=
  squareComparisonIso X (productSliceSourceSquare X G G') uH

/-- The product-slice source square comparison with the explicit right vertical functor as target. -/
noncomputable def productSliceSourceSquareComparisonIso
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (uH : productSliceSourceSquare X G G' ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    FibredInGroupoidsMor.G uH.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      productSliceSourceRightVerticalFunctor X G G' :=
  productSliceSourceSquareComparisonIsoRaw X G G' uH ≪≫
    productSliceSourceSquareComparisonTargetIso X G G'

/-- The total-category equivalence behind Lemma 4.42.6 `(1) -> (2)`, with the
terminal factorizations supplied as opaque square morphisms. -/
noncomputable def productSliceDiagonalBasechangeTotalEquiv
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (uH : productSliceSourceSquare X G G' ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct G' G).S ≌
      (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).S := by
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  let eU : FibredInGroupoidsMor.G G ⋙ X.p ≅ Over.forget U :=
    eqToIso (FibredInGroupoidsMor.comm G)
  let eV : FibredInGroupoidsMor.G G' ⋙ X.p ≅ Over.forget V :=
    eqToIso (FibredInGroupoidsMor.comm G')
  let RV := productSliceSourceRightVerticalFunctor X G G'
  let Δ := Limits.categorical_pullback_diagonal X.p
  let isoH : (FibredInGroupoidsMor.G uH.hom ⋙ eDT.functor) ≅ RV :=
    productSliceSourceSquareComparisonIso X G G' uH
  let isoD : (FibredInGroupoidsMor.G uDg.hom ⋙ eDT.functor) ≅ Δ :=
    diagonalSourceSquareComparisonIso X uDg
  let eSource : (FibredInGroupoidsOver.twoFibreProduct G' G).S ≌
      (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) :=
    twoFibreProductEquivCatPullback G' G
  let eDiag : (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) ≌ RV ⊡ Δ :=
    (productSliceDiagonalComparisonFunctor (gU := FibredInGroupoidsMor.G G)
      (gV := FibredInGroupoidsMor.G G') (xp := X.p) eU eV).asEquivalence
  let eLegs : ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
      ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ≌ RV ⊡ Δ :=
    catPullbackCongrLegs isoH isoD
  let eBase : (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) ≌
      ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
        ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) :=
    catPullbackCongrBase (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) eDT
  let eTarget : (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).S ≌
      (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) :=
    twoFibreProductEquivCatPullback uH.hom uDg.hom
  exact eSource.trans (eDiag.trans (eLegs.symm.trans (eBase.symm.trans eTarget.symm)))

/-- The forward functor behind the product-slice/diagonal base-change equivalence.  Naming this
separately keeps projection-formula statements from unfolding the whole `Equivalence.trans` chain. -/
noncomputable def productSliceDiagonalBasechangeFunctor
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (uH : productSliceSourceSquare X G G' ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct G' G).S ⥤
      (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).S :=
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  let eU : FibredInGroupoidsMor.G G ⋙ X.p ≅ Over.forget U :=
    eqToIso (FibredInGroupoidsMor.comm G)
  let eV : FibredInGroupoidsMor.G G' ⋙ X.p ≅ Over.forget V :=
    eqToIso (FibredInGroupoidsMor.comm G')
  let RV := productSliceSourceRightVerticalFunctor X G G'
  let Δ := Limits.categorical_pullback_diagonal X.p
  let isoH : (FibredInGroupoidsMor.G uH.hom ⋙ eDT.functor) ≅ RV :=
    productSliceSourceSquareComparisonIso X G G' uH
  let isoD : (FibredInGroupoidsMor.G uDg.hom ⋙ eDT.functor) ≅ Δ :=
    diagonalSourceSquareComparisonIso X uDg
  let eSource : (FibredInGroupoidsOver.twoFibreProduct G' G).S ≌
      (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) :=
    twoFibreProductEquivCatPullback G' G
  let eDiag : (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) ≌ RV ⊡ Δ :=
    (productSliceDiagonalComparisonFunctor (gU := FibredInGroupoidsMor.G G)
      (gV := FibredInGroupoidsMor.G G') (xp := X.p) eU eV).asEquivalence
  let eLegs : ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
      ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ≌ RV ⊡ Δ :=
    catPullbackCongrLegs isoH isoD
  let eBase : (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) ≌
      ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
        ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) :=
    catPullbackCongrBase (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) eDT
  let eTarget : (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).S ≌
      (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) :=
    twoFibreProductEquivCatPullback uH.hom uDg.hom
  eSource.functor ⋙ (eDiag.functor ⋙ (eLegs.inverse ⋙ (eBase.inverse ⋙ eTarget.inverse)))

/-- Transport representability across the product-slice/diagonal base-change comparison. -/
noncomputable def productSliceDiagonalBasechange_representabilityTransport
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (uH : productSliceSourceSquare X G G' ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct G' G).IsRepresentable := by
  intro hRep
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  let eU : FibredInGroupoidsMor.G G ⋙ X.p ≅ Over.forget U :=
    eqToIso (FibredInGroupoidsMor.comm G)
  let eV : FibredInGroupoidsMor.G G' ⋙ X.p ≅ Over.forget V :=
    eqToIso (FibredInGroupoidsMor.comm G')
  let RV := productSliceSourceRightVerticalFunctor X G G'
  let Δ := Limits.categorical_pullback_diagonal X.p
  let isoH : (FibredInGroupoidsMor.G uH.hom ⋙ eDT.functor) ≅ RV :=
    productSliceSourceSquareComparisonIso X G G' uH
  let isoD : (FibredInGroupoidsMor.G uDg.hom ⋙ eDT.functor) ≅ Δ :=
    diagonalSourceSquareComparisonIso X uDg
  let eSource : (FibredInGroupoidsOver.twoFibreProduct G' G).S ≌
      (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) :=
    twoFibreProductEquivCatPullback G' G
  let eDiag : (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) ≌ RV ⊡ Δ :=
    (productSliceDiagonalComparisonFunctor (gU := FibredInGroupoidsMor.G G)
      (gV := FibredInGroupoidsMor.G G') (xp := X.p) eU eV).asEquivalence
  let eLegs : ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
      ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ≌ RV ⊡ Δ :=
    catPullbackCongrLegs isoH isoD
  let eBase : (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) ≌
      ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
        ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) :=
    catPullbackCongrBase (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) eDT
  let eTarget : (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).S ≌
      (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) :=
    twoFibreProductEquivCatPullback uH.hom uDg.hom
  let source := FibredInGroupoidsOver.twoFibreProduct G' G
  let target := FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom
  let pProd := (productSliceSourceSquare X G G').obj.p
  have hTarget : eTarget.inverse ⋙ target.p ≅
      π₁ (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) ⋙ pProd := by
    simpa [eTarget, target, pProd] using
      (productSliceSource_twoFibreProductEquiv_inverse_baseIso_left X G G' uH.hom uDg.hom)
  have hBase : eBase.inverse ⋙
        (π₁ (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) ⋙ pProd) ≅
      π₁ ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor)
          ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ⋙ pProd :=
    catPullbackCongrBase_inverse_fst_baseIso
      (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) eDT pProd
  have hLegs : eLegs.inverse ⋙
        (π₁ ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor)
          ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ⋙ pProd) ≅
      π₁ RV Δ ⋙ pProd :=
    catPullbackCongrLegs_inverse_fst_baseIso isoH isoD pProd
  have hDiag : eDiag.functor ⋙ (π₁ RV Δ ⋙ pProd) ≅
      π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U := by
    change eDiag.functor ⋙ (π₁ RV Δ ⋙ Over.forget (Limits.prod U V)) ≅
      π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U
    simpa [eDiag, RV, productSliceSourceRightVerticalFunctor, Δ] using
      (productSliceDiagonalComparisonFunctor_leftBaseIso
        (gU := FibredInGroupoidsMor.G G) (gV := FibredInGroupoidsMor.G G') (xp := X.p) eU eV)
  have hSource : eSource.functor ⋙
        (π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U) ≅ source.p := by
    simpa [eSource, source] using
      (twoFibreProductEquivCatPullback_functor_baseIso_right G' G)
  exact isRepresentable_of_total_equivalence_transportData
    (functorCompBaseIso5_transportData (P := source) (Q := target)
      eSource.functor eDiag.functor eLegs.inverse eBase.inverse eTarget.inverse
      (π₁ (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) ⋙ pProd)
      (π₁ ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor)
        ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ⋙ pProd)
      (π₁ RV Δ ⋙ pProd)
      (π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U)
      hTarget hBase hLegs hDiag hSource) hRep

/-- Reverse transport across the product-slice/diagonal base-change comparison.  This is the same
Stacks projection formula as `productSliceDiagonalBasechange_representabilityTransport`, but with the
five equivalence steps traversed in the opposite direction. -/
noncomputable def productSliceDiagonalBasechange_representabilityTransport_reverse
    (X : FibredInGroupoidsOver C)
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X)
    (uH : productSliceSourceSquare X G G' ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct G' G).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).IsRepresentable := by
  intro hRep
  let eDT := twoFibreProductEquivCatPullback X.baseProjection X.baseProjection
  let eU : FibredInGroupoidsMor.G G ⋙ X.p ≅ Over.forget U :=
    eqToIso (FibredInGroupoidsMor.comm G)
  let eV : FibredInGroupoidsMor.G G' ⋙ X.p ≅ Over.forget V :=
    eqToIso (FibredInGroupoidsMor.comm G')
  let RV := productSliceSourceRightVerticalFunctor X G G'
  let Δ := Limits.categorical_pullback_diagonal X.p
  let isoH : (FibredInGroupoidsMor.G uH.hom ⋙ eDT.functor) ≅ RV :=
    productSliceSourceSquareComparisonIso X G G' uH
  let isoD : (FibredInGroupoidsMor.G uDg.hom ⋙ eDT.functor) ≅ Δ :=
    diagonalSourceSquareComparisonIso X uDg
  let eSource : (FibredInGroupoidsOver.twoFibreProduct G' G).S ≌
      (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) :=
    twoFibreProductEquivCatPullback G' G
  let eDiag : (FibredInGroupoidsMor.G G') ⊡ (FibredInGroupoidsMor.G G) ≌ RV ⊡ Δ :=
    (productSliceDiagonalComparisonFunctor (gU := FibredInGroupoidsMor.G G)
      (gV := FibredInGroupoidsMor.G G') (xp := X.p) eU eV).asEquivalence
  let eLegs : ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
      ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ≌ RV ⊡ Δ :=
    catPullbackCongrLegs isoH isoD
  let eBase : (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) ≌
      ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor) ⊡
        ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) :=
    catPullbackCongrBase (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) eDT
  let eTarget : (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).S ≌
      (FibredInGroupoidsMor.G uH.hom) ⊡ (FibredInGroupoidsMor.G uDg.hom) :=
    twoFibreProductEquivCatPullback uH.hom uDg.hom
  let source := FibredInGroupoidsOver.twoFibreProduct G' G
  let target := FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom
  let pProd := (productSliceSourceSquare X G G').obj.p
  have hSource : eSource.inverse ⋙ source.p ≅
      π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U := by
    simpa [eSource, source] using
      (twoFibreProductEquivCatPullback_inverse_baseIso_right G' G)
  have hDiagForward : eDiag.functor ⋙ (π₁ RV Δ ⋙ pProd) ≅
      π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U := by
    change eDiag.functor ⋙ (π₁ RV Δ ⋙ Over.forget (Limits.prod U V)) ≅
      π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U
    simpa [eDiag, RV, productSliceSourceRightVerticalFunctor, Δ] using
      (productSliceDiagonalComparisonFunctor_leftBaseIso
        (gU := FibredInGroupoidsMor.G G) (gV := FibredInGroupoidsMor.G G') (xp := X.p) eU eV)
  have hDiag : eDiag.inverse ⋙
        (π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U) ≅
      π₁ RV Δ ⋙ pProd :=
    equivalence_inverse_baseIso eDiag
      (π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U)
      (π₁ RV Δ ⋙ pProd) hDiagForward
  have hLegs : eLegs.functor ⋙ (π₁ RV Δ ⋙ pProd) ≅
      π₁ ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor)
          ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ⋙ pProd :=
    catPullbackCongrLegs_functor_fst_baseIso isoH isoD pProd
  have hBase : eBase.functor ⋙
        (π₁ ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor)
          ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ⋙ pProd) ≅
      π₁ (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) ⋙ pProd :=
    catPullbackCongrBase_functor_fst_baseIso
      (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) eDT pProd
  have hTarget : eTarget.functor ⋙
        (π₁ (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) ⋙ pProd) ≅ target.p := by
    simpa [eTarget, target, pProd] using
      (twoFibreProductEquivCatPullback_functor_baseIso_left uH.hom uDg.hom)
  exact isRepresentable_of_total_equivalence_transportData
    (functorCompBaseIso5_transportData (P := target) (Q := source)
      eTarget.functor eBase.functor eLegs.functor eDiag.inverse eSource.inverse
      (π₂ (FibredInGroupoidsMor.G G') (FibredInGroupoidsMor.G G) ⋙ Over.forget U)
      (π₁ RV Δ ⋙ pProd)
      (π₁ ((FibredInGroupoidsMor.G uH.hom) ⋙ eDT.functor)
        ((FibredInGroupoidsMor.G uDg.hom) ⋙ eDT.functor) ⋙ pProd)
      (π₁ (FibredInGroupoidsMor.G uH.hom) (FibredInGroupoidsMor.G uDg.hom) ⋙ pProd)
      hSource hDiag hLegs hBase hTarget) hRep

omit [HasBinaryProducts C] in
/-- Canonical diagonal-base-change step in Lemma 4.42.6 `(2) -> (1)`: after replacing the product
pullback by the product-slice/diagonal comparison, base-change it along the diagonal
`W -> W × W`. -/
opaque canonical_diagonal_basechange_representable_of_product
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C) {W : C}
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (uH : productSliceSourceSquare X L R ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (hprodLR : (FibredInGroupoidsOver.twoFibreProduct R L).IsRepresentable) :
    (FibredInGroupoidsOver.twoFibreProduct
      (FibredInGroupoidsOver.overMap (Limits.prod.lift (𝟙 W) (𝟙 W) : W ⟶ Limits.prod W W) ≫
        uH.hom)
      uDg.hom).IsRepresentable := by
  have hcanonProd : (FibredInGroupoidsOver.twoFibreProduct uH.hom uDg.hom).IsRepresentable :=
    productSliceDiagonalBasechange_representabilityTransport_reverse X L R uH uDg hprodLR
  let J := FibredInGroupoidsOver.twoFibreProductLeftProjection uH.hom uDg.hom
  let δ : W ⟶ Limits.prod W W := Limits.prod.lift (𝟙 W) (𝟙 W)
  have hbase :
      (FibredInGroupoidsOver.twoFibreProduct (FibredInGroupoidsOver.overMap δ) J).IsRepresentable :=
    twoFibreProduct_overMap_representable_of_representable J δ hcanonProd
  exact twoFibreProduct_leftProjection_representable_transport
    (FibredInGroupoidsOver.overMap δ) uH.hom uDg.hom hbase

end ProductSliceSourceRightVertical

end CategoryTheory
