module

public import stacks_project.Chap04.Lemma_4_35_7
public import stacks_project.Chap04.Remark_4_35_8

@[expose] public section

/-!
# Product-of-slices (pasting support for Lemma 4.42.6)

The bundled diagonal-pasting law needed to close the two remaining cores of Lemma 4.42.6
(`Direction1`/`Direction2`) rests on the Stacks identification `C/U × C/V ≅ C/(U ⨯ V)`. This file
provides that identification at the categorical-pullback (`⊡`) level — the form in which it feeds
through `Remark_4_35_8.explicitTwoFibreProduct_equiv_categoricalPullback` and the groupoid-free
diagonal pasting `Remark_4_31_5.symmetricTwoFibreProductComparison_isEquivalence`.

`sliceProdEquiv U V : (Over.forget U) ⊡ (Over.forget V) ≌ Over (U ⨯ V)` is a self-contained,
axiom-clean equivalence: an object of the categorical pullback of the two slice forgetful functors
is `(a : Over U, b : Over V, a.left ≅ b.left)`, which `prod.lift` packages into a single arrow
`a.left ⟶ U ⨯ V`, and conversely a slice over `U ⨯ V` projects to the two factors.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback

universe v u

namespace CategoryTheory

namespace Over

section MapFormulae

variable {T : Type u} [Category.{v} T] {X Y : T}

/-- Object formula for the slice postcomposition functor. -/
@[simp] theorem map_obj_eq (f : X ⟶ Y) (c : Over X) :
    (Over.map f).obj c = Over.mk (c.hom ≫ f) :=
  rfl

/-- Morphism formula for the slice postcomposition functor. -/
@[simp] theorem map_map_eq (f : X ⟶ Y) {c d : Over X} (g : c ⟶ d) :
    (Over.map f).map g =
      Over.homMk (U := Over.mk (c.hom ≫ f)) (V := Over.mk (d.hom ≫ f)) g.left
        (by simpa [Category.assoc] using congrArg (fun t => t ≫ f) (Over.w g)) := by
  apply Over.OverMorphism.ext
  rfl

/-- Identity formula for morphisms built with Over.homMk. -/
@[simp] theorem homMk_id {X : T} (c : Over X)
    (h : 𝟙 c.left ≫ c.hom = c.hom := by simp) :
    (Over.homMk (U := c) (V := c) (𝟙 c.left) h) = 𝟙 c := by
  apply Over.OverMorphism.ext
  simp

/-- The slice postcomposition functor preserves identity morphisms, with the target kept explicit.
This prevents later simplification proofs from unfolding the identity case to a raw Over.homMk. -/
@[simp high] theorem map_map_id (f : X ⟶ Y) (c : Over X) :
    (Over.map f).map (𝟙 c) = 𝟙 ((Over.map f).obj c) :=
  (Over.map f).map_id c

/-- The slice postcomposition functor preserves composition, with the intermediate objects kept
explicit. -/
@[simp high] theorem map_map_comp (f : X ⟶ Y) {c d e : Over X} (g : c ⟶ d) (h : d ⟶ e) :
    (Over.map f).map (g ≫ h) = (Over.map f).map g ≫ (Over.map f).map h :=
  (Over.map f).map_comp g h

attribute [simp] homMk_comp

end MapFormulae

end Over

/-! ### Equivalence-invariance of the categorical pullback `⊡`

Mathlib lists "Full equivalence-invariance of the notion (follows from suitable 2-functoriality)"
of `CategoricalPullback` as a TODO. The two congruences below are the special cases needed for the
diagonal-pasting law of Lemma 4.42.6: invariance under postcomposing both legs with an equivalence
of the common base, and invariance under natural isomorphisms of the two legs. Both are proved
directly on the explicit `(a, b, F a ≅ G b)` model. -/

section CatPullbackCongr

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Postcomposing both legs of a categorical pullback with a functor `K` of the common base induces
a functor `F ⊡ G ⥤ (F ⋙ K) ⊡ (G ⋙ K)` by applying `K` to the structural isomorphism. -/
@[simps obj_fst obj_snd map_fst map_snd]
noncomputable def catPullbackMapBase (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (K : D₀ ⥤ D₀') :
    F ⊡ G ⥤ (F ⋙ K) ⊡ (G ⋙ K) where
  obj x :=
    { fst := x.fst
      snd := x.snd
      iso := K.mapIso x.iso }
  map {x y} f :=
    { fst := f.fst
      snd := f.snd
      w := by
        dsimp only [Functor.comp_obj, Functor.comp_map, Functor.mapIso_hom]
        rw [← K.map_comp, ← K.map_comp, f.w] }

instance (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) {D₀' : Type*} [Category D₀'] (K : D₀ ⥤ D₀') :
    (catPullbackMapBase F G K).Faithful where
  map_injective h := by
    apply CategoricalPullback.hom_ext
    · exact congrArg (fun t => t.fst) h
    · exact congrArg (fun t => t.snd) h

instance (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) {D₀' : Type*} [Category D₀'] (K : D₀ ⥤ D₀')
    [K.Full] [K.Faithful] :
    (catPullbackMapBase F G K).Full where
  map_surjective {x y} g := by
    refine ⟨{ fst := g.fst, snd := g.snd, w := ?_ }, ?_⟩
    · apply K.map_injective
      have hg := g.w
      simp only at hg ⊢
      simpa [Functor.map_comp] using hg
    · apply CategoricalPullback.hom_ext <;> rfl

instance (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) {D₀' : Type*} [Category D₀'] (K : D₀ ⥤ D₀')
    [K.EssSurj] [K.Full] [K.Faithful] :
    (catPullbackMapBase F G K).EssSurj where
  mem_essImage y := by
    refine ⟨{ fst := y.fst, snd := y.snd, iso := K.preimageIso y.iso }, ⟨?_⟩⟩
    refine CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) ?_
    dsimp [catPullbackMapBase]
    simp

instance (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) {D₀' : Type*} [Category D₀'] (K : D₀ ⥤ D₀')
    [K.EssSurj] [K.Full] [K.Faithful] :
    (catPullbackMapBase F G K).IsEquivalence where

/-- The categorical pullback is invariant under postcomposing both legs with an equivalence of the
common base. -/
noncomputable def catPullbackCongrBase (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    F ⊡ G ≌ (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor) :=
  (catPullbackMapBase F G eB.functor).asEquivalence

/-- The forward functor of `catPullbackCongrBase` is compatible with the left projection,
after composing that projection with any base functor on the left domain. -/
noncomputable def catPullbackCongrBase_functor_fst_baseIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' E₀ : Type*} [Category D₀'] [Category E₀]
    (eB : D₀ ≌ D₀') (pA : A₀ ⥤ E₀) :
    (catPullbackCongrBase F G eB).functor ⋙
        (π₁ (F ⋙ eB.functor) (G ⋙ eB.functor) ⋙ pA) ≅
      π₁ F G ⋙ pA :=
  Iso.refl _

/-- The inverse of `catPullbackCongrBase` is compatible with the left projection, after composing
that projection with any base functor on the left domain. -/
noncomputable def catPullbackCongrBase_inverse_fst_baseIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' E₀ : Type*} [Category D₀'] [Category E₀]
    (eB : D₀ ≌ D₀') (pA : A₀ ⥤ E₀) :
    (catPullbackCongrBase F G eB).inverse ⋙ (π₁ F G ⋙ pA) ≅
      π₁ (F ⋙ eB.functor) (G ⋙ eB.functor) ⋙ pA :=
  equivalence_inverse_baseIso (catPullbackCongrBase F G eB)
    (π₁ F G ⋙ pA) (π₁ (F ⋙ eB.functor) (G ⋙ eB.functor) ⋙ pA) (Iso.refl _)

/-- Natural isomorphisms of both legs induce a functor `F ⊡ G ⥤ F' ⊡ G'`. -/
@[simps obj_fst obj_snd map_fst map_snd]
noncomputable def catPullbackMapLegs {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    F ⊡ G ⥤ F' ⊡ G' where
  obj x :=
    { fst := x.fst
      snd := x.snd
      iso := (eF.app x.fst).symm ≪≫ x.iso ≪≫ eG.app x.snd }
  map {x y} f :=
    { fst := f.fst
      snd := f.snd
      w := by
        dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom]
        have hnatF : F'.map f.fst ≫ eF.inv.app y.fst = eF.inv.app x.fst ≫ F.map f.fst :=
          eF.inv.naturality f.fst
        have hnatG : G.map f.snd ≫ eG.hom.app y.snd = eG.hom.app x.snd ≫ G'.map f.snd :=
          eG.hom.naturality f.snd
        rw [← Category.assoc, hnatF, Category.assoc, Category.assoc]
        rw [← Category.assoc (F.map f.fst), f.w, Category.assoc, Category.assoc, hnatG] }

/-- The structural isomorphism stored by catPullbackMapLegs, in the forward direction. -/
@[simp] theorem catPullbackMapLegs_obj_iso_hom
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((catPullbackMapLegs eF eG).obj x).iso.hom =
      (eF.app x.fst).inv ≫ x.iso.hom ≫ (eG.app x.snd).hom :=
  rfl

/-- The structural isomorphism stored by catPullbackMapLegs, in the inverse direction. -/
@[simp] theorem catPullbackMapLegs_obj_iso_inv
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((catPullbackMapLegs eF eG).obj x).iso.inv =
      (eG.app x.snd).inv ≫ x.iso.inv ≫ (eF.app x.fst).hom := by
  simp [catPullbackMapLegs]

/-- The categorical pullback is invariant under natural isomorphisms of the two legs. -/
noncomputable def catPullbackCongrLegs {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    F ⊡ G ≌ F' ⊡ G' where
  functor := catPullbackMapLegs eF eG
  inverse := catPullbackMapLegs eF.symm eG.symm
  unitIso := NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      dsimp [catPullbackMapLegs]; simp))
    (by intro x y f; apply CategoricalPullback.hom_ext <;> simp [catPullbackMapLegs])
  counitIso := NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      dsimp [catPullbackMapLegs]; simp))
    (by intro x y f; apply CategoricalPullback.hom_ext <;> simp [catPullbackMapLegs])

/-- The forward functor of `catPullbackCongrLegs` is compatible with the left projection,
after composing that projection with any base functor on the left domain. -/
noncomputable def catPullbackCongrLegs_functor_fst_baseIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} {E₀ : Type*} [Category E₀]
    (eF : F ≅ F') (eG : G ≅ G') (pA : A₀ ⥤ E₀) :
    (catPullbackCongrLegs eF eG).functor ⋙ (π₁ F' G' ⋙ pA) ≅
      π₁ F G ⋙ pA :=
  Iso.refl _

/-- The inverse of `catPullbackCongrLegs` is compatible with the left projection, after composing
that projection with any base functor on the left domain. -/
noncomputable def catPullbackCongrLegs_inverse_fst_baseIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} {E₀ : Type*} [Category E₀]
    (eF : F ≅ F') (eG : G ≅ G') (pA : A₀ ⥤ E₀) :
    (catPullbackCongrLegs eF eG).inverse ⋙ (π₁ F G ⋙ pA) ≅
      π₁ F' G' ⋙ pA :=
  equivalence_inverse_baseIso (catPullbackCongrLegs eF eG)
    (π₁ F G ⋙ pA) (π₁ F' G' ⋙ pA) (Iso.refl _)

/-- The forward functor of `catPullbackCongrLegs` is compatible with the right projection,
after composing that projection with any base functor on the right domain. -/
noncomputable def catPullbackCongrLegs_functor_snd_baseIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} {E₀ : Type*} [Category E₀]
    (eF : F ≅ F') (eG : G ≅ G') (pB : B₀ ⥤ E₀) :
    (catPullbackCongrLegs eF eG).functor ⋙ (π₂ F' G' ⋙ pB) ≅
      π₂ F G ⋙ pB :=
  Iso.refl _

/-- The inverse of `catPullbackCongrLegs` is compatible with the right projection, after composing
that projection with any base functor on the right domain. -/
noncomputable def catPullbackCongrLegs_inverse_snd_baseIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} {E₀ : Type*} [Category E₀]
    (eF : F ≅ F') (eG : G ≅ G') (pB : B₀ ⥤ E₀) :
    (catPullbackCongrLegs eF eG).inverse ⋙ (π₂ F G ⋙ pB) ≅
      π₂ F' G' ⋙ pB :=
  equivalence_inverse_baseIso (catPullbackCongrLegs eF eG)
    (π₂ F G ⋙ pB) (π₂ F' G' ⋙ pB) (Iso.refl _)

end CatPullbackCongr

/-- The underlying-functor isomorphism induced by a `2`-cell isomorphism of morphisms of categories
fibred in groupoids over `C`. -/
noncomputable def ownerIsoToFunctorIso {C : Type u} [Category.{v} C]
    {X Y : FibredInGroupoidsOver C} {f g : X ⟶ Y} (α : f ≅ g) :
    FibredInGroupoidsMor.G f ≅ FibredInGroupoidsMor.G g :=
  (BasedNatTrans.forgetful X.toBasedCategory Y.toBasedCategory).mapIso
    (FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso α)

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- Forward functor of the product-of-slices equivalence: package the two slice arrows and the
structural isomorphism into a single arrow to `U ⨯ V`. -/
@[simps]
noncomputable def sliceProdToProdSlice (U V : C) :
    (Over.forget U) ⊡ (Over.forget V) ⥤ Over (Limits.prod U V) where
  obj x := Over.mk (Limits.prod.lift x.fst.hom (x.iso.hom ≫ x.snd.hom))
  map {x y} f := Over.homMk f.fst.left (by
    have hw : f.fst.left ≫ y.iso.hom = x.iso.hom ≫ f.snd.left := f.w
    apply Limits.prod.hom_ext
    · simpa [Limits.prod.lift_fst] using Over.w f.fst
    · have hsnd : f.fst.left ≫ y.iso.hom ≫ y.snd.hom = x.iso.hom ≫ x.snd.hom := by
        rw [reassoc_of% hw]
        exact (Category.assoc _ _ _).trans (congrArg (x.iso.hom ≫ ·) (Over.w f.snd))
      simpa [Limits.prod.lift_snd] using hsnd)

/-- Inverse functor of the product-of-slices equivalence: a slice over `U ⨯ V` projects to its two
factors with the identity structural isomorphism. -/
@[simps]
noncomputable def prodSliceToSliceProd (U V : C) :
    Over (Limits.prod U V) ⥤ (Over.forget U) ⊡ (Over.forget V) where
  obj c :=
    { fst := Over.mk (c.hom ≫ Limits.prod.fst)
      snd := Over.mk (c.hom ≫ Limits.prod.snd)
      iso := Iso.refl c.left }
  map {c d} g :=
    { fst := Over.homMk g.left (by simpa using Over.w g =≫ Limits.prod.fst)
      snd := Over.homMk g.left (by simpa using Over.w g =≫ Limits.prod.snd) }

/-- The product-of-slices equivalence `C/U ×_C C/V ≅ C/(U ⨯ V)` in categorical-pullback form. -/
noncomputable def sliceProdEquiv (U V : C) :
    (Over.forget U) ⊡ (Over.forget V) ≌ Over (Limits.prod U V) where
  functor := sliceProdToProdSlice U V
  inverse := prodSliceToSliceProd U V
  unitIso := NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso
      (Over.isoMk (Iso.refl x.fst.left) (by simp [Limits.prod.lift_fst]))
      (Over.isoMk x.iso.symm (by simp [Limits.prod.lift_snd]))
      (by simp))
    (by intro x y f
        apply CategoricalPullback.hom_ext
        · apply Over.OverMorphism.ext; simp
        · apply Over.OverMorphism.ext; simpa using f.w')
  counitIso := NatIso.ofComponents
    (fun c => Over.isoMk (Iso.refl c.left)
      (by simp [← Limits.prod.comp_lift, Limits.prod.lift_fst_snd]))
    (by intro c d g; apply Over.OverMorphism.ext; simp)

/-! ### Remark 4.35.8 bridge for the bundled two-fibre product

`(FibredInGroupoidsOver.twoFibreProduct F G).S` is definitionally the explicit pullback
`(explicitTwoFibreProduct F.toBasedFunctor G.toBasedFunctor).obj`, so Remark 4.35.8 applies
directly to identify it with the ordinary categorical pullback of the underlying functors. -/

variable {X Y S : FibredInGroupoidsOver C}

/-- The bundled two-fibre product `F ×_S G` has total category equivalent to the categorical
pullback `F.G ⊡ G.G` of the underlying functors (Remark 4.35.8, applied to the bundled product). -/
noncomputable def twoFibreProductEquivCatPullback (F : X ⟶ S) (G : Y ⟶ S) :
    (FibredInGroupoidsOver.twoFibreProduct F G).S ≌
      (FibredInGroupoidsMor.toBasedFunctor F).toFunctor ⊡
        (FibredInGroupoidsMor.toBasedFunctor G).toFunctor :=
  explicitTwoFibreProduct_equiv_categoricalPullback
    (FibredInGroupoidsMor.toBasedFunctor F) (FibredInGroupoidsMor.toBasedFunctor G)

/-- Forward left-projection base compatibility for the bundled Remark-4.35.8 bridge. -/
noncomputable def twoFibreProductEquivCatPullback_functor_baseIso_left
    (F : X ⟶ S) (G : Y ⟶ S) :
    (twoFibreProductEquivCatPullback F G).functor ⋙
        (π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ⋙ X.p) ≅
      (FibredInGroupoidsOver.twoFibreProduct F G).p := by
  haveI : IsFibredInGroupoids X.p := X.property
  haveI : IsFibredInGroupoids Y.p := Y.property
  haveI : IsFibredInGroupoids S.p := S.property
  simpa [twoFibreProductEquivCatPullback] using
    (explicitTwoFibreProduct_equiv_categoricalPullback_functor_baseIso_left
      (FibredInGroupoidsMor.toBasedFunctor F)
      (FibredInGroupoidsMor.toBasedFunctor G))

/-- Forward right-projection base compatibility for the bundled Remark-4.35.8 bridge. -/
noncomputable def twoFibreProductEquivCatPullback_functor_baseIso_right
    (F : X ⟶ S) (G : Y ⟶ S) :
    (twoFibreProductEquivCatPullback F G).functor ⋙
        (π₂ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ⋙ Y.p) ≅
      (FibredInGroupoidsOver.twoFibreProduct F G).p := by
  haveI : IsFibredInGroupoids X.p := X.property
  haveI : IsFibredInGroupoids Y.p := Y.property
  haveI : IsFibredInGroupoids S.p := S.property
  simpa [twoFibreProductEquivCatPullback] using
    (explicitTwoFibreProduct_equiv_categoricalPullback_functor_baseIso_right
      (FibredInGroupoidsMor.toBasedFunctor F)
      (FibredInGroupoidsMor.toBasedFunctor G))

/-- Inverse left-projection base compatibility for the bundled Remark-4.35.8 bridge. -/
noncomputable def twoFibreProductEquivCatPullback_inverse_baseIso_left
    (F : X ⟶ S) (G : Y ⟶ S) :
    (twoFibreProductEquivCatPullback F G).inverse ⋙
        (FibredInGroupoidsOver.twoFibreProduct F G).p ≅
      π₁ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ⋙ X.p := by
  haveI : IsFibredInGroupoids X.p := X.property
  haveI : IsFibredInGroupoids Y.p := Y.property
  haveI : IsFibredInGroupoids S.p := S.property
  simpa [twoFibreProductEquivCatPullback] using
    (explicitTwoFibreProduct_equiv_categoricalPullback_inverse_baseIso_left
      (FibredInGroupoidsMor.toBasedFunctor F)
      (FibredInGroupoidsMor.toBasedFunctor G))

/-- Inverse right-projection base compatibility for the bundled Remark-4.35.8 bridge. -/
noncomputable def twoFibreProductEquivCatPullback_inverse_baseIso_right
    (F : X ⟶ S) (G : Y ⟶ S) :
    (twoFibreProductEquivCatPullback F G).inverse ⋙
        (FibredInGroupoidsOver.twoFibreProduct F G).p ≅
      π₂ (FibredInGroupoidsMor.G F) (FibredInGroupoidsMor.G G) ⋙ Y.p := by
  haveI : IsFibredInGroupoids X.p := X.property
  haveI : IsFibredInGroupoids Y.p := Y.property
  haveI : IsFibredInGroupoids S.p := S.property
  simpa [twoFibreProductEquivCatPullback] using
    (explicitTwoFibreProduct_equiv_categoricalPullback_inverse_baseIso_right
      (FibredInGroupoidsMor.toBasedFunctor F)
      (FibredInGroupoidsMor.toBasedFunctor G))

end CategoryTheory
