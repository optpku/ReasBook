module

public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Definition_4_39_2
public import stacks_project.Chap04.Lemma_4_35_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ v₁

namespace CategoryTheory

open FibredInGroupoidsOver
open FibredInGroupoidsMor
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]

/- Domain-style sampling for Lemma 4.40.3:
- primary domain: morphisms between representable categories fibred in groupoids over a fixed base
  and their description through slice categories;
- sampled owner-level declarations:
  `FibredInGroupoidsOver.ofFunctor`,
  `FibredInGroupoidsMor`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence`;
- best owner abstraction: the bundled chapter owner `FibredInGroupoidsOver C`, with morphisms
  expressed by `FibredInGroupoidsMor`;
- primitive data: only the represented fibred-groupoid objects and the chosen equivalences over
  `C` to slice projections;
- derived API: the source-facing predicate `FibredInGroupoidsMor.InducesHom`, together with the
  quotient-level equivalence on `2`-isomorphism classes of morphisms and its slice
  specialization.

Source/core/bridge triage:
- `source-facing`: Lemma 4.40.3 for represented fibred groupoids and its slice specialization;
- `core/canonical`: `FibredInGroupoidsOver`, `FibredInGroupoidsMor`,
  `BasedFunctor.IsEquivalenceOverBase`;
- `bridge/view`: the internal transport from a represented fibred groupoid to the slice model
  `Over.forget X`.

The refinement therefore keeps the slice transport machinery private, but moves the public API to
the owner-level morphism type `FibredInGroupoidsMor` instead of repeating raw
`BasedCategory.ofFunctor ... ⥤ᵇ ...` types.
-/

namespace FibredInGroupoidsOver

/-- The canonical morphism `C/X ⟶ C/Y` over `C` induced by postcomposition with
`φ : X ⟶ Y`. This is the owner-level bridge from `Over.map φ` to the chapter's morphism type
`FibredInGroupoidsMor`. -/
abbrev overMap {X Y : C} (φ : X ⟶ Y) :
    FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := Over.map φ
      w := Over.mapForget_eq φ }

end FibredInGroupoidsOver

-- Proof sketch: because a based functor `F : C/X ⟶ C/Y` commutes strictly with the forgetful
-- functors to `C`, the object `F.obj (Over.mk (𝟙 X))` lies over `X`.
/-- The image of `id_X : X/X` under a morphism `C/X ⟶ C/Y` over `C` has source object `X`. -/
theorem sliceMor_obj_id_left_eq {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)) :
    ((G F).obj (Over.mk (𝟙 X))).left = X := by
  -- Evaluate the over-base compatibility of `F` at the universal slice object `id_X : X/X`.
  simpa using
    (show (Over.forget Y).obj ((G F).obj (Over.mk (𝟙 X))) =
        (Over.forget X).obj (Over.mk (𝟙 X)) from
      congrArg (fun H : Over X ⥤ C ↦ H.obj (Over.mk (𝟙 X)))
        (FibredInGroupoidsMor.comm F))

/-- Helper for Lemma 4.40.3: every object of `C/X` is sent by a morphism over `C` to an object of
`C/Y` lying over the same base object. -/
private theorem sliceMor_obj_left_eq {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)) (a : Over X) :
    ((G F).obj a).left = a.left := by
  -- This is the same over-base compatibility, evaluated at an arbitrary slice object.
  simpa using
    (show (Over.forget Y).obj ((G F).obj a) = (Over.forget X).obj a from
      congrArg (fun H : Over X ⥤ C ↦ H.obj a) (FibredInGroupoidsMor.comm F))

/-- The morphism `X ⟶ Y` obtained by evaluating `F : C/X ⟶ C/Y` over `C` at `id_X : X/X`. -/
def sliceMorToHom {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)) :
    X ⟶ Y :=
  eqToHom (sliceMor_obj_id_left_eq F).symm ≫ ((G F).obj (Over.mk (𝟙 X))).hom

/-- Helper for Lemma 4.40.3: a vertical morphism in `C/Y` between two objects lying over `X`
identifies the two corresponding arrows `X ⟶ Y`. -/
private theorem over_hom_eq_of_homlift_id {X Y : C}
    {a b : Over Y} (ha : a.left = X) (hb : b.left = X)
    (m : a ⟶ b) (hm : (Over.forget Y).IsHomLift (𝟙 X) m) :
    eqToHom ha.symm ≫ a.hom = eqToHom hb.symm ≫ b.hom := by
  have hfac : (Over.forget Y).map m = eqToHom ha ≫ 𝟙 X ≫ eqToHom hb.symm := by
    simpa using (@IsHomLift.fac' _ _ _ _ (Over.forget Y) _ _ _ _ (𝟙 X) m hm)
  have hleft : m.left = eqToHom ha ≫ 𝟙 X ≫ eqToHom hb.symm := by
    simpa using hfac
  have hw : m.left ≫ b.hom = a.hom := by
    simpa using Over.w m
  calc
    eqToHom ha.symm ≫ a.hom = eqToHom ha.symm ≫ m.left ≫ b.hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ eqToHom ha.symm ≫ k) hw.symm
    _ = eqToHom hb.symm ≫ b.hom := by
      rw [hleft]
      simp

-- Proof sketch: a vertical natural isomorphism between two morphisms `C/X ⟶ C/Y` over `C`
-- evaluates at `id_X` to a vertical isomorphism in `C/Y`, hence identifies the recovered arrows
-- `X ⟶ Y`.
private theorem sliceMorToHom_eq_of_isomorphic {X Y : C}
    {F H : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)}
    (hFH : IsIsomorphic F H) :
    sliceMorToHom F = sliceMorToHom H := by
  rcases hFH with ⟨τ⟩
  let τBased := FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso τ
  let m : ((G F).obj (Over.mk (𝟙 X))) ⟶ ((G H).obj (Over.mk (𝟙 X))) :=
    τBased.hom.app (Over.mk (𝟙 X))
  have hm : (Over.forget Y).IsHomLift (𝟙 X) m := by
    -- The component of a based natural isomorphism is vertical over the identity on the base.
    simpa using
      BasedNatTrans.isHomLift τBased.hom
        (rfl : (Over.forget X).obj (Over.mk (𝟙 X)) = X)
  -- The vertical component over `id_X` identifies the two recovered arrows `X ⟶ Y`.
  simpa [sliceMorToHom] using
    over_hom_eq_of_homlift_id
      (sliceMor_obj_id_left_eq F) (sliceMor_obj_id_left_eq H) m hm

/-- Helper for Lemma 4.40.3: evaluating the canonical postcomposition morphism at `id_X` recovers
the original arrow `φ : X ⟶ Y`. -/
private theorem sliceMorToHom_overMap {X Y : C} (φ : X ⟶ Y) :
    sliceMorToHom (FibredInGroupoidsOver.overMap φ) = φ := by
  -- For `overMap φ`, the image of `id_X` is literally the slice object represented by `φ`.
  change eqToHom rfl.symm ≫ (𝟙 X ≫ φ) = φ
  simp

/-- Helper for Lemma 4.40.3: the value of `F` on an object `a : C/X` is obtained by composing
`a.hom` with the recovered arrow `sliceMorToHom F`. -/
private theorem sliceMor_obj_hom_eq_comp_sliceMorToHom {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)) (a : Over X) :
    eqToHom (sliceMor_obj_left_eq F a) ≫ (a.hom ≫ sliceMorToHom F) =
      ((G F).obj a).hom := by
  let ψ : a ⟶ Over.mk (𝟙 X) :=
    Over.homMk (U := a) (V := Over.mk (𝟙 X)) a.hom (by simp)
  have hψlift : (Over.forget X).IsHomLift a.hom ψ := by
    -- The canonical arrow `a ⟶ id_X` in the slice category lies over `a.hom`.
    refine IsHomLift.of_fac' (Over.forget X) a.hom ψ rfl rfl ?_
    simp [ψ]
  have hmaplift : (Over.forget Y).IsHomLift a.hom ((G F).map ψ) := by
    exact ((FibredInGroupoidsMor.toBasedFunctor F).isHomLift_iff a.hom ψ).2 hψlift
  have hmap : ((G F).map ψ).left =
      eqToHom (sliceMor_obj_left_eq F a) ≫ a.hom ≫
        eqToHom (sliceMor_obj_id_left_eq F).symm := by
    -- The image of `ψ` still lies over the same base arrow `a.hom`.
    simpa using
      (@IsHomLift.fac' _ _ _ _ (Over.forget Y) _ _ _ _ a.hom ((G F).map ψ) hmaplift)
  have hw : ((G F).map ψ).left ≫ ((G F).obj (Over.mk (𝟙 X))).hom =
      ((G F).obj a).hom := by
    simpa [ψ] using Over.w ((G F).map ψ)
  have hw' :
      eqToHom (sliceMor_obj_left_eq F a) ≫ a.hom ≫
          eqToHom (sliceMor_obj_id_left_eq F).symm ≫
            ((G F).obj (Over.mk (𝟙 X))).hom =
        ((G F).obj a).hom := by
    simpa [hmap, Category.assoc] using hw
  simpa [sliceMorToHom, Category.assoc] using hw'

/-- Helper for Lemma 4.40.3: on a morphism `f : a ⟶ b` in `C/X`, the underlying base arrow of
`F.map f` is the same base arrow `f.left`, transported across the over-base identifications. -/
private theorem sliceMor_map_left_eq {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y))
    {a b : Over X} (f : a ⟶ b) :
    ((G F).map f).left =
      eqToHom (sliceMor_obj_left_eq F a) ≫ f.left ≫
        eqToHom (sliceMor_obj_left_eq F b).symm := by
  have hflift : (Over.forget X).IsHomLift f.left f := by
    -- Every slice morphism lies over its underlying arrow in `C`.
    refine IsHomLift.of_fac' (Over.forget X) f.left f rfl rfl ?_
    simp
  have hmaplift : (Over.forget Y).IsHomLift f.left ((G F).map f) := by
    exact ((FibredInGroupoidsMor.toBasedFunctor F).isHomLift_iff f.left f).2 hflift
  simpa using
    (@IsHomLift.fac' _ _ _ _ (Over.forget Y) _ _ _ _ f.left ((G F).map f) hmaplift)

/-- Helper for Lemma 4.40.3: a based-functor isomorphism induces an isomorphism in the owner
category of fibred groupoids. -/
private noncomputable def ofBasedFunctorIso
    {P Q : FibredInGroupoidsOver C} {F G : P ⟶ Q}
    (e : FibredInGroupoidsMor.toBasedFunctor F ≅ FibredInGroupoidsMor.toBasedFunctor G) :
    F ≅ G := by
  let eFibCat :
      FibredInGroupoidsMor.toFibredCategoryMor F ≅
        FibredInGroupoidsMor.toFibredCategoryMor G :=
    CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial
  exact FibredInGroupoidsMor.ofFibredCategoryMorIso eFibCat

/-- Helper for Lemma 4.40.3: every morphism `C/X ⟶ C/Y` over `C` is `2`-isomorphic to
postcomposition by the recovered arrow `sliceMorToHom F`. -/
private theorem sliceMor_isomorphic_overMap_recovered {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)) :
    Nonempty (F ≅ FibredInGroupoidsOver.overMap (sliceMorToHom F)) := by
  let eNat : (G F) ≅ (G (FibredInGroupoidsOver.overMap (sliceMorToHom F))) :=
    NatIso.ofComponents
      (fun a ↦
        Over.isoMk (eqToIso (sliceMor_obj_left_eq F a))
          (by
            -- Objectwise, the target object is exactly obtained by composing with `sliceMorToHom F`.
            simpa [FibredInGroupoidsOver.overMap] using
              sliceMor_obj_hom_eq_comp_sliceMorToHom F a))
      (by
        intro a b f
        apply Over.OverMorphism.ext
        -- Naturality reduces to the equality of the underlying base arrows in `C`.
        change ((G F).map f).left ≫ eqToHom (sliceMor_obj_left_eq F b) =
          eqToHom (sliceMor_obj_left_eq F a) ≫ f.left
        rw [sliceMor_map_left_eq]
        simp [Category.assoc])
  let eBased :
      FibredInGroupoidsMor.toBasedFunctor F ≅
        FibredInGroupoidsMor.toBasedFunctor
          (FibredInGroupoidsOver.overMap (sliceMorToHom F)) :=
    BasedNatIso.mkNatIso eNat
      (fun a ↦ by
        -- Each component is vertical, so the natural isomorphism lies over the identity on the
        -- common base object `a.left`.
        refine IsHomLift.of_fac' (Over.forget Y) (𝟙 a.left) (eNat.hom.app a) ?_ ?_ ?_
        · simpa using sliceMor_obj_left_eq F a
        · rfl
        · simp [eNat])
  exact ⟨ofBasedFunctorIso eBased⟩

private noncomputable def sliceMorIsoClassesToHom (X Y : C) :
    isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)))) →
      (X ⟶ Y) :=
  fun q ↦
    Quotient.liftOn q
      (fun F : FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)) ↦
        sliceMorToHom F)
      (fun _ _ hFG ↦ sliceMorToHom_eq_of_isomorphic hFG)

-- Proof sketch: specialize
-- `FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence` to
-- `(FibredInGroupoidsOver.ofFunctor (Over.forget Y) : FibredInGroupoidsOver C).toFibredCategoryOver`
-- at `X`, so evaluation at `id_X` induces a bijection on isomorphism classes; compose with the
-- canonical identification of the fiber of `Over.forget Y` over `X` with `Hom_C(X, Y)`.
private theorem sliceMorIsoClassesToHom_bijective (X Y : C) :
    Function.Bijective (sliceMorIsoClassesToHom X Y) := by
  constructor
  · intro q₁ q₂ hq
    revert hq
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro F G hq
    -- Equal recovered arrows force both slice morphisms into the same canonical `overMap`.
    let F' : FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)) := F
    let G' : FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)) := G
    rcases sliceMor_isomorphic_overMap_recovered F with ⟨τF⟩
    rcases sliceMor_isomorphic_overMap_recovered G with ⟨τG⟩
    have hFclass :
        (Quotient.mk'' F' :
          isomorphismClasses.obj
            (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X))
              (ofFunctor (Over.forget Y))))) =
          Quotient.mk'' (FibredInGroupoidsOver.overMap (sliceMorToHom F')) := by
      exact Quot.sound (show IsIsomorphic F'
        (FibredInGroupoidsOver.overMap (sliceMorToHom F')) from ⟨τF⟩)
    have hGclass :
        (Quotient.mk'' G' :
          isomorphismClasses.obj
            (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X))
              (ofFunctor (Over.forget Y))))) =
          Quotient.mk'' (FibredInGroupoidsOver.overMap (sliceMorToHom G')) := by
      exact Quot.sound (show IsIsomorphic G'
        (FibredInGroupoidsOver.overMap (sliceMorToHom G')) from ⟨τG⟩)
    calc
      Quotient.mk'' F' =
          Quotient.mk'' (FibredInGroupoidsOver.overMap (sliceMorToHom F')) := hFclass
      _ = Quotient.mk'' (FibredInGroupoidsOver.overMap (sliceMorToHom G')) := by
            have hHom : sliceMorToHom F' = sliceMorToHom G' := by
              simpa [sliceMorIsoClassesToHom] using hq
            have hOver :
                FibredInGroupoidsOver.overMap (sliceMorToHom F') =
                  FibredInGroupoidsOver.overMap (sliceMorToHom G') :=
              congrArg FibredInGroupoidsOver.overMap hHom
            simp [hOver]
      _ = Quotient.mk'' G' := hGclass.symm
  · intro φ
    refine ⟨Quotient.mk'' (FibredInGroupoidsOver.overMap φ), ?_⟩
    exact sliceMorToHom_overMap φ

theorem slice_id_isEquivalenceOverBase (X : C) :
    FibredInGroupoidsMor.IsEquivalenceOverBase
      (((𝟙 (ofFunctor (Over.forget X))) :
        FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget X)))) :=
  FibredInGroupoidsOver.hom_isEquivalenceOverBase (Bicategory.Equivalence.id _)

/-- Transport a morphism between represented fibred categories to a morphism between the
corresponding slice categories. -/
noncomputable def representableFibredInGroupoidsMorToSliceMor
    {P Q : FibredInGroupoidsOver C}
    {X Y : C}
    (j : P ⟶ ofFunctor (Over.forget X))
    (j' : Q ⟶ ofFunctor (Over.forget Y))
    (hj : FibredInGroupoidsMor.IsEquivalenceOverBase j)
    (F : P ⟶ Q) :
    ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y) :=
  let i : ofFunctor (Over.forget X) ⟶ P :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j hj)
  (i ≫ F) ≫ j'

theorem representableFibredInGroupoidsMorToHom_eq_of_isomorphic
    {P Q : FibredInGroupoidsOver C}
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase)
    {F G : FibredInGroupoidsMor P Q}
    (hFG : IsIsomorphic F G) :
    sliceMorToHom (representableFibredInGroupoidsMorToSliceMor j j' hj F) =
      sliceMorToHom (representableFibredInGroupoidsMorToSliceMor j j' hj G) := by
  classical
  let i : ofFunctor (Over.forget X) ⟶ P :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j hj)
  rcases hFG with ⟨τ⟩
  -- Whiskering the chosen `2`-isomorphism by `i` and `j'` transports it to the slice model.
  exact
    sliceMorToHom_eq_of_isomorphic
      ⟨(Bicategory.whiskerLeftIso i τ) ▷ᵢ j'⟩

/-- Helper for Lemma 4.40.3: the chosen quasi-inverse to `j : P ⟶ C/X` induces a map from
isomorphism classes of morphisms `P ⟶ Q` to isomorphism classes of slice morphisms `C/X ⟶ C/Y`. -/
private noncomputable def representableMorIsoClassesToSliceMorIsoClasses
    (P Q : FibredInGroupoidsOver C)
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) :
    isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) →
      isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X))
          (ofFunctor (Over.forget Y)))) := by
  classical
  let i : ofFunctor (Over.forget X) ⟶ P :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j hj)
  exact
    fun qFG ↦
      Quotient.liftOn qFG
        (fun F : FibredInGroupoidsMor P Q ↦
          Quotient.mk'' (representableFibredInGroupoidsMorToSliceMor j j' hj F))
        (fun _ _ hFG ↦ by
          rcases hFG with ⟨τ⟩
          exact Quot.sound ⟨(Bicategory.whiskerLeftIso i τ) ▷ᵢ j'⟩)

/-- Helper for Lemma 4.40.3: the chosen presentations `j : P ⟶ C/X` and `j' : Q ⟶ C/Y` induce
the reverse transport from slice morphism classes back to classes of morphisms `P ⟶ Q`. -/
private noncomputable def sliceMorIsoClassesToRepresentableMorIsoClasses
    (P Q : FibredInGroupoidsOver C)
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj' : j'.IsEquivalenceOverBase) :
    isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X))
          (ofFunctor (Over.forget Y)))) →
      isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) := by
  classical
  let i' : ofFunctor (Over.forget Y) ⟶ Q :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j' hj')
  exact
    fun qFG ↦
      Quotient.liftOn qFG
        (fun F : FibredInGroupoidsMor (ofFunctor (Over.forget X))
            (ofFunctor (Over.forget Y)) ↦
          Quotient.mk'' ((j ≫ F) ≫ i'))
        (fun _ _ hFG ↦ by
          rcases hFG with ⟨τ⟩
          exact Quot.sound ⟨(Bicategory.whiskerLeftIso j τ) ▷ᵢ i'⟩)

noncomputable def representableFibredInGroupoidsMorIsoClassesToHom
    (P Q : FibredInGroupoidsOver C)
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) :
    isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor P Q)) →
      (X ⟶ Y) :=
  fun qFG ↦
    Quotient.liftOn qFG
      (fun F : FibredInGroupoidsMor P Q ↦
        sliceMorToHom (representableFibredInGroupoidsMorToSliceMor j j' hj F))
      (fun _ _ hFG ↦ representableFibredInGroupoidsMorToHom_eq_of_isomorphic j j' hj hFG)

-- Proof sketch: transport the hom-category of morphisms `p ⟶ q` across the chosen slice
-- presentations, reduce to the slice statement proved above, and use the fact that changing the
-- quasi-inverse of `j` does not change the induced class in the slice hom-category.
theorem representableFibredInGroupoidsMorIsoClassesToHom_bijective
    (P Q : FibredInGroupoidsOver C)
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase) :
    Function.Bijective
      (representableFibredInGroupoidsMorIsoClassesToHom P Q j j' hj) := by
  classical
  let toSlice :=
    representableMorIsoClassesToSliceMorIsoClasses P Q j j' hj
  let fromSlice :=
    sliceMorIsoClassesToRepresentableMorIsoClasses P Q j j' hj'
  let i : ofFunctor (Over.forget X) ⟶ P :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j hj)
  let i' : ofFunctor (Over.forget Y) ⟶ Q :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j' hj')
  have hjSpec := Classical.choose_spec (FibredInGroupoidsMor.exists_inverse j hj)
  have hj'Spec := Classical.choose_spec (FibredInGroupoidsMor.exists_inverse j' hj')
  have hLeftInv : Function.LeftInverse fromSlice toSlice := by
    intro q
    refine Quotient.inductionOn q ?_
    intro F
    apply Quot.sound
    rcases hjSpec.1 with ⟨ηj⟩
    rcases hj'Spec.1 with ⟨ηj'⟩
    -- Insert the chosen units `𝟙_P ≅ j ≫ i` and `𝟙_Q ≅ j' ≫ i'` on both sides of `F`.
    refine ⟨?_⟩
    simpa [toSlice, fromSlice, representableFibredInGroupoidsMorToSliceMor, Category.assoc] using
      ((((Bicategory.leftUnitor F).symm ≪≫ (ηj ▷ᵢ F)) ≪≫
        (Bicategory.rightUnitor ((j ≫ i) ≫ F)).symm ≪≫
          (((j ≫ i) ≫ F) ◁ᵢ ηj')).symm)
  have hRightInv : Function.RightInverse fromSlice toSlice := by
    intro q
    refine Quotient.inductionOn q ?_
    intro F
    apply Quot.sound
    rcases hjSpec.2 with ⟨εj⟩
    rcases hj'Spec.2 with ⟨εj'⟩
    -- Insert the chosen counits `i ≫ j ≅ 𝟙_{C/X}` and `i' ≫ j' ≅ 𝟙_{C/Y}` around `F`.
    refine ⟨?_⟩
    simpa [toSlice, fromSlice, representableFibredInGroupoidsMorToSliceMor, Category.assoc] using
      ((((Bicategory.leftUnitor F).symm ≪≫ (εj.symm ▷ᵢ F)) ≪≫
        (Bicategory.rightUnitor ((i ≫ j) ≫ F)).symm ≪≫
          (((i ≫ j) ≫ F) ◁ᵢ εj'.symm)).symm)
  have hToSliceBij : Function.Bijective toSlice :=
    ⟨hLeftInv.injective, hRightInv.surjective⟩
  have hComp :
      representableFibredInGroupoidsMorIsoClassesToHom P Q j j' hj =
        (sliceMorIsoClassesToHom X Y) ∘ toSlice := by
    funext q
    refine Quotient.inductionOn q ?_
    intro F
    rfl
  simpa [hComp] using
    Function.Bijective.comp (sliceMorIsoClassesToHom_bijective X Y) hToSliceBij

namespace FibredInGroupoidsMor

variable {P Q : FibredInGroupoidsOver C}

/-- A morphism `F : P ⟶ Q` induces the morphism `φ : X ⟶ Y` on isomorphism classes of objects,
with respect to chosen presentations `j : P ⟶ C/X` and `j' : Q ⟶ C/Y`, when the two composites
`P ⟶ Q ⟶ C/Y` and `P ⟶ C/X ⟶ C/Y` are `2`-isomorphic over `C`. This is the source-facing
condition behind Lemma 4.40.3. -/
def InducesHom
    {X Y : C}
    (F : P ⟶ Q)
    (j : P ⟶ ofFunctor (Over.forget X))
    (j' : Q ⟶ ofFunctor (Over.forget Y))
    (φ : X ⟶ Y) : Prop :=
  Nonempty
    ((F ≫ j') ≅
      (j ≫ FibredInGroupoidsOver.overMap φ))

end FibredInGroupoidsMor

namespace FibredInGroupoidsOver

variable {P Q : FibredInGroupoidsOver C}

/-- Quotient-level reformulation of Lemma 4.40.3: if bundled categories fibred in groupoids `P`
and `Q` are represented by objects `X` and `Y` of `C` through presentation morphisms over `C`,
then the set of `2`-isomorphism classes of `1`-morphisms from `P` to `Q` is canonically
identified with `Hom_C(X, Y)`. The source-facing induced-map condition is exposed separately as
`FibredInGroupoidsMor.InducesHom`. -/
noncomputable def mor_isoClasses_equiv_hom
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase) :
    isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) ≃ (X ⟶ Y) :=
  Equiv.ofBijective
    (representableFibredInGroupoidsMorIsoClassesToHom P Q j j' hj)
    (representableFibredInGroupoidsMorIsoClassesToHom_bijective P Q j j' hj hj')

/-- Companion bridge for Lemma 4.40.3: the same canonical equivalence expressed using chosen
bicategorical equivalences `P ≌ C/X` and `Q ≌ C/Y` in `FibredInGroupoidsOver C`. -/
noncomputable def mor_isoClasses_equiv_hom_of_equivalences
    {X Y : C}
    (eP : P ≌ ofFunctor (Over.forget X))
    (eQ : Q ≌ ofFunctor (Over.forget Y)) :
    isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) ≃
      (X ⟶ Y) :=
  mor_isoClasses_equiv_hom
    eP.hom
    eQ.hom
    (FibredInGroupoidsOver.hom_isEquivalenceOverBase eP)
    (FibredInGroupoidsOver.hom_isEquivalenceOverBase eQ)

/-- Companion reformulation of Lemma 4.40.3: for chosen presentation morphisms of `P` and `Q`
by `X` and `Y`, the canonical map from `2`-isomorphism classes of `1`-morphisms `P ⟶ Q` to
`Hom_C(X, Y)` is bijective. -/
theorem mor_isoClasses_to_hom_bijective
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase) :
    Function.Bijective
      (mor_isoClasses_equiv_hom j j' hj hj' :
        isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) →
          (X ⟶ Y)) :=
  (mor_isoClasses_equiv_hom j j' hj hj').bijective

/-- Companion bridge reformulation of Lemma 4.40.3 using chosen bicategorical equivalences to the
slice presentations `C/X ⥤ C` and `C/Y ⥤ C`. -/
theorem mor_isoClasses_to_hom_bijective_of_equivalences
    {X Y : C}
    (eP : P ≌ ofFunctor (Over.forget X))
    (eQ : Q ≌ ofFunctor (Over.forget Y)) :
    Function.Bijective
      (mor_isoClasses_equiv_hom_of_equivalences eP eQ :
        isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) →
          (X ⟶ Y)) :=
  (mor_isoClasses_equiv_hom_of_equivalences eP eQ).bijective

/-- Helper for Lemma 4.40.3: an equivalence over `C` from `Q` to a slice projection forces the
fibers of `Q` to be setoids. -/
private theorem isFibredInSetoids_of_equivalence_to_over
    {Q : FibredInGroupoidsOver C} {Y : C}
    (e : Q ≌ ofFunctor (Over.forget Y)) :
    CategoryTheory.IsFibredInSetoids Q.p := by
  let hBase : (FibredInGroupoidsMor.toBasedFunctor e.hom).IsEquivalenceOverBase :=
    FibredInGroupoidsOver.hom_isEquivalenceOverBase e
  refine { fiber_isThin := ?_ }
  intro U
  let F := FibredInGroupoidsMor.fiberFunctor e.hom U
  letI : F.IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (FibredInGroupoidsMor.toBasedFunctor e.hom) hBase U
  letI : F.Faithful := by
    infer_instance
  have hThinTarget : Quiver.IsThin ((Over.forget Y).Fiber U) := by
    intro a b
    refine ⟨?_⟩
    intro f g
    apply Functor.Fiber.hom_ext
    apply Over.OverMorphism.ext
    have hf := @IsHomLift.fac' _ _ _ _ (Over.forget Y) U U _ _ (𝟙 U)
      (Functor.Fiber.fiberInclusion.map f) f.2
    have hg := @IsHomLift.fac' _ _ _ _ (Over.forget Y) U U _ _ (𝟙 U)
      (Functor.Fiber.fiberInclusion.map g) g.2
    simpa using hf.trans hg.symm
  intro a b
  refine ⟨?_⟩
  intro f g
  apply F.map_injective
  have hSub : Subsingleton (F.obj a ⟶ F.obj b) := hThinTarget (F.obj a) (F.obj b)
  exact @Subsingleton.elim _ hSub _ _

/-- Helper for Lemma 4.40.3: a presentation of `Q` by a slice category upgrades `Q` to a
fibred-in-setoids object. -/
private theorem isFibredInSetoids_of_presentation
    {Q : FibredInGroupoidsOver C} {Y : C}
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj' : j'.IsEquivalenceOverBase) :
    CategoryTheory.IsFibredInSetoids Q.p := by
  let e := Classical.choose (FibredInGroupoidsMor.exists_equivalence j' hj')
  have he : e.hom = j' := Classical.choose_spec (FibredInGroupoidsMor.exists_equivalence j' hj')
  simpa [he] using isFibredInSetoids_of_equivalence_to_over e

/-- Helper for Lemma 4.40.3: if the target has setoid fibers, then any two `2`-morphisms between
fixed `1`-morphisms into it are equal. -/
private theorem fibredInGroupoidsOverTwoHom_subsingleton_of_target_setoid
    {P Q : FibredInGroupoidsOver C} [CategoryTheory.IsFibredInSetoids Q.p]
    (F G : P ⟶ Q) :
    Subsingleton (F ⟶ G) := by
  constructor
  intro τ σ
  -- Equality in the owner hom-category reduces to equality of the underlying based natural
  -- transformations, so it suffices to compare components in the thin target fibers.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  have hτlift :
      Functor.IsHomLift Q.p (𝟙 (P.p.obj a))
        (τ.hom.hom.hom.hom.app a) := by
    exact (τ.hom.hom.hom.hom).isHomLift rfl
  have hσlift :
      Functor.IsHomLift Q.p (𝟙 (P.p.obj a))
        (σ.hom.hom.hom.hom.app a) := by
    exact (σ.hom.hom.hom.hom).isHomLift rfl
  letI := hτlift
  letI := hσlift
  have hFiber :
      Functor.Fiber.homMk Q.p (P.p.obj a) (τ.hom.hom.hom.hom.app a) =
        Functor.Fiber.homMk Q.p (P.p.obj a) (σ.hom.hom.hom.hom.app a) :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hFiber

/-- Helper for Lemma 4.40.3: if the target has setoid fibers, then any two `2`-isomorphisms
between fixed `1`-morphisms into it are equal. -/
private theorem fibredInGroupoidsOverTwoIso_subsingleton_of_target_setoid
    {P Q : FibredInGroupoidsOver C} [CategoryTheory.IsFibredInSetoids Q.p]
    {F G : P ⟶ Q} :
    Subsingleton (F ≅ G) := by
  constructor
  intro τ σ
  -- An isomorphism is determined by its forward and inverse `2`-morphisms, and those are already
  -- unique in the target setoid fibers.
  cases τ
  cases σ
  congr
  · exact (fibredInGroupoidsOverTwoHom_subsingleton_of_target_setoid F G).elim _ _
  · exact (fibredInGroupoidsOverTwoHom_subsingleton_of_target_setoid G F).elim _ _

/-- Companion bridge for Lemma 4.40.3: the source-facing induced-map condition agrees with the
quotient-level equivalence `mor_isoClasses_equiv_hom`. -/
theorem inducesHom_iff_mor_isoClasses_equiv_hom_eq
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase)
    (F : FibredInGroupoidsMor P Q) (φ : X ⟶ Y) :
    FibredInGroupoidsMor.InducesHom F j j' φ ↔
      mor_isoClasses_equiv_hom j j' hj hj' (Quotient.mk'' F) = φ := by
  classical
  let i : ofFunctor (Over.forget X) ⟶ P :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j hj)
  have hi := Classical.choose_spec (FibredInGroupoidsMor.exists_inverse j hj)
  constructor
  · rintro ⟨τ⟩
    rcases hi.2 with ⟨eps⟩
    have hSlice :
        IsIsomorphic (representableFibredInGroupoidsMorToSliceMor j j' hj F)
          (FibredInGroupoidsOver.overMap φ) := by
      -- Whisker the induced `2`-isomorphism by the chosen inverse of `j`, then cancel `i ≫ j`.
      refine ⟨?_⟩
      simpa [representableFibredInGroupoidsMorToSliceMor, Category.assoc] using
        (Bicategory.associator i F j' ≪≫ (i ◁ᵢ τ) ≪≫
          (Bicategory.associator i j (FibredInGroupoidsOver.overMap φ)).symm ≪≫
            (eps ▷ᵢ FibredInGroupoidsOver.overMap φ) ≪≫
              Bicategory.leftUnitor (FibredInGroupoidsOver.overMap φ))
    -- The slice representative therefore recovers exactly the arrow `φ`.
    exact
      sliceMorToHom_eq_of_isomorphic hSlice |>.trans
        (sliceMorToHom_overMap φ)
  · intro hφ
    have hSlice :
        IsIsomorphic (representableFibredInGroupoidsMorToSliceMor j j' hj F)
          (FibredInGroupoidsOver.overMap φ) := by
      -- Route correction: first recover the canonical slice `overMap` from the quotient value,
      -- then transport that slice isomorphism back across the presentation `j`.
      have hRecovered :
          sliceMorToHom (representableFibredInGroupoidsMorToSliceMor j j' hj F) = φ := hφ
      rcases
        (show
            Nonempty
              (representableFibredInGroupoidsMorToSliceMor j j' hj F ≅
                FibredInGroupoidsOver.overMap φ) from by
            simpa [hRecovered] using
              sliceMor_isomorphic_overMap_recovered
                (representableFibredInGroupoidsMorToSliceMor j j' hj F)) with
        ⟨τ⟩
      exact ⟨τ⟩
    rcases hi.1 with ⟨η⟩
    refine ⟨?_⟩
    -- Reinsert the chosen unit `𝟙_P ≅ j ≫ i` and then whisker by the recovered slice isomorphism.
    simpa [FibredInGroupoidsMor.InducesHom, representableFibredInGroupoidsMorToSliceMor,
      Category.assoc] using
      ((Bicategory.leftUnitor (F ≫ j')).symm ≪≫
        (η ▷ᵢ (F ≫ j')) ≪≫
          (j ◁ᵢ (Classical.choice hSlice)))

/-- Lemma 4.40.3, more precisely: every morphism `φ : X ⟶ Y` is represented by a `1`-morphism
`F : P ⟶ Q` over `C` that induces `φ` on isomorphism classes of objects, and such an `F` is
unique up to a unique `2`-isomorphism. -/
theorem exists_unique_morphism_up_to_unique_iso_of_hom
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase)
    (φ : X ⟶ Y) :
    ∃ F : FibredInGroupoidsMor P Q,
      FibredInGroupoidsMor.InducesHom F j j' φ ∧
        ∀ G : FibredInGroupoidsMor P Q,
          FibredInGroupoidsMor.InducesHom G j j' φ →
            Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G) := by
  classical
  let e := mor_isoClasses_equiv_hom j j' hj hj'
  let q : isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) := e.symm φ
  let F : FibredInGroupoidsMor P Q := Classical.choose (Quotient.exists_rep q)
  have hFq :
      (Quotient.mk'' F :
        isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q))) = q :=
    Classical.choose_spec (Quotient.exists_rep q)
  have hqEq : e q = φ := by
    dsimp [q]
    exact e.apply_symm_apply φ
  refine ⟨F, ?_, ?_⟩
  · -- Choose the representative `F` of the class `e.symm φ`.
    have hEq : e (Quotient.mk'' F) = φ := by
      calc
        e (Quotient.mk'' F) = e q := congrArg e hFq
        _ = φ := hqEq
    exact (inducesHom_iff_mor_isoClasses_equiv_hom_eq j j' hj hj' F φ).2 hEq
  · intro G hG
    have hQsetoid : CategoryTheory.IsFibredInSetoids Q.p :=
      isFibredInSetoids_of_presentation j' hj'
    have hF : e (Quotient.mk'' F) = φ := by
      calc
        e (Quotient.mk'' F) = e q := congrArg e hFq
        _ = φ := hqEq
    have hG' :
        e (Quotient.mk'' G) = φ :=
      (inducesHom_iff_mor_isoClasses_equiv_hom_eq j j' hj hj' G φ).1 hG
    have hClass :
        (Quotient.mk'' F :
          isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q))) =
          Quotient.mk'' G := by
      exact e.injective (hF.trans hG'.symm)
    have hIso : Nonempty (F ≅ G) := by
      exact Quotient.exact hClass
    have hSub : Subsingleton (F ≅ G) := by
      letI : CategoryTheory.IsFibredInSetoids Q.p := hQsetoid
      exact fibredInGroupoidsOverTwoIso_subsingleton_of_target_setoid
    exact ⟨hIso, hSub⟩

/-- Companion bridge form of the existence-and-uniqueness statement in Lemma 4.40.3, using
chosen bicategorical equivalences to slice categories. -/
theorem exists_unique_morphism_up_to_unique_iso_of_hom_of_equivalences
    {X Y : C}
    (eP : P ≌ ofFunctor (Over.forget X))
    (eQ : Q ≌ ofFunctor (Over.forget Y))
    (φ : X ⟶ Y) :
    ∃ F : FibredInGroupoidsMor P Q,
      FibredInGroupoidsMor.InducesHom F eP.hom eQ.hom φ ∧
        ∀ G : FibredInGroupoidsMor P Q,
          FibredInGroupoidsMor.InducesHom G eP.hom eQ.hom φ →
            Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G) := by
  simpa [FibredInGroupoidsMor.InducesHom, mor_isoClasses_equiv_hom_of_equivalences] using
    exists_unique_morphism_up_to_unique_iso_of_hom
      eP.hom
      eQ.hom
      (FibredInGroupoidsOver.hom_isEquivalenceOverBase eP)
      (FibredInGroupoidsOver.hom_isEquivalenceOverBase eQ)
      φ

end FibredInGroupoidsOver

/-- Quotient-level specialization of Lemma 4.40.3 to slice categories: the set of
`2`-isomorphism classes of morphisms `C/X ⟶ C/Y` over `C` is canonically identified with
`Hom_C(X, Y)`. -/
noncomputable def sliceMor_isoClasses_equiv_hom (X Y : C) :
    isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)))) ≃
      (X ⟶ Y) :=
  FibredInGroupoidsOver.mor_isoClasses_equiv_hom
    (𝟙 (ofFunctor (Over.forget X)))
    (𝟙 (ofFunctor (Over.forget Y)))
    (slice_id_isEquivalenceOverBase X)
    (slice_id_isEquivalenceOverBase Y)

/-- Companion reformulation of the slice specialization of Lemma 4.40.3: the canonical map to
`Hom_C(X, Y)` is bijective. -/
theorem sliceMor_isoClasses_to_hom_bijective (X Y : C) :
    Function.Bijective
      (sliceMor_isoClasses_equiv_hom X Y :
        isomorphismClasses.obj
            (Cat.of
              (FibredInGroupoidsMor (ofFunctor (Over.forget X))
                (ofFunctor (Over.forget Y)))) →
          (X ⟶ Y)) :=
  (sliceMor_isoClasses_equiv_hom X Y).bijective

/-- Companion specialization of the existence-and-uniqueness form of Lemma 4.40.3 to slice
categories. -/
theorem exists_unique_slice_morphism_up_to_unique_iso_of_hom {X Y : C} (φ : X ⟶ Y) :
    ∃ F :
        FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)),
      FibredInGroupoidsMor.InducesHom
          F (𝟙 (ofFunctor (Over.forget X))) (𝟙 (ofFunctor (Over.forget Y))) φ ∧
        ∀ G :
            FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)),
          FibredInGroupoidsMor.InducesHom
            G (𝟙 (ofFunctor (Over.forget X))) (𝟙 (ofFunctor (Over.forget Y))) φ →
            Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G) := by
  simpa [sliceMor_isoClasses_equiv_hom, FibredInGroupoidsMor.InducesHom] using
    FibredInGroupoidsOver.exists_unique_morphism_up_to_unique_iso_of_hom
      (𝟙 (ofFunctor (Over.forget X)))
      (𝟙 (ofFunctor (Over.forget Y)))
      (slice_id_isEquivalenceOverBase X)
      (slice_id_isEquivalenceOverBase Y)
      φ

end CategoryTheory
