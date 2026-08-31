module

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import stacks_project.Chap04.Definition_4_31_2
public import stacks_project.Chap04.Lemma_4_32_3
public import stacks_project.Chap04.Lemma_4_39_6
public import stacks_project.Chap04.Lemma_4_39_4
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open CategoricalPullback
open FibredInSetoidsOver
open scoped Bicategory
open scoped CategoricalPullback

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FibredInSetoidsOver.{u, v, max u v, v} C}
variable {F : X ⟶ Y} {G : Z ⟶ Y}

/-
Domain-style sampling:
- primary domain: categories fibred in setoids over a fixed base, bicategorical `2`-fibre
  product squares between them, and the presheaves of fiberwise isomorphism classes attached to
  such objects;
- inspected owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `fibredInSetoidsToPresheaf`,
  `FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom`,
  `IsPullback`;
- best owner abstraction: the main statement should live at the canonical presheaf pullback level,
  namely `IsPullback` for the square obtained by applying `fibredInSetoidsToPresheaf` to a chosen
  bicategorical `2`-fibre product square;
- primitive data: the two owner morphisms `F : X ⟶ Y` and `G : Z ⟶ Y`, together with a chosen
  square `P : BicategoricalTwoCommutativeSquare F G`;
- derived API: the projection morphisms of `P` and the induced presheaf morphisms obtained by
  functoriality of `fibredInSetoidsToPresheaf`.

Source/core/bridge triage:
- `source-facing`: the textbook claim that iso-classes of a chosen fibred `2`-fibre product form
  the pullback presheaf;
- `core/canonical`: `Bicategory.IsFinal`, `FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom`,
  and the target owner `IsPullback` in the presheaf category;
- `bridge/view`: the projections of a chosen square `P : BicategoricalTwoCommutativeSquare F G`,
  whose images under `fibredInSetoidsToPresheaf` form the pullback square. -/
namespace FibredInSetoidsOver

/-- Helper for Lemma 4.39.8: the quotient of a discrete category by isomorphism classes is
canonically identified with its object type. -/
private noncomputable def isoClasses_equiv_of_isDiscrete
    (D : Type u) [Category.{v} D] [IsDiscrete D] :
    isomorphismClasses.obj (Cat.of D) ≃ D :=
  (Equiv.ofBijective
      (fun x : D ↦ Quotient.mk'' x)
      (by
        constructor
        · intro x y hxy
          exact Quotient.exact hxy |>.elim fun i ↦ obj_ext_of_isDiscrete i.hom
        · intro q
          refine Quotient.inductionOn q ?_
          intro x
          exact ⟨x, rfl⟩)).symm

/-- Helper for Lemma 4.39.8: choose an actual morphism of fibred-in-setoids categories whose
associated presheaf map is a prescribed natural transformation. -/
private noncomputable def representative_hom_of_presheafHom
    {A B : FibredInSetoidsOver C}
    (α : fibredInSetoidsToPresheaf.obj A ⟶ fibredInSetoidsToPresheaf.obj B) :
    A ⟶ B :=
  Quotient.out ((FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom A B).symm α)

/-- Helper for Lemma 4.39.8: the chosen representative really induces the prescribed presheaf
map. -/
private theorem representative_hom_of_presheafHom_spec
    {A B : FibredInSetoidsOver C}
    (α : fibredInSetoidsToPresheaf.obj A ⟶ fibredInSetoidsToPresheaf.obj B) :
    fibredInSetoidsToPresheaf.map (representative_hom_of_presheafHom α) = α := by
  -- Apply the hom-to-presheaf equivalence to the quotient equality defining `Quotient.out`.
  simpa [representative_hom_of_presheafHom] using
    congrArg
      (FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom A B)
      (Quotient.out_eq ((FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom A B).symm α))

/-- Helper for Lemma 4.39.8: an equivalence of categories induces a bijection on isomorphism
classes. -/
private theorem isoClasses_map_bijective_of_equivalence
    {A : Type u} {B : Type u} [Category.{v} A] [Category.{v} B]
    (e : A ≌ B) :
    Function.Bijective (isomorphismClasses.map e.functor.toCatHom) := by
  -- Use the quasi-inverse to build a set-theoretic inverse on quotient classes.
  have hleft :
      Function.LeftInverse
        (isomorphismClasses.map e.inverse.toCatHom)
        (isomorphismClasses.map e.functor.toCatHom) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid A) (e.inverse.obj (e.functor.obj a)) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid A) a
    rw [Quotient.eq'']
    exact ⟨e.unitIso.symm.app a⟩
  constructor
  · intro q₁ q₂ hq
    exact hleft.injective hq
  · intro q
    refine Quotient.inductionOn q ?_
    intro b
    refine ⟨Quotient.mk'' (e.inverse.obj b), ?_⟩
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid B) (e.functor.obj (e.inverse.obj b)) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid B) b
    rw [Quotient.eq'']
    exact ⟨e.counitIso.app b⟩

/-- Helper for Lemma 4.39.8: a `2`-morphism already forces equality on iso-class presheaves,
since the local hom-categories are groupoids. -/
private theorem presheaf_map_eq_of_two_hom
    {A B : FibredInSetoidsOver C} {H K : A ⟶ B} (η : H ⟶ K) :
    fibredInSetoidsToPresheaf.map H =
      fibredInSetoidsToPresheaf.map K := by
  -- A `2`-morphism in this bicategory is pointwise vertical in the target fibre, hence identifies
  -- the two images in every quotient by fibrewise isomorphism classes.
  ext U q
  refine Quotient.inductionOn q ?_
  intro x
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (B.p.Fiber (Opposite.unop U)))
        ((FibredInGroupoidsMor.fiberFunctor H.toHom (Opposite.unop U)).obj x) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (B.p.Fiber (Opposite.unop U)))
        ((FibredInGroupoidsMor.fiberFunctor K.toHom (Opposite.unop U)).obj x)
  have hηlift :
      Functor.IsHomLift B.p (𝟙 (Opposite.unop U))
        ((η.hom.hom.hom.hom.hom.hom).app x.1) := by
    exact BasedNatTrans.isHomLift (η.hom.hom.hom.hom.hom.hom) (by simpa [x.2])
  let m :
      ((FibredInGroupoidsMor.fiberFunctor H.toHom (Opposite.unop U)).obj x) ⟶
        ((FibredInGroupoidsMor.fiberFunctor K.toHom (Opposite.unop U)).obj x) :=
    ⟨(η.hom.hom.hom.hom.hom.hom).app x.1, hηlift⟩
  rw [Quotient.eq'']
  exact ⟨asIso m⟩

/-- Helper for Lemma 4.39.8: isomorphic morphisms of fibred-in-setoids categories induce the same
map on presheaves of isomorphism classes. -/
private theorem presheaf_map_eq_of_iso
    {A B : FibredInSetoidsOver C} {H K : A ⟶ B} (e : H ≅ K) :
    fibredInSetoidsToPresheaf.map H =
      fibredInSetoidsToPresheaf.map K := by
  -- Forget the inverse data and use the forward `2`-morphism componentwise on every fibre.
  exact presheaf_map_eq_of_two_hom e.hom

/-- Helper for Lemma 4.39.8: the explicit two-fibre-product total category, rebundled as a
category fibred in setoids over `C`. -/
private abbrev explicit_two_fibre_product_obj
    (F : X ⟶ Y) (G : Z ⟶ Y) :
    FibredInSetoidsOver C :=
  FibredInSetoidsOver.ofFunctor
    ((CategoryOver.explicitTwoFibreProduct
      (FibredInSetoidsOver.toBasedFunctor F)
      (FibredInSetoidsOver.toBasedFunctor G)).p)

/-- Helper for Lemma 4.39.8: the left projection from the explicit two-fibre-product model. -/
private abbrev explicit_two_fibre_product_left_projection
    (F : X ⟶ Y) (G : Z ⟶ Y) :
    explicit_two_fibre_product_obj (F := F) (G := G) ⟶ X :=
  FibredInSetoidsOver.ofBasedFunctor
    (CategoryOver.explicitTwoFibreProductLeftProjection
      (FibredInSetoidsOver.toBasedFunctor F)
      (FibredInSetoidsOver.toBasedFunctor G))

/-- Helper for Lemma 4.39.8: the right projection from the explicit two-fibre-product model. -/
private abbrev explicit_two_fibre_product_right_projection
    (F : X ⟶ Y) (G : Z ⟶ Y) :
    explicit_two_fibre_product_obj (F := F) (G := G) ⟶ Z :=
  FibredInSetoidsOver.ofBasedFunctor
    (CategoryOver.explicitTwoFibreProductRightProjection
      (FibredInSetoidsOver.toBasedFunctor F)
      (FibredInSetoidsOver.toBasedFunctor G))

/-- Helper for Lemma 4.39.8: a based-functor isomorphism induces an isomorphism of morphisms in
the ambient fibred-in-groupoids owner category. -/
private noncomputable def fibredInGroupoids_isoOfBasedFunctorIso
    {P Q : FibredInGroupoidsOver C} {H K : P ⟶ Q}
    (e : FibredInGroupoidsMor.toBasedFunctor H ≅
      FibredInGroupoidsMor.toBasedFunctor K) :
    H ≅ K :=
  FibredInGroupoidsMor.ofFibredCategoryMorIso
    (CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial)

/-- Helper for Lemma 4.39.8: the explicit two-fibre-product model carries the canonical
comparison isomorphism over `Y`. -/
private noncomputable abbrev explicit_two_fibre_product_comparison_iso
    (F : X ⟶ Y) (G : Z ⟶ Y) :
    explicit_two_fibre_product_left_projection (F := F) (G := G) ≫ F ≅
      explicit_two_fibre_product_right_projection (F := F) (G := G) ≫ G :=
  FibredInSetoidsOver.ofAmbientIso
    (fibredInGroupoids_isoOfBasedFunctorIso
      (CategoryOver.explicitTwoFibreProductComparisonIsoOver
        (FibredInSetoidsOver.toBasedFunctor F)
        (FibredInSetoidsOver.toBasedFunctor G)))

/-- Helper for Lemma 4.39.8: the explicit two-fibre-product model defines a bicategorical square
over `F` and `G`. -/
private noncomputable def explicit_two_fibre_product_square
    (F : X ⟶ Y) (G : Z ⟶ Y) :
    BicategoricalTwoCommutativeSquare F G where
  obj := explicit_two_fibre_product_obj F G
  p := explicit_two_fibre_product_left_projection F G
  q := explicit_two_fibre_product_right_projection F G
  ψ := explicit_two_fibre_product_comparison_iso F G

/-- Helper for Lemma 4.39.8: passing to iso-class presheaves turns the commutative `2`-cell of
any bicategorical square into an actual commuting square of presheaf maps. -/
private theorem presheaf_square_comm
    {P : BicategoricalTwoCommutativeSquare F G} :
    fibredInSetoidsToPresheaf.map P.p ≫ fibredInSetoidsToPresheaf.map F =
      fibredInSetoidsToPresheaf.map P.q ≫ fibredInSetoidsToPresheaf.map G := by
  -- The chosen square `2`-isomorphism becomes equality after quotienting by fibrewise
  -- isomorphism classes.
  simpa [Functor.map_comp] using presheaf_map_eq_of_iso P.ψ

/-- Helper for Lemma 4.39.8: passing to iso-class presheaves sends the explicit comparison
isomorphism to a commuting square of presheaf maps. -/
private theorem explicit_two_fibre_product_presheaf_square_comm
    (F : X ⟶ Y) (G : Z ⟶ Y) :
    fibredInSetoidsToPresheaf.map
        (explicit_two_fibre_product_left_projection (F := F) (G := G)) ≫
      fibredInSetoidsToPresheaf.map F =
    fibredInSetoidsToPresheaf.map
        (explicit_two_fibre_product_right_projection (F := F) (G := G)) ≫
      fibredInSetoidsToPresheaf.map G := by
  -- The comparison isomorphism becomes equality after quotienting by fibrewise isomorphism classes.
  simpa [Functor.map_comp] using
    presheaf_map_eq_of_iso
      (explicit_two_fibre_product_comparison_iso (F := F) (G := G))

/-- Helper for Lemma 4.39.8: a pullback object in the fibre categories determines a compatible
pair of iso-classes in the fibres of `X` and `Z`. -/
private theorem pullback_isoClasses_to_types_pullback_well_defined
    (F : X ⟶ Y) (G : Z ⟶ Y) (U : C)
    {P Q :
      ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U) ⊡
        ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U)}
    (hPQ : CategoryTheory.IsIsomorphic P Q) :
    (⟨⟨Quotient.mk'' P.fst, Quotient.mk'' P.snd⟩, by
      change
        @Quotient.mk'' _
          (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
          (((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).obj P.fst) =
          @Quotient.mk'' _
            (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
            (((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).obj P.snd)
      rw [Quotient.eq'']
      exact ⟨P.iso⟩⟩ :
      Limits.Types.PullbackObj
        ((fibredInSetoidsToPresheaf.map F).app (Opposite.op U))
        ((fibredInSetoidsToPresheaf.map G).app (Opposite.op U))) =
      ⟨⟨Quotient.mk'' Q.fst, Quotient.mk'' Q.snd⟩, by
        change
          @Quotient.mk'' _
            (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
            (((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).obj Q.fst) =
            @Quotient.mk'' _
              (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
              (((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).obj Q.snd)
        rw [Quotient.eq'']
        exact ⟨Q.iso⟩⟩ := by
  rcases hPQ with ⟨e⟩
  -- Project the pullback isomorphism to the two fibres and pass to quotient classes.
  apply Subtype.ext
  apply Prod.ext
  · exact Quot.sound ⟨asIso e.hom.fst⟩
  · exact Quot.sound ⟨asIso e.hom.snd⟩

/-- Helper for Lemma 4.39.8: from an isomorphism class in the pullback of fibres, record the
corresponding compatible pair of iso-classes in the two fibres. -/
private noncomputable def pullback_isoClasses_to_types_pullback
    (F : X ⟶ Y) (G : Z ⟶ Y) (U : C) :
    isomorphismClasses.obj
        (Cat.of
          (((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U) ⊡
            ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U))) →
      Limits.Types.PullbackObj
        ((fibredInSetoidsToPresheaf.map F).app (Opposite.op U))
        ((fibredInSetoidsToPresheaf.map G).app (Opposite.op U)) :=
  fun q ↦
    Quotient.liftOn q
      (fun P ↦
        show Limits.Types.PullbackObj
            ((fibredInSetoidsToPresheaf.map F).app (Opposite.op U))
            ((fibredInSetoidsToPresheaf.map G).app (Opposite.op U)) from
          ⟨⟨Quotient.mk'' P.fst, Quotient.mk'' P.snd⟩, by
            change
              @Quotient.mk'' _
                (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
                (((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).obj P.fst) =
                @Quotient.mk'' _
                  (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
                  (((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).obj P.snd)
            rw [Quotient.eq'']
            exact ⟨P.iso⟩⟩)
      (fun P Q hPQ ↦
        pullback_isoClasses_to_types_pullback_well_defined (F := F) (G := G) U hPQ)

/-- Helper for Lemma 4.39.8: the quotient of the pullback of fibres is identified with the
set-theoretic pullback of the quotients of the fibres. -/
private theorem pullback_isoClasses_to_types_pullback_bijective
    (F : X ⟶ Y) (G : Z ⟶ Y) (U : C) :
    Function.Bijective (pullback_isoClasses_to_types_pullback (F := F) (G := G) U) := by
  constructor
  · intro q₁ q₂ hq
    revert hq
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro P Q hPQ
    apply Quot.sound
    -- Equality of the projected quotient classes gives isomorphisms on the two components.
    have hProd := congrArg Subtype.val hPQ
    have hfst :
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber U)) P.fst =
          @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber U)) Q.fst := by
      exact congrArg (fun p ↦ p.1) hProd
    have hsnd :
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) P.snd =
          @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) Q.snd := by
      exact congrArg (fun p ↦ p.2) hProd
    rw [Quotient.eq''] at hfst
    rw [Quotient.eq''] at hsnd
    let efst : P.fst ≅ Q.fst := Classical.choice hfst
    let esnd : P.snd ≅ Q.snd := Classical.choice hsnd
    let left :
        ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).obj P.fst ⟶
          ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).obj Q.snd :=
      ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).map efst.hom ≫ Q.iso.hom
    let right :
        ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).obj P.fst ⟶
          ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).obj Q.snd :=
      P.iso.hom ≫ ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).map esnd.hom
    have hcompat : left = right := by
      -- Both sides are vertical morphisms in the thin fibre of `Y` over `U`.
      exact Subsingleton.elim _ _
    have hw :
        ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).map efst.hom ≫ Q.iso.hom =
          P.iso.hom ≫ ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).map esnd.hom := by
      simpa [left, right] using hcompat
    let e :
        P ≅ Q :=
      CategoricalPullback.mkIso efst esnd hw
    exact ⟨e⟩
  · intro t
    rcases t with ⟨⟨x, z⟩, hxz⟩
    revert hxz
    refine Quotient.inductionOn₂ x z ?_
    intro a b
    intro hab
    -- Choose representatives in the two fibres and lift the equality in `Y` to an actual isomorphism.
    let e :
        ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor U).obj a ≅
          ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor U).obj b :=
      Classical.choice (Quotient.exact hab)
    refine ⟨Quotient.mk'' (⟨a, b, e⟩), ?_⟩
    rfl

/-- Helper for Lemma 4.39.8: the canonical map from the iso-classes in the explicit pullback
fibre to the pullback of the iso-class fibres is the appwise pullback-cone map. -/
private noncomputable def explicit_two_fibre_product_isoClasses_app_to_pullback
    (F : X ⟶ Y) (G : Z ⟶ Y) (U : Cᵒᵖ) :
    ((fibredInSetoidsToPresheaf.obj
        (explicit_two_fibre_product_obj (F := F) (G := G))).obj U) →
      Limits.Types.PullbackObj
        ((fibredInSetoidsToPresheaf.map F).app U)
        ((fibredInSetoidsToPresheaf.map G).app U) :=
  (PullbackCone.mk
      ((fibredInSetoidsToPresheaf.map
          (explicit_two_fibre_product_left_projection (F := F) (G := G))).app U)
      ((fibredInSetoidsToPresheaf.map
          (explicit_two_fibre_product_right_projection (F := F) (G := G))).app U)
      (congrArg (fun α ↦ α.app U)
        (explicit_two_fibre_product_presheaf_square_comm (F := F) (G := G)))).toPullbackObj

/-- Helper for Lemma 4.39.8: the canonical appwise map for the explicit two-fibre-product square
factors through the pullback-of-fibres equivalence. -/
private theorem explicit_two_fibre_product_isoClasses_app_to_pullback_factorization
    (F : X ⟶ Y) (G : Z ⟶ Y) (U : Cᵒᵖ) :
    explicit_two_fibre_product_isoClasses_app_to_pullback (F := F) (G := G) U =
      pullback_isoClasses_to_types_pullback (F := F) (G := G) (Opposite.unop U) ∘
        isomorphismClasses.map
          ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
              (FibredInSetoidsOver.toBasedFunctor F)
              (FibredInSetoidsOver.toBasedFunctor G)
              (Opposite.unop U)).functor.toCatHom) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro P
  apply Subtype.ext
  apply Prod.ext
  · -- The first projection of the fibre equivalence is the fibre functor of the left leg.
    have hπ₁ :
        ((FibredInSetoidsOver.toBasedFunctor
            (explicit_two_fibre_product_left_projection (F := F) (G := G))).fiberFunctor
            (Opposite.unop U)) =
          (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
              (FibredInSetoidsOver.toBasedFunctor F)
              (FibredInSetoidsOver.toBasedFunctor G)
              (Opposite.unop U)).functor ⋙
            π₁
              ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor (Opposite.unop U))
              ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor (Opposite.unop U)) := by
      symm
      simpa [explicit_two_fibre_product_left_projection] using
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
          (FibredInSetoidsOver.toBasedFunctor F)
          (FibredInSetoidsOver.toBasedFunctor G)
          (Opposite.unop U))
    exact congrArg (fun H ↦ Quotient.mk'' (H.obj P)) hπ₁
  · -- The right projection is handled by the analogous comparison theorem.
    have hπ₂ :
        ((FibredInSetoidsOver.toBasedFunctor
            (explicit_two_fibre_product_right_projection (F := F) (G := G))).fiberFunctor
            (Opposite.unop U)) =
          (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
              (FibredInSetoidsOver.toBasedFunctor F)
              (FibredInSetoidsOver.toBasedFunctor G)
              (Opposite.unop U)).functor ⋙
            π₂
              ((FibredInSetoidsOver.toBasedFunctor F).fiberFunctor (Opposite.unop U))
              ((FibredInSetoidsOver.toBasedFunctor G).fiberFunctor (Opposite.unop U)) := by
      symm
      simpa [explicit_two_fibre_product_right_projection] using
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
          (FibredInSetoidsOver.toBasedFunctor F)
          (FibredInSetoidsOver.toBasedFunctor G)
          (Opposite.unop U))
    exact congrArg (fun H ↦ Quotient.mk'' (H.obj P)) hπ₂

/-- Helper for Lemma 4.39.8: pointwise, the iso-classes in the explicit pullback fibre form the
usual pullback of types. -/
private theorem explicit_two_fibre_product_isoClasses_app_bijective
    (F : X ⟶ Y) (G : Z ⟶ Y) (U : Cᵒᵖ) :
    Function.Bijective
      (explicit_two_fibre_product_isoClasses_app_to_pullback (F := F) (G := G) U) := by
  let e :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (FibredInSetoidsOver.toBasedFunctor F)
      (FibredInSetoidsOver.toBasedFunctor G)
      (Opposite.unop U)
  have hIso :
      Function.Bijective
        (isomorphismClasses.map e.functor.toCatHom) :=
    isoClasses_map_bijective_of_equivalence e
  have hPull :
      Function.Bijective
        (pullback_isoClasses_to_types_pullback (F := F) (G := G) (Opposite.unop U)) :=
    pullback_isoClasses_to_types_pullback_bijective (F := F) (G := G) (Opposite.unop U)
  -- The canonical appwise map is the composite of the quotient-level fibre equivalence with the
  -- quotient-level pullback identification.
  rw [explicit_two_fibre_product_isoClasses_app_to_pullback_factorization (F := F) (G := G) U]
  exact hPull.comp hIso

/-- Helper for Lemma 4.39.8: the presheaf attached to the explicit two-fibre-product square is a
pullback presheaf. -/
private theorem explicit_two_fibre_product_presheaf_isPullback
    (F : X ⟶ Y) (G : Z ⟶ Y) :
    IsPullback
      (fibredInSetoidsToPresheaf.map
        (explicit_two_fibre_product_left_projection (F := F) (G := G)))
      (fibredInSetoidsToPresheaf.map
        (explicit_two_fibre_product_right_projection (F := F) (G := G)))
      (fibredInSetoidsToPresheaf.map F)
      (fibredInSetoidsToPresheaf.map G) := by
  -- Pullbacks in a presheaf category are computed objectwise, so it suffices to prove the fibrewise
  -- statement over each `U : C`.
  refine IsPullback.of_forall_isPullback_app ?_
  intro U
  let c :
      PullbackCone
        ((fibredInSetoidsToPresheaf.map F).app U)
        ((fibredInSetoidsToPresheaf.map G).app U) :=
    PullbackCone.mk
      ((fibredInSetoidsToPresheaf.map
          (explicit_two_fibre_product_left_projection (F := F) (G := G))).app U)
      ((fibredInSetoidsToPresheaf.map
          (explicit_two_fibre_product_right_projection (F := F) (G := G))).app U)
      (congrArg (fun α ↦ α.app U)
        (explicit_two_fibre_product_presheaf_square_comm (F := F) (G := G)))
  have hBij :
      Function.Bijective c.toPullbackObj := by
    -- The explicit fibrewise pullback model already gives the desired bijection with the type-theoretic pullback.
    simpa [c, explicit_two_fibre_product_isoClasses_app_to_pullback] using
      explicit_two_fibre_product_isoClasses_app_bijective (F := F) (G := G) U
  exact IsPullback.of_isLimit ((PullbackCone.isLimitEquivBijective c).symm hBij)

/-- Helper for Lemma 4.39.8: equality of induced presheaf maps yields an actual `2`-isomorphism
between the underlying morphisms of categories fibred in setoids. -/
private theorem nonempty_iso_of_presheaf_map_eq
    {A B : FibredInSetoidsOver C} {H K : A ⟶ B}
    (h : fibredInSetoidsToPresheaf.map H = fibredInSetoidsToPresheaf.map K) :
    Nonempty (H ≅ K) := by
  -- Route correction: rather than transport through the square bicategory, pass to the associated
  -- fibred-in-sets morphisms where Lemma `4.39.6` already upgrades map equality to an isomorphism.
  have hSets :
      fibredInSetoidsToFibredInSets.map H =
        fibredInSetoidsToFibredInSets.map K := by
    let eP := FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom A B
    let eS := FibredInSetoidsOver.hom_isoClasses_equiv_fibredInSetsHom A B
    have hq :
        eP.symm (fibredInSetoidsToPresheaf.map H) =
          eP.symm (fibredInSetoidsToPresheaf.map K) := by
      exact congrArg eP.symm h
    have hH :
        eP.symm (fibredInSetoidsToPresheaf.map H) =
          @Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) H := by
      have he :
          eP (@Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) H) =
            fibredInSetoidsToPresheaf.map H := rfl
      rw [← he]
      exact eP.left_inv _
    have hK :
        eP.symm (fibredInSetoidsToPresheaf.map K) =
          @Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) K := by
      have he :
          eP (@Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) K) =
            fibredInSetoidsToPresheaf.map K := rfl
      rw [← he]
      exact eP.left_inv _
    have hq' :
        @Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) H =
          @Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) K := by
      rw [← hH, ← hK]
      exact hq
    have hSets' := congrArg eS hq'
    have hSH :
        eS (@Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) H) =
          fibredInSetoidsToFibredInSets.map H := rfl
    have hSK :
        eS (@Quotient.mk'' (A ⟶ B) (CategoryTheory.isIsomorphicSetoid (A ⟶ B)) K) =
          fibredInSetoidsToFibredInSets.map K := rfl
    rw [hSH, hSK] at hSets'
    exact hSets'
  exact fibredInSetoidsToFibredInSets_nonempty_iso_of_map_eq
    (X := A) (Y := B) (F := H) (G := K) hSets

/-- Helper for Lemma 4.39.8: every `2`-morphism between morphisms of categories fibred in setoids
is invertible. -/
private theorem fibredInSetoidsOver_two_hom_isIso
    {A B : FibredInSetoidsOver.{u, v, max u v, v} C} {H K : A ⟶ B} (η : H ⟶ K) :
    IsIso η := by
  -- Passing to quotient classes of `1`-morphisms identifies them with presheaf maps, and the
  -- given `2`-morphism makes those two presheaf maps equal componentwise.
  let e := FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom (C := C) (X := A) (Y := B)
  have hqMap : e (Quotient.mk'' H) = e (Quotient.mk'' K) := by
    ext U q
    refine Quotient.inductionOn q ?_
    intro x
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (B.p.Fiber (Opposite.unop U)))
          ((FibredInGroupoidsMor.fiberFunctor H.toHom (Opposite.unop U)).obj x) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (B.p.Fiber (Opposite.unop U)))
          ((FibredInGroupoidsMor.fiberFunctor K.toHom (Opposite.unop U)).obj x)
    have hηlift :
        Functor.IsHomLift B.p (𝟙 (Opposite.unop U))
          ((η.hom.hom.hom.hom.hom.hom).app x.1) := by
      exact BasedNatTrans.isHomLift (η.hom.hom.hom.hom.hom.hom) (by simpa [x.2])
    let m :
        ((FibredInGroupoidsMor.fiberFunctor H.toHom (Opposite.unop U)).obj x) ⟶
          ((FibredInGroupoidsMor.fiberFunctor K.toHom (Opposite.unop U)).obj x) :=
      ⟨(η.hom.hom.hom.hom.hom.hom).app x.1, hηlift⟩
    rw [Quotient.eq'']
    exact ⟨asIso m⟩
  have hq : Quotient.mk'' H = Quotient.mk'' K := e.injective hqMap
  rcases Quotient.exact hq with ⟨eHK⟩
  have hη : η = eHK.hom := (fibredInSetoidsOverTwoHom_subsingleton H K).elim _ _
  rw [hη]
  infer_instance

/-- Helper for Lemma 4.39.8: the bicategory of categories fibred in setoids over `C` is locally
groupoidal. -/
private noncomputable instance fibredInSetoidsOver_isLocallyGroupoid :
    Bicategory.IsLocallyGroupoid (FibredInSetoidsOver.{u, v, max u v, v} C) := by
  intro A B
  refine { all_isIso := ?_ }
  intro H K η
  exact fibredInSetoidsOver_two_hom_isIso (A := A) (B := B) (H := H) (K := K) η

/-- Helper for Lemma 4.39.8: a morphism of bicategorical squares induces the expected equalities on
the two projection maps after applying the presheaf of iso-classes construction. -/
private theorem square_hom_presheaf_leg_eq
    {P₁ P₂ : BicategoricalTwoCommutativeSquare F G}
    (u : P₁ ⟶ P₂) :
    fibredInSetoidsToPresheaf.map u.hom ≫ fibredInSetoidsToPresheaf.map P₂.p =
        fibredInSetoidsToPresheaf.map P₁.p ∧
      fibredInSetoidsToPresheaf.map u.hom ≫ fibredInSetoidsToPresheaf.map P₂.q =
        fibredInSetoidsToPresheaf.map P₁.q := by
  constructor
  · -- The left comparison `2`-cell becomes equality after passing to quotient presheaves.
    simpa [Functor.map_comp] using presheaf_map_eq_of_two_hom u.left
  · -- The right comparison `2`-cell is handled identically.
    simpa [Functor.map_comp] using presheaf_map_eq_of_two_hom u.right

/-- Helper for Lemma 4.39.8: a final square inherits the pullback property from any comparison
square whose presheaf image is already known to be a pullback. -/
private theorem isPullback_of_isFinal_of_pullback_square
    {P Q : BicategoricalTwoCommutativeSquare F G}
    (hQ :
      IsPullback
        (fibredInSetoidsToPresheaf.map Q.p)
        (fibredInSetoidsToPresheaf.map Q.q)
        (fibredInSetoidsToPresheaf.map F)
        (fibredInSetoidsToPresheaf.map G))
    (hP : Bicategory.IsFinal P) :
    IsPullback
      (fibredInSetoidsToPresheaf.map P.p)
      (fibredInSetoidsToPresheaf.map P.q)
      (fibredInSetoidsToPresheaf.map F)
      (fibredInSetoidsToPresheaf.map G) := by
  letI : Bicategory.IsFinal P := hP
  let u : Q ⟶ P := ⊤_ (Q ⟶ P)
  let β :
      fibredInSetoidsToPresheaf.obj Q.obj ⟶
        fibredInSetoidsToPresheaf.obj P.obj :=
    fibredInSetoidsToPresheaf.map u.hom
  let α :
      fibredInSetoidsToPresheaf.obj P.obj ⟶
        fibredInSetoidsToPresheaf.obj Q.obj :=
    hQ.lift
      (fibredInSetoidsToPresheaf.map P.p)
      (fibredInSetoidsToPresheaf.map P.q)
      (presheaf_square_comm (P := P))
  have hβp :
      β ≫ fibredInSetoidsToPresheaf.map P.p =
        fibredInSetoidsToPresheaf.map Q.p := by
    exact (square_hom_presheaf_leg_eq u).1
  have hβq :
      β ≫ fibredInSetoidsToPresheaf.map P.q =
        fibredInSetoidsToPresheaf.map Q.q := by
    exact (square_hom_presheaf_leg_eq u).2
  have hαp :
      α ≫ fibredInSetoidsToPresheaf.map Q.p =
        fibredInSetoidsToPresheaf.map P.p := by
    -- The pullback lift is defined precisely so that its left leg is `P.p`.
    simpa [α] using
      hQ.lift_fst
        (fibredInSetoidsToPresheaf.map P.p)
        (fibredInSetoidsToPresheaf.map P.q)
        (presheaf_square_comm (P := P))
  have hαq :
      α ≫ fibredInSetoidsToPresheaf.map Q.q =
        fibredInSetoidsToPresheaf.map P.q := by
    -- The same defining property on the right leg gives compatibility with `P.q`.
    simpa [α] using
      hQ.lift_snd
        (fibredInSetoidsToPresheaf.map P.p)
        (fibredInSetoidsToPresheaf.map P.q)
        (presheaf_square_comm (P := P))
  have hβα :
      β ≫ α = 𝟙 (fibredInSetoidsToPresheaf.obj Q.obj) := by
    -- The known pullback square sees `β ≫ α` and the identity as maps with the same two legs.
    apply hQ.hom_ext
    · calc
        (β ≫ α) ≫ fibredInSetoidsToPresheaf.map Q.p =
            β ≫ (α ≫ fibredInSetoidsToPresheaf.map Q.p) := by simp [Category.assoc]
        _ = β ≫ fibredInSetoidsToPresheaf.map P.p := by rw [hαp]
        _ = fibredInSetoidsToPresheaf.map Q.p := hβp
        _ = (𝟙 (fibredInSetoidsToPresheaf.obj Q.obj)) ≫
              fibredInSetoidsToPresheaf.map Q.p := by simp
    · calc
        (β ≫ α) ≫ fibredInSetoidsToPresheaf.map Q.q =
            β ≫ (α ≫ fibredInSetoidsToPresheaf.map Q.q) := by simp [Category.assoc]
        _ = β ≫ fibredInSetoidsToPresheaf.map P.q := by rw [hαq]
        _ = fibredInSetoidsToPresheaf.map Q.q := hβq
        _ = (𝟙 (fibredInSetoidsToPresheaf.obj Q.obj)) ≫
              fibredInSetoidsToPresheaf.map Q.q := by simp
  let a : P.obj ⟶ Q.obj := representative_hom_of_presheafHom α
  have ha :
      fibredInSetoidsToPresheaf.map a = α := by
    exact representative_hom_of_presheafHom_spec α
  have hleft_map :
      fibredInSetoidsToPresheaf.map (a ≫ Q.p) =
        fibredInSetoidsToPresheaf.map P.p := by
    -- Replacing `a` by the prescribed representative identifies the left leg of the lift.
    calc
      fibredInSetoidsToPresheaf.map (a ≫ Q.p) =
          fibredInSetoidsToPresheaf.map a ≫ fibredInSetoidsToPresheaf.map Q.p := by
            simp
      _ = α ≫ fibredInSetoidsToPresheaf.map Q.p := by rw [ha]
      _ = fibredInSetoidsToPresheaf.map P.p := hαp
  have hright_map :
      fibredInSetoidsToPresheaf.map (a ≫ Q.q) =
        fibredInSetoidsToPresheaf.map P.q := by
    -- The same replacement gives the right leg of the lift.
    calc
      fibredInSetoidsToPresheaf.map (a ≫ Q.q) =
          fibredInSetoidsToPresheaf.map a ≫ fibredInSetoidsToPresheaf.map Q.q := by
            simp
      _ = α ≫ fibredInSetoidsToPresheaf.map Q.q := by rw [ha]
      _ = fibredInSetoidsToPresheaf.map P.q := hαq
  let leftIso : a ≫ Q.p ≅ P.p := Classical.choice (nonempty_iso_of_presheaf_map_eq hleft_map)
  let rightIso : a ≫ Q.q ≅ P.q := Classical.choice (nonempty_iso_of_presheaf_map_eq hright_map)
  let v : P ⟶ Q :=
    { hom := a
      left := leftIso.hom
      right := rightIso.hom
      comm := by
        -- The square-compatibility constraint lives in a thin hom-set, so the chosen left and
        -- right comparison isomorphisms automatically satisfy it.
        letI :
            Subsingleton
              (((a ≫ Q.p) ≫ F) ⟶ (P.q ≫ G)) :=
          fibredInSetoidsOverTwoHom_subsingleton (((a ≫ Q.p) ≫ F)) (P.q ≫ G)
        exact Subsingleton.elim _ _ }
  have hαβ :
      α ≫ β = 𝟙 (fibredInSetoidsToPresheaf.obj P.obj) := by
    -- Finality of `P` gives a comparison `2`-cell from `v ≫ u` to the identity square map.
    let τ : v ≫ u ⟶ 𝟙 P :=
      (Bicategory.IsFinal.homIsTerminal (x := P) (y := P) (f := 𝟙 P)).from (v ≫ u)
    have hτmap :
        fibredInSetoidsToPresheaf.map ((v ≫ u).hom) =
          fibredInSetoidsToPresheaf.map ((𝟙 P : P ⟶ P).hom) := by
      exact presheaf_map_eq_of_two_hom τ.hom
    have hid :
        fibredInSetoidsToPresheaf.map ((𝟙 P : P ⟶ P).hom) =
          𝟙 (fibredInSetoidsToPresheaf.obj P.obj) := by
      change fibredInSetoidsToPresheaf.map (𝟙 P.obj) =
        𝟙 (fibredInSetoidsToPresheaf.obj P.obj)
      simp
    have hmap :
        fibredInSetoidsToPresheaf.map (a ≫ u.hom) =
          𝟙 (fibredInSetoidsToPresheaf.obj P.obj) := by
      calc
        fibredInSetoidsToPresheaf.map (a ≫ u.hom) =
            fibredInSetoidsToPresheaf.map ((v ≫ u).hom) := by rfl
        _ = fibredInSetoidsToPresheaf.map ((𝟙 P : P ⟶ P).hom) := hτmap
        _ = 𝟙 (fibredInSetoidsToPresheaf.obj P.obj) := hid
    calc
      α ≫ β = fibredInSetoidsToPresheaf.map a ≫ fibredInSetoidsToPresheaf.map u.hom := by
        rw [ha]
      _ = fibredInSetoidsToPresheaf.map (a ≫ u.hom) := by simp
      _ = 𝟙 (fibredInSetoidsToPresheaf.obj P.obj) := hmap
  let e :
      fibredInSetoidsToPresheaf.obj P.obj ≅
        fibredInSetoidsToPresheaf.obj Q.obj :=
    { hom := α
      inv := β
      hom_inv_id := hαβ
      inv_hom_id := hβα }
  -- Transport the known pullback square for `Q` across the resulting apex presheaf isomorphism.
  exact hQ.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) hαp hαq (by simp) (by simp)

-- Proof sketch: identify sections of the presheaf attached to a chosen bicategorical
-- `2`-fibre product square over each `U : C` with compatible pairs of isomorphism classes in the
-- fibers of `X` and `Z` over the common class in the fiber of `Y`; setoidness of the fibers
-- makes the comparison from the invertible `2`-morphism `P.ψ` collapse to equality on
-- isomorphism classes, and the finality of `P` gives the pullback universal property.
/-- Lemma 4.39.8: if `P` is a bicategorical `2`-fibre product square of morphisms of categories
fibred in setoids, then the presheaf of isomorphism classes associated to its apex is the
pullback of the presheaves associated to the two factors over the presheaf associated to the
base. -/
lemma isoClasses_presheaf_isPullback_of_isFinal
    (P : BicategoricalTwoCommutativeSquare F G) (hP : Bicategory.IsFinal P) :
    IsPullback
      (fibredInSetoidsToPresheaf.map P.p)
      (fibredInSetoidsToPresheaf.map P.q)
      (fibredInSetoidsToPresheaf.map F)
      (fibredInSetoidsToPresheaf.map G) := by
  -- Route correction: use the explicit pullback square as the known pullback and transport that
  -- universal property to `P` through the terminal comparison supplied by finality.
  let Q : BicategoricalTwoCommutativeSquare F G :=
    explicit_two_fibre_product_square (F := F) (G := G)
  let hQ :
      IsPullback
        (fibredInSetoidsToPresheaf.map Q.p)
        (fibredInSetoidsToPresheaf.map Q.q)
        (fibredInSetoidsToPresheaf.map F)
        (fibredInSetoidsToPresheaf.map G) :=
    explicit_two_fibre_product_presheaf_isPullback (F := F) (G := G)
  exact isPullback_of_isFinal_of_pullback_square (P := P) (Q := Q) hQ hP

end FibredInSetoidsOver

end CategoryTheory
