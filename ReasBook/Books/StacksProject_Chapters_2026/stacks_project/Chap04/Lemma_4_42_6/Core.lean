module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Lemma_4_42_6.SliceRepresentable

@[expose] public section

/-!
# Core helpers for Lemma 4.42.6

This module collects the reusable owner-level helpers extracted from the main `Lemma_4_42_6.lean`
file so that the two direction proofs (`Direction1.lean`, `Direction2.lean`) can share them without
public import cycles. These are the diagonal owner, the equivalence-transport of representability, and the
product-slice / diagonal base-change scaffolding.
-/

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver

variable {C : Type (max u v)} [Category.{v} C]

open Functor IsHomLift IsStronglyCartesian Bicategory

/-! ### A `2`-cell of categories fibred in groupoids into a groupoid fibration is invertible -/

/-- A morphism of the total category lying over an identity arrow, into a category fibred in
groupoids, is an isomorphism. (This is the standard "verticals are invertible" fact; cf. the
argument in `Definition_4_35_1` showing fibers are groupoids.) -/
theorem cfg_hom_over_id_isIso {𝒮 𝒞 : Type*} [Category 𝒮] [Category 𝒞]
    {p : 𝒮 ⥤ 𝒞} [IsFibredInGroupoids p] {U : 𝒞} {a b : 𝒮}
    (φ : a ⟶ b) (hφ : p.IsHomLift (𝟙 U) φ) : IsIso φ := by
  letI : p.IsHomLift (𝟙 U) φ := hφ
  -- The base image of `φ` is the identity up to `eqToHom`, hence an isomorphism.
  haveI : IsIso (p.map φ) := by
    simpa [fac' p (𝟙 U) φ] using
      (show IsIso (eqToHom (domain_eq p (𝟙 U) φ) ≫ 𝟙 U ≫ eqToHom (codomain_eq p (𝟙 U) φ).symm)
        from inferInstance)
  -- In a groupoid fibration every morphism is strongly cartesian over its own base image.
  haveI : p.IsStronglyCartesian (p.map φ) φ :=
    (inferInstance : IsFibredInGroupoids p).isStronglyCartesian_map φ
  exact IsStronglyCartesian.isIso_of_base_isIso p (p.map φ) φ

/-- A `2`-morphism of based functors over `C` whose target category is fibred in groupoids is
invertible: its components lift identities, hence are isomorphisms. -/
theorem based_natTrans_into_cfg_isIso
    {𝒳 : BasedCategory.{v₁, u₁} C} {𝒴 : BasedCategory.{v₂, u₂} C} [IsFibredInGroupoids 𝒴.p]
    {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) : IsIso α := by
  haveI happ : ∀ a : 𝒳.obj, IsIso (α.toNatTrans.app a) := fun a =>
    cfg_hom_over_id_isIso (α.toNatTrans.app a) (α.app_isHomLift a)
  haveI : IsIso (X := F.toFunctor) α.toNatTrans := NatIso.isIso_of_isIso_app α.toNatTrans
  exact BasedNatIso.isIso_of_toNatTrans_isIso α

/-- A `2`-morphism of morphisms of fibred categories over `C`, with target fibred in groupoids,
is invertible. (The hom-category inclusion to based natural transformations is fully faithful, and
the corresponding based natural transformation is invertible by `based_natTrans_into_cfg_isIso`.) -/
theorem fibredCategoryMor_twoCell_into_cfg_isIso
    {X Y : FibredCategoryOver C} [IsFibredInGroupoids Y.p] {F G : X ⟶ Y} (α : F ⟶ G) :
    IsIso α := by
  set incl := ((fibredCategoryOverSubTwoCategory C).hom X Y).inclusion with hincl
  haveI : incl.Full := ⟨fun {F' G'} η => ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩⟩
  haveI : incl.Faithful := inferInstance
  haveI : IsIso (incl.map α) := based_natTrans_into_cfg_isIso (incl.map α)
  exact isIso_of_fully_faithful incl α

/-- A `2`-morphism in `FibredInGroupoidsOver C` is invertible: `FibredInGroupoidsOver C` is a
`(2,1)`-category. -/
theorem fibredInGroupoidsMor_twoCell_isIso
    {X Y : FibredInGroupoidsOver C} {F G : X ⟶ Y} (α : F ⟶ G) : IsIso α := by
  set incl := ((fibredInGroupoidsOverSubTwoCategory C).hom X Y).inclusion with hincl
  haveI : incl.Full := inferInstance
  haveI : incl.Faithful := inferInstance
  haveI : IsFibredInGroupoids Y.toFibredCategoryOver.p := Y.property
  haveI : IsIso (incl.map α) := fibredCategoryMor_twoCell_into_cfg_isIso (incl.map α)
  exact isIso_of_fully_faithful incl α

/-- The `2`-category of categories fibred in groupoids over `C` is locally groupoidal. -/
instance fibredInGroupoidsOver_isLocallyGroupoid :
    Bicategory.IsLocallyGroupoid (FibredInGroupoidsOver C) :=
  fun _ _ => ⟨fun α => fibredInGroupoidsMor_twoCell_isIso α⟩

/-! ### Uniqueness of final objects in a locally groupoidal bicategory -/

/-- In a locally groupoidal bicategory, any two parallel `1`-morphisms into a final object are
isomorphic (via the unique comparison `2`-morphism, which is invertible). -/
noncomputable def isoOfFinal {B : Type*} [Bicategory B] [IsLocallyGroupoid B]
    {x y : B} [IsFinal y] (f g : x ⟶ y) : f ≅ g :=
  haveI : IsGroupoid (x ⟶ y) := ‹IsLocallyGroupoid B› x y
  asIso (default : f ⟶ g)

/-- In a locally groupoidal bicategory, any two final objects are bicategorically equivalent.
This is the uniqueness of `2`-fibre products: applied in the bicategory of `2`-commutative squares
over a fixed cospan, two final squares have equivalent apexes. -/
noncomputable def equivalenceOfFinal {B : Type*} [Bicategory B] [IsLocallyGroupoid B]
    (x y : B) [IsFinal x] [IsFinal y] : Bicategory.Equivalence x y :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (isoOfFinal (𝟙 x) ((⊤_ (x ⟶ y)) ≫ (⊤_ (y ⟶ x))))
    (isoOfFinal ((⊤_ (y ⟶ x)) ≫ (⊤_ (x ⟶ y))) (𝟙 y))


namespace FibredInGroupoidsMor

/-- Helper for Lemma 4.42.6: the canonical self-`2`-fibre-product target of the diagonal of a
morphism of categories fibred in groupoids over `C`. -/
noncomputable def twoFibreProductDiagonalTarget
    {X Y : FibredInGroupoidsOver C}
    (F : X ⟶ Y) : FibredInGroupoidsOver C :=
  FibredInGroupoidsOver.twoFibreProduct F F

/-- Helper for Lemma 4.42.6: the canonical diagonal morphism into the explicit self-pullback. -/
@[irreducible] noncomputable def twoFibreProductDiagonalMor
    {X Y : FibredInGroupoidsOver C}
    (F : X ⟶ Y) : X ⟶ FibredInGroupoidsOver.twoFibreProduct F F := by
  let P : BicategoricalTwoCommutativeSquare F F :=
    { obj := X
      p := 𝟙 X
      q := 𝟙 X
      ψ := Iso.refl F }
  let T := FibredInGroupoidsOver.twoFibreProductSquare F F
  letI : Bicategory.IsFinal T :=
    FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct F F
  exact (⊤_ (P ⟶ T)).hom

end FibredInGroupoidsMor

/-- Helper for Lemma 4.42.6: representability of a category fibred in groupoids is preserved by
equivalence over the fixed base category. -/
theorem isRepresentable_iff_of_equivalence_over_base
    {P Q : FibredInGroupoidsOver C}
    (e : Bicategory.Equivalence P Q) :
    P.IsRepresentable ↔ Q.IsRepresentable := by
  -- Transport representability through the presentation criterion over a slice category.
  rw [FibredInGroupoidsOver.isRepresentable_iff_exists_presentation,
    FibredInGroupoidsOver.isRepresentable_iff_exists_presentation]
  constructor
  · rintro ⟨U, j, hj⟩
    refine ⟨U, e.inv ≫ j, ?_⟩
    -- The inverse side of the given equivalence is again an equivalence over the base.
    have heInv : FibredInGroupoidsMor.IsEquivalenceOverBase e.inv := by
      let eInv : Bicategory.Equivalence Q P :=
        Bicategory.Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm
      simpa using FibredInGroupoidsOver.hom_isEquivalenceOverBase eInv
    -- Composing two equivalences over the base keeps the presentation representable.
    change BasedFunctor.IsEquivalenceOverBase
      (BasedFunctor.comp (FibredInGroupoidsMor.toBasedFunctor e.inv)
        (FibredInGroupoidsMor.toBasedFunctor j))
    exact BasedFunctor.IsEquivalenceOverBase.comp heInv hj
  · rintro ⟨U, j, hj⟩
    refine ⟨U, e.hom ≫ j, ?_⟩
    -- Compose the transported presentation with the forward half of the equivalence.
    change BasedFunctor.IsEquivalenceOverBase
      (BasedFunctor.comp (FibredInGroupoidsMor.toBasedFunctor e.hom)
        (FibredInGroupoidsMor.toBasedFunctor j))
    exact BasedFunctor.IsEquivalenceOverBase.comp
      (FibredInGroupoidsOver.hom_isEquivalenceOverBase e) hj

/-- Helper for Lemma 4.42.6: precomposing a slice morphism with `Over.map f` gives the pulled-back
slice morphism over the new base object. -/
noncomputable abbrev over_map_morphism
    {U V : C} (f : V ⟶ U) :
    ofFunctor (Over.forget V) ⟶ ofFunctor (Over.forget U) :=
  FibredInGroupoidsMor.ofBasedFunctor
    (show (ofFunctor (Over.forget V)).toBasedCategory ⥤ᵇ
        (ofFunctor (Over.forget U)).toBasedCategory from
      { toFunctor := Over.map f
        w := by rfl })

/-- Helper for Lemma 4.42.6: precomposing a slice morphism with `Over.map f` gives the pulled-back
slice morphism over the new base object. -/
noncomputable abbrev slice_morphism_pullback
    (X : FibredInGroupoidsOver C)
    {U V : C} (f : V ⟶ U) (G : ofFunctor (Over.forget U) ⟶ X) :
    ofFunctor (Over.forget V) ⟶ X :=
  over_map_morphism f ≫ G

/-- Helper for Lemma 4.42.6: the pulled-back test morphisms over `U × V` package into a single
morphism to the diagonal target of `X`. -/
noncomputable abbrev product_slice_pullbacks_base_projection_iso
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C)
    {U V : C}
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    ((slice_morphism_pullback X Limits.prod.fst G) ≫ X.baseProjection) ≅
      ((slice_morphism_pullback X Limits.prod.snd G') ≫ X.baseProjection) := by
  -- Both composites are the canonical base projection from the product slice.
  refine eqToIso ?_
  let Lbf :=
    FibredInGroupoidsMor.toBasedFunctor
      ((slice_morphism_pullback X (Limits.prod.fst (X := U) (Y := V)) G) ≫
      X.baseProjection)
  let Rbf :=
    FibredInGroupoidsMor.toBasedFunctor
      ((slice_morphism_pullback X (Limits.prod.snd (X := U) (Y := V)) G') ≫
      X.baseProjection)
  change FibredInGroupoidsMor.ofBasedFunctor Lbf = FibredInGroupoidsMor.ofBasedFunctor Rbf
  have hL : Lbf.toFunctor = Over.forget (Limits.prod U V) := by
    calc
      Lbf.toFunctor = Over.map (Limits.prod.fst (X := U) (Y := V)) ⋙ Over.forget U := by
        simpa [Lbf, slice_morphism_pullback, over_map_morphism, Category.assoc] using
          congrArg (fun k => Over.map (Limits.prod.fst (X := U) (Y := V)) ⋙ k)
            (FibredInGroupoidsMor.comm G)
      _ = Over.forget (Limits.prod U V) := by
        rfl
  have hR : Rbf.toFunctor = Over.forget (Limits.prod U V) := by
    calc
      Rbf.toFunctor = Over.map (Limits.prod.snd (X := U) (Y := V)) ⋙ Over.forget V := by
        simpa [Rbf, slice_morphism_pullback, over_map_morphism, Category.assoc] using
          congrArg (fun k => Over.map (Limits.prod.snd (X := U) (Y := V)) ⋙ k)
            (FibredInGroupoidsMor.comm G')
      _ = Over.forget (Limits.prod U V) := by
        rfl
  have hFun : Lbf.toFunctor = Rbf.toFunctor := hL.trans hR.symm
  revert hFun
  cases Lbf
  cases Rbf
  intro hFun
  cases hFun
  simp

/-- Helper for Lemma 4.42.6: the product-base square formed by the two pulled-back slice maps is
the source square whose terminal factorization defines the comparison to the diagonal target. -/
noncomputable def product_slice_to_diagonal_target
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C)
    {U V : C}
    (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    ofFunctor (Over.forget (Limits.prod U V)) ⟶
      FibredInGroupoidsMor.twoFibreProductDiagonalTarget X.baseProjection := by
  let P : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection :=
    { obj := ofFunctor (Over.forget (Limits.prod U V))
      p := slice_morphism_pullback X Limits.prod.fst G
      q := slice_morphism_pullback X Limits.prod.snd G'
      ψ := product_slice_pullbacks_base_projection_iso X G G' }
  let T := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  letI : Bicategory.IsFinal T :=
    FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct
      X.baseProjection X.baseProjection
  unfold FibredInGroupoidsMor.twoFibreProductDiagonalTarget
  exact (⊤_ (P ⟶ T)).hom

/-- Helper for Lemma 4.42.6: applying the representability criterion for the diagonal to a single
test morphism into the diagonal target produces the corresponding representable slice base change.
-/
theorem diagonal_slice_basechange_representable
    [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hDiagonal :
      FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection))
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    (FibredInGroupoidsMor.sliceTwoFibreProduct
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) H).IsRepresentable := by
  -- Unfold the representability predicate for the diagonal and specialize it to the chosen test
  -- morphism into the diagonal target.
  rw [FibredInGroupoidsMor.isRepresentable_iff_forall_sliceTwoFibreProduct_isRepresentable] at hDiagonal
  exact hDiagonal H

/-- Absolute form of `diagonal_slice_basechange_representable`: after composing the slice base with
`C`, the diagonal base change is the bundled two-fibre product of the test map and the diagonal. -/
theorem diagonal_twoFibreProduct_isRepresentable_of_representable
    [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hDiagonal :
      FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection))
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct H
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)).IsRepresentable := by
  have hRep := diagonal_slice_basechange_representable X hDiagonal H
  rw [isRepresentable_iff_absolutize_isRepresentable] at hRep
  rw [absolutize_sliceTwoFibreProduct_eq
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) H] at hRep
  exact hRep

/-- Helper for Lemma 4.42.6: the global slice representability hypothesis specializes to any
ordinary pullback of a slice morphism along `Over.map f`. -/
theorem slice_morphism_pullback_representable
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G)
    {U V : C}
    (f : V ⟶ U)
    (G : ofFunctor (Over.forget U) ⟶ X) :
    FibredInGroupoidsMor.IsRepresentable (slice_morphism_pullback X f G) := by
  -- Apply the global slice criterion to the rebased morphism over the new slice base.
  exact hAll (slice_morphism_pullback X f G)

end CategoryTheory
