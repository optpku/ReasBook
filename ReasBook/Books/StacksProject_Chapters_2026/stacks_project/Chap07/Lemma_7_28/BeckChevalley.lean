module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import stacks_project.Chap07.Lemma_7_20_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.TwoSquare
open Opposite

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

noncomputable section

namespace CategoryTheory

section

variable {C' : Type u₁} [Category.{v₁} C']
variable {C : Type u₂} [Category.{v₂} C]
variable {D' : Type u₃} [Category.{v₃} D']
variable {D : Type u₄} [Category.{v₄} D]

variable (J' : GrothendieckTopology C') (J : GrothendieckTopology C)
variable (K' : GrothendieckTopology D') (K : GrothendieckTopology D)

variable {u' : C' ⥤ D'} {v' : C' ⥤ C} {u : C ⥤ D} {v : D' ⥤ D}

variable [Functor.IsCocontinuous u J K] [Functor.IsCocontinuous u' J' K']
variable [Functor.IsContinuous v K' K] [Functor.IsContinuous v' J' J]

/-
Domain-style sampling for Lemma 7.28.6:
- primary domain: base-change comparisons for sheaf pushforward and pullback functors on sites;
- sampled owner API:
  `CatCommSq`,
  `TwoSquare`,
  `TwoSquare.GuitartExact`,
  `TwoSquare.guitartExact_iff_final`,
  `Functor.pushforwardContinuousSheafificationComparison`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.pushforwardContinuousSheafificationCompatibility`,
  `Functor.sheafPullbackCocontinuous`,
  `Functor.sheafPullbackCocontinuousAdjunction`,
  `mateEquiv`,
  `Functor.whiskeringLeftObjCompIso`;
- source-facing layer: the base-change comparison for a commutative square of site functors;
- core/canonical layer: the sheaf functor owners
  `sheafPushforwardContinuous`, `sheafPushforwardCocontinuous`, and
  `sheafPullbackCocontinuous`, with
  the `CatCommSq v' u' u v` owner for the commutative square and the associated
  `TwoSquare.GuitartExact` exactness condition on its underlying `2`-cell;
- bridge/view layer: the induced comparison `2`-cells on inverse-image functors, the comparison
  morphisms between the two composite right adjoints, and their left-adjoint mates.

Primitive data are the chosen commutative-square owner `[CatCommSq v' u' u v]`, the
continuity/cocontinuity and Kan-extension hypotheses needed to form the sheaf functor owners, and
the finality condition on the canonical owner functors
`TwoSquare.costructuredArrowRightwards (CatCommSq.iso v' u' u v).hom V'`; the equivalent
exactness hypothesis is the canonical owner property
`TwoSquare.GuitartExact (CatCommSq.iso v' u' u v).hom` via
`TwoSquare.guitartExact_iff_final`. The public statements below therefore keep the owner-level
finality Beck-Chevalley isomorphism as the main source-facing entry and treat the
`GuitartExact`-based form as a companion used to construct it; the sheafification/pushforward
bridge is reused directly from the canonical owner
`Functor.pushforwardContinuousSheafificationCompatibility`.
-/

variable [∀ (F : C'ᵒᵖ ⥤ Type w), u'.op.HasPointwiseRightKanExtension F]
variable [∀ (F : Cᵒᵖ ⥤ Type w), u.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify J' (Type w)] [HasWeakSheafify J (Type w)]

/-- Helper for Lemma 7.28.6: the commutative-square comparison on inverse-image type functors,
built from strict presheaf commutativity and the continuous sheafification comparison on the
`v'`-side. -/
noncomputable def site_square_inverse_image_comparison
    (sq : CatCommSq v' u' u v) :
    v.sheafPushforwardContinuous (Type w) K' K ⋙
        u'.sheafPullbackCocontinuous (Type w) J' K' ⟶
      u.sheafPullbackCocontinuous (Type w) J K ⋙
        v'.sheafPushforwardContinuous (Type w) J' J :=
  let leftIso :
      v.sheafPushforwardContinuous (Type w) K' K ⋙
          u'.sheafPullbackCocontinuous (Type w) J' K' ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) := by
    calc
      v.sheafPushforwardContinuous (Type w) K' K ⋙
          u'.sheafPullbackCocontinuous (Type w) J' K' ≅
        v.sheafPushforwardContinuous (Type w) K' K ⋙
          sheafToPresheaf K' (Type w) ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) := by
          exact Iso.refl _
      _ ≅ sheafToPresheaf K (Type w) ⋙
            (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
            (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
            presheafToSheaf J' (Type w) := by
          simpa using
            Functor.isoWhiskerRight
              (v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K)
              ((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
                presheafToSheaf J' (Type w))
  let middleIso :
      sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (Type w)).obj v'.op ⋙
          presheafToSheaf J' (Type w) :=
    Functor.isoWhiskerLeft
      (sheafToPresheaf K (Type w))
      (Functor.isoWhiskerRight
        ((u'.op.whiskeringLeftObjCompIso v.op).symm ≪≫
          (Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).mapIso
            ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
              (NatIso.op sq.iso.symm).symm ≪≫
              (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _)) ≪≫
          v'.op.whiskeringLeftObjCompIso u.op)
        (presheafToSheaf J' (Type w)))
  let rightComparison :
      sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (Type w)).obj v'.op ⋙
          presheafToSheaf J' (Type w) ⟶
        u.sheafPullbackCocontinuous (Type w) J K ⋙
          v'.sheafPushforwardContinuous (Type w) J' J :=
    Functor.whiskerLeft
      (sheafToPresheaf K (Type w) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op)
      (v'.pushforwardContinuousSheafificationComparison J' J)
  -- Route correction: without extra cocontinuity data for `v'`, the `v'`-side contributes only
  -- the canonical comparison natural transformation, not an isomorphism.
  leftIso.hom ≫ middleIso.hom ≫ rightComparison

-- Proof sketch: start from the commutative square of inverse-image functors encoded by
-- `site_square_inverse_image_comparison`, and take its horizontal mate across
-- `u.sheafPullbackCocontinuousAdjunction` and `u'.sheafPullbackCocontinuousAdjunction`. This
-- yields the canonical base-change morphism `g⁻¹ f_* ⟶ f'_* (g')⁻¹` in left-to-right
-- composition notation.
/-- The canonical base-change morphism attached to the commutative square of site functors. -/
noncomputable def site_square_direct_image_inverse_image_baseChange
    (sq : CatCommSq v' u' u v) :
    u.sheafPushforwardCocontinuous (Type w) J K ⋙
        v.sheafPushforwardContinuous (Type w) K' K ⟶
      v'.sheafPushforwardContinuous (Type w) J' J ⋙
        u'.sheafPushforwardCocontinuous (Type w) J' K' :=
  (mateEquiv
      (u.sheafPullbackCocontinuousAdjunction J K)
      (u'.sheafPullbackCocontinuousAdjunction J' K')
      (site_square_inverse_image_comparison J' J K' K sq))

-- Proof sketch: opposing a Guitart exact square preserves Guitart exactness, and then the
-- canonical owner theorem `TwoSquare.guitartExact_iff_initial` supplies the required initiality
-- on the structured-arrow side of the opposite square.
omit [∀ (F : C'ᵒᵖ ⥤ Type w), u'.op.HasPointwiseRightKanExtension F]
  [∀ (F : Cᵒᵖ ⥤ Type w), u.op.HasPointwiseRightKanExtension F] in
/-- Helper for Lemma 7.28.6: the structured-arrow functor on the opposite square is initial. -/
theorem site_square_op_structuredArrowDownwards_initial
    (sq : CatCommSq v' u' u v)
    (hsq : TwoSquare.GuitartExact sq.iso.hom)
    (V' : D'ᵒᵖ) :
    Functor.Initial ((TwoSquare.op sq.iso.hom).structuredArrowDownwards V') := by
  -- Opposing the square converts the given finality package into the exact initiality needed for
  -- `Functor.Initial.limitIso`.
  let _ : TwoSquare.GuitartExact (TwoSquare.op sq.iso.hom) :=
    (TwoSquare.guitartExact_op_iff (w := sq.iso.hom)).2 hsq
  infer_instance

/-- Helper for Lemma 7.28.6: the opposite-square comparison obtained by transporting the canonical
`u.op.ranCounit` along the commutative square is a right-extension candidate for
`v'.op ⋙ ℱ.1` along `u'.op`. -/
noncomputable def site_square_presheaf_right_extension
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w)) :
    Functor.RightExtension u'.op (v'.op ⋙ ℱ.1) :=
  Functor.RightExtension.mk
    (v.op ⋙ u.op.ran.obj ℱ.1)
    ((Functor.isoWhiskerRight
        ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
          (NatIso.op sq.iso) ≪≫
          (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
        (u.op.ran.obj ℱ.1)).hom ≫
      (Functor.whiskerLeft v'.op (u.op.ranCounit.app ℱ.1)))

/-- Helper for Lemma 7.28.6: at `V'`, the cone attached to the presheaf-side right-extension
candidate is canonically isomorphic to the whiskering of the canonical cone for `u.op.ranCounit`
along the structured-arrow functor of the opposite square. -/
noncomputable def site_square_presheaf_right_extension_coneAt_iso_whisker
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w))
    (V' : D'ᵒᵖ) :
    (site_square_presheaf_right_extension (J := J) sq ℱ).coneAt V' ≅
      Limits.Cone.whisker ((TwoSquare.op sq.iso.hom).structuredArrowDownwards V')
        ((Functor.RightExtension.mk (u.op.ran.obj ℱ.1) (u.op.ranCounit.app ℱ.1)).coneAt
          (v.op.obj V')) := by
  -- Both cones are defined by the same structured-arrow legs after transporting along the square.
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro g
  simp [site_square_presheaf_right_extension, Functor.RightExtension.coneAt_π_app,
    TwoSquare.structuredArrowDownwards]

/-- Helper for Lemma 7.28.6: Guitart exactness makes the presheaf-side comparison a pointwise
right Kan extension, because the opposite structured-arrow functors are initial. -/
noncomputable def site_square_presheaf_right_extension_isPointwise_of_guitartExact
    (sq : CatCommSq v' u' u v)
    (hsq : TwoSquare.GuitartExact sq.iso.hom)
    (ℱ : Sheaf J (Type w)) :
    (site_square_presheaf_right_extension (J := J) sq ℱ).IsPointwiseRightKanExtension := by
  intro V'
  have hInitial :
      Functor.Initial ((TwoSquare.op sq.iso.hom).structuredArrowDownwards V') :=
    site_square_op_structuredArrowDownwards_initial (sq := sq) hsq V'
  let _ : Functor.Initial ((TwoSquare.op sq.iso.hom).structuredArrowDownwards V') := hInitial
  -- The source proof's cofinality comparison is exactly the initiality witness needed to transfer
  -- the canonical pointwise right Kan extension along `u.op`.
  refine Limits.IsLimit.ofIsoLimit
    (((Functor.Initial.isLimitWhiskerEquiv
        ((TwoSquare.op sq.iso.hom).structuredArrowDownwards V') _).symm
      (u.op.isPointwiseRightKanExtensionRanCounit ℱ.1 (v.op.obj V'))))
    (site_square_presheaf_right_extension_coneAt_iso_whisker (J := J) sq ℱ V').symm

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 7.28.6: after forgetting to presheaves, the counit of the restricted
cocontinuous pullback adjunction is the counit of the ambient composite adjunction. -/
lemma Functor.sheafPullbackCocontinuousAdjunction_counit_app_hom
    (G : C ⥤ D)
    (J : GrothendieckTopology C)
    (K : GrothendieckTopology D)
    [G.IsCocontinuous J K]
    [∀ (F : Cᵒᵖ ⥤ Type w), G.op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J (Type w)]
    (ℱ : Sheaf J (Type w)) :
    ((G.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ).hom =
      ((((G.op.ranAdjunction (Type w)).comp
          (sheafificationAdjunction J (Type w))).counit.app ℱ).hom) := by
  let commLeft :
      sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj G.op ⋙
          presheafToSheaf J (Type w) ≅
        G.sheafPullbackCocontinuous (Type w) J K ⋙ 𝟭 (Sheaf J (Type w)) :=
    Iso.refl _
  -- The restricted counit is obtained from the ambient counit by `restrictFullyFaithful`.
  have hCounit :=
    congrArg (fun f => f.hom)
      (((((G.op.ranAdjunction (Type w)).comp
          (sheafificationAdjunction J (Type w))).map_restrictFullyFaithful_counit_app
          (fullyFaithfulSheafToPresheaf K (Type w))
          (Functor.FullyFaithful.id _)
          commLeft
          (G.sheafPushforwardCocontinuousCompSheafToPresheafIso
            (Type w) J K).symm) ℱ))
  -- The left-side restriction comparison is definitional for cocontinuous pullback.
  simpa [commLeft, Functor.sheafPullbackCocontinuous] using hCounit

/-- Helper for Lemma 7.28.6: precomposing the source-facing `v'`-comparison with `toSheafify`
recovers whiskering of the presheaf sheafification unit. -/
lemma pushforwardContinuousSheafificationComparison_precompose_toSheafify_app
    (F : Cᵒᵖ ⥤ Type w)
    (U' : C'ᵒᵖ) :
    ((toSheafify J' (v'.op ⋙ F)).app U' ≫
        ((sheafToPresheaf J' (Type w)).map
          ((v'.pushforwardContinuousSheafificationComparison J' J).app F)).app U') =
      (Functor.whiskerLeft v'.op (toSheafify J F)).app U' := by
  -- This is the defining `sheafifyLift` equation for the source-facing comparison.
  change
    ((toSheafify J' (v'.op ⋙ F)).app U' ≫
        (sheafifyLift J'
          (Functor.whiskerLeft v'.op (toSheafify J F))
          ((presheafToSheaf J (Type w) ⋙ v'.sheafPushforwardContinuous (Type w) J' J).obj F).property).app
            U') =
      (Functor.whiskerLeft v'.op (toSheafify J F)).app U'
  exact
    congrArg (fun η => η.app U')
      (toSheafify_sheafifyLift J'
        (Functor.whiskerLeft v'.op (toSheafify J F))
        ((presheafToSheaf J (Type w) ⋙ v'.sheafPushforwardContinuous (Type w) J' J).obj F).property)

/-- Helper for Lemma 7.28.6: forgetting the image of a sheaf morphism under continuous
pushforward along `v'` is just whiskering its underlying presheaf morphism by `v'.op`. -/
lemma sheafPushforwardContinuous_map_app_eq_whiskerLeft
    {ℱ 𝒢 : Sheaf J (Type w)}
    (α : ℱ ⟶ 𝒢)
    (U' : C'ᵒᵖ) :
    ((sheafToPresheaf J' (Type w)).map
        ((v'.sheafPushforwardContinuous (Type w) J' J).map α)).app U' =
      (Functor.whiskerLeft v'.op ((sheafToPresheaf J (Type w)).map α)).app U' := by
  -- The continuous pushforward is defined by whiskering the underlying presheaf map.
  rfl

/-- Helper for Lemma 7.28.6: after precomposing with the sheafification unit, the left side of
`mateEquiv_counit` becomes the raw base-change component whiskered by `u'.op` and postcomposed
with the `ran` counit. -/
lemma
    site_square_direct_image_inverse_image_baseChange_mate_counit_left_whisker_eq_underlying_comp_counit
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w)) :
    toSheafify J'
        (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
          (((sheafToPresheaf K' (Type w)).obj
            ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))) ≫
      ((sheafToPresheaf J' (Type w)).map
        ((u'.sheafPullbackCocontinuous (Type w) J' K').map
            ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ) ≫
          (u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
            ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ))) =
      Functor.whiskerLeft u'.op
          ((sheafToPresheaf K' (Type w)).map
            ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ)) ≫
        (u'.op.ranCounit.app (v'.op ⋙ ℱ.1)) := by
  -- Route correction: normalize the `mateEquiv_counit` left side via the restricted unit/counit
  -- formulas before comparing it to the raw presheaf component at `u'.op.obj U'`.
  let η :=
    Functor.whiskerLeft u'.op
      ((sheafToPresheaf K' (Type w)).map
        ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ))
  -- After forgetting to presheaves, the restricted pullback functor acts by whiskering with
  -- `u'.op`, so the left side is exactly the `toSheafify` naturality square for `η`.
  rw [Functor.map_comp]
  have hnat :=
    toSheafify_naturality_assoc (J := J')
      (η := η)
      (h := (sheafToPresheaf J' (Type w)).map
        ((u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
          ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)))
  have hnat' :
      toSheafify J'
          (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
            ((sheafToPresheaf K' (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                  v.sheafPushforwardContinuous (Type w) K' K).obj ℱ))) ≫
        ((sheafToPresheaf J' (Type w)).map
            ((u'.sheafPullbackCocontinuous (Type w) J' K').map
              ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ))) ≫
          (sheafToPresheaf J' (Type w)).map
            ((u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
              ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)) =
        η ≫
          toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                ((sheafToPresheaf K' (Type w)).obj
                  ((v'.sheafPushforwardContinuous (Type w) J' J ⋙
                      u'.sheafPushforwardCocontinuous (Type w) J' K').obj ℱ))) ≫
            (sheafToPresheaf J' (Type w)).map
              ((u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
                ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)) := by
    simpa [η, Functor.sheafPullbackCocontinuous] using hnat.symm
  have hcounit :
      toSheafify J'
          (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
            ((sheafToPresheaf K' (Type w)).obj
              ((v'.sheafPushforwardContinuous (Type w) J' J ⋙
                  u'.sheafPushforwardCocontinuous (Type w) J' K').obj ℱ))) ≫
        (sheafToPresheaf J' (Type w)).map
          ((u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
            ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)) =
      u'.op.ranCounit.app (v'.op ⋙ ℱ.1) := by
    -- The ambient `ran` counit is exactly the factorization defining the restricted counit.
    change
      toSheafify J'
          (u'.op ⋙
            ((u'.sheafPushforwardCocontinuous (Type w) J' K').obj
              ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)).obj) ≫
        ((u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
          ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)).hom =
      u'.op.ranCounit.app (v'.op ⋙ ℱ.1)
    rw [Functor.sheafPullbackCocontinuousAdjunction_counit_app_hom]
    change
      toSheafify J'
          (u'.op ⋙
            ((u'.sheafPushforwardCocontinuous (Type w) J' K').obj
              ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)).obj) ≫
        sheafifyLift J'
          (u'.op.ranCounit.app
            ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ).obj)
          ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ).property =
      u'.op.ranCounit.app
        ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ).obj
    exact
      toSheafify_sheafifyLift J'
        (u'.op.ranCounit.app
          ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ).obj)
        ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ).property
  -- Compose the naturality square with the ambient counit identification.
  have hcomp :
      η ≫
          toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                ((sheafToPresheaf K' (Type w)).obj
                  ((v'.sheafPushforwardContinuous (Type w) J' J ⋙
                      u'.sheafPushforwardCocontinuous (Type w) J' K').obj ℱ))) ≫
            (sheafToPresheaf J' (Type w)).map
              ((u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
                ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ)) =
        η ≫ u'.op.ranCounit.app (v'.op ⋙ ℱ.1) := by
    exact congrArg (fun f => η ≫ f) hcounit
  simpa [η, Functor.map_comp, Category.assoc] using hnat'.trans hcomp

/-- Helper for Lemma 7.28.6: after precomposing with the sheafification unit, the right side of
`mateEquiv_counit` is exactly the transported presheaf right-extension morphism. -/
lemma site_square_inverse_image_comparison_transport_eq
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w)) :
    u'.op.whiskerLeft
          ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) ≫
        ((u'.op.whiskeringLeftObjCompIso v.op).inv.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (u'.op ⋙ v.op))).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (v' ⋙ u).op)).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        ((v'.op.whiskeringLeftObjCompIso u.op).hom.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) =
      (Functor.isoWhiskerRight
          ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
            (NatIso.op sq.iso) ≪≫
            (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
          (u.op.ran.obj ℱ.1)).hom := by
  -- The explicit transport chain in the square comparison is exactly the whiskered square
  -- isomorphism once the cocontinuous pushforward is unfolded to its ambient `ran`.
  ext X x
  simpa [Functor.sheafPushforwardCocontinuous]

/-- Helper for Lemma 7.28.6: before evaluating at an object of `C'ᵒᵖ`, precomposing the
source-facing inverse-image comparison with `toSheafify J'` exposes exactly the transported
square comparison `τ`, followed by the canonical `v'`-side sheafification comparison. -/
lemma toSheafify_comp_eq_of_eq
    {A B : C'ᵒᵖ ⥤ Type w}
    {f g : ((presheafToSheaf J' (Type w)).obj A).1 ⟶ B}
    (h : f = g) :
    toSheafify J' A ≫ f = toSheafify J' A ≫ g := by
  -- Precomposition by the sheafification unit preserves the owner-level forgotten equality.
  simpa [h]

/-- Helper for Lemma 7.28.6: the explicit owner transport chain is unchanged after deleting the
identity whiskers inserted by the two reflexive square-identifications. -/
lemma site_square_inverse_image_comparison_transport_with_id_whiskers_eq
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w)) :
    u'.op.whiskerLeft
          ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) ≫
        (u'.op.whiskeringLeftObjCompIso v.op).inv.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj ≫
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (u'.op ⋙ v.op))).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (v' ⋙ u).op)).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        (v'.op.whiskeringLeftObjCompIso u.op).hom.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj =
      u'.op.whiskerLeft
          ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) ≫
        (u'.op.whiskeringLeftObjCompIso v.op).inv.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj ≫
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        (v'.op.whiskeringLeftObjCompIso u.op).hom.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj := by
  -- The two inserted whiskers are identities, so the composite contracts immediately.
  simp

/-- Helper for Lemma 7.28.6: after evaluating the forgotten transported square comparison at
`U'`, the final `v'.op`-whiskering component carries the full transport chain with identity
whiskers to the trimmed transport chain. -/
lemma site_square_inverse_image_comparison_transport_component_eq
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w))
    (U' : C'ᵒᵖ)
    (a :
      ((sheafToPresheaf J' (Type w)).obj
            ((v.sheafPushforwardContinuous (Type w) K' K ⋙
                u'.sheafPullbackCocontinuous (Type w) J' K').obj
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))).obj
        U') :
    ((presheafToSheaf J' (Type w)).map
            ((v'.op.whiskeringLeftObjCompIso u.op).hom.app
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
      U'
      (((presheafToSheaf J' (Type w)).map
              (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (v' ⋙ u).op)).app
                ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
        U'
        (((presheafToSheaf J' (Type w)).map
                (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
                  ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
          U'
          (((presheafToSheaf J' (Type w)).map
                  (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (u'.op ⋙ v.op))).app
                    ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
            U'
            (((presheafToSheaf J' (Type w)).map
                    ((u'.op.whiskeringLeftObjCompIso v.op).inv.app
                      ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
              U'
              (((presheafToSheaf J' (Type w)).map
                      (u'.op.whiskerLeft
                        ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
                          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))).hom.app
                U' a))))) =
      ((presheafToSheaf J' (Type w)).map
            ((v'.op.whiskeringLeftObjCompIso u.op).hom.app
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
      U'
      (((presheafToSheaf J' (Type w)).map
              (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
                ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
        U'
        (((presheafToSheaf J' (Type w)).map
                ((u'.op.whiskeringLeftObjCompIso v.op).inv.app
                  ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom.app
          U'
          (((presheafToSheaf J' (Type w)).map
                  (u'.op.whiskerLeft
                    ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
                      ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))).hom.app
            U' a))) := by
  let σfull :
      u'.op ⋙
          ((v.sheafPushforwardContinuous (Type w) K' K).obj
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)).obj ⟶
        v'.op ⋙ u.op ⋙ u.op.ran.obj ℱ.1 :=
    u'.op.whiskerLeft
        ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) ≫
      (u'.op.whiskeringLeftObjCompIso v.op).inv.app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj ≫
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (u'.op ⋙ v.op))).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (v' ⋙ u).op)).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
      (v'.op.whiskeringLeftObjCompIso u.op).hom.app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj
  let σtrim :
      u'.op ⋙
          ((v.sheafPushforwardContinuous (Type w) K' K).obj
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)).obj ⟶
        v'.op ⋙ u.op ⋙ u.op.ran.obj ℱ.1 :=
    u'.op.whiskerLeft
        ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) ≫
      (u'.op.whiskeringLeftObjCompIso v.op).inv.app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj ≫
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
      (v'.op.whiskeringLeftObjCompIso u.op).hom.app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj
  -- Apply the presheaf transport cleanup after mapping it through sheafification.
  have hmap :
      ((presheafToSheaf J' (Type w)).map σfull).hom =
        ((presheafToSheaf J' (Type w)).map σtrim).hom := by
    -- This is the mapped form of deleting the two identity whiskers in `σfull`.
    simp [σfull, σtrim, Functor.map_comp, Category.assoc]
  -- Evaluating at `U'` and then at `a` yields the desired pointwise normalization.
  have happ :
      (((presheafToSheaf J' (Type w)).map σfull).hom.app U') a =
        (((presheafToSheaf J' (Type w)).map σtrim).hom.app U') a := by
    exact congrArg (fun k => k.app U' a) hmap
  simpa [σfull, σtrim, Functor.map_comp, Category.assoc] using happ

/-- Helper for Lemma 7.28.6: forgetting the source-facing inverse-image comparison identifies it
with the explicit transported square comparison `σ`, followed by the canonical `v'`-side
sheafification comparison. -/
lemma site_square_inverse_image_comparison_underlying_eq_sigma
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w)) :
    (sheafToPresheaf J' (Type w)).map
        ((site_square_inverse_image_comparison J' J K' K sq).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) =
      ((presheafToSheaf J' (Type w)).map
          (u'.op.whiskerLeft
              ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
                ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) ≫
            (u'.op.whiskeringLeftObjCompIso v.op).inv.app
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj ≫
            ((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj ≫
            (v'.op.whiskeringLeftObjCompIso u.op).hom.app
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom ≫
        (sheafToPresheaf J' (Type w)).map
      ((v'.pushforwardContinuousSheafificationComparison J' J).app
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
            ((sheafToPresheaf K (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))) := by
  -- Expose the forgotten owner wrapper componentwise before trimming the two identity whiskers.
  ext U' a
  simp [site_square_inverse_image_comparison, Functor.map_comp, NatTrans.comp_app,
    Category.assoc]
  -- The remaining comparison is functorial in the transported presheaf morphism, so it is enough
  -- to rewrite that morphism by the already-proved whisker-cleanup lemma.
  refine congrArg
    (fun x =>
      ((v'.pushforwardContinuousSheafificationComparison J' J).app
            (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
              ((sheafToPresheaf K (Type w)).obj
                ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))).hom.app U' x)
    ?_
  exact
    site_square_inverse_image_comparison_transport_component_eq
      (J' := J') (J := J) (K' := K') (K := K) (sq := sq) (ℱ := ℱ) U' a

lemma
    site_square_inverse_image_comparison_precompose_toSheafify_eq_sheafifyMap_transport
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w)) :
    toSheafify J'
        (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
          (((sheafToPresheaf K' (Type w)).obj
            ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))) ≫
      ((sheafToPresheaf J' (Type w)).map
        ((site_square_inverse_image_comparison J' J K' K sq).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))) =
    toSheafify J' (u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1) ≫
      sheafifyMap J'
        ((Functor.isoWhiskerRight
            ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
              (NatIso.op sq.iso) ≪≫
              (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
            (u.op.ran.obj ℱ.1)).hom) ≫
      (sheafToPresheaf J' (Type w)).map
        ((v'.pushforwardContinuousSheafificationComparison J' J).app
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
            ((sheafToPresheaf K (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))) := by
  let F : Cᵒᵖ ⥤ Type w :=
    (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
      ((sheafToPresheaf K (Type w)).obj
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))
  let τ :
      u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1 ⟶ v'.op ⋙ u.op ⋙ u.op.ran.obj ℱ.1 :=
    (Functor.isoWhiskerRight
      ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
        (NatIso.op sq.iso) ≪≫
        (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
      (u.op.ran.obj ℱ.1)).hom
  let σ :
      u'.op ⋙
          ((v.sheafPushforwardContinuous (Type w) K' K).obj
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)).obj ⟶
        v'.op ⋙ u.op ⋙ u.op.ran.obj ℱ.1 :=
    u'.op.whiskerLeft
        ((v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K).hom.app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)) ≫
      (u'.op.whiskeringLeftObjCompIso v.op).inv.app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj ≫
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (u'.op ⋙ v.op))).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op sq.iso.hom)).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (v' ⋙ u).op)).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
      (v'.op.whiskeringLeftObjCompIso u.op).hom.app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj
  have htransport' : ((presheafToSheaf J' (Type w)).map σ).hom = ((presheafToSheaf J' (Type w)).map τ).hom := by
    -- Lift the presheaf-level transport comparison into the sheafification functor.
    exact congrArg (fun y => ((presheafToSheaf J' (Type w)).map y).hom)
      (site_square_inverse_image_comparison_transport_eq
        (J := J) (K' := K') (K := K) (sq := sq) (ℱ := ℱ))
  have htransport'' :
      toSheafify J'
          (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
            (((sheafToPresheaf K' (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                  v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))) ≫
        ((presheafToSheaf J' (Type w)).map σ).hom ≫
        (sheafToPresheaf J' (Type w)).map
          ((v'.pushforwardContinuousSheafificationComparison J' J).app F) =
      toSheafify J' (u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1) ≫
        ((presheafToSheaf J' (Type w)).map τ).hom ≫
        (sheafToPresheaf J' (Type w)).map
          ((v'.pushforwardContinuousSheafificationComparison J' J).app F) := by
    -- Postcompose the lifted transport equality with the canonical `v'`-comparison.
    exact congrArg
      (fun k =>
        toSheafify J'
            (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
              (((sheafToPresheaf K' (Type w)).obj
                ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                    v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))) ≫
          k ≫
          (sheafToPresheaf J' (Type w)).map
            ((v'.pushforwardContinuousSheafificationComparison J' J).app F))
      htransport'
  have hid1 :
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (u'.op ⋙ v.op))).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) =
      𝟙 _ := by
    simp [Functor.map_id, NatTrans.id_app]
  have hid2 :
      (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (v' ⋙ u).op)).app
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) =
      𝟙 _ := by
    simp [Functor.map_id, NatTrans.id_app]
  have hmap_id1 :
      ((presheafToSheaf J' (Type w)).map
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (u'.op ⋙ v.op))).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom =
      𝟙 _ := by
    simpa [hid1]
  have hmap_id2 :
      ((presheafToSheaf J' (Type w)).map
        (((Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).map (𝟙 (v' ⋙ u).op)).app
          ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj)).hom =
      𝟙 _ := by
    simpa [hid2]
  have hmap_transport : ((presheafToSheaf J' (Type w)).map τ).hom = sheafifyMap J' τ := by
    rfl
  -- Expand `site_square_inverse_image_comparison` only to its owner-level factors, then rewrite
  -- the transport block via `htransport''`.
  have hleft :
      toSheafify J'
          (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
            (((sheafToPresheaf K' (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                  v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))) ≫
        ((sheafToPresheaf J' (Type w)).map
          ((site_square_inverse_image_comparison J' J K' K sq).app
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))) =
      toSheafify J'
          (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
            (((sheafToPresheaf K' (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                  v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))) ≫
        ((presheafToSheaf J' (Type w)).map σ).hom ≫
        (sheafToPresheaf J' (Type w)).map
          ((v'.pushforwardContinuousSheafificationComparison J' J).app F) := by
    -- Reduce the precomposition comparison to the exact owner-level forgotten equality.
    simpa [σ, hid1, hid2] using
      toSheafify_comp_eq_of_eq (J' := J')
        (site_square_inverse_image_comparison_underlying_eq_sigma
          (J' := J') (J := J) (K' := K') (K := K) (sq := sq) (ℱ := ℱ))
  have hright :
      toSheafify J' (u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1) ≫
          ((presheafToSheaf J' (Type w)).map τ).hom ≫
          (sheafToPresheaf J' (Type w)).map
            ((v'.pushforwardContinuousSheafificationComparison J' J).app F) =
      toSheafify J' (u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1) ≫
          sheafifyMap J' τ ≫
          (sheafToPresheaf J' (Type w)).map
            ((v'.pushforwardContinuousSheafificationComparison J' J).app F) := by
    simpa [hmap_transport]
  exact hleft.trans (htransport''.trans hright)

/-- Helper for Lemma 7.28.6: after precomposing with the sheafification unit, the right side of
`mateEquiv_counit` is exactly the transported presheaf right-extension morphism. -/
lemma
    site_square_inverse_image_comparison_precompose_toSheafify_app_eq_transport_whisker
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w))
    (U' : C'ᵒᵖ) :
    ((toSheafify J'
          (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
            (((sheafToPresheaf K' (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                  v.sheafPushforwardContinuous (Type w) K' K).obj ℱ))))).app U' ≫
        ((sheafToPresheaf J' (Type w)).map
          ((site_square_inverse_image_comparison J' J K' K sq).app
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))).app U') =
      (Functor.isoWhiskerRight
          ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
            (NatIso.op sq.iso) ≪≫
            (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
          (u.op.ran.obj ℱ.1)).hom.app U' ≫
        (Functor.whiskerLeft v'.op
          (toSheafify J
            (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
              ((sheafToPresheaf K (Type w)).obj
                ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))))).app U' := by
  -- Route correction: normalize the source-facing `v'`-comparison directly, without using the
  -- unavailable `v'`-cocontinuity compatibility isomorphism.
  let F : Cᵒᵖ ⥤ Type w :=
    (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
      ((sheafToPresheaf K (Type w)).obj
        ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))
  let τ :
      u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1 ⟶ v'.op ⋙ u.op ⋙ u.op.ran.obj ℱ.1 :=
    (Functor.isoWhiskerRight
      ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
        (NatIso.op sq.iso) ≪≫
        (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
      (u.op.ran.obj ℱ.1)).hom
  have hnat :=
    congrArg (fun η => η.app U')
      (toSheafify_naturality_assoc (J := J') (η := τ)
        (h := (sheafToPresheaf J' (Type w)).map
          ((v'.pushforwardContinuousSheafificationComparison J' J).app
            F)))
  have hcomp :=
    pushforwardContinuousSheafificationComparison_precompose_toSheafify_app
      (J' := J') (J := J) (v' := v') F
      U'
  have hstep1 :
      ((toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                ((sheafToPresheaf K' (Type w)).obj
                  ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                      v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))).app
            U' ≫
          ((sheafToPresheaf J' (Type w)).map
                  ((site_square_inverse_image_comparison J' J K' K sq).app
                    ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))).app
              U') =
        (fun η => η.app U')
          (toSheafify J' (u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1) ≫
            sheafifyMap J' τ ≫
              (sheafToPresheaf J' (Type w)).map
                ((v'.pushforwardContinuousSheafificationComparison J' J).app F)) := by
    -- Evaluate the owner-level normalization before any componentwise transport simplification.
    exact
      congrArg (fun η => η.app U')
        (site_square_inverse_image_comparison_precompose_toSheafify_eq_sheafifyMap_transport
          (J' := J') (J := J) (K' := K') (K := K) (sq := sq) (ℱ := ℱ))
  have hstep2 :
      (fun η => η.app U')
        (toSheafify J' (u'.op ⋙ v.op ⋙ u.op.ran.obj ℱ.1) ≫
          sheafifyMap J' τ ≫
            (sheafToPresheaf J' (Type w)).map
              ((v'.pushforwardContinuousSheafificationComparison J' J).app F)) =
        (fun η => η.app U')
          (τ ≫
            toSheafify J' (v'.op ⋙ u.op ⋙ u.op.ran.obj ℱ.1) ≫
              (sheafToPresheaf J' (Type w)).map
                ((v'.pushforwardContinuousSheafificationComparison J' J).app F)) := by
    exact hnat.symm
  have hstep3 :
      (fun η => η.app U')
        (τ ≫
          toSheafify J' (v'.op ⋙ u.op ⋙ u.op.ran.obj ℱ.1) ≫
            (sheafToPresheaf J' (Type w)).map
              ((v'.pushforwardContinuousSheafificationComparison J' J).app F)) =
        (Functor.isoWhiskerRight
                ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                  (NatIso.op sq.iso) ≪≫
                  (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
                (u.op.ran.obj ℱ.1)).hom.app U' ≫
          (toSheafify J' (v'.op ⋙ F)).app U' ≫
            ((sheafToPresheaf J' (Type w)).map
              ((v'.pushforwardContinuousSheafificationComparison J' J).app F)).app U' := by
    -- The transported square isomorphism is already the component carried by `τ`.
    rfl
  have hstep4 :
      (Functor.isoWhiskerRight
              ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                (NatIso.op sq.iso) ≪≫
                (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
              (u.op.ran.obj ℱ.1)).hom.app U' ≫
          (toSheafify J' (v'.op ⋙ F)).app U' ≫
            ((sheafToPresheaf J' (Type w)).map
              ((v'.pushforwardContinuousSheafificationComparison J' J).app F)).app U' =
        (Functor.isoWhiskerRight
                ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                  (NatIso.op sq.iso) ≪≫
                  (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
                (u.op.ran.obj ℱ.1)).hom.app U' ≫
          (Functor.whiskerLeft v'.op (toSheafify J F)).app U' := by
    simpa [Category.assoc] using
      congrArg
        (fun k =>
          (Functor.isoWhiskerRight
              ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                (NatIso.op sq.iso) ≪≫
                (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
              (u.op.ran.obj ℱ.1)).hom.app U' ≫ k)
        hcomp
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

/-- Helper for Lemma 7.28.6: after whiskering the `u`-side counit across `v'.op`, the full
right-hand side of `mateEquiv_counit` becomes the transported `u.op.ranCounit`. -/
lemma
    site_square_direct_image_inverse_image_baseChange_mate_counit_right_whisker_app_eq_presheaf_right_extension
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w))
    (U' : C'ᵒᵖ) :
    ((toSheafify J'
          (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
            (((sheafToPresheaf K' (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                  v.sheafPushforwardContinuous (Type w) K' K).obj ℱ))))).app U' ≫
        ((sheafToPresheaf J' (Type w)).map
          ((site_square_inverse_image_comparison J' J K' K sq).app
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ) ≫
            (v'.sheafPushforwardContinuous (Type w) J' J).map
              ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app U') =
      ((site_square_presheaf_right_extension (J := J) sq ℱ).hom).app U' := by
  -- First expose the raw transported `v'`-comparison before introducing the `u`-counit.
  rw [Functor.map_comp, NatTrans.comp_app]
  have hcompare :=
    site_square_inverse_image_comparison_precompose_toSheafify_app_eq_transport_whisker
      (J' := J') (J := J) (K' := K') (K := K) (sq := sq) (ℱ := ℱ) (U' := U')
  have hcompare' :=
    congrArg
      (fun k =>
        k ≫
          ((sheafToPresheaf J' (Type w)).map
            ((v'.sheafPushforwardContinuous (Type w) J' J).map
              ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app U')
      hcompare
  have hcompare'' :
      (toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                (((sheafToPresheaf K' (Type w)).obj
                  ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                      v.sheafPushforwardContinuous (Type w) K' K).obj ℱ))))).app U' ≫
            ((sheafToPresheaf J' (Type w)).map
                    ((site_square_inverse_image_comparison J' J K' K sq).app
                      ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))).app
                U' ≫
              ((sheafToPresheaf J' (Type w)).map
                    ((v'.sheafPushforwardContinuous (Type w) J' J).map
                      ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app
                U' =
        (Functor.isoWhiskerRight
                ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                  (NatIso.op sq.iso) ≪≫
                  (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
                (u.op.ran.obj ℱ.1)).hom.app
            U' ≫
          (Functor.whiskerLeft v'.op
                (toSheafify J
                  (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
                    ((sheafToPresheaf K (Type w)).obj
                      ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))))).app
              U' ≫
            ((sheafToPresheaf J' (Type w)).map
                  ((v'.sheafPushforwardContinuous (Type w) J' J).map
                    ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app
              U' := by
    simpa [Category.assoc] using hcompare'
  -- Then rewrite the whiskered sheaf-level counit to the ambient `u.op.ranCounit`.
  have hcounit :
      toSheafify J
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
            ((sheafToPresheaf K (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))) ≫
        (sheafToPresheaf J (Type w)).map
          ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ) =
      u.op.ranCounit.app ℱ.1 := by
    -- The restricted counit is the ambient `ran` counit followed by the sheafification factor.
    change
      toSheafify J
          (u.op ⋙
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ).hom =
      u.op.ranCounit.app ℱ.1
    rw [Functor.sheafPullbackCocontinuousAdjunction_counit_app_hom]
    change
      toSheafify J
          (u.op ⋙
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).obj) ≫
        sheafifyLift J
          (u.op.ranCounit.app ℱ.1)
          ℱ.property =
      u.op.ranCounit.app ℱ.1
    exact
      toSheafify_sheafifyLift J
        (u.op.ranCounit.app ℱ.1)
        ℱ.property
  have hcounit_whisker :
      (toSheafify J
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
            ((sheafToPresheaf K (Type w)).obj
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ)))).app
          (Opposite.op (v'.obj (unop U'))) ≫
        ((sheafToPresheaf J' (Type w)).map
          ((v'.sheafPushforwardContinuous (Type w) J' J).map
            ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app U' =
      (Functor.whiskerLeft v'.op (u.op.ranCounit.app ℱ.1)).app U' := by
    rw [sheafPushforwardContinuous_map_app_eq_whiskerLeft (J' := J') (J := J) (v' := v')
      ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ) U']
    simpa [Functor.whiskerLeft_app, Category.assoc] using
      congrArg (fun η => η.app U') (congrArg (Functor.whiskerLeft v'.op) hcounit)
  -- The resulting component is exactly the defining presheaf right-extension map.
  have hmid :
      (Functor.isoWhiskerRight
              ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                (NatIso.op sq.iso) ≪≫
                (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
              (u.op.ran.obj ℱ.1)).hom.app U' ≫
          (Functor.whiskerLeft v'.op
            (toSheafify J
              (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).obj
                ((sheafToPresheaf K (Type w)).obj
                  ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ))))).app U' ≫
          ((sheafToPresheaf J' (Type w)).map
            ((v'.sheafPushforwardContinuous (Type w) J' J).map
              ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app U' =
        (Functor.isoWhiskerRight
                ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                  (NatIso.op sq.iso) ≪≫
                  (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
                (u.op.ran.obj ℱ.1)).hom.app U' ≫
          (Functor.whiskerLeft v'.op (u.op.ranCounit.app ℱ.1)).app U' := by
    simpa [Category.assoc] using
      congrArg
        (fun k =>
          (Functor.isoWhiskerRight
              ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                (NatIso.op sq.iso) ≪≫
                (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
              (u.op.ran.obj ℱ.1)).hom.app U' ≫ k)
        hcounit_whisker
  have hfinal :
      (Functor.isoWhiskerRight
              ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
                (NatIso.op sq.iso) ≪≫
                (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
              (u.op.ran.obj ℱ.1)).hom.app U' ≫
          (Functor.whiskerLeft v'.op (u.op.ranCounit.app ℱ.1)).app U' =
        ((site_square_presheaf_right_extension (J := J) sq ℱ).hom).app U' := by
    rfl
  exact hcompare''.trans (hmid.trans hfinal)

/-- Helper for Lemma 7.28.6: after precomposing with the sheafification unit, the right side of
`mateEquiv_counit` is exactly the transported presheaf right-extension morphism. -/
lemma
    site_square_direct_image_inverse_image_baseChange_mate_counit_right_whisker_eq_presheaf_right_extension
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w)) :
    toSheafify J'
        (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
          (((sheafToPresheaf K' (Type w)).obj
            ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))) ≫
      ((sheafToPresheaf J' (Type w)).map
        ((site_square_inverse_image_comparison J' J K' K sq).app
            ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ) ≫
          (v'.sheafPushforwardContinuous (Type w) J' J).map
            ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))) =
      (site_square_presheaf_right_extension (J := J) sq ℱ).hom := by
  -- Evaluate componentwise so the source-facing comparison and the `u`-counit can be normalized
  -- separately before reassembling the transported `ran` counit.
  rw [Functor.map_comp]
  ext U' x
  simpa [Category.assoc] using
    congrFun
      (site_square_direct_image_inverse_image_baseChange_mate_counit_right_whisker_app_eq_presheaf_right_extension
        (J' := J') (J := J) (K' := K') (K := K) sq ℱ U')
      x

/-- Helper for Lemma 7.28.6: after forgetting to presheaves, the underlying base-change
component becomes the whiskered presheaf right-extension morphism after postcomposition with the
`u'.op.ranAdjunction` counit. -/
lemma
    site_square_direct_image_inverse_image_baseChange_underlying_comp_counit_eq_presheaf_right_extension
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w))
    (U' : C'ᵒᵖ) :
    (((sheafToPresheaf K' (Type w)).map
        ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ)).app
          (u'.op.obj U')) ≫
        (((u'.op.ranAdjunction (Type w)).counit.app (v'.op ⋙ ℱ.1)).app U') =
      ((site_square_presheaf_right_extension (J := J) sq ℱ).hom).app U' := by
  -- Route correction: compare the mate only after postcomposition with the ambient counit, where
  -- the restricted adjunction opens by a stable `map_restrictFullyFaithful_counit_app` formula.
  have hMate :=
    mateEquiv_counit
      (u.sheafPullbackCocontinuousAdjunction J K)
      (u'.sheafPullbackCocontinuousAdjunction J' K')
      (site_square_inverse_image_comparison J' J K' K sq)
      ℱ
  -- Evaluate the mate identity on `U'` after forgetting to presheaves.
  have hUnderlying :=
    congrArg
      (fun f =>
        (((sheafToPresheaf J' (Type w)).map f).app U'))
      hMate
  -- TODO for Lemma 7.28.6: replace the evaluated mate identity `hUnderlying` by the two
  -- precomposition lemmas above, then read off the component equality at `U'`.
  have hLeft :=
    site_square_direct_image_inverse_image_baseChange_mate_counit_left_whisker_eq_underlying_comp_counit
      (J' := J') (J := J) (K' := K') (K := K) sq ℱ
  have hRight :=
    site_square_direct_image_inverse_image_baseChange_mate_counit_right_whisker_eq_presheaf_right_extension
      (J' := J') (J := J) (K' := K') (K := K) sq ℱ
  -- The mate identity becomes the desired componentwise equality after the two presheaf-level
  -- normalizations and evaluation at `U'`.
  have hUnderlying0 :
      ((sheafToPresheaf J' (Type w)).map
          ((u'.sheafPullbackCocontinuous (Type w) J' K').map
              ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ) ≫
            (u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
              ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ))).app
        U' =
        ((sheafToPresheaf J' (Type w)).map
          ((site_square_inverse_image_comparison J' J K' K sq).app
              ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ) ≫
            (v'.sheafPushforwardContinuous (Type w) J' J).map
              ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app
        U' := by
    simpa [site_square_direct_image_inverse_image_baseChange, Functor.sheafPullbackCocontinuous,
      NatTrans.comp_app, Functor.map_comp, Category.assoc] using hUnderlying
  have hUnderlying' :
      ((toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                ((sheafToPresheaf K' (Type w)).obj
                  ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                      v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))).app
            U' ≫
          ((sheafToPresheaf J' (Type w)).map
                  ((u'.sheafPullbackCocontinuous (Type w) J' K').map
                      ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ) ≫
                    (u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
                      ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ))).app
              U') =
        ((toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                ((sheafToPresheaf K' (Type w)).obj
                  ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                      v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))).app
            U' ≫
          ((sheafToPresheaf J' (Type w)).map
                  ((site_square_inverse_image_comparison J' J K' K sq).app
                      ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ) ≫
                    (v'.sheafPushforwardContinuous (Type w) J' J).map
                      ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app
              U') := by
    exact congrArg
      (fun k =>
        (toSheafify J'
            (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
              ((sheafToPresheaf K' (Type w)).obj
                ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                    v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))).app U' ≫
          k)
      hUnderlying0
  have hLeftApp :
      (((sheafToPresheaf K' (Type w)).map
          ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ)).app
            (u'.op.obj U')) ≫
          (((u'.op.ranAdjunction (Type w)).counit.app (v'.op ⋙ ℱ.1)).app U') =
        ((toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                ((sheafToPresheaf K' (Type w)).obj
                  ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                      v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))).app
            U' ≫
          ((sheafToPresheaf J' (Type w)).map
                  ((u'.sheafPullbackCocontinuous (Type w) J' K').map
                      ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ) ≫
                    (u'.sheafPullbackCocontinuousAdjunction J' K').counit.app
                      ((v'.sheafPushforwardContinuous (Type w) J' J).obj ℱ))).app
              U') := by
    simpa [NatTrans.comp_app, Category.assoc] using
      (congrArg (fun η => η.app U')
        (site_square_direct_image_inverse_image_baseChange_mate_counit_left_whisker_eq_underlying_comp_counit
          (J' := J') (J := J) (K' := K') (K := K) sq ℱ)).symm
  have hRightApp :
      ((toSheafify J'
              (((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op).obj
                ((sheafToPresheaf K' (Type w)).obj
                  ((u.sheafPushforwardCocontinuous (Type w) J K ⋙
                      v.sheafPushforwardContinuous (Type w) K' K).obj ℱ)))).app
            U' ≫
          ((sheafToPresheaf J' (Type w)).map
                  ((site_square_inverse_image_comparison J' J K' K sq).app
                      ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ) ≫
                    (v'.sheafPushforwardContinuous (Type w) J' J).map
                      ((u.sheafPullbackCocontinuousAdjunction J K).counit.app ℱ))).app
              U') =
        ((site_square_presheaf_right_extension (J := J) sq ℱ).hom).app U' := by
    simpa [NatTrans.comp_app, Category.assoc] using
      congrArg (fun η => η.app U')
        (site_square_direct_image_inverse_image_baseChange_mate_counit_right_whisker_eq_presheaf_right_extension
          (J' := J') (J := J) (K' := K') (K := K) sq ℱ)
  exact hLeftApp.trans (hUnderlying'.trans hRightApp)

/-- Helper for Lemma 7.28.6: the underlying component of the sheaf-level base-change morphism is
the `u'.op.ranAdjunction` hom-equivalence image of the presheaf right-extension morphism. -/
lemma site_square_direct_image_inverse_image_baseChange_app_underlying_eq_ran_homEquiv
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w))
    (V' : D'ᵒᵖ) :
    (((sheafToPresheaf K' (Type w)).map
        ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ)).app V') =
      (((u'.op.ranAdjunction (Type w)).homEquiv
          (v.op ⋙ u.op.ran.obj ℱ.1) (v'.op ⋙ ℱ.1)
          (site_square_presheaf_right_extension (J := J) sq ℱ).hom).app V') := by
  -- Recover the raw `homEquiv` description from the counit-side comparison.
  let adj := u'.op.ranAdjunction (Type w)
  let lhs :
      v.op ⋙ u.op.ran.obj ℱ.1 ⟶ u'.op.ran.obj (v'.op ⋙ ℱ.1) :=
    (sheafToPresheaf K' (Type w)).map
      ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ)
  let rhs :=
    (site_square_presheaf_right_extension (J := J) sq ℱ).hom
  have hNat :
      lhs = adj.homEquiv (v.op ⋙ u.op.ran.obj ℱ.1) (v'.op ⋙ ℱ.1) rhs := by
    apply (adj.homEquiv (v.op ⋙ u.op.ran.obj ℱ.1) (v'.op ⋙ ℱ.1)).symm.injective
    ext U' a
    -- Compare both sides after postcomposition with the `ran` counit.
    rw [adj.homEquiv_counit]
    simp only [lhs, rhs, Equiv.symm_apply_apply]
    simpa using
      congrFun
        (site_square_direct_image_inverse_image_baseChange_underlying_comp_counit_eq_presheaf_right_extension
          (J' := J') (J := J) (K' := K') (K := K) sq ℱ U')
        a
  exact congrFun (congrArg NatTrans.app hNat) V'

omit [∀ (F : C'ᵒᵖ ⥤ Type w), u'.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J (Type w)] in
/-- Helper for Lemma 7.28.6: the presheaf-side right-extension morphism is obtained by
transporting `u.op.ranCounit` across the commutative square and evaluating at `U'`. -/
lemma site_square_presheaf_right_extension_hom_app
    (sq : CatCommSq v' u' u v)
    (ℱ : Sheaf J (Type w))
    (U' : C'ᵒᵖ) :
    (site_square_presheaf_right_extension (J := J) sq ℱ).hom.app U' =
      (Functor.isoWhiskerRight
          ((show u'.op ⋙ v.op ≅ (u' ⋙ v).op from Iso.refl _) ≪≫
            (NatIso.op sq.iso) ≪≫
            (show (v' ⋙ u).op ≅ v'.op ⋙ u.op from Iso.refl _))
          (u.op.ran.obj ℱ.1)).hom.app U' ≫
        (Functor.whiskerLeft v'.op (u.op.ranCounit.app ℱ.1)).app U' := by
  -- This is just the defining component formula for the transported right-extension morphism.
  rfl

-- Proof sketch: evaluate the canonical base-change morphism on a sheaf `ℱ` and an object
-- `V' : D'` using the right-Kan-extension descriptions of the cocontinuous pushforwards. The two
-- resulting limits are indexed by `CostructuredArrow u' V'` and `CostructuredArrow u (v.obj V')`.
-- Guitart exactness of the site square is the owner abstraction packaging the needed
-- finality hypotheses uniformly.
/-- Under Guitart exactness of the site square, the canonical base-change morphism is an
isomorphism. -/
theorem site_square_direct_image_inverse_image_baseChange_isIso_of_guitartExact
    (sq : CatCommSq v' u' u v)
    (hsq : TwoSquare.GuitartExact sq.iso.hom) :
    IsIso (site_square_direct_image_inverse_image_baseChange J' J K' K sq) := by
  let _ : TwoSquare.GuitartExact sq.iso.hom := hsq
  rw [NatTrans.isIso_iff_isIso_app]
  intro ℱ
  -- Reflect the sheaf-level comparison through the fully faithful inclusion into presheaves.
  have hUnderlying :
      IsIso
        (((sheafToPresheaf K' (Type w)).map
          ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V'
    have hInitial :
        Functor.Initial ((TwoSquare.op sq.iso.hom).structuredArrowDownwards V') :=
      site_square_op_structuredArrowDownwards_initial (sq := sq) hsq V'
    let _ : Functor.Initial ((TwoSquare.op sq.iso.hom).structuredArrowDownwards V') := hInitial
    have hIsoRan :
        IsIso
          ((((u'.op.ranAdjunction (Type w)).homEquiv
              (v.op ⋙ u.op.ran.obj ℱ.1) (v'.op ⋙ ℱ.1)
              (site_square_presheaf_right_extension (J := J) sq ℱ).hom).app V')) := by
      have hRight :
          (v.op ⋙ u.op.ran.obj ℱ.1).IsRightKanExtension
            ((site_square_presheaf_right_extension (J := J) sq ℱ).hom) :=
        (site_square_presheaf_right_extension_isPointwise_of_guitartExact
          (J := J) sq hsq ℱ).isRightKanExtension
      have hIsoNat :
          IsIso
            (((u'.op.ranAdjunction (Type w)).homEquiv
              (v.op ⋙ u.op.ran.obj ℱ.1) (v'.op ⋙ ℱ.1)
              (site_square_presheaf_right_extension (J := J) sq ℱ).hom)) := by
        exact
          (u'.op.isIso_ranAdjunction_homEquiv_iff
            ((site_square_presheaf_right_extension (J := J) sq ℱ).hom)).2 hRight
      exact inferInstance
    have hEq :
        (((sheafToPresheaf K' (Type w)).map
            ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ)).app V') =
          (((u'.op.ranAdjunction (Type w)).homEquiv
              (v.op ⋙ u.op.ran.obj ℱ.1) (v'.op ⋙ ℱ.1)
              (site_square_presheaf_right_extension (J := J) sq ℱ).hom).app V') := by
      -- The remaining normalization is exactly the presheaf-level `ran` hom-equivalence formula.
      exact
        site_square_direct_image_inverse_image_baseChange_app_underlying_eq_ran_homEquiv
          (J' := J') (J := J) (K' := K') (K := K) sq ℱ V'
    rw [hEq]
    exact hIsoRan
  let _ := hUnderlying
  exact
    (CategoryTheory.isIso_of_reflects_iso
      ((site_square_direct_image_inverse_image_baseChange J' J K' K sq).app ℱ)
      (sheafToPresheaf K' (Type w)))

-- Proof sketch: `site_square_direct_image_inverse_image_baseChange` is the canonical comparison in
-- the direction `g⁻¹ f_* ⟶ f'_* (g')⁻¹`; under Guitart exactness of the site square it
-- is an isomorphism, so we package its inverse as the comparison
-- `f'_* (g')⁻¹ ≅ g⁻¹ f_*`.
/-- `GuitartExact` companion to `site_square_direct_image_inverse_image_iso`. -/
noncomputable def site_square_direct_image_inverse_image_iso_of_guitartExact
    (sq : CatCommSq v' u' u v)
    (hsq : TwoSquare.GuitartExact sq.iso.hom) :
    v'.sheafPushforwardContinuous (Type w) J' J ⋙
        u'.sheafPushforwardCocontinuous (Type w) J' K' ≅
      u.sheafPushforwardCocontinuous (Type w) J K ⋙
        v.sheafPushforwardContinuous (Type w) K' K := by
  let _ : IsIso (site_square_direct_image_inverse_image_baseChange J' J K' K sq) :=
    site_square_direct_image_inverse_image_baseChange_isIso_of_guitartExact
      J' J K' K sq hsq
  exact
    (asIso (site_square_direct_image_inverse_image_baseChange J' J K' K sq)).symm

/-- Lemma 7.28.6: for a `CatCommSq` of site functors
`C' ⥤ C`, `C' ⥤ D'`, `C ⥤ D`, and `D' ⥤ D` with `u,u'` cocontinuous and `v,v'`
continuous, if for every
`V' : D'` the canonical functor
`TwoSquare.costructuredArrowRightwards sq.iso.hom V' :
CostructuredArrow u' V' ⥤ CostructuredArrow u (v.obj V')`
is final, then direct image along `u'` after inverse image along `v'` is canonically isomorphic to
inverse image along `v` after direct image along `u`. -/
noncomputable def site_square_direct_image_inverse_image_iso
    (sq : CatCommSq v' u' u v)
    (hfinal : ∀ V' : D', (TwoSquare.costructuredArrowRightwards sq.iso.hom V').Final) :
    v'.sheafPushforwardContinuous (Type w) J' J ⋙
      u'.sheafPushforwardCocontinuous (Type w) J' K' ≅
      u.sheafPushforwardCocontinuous (Type w) J K ⋙
        v.sheafPushforwardContinuous (Type w) K' K := by
  let hsq : TwoSquare.GuitartExact sq.iso.hom :=
    (TwoSquare.guitartExact_iff_final sq.iso.hom).2 hfinal
  exact site_square_direct_image_inverse_image_iso_of_guitartExact
    J' J K' K sq hsq

-- Proof sketch: this is the defining `Iso.hom_inv_id` identity for the canonical Beck-Chevalley
-- isomorphism `site_square_direct_image_inverse_image_iso`.
/-- The canonical direct-image/inverse-image comparison isomorphism has the expected left inverse
identity. -/
theorem site_square_direct_image_inverse_image_iso_hom_inv_id
    (sq : CatCommSq v' u' u v)
    (hfinal : ∀ V' : D', (TwoSquare.costructuredArrowRightwards sq.iso.hom V').Final) :
    (site_square_direct_image_inverse_image_iso J' J K' K sq hfinal).hom ≫
        (site_square_direct_image_inverse_image_iso J' J K' K sq hfinal).inv =
      𝟙
        (v'.sheafPushforwardContinuous (Type w) J' J ⋙
          u'.sheafPushforwardCocontinuous (Type w) J' K') := by
  -- This is the defining `Iso.hom_inv_id` identity for the Beck-Chevalley isomorphism.
  exact (site_square_direct_image_inverse_image_iso J' J K' K sq hfinal).hom_inv_id

end

end CategoryTheory
