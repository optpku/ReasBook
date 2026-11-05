module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Example_4_31_3
public import stacks_project.Chap04.Lemma_4_33_8
public import stacks_project.Chap04.Lemma_4_35_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryOver
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open Functor
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X Y Z : CategoryOver C}

/- Domain-style sampling for Remark 4.35.8:
-- primary domain: comparison between the explicit `2`-fibre product in `Cat/C` and the standard
  categorical pullback of the underlying functors, after using the fibred-in-groupoids hypotheses
  to transport along base isomorphisms;
- sampled owner-level declarations:
  `CategoryOver.explicitTwoFibreProductSquareOver`,
  `explicitTwoFibreProductComparisonIsoOver`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`;
-- best owner abstraction: the source-facing owner is the over-`C` square
  `explicitTwoFibreProductSquare F G`; the comparison with the ordinary categorical pullback is
  a fibred-in-groupoids consequence, not a pure `Cat`-level consequence of forgetting the base;
- primitive data: owned upstream by `explicitTwoFibreProductSquareOver F G`;
-- derived API: the comparison functor and the resulting equivalence with the standard categorical
  pullback under the fibred-in-groupoids assumptions.

Source/core/bridge triage:
-- `source-facing`: the comparison equivalence of Remark 4.35.8;
-- `core/canonical`: `explicitTwoFibreProductSquare F G`;
- `bridge/view`: the forgotten categorical square and its induced functor to
  `F.toFunctor ⊡ G.toFunctor`. -/

/- Lemma 4.35.7 supplies the fibred-in-groupoids closure statement for the explicit
`2`-fibre-product apex; the comparison equivalence below is the separate categorical consequence
of the owner square `explicitTwoFibreProductSquareOver F G`. -/
#check CategoryTheory.explicitTwoFibreProductProjection_isFibredInGroupoids

/-- Helper for Remark 4.35.8: the canonical comparison functor from the explicit pullback over
`C` to the ordinary categorical pullback forgets only the common-base witness. -/
abbrev explicitTwoFibreProductComparisonFunctor
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct F G).obj ⥤ F.toFunctor ⊡ G.toFunctor :=
  (toFunctorToCategoricalPullback F.toFunctor G.toFunctor
    (explicitTwoFibreProduct F G).obj).obj (explicitTwoFibreProductSquareOver F G)

/-- Helper for Remark 4.35.8: the left component of an ordinary pullback object lies over the
expected base object after expanding the over-base identity of `F`. -/
private theorem categoricalPullback_left_base_eq
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (Q : F.toFunctor ⊡ G.toFunctor) :
    Z.p.obj (F.obj Q.fst) = X.p.obj Q.fst := by
  exact congrArg (fun H : X.obj ⥤ C => H.obj Q.fst) F.w

/-- Helper for Remark 4.35.8: the right component of an ordinary pullback object lies over the
expected base object after expanding the over-base identity of `G`. -/
private theorem categoricalPullback_right_base_eq
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (Q : F.toFunctor ⊡ G.toFunctor) :
    Z.p.obj (G.obj Q.snd) = Y.p.obj Q.snd := by
  exact congrArg (fun H : Y.obj ⥤ C => H.obj Q.snd) G.w

/-- Helper for Remark 4.35.8: an ordinary pullback object canonically determines the base
isomorphism along which its right component must be transported. -/
private def categoricalPullback_base_iso
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (Q : F.toFunctor ⊡ G.toFunctor) :
    X.p.obj Q.fst ≅ Y.p.obj Q.snd :=
  eqToIso (categoricalPullback_left_base_eq F G Q).symm ≪≫
    Z.p.mapIso Q.iso ≪≫
    eqToIso (categoricalPullback_right_base_eq F G Q)

/-- Helper for Remark 4.35.8: the underlying base morphism of an ordinary pullback object is the
hom-component of its transported base isomorphism. -/
private abbrev categoricalPullback_base_hom
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (Q : F.toFunctor ⊡ G.toFunctor) :
    X.p.obj Q.fst ⟶ Y.p.obj Q.snd :=
  (categoricalPullback_base_iso F G Q).hom

/-- Helper for Remark 4.35.8: the map of a morphism under a based functor has the expected base
transport in the target category. -/
private theorem basedFunctor_map_base
    (H : X ⥤ᵇ Z) {a b : X.obj} (φ : a ⟶ b) :
    Z.p.map (H.map φ) = eqToHom (H.w_obj a) ≫ X.p.map φ ≫ eqToHom (H.w_obj b).symm := by
  have hlift : Z.p.IsHomLift (X.p.map φ) (H.map φ) :=
    (H.isHomLift_iff (X.p.map φ) φ).2 (show X.p.IsHomLift (X.p.map φ) φ from inferInstance)
  let _ : Z.p.IsHomLift (X.p.map φ) (H.map φ) := hlift
  simpa using (IsHomLift.fac' Z.p (X.p.map φ) (H.map φ))

/-- Helper for Remark 4.35.8: the stored comparison of an explicit pullback object is vertical in
`Z`, so its image in the base category is the identity on the common base object. -/
private theorem explicitTwoFibreProduct_comparison_base
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (P : (explicitTwoFibreProduct F G).obj) :
    Z.p.map P.comparison =
      eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2) ≫
        𝟙 P.U ≫
          eqToHom (((G.w_obj P.obj.snd.1).trans P.obj.snd.2)).symm := by
  let _ : Z.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  simpa [ExplicitTwoFibreProductObject.comparison, Category.assoc] using
    (IsHomLift.fac' Z.p (𝟙 P.U) P.comparison)

/-- Helper for Remark 4.35.8: the ordinary comparison isomorphism attached to an explicit pullback
object is the stored comparison morphism itself. -/
private theorem explicitTwoFibreProductComparisonIsoOver_hom_app
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (P : (explicitTwoFibreProduct F G).obj) :
    (explicitTwoFibreProductComparisonIsoOver F G).hom.app P = P.comparison :=
  rfl

/-- Helper for Remark 4.35.8: once a morphism is known to be strongly cartesian, any other lift of
the same base arrow through the same underlying morphism carries the same strong-cartesian
structure. -/
private theorem isStronglyCartesian_rebase
    {S : Type u} {E : Type*} [Category.{v} S] [Category E]
    (p : E ⥤ S) {a b : E} {f f' : p.obj a ⟶ p.obj b} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f' φ] :
    p.IsStronglyCartesian f' φ := by
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  have hf' : f' = p.map φ := IsHomLift.eq_of_isHomLift p f' φ
  subst hf
  subst hf'
  infer_instance

/-- Helper for Remark 4.35.8: a strong-cartesian structure over the owner base map of a morphism
rebases along any external lift witness for that same morphism. -/
private theorem isStronglyCartesian_external
    {S : Type u} {E : Type*} [Category.{v} S] [Category E]
    (p : E ⥤ S) {R T : S} {a b : E} {f : R ⟶ T} (φ : a ⟶ b)
    [p.IsStronglyCartesian (p.map φ) φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian f φ := by
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = T := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase (p := p) (f := p.map φ) (f' := f) (φ := φ)

/-- Helper for Remark 4.35.8: the comparison arrow of an ordinary pullback object lifts the
transported base morphism obtained from the object's structural isomorphism. -/
private theorem categoricalPullback_comparison_isHomLift
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (Q : F.toFunctor ⊡ G.toFunctor) :
    Z.p.IsHomLift (categoricalPullback_base_hom F G Q) Q.iso.hom := by
  let ha := categoricalPullback_left_base_eq F G Q
  let hb := categoricalPullback_right_base_eq F G Q
  -- Expanding the transported base isomorphism shows that its hom is exactly the image of the
  -- comparison morphism in the base.
  refine IsHomLift.of_fac Z.p (categoricalPullback_base_hom F G Q) Q.iso.hom ha hb ?_
  simp [categoricalPullback_base_hom, categoricalPullback_base_iso]

/-- Helper for Remark 4.35.8: strictifying the right component along the transported base map
produces a vertical comparison into the pulled-back object. -/
private theorem categoricalPullback_strictification_factor
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (Q : F.toFunctor ⊡ G.toFunctor) :
    ∃ (y' : Y.obj) (γ : y' ⟶ Q.snd) (α' : F.obj Q.fst ⟶ G.obj y'),
      Y.p.IsStronglyCartesian (categoricalPullback_base_hom F G Q) γ ∧
        Z.p.IsHomLift (𝟙 (X.p.obj Q.fst)) α' ∧
          α' ≫ G.map γ = Q.iso.hom := by
  let δ := categoricalPullback_base_hom F G Q
  obtain ⟨y', γ, hγcart⟩ := IsPreFibered.exists_isCartesian Y.p rfl δ
  have hγcart : Y.p.IsCartesian δ γ := by
    exact hγcart
  have hγstrong : Y.p.IsStronglyCartesian δ γ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p δ γ
  have hγlift : Y.p.IsHomLift δ γ := IsCartesian.toIsHomLift
  have hGγlift : Z.p.IsHomLift δ (G.map γ) :=
    (G.isHomLift_iff δ γ).2 hγlift
  have hGγstrong :
      Z.p.IsStronglyCartesian δ (G.map γ) :=
    by
      let _ : Z.p.IsStronglyCartesian (Z.p.map (G.map γ)) (G.map γ) :=
        (inferInstance : Z.p.IsStronglyCartesian (Z.p.map (G.map γ)) (G.map γ))
      let _ : Z.p.IsHomLift δ (G.map γ) := hGγlift
      exact isStronglyCartesian_external (p := Z.p) (f := δ) (φ := G.map γ)
  have hQ : Z.p.IsHomLift δ Q.iso.hom :=
    categoricalPullback_comparison_isHomLift F G Q
  -- Apply the strong universal property of the pulled-back right leg to factor the old
  -- comparison into a vertical one followed by the chosen cartesian lift.
  let _ : Z.p.IsStronglyCartesian δ (G.map γ) := hGγstrong
  have hδ' :
      δ = 𝟙 (X.p.obj Q.fst) ≫ δ := by
    simp
  obtain ⟨α', hαprop⟩ :=
    ExistsUnique.exists <| Functor.IsStronglyCartesian.universal_property
      Z.p δ (G.map γ) (𝟙 (X.p.obj Q.fst)) δ hδ' Q.iso.hom
  exact ⟨y', γ, α', hγstrong, hαprop.1, hαprop.2⟩

/-- Helper for Remark 4.35.8: every ordinary pullback object is isomorphic to the image of a
strictified object in the explicit pullback category. -/
private theorem categoricalPullback_strictification_iso
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    (Q : F.toFunctor ⊡ G.toFunctor) :
    ∃ P : (explicitTwoFibreProduct F G).obj,
      Nonempty ((explicitTwoFibreProductComparisonFunctor F G).obj P ≅ Q) := by
  let δ := categoricalPullback_base_hom F G Q
  obtain ⟨y', γ, α', hγstrong, hαlift, hfac⟩ :=
    categoricalPullback_strictification_factor F G Q
  have hγlift : Y.p.IsHomLift δ γ := by
    infer_instance
  let _ : Z.p.IsHomLift (𝟙 (X.p.obj Q.fst)) α' := hαlift
  have hαstrong : Z.p.IsStronglyCartesian (𝟙 (X.p.obj Q.fst)) α' := by
    let _ : Z.p.IsStronglyCartesian (Z.p.map α') α' :=
      (inferInstance : Z.p.IsStronglyCartesian (Z.p.map α') α')
    exact isStronglyCartesian_external (p := Z.p) (f := 𝟙 (X.p.obj Q.fst)) (φ := α')
  let _ : Z.p.IsStronglyCartesian (𝟙 (X.p.obj Q.fst)) α' := hαstrong
  haveI : IsIso α' :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := Z.p) (f := 𝟙 (X.p.obj Q.fst)) (φ := α')
  let _ : Y.p.IsStronglyCartesian δ γ := hγstrong
  haveI : IsIso δ := by
    dsimp [δ, categoricalPullback_base_hom]
    infer_instance
  haveI : IsIso γ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := Y.p) (f := δ) (φ := γ)
  have hαinv : Z.p.IsHomLift (𝟙 (X.p.obj Q.fst)) (inv α') := by
    let _ : Z.p.IsHomLift (𝟙 (X.p.obj Q.fst)) α' := hαlift
    infer_instance
  let _ : Z.p.IsHomLift (𝟙 (X.p.obj Q.fst)) (inv α') := hαinv
  let P : (explicitTwoFibreProduct F G).obj :=
    { U := X.p.obj Q.fst
      obj :=
        { fst := Functor.Fiber.mk rfl
          snd := Functor.Fiber.mk (IsHomLift.domain_eq Y.p δ γ)
          iso :=
            { hom := Functor.Fiber.homMk Z.p (X.p.obj Q.fst) α'
              inv := Functor.Fiber.homMk Z.p (X.p.obj Q.fst) (inv α')
              hom_inv_id := by
                apply Functor.Fiber.hom_ext
                change α' ≫ inv α' = 𝟙 _
                simp
              inv_hom_id := by
                apply Functor.Fiber.hom_ext
                change inv α' ≫ α' = 𝟙 _
                simp } } }
  refine ⟨P, ?_⟩
  -- The strictified object maps to the original one by keeping the left leg fixed and using the
  -- pulled-back right-leg isomorphism.
  have hPcomparison : P.comparison = α' := by
    rfl
  let eγ : y' ≅ Q.snd := asIso γ
  have hcompare :
      (explicitTwoFibreProductComparisonIsoOver F G).hom.app P = α' := by
    simpa [hPcomparison] using explicitTwoFibreProductComparisonIsoOver_hom_app F G P
  refine ⟨CategoricalPullback.mkIso (.refl Q.fst) eγ ?_⟩
  calc
    F.map (𝟙 Q.fst) ≫ Q.iso.hom = Q.iso.hom := by simp
    _ = α' ≫ G.map γ := hfac.symm
    _ = (explicitTwoFibreProductComparisonIsoOver F G).hom.app P ≫ G.map eγ.hom := by
      change α' ≫ G.map γ = α' ≫ G.map γ
      rfl

/-- Helper for Remark 4.35.8: a morphism in the ordinary pullback between strict objects forces
its two components to lie over the same base arrow in `C`. -/
private theorem comparison_left_composite_base_transport
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (explicitTwoFibreProduct F G).obj}
    (η : (explicitTwoFibreProductComparisonFunctor F G).obj P ⟶
      (explicitTwoFibreProductComparisonFunctor F G).obj Q) :
    eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        Z.p.map (F.map η.fst ≫ (explicitTwoFibreProductComparisonIsoOver F G).hom.app Q) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) =
      eqToHom P.obj.fst.2.symm ≫ X.p.map η.fst ≫ eqToHom Q.obj.fst.2 := by
  have hmapF := basedFunctor_map_base (H := F) (φ := η.fst)
  have hcompQ := explicitTwoFibreProduct_comparison_base F G Q
  -- First isolate the two mapped factors inside the conjugated composite.
  calc
    eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        Z.p.map (F.map η.fst ≫ (explicitTwoFibreProductComparisonIsoOver F G).hom.app Q) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) =
      eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        (Z.p.map (F.map η.fst) ≫ Z.p.map Q.comparison) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) := by
        rw [explicitTwoFibreProductComparisonIsoOver_hom_app, Functor.map_comp]
        simp [Category.assoc]
    _ =
      eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        (Z.p.map (F.map η.fst) ≫
          (eqToHom ((F.w_obj Q.obj.fst.1).trans Q.obj.fst.2) ≫
            𝟙 Q.U ≫ eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)).symm)) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) := by
        simp [Category.assoc, hcompQ]
    _ = eqToHom P.obj.fst.2.symm ≫ X.p.map η.fst ≫ eqToHom Q.obj.fst.2 := by
        simpa [Category.assoc] using congrArg
          (fun k ↦
            eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
              k ≫ eqToHom ((F.w_obj Q.obj.fst.1).trans Q.obj.fst.2))
          hmapF

/-- Helper for Remark 4.35.8: conjugating the right-hand side of the pullback compatibility
equation by the source and target base transports recovers the transported base map of the right
component. -/
private theorem comparison_right_composite_base_transport
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (explicitTwoFibreProduct F G).obj}
    (η : (explicitTwoFibreProductComparisonFunctor F G).obj P ⟶
      (explicitTwoFibreProductComparisonFunctor F G).obj Q) :
    eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        Z.p.map ((explicitTwoFibreProductComparisonIsoOver F G).hom.app P ≫ G.map η.snd) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) =
      eqToHom P.obj.snd.2.symm ≫ Y.p.map η.snd ≫ eqToHom Q.obj.snd.2 := by
  have hcompP := explicitTwoFibreProduct_comparison_base F G P
  have hmapG := basedFunctor_map_base (H := G) (φ := η.snd)
  -- First isolate the two mapped factors inside the conjugated composite.
  calc
    eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        Z.p.map ((explicitTwoFibreProductComparisonIsoOver F G).hom.app P ≫ G.map η.snd) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) =
      eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        (Z.p.map P.comparison ≫ Z.p.map (G.map η.snd)) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) := by
        rw [explicitTwoFibreProductComparisonIsoOver_hom_app, Functor.map_comp]
        simp [Category.assoc]
    _ =
      eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
        ((eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2) ≫
            𝟙 P.U ≫ eqToHom (((G.w_obj P.obj.snd.1).trans P.obj.snd.2)).symm) ≫
          Z.p.map (G.map η.snd)) ≫
          eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) := by
        simp [Category.assoc, hcompP]
    _ = eqToHom P.obj.snd.2.symm ≫ Y.p.map η.snd ≫ eqToHom Q.obj.snd.2 := by
        simpa [Category.assoc] using congrArg
          (fun k ↦
            eqToHom (((G.w_obj P.obj.snd.1).trans P.obj.snd.2)).symm ≫
              k ≫ eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)))
          hmapG

/-- Helper for Remark 4.35.8: a morphism in the ordinary pullback between strict objects forces
its two components to lie over the same base arrow in `C`. -/
private theorem categoricalPullback_hom_components_share_base
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (explicitTwoFibreProduct F G).obj}
    (η : (explicitTwoFibreProductComparisonFunctor F G).obj P ⟶
      (explicitTwoFibreProductComparisonFunctor F G).obj Q) :
    eqToHom P.obj.fst.2.symm ≫ X.p.map η.fst ≫ eqToHom Q.obj.fst.2 =
      eqToHom P.obj.snd.2.symm ≫ Y.p.map η.snd ≫ eqToHom Q.obj.snd.2 := by
  -- Route correction: instead of simplifying `Z.p.map` of `η.w` in place, conjugate by the outer
  -- transports so the `F.w_obj` and `G.w_obj` terms cancel before normalization.
  have hη :
      eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
          Z.p.map (F.map η.fst ≫ (explicitTwoFibreProductComparisonIsoOver F G).hom.app Q) ≫
            eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) =
        eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
          Z.p.map ((explicitTwoFibreProductComparisonIsoOver F G).hom.app P ≫ G.map η.snd) ≫
            eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)) := by
    -- Apply `Z.p.map` to the pullback-compatibility equation and insert the common transports.
    exact congrArg
      (fun k ↦
        eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm ≫
          Z.p.map k ≫
            eqToHom (((G.w_obj Q.obj.snd.1).trans Q.obj.snd.2)))
      η.w
  -- Each side now normalizes independently to the transported base map of one component.
  rw [comparison_left_composite_base_transport F G η,
    comparison_right_composite_base_transport F G η] at hη
  exact hη

/-- Helper for Remark 4.35.8: the canonical comparison functor is full because the common base
arrow is recovered from either component of a morphism in the ordinary pullback. -/
theorem explicitTwoFibreProduct_comparison_full
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProductComparisonFunctor F G).Full := by
  refine ⟨?_⟩
  intro P Q η
  let f :=
    eqToHom P.obj.fst.2.symm ≫ X.p.map η.fst ≫ eqToHom Q.obj.fst.2
  have hleft : X.p.IsHomLift f η.fst := by
    refine IsHomLift.of_fac' X.p f η.fst P.obj.fst.2 Q.obj.fst.2 ?_
    simp [f, Category.assoc]
  have hright0 : Y.p.IsHomLift
      (eqToHom P.obj.snd.2.symm ≫ Y.p.map η.snd ≫ eqToHom Q.obj.snd.2) η.snd := by
    refine IsHomLift.of_fac' Y.p
      (eqToHom P.obj.snd.2.symm ≫ Y.p.map η.snd ≫ eqToHom Q.obj.snd.2)
      η.snd P.obj.snd.2 Q.obj.snd.2 ?_
    simp [Category.assoc]
  have hbase :
      f = eqToHom P.obj.snd.2.symm ≫ Y.p.map η.snd ≫ eqToHom Q.obj.snd.2 :=
    categoricalPullback_hom_components_share_base F G η
  have hright : Y.p.IsHomLift f η.snd := by
    exact hbase.symm ▸ hright0
  refine ⟨
    { base := f
      a := η.fst
      a_over := hleft
      b := η.snd
      b_over := hright
      comm := ⟨by simpa using η.w⟩ }, ?_⟩
  apply CategoricalPullback.hom_ext <;> rfl

/-- Remark 4.35.8: for `1`-morphisms of categories fibred in groupoids over `C`, the explicit
`2`-fibre product from Lemma 4.35.7 is canonically equivalent to the standard `2`-fibre product
category of Example 4.31.3. The fibred-in-groupoids hypotheses are essential: after forgetting
the base, an object of the ordinary pullback only gives an isomorphism between base objects, and
the groupoid fibration structure supplies the transport needed to compare it with the strict
same-fibre model. -/
noncomputable def explicitTwoFibreProduct_equiv_categoricalPullback
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct F G).obj ≌ F.toFunctor ⊡ G.toFunctor := by
  let H := explicitTwoFibreProductComparisonFunctor F G
  let _ : H.Faithful := by
    refine ⟨?_⟩
    intro P Q φ ψ hφψ
    apply ExplicitTwoFibreProductHom.ext
    · exact congrArg (fun k => k.fst) hφψ
    · exact congrArg (fun k => k.snd) hφψ
  let _ : H.Full := explicitTwoFibreProduct_comparison_full F G
  let _ : H.EssSurj := by
    refine ⟨?_⟩
    intro Q
    obtain ⟨P, e⟩ := categoricalPullback_strictification_iso F G Q
    exact ⟨P, e⟩
  let _ : H.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  -- Route correction: the ordinary pullback comparison is not final in `Cat` a priori, so we
  -- prove directly that the canonical comparison functor is faithful, full, and essentially
  -- surjective after strictifying along cartesian lifts.
  exact H.asEquivalence

/-- The forward functor of `explicitTwoFibreProduct_equiv_categoricalPullback` is the canonical
comparison functor from the explicit `2`-fibre product square to the standard categorical
pullback. -/
-- Proof sketch: unfold `explicitTwoFibreProduct_equiv_categoricalPullback`; it is defined by
-- applying `Functor.asEquivalence` to the comparison functor induced by
-- `explicitTwoFibreProductSquareOver F G`.
theorem explicitTwoFibreProduct_equiv_categoricalPullback_functor
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct_equiv_categoricalPullback F G).functor =
      (toFunctorToCategoricalPullback F.toFunctor G.toFunctor
        (explicitTwoFibreProduct F G).obj).obj (explicitTwoFibreProductSquareOver F G) := by
  -- Unfolding `Functor.asEquivalence` shows that the forward functor is definitionally the
  -- comparison functor.
  simp [explicitTwoFibreProduct_equiv_categoricalPullback, explicitTwoFibreProductComparisonFunctor]

/-- The base projection of the explicit two-fibre product sends a morphism to its stored common
base morphism. -/
@[simp] theorem explicitTwoFibreProduct_p_map
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (explicitTwoFibreProduct F G).obj} (φ : P ⟶ Q) :
    (explicitTwoFibreProduct F G).p.map φ = φ.base :=
  rfl

/-- Remark 4.35.8 is compatible with the left base projection: the forward comparison from the
explicit two-fibre product to the ordinary categorical pullback preserves the base projection up
to the canonical equality witness stored in the left component. -/
noncomputable def explicitTwoFibreProduct_equiv_categoricalPullback_functor_baseIso_left
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct_equiv_categoricalPullback F G).functor ⋙
        (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≅
      (explicitTwoFibreProduct F G).p := by
  refine NatIso.ofComponents (fun P => eqToIso P.obj.fst.2) ?_
  intro P Q φ
  dsimp [explicitTwoFibreProduct_equiv_categoricalPullback]
  have hfac := IsHomLift.fac' X.p φ.base φ.a
  rw [hfac]
  change (eqToHom P.obj.fst.2 ≫ φ.base ≫ eqToHom Q.obj.fst.2.symm) ≫
      eqToHom Q.obj.fst.2 = eqToHom P.obj.fst.2 ≫ φ.base
  simp [Category.assoc]

/-- Remark 4.35.8 is compatible with the right base projection: the forward comparison from the
explicit two-fibre product to the ordinary categorical pullback preserves the base projection up
to the canonical equality witness stored in the right component. -/
noncomputable def explicitTwoFibreProduct_equiv_categoricalPullback_functor_baseIso_right
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct_equiv_categoricalPullback F G).functor ⋙
        (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≅
      (explicitTwoFibreProduct F G).p := by
  refine NatIso.ofComponents (fun P => eqToIso P.obj.snd.2) ?_
  intro P Q φ
  dsimp [explicitTwoFibreProduct_equiv_categoricalPullback]
  have hfac := IsHomLift.fac' Y.p φ.base φ.b
  rw [hfac]
  change (eqToHom P.obj.snd.2 ≫ φ.base ≫ eqToHom Q.obj.snd.2.symm) ≫
      eqToHom Q.obj.snd.2 = eqToHom P.obj.snd.2 ≫ φ.base
  simp [Category.assoc]

/-- If the forward functor of an equivalence is compatible with a base functor up to a natural
isomorphism, then the inverse functor is compatible with the base functor in the opposite
direction. -/
noncomputable def equivalence_inverse_baseIso
    {A B D : Type*} [Category A] [Category B] [Category D]
    (e : A ≌ B) (pA : A ⥤ D) (pB : B ⥤ D)
    (α : e.functor ⋙ pB ≅ pA) :
    e.inverse ⋙ pA ≅ pB :=
  (Functor.isoWhiskerLeft e.inverse α.symm) ≪≫
    (Functor.associator e.inverse e.functor pB).symm ≪≫
      Functor.isoWhiskerRight e.counitIso pB ≪≫
        pB.leftUnitor

/-- The forward functor followed by the inverse side of an equivalence is compatible with any base
functor on the source, via the unit of the equivalence. -/
noncomputable def equivalence_functor_inverse_baseIso
    {A B D : Type*} [Category A] [Category B] [Category D]
    (e : A ≌ B) (pA : A ⥤ D) :
    e.functor ⋙ (e.inverse ⋙ pA) ≅ pA :=
  (Functor.associator e.functor e.inverse pA).symm ≪≫
    Functor.isoWhiskerRight e.unitIso.symm pA ≪≫
      pA.leftUnitor

/-- Compose two functor/base-projection compatibility isomorphisms.  Keeping this as a named API
near Remark 4.35.8 avoids asking elaboration to infer long chains of associators in projection
formula proofs. -/
noncomputable def functorCompBaseIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D) (p : D ⥤ E) (q : B ⥤ E) (r : A ⥤ E)
    (hG : G ⋙ p ≅ q) (hF : F ⋙ q ≅ r) :
    (F ⋙ G) ⋙ p ≅ r :=
  Functor.associator F G p ≪≫ Functor.isoWhiskerLeft F hG ≪≫ hF

/-- Compose five successive functor/base-projection compatibility isomorphisms. -/
noncomputable def functorCompBaseIso5
    {A B D E F G H : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F] [Category G] [Category H]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (F₃ : D ⥤ E) (F₄ : E ⥤ F) (F₅ : F ⥤ G)
    (p : G ⥤ H) (q₄ : F ⥤ H) (q₃ : E ⥤ H) (q₂ : D ⥤ H) (q₁ : B ⥤ H)
    (r : A ⥤ H)
    (h₅ : F₅ ⋙ p ≅ q₄) (h₄ : F₄ ⋙ q₄ ≅ q₃) (h₃ : F₃ ⋙ q₃ ≅ q₂)
    (h₂ : F₂ ⋙ q₂ ≅ q₁) (h₁ : F₁ ⋙ q₁ ≅ r) :
    (F₁ ⋙ (F₂ ⋙ (F₃ ⋙ (F₄ ⋙ F₅)))) ⋙ p ≅ r := by
  let F45 := F₄ ⋙ F₅
  have h45 : F45 ⋙ p ≅ q₃ :=
    functorCompBaseIso F₄ F₅ p q₄ q₃ h₅ h₄
  let F345 := F₃ ⋙ F45
  have h345 : F345 ⋙ p ≅ q₂ :=
    functorCompBaseIso F₃ F45 p q₃ q₂ h45 h₃
  let F2345 := F₂ ⋙ F345
  have h2345 : F2345 ⋙ p ≅ q₁ :=
    functorCompBaseIso F₂ F345 p q₂ q₁ h345 h₂
  let F12345 := F₁ ⋙ F2345
  have h12345 : F12345 ⋙ p ≅ r :=
    functorCompBaseIso F₁ F2345 p q₁ r h2345 h₁
  simpa [F12345, F2345, F345, F45] using h12345

/-- Inverse form of the left projection compatibility for Remark 4.35.8. -/
noncomputable def explicitTwoFibreProduct_equiv_categoricalPullback_inverse_baseIso_left
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct_equiv_categoricalPullback F G).inverse ⋙
        (explicitTwoFibreProduct F G).p ≅
      π₁ F.toFunctor G.toFunctor ⋙ X.p :=
  equivalence_inverse_baseIso
    (explicitTwoFibreProduct_equiv_categoricalPullback F G)
    (explicitTwoFibreProduct F G).p
    (π₁ F.toFunctor G.toFunctor ⋙ X.p)
    (explicitTwoFibreProduct_equiv_categoricalPullback_functor_baseIso_left F G)

/-- Inverse form of the right projection compatibility for Remark 4.35.8. -/
noncomputable def explicitTwoFibreProduct_equiv_categoricalPullback_inverse_baseIso_right
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids Z.p]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct_equiv_categoricalPullback F G).inverse ⋙
        (explicitTwoFibreProduct F G).p ≅
      π₂ F.toFunctor G.toFunctor ⋙ Y.p :=
  equivalence_inverse_baseIso
    (explicitTwoFibreProduct_equiv_categoricalPullback F G)
    (explicitTwoFibreProduct F G).p
    (π₂ F.toFunctor G.toFunctor ⋙ Y.p)
    (explicitTwoFibreProduct_equiv_categoricalPullback_functor_baseIso_right F G)

end CategoryTheory
