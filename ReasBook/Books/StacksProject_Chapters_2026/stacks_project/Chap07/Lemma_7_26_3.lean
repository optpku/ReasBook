module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Lemma_7_21_1
public import stacks_project.Chap07.Lemma_7_25_7
public import stacks_project.Chap07.Lemma_7_26_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable
open scoped CartesianClosed
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (U : C) (ℱ : Sheaf J (Type (max u v)))

/- Domain-style sampling for Lemma 7.26.3:
- primary domain: internal Hom for sheaves of types and the localization direct image `j_{U*}`;
- sampled owner API:
  `sheaf_prod_sheafHom_equiv`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `GrothendieckTopology.overPullback`/`Sheaf.over`,
  `localization_lowerShriek_overPullback_prodIso`,
  `Functor.sheafAdjunctionCocontinuous`;
- source/core/bridge triage:
  `source-facing`: the canonical identification `sheafHom (h_U^#) ℱ ≅ j_{U*}(ℱ.over U)`;
  `core/canonical`: the localization morphism of topoi
  `(Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J` and its direct image `j_{U*}`;
  `bridge/view`: the product comparison `localization_lowerShriek_overPullback_prodIso U 𝒢`,
  the currying equivalence `sheaf_prod_sheafHom_equiv`, and the adjunction chain induced by
  `Over.forget U`.

Primitive data are only the localized object `U` and the sheaf `ℱ`. The Hom-equivalence for a test
sheaf `𝒢` is derived from these owner-level constructions, so it should remain private proof
machinery rather than a second public owner.
-/

/-- Helper for Lemma 7.26.3: the localized Hom presheaf is canonically identified with the
functor-category internal Hom proxy. -/
def presheaf_hom_iso_functor_hom
    (F G : Cᵒᵖ ⥤ Type (max u v)) :
    presheafHom F G ≅ F.functorHom G :=
  NatIso.ofComponents
    (fun X ↦
      (show (presheafHom F G).obj X ≃ (F.functorHom G).obj X from
        { toFun := fun α ↦
            { app := fun Y f ↦ α.app (op (Over.mk f.unop))
              naturality := by
                intro Y Z g f
                simpa using
                  α.naturality
                    (Over.homMk g.unop : Over.mk ((f ≫ g).unop) ⟶ Over.mk f.unop).op }
          invFun := fun α ↦
            { app := fun ⟨Y⟩ ↦ α.app (op Y.left) Y.hom.op
              naturality := by
                rintro ⟨Y⟩ ⟨Z⟩ ⟨g⟩
                dsimp
                have hfg : Y.hom.op ≫ g.left.op = Z.hom.op := by
                  simpa using congrArg Quiver.Hom.op (Over.w g)
                erw [← hfg]
                exact α.naturality g.left.op Y.hom.op }
          left_inv := fun _ ↦ rfl
          right_inv := fun α ↦ by
            ext Y f
            rfl }).toIso)
    fun {X} {Y} f ↦ by
      ext α Z g
      rfl

/-- Helper for Lemma 7.26.3: for sheaves of types, the exponential object is canonically the
sheaf of localized morphisms. -/
def ihom_iso_sheafHom
    (G H : Sheaf J (Type (max u v))) :
    G ⟹ H ≅ sheafHom G H :=
  (fullyFaithfulSheafToPresheaf J (Type (max u v))).preimageIso
    ((presheaf_hom_iso_functor_hom G.obj H.obj).symm ≪≫ (sheafHom'Iso G H).symm)

/-- Helper for Lemma 7.26.3: the standard currying equivalence for sheaf-Hom, written using local
owner-level transports so later naturality proofs do not depend on private declarations from
Lemma 7.26.2. -/
def sheaf_prod_sheafHom_equiv_local
    (F G H : Sheaf J (Type (max u v))) :
    ((F ⨯ G) ⟶ H) ≃ (F ⟶ sheafHom G H) :=
  (((prod.braiding F G).homCongr (Iso.refl H)).trans
      ((((tensorLeftIsoProd G).app F).symm.homCongr (Iso.refl H)).trans
        ((ihom.adjunction G).homEquiv F H))).trans
    ((Iso.refl F).homCongr (ihom_iso_sheafHom G H))

/-- Helper for Lemma 7.26.3: applying the inverse local currying equivalence and currying back
recovers the original sheaf-Hom morphism. -/
theorem sheaf_prod_sheafHom_equiv_local_apply_symm_apply
    (F G H : Sheaf J (Type (max u v))) (f : F ⟶ sheafHom G H) :
    sheaf_prod_sheafHom_equiv_local F G H
        ((sheaf_prod_sheafHom_equiv_local F G H).symm f) = f := by
  exact (sheaf_prod_sheafHom_equiv_local F G H).apply_symm_apply f

noncomputable def sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv
    (𝒢 : Sheaf J (Type (max u v))) :
    (𝒢 ⟶ sheafHom h[U]^#[J] ℱ) ≃
      (𝒢 ⟶ ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj
        (ℱ.over U))) := by
  simpa using
    (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm.trans
      (((localization_lowerShriek_overPullback_prodIso U 𝒢).symm.homCongr
          (Iso.refl ℱ)).trans
        ((((Over.forget U).sheafAdjunctionContinuous
            (Type (max u v)) (J.over U) J).homEquiv _ _).trans
          (((Over.forget U).sheafAdjunctionCocontinuous
            (Type (max u v)) (J.over U) J).homEquiv _ _)))

/-- Helper for Lemma 7.26.3: the currying equivalence
`((𝒢 × h_U^#) ⟶ ℱ) ≃ (𝒢 ⟶ sheafHom h_U^# ℱ)` is natural in the test sheaf. -/
theorem sheaf_prod_sheafHom_equiv_naturality_left
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢)
    (k : (𝒢 ⨯ h[U]^#[J]) ⟶ ℱ) :
    sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ (prod.map f (𝟙 h[U]^#[J]) ≫ k) =
      f ≫ sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ k := by
  -- Route correction: prove naturality for the forward currying map first, so the only
  -- substantive rewrite is the public `ihom.adjunction` naturality theorem.
  -- Rewrite the currying equivalence into the adjunction `Hom(G ⊗ -, ℱ) ≃ Hom(-, G ⟹ ℱ)`.
  unfold sheaf_prod_sheafHom_equiv_local
  repeat rw [Equiv.trans_apply]
  simp only [Iso.homCongr_apply, Category.assoc, Iso.refl_hom, Iso.refl_inv]
  -- Identify precomposition by `prod.map f (𝟙 _)` with the left adjoint's action on `f`.
  change ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ)
      (((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
        (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ) ≫
      (ihom_iso_sheafHom h[U]^#[J] ℱ).hom =
    f ≫ ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢 ℱ)
      (((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
        (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ) ≫
      (ihom_iso_sheafHom h[U]^#[J] ℱ).hom
  have hpre :
      ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
          (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ =
        (MonoidalCategory.tensorLeft h[U]^#[J]).map f ≫
          ((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
            (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ := by
    have hbraid :
        (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) =
          prod.map (𝟙 h[U]^#[J]) f ≫ (prod.braiding 𝒢 h[U]^#[J]).inv := by
      apply prod.hom_ext
      · simp
      · simp
    calc
      ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
          (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ =
        ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
          prod.map (𝟙 h[U]^#[J]) f ≫ (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ := by
        change
          ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
              ((prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J])) ≫
                k ≫ 𝟙 ℱ =
            ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
              (prod.map (𝟙 h[U]^#[J]) f ≫ (prod.braiding 𝒢 h[U]^#[J]).inv) ≫
                k ≫ 𝟙 ℱ
        exact congrArg
          (fun m ↦ ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫ m ≫ k ≫ 𝟙 ℱ)
          hbraid
      _ =
        (MonoidalCategory.tensorLeft h[U]^#[J]).map f ≫
          ((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
            (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ := by
        simpa [Category.assoc] using
          congrArg
            (fun m ↦ m ≫ (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ)
            (((tensorLeftIsoProd h[U]^#[J]).hom.naturality f).symm)
  have harg :
      ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ)
          (((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
            (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ) =
        ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ)
          ((MonoidalCategory.tensorLeft h[U]^#[J]).map f ≫
            ((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
              (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ) := by
    exact congrArg ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ) hpre
  rw [harg]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  rfl

/-- Helper for Lemma 7.26.3: the currying equivalence
`((𝒢 × h_U^#) ⟶ ℱ) ≃ (𝒢 ⟶ sheafHom h_U^# ℱ)` is natural in the test sheaf. -/
theorem sheaf_prod_sheafHom_equiv_naturality_left_symm
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢)
    (g : 𝒢 ⟶ sheafHom h[U]^#[J] ℱ) :
    (sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ).symm (f ≫ g) =
      prod.map f (𝟙 h[U]^#[J]) ≫
        (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g := by
  -- Apply the forward currying equivalence to both sides and cancel using its inverse laws.
  apply (sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ).injective
  -- The left-hand side re-curries to `f ≫ g`, while the right-hand side does so by forward
  -- naturality of the already-proved currying equivalence.
  rw [sheaf_prod_sheafHom_equiv_local_apply_symm_apply]
  rw [sheaf_prod_sheafHom_equiv_naturality_left (U := U) (ℱ := ℱ) f]
  rw [sheaf_prod_sheafHom_equiv_local_apply_symm_apply]

/-- Helper for Lemma 7.26.3: the product comparison of Lemma 7.25.7 is natural in the sheaf
variable. -/
theorem localization_lowerShriek_overPullback_prodIso_hom_naturality
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢) :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.overPullback (Type (max u v)) U).map f) ≫
      (localization_lowerShriek_overPullback_prodIso U 𝒢).hom =
        (localization_lowerShriek_overPullback_prodIso U 𝒢').hom ≫
          prod.map f (𝟙 h[U]^#[J]) := by
  -- Rewrite the packaged comparison once so the goal becomes a product-map identity.
  simp [localization_lowerShriek_overPullback_prodIso,
    GrothendieckTopology.representableLocalizationComparison]
  -- Check the two product projections separately, using naturality of the comparison from
  -- Lemma 7.30.7.
  apply prod.hom_ext
  · rw [prod.lift_fst, prod.lift_fst]
    have h := congrArg (fun k => k ≫ prod.snd)
      (congrArg CommaMorphism.left
        ((J.representableLocalizationComparison_inverseImageIso U).hom.naturality f))
    simpa [Sheaf.over, Category.assoc] using h
  · rw [prod.lift_snd, prod.lift_snd]
    have h := congrArg (fun k => k ≫ prod.fst)
      (congrArg CommaMorphism.left
        ((J.representableLocalizationComparison_inverseImageIso U).hom.naturality f))
    simpa [Sheaf.over, Category.assoc] using h

theorem sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv_naturality
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢)
    (g : 𝒢 ⟶ sheafHom h[U]^#[J] ℱ) :
    sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢' (f ≫ g) =
      f ≫ sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢 g := by
  -- Unfold the composite equivalence once so each source-proof step becomes a separate rewrite.
  unfold sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv
  -- First pass through the inverse currying equivalence.
  change
    ((localization_lowerShriek_overPullback_prodIso U 𝒢').symm.homCongr (Iso.refl ℱ)).trans
        ((((Over.forget U).sheafAdjunctionContinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _).trans
          (((Over.forget U).sheafAdjunctionCocontinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _))
        ((sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ).symm (f ≫ g)) =
      f ≫
        ((localization_lowerShriek_overPullback_prodIso U 𝒢).symm.homCongr (Iso.refl ℱ)).trans
            ((((Over.forget U).sheafAdjunctionContinuous
                  (Type (max u v)) (J.over U) J).homEquiv _ _).trans
              (((Over.forget U).sheafAdjunctionCocontinuous
                  (Type (max u v)) (J.over U) J).homEquiv _ _))
            ((sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g)
  rw [sheaf_prod_sheafHom_equiv_naturality_left_symm (U := U) (ℱ := ℱ) f g]
  -- Then rewrite across the comparison `j_{U!} j_U^{-1} 𝒢 ≅ 𝒢 × h_U^#`.
  have hloc :
      ((localization_lowerShriek_overPullback_prodIso U 𝒢').symm.homCongr (Iso.refl ℱ))
        (prod.map f (𝟙 h[U]^#[J]) ≫
          (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g) =
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.overPullback (Type (max u v)) U).map f) ≫
        ((localization_lowerShriek_overPullback_prodIso U 𝒢).symm.homCongr (Iso.refl ℱ))
          ((sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g) := by
    simpa [Iso.homCongr_apply, Category.assoc] using
      congrArg
        (fun m ↦ m ≫ (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g)
        ((localization_lowerShriek_overPullback_prodIso_hom_naturality (U := U)
          (𝒢 := 𝒢) (𝒢' := 𝒢') f).symm)
  simpa [Equiv.trans_apply, Category.assoc,
    CategoryTheory.Adjunction.homEquiv_naturality_left] using
    congrArg
      (fun x ↦
        ((((Over.forget U).sheafAdjunctionContinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _).trans
          (((Over.forget U).sheafAdjunctionCocontinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _)) x)
      hloc
  -- The final two rewrites are the left naturality squares for the localization adjunctions.

/-- Lemma 7.26.3: for a site `(C, J)`, an object `U : C`, and a sheaf of sets `ℱ`, the sheaf-Hom
from the sheafified representable `h_U^#` to `ℱ` is canonically identified with the pushforward of
the restricted sheaf `ℱ.over U` from the slice site `(C/U, J.over U)` back to `(C, J)`. -/
noncomputable def sheafHom_sheafifiedRepresentable_iso_pushforward_restriction
    :
    sheafHom h[U]^#[J] ℱ ≅
      ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj (ℱ.over U)) :=
  Yoneda.ext _ _
    (fun {𝒢} f ↦
      sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢 f)
    (fun {𝒢} f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢).symm f)
    (fun f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ _).left_inv f)
    (fun f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ _).right_inv f)
    (fun f g ↦
      sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv_naturality U ℱ f g)

-- Proof sketch: the forward comparison morphism here is the `hom` of an explicit isomorphism, so
-- it is an isomorphism by the standard `Iso.hom` instance.
/-- The forward comparison morphism from `sheafHom h_U^# ℱ` to `j_{U*}(ℱ.over U)` is an
isomorphism. -/
theorem sheafHom_sheafifiedRepresentable_iso_pushforward_restriction_hom_isIso :
    IsIso (sheafHom_sheafifiedRepresentable_iso_pushforward_restriction U ℱ).hom := by
  -- The comparison morphism is already the `hom` field of the explicit Yoneda isomorphism above.
  infer_instance

end
