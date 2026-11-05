module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.UnivLE
public import stacks_project.Chap07.Lemma_7_20_3
public import stacks_project.Chap07.Lemma_7_28.BeckChevalley
public import stacks_project.Chap07.Lemma_7_28_5.Index

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

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

/- Domain-style sampling for Lemma 7.28.5:
- primary domain: Grothendieck topologies induced on comma-style categories, together with the
  continuous/cocontinuous functors and the induced direct-image comparison on sheaves;
- sampled owner API:
  `GrothendieckTopology.over`,
  `Functor.IsContinuous`,
  `Functor.IsCocontinuous`,
  `CategoryTheory.CatCommSq`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `CategoryTheory.site_square_direct_image_inverse_image_iso`,
  `Functor.toOver_comp_forget`;
- source-facing layer: the site structure on `CostructuredArrow u V` whose covering sieves are
  detected after projection to `C`, the commuting square
  `CostructuredArrow.proj u V`, `CostructuredArrow.toOver u V`, `u`, `Over.forget V`, and the
  resulting comparison `f'_* j^{-1} ≅ j_V^{-1} f_*`;
- core/canonical layer: the mathlib/project site-functor owners for continuity, cocontinuity, and
  the corresponding inverse-image and direct-image functors on sheaves;
- bridge/view: the source proof identifies the indexing category over an object of `D / V` with
  the corresponding indexing category over its image in `D`. In Lean this is the finality
  condition consumed by the general Beck-Chevalley owner theorem.

Primitive data here are only the covering sieves on `CostructuredArrow u V`. The continuity,
cocontinuity, the commutative square, and the sheaf-level comparison statements are derived API.
-/

local notation "j" => CostructuredArrow.proj u V
local notation "uOver" => CostructuredArrow.toOver u V

/-- Helper for Lemma 7.28.5: the category of arrows `u(U) ⟶ V` becomes a site by declaring a
sieve to be covering exactly when its pushforward along the projection to `C` is covering for
`J`. -/
def cocontinuousOverTopology : GrothendieckTopology (CostructuredArrow u V) :=
  cocontinuousOverTopologyCore J u V

local notation "J'" => cocontinuousOverTopologyCore J u V

/-- Helper for Lemma 7.28.5: covers for the induced topology on `CostructuredArrow u V` are
already defined by pushforward along the projection `j`. -/
theorem cocontinuousOverProjection_coverPreserving :
    CoverPreserving J' J j where
  cover_preserve hS := hS

/-- Helper for Lemma 7.28.5: the projection `j` preserves compatible families because a common
comparison object can be built directly in `CostructuredArrow u V`. -/
theorem cocontinuousOverProjection_compatiblePreserving :
    CompatiblePreserving J j where
  compatible {ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : CostructuredArrow u V := CostructuredArrow.mk (u.map f₁ ≫ Y₁.hom)
    -- The equality in `C` forces the two structure maps to `V` to agree.
    have hw_base : u.map f₂ ≫ Y₂.hom = u.map f₁ ≫ Y₁.hom := by
      have hleft : f₂ ≫ g₂.left = f₁ ≫ g₁.left := by
        simpa using h.symm
      have hw₂ : u.map f₂ ≫ Y₂.hom = u.map (f₂ ≫ g₂.left) ≫ Z.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun k => u.map f₂ ≫ k) (CostructuredArrow.w g₂).symm
      have hmid : u.map (f₂ ≫ g₂.left) ≫ Z.hom = u.map (f₁ ≫ g₁.left) ≫ Z.hom := by
        simpa using congrArg (fun k => u.map k ≫ Z.hom) hleft
      have hw₁ : u.map (f₁ ≫ g₁.left) ≫ Z.hom = u.map f₁ ≫ Y₁.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun k => u.map f₁ ≫ k) (CostructuredArrow.w g₁)
      exact hw₂.trans (hmid.trans hw₁)
    have hw : u.map f₂ ≫ Y₂.hom = W'.hom := by
      simpa [W'] using hw_base
    let g₁' : W' ⟶ Y₁ := CostructuredArrow.homMk f₁
    let g₂' : W' ⟶ Y₂ := CostructuredArrow.homMk f₂ hw
    -- Compatibility in the comma category reduces to the original equality in `C`.
    have hcomp : g₁' ≫ g₁ = g₂' ≫ g₂ := by
      ext
      exact h
    simpa [g₁', g₂'] using hx g₁' g₂' hg₁ hg₂ hcomp

/-- Helper for Lemma 7.28.5: every arrow into `X.left` lifts canonically to an arrow into `X` in
the costructured-arrow category. -/
theorem cocontinuousOverProjection_le_pushforward_functorPullback
    (X : CostructuredArrow u V) (S : Sieve X.left) :
    S ≤ Sieve.functorPushforward j (Sieve.functorPullback j S) := by
  intro Y f hf
  let Y' : CostructuredArrow u V := CostructuredArrow.mk (u.map f ≫ X.hom)
  have hmem : Sieve.functorPullback j S (CostructuredArrow.homMk f : Y' ⟶ X) := by
    simpa using hf
  -- The lifted arrow maps back to the original arrow under `j`.
  simpa using
    (Sieve.image_mem_functorPushforward (F := j) (R := Sieve.functorPullback j S) hmem)

/-- Helper for Lemma 7.28.5: the projection `j : {}^u_V \mathcal I ⥤ C` is continuous for the
declared site structure on `{}^u_V \mathcal I`. -/
instance cocontinuousOverProjection_isContinuous :
    Functor.IsContinuous j J' J := by
  -- Continuity follows from the induced-cover definition plus compatibility preservation.
  exact Functor.isContinuous_of_coverPreserving
    (cocontinuousOverProjection_compatiblePreserving (J := J) (u := u) (V := V))
    (cocontinuousOverProjection_coverPreserving (J := J) (u := u) (V := V))

/-- Helper for Lemma 7.28.5: the projection `j : {}^u_V \mathcal I ⥤ C` is cocontinuous for the
declared site structure on `{}^u_V \mathcal I`. -/
instance cocontinuousOverProjection_isCocontinuous :
    Functor.IsCocontinuous j J' J where
  cover_lift {X} S hS := by
    -- Every base arrow lifts to an arrow in `CostructuredArrow u V`, so covers lift along `j`.
    change Sieve.functorPushforward j (Sieve.functorPullback j S) ∈ J X.left
    exact J.superset_covering
      (cocontinuousOverProjection_le_pushforward_functorPullback (u := u) (V := V) X S)
      hS

/-- The forgetful functor from the costructured-arrow category to the slice category composes with
the slice forgetful functor as the projected functor `j ⋙ u`. -/
theorem cocontinuousOver_toOver_comp_forget_eq :
    uOver ⋙ Over.forget V = j ⋙ u := by
  -- This is the canonical strict equality for `Functor.toOver`.
  exact Functor.toOver_comp_forget (j ⋙ u) V (fun X ↦ X.hom)
    (fun f ↦ by simpa using CostructuredArrow.w f)

/-- Helper for Lemma 7.28.5: after pulling a sieve on `Over V` back along `uOver`, pushing it
forward along `j` lands inside the pullback along `u` of the corresponding base sieve on `D`. -/
theorem cocontinuousOverToOver_pushforward_pullback_le
    (X : CostructuredArrow u V) (S : Sieve ((CostructuredArrow.toOver u V).obj X)) :
    Sieve.functorPullback u
        (Sieve.overEquiv ((CostructuredArrow.toOver u V).obj X) S) ≤
      Sieve.functorPushforward j (Sieve.functorPullback (CostructuredArrow.toOver u V) S) := by
  intro Y f hf
  change (Sieve.overEquiv ((CostructuredArrow.toOver u V).obj X) S) (u.map f) at hf
  rw [Sieve.overEquiv_iff] at hf
  let Y' : CostructuredArrow u V := CostructuredArrow.mk (u.map f ≫ X.hom)
  have hpull :
      Sieve.functorPullback (CostructuredArrow.toOver u V) S
        (CostructuredArrow.homMk f : Y' ⟶ X) := by
    change S ((CostructuredArrow.toOver u V).map (CostructuredArrow.homMk f : Y' ⟶ X))
    simpa using hf
  -- The lifted arrow in `CostructuredArrow u V` maps back to the original base arrow.
  simpa using
    (Sieve.image_mem_functorPushforward
      (F := j) (R := Sieve.functorPullback (CostructuredArrow.toOver u V) S) hpull)

/-- Helper for Lemma 7.28.5: if `u` is cocontinuous, then the functor
`u' : {}^u_V \mathcal I ⥤ \mathcal D / V` is cocontinuous. -/
instance cocontinuousOverToOver_isCocontinuous
    [u.IsCocontinuous J K] :
    Functor.IsCocontinuous uOver J' (K.over V) where
  cover_lift {X} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS
    -- Route correction: prove cocontinuity through the base sieve `Sieve.overEquiv _ S` on `D`,
    -- then compare it with the pushed-forward pullback along `j`.
    change Sieve.functorPushforward j (Sieve.functorPullback uOver S) ∈ J X.left
    exact J.superset_covering
      (cocontinuousOverToOver_pushforward_pullback_le (u := u) (V := V) X S)
      (u.cover_lift J K hS)

/-- Helper for Lemma 7.28.5: the functors `j`, `u'`, `u`, and `Over.forget V` form the canonical
commutative square of sites. -/
instance cocontinuousOver_square : CatCommSq j uOver u (Over.forget V) where
  iso := eqToIso (cocontinuousOver_toOver_comp_forget_eq u V)

/-- Helper for Lemma 7.28.5: use the definitional commutative square when comparing the
costructured-arrow categories in the source proof. -/
def cocontinuousOver_square_hom :
    j ⋙ u ⟶ uOver ⋙ Over.forget V :=
  (Iso.refl _).hom

/-- Helper for Lemma 7.28.5: for an object over `V`, the rightwards arrow-category functor
attached to the canonical square is an equivalence. -/
noncomputable def cocontinuousOver_costructuredArrowRightwards_equivalence
    (Y : Over V) :
    CostructuredArrow uOver Y ≌ CostructuredArrow u Y.left where
  functor :=
    TwoSquare.costructuredArrowRightwards
      (cocontinuousOver_square_hom (u := u) (V := V)) Y
  inverse := CostructuredArrow.costructuredArrowToOverEquivalence.inverse u Y
  unitIso := NatIso.ofComponents (fun X ↦
    -- The source proof only forgets the over-`V` packaging; the underlying arrows are unchanged.
    CostructuredArrow.isoMk
      (CostructuredArrow.isoMk (Iso.refl _) (by
        simpa [cocontinuousOver_square_hom, Category.assoc] using X.hom.w))
      (by
        ext
        simp [cocontinuousOver_square_hom]))
  counitIso := NatIso.ofComponents (fun X ↦
    -- Repackaging an arrow `u(X) ⟶ Y.left` and forgetting it again is the identity.
    CostructuredArrow.isoMk (Iso.refl _) (by
      simp [cocontinuousOver_square_hom]))
  functor_unitIso_comp := by
    intro X
    ext
    simp [cocontinuousOver_square_hom]

/-- Helper for Lemma 7.28.5: the source-proof equivalence of indexing categories supplies the
finality condition required by the Beck-Chevalley owner theorem. -/
theorem cocontinuousOver_costructuredArrowRightwards_final
    (Y : Over V) :
    (TwoSquare.costructuredArrowRightwards
      (cocontinuousOver_square_hom (u := u) (V := V)) Y).Final := by
  let e := cocontinuousOver_costructuredArrowRightwards_equivalence (u := u) (V := V) Y
  letI : e.functor.IsEquivalence := e.isEquivalence_functor
  have hcomp : (e.functor ⋙ 𝟭 _).Final :=
    (Functor.final_iff_equivalence_comp (F := e.functor) (G := 𝟭 _)).1 inferInstance
  -- Remove the harmless right-unit functor from the final equivalence functor.
  exact Functor.final_of_natIso (F := e.functor ⋙ 𝟭 _) (F' := e.functor)
    (Functor.rightUnitor e.functor)

/-- Lemma 7.28.5: the source direct-image comparison
`f'_* j^{-1} ≅ j_V^{-1} f_*` for the canonical site square over `V`.

In left-to-right composition notation this is
`j^{-1} ⋙ (u')_* ≅ u_* ⋙ j_V^{-1}`. -/
noncomputable def cocontinuousOver_directImage_inverseImage_iso
    [u.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type t,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J' (Type t)]
    [HasWeakSheafify J (Type t)] :
    Functor.sheafPushforwardContinuous j (Type t) J' J ⋙
        Functor.sheafPushforwardCocontinuous uOver (Type t) J' (K.over V) ≅
      Functor.sheafPushforwardCocontinuous u (Type t) J K ⋙
        Functor.sheafPushforwardContinuous (Over.forget V) (Type t) (K.over V) K := by
  let sq : CatCommSq j uOver u (Over.forget V) := { iso := Iso.refl _ }
  -- The general Beck-Chevalley theorem applies because the source indexing functor is final.
  exact site_square_direct_image_inverse_image_iso J' J (K.over V) K sq
    (fun Y ↦ cocontinuousOver_costructuredArrowRightwards_final (u := u) (V := V) Y)

/-- The canonical direct-image comparison isomorphism has the expected left inverse identity. -/
theorem cocontinuousOver_directImage_inverseImage_iso_hom_inv_id
    [u.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type t,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J' (Type t)]
    [HasWeakSheafify J (Type t)] :
    (cocontinuousOver_directImage_inverseImage_iso J K u V).hom ≫
        (cocontinuousOver_directImage_inverseImage_iso J K u V).inv =
      𝟙
        (Functor.sheafPushforwardContinuous j (Type t) J' J ⋙
          Functor.sheafPushforwardCocontinuous uOver (Type t) J' (K.over V)) := by
  -- This is the standard `hom ≫ inv = 𝟙` identity for the packaged isomorphism.
  exact (cocontinuousOver_directImage_inverseImage_iso J K u V).hom_inv_id

/-- Helper for Lemma 7.28.5: the canonical direct-image comparison isomorphism has the expected
right inverse identity. -/
theorem cocontinuousOver_directImage_inverseImage_iso_inv_hom_id
    [u.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type t,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J' (Type t)]
    [HasWeakSheafify J (Type t)] :
    (cocontinuousOver_directImage_inverseImage_iso J K u V).inv ≫
        (cocontinuousOver_directImage_inverseImage_iso J K u V).hom =
      𝟙
        (Functor.sheafPushforwardCocontinuous u (Type t) J K ⋙
          Functor.sheafPushforwardContinuous (Over.forget V) (Type t) (K.over V) K) := by
  -- The companion triangle identity follows from the same packaged isomorphism.
  exact (cocontinuousOver_directImage_inverseImage_iso J K u V).inv_hom_id

end CategoryTheory
