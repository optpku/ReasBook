module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_21_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (U : C)

/- Domain-style sampling for Lemma 7.28.4:
- primary domain: localized cocontinuous functors between slice sites and their induced
  direct-image functors on sheaf categories;
- sampled owner API:
  `Functor.IsCocontinuous`,
  `GrothendieckTopology.over`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousComp`,
  `Functor.sheafPushforwardCocontinuousComp'`;
- source/core/bridge triage:
  `source-facing`: cocontinuity of the induced slice functor `Over.post u`;
  `core/canonical`: `Functor.IsCocontinuous` together with
  `Functor.sheafPushforwardCocontinuous`;
- bridge/view: the slice specialization of `Functor.sheafPushforwardCocontinuousComp'` for
  `Over.post u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u`.

Primitive data are only the sites `J`, `K`, the cocontinuous functor `u`, and the object `U`.
The sheaf-level comparison square is derived API from the owner comparison theorems of
Lemma `7.21.2`, so the refined file keeps the localized cocontinuity instance and reuses that
canonical bridge directly, treating the right-hand composite Kan-extension hypothesis as derived
data from the left-hand one rather than exporting any separate local wrapper.
-/

-- Proof sketch: pull a covering sieve on `Over (u.obj U)` back along `Over.post u`; under the
-- equivalence between sieves on a slice object and sieves on its domain, this reduces to pulling
-- back the corresponding covering sieve in `D` along `u`, and then transporting the resulting
-- cover back to the slice site.
/-- Helper for Lemma 7.28.4: after transporting sieves on slice objects to sieves on their
domains, pulling back along `Over.post u` becomes pulling back along `u`. -/
lemma overEquiv_functorPullback_post {Y : Over U} (S : Sieve ((Over.post u).obj Y)) :
    Sieve.overEquiv Y (S.functorPullback (Over.post u)) =
      (Sieve.overEquiv ((Over.post u).obj Y) S).functorPullback u := by
  ext Z g
  let e : (Over.post u).obj (Over.mk (g ≫ Y.hom)) ⟶
      Over.mk (u.map g ≫ ((Over.post u).obj Y).hom) :=
    Over.homMk (𝟙 (u.obj Z)) (by simp)
  let eInv : Over.mk (u.map g ≫ ((Over.post u).obj Y).hom) ⟶
      (Over.post u).obj (Over.mk (g ≫ Y.hom)) :=
    Over.homMk (𝟙 (u.obj Z)) (by simp)
  have heq :
      (Over.post u).map (Over.homMk (U := Over.mk (g ≫ Y.hom)) g rfl) =
        e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl := by
    -- The image of `g` under `Over.post u` differs from the canonical lift of `u.map g`
    -- only by the evident identity isomorphism on the source object.
    apply CategoryTheory.CommaMorphism.ext
    · change u.map g = (𝟙 (u.obj Z)) ≫ u.map g
      simp
    · simp
  constructor
  · intro hg
    -- Rewrite slice membership as membership in the pulled-back sieve on the base category.
    rw [Sieve.overEquiv_iff] at hg
    change S ((Over.post u).map (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y)) at hg
    have hg' : S (e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl) := by
      convert hg using 1
      exact heq.symm
    have hdown :
        S (eInv ≫ e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl) :=
      S.downward_closed hg' eInv
    change (Sieve.overEquiv ((Over.post u).obj Y) S) (u.map g)
    rw [Sieve.overEquiv_iff]
    convert hdown using 1
    apply CategoryTheory.CommaMorphism.ext
    · change u.map g = (𝟙 (u.obj Z)) ≫ 𝟙 (u.obj Z) ≫ u.map g
      simp
    · simp
  · intro hg
    -- Conversely, precompose the canonical lift of `u.map g` by the same identity arrow.
    rw [Sieve.overEquiv_iff]
    change (Sieve.overEquiv ((Over.post u).obj Y) S) (u.map g) at hg
    rw [Sieve.overEquiv_iff] at hg
    change S ((Over.post u).map (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y))
    have hg' : S (e ≫ Over.homMk (V := (Over.post u).obj Y) (u.map g) rfl) :=
      S.downward_closed hg e
    convert hg' using 1

/-- Helper for Lemma 7.28.4: a covering sieve on `u.obj Y.left` lifts to the pullback covering
for the induced slice functor `Over.post u`. -/
lemma over_post_cover_lift [u.IsCocontinuous J K] {Y : Over U}
    {S : Sieve ((Over.post u).obj Y)}
    (hS : Sieve.overEquiv ((Over.post u).obj Y) S ∈ K (u.obj Y.left)) :
    Sieve.overEquiv Y (S.functorPullback (Over.post u)) ∈ J Y.left := by
  -- After the transport lemma, the textbook covering argument is exactly `u.cover_lift`.
  rw [overEquiv_functorPullback_post (u := u) (U := U)]
  exact u.cover_lift J K hS

/-- Lemma 7.28.4: a cocontinuous functor between sites induces a cocontinuous functor on the
corresponding localized sites. -/
instance overPost_isCocontinuous [u.IsCocontinuous J K] :
    Functor.IsCocontinuous (Over.post u) (J.over U) (K.over (u.obj U)) where
  cover_lift {Y} S hS := by
    -- Transport the slice covering condition to the base sites, apply cocontinuity of `u`,
    -- and transport the lifted cover back to the slice site.
    rw [K.mem_over_iff] at hS
    rw [J.mem_over_iff]
    exact over_post_cover_lift (J := J) (K := K) (u := u) (U := U) hS

section

variable [u.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over (u.obj U))ᵒᵖ ⥤ Type w,
  (Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.post u).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w,
  (Over.post u ⋙ Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F]

/- Lemma 7.28.4: on sheaves of sets, the localized direct-image square is exactly the slice
specialization of the owner comparison theorems
`Functor.sheafPushforwardCocontinuousComp'` and
`Functor.sheafPushforwardCocontinuousComp`. The right-hand composite
`(Over.forget U ⋙ u).op` has pointwise right Kan extensions by transport across the definitional
identity `Over.post u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u`, so no local wrapper is
needed. -/
#check
  (by
    letI : Functor.IsCocontinuous (Over.forget U ⋙ u) (J.over U) K :=
      isCocontinuous_comp (Over.forget U) u (J.over U) J
    letI : ∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U ⋙ u).op.HasPointwiseRightKanExtension F := by
      intro F
      change (Over.post u ⋙ Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F
      infer_instance
    exact
      (Functor.sheafPushforwardCocontinuousComp'
          (J.over U) (K.over (u.obj U)) K (Over.post u) (Over.forget (u.obj U))
          (show Over.post u ⋙ Over.forget (u.obj U) ≅ Over.forget U ⋙ u from Iso.refl _) ≪≫
        (Functor.sheafPushforwardCocontinuousComp
          (J.over U) J K (Over.forget U) u).symm :
        (Over.post u).sheafPushforwardCocontinuous (Type w) (J.over U) (K.over (u.obj U)) ⋙
            (Over.forget (u.obj U)).sheafPushforwardCocontinuous (Type w)
              (K.over (u.obj U)) K ≅
          (Over.forget U).sheafPushforwardCocontinuous (Type w) (J.over U) J ⋙
            u.sheafPushforwardCocontinuous (Type w) J K))

end

end

end CategoryTheory
