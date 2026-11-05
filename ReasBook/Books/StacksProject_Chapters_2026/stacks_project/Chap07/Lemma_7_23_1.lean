module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap07.Lemma_7_20_3
public import stacks_project.Chap07.Lemma_7_21_1
public import stacks_project.Chap07.Lemma_7_22_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe t u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling:
- primary domain: inverse- and direct-image functors on sheaves attached to continuous and
  cocontinuous functors of sites, together with adjunction-uniqueness comparisons;
- sampled owner API:
  `Functor.sheafPullback`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPullbackCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Adjunction.leftAdjointUniq`;
- source-facing layer: the Stacks comparison between the lower-shriek `g_!` attached to the
  right adjoint `u` and the functors induced by its left adjoint `w`;
- core/canonical owner: `u.sheafPullback A J K` for `g_!`, together with
  `w.sheafPullbackCocontinuous A K J`, `w.sheafPushforwardContinuous A K J`, and
  `w.sheafPushforwardCocontinuous A K J` for the left-adjoint-side constructions, plus
  `w.morphismOfTopoiInOfCocontinuous K J` for the source-facing cocontinuous morphism of topoi;
- bridge/view: the comparison lemmas below identify these owner functors under `w ⊣ u`, and
  clause `(5)` reuses the existing Chapter 7 bridge
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`
  specialized to `adj.symm`.

Primitive data are the functors `u`, `w`, the adjunction `w ⊣ u`, and the sheafification/Kan
extension hypotheses needed to form the owner functors. The sheafification-of-pullback formula is
already the project owner `w.sheafPullbackCocontinuous K J`, so this file should reuse that owner
directly rather than keep a parallel local abbreviation.
-/

section

variable (u : C ⥤ D) (w : D ⥤ C)
variable [u.IsContinuous J K]
variable (adj : w ⊣ u)

section LeftKanExtension

-- Proof sketch: `u.sheafPullback (Type t) J K` is the chosen left adjoint to
-- `u.sheafPushforwardContinuous (Type t) J K`, while `w.sheafPullbackCocontinuous K J` is the
-- canonical sheafified pullback along `w.op`; Lemma `7.19.3` identifies pullback along `w.op`
-- with the chosen left adjoint to pullback along `u.op`, and then uniqueness of left adjoints
-- gives the comparison.
/-- Lemma 7.23.1 (1): if `w ⊣ u`, then the lower shriek functor `g_!` attached to the
continuous functor `u` is the sheaf associated to the presheaf pullback `w^p`;
in the project API this is the canonical isomorphism from `u.sheafPullback` to
`w.sheafPullbackCocontinuous A K J`. -/
noncomputable def sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint
    (A : Type (t + 1)) [Category.{t} A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [HasWeakSheafify K A] :
    u.sheafPullback A J K ≅ w.sheafPullbackCocontinuous A K J := by
  let hLan :
      (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj w.op ≅ u.op.lan :=
    (adj.op.whiskerLeft A).leftAdjointUniq (u.op.lanAdjunction A)
  let hComp :
      w.sheafPullbackCocontinuous A K J ≅
        Functor.sheafPullbackConstruction.sheafPullback u A J K := by
    simpa [Functor.sheafPullbackCocontinuous, Functor.sheafPullbackConstruction.sheafPullback] using
      Functor.isoWhiskerLeft (sheafToPresheaf J A)
        (Functor.isoWhiskerRight hLan (presheafToSheaf K A))
  exact Functor.sheafPullbackConstruction.sheafPullbackIso u A J K ≪≫ hComp.symm

-- Proof sketch: this is the `hom` of the canonical comparison isomorphism from clause `(1)`, so
-- it is an isomorphism by definition of that comparison.
/-- The comparison map from `u.sheafPullback` to `w.sheafPullbackCocontinuous` is an isomorphism. -/
theorem sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint_hom_isIso
    (A : Type (t + 1)) [Category.{t} A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [HasWeakSheafify K A] :
    IsIso
      ((sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint u w adj A).hom :
        u.sheafPullback A J K ⟶ w.sheafPullbackCocontinuous A K J) := by
  -- The displayed morphism is the `hom` of the canonical comparison isomorphism from clause `(1)`.
  infer_instance

-- Proof sketch: by the previous clause, `u.sheafPullback (Type t) J K` is the canonical
-- sheafified pullback `w.sheafPullbackCocontinuous K J`, whose underlying presheaf construction
-- is pullback along the right adjoint `w.op`; that pullback preserves finite limits, and
-- sheafification is exact, so the composite is exact.
/-- Lemma 7.23.1 (2): the lower shriek functor `g_!`, realized here as `u.sheafPullback`, is
exact. -/
theorem sheafPullback_exact_of_leftAdjoint
    (w : D ⥤ C) (adj : w ⊣ u)
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P]
    [HasSheafify K (Type t)] :
    exactFunctor (Sheaf J (Type t)) (Sheaf K (Type t)) (u.sheafPullback (Type t) J K) := by
  let _ : (u.sheafPullback (Type t) J K).IsLeftAdjoint :=
    (u.sheafAdjunctionContinuous (Type t) J K).isLeftAdjoint
  let _ : PreservesFiniteLimits (w.sheafPullbackCocontinuous (Type t) K J) := by
    let _ :
        PreservesFiniteLimits
          (((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ (Type t)).obj w.op) ⋙
            presheafToSheaf K (Type t)) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  let _ : PreservesFiniteLimits (u.sheafPullback (Type t) J K) :=
    preservesFiniteLimits_of_natIso
      (sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint u w adj (Type t)).symm
  let _ : PreservesFiniteColimits (u.sheafPullback (Type t) J K) := inferInstance
  rw [exactFunctor_iff]
  exact ⟨inferInstance, inferInstance⟩

end LeftKanExtension

section ContinuousLeftAdjoint

-- Proof sketch: when both `u` and `w` are continuous, `Adjunction.sheafPushforwardContinuous adj
-- K J` identifies the source functor `w^s` with the owner
-- `w.sheafPushforwardContinuous (Type t) K J`; uniqueness of left adjoints to
-- `u.sheafPushforwardContinuous (Type t) J K` then gives the comparison with the chosen owner
-- `u.sheafPullback (Type t) J K`.
/-- Lemma 7.23.1 (3): if the left adjoint `w` is continuous, then the lower shriek functor `g_!`
is canonically isomorphic to the continuous sheaf functor `w^s`, i.e.
`w.sheafPushforwardContinuous`. -/
noncomputable def sheafPullbackIso_sheafPushforwardContinuous_of_continuous_leftAdjoint
    [(u.sheafPushforwardContinuous (Type t) J K).IsRightAdjoint]
    [w.IsContinuous K J] :
    u.sheafPullback (Type t) J K ≅ w.sheafPushforwardContinuous (Type t) K J :=
  Adjunction.leftAdjointUniq
    (u.sheafAdjunctionContinuous (Type t) J K)
    (Adjunction.sheafPushforwardContinuous adj K J)

-- Proof sketch: this is the `hom` of the canonical comparison isomorphism from clause `(3)`, so
-- it is automatically an isomorphism.
/-- The comparison map from `g_!` to the continuous sheaf functor `w^s` is an isomorphism. -/
theorem sheafPullbackIso_sheafPushforwardContinuous_of_continuous_leftAdjoint_hom_isIso
    [(u.sheafPushforwardContinuous (Type t) J K).IsRightAdjoint]
    [w.IsContinuous K J] :
    IsIso
      ((sheafPullbackIso_sheafPushforwardContinuous_of_continuous_leftAdjoint u w adj).hom :
        u.sheafPullback (Type t) J K ⟶
          w.sheafPushforwardContinuous (Type t) K J) := by
  -- The displayed morphism is the `hom` of the canonical comparison isomorphism from clause `(3)`.
  infer_instance

-- Proof sketch: clause `(3)` identifies `g_!` with `w^s`. Whenever the latter admits a left
-- adjoint, transport that right-adjoint structure across the canonical isomorphism.
/-- Lemma 7.23.1 (3), source-facing consequence: under the canonical identification
`g_! ≅ w^s`, if the continuous sheaf functor `w^s` admits a left adjoint, then so does `g_!`. -/
theorem sheafPullback_isRightAdjoint_of_continuous_leftAdjoint
    (adj : w ⊣ u)
    [(u.sheafPushforwardContinuous (Type t) J K).IsRightAdjoint]
    [w.IsContinuous K J]
    [(w.sheafPushforwardContinuous (Type t) K J).IsRightAdjoint] :
    (u.sheafPullback (Type t) J K).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso
    (sheafPullbackIso_sheafPushforwardContinuous_of_continuous_leftAdjoint u w adj).symm

end ContinuousLeftAdjoint

section CocontinuousLeftAdjoint

variable [w.IsCocontinuous K J]

-- Proof sketch: for cocontinuous `w`, Lemma `7.21.1` packages the source-facing morphism of
-- topoi `h` as `w.morphismOfTopoiInOfCocontinuous K J`, whose inverse-image functor is the
-- canonical sheafified pullback `w.sheafPullbackCocontinuous K J`. Clause (1) identifies
-- `u.sheafPullback` with that same owner, so under the extra sheafification and right Kan
-- extension hypotheses needed to build `h`, we obtain the comparison `g_! ≅ h⁻¹`.
/-- Lemma 7.23.1 (4): if the left adjoint `w` is cocontinuous, then the lower shriek functor
`g_!` is canonically isomorphic to the inverse-image functor `h⁻¹` of the morphism of topoi
attached to `w`. -/
noncomputable def sheafPullbackIso_morphismOfTopoiInOfCocontinuous_inverseImage_of_cocontinuous_leftAdjoint
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P]
    [HasSheafify K (Type t)]
    [∀ P : Dᵒᵖ ⥤ Type t, w.op.HasPointwiseRightKanExtension P] :
    u.sheafPullback (Type t) J K ≅
      (w.morphismOfTopoiInOfCocontinuous K J)⁻¹ := by
  -- Rewrite the target inverse-image functor to the canonical cocontinuous pullback owner.
  simpa using sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint u w adj (Type t)

-- Proof sketch: this is the `hom` of the canonical comparison isomorphism from clause `(4)`, so
-- it is an isomorphism in the sheaf category.
/-- The comparison map from `g_!` to the inverse-image functor of
`w.morphismOfTopoiInOfCocontinuous K J` is an isomorphism. -/
theorem sheafPullbackIso_morphismOfTopoiInOfCocontinuous_inverseImage_of_cocontinuous_leftAdjoint_hom_isIso
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P]
    [HasSheafify K (Type t)]
    [∀ P : Dᵒᵖ ⥤ Type t, w.op.HasPointwiseRightKanExtension P] :
    IsIso
      ((sheafPullbackIso_morphismOfTopoiInOfCocontinuous_inverseImage_of_cocontinuous_leftAdjoint
          u w adj).hom :
        u.sheafPullback (Type t) J K ⟶
          (w.morphismOfTopoiInOfCocontinuous K J)⁻¹) := by
  -- The displayed morphism is the `hom` of the canonical comparison isomorphism from clause `(4)`.
  infer_instance

-- Proof sketch: this is the role-swapped specialization of Chapter 7's canonical comparison
-- `CategoryTheory.continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`
-- to the adjunction `adj.symm`; equivalently, after the previous clause identifies `g_!` with
-- `h⁻¹`, both `g⁻¹` and `h_*` are right adjoint to that same functor, so uniqueness of right
-- adjoints yields the comparison of pushforwards.
/- Lemma 7.23.1 (5): if the left adjoint `w` is cocontinuous, then the inverse-image functor
`g⁻¹` is canonically isomorphic to the direct-image functor `h_*` of the morphism of topoi
attached to `w`. This is exactly the role-swapped specialization of the canonical Chapter 7 owner
theorem `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`. -/
recall continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward

end CocontinuousLeftAdjoint

end

end CategoryTheory
