module

public import stacks_project.Chap07.Example_7_14_3
public import stacks_project.Chap07.Lemma_7_22_2
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J J' : GrothendieckTopology C}

/- Domain-style sampling for Example 7.22.3:
- primary domain: change of Grothendieck topology on a fixed category and the induced direct-image
  functors on sheaves;
- sampled owner API:
  `id_isContinuous_of_le`,
  `Functor.IsCocontinuous`,
  `StructuredArrow.mkIdInitial`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- source/core/bridge triage:
  `source-facing`: the topology-change direct-image comparison for `J' ≤ J`;
  `core/canonical`: the chapter owner theorem for a continuous right adjoint and the sheaf
  pushforward owners it compares;
  `bridge/view`: the specialization to the identity adjunction on `C`.

Primitive data are only the order relation `hle : J' ≤ J`. The continuity and cocontinuity of
`𝟭 C` are derived from `hle` and used only locally to state the specialization below, and the
pointwise right-Kan-extension fact for `(𝟭 C).op` is likewise local implementation support,
derived from the initiality of `StructuredArrow.mk (𝟙 U)`.
-/

section

variable (hle : J' ≤ J)

-- Proof sketch: specialize the Chapter 7 owner theorem
-- `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward` to the identity
-- adjunction on `C`. The topology-comparison hypotheses and the pointwise right-Kan-extension
-- instance for `(𝟭 C).op` are supplied locally from the site comparison `hle`.
/-- Example 7.22.3: if `J' ≤ J` are the two Grothendieck topologies from Example 7.14.3, then
the direct-image functor of the topology-change morphism of topoi
`Sh(J) ⟶ Sh(J')` is canonically isomorphic to the direct image attached to the cocontinuous
identity functor `(C, J) ⥤ (C, J')`. -/
noncomputable def topology_change_pushforwardIso_cocontinuousPushforward
    : by
      letI : Functor.IsContinuous (𝟭 C) J' J := id_isContinuous_of_le hle
      letI : Functor.IsCocontinuous (𝟭 C) J J' := ⟨fun hS ↦ by simpa using hle _ hS⟩
      letI (P : Cᵒᵖ ⥤ Type w) : ((𝟭 C).op).HasPointwiseRightKanExtension P := by
        intro U
        let _ : HasInitial (StructuredArrow U ((𝟭 C).op)) :=
          (StructuredArrow.mkIdInitial : IsInitial (StructuredArrow.mk (𝟙 U))).hasInitial
        infer_instance
      exact
        (𝟭 C).sheafPushforwardContinuous (Type w) J' J ≅
          (𝟭 C).sheafPushforwardCocontinuous (Type w) J J' :=
  letI : Functor.IsContinuous (𝟭 C) J' J := id_isContinuous_of_le hle
  letI : Functor.IsCocontinuous (𝟭 C) J J' := ⟨fun hS ↦ by simpa using hle _ hS⟩
  letI (P : Cᵒᵖ ⥤ Type w) : ((𝟭 C).op).HasPointwiseRightKanExtension P := by
    intro U
    let _ : HasInitial (StructuredArrow U ((𝟭 C).op)) :=
      (StructuredArrow.mkIdInitial : IsInitial (StructuredArrow.mk (𝟙 U))).hasInitial
    infer_instance
  continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
    (𝟭 C) (𝟭 C) (Type w) Adjunction.id

-- Proof sketch: this morphism is the `hom` component of the canonical comparison isomorphism
-- `topology_change_pushforwardIso_cocontinuousPushforward`.
/-- The forward comparison morphism from topology-change direct image to cocontinuous direct image
is an isomorphism. -/
theorem topology_change_pushforwardIso_cocontinuousPushforward_hom_isIso :
    IsIso
      ((topology_change_pushforwardIso_cocontinuousPushforward hle).hom) := by
  -- The displayed morphism is the `hom` of the canonical comparison isomorphism.
  infer_instance

-- Proof sketch: this is the `hom_inv_id` identity for the canonical comparison isomorphism
-- specialized above to the identity functor and the topology comparison `J' ≤ J`.
/-- The forward map of `topology_change_pushforwardIso_cocontinuousPushforward` followed by its
inverse is the identity. -/
@[simp] theorem topology_change_pushforwardIso_cocontinuousPushforward_hom_inv_id :
    (topology_change_pushforwardIso_cocontinuousPushforward hle).hom ≫
      (topology_change_pushforwardIso_cocontinuousPushforward hle).inv =
        𝟙 _ := by
  -- This is the standard `hom_inv_id` identity for the comparison isomorphism.
  exact (topology_change_pushforwardIso_cocontinuousPushforward hle).hom_inv_id

end

end CategoryTheory
