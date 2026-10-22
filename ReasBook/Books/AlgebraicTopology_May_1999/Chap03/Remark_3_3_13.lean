/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_11
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_3
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_10
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_11

set_option maxHeartbeats 1000000

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Membership in `p(π(E, e))` is equivalent to fixing the distinguished point `⟨e, rfl⟩` under
direct fiber translation. -/
private theorem mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq
    (hp : Functor.IsCovering p) (e : E) (γ : p.obj e ⟶ p.obj e) :
    γ ∈ (Functor.mapVertexGroup p e).range ↔
      fiberTranslationMap hp γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · intro hγ
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
    change fiberTranslationMap hp γ⁻¹ x₀ = x₀ at hstab
    calc
      fiberTranslationMap hp γ x₀ = fiberTranslationMap hp γ (fiberTranslationMap hp γ⁻¹ x₀) := by
        rw [hstab]
      _ = fiberTranslationMap hp (γ⁻¹ ≫ γ) x₀ := by
        symm
        exact congrFun (fiberTranslationMap_comp hp γ⁻¹ γ) x₀
      _ = x₀ := by simp [fiberTranslationMap_id]
  · intro hγ
    have hinv : fiberTranslationMap hp γ⁻¹ x₀ = x₀ := by
      calc
        fiberTranslationMap hp γ⁻¹ x₀ =
            fiberTranslationMap hp γ⁻¹ (fiberTranslationMap hp γ x₀) := by
          rw [hγ]
        _ = fiberTranslationMap hp (γ ≫ γ⁻¹) x₀ := by
          symm
          exact congrFun (fiberTranslationMap_comp hp γ γ⁻¹) x₀
        _ = x₀ := by simp [fiberTranslationMap_id]
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      change fiberTranslationMap hp γ⁻¹ x₀ = x₀
      exact hinv
    rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e] at hstab

/-- Helper for Remark 3.3.13: the direct endpoint map on the fiber is visibly compatible with the
right-coset relation attached to `p(π(E,e))`. -/
private theorem fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range_rightRel
    (hp : Functor.IsCovering p) (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e)
    (hγ : γ₂ * γ₁⁻¹ ∈ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp γ₁ ⟨e, rfl⟩ = fiberTranslationMap hp γ₂ ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  -- First note that the subgroup element appended on the left fixes the base fiber point.
  have hfix : fiberTranslationMap hp (γ₂ * γ₁⁻¹) x₀ = x₀ := by
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e
      (γ₂ * γ₁⁻¹)).mp hγ
  -- Then rewrite `γ₂` as `(γ₂ * γ₁⁻¹) * γ₁` and collapse the fixed-point factor.
  calc
    fiberTranslationMap hp γ₁ x₀ =
        fiberTranslationMap hp γ₁ (fiberTranslationMap hp (γ₂ * γ₁⁻¹) x₀) := by
      rw [hfix]
    _ = fiberTranslationMap hp ((γ₂ * γ₁⁻¹) * γ₁) x₀ := by
      symm
      simpa [mul_assoc] using
        congrArg (fun m ↦ m x₀)
          (fiberTranslationMap_comp hp (γ₂ * γ₁⁻¹) γ₁)
    _ = fiberTranslationMap hp γ₂ x₀ := by
      simp

/-- If two loops differ on the right by an element of `p(π(E, e))`, then they determine the same
endpoint in the distinguished fiber over `p.obj e`. -/
-- Proof sketch: this is exactly the right-coset compatibility already verified for direct fiber
-- translation at the chosen basepoint.
theorem fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range (hp : Functor.IsCovering p)
    (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e)
    (hγ : γ₂ * γ₁⁻¹ ∈ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp γ₁ ⟨e, rfl⟩ = fiberTranslationMap hp γ₂ ⟨e, rfl⟩ := by
  -- Route correction: the public helper now records the right-coset compatibility that matches
  -- the direct endpoint geometry, instead of the false left-coset variant.
  exact fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range_rightRel hp e γ₁ γ₂ hγ

/-- The canonical map from `π(B, p.obj e) / p(π(E, e))` to the fiber over `p.obj e`. -/
noncomputable def quotientMapVertexGroupRangeToFiber (hp : Functor.IsCovering p) (e : E) :
    (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range → p.Fiber (p.obj e) :=
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  (MulAction.ofQuotientStabilizer (p.obj e ⟶ p.obj e) x₀) ∘
    Subgroup.quotientEquivOfEq
      (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm

/-- Helper for Remark 3.3.13: on a representative, the quotient-to-fiber map acts by inverse-loop
fiber translation from the distinguished basepoint. -/
@[simp] theorem quotientMapVertexGroupRangeToFiber_mk (hp : Functor.IsCovering p) (e : E)
    (γ : p.obj e ⟶ p.obj e) :
    quotientMapVertexGroupRangeToFiber hp e (QuotientGroup.mk γ) =
      fiberTranslationMap hp γ⁻¹ ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  -- Unfold the stabilizer identification and evaluate both quotient maps on the representative.
  change
    MulAction.ofQuotientStabilizer (p.obj e ⟶ p.obj e) x₀
        (Subgroup.quotientEquivOfEq
          (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm
          (QuotientGroup.mk γ)) =
      fiberTranslationMap hp γ⁻¹ x₀
  rw [Subgroup.quotientEquivOfEq_mk, MulAction.ofQuotientStabilizer_mk]
  rfl

/-- Helper for Remark 3.3.13: the subgroup `p(π(E,e))` viewed inside the reversed endomorphism
group `End (p.obj e)`. -/
private def mapVertexGroupRangeEnd (p : E ⥤ B) (e : E) :
    Subgroup (CategoryTheory.End (p.obj e)) where
  carrier := (Functor.mapVertexGroup p e).range.carrier
  one_mem' := by
    simpa using (Functor.mapVertexGroup p e).range.one_mem
  mul_mem' ha hb := by
    simpa [CategoryTheory.End.mul_def] using (Functor.mapVertexGroup p e).range.mul_mem hb ha
  inv_mem' ha := by
    rcases ha with ⟨δ, rfl⟩
    refine ⟨δ⁻¹, ?_⟩
    exact _root_.map_inv (Functor.mapVertexGroup p e) δ

/-- Helper for Remark 3.3.13: the left-coset relation for the reversed `End` group is the
ordinary right-coset relation for `p(π(E,e))`. -/
private theorem leftRel_mapVertexGroupRangeEnd_iff_rightRel_mapVertexGroup_range
    (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e) :
    QuotientGroup.leftRel (mapVertexGroupRangeEnd p e) γ₁ γ₂ ↔
      QuotientGroup.rightRel ((Functor.mapVertexGroup p e).range) γ₁ γ₂ := by
  -- Unfold both quotient relations; the reversed multiplication on `End` turns left cosets into
  -- the original right-coset relation.
  rw [QuotientGroup.leftRel_apply, QuotientGroup.rightRel_apply]
  rfl

/-- Helper for Remark 3.3.13: for the direct `End`-action on the fiber over `p.obj e`, the
stabilizer of the distinguished point is exactly `p(π(E,e))`. -/
theorem vertexGroupMulAction_basepoint_stabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) (e : E) :
    let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
    letI : MulAction (CategoryTheory.End (p.obj e)) (p.Fiber (p.obj e)) :=
      CategoryTheory.Functor.vertexGroupMulAction (fiberTranslationFunctor hp) (p.obj e)
    MulAction.stabilizer (CategoryTheory.End (p.obj e)) x₀ =
      mapVertexGroupRangeEnd p e := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (CategoryTheory.End (p.obj e)) (p.Fiber (p.obj e)) :=
    CategoryTheory.Functor.vertexGroupMulAction (fiberTranslationFunctor hp) (p.obj e)
  ext γ
  constructor
  · intro hγ
    -- Rewrite stabilizer membership as a fixed-point statement for direct fiber translation.
    change fiberTranslationMap hp γ x₀ = x₀ at hγ
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e γ).mpr hγ
  · intro hγ
    -- The explicit `End`-subgroup has the same carrier as the image subgroup in the loop group.
    change fiberTranslationMap hp γ x₀ = x₀
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e γ).mp hγ

/-- Remark 3.3.13: if the fiber-translation action of `π(B, p.obj e)` on the fiber over `p.obj e`
is pretransitive, then the canonical map from `π(B, p.obj e) / p(π(E, e))` to that fiber is
bijective. -/
-- Proof sketch: identify `p(π(E, e))` with the stabilizer of the distinguished fiber point
-- `⟨e, rfl⟩`, then apply the quotient-stabilizer equivalence for the pretransitive
-- fiber-translation action.
theorem quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    Function.Bijective (quotientMapVertexGroupRangeToFiber hp e) := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := htrans
  -- Route correction: work on Lean's actual left quotient by first identifying the subgroup with
  -- the stabilizer of `x₀`, then apply the standard orbit-stabilizer bijection.
  exact
    (ofQuotientStabilizer_bijective_of_isPretransitive (G := p.obj e ⟶ p.obj e)
      (S := p.Fiber (p.obj e)) x₀).comp
      (Subgroup.quotientEquivOfEq
        (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm).bijective

noncomputable def quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range ≃ p.Fiber (p.obj e) :=
  Equiv.ofBijective
    (quotientMapVertexGroupRangeToFiber hp e)
    (quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive hp e htrans)

@[simp] theorem quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive_apply
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e))
    (q : (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range) :
    quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive hp e htrans q =
      quotientMapVertexGroupRangeToFiber hp e q := rfl

/-- The underlying orbit map of the regular `π(B, p.obj e)`-set equivalence is bijective. -/
-- Proof sketch: specialize the quotient-stabilizer description to the trivial subgroup
-- `p(π(E, e)) = ⊥`, and identify `π(B, p.obj e) / ⊥` with `π(B, p.obj e)`.
theorem vertexGroupToFiber_bijectiveOfIsUniversalCovering (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e)) :
    Function.Bijective
      (fun γ : p.obj e ⟶ p.obj e ↦
        fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩) := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let quotientToFiber :
      (p.obj e ⟶ p.obj e) ⧸ (⊥ : Subgroup (p.obj e ⟶ p.obj e)) → p.Fiber (p.obj e) :=
    quotientMapVertexGroupRangeToFiber hp.isCovering e ∘
      Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm
  have hquotientToFiber : Function.Bijective quotientToFiber := by
    -- First identify the quotient by `p(π(E,e))` with the quotient by `⊥`.
    exact
      (quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive hp.isCovering e htrans).comp
        (Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm).bijective
  let inverseVertexToFiber : (p.obj e ⟶ p.obj e) → p.Fiber (p.obj e) :=
    quotientToFiber ∘ QuotientGroup.quotientBot.symm
  have hinverseVertexToFiber : Function.Bijective inverseVertexToFiber := by
    -- Then use the canonical identification `π(B,p.obj e) / ⊥ ≃ π(B,p.obj e)`.
    exact hquotientToFiber.comp QuotientGroup.quotientBot.symm.bijective
  have hinverseVertexToFiber_eq :
      inverseVertexToFiber =
        (fun γ : p.obj e ⟶ p.obj e ↦
          fiberTranslationMap hp.isCovering γ⁻¹ x₀) := by
    funext γ
    -- On representatives, the quotient map uses the inverse-loop action from `x₀`.
    show quotientToFiber (QuotientGroup.quotientBot.symm γ) =
      fiberTranslationMap hp.isCovering γ⁻¹ x₀
    show quotientMapVertexGroupRangeToFiber hp.isCovering e
        ((Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm)
          (QuotientGroup.quotientBot.symm γ)) =
      fiberTranslationMap hp.isCovering γ⁻¹ x₀
    rw [QuotientGroup.quotientBot_symm_apply, Subgroup.quotientEquivOfEq_mk]
    exact quotientMapVertexGroupRangeToFiber_mk hp.isCovering e γ
  rw [hinverseVertexToFiber_eq] at hinverseVertexToFiber
  have hdirect_eq :
      (fun γ : p.obj e ⟶ p.obj e ↦
        fiberTranslationMap hp.isCovering γ x₀) =
        (fun γ : p.obj e ⟶ p.obj e ↦
          fiberTranslationMap hp.isCovering γ⁻¹ x₀) ∘ fun γ : p.obj e ⟶ p.obj e ↦ γ⁻¹ := by
    funext γ
    -- Precomposing the inverse-representative orbit map with inversion recovers the textbook map.
    change fiberTranslationMap hp.isCovering γ x₀ =
      fiberTranslationMap hp.isCovering ((γ⁻¹)⁻¹) x₀
    simp
  have hinv : Function.Bijective (fun γ : p.obj e ⟶ p.obj e ↦ CategoryTheory.inv γ) := by
    constructor
    · intro γ₁ γ₂ hγ
      simpa using congrArg (fun δ : p.obj e ⟶ p.obj e ↦ CategoryTheory.inv δ) hγ
    · intro γ
      refine ⟨CategoryTheory.inv γ, ?_⟩
      simp
  -- Compose the inverse-representative bijection with inversion on the vertex group.
  simpa [x₀, hdirect_eq] using
    hinverseVertexToFiber.comp hinv

/-- For a universal covering with pretransitive fiber translation, the fiber over `p.obj e` is
canonically equivalent to the regular `π(B, p.obj e)`-set. -/
noncomputable def vertexGroupToFiberEquivOfIsUniversalCovering
    (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e)) :
    (p.obj e ⟶ p.obj e) ≃ p.Fiber (p.obj e) :=
  Equiv.ofBijective
    (fun γ : p.obj e ⟶ p.obj e ↦ fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩)
    (vertexGroupToFiber_bijectiveOfIsUniversalCovering hp htrans)

@[simp] theorem vertexGroupToFiberEquivOfIsUniversalCovering_apply
    (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e))
    (γ : p.obj e ⟶ p.obj e) :
    vertexGroupToFiberEquivOfIsUniversalCovering hp htrans γ =
      fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩ := rfl

end CategoryTheory.Functor.IsCovering
