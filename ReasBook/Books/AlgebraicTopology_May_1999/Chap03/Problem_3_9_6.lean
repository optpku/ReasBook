/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Problem_3_9_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory QuotientGroup Topology
open scoped MulAction

variable {G : Type u} [Group G]
variable {H K L : O(G)}
variable {X : Type v} [TopologicalSpace X] [MulAction G X]

namespace MulAction

/-- The fixed-point subspace of a `G`-space `X` under a subgroup `H ≤ G`, written `X^H`. -/
scoped notation:51 X "^" H:52 => fixedPoints H X

end MulAction

/-- The canonical fixed coset attached to an orbit-category morphism sends `K`-fixed points of `X`
to `H`-fixed points. -/
-- Proof sketch: if `α : G ⧸ H → G ⧸ K` sends `1H` to `γK`, then `h • γK = γK` for every `h ∈ H`,
-- so `γ⁻¹ h γ ∈ K`. Apply the `K`-fixed condition to `x` and conjugate the action.
theorem fixedPointSpaceMap_mem_fixedPoints (α : H ⟶ K) (x : X^K) :
    fixedPointsOrbitMap x (Subgroup.orbitCategoryHomEvalOne H K α) ∈ X^H := by
  -- Choose a representative for the distinguished fixed coset attached to `α`.
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne H K α :
      MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) : G ⧸ K)
  have hsub := subgroup_map_conj_inv_le_of_quotient_mulActionHom_apply_one α γ (by
    simpa [Subgroup.orbitCategoryHomEvalOne] using hγ.symm)
  rw [MulAction.mem_fixedPoints]
  intro h
  rw [Subgroup.pointwise_smul_def] at hsub
  have hk : (γ⁻¹ * (h : G) * γ : G) ∈ K := by
    exact hsub ⟨h, h.2, by simp [mul_assoc]⟩
  have hxk : ((γ⁻¹ * (h : G) * γ : G)) • (x : X) = x := by
    exact (MulAction.mem_fixedPoints.mp x.2) ⟨γ⁻¹ * (h : G) * γ, hk⟩
  -- Rewrite the orbit map through `γ` and then use the `K`-fixed condition on `x`.
  rw [← hγ, fixedPointsOrbitMap_apply_mk]
  calc
    (h : G) • (γ • (x : X)) = γ • (((γ⁻¹ * (h : G) * γ : G)) • (x : X)) := by
      simp [smul_smul, mul_assoc]
    _ = γ • (x : X) := by
      simpa using congrArg (fun y : X ↦ γ • y) hxk

/-- The underlying function on fixed-point spaces induced by a morphism in the orbit category. -/
noncomputable def fixedPointSpaceMapFn (α : H ⟶ K) :
    X^K → X^H :=
  fun x ↦
    ⟨fixedPointsOrbitMap x (Subgroup.orbitCategoryHomEvalOne H K α),
      fixedPointSpaceMap_mem_fixedPoints α x⟩

/-- Helper for Problem 3.9.6: if `α(1H) = γK`, then the induced fixed-point map is translation by
`γ` on underlying points. -/
theorem fixedPointSpaceMapFn_val_eq_smul_of_apply_one (α : H ⟶ K) {γ : G}
    (hα : α.toFun ((1 : G) : G ⧸ H) = (γ : G ⧸ K)) (x : X^K) :
    ((fixedPointSpaceMapFn α x : X^H) : X) = γ • (x : X) := by
  -- Replace the canonical fixed coset `α(1H)` by the representative `γK`.
  change fixedPointsOrbitMap x (Subgroup.orbitCategoryHomEvalOne H K α) = γ • (x : X)
  change fixedPointsOrbitMap x (α.toFun ((1 : G) : G ⧸ H)) = γ • (x : X)
  rw [hα, fixedPointsOrbitMap_apply_mk]

/-- The fixed-point map induced by an orbit-category morphism is continuous. -/
-- Proof sketch: it is the restriction of the continuous self-map `x ↦ γ • x` of `X`, where
-- `γK = α(1H)`, and the target restriction lands in `X^H` by the previous
-- lemma.
theorem fixedPointSpaceMapFn_continuous [ContinuousConstSMul G X] (α : H ⟶ K) :
    Continuous (fixedPointSpaceMapFn α : X^K → X^H) :=
  by
  -- Choose a representative for the distinguished fixed coset of `α`.
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne H K α :
      MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) : G ⧸ K)
  have hα : α.toFun ((1 : G) : G ⧸ H) = (γ : G ⧸ K) := by
    simpa [Subgroup.orbitCategoryHomEvalOne] using hγ.symm
  -- After that rewrite, the map is the restriction of the translate `x ↦ γ • x`.
  have hcont : Continuous fun x : X^K => ((fixedPointSpaceMapFn α x : X^H) : X) := by
    simpa [fixedPointSpaceMapFn_val_eq_smul_of_apply_one (α := α) hα] using
      ((continuous_const_smul γ).comp continuous_subtype_val)
  exact Continuous.subtype_mk hcont (fun x => fixedPointSpaceMap_mem_fixedPoints α x)

/-- A morphism in the orbit category induces a continuous map between the corresponding
fixed-point spaces in the contravariant direction. -/
noncomputable def fixedPointSpaceMap [ContinuousConstSMul G X] (α : H ⟶ K) :
    C(X^K, X^H) :=
  ⟨fixedPointSpaceMapFn α, fixedPointSpaceMapFn_continuous α⟩

/-- The fixed-point map attached to the identity orbit-category morphism is the identity. -/
-- Proof sketch: the identity map sends `1H` to `1H`, so its chosen representative acts by `1`,
-- and the formula defining `fixedPointSpaceMap` reduces to the identity on `X^H`.
theorem fixedPointSpaceMap_id [ContinuousConstSMul G X] (H : O(G)) :
    fixedPointSpaceMap (𝟙 H) = ContinuousMap.id (X^H) := by
  -- Compare the two continuous maps on fixed points and evaluate at the identity coset.
  ext x
  simpa [fixedPointSpaceMap, fixedPointSpaceMapFn, Subgroup.orbitCategoryHomEvalOne] using
    (fixedPointsOrbitMap_apply_one (H := H) x : fixedPointsOrbitMap x ((1 : G) : G ⧸ H) = x)

/-- Fixed-point maps compose contravariantly with composition in the orbit category. -/
-- Proof sketch: if `α(1H) = γK` and `β(1K) = δL`, then precomposition shows
-- `(β ≫ α)(1H) = γδL`, so the induced map on fixed points is `x ↦ γ • (δ • x)`.
theorem fixedPointSpaceMap_comp [ContinuousConstSMul G X] (α : H ⟶ K) (β : K ⟶ L) :
    (fixedPointSpaceMap (α ≫ β) : C(X^L, X^H)) =
      (fixedPointSpaceMap α : C(X^K, X^H)).comp (fixedPointSpaceMap β : C(X^L, X^K)) := by
  -- Choose representatives for the fixed cosets controlling `α` and `β`.
  obtain ⟨γ, hα_rep⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne H K α :
      MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) : G ⧸ K)
  obtain ⟨δ, hβ_rep⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne K L β :
      MulAction.fixedPoints (K : Subgroup G) (G ⧸ L)) : G ⧸ L)
  have hα : α.toFun ((1 : G) : G ⧸ H) = (γ : G ⧸ K) := by
    simpa [Subgroup.orbitCategoryHomEvalOne] using hα_rep.symm
  have hβ : β.toFun ((1 : G) : G ⧸ K) = (δ : G ⧸ L) := by
    simpa [Subgroup.orbitCategoryHomEvalOne] using hβ_rep.symm
  have hcomp : (α ≫ β).toFun ((1 : G) : G ⧸ H) = ((γ * δ : G) : G ⧸ L) := by
    -- The composite sends `1H` to `β (γK) = (γδ)L`.
    change β.toFun (Subgroup.orbitCategoryHomEvalOne H K α) = ((γ * δ : G) : G ⧸ L)
    rw [← hα_rep]
    exact quotient_mulActionHom_apply_coe_eq_coe_mul_of_apply_one β δ γ hβ
  -- Compare both continuous maps pointwise, then simplify the action of the product `γ * δ`.
  ext x
  rw [ContinuousMap.comp_apply]
  change ((fixedPointSpaceMapFn (α ≫ β) x : X^H) : X) =
      ((fixedPointSpaceMapFn α (fixedPointSpaceMapFn β x) : X^H) : X)
  rw [fixedPointSpaceMapFn_val_eq_smul_of_apply_one (α := α ≫ β) hcomp]
  rw [fixedPointSpaceMapFn_val_eq_smul_of_apply_one (α := α) hα (x := fixedPointSpaceMapFn β x)]
  rw [fixedPointSpaceMapFn_val_eq_smul_of_apply_one (α := β) hβ]
  simp [smul_smul]

variable (G) (X)

/-- Problem 3.9.6: for a `G`-space `X`, the assignment `G ⧸ H ↦ X^H` extends to a contravariant
functor `X^{(-)} : O(G) ⥤ Top`, encoded in Lean as a functor `(O(G))ᵒᵖ ⥤ TopCat`. -/
noncomputable def fixedPointSpaceFunctor [ContinuousConstSMul G X] :
    (O(G))ᵒᵖ ⥤ TopCat where
  obj H := TopCat.of (X^H.unop)
  map {_ _} α := TopCat.ofHom (fixedPointSpaceMap α.unop)
  map_id H := by
    simpa using congrArg TopCat.ofHom (fixedPointSpaceMap_id H.unop)
  map_comp α β := by
    simpa using congrArg TopCat.ofHom (fixedPointSpaceMap_comp β.unop α.unop)

local notation X "^{(-)}" => fixedPointSpaceFunctor G X

/-- The functor `X^{(-)}` sends the orbit `G ⧸ H` to the fixed-point subspace `X^H`. -/
theorem fixedPointSpaceFunctor_obj [ContinuousConstSMul G X] (H : (O(G))ᵒᵖ) :
    (X^{(-)}).obj H = TopCat.of (X^H.unop) :=
  rfl
