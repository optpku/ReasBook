/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_8_7
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open QuotientGroup
open Topology

variable (G : Type u) [Group G]

variable {G}
variable {X : Type v} [MulAction G X]

/-- A coset `γK` acts on the orbit space `X/K` by the canonical formula `x ↦ K (γ⁻¹ • x)`. -/
noncomputable def orbitSpacePointMap {K : O(G)} (x : X) : G ⧸ K → X /[K] :=
  Quotient.lift (fun γ : G ↦ Quotient.mk'' (γ⁻¹ • x)) fun a b hab ↦ by
    apply Quotient.sound
    change MulAction.orbitRel (K : Subgroup G) X (a⁻¹ • x) (b⁻¹ • x)
    rw [MulAction.orbitRel_apply]
    have hk : a⁻¹ * b ∈ (K : Subgroup G) := (QuotientGroup.leftRel_apply).mp hab
    refine ⟨⟨a⁻¹ * b, hk⟩, ?_⟩
    simp [smul_smul, mul_assoc]

/-- Evaluating `orbitSpacePointMap` on a represented coset gives the expected formula. -/
@[simp] theorem orbitSpacePointMap_apply_mk {K : O(G)} (x : X) (γ : G) :
    orbitSpacePointMap x (γ : G ⧸ K) = Quotient.mk'' (γ⁻¹ • x) :=
  rfl

/-- The pointwise orbit-space formula attached to an orbit-category morphism uses the canonical
fixed coset `α(1H)` from `Subgroup.orbitCategoryHomEvalOne`. -/
noncomputable def orbitSpaceMapFn {H K : O(G)} (α : H ⟶ K) : X → X /[K] :=
  fun x ↦ orbitSpacePointMap x (Subgroup.orbitCategoryHomEvalOne H K α)

/-- The pointwise orbit-space formula is constant on `H`-orbits. -/
-- Proof sketch: if `y = h • x`, the coset `α(1H)` is `H`-fixed in `G ⧸ K`, so the corresponding
-- conjugate of `h` lies in `K`; this exactly identifies the two classes in `X/K`.
theorem orbitSpaceMapFn_eq_of_orbitRel {H K : O(G)} (α : H ⟶ K) {x y : X}
    (hxy : MulAction.orbitRel (H : Subgroup G) X x y) :
    orbitSpaceMapFn α x = orbitSpaceMapFn α y := by
  -- Choose a representative of the fixed coset controlling `α`.
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne H K α :
      MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) : G ⧸ K)
  -- Translate the fixed-point condition into the needed subconjugacy inclusion.
  have hsub := subgroup_map_conj_inv_le_of_quotient_mulActionHom_apply_one α γ (by
    simpa [Subgroup.orbitCategoryHomEvalOne] using hγ.symm)
  -- After rewriting the distinguished coset as `γK`, equality in `X /[K]` is orbit relation.
  rw [orbitSpaceMapFn, orbitSpaceMapFn, ← hγ, orbitSpacePointMap_apply_mk,
    orbitSpacePointMap_apply_mk]
  apply Quotient.sound
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
  obtain ⟨h, rfl⟩ := hxy
  rw [Subgroup.pointwise_smul_def] at hsub
  refine ⟨⟨γ⁻¹ * (h : G) * γ, hsub ⟨h, h.2, by simp [mul_assoc]⟩⟩, ?_⟩
  -- The witness `γ⁻¹ h γ ∈ K` transports the `H`-orbit relation to a `K`-orbit relation.
  change ((γ⁻¹ * (h : G) * γ : G)) • (γ⁻¹ • y) = γ⁻¹ • ((h : G) • y)
  simp [smul_smul, mul_assoc]

section Topological

variable [TopologicalSpace X]

/-- Restricting a `G`-space action along a subgroup again gives a continuous action. -/
instance subgroup_continuousConstSMul (H : Subgroup G) [ContinuousConstSMul G X] :
    ContinuousConstSMul H X where
  continuous_const_smul h := by
    -- Restrict the ambient continuous translate `x ↦ h • x` along the subgroup inclusion.
    simpa using (continuous_const_smul (h : G) : Continuous fun x : X => (h : G) • x)

/-- The pointwise orbit-space formula is continuous. -/
-- Proof sketch: for a fixed coset `γK`, the map `x ↦ K (γ⁻¹ • x)` is the quotient projection
-- composed with the continuous translate `x ↦ γ⁻¹ • x`.
theorem orbitSpaceMapFn_continuous [ContinuousConstSMul G X] {H K : O(G)} (α : H ⟶ K) :
    Continuous (orbitSpaceMapFn α : X → X /[K]) := by
  -- Pick a representative for the distinguished fixed coset of `α`.
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne H K α :
      MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) : G ⧸ K)
  -- Rewrite the map as the quotient projection after the continuous translate by `γ⁻¹`.
  rw [show (orbitSpaceMapFn α : X → X /[K]) = fun x ↦ orbitSpacePointMap x (γ : G ⧸ K) by
    funext x
    rw [orbitSpaceMapFn, ← hγ]]
  simpa using (continuous_quotient_mk'.comp (continuous_const_smul (γ⁻¹ : G)))

/-- The continuous map on orbit spaces induced by a morphism in the orbit category. -/
noncomputable def orbitSpaceMap (G : Type u) [Group G] (X : Type v)
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] {H K : O(G)}
    (α : H ⟶ K) :
    C(X /[H], X /[K]) :=
  ⟨Quotient.lift (orbitSpaceMapFn α) fun _ _ hxy ↦ orbitSpaceMapFn_eq_of_orbitRel α hxy,
    continuous_quot_lift
      (fun _ _ hxy ↦ orbitSpaceMapFn_eq_of_orbitRel α hxy)
      (orbitSpaceMapFn_continuous α)⟩

/-- Applying the induced orbit-space map to an orbit class uses the canonical fixed coset
`α(1H)`. -/
theorem orbitSpaceMap_apply_mk [ContinuousConstSMul G X] {H K : O(G)}
    (α : H ⟶ K) (x : X) :
    orbitSpaceMap G X α (Quotient.mk'' x) =
      orbitSpacePointMap x (Subgroup.orbitCategoryHomEvalOne H K α) :=
  rfl

/-- If `α : G/H ⟶ G/K` sends `1H` to `γK`, then the induced map on orbit spaces sends `Hx` to
`K (γ⁻¹ • x)`. -/
-- Proof sketch: replace the canonical fixed coset `Subgroup.orbitCategoryHomEvalOne H K α` by the
-- represented coset `γK` and evaluate `orbitSpacePointMap` at that class.
theorem orbitSpaceMap_apply_mk_of_apply_one [ContinuousConstSMul G X]
    {H K : O(G)} (α : H ⟶ K) {γ : G}
    (hα : α.toFun ((1 : G) : G ⧸ H) = (γ : G ⧸ K)) (x : X) :
    orbitSpaceMap G X α (Quotient.mk'' x) = Quotient.mk'' (γ⁻¹ • x) := by
  -- Rewrite the canonical fixed coset `α(1H)` as the represented coset `γK`.
  change orbitSpacePointMap x (α.toFun ((1 : G) : G ⧸ H)) = Quotient.mk'' (γ⁻¹ • x)
  rw [hα, orbitSpacePointMap_apply_mk]

/-- The orbit-space map is the identity on `X/H` for the identity morphism of `H`. -/
-- Proof sketch: the identity morphism sends `1H` to `1H`, so the induced pointwise formula is the
-- identity on orbit classes.
theorem orbitSpaceMap_id (G : Type u) [Group G] (X : Type v)
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] (H : O(G)) :
    orbitSpaceMap G X (𝟙 H) = ContinuousMap.id (X /[H]) := by
  -- Compare the two continuous maps on orbit representatives.
  ext q
  refine Quotient.inductionOn' q ?_
  intro x
  -- The identity morphism is determined by the base coset `1H`.
  rw [orbitSpaceMap_apply_mk_of_apply_one (α := 𝟙 H) (x := x) rfl]
  simp

/-- Composition of orbit-space maps matches composition in the orbit category. -/
-- Proof sketch: the canonical fixed coset of `β ∘ α` is the product of the fixed cosets of `α`
-- and `β`, so the pointwise formulas agree on representatives.
theorem orbitSpaceMap_comp (G : Type u) [Group G] (X : Type v)
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] {H K L : O(G)}
    (α : H ⟶ K) (β : K ⟶ L) :
    (orbitSpaceMap G X (α ≫ β) : C(X /[H], X /[L])) =
      (orbitSpaceMap G X β : C(X /[K], X /[L])).comp
        (orbitSpaceMap G X α : C(X /[H], X /[K])) := by
  -- Choose representatives for the canonical fixed cosets of `α` and `β`.
  obtain ⟨γ, hα⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne H K α :
      MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) : G ⧸ K)
  obtain ⟨δ, hβ⟩ := Quotient.exists_rep
    ((Subgroup.orbitCategoryHomEvalOne K L β :
      MulAction.fixedPoints (K : Subgroup G) (G ⧸ L)) : G ⧸ L)
  have hα_apply : α.toFun ((1 : G) : G ⧸ H) = (γ : G ⧸ K) := by
    -- Unwrap the chosen representative of the fixed coset attached to `α`.
    simpa [Subgroup.orbitCategoryHomEvalOne] using hα.symm
  have hβ_apply : β.toFun ((1 : G) : G ⧸ K) = (δ : G ⧸ L) := by
    -- Unwrap the chosen representative of the fixed coset attached to `β`.
    simpa [Subgroup.orbitCategoryHomEvalOne] using hβ.symm
  have hcomp : (α ≫ β).toFun ((1 : G) : G ⧸ H) = ((γ * δ : G) : G ⧸ L) := by
    -- The composite sends `1H` to `β (γK) = (γδ)L`.
    change β.toFun (Subgroup.orbitCategoryHomEvalOne H K α) = ((γ * δ : G) : G ⧸ L)
    rw [← hα]
    exact quotient_mulActionHom_apply_coe_eq_coe_mul_of_apply_one β δ γ hβ_apply
  -- Check the two maps on quotient representatives, then simplify the inverse product formula.
  ext q
  refine Quotient.inductionOn' q ?_
  intro x
  rw [orbitSpaceMap_apply_mk_of_apply_one (α := α ≫ β) (x := x) hcomp]
  rw [ContinuousMap.comp_apply]
  rw [orbitSpaceMap_apply_mk_of_apply_one (α := α) (x := x) hα_apply]
  rw [orbitSpaceMap_apply_mk_of_apply_one (α := β) (x := γ⁻¹ • x) hβ_apply]
  change Quotient.mk'' (((γ * δ)⁻¹ : G) • x) = Quotient.mk'' (δ⁻¹ • (γ⁻¹ • x) : X)
  simp [smul_smul]

/-- Lemma 3.8.8: for a `G`-space `X`, passage to orbit spaces defines a functor
`X/(-) : O(G) ⥤ TopCat`, sending `G/H` to `X/H` and an orbit map determined by `γ` to the map
`Hx ↦ K (γ⁻¹ • x)`. -/
noncomputable def orbitSpaceFunctor (G : Type u) [Group G] (X : Type v)
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] :
    O(G) ⥤ TopCat where
  obj H := TopCat.of (X /[H])
  map {_ _} α := TopCat.ofHom (orbitSpaceMap G X α)
  map_id H := by
    simpa using congrArg TopCat.ofHom (orbitSpaceMap_id G X H)
  map_comp α β := by
    simpa using congrArg TopCat.ofHom (orbitSpaceMap_comp G X α β)

end Topological
